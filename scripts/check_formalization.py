#!/usr/bin/env python3
"""Check CKMA's gap index, source inventory, compilation and axiom dependencies.

Run from the Lake root after `lake build > /tmp/ckma-build.log 2>&1`.
Default: metadata checks. --check-lean: check each source with package options.
--audit: ask Lean for every declaration's axiom dependencies and save them.
--refresh: refresh declaration locations after source edits (clears the previous audit).
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
INDEX = ROOT / 'formalization.json'
DECL = re.compile(
    r'^(private )?(noncomputable )?(theorem|lemma|def|abbrev|structure) ([\w.\']+)')
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def mask_comments_and_strings(source):
    """Mask Lean comments and quoted strings, preserving source offsets and newlines."""
    chars = list(source)
    i, depth = 0, 0
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                chars[i:i + 2] = '  '
                depth += 1
                i += 2
            elif source.startswith('-/', i):
                chars[i:i + 2] = '  '
                depth -= 1
                i += 2
            else:
                if source[i] != '\n':
                    chars[i] = ' '
                i += 1
        elif source.startswith('/-', i):
            chars[i:i + 2] = '  '
            depth = 1
            i += 2
        elif source.startswith('--', i):
            while i < len(source) and source[i] != '\n':
                chars[i] = ' '
                i += 1
        elif source[i] == '"':
            chars[i] = ' '
            i += 1
            while i < len(source):
                c = source[i]
                if c != '\n':
                    chars[i] = ' '
                i += 1
                if c == '\\' and i < len(source):
                    if source[i] != '\n':
                        chars[i] = ' '
                    i += 1
                elif c == '"':
                    break
        else:
            i += 1
    return ''.join(chars)


SCOPE = re.compile(r'^(namespace|section|end)(?:\s+([\w.]+))?\s*$')


def declaration_names(code):
    """Fully qualified names, following `namespace` and ignoring `section`."""
    stack = []
    found = []
    offset = 0
    for line in code.splitlines(keepends=True):
        scope = SCOPE.match(line)
        if scope:
            kind, name = scope.group(1), scope.group(2)
            if kind == 'namespace':
                stack.extend(('ns', part) for part in name.split('.'))
            elif kind == 'section':
                stack.append(('sec', name))
            elif name is None:
                stack.pop()
            else:
                parts = name.split('.')
                if len(parts) == 1 and stack and stack[-1] == ('sec', parts[0]):
                    stack.pop()
                else:
                    del stack[-len(parts):]
        else:
            match = DECL.match(line)
            if match:
                prefix = '.'.join(part for kind, part in stack if kind == 'ns')
                short = match[4]
                found.append((offset + match.start(), offset + match.end(), match[3],
                              f'{prefix}.{short}' if prefix else short, match[1] is not None))
        offset += len(line)
    return found


def inventory():
    result = []
    for path in sorted((ROOT / 'CKMA').rglob('*.lean')):
        source = path.read_text()
        code = mask_comments_and_strings(source)
        matches = declaration_names(code)
        if matches:
            assert 'namespace CKMA' in source, f'Missing namespace: {path}'
            assert '_root_' not in source, f'Unexpected root declaration: {path}'
        for i, (start, match_end, kind, full_name, private) in enumerate(matches):
            end = matches[i + 1][0] if i + 1 < len(matches) else len(source)
            if private:
                continue
            result.append({
                'name': full_name,
                'kind': kind,
                'module': '.'.join(path.relative_to(ROOT).with_suffix('').parts),
                'line': source.count('\n', 0, start) + 1,
                'direct_sorry': bool(re.search(r'^\s*sorry\s*$', code[match_end:end], re.M)),
            })
    return result


def source_hashes():
    files = [ROOT / 'CKMA.lean', *sorted((ROOT / 'CKMA').rglob('*.lean'))]
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}


def check(data, current):
    assert data.get('source_sha256') == source_hashes(), 'Changed Lean sources; rebuild, --refresh and --audit.'
    gaps = re.findall(r'^\* \*\*(\d{2}\.\d+)\. (.*?)\*\*', (ROOT / 'GAPS.md').read_text(), re.M)
    assert [(e['id'], e['title']) for e in data['entries']] == [(i, t.rstrip('.')) for i, t in gaps]
    assert len(gaps) == 603 and len(set(i for i, _ in gaps)) == 603
    easy = set(re.findall(r'^### (\d{2}\.\d+)\.', (ROOT / 'GAPS_EASY.md').read_text(), re.M))
    assert easy == {e['id'] for e in data['entries'] if e['easy']}
    assert len(easy) == 59
    recorded = [{k: v for k, v in d.items() if k != 'axioms'} for d in data['declarations']]
    assert recorded == current, 'Stale declaration inventory; run --refresh and repeat --audit.'
    names = {d['name']: d for d in current}
    assert len(names) == len(current), 'Duplicate declaration name'
    for e in data['entries']:
        assert e['status'] in data['status_meanings']
        assert (e['status'] == 'not_started') == (e['module'] is None)
        assert bool(e['declarations']) == (e['module'] is not None)
        for name in e['declarations']:
            assert name in names, f"Unknown declaration for {e['id']}: {name}"
            assert names[name]['module'] == e['module']
    for area in ['Analysis', 'Probability', 'Dynamics', 'MeasureTheory']:
        assembly = (ROOT / 'CKMA' / (area + '.lean')).read_text()
        expected = {'.'.join(p.relative_to(ROOT).with_suffix('').parts)
                    for p in (ROOT / 'CKMA' / area).rglob('*.lean')}
        assert set(re.findall(r'^public import (\S+)', assembly, re.M)) == expected
    print(f"Index: {len(gaps)} gaps, {sum(e['module'] is not None for e in data['entries'])} started; "
          f"{len(current)} declarations.", flush=True)


def check_lean():
    files = [ROOT / 'CKMA.lean', *sorted((ROOT / 'CKMA').rglob('*.lean'))]
    log = Path('/tmp/ckma-single-files.log')
    with log.open('w') as output:
        for i, path in enumerate(files, 1):
            command = ['lake', 'env', 'lean', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
                       str(path.relative_to(ROOT))]
            output.write(f"\nChecking {path.relative_to(ROOT)}\n")
            output.flush()
            subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT, check=True)
            if i % 10 == 0 or i == len(files):
                print(f'Lean: {i}/{len(files)} files checked.', flush=True)
    print(f'Per-file log: {log}', flush=True)


def audit(data):
    # The audit file is temporary, imports the public entry module, and declares no constants.
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', dir='/tmp', delete=False) as audit_file:
        path = Path(audit_file.name)
        audit_file.write('import CKMA\n\n')
        for decl in data['declarations']:
            audit_file.write('#print axioms ' + decl['name'] + '\n')
    try:
        run = subprocess.run(['lake', 'env', 'lean', '-DautoImplicit=false',
                              '-DrelaxedAutoImplicit=false', str(path)], cwd=ROOT,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        Path('/tmp/ckma-axioms.log').write_text(run.stdout)
        assert run.returncode == 0, 'Lean axiom audit failed; see /tmp/ckma-axioms.log'
        axioms = {}
        lines = run.stdout.splitlines()
        index = 0
        while index < len(lines):
            line = lines[index]
            none = re.match(r"^'(.*)' does not depend on any axioms$", line)
            one = re.match(r"^'(.*)' depends on axioms: \[(.*)\]$", line)
            many = re.match(r"^'(.*)' depends on axioms: \[(.*)$", line)
            if none:
                axioms[none[1]] = []
            elif one:
                axioms[one[1]] = sorted(
                    filter(None, (part.strip() for part in one[2].split(','))))
            elif many:
                parts = [many[2]]
                index += 1
                while index < len(lines) and ']' not in lines[index]:
                    parts.append(lines[index])
                    index += 1
                parts.append(lines[index].split(']', 1)[0])
                axioms[many[1]] = sorted(
                    filter(None, (part.strip() for part in ','.join(parts).split(','))))
            index += 1
        for decl in data['declarations']:
            assert decl['name'] in axioms, f"Missing audit output: {decl['name']}"
            decl['axioms'] = axioms[decl['name']]
            unexpected = set(decl['axioms']) - STANDARD_AXIOMS - {'sorryAx'}
            assert not unexpected, f"Unexpected axioms for {decl['name']}: {unexpected}"
            if decl['kind'] in {'def', 'abbrev', 'structure'}:
                assert 'sorryAx' not in decl['axioms'], f"Admitted definition: {decl['name']}"
            if decl['direct_sorry']:
                assert 'sorryAx' in decl['axioms']
        by_name = {d['name']: d for d in data['declarations']}
        for entry in data['entries']:
            if entry['status'] == 'proved':
                assert all('sorryAx' not in by_name[n]['axioms'] for n in entry['declarations']), entry['id']
        admitted = sum('sorryAx' in d['axioms'] for d in data['declarations'])
        direct = sum(d['direct_sorry'] for d in data['declarations'])
        print(f'Axioms: {admitted} declarations depend on sorryAx ({direct} direct admissions); '
              f'{len(data["declarations"]) - admitted} declarations use only standard axioms.', flush=True)
    finally:
        path.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--refresh', action='store_true')
    parser.add_argument('--check-lean', action='store_true')
    parser.add_argument('--audit', action='store_true')
    args = parser.parse_args()
    data = json.loads(INDEX.read_text())
    current = inventory()
    if args.refresh:
        data['declarations'] = current
        data['source_sha256'] = source_hashes()
    check(data, current)
    if args.check_lean:
        check_lean()
    if args.audit:
        audit(data)
    if args.refresh or args.audit:
        INDEX.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


if __name__ == '__main__':
    main()
