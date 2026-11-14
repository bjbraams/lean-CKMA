
import os, re, json
from pathlib import Path

ROOT = Path(".")
for area in ['Analysis', 'Probability', 'Dynamics', 'MeasureTheory']:
    lean_file = ROOT / 'CKMA' / (area + '.lean')
    assembly = lean_file.read_text()
    expected = {'.'.join(p.relative_to(ROOT).with_suffix('').parts)
                for p in (ROOT / 'CKMA' / area).rglob('*.lean')}
    actual = set(re.findall(r'^public import (\S+)', assembly, re.M))
    
    missing = expected - actual
    if missing:
        lines = assembly.splitlines()
        for i, line in enumerate(lines):
            if line.startswith('public import '):
                # find the end of imports
                pass
        
        # just append them at the end, then sort imports
        # Or better, just collect all imports, sort them, and put them back.
        header = []
        footer = []
        in_imports = False
        imports = list(expected)
        imports.sort()
        
        new_lines = []
        for line in lines:
            if line.startswith('public import '):
                continue
            if line.startswith('/-!'):
                new_lines.extend(['public import ' + imp for imp in imports])
                new_lines.append('')
                new_lines.append(line)
            else:
                new_lines.append(line)
        
        # if no docstring, just append
        if not any(line.startswith('/-!') for line in lines):
            # this shouldn't happen based on the file structure
            pass
            
        lean_file.write_text('\n'.join(new_lines) + '\n')

# Now update formalization.json
with open("formalization.json") as f:
    data = json.load(f)

names = {}
for root, dirs, files in os.walk("CKMA"):
    for file in files:
        if file.endswith(".lean"):
            path = os.path.relpath(os.path.join(root, file), "CKMA")
            module = "CKMA." + path[:-5].replace("/", ".")
            with open(os.path.join(root, file)) as f:
                for line in f:
                    m = re.match(r'^(theorem|lemma|def|structure|class|inductive|abbrev) ([a-zA-Z0-9_]+)', line)
                    if m:
                        names[m.group(2)] = module

for e in data['entries']:
    if e['module'] is None:
        continue
    for name in e['declarations']:
        if name in names:
            if names[name] != e['module']:
                e['module'] = names[name]

with open("formalization.json", "w") as f:
    json.dump(data, f, indent=4)
    f.write('\n')
