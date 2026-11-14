
import json, re, os

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
                    m = re.match(r'^(?:private |protected |noncomputable |) *(?:theorem|lemma|def|structure|class|inductive|abbrev) ([a-zA-Z0-9_]+)', line)
                    if m:
                        names[m.group(1)] = module

for e in data['entries']:
    if e['module'] is None:
        continue
    for name in e['declarations']:
        if name in names:
            if names[name] != e['module']:
                print(f"Mismatch for {name}: code says {names[name]}, json says {e['module']}")
        else:
            print(f"Declaration {name} not found in code")
