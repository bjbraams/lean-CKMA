
import json

with open("formalization.json") as f:
    data = json.load(f)

# The script seems to fail on names[name]['module'] == e['module']
# Let's write a simple script to find the mismatch.
import re, os
def find_modules():
    names = {}
    for root, dirs, files in os.walk("CKMA"):
        for file in files:
            if file.endswith(".lean"):
                mod = file[:-5]
                path = os.path.relpath(os.path.join(root, mod), "CKMA").replace("/", ".")
                module = "CKMA." + path
                with open(os.path.join(root, file)) as f:
                    for line in f:
                        m = re.match(r'^(theorem|lemma|def|structure|class|inductive) ([a-zA-Z0-9_]+)', line)
                        if m:
                            names[m.group(2)] = module
    for e in data['entries']:
        name = e.get('lean_name')
        if name and name in names:
            if names[name] != e['module']:
                print(f"Mismatch for {name}: code says {names[name]}, json says {e['module']}")

find_modules()
