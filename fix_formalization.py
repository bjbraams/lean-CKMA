
import json

with open("formalization.json") as f:
    data = json.load(f)

for e in data['entries']:
    if e['id'] == '49.6':
        e['module'] = 'CKMA.Analysis.SpecialFunctions.Classical.GammaMultiplication'
    elif e['id'] == '49.13':
        e['module'] = 'CKMA.Analysis.SpecialFunctions.Classical.Hypergeometric'
    elif e['id'] == '49.30':
        e['module'] = 'CKMA.Analysis.SpecialFunctions.Classical.BesselGenerating'

with open("formalization.json", "w") as f:
    json.dump(data, f, indent=4)
    f.write('\n')
