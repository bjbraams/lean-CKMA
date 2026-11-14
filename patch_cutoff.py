with open("CKMA/Analysis/Fourier/Inequalities/Cutoff.lean", "r") as f:
    text = f.read()

import re
text = re.sub(r'have hEq : \(freqBumpScaled n : V → ℂ\) =\n\s*Complex.ofReal ∘ \(heisenbergFreqBump n : V → ℝ\) := by\n\s*rfl', 'have hEq : (freqBumpScaled n : V → ℂ) = Complex.ofReal ∘ (heisenbergFreqBump n : V → ℝ) := rfl', text)
text = re.sub(r'have hEq : \(freqBumpScaled n : V → ℂ\) =\n\s*\(Complex.ofRealCLM : ℝ → ℂ\) ∘ \(heisenbergFreqBump n : V → ℝ\) := by\n\s*rfl', 'have hEq : (freqBumpScaled n : V → ℂ) = (Complex.ofRealCLM : ℝ → ℂ) ∘ (heisenbergFreqBump n : V → ℝ) := rfl', text)

with open("CKMA/Analysis/Fourier/Inequalities/Cutoff.lean", "w") as f:
    f.write(text)
