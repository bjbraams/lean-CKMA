with open("CKMA/Analysis/Nonlinear/Monotone.lean", "r") as f:
    text = f.read()

lemma = """/-- A finite sum of continuous complex functions of a real variable is continuous. -/
private lemma continuous_finset_sum' {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℂ}
    (hf : ∀ i ∈ s, Continuous (f i)) : Continuous (fun t ↦ ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simpa using continuous_const
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

"""

text = text.replace("namespace CKMA\n\n", "namespace CKMA\n\n" + lemma)
text = text.replace("continuous_finset_sum", "continuous_finset_sum'")

with open("CKMA/Analysis/Nonlinear/Monotone.lean", "w") as f:
    f.write(text)
