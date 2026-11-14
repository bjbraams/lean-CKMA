with open("CKMA/Analysis/SpecialFunctions/Classical/GammaMultiplication.lean", "r") as f:
    text = f.read()

lemma = """/-- A finite sum of convex real functions on `(0, ∞)` is convex. -/
private theorem convexOn_sum {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, ConvexOn ℝ (Set.Ioi 0) (f i)) :
    ConvexOn ℝ (Set.Ioi 0) (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using convexOn_const (0 : ℝ) (convex_Ioi (0 : ℝ))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

"""

text = text.replace("namespace CKMA\n\n", "namespace CKMA\n\n" + lemma)
text = text.replace("ConvexOn.sum", "convexOn_sum")

with open("CKMA/Analysis/SpecialFunctions/Classical/GammaMultiplication.lean", "w") as f:
    f.write(text)
