
import Mathlib

private lemma continuous_finset_sum' {α β ι : Type*} [TopologicalSpace α] [AddCommMonoid β] [TopologicalSpace β] [ContinuousAdd β] (s : Finset ι) {f : ι → α → β}
    (hf : ∀ i ∈ s, Continuous (f i)) : Continuous (fun t ↦ ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simpa using continuous_const
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {n : ℕ} (p : Fin n → H × H)
let bary (weight : Fin n → ℝ) : H := ∑ i, weight i • (p i).1
#check (continuous_finset_sum' Finset.univ (fun i _ => continuous_const))
