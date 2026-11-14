
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable (T : Ω ≃ᵐ Ω)

private lemma symm_iterate_apply (i : ℕ) (x : Ω) : (T.symm^[i]) ((T^[i]) x) = x := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ, Function.iterate_succ_apply', Function.comp_apply, T.symm_apply_apply, ih]

private lemma iterate_symm_apply (i : ℕ) (x : Ω) : (T^[i]) ((T.symm^[i]) x) = x := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ, Function.iterate_succ_apply', Function.comp_apply, T.apply_symm_apply, ih]
