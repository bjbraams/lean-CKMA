
import Mathlib

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]

private theorem freudenthal_rescale_bounds {u x : E} {c : ℝ} (hu : 0 ≤ u) (hc0 : 0 ≤ c)
    (hxc : |x| ≤ c • u) :
    let c1 : ℝ := c + 1
    let lam : ℝ := 2 * c1
    let w1 : E := lam⁻¹ • (x + c1 • u)
    0 < lam ∧ 0 ≤ w1 ∧ w1 ≤ u ∧ lam • w1 = x + c1 • u := by
  intro c1 lam w1
  set w := x + c1 • u
  have hlam : 0 < lam := by dsimp [lam, c1]; linarith
  have hx_le_abs : -|x| ≤ x := neg_le_abs x
  have hw0 : 0 ≤ w := by
    have hbase : 0 ≤ (c1 - c) • u := smul_nonneg (by dsimp [c1]; linarith) hu
    have hrest : (c1 - c) • u = -(c • u) + c1 • u := by
      rw [sub_smul, neg_add_eq_sub, sub_eq_add_neg, add_comm]
    calc
      0 ≤ (c1 - c) • u := hbase
      _ = -(c • u) + c1 • u := hrest
      _ ≤ -|x| + c1 • u := add_le_add_left (neg_le_neg hxc) _
      _ ≤ x + c1 • u := add_le_add_left hx_le_abs _
  have hclam : c + c1 ≤ lam := by dsimp [c1, lam]; linarith
  have hwlam : w ≤ lam • u := by
    calc
      w = x + c1 • u := rfl
      _ ≤ |x| + c1 • u := add_le_add_left (le_abs_self x) _
      _ ≤ c • u + c1 • u := add_le_add_left hxc _
      _ = (c + c1) • u := by rw [← add_smul]
      _ ≤ lam • u := smul_le_smul_of_nonneg_right hclam hu
  have hw10 : 0 ≤ w1 := smul_nonneg (inv_nonneg.2 hlam.le) hw0
  have hw1u : w1 ≤ u := by
    have hmul := smul_le_smul_of_nonneg_left hwlam (inv_nonneg.2 hlam.le)
    have hcancel : lam⁻¹ • (lam • u) = u := by
      rw [← mul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
    rwa [hcancel] at hmul
  have hw1w : lam • w1 = x + c1 • u := by
    dsimp [w1]
    rw [← mul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
  exact ⟨hlam, hw10, hw1u, hw1w⟩
