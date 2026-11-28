/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Linear Volterra integral equations of the second kind

For a kernel `k : ℝ → ℝ → E →L[ℝ] E` continuous on the triangle `0 ≤ s ≤ t ≤ T` and continuous
data `f` on `[0, T]` with values in a real Banach space `E`, the equation
`u t = f t + ∫ s in 0..t, k t s (u s)` has a unique continuous solution on `[0, T]`. The scalar
form with a coupling constant, `u t = f t + c * ∫ s in 0..t, k t s * u s` over `ℝ` or `ℂ`, is
the special case of multiplication operators. For `T < 0` the interval is empty and the
statements are vacuous.

## Main definitions

* `CKMA.volterraIntegral`: the Volterra integral operator `t ↦ ∫ s in 0..t, k t s (u s)`.

## Main results

* `CKMA.existsUnique_volterra`: unique continuous solvability of the linear Volterra equation of
  the second kind with an operator-valued kernel.
* `CKMA.existsUnique_volterra_mul`: the scalar form over `RCLike 𝕜` with a coupling constant.

## Implementation notes

The kernel is extended from the triangle to the plane by composing with a continuous retraction
of the plane onto the triangle. The `n`-th iterate of the Volterra operator has norm at most
`(M T) ^ n / n!`, where `M` bounds the kernel on the triangle (`integral_pow`), so some iterate
of the affine map `u ↦ f + K u` is a contraction and its fixed point
(`ContractingWith.isFixedPt_fixedPoint_iterate`) is the solution.

## References

* R. Kress, *Linear Integral Equations*, 3rd ed., Springer, 2014.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology intervalIntegral Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Volterra integral `t ↦ ∫ s in 0..t, k t s (u s)` of an operator-valued kernel `k`. -/
@[expose]
def volterraIntegral (k : ℝ → ℝ → E →L[ℝ] E) (u : ℝ → E) (t : ℝ) : E :=
  ∫ s in (0 : ℝ)..t, k t s (u s)

/-- Defining equation of `volterraIntegral`. -/
theorem volterraIntegral_def (k : ℝ → ℝ → E →L[ℝ] E) (u : ℝ → E) (t : ℝ) :
    volterraIntegral k u t = ∫ s in (0 : ℝ)..t, k t s (u s) :=
  rfl

/-- The triangle `0 ≤ s ≤ t ≤ T` on which a Volterra kernel is controlled. -/
private def volterraTriangle (T : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}

/-- The triangle is compact. -/
private lemma isCompact_volterraTriangle (T : ℝ) : IsCompact (volterraTriangle T) := by
  have hcl : IsClosed (volterraTriangle T) :=
    (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst continuous_const))
  refine ((isCompact_Icc (a := (0 : ℝ)) (b := T)).prod
      (isCompact_Icc (a := (0 : ℝ)) (b := T))).of_isClosed_subset hcl ?_
  intro p hp
  exact ⟨⟨hp.1.trans hp.2.1, hp.2.2⟩, ⟨hp.1, hp.2.1.trans hp.2.2⟩⟩

/-- A continuous retraction of the plane onto the triangle `0 ≤ s ≤ t ≤ T`. -/
private def volterraRetract (T : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (max 0 (min p.1 T), max 0 (min p.2 (max 0 (min p.1 T))))

/-- The retraction is continuous. -/
private lemma continuous_volterraRetract (T : ℝ) : Continuous (volterraRetract T) := by
  unfold volterraRetract
  fun_prop

/-- The retraction maps into the triangle when `0 ≤ T`. -/
private lemma volterraRetract_mem {T : ℝ} (hT : 0 ≤ T) (p : ℝ × ℝ) :
    volterraRetract T p ∈ volterraTriangle T :=
  ⟨le_max_left _ _, max_le (le_max_left _ _) (min_le_right _ _),
    max_le hT (min_le_right _ _)⟩

/-- The retraction fixes the triangle. -/
private lemma volterraRetract_of_mem {T : ℝ} {p : ℝ × ℝ} (hp : p ∈ volterraTriangle T) :
    volterraRetract T p = p := by
  obtain ⟨h0, hst, htT⟩ := hp
  have h1 : max 0 (min p.1 T) = p.1 := by
    rw [min_eq_left htT, max_eq_right (h0.trans hst)]
  simp only [volterraRetract, h1, min_eq_left hst, max_eq_right h0]

/-- Extension of a continuous path on `[0, T]` to the line, by its endpoint values. -/
private def volterraProj {T : ℝ} (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, E)) (s : ℝ) : E :=
  u (projIcc 0 T hT s)

omit [NormedSpace ℝ E] in
/-- The projected extension is continuous. -/
private lemma continuous_volterraProj {T : ℝ} (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, E)) :
    Continuous (volterraProj hT u) :=
  u.continuous.comp continuous_projIcc

omit [NormedSpace ℝ E] in
/-- On `[0, T]` the projected extension is the path itself. -/
private lemma volterraProj_of_mem {T : ℝ} (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, E)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) : volterraProj hT u s = u ⟨s, hs⟩ := by
  simp [volterraProj, projIcc_of_mem hT hs]

/-- The Volterra operator of a kernel `g` continuous on the plane, acting on `C([0, T], E)`. -/
private def volterraOp {T : ℝ} (hT : 0 ≤ T) {g : ℝ × ℝ → E →L[ℝ] E} (hg : Continuous g)
    (u : C(Icc (0 : ℝ) T, E)) : C(Icc (0 : ℝ) T, E) :=
  ⟨fun t ↦ ∫ s in (0 : ℝ)..(t : ℝ), g ((t : ℝ), s) (volterraProj hT u s),
    (continuous_parametric_intervalIntegral_of_continuous
      (f := fun t s ↦ g (t, s) (volterraProj hT u s))
      (hg.clm_apply ((continuous_volterraProj hT u).comp continuous_snd))
      continuous_id).comp continuous_subtype_val⟩

/-- Evaluation of the Volterra operator. -/
private lemma volterraOp_apply {T : ℝ} (hT : 0 ≤ T) {g : ℝ × ℝ → E →L[ℝ] E} (hg : Continuous g)
    (u : C(Icc (0 : ℝ) T, E)) (t : Icc (0 : ℝ) T) :
    volterraOp hT hg u t = ∫ s in (0 : ℝ)..(t : ℝ), g ((t : ℝ), s) (volterraProj hT u s) :=
  rfl

/-- The Volterra operator is additive. -/
private lemma volterraOp_sub {T : ℝ} (hT : 0 ≤ T) {g : ℝ × ℝ → E →L[ℝ] E} (hg : Continuous g)
    (u v : C(Icc (0 : ℝ) T, E)) :
    volterraOp hT hg (u - v) = volterraOp hT hg u - volterraOp hT hg v := by
  ext t
  have hint (w : C(Icc (0 : ℝ) T, E)) :
      IntervalIntegrable (fun s ↦ g ((t : ℝ), s) (volterraProj hT w s)) volume 0 t :=
    ((hg.comp (continuous_const.prodMk continuous_id)).clm_apply
      (continuous_volterraProj hT w)).intervalIntegrable _ _
  rw [ContinuousMap.sub_apply, volterraOp_apply, volterraOp_apply, volterraOp_apply,
    ← intervalIntegral.integral_sub (hint u) (hint v)]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  simp [volterraProj]

/-- The iterates of the Volterra operator obey `‖K^n w (t)‖ ≤ ‖w‖ M^n t^n / n!` when `M` bounds
the kernel on the triangle. -/
private lemma norm_volterraOp_iterate_le {T : ℝ} (hT : 0 ≤ T) {g : ℝ × ℝ → E →L[ℝ] E}
    (hg : Continuous g) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ p ∈ volterraTriangle T, ‖g p‖ ≤ M)
    (n : ℕ) (w : C(Icc (0 : ℝ) T, E)) (t : Icc (0 : ℝ) T) :
    ‖((volterraOp hT hg)^[n] w) t‖ ≤ ‖w‖ * M ^ n * (t : ℝ) ^ n / n.factorial := by
  induction n generalizing t with
  | zero => simpa using w.norm_coe_le_norm t
  | succ n ih =>
    rw [Function.iterate_succ_apply', volterraOp_apply]
    have hle : ‖∫ s in (0 : ℝ)..(t : ℝ),
          g ((t : ℝ), s) (volterraProj hT ((volterraOp hT hg)^[n] w) s)‖ ≤
        ∫ s in (0 : ℝ)..(t : ℝ), ‖w‖ * M ^ (n + 1) / n.factorial * s ^ n := by
      refine intervalIntegral.norm_integral_le_of_norm_le t.2.1
        (ae_of_all _ fun s hs ↦ ?_) (Continuous.intervalIntegrable (by fun_prop) _ _)
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.trans t.2.2⟩
      rw [volterraProj_of_mem hT _ hsT]
      calc
        _ ≤ ‖g ((t : ℝ), s)‖ * ‖((volterraOp hT hg)^[n] w) ⟨s, hsT⟩‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ M * (‖w‖ * M ^ n * s ^ n / n.factorial) :=
          mul_le_mul (hM _ ⟨hs.1.le, hs.2, t.2.2⟩) (ih ⟨s, hsT⟩) (norm_nonneg _) hM0
        _ = ‖w‖ * M ^ (n + 1) / n.factorial * s ^ n := by ring
    refine hle.trans_eq ?_
    rw [intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The `n`-th iterate of `u ↦ f + K u` is Lipschitz with constant `(M T) ^ n / n!`. -/
private lemma dist_iterate_volterra_le {T : ℝ} (hT : 0 ≤ T) {g : ℝ × ℝ → E →L[ℝ] E}
    (hg : Continuous g) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ p ∈ volterraTriangle T, ‖g p‖ ≤ M)
    (f : C(Icc (0 : ℝ) T, E)) (n : ℕ) (u v : C(Icc (0 : ℝ) T, E)) :
    dist ((fun w ↦ f + volterraOp hT hg w)^[n] u) ((fun w ↦ f + volterraOp hT hg w)^[n] v) ≤
      (M * T) ^ n / n.factorial * dist u v := by
  have hiter : ∀ n : ℕ, (fun w ↦ f + volterraOp hT hg w)^[n] u -
      (fun w ↦ f + volterraOp hT hg w)^[n] v = (volterraOp hT hg)^[n] (u - v) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [Function.iterate_succ_apply', add_sub_add_left_eq_sub, ← volterraOp_sub, ih]
  rw [ContinuousMap.dist_le (by positivity)]
  intro t
  rw [dist_eq_norm, ← ContinuousMap.sub_apply, hiter, dist_eq_norm]
  calc
    _ ≤ ‖u - v‖ * M ^ n * (t : ℝ) ^ n / n.factorial :=
      norm_volterraOp_iterate_le hT hg hM0 hM n (u - v) t
    _ ≤ ‖u - v‖ * M ^ n * T ^ n / n.factorial := by
      gcongr
      exact t.2.1
      exact t.2.2
    _ = (M * T) ^ n / n.factorial * ‖u - v‖ := by ring

/-- **25.18**, Volterra equations of the second kind: for a kernel `k : ℝ → ℝ → E →L[ℝ] E`
continuous on the triangle `0 ≤ s ≤ t ≤ T` and continuous data `f` on `[0, T]` in a real
Banach space `E`, the equation `u t = f t + ∫ s in 0..t, k t s (u s)` has a unique continuous
solution on `[0, T]`. For `T < 0` the interval `Icc 0 T` is empty, so the statement is
vacuous. -/
theorem existsUnique_volterra [CompleteSpace E] {T : ℝ} (k : ℝ → ℝ → E →L[ℝ] E)
    (hk : ContinuousOn (fun p : ℝ × ℝ ↦ k p.1 p.2) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    (f : C(Icc (0 : ℝ) T, E)) :
    ∃! u : C(Icc (0 : ℝ) T, E), ∀ t : Icc (0 : ℝ) T,
      u t = f t + volterraIntegral k
        (fun s ↦ if hs : s ∈ Icc (0 : ℝ) T then u ⟨s, hs⟩ else 0) t.1 := by
  by_cases hT : 0 ≤ T
  swap
  · have hempty : IsEmpty (Icc (0 : ℝ) T) := ⟨fun t ↦ hT (t.2.1.trans t.2.2)⟩
    exact ⟨0, fun t ↦ hempty.elim t, fun _ _ ↦ ContinuousMap.ext fun t ↦ hempty.elim t⟩
  have htri : ContinuousOn (fun p : ℝ × ℝ ↦ k p.1 p.2) (volterraTriangle T) := hk
  set g : ℝ × ℝ → E →L[ℝ] E := fun p ↦ k (volterraRetract T p).1 (volterraRetract T p).2
  have hg : Continuous g :=
    htri.comp_continuous (continuous_volterraRetract T) (volterraRetract_mem hT)
  have hgk : ∀ p ∈ volterraTriangle T, g p = k p.1 p.2 := fun p hp ↦ by
    simp only [g, volterraRetract_of_mem hp]
  obtain ⟨p₀, -, hmax⟩ := (isCompact_volterraTriangle T).exists_isMaxOn
    ⟨(0, 0), le_rfl, le_rfl, hT⟩ (continuous_norm.comp_continuousOn htri)
  set M := ‖k p₀.1 p₀.2‖
  have hM : ∀ p ∈ volterraTriangle T, ‖g p‖ ≤ M := fun p hp ↦ by
    rw [hgk p hp]
    exact hmax hp
  set Φ : C(Icc (0 : ℝ) T, E) → C(Icc (0 : ℝ) T, E) := fun w ↦ f + volterraOp hT hg w
  -- The fixed points of `Φ` are exactly the solutions.
  have hfix : ∀ w : C(Icc (0 : ℝ) T, E), Φ w = w ↔ ∀ t : Icc (0 : ℝ) T,
      w t = f t + volterraIntegral k
        (fun s ↦ if hs : s ∈ Icc (0 : ℝ) T then w ⟨s, hs⟩ else 0) t.1 := by
    intro w
    have hK : ∀ t : Icc (0 : ℝ) T, volterraOp hT hg w t = volterraIntegral k
        (fun s ↦ if hs : s ∈ Icc (0 : ℝ) T then w ⟨s, hs⟩ else 0) t.1 := by
      intro t
      refine intervalIntegral.integral_congr fun s hs ↦ ?_
      rw [uIcc_of_le t.2.1] at hs
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans t.2.2⟩
      simp [volterraProj_of_mem hT w hsT, hgk ((t : ℝ), s) ⟨hs.1, hs.2, t.2.2⟩, hsT]
    simp only [Φ, ContinuousMap.ext_iff, ContinuousMap.add_apply, hK, eq_comm (a := w _)]
  obtain ⟨n, hn⟩ := (FloorSemiring.tendsto_pow_div_factorial_atTop (M * T)).eventually
    (gt_mem_nhds zero_lt_one) |>.exists
  have hr0 : 0 ≤ (M * T) ^ n / n.factorial := by positivity
  have : Nonempty C(Icc (0 : ℝ) T, E) := ⟨0⟩
  have hcontr : ContractingWith (Real.toNNReal ((M * T) ^ n / n.factorial)) (Φ^[n]) :=
    ⟨by rwa [Real.toNNReal_lt_iff_lt_coe hr0, NNReal.coe_one],
      LipschitzWith.of_dist_le' fun u v ↦ dist_iterate_volterra_le hT hg (norm_nonneg _) hM f n u v⟩
  refine ⟨hcontr.fixedPoint (Φ^[n]), (hfix _).1 hcontr.isFixedPt_fixedPoint_iterate,
    fun v hv ↦ ?_⟩
  exact (hcontr.eq_or_edist_eq_top_of_fixedPoints (Function.IsFixedPt.iterate ((hfix v).2 hv) n)
    (Function.IsFixedPt.iterate hcontr.isFixedPt_fixedPoint_iterate n)).resolve_right
    (edist_ne_top _ _)

/-- **25.18**, scalar form: for a scalar kernel `k : ℝ → ℝ → 𝕜` over `𝕜 = ℝ` or `ℂ`,
continuous on the triangle `0 ≤ s ≤ t ≤ T`, every coupling `c : 𝕜` and continuous data `f`,
the equation `u t = f t + c * ∫ s in 0..t, k t s * u s` has a unique continuous solution on
`[0, T]`. -/
theorem existsUnique_volterra_mul {𝕜 : Type*} [RCLike 𝕜] {T : ℝ} (k : ℝ → ℝ → 𝕜)
    (hk : ContinuousOn (fun p : ℝ × ℝ ↦ k p.1 p.2) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    (c : 𝕜) (f : C(Icc (0 : ℝ) T, 𝕜)) :
    ∃! u : C(Icc (0 : ℝ) T, 𝕜), ∀ t : Icc (0 : ℝ) T,
      u t = f t + c * ∫ s in (0 : ℝ)..t.1,
        k t.1 s * (if hs : s ∈ Icc (0 : ℝ) T then u ⟨s, hs⟩ else 0) := by
  have hk' : ContinuousOn (fun p : ℝ × ℝ ↦ ContinuousLinearMap.mul ℝ 𝕜 (c * k p.1 p.2))
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} :=
    (ContinuousLinearMap.mul ℝ 𝕜).continuous.comp_continuousOn (continuousOn_const.mul hk)
  refine (existsUnique_congr fun u ↦ forall_congr' fun t ↦ ?_).1
    (existsUnique_volterra (fun t s ↦ ContinuousLinearMap.mul ℝ 𝕜 (c * k t s)) hk' f)
  rw [volterraIntegral_def, ← intervalIntegral.integral_const_mul]
  simp only [ContinuousLinearMap.mul_apply', mul_assoc]

end CKMA
