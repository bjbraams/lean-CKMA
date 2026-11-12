/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.OrderedSpace.Bands.Lattice
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Kakutani representation of an AM space with unit

An AM unit identifies the closed norm ball with an order interval. The corresponding
weak-star state space is weak-star compact, and its extreme points are lattice
homomorphisms. Evaluation on the weak-star closure of those homomorphisms is a
lattice isometry onto `C(K, ℝ)`, by Krein–Milman and Stone–Weierstrass. The zero
space is represented by the empty compact carrier. The argument follows Schaefer,
*Banach Lattices and Positive Operators*, Proposition II.4.4 and Theorem II.7.4.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open Set Metric LinearMap WeakDual ContinuousLinearMap

namespace CKMA

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]

variable {e : E} (he0 : 0 ≤ e) (hball : closedBall (0 : E) 1 = Icc (-e) e)

/-- The weak-star dual is locally convex, so Krein–Milman applies to state spaces. -/
instance amWeakDualLocallyConvex (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    LocallyConvexSpace ℝ (WeakDual ℝ E) :=
  WeakBilin.locallyConvexSpace (B := topDualPairing ℝ E)

include he0 hball in
/-- A closed ball equal to `[-e, e]` forces every vector under the unit. -/
theorem abs_le_smul_amUnit (x : E) : |x| ≤ ‖x‖ • e := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hu : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hmem : ‖x‖⁻¹ • x ∈ Icc (-e) e := by
      rw [← hball, mem_closedBall_iff_norm]
      simpa using hu.le
    have hz1 : ‖x‖⁻¹ • x ≤ e := hmem.2
    have hz2 : -(‖x‖⁻¹ • x) ≤ e := by simpa using neg_le_neg hmem.1
    have habs : |‖x‖⁻¹ • x| ≤ e := sup_le hz1 hz2
    rw [abs_smul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))] at habs
    have hmul := smul_le_smul_of_nonneg_left habs (norm_nonneg x)
    simpa [smul_smul, mul_inv_cancel₀ hn] using hmul

include he0 hball in
/-- The AM unit has norm at most one. -/
theorem amUnit_norm_le_one : ‖e‖ ≤ 1 := by
  have hmem : e ∈ Icc (-e) e := ⟨le_trans (neg_nonpos.mpr he0) he0, le_rfl⟩
  rw [← hball, mem_closedBall_iff_norm] at hmem
  simpa using hmem

include he0 hball in
/-- A nonzero AM unit is a norm-one vector. -/
theorem amUnit_norm_eq_one (he : e ≠ 0) : ‖e‖ = 1 := by
  apply le_antisymm (amUnit_norm_le_one he0 hball)
  have habs : e ≤ ‖e‖ • e := by
    simpa [abs_of_nonneg he0] using abs_le_smul_amUnit he0 hball e
  have hsub : (1 - ‖e‖) • e ≤ 0 := by
    rw [sub_smul, one_smul]
    exact sub_nonpos.mpr habs
  by_contra hlt
  have hpos : 0 < 1 - ‖e‖ := sub_pos.mpr (lt_of_not_ge hlt)
  have hmul := smul_le_smul_of_nonneg_left hsub (inv_nonneg.mpr hpos.le)
  have hcancel : (1 - ‖e‖)⁻¹ • ((1 - ‖e‖) • e) = e := by
    rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  rw [hcancel] at hmul
  have hzero : e ≤ 0 := by simpa using hmul
  exact he (le_antisymm hzero he0)

include he0 hball in
/-- The zero AM unit occurs only for the zero space. -/
theorem subsingleton_of_amUnit_eq_zero (he : e = 0) : Subsingleton E := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  by_contra hx
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hu : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have hball' : closedBall (0 : E) 1 = {0} := by simpa [he, Icc_self] using hball
  have hmem : ‖x‖⁻¹ • x ∈ ({0} : Set E) := by
    rw [← hball', mem_closedBall_iff_norm]
    simpa using hu.le
  have hzero : ‖x‖⁻¹ • x = 0 := by simpa using hmem
  exact hx ((smul_eq_zero.mp hzero).resolve_left (inv_ne_zero hn))

include he0 hball in
/-- A positive continuous linear functional attains its norm on the AM unit. -/
theorem amPositive_opNorm_eq (he : e ≠ 0) (φ : E →L[ℝ] ℝ)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ φ x) : ‖φ‖ = φ e := by
  have hmono : Monotone φ := by
    intro a b hab
    have hsub : 0 ≤ φ (b - a) := hpos _ (sub_nonneg.mpr hab)
    have : 0 ≤ φ b - φ a := by simpa [map_sub] using hsub
    exact sub_nonneg.mp this
  have hbound : ∀ y, ‖φ y‖ ≤ φ e * ‖y‖ := by
    intro y
    have habs : |φ y| ≤ φ |y| := by
      refine abs_le.mpr ⟨?_, hmono (le_abs_self y)⟩
      have horder : -|y| ≤ y := by
        have h := neg_le_neg (le_abs_self (-y))
        rw [abs_neg, neg_neg] at h
        exact h
      have hneg : φ (-|y|) ≤ φ y := hmono horder
      simpa [map_neg] using hneg
    have hdom : φ |y| ≤ ‖y‖ * φ e := by
      have hy : |y| ≤ ‖y‖ • e := abs_le_smul_amUnit he0 hball y
      simpa [map_smul, smul_eq_mul] using hmono hy
    rw [Real.norm_eq_abs]
    exact habs.trans (by simpa [mul_comm] using hdom)
  have hle : ‖φ‖ ≤ φ e := φ.opNorm_le_bound (hpos e he0) hbound
  have hge : φ e ≤ ‖φ‖ := by
    have hnorm := φ.le_opNorm e
    rw [amUnit_norm_eq_one he0 hball he, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (hpos e he0)] at hnorm
    exact hnorm
  exact le_antisymm hle hge

/-- Norm of the positive part. -/
theorem posNorm_le_norm (y : E) : ‖y⁺‖ ≤ ‖y‖ := by
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (posPart_nonneg y)]
  calc
    y⁺ ≤ y⁺ + y⁻ := le_add_of_nonneg_right (negPart_nonneg y)
    _ = |y| := posPart_add_negPart y

/-- The positive-part norm is sublinear. -/
theorem posNorm_add_le (y₁ y₂ : E) : ‖(y₁ + y₂)⁺‖ ≤ ‖y₁⁺‖ + ‖y₂⁺‖ := by
  have hle : (y₁ + y₂)⁺ ≤ y₁⁺ + y₂⁺ :=
    sup_le (add_le_add (le_posPart y₁) (le_posPart y₂))
      (add_nonneg (posPart_nonneg y₁) (posPart_nonneg y₂))
  have hnorm : ‖(y₁ + y₂)⁺‖ ≤ ‖y₁⁺ + y₂⁺‖ := by
    apply norm_le_norm_of_abs_le_abs
    rw [abs_of_nonneg (posPart_nonneg _),
      abs_of_nonneg (add_nonneg (posPart_nonneg _) (posPart_nonneg _))]
    exact hle
  exact hnorm.trans (norm_add_le _ _)

/-- Positive-part norm is positively homogeneous. -/
theorem posNorm_smul {c : ℝ} (hc : 0 < c) (y : E) : ‖(c • y)⁺‖ = c * ‖y⁺‖ := by
  rw [posPart_smul_of_nonneg hc.le, norm_smul, Real.norm_eq_abs, abs_of_pos hc]

/-- Monotonicity of a linear map that is nonnegative on the positive cone. -/
theorem monotone_of_map_nonneg {φ : E →ₗ[ℝ] ℝ} (hpos : ∀ x, 0 ≤ x → 0 ≤ φ x) : Monotone φ := by
  intro a b hab
  have hsub : 0 ≤ φ (b - a) := hpos _ (sub_nonneg.mpr hab)
  have : 0 ≤ φ b - φ a := by simpa [map_sub] using hsub
  exact sub_nonneg.mp this

include he0 hball in
set_option backward.isDefEq.respectTransparency false in
/-- A positive norm-one state normalizing a given positive vector. -/
theorem exists_amState_norming (he : e ≠ 0) {x : E} (hx0 : 0 ≤ x) (hx : x ≠ 0) :
    ∃ φ : WeakDual ℝ E, (∀ y, 0 ≤ y → 0 ≤ φ y) ∧ φ e = 1 ∧ φ x = ‖x‖ := by
  let N : E → ℝ := fun y => ‖y⁺‖
  have hNadd : ∀ y₁ y₂, N (y₁ + y₂) ≤ N y₁ + N y₂ := posNorm_add_le
  have hNhom : ∀ c : ℝ, 0 < c → ∀ y, N (c • y) = c * N y := fun c hc y =>
    posNorm_smul hc y
  let f : E →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton x ‖x‖ hx
  have hExt := exists_extension_of_le_sublinear f N hNhom hNadd (by
    rintro ⟨z, hz⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [LinearPMap.mkSpanSingleton'_apply, RingHom.id_apply, smul_eq_mul]
    rcases le_or_gt c 0 with hc | hc
    · have hnonpos : c • x ≤ 0 := smul_nonpos_of_nonpos_of_nonneg hc hx0
      simp [N, posPart_eq_zero_of_nonpos hnonpos,
        mul_nonpos_of_nonpos_of_nonneg hc (norm_nonneg x)]
    · simp [N, posPart_smul_of_nonneg hc.le, hx0, norm_smul, Real.norm_eq_abs, abs_of_pos hc])
  obtain ⟨φ, hφdom, hφle⟩ := hExt
  have hφx : φ x = ‖x‖ := by
    rw [← f.domain.coe_mk x (Submodule.mem_span_singleton_self _), hφdom,
      LinearPMap.mkSpanSingleton'_apply_self]
  have hpos : ∀ y, 0 ≤ y → 0 ≤ φ y := by
    intro y hy
    have hneg : φ (-y) ≤ N (-y) := hφle (-y)
    have hNy : N (-y) = 0 := by
      simp [N, posPart_neg, negPart_eq_zero_of_nonneg hy]
    rw [map_neg] at hneg
    linarith
  have hbound : ∀ y, ‖φ y‖ ≤ 1 * ‖y‖ := by
    intro y
    have hup : φ y ≤ ‖y‖ := (hφle y).trans (posNorm_le_norm y)
    have hdown : -‖y‖ ≤ φ y := by
      have hneg : φ (-y) ≤ ‖(-y)⁺‖ := hφle (-y)
      rw [map_neg, posPart_neg] at hneg
      have hnegle : ‖y⁻‖ ≤ ‖y‖ := by
        apply norm_le_norm_of_abs_le_abs
        rw [abs_of_nonneg (negPart_nonneg y)]
        calc
          y⁻ ≤ y⁺ + y⁻ := le_add_of_nonneg_left (posPart_nonneg y)
          _ = |y| := posPart_add_negPart y
      linarith
    rw [← one_mul ‖y‖] at hup hdown
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨hdown, hup⟩
  let ψ : E →L[ℝ] ℝ := φ.mkContinuous 1 hbound
  have hψpos : ∀ y, 0 ≤ y → 0 ≤ ψ y := by simpa [ψ] using hpos
  have hψx : ψ x = ‖x‖ := by simpa [ψ] using hφx
  have hψe : ψ e = 1 := by
    have hle : ψ x ≤ ‖x‖ * ψ e := by
      have hxle : x ≤ ‖x‖ • e := by
        simpa [abs_of_nonneg hx0] using abs_le_smul_amUnit he0 hball x
      simpa [map_smul, smul_eq_mul] using
        (monotone_of_map_nonneg (φ := ψ.toLinearMap) fun y hy => by simpa using hψpos y hy) hxle
    have hone : 1 ≤ ψ e := by
      have hxpos : 0 < ‖x‖ := (norm_pos_iff).mpr hx
      have : ‖x‖ ≤ ‖x‖ * ψ e := by simpa [hψx] using hle
      exact (le_mul_iff_one_le_right hxpos).mp this
    have hge : ψ e ≤ 1 := by
      have : ψ e ≤ ‖e⁺‖ := by simpa [ψ, N] using hφle e
      simpa [posPart_eq_self.mpr he0, amUnit_norm_eq_one he0 hball he] using this
    exact le_antisymm hge hone
  exact ⟨StrongDual.toWeakDual ψ, fun y hy => by simpa using hψpos y hy, by simpa using hψe,
    by simpa using hψx⟩

/-- Pointwise formula for a real convex combination in the weak-star dual. -/
theorem amWeakDual_combine (φ ψ : WeakDual ℝ E) (a b : ℝ) (x : E) :
    (a • φ + b • ψ) x = a * φ x + b * ψ x := by
  rw [← toStrongDual_apply (a • φ + b • ψ), LinearEquiv.map_add, LinearEquiv.map_smul,
    LinearEquiv.map_smul, IsAddApply.add_apply, IsSMulApply.smul_apply, IsSMulApply.smul_apply,
    smul_eq_mul, smul_eq_mul, toStrongDual_apply, toStrongDual_apply]

/-- Weak-star states normalized at the AM unit. -/
def amStateSet (e : E) : Set (WeakDual ℝ E) :=
  {φ | (∀ x, 0 ≤ x → 0 ≤ φ x) ∧ φ e = 1}

/-- The state space is weak-star closed. -/
theorem isClosed_amStateSet : IsClosed (amStateSet e) := by
  have hEq : IsClosed {φ : WeakDual ℝ E | φ e = 1} :=
    isClosed_eq (eval_continuous e) continuous_const
  have hPos : IsClosed {φ : WeakDual ℝ E | ∀ x, 0 ≤ x → 0 ≤ φ x} := by
    have hset : {φ : WeakDual ℝ E | ∀ x, 0 ≤ x → 0 ≤ φ x} =
        ⋂ x : {x : E // 0 ≤ x}, {φ | 0 ≤ φ x.1} := by
      ext φ
      simp [Subtype.forall]
    rw [hset]
    exact isClosed_iInter fun x => isClosed_le continuous_const (eval_continuous x.1)
  simpa [amStateSet, ofPred_and] using hPos.inter hEq

/-- The state space is convex. -/
theorem convex_amStateSet : Convex ℝ (amStateSet e) := by
  intro φ hφ ψ hψ a b ha hb hab
  refine ⟨fun x hx => ?_, ?_⟩
  · have hsum : 0 ≤ a * φ x + b * ψ x :=
      add_nonneg (mul_nonneg ha (hφ.1 x hx)) (mul_nonneg hb (hψ.1 x hx))
    rw [amWeakDual_combine]
    exact hsum
  · rw [amWeakDual_combine, hφ.2, hψ.2, mul_one, mul_one, hab]

include he0 hball in
/-- A nonzero AM unit admits a state. -/
theorem amStateSet_nonempty (he : e ≠ 0) : (amStateSet e).Nonempty := by
  obtain ⟨φ, hpos, heφ, -⟩ := exists_amState_norming he0 hball he he0 he
  exact ⟨φ, hpos, heφ⟩

include he0 hball in
/-- Every state has dual norm one. -/
theorem amState_opNorm_eq (he : e ≠ 0) {φ : WeakDual ℝ E} (hφ : φ ∈ amStateSet e) :
    ‖φ.toStrongDual‖ = 1 := by
  have hpos : ∀ x, 0 ≤ x → 0 ≤ φ.toStrongDual x := fun x hx => by simpa using hφ.1 x hx
  simpa [hφ.2] using amPositive_opNorm_eq he0 hball he φ.toStrongDual hpos

include he0 hball in
/-- The state space is weak-star compact. -/
theorem isCompact_amStateSet (he : e ≠ 0) : IsCompact (amStateSet e) := by
  have hsub : amStateSet e ⊆ toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) 1 := by
    intro φ hφ
    rw [mem_preimage, mem_closedBall_iff_norm]
    simpa using (amState_opNorm_eq he0 hball he hφ).le
  exact (isCompact_closedBall (0 : StrongDual ℝ E) 1).of_isClosed_subset
    isClosed_amStateSet hsub

/-- Vectors dominated by the test vector and by the argument. -/
def truncAdmissible (v y : E) : Set E :=
  {z | 0 ≤ z ∧ z ≤ y ∧ ∃ c : ℝ, 0 ≤ c ∧ z ≤ c • v}

/-- The truncated supremum of a scalar functional. -/
def truncSup (φ : E →ₗ[ℝ] ℝ) (v y : E) : ℝ :=
  sSup (φ '' truncAdmissible v y)

/-- Zero is an admissible truncation. -/
theorem zero_mem_truncAdmissible {v y : E} (hy : 0 ≤ y) : (0 : E) ∈ truncAdmissible v y :=
  ⟨le_rfl, hy, 0, le_rfl, by simp⟩

/-- Only zero is admissible under the zero vector. -/
theorem truncAdmissible_zero (v : E) : truncAdmissible v (0 : E) = {0} := by
  ext z
  constructor
  · rintro ⟨hz0, hzle, _⟩
    exact le_antisymm hzle hz0
  · rintro rfl
    exact ⟨le_rfl, le_rfl, 0, le_rfl, by simp⟩

/-- The truncated image is nonempty for a nonnegative argument. -/
theorem truncImage_nonempty (φ : E →ₗ[ℝ] ℝ) (v : E) {y : E} (hy : 0 ≤ y) :
    (φ '' truncAdmissible v y).Nonempty :=
  ⟨φ 0, 0, zero_mem_truncAdmissible hy, rfl⟩

/-- A monotone functional bounds the truncated image. -/
theorem truncImage_bddAbove {φ : E →ₗ[ℝ] ℝ} (hmono : Monotone φ) (v : E) {y : E} (_hy : 0 ≤ y) :
    BddAbove (φ '' truncAdmissible v y) :=
  ⟨φ y, by rintro _ ⟨z, ⟨_, hzle, _⟩, rfl⟩; exact hmono hzle⟩

/-- Truncated suprema are nonnegative. -/
theorem truncSup_nonneg {φ : E →ₗ[ℝ] ℝ} (hmono : Monotone φ) (v : E) {y : E} (hy : 0 ≤ y) :
    0 ≤ truncSup φ v y := by
  have h0 : (0 : ℝ) ∈ φ '' truncAdmissible v y := by
    rw [show (0 : ℝ) = φ 0 by simp]
    exact ⟨0, zero_mem_truncAdmissible hy, rfl⟩
  exact le_csSup (truncImage_bddAbove hmono v hy) h0

/-- A monotone functional dominates its truncated supremum. -/
theorem truncSup_le {φ : E →ₗ[ℝ] ℝ} (hmono : Monotone φ) (v : E) {y : E} (hy : 0 ≤ y) :
    truncSup φ v y ≤ φ y :=
  csSup_le (truncImage_nonempty φ v hy) (by
    rintro _ ⟨z, ⟨_, hzle, _⟩, rfl⟩
    exact hmono hzle)

/-- The test vector saturates its own truncated supremum. -/
theorem truncSup_self {φ : E →ₗ[ℝ] ℝ} (hmono : Monotone φ) {v : E} (hv : 0 ≤ v) :
    truncSup φ v v = φ v := by
  have hvmem : v ∈ truncAdmissible v v := ⟨hv, le_rfl, 1, by positivity, by simp⟩
  apply le_antisymm (truncSup_le hmono v hv)
  exact le_csSup (truncImage_bddAbove hmono v hv) ⟨v, hvmem, rfl⟩

/-- Admissible truncations add. -/
theorem add_mem_truncAdmissible {v y₁ y₂ z₁ z₂ : E}
    (hz₁ : z₁ ∈ truncAdmissible v y₁) (hz₂ : z₂ ∈ truncAdmissible v y₂) :
    z₁ + z₂ ∈ truncAdmissible v (y₁ + y₂) := by
  obtain ⟨h10, h1y, c₁, hc₁, h1c⟩ := hz₁
  obtain ⟨h20, h2y, c₂, hc₂, h2c⟩ := hz₂
  refine ⟨add_nonneg h10 h20, add_le_add h1y h2y, c₁ + c₂, add_nonneg hc₁ hc₂, ?_⟩
  calc
    z₁ + z₂ ≤ c₁ • v + c₂ • v := add_le_add h1c h2c
    _ = (c₁ + c₂) • v := by rw [add_smul]

/-- Real comparison by an arbitrary positive slack. -/
theorem le_of_forall_pos_le_add {a b : ℝ} (h : ∀ ε, 0 < ε → a ≤ b + ε) : a ≤ b := by
  contrapose! h
  refine ⟨(a - b) / 2, by linarith, ?_⟩
  linarith

/-- Truncated suprema are additive on the positive cone. -/
theorem truncSup_add {φ : E →ₗ[ℝ] ℝ} (hmono : Monotone φ) (v y₁ y₂ : E)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) :
    truncSup φ v (y₁ + y₂) = truncSup φ v y₁ + truncSup φ v y₂ := by
  have hb₁ := truncImage_bddAbove hmono v hy₁
  have hb₂ := truncImage_bddAbove hmono v hy₂
  have hb := truncImage_bddAbove hmono v (add_nonneg hy₁ hy₂)
  have hn₁ := truncImage_nonempty φ v hy₁
  have hn₂ := truncImage_nonempty φ v hy₂
  have hn := truncImage_nonempty φ v (add_nonneg hy₁ hy₂)
  apply le_antisymm
  · apply csSup_le hn
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hz0, hzle, c, hc, hzc⟩ := hz
    obtain ⟨z₁, z₂, hzsum, hz10, hz1y, hz20, hz2y⟩ :=
      exists_add_eq_of_le_add hz0 hy₁ hy₂ hzle
    have hz1le : z₁ ≤ z := by
      have := add_le_add_left hz20 z₁
      simpa [hzsum, add_zero] using this
    have hz2le : z₂ ≤ z := by
      have := add_le_add_right hz10 z₂
      simpa [hzsum, zero_add] using this
    have hz1mem : z₁ ∈ truncAdmissible v y₁ := ⟨hz10, hz1y, c, hc, hz1le.trans hzc⟩
    have hz2mem : z₂ ∈ truncAdmissible v y₂ := ⟨hz20, hz2y, c, hc, hz2le.trans hzc⟩
    calc
      φ z = φ z₁ + φ z₂ := by rw [← map_add, hzsum]
      _ ≤ truncSup φ v y₁ + truncSup φ v y₂ :=
        add_le_add (le_csSup hb₁ ⟨z₁, hz1mem, rfl⟩) (le_csSup hb₂ ⟨z₂, hz2mem, rfl⟩)
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨t₁, ht₁, ht₁lt⟩ :=
      exists_lt_of_lt_csSup hn₁ (by linarith : truncSup φ v y₁ - ε / 2 < truncSup φ v y₁)
    obtain ⟨t₂, ht₂, ht₂lt⟩ :=
      exists_lt_of_lt_csSup hn₂ (by linarith : truncSup φ v y₂ - ε / 2 < truncSup φ v y₂)
    obtain ⟨z₁, hz₁, rfl⟩ := ht₁
    obtain ⟨z₂, hz₂, rfl⟩ := ht₂
    have hzmem := add_mem_truncAdmissible hz₁ hz₂
    have hle : φ z₁ + φ z₂ ≤ truncSup φ v (y₁ + y₂) := by
      rw [← map_add]
      exact le_csSup hb ⟨z₁ + z₂, hzmem, rfl⟩
    linarith

/-- Truncated suprema are positively homogeneous. -/
theorem truncSup_smul {φ : E →ₗ[ℝ] ℝ} (hmono : Monotone φ) (v : E) {c : ℝ} (hc : 0 ≤ c)
    {y : E} (hy : 0 ≤ y) : truncSup φ v (c • y) = c * truncSup φ v y := by
  rcases eq_or_lt_of_le hc with rfl | hc
  · have himage : φ '' truncAdmissible v (0 : E) = {0} := by
      rw [truncAdmissible_zero, image_singleton, map_zero]
    simp [truncSup, zero_smul, himage]
  · have hby := truncImage_bddAbove hmono v hy
    have hbc := truncImage_bddAbove hmono v (smul_nonneg hc.le hy)
    have hny := truncImage_nonempty φ v hy
    have hnc := truncImage_nonempty φ v (smul_nonneg hc.le hy)
    apply le_antisymm
    · apply csSup_le hnc
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨hz0, hzle, d, hd, hzd⟩ := hz
      have hz' : c⁻¹ • z ∈ truncAdmissible v y := by
        refine ⟨smul_nonneg (inv_nonneg.mpr hc.le) hz0, ?_, d * c⁻¹,
          mul_nonneg hd (inv_nonneg.mpr hc.le), ?_⟩
        · have hmul := smul_le_smul_of_nonneg_left hzle (inv_nonneg.mpr hc.le)
          simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using hmul
        · have hmul := smul_le_smul_of_nonneg_left hzd (inv_nonneg.mpr hc.le)
          simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using hmul
      have hφz : φ z = c * φ (c⁻¹ • z) := by
        conv_lhs => rw [show z = c • (c⁻¹ • z) by
          rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]]
        rw [map_smul, smul_eq_mul]
      rw [hφz]
      exact mul_le_mul_of_nonneg_left (le_csSup hby ⟨c⁻¹ • z, hz', rfl⟩) hc.le
    · have hinv : truncSup φ v y ≤ c⁻¹ * truncSup φ v (c • y) := by
        apply csSup_le hny
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨hz0, hzle, d, hd, hzd⟩ := hz
        have hz' : c • z ∈ truncAdmissible v (c • y) := by
          refine ⟨smul_nonneg hc.le hz0, smul_le_smul_of_nonneg_left hzle hc.le, c * d,
            mul_nonneg hc.le hd, ?_⟩
          calc
            c • z ≤ c • (d • v) := smul_le_smul_of_nonneg_left hzd hc.le
            _ = (c * d) • v := by rw [smul_smul, mul_comm]
        have hle := le_csSup hbc ⟨c • z, hz', rfl⟩
        rw [map_smul, smul_eq_mul] at hle
        have hmul := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hc.le)
        rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at hmul
        exact hmul
      have hmul := mul_le_mul_of_nonneg_left hinv hc.le
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at hmul
      exact hmul

/-- A positive vector disjoint from every multiple of `v` has truncated supremum zero. -/
theorem truncSup_eq_zero_of_disjoint {φ : E →ₗ[ℝ] ℝ} (v y : E) (hy : 0 ≤ y)
    (hdis : ∀ c : ℝ, 0 ≤ c → (c • v) ⊓ y = 0) : truncSup φ v y = 0 := by
  have himage : φ '' truncAdmissible v y = {0} := by
    ext t
    constructor
    · rintro ⟨z, ⟨hz0, hzle, c, hc, hzc⟩, rfl⟩
      have hz : z = 0 := by
        have hle : z ≤ (c • v) ⊓ y := le_inf hzc hzle
        exact le_antisymm (hle.trans_eq (hdis c hc)) hz0
      simp [hz]
    · rintro rfl
      exact ⟨0, zero_mem_truncAdmissible hy, by simp⟩
  rw [truncSup, himage]
  exact csSup_singleton (0 : ℝ)

include he0 hball in
/-- Extreme states preserve lattice absolute values. -/
theorem amState_extreme_abs (he : e ≠ 0) {φ : WeakDual ℝ E}
    (hφ : φ ∈ (amStateSet e).extremePoints ℝ) (x : E) : φ |x| = |φ x| := by
  have hmem : φ ∈ amStateSet e := extremePoints_subset hφ
  let ψ := φ.toStrongDual
  have hposψ : ∀ y, 0 ≤ y → 0 ≤ ψ y := fun y hy => by simpa [ψ] using hmem.1 y hy
  have hmono : Monotone ψ.toLinearMap := monotone_of_map_nonneg fun y hy => by
    simpa using hposψ y hy
  let v : E := x⁻
  have hadd : ∀ a b : E, 0 ≤ a → 0 ≤ b →
      truncSup ψ.toLinearMap v (a + b) =
        truncSup ψ.toLinearMap v a + truncSup ψ.toLinearMap v b :=
    fun a b ha hb => truncSup_add hmono v a b ha hb
  have hsmul : ∀ (c : ℝ) (a : E), 0 ≤ c → 0 ≤ a →
      truncSup ψ.toLinearMap v (c • a) = c • truncSup ψ.toLinearMap v a :=
    fun c a hc ha => by simpa [smul_eq_mul] using truncSup_smul hmono v hc ha
  let Rlin := coneAdditiveLinearMap (fun y => truncSup ψ.toLinearMap v y) hadd hsmul
  have hRpos : ∀ y, 0 ≤ y → 0 ≤ Rlin y := by
    intro y hy
    rw [coneAdditiveLinearMap_apply_of_nonneg _ _ _ hy]
    exact truncSup_nonneg hmono v hy
  have hRle : ∀ y, 0 ≤ y → Rlin y ≤ ψ y := by
    intro y hy
    rw [coneAdditiveLinearMap_apply_of_nonneg _ _ _ hy]
    exact truncSup_le hmono v hy
  have hbound : ∀ y, ‖Rlin y‖ ≤ 1 * ‖y‖ := by
    intro y
    have hup : Rlin y⁺ ≤ ψ y⁺ := hRle _ (posPart_nonneg y)
    have hup' : Rlin y⁻ ≤ ψ y⁻ := hRle _ (negPart_nonneg y)
    have hRp : 0 ≤ Rlin y⁺ := hRpos _ (posPart_nonneg y)
    have hRn : 0 ≤ Rlin y⁻ := hRpos _ (negPart_nonneg y)
    have hsplit : Rlin y = Rlin y⁺ - Rlin y⁻ :=
      (congrArg Rlin (posPart_sub_negPart y).symm).trans (map_sub Rlin y⁺ y⁻)
    have hsum : Rlin y⁺ + Rlin y⁻ ≤ ψ |y| := by
      calc
        Rlin y⁺ + Rlin y⁻ ≤ ψ y⁺ + ψ y⁻ := add_le_add hup hup'
        _ = ψ |y| := by rw [← map_add, posPart_add_negPart]
    have habs : |Rlin y| ≤ ψ |y| := by
      rw [hsplit, abs_le]
      constructor <;> linarith
    have hop : ψ |y| ≤ ‖y‖ := by
      have hnorm : ‖ψ‖ = 1 := amState_opNorm_eq he0 hball he hmem
      have hle := ψ.le_opNorm |y|
      rw [hnorm, one_mul, norm_abs_eq_norm, Real.norm_eq_abs,
        abs_of_nonneg (hposψ _ (abs_nonneg y))] at hle
      exact hle
    have hfin : |Rlin y| ≤ ‖y‖ := habs.trans hop
    rw [← one_mul ‖y‖] at hfin
    rw [Real.norm_eq_abs]
    exact hfin
  let R : E →L[ℝ] ℝ := Rlin.mkContinuous 1 hbound
  have hRpos' : ∀ y, 0 ≤ y → 0 ≤ R y := by simpa [R] using hRpos
  have hRle' : ∀ y, 0 ≤ y → R y ≤ ψ y := by simpa [R] using hRle
  have hRxneg : R x⁻ = ψ x⁻ := by
    have hself : truncSup ψ.toLinearMap v v = ψ v := truncSup_self hmono (negPart_nonneg x)
    simpa [R, Rlin, v, coneAdditiveLinearMap_apply_of_nonneg _ _ _ (negPart_nonneg x)] using hself
  have hRxpos : R x⁺ = 0 := by
    have hdis : ∀ c : ℝ, 0 ≤ c → (c • x⁻) ⊓ x⁺ = 0 := fun c hc =>
      inf_smul_eq_zero hc (negPart_nonneg x) (posPart_nonneg x)
        (by simpa [inf_comm] using posPart_inf_negPart_eq_zero x)
    have hzero := truncSup_eq_zero_of_disjoint (φ := ψ.toLinearMap) x⁻ x⁺ (posPart_nonneg x) hdis
    simpa [R, Rlin, v, coneAdditiveLinearMap_apply_of_nonneg _ _ _ (posPart_nonneg x)] using hzero
  set α : ℝ := R e with hαdef
  have hα0 : 0 ≤ α := hRpos' e he0
  have hα1 : α ≤ 1 := by
    rw [hαdef, ← hmem.2]
    exact hRle' e he0
  have hprod : ψ x⁺ * ψ x⁻ = 0 := by
    rcases eq_or_lt_of_le hα0 with hα | hα
    · have hR0 : R = 0 := by
        have hnorm : ‖R‖ = R e := amPositive_opNorm_eq he0 hball he R hRpos'
        rw [← hαdef, ← hα] at hnorm
        exact norm_eq_zero.mp hnorm
      have : ψ x⁻ = 0 := by
        rw [hR0, IsZeroApply.zero_apply] at hRxneg
        exact hRxneg.symm
      rw [this, mul_zero]
    · rcases eq_or_lt_of_le hα1 with hαeq | hαlt
      · have hdiff : ‖ψ - R‖ = 0 := by
          have hposdiff : ∀ y, 0 ≤ y → 0 ≤ (ψ - R) y := fun y hy => by
            simp [sub_nonneg, hRle' y hy]
          have happ : (ψ - R) e = 0 := by
            rw [IsSubApply.sub_apply, show ψ e = φ e by simp [ψ], hmem.2, ← hαdef, hαeq,
              sub_self]
          simpa [happ] using amPositive_opNorm_eq he0 hball he (ψ - R) hposdiff
        have hψR : ψ = R := by
          have : ψ - R = 0 := norm_eq_zero.mp hdiff
          exact sub_eq_zero.mp this
        have : ψ x⁺ = 0 := by
          rw [hψR]
          exact hRxpos
        rw [this, zero_mul]
      · let g₁ : WeakDual ℝ E := StrongDual.toWeakDual (α⁻¹ • R)
        let g₂ : WeakDual ℝ E := StrongDual.toWeakDual ((1 - α)⁻¹ • (ψ - R))
        have hg₁ : g₁ ∈ amStateSet e := by
          refine ⟨fun y hy => ?_, ?_⟩
          · have : 0 ≤ α⁻¹ * R y := mul_nonneg (inv_nonneg.mpr hα.le) (hRpos' y hy)
            simpa only [g₁, IsSMulApply.smul_apply, smul_eq_mul,
              StrongDual.toWeakDual_apply] using this
          · simp only [g₁, IsSMulApply.smul_apply, smul_eq_mul, α,
              StrongDual.toWeakDual_apply, inv_mul_cancel₀ hα.ne']
        have hg₂ : g₂ ∈ amStateSet e := by
          refine ⟨fun y hy => ?_, ?_⟩
          · have hdiff : 0 ≤ ψ y - R y := sub_nonneg.mpr (hRle' y hy)
            have : 0 ≤ (1 - α)⁻¹ * (ψ y - R y) :=
              mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hαlt.le)) hdiff
            simpa only [g₂, IsSMulApply.smul_apply, IsSubApply.sub_apply, smul_eq_mul,
              StrongDual.toWeakDual_apply] using this
          · have hone : (ψ - R) e = 1 - α := by
              rw [IsSubApply.sub_apply, show ψ e = φ e by simp [ψ], hmem.2, ← hαdef]
            unfold g₂
            rw [StrongDual.toWeakDual_apply, IsSMulApply.smul_apply, smul_eq_mul, hone,
              inv_mul_cancel₀ (sub_ne_zero.mpr hαlt.ne.symm)]
        have hseg : φ ∈ openSegment ℝ g₁ g₂ := by
          refine ⟨α, 1 - α, hα, sub_pos.mpr hαlt, by ring, ?_⟩
          refine DFunLike.ext _ _ fun y => ?_
          rw [amWeakDual_combine]
          have h1 : g₁ y = α⁻¹ * R y := by
            unfold g₁
            rw [StrongDual.toWeakDual_apply, IsSMulApply.smul_apply, smul_eq_mul]
          have h2 : g₂ y = (1 - α)⁻¹ * (ψ y - R y) := by
            unfold g₂
            rw [StrongDual.toWeakDual_apply, IsSMulApply.smul_apply, IsSubApply.sub_apply,
              smul_eq_mul]
          rw [h1, h2, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hα.ne',
            mul_inv_cancel₀ (sub_ne_zero.mpr hαlt.ne.symm), one_mul, one_mul]
          have hcancel : R y + (ψ y - R y) = ψ y := by ring
          rw [hcancel]
          simp [ψ]
        have hg : g₁ = φ :=
          ((mem_extremePoints.mp hφ).2 g₁ hg₁ g₂ hg₂ hseg).1
        have hRφ : R = α • ψ := by
          apply ContinuousLinearMap.ext
          intro y
          have hy : g₁ y = φ y := congrArg (fun f => f y) hg
          unfold g₁ at hy
          rw [StrongDual.toWeakDual_apply, IsSMulApply.smul_apply, smul_eq_mul] at hy
          have hmul : R y = α * φ y := by
            have hmul' := congrArg (fun t : ℝ => α * t) hy
            rw [← mul_assoc, mul_inv_cancel₀ hα.ne', one_mul] at hmul'
            exact hmul'
          rw [IsSMulApply.smul_apply, smul_eq_mul, hmul]
          simp [ψ]
        have hscale : ψ x⁻ = α * ψ x⁻ := by
          have hRx := congrArg (fun f : E →L[ℝ] ℝ => f x⁻) hRφ
          rw [hRxneg, IsSMulApply.smul_apply, smul_eq_mul] at hRx
          exact hRx
        have : (1 - α) * ψ x⁻ = 0 := by
          rw [sub_mul, one_mul]
          exact sub_eq_zero.mpr hscale
        have : ψ x⁻ = 0 := (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hαlt.ne.symm)
        rw [this, mul_zero]
  have ha : 0 ≤ ψ x⁺ := hposψ _ (posPart_nonneg x)
  have hb : 0 ≤ ψ x⁻ := hposψ _ (negPart_nonneg x)
  have habs : |ψ x⁺ - ψ x⁻| = ψ x⁺ + ψ x⁻ := by
    rcases mul_eq_zero.mp hprod with h0 | h0
    · rw [h0, zero_sub, abs_neg, abs_of_nonneg hb, zero_add]
    · rw [h0, sub_zero, abs_of_nonneg ha, add_zero]
  calc
    φ |x| = ψ |x| := by simp [ψ]
    _ = ψ x⁺ + ψ x⁻ := by rw [← map_add, posPart_add_negPart]
    _ = |ψ x⁺ - ψ x⁻| := habs.symm
    _ = |ψ x| := by rw [← map_sub, posPart_sub_negPart]
    _ = |φ x| := by simp [ψ]

/-- Lattice homomorphisms normalized at the AM unit. -/
def amLatticeHomSet (e : E) : Set (WeakDual ℝ E) :=
  {φ | φ e = 1 ∧ ∀ x, φ |x| = |φ x|}

include he0 hball in
/-- Extreme states are normalized lattice homomorphisms. -/
theorem extremePoints_subset_amLatticeHomSet (he : e ≠ 0) :
    (amStateSet e).extremePoints ℝ ⊆ amLatticeHomSet e := by
  intro φ hφ
  exact ⟨(extremePoints_subset hφ).2, amState_extreme_abs he0 hball he hφ⟩

include he0 hball in
/-- The normalized lattice homomorphisms form a nonempty weak-star compact set. -/
theorem isCompact_amLatticeHomSet (he : e ≠ 0) : IsCompact (amLatticeHomSet e) := by
  have hsub : amLatticeHomSet e ⊆ toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) 1 := by
    intro φ hφ
    have hpos : ∀ x, 0 ≤ x → 0 ≤ φ x := by
      intro x hx
      have habs := hφ.2 x
      rw [abs_of_nonneg hx] at habs
      have hnn : 0 ≤ |φ x| := abs_nonneg (φ x)
      rw [← habs] at hnn
      exact hnn
    have hstate : φ ∈ amStateSet e := ⟨hpos, hφ.1⟩
    rw [mem_preimage, mem_closedBall_iff_norm]
    simpa using (amState_opNorm_eq he0 hball he hstate).le
  have hclosed : IsClosed (amLatticeHomSet e) := by
    have hEq : IsClosed {φ : WeakDual ℝ E | φ e = 1} :=
      isClosed_eq (eval_continuous e) continuous_const
    have hAbs : IsClosed {φ : WeakDual ℝ E | ∀ x, φ |x| = |φ x|} := by
      have hset : {φ : WeakDual ℝ E | ∀ x, φ |x| = |φ x|} =
          ⋂ x : E, {φ | φ |x| = |φ x|} := by
        ext φ
        simp
      rw [hset]
      refine isClosed_iInter fun x => ?_
      exact isClosed_eq ((eval_continuous |x|))
        ((continuous_abs).comp (eval_continuous x))
    simpa [amLatticeHomSet, ofPred_and] using hEq.inter hAbs
  exact (isCompact_closedBall (0 : StrongDual ℝ E) 1).of_isClosed_subset hclosed hsub

include he0 hball in
/-- A nonzero AM unit has a normalized lattice homomorphism. -/
theorem amLatticeHomSet_nonempty (he : e ≠ 0) : (amLatticeHomSet e).Nonempty := by
  obtain ⟨φ, hφ⟩ :=
    (isCompact_amStateSet he0 hball he).extremePoints_nonempty (amStateSet_nonempty he0 hball he)
  exact ⟨φ, extremePoints_subset_amLatticeHomSet he0 hball he hφ⟩

include he0 hball in
/-- Supremum of a continuous linear image is unchanged by passing to extreme points. -/
theorem csSup_extreme_eval (he : e ≠ 0) {y : E} :
    sSup ((fun φ : WeakDual ℝ E => φ y) '' (amStateSet e).extremePoints ℝ) =
      sSup ((fun φ : WeakDual ℝ E => φ y) '' amStateSet e) := by
  let s := amStateSet e
  let ext := s.extremePoints ℝ
  let f : WeakDual ℝ E → ℝ := fun φ => φ y
  have hscomp : IsCompact s := isCompact_amStateSet he0 hball he
  have hsconv : Convex ℝ s := convex_amStateSet
  have hsne : s.Nonempty := amStateSet_nonempty he0 hball he
  have hextne : ext.Nonempty := hscomp.extremePoints_nonempty hsne
  have hbext : BddAbove (f '' ext) := by
    obtain ⟨φ₀, hφ₀⟩ := hsne
    have hnorm : ‖φ₀.toStrongDual‖ = 1 := amState_opNorm_eq he0 hball he hφ₀
    refine ⟨‖y‖, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    have hstate : φ ∈ s := extremePoints_subset hφ
    have hop : ‖φ.toStrongDual‖ = 1 := amState_opNorm_eq he0 hball he hstate
    have hle := φ.toStrongDual.le_opNorm y
    rw [hop, one_mul, toStrongDual_apply] at hle
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hle)
  have hbs : BddAbove (f '' s) := by
    refine ⟨‖y‖, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    have hop : ‖φ.toStrongDual‖ = 1 := amState_opNorm_eq he0 hball he hφ
    have hle := φ.toStrongDual.le_opNorm y
    rw [hop, one_mul, toStrongDual_apply] at hle
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hle)
  have hle : sSup (f '' ext) ≤ sSup (f '' s) :=
    csSup_le_csSup hbs (hextne.image f) (image_mono extremePoints_subset)
  have hge : sSup (f '' s) ≤ sSup (f '' ext) := by
    let M : ℝ := sSup (f '' ext)
    have hlevel : ext ⊆ {φ | f φ ≤ M} := by
      intro φ hφ
      exact le_csSup hbext ⟨φ, hφ, rfl⟩
    have hclosed : IsClosed {φ : WeakDual ℝ E | f φ ≤ M} :=
      isClosed_le (eval_continuous y) continuous_const
    have hhull : convexHull ℝ ext ⊆ {φ | f φ ≤ M} := convexHull_min hlevel (by
      intro φ hφ ψ hψ a b ha hb hab
      have hcomb : f (a • φ + b • ψ) = a * f φ + b * f ψ := by
        change (a • φ + b • ψ) y = a * φ y + b * ψ y
        exact amWeakDual_combine φ ψ a b y
      have hle' : a * f φ + b * f ψ ≤ M := by
        calc
          a * f φ + b * f ψ ≤ a * M + b * M :=
            add_le_add (mul_le_mul_of_nonneg_left hφ ha) (mul_le_mul_of_nonneg_left hψ hb)
          _ = (a + b) * M := by rw [add_mul]
          _ = M := by rw [hab, one_mul]
      show f (a • φ + b • ψ) ≤ M
      rw [hcomb]
      exact hle')
    have hcl : closure (convexHull ℝ ext) ⊆ {φ | f φ ≤ M} :=
      closure_minimal hhull hclosed
    have hkm : closure (convexHull ℝ ext) = s :=
      closure_convexHull_extremePoints hscomp hsconv
    have hslevel : s ⊆ {φ | f φ ≤ M} := by simpa [hkm] using hcl
    apply csSup_le (hsne.image f)
    rintro _ ⟨φ, hφ, rfl⟩
    exact hslevel hφ
  exact le_antisymm hle hge

include he0 hball in
/-- Positive states recover the norm of a positive vector. -/
theorem csSup_amState_eval (he : e ≠ 0) {y : E} (hy : 0 ≤ y) :
    sSup ((fun φ : WeakDual ℝ E => φ y) '' amStateSet e) = ‖y‖ := by
  have hsne : (amStateSet e).Nonempty := amStateSet_nonempty he0 hball he
  have hb : BddAbove ((fun φ : WeakDual ℝ E => φ y) '' amStateSet e) := by
    refine ⟨‖y‖, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    have hop : ‖φ.toStrongDual‖ = 1 := amState_opNorm_eq he0 hball he hφ
    have hle := φ.toStrongDual.le_opNorm y
    rw [hop, one_mul, toStrongDual_apply] at hle
    calc
      φ y ≤ |φ y| := le_abs_self _
      _ ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using hle
  apply le_antisymm
  · apply csSup_le (hsne.image _)
    rintro _ ⟨φ, hφ, rfl⟩
    have hop : ‖φ.toStrongDual‖ = 1 := amState_opNorm_eq he0 hball he hφ
    have hle := φ.toStrongDual.le_opNorm y
    rw [hop, one_mul, toStrongDual_apply] at hle
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hle)
  · rcases eq_or_ne y 0 with rfl | hy0
    · have himage : (fun φ : WeakDual ℝ E => φ (0 : E)) '' amStateSet e = {0} := by
        ext t
        constructor
        · rintro ⟨φ, -, rfl⟩
          simp
        · rintro rfl
          obtain ⟨φ, hφ⟩ := hsne
          exact ⟨φ, hφ, by simp⟩
      rw [norm_zero, himage]
      exact (csSup_singleton (0 : ℝ)).ge
    · obtain ⟨φ, hpos, heφ, hyφ⟩ := exists_amState_norming he0 hball he hy hy0
      have hmem : φ ∈ amStateSet e := ⟨hpos, heφ⟩
      calc
        ‖y‖ = φ y := hyφ.symm
        _ ≤ sSup ((fun ψ : WeakDual ℝ E => ψ y) '' amStateSet e) :=
          le_csSup hb ⟨φ, hmem, rfl⟩

include he0 hball in
/-- Lattice homomorphisms recover the norm. -/
theorem csSup_amLatticeHom_abs (he : e ≠ 0) (x : E) :
    sSup ((fun φ : WeakDual ℝ E => |φ x|) '' amLatticeHomSet e) = ‖x‖ := by
  have hext : sSup ((fun φ : WeakDual ℝ E => φ |x|) '' (amStateSet e).extremePoints ℝ) = ‖x‖ := by
    rw [csSup_extreme_eval he0 hball he, csSup_amState_eval he0 hball he (abs_nonneg x),
      norm_abs_eq_norm]
  have hne : ((amStateSet e).extremePoints ℝ).Nonempty :=
    (isCompact_amStateSet he0 hball he).extremePoints_nonempty (amStateSet_nonempty he0 hball he)
  have hb : BddAbove ((fun φ : WeakDual ℝ E => |φ x|) '' amLatticeHomSet e) := by
    refine ⟨‖x‖, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    have hpos : ∀ y, 0 ≤ y → 0 ≤ φ y := by
      intro y hy
      have habs := hφ.2 y
      rw [abs_of_nonneg hy] at habs
      have hnn : 0 ≤ |φ y| := abs_nonneg (φ y)
      rw [← habs] at hnn
      exact hnn
    have hop : ‖φ.toStrongDual‖ = 1 :=
      amState_opNorm_eq he0 hball he ⟨hpos, hφ.1⟩
    have hle := φ.toStrongDual.le_opNorm x
    rw [hop, one_mul, toStrongDual_apply] at hle
    simpa [Real.norm_eq_abs] using hle
  have hle : sSup ((fun φ : WeakDual ℝ E => φ |x|) '' (amStateSet e).extremePoints ℝ) ≤
      sSup ((fun φ : WeakDual ℝ E => |φ x|) '' amLatticeHomSet e) := by
    apply csSup_le_csSup hb (hne.image _)
    intro t ht
    obtain ⟨φ, hφ, rfl⟩ := ht
    have hK : φ ∈ amLatticeHomSet e := extremePoints_subset_amLatticeHomSet he0 hball he hφ
    refine ⟨φ, hK, ?_⟩
    exact (hK.2 x).symm
  have hge : sSup ((fun φ : WeakDual ℝ E => |φ x|) '' amLatticeHomSet e) ≤ ‖x‖ :=
    csSup_le ((amLatticeHomSet_nonempty he0 hball he).image _) (by
      rintro _ ⟨φ, hφ, rfl⟩
      have hpos : ∀ y, 0 ≤ y → 0 ≤ φ y := by
        intro y hy
        have habs := hφ.2 y
        rw [abs_of_nonneg hy] at habs
        have hnn : 0 ≤ |φ y| := abs_nonneg (φ y)
        rw [← habs] at hnn
        exact hnn
      have hop : ‖φ.toStrongDual‖ = 1 := amState_opNorm_eq he0 hball he ⟨hpos, hφ.1⟩
      have hle' := φ.toStrongDual.le_opNorm x
      rw [hop, one_mul, toStrongDual_apply] at hle'
      simpa [Real.norm_eq_abs] using hle')
  exact le_antisymm hge (hext.symm.trans_le hle)

include he0 hball in
/-- **19.27**. An AM space with unit is lattice isometric to `C(K, ℝ)`. -/
theorem exists_am_representation [CompleteSpace E] :
    ∃ K : CompHaus.{u}, ∃ U : E ≃ₗᵢ[ℝ] C(K, ℝ),
      U e = 1 ∧ ∀ x y, U (x ⊔ y) = U x ⊔ U y := by
  by_cases he : e = 0
  · have _ : Subsingleton E := subsingleton_of_amUnit_eq_zero he0 hball he
    have hempty : amLatticeHomSet e = ∅ := by
      ext φ
      simp only [amLatticeHomSet, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hφ
      have hφe := hφ.1
      rw [he, map_zero] at hφe
      exact zero_ne_one hφe
    have hcomp : IsCompact (amLatticeHomSet e) := by simp [hempty]
    let : CompactSpace (↥(amLatticeHomSet e)) := isCompact_iff_compactSpace.mp hcomp
    let : T2Space (↥(amLatticeHomSet e)) := inferInstance
    let K : CompHaus.{u} := CompHaus.of (↥(amLatticeHomSet e))
    have hEmpty : IsEmpty K := by
      rw [show (K : Type u) = ↥(amLatticeHomSet e) from CompHausLike.coe_of _ _]
      rw [hempty]
      infer_instance
    have hsubC : Subsingleton C(K, ℝ) := ⟨fun f g => by ext x; exact hEmpty.elim x⟩
    let L : E →ₗᵢ[ℝ] C(K, ℝ) :=
      { toLinearMap := (0 : E →ₗ[ℝ] C(K, ℝ))
        norm_map' := fun x => by
          have hx : x = (0 : E) := Subsingleton.elim x 0
          rw [hx, LinearMap.zero_apply, norm_zero, norm_zero] }
    have hsurj : Function.Surjective L := fun f => ⟨0, hsubC.elim _ _⟩
    let U := LinearIsometryEquiv.ofSurjective L hsurj
    refine ⟨K, U, ?_, ?_⟩
    · exact hsubC.elim _ _
    · intro x y
      exact hsubC.elim _ _
  · have hcomp : IsCompact (amLatticeHomSet e) := isCompact_amLatticeHomSet he0 hball he
    let : CompactSpace (↥(amLatticeHomSet e)) := isCompact_iff_compactSpace.mp hcomp
    let : T2Space (↥(amLatticeHomSet e)) := inferInstance
    let K : CompHaus.{u} := CompHaus.of (↥(amLatticeHomSet e))
    let evalC : E → C(K, ℝ) := fun x =>
      ⟨fun φ => (φ : WeakDual ℝ E) x,
        (eval_continuous x).comp continuous_subtype_val⟩
    have heval_sup : ∀ x y, evalC (x ⊔ y) = evalC x ⊔ evalC y := by
      intro x y
      ext φ
      have habs : (φ : WeakDual ℝ E) |y - x| = |(φ : WeakDual ℝ E) (y - x)| :=
        φ.property.2 (y - x)
      have hleft : (φ : WeakDual ℝ E) (x ⊔ y) =
          (2⁻¹ : ℝ) * ((φ : WeakDual ℝ E) x + (φ : WeakDual ℝ E) y +
            |(φ : WeakDual ℝ E) y - (φ : WeakDual ℝ E) x|) := by
        rw [sup_eq_half_smul_add_add_abs_sub' ℝ x y, map_smul, map_add, map_add, smul_eq_mul,
          habs, map_sub]
      have hright : (φ : WeakDual ℝ E) x ⊔ (φ : WeakDual ℝ E) y =
          (2⁻¹ : ℝ) * ((φ : WeakDual ℝ E) x + (φ : WeakDual ℝ E) y +
            |(φ : WeakDual ℝ E) y - (φ : WeakDual ℝ E) x|) := by
        simpa [smul_eq_mul] using
          sup_eq_half_smul_add_add_abs_sub' ℝ ((φ : WeakDual ℝ E) x) ((φ : WeakDual ℝ E) y)
      change evalC (x ⊔ y) φ = (evalC x ⊔ evalC y) φ
      rw [ContinuousMap.sup_apply]
      simp [evalC, hleft, hright]
    have heval_inf : ∀ x y, evalC (x ⊓ y) = evalC x ⊓ evalC y := by
      intro x y
      have hneg : ∀ a b : E, evalC (-(a ⊔ b)) = -evalC (a ⊔ b) := by
        intro a b
        ext φ
        simp [evalC, map_neg]
      have hinfE : x ⊓ y = -(-x ⊔ -y) := by
        rw [← neg_neg (x ⊓ y), neg_inf]
      have hinfC : evalC x ⊓ evalC y = -(-evalC x ⊔ -evalC y) := by
        rw [← neg_neg (evalC x ⊓ evalC y), neg_inf]
      have hnegx : evalC (-x) = -evalC x := by
        ext φ
        simp [evalC, map_neg]
      have hnegy : evalC (-y) = -evalC y := by
        ext φ
        simp [evalC, map_neg]
      rw [hinfE, hneg (-x) (-y), heval_sup, hnegx, hnegy, ← hinfC]
    let L : E →ₗᵢ[ℝ] C(K, ℝ) :=
      { toLinearMap :=
          { toFun := evalC
            map_add' := fun x y => by ext φ; simp [evalC, map_add]
            map_smul' := fun c x => by ext φ; simp [evalC, map_smul, smul_eq_mul] }
        norm_map' := fun x => by
          rw [ContinuousMap.norm_eq_iSup_norm]
          have hne : Nonempty K := (amLatticeHomSet_nonempty he0 hball he).to_subtype
          have hsup : ⨆ φ : K, ‖evalC x φ‖ = ‖x‖ := by
            have hrange : range (fun φ : K => |((φ : WeakDual ℝ E) x)|) =
                (fun ψ : WeakDual ℝ E => |ψ x|) '' amLatticeHomSet e := by
              ext t
              constructor
              · rintro ⟨φ, rfl⟩
                exact ⟨φ, φ.property, rfl⟩
              · rintro ⟨ψ, hψ, rfl⟩
                exact ⟨⟨ψ, hψ⟩, rfl⟩
            rw [show ⨆ φ : K, ‖evalC x φ‖ =
                sSup (range fun φ : K => |((φ : WeakDual ℝ E) x)|) by
                  simp [evalC, Real.norm_eq_abs, iSup]]
            rw [hrange, csSup_amLatticeHom_abs he0 hball he x]
          exact hsup }
    have hsep : (range L).SeparatesPointsStrongly := by
      intro v φ ψ
      by_cases hφψ : φ = ψ
      · subst hφψ
        refine ⟨L ((v φ) • e), ⟨(v φ) • e, rfl⟩, ?_, ?_⟩
        · have : L ((v φ) • e) φ = v φ := by
            simp [L, evalC, map_smul, smul_eq_mul, φ.property.1]
          exact this
        · have : L ((v φ) • e) φ = v φ := by
            simp [L, evalC, map_smul, smul_eq_mul, φ.property.1]
          exact this
      · have hne : (φ : WeakDual ℝ E) ≠ ψ := by
          intro h
          exact hφψ (Subtype.ext h)
        obtain ⟨a, ha⟩ := DFunLike.exists_ne hne
        let δ : ℝ := (φ : WeakDual ℝ E) a - (ψ : WeakDual ℝ E) a
        have hδ : δ ≠ 0 := sub_ne_zero.mpr ha
        let q : ℝ := (v φ - v ψ) / δ
        let p : ℝ := v φ - q * (φ : WeakDual ℝ E) a
        refine ⟨L (p • e + q • a), ⟨p • e + q • a, rfl⟩, ?_, ?_⟩
        · simp [L, evalC, map_add, map_smul, smul_eq_mul, φ.property.1, p, q]
        · have hψ : L (p • e + q • a) ψ =
              p + q * (ψ : WeakDual ℝ E) a := by
            simp [L, evalC, map_add, map_smul, smul_eq_mul, ψ.property.1]
          rw [hψ]
          have hδ' : q * δ = v φ - v ψ := by
            simp [q, δ, div_mul_cancel₀ _ hδ]
          have : p + q * (ψ : WeakDual ℝ E) a = v φ - q * δ := by
            unfold p δ
            ring
          rw [this]
          linarith [hδ']
    have hclosed : IsClosed (range L) :=
      L.antilipschitzWith.isClosed_range L.lipschitzWith.uniformContinuous
    have htop : range L = univ := by
      have hcl := ContinuousMap.sublattice_closure_eq_top (range L) ⟨L 0, 0, rfl⟩
        (fun f hf g hg => by
          obtain ⟨x, rfl⟩ := hf
          obtain ⟨y, rfl⟩ := hg
          refine ⟨x ⊓ y, ?_⟩
          ext φ
          simp [L, evalC, heval_inf])
        (fun f hf g hg => by
          obtain ⟨x, rfl⟩ := hf
          obtain ⟨y, rfl⟩ := hg
          refine ⟨x ⊔ y, ?_⟩
          ext φ
          simp [L, evalC, heval_sup])
        hsep
      rw [IsClosed.closure_eq hclosed] at hcl
      simpa using hcl
    let U := LinearIsometryEquiv.ofSurjective L (range_eq_univ.mp htop)
    refine ⟨K, U, ?_, ?_⟩
    · ext φ
      simp [U, L, evalC, φ.property.1]
    · intro x y
      ext φ
      simp [U, L, evalC, heval_sup]

end CKMA
