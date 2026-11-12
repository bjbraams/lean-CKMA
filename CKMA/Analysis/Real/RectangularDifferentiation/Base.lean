/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.Basic

/-!
# One-dimensional weak type and the strong maximal kernel

Axis-parallel rectangles, the strong maximal operator, and the uncentered weak-type bound on
the line. The endpoint growth is `u(1+log⁺u)^(d-1)`, and the iteration kernel compares a
half-scaled growth of order `n` with the growth of order `n + 1`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- A bounded open axis-parallel box with positive side lengths. -/
structure OpenRectangle (d : ℕ) where
  /-- Lower coordinates. -/
  lower : Fin d → ℝ
  /-- Upper coordinates. -/
  upper : Fin d → ℝ
  /-- Every side has positive length. -/
  lower_lt_upper : ∀ j, lower j < upper j

/-- The underlying open set of a rectangle. -/
def OpenRectangle.carrier {d : ℕ} (R : OpenRectangle d) : Set (Fin d → ℝ) :=
  {x | ∀ j, R.lower j < x j ∧ x j < R.upper j}

/-- Sum of side lengths, an equivalent fixed-dimensional measure of shrinking rectangles. -/
def OpenRectangle.totalWidth {d : ℕ} (R : OpenRectangle d) : ℝ :=
  ∑ j, (R.upper j - R.lower j)

/-- Signed average on a rectangle; used when local integrability is assumed. -/
def OpenRectangle.average {d : ℕ} (R : OpenRectangle d) (f : (Fin d → ℝ) → ℝ) : ℝ :=
  (volume R.carrier).toReal⁻¹ * ∫ y in R.carrier, f y

/-- The positive strong maximal operator, retaining infinite local integrals. -/
def strongMaximalFunction {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ≥0∞ :=
  ⨆ (R : OpenRectangle d) (_hx : x ∈ R.carrier),
    (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) / volume R.carrier

/-- The endpoint Orlicz growth `u(1+log⁺u)^(d-1)` for nonnegative `u`. -/
def strongMaximalGrowth (d : ℕ) (u : ℝ) : ℝ :=
  u * (1 + max 0 (Real.log u)) ^ (d - 1)

/-- Local endpoint integrability, expressed on all compact subsets. -/
def IsLocallyLLog (d : ℕ) (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ K : Set (Fin d → ℝ), IsCompact K →
    IntegrableOn (fun x ↦ strongMaximalGrowth d |f x|) K

/-- All rectangles containing the point, with unrestricted eccentricity, recover its value. -/
def RectanglesDifferentiateAt {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ R : OpenRectangle d,
    x ∈ R.carrier → R.totalWidth < δ → |R.average f - f x| < ε

/-- An open bounded interval, the one-dimensional case of an open rectangle. -/
structure OpenInterval where
  /-- Left endpoint. -/
  left : ℝ
  /-- Right endpoint. -/
  right : ℝ
  /-- The interval is nonempty. -/
  left_lt_right : left < right

namespace OpenInterval

/-- The underlying open interval. -/
def carrier (I : OpenInterval) : Set ℝ := Ioo I.left I.right

/-- Euclidean length. -/
def length (I : OpenInterval) : ℝ := I.right - I.left

/-- The length is positive. -/
theorem length_pos (I : OpenInterval) : 0 < I.length := sub_pos.2 I.left_lt_right

/-- The carrier is nonempty. -/
theorem carrier_nonempty (I : OpenInterval) : I.carrier.Nonempty :=
  nonempty_Ioo.2 I.left_lt_right

end OpenInterval

/-- Extended average of a nonnegative function over an open interval. -/
def intervalAverage (g : ℝ → ℝ≥0∞) (I : OpenInterval) : ℝ≥0∞ :=
  (∫⁻ t in I.carrier, g t) / ENNReal.ofReal I.length

/-- The uncentered maximal function of a function with values in the extended nonnegative reals. -/
def oneDimMaximalENN (φ : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ I : OpenInterval, ⨆ (_ : x ∈ I.carrier), intervalAverage φ I

/-- The uncentered one-dimensional Hardy–Littlewood maximal function. -/
def oneDimMaximal (g : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  oneDimMaximalENN (fun t ↦ ENNReal.ofReal |g t|) x

/-- An open interval with rational endpoints. -/
structure RatInterval where
  /-- Left endpoint. -/
  left : ℚ
  /-- Right endpoint. -/
  right : ℚ
  /-- The endpoints are ordered. -/
  left_lt_right : left < right

namespace RatInterval

/-- The underlying open interval. -/
def carrier (I : RatInterval) : Set ℝ := Ioo (I.left : ℝ) (I.right : ℝ)

/-- Euclidean length. -/
def length (I : RatInterval) : ℝ := (I.right : ℝ) - (I.left : ℝ)

/-- The length is positive. -/
theorem length_pos (I : RatInterval) : 0 < I.length := by
  simpa [length] using (Rat.cast_lt (K := ℝ)).2 I.left_lt_right

/-- The carrier is a nonempty open interval. -/
theorem carrier_nonempty (I : RatInterval) : I.carrier.Nonempty :=
  nonempty_Ioo.2 (by exact_mod_cast I.left_lt_right)

/-- The rational-endpoint intervals are a countable family. -/
instance : Countable RatInterval :=
  Function.Injective.countable (f := fun I : RatInterval ↦ (I.left, I.right))
    (fun I J h ↦ by cases I; cases J; aesop)

/-- View a rational interval as an open interval. -/
def toOpen (I : RatInterval) : OpenInterval where
  left := I.left
  right := I.right
  left_lt_right := by exact_mod_cast I.left_lt_right

/-- The carrier agrees with the underlying open interval. -/
theorem carrier_toOpen (I : RatInterval) : I.toOpen.carrier = I.carrier := rfl

/-- Lengths agree after forgetting rationality of the endpoints. -/
theorem length_toOpen (I : RatInterval) : I.toOpen.length = I.length := rfl

end RatInterval

/-- Extended average over a rational-endpoint interval. -/
def ratIntervalAverage (g : ℝ → ℝ≥0∞) (I : RatInterval) : ℝ≥0∞ :=
  intervalAverage g I.toOpen

/-- The real enlargement of a rational interval by the factor `τ` on each side. -/
def ratEnlargement (τ : ℝ) (J : RatInterval) : Set ℝ :=
  Ioo ((J.left : ℝ) - τ * J.length) ((J.right : ℝ) + τ * J.length)

/-- Enlargement multiplies the length by `1 + 2τ`, as an identity of endpoints. -/
theorem volume_ratEnlargement (τ : ℝ) (J : RatInterval) :
    volume (ratEnlargement τ J) = ENNReal.ofReal ((1 + 2 * τ) * J.length) := by
  have hdiff :
      ((J.right : ℝ) + τ * J.length) - ((J.left : ℝ) - τ * J.length) =
        (1 + 2 * τ) * J.length := by
    simp only [RatInterval.length]
    ring
  rw [ratEnlargement, Real.volume_Ioo, hdiff]

/-- An interval that meets a comparable selected interval sits inside its enlargement. -/
theorem carrier_subset_ratEnlargement {τ : ℝ} {I J : RatInterval}
    (hcap : (I.carrier ∩ J.carrier).Nonempty) (hlen : I.length ≤ τ * J.length) :
    I.carrier ⊆ ratEnlargement τ J := by
  intro x hx
  rcases hcap with ⟨z, hzI, hzJ⟩
  have hx1 : (I.left : ℝ) < x := hx.1
  have hx2 : x < (I.right : ℝ) := hx.2
  have hzI1 : (I.left : ℝ) < z := hzI.1
  have hzI2 : z < (I.right : ℝ) := hzI.2
  have hzJ1 : (J.left : ℝ) < z := hzJ.1
  have hzJ2 : z < (J.right : ℝ) := hzJ.2
  have hLi : I.length = (I.right : ℝ) - (I.left : ℝ) := rfl
  have hLj : J.length = (J.right : ℝ) - (J.left : ℝ) := rfl
  refine ⟨?_, ?_⟩
  · have : (J.left : ℝ) - τ * J.length < x := by
      have hxz : z - I.length < x := by
        linarith
      have hz : (J.left : ℝ) - τ * J.length ≤ z - I.length := by
        linarith
      linarith
    exact this
  · have : x < (J.right : ℝ) + τ * J.length := by
      have hxz : x < z + I.length := by
        linarith
      have hz : z + I.length ≤ (J.right : ℝ) + τ * J.length := by
        linarith
      linarith
    exact this

/-- A strict interval average survives a small outward rational perturbation. -/
theorem exists_ratInterval_of_average_gt (g : ℝ → ℝ≥0∞)
    (hfin : ∫⁻ t, g t ≠ ∞) (I : OpenInterval) {α : ℝ} (hα : 0 < α)
    (havg : ENNReal.ofReal α < intervalAverage g I) :
    ∃ J : RatInterval, I.carrier ⊆ J.carrier ∧ ENNReal.ofReal α < ratIntervalAverage g J := by
  have hL : 0 < I.length := I.length_pos
  have hmul : ENNReal.ofReal α * ENNReal.ofReal I.length < ∫⁻ t in I.carrier, g t := by
    refine (ENNReal.lt_div_iff_mul_lt ?_ ?_).1 havg
    · exact Or.inl (ne_of_gt (ENNReal.ofReal_pos.2 hL))
    · exact Or.inl ENNReal.ofReal_ne_top
  have hI0 : ∫⁻ t in I.carrier, g t ≠ ∞ :=
    ne_of_lt <| (setLIntegral_le_lintegral _ _).trans_lt (lt_top_iff_ne_top.2 hfin)
  have hprod : ENNReal.ofReal (α * I.length) < ∫⁻ t in I.carrier, g t := by
    simpa [ENNReal.ofReal_mul hα.le] using hmul
  have hI0pos : 0 < ∫⁻ t in I.carrier, g t :=
    (ENNReal.ofReal_pos.2 (mul_pos hα hL)).trans hprod
  have hto : 0 < (∫⁻ t in I.carrier, g t).toReal :=
    ENNReal.toReal_pos hI0pos.ne' hI0
  have hroom : α * I.length < (∫⁻ t in I.carrier, g t).toReal := by
    rw [← ENNReal.ofReal_lt_ofReal_iff hto, ENNReal.ofReal_toReal hI0]
    exact hprod
  set room : ℝ := (∫⁻ t in I.carrier, g t).toReal - α * I.length
  have hroompos : 0 < room := sub_pos.2 hroom
  set δ : ℝ := room / (4 * α)
  have hδ : 0 < δ := div_pos hroompos (mul_pos (by norm_num : (0 : ℝ) < 4) hα)
  have hδavg : α * (I.length + 2 * δ) < (∫⁻ t in I.carrier, g t).toReal := by
    have hδeq : 2 * α * δ = room / 2 := by
      unfold δ
      field_simp [hα.ne']
      ring
    linarith [hδeq, hroompos]
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show I.left - δ < I.left by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show I.right < I.right + δ by linarith)
  have hpq : (p : ℝ) < (q : ℝ) := by linarith [I.left_lt_right]
  let J : RatInterval := ⟨p, q, by exact_mod_cast hpq⟩
  have hsub : I.carrier ⊆ J.carrier := by
    intro x hx
    exact ⟨lt_trans hp2 hx.1, lt_trans hx.2 hq1⟩
  have hlen : J.length < I.length + 2 * δ := by
    simp only [RatInterval.length, OpenInterval.length]
    linarith
  have hJpos : 0 < J.length := J.length_pos
  have hαlen : α * J.length < (∫⁻ t in I.carrier, g t).toReal := by
    nlinarith
  have hint : ∫⁻ t in I.carrier, g t ≤ ∫⁻ t in J.carrier, g t :=
    lintegral_mono_set hsub
  have hstrict : ENNReal.ofReal (α * J.length) < ∫⁻ t in J.carrier, g t := by
    refine lt_of_lt_of_le ?_ hint
    rw [← ENNReal.ofReal_toReal hI0]
    exact (ENNReal.ofReal_lt_ofReal_iff hto).2 hαlen
  have hdiv : ENNReal.ofReal α <
      (∫⁻ t in J.carrier, g t) / ENNReal.ofReal J.length := by
    refine (ENNReal.lt_div_iff_mul_lt ?_ ?_).2 ?_
    · exact Or.inl (ne_of_gt (ENNReal.ofReal_pos.2 hJpos))
    · exact Or.inl ENNReal.ofReal_ne_top
    simpa [ENNReal.ofReal_mul hα.le] using hstrict
  refine ⟨J, hsub, ?_⟩
  simpa [ratIntervalAverage, intervalAverage, RatInterval.carrier_toOpen,
    RatInterval.length_toOpen] using hdiv

/-- Constant in the one-dimensional uncentered weak-type bound proved below. -/
def oneDimWeakConstant : ℝ := 5

/-- The uncentered maximal function on `ℝ` is weak type `(1, 1)` with constant `5`. -/
theorem oneDimMaximalENN_weakType (φ : ℝ → ℝ≥0∞) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal α < oneDimMaximalENN φ x} ≤
      ENNReal.ofReal oneDimWeakConstant * (∫⁻ x, φ x) / ENNReal.ofReal α := by
  by_cases hfin : ∫⁻ t, φ t = ∞
  · have hposC : (0 : ℝ) < oneDimWeakConstant := by
      unfold oneDimWeakConstant
      norm_num
    rw [hfin, ENNReal.mul_top (ENNReal.ofReal_pos.2 hposC).ne',
      ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
    exact le_top
  let t : Set RatInterval := {I | ENNReal.ofReal α < ratIntervalAverage φ I}
  have hcover_rat : {x | ENNReal.ofReal α < oneDimMaximalENN φ x} ⊆ ⋃ I ∈ t, I.carrier := by
    intro x hx
    have hx' : ENNReal.ofReal α < oneDimMaximalENN φ x := by
      simpa only [Set.mem_ofPred_eq] using hx
    unfold oneDimMaximalENN at hx'
    rw [lt_iSup_iff] at hx'
    obtain ⟨I, hxI⟩ := hx'
    rw [lt_iSup_iff] at hxI
    obtain ⟨hxmem, havg⟩ := hxI
    obtain ⟨J, hsub, hJ⟩ := exists_ratInterval_of_average_gt φ hfin I hα havg
    exact mem_iUnion₂.2 ⟨J, hJ, hsub hxmem⟩
  have hlen_le : ∀ I ∈ t, I.length ≤ (∫⁻ s, φ s).toReal / α := by
    intro I hI
    have hmul : ENNReal.ofReal α * ENNReal.ofReal I.length < ∫⁻ s in I.carrier, φ s := by
      refine (ENNReal.lt_div_iff_mul_lt ?_ ?_).1 hI
      · exact Or.inl (ne_of_gt (ENNReal.ofReal_pos.2 I.length_pos))
      · exact Or.inl ENNReal.ofReal_ne_top
    have hint : ∫⁻ s in I.carrier, φ s ≤ ∫⁻ s, φ s := setLIntegral_le_lintegral _ _
    have hlt : ENNReal.ofReal (α * I.length) < ∫⁻ s, φ s := by
      refine lt_of_lt_of_le ?_ hint
      simpa [ENNReal.ofReal_mul hα.le] using hmul
    have htoPos : 0 < (∫⁻ s, φ s).toReal :=
      ENNReal.toReal_pos ((ENNReal.ofReal_pos.2 (mul_pos hα I.length_pos)).trans hlt).ne' hfin
    have hto : α * I.length < (∫⁻ s, φ s).toReal := by
      rw [← ENNReal.ofReal_lt_ofReal_iff htoPos, ENNReal.ofReal_toReal hfin]
      exact hlt
    have : I.length * α < (∫⁻ s, φ s).toReal := by
      simpa [mul_comm] using hto
    have : I.length < (∫⁻ s, φ s).toReal / α := by
      rwa [lt_div_iff₀ hα]
    exact this.le
  set Rbound : ℝ := (∫⁻ s, φ s).toReal / α
  obtain ⟨u, hut, hdisj, hsel⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun I : RatInterval ↦ I.carrier) t (fun I ↦ I.length) 2
      (by norm_num) (fun I _ ↦ I.length_pos.le) Rbound hlen_le
      (fun I _ ↦ I.carrier_nonempty)
  have hcount : u.Countable :=
    hdisj.countable_of_nonempty_interior fun I hI ↦ by
      change (interior (Ioo (I.left : ℝ) (I.right : ℝ))).Nonempty
      rw [isOpen_Ioo.interior_eq]
      exact nonempty_Ioo.2 (by exact_mod_cast I.left_lt_right)
  have hsub_enl : ⋃ I ∈ t, I.carrier ⊆ ⋃ J ∈ u, ratEnlargement 2 J := by
    intro x hx
    obtain ⟨I, hIt, hxI⟩ := mem_iUnion₂.1 hx
    obtain ⟨J, hJu, hcap, hlen⟩ := hsel I hIt
    exact mem_iUnion₂.2 ⟨J, hJu, carrier_subset_ratEnlargement hcap hlen hxI⟩
  have hvol : volume {x | ENNReal.ofReal α < oneDimMaximalENN φ x} ≤
      ∑' J : u, volume (ratEnlargement 2 (J : RatInterval)) := by
    refine le_trans (measure_mono (hcover_rat.trans hsub_enl)) ?_
    rw [Set.biUnion_eq_iUnion]
    exact measure_iUnion_le _
  have hvol_enl : ∀ J : u, volume (ratEnlargement 2 (J : RatInterval)) =
      ENNReal.ofReal (5 * (J : RatInterval).length) := by
    intro J
    simpa [oneDimWeakConstant, show (1 + 2 * (2 : ℝ)) * (J : RatInterval).length =
      5 * (J : RatInterval).length by ring] using
      volume_ratEnlargement 2 (J : RatInterval)
  have hsum_int : ∑' J : u, ∫⁻ s in (J : RatInterval).carrier, φ s ≤ ∫⁻ s, φ s := by
    have hm : ∀ I ∈ u, MeasurableSet I.carrier := fun _ _ ↦ measurableSet_Ioo
    rw [← lintegral_biUnion hcount hm hdisj φ]
    exact setLIntegral_le_lintegral _ _
  have hpiece : ∀ J : u, ENNReal.ofReal α * ENNReal.ofReal (J : RatInterval).length ≤
      ∫⁻ s in (J : RatInterval).carrier, φ s := by
    intro J
    have hJ : ENNReal.ofReal α < ratIntervalAverage φ (J : RatInterval) := hut J.2
    have hmul := (ENNReal.lt_div_iff_mul_lt
      (Or.inl (ne_of_gt (ENNReal.ofReal_pos.2 (J : RatInterval).length_pos)))
      (Or.inl ENNReal.ofReal_ne_top)).1 hJ
    exact hmul.le
  have hsum_len : ENNReal.ofReal α * ∑' J : u, ENNReal.ofReal (J : RatInterval).length ≤
      ∫⁻ s, φ s := by
    refine le_trans ?_ hsum_int
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun J ↦ hpiece J
  have hsum_len' : ∑' J : u, ENNReal.ofReal (J : RatInterval).length ≤
      (∫⁻ s, φ s) / ENNReal.ofReal α := by
    refine (ENNReal.le_div_iff_mul_le ?_ ?_).2 ?_
    · exact Or.inl (ne_of_gt (ENNReal.ofReal_pos.2 hα))
    · exact Or.inl ENNReal.ofReal_ne_top
    simpa [mul_comm] using hsum_len
  have hsum_enl : ∑' J : u, volume (ratEnlargement 2 (J : RatInterval)) ≤
      ENNReal.ofReal 5 * ((∫⁻ s, φ s) / ENNReal.ofReal α) := by
    calc
      ∑' J : u, volume (ratEnlargement 2 (J : RatInterval))
          = ∑' J : u, ENNReal.ofReal (5 * (J : RatInterval).length) := by
            simp_rw [hvol_enl]
      _ = ∑' J : u, ENNReal.ofReal 5 * ENNReal.ofReal (J : RatInterval).length := by
            congr 1
            ext J
            exact ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)
      _ = ENNReal.ofReal 5 * ∑' J : u, ENNReal.ofReal (J : RatInterval).length := by
            rw [ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal 5 * ((∫⁻ s, φ s) / ENNReal.ofReal α) := by
            gcongr
  have hconst : ENNReal.ofReal oneDimWeakConstant = ENNReal.ofReal 5 := by
    simp [oneDimWeakConstant]
  calc
    volume {x | ENNReal.ofReal α < oneDimMaximalENN φ x}
        ≤ ∑' J : u, volume (ratEnlargement 2 (J : RatInterval)) := hvol
    _ ≤ ENNReal.ofReal 5 * ((∫⁻ s, φ s) / ENNReal.ofReal α) := hsum_enl
    _ = (ENNReal.ofReal oneDimWeakConstant * ∫⁻ x, φ x) / ENNReal.ofReal α := by
        rw [hconst]
        simp only [div_eq_mul_inv, mul_assoc]

/-- The real uncentered maximal function is weak type `(1, 1)` with constant `5`. -/
theorem oneDimMaximal_weakType (g : ℝ → ℝ) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal α < oneDimMaximal g x} ≤
      ENNReal.ofReal oneDimWeakConstant * ∫⁻ x, ENNReal.ofReal (|g x| / α) := by
  have hmul := lintegral_const_mul' (μ := (volume : Measure ℝ)) (ENNReal.ofReal α)⁻¹
    (fun s ↦ ENNReal.ofReal |g s|)
    (ENNReal.inv_ne_top.2 (ne_of_gt (ENNReal.ofReal_pos.2 hα)))
  have hscale : (∫⁻ s, ENNReal.ofReal |g s|) / ENNReal.ofReal α =
      ∫⁻ s, ENNReal.ofReal (|g s| / α) := by
    calc
      (∫⁻ s, ENNReal.ofReal |g s|) / ENNReal.ofReal α =
          (∫⁻ s, ENNReal.ofReal |g s|) * (ENNReal.ofReal α)⁻¹ := by
        rw [div_eq_mul_inv]
      _ = (ENNReal.ofReal α)⁻¹ * ∫⁻ s, ENNReal.ofReal |g s| := by
        rw [mul_comm]
      _ = ∫⁻ s, (ENNReal.ofReal α)⁻¹ * ENNReal.ofReal |g s| := hmul.symm
      _ = ∫⁻ s, ENNReal.ofReal (|g s| / α) := by
        refine lintegral_congr fun s ↦ ?_
        rw [ENNReal.ofReal_div_of_pos hα, div_eq_mul_inv, mul_comm]
  have hEN := oneDimMaximalENN_weakType (fun t ↦ ENNReal.ofReal |g t|) hα
  have hRHS :
      (ENNReal.ofReal oneDimWeakConstant * ∫⁻ t, ENNReal.ofReal |g t|) / ENNReal.ofReal α =
        ENNReal.ofReal oneDimWeakConstant * ∫⁻ x, ENNReal.ofReal (|g x| / α) := by
    calc
      (ENNReal.ofReal oneDimWeakConstant * ∫⁻ t, ENNReal.ofReal |g t|) / ENNReal.ofReal α =
          ENNReal.ofReal oneDimWeakConstant *
            ((∫⁻ t, ENNReal.ofReal |g t|) / ENNReal.ofReal α) := by
        simp only [div_eq_mul_inv, mul_assoc]
      _ = ENNReal.ofReal oneDimWeakConstant * ∫⁻ x, ENNReal.ofReal (|g x| / α) := by
        rw [hscale]
  simpa [oneDimMaximal, hRHS] using hEN

/-- In dimension one the endpoint growth is the identity. -/
theorem strongMaximalGrowth_one (u : ℝ) : strongMaximalGrowth 1 u = u := by
  simp [strongMaximalGrowth]

/-- The endpoint growth dominates the identity on the nonnegative reals. -/
theorem strongMaximalGrowth_ge_self {d : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    u ≤ strongMaximalGrowth d u := by
  have hbase : (1 : ℝ) ≤ 1 + max 0 (Real.log u) := by
    linarith [le_max_left (0 : ℝ) (Real.log u)]
  exact le_mul_of_one_le_right hu (one_le_pow₀ hbase)

/-- The carrier of a rectangle is the product of its open sides. -/
theorem OpenRectangle.carrier_eq_pi {d : ℕ} (R : OpenRectangle d) :
    R.carrier = pi univ fun j ↦ Ioo (R.lower j) (R.upper j) := by
  ext x
  simp [OpenRectangle.carrier, mem_Ioo]

/-- The volume of a rectangle is the product of its side lengths. -/
theorem OpenRectangle.volume_carrier {d : ℕ} (R : OpenRectangle d) :
    volume R.carrier = ∏ j, ENNReal.ofReal (R.upper j - R.lower j) := by
  rw [R.carrier_eq_pi, Real.volume_pi_Ioo]

/-- On `Fin 1` the strong maximal function is the uncentered maximal function of the line. -/
theorem strongMaximalFunction_finOne (f : (Fin 1 → ℝ) → ℝ) (x : Fin 1 → ℝ) :
    strongMaximalFunction f x = oneDimMaximal (fun t ↦ f fun _ : Fin 1 ↦ t) (x 0) := by
  let g : ℝ → ℝ := fun t ↦ f fun _ : Fin 1 ↦ t
  let e := MeasurableEquiv.funUnique (Fin 1) ℝ
  have hev : MeasurePreserving e volume volume := volume_preserving_funUnique (Fin 1) ℝ
  have he0 : ∀ y : Fin 1 → ℝ, e y = y 0 := fun _ ↦ rfl
  have hconst : ∀ y : Fin 1 → ℝ, f y = g (y 0) := by
    intro y
    have hy : y = fun _ : Fin 1 ↦ y 0 := by
      ext i
      fin_cases i
      rfl
    rw [hy]
  have hcarrier : ∀ R : OpenRectangle 1,
      R.carrier = e ⁻¹' Ioo (R.lower 0) (R.upper 0) := by
    intro R
    ext y
    simp only [OpenRectangle.carrier, mem_preimage, mem_Ioo, he0]
    constructor
    · intro hy
      exact hy 0
    · intro hy j
      fin_cases j
      exact hy
  have hvol : ∀ R : OpenRectangle 1,
      volume R.carrier = ENNReal.ofReal (R.upper 0 - R.lower 0) := by
    intro R
    rw [hcarrier R, hev.measure_preimage_equiv, Real.volume_Ioo]
  have hint : ∀ R : OpenRectangle 1,
      (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) =
        ∫⁻ t in Ioo (R.lower 0) (R.upper 0), ENNReal.ofReal |g t| := by
    intro R
    let s : Set ℝ := Ioo (R.lower 0) (R.upper 0)
    have hs : MeasurableSet s := measurableSet_Ioo
    have hspre : MeasurableSet (e ⁻¹' s) := hs.preimage e.measurable
    simp_rw [show ∀ y, ENNReal.ofReal |f y| = ENNReal.ofReal |g (e y)| by
      intro y; rw [hconst y, he0 y], hcarrier R]
    rw [← lintegral_indicator hspre]
    have hcomp := hev.lintegral_comp_emb e.measurableEmbedding
      (s.indicator fun t ↦ ENNReal.ofReal |g t|)
    rw [lintegral_indicator hs] at hcomp
    rw [← hcomp]
    congr 1
  apply le_antisymm
  · refine iSup_le fun R ↦ iSup_le fun hxR ↦ ?_
    let I : OpenInterval := ⟨R.lower 0, R.upper 0, R.lower_lt_upper 0⟩
    have hxI : x 0 ∈ I.carrier := by
      rw [OpenInterval.carrier, mem_Ioo]
      exact hxR 0
    have havg : (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) / volume R.carrier =
        intervalAverage (fun t ↦ ENNReal.ofReal |g t|) I := by
      simp only [intervalAverage, OpenInterval.carrier, OpenInterval.length]
      rw [hint R, hvol R]
    rw [havg]
    exact (le_iSup (fun h : x 0 ∈ I.carrier ↦
      intervalAverage (fun t ↦ ENNReal.ofReal |g t|) I) hxI).trans
      (le_iSup (fun J : OpenInterval ↦ ⨆ h : x 0 ∈ J.carrier,
        intervalAverage (fun t ↦ ENNReal.ofReal |g t|) J) I)
  · refine iSup_le fun I ↦ iSup_le fun hxI ↦ ?_
    let R : OpenRectangle 1 := ⟨fun _ ↦ I.left, fun _ ↦ I.right, fun _ ↦ I.left_lt_right⟩
    have hxR : x ∈ R.carrier := by
      intro j
      fin_cases j
      rw [OpenInterval.carrier, mem_Ioo] at hxI
      exact hxI
    have havg : intervalAverage (fun t ↦ ENNReal.ofReal |g t|) I =
        (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) / volume R.carrier := by
      simp only [intervalAverage, OpenInterval.carrier, OpenInterval.length]
      rw [hint R, hvol R]
    rw [havg]
    exact (le_iSup (fun h : x ∈ R.carrier ↦
      (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) / volume R.carrier) hxR).trans
      (le_iSup (fun S : OpenRectangle 1 ↦ ⨆ h : x ∈ S.carrier,
        (∫⁻ y in S.carrier, ENNReal.ofReal |f y|) / volume S.carrier) R)

/-- The strong maximal operator on a line is weak type `(1, 1)`. -/
theorem strongMaximal_weakType_one (f : (Fin 1 → ℝ) → ℝ) {a : ℝ} (ha : 0 < a) :
    volume {x | ENNReal.ofReal a < strongMaximalFunction f x} ≤
      ENNReal.ofReal oneDimWeakConstant *
        ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth 1 (|f x| / a)) := by
  let g : ℝ → ℝ := fun t ↦ f fun _ : Fin 1 ↦ t
  let e := MeasurableEquiv.funUnique (Fin 1) ℝ
  have hev : MeasurePreserving e volume volume := volume_preserving_funUnique (Fin 1) ℝ
  have he0 : ∀ y : Fin 1 → ℝ, e y = y 0 := fun _ ↦ rfl
  have hset : {x | ENNReal.ofReal a < strongMaximalFunction f x} =
      e ⁻¹' {t | ENNReal.ofReal a < oneDimMaximal g t} := by
    ext x
    simp [strongMaximalFunction_finOne, he0, g]
  have hint : ∫⁻ x, ENNReal.ofReal (|f x| / a) = ∫⁻ t, ENNReal.ofReal (|g t| / a) := by
    have hpt : ∀ x, ENNReal.ofReal (|f x| / a) = ENNReal.ofReal (|g (e x)| / a) := by
      intro x
      have hx : f x = g (x 0) := by
        have : x = fun _ : Fin 1 ↦ x 0 := by
          ext i
          fin_cases i
          rfl
        rw [this]
      rw [hx, he0 x]
    simp_rw [hpt]
    exact hev.lintegral_comp_emb e.measurableEmbedding fun t ↦ ENNReal.ofReal (|g t| / a)
  rw [hset, hev.measure_preimage_equiv]
  simp_rw [strongMaximalGrowth_one]
  rw [hint]
  exact oneDimMaximal_weakType g ha

/-- The coefficient produced by comparing `log(4u)` with `(1 + log 4)(1 + log⁺ u)`. -/
def strongMaximalIterationFactor (n : ℕ) : ℝ := 2 * (1 + Real.log 4) ^ n

/-- The iteration factor is positive. -/
theorem strongMaximalIterationFactor_pos (n : ℕ) : 0 < strongMaximalIterationFactor n := by
  unfold strongMaximalIterationFactor
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  positivity

/-- A layer-cake bracket of order `k` is bounded by the next power of `1 + log⁺`. -/
theorem strongMaximalGrowth_bracket {k : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    (1 + max 0 (Real.log (2 * u))) ^ k +
      (if 2 * u ≤ (1 / 2 : ℝ) then (0 : ℝ) else
        ∫ s in (1 / 2 : ℝ)..(2 * u), (2 / s) *
          (1 + max 0 (Real.log (2 * u / s))) ^ k) ≤
      strongMaximalIterationFactor (k + 1) * (1 + max 0 (Real.log u)) ^ (k + 1) := by
  have hfactor : (1 : ℝ) ≤ 1 + Real.log 4 := by
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 4)]
  by_cases hsmall : 2 * u ≤ (1 / 2 : ℝ)
  · have hlog : Real.log (2 * u) ≤ 0 := by
      by_cases hu0 : u = 0
      · simp [hu0, Real.log_zero]
      · have hpos : 0 < 2 * u := by
          apply mul_pos (by norm_num : (0 : ℝ) < 2) (lt_of_le_of_ne hu (Ne.symm hu0))
        have hle : 2 * u ≤ 1 := le_trans hsmall (by norm_num)
        exact Real.log_nonpos hpos.le hle
    simp only [hsmall, ite_true, add_zero, max_eq_left hlog, one_pow]
    have hpow : (1 : ℝ) ≤ (1 + Real.log 4) ^ (k + 1) := one_le_pow₀ hfactor
    have hlogu : (1 : ℝ) ≤ 1 + max 0 (Real.log u) := by
      linarith [le_max_left (0 : ℝ) (Real.log u)]
    have hpowu : (1 : ℝ) ≤ (1 + max 0 (Real.log u)) ^ (k + 1) := one_le_pow₀ hlogu
    unfold strongMaximalIterationFactor
    nlinarith [mul_le_mul hpow hpowu (by norm_num : (0 : ℝ) ≤ 1) (by positivity :
      0 ≤ (1 + Real.log 4) ^ (k + 1))]
  · have hle : (1 / 2 : ℝ) ≤ 2 * u := le_of_not_ge hsmall
    have hu4 : (1 / 4 : ℝ) < u := by
      have : (1 / 2 : ℝ) < 2 * u := lt_of_not_ge hsmall
      linarith
    have hu0 : 0 < u := lt_trans (by norm_num : (0 : ℝ) < 1 / 4) hu4
    have h4u : 1 < 4 * u := by linarith
    have hlog4u : 0 < Real.log (4 * u) := Real.log_pos h4u
    have hbase : 0 ≤ 1 + Real.log (4 * u) := by linarith
    have hpoint : ∀ s ∈ Set.Icc (1 / 2 : ℝ) (2 * u),
        (2 / s) * (1 + max 0 (Real.log (2 * u / s))) ^ k ≤
          (1 + Real.log (4 * u)) ^ k * (2 / s) := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hs.1
      have hratio_pos : 0 < 2 * u / s := div_pos (mul_pos (by norm_num) hu0) hs0
      have hratio_le : 2 * u / s ≤ 4 * u := by
        rw [div_le_iff₀ hs0]
        nlinarith [hs.1]
      have hlogle : max 0 (Real.log (2 * u / s)) ≤ Real.log (4 * u) := by
        by_cases h1 : 2 * u / s ≤ 1
        · exact le_trans (max_eq_left (Real.log_nonpos hratio_pos.le h1)).le hlog4u.le
        · rw [max_eq_right (Real.log_nonneg (le_of_not_ge h1))]
          exact (Real.log_le_log_iff hratio_pos (mul_pos (by norm_num) hu0)).2 hratio_le
      have hpowle : (1 + max 0 (Real.log (2 * u / s))) ^ k ≤
          (1 + Real.log (4 * u)) ^ k :=
        pow_le_pow_left₀ (by linarith [le_max_left 0 (Real.log (2 * u / s))])
          (by linarith) k
      have hcoef : 0 ≤ 2 / s := div_nonneg (by norm_num) hs0.le
      calc
        (2 / s) * (1 + max 0 (Real.log (2 * u / s))) ^ k ≤
            (2 / s) * (1 + Real.log (4 * u)) ^ k := by gcongr
        _ = (1 + Real.log (4 * u)) ^ k * (2 / s) := by ring
    have hpos_s : ∀ s ∈ Set.Icc (1 / 2 : ℝ) (2 * u), 0 < s := fun s hs ↦
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hs.1
    have hint_left : IntervalIntegrable
        (fun s ↦ (2 / s) * (1 + max 0 (Real.log (2 * u / s))) ^ k) volume (1 / 2) (2 * u) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hle]
      have hquot : ContinuousOn (fun s : ℝ ↦ 2 * u / s) (Set.Icc (1 / 2) (2 * u)) := by
        apply ContinuousOn.div continuousOn_const continuousOn_id
        intro s hs
        exact (hpos_s s hs).ne'
      have hlogc : ContinuousOn (fun s : ℝ ↦ Real.log (2 * u / s)) (Set.Icc (1 / 2) (2 * u)) :=
        Real.continuousOn_log.comp hquot fun s hs ↦
          (div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hu0) (hpos_s s hs)).ne'
      have hmax : ContinuousOn (fun s : ℝ ↦ max 0 (Real.log (2 * u / s)))
          (Set.Icc (1 / 2) (2 * u)) :=
        continuous_max.continuousOn.comp (ContinuousOn.prodMk continuousOn_const hlogc)
          fun _ _ ↦ Set.mem_univ _
      exact ContinuousOn.mul
        (ContinuousOn.div continuousOn_const continuousOn_id fun s hs ↦ (hpos_s s hs).ne')
        (ContinuousOn.pow (ContinuousOn.add continuousOn_const hmax) k)
    have hint_right : IntervalIntegrable (fun s ↦ (1 + Real.log (4 * u)) ^ k * (2 / s))
        volume (1 / 2) (2 * u) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hle]
      exact ContinuousOn.mul continuousOn_const
        (ContinuousOn.div continuousOn_const continuousOn_id fun s hs ↦ (hpos_s s hs).ne')
    have hint : (∫ s in (1 / 2 : ℝ)..(2 * u), (2 / s) *
          (1 + max 0 (Real.log (2 * u / s))) ^ k) ≤
        (1 + Real.log (4 * u)) ^ k * (∫ s in (1 / 2 : ℝ)..(2 * u), 2 / s) := by
      have hmono := intervalIntegral.integral_mono_on hle hint_left hint_right hpoint
      have hpull : (∫ s in (1 / 2 : ℝ)..(2 * u),
          (1 + Real.log (4 * u)) ^ k * (2 / s)) =
          (1 + Real.log (4 * u)) ^ k * ∫ s in (1 / 2 : ℝ)..(2 * u), 2 / s := by
        exact intervalIntegral.integral_const_mul ((1 + Real.log (4 * u)) ^ k)
          (fun s ↦ 2 / s)
      exact hmono.trans_eq hpull
    have hinv : (∫ s in (1 / 2 : ℝ)..(2 * u), 2 / s) = 2 * Real.log (4 * u) := by
      have hdiv : (∫ s in (1 / 2 : ℝ)..(2 * u), 2 / s) =
          2 * ∫ s in (1 / 2 : ℝ)..(2 * u), s⁻¹ := by
        simp_rw [div_eq_mul_inv]
        exact intervalIntegral.integral_const_mul (2 : ℝ) (fun s ↦ s⁻¹)
      rw [hdiv, integral_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
        (by linarith : 0 < 2 * u), show (2 * u) / (1 / 2 : ℝ) = 4 * u by ring]
    have hlog2 : max 0 (Real.log (2 * u)) ≤ Real.log (4 * u) := by
      by_cases h1 : 2 * u ≤ 1
      · exact le_trans (max_eq_left (Real.log_nonpos (mul_pos (by norm_num) hu0).le h1)).le
          hlog4u.le
      · rw [max_eq_right (Real.log_nonneg (le_of_not_ge h1))]
        exact (Real.log_le_log_iff (mul_pos (by norm_num) hu0) (mul_pos (by norm_num) hu0)).2
          (by linarith)
    have hfirst : (1 + max 0 (Real.log (2 * u))) ^ k ≤ (1 + Real.log (4 * u)) ^ k :=
      pow_le_pow_left₀ (by linarith [le_max_left 0 (Real.log (2 * u))]) (by linarith) k
    have hsum : (1 + max 0 (Real.log (2 * u))) ^ k +
        ∫ s in (1 / 2 : ℝ)..(2 * u), (2 / s) *
          (1 + max 0 (Real.log (2 * u / s))) ^ k ≤
        2 * (1 + Real.log (4 * u)) ^ (k + 1) := by
      have hinter := hint.trans <| by
        rw [hinv]
      calc
        _ ≤ (1 + Real.log (4 * u)) ^ k + (1 + Real.log (4 * u)) ^ k * (2 * Real.log (4 * u)) := by
          gcongr
        _ = (1 + Real.log (4 * u)) ^ k * (1 + 2 * Real.log (4 * u)) := by ring
        _ ≤ (1 + Real.log (4 * u)) ^ k * (2 * (1 + Real.log (4 * u))) := by
          gcongr
          linarith
        _ = 2 * (1 + Real.log (4 * u)) ^ (k + 1) := by ring
    have hcompare : 1 + Real.log (4 * u) ≤
        (1 + Real.log 4) * (1 + max 0 (Real.log u)) := by
      by_cases hu1 : 1 ≤ u
      · have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu1
        rw [max_eq_right hlogu, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hu0.ne']
        nlinarith [mul_nonneg (Real.log_pos (by norm_num : (1 : ℝ) < 4)).le hlogu]
      · have hlogu : Real.log u ≤ 0 := Real.log_nonpos hu0.le (le_of_not_ge hu1)
        have h4le : 4 * u ≤ 4 := by linarith
        have hlogle : Real.log (4 * u) ≤ Real.log 4 :=
          (Real.log_le_log_iff (mul_pos (by norm_num) hu0) (by norm_num)).2 h4le
        simp only [max_eq_left hlogu, add_zero, mul_one]
        linarith
    have hpow : (1 + Real.log (4 * u)) ^ (k + 1) ≤
        ((1 + Real.log 4) * (1 + max 0 (Real.log u))) ^ (k + 1) :=
      pow_le_pow_left₀ hbase hcompare (k + 1)
    simp only [show ¬ 2 * u ≤ (1 / 2 : ℝ) from hsmall, ite_false]
    unfold strongMaximalIterationFactor
    calc
      (1 + max 0 (Real.log (2 * u))) ^ k +
          ∫ s in (1 / 2 : ℝ)..(2 * u), (2 / s) *
            (1 + max 0 (Real.log (2 * u / s))) ^ k ≤
          2 * (1 + Real.log (4 * u)) ^ (k + 1) := hsum
      _ ≤ 2 * ((1 + Real.log 4) * (1 + max 0 (Real.log u))) ^ (k + 1) := by gcongr
      _ = 2 * ((1 + Real.log 4) ^ (k + 1) *
          (1 + max 0 (Real.log u)) ^ (k + 1)) := by
        rw [mul_pow]
      _ = 2 * (1 + Real.log 4) ^ (k + 1) *
          (1 + max 0 (Real.log u)) ^ (k + 1) := by ring

/-- Half a scaled growth plus its logarithmic integral is the next Orlicz growth. -/
theorem strongMaximalGrowth_scaled_kernel {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 ≤ u) :
    (1 / 2) * strongMaximalGrowth n (2 * u) +
      (if u ≤ (1 / 4 : ℝ) then (0 : ℝ) else
        ∫ s in (1 / 2 : ℝ)..(2 * u), strongMaximalGrowth n (2 * u / s)) ≤
      strongMaximalIterationFactor n * strongMaximalGrowth (n + 1) u := by
  have hk : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hbracket := strongMaximalGrowth_bracket (k := n - 1) hu
  simp only [strongMaximalGrowth, hk, Nat.add_sub_cancel] at hbracket ⊢
  by_cases hsmall : u ≤ (1 / 4 : ℝ)
  · have h2 : 2 * u ≤ (1 / 2 : ℝ) := by linarith
    simp only [hsmall, h2, ite_true, add_zero] at hbracket ⊢
    have hlog : Real.log (2 * u) ≤ 0 := by
      by_cases hu0 : u = 0
      · simp [hu0, Real.log_zero]
      · exact Real.log_nonpos (mul_pos (by norm_num) (lt_of_le_of_ne hu (Ne.symm hu0))).le
          (le_trans h2 (by norm_num))
    simp only [max_eq_left hlog, add_zero, one_pow, mul_one] at hbracket ⊢
    have hmul := mul_le_mul_of_nonneg_left hbracket hu
    have hhalf : (1 / 2) * (2 * u) = u := by ring
    rw [hhalf]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  · have h2 : ¬ 2 * u ≤ (1 / 2 : ℝ) := by
      intro h
      exact hsmall (by linarith)
    simp only [hsmall, h2, ite_false] at hbracket ⊢
    have hu0 : 0 < u := lt_of_not_ge (by
      intro hu0
      exact hsmall (le_trans hu0 (by norm_num)))
    have hpull : (∫ s in (1 / 2 : ℝ)..(2 * u),
        (2 * u / s) * (1 + max 0 (Real.log (2 * u / s))) ^ (n - 1)) =
        u * ∫ s in (1 / 2 : ℝ)..(2 * u),
          (2 / s) * (1 + max 0 (Real.log (2 * u / s))) ^ (n - 1) := by
      have hfun : ∀ s, (2 * u / s) * (1 + max 0 (Real.log (2 * u / s))) ^ (n - 1) =
          u * ((2 / s) * (1 + max 0 (Real.log (2 * u / s))) ^ (n - 1)) := by
        intro s
        ring
      simp_rw [hfun]
      exact intervalIntegral.integral_const_mul u
        (fun s ↦ (2 / s) * (1 + max 0 (Real.log (2 * u / s))) ^ (n - 1))
    have hhalf : (1 / 2) * ((2 * u) * (1 + max 0 (Real.log (2 * u))) ^ (n - 1)) =
        u * (1 + max 0 (Real.log (2 * u))) ^ (n - 1) := by ring
    rw [hhalf, hpull]
    calc
      u * (1 + max 0 (Real.log (2 * u))) ^ (n - 1) +
          u * ∫ s in (1 / 2 : ℝ)..(2 * u),
            (2 / s) * (1 + max 0 (Real.log (2 * u / s))) ^ (n - 1) =
          u * ((1 + max 0 (Real.log (2 * u))) ^ (n - 1) +
            ∫ s in (1 / 2 : ℝ)..(2 * u),
              (2 / s) * (1 + max 0 (Real.log (2 * u / s))) ^ (n - 1)) := by ring
      _ ≤ u * (strongMaximalIterationFactor n *
          (1 + max 0 (Real.log u)) ^ n) := by
        exact mul_le_mul_of_nonneg_left hbracket hu
      _ = strongMaximalIterationFactor n *
          (u * (1 + max 0 (Real.log u)) ^ n) := by ring

end CKMA
