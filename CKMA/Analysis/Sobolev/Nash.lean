/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.TemperedDistribution
public import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Nash inequality

Nash's inequality on L¹∩H¹ with an actual weak derivative. The argument compares the integral
Fourier transform with the `L²` transform (`MeasureTheory.Lp.fourier_toTemperedDistribution_eq`,
`MeasureTheory.Lp.ae_eq_of_toTemperedDistribution_apply_eq`, `MeasureTheory.Lp.norm_fourier_eq`,
`Real.norm_fourier_le_integral_norm`), reads weak derivatives through
`TauCeti.hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_ofReal_eq`, and uses
`TemperedDistribution.fourier_lineDerivOp_eq` together with `EuclideanSpace.volume_ball`.
Source: GAPS 14.40. The critical unboundedness statement is in `CKMA.Analysis.Sobolev.Critical`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory FourierTransform TemperedDistribution SchwartzMap TopologicalSpace
open scoped ENNReal FourierTransform SchwartzMap LineDeriv RealInnerProductSpace

/-- Volume of the Euclidean unit ball in dimension `d`. -/
private def nashVolumeFactor (d : ℕ) : ℝ :=
  Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1)

/-- The unit-ball volume is positive in every positive dimension. -/
private theorem nashVolumeFactor_pos (d : ℕ) (hd : 0 < d) : 0 < nashVolumeFactor d := by
  have hnum : 0 < Real.sqrt Real.pi ^ d := pow_pos (Real.sqrt_pos.mpr Real.pi_pos) d
  have hden : 0 < Real.Gamma ((d : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  exact div_pos hnum hden

/-- The factor `1 / (2π)²` in the Fourier expression for the homogeneous `H¹` norm. -/
private def nashFourierWeight : ℝ := ((2 * Real.pi) ^ (2 : ℕ))⁻¹

/-- `nashFourierWeight` is positive. -/
private theorem nashFourierWeight_pos : 0 < nashFourierWeight := by
  simpa [nashFourierWeight] using inv_pos.mpr (pow_pos (mul_pos two_pos Real.pi_pos) 2)

/-- Nash constant obtained by optimizing the Fourier ball split in dimension `d`. -/
private def nashConst (d : ℕ) : ℝ :=
  (2 * nashVolumeFactor d ^ (2 / ((d : ℝ) + 2)) *
      nashFourierWeight ^ ((d : ℝ) / ((d : ℝ) + 2))) ^
    (((d : ℝ) + 2) / (d : ℝ))

/-- The optimized Nash constant is positive. -/
private theorem nashConst_pos (d : ℕ) (hd : 0 < d) : 0 < nashConst d := by
  have hω : 0 < nashVolumeFactor d := nashVolumeFactor_pos d hd
  have hK : 0 < nashFourierWeight := nashFourierWeight_pos
  have hbase : 0 < 2 * nashVolumeFactor d ^ (2 / ((d : ℝ) + 2)) *
      nashFourierWeight ^ ((d : ℝ) / ((d : ℝ) + 2)) :=
    mul_pos (mul_pos two_pos (Real.rpow_pos_of_pos hω _)) (Real.rpow_pos_of_pos hK _)
  simpa [nashConst] using Real.rpow_pos_of_pos hbase _

/-- Lebesgue volume of a Euclidean ball centered at the origin. -/
private theorem volume_real_ball_zero (d : ℕ) (hd : 0 < d) {R : ℝ} (hR : 0 ≤ R) :
    (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball 0 R) =
      nashVolumeFactor d * R ^ d := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [measureReal_def,
    EuclideanSpace.volume_ball (Fin d) (0 : EuclideanSpace ℝ (Fin d)) R, Fintype.card_fin,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR]
  have hfac : 0 ≤ √Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := by
    simpa [nashVolumeFactor] using (nashVolumeFactor_pos d hd).le
  rw [ENNReal.toReal_ofReal hfac, nashVolumeFactor, mul_comm]

/-- Squared `L²` norm as the integral of the squared pointwise norm. -/
private theorem integral_norm_sq_eq_sq_norm {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} (f : Lp F 2 μ) :
    ∫ x, ‖f x‖ ^ 2 ∂μ = ‖f‖ ^ 2 := by
  have hlp : lpNorm (f : α → F) 2 μ =
      (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (Lp.aestronglyMeasurable f)]
    simp only [ENNReal.toReal_ofNat]
  simp_rw [Real.rpow_two] at hlp
  have hI : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hsq : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
    calc ‖f‖ ^ 2
        = (lpNorm (f : α → F) 2 μ) ^ (2 : ℝ) := by
          rw [Lp.norm_def, toReal_eLpNorm, ← Real.rpow_two]
        _ = ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹) ^ (2 : ℝ) := by rw [hlp]
        _ = (∫ x, ‖f x‖ ^ 2 ∂μ) ^ ((2 : ℝ)⁻¹ * 2) := by rw [← Real.rpow_mul hI]
        _ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
          rw [show ((2 : ℝ)⁻¹) * 2 = 1 by norm_num, Real.rpow_one]
  exact hsq.symm

/-- The distributional Fourier transform of an `L¹` function pairs as the integral transform. -/
private theorem fourier_lp_apply {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] (v : Lp F 1 (volume : Measure E)) (φ : 𝓢(E, ℂ)) :
    𝓕 (v : 𝓢'(E, F)) φ = ∫ x, φ x • 𝓕 (v : E → F) x := by
  rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply, SchwartzMap.fourier_coe]
  have hL : Continuous fun p : E × E => (innerₗ E) p.1 p.2 := by
    simp only [innerₗ_apply_apply]
    fun_prop
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip Real.continuous_fourierChar hL
    (φ.integrable (μ := volume)) (L1.integrable_coeFn v)
  rw [flip_innerₗ] at h
  exact h

/-- The `L²` Fourier transform, coerced to a pointwise function. -/
private abbrev fourierL2Fun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : Lp ℂ 2 (volume : Measure E)) : E → ℂ :=
  (𝓕 f : Lp ℂ 2 (volume : Measure E))

/-- An `L²` Fourier transform agrees almost everywhere with the integral transform of an a.e.-equal
`L¹` representative. -/
private theorem fourier_l2_ae_eq_l1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f1 : Lp ℂ 1 (volume : Measure E)) (f2 : Lp ℂ 2 (volume : Measure E))
    (hae : (f1 : E → ℂ) =ᵐ[volume] (f2 : E → ℂ)) :
    fourierL2Fun f2 =ᵐ[volume] 𝓕 (f1 : E → ℂ) := by
  have hdist : (f1 : 𝓢'(E, ℂ)) = (f2 : 𝓢'(E, ℂ)) := by
    ext φ
    simp only [Lp.toTemperedDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  have hcont : Continuous (𝓕 (f1 : E → ℂ)) := by
    change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ E) _)
    refine VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar ?_
      (L1.integrable_coeFn f1)
    simp only [innerₗ_apply_apply]
    fun_prop
  refine Lp.ae_eq_of_toTemperedDistribution_apply_eq (𝓕 f2) hcont.locallyIntegrable ?_
  intro φ
  calc (Lp.toTemperedDistribution (𝓕 f2)) φ
      = 𝓕 (f2 : 𝓢'(E, ℂ)) φ := by
        exact congrFun (congrArg DFunLike.coe (Lp.fourier_toTemperedDistribution_eq f2).symm) φ
      _ = 𝓕 (f1 : 𝓢'(E, ℂ)) φ := by rw [hdist]
      _ = ∫ x, φ x • 𝓕 (f1 : E → ℂ) x := fourier_lp_apply f1 φ

/-- Sum of squares of a real linear form on an orthonormal basis is the squared operator norm. -/
private theorem sum_sq_apply_orthonormalBasis {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : E →L[ℝ] ℝ) :
    ∑ i, (L (stdOrthonormalBasis ℝ E i)) ^ 2 = ‖L‖ ^ 2 := by
  let b := stdOrthonormalBasis ℝ E
  calc ∑ i, (L (b i)) ^ 2
      = ∑ i, ⟪(InnerProductSpace.toDual ℝ E).symm L, b i⟫ ^ 2 := by
        simp [← InnerProductSpace.toDual_symm_apply]
      _ = ‖(InnerProductSpace.toDual ℝ E).symm L‖ ^ 2 := b.sum_sq_inner_left _
      _ = ‖L‖ ^ 2 := by rw [(InnerProductSpace.toDual ℝ E).symm.norm_map L]

/-- Modulus of the derivative symbol `(2πI) · ⟪ξ, v⟫ · z`. -/
private theorem norm_fourier_symbol (t : ℝ) (z : ℂ) :
    ‖(2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ) * z‖ = 2 * Real.pi * |t| * ‖z‖ := by
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hcoe : ((2 * Real.pi : ℝ) : ℂ) = (2 : ℂ) * Real.pi := by
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [← hcoe, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hpi, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  ring

/-- Real-analytic optimization of `M ≤ ω R^d A + K B / R²`. -/
private theorem nash_rpow_of_forall_radius {d : ℕ} (hd : 0 < d) {A B M : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hball : ∀ R : ℝ, 0 < R →
      M ≤ nashVolumeFactor d * R ^ d * A + nashFourierWeight * B / R ^ 2) :
    M ^ (((d : ℝ) + 2) / d) ≤ nashConst d * A ^ (2 / (d : ℝ)) * B := by
  have hp : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hq0 : 0 < ((d : ℝ) + 2) / (d : ℝ) := div_pos (by linarith) hp
  by_cases hA0 : A = 0
  · have hM0 : M = 0 := by
      refine le_antisymm ?_ hM
      refine le_of_forall_pos_le_add fun ε hε => ?_
      by_cases hB0 : B = 0
      · have hle := hball 1 one_pos
        rw [hA0, hB0] at hle
        simp only [mul_zero, add_zero, zero_div] at hle
        linarith
      · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
        have hK : 0 < nashFourierWeight := nashFourierWeight_pos
        let R := Real.sqrt (nashFourierWeight * B / ε)
        have hrad : 0 < nashFourierWeight * B / ε := div_pos (mul_pos hK hBpos) hε
        have hRpos : 0 < R := Real.sqrt_pos.mpr hrad
        have hsq : R ^ 2 = nashFourierWeight * B / ε := Real.sq_sqrt hrad.le
        have hle := hball R hRpos
        rw [hA0, mul_zero, zero_add, hsq,
          div_div_cancel₀ (mul_pos hK hBpos).ne'] at hle
        linarith
    rw [hM0, Real.zero_rpow hq0.ne']
    exact mul_nonneg (mul_nonneg (nashConst_pos d hd).le (Real.rpow_nonneg hA _)) hB
  · by_cases hB0 : B = 0
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
      have hω : 0 < nashVolumeFactor d := nashVolumeFactor_pos d hd
      have hM0 : M = 0 := by
        refine le_antisymm ?_ hM
        refine le_of_forall_pos_le_add fun ε hε => ?_
        let R := (ε / (nashVolumeFactor d * A)) ^ (1 / (d : ℝ))
        have hbase : 0 < ε / (nashVolumeFactor d * A) := by positivity
        have hRpos : 0 < R := Real.rpow_pos_of_pos hbase _
        have hRd : R ^ (d : ℝ) = ε / (nashVolumeFactor d * A) := by
          rw [← Real.rpow_mul hbase.le]
          rw [show (1 / (d : ℝ)) * (d : ℝ) = 1 by field_simp, Real.rpow_one]
        have hle := hball R hRpos
        rw [hB0, mul_zero, zero_div, add_zero, ← Real.rpow_natCast, hRd] at hle
        have hcancel : nashVolumeFactor d * (ε / (nashVolumeFactor d * A)) * A = ε := by
          field_simp
        rw [hcancel] at hle
        linarith
      rw [hM0, Real.zero_rpow hq0.ne']
      exact mul_nonneg (mul_nonneg (nashConst_pos d hd).le (Real.rpow_nonneg hA _)) hB
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
      have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
      let ω := nashVolumeFactor d
      have hω : 0 < ω := nashVolumeFactor_pos d hd
      let K := nashFourierWeight
      have hK : 0 < K := nashFourierWeight_pos
      let p : ℝ := d
      let eA : ℝ := 2 / (p + 2)
      let eB : ℝ := p / (p + 2)
      let q : ℝ := (p + 2) / p
      have heA : 0 < eA := by positivity
      have heB : 0 ≤ eB := by positivity
      have hq : 0 ≤ q := by positivity
      have hsum : eA + eB = 1 := by
        dsimp [eA, eB]
        rw [div_eq_mul_inv, div_eq_mul_inv, ← add_mul, add_comm,
          mul_inv_cancel₀ (by positivity)]
      let base := K * B / (ω * A)
      have hbase : 0 < base := by positivity
      let R := base ^ (1 / (p + 2))
      have hRpos : 0 < R := Real.rpow_pos_of_pos hbase _
      have hRp : R ^ p = base ^ eB := by
        rw [← Real.rpow_mul hbase.le]
        dsimp [eB]
        congr 1
        field_simp
      have hR2 : R ^ (2 : ℝ) = base ^ eA := by
        rw [← Real.rpow_mul hbase.le]
        dsimp [eA]
        congr 1
        field_simp
      have ht : 0 < ω * A := mul_pos hω hApos
      have hs : 0 < K * B := mul_pos hK hBpos
      have hterm1 : ω * base ^ eB * A = (ω * A) ^ eA * (K * B) ^ eB := by
        have hb : base = (K * B) / (ω * A) := rfl
        rw [hb, Real.div_rpow hs.le ht.le]
        have heq : eA = 1 - eB := by linarith
        have hsub : (ω * A) ^ (1 - eB) = (ω * A) / (ω * A) ^ eB := by
          rw [Real.rpow_sub ht, Real.rpow_one]
        calc ω * ((K * B) ^ eB / (ω * A) ^ eB) * A
            = (ω * A) * (K * B) ^ eB / (ω * A) ^ eB := by field_simp
            _ = (ω * A) / (ω * A) ^ eB * (K * B) ^ eB := by field_simp
            _ = (ω * A) ^ (1 - eB) * (K * B) ^ eB := by rw [← hsub]
            _ = (ω * A) ^ eA * (K * B) ^ eB := by rw [heq]
      have hterm2 : K * B / base ^ eA = (ω * A) ^ eA * (K * B) ^ eB := by
        have hb : base = (K * B) / (ω * A) := rfl
        rw [hb, Real.div_rpow hs.le ht.le]
        have heq : eB = 1 - eA := by linarith
        have hsub : (K * B) ^ (1 - eA) = (K * B) / (K * B) ^ eA := by
          rw [Real.rpow_sub hs, Real.rpow_one]
        calc K * B / ((K * B) ^ eA / (ω * A) ^ eA)
            = K * B * ((ω * A) ^ eA / (K * B) ^ eA) := by field_simp
            _ = (ω * A) ^ eA * ((K * B) / (K * B) ^ eA) := by field_simp
            _ = (ω * A) ^ eA * (K * B) ^ (1 - eA) := by rw [← hsub]
            _ = (ω * A) ^ eA * (K * B) ^ eB := by rw [heq]
      have hle := hball R hRpos
      rw [← Real.rpow_natCast, hRp, ← Real.rpow_two, hR2, hterm1, hterm2] at hle
      have htwo : M ≤ 2 * ((ω * A) ^ eA * (K * B) ^ eB) := by
        have h2 : (ω * A) ^ eA * (K * B) ^ eB + (ω * A) ^ eA * (K * B) ^ eB =
            2 * ((ω * A) ^ eA * (K * B) ^ eB) := by ring
        linarith
      have hprod : (ω * A) ^ eA * (K * B) ^ eB =
          ω ^ eA * K ^ eB * A ^ eA * B ^ eB := by
        rw [Real.mul_rpow hω.le hA, Real.mul_rpow hK.le hB]
        ring
      rw [hprod] at htwo
      let C1 := 2 * ω ^ eA * K ^ eB
      have hC1 : M ≤ C1 * A ^ eA * B ^ eB := by
        dsimp [C1]
        linarith
      have hC1nn : 0 ≤ C1 := by
        dsimp [C1]
        exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hω.le _))
          (Real.rpow_nonneg hK.le _)
      have hAe : 0 ≤ A ^ eA := Real.rpow_nonneg hA _
      have hBe : 0 ≤ B ^ eB := Real.rpow_nonneg hB _
      have hraise := Real.rpow_le_rpow hM hC1 hq
      rw [Real.mul_rpow (mul_nonneg hC1nn hAe) hBe, Real.mul_rpow hC1nn hAe,
        ← Real.rpow_mul hA, ← Real.rpow_mul hB] at hraise
      have hAq : eA * q = 2 / p := by
        dsimp [eA, q, p]
        field_simp
      have hBq : eB * q = 1 := by
        dsimp [eB, q, p]
        field_simp
      have hCq : C1 ^ q = nashConst d := by
        simp [C1, q, eA, eB, p, nashConst, ω, K]
      rw [hAq, hBq, Real.rpow_one, hCq] at hraise
      simpa [p, q] using hraise

section Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Squared `L²` norm of one weak directional derivative, as a weighted integral of `|û|²`. -/
private theorem integral_sq_weakLine_fourier {u u' : E → ℝ} {v : E}
    (hu1 : MemLp u 1 volume) (hu2 : MemLp u 2 volume) (hu' : MemLp u' 2 volume)
    (hweak : TauCeti.HasWeakLineDerivOn volume ⊤ u u' v) :
    Integrable (fun ξ : E => ⟪ξ, v⟫ ^ 2 *
        ‖𝓕 ((Complex.ofRealCLM.compLp (hu1.toLp u) : E → ℂ)) ξ‖ ^ 2) volume ∧
      ∫ x, u' x ^ 2 ∂(volume : Measure E) =
        (2 * Real.pi) ^ 2 * ∫ ξ, ⟪ξ, v⟫ ^ 2 *
          ‖𝓕 ((Complex.ofRealCLM.compLp (hu1.toLp u) : E → ℂ)) ξ‖ ^ 2 ∂volume := by
  let u1 : Lp ℝ 1 (volume : Measure E) := hu1.toLp u
  let u2 : Lp ℝ 2 (volume : Measure E) := hu2.toLp u
  let up : Lp ℝ 2 (volume : Measure E) := hu'.toLp u'
  let uc1 : Lp ℂ 1 (volume : Measure E) := Complex.ofRealCLM.compLp u1
  let uc2 : Lp ℂ 2 (volume : Measure E) := Complex.ofRealCLM.compLp u2
  let uc' : Lp ℂ 2 (volume : Measure E) := Complex.ofRealCLM.compLp up
  let uHat : E → ℂ := 𝓕 (uc1 : E → ℂ)
  have hae12 : (uc1 : E → ℂ) =ᵐ[volume] (uc2 : E → ℂ) := by
    have h1 : (uc1 : E → ℂ) =ᵐ[volume] fun x => (u x : ℂ) := by
      filter_upwards [Complex.ofRealCLM.coeFn_compLp u1, hu1.coeFn_toLp] with x hxc hxu
      rw [hxc, hxu, Complex.ofRealCLM_apply]
    have h2 : (uc2 : E → ℂ) =ᵐ[volume] fun x => (u x : ℂ) := by
      filter_upwards [Complex.ofRealCLM.coeFn_compLp u2, hu2.coeFn_toLp] with x hxc hxu
      rw [hxc, hxu, Complex.ofRealCLM_apply]
    exact h1.trans h2.symm
  have haeHat : fourierL2Fun (Complex.ofRealCLM.compLp u2) =ᵐ[volume] uHat :=
    fourier_l2_ae_eq_l1 uc1 uc2 hae12
  have hrest : (volume : Measure E).restrict (⊤ : Opens E) = volume := by
    rw [Opens.coe_top, Measure.restrict_univ]
  have haeu : u =ᵐ[volume.restrict (⊤ : Opens E)] (u2 : E → ℝ) := by
    rw [hrest]
    exact hu2.coeFn_toLp.symm
  have haeu' : u' =ᵐ[volume.restrict (⊤ : Opens E)] (up : E → ℝ) := by
    rw [hrest]
    exact hu'.coeFn_toLp.symm
  have hline : TauCeti.HasWeakLineDerivOn volume ⊤ (u2 : E → ℝ) (up : E → ℝ) v :=
    (hweak.congr_ae haeu).congr_ae_deriv haeu'
  have hdist :=
    (TauCeti.hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_ofReal_eq u2 up v).1
      hline
  have hF := congrArg (fun T : 𝓢'(E, ℂ) => 𝓕 T) hdist
  rw [TemperedDistribution.fourier_lineDerivOp_eq] at hF
  rw [Lp.fourier_toTemperedDistribution_eq, Lp.fourier_toTemperedDistribution_eq] at hF
  let g : E → ℂ := fun ξ => (2 * (Real.pi : ℂ) * Complex.I) * (⟪ξ, v⟫ : ℂ) * uHat ξ
  have hgcont : Continuous g := by
    have hHat : Continuous uHat := by
      change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ E) _)
      refine VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar ?_
        (L1.integrable_coeFn uc1)
      simp only [innerₗ_apply_apply]
      fun_prop
    fun_prop
  have haeg : fourierL2Fun uc' =ᵐ[volume] g := by
    refine Lp.ae_eq_of_toTemperedDistribution_apply_eq (𝓕 uc') hgcont.locallyIntegrable ?_
    intro φ
    rw [← hF, smul_apply, TemperedDistribution.smulLeftCLM_apply_apply,
      Lp.toTemperedDistribution_apply]
    have hgrow : (fun x : E => (⟪x, v⟫ : ℂ)).HasTemperateGrowth := by fun_prop
    simp_rw [SchwartzMap.smulLeftCLM_apply_apply hgrow]
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [haeHat] with ξ hξ
    dsimp [fourierL2Fun] at hξ
    simp only [smul_eq_mul, hξ, g]
    ring
  have hsq : ∀ ξ, ‖g ξ‖ ^ 2 =
      (2 * Real.pi) ^ 2 * ⟪ξ, v⟫ ^ 2 * ‖uHat ξ‖ ^ 2 := by
    intro ξ
    rw [norm_fourier_symbol, mul_pow, mul_pow, sq_abs]
  have hintg : Integrable (fun ξ => ‖g ξ‖ ^ 2) volume := by
    have hint : Integrable (fun ξ => ‖fourierL2Fun uc' ξ‖ ^ 2) volume := by
      simpa [ENNReal.toReal_ofNat, Real.rpow_two] using
        (Lp.memLp (𝓕 uc')).integrable_norm_rpow (by norm_num) (by norm_num)
    refine hint.congr ?_
    filter_upwards [haeg] with ξ hξ
    rw [hξ]
  have hintw : Integrable (fun ξ => ⟪ξ, v⟫ ^ 2 * ‖uHat ξ‖ ^ 2) volume := by
    have hpt : (fun ξ => ⟪ξ, v⟫ ^ 2 * ‖uHat ξ‖ ^ 2) =ᵐ[volume]
        fun ξ => ‖g ξ‖ ^ 2 / (2 * Real.pi) ^ 2 := by
      filter_upwards with ξ
      rw [hsq ξ]
      field_simp
    exact (hintg.div_const _).congr hpt.symm
  have hleft : ∫ x, u' x ^ 2 ∂volume = ‖uc'‖ ^ 2 := by
    calc ∫ x, u' x ^ 2 ∂volume
        = ∫ x, ‖(u' x : ℂ)‖ ^ 2 ∂volume := by
          simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
        _ = ∫ x, ‖(uc' : E → ℂ) x‖ ^ 2 ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [Complex.ofRealCLM.coeFn_compLp up, hu'.coeFn_toLp] with x hxc hxu
          dsimp [uc']
          rw [hxc, hxu, Complex.ofRealCLM_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        _ = ‖uc'‖ ^ 2 := integral_norm_sq_eq_sq_norm uc'
  have hright : ‖uc'‖ ^ 2 =
      (2 * Real.pi) ^ 2 * ∫ ξ, ⟪ξ, v⟫ ^ 2 * ‖uHat ξ‖ ^ 2 ∂volume := by
    calc ‖uc'‖ ^ 2
        = ‖𝓕 uc'‖ ^ 2 := by rw [Lp.norm_fourier_eq]
        _ = ∫ ξ, ‖fourierL2Fun uc' ξ‖ ^ 2 ∂volume :=
          (integral_norm_sq_eq_sq_norm (𝓕 uc')).symm
        _ = ∫ ξ, ‖g ξ‖ ^ 2 ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [haeg] with ξ hξ
          rw [hξ]
        _ = ∫ ξ, (2 * Real.pi) ^ 2 * (⟪ξ, v⟫ ^ 2 * ‖uHat ξ‖ ^ 2) ∂volume := by
          refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
          dsimp
          rw [hsq ξ, mul_assoc]
        _ = (2 * Real.pi) ^ 2 * ∫ ξ, ⟪ξ, v⟫ ^ 2 * ‖uHat ξ‖ ^ 2 ∂volume := by
          rw [integral_const_mul]
  refine ⟨?_, ?_⟩
  · simpa [uHat] using hintw
  · rw [hleft, hright]

/-- Fourier splitting of the Nash integrand at radius `R`. -/
private theorem nash_ball_split (hd : 0 < d) {u : E → ℝ}
    {U : E → E →L[ℝ] ℝ} (hu1 : MemLp u 1 volume) (hu2 : MemLp u 2 volume)
    (hU : MemLp U 2 volume) (hweak : TauCeti.HasWeakFDerivOn volume ⊤ u U) {R : ℝ}
    (hR : 0 < R) :
    (eLpNorm u 2 volume).toReal ^ 2 ≤
      nashVolumeFactor d * R ^ d * (eLpNorm u 1 volume).toReal ^ 2 +
        nashFourierWeight * (eLpNorm U 2 volume).toReal ^ 2 / R ^ 2 := by
  let u1 : Lp ℝ 1 (volume : Measure E) := hu1.toLp u
  let uc1 : Lp ℂ 1 (volume : Measure E) := Complex.ofRealCLM.compLp u1
  let uHat : E → ℂ := 𝓕 (uc1 : E → ℂ)
  let A := (eLpNorm u 1 volume).toReal ^ 2
  let B := (eLpNorm U 2 volume).toReal ^ 2
  let f : E → ℝ := fun ξ => ‖uHat ξ‖ ^ 2
  have hn1 : ∫ x, ‖(uc1 : E → ℂ) x‖ ∂volume = (eLpNorm u 1 volume).toReal := by
    rw [← L1.norm_eq_integral_norm uc1, Lp.norm_def]
    refine congrArg ENNReal.toReal ?_
    refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable uc1) hu1.aestronglyMeasurable ?_
    filter_upwards [Complex.ofRealCLM.coeFn_compLp u1, hu1.coeFn_toLp] with x hxc hxu
    rw [hxc, hxu, Complex.ofRealCLM_apply, Complex.norm_real]
  have hbound : ∀ ξ, ‖uHat ξ‖ ≤ (eLpNorm u 1 volume).toReal := by
    intro ξ
    calc ‖uHat ξ‖
        ≤ ∫ x, ‖(uc1 : E → ℂ) x‖ ∂volume := Real.norm_fourier_le_integral_norm _ ξ
        _ = (eLpNorm u 1 volume).toReal := hn1
  have hA : 0 ≤ A := sq_nonneg _
  have hf_le : ∀ ξ, f ξ ≤ A := by
    intro ξ
    dsimp [f, A]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound ξ) 2
  let u2 : Lp ℝ 2 (volume : Measure E) := hu2.toLp u
  let uc2 : Lp ℂ 2 (volume : Measure E) := Complex.ofRealCLM.compLp u2
  have hae12 : (uc1 : E → ℂ) =ᵐ[volume] (uc2 : E → ℂ) := by
    have h1 : (uc1 : E → ℂ) =ᵐ[volume] fun x => (u x : ℂ) := by
      filter_upwards [Complex.ofRealCLM.coeFn_compLp u1, hu1.coeFn_toLp] with x hxc hxu
      rw [hxc, hxu, Complex.ofRealCLM_apply]
    have h2 : (uc2 : E → ℂ) =ᵐ[volume] fun x => (u x : ℂ) := by
      filter_upwards [Complex.ofRealCLM.coeFn_compLp u2, hu2.coeFn_toLp] with x hxc hxu
      rw [hxc, hxu, Complex.ofRealCLM_apply]
    exact h1.trans h2.symm
  have haeF : fourierL2Fun uc2 =ᵐ[volume] uHat := fourier_l2_ae_eq_l1 uc1 uc2 hae12
  have hintf : Integrable f volume := by
    have hint : Integrable (fun ξ => ‖fourierL2Fun uc2 ξ‖ ^ 2) volume := by
      simpa [ENNReal.toReal_ofNat, Real.rpow_two] using
        (Lp.memLp (𝓕 uc2)).integrable_norm_rpow (by norm_num) (by norm_num)
    refine hint.congr ?_
    filter_upwards [haeF] with ξ hξ
    simp [f, hξ]
  have hM : ∫ ξ, f ξ ∂volume = (eLpNorm u 2 volume).toReal ^ 2 := by
    calc ∫ ξ, f ξ ∂volume
        = ∫ ξ, ‖fourierL2Fun uc2 ξ‖ ^ 2 ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [haeF] with ξ hξ
          simp [f, hξ]
        _ = ‖𝓕 uc2‖ ^ 2 := integral_norm_sq_eq_sq_norm (𝓕 uc2)
        _ = ‖uc2‖ ^ 2 := by rw [Lp.norm_fourier_eq]
        _ = (eLpNorm (uc2 : E → ℂ) 2 volume).toReal ^ 2 := by rw [Lp.norm_def]
        _ = (eLpNorm u 2 volume).toReal ^ 2 := by
          refine congrArg (fun t : ℝ≥0∞ => t.toReal ^ 2) ?_
          refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable uc2)
            hu2.aestronglyMeasurable ?_
          filter_upwards [Complex.ofRealCLM.coeFn_compLp u2, hu2.coeFn_toLp] with x hxc hxu
          rw [hxc, hxu, Complex.ofRealCLM_apply, Complex.norm_real]
  let b := stdOrthonormalBasis ℝ E
  have hmem (i : Fin (Module.finrank ℝ E)) :
      MemLp (fun x => U x (b i)) 2 volume := by
    refine MemLp.ae_eq ?_ ((ContinuousLinearMap.apply ℝ ℝ (b i)).comp_memLp' hU)
    filter_upwards with x
    exact ContinuousLinearMap.apply_apply (b i) (U x)
  have hpack (i : Fin (Module.finrank ℝ E)) :=
    integral_sq_weakLine_fourier hu1 hu2 (hmem i) (hweak.hasWeakLineDerivOn (b i))
  have hintDir (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun x => (U x (b i)) ^ 2) volume := (hmem i).integrable_sq
  have hintW (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun ξ => ⟪ξ, b i⟫ ^ 2 * f ξ) volume := by
    simpa [uHat, f] using (hpack i).1
  have hdir (i : Fin (Module.finrank ℝ E)) :
      ∫ x, (U x (b i)) ^ 2 ∂volume =
        (2 * Real.pi) ^ 2 * ∫ ξ, ⟪ξ, b i⟫ ^ 2 * f ξ ∂volume := by
    simpa [uHat, f] using (hpack i).2
  have hpoint : ∀ x, ‖U x‖ ^ 2 = ∑ i, (U x (b i)) ^ 2 := by
    intro x
    simpa [b] using (sum_sq_apply_orthonormalBasis (U x)).symm
  have hintNorm : Integrable (fun ξ => ‖ξ‖ ^ 2 * f ξ) volume := by
    have hpt : (fun ξ => ‖ξ‖ ^ 2 * f ξ) = fun ξ => ∑ i, ⟪ξ, b i⟫ ^ 2 * f ξ := by
      funext ξ
      rw [← Finset.sum_mul, b.sum_sq_inner_left ξ]
    rw [hpt]
    exact integrable_finsetSum Finset.univ fun i _ => hintW i
  have hsum : ∫ x, ‖U x‖ ^ 2 ∂volume =
      (2 * Real.pi) ^ 2 * ∫ ξ, ‖ξ‖ ^ 2 * f ξ ∂volume := by
    calc ∫ x, ‖U x‖ ^ 2 ∂volume
        = ∫ x, ∑ i, (U x (b i)) ^ 2 ∂volume := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          dsimp
          exact hpoint x
        _ = ∑ i, ∫ x, (U x (b i)) ^ 2 ∂volume := by
          rw [integral_finsetSum Finset.univ fun i _ => hintDir i]
        _ = ∑ i, (2 * Real.pi) ^ 2 * ∫ ξ, ⟪ξ, b i⟫ ^ 2 * f ξ ∂volume := by
          refine Finset.sum_congr rfl fun i _ => hdir i
        _ = (2 * Real.pi) ^ 2 * ∑ i, ∫ ξ, ⟪ξ, b i⟫ ^ 2 * f ξ ∂volume := by
          rw [← Finset.mul_sum]
        _ = (2 * Real.pi) ^ 2 * ∫ ξ, ∑ i, ⟪ξ, b i⟫ ^ 2 * f ξ ∂volume := by
          rw [integral_finsetSum Finset.univ fun i _ => hintW i]
        _ = (2 * Real.pi) ^ 2 * ∫ ξ, ‖ξ‖ ^ 2 * f ξ ∂volume := by
          refine congrArg (fun t => (2 * Real.pi) ^ 2 * t) ?_
          refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
          dsimp
          rw [← Finset.sum_mul, b.sum_sq_inner_left ξ]
  have hBint : ∫ x, ‖U x‖ ^ 2 ∂volume = B := by
    calc ∫ x, ‖U x‖ ^ 2 ∂volume
        = ∫ x, ‖(hU.toLp U : E → E →L[ℝ] ℝ) x‖ ^ 2 ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [hU.coeFn_toLp] with x hx
          rw [← hx]
        _ = ‖hU.toLp U‖ ^ 2 := integral_norm_sq_eq_sq_norm (hU.toLp U)
        _ = B := by
          dsimp [B]
          congr 1
          rw [Lp.norm_def]
          exact congrArg ENNReal.toReal (eLpNorm_congr_ae hU.coeFn_toLp)
  have hweight : ∫ ξ, ‖ξ‖ ^ 2 * f ξ ∂volume = nashFourierWeight * B := by
    have hmul : B = (2 * Real.pi) ^ 2 * ∫ ξ, ‖ξ‖ ^ 2 * f ξ ∂volume := by
      rw [← hsum, hBint]
    rw [nashFourierWeight, ← div_eq_inv_mul, eq_div_iff (by positivity)]
    rw [mul_comm]
    exact hmul.symm
  let s := Metric.ball (0 : E) R
  have hs : MeasurableSet s := measurableSet_ball
  have hconst : IntegrableOn (fun _ : E => A) s volume :=
    integrableOn_const (hs := measure_ball_ne_top) (hC := enorm_ne_top)
  have hball : ∫ ξ in s, f ξ ∂volume ≤ (volume : Measure E).real s * A := by
    have hmono : ∫ ξ in s, f ξ ∂volume ≤ ∫ ξ in s, A ∂volume :=
      setIntegral_mono_on (hf := hintf.integrableOn) (hg := hconst) hs fun ξ _ => hf_le ξ
    rwa [setIntegral_const, smul_eq_mul] at hmono
  have htail : ∫ ξ in sᶜ, f ξ ∂volume ≤
      (∫ ξ, ‖ξ‖ ^ 2 * f ξ ∂volume) / R ^ 2 := by
    have hdiv : Integrable (fun ξ => ‖ξ‖ ^ 2 * f ξ / R ^ 2) volume := hintNorm.div_const _
    have hmono : ∫ ξ in sᶜ, f ξ ∂volume ≤
        ∫ ξ in sᶜ, ‖ξ‖ ^ 2 * f ξ / R ^ 2 ∂volume := by
      refine setIntegral_mono_on (hf := hintf.integrableOn) (hg := hdiv.integrableOn)
        hs.compl ?_
      intro ξ hξ
      have hξR : R ≤ ‖ξ‖ := by
        simpa [s, Metric.mem_ball, dist_zero_right] using hξ
      have hf0 : 0 ≤ f ξ := sq_nonneg _
      have hr : (1 : ℝ) ≤ ‖ξ‖ ^ 2 / R ^ 2 := by
        rw [one_le_div (by positivity : 0 < R ^ 2)]
        exact pow_le_pow_left₀ (by positivity : 0 ≤ R) hξR 2
      calc f ξ
          = f ξ * 1 := by ring
          _ ≤ f ξ * (‖ξ‖ ^ 2 / R ^ 2) := mul_le_mul_of_nonneg_left hr hf0
          _ = ‖ξ‖ ^ 2 * f ξ / R ^ 2 := by ring
    have hle2 : ∫ ξ in sᶜ, ‖ξ‖ ^ 2 * f ξ / R ^ 2 ∂volume ≤
        ∫ ξ, ‖ξ‖ ^ 2 * f ξ / R ^ 2 ∂volume :=
      setIntegral_le_integral hdiv (ae_of_all _ fun ξ => by positivity)
    have hquot : ∫ ξ, ‖ξ‖ ^ 2 * f ξ / R ^ 2 ∂volume =
        (∫ ξ, ‖ξ‖ ^ 2 * f ξ ∂volume) / R ^ 2 := integral_div _ _
    linarith
  rw [volume_real_ball_zero d hd hR.le] at hball
  calc (eLpNorm u 2 volume).toReal ^ 2
      = ∫ ξ, f ξ ∂volume := hM.symm
      _ = ∫ ξ in s, f ξ ∂volume + ∫ ξ in sᶜ, f ξ ∂volume :=
        (integral_add_compl hs hintf).symm
      _ ≤ nashVolumeFactor d * R ^ d * A +
          (∫ ξ, ‖ξ‖ ^ 2 * f ξ ∂volume) / R ^ 2 := by
        gcongr
      _ = nashVolumeFactor d * R ^ d * A + nashFourierWeight * B / R ^ 2 := by
        rw [hweight, div_eq_mul_inv, mul_comm (nashFourierWeight * B) _, mul_assoc]

end Euclidean

/-- **14.40**: Nash's inequality on `L¹ ∩ H¹`, including weak derivatives. -/
theorem nash {d : ℕ} (hd : 0 < d) : ∃ C : ℝ, 0 < C ∧
    ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
      (U : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      MemLp u 1 volume → MemLp u 2 volume → MemLp U 2 volume →
      TauCeti.HasWeakFDerivOn volume ⊤ u U →
      (eLpNorm u 2 volume).toReal ^ (2 + 4 / (d : ℝ)) ≤
        C * (eLpNorm U 2 volume).toReal ^ 2 * (eLpNorm u 1 volume).toReal ^ (4 / (d : ℝ)) := by
  refine ⟨nashConst d, nashConst_pos d hd, ?_⟩
  intro u U hu1 hu2 hU hweak
  let A := (eLpNorm u 1 volume).toReal ^ 2
  let B := (eLpNorm U 2 volume).toReal ^ 2
  let M := (eLpNorm u 2 volume).toReal ^ 2
  have hball : ∀ R : ℝ, 0 < R →
      M ≤ nashVolumeFactor d * R ^ d * A + nashFourierWeight * B / R ^ 2 := by
    intro R hR
    simpa [A, B, M] using nash_ball_split hd hu1 hu2 hU hweak hR
  have hopt := nash_rpow_of_forall_radius hd (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) hball
  have hn2 : 0 ≤ (eLpNorm u 2 volume).toReal := ENNReal.toReal_nonneg
  have hn1 : 0 ≤ (eLpNorm u 1 volume).toReal := ENNReal.toReal_nonneg
  have hMpow : M ^ (((d : ℝ) + 2) / d) =
      (eLpNorm u 2 volume).toReal ^ (2 + 4 / (d : ℝ)) := by
    rw [show M = (eLpNorm u 2 volume).toReal ^ (2 : ℝ) by rw [Real.rpow_two]]
    rw [← Real.rpow_mul hn2]
    congr 1
    field_simp
    ring
  have hApow : A ^ (2 / (d : ℝ)) =
      (eLpNorm u 1 volume).toReal ^ (4 / (d : ℝ)) := by
    rw [show A = (eLpNorm u 1 volume).toReal ^ (2 : ℝ) by rw [Real.rpow_two]]
    rw [← Real.rpow_mul hn1]
    congr 1
    field_simp
    ring
  calc (eLpNorm u 2 volume).toReal ^ (2 + 4 / (d : ℝ))
      = M ^ (((d : ℝ) + 2) / d) := hMpow.symm
      _ ≤ nashConst d * A ^ (2 / (d : ℝ)) * B := hopt
      _ = nashConst d * (eLpNorm u 1 volume).toReal ^ (4 / (d : ℝ)) *
          (eLpNorm U 2 volume).toReal ^ 2 := by rw [hApow]
      _ = nashConst d * (eLpNorm U 2 volume).toReal ^ 2 *
          (eLpNorm u 1 volume).toReal ^ (4 / (d : ℝ)) := by ring

end CKMA
