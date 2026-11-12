/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# Volterra equations and fractional integrals

Volterra equations use continuous complex-valued data on a compact real interval and a
continuous triangular kernel, with arbitrary complex coupling. Real Riemann–Liouville integrals
carry the Gamma normalization; positive-order semigroup and inverse statements are a.e. identities
on the open interval. The range criterion uses an absolutely continuous representative vanishing
at the left endpoint. The semigroup identity uses
`TauCeti.integral_rpow_mul_one_sub_rpow`. Sources: GAPS 25.18 and 25.23.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology intervalIntegral Real Set

open scoped ENNReal

/-- The scalar Volterra integral of a kernel and a function. -/
def volterraIntegral (k : ℝ → ℝ → ℂ) (u : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, k t s * u s

/-- **25.18**: a continuous triangular kernel gives a unique continuous solution at every
complex coupling. The series and data-dependence clauses are separate targets. -/
theorem existsUnique_volterra {T : ℝ} (hT : 0 ≤ T) (k : ℝ → ℝ → ℂ)
    (hk : ContinuousOn (fun p : ℝ × ℝ ↦ k p.1 p.2)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}) (c : ℂ) (f : C(Set.Icc 0 T, ℂ)) :
    ∃! u : C(Set.Icc 0 T, ℂ), ∀ t : Set.Icc 0 T,
      u t = f t + c * ∫ s in (0 : ℝ)..t.1,
        k t.1 s * (if hs : s ∈ Set.Icc 0 T then u ⟨s, hs⟩ else 0) := by
  sorry

/-- Riemann–Liouville fractional integration, with the Gamma normalization. -/
def fractionalIntegral (α : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  (Real.Gamma α)⁻¹ * ∫ s in (0 : ℝ)..t, (t - s) ^ (α - 1) * u s

/-- Power `x ^ c` for positive `x`, and `0` otherwise. It agrees with `Real.rpow` off `0`. -/
private def kernelPow (c x : ℝ) : ℝ :=
  if 0 < x then exp (log x * c) else 0

/-- `kernelPow` is Borel measurable. -/
private lemma measurable_kernelPow (c : ℝ) : Measurable (kernelPow c) := by
  unfold kernelPow
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  exact Real.measurable_exp.comp
    ((Real.measurable_log.comp measurable_id).mul measurable_const)

/-- Off zero, `kernelPow` is real exponentiation. -/
private lemma kernelPow_eq_rpow {c x : ℝ} (hx : 0 < x) : kernelPow c x = x ^ c := by
  simp only [kernelPow, hx, true_and, and_true, ↓reduceIte]
  exact (rpow_def_of_pos hx c).symm

/-- `kernelPow` takes nonnegative values. -/
private lemma kernelPow_nonneg (c x : ℝ) : 0 ≤ kernelPow c x := by
  unfold kernelPow
  split_ifs with hx
  · exact (exp_pos _).le
  · exact le_rfl

/-- The integral of a pure power of the remaining distance. -/
private lemma integral_sub_rpow {a b γ : ℝ} (hab : a ≤ b) (hγ : 0 < γ) :
    ∫ s in a..b, (b - s) ^ (γ - 1) = (b - a) ^ γ / γ := by
  have hshift : ∫ s in a..b, (b - s) ^ (γ - 1) =
      ∫ s in (0 : ℝ)..(b - a), s ^ (γ - 1) := by
    simpa using integral_comp_sub_left (fun s => s ^ (γ - 1)) b (a := a) (b := b)
  rw [hshift, integral_rpow (Or.inl (by linarith : -1 < γ - 1))]
  have hz : (0 : ℝ) ^ γ = 0 := zero_rpow hγ.ne'
  simp [hz, sub_zero, add_sub_cancel]

/-- The same power is integrable, so its Lebesgue integral equals the interval integral. -/
private lemma lintegral_Ioo_sub_rpow {a b γ : ℝ} (hab : a < b) (hγ : 0 < γ) :
    ∫⁻ t in Ioo a b, ENNReal.ofReal ((t - a) ^ (γ - 1)) =
      ENNReal.ofReal ((b - a) ^ γ / γ) := by
  have hbase : IntervalIntegrable (fun x => x ^ (γ - 1)) volume 0 (b - a) :=
    intervalIntegrable_rpow' (by linarith : -1 < γ - 1)
  have hint : IntervalIntegrable (fun t => (t - a) ^ (γ - 1)) volume a b := by
    simpa [sub_zero, sub_add_cancel] using hbase.comp_sub_right a
  let f : ℝ → ℝ := fun t => (t - a) ^ (γ - 1)
  have hInt : Integrable (indicator (Ioc a b) f) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).1 hint).integrable_indicator
      measurableSet_Ioc
  have hnn : 0 ≤ᵐ[volume] indicator (Ioc a b) f := by
    refine ae_of_all _ fun t => ?_
    simp only [indicator_apply]
    split_ifs with ht
    · exact rpow_nonneg (sub_nonneg.mpr ht.1.le) _
    · exact le_rfl
  have hval : ∫ t, indicator (Ioc a b) f t = (b - a) ^ γ / γ := by
    rw [MeasureTheory.integral_indicator measurableSet_Ioc, ← integral_of_le hab.le]
    have hshift : ∫ t in a..b, f t = ∫ s in (0 : ℝ)..(b - a), s ^ (γ - 1) := by
      simpa [f] using
        integral_comp_sub_right (f := fun s => s ^ (γ - 1)) (a := a) (b := b) a
    rw [hshift, integral_rpow (Or.inl (by linarith : -1 < γ - 1))]
    have hz : (0 : ℝ) ^ γ = 0 := zero_rpow hγ.ne'
    simp [hz, sub_zero]
  have hlin := ofReal_integral_eq_lintegral_ofReal hInt hnn
  rw [hval] at hlin
  have hind : (fun t => ENNReal.ofReal (indicator (Ioc a b) f t)) =
      indicator (Ioc a b) fun t => ENNReal.ofReal (f t) := by
    ext t
    by_cases ht : t ∈ Ioc a b
    · simp [indicator_of_mem ht]
    · simp [indicator_of_notMem ht, ENNReal.ofReal_zero]
  rw [hind, lintegral_indicator measurableSet_Ioc] at hlin
  have hlin' : ENNReal.ofReal ((b - a) ^ γ / γ) =
      ∫⁻ t in Ioc a b, ENNReal.ofReal ((t - a) ^ (γ - 1)) := by
    simpa [f] using hlin
  rw [setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume)), hlin']

/-- Zero extension past the right endpoint preserves an interval integral. -/
private lemma integral_of_lt_indicator {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (f : ℝ → ℝ) :
    ∫ r in (0 : ℝ)..s, f r = ∫ r in (0 : ℝ)..t, (if r < s then f r else 0) := by
  rw [integral_of_le hs, integral_of_le (hs.trans hst), integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]
  have hEq : EqOn (fun r => if r < s then f r else 0) ((Ioo 0 s).indicator f) (Ioo 0 t) := by
    intro r hr
    by_cases hrs : r < s
    · simp [hrs, indicator_of_mem (show r ∈ Ioo 0 s from ⟨hr.1, hrs⟩)]
    · have hnot : r ∉ Ioo 0 s := by
        intro hrI
        exact hrs (And.right (mem_Ioo.mp hrI))
      simp [hrs, indicator_of_notMem hnot]
  rw [setIntegral_congr_fun measurableSet_Ioo hEq, setIntegral_indicator measurableSet_Ioo,
    inter_eq_right.mpr (Ioo_subset_Ioo le_rfl hst)]

/-- Zero extension before the left endpoint preserves an interval integral. -/
private lemma integral_of_gt_indicator {t r : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (g : ℝ → ℝ) :
    ∫ s in (0 : ℝ)..t, (if r < s then g s else 0) = ∫ s in r..t, g s := by
  rw [integral_of_le (hr.trans hrt), integral_of_le hrt, integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]
  have hEq : EqOn (fun s => if r < s then g s else 0) ((Ioo r t).indicator g) (Ioo 0 t) := by
    intro s hs
    by_cases hrs : r < s
    · simp [hrs, indicator_of_mem (show s ∈ Ioo r t from ⟨hrs, hs.2⟩)]
    · have hnot : s ∉ Ioo r t := by
        intro hsI
        exact hrs (And.left (mem_Ioo.mp hsI))
      simp [hrs, indicator_of_notMem hnot]
  rw [setIntegral_congr_fun measurableSet_Ioo hEq, setIntegral_indicator measurableSet_Ioo,
    inter_eq_right.mpr (Ioo_subset_Ioo hr le_rfl)]

/-- Scaling the beta kernel on an interval of length `t - r`. -/
private lemma integral_betaKernel {t r α β : ℝ} (hrt : r < t) (hα : 0 < α) (hβ : 0 < β) :
    ∫ s in r..t, (t - s) ^ (α - 1) * (s - r) ^ (β - 1) =
      (t - r) ^ (α + β - 1) *
        ∫ v in (0 : ℝ)..1, v ^ (β - 1) * (1 - v) ^ (α - 1) := by
  let c := t - r
  have hc : 0 < c := sub_pos.mpr hrt
  let g : ℝ → ℝ := fun s => (t - s) ^ (α - 1) * (s - r) ^ (β - 1)
  have hsub : c * ∫ v in (0 : ℝ)..1, g (r + c * v) = ∫ s in r..t, g s := by
    simpa [g, c, zero_add, mul_zero, add_zero, mul_one, sub_add_cancel] using
      (smul_integral_comp_add_mul (f := g) (a := (0 : ℝ)) (b := 1) c r)
  rw [← hsub]
  have hpt : EqOn (fun v => g (r + c * v))
      (fun v => c ^ (α + β - 2) * (v ^ (β - 1) * (1 - v) ^ (α - 1))) (uIcc 0 1) := by
    intro v hv
    rw [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hv
    have hv0 : 0 ≤ v := hv.1
    have hv1 : v ≤ 1 := hv.2
    have h1v : 0 ≤ 1 - v := sub_nonneg.mpr hv1
    have hts : t - (r + c * v) = c * (1 - v) := by
      dsimp [c]
      ring
    have hsr : r + c * v - r = c * v := by ring
    simp only [g]
    rw [hts, hsr, mul_rpow hc.le h1v, mul_rpow hc.le hv0]
    have hcadd : c ^ (α - 1) * c ^ (β - 1) = c ^ (α + β - 2) := by
      rw [← rpow_add hc]
      ring_nf
    calc
      c ^ (α - 1) * (1 - v) ^ (α - 1) * (c ^ (β - 1) * v ^ (β - 1))
          = c ^ (α - 1) * c ^ (β - 1) * (v ^ (β - 1) * (1 - v) ^ (α - 1)) := by ring
      _ = c ^ (α + β - 2) * (v ^ (β - 1) * (1 - v) ^ (α - 1)) := by rw [hcadd]
  rw [integral_congr hpt, intervalIntegral.integral_const_mul]
  have hcpow : c * c ^ (α + β - 2) = c ^ (α + β - 1) := by
    rw [mul_comm, ← rpow_add_one hc.ne']
    ring_nf
  rw [← mul_assoc, hcpow]

/-- The beta evaluation of the scaled kernel. -/
private lemma integral_betaKernel_beta {t r α β : ℝ} (hrt : r < t) (hα : 0 < α) (hβ : 0 < β) :
    ∫ s in r..t, (t - s) ^ (α - 1) * (s - r) ^ (β - 1) =
      (t - r) ^ (α + β - 1) * ProbabilityTheory.beta β α := by
  rw [integral_betaKernel hrt hα hβ, TauCeti.integral_rpow_mul_one_sub_rpow hβ hα]

/-- The Gamma quotient carried by the beta function cancels the two normalizing constants. -/
private lemma gamma_beta_factor {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (Gamma α)⁻¹ * (Gamma β)⁻¹ * ProbabilityTheory.beta β α = (Gamma (α + β))⁻¹ := by
  have hα' : Gamma α ≠ 0 := (Gamma_pos_of_pos hα).ne'
  have hβ' : Gamma β ≠ 0 := (Gamma_pos_of_pos hβ).ne'
  have hs : Gamma (α + β) ≠ 0 := (Gamma_pos_of_pos (add_pos hα hβ)).ne'
  simp only [ProbabilityTheory.beta, add_comm β α]
  field_simp

/-- Absolute values of an integrable density, cut off outside `(0, T)`. -/
private def absCut (T : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  indicator (Ioo 0 T) fun s => |u s|

/-- The cutoff of an integrable function is integrable on the line. -/
private lemma integrable_absCut {T : ℝ} {u : ℝ → ℝ} (hu : IntegrableOn u (Ioo 0 T)) :
    Integrable (absCut T u) := by
  simpa [absCut, Real.norm_eq_abs] using
    IntegrableOn.integrable_indicator (Integrable.norm hu) measurableSet_Ioo

/-- The cutoff is nonnegative. -/
private lemma absCut_nonneg (T : ℝ) (u : ℝ → ℝ) (s : ℝ) : 0 ≤ absCut T u s := by
  unfold absCut
  simp only [indicator_apply]
  split_ifs <;> positivity

/-- Joint integrand of `kernelPow (γ - 1) (t - s)` against the cutoff density on `0 < s < t < T`. -/
private def kernelProd (T γ : ℝ) (u : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => if p.2 < p.1 ∧ 0 < p.1 ∧ p.1 < T then
    kernelPow (γ - 1) (p.1 - p.2) * absCut T u p.2 else 0

/-- The joint kernel is nonnegative. -/
private lemma kernelProd_nonneg (T γ : ℝ) (u : ℝ → ℝ) (p : ℝ × ℝ) : 0 ≤ kernelProd T γ u p := by
  unfold kernelProd
  by_cases hp : p.2 < p.1 ∧ 0 < p.1 ∧ p.1 < T
  · simp only [hp, true_and, and_true, ↓reduceIte]
    exact mul_nonneg (kernelPow_nonneg _ _) (absCut_nonneg T u _)
  · simp only [hp, true_and, and_true, ↓reduceIte]
    exact le_rfl

/-- The joint kernel against a cutoff density is integrable on the half-square `0 < s < t < T`. -/
private lemma integrable_kernel_prod {T γ : ℝ} (hT : 0 < T) (hγ : 0 < γ) {u : ℝ → ℝ}
    (hu : IntegrableOn u (Ioo 0 T)) : Integrable (kernelProd T γ u) (volume.prod volume) := by
  let v := absCut T u
  have hv : Integrable v := integrable_absCut hu
  let F : ℝ × ℝ → ℝ := fun p =>
    (if p.2 < p.1 ∧ 0 < p.1 ∧ p.1 < T then kernelPow (γ - 1) (p.1 - p.2) else 0) * v p.2
  have hEq : kernelProd T γ u = F := by
    ext p
    by_cases hp : p.2 < p.1 ∧ 0 < p.1 ∧ p.1 < T
    · simp only [kernelProd, F, v, hp, ↓reduceIte]
      rfl
    · simp only [kernelProd, F, hp, ↓reduceIte, zero_mul]
  rw [hEq]
  have hFmeas : AEStronglyMeasurable F (volume.prod volume) := by
    refine AEStronglyMeasurable.mul ?_ hv.aestronglyMeasurable.comp_snd
    refine Measurable.aestronglyMeasurable ?_
    refine Measurable.ite ?_ ((measurable_kernelPow _).comp (measurable_fst.sub measurable_snd))
      measurable_const
    exact (measurableSet_lt measurable_snd measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_fst measurable_const))
  have hFnn : ∀ p, 0 ≤ F p := by
    intro p
    by_cases hp : p.2 < p.1 ∧ 0 < p.1 ∧ p.1 < T
    · simp only [F, hp, true_and, and_true, ↓reduceIte]
      exact mul_nonneg (kernelPow_nonneg _ _) (absCut_nonneg T u _)
    · simp only [F, hp, true_and, and_true, ↓reduceIte, zero_mul]
      exact le_rfl
  have hAE : AEMeasurable (fun p => ENNReal.ofReal (F p)) (volume.prod volume) :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable hFmeas.aemeasurable
  have hswap := lintegral_prod_symm (fun p => ENNReal.ofReal (F p)) hAE
  have hinner : ∀ s, ∫⁻ t, ENNReal.ofReal (F (t, s)) =
      ENNReal.ofReal (v s * (T - s) ^ γ / γ) := by
    intro s
    by_cases hvs : v s = 0
    · have h0 : ∀ t, F (t, s) = 0 := fun t => by simp only [F, hvs, mul_zero]
      simp only [h0, ENNReal.ofReal_zero, lintegral_zero, hvs, zero_div, zero_mul]
    · have hsI : s ∈ Ioo 0 T := by
        by_contra hs
        exact hvs (by simp only [v, absCut, indicator_of_notMem hs])
      have hs0 : 0 < s := hsI.1
      have hsT : s < T := hsI.2
      have hpt : ∀ t, ENNReal.ofReal (F (t, s)) =
          indicator (Ioo s T) (fun t => ENNReal.ofReal (kernelPow (γ - 1) (t - s) * v s)) t := by
        intro t
        by_cases ht : t ∈ Ioo s T
        · have hts : s < t := ht.1
          have htT : t < T := ht.2
          have ht0 : 0 < t := hs0.trans hts
          have hcond : s < t ∧ 0 < t ∧ t < T := ⟨hts, ht0, htT⟩
          simp only [F, hcond, true_and, and_true, ↓reduceIte, indicator_of_mem ht]
        · have hF0 : F (t, s) = 0 := by
            by_cases hcond : s < t ∧ 0 < t ∧ t < T
            · exact absurd ⟨hcond.1, hcond.2.2⟩ ht
            · simp only [F, hcond, true_and, and_true, ↓reduceIte, zero_mul]
          rw [hF0, ENNReal.ofReal_zero, indicator_of_notMem ht]
      rw [lintegral_congr hpt, lintegral_indicator measurableSet_Ioo]
      have hpow : EqOn (fun t => ENNReal.ofReal (kernelPow (γ - 1) (t - s) * v s))
          (fun t => ENNReal.ofReal ((t - s) ^ (γ - 1) * v s)) (Ioo s T) := by
        intro t ht
        dsimp only
        rw [kernelPow_eq_rpow (sub_pos.mpr ht.1)]
      rw [setLIntegral_congr_fun measurableSet_Ioo hpow]
      have hfac : EqOn (fun t => ENNReal.ofReal ((t - s) ^ (γ - 1) * v s))
          (fun t => ENNReal.ofReal (v s) * ENNReal.ofReal ((t - s) ^ (γ - 1))) (Ioo s T) := by
        intro t ht
        dsimp only
        have hbase : 0 ≤ t - s := (sub_pos.mpr ht.1).le
        rw [ENNReal.ofReal_mul (rpow_nonneg hbase _), mul_comm]
      rw [setLIntegral_congr_fun measurableSet_Ioo hfac,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioo_sub_rpow hsT hγ]
      rw [← ENNReal.ofReal_mul (absCut_nonneg T u s), mul_div_assoc]
  have hle : ∫⁻ s, ENNReal.ofReal (v s * (T - s) ^ γ / γ) ≤
      ENNReal.ofReal (T ^ γ / γ) * ∫⁻ s, ENNReal.ofReal (v s) := by
    have hpt : ∀ s, ENNReal.ofReal (v s * (T - s) ^ γ / γ) ≤
        ENNReal.ofReal (T ^ γ / γ) * ENNReal.ofReal (v s) := by
      intro s
      by_cases hvs : v s = 0
      · simp only [hvs, zero_mul, zero_div, ENNReal.ofReal_zero, mul_zero]
        exact le_rfl
      · have hsI : s ∈ Ioo 0 T := by
          by_contra hs
          exact hvs (by simp only [v, absCut, indicator_of_notMem hs])
        have hTs0 : 0 ≤ T - s := sub_nonneg.mpr hsI.2.le
        have hTs : T - s ≤ T := sub_le_self T hsI.1.le
        have hpow : (T - s) ^ γ ≤ T ^ γ := rpow_le_rpow hTs0 hTs hγ.le
        have hdiv : (T - s) ^ γ / γ ≤ T ^ γ / γ := div_le_div_of_nonneg_right hpow hγ.le
        calc
          ENNReal.ofReal (v s * (T - s) ^ γ / γ)
              = ENNReal.ofReal (v s) * ENNReal.ofReal ((T - s) ^ γ / γ) := by
                rw [← ENNReal.ofReal_mul (absCut_nonneg T u s), mul_div_assoc]
          _ ≤ ENNReal.ofReal (v s) * ENNReal.ofReal (T ^ γ / γ) :=
                mul_le_mul_right (ENNReal.ofReal_le_ofReal hdiv) _
          _ = ENNReal.ofReal (T ^ γ / γ) * ENNReal.ofReal (v s) := mul_comm _ _
    calc
      ∫⁻ s, ENNReal.ofReal (v s * (T - s) ^ γ / γ)
          ≤ ∫⁻ s, ENNReal.ofReal (T ^ γ / γ) * ENNReal.ofReal (v s) := lintegral_mono hpt
      _ = ENNReal.ofReal (T ^ γ / γ) * ∫⁻ s, ENNReal.ofReal (v s) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hvnn : 0 ≤ᵐ[volume] v := ae_of_all _ (absCut_nonneg T u)
  have hvint : ∫⁻ s, ENNReal.ofReal (v s) = ENNReal.ofReal (∫ s, v s) :=
    (ofReal_integral_eq_lintegral_ofReal hv hvnn).symm
  have hfin : ∫⁻ p, ENNReal.ofReal (F p) ∂volume.prod volume < ⊤ := by
    rw [hswap]
    simp_rw [hinner]
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
      rw [hvint]; exact ENNReal.ofReal_lt_top))
  have hfi : HasFiniteIntegral F (volume.prod volume) :=
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hFnn)).2 hfin
  exact ⟨hFmeas, hfi⟩

/-- Off the right endpoint, `kernelPow` and real exponentiation have the same integral. -/
private lemma integral_kernelPow_eq {t γ : ℝ} (ht : 0 ≤ t) (f : ℝ → ℝ) :
    ∫ s in (0 : ℝ)..t, kernelPow (γ - 1) (t - s) * f s =
      ∫ s in (0 : ℝ)..t, (t - s) ^ (γ - 1) * f s := by
  refine integral_congr_Ioo_of_le ht ?_
  intro s hs
  dsimp only
  rw [kernelPow_eq_rpow (sub_pos.mpr hs.2)]

/-- At height `t ∈ (0, T)`, the joint kernel is the cutoff power times `|u|`. -/
private lemma kernelProd_apply {T γ : ℝ} {u : ℝ → ℝ} {t s : ℝ} (ht0 : 0 < t) (htT : t < T) :
    kernelProd T γ u (t, s) =
      if s < t ∧ 0 < s then kernelPow (γ - 1) (t - s) * |u s| else 0 := by
  by_cases hst : s < t ∧ 0 < s
  · have hcond : s < t ∧ 0 < t ∧ t < T := ⟨hst.1, ht0, htT⟩
    have hmem : s ∈ Ioo 0 T := ⟨hst.2, hst.1.trans htT⟩
    simp only [kernelProd, hcond, hst, true_and, and_true, ↓reduceIte, absCut,
      indicator_of_mem hmem]
  · have hzero : kernelProd T γ u (t, s) = 0 := by
      by_cases hcond : s < t ∧ 0 < t ∧ t < T
      · have hnot : s ∉ Ioo 0 T := by
          intro hs
          exact hst ⟨hcond.1, hs.1⟩
        simp only [kernelProd, hcond, true_and, and_true, ↓reduceIte, absCut,
          indicator_of_notMem hnot, mul_zero]
      · simp only [kernelProd, hcond, true_and, and_true, ↓reduceIte]
    simp only [hzero, hst, true_and, and_true, ↓reduceIte]

/-- Inner integral of the joint kernel. -/
private def kernelSlice (T γ : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun t => ∫ s, kernelProd T γ u (t, s)

/-- The slice integral is integrable on the line. -/
private lemma kernelSlice_integrable {T γ : ℝ} (hT : 0 < T) (hγ : 0 < γ) {u : ℝ → ℝ}
    (hu : IntegrableOn u (Ioo 0 T)) : Integrable (kernelSlice T γ u) :=
  (integrable_kernel_prod hT hγ hu).integral_prod_left

/-- The slice integral is nonnegative. -/
private lemma kernelSlice_nonneg (T γ : ℝ) (u : ℝ → ℝ) (t : ℝ) : 0 ≤ kernelSlice T γ u t :=
  MeasureTheory.integral_nonneg fun s => kernelProd_nonneg T γ u (t, s)

/-- Inside `(0, T)`, the slice is the integral of `kernelPow` against `|u|`. -/
private lemma kernelSlice_eq_kernelPow {T γ : ℝ} {u : ℝ → ℝ} {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    kernelSlice T γ u t = ∫ s in (0 : ℝ)..t, kernelPow (γ - 1) (t - s) * |u s| := by
  have hpt : ∀ s, kernelProd T γ u (t, s) =
      indicator (Ioc 0 t) (fun s => kernelPow (γ - 1) (t - s) * |u s|) s := by
    intro s
    rw [kernelProd_apply ht0 htT]
    by_cases hs : s ∈ Ioc 0 t
    · by_cases hlt : s < t
      · simp only [hlt, hs.1, true_and, true_and, and_true, ↓reduceIte, indicator_of_mem hs]
      · have hseq : s = t := le_antisymm hs.2 (le_of_not_gt hlt)
        have htmem : t ∈ Ioc 0 t := hseq ▸ hs
        simp only [hseq, lt_irrefl, false_and, ↓reduceIte]
        rw [indicator_of_mem htmem]
        simp only [kernelPow, sub_self, lt_irrefl, ↓reduceIte, zero_mul]
    · have hif : ¬ (s < t ∧ 0 < s) := fun h => hs ⟨h.2, h.1.le⟩
      simp only [hif, true_and, and_true, ↓reduceIte, indicator_of_notMem hs]
  rw [kernelSlice, MeasureTheory.integral_congr_ae (ae_of_all _ hpt),
    MeasureTheory.integral_indicator measurableSet_Ioc, ← integral_of_le ht0.le]

/-- Inside `(0, T)`, the slice is the fractional kernel of `|u|`. -/
private lemma kernelSlice_eq_rawAbs {T γ : ℝ} {u : ℝ → ℝ} {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    kernelSlice T γ u t = ∫ s in (0 : ℝ)..t, (t - s) ^ (γ - 1) * |u s| := by
  rw [kernelSlice_eq_kernelPow ht0 htT, integral_kernelPow_eq ht0.le]

/-- For almost every upper limit in `(0, T)`, the fractional kernel of an integrable density is
interval integrable. -/
private lemma ae_intervalIntegrable_pow {T γ : ℝ} (hT : 0 < T) (hγ : 0 < γ) {u : ℝ → ℝ}
    (hu : IntegrableOn u (Ioo 0 T)) :
    ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      IntervalIntegrable (fun s => (t - s) ^ (γ - 1) * u s) volume 0 t := by
  have hae := (integrable_kernel_prod hT hγ hu).prod_right_ae
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [hae] with t ht htI
  have ht0 : 0 < t := htI.1
  have htT : t < T := htI.2
  let φ : ℝ → ℝ := fun s => kernelPow (γ - 1) (t - s) * u s
  have hu_t : AEStronglyMeasurable u (volume.restrict (Ioc 0 t)) := by
    have hsub : Ioo 0 t ⊆ Ioo 0 T := Ioo_subset_Ioo le_rfl htT.le
    have huoo : IntegrableOn u (Ioo 0 t) := hu.mono_set hsub
    exact ((integrableOn_congr_set_ae (Ioo_ae_eq_Ioc (μ := volume))).1
      huoo).aestronglyMeasurable
  have hφmeas : AEStronglyMeasurable φ (volume.restrict (Ioc 0 t)) :=
    ((measurable_kernelPow _).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable.mul hu_t
  have habs : IntegrableOn (fun s => |φ s|) (Ioc 0 t) := by
    have hF : IntegrableOn (fun s => kernelProd T γ u (t, s)) (Ioc 0 t) := ht.integrableOn
    refine hF.congr_fun ?_ measurableSet_Ioc
    intro s hs
    dsimp only
    rw [kernelProd_apply ht0 htT]
    dsimp only [φ]
    by_cases hlt : s < t
    · simp only [φ, hlt, hs.1, true_and, true_and, and_true, ↓reduceIte, abs_mul,
        abs_of_nonneg (kernelPow_nonneg _ _)]
    · have hseq : s = t := le_antisymm hs.2 (le_of_not_gt hlt)
      simp only [φ, hseq, kernelPow, sub_self, lt_irrefl, false_and, true_and, and_true,
        ↓reduceIte, zero_mul, abs_zero]
  have hφ : IntegrableOn φ (Ioc 0 t) :=
    Integrable.mono habs.integrable hφmeas <| ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
  have hI : IntervalIntegrable φ volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le).2 hφ
  refine hI.congr_uIoo ?_
  intro s hs
  rw [uIoo_of_le ht0.le] at hs
  dsimp only [φ]
  rw [kernelPow_eq_rpow (sub_pos.mpr hs.2)]

/-- Signed kernel on the triangle `0 < s < t < T`. -/
private def kernelSigned (T γ : ℝ) (u : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => if p.2 < p.1 ∧ 0 < p.2 ∧ p.1 < T then
    kernelPow (γ - 1) (p.1 - p.2) * u p.2 else 0

/-- The signed kernel is integrable when the density is integrable on `(0, T)`. -/
private lemma integrable_kernelSigned {T γ : ℝ} (hT : 0 < T) (hγ : 0 < γ) {u : ℝ → ℝ}
    (hu : IntegrableOn u (Ioo 0 T)) :
    Integrable (kernelSigned T γ u) (volume.prod volume) := by
  let u0 := indicator (Ioo 0 T) u
  have hu0 : Integrable u0 := hu.integrable_indicator measurableSet_Ioo
  let S : ℝ × ℝ → ℝ := fun p =>
    (if p.2 < p.1 ∧ 0 < p.2 ∧ p.1 < T then kernelPow (γ - 1) (p.1 - p.2) else 0) * u0 p.2
  have hSmeas : AEStronglyMeasurable S (volume.prod volume) := by
    refine AEStronglyMeasurable.mul ?_ hu0.aestronglyMeasurable.comp_snd
    refine Measurable.aestronglyMeasurable ?_
    refine Measurable.ite ?_ ((measurable_kernelPow _).comp (measurable_fst.sub measurable_snd))
      measurable_const
    exact (measurableSet_lt measurable_snd measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_fst measurable_const))
  have hdom : ∀ p, ‖S p‖ ≤ ‖kernelProd T γ u p‖ := by
    intro p
    by_cases hp : p.2 < p.1 ∧ 0 < p.2 ∧ p.1 < T
    · have hmem : p.2 ∈ Ioo 0 T := ⟨hp.2.1, hp.1.trans hp.2.2⟩
      have hp1 : p.2 < p.1 ∧ 0 < p.1 ∧ p.1 < T := ⟨hp.1, hp.2.1.trans hp.1, hp.2.2⟩
      have hS : S p = kernelPow (γ - 1) (p.1 - p.2) * u p.2 := by
        simp only [S, hp, true_and, and_true, ↓reduceIte, u0, indicator_of_mem hmem]
      have hK : kernelProd T γ u p =
          kernelPow (γ - 1) (p.1 - p.2) * |u p.2| := by
        simp only [kernelProd, hp1, true_and, and_true, ↓reduceIte, absCut,
          indicator_of_mem hmem]
      rw [hS, hK, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (kernelPow_nonneg _ _), abs_abs]
    · simp only [S, hp, true_and, and_true, ↓reduceIte, zero_mul, norm_zero]
      exact norm_nonneg _
  have hS : Integrable S := (integrable_kernel_prod hT hγ hu).mono hSmeas (ae_of_all _ hdom)
  refine hS.congr (ae_of_all _ fun p => ?_)
  by_cases hp : p.2 < p.1 ∧ 0 < p.2 ∧ p.1 < T
  · have hmem : p.2 ∈ Ioo 0 T := ⟨hp.2.1, hp.1.trans hp.2.2⟩
    simp only [kernelSigned, S, hp, true_and, and_true, ↓reduceIte, u0, indicator_of_mem hmem]
  · simp only [kernelSigned, S, hp, true_and, and_true, ↓reduceIte, zero_mul]

/-- Inner integral of the signed kernel. -/
private def kernelSliceSigned (T γ : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun t => ∫ s, kernelSigned T γ u (t, s)

/-- The signed slice is integrable on the line. -/
private lemma kernelSliceSigned_integrable {T γ : ℝ} (hT : 0 < T) (hγ : 0 < γ) {u : ℝ → ℝ}
    (hu : IntegrableOn u (Ioo 0 T)) : Integrable (kernelSliceSigned T γ u) :=
  (integrable_kernelSigned hT hγ hu).integral_prod_left

/-- Inside `(0, T)`, the signed slice is the un-normalized fractional integral. -/
private lemma kernelSliceSigned_eq {T γ : ℝ} {u : ℝ → ℝ} {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    kernelSliceSigned T γ u t = ∫ s in (0 : ℝ)..t, (t - s) ^ (γ - 1) * u s := by
  have hpt : ∀ s, kernelSigned T γ u (t, s) =
      indicator (Ioc 0 t) (fun s => kernelPow (γ - 1) (t - s) * u s) s := by
    intro s
    by_cases hs : s ∈ Ioc 0 t
    · by_cases hlt : s < t
      · have hcond : s < t ∧ 0 < s ∧ t < T := ⟨hlt, hs.1, htT⟩
        simp only [kernelSigned, hcond, true_and, and_true, ↓reduceIte, indicator_of_mem hs]
      · have hseq : s = t := le_antisymm hs.2 (le_of_not_gt hlt)
        have htmem : t ∈ Ioc 0 t := hseq ▸ hs
        simp only [kernelSigned, hseq, lt_irrefl, false_and, ↓reduceIte]
        rw [indicator_of_mem htmem]
        simp only [kernelPow, sub_self, lt_irrefl, ↓reduceIte, zero_mul]
    · have hif : ¬ (s < t ∧ 0 < s ∧ t < T) := fun h => hs ⟨h.2.1, h.1.le⟩
      simp only [kernelSigned, hif, true_and, and_true, ↓reduceIte, indicator_of_notMem hs]
  rw [kernelSliceSigned, MeasureTheory.integral_congr_ae (ae_of_all _ hpt),
    MeasureTheory.integral_indicator measurableSet_Ioc, ← integral_of_le ht0.le,
    integral_kernelPow_eq ht0.le]

/-- A fractional integral of an `L¹` density stays in `L¹(0, T)`. -/
private lemma integrableOn_fractionalIntegral {T α : ℝ} (hT : 0 < T) (hα : 0 < α) {u : ℝ → ℝ}
    (hu : IntegrableOn u (Ioo 0 T)) : IntegrableOn (fractionalIntegral α u) (Ioo 0 T) := by
  have hint := kernelSliceSigned_integrable hT hα hu
  have hEq : EqOn (fun t => (Gamma α)⁻¹ * kernelSliceSigned T α u t) (fractionalIntegral α u)
      (Ioo 0 T) := by
    intro t ht
    dsimp only
    rw [fractionalIntegral, kernelSliceSigned_eq ht.1 ht.2]
  refine ((hint.smul (Gamma α)⁻¹).integrableOn).congr_fun ?_ measurableSet_Ioo
  intro t ht
  rw [Pi.smul_apply, smul_eq_mul]
  exact hEq ht

/-- Order `1` is ordinary integration from `0`. -/
private lemma fractionalIntegral_one {u : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    fractionalIntegral 1 u t = ∫ s in (0 : ℝ)..t, u s := by
  rw [fractionalIntegral, Gamma_one, inv_one, one_mul]
  refine integral_congr fun s _ => ?_
  rw [sub_self, rpow_zero, one_mul]

/-- The fractional integral of zero vanishes. -/
private lemma fractionalIntegral_zero (α t : ℝ) : fractionalIntegral α (fun _ : ℝ => 0) t = 0 := by
  simp [fractionalIntegral, integral_zero]

/-- Fractional integrals do not see values outside `(0, T)`, up to a null set. -/
private lemma fractionalIntegral_congr {T α : ℝ} {u v : ℝ → ℝ}
    (h : u =ᵐ[volume.restrict (Ioo 0 T)] v) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    fractionalIntegral α u t = fractionalIntegral α v t := by
  rw [fractionalIntegral, fractionalIntegral]
  congr 1
  rw [integral_of_le ht0, integral_of_le ht0, integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  refine (ae_restrict_iff' measurableSet_Ioo).1 ?_
  exact (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl htT) h).mono
    fun s hs => by rw [hs]

/-- Subtraction passes inside a fractional integral, almost everywhere on `(0, T)`. -/
private lemma fractionalIntegral_sub_ae {T α : ℝ} (hT : 0 < T) (hα : 0 < α) {u v : ℝ → ℝ}
    (hu : IntegrableOn u (Ioo 0 T)) (hv : IntegrableOn v (Ioo 0 T)) :
    fractionalIntegral α (fun x => u x - v x) =ᵐ[volume.restrict (Ioo 0 T)]
      fun t => fractionalIntegral α u t - fractionalIntegral α v t := by
  have huI := ae_intervalIntegrable_pow hT hα hu
  have hvI := ae_intervalIntegrable_pow hT hα hv
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 huI,
    (ae_restrict_iff' measurableSet_Ioo).1 hvI] with t htu htv htI
  rw [fractionalIntegral, fractionalIntegral, fractionalIntegral, ← mul_sub]
  congr 1
  have hsub : ∫ s in (0 : ℝ)..t, (t - s) ^ (α - 1) * (u s - v s) =
      (∫ s in (0 : ℝ)..t, (t - s) ^ (α - 1) * u s) -
        ∫ s in (0 : ℝ)..t, (t - s) ^ (α - 1) * v s := by
    rw [← intervalIntegral.integral_sub (htu htI) (htv htI)]
    refine integral_congr fun s _ => ?_
    ring
  exact hsub

/-- The iterated kernels multiply by the beta constant, almost everywhere on `(0, T)`. -/
private lemma rawFractional_comm {T α β : ℝ} (hT : 0 < T) (hα : 0 < α) (hβ : 0 < β)
    {u : ℝ → ℝ} (hu : IntegrableOn u (Ioo 0 T)) :
    (fun t => ∫ r in (0 : ℝ)..t, (t - r) ^ (α - 1) *
        ∫ s in (0 : ℝ)..r, (r - s) ^ (β - 1) * u s) =ᵐ[volume.restrict (Ioo 0 T)]
      fun t => ProbabilityTheory.beta β α *
        ∫ s in (0 : ℝ)..t, (t - s) ^ (α + β - 1) * u s := by
  let w := kernelSlice T β u
  have hw : IntegrableOn w (Ioo 0 T) := (kernelSlice_integrable hT hβ hu).integrableOn
  have houter := (integrable_kernel_prod hT hα hw).prod_right_ae
  have hinner := ae_intervalIntegrable_pow hT hβ hu
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [houter] with t htOut htI
  have ht0 : 0 < t := htI.1
  have htT : t < T := htI.2
  let u0 := indicator (Ioo 0 T) u
  have hu0 : Integrable u0 := hu.integrable_indicator measurableSet_Ioo
  let Ψ : ℝ × ℝ → ℝ := fun p =>
    (if p.2 < p.1 then kernelPow (β - 1) (p.1 - p.2) * u0 p.2 else 0) *
      kernelPow (α - 1) (t - p.1)
  have hASM0 : AEStronglyMeasurable Ψ (volume.prod volume) := by
    have hcut : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        if p.2 < p.1 then kernelPow (β - 1) (p.1 - p.2) else (0 : ℝ)) (volume.prod volume) := by
      refine Measurable.aestronglyMeasurable ?_
      refine Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
        ((measurable_kernelPow _).comp (measurable_fst.sub measurable_snd)) measurable_const
    have hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => kernelPow (α - 1) (t - p.1))
        (volume.prod volume) :=
      ((measurable_kernelPow _).comp
        (measurable_const.sub measurable_fst)).aestronglyMeasurable
    have hΨ : Ψ = fun p =>
        (if p.2 < p.1 then kernelPow (β - 1) (p.1 - p.2) else 0) * u0 p.2 *
          kernelPow (α - 1) (t - p.1) := by
      ext p
      by_cases hp : p.2 < p.1
      · simp only [Ψ, hp, ↓reduceIte]
      · simp only [Ψ, hp, ↓reduceIte, zero_mul]
    rw [hΨ]
    exact (hcut.mul hu0.aestronglyMeasurable.comp_snd).mul hpow
  have hle : (volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t)) ≤ volume.prod volume := by
    rw [Measure.prod_restrict]
    exact Measure.restrict_le_self
  have hASM : AEStronglyMeasurable Ψ
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) := hASM0.mono_measure hle
  have hsubI : Ioc 0 t ⊆ Ioo 0 T := fun s hs => ⟨hs.1, hs.2.trans_lt htT⟩
  have hinn : ∀ᵐ r ∂volume.restrict (Ioc 0 t),
      IntervalIntegrable (fun s => (r - s) ^ (β - 1) * u s) volume 0 r :=
    ae_restrict_of_ae_restrict_of_subset hsubI hinner
  have hslice : ∀ᵐ r ∂volume.restrict (Ioc 0 t),
      Integrable (fun s => Ψ (r, s)) (volume.restrict (Ioc 0 t)) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 hinn] with r hr hrI
    by_cases hrt : r < t
    · have hr0 : 0 < r := hrI.1
      have hker : IntervalIntegrable (fun s => kernelPow (β - 1) (r - s) * u s) volume 0 r := by
        refine (hr hrI).congr_uIoo ?_
        intro s hs
        rw [uIoo_of_le hr0.le] at hs
        dsimp only
        rw [← kernelPow_eq_rpow (sub_pos.mpr hs.2)]
      have hkerOn : IntegrableOn (fun s => kernelPow (β - 1) (r - s) * u s) (Ioc 0 r) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hr0.le).1 hker
      let f : ℝ → ℝ := fun s => if s < r then kernelPow (β - 1) (r - s) * u s else 0
      have hf : IntegrableOn f (Ioc 0 t) := by
        have hind : Integrable (indicator (Ioc 0 r)
            (fun s => kernelPow (β - 1) (r - s) * u s)) :=
          hkerOn.integrable_indicator measurableSet_Ioc
        refine hind.integrableOn.congr_fun ?_ measurableSet_Ioc
        intro s hs
        by_cases hsr : s < r
        · have hsR : s ∈ Ioc 0 r := ⟨hs.1, hsr.le⟩
          simp only [f, hsr, true_and, and_true, ↓reduceIte, indicator_of_mem hsR]
        · have hge : r ≤ s := le_of_not_gt hsr
          have hzero_f : f s = 0 := by simp only [f, hsr, true_and, and_true, ↓reduceIte]
          have hzero_ind : indicator (Ioc 0 r)
              (fun s => kernelPow (β - 1) (r - s) * u s) s = 0 := by
            by_cases hsR : s ∈ Ioc 0 r
            · have hseq : s = r := le_antisymm hsR.2 hge
              rw [indicator_of_mem hsR]
              simp only [hseq, kernelPow, sub_self, lt_irrefl, ↓reduceIte, zero_mul]
            · simp only [indicator_of_notMem hsR]
          rw [hzero_f, hzero_ind]
      have hconst : IntegrableOn (fun s => kernelPow (α - 1) (t - r) * f s) (Ioc 0 t) :=
        hf.smul (kernelPow (α - 1) (t - r))
      refine hconst.congr_fun ?_ measurableSet_Ioc
      intro s hs
      have hsU : s ∈ Ioo 0 T := ⟨hs.1, hs.2.trans_lt htT⟩
      simp only [Ψ, u0, indicator_of_mem hsU, f, smul_eq_mul]
      ring
    · have hseq : r = t := le_antisymm hrI.2 (le_of_not_gt hrt)
      have h0 : (fun s => Ψ (r, s)) = fun _ => (0 : ℝ) := by
        ext s
        simp only [Ψ, hseq, kernelPow, sub_self, lt_irrefl, true_and, and_true,
          ↓reduceIte, mul_zero]
      rw [h0]
      exact integrable_zero _ _ _
  have hnorm_eq : ∀ r ∈ Ioc 0 t,
      ∫ s, ‖Ψ (r, s)‖ ∂volume.restrict (Ioc 0 t) = kernelProd T α w (t, r) := by
    intro r hr
    have hr0 : 0 < r := hr.1
    by_cases hlt : r < t
    · have hc : 0 ≤ kernelPow (α - 1) (t - r) := kernelPow_nonneg _ _
      have habs_int : ∫ s in (0 : ℝ)..t, ‖Ψ (r, s)‖ =
          kernelPow (α - 1) (t - r) *
            ∫ s in (0 : ℝ)..r, kernelPow (β - 1) (r - s) * |u s| := by
        have hcongr : ∫ s in (0 : ℝ)..t, ‖Ψ (r, s)‖ =
            ∫ s in (0 : ℝ)..t, kernelPow (α - 1) (t - r) *
              (if s < r then kernelPow (β - 1) (r - s) * |u s| else 0) := by
          refine integral_congr_Ioo_of_le ht0.le ?_
          intro s hs
          dsimp only
          have hsU : s ∈ Ioo 0 T := ⟨hs.1, hs.2.trans htT⟩
          rw [show Ψ (r, s) = (if s < r then kernelPow (β - 1) (r - s) * u s else 0) *
              kernelPow (α - 1) (t - r) by simp only [Ψ, u0, indicator_of_mem hsU]]
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, mul_comm]
          by_cases hsr : s < r
          · simp only [hsr, true_and, and_true, ↓reduceIte, abs_mul,
              abs_of_nonneg (kernelPow_nonneg _ _)]
          · simp only [hsr, ↓reduceIte, abs_zero, mul_zero]
        rw [hcongr, intervalIntegral.integral_const_mul,
          ← integral_of_lt_indicator hr0.le hlt.le
            (fun s => kernelPow (β - 1) (r - s) * |u s|)]
      rw [← integral_of_le ht0.le, habs_int,
        ← kernelSlice_eq_kernelPow hr0 (hlt.trans htT)]
      have hrI : r ∈ Ioo 0 T := ⟨hr0, hlt.trans htT⟩
      have hcond : r < t ∧ 0 < t ∧ t < T := ⟨hlt, ht0, htT⟩
      simp only [w, kernelProd, hcond, true_and, and_true, ↓reduceIte, absCut,
        indicator_of_mem hrI]
      rw [abs_of_nonneg (kernelSlice_nonneg T β u r)]
    · have hseq : r = t := le_antisymm hr.2 (le_of_not_gt hlt)
      have hzero : ∀ s, Ψ (r, s) = 0 := by
        intro s
        simp only [Ψ, hseq, kernelPow, sub_self, lt_irrefl, true_and, and_true,
          ↓reduceIte, mul_zero]
      have hprod : kernelProd T α w (t, r) = 0 := by
        simp only [kernelProd, hseq, lt_irrefl, false_and, true_and, and_true, ↓reduceIte]
      rw [hprod]
      simp only [hzero, norm_zero, MeasureTheory.integral_zero]
  have hnorm : Integrable (fun r => ∫ s, ‖Ψ (r, s)‖ ∂volume.restrict (Ioc 0 t))
      (volume.restrict (Ioc 0 t)) := by
    refine htOut.integrableOn.congr_fun ?_ measurableSet_Ioc
    intro r hr
    exact (hnorm_eq r hr).symm
  have hprod : Integrable Ψ
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) :=
    (integrable_prod_iff hASM).2 ⟨hslice, hnorm⟩
  let G : ℝ → ℝ → ℝ := fun r s =>
    (if s < r then kernelPow (β - 1) (r - s) * u s else 0) * kernelPow (α - 1) (t - r)
  have hOn : IntegrableOn G.uncurry (uIoc 0 t ×ˢ uIoc 0 t) := by
    rw [uIoc_of_le ht0.le]
    refine (show IntegrableOn Ψ (Ioc 0 t ×ˢ Ioc 0 t) by
      simpa [IntegrableOn, Measure.prod_restrict, Measure.volume_eq_prod] using
        hprod).congr_fun ?_ (measurableSet_Ioc.prod measurableSet_Ioc)
    intro p hp
    have hsU : p.2 ∈ Ioo 0 T := ⟨hp.2.1, hp.2.2.trans_lt htT⟩
    rw [Function.uncurry_apply_pair]
    simp only [Ψ, G, u0, indicator_of_mem hsU]
  have hswap := intervalIntegral_intervalIntegral_swap (F := G) hOn
  have hLeft : ∫ r in (0 : ℝ)..t, ∫ s in (0 : ℝ)..t, G r s =
      ∫ r in (0 : ℝ)..t, (t - r) ^ (α - 1) *
        ∫ s in (0 : ℝ)..r, (r - s) ^ (β - 1) * u s := by
    refine integral_congr_Ioo_of_le ht0.le ?_
    intro r hr
    dsimp only
    have hr0 : 0 < r := hr.1
    have hrt : r < t := hr.2
    have hconst : ∫ s in (0 : ℝ)..t, G r s =
        kernelPow (α - 1) (t - r) * ∫ s in (0 : ℝ)..t,
          (if s < r then kernelPow (β - 1) (r - s) * u s else 0) := by
      rw [← intervalIntegral.integral_const_mul]
      refine integral_congr fun s _ => ?_
      by_cases hsr : s < r
      · simp only [G, hsr, ↓reduceIte]
        ring
      · simp only [G, hsr, ↓reduceIte]
        ring
    rw [hconst, kernelPow_eq_rpow (sub_pos.mpr hrt),
      ← integral_of_lt_indicator hr0.le hrt.le (fun s => kernelPow (β - 1) (r - s) * u s),
      integral_kernelPow_eq hr0.le]
  have hRight : ∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..t, G r s =
      ProbabilityTheory.beta β α *
        ∫ s in (0 : ℝ)..t, (t - s) ^ (α + β - 1) * u s := by
    have hstep : ∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..t, G r s =
        ∫ s in (0 : ℝ)..t, u s * ∫ r in s..t,
          kernelPow (α - 1) (t - r) * kernelPow (β - 1) (r - s) := by
      refine integral_congr_Ioo_of_le ht0.le ?_
      intro s hs
      dsimp only
      have hpull : ∫ r in (0 : ℝ)..t, G r s =
          u s * ∫ r in (0 : ℝ)..t,
            (if s < r then kernelPow (α - 1) (t - r) * kernelPow (β - 1) (r - s) else 0) := by
        rw [← intervalIntegral.integral_const_mul]
        refine integral_congr fun r _ => ?_
        by_cases hsr : s < r
        · simp only [G, hsr, ↓reduceIte]
          ring
        · simp only [G, hsr, ↓reduceIte]
          ring
      rw [hpull, integral_of_gt_indicator hs.1.le hs.2.le]
    rw [hstep]
    have hbeta : ∫ s in (0 : ℝ)..t, u s * ∫ r in s..t,
          kernelPow (α - 1) (t - r) * kernelPow (β - 1) (r - s) =
        ∫ s in (0 : ℝ)..t,
          (u s * (t - s) ^ (α + β - 1)) * ProbabilityTheory.beta β α := by
      refine integral_congr_Ioo_of_le ht0.le ?_
      intro s hs
      dsimp only
      have hpow : ∫ r in s..t, kernelPow (α - 1) (t - r) * kernelPow (β - 1) (r - s) =
          ∫ r in s..t, (t - r) ^ (α - 1) * (r - s) ^ (β - 1) := by
        refine integral_congr_Ioo_of_le hs.2.le ?_
        intro r hr
        dsimp only
        rw [kernelPow_eq_rpow (sub_pos.mpr hr.2), kernelPow_eq_rpow (sub_pos.mpr hr.1)]
      rw [hpow, integral_betaKernel_beta hs.2 hα hβ]
      ring
    rw [hbeta, intervalIntegral.integral_mul_const, mul_comm]
    congr 1
    refine integral_congr fun s _ => ?_
    ring
  rw [← hLeft, hswap, hRight]

/-- Vanishing of the order-one integral forces the density to vanish almost everywhere. -/
private lemma ae_eq_zero_of_fractionalIntegral_one {T : ℝ} (hT : 0 < T) {u : ℝ → ℝ}
    (hu : IntegrableOn u (Ioo 0 T))
    (hz : fractionalIntegral 1 u =ᵐ[volume.restrict (Ioo 0 T)] fun _ => 0) :
    u =ᵐ[volume.restrict (Ioo 0 T)] fun _ => 0 := by
  have huI : IntervalIntegrable u volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (μ := volume) hT.le).2 hu
  let G : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, u s
  have hGac : AbsolutelyContinuousOnInterval G 0 T :=
    huI.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
  have hGI : fractionalIntegral 1 u =ᵐ[volume.restrict (Ioo 0 T)] G :=
    (ae_restrict_mem measurableSet_Ioo).mono fun t ht => fractionalIntegral_one ht.1.le
  have hG0 : EqOn G (fun _ => 0) (Ioo 0 T) :=
    Measure.eqOn_open_of_ae_eq (hGI.symm.trans hz) isOpen_Ioo
      (hGac.continuousOn.mono (by rw [uIcc_of_le hT.le]; exact Ioo_subset_Icc_self))
      continuousOn_const
  have hderiv : ∀ᵐ x, x ∈ Ioo 0 T → HasDerivAt G (u x) x := by
    filter_upwards [huI.ae_hasDerivAt_integral] with x hx hxI
    have hxU : x ∈ uIcc 0 T := by
      rw [uIcc_of_le hT.le]
      exact Ioo_subset_Icc_self hxI
    exact hx hxU 0 left_mem_uIcc
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [hderiv] with x hx hxI
  have hzero : HasDerivAt G 0 x := by
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hxI] with y hy
    exact hG0 hy
  exact (hx hxI).unique hzero

/-- The positive-order fractional integral semigroup, as an a.e. identity. -/
theorem fractionalIntegral_add {T α β : ℝ} (hT : 0 < T) (hα : 0 < α) (hβ : 0 < β)
    {u : ℝ → ℝ} (hu : IntegrableOn u (Set.Ioo 0 T)) :
    fractionalIntegral α (fractionalIntegral β u) =ᵐ[volume.restrict (Set.Ioo 0 T)]
      fractionalIntegral (α + β) u := by
  have hraw := rawFractional_comm hT hα hβ hu
  have hfac := gamma_beta_factor hα hβ
  filter_upwards [hraw] with t hteq
  rw [fractionalIntegral, fractionalIntegral]
  have hpull : ∫ r in (0 : ℝ)..t, (t - r) ^ (α - 1) * fractionalIntegral β u r =
      (Gamma β)⁻¹ * ∫ r in (0 : ℝ)..t, (t - r) ^ (α - 1) *
        ∫ s in (0 : ℝ)..r, (r - s) ^ (β - 1) * u s := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun r _ => ?_
    rw [fractionalIntegral, mul_left_comm]
  rw [hpull, hteq, ← mul_assoc, ← mul_assoc, hfac]

/-- A fractional integral of order in `(0, 1)` vanishes only for the zero density. -/
private lemma fractionalIntegral_ae_eq_zero {T β : ℝ} (hT : 0 < T) (hβ : 0 < β)
    (hβ1 : β < 1) {u : ℝ → ℝ} (hu : IntegrableOn u (Ioo 0 T))
    (hz : fractionalIntegral β u =ᵐ[volume.restrict (Ioo 0 T)] fun _ => 0) :
    u =ᵐ[volume.restrict (Ioo 0 T)] fun _ => 0 := by
  have h1β : 0 < 1 - β := sub_pos.mpr hβ1
  have hadd := fractionalIntegral_add hT h1β hβ hu
  simp only [sub_add_cancel] at hadd
  have hzero : fractionalIntegral (1 - β) (fractionalIntegral β u) =ᵐ[volume.restrict (Ioo 0 T)]
      fun _ => 0 :=
    (ae_restrict_mem measurableSet_Ioo).mono fun t ht => by
      rw [fractionalIntegral_congr hz ht.1.le ht.2.le, fractionalIntegral_zero]
  exact ae_eq_zero_of_fractionalIntegral_one hT hu (hadd.symm.trans hzero)

/-- `I^α` inverts differentiation of the absolutely continuous representative of `I^(1-α) f`. -/
private lemma fractionalIntegral_of_acDeriv {T α : ℝ} (hT : 0 < T) (hα : 0 < α)
    (hα1 : α < 1) {f g : ℝ → ℝ} (hf : IntegrableOn f (Ioo 0 T))
    (hg : AbsolutelyContinuousOnInterval g 0 T) (hg0 : g 0 = 0)
    (heq : g =ᵐ[volume.restrict (Ioo 0 T)] fractionalIntegral (1 - α) f) :
    fractionalIntegral α (deriv g) =ᵐ[volume.restrict (Ioo 0 T)] f := by
  have h1α : 0 < 1 - α := sub_pos.mpr hα1
  have h1α1 : 1 - α < 1 := sub_lt_self 1 hα
  let u := deriv g
  have huI : IntervalIntegrable u volume 0 T := hg.intervalIntegrable_deriv
  have hu : IntegrableOn u (Ioo 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (μ := volume) hT.le).1 huI
  have hFt : ∀ t ∈ Icc 0 T, fractionalIntegral 1 u t = g t := by
    intro t ht
    have hsub : uIcc 0 t ⊆ uIcc 0 T := by
      rw [uIcc_of_le ht.1, uIcc_of_le hT.le]
      exact Icc_subset_Icc le_rfl ht.2
    rw [fractionalIntegral_one ht.1, (hg.mono hsub).integral_deriv_eq_sub, hg0, sub_zero]
  have hFae : fractionalIntegral 1 u =ᵐ[volume.restrict (Ioo 0 T)] g :=
    (ae_restrict_mem measurableSet_Ioo).mono fun t ht => hFt t ⟨ht.1.le, ht.2.le⟩
  have hadd := fractionalIntegral_add hT h1α hα hu
  simp only [sub_add_cancel] at hadd
  have hcomp : fractionalIntegral (1 - α) (fractionalIntegral α u) =ᵐ[volume.restrict (Ioo 0 T)]
      fractionalIntegral (1 - α) f := hadd.trans (hFae.trans heq)
  have hHu : IntegrableOn (fractionalIntegral α u) (Ioo 0 T) :=
    integrableOn_fractionalIntegral hT hα hu
  have hdiff : fractionalIntegral (1 - α) (fun x => fractionalIntegral α u x - f x) =ᵐ[
      volume.restrict (Ioo 0 T)] fun _ => 0 := by
    refine (fractionalIntegral_sub_ae hT h1α hHu hf).trans ?_
    filter_upwards [hcomp] with t ht
    rw [ht, sub_self]
  have hzero := fractionalIntegral_ae_eq_zero hT h1α h1α1 (hHu.sub hf) hdiff
  filter_upwards [hzero] with t ht
  exact sub_eq_zero.mp ht

/-- **25.23**: the range of `I^α` on `L¹(0,T)` is characterized by an absolutely continuous
representative of `I^(1-α) f` vanishing at zero. -/
theorem mem_range_fractionalIntegral_iff {T α : ℝ} (hT : 0 < T)
    (hα : 0 < α) (hα1 : α < 1) {f : ℝ → ℝ} (hf : IntegrableOn f (Set.Ioo 0 T)) :
    (∃ u : ℝ → ℝ, IntegrableOn u (Set.Ioo 0 T) ∧
      fractionalIntegral α u =ᵐ[volume.restrict (Set.Ioo 0 T)] f) ↔
    ∃ g : ℝ → ℝ, AbsolutelyContinuousOnInterval g 0 T ∧ g 0 = 0 ∧
      g =ᵐ[volume.restrict (Set.Ioo 0 T)] fractionalIntegral (1 - α) f := by
  constructor
  · rintro ⟨u, hu, hueq⟩
    have h1α : 0 < 1 - α := sub_pos.mpr hα1
    have huI : IntervalIntegrable u volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (μ := volume) hT.le).2 hu
    refine ⟨fun t => ∫ s in (0 : ℝ)..t, u s, ?_, ?_, ?_⟩
    · exact huI.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
    · exact integral_same
    · have hg1 : (fun t => ∫ s in (0 : ℝ)..t, u s) =ᵐ[volume.restrict (Ioo 0 T)]
          fractionalIntegral 1 u :=
        (ae_restrict_mem measurableSet_Ioo).mono fun t ht => (fractionalIntegral_one ht.1.le).symm
      have hadd := fractionalIntegral_add hT h1α hα hu
      simp only [sub_add_cancel] at hadd
      have hcong : fractionalIntegral (1 - α) (fractionalIntegral α u) =ᵐ[
          volume.restrict (Ioo 0 T)] fractionalIntegral (1 - α) f :=
        (ae_restrict_mem measurableSet_Ioo).mono fun t ht =>
          fractionalIntegral_congr hueq ht.1.le ht.2.le
      exact hg1.trans (hadd.symm.trans hcong)
  · rintro ⟨g, hg, hg0, heq⟩
    refine ⟨deriv g,
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (μ := volume) hT.le).1
        hg.intervalIntegrable_deriv,
      fractionalIntegral_of_acDeriv hT hα hα1 hf hg hg0 heq⟩

/-- Differentiating that absolutely continuous representative gives the inverse. -/
theorem fractionalIntegral_deriv_inverse {T α : ℝ} (hT : 0 < T)
    (hα : 0 < α) (hα1 : α < 1) {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Ioo 0 T)) (hg : AbsolutelyContinuousOnInterval g 0 T)
    (hg0 : g 0 = 0)
    (heq : g =ᵐ[volume.restrict (Set.Ioo 0 T)] fractionalIntegral (1 - α) f) :
    fractionalIntegral α (deriv g) =ᵐ[volume.restrict (Set.Ioo 0 T)] f :=
  fractionalIntegral_of_acDeriv hT hα hα1 hf hg hg0 heq

end CKMA
