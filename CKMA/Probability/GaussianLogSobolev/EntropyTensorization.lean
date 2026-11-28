/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.GaussianLogSobolev.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Subadditivity of entropy on product measures

For an integrable nonnegative function on a product of probability spaces, the extended entropy
`CKMA.nonnegativeFunctionEntropy` is at most the sum over the coordinates of the averaged entropy
in that coordinate with the other coordinates frozen. This is the entropy analogue of the
Efron–Stein inequality and the tensorization principle behind logarithmic Sobolev inequalities
on product spaces.

The two-factor bound compares the perspective `M * klFun (a / M)` of `klFun` at the total mass
with its values at the two partial masses; the defect integrates to zero, and the remaining term
is a nonnegative relative entropy. The finite-product statement follows by induction on the
number of coordinates, as in TauCeti's proof of the Efron–Stein inequality.

## Main results

* `CKMA.measurable_nonnegativeFunctionEntropy_slice`: measurability of slice entropies.
* `CKMA.nonnegativeFunctionEntropy_prod_le`: subadditivity on a product of two probability
  spaces.
* `CKMA.nonnegativeFunctionEntropy_pi_le`: subadditivity on a finite product of probability
  spaces.

## References

* M. Ledoux, *The Concentration of Measure Phenomenon*, Proposition 5.6.
* S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Theorem 4.10.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory InformationTheory
open scoped ENNReal

section Basic

variable {X : Type*} [MeasurableSpace X]

/-- The entropy of the slices `y ↦ h (x, y)` of a measurable function depends measurably
on `x`. -/
theorem measurable_nonnegativeFunctionEntropy_slice {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν] {h : X × Y → ℝ} (hh : Measurable h) :
    Measurable fun x ↦ nonnegativeFunctionEntropy ν (fun y ↦ h (x, y)) := by
  have hI : Measurable fun x ↦ ∫ y, h (x, y) ∂ν :=
    (hh.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have hk : Measurable fun p : X × Y ↦ ENNReal.ofReal (klFun (h p / ∫ y, h (p.1, y) ∂ν)) :=
    (measurable_klFun.comp (hh.div (hI.comp measurable_fst))).ennreal_ofReal
  exact hI.ennreal_ofReal.mul hk.lintegral_prod_right'

end Basic

section Prod

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The perspective of `klFun` at a positive mass, written out. -/
private lemma mul_klFun_div_eq {a M : ℝ} (ha : 0 < a) (hM : 0 < M) :
    M * klFun (a / M) = a * Real.log a - a * Real.log M + M - a := by
  rw [klFun_apply, Real.log_div ha.ne' hM.ne']
  field_simp

/-- Pointwise comparison of the perspective of `klFun` at the total mass `m` with its values
at the partial masses `H` and `n`, up to a correction term of integral zero. -/
private lemma mul_klFun_div_add_le {a H n m : ℝ} (ha : 0 ≤ a) (hH : 0 ≤ H) (hn : 0 ≤ n)
    (hm : 0 < m) (hHa : H = 0 → a = 0) (hna : n = 0 → a = 0) :
    m * klFun (a / m) + (H + n - m - n * H / m) ≤ H * klFun (a / H) + n * klFun (a / n) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp only [zero_div, klFun_zero, mul_one]
    have : 0 ≤ n * H / m := by positivity
    linarith
  have hH' : 0 < H := hH.lt_of_ne fun h ↦ ha.ne' (hHa h.symm)
  have hn' : 0 < n := hn.lt_of_ne fun h ↦ ha.ne' (hna h.symm)
  have hK : 0 < n * H / m := by positivity
  have hkl := mul_nonneg hK.le (klFun_nonneg (div_nonneg ha.le hK.le))
  rw [mul_klFun_div_eq ha hK, Real.log_div (by positivity) hm.ne',
    Real.log_mul hn'.ne' hH'.ne'] at hkl
  rw [mul_klFun_div_eq ha hm, mul_klFun_div_eq ha hH', mul_klFun_div_eq ha hn']
  have hexp : a * (Real.log n + Real.log H - Real.log m) =
      a * Real.log n + a * Real.log H - a * Real.log m := by ring
  linarith

/-- If `A + c ≤ B` almost everywhere, with `A` and `B` nonnegative and `c` integrable with
nonnegative integral, then the lower integral of `A` is at most that of `B`. -/
private lemma lintegral_ofReal_le_of_add_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A B c : α → ℝ} (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x) (hBm : AEStronglyMeasurable B μ)
    (hc : Integrable c μ) (hc0 : 0 ≤ ∫ x, c x ∂μ) (hle : ∀ᵐ x ∂μ, A x + c x ≤ B x) :
    ∫⁻ x, ENNReal.ofReal (A x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (B x) ∂μ := by
  by_cases htop : ∫⁻ x, ENNReal.ofReal (B x) ∂μ = ⊤
  · rw [htop]
    exact le_top
  have hB' : 0 ≤ᵐ[μ] B := ae_of_all _ hB
  have hBi : Integrable B μ := (lintegral_ofReal_ne_top_iff_integrable hBm hB').1 htop
  have hD : 0 ≤ᵐ[μ] fun x ↦ B x - c x := by
    filter_upwards [hle] with x hx
    have := hA x
    simp only [Pi.zero_apply]
    linarith
  calc ∫⁻ x, ENNReal.ofReal (A x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (B x - c x) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hle] with x hx
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (∫ x, (B x - c x) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal (hBi.sub hc) hD).symm
    _ ≤ ENNReal.ofReal (∫ x, B x ∂μ) := by
        rw [integral_sub hBi hc]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = ∫⁻ x, ENNReal.ofReal (B x) ∂μ := ofReal_integral_eq_lintegral_ofReal hBi hB'

/-- Almost everywhere on a product, a nonnegative integrable function vanishes wherever its
integral over the second factor vanishes. -/
private lemma ae_prod_eq_zero_of_integral_right_eq_zero (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] {h : X × Y → ℝ} (hh : Measurable h) (hnn : ∀ p, 0 ≤ h p)
    (hint : Integrable h (μ.prod ν)) :
    ∀ᵐ p ∂μ.prod ν, (∫ y, h (p.1, y) ∂ν) = 0 → h p = 0 := by
  have hN : Measurable fun x ↦ ∫ y, h (x, y) ∂ν :=
    (hh.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have hs : MeasurableSet {p : X × Y | (∫ y, h (p.1, y) ∂ν) = 0 → h p = 0} := by
    have he : {p : X × Y | (∫ y, h (p.1, y) ∂ν) = 0 → h p = 0} =
        {p | (∫ y, h (p.1, y) ∂ν) = 0}ᶜ ∪ {p | h p = 0} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]
      tauto
    rw [he]
    exact (measurableSet_eq_fun (hN.comp measurable_fst) measurable_const).compl.union
      (measurableSet_eq_fun hh measurable_const)
  refine (Measure.ae_prod_mem_iff_ae_ae_mem hs).2 ?_
  filter_upwards [hint.prod_right_ae] with x hx
  by_cases h0 : (∫ y, h (x, y) ∂ν) = 0
  · filter_upwards [(integral_eq_zero_iff_of_nonneg (fun y ↦ hnn (x, y)) hx).1 h0] with y hy
    exact fun _ ↦ hy
  · exact Filter.Eventually.of_forall fun y hy ↦ (h0 hy).elim

/-- **Subadditivity of entropy** on a product of two probability spaces: the entropy of an
integrable nonnegative function is at most the sum of the averaged entropies of its slices in
each factor. -/
theorem nonnegativeFunctionEntropy_prod_le (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {h : X × Y → ℝ} (hh : Measurable h)
    (hnn : ∀ p, 0 ≤ h p) (hint : Integrable h (μ.prod ν)) :
    nonnegativeFunctionEntropy (μ.prod ν) h ≤
      ∫⁻ y, nonnegativeFunctionEntropy μ (fun x ↦ h (x, y)) ∂ν +
        ∫⁻ x, nonnegativeFunctionEntropy ν (fun y ↦ h (x, y)) ∂μ := by
  obtain ⟨m, hm⟩ : ∃ m, ∫ p, h p ∂μ.prod ν = m := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := hm ▸ integral_nonneg hnn
  rw [nonnegativeFunctionEntropy_eq_lintegral (hm ▸ hm0), hm]
  rcases hm0.eq_or_lt with hm0 | hmpos
  · simp only [← hm0, zero_mul, ENNReal.ofReal_zero, lintegral_zero, zero_le]
  let H : Y → ℝ := fun y ↦ ∫ x, h (x, y) ∂μ
  let N : X → ℝ := fun x ↦ ∫ y, h (x, y) ∂ν
  have hHm : Measurable H := (hh.stronglyMeasurable.integral_prod_left' (μ := μ)).measurable
  have hNm : Measurable N := (hh.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have hH0 (y : Y) : 0 ≤ H y := integral_nonneg fun x ↦ hnn (x, y)
  have hN0 (x : X) : 0 ≤ N x := integral_nonneg fun y ↦ hnn (x, y)
  have hHi : Integrable H ν := hint.integral_prod_right
  have hNi : Integrable N μ := hint.integral_prod_left
  have hHint : ∫ y, H y ∂ν = m := (integral_prod_symm h hint).symm.trans hm
  have hNint : ∫ x, N x ∂μ = m := (integral_prod h hint).symm.trans hm
  let Φ : ℝ → ℝ → ℝ := fun a M ↦ M * klFun (a / M)
  have hΦm : Measurable fun q : ℝ × ℝ ↦ Φ q.1 q.2 :=
    measurable_snd.mul (measurable_klFun.comp (measurable_fst.div measurable_snd))
  have hΦ0 {a M : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M) : 0 ≤ Φ a M :=
    mul_nonneg hM (klFun_nonneg (div_nonneg ha hM))
  let B₁ : X × Y → ℝ := fun p ↦ Φ (h p) (H p.2)
  let B₂ : X × Y → ℝ := fun p ↦ Φ (h p) (N p.1)
  let c : X × Y → ℝ := fun p ↦ H p.2 + N p.1 - m - N p.1 * H p.2 / m
  have hB₁m : Measurable B₁ := hΦm.comp (hh.prodMk (hHm.comp measurable_snd))
  have hB₂m : Measurable B₂ := hΦm.comp (hh.prodMk (hNm.comp measurable_fst))
  have h1 : Integrable (fun p : X × Y ↦ H p.2) (μ.prod ν) := by
    simpa using (integrable_const (1 : ℝ)).mul_prod hHi
  have h2 : Integrable (fun p : X × Y ↦ N p.1) (μ.prod ν) := by
    simpa using hNi.mul_prod (integrable_const (1 : ℝ))
  have h3 : Integrable (fun p : X × Y ↦ N p.1 * H p.2 / m) (μ.prod ν) :=
    (hNi.mul_prod hHi).div_const m
  have hci : Integrable c (μ.prod ν) := ((h1.add h2).sub (integrable_const m)).sub h3
  have hc0 : ∫ p, c p ∂μ.prod ν = 0 := by
    have e1 : ∫ p, H p.2 ∂μ.prod ν = m := by
      simpa [hHint] using integral_prod_mul (μ := μ) (ν := ν) (fun _ ↦ (1 : ℝ)) H
    have e2 : ∫ p, N p.1 ∂μ.prod ν = m := by
      simpa [hNint] using integral_prod_mul (μ := μ) (ν := ν) N (fun _ ↦ (1 : ℝ))
    have e3 : ∫ p, N p.1 * H p.2 / m ∂μ.prod ν = m := by
      rw [integral_div, integral_prod_mul, hNint, hHint]
      field_simp
    simp only [c]
    rw [integral_sub (f := fun p : X × Y ↦ H p.2 + N p.1 - m)
        (g := fun p ↦ N p.1 * H p.2 / m) ((h1.add h2).sub (integrable_const m)) h3,
      integral_sub (f := fun p : X × Y ↦ H p.2 + N p.1) (g := fun _ ↦ m) (h1.add h2)
        (integrable_const m), integral_add h1 h2, e1, e2, e3]
    simp
  have hzH : ∀ᵐ p ∂μ.prod ν, H p.2 = 0 → h p = 0 := by
    have hsw := ae_prod_eq_zero_of_integral_right_eq_zero ν μ (hh.comp measurable_swap)
      (fun p ↦ hnn p.swap) hint.swap
    exact (Measure.measurePreserving_swap (μ := μ) (ν := ν)).quasiMeasurePreserving.ae hsw
  have hzN : ∀ᵐ p ∂μ.prod ν, N p.1 = 0 → h p = 0 :=
    ae_prod_eq_zero_of_integral_right_eq_zero μ ν hh hnn hint
  have hstep : ∫⁻ p, ENNReal.ofReal (Φ (h p) m) ∂μ.prod ν ≤
      ∫⁻ p, ENNReal.ofReal (B₁ p + B₂ p) ∂μ.prod ν := by
    refine lintegral_ofReal_le_of_add_le (fun p ↦ hΦ0 (hnn p) hmpos.le)
      (fun p ↦ add_nonneg (hΦ0 (hnn p) (hH0 _)) (hΦ0 (hnn p) (hN0 _)))
      (hB₁m.add hB₂m).aestronglyMeasurable hci hc0.ge ?_
    filter_upwards [hzH, hzN] with p hp₁ hp₂
    exact mul_klFun_div_add_le (hnn p) (hH0 p.2) (hN0 p.1) hmpos hp₁ hp₂
  have hsplit : ∫⁻ p, ENNReal.ofReal (B₁ p + B₂ p) ∂μ.prod ν =
      ∫⁻ p, ENNReal.ofReal (B₁ p) ∂μ.prod ν + ∫⁻ p, ENNReal.ofReal (B₂ p) ∂μ.prod ν := by
    rw [← lintegral_add_left hB₁m.ennreal_ofReal]
    refine lintegral_congr fun p ↦ ?_
    exact ENNReal.ofReal_add (hΦ0 (hnn p) (hH0 _)) (hΦ0 (hnn p) (hN0 _))
  have hB₁eq : ∫⁻ p, ENNReal.ofReal (B₁ p) ∂μ.prod ν =
      ∫⁻ y, nonnegativeFunctionEntropy μ (fun x ↦ h (x, y)) ∂ν := by
    rw [lintegral_prod_symm' _ hB₁m.ennreal_ofReal]
    exact lintegral_congr fun y ↦ (nonnegativeFunctionEntropy_eq_lintegral (hH0 y)).symm
  have hB₂eq : ∫⁻ p, ENNReal.ofReal (B₂ p) ∂μ.prod ν =
      ∫⁻ x, nonnegativeFunctionEntropy ν (fun y ↦ h (x, y)) ∂μ := by
    rw [lintegral_prod _ hB₂m.ennreal_ofReal.aemeasurable]
    exact lintegral_congr fun x ↦ (nonnegativeFunctionEntropy_eq_lintegral (hN0 x)).symm
  rw [← hB₁eq, ← hB₂eq, ← hsplit]
  exact hstep

end Prod

section Pi

universe u

/-- On a product indexed by `Fin 0` every function is constant, so its entropy vanishes. -/
private lemma nonnegativeFunctionEntropy_pi_fin_zero {α : Fin 0 → Type u}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (h : (∀ i, α i) → ℝ) : nonnegativeFunctionEntropy (Measure.pi μ) h = 0 := by
  have hc : h = fun _ ↦ h default := funext fun x ↦ by rw [Subsingleton.elim x default]
  rw [hc]
  rcases eq_or_ne (h default) 0 with h0 | h0
  · simp [nonnegativeFunctionEntropy, h0]
  · simp [nonnegativeFunctionEntropy, div_self h0, klFun_one]

/-- The slice entropy in coordinate `i` is a measurable function of the frozen coordinates. -/
private lemma measurable_nonnegativeFunctionEntropy_update {ι : Type*} [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) (i : ι)
    [SFinite (μ i)] {h : (∀ i, α i) → ℝ} (hh : Measurable h) :
    Measurable fun x ↦ nonnegativeFunctionEntropy (μ i) (fun y ↦ h (Function.update x i y)) :=
  measurable_nonnegativeFunctionEntropy_slice (μ i)
    (h := fun q : (∀ j, α j) × α i ↦ h (Function.update q.1 i q.2)) (hh.comp measurable_update')

/-- The average over the remaining coordinates of the slice entropy in coordinate `0` is the
`i = 0` term of the tensorization sum. -/
private lemma lintegral_nonnegativeFunctionEntropy_piFinSuccAbove_symm_zero {n : ℕ}
    {α : Fin (n + 1) → Type u} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] {h : (∀ i, α i) → ℝ} (hh : Measurable h) :
    ∫⁻ w, nonnegativeFunctionEntropy (μ 0)
        (fun a ↦ h ((MeasurableEquiv.piFinSuccAbove α 0).symm (a, w)))
        ∂(Measure.pi fun j ↦ μ (Fin.succAbove 0 j)) =
      ∫⁻ x, nonnegativeFunctionEntropy (μ 0) (fun y ↦ h (Function.update x 0 y))
        ∂Measure.pi μ := by
  have hGp : Measurable fun p ↦ nonnegativeFunctionEntropy (μ 0) (fun y ↦ h (Function.update
      ((MeasurableEquiv.piFinSuccAbove α 0).symm p) 0 y)) :=
    (measurable_nonnegativeFunctionEntropy_update μ 0 hh).comp
      (MeasurableEquiv.piFinSuccAbove α 0).symm.measurable
  rw [← ((measurePreserving_piFinSuccAbove μ 0).symm _).lintegral_comp_emb
      (MeasurableEquiv.piFinSuccAbove α 0).symm.measurableEmbedding,
    lintegral_prod _ hGp.aemeasurable]
  simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
    Fin.update_insertNth]
  rw [lintegral_const, measure_univ, mul_one]

/-- Subadditivity of entropy on `Measure.pi` over `Fin n`. -/
private theorem nonnegativeFunctionEntropy_pi_fin_le : ∀ {n : ℕ} {α : Fin n → Type u}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {h : (∀ i, α i) → ℝ}, Measurable h → (∀ x, 0 ≤ h x) → Integrable h (Measure.pi μ) →
    nonnegativeFunctionEntropy (Measure.pi μ) h ≤
      ∑ i, ∫⁻ x, nonnegativeFunctionEntropy (μ i) (fun y ↦ h (Function.update x i y))
        ∂Measure.pi μ
  | 0, _, _, μ, _, h, _, _, _ => by
    rw [nonnegativeFunctionEntropy_pi_fin_zero μ h]
    exact zero_le
  | n + 1, α, _, μ, _, h, hh, hnn, hi => by
    set e := MeasurableEquiv.piFinSuccAbove α 0 with he
    have mp : MeasurePreserving e (Measure.pi μ)
        ((μ 0).prod (Measure.pi fun j ↦ μ (Fin.succAbove 0 j))) :=
      measurePreserving_piFinSuccAbove μ 0
    have mps := mp.symm e
    set F : α 0 × (∀ j, α (Fin.succAbove 0 j)) → ℝ := fun p ↦ h (e.symm p) with hFdef
    have hFm : Measurable F := hh.comp e.symm.measurable
    have hFi : Integrable F ((μ 0).prod (Measure.pi fun j ↦ μ (Fin.succAbove 0 j))) :=
      (mps.integrable_comp_emb e.symm.measurableEmbedding).2 hi
    set G : Fin (n + 1) → (∀ i, α i) → ℝ≥0∞ :=
      fun i x ↦ nonnegativeFunctionEntropy (μ i) (fun y ↦ h (Function.update x i y))
      with hGdef
    have hGm (i : Fin (n + 1)) : Measurable (G i) :=
      measurable_nonnegativeFunctionEntropy_update μ i hh
    have hEnt : nonnegativeFunctionEntropy (Measure.pi μ) h =
        nonnegativeFunctionEntropy ((μ 0).prod (Measure.pi fun j ↦ μ (Fin.succAbove 0 j))) F :=
      (nonnegativeFunctionEntropy_comp_measurePreserving mps e.symm.measurableEmbedding h).symm
    have hG (j : Fin n) (a : α 0) (w : ∀ j, α (Fin.succAbove 0 j)) :
        nonnegativeFunctionEntropy (μ (Fin.succAbove 0 j))
            (fun y ↦ F (a, Function.update w j y)) =
          G (Fin.succAbove 0 j) (e.symm (a, w)) := by
      simp only [hFdef, hGdef, he, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv_apply, Fin.insertNth_update]
    have hGp (j : Fin (n + 1)) : Measurable fun p ↦ G j (e.symm p) :=
      (hGm j).comp e.symm.measurable
    have h1 : ∫⁻ a, nonnegativeFunctionEntropy (Measure.pi fun j ↦ μ (Fin.succAbove 0 j))
          (fun w ↦ F (a, w)) ∂(μ 0) ≤
        ∑ j : Fin n, ∫⁻ x, G (Fin.succAbove 0 j) x ∂Measure.pi μ := by
      calc _ ≤ ∫⁻ a, ∑ j : Fin n, ∫⁻ w, G (Fin.succAbove 0 j) (e.symm (a, w))
              ∂(Measure.pi fun j ↦ μ (Fin.succAbove 0 j)) ∂(μ 0) := by
            refine lintegral_mono_ae ?_
            filter_upwards [hFi.prod_right_ae] with a ha
            have := nonnegativeFunctionEntropy_pi_fin_le (α := fun j ↦ α (Fin.succAbove 0 j))
              (fun j ↦ μ (Fin.succAbove 0 j)) (h := fun w ↦ F (a, w))
              (hFm.comp measurable_prodMk_left) (fun w ↦ hnn _) ha
            simpa only [hG] using this
        _ = ∑ j : Fin n, ∫⁻ a, ∫⁻ w, G (Fin.succAbove 0 j) (e.symm (a, w))
              ∂(Measure.pi fun j ↦ μ (Fin.succAbove 0 j)) ∂(μ 0) :=
            lintegral_finsetSum' _ fun j _ ↦
              (Measurable.lintegral_prod_right' (hGp _)).aemeasurable
        _ = _ := Finset.sum_congr rfl fun j _ ↦ by
            rw [← mps.lintegral_comp_emb e.symm.measurableEmbedding,
              lintegral_prod _ (hGp _).aemeasurable]
    have h2 := lintegral_nonnegativeFunctionEntropy_piFinSuccAbove_symm_zero μ hh
    calc nonnegativeFunctionEntropy (Measure.pi μ) h = _ := hEnt
      _ ≤ _ := nonnegativeFunctionEntropy_prod_le _ _ hFm (fun p ↦ hnn _) hFi
      _ ≤ ∫⁻ x, G 0 x ∂Measure.pi μ +
          ∑ j : Fin n, ∫⁻ x, G (Fin.succAbove 0 j) x ∂Measure.pi μ := add_le_add h2.le h1
      _ = ∑ i, ∫⁻ x, G i x ∂Measure.pi μ := by rw [Fin.sum_univ_succAbove _ 0]

/-- **Subadditivity of entropy** on a finite product of probability spaces: the entropy of an
integrable nonnegative measurable function is at most the sum over the coordinates `i` of the
averaged entropy of `y ↦ h (Function.update x i y)` under `μ i`. -/
theorem nonnegativeFunctionEntropy_pi_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type u} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] {h : (∀ i, α i) → ℝ} (hh : Measurable h)
    (hnn : ∀ x, 0 ≤ h x) (hi : Integrable h (Measure.pi μ)) :
    nonnegativeFunctionEntropy (Measure.pi μ) h ≤
      ∑ i, ∫⁻ x, nonnegativeFunctionEntropy (μ i) (fun y ↦ h (Function.update x i y))
        ∂Measure.pi μ := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let Φ := MeasurableEquiv.piCongrLeft α e
  have mp : MeasurePreserving Φ (Measure.pi fun k ↦ μ (e k)) (Measure.pi μ) :=
    measurePreserving_piCongrLeft μ e
  have hupd (k : Fin (Fintype.card ι)) (y : ∀ k, α (e k)) (v : α (e k)) :
      Φ (Function.update y k v) = Function.update (Φ y) (e k) v := by
    simpa [Φ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft] using
      Function.piCongrLeft'_symm_update α e.symm y k v
  have hterm (k : Fin (Fintype.card ι)) :
      ∫⁻ y, nonnegativeFunctionEntropy (μ (e k)) (fun v ↦ h (Φ (Function.update y k v)))
          ∂Measure.pi (fun k ↦ μ (e k)) =
        ∫⁻ x, nonnegativeFunctionEntropy (μ (e k)) (fun v ↦ h (Function.update x (e k) v))
          ∂Measure.pi μ := by
    simp_rw [hupd]
    exact mp.lintegral_comp_emb Φ.measurableEmbedding
      (fun x ↦ nonnegativeFunctionEntropy (μ (e k)) (fun v ↦ h (Function.update x (e k) v)))
  calc nonnegativeFunctionEntropy (Measure.pi μ) h
      = nonnegativeFunctionEntropy (Measure.pi fun k ↦ μ (e k)) (fun x ↦ h (Φ x)) :=
        (nonnegativeFunctionEntropy_comp_measurePreserving mp Φ.measurableEmbedding h).symm
    _ ≤ ∑ k, ∫⁻ y, nonnegativeFunctionEntropy (μ (e k))
          (fun v ↦ h (Φ (Function.update y k v))) ∂Measure.pi (fun k ↦ μ (e k)) :=
        nonnegativeFunctionEntropy_pi_fin_le (α := fun k ↦ α (e k)) (fun k ↦ μ (e k))
          (h := fun x ↦ h (Φ x)) (hh.comp Φ.measurable) (fun x ↦ hnn _)
          ((mp.integrable_comp_emb Φ.measurableEmbedding).2 hi)
    _ = ∑ k, ∫⁻ x, nonnegativeFunctionEntropy (μ (e k))
          (fun v ↦ h (Function.update x (e k) v)) ∂Measure.pi μ :=
        Finset.sum_congr rfl fun k _ ↦ hterm k
    _ = ∑ i, ∫⁻ x, nonnegativeFunctionEntropy (μ i) (fun y ↦ h (Function.update x i y))
          ∂Measure.pi μ :=
        Equiv.sum_comp e fun i ↦
          ∫⁻ x, nonnegativeFunctionEntropy (μ i) (fun y ↦ h (Function.update x i y))
            ∂Measure.pi μ

end Pi

end CKMA
