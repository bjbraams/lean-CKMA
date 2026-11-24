/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability

import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Enumerating the zeros of an entire function

The zeros of an entire function, repeated by multiplicity, form a countable set. An injective
encoding into `ℕ` produces the `Option`-valued sequence used by a canonical product: `none` pads
the sequence when there are only finitely many zeros.

The summability statement is the exponent-of-convergence input of Hadamard factorization. It is
the pushforward, along the encoding, of `TauCeti.OrderLE.summable_divisor_mul_norm_rpow`.
-/

public section

noncomputable section

namespace CKMA

open Classical Filter Function Metric Set
open scoped BigOperators Topology

/-- The zeros of an entire function, each repeated by its multiplicity. -/
@[expose]
abbrev ZeroAtom (g : ℂ → ℂ) :=
  Σ ρ : {z : ℂ // z ∈ (MeromorphicOn.divisor g Set.univ).support},
    Fin ((MeromorphicOn.divisor g Set.univ (ρ : ℂ)).toNat)

/-- Deprecated name for `ZeroAtom`. -/
@[deprecated (since := "2026-11-21")]
alias zeroAtom := ZeroAtom

/-- The support of the divisor of an entire function is a countable set of isolated zeros. -/
theorem countable_divisor_support {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    (MeromorphicOn.divisor g Set.univ).support.Countable := by
  have hsub : (MeromorphicOn.divisor g Set.univ).support ⊆
      ⋃ n : ℕ, (MeromorphicOn.divisor g (closedBall 0 (n : ℝ))).support := by
    intro z hz
    refine mem_iUnion.2 ⟨⌈‖z‖⌉₊, ?_⟩
    have hzR : z ∈ closedBall (0 : ℂ) (⌈‖z‖⌉₊ : ℝ) := by
      simp [mem_closedBall, dist_zero_right, Nat.le_ceil]
    have hball : AnalyticOnNhd ℂ g (closedBall 0 (⌈‖z‖⌉₊ : ℝ)) := fun w _ => hg.analyticAt w
    have huniv : AnalyticOnNhd ℂ g Set.univ := fun w _ => hg.analyticAt w
    have hd : MeromorphicOn.divisor g (closedBall 0 (⌈‖z‖⌉₊ : ℝ)) z =
        MeromorphicOn.divisor g Set.univ z := by
      rw [hball.meromorphicOn.divisor_eq_analyticOrderNatAt (hg.analyticAt z) hzR,
        huniv.meromorphicOn.divisor_eq_analyticOrderNatAt (hg.analyticAt z) (mem_univ z)]
    simpa [Function.mem_support, hd] using hz
  refine (Set.countable_iUnion fun n : ℕ => ?_).mono hsub
  have hAn : AnalyticOnNhd ℂ g (closedBall 0 (n : ℝ)) := fun w _ => hg.analyticAt w
  exact (hAn.meromorphicOn.divisor_support_finite_of_subset (isCompact_closedBall 0 (n : ℝ))
    subset_rfl).countable

/-- Multiplicities are nonnegative, so the integer divisor and its `toNat` agree as reals. -/
theorem divisor_toNat_cast {g : ℂ → ℂ} (hg : Differentiable ℂ g) (z : ℂ) :
    ((MeromorphicOn.divisor g Set.univ z).toNat : ℝ) =
      (MeromorphicOn.divisor g Set.univ z : ℝ) := by
  have hnn : 0 ≤ MeromorphicOn.divisor g Set.univ z :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun w _ => hg.analyticAt w) z
  exact_mod_cast Int.toNat_of_nonneg hnn

/-- An entire function nonzero at the origin has no atom supported at `0`. -/
theorem zero_not_mem_divisor_support {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hg0 : g 0 ≠ 0) :
    (0 : ℂ) ∉ (MeromorphicOn.divisor g Set.univ).support := by
  intro hz
  have hord : analyticOrderAt g 0 = 0 :=
    (hg.analyticAt 0).analyticOrderAt_eq_zero.mpr hg0
  have hA : AnalyticOnNhd ℂ g Set.univ := fun w _ => hg.analyticAt w
  have hd : MeromorphicOn.divisor g Set.univ 0 = 0 := by
    rw [hA.meromorphicOn.divisor_eq_analyticOrderNatAt (hg.analyticAt 0) (mem_univ 0),
      analyticOrderNatAt, hord, ENat.toNat_zero, Nat.cast_zero]
  exact hz (by simpa [Function.mem_support] using hd)

/-- The atoms of an entire function form a countable set. -/
theorem countable_zeroAtom {g : ℂ → ℂ} (hg : Differentiable ℂ g) : Countable (ZeroAtom g) := by
  have : Countable {z : ℂ // z ∈ (MeromorphicOn.divisor g Set.univ).support} :=
    (countable_divisor_support hg).to_subtype
  infer_instance

/-- An injective encoding of the zeros, repeated by multiplicity, together with the proof. -/
@[expose]
def zeroEncoding {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    {f : ZeroAtom g → ℕ // Injective f} :=
  letI := countable_zeroAtom hg
  ⟨Classical.choose (Countable.exists_injective_nat (ZeroAtom g)),
    Classical.choose_spec (Countable.exists_injective_nat (ZeroAtom g))⟩

/-- An injective encoding of the zeros, repeated by multiplicity. -/
@[expose]
def zeroEncode {g : ℂ → ℂ} (hg : Differentiable ℂ g) : ZeroAtom g → ℕ :=
  (zeroEncoding hg).1

/-- The encoding of zeros is injective. -/
theorem zeroEncode_injective {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Injective (zeroEncode hg) :=
  (zeroEncoding hg).2

/-- The `Option`-valued list of zeros. `none` fills the unused indices. -/
@[expose]
def enumeratedZero {g : ℂ → ℂ} (hg : Differentiable ℂ g) (n : ℕ) : Option ℂ :=
  if h : ∃ a : ZeroAtom g, zeroEncode hg a = n then some (Classical.choose h).1 else none

/-- Every atom appears at its encoded index. -/
theorem enumeratedZero_zeroEncode {g : ℂ → ℂ} (hg : Differentiable ℂ g) (a : ZeroAtom g) :
    enumeratedZero hg (zeroEncode hg a) = some (a.1 : ℂ) := by
  have h : ∃ b : ZeroAtom g, zeroEncode hg b = zeroEncode hg a := ⟨a, rfl⟩
  rw [enumeratedZero, dite_eq_left h, zeroEncode_injective hg (Classical.choose_spec h)]

/-- A listed value comes from a unique atom. -/
theorem exists_zeroAtom_of_enumeratedZero {g : ℂ → ℂ} (hg : Differentiable ℂ g) {n : ℕ} {w : ℂ}
    (hw : enumeratedZero hg n = some w) :
    ∃ a : ZeroAtom g, zeroEncode hg a = n ∧ (a.1 : ℂ) = w := by
  by_cases h : ∃ a : ZeroAtom g, zeroEncode hg a = n
  · rw [enumeratedZero, dite_eq_left h] at hw
    exact ⟨Classical.choose h, Classical.choose_spec h, Option.some_injective _ hw⟩
  · rw [enumeratedZero, dite_eq_right h] at hw
    simp at hw

/-- A listed value is a genuine zero, hence not the origin when `g 0 ≠ 0`. -/
theorem enumeratedZero_ne_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hg0 : g 0 ≠ 0) {n : ℕ}
    {w : ℂ} (hw : enumeratedZero hg n = some w) : w ≠ 0 := by
  intro hw0
  obtain ⟨a, -, ha⟩ := exists_zeroAtom_of_enumeratedZero hg hw
  exact zero_not_mem_divisor_support hg hg0 (hw0 ▸ ha ▸ a.1.2)

/-- The reciprocal powers of the enumerated zeros are the atom weights pushed along the encoding. -/
theorem summable_enumeratedZero_rpow {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {ρ q : ℝ} (hord : TauCeti.OrderLE g ρ) (hq : ρ < q) :
    Summable fun n ↦ match enumeratedZero hg n with
      | none => (0 : ℝ)
      | some w => ‖w‖ ^ (-q) := by
  classical
  let d := MeromorphicOn.divisor g Set.univ
  have hTau := hord.summable_divisor_mul_norm_rpow hg hq
  have hAtom : Summable fun a : ZeroAtom g ↦ ‖(a.1 : ℂ)‖ ^ (-q) := by
    rw [summable_sigma_of_nonneg (fun a ↦ Real.rpow_nonneg (norm_nonneg _) _)]
    refine ⟨fun _ ↦ Summable.of_finite, ?_⟩
    refine hTau.congr fun ρ ↦ ?_
    have hfun : (fun k : Fin (d (ρ : ℂ)).toNat ↦ ‖((⟨ρ, k⟩ : ZeroAtom g).1 : ℂ)‖ ^ (-q)) =
        fun _ ↦ ‖(ρ : ℂ)‖ ^ (-q) := by
      funext k
      rfl
    rw [hfun, tsum_eq_sum (s := Finset.univ)
        (fun k hk ↦ (hk (Finset.mem_univ k)).elim),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      divisor_toNat_cast hg]
  let weight : ℕ → ℝ := fun n ↦ match enumeratedZero hg n with
    | none => 0
    | some w => ‖w‖ ^ (-q)
  rw [← summable_subtype_and_compl (s := range (zeroEncode hg)) (f := weight)]
  refine ⟨?_, ?_⟩
  · let e := Equiv.ofInjective (zeroEncode hg) (zeroEncode_injective hg)
    rw [← e.summable_iff]
    refine hAtom.congr fun a ↦ ?_
    simp [weight, e, Equiv.ofInjective, enumeratedZero_zeroEncode]
  · refine (summable_zero :
        Summable (fun _ : ↑(Set.range (zeroEncode hg))ᶜ ↦ (0 : ℝ))).congr fun n ↦ ?_
    have hn : ¬∃ a : ZeroAtom g, zeroEncode hg a = n.1 := by
      simpa [Set.range] using n.2
    have hnone : enumeratedZero hg n.1 = none := by
      rw [enumeratedZero, dite_eq_right hn]
    simp [weight, hnone]

/-- The number of times `w` is listed equals the analytic multiplicity of `g` at `w`. -/
theorem enumeratedZero_ncard {g : ℂ → ℂ} (hg : Differentiable ℂ g) (w : ℂ) :
    {n | enumeratedZero hg n = some w}.ncard = analyticOrderNatAt g w := by
  classical
  let d := MeromorphicOn.divisor g Set.univ
  by_cases hw : w ∈ d.support
  · let ρ : {z : ℂ // z ∈ d.support} := ⟨w, hw⟩
    let ι : Fin (d w).toNat → {n | enumeratedZero hg n = some w} :=
      fun k ↦ ⟨zeroEncode hg ⟨ρ, k⟩, by
        change enumeratedZero hg (zeroEncode hg ⟨ρ, k⟩) = some w
        rw [enumeratedZero_zeroEncode]⟩
    have hinj : Injective ι := by
      intro k₁ k₂ hk
      have henc := zeroEncode_injective hg (congrArg Subtype.val hk)
      obtain ⟨-, hsnd⟩ := Sigma.ext_iff.mp henc
      exact eq_of_heq hsnd
    have hsurj : Surjective ι := by
      intro ⟨n, hn⟩
      obtain ⟨a, haenc, ha1⟩ := exists_zeroAtom_of_enumeratedZero hg hn
      rcases a with ⟨ρ', k⟩
      have hρ : ρ' = ρ := Subtype.ext (by simpa [ρ] using ha1)
      subst hρ
      exact ⟨k, Subtype.ext haenc⟩
    have e := Equiv.ofBijective ι ⟨hinj, hsurj⟩
    have hA : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
    have hdiv : d w = (analyticOrderNatAt g w : ℤ) :=
      hA.meromorphicOn.divisor_eq_analyticOrderNatAt (hg.analyticAt w) (mem_univ w)
    calc
      {n | enumeratedZero hg n = some w}.ncard
          = Nat.card {n | enumeratedZero hg n = some w} := rfl
      _ = (d w).toNat := by rw [← Nat.card_congr e, Nat.card_fin]
      _ = analyticOrderNatAt g w := by
        rw [hdiv, Int.toNat_natCast]
  · have hempty : {n | enumeratedZero hg n = some w} = ∅ := by
      ext n
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hn
      obtain ⟨a, -, ha⟩ := exists_zeroAtom_of_enumeratedZero hg hn
      exact hw (ha ▸ a.1.2)
    have hd : d w = 0 := by simpa [Function.mem_support, d] using hw
    have hA : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
    have heq := hA.meromorphicOn.divisor_eq_analyticOrderNatAt (hg.analyticAt w) (mem_univ w)
    rw [hd] at heq
    have hord : analyticOrderNatAt g w = 0 := by exact_mod_cast heq.symm
    simp [hempty, hord]

end CKMA
