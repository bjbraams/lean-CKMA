/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.Arith
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Complex.Arg
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Asymptotic expansions and Laplace–Tauberian limits

Poincaré expansions are defined in scalar little-o scales, with coefficient uniqueness
for nonvanishing scales. Complex sectors support Borel–Ritt realization. Watson's
lemma controls Laplace remainders and full expansions, while an interior minimum gives
the leading Laplace term. Karamata's equivalence relates positive half-line measures,
their Laplace–Stieltjes transforms and regularly varying cumulative mass.

Sources: GAPS 50.6, 50.9, 50.11 and 50.29.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology Asymptotics
open scoped BigOperators

/-- An asymptotic scale consists of successive terms which are little-o of their predecessors. -/
def IsAsymptoticScale {X : Type*} (φ : ℕ → X → ℂ) (l : Filter X) : Prop :=
  ∀ n, (φ (n + 1)) =o[l] (φ n)

/-- A Poincaré expansion in an arbitrary scalar asymptotic scale. The `N=0` truncation is omitted.
  -/
def HasAsymptoticExpansion {X : Type*} (f : X → ℂ) (a : ℕ → ℂ)
    (φ : ℕ → X → ℂ) (l : Filter X) : Prop :=
  ∀ N : ℕ, 0 < N → (fun x ↦ f x - ∑ n ∈ Finset.range N, a n * φ n x) =o[l] (φ (N - 1))

/-- Zero has its zero-coefficient expansion in every scale. -/
theorem hasAsymptoticExpansion_zero {X : Type*} (φ : ℕ → X → ℂ) (l : Filter X) :
    HasAsymptoticExpansion (fun _ ↦ 0) (fun _ ↦ 0) φ l := by
  intro N hN
  simp

/-- Coefficients are unique for a nonvanishing asymptotic scale along a nontrivial filter. -/
theorem HasAsymptoticExpansion.coefficients_eq {X : Type*} {l : Filter X} [NeBot l]
    {φ : ℕ → X → ℂ} (_hφ : IsAsymptoticScale φ l)
    (hne : ∀ n, ∀ᶠ x in l, φ n x ≠ 0) {f : X → ℂ} {a b : ℕ → ℂ}
    (ha : HasAsymptoticExpansion f a φ l) (hb : HasAsymptoticExpansion f b φ l) : a = b := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hpre : ∀ x, (∑ k ∈ Finset.range n, a k * φ k x) =
        ∑ k ∈ Finset.range n, b k * φ k x := by
      intro x
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih k (Finset.mem_range.mp hk)]
    have hd : (fun x ↦ (a n - b n) * φ n x) =o[l] (φ n) := by
      have h := (hb (n + 1) (Nat.succ_pos n)).sub (ha (n + 1) (Nat.succ_pos n))
      simp only [Nat.add_sub_cancel_right] at h
      apply h.congr_left
      intro x
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hpre x]
      ring
    by_contra hab
    have hc : 0 < ‖a n - b n‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
    obtain ⟨x, hx, hn⟩ := ((hd.bound (half_pos hc)).and (hne n)).exists
    rw [norm_mul] at hx
    exact (mul_lt_mul_of_pos_right (half_lt_self hc) (norm_pos_iff.mpr hn)).not_ge hx

/-- The open complex sector centered on angle `θ` with opening `ω`, excluding its vertex. -/
def complexSector (θ ω : ℝ) : Set ℂ :=
  {z | z ≠ 0 ∧ |Complex.arg (Complex.exp (-(θ : ℂ) * Complex.I) * z)| < ω / 2}

/-- A closed proper subsector, with vertex still omitted. -/
def closedComplexSector (θ ω : ℝ) : Set ℂ :=
  {z | z ≠ 0 ∧ |Complex.arg (Complex.exp (-(θ : ℂ) * Complex.I) * z)| ≤ ω / 2}

/-- Sectorial power expansion with estimates uniform on every closed proper subsector.
The conventional `O(z^N)` remainder is required at every order. -/
def HasSectorialPowerExpansion (f : ℂ → ℂ) (a : ℕ → ℂ) (θ ω : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η < ω → ∀ N : ℕ, ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
    ∀ z ∈ closedComplexSector θ η, ‖z‖ < r →
      ‖f z - ∑ n ∈ Finset.range N, a n * z ^ n‖ ≤ C * ‖z‖ ^ N

/-- **50.6**: Borel–Ritt realization on a sector of opening strictly less than `2π`. -/
theorem borel_ritt (a : ℕ → ℂ) (θ : ℝ) {ω : ℝ} (hω : 0 < ω) (hωπ : ω < 2 * Real.pi) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (complexSector θ ω) ∧
      HasSectorialPowerExpansion f a θ ω := by
  sorry

/-- A real-axis Laplace integral with complex amplitude. -/
def asymptoticLaplaceIntegral (a : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(x * t : ℝ)) * a t

/-- Exponential growth in the tail, with constants that need not be sharp. -/
def HasExponentialTailBound (a : ℝ → ℂ) : Prop :=
  ∃ C c T : ℝ, 0 < C ∧ 0 < T ∧ ∀ t : ℝ, T ≤ t → ‖a t‖ ≤ C * Real.exp (c * t)

/-- **50.9**, finite-order Watson remainder: local power control gives the corresponding
Laplace remainder. The `L¹` condition at zero and exponential tail are explicit. -/
theorem watson_laplace_remainder {α : ℝ} (hα : 0 < α) (N : ℕ) (a : ℝ → ℂ)
    (c : ℕ → ℂ) (hloc : ∀ R : ℝ, 0 < R → IntegrableOn a (Set.Ioo 0 R))
    (htail : HasExponentialTailBound a)
    (hrem : (fun t ↦ a t - ∑ n ∈ Finset.range N, c n * (t ^ ((n : ℝ) + α - 1) : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun t ↦ t ^ ((N : ℝ) + α - 1))) :
    (fun x ↦ asymptoticLaplaceIntegral a x - ∑ n ∈ Finset.range N,
      c n * Real.Gamma ((n : ℝ) + α) * (x ^ (-((n : ℝ) + α)) : ℝ))
      =O[atTop] (fun x : ℝ ↦ x ^ (-((N : ℝ) + α))) := by
  sorry

/-- The full Watson expansion in the inverse-power scale. -/
theorem watson_laplace_expansion {α : ℝ} (hα : 0 < α) (a : ℝ → ℂ)
    (c : ℕ → ℂ) (hloc : ∀ R : ℝ, 0 < R → IntegrableOn a (Set.Ioo 0 R))
    (htail : HasExponentialTailBound a)
    (hrem : ∀ N : ℕ,
      (fun t ↦ a t - ∑ n ∈ Finset.range N, c n * (t ^ ((n : ℝ) + α - 1) : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun t ↦ t ^ ((N : ℝ) + α - 1))) :
    HasAsymptoticExpansion (asymptoticLaplaceIntegral a)
      (fun n ↦ c n * Real.Gamma ((n : ℝ) + α))
      (fun n x ↦ (x ^ (-((n : ℝ) + α)) : ℝ)) atTop := by
  sorry

/-- **50.11**, leading interior Laplace term, expressed as a scaled limit so that vanishing
amplitude at the minimum is permitted. Higher-order coefficients remain a separate target. -/
theorem laplace_interior_minimum {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ Set.Ioo a b) (φ : ℝ → ℝ) (A : ℝ → ℂ)
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc a b)) (hA : ContinuousOn A (Set.Icc a b))
    (hcrit : deriv φ t₀ = 0) (hsecond : 0 < deriv (deriv φ) t₀)
    (hmin : ∀ t ∈ Set.Icc a b, t ≠ t₀ → φ t₀ < φ t) :
    Tendsto (fun x : ℝ ↦ (Real.sqrt x * Real.exp (x * φ t₀) : ℝ) *
      ∫ t in a..b, Complex.exp (-(x * φ t : ℝ)) * A t)
      atTop (𝓝 (A t₀ * Real.sqrt (2 * Real.pi / deriv (deriv φ) t₀))) := by
  sorry

/-- A slowly varying function is eventually positive and asymptotically invariant under every
positive dilation. Measurability is imposed by Tauberian theorems rather than by this predicate. -/
def IsSlowlyVarying (L : ℝ → ℝ) : Prop :=
  (∀ᶠ x in atTop, 0 < L x) ∧ ∀ t : ℝ, 0 < t →
    Tendsto (fun x ↦ L (t * x) / L x) atTop (𝓝 1)

/-- The cumulative mass on the nonnegative half-line. -/
def nonnegativeCumulativeMass (μ : Measure ℝ) (x : ℝ) : ℝ := (μ (Set.Icc 0 x)).toReal

/-- The real Laplace–Stieltjes transform of a positive measure. -/
def laplaceStieltjesTransform (μ : Measure ℝ) (s : ℝ) : ℝ :=
  ∫ t, Real.exp (-s * t) ∂μ

/-- **50.29**: Karamata's Tauberian equivalence for positive locally finite measures supported
on the half-line. All positive Laplace parameters are assumed integrable. -/
theorem karamatas_tauberian (μ : Measure ℝ) [IsLocallyFiniteMeasure μ]
    (hμ : μ (Set.Ici (0 : ℝ))ᶜ = 0)
    (hint : ∀ s : ℝ, 0 < s → Integrable (fun t ↦ Real.exp (-s * t)) μ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (L : ℝ → ℝ) (hL : Measurable L) (hslow : IsSlowlyVarying L) :
    Tendsto (fun s ↦ laplaceStieltjesTransform μ s / (s ^ (-ρ) * L s⁻¹))
      (𝓝[>] (0 : ℝ)) (𝓝 1) ↔
    Tendsto (fun x ↦ nonnegativeCumulativeMass μ x / (x ^ ρ * L x)) atTop
      (𝓝 ((Real.Gamma (1 + ρ))⁻¹)) := by
  sorry

end CKMA
