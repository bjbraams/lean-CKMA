/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Potential.Cutoff
public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
public import TauCeti.Analysis.PDE.Perron.Basic

/-!
# Newtonian capacity, equilibrium and boundary regularity

Variational Newtonian capacity, its inner and outer extensions, singular potentials
and equilibrium charges in dimension at least three. The statements include continuity
of capacity, capacitability, the Wiener boundary criterion, Perron resolutivity and
harmonic measure. Zero capacity and infinite potential energies are retained explicitly.
The fundamental solution and Perron envelope reuse TauCeti's Euclidean PDE modules.
Sources: GAPS 38.17, 38.20, 38.28 and 38.30.

## Main definitions

* `CKMA.dirichletEnergy`: squared Dirichlet energy of a scalar function on `ℝ^d`.
* `CKMA.compactNewtonianCapacity`, `CKMA.openNewtonianCapacity`, `CKMA.newtonianCapacity`:
  variational, inner, and outer Newtonian capacities.
* `CKMA.newtonianKernelENNReal`, `CKMA.newtonianPotential`, `CKMA.newtonianMeasureEnergy`: the
  extended Newtonian kernel, potential, and energy of a measure.
* `CKMA.IsNewtonianEquilibriumCharge`: the equilibrium-charge conditions on a compact set.
* `CKMA.IsNewtonianRegularBoundaryPoint`, `CKMA.wienerAnnularPiece`: Perron boundary regularity
  and the dyadic annular pieces of the complement in Wiener's series.
* `CKMA.upperPerronSolution`, `CKMA.RepresentsHarmonicMeasure`: the upper Perron envelope and
  representation of the Perron solution by a harmonic measure.

## Main results

* `CKMA.existsUnique_newtonianEquilibriumCharge` (**38.17**): existence and uniqueness of the
  equilibrium charge of a compact set.
* `CKMA.newtonianCapacity_eq_compact`: the outer and variational capacities agree on compact
  sets.
* `CKMA.newtonianCapacity_iUnion` (**38.20**), `CKMA.newtonianCapacity_iInter_compact`,
  `CKMA.newtonianCapacity_iUnion_le`, `CKMA.newtonianCapacity_eq_iSup_compact`: continuity from
  below and from above on compact sets, countable subadditivity, and capacitability of Borel sets.
* `CKMA.perron_resolutive` (**38.28**): continuous boundary data are resolutive on bounded open
  sets.
* `CKMA.existsUnique_harmonicMeasure`: existence and uniqueness of the harmonic probability
  measure at each point of a bounded open set.
* `CKMA.isNewtonianRegularBoundaryPoint_iff_wiener` (**38.30**): Wiener's criterion for boundary
  regularity.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

/-- Squared Dirichlet energy. For real scalar functions on Euclidean space the operator
norm of the derivative is the Euclidean norm of the gradient. -/
@[expose]
def dirichletEnergy {d : ℕ} (φ : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ φ x‖ ^ 2)

/-- The variational capacity of a compact set, before its outer extension. -/
@[expose]
def compactNewtonianCapacity {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ⨅ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (_h : IsCapacityAdmissible K φ), dirichletEnergy φ

/-- Inner capacity of an open set, defined by compact exhaustion. -/
@[expose]
def openNewtonianCapacity {d : ℕ} (U : Set (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ⨆ (K : Set (EuclideanSpace ℝ (Fin d))) (_hK : IsCompact K) (_hsub : K ⊆ U),
    compactNewtonianCapacity K

/-- Outer Newtonian capacity of an arbitrary set. -/
@[expose]
def newtonianCapacity {d : ℕ} (A : Set (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ⨅ (U : Set (EuclideanSpace ℝ (Fin d))) (_hU : IsOpen U) (_hsub : A ⊆ U),
    openNewtonianCapacity U

/-- Variational capacity is monotone before taking the outer extension. -/
theorem compactNewtonianCapacity_mono {d : ℕ} {K L : Set (EuclideanSpace ℝ (Fin d))}
    (hKL : K ⊆ L) : compactNewtonianCapacity K ≤ compactNewtonianCapacity L := by
  apply le_iInf
  intro φ
  apply le_iInf
  intro hφ
  exact iInf_le_of_le φ (iInf_le _ (hφ.mono hKL))

/-- Outer capacity is monotone by its definition through open supersets. -/
theorem newtonianCapacity_mono {d : ℕ} {A B : Set (EuclideanSpace ℝ (Fin d))}
    (hAB : A ⊆ B) : newtonianCapacity A ≤ newtonianCapacity B := by
  apply le_iInf
  intro U
  apply le_iInf
  intro hU
  apply le_iInf
  intro hB
  exact iInf_le_of_le U (iInf_le_of_le hU (iInf_le _ (hAB.trans hB)))

/-- The nonnegative Newtonian kernel in dimensions at least three, with value `∞` at its pole.
Away from zero it reuses TauCeti's normalized fundamental solution for `-Δ`.
In lower dimensions this is only the positive-part adapter of the corresponding real kernel. -/
@[expose]
def newtonianKernelENNReal (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  if x = 0 then ∞ else ENNReal.ofReal (TauCeti.newtonianKernel d x)

@[deprecated (since := "2026-11-15")] alias newtonianKernelENN := newtonianKernelENNReal

/-- Newtonian potential of a positive measure. Infinite values are retained. -/
@[expose]
def newtonianPotential {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ∫⁻ y, newtonianKernelENNReal d (x - y) ∂μ

/-- Newtonian energy, with the singular diagonal retained rather than discarded. -/
@[expose]
def newtonianMeasureEnergy {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ∫⁻ x, newtonianPotential μ x ∂μ

/-- The equilibrium-charge conditions, including support, mass, energy, global upper bound,
and the capacity-zero exceptional set on which the potential need not equal one. -/
@[expose]
def IsNewtonianEquilibriumCharge {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  IsFiniteMeasure μ ∧ μ Kᶜ = 0 ∧ μ K = newtonianCapacity K ∧
    newtonianMeasureEnergy μ = newtonianCapacity K ∧
    (∀ x, newtonianPotential μ x ≤ 1) ∧
    newtonianCapacity {x ∈ K | newtonianPotential μ x ≠ 1} = 0

/-- **38.17**: every compact set has a unique equilibrium charge; in capacity zero its
mass and hence the measure itself are zero. No positive-capacity division is needed. -/
theorem existsUnique_newtonianEquilibriumCharge {d : ℕ} (hd : 3 ≤ d)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K) :
    ∃! μ, IsNewtonianEquilibriumCharge K μ := by
  sorry

set_option linter.unusedVariables false in
/-- The compact test-function definition and the outer capacity agree on compact sets.
The proof holds in every dimension. The dimension argument is retained for compatibility. -/
theorem newtonianCapacity_eq_compact {d : ℕ} (hd : 3 ≤ d)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) :
    newtonianCapacity K = compactNewtonianCapacity K := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun φ ↦ le_iInf fun hφ ↦ ?_
    obtain ⟨hφsmooth, hφsupport, U, hU, hKU, hφU⟩ := hφ
    calc
      newtonianCapacity K ≤ openNewtonianCapacity U :=
        iInf_le_of_le U (iInf_le_of_le hU (iInf_le _ hKU))
      _ ≤ dirichletEnergy φ := by
        refine iSup_le fun L ↦ iSup_le fun _ ↦ iSup_le fun hLU ↦ ?_
        exact iInf_le_of_le φ
          (iInf_le _ ⟨hφsmooth, hφsupport, U, hU, hLU, hφU⟩)
  · refine le_iInf fun U ↦ le_iInf fun _ ↦ le_iInf fun hKU ↦ ?_
    exact le_iSup_of_le K
      (le_iSup_of_le hK (le_iSup (fun _ : K ⊆ U ↦ compactNewtonianCapacity K) hKU))

/-- **38.20**, continuity from below for arbitrary increasing sequences. -/
theorem newtonianCapacity_iUnion {d : ℕ} (hd : 3 ≤ d)
    (A : ℕ → Set (EuclideanSpace ℝ (Fin d))) (hA : Monotone A) :
    newtonianCapacity (⋃ n, A n) = ⨆ n, newtonianCapacity (A n) := by
  sorry

set_option linter.unusedVariables false in
/-- Continuity from above on decreasing compact sets.
The proof holds in every dimension. The dimension argument is retained for compatibility. -/
theorem newtonianCapacity_iInter_compact {d : ℕ} (hd : 3 ≤ d)
    (K : ℕ → Set (EuclideanSpace ℝ (Fin d))) (hK : ∀ n, IsCompact (K n))
    (hmono : Antitone K) :
    newtonianCapacity (⋂ n, K n) = ⨅ n, newtonianCapacity (K n) := by
  refine le_antisymm
    (le_iInf fun n ↦ newtonianCapacity_mono (Set.iInter_subset K n)) ?_
  refine le_iInf fun U ↦ le_iInf fun hU ↦ le_iInf fun hKU ↦ ?_
  -- Some member of the decreasing sequence lies in each open neighbourhood.
  have hdisjoint : Disjoint (K 0 ∩ Uᶜ) (⋂ n, K n) :=
    Set.disjoint_left.mpr fun _ hx hxK ↦ hx.2 (hKU hxK)
  obtain ⟨n, hn⟩ := ((hK 0).inter_right hU.isClosed_compl).elim_directed_family_closed
    K (fun m ↦ (hK m).isClosed) hdisjoint hmono.directed_ge
  have hnU : K n ⊆ U := fun x hx ↦ by
    by_contra h
    exact Set.disjoint_left.mp hn ⟨hmono (Nat.zero_le n) hx, h⟩ hx
  exact (iInf_le (fun m ↦ newtonianCapacity (K m)) n).trans
    (iInf_le_of_le U (iInf_le_of_le hU (iInf_le _ hnU)))

/-- Countable subadditivity of outer Newtonian capacity. -/
theorem newtonianCapacity_iUnion_le {d : ℕ} (hd : 3 ≤ d)
    (A : ℕ → Set (EuclideanSpace ℝ (Fin d))) :
    newtonianCapacity (⋃ n, A n) ≤ ∑' n, newtonianCapacity (A n) := by
  sorry

/-- Borel sets are capacitable. The stronger analytic-set clause remains a separate interface. -/
theorem newtonianCapacity_eq_iSup_compact {d : ℕ} (hd : 3 ≤ d)
    {A : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A) :
    newtonianCapacity A = ⨆ (K : Set (EuclideanSpace ℝ (Fin d)))
      (_hK : IsCompact K) (_hsub : K ⊆ A), newtonianCapacity K := by
  sorry

/-- Boundary regularity by attainment of all continuous boundary data by TauCeti's lower
Perron solution. The boundary domain hypotheses are supplied by the criterion theorem. -/
@[expose]
def IsNewtonianRegularBoundaryPoint {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (x₀ : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn g (frontier Ω) →
    Tendsto (TauCeti.perronSolution Ω g) (𝓝[Ω] x₀) (𝓝 (g x₀))

/-- Dyadic annular pieces of the complement at a boundary point. The index starts at zero;
removing its first finite-capacity term does not affect divergence in Wiener's criterion. -/
@[expose]
def wienerAnnularPiece {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (x₀ : EuclideanSpace ℝ (Fin d)) (k : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  Ωᶜ ∩ {x | (2 : ℝ) ^ (-(k : ℤ) - 1) ≤ dist x x₀ ∧ dist x x₀ ≤ (2 : ℝ) ^ (-(k : ℤ))}

/-- **38.30**: the classical Wiener series criterion on bounded open Euclidean sets. -/
theorem isNewtonianRegularBoundaryPoint_iff_wiener {d : ℕ} (hd : 3 ≤ d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ frontier Ω) :
    IsNewtonianRegularBoundaryPoint Ω x₀ ↔
      (∑' k : ℕ, (2 : ℝ≥0∞) ^ (k * (d - 2)) *
        newtonianCapacity (wienerAnnularPiece Ω x₀ k)) = ∞ := by
  sorry

/-- The upper envelope obtained by negating the lower Perron solution of negated data. -/
@[expose]
def upperPerronSolution {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (g : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -TauCeti.perronSolution Ω (fun y ↦ -g y) x

/-- **38.28**: continuous boundary data are resolutive even on bounded open sets with irregular
boundary points. This equality does not assert boundary attainment at those points. -/
theorem perron_resolutive {d : ℕ} (hd : 2 ≤ d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : ContinuousOn g (frontier Ω)) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) :
    TauCeti.perronSolution Ω g x = upperPerronSolution Ω g x := by
  sorry

/-- Harmonic measure represents the Perron solution by continuous boundary tests. -/
@[expose]
def RepresentsHarmonicMeasure {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) (μ : Measure (frontier Ω)) : Prop :=
  ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn g (frontier Ω) →
    (∫ y : frontier Ω, g y.1 ∂μ) = TauCeti.perronSolution Ω g x

/-- The harmonic-measure consequence of resolutivity, with a normalized probability measure. -/
theorem existsUnique_harmonicMeasure {d : ℕ} (hd : 2 ≤ d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) :
    ∃! μ : Measure (frontier Ω), IsProbabilityMeasure μ ∧ RepresentsHarmonicMeasure Ω x μ := by
  sorry

end CKMA
