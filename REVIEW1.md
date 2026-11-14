# Review of Lean Code under `CKMA/`

This document reviews all 239 Lean files (98,226 lines, 4,448 top-level declarations) under `CKMA/` against the project and Mathlib/TauCeti criteria.

---

## 1. Generality of Theorem Statements

While many foundational modules use appropriate generality (for instance `[RCLike 𝕜]` in [Frame.lean](CKMA/Analysis/InnerProductSpace/Frame.lean) and [TraceIdeals.lean](CKMA/Analysis/Operator/TraceIdeals.lean)), several modules artificially restrict scalar fields, index types, domains, or ambient spaces:

- **Scalar field restricted to `ℂ` or `ℝ` instead of `[RCLike 𝕜]` (or general fields/rings)**:
  - **Operator dilations and closed forms**: All 15 files in `CKMA/Analysis/Operator/Dilation/` (such as [Dilation.lean](CKMA/Analysis/Operator/Dilation.lean), [Wold.lean](CKMA/Analysis/Operator/Dilation/Wold.lean), and [L2Shift.lean](CKMA/Analysis/Operator/Dilation/L2Shift.lean)) and all of [ClosedForms.lean](CKMA/Analysis/Operator/ClosedForms.lean) (lines 36–104) are hardcoded to `ℂ` and a single universe `Type u`. In [Fredholm.lean](CKMA/Analysis/Operator/Fredholm.lean) (lines 96–122), `essentialSpectrum` and `IsIsolatedIn` are restricted to `ℂ`, whereas `IsFredholm` in the same file (lines 45–52) works over `[RCLike 𝕜]`.
  - **Function families and integral equations**: [L2FunctionFamilies.lean](CKMA/Analysis/InnerProductSpace/L2FunctionFamilies.lean) (lines 43–97) specializes `IsL2RieszSequence`, `IsL2RieszBasis`, and `IsL2FrameFamily` to `Lp ℂ 2 μ`, even though [Frame.lean](CKMA/Analysis/InnerProductSpace/Frame.lean) (line 42) works over `[RCLike 𝕜]`. In [IntegralEquation/Basic.lean](CKMA/Analysis/IntegralEquation/Basic.lean) (lines 38–54), `volterraIntegral` is hardcoded to `ℝ → ℂ` while `fractionalIntegral` in the same file is hardcoded to `ℝ → ℝ`.
  - **ODE determinant and Liouville helpers**: In [PeriodicAndSturm.lean](CKMA/Analysis/ODE/PeriodicAndSturm.lean) (lines 73–350), `IsFundamentalOperator` and `fundamental_monodromy` work over `[RCLike 𝕜]`, but `det_eq_sum_perm_row` (line 158), `hasDerivAt_matrix_det` (line 165), `fundamental_det_ne_zero` (line 297), and `fundamental_isInvertible` (line 346) specialize to `ℂ`. Several declarations there (lines 73, 94, 107, 222–243) also assume `[NormedSpace 𝕜 E] [NormedSpace ℝ E]` without `[IsScalarTower ℝ 𝕜 E]`.
  - **Asymptotic expansions**: In [Expansions.lean](CKMA/Analysis/Asymptotics/Expansions.lean) (lines 37–57), `IsAsymptoticScale` and `HasAsymptoticExpansion` are hardcoded to `X → ℂ`, forcing real asymptotic expansions such as `watson_laplace_expansion` (lines 128–130) to cast real powers `((x ^ (-((n : ℝ) + α)) : ℝ) : ℂ)`.
  - **Banach space geometry and compressed sensing**: [BanachSpace/Geometry.lean](CKMA/Analysis/BanachSpace/Geometry.lean) (lines 45–78: `IsEquivalentToEllOneBasis`, `HasRademacherType`, `HasRademacherCotype`, `kwapien`) and [Pietsch.lean](CKMA/Analysis/BanachSpace/Pietsch.lean) (lines 36–48: `pietsch_domination`) are restricted to `ℝ`, while [CompressedSensing.lean](CKMA/Analysis/Approximation/CompressedSensing.lean) (lines 40–69: `HasRestrictedIsometryBound`, `restricted_isometry_stable_recovery`) is restricted to `ℂ`.
  - **Polydisc Weierstrass theorem**: In [Polydisc.lean](CKMA/Analysis/Complex/Polydisc.lean) (lines 870–873), `differentiableOn_of_locallyUniformLimit` restricts the codomain to `ℂ`, whereas all earlier theorems in the file (`polydisc_taylor`, `torusIntegral_eq_of_locallyUniformLimit`) are proved for a general complex Banach space `E`.
- **Index sets restricted to `Fin n` instead of `{ι : Type*} [Fintype ι]`**:
  - [Majorization.lean](CKMA/Analysis/Convex/Majorization.lean) (lines 52–55, 351–359: `IsMajorizedBy`, `isMajorizedBy_iff_exists_doublyStochastic`), whereas Mathlib's `doublyStochastic` works over arbitrary `[Fintype ι] [DecidableEq ι]`.
  - [Duality.lean](CKMA/Analysis/Convex/Duality.lean) (lines 127–143) and [KKT.lean](CKMA/Analysis/Convex/Duality/KKT.lean) (line 746: `HasConvexKKTMultipliers`, `exists_convexKKTMultipliers`).
  - [Concentration.lean](CKMA/Probability/Concentration.lean) (line 366: `bernstein`), [HansonWright.lean](CKMA/Probability/HansonWright.lean) (line 60: `hanson_wright`), and [Symmetrization.lean](CKMA/Probability/Symmetrization.lean) (line 638: `symmetrization`).
  - [InterpolationStability/Basic.lean](CKMA/Analysis/Approximation/InterpolationStability/Basic.lean) (lines 44–60: `lagrangeCardinalPolynomial`, `lebesgueFunction`), which also hardcodes `Set.Icc (-1 : ℝ) 1` even for general Lebesgue-constant lemmas that hold on any `Set.Icc a b`.
  - [Korovkin.lean](CKMA/Analysis/Approximation/Korovkin.lean) (lines 244–249: `korovkin_iff`), which hardcodes `ℕ` along `atTop` and `Set.Icc (0 : ℝ) 1`, though the proof works for any filter `l : Filter ι` and `Set.Icc a b`.
- **Domain, measure, or topological restrictions**:
  - **Ergodic theory**: [Pointwise.lean](CKMA/Dynamics/Ergodic/Pointwise.lean) (line 48: `maximal_ergodic`) assumes `[IsProbabilityMeasure μ]`, even though the underlying proof `integral_nonneg_maximalErgodicSet` in [Maximal.lean](CKMA/Dynamics/Ergodic/Pointwise/Maximal.lean) (line 295) requires no finite or probability measure assumption at all.
  - **Haar modular character**: [Modular.lean](CKMA/MeasureTheory/Group/Modular.lean) (line 40: `map_inv_haar`) assumes `[SecondCountableTopology G]`, whereas `continuous_modularCharacter` (line 35) does not and Mathlib's Haar measure uniqueness needs only `[LocallyCompactSpace G] [T2Space G]`.
  - **Fourier circle convergence**: [CircleSummation.lean](CKMA/Analysis/Fourier/CircleSummation.lean) (lines 63–86) and [CircleConvergence.lean](CKMA/Analysis/Fourier/CircleConvergence.lean) (lines 31–74) hardcode the period `AddCircle (1 : ℝ)` rather than `AddCircle T` with `[Fact (0 < T)]`.
  - **Heisenberg uncertainty**: [Fourier/Inequalities.lean](CKMA/Analysis/Fourier/Inequalities.lean) (lines 1177–1185: `heisenberg_uncertainty`) assumes `(hf : ‖f‖ = 1)` rather than stating the scale-invariant inequality with `‖f‖ ^ 2`.
  - **Elliptic PDE estimates on unit balls**: In [EllipticEstimates.lean](CKMA/Analysis/PDE/EllipticEstimates.lean) (lines 58–146) and [Viscosity.lean](CKMA/Analysis/PDE/Viscosity.lean) (line 87), `meyers_higherIntegrability`, `krylov_safonov_classical`, `interior_schauder`, `interior_hessian_Lp`, `weakPHarmonic_regular`, and `evans_krylov` are stated only for `Metric.ball 0 1` inside `Metric.ball 0 2` rather than concentric balls `Metric.ball x₀ r` inside `Metric.ball x₀ (2 * r)`.
  - **1D restriction in Hamilton–Jacobi**: [PDE/Entropy.lean](CKMA/Analysis/PDE/Entropy.lean) (lines 80–108) restricts `hopfLaxHamiltonian` and `hopfLaxHamiltonian_viscosity` to spatial dimension 1 (`ℝ → ℝ`), whereas `IsKruzhkovSolution` (line 27) in the same file uses `EuclideanRealSpace d`.
  - **Purely order-theoretic Riesz-space lemmas carrying norm typeclasses**: In [Representation/AL.lean](CKMA/Analysis/OrderedSpace/Representation/AL.lean) (lines 133–494), [Representation/AL/Gluing.lean](CKMA/Analysis/OrderedSpace/Representation/AL/Gluing.lean) (lines 51–375), and [Representation/AM.lean](CKMA/Analysis/OrderedSpace/Representation/AM.lean) (lines 169–457), section variables attach `[NormedAddCommGroup E] [NormedSpace ℝ E] [HasSolidNorm E]` to purely algebraic lattice and order-ideal lemmas.
  - **Lyapunov stability**: In [Lyapunov.lean](CKMA/Dynamics/Lyapunov.lean) (lines 156–273), `isLyapunovStable_of_lyapunov` and `isLocallyAttracting_of_strict_lyapunov` assume `[FiniteDimensional ℝ E]` only for sphere compactness, where `[ProperSpace E]` suffices.

---

## 2. Hypotheses: Mathematical Issues in `sorry` Statements and Redundant/Unused Hypotheses

### A. Mathematical Issues in `sorry`-Admitted Statements

1. **`L¹` Fourier integral `𝓕` applied to an `L²` function in [HilbertTransform.lean](CKMA/Analysis/Fourier/HilbertTransform.lean) and [Gabor.lean](CKMA/Analysis/Fourier/Gabor.lean)**:
   - In `existsUnique_hilbertTransform_L2` ([HilbertTransform.lean](CKMA/Analysis/Fourier/HilbertTransform.lean), lines 49–54):
     `(Lp.fourierTransformₗᵢ ℝ ℂ Hf : ℝ → ℂ) =ᵐ[volume] (fun ξ ↦ -(Complex.I * (SignType.sign ξ : ℂ)) * (𝓕 f) ξ)`
     Here `f : Lp ℂ 2 (volume : Measure ℝ)`. On the right-hand side, `(𝓕 f) ξ` coerces `f` to `⇑f : ℝ → ℂ` and applies the `L¹` Bochner integral `VectorFourier.fourierIntegral`, which returns `0` whenever `f ∉ L¹(ℝ)`. The right-hand side should use `Lp.fourierTransformₗᵢ ℝ ℂ f` (or `(𝓕 f : Lp ℂ 2 volume)`), matching the left-hand side.
   - The same issue occurs in `balian_low` ([Gabor.lean](CKMA/Analysis/Fourier/Gabor.lean), lines 53–58), which writes `(𝓕 (g : ℝ → ℂ)) ξ` for `g : Lp ℂ 2 (volume : Measure ℝ)` instead of `(𝓕 g : Lp ℂ 2 (volume : Measure ℝ)) ξ` (compare [Fourier/Inequalities.lean](CKMA/Analysis/Fourier/Inequalities.lean), line 1181).

### B. Unused Hypotheses in Main/Public Theorems (Silenced in Proofs)

1. **Unused Archimedean hypothesis in Freudenthal's spectral theorem**:
   - In [Bands.lean](CKMA/Analysis/OrderedSpace/Bands.lean) (lines 397–408, `freudenthal_approximation`), line 397 sets `set_option linter.unusedVariables false in` to hide that `(ha : IsArchimedeanRieszSpace E)` is completely unused in the proof, even though the docstring at lines 398–399 claims *"The Archimedean hypothesis is explicit, as required by the usual spectral theorem."* (The proof in [Freudenthal.lean](CKMA/Analysis/OrderedSpace/Bands/Freudenthal.lean), lines 128–222, uses `Archimedean ℝ` together with `hx : x ∈ principalOrderIdeal u` and `(P 1).carrier = 0`.)
2. **Unused completeness and lower-semicontinuity hypotheses in [Convex/Duality.lean](CKMA/Analysis/Convex/Duality.lean) (lines 76–124)**:
   - `dualSubdifferential_add` (lines 76–88) takes `[CompleteSpace E]`, `(hlf : LowerSemicontinuous f)`, and `(hlg : LowerSemicontinuous g)` and explicitly discards all three via `let _ := hlf; let _ := hlg; have _ := ‹CompleteSpace E›` before calling `subdifferential_add_eq` ([Sum.lean](CKMA/Analysis/Convex/Duality/Sum.lean), line 184).
   - `exists_fenchelDual_maximizer` (lines 104–124) takes `[CompleteSpace E]`, `[CompleteSpace F]`, `hlf`, and `hlg` and discards all four (lines 114–117) before calling `exists_fenchelDual_maximizer_of_qual` ([FenchelRockafellar.lean](CKMA/Analysis/Convex/Duality/FenchelRockafellar.lean), line 567).
3. **Unused hypotheses in Sturm separation and comparison ([PeriodicAndSturm.lean](CKMA/Analysis/ODE/PeriodicAndSturm.lean), lines 648–883)**:
   - `sturm_separation` (lines 649–656) silences `(hq : ContinuousOn q (Set.Icc a b))` and `(hw : ContinuousOn w (Set.Icc a b))` with `have _hq := hq` and `have _hw := hw`.
   - `sturm_comparison` (lines 876–882) silences `(hq : ContinuousOn q (Set.Icc a b))` with `have _hq := hq`.
4. **Unused `IsClosed` and `T2Space` in Shilov boundary ([Factorization.lean](CKMA/Analysis/BanachAlgebra/Factorization.lean), lines 661–668)**:
   - `exists_shilov_boundary` silences `(hA : IsClosed (A : Set C(K, ℂ)))` via `have _hA := hA` on line 667, and `[T2Space K]` is also unused.
5. **Unused `IsOpen U` in [Polydisc.lean](CKMA/Analysis/Complex/Polydisc.lean) (lines 596–606)**:
   - `polydisc_taylor` silences `(hU : IsOpen U)` with `have _hOpen : IsOpen U := hU` on line 604.
6. **Unused `Integrable` hypothesis in [WeightedMaximal.lean](CKMA/Analysis/Fourier/WeightedMaximal.lean) (lines 686–695)**:
   - `weighted_maximal_weakType` requires `Integrable f (weightedLebesgueMeasure w)` and ignores it (`intro f _ a ha`) because `weighted_maximal_weakType_raw` (line 623) holds without integrability.
7. **Unused `(hT : ‖T‖ ≤ 1)` threaded through 21 declarations in [CommutantBlock.lean](CKMA/Analysis/Operator/Dilation/CommutantBlock.lean) (lines 351–421) and [CommutantLift.lean](CKMA/Analysis/Operator/Dilation/CommutantLift.lean) (lines 45–487)**, and unused minimality in `commutant_lifting` ([Dilation.lean](CKMA/Analysis/Operator/Dilation.lean), lines 94–100).
8. **Unused continuity and equilibrium hypotheses in [Lyapunov.lean](CKMA/Dynamics/Lyapunov.lean) (lines 159–428)**:
   - `(_heq : ∀ t, ϕ t x₀ = x₀)` in `isLyapunovStable_of_lyapunov` (line 159) and `(hF : Continuous F)` in `lasalle` (line 422).
9. **Unused `(ht : t₁ ≤ t₂)` in [Transversal.lean](CKMA/Dynamics/ODE/Planar/Transversal.lean) (lines 619–666, `finite_orbit_segment`)**.

### C. Redundant Hypotheses (Implied by Other Hypotheses or Structure Bundles)

- **Bundled predicate plus repeated unpacked fields**:
  - [WeightedMaximal.lean](CKMA/Analysis/Fourier/WeightedMaximal.lean) (lines 663–667, `weighted_maximal_iff`): takes `(hp : 1 < p) (hm : Measurable w) (hpos : ∀ᵐ x ∂volume, 0 < w x) (hloc : LocallyIntegrable w volume)`, all four of which are already conjuncts inside `IsMuckenhouptWeight p w` (lines 58–60).
  - [EllipticEstimates.lean](CKMA/Analysis/PDE/EllipticEstimates.lean) (lines 58–90, `meyers_higherIntegrability`, `abp_classical`, `krylov_safonov_classical`): takes `(hell : 0 < ell) (hΛ : ell ≤ Λ)`, which are already inside `IsUniformlyEllipticOn` ([Euclidean.lean](CKMA/Analysis/PDE/Euclidean.lean), line 68).
  - [CarlesonInterpolation.lean](CKMA/Analysis/Complex/CarlesonInterpolation.lean) (lines 42–66, `carleson_embedding_iff`, `carleson_interpolation_iff`): repeats `[IsFiniteMeasure μ]`, `μ complexUnitDiskᶜ = 0`, `∀ n, a n ∈ complexUnitDisk`, and `Function.Injective a`, which are already bundled into `IsDiskCarlesonMeasure` and `IsHardyInterpolatingSequence`.
  - [CharRoot.lean](CKMA/Probability/InfinitelyDivisible/CharRoot.lean) (lines 86–342), [Tightness.lean](CKMA/Probability/InfinitelyDivisible/Tightness.lean) (lines 182–674), and [Existence.lean](CKMA/Probability/InfinitelyDivisible/Existence.lean) (lines 43–332): over 30 lemmas assume both `[IsProbabilityMeasure μ]` and `(h : IsInfinitelyDivisible μ)`, even though `IsInfinitelyDivisible μ` ([Basic.lean](CKMA/Probability/InfinitelyDivisible/Basic.lean), line 38) has `IsProbabilityMeasure μ` as its first conjunct. The same occurs with `[IsProbabilityMeasure μ]` alongside `(hB : IsBrownianReal B μ)` in [Reflection/Past.lean](CKMA/Probability/BrownianTheory/Reflection/Past.lean) (lines 160–347) and [Reflection/Bound.lean](CKMA/Probability/BrownianTheory/Reflection/Bound.lean) (lines 64–412).
- **Redundant `[IsStarNormal A]` alongside `(hA : IsSelfAdjoint A)`**:
  - 7 lemmas in [SpectralDynamics.lean](CKMA/Analysis/Operator/SpectralDynamics.lean) (lines 765–1083) require `[IsStarNormal A]` even though `hA.isStarNormal` provides it.
- **Redundant `(hf_meas : Measurable f)` alongside `(hf : Integrable f μ)`**:
  - Over 30 lemmas across `CKMA/Dynamics/Ergodic/Pointwise/` (such as [Birkhoff.lean](CKMA/Dynamics/Ergodic/Pointwise/Birkhoff.lean), lines 221–415; [KingmanFull.lean](CKMA/Dynamics/Ergodic/Pointwise/KingmanFull.lean), lines 206–326; and [KingmanConv.lean](CKMA/Dynamics/Ergodic/Pointwise/KingmanConv.lean), lines 337–669) require both `Integrable f μ` and `Measurable f`.
- **Untyped shadowing binder `hE` in [Representation/AL/Gluing.lean](CKMA/Analysis/OrderedSpace/Representation/AL/Gluing.lean) (lines 991–1119)**:
  - `variable (hE : ...)` is declared at line 888, and then `norm_sum_indexProjection` (line 991), `summable_norm_indexProjection` (line 999), `summable_indexProjection` (line 1017), and `tsum_norm_indexProjection` (line 1119) write `theorem ... hE ...`, introducing an untyped binder named `hE` that shadows the section variable.
- **Global `set_option linter.unusedSectionVars false`**:
  - Enabled across 14 files (7 in `Analysis/OrderedSpace/` and 7 in `Dynamics/` and `Probability/BrownianTheory/`), attaching unused section variables (such as `[IsProbabilityMeasure μ]` on deterministic grid/set lemmas in [Reflection/Grid.lean](CKMA/Probability/BrownianTheory/Reflection/Grid.lean), lines 35–128) to many declarations.

---

## 3. Adherence to Mathlib Naming Conventions

Adherence is generally high, with the following specific violations:

- **Structures and `Type` abbreviations starting with lowercase instead of `UpperCamelCase`**:
  - `structure bandIndex` in [Gluing.lean](CKMA/Analysis/OrderedSpace/Representation/AL/Gluing.lean) (line 94) → should be `BandIndex`.
  - `abbrev bandFiber` and `abbrev alCarrier` in [Sum.lean](CKMA/Analysis/OrderedSpace/Representation/AL/Gluing/Sum.lean) (lines 41, 49) → should be `BandFiber` and `ALCarrier`.
- **`Prop`-valued `def`s starting with lowercase instead of `UpperCamelCase`**:
  - `def ExtremalChain.stopped : Prop` in [Polynomial.lean](CKMA/Analysis/Approximation/Polynomial.lean) (line 662) → `ExtremalChain.Stopped` or `ExtremalChain.IsStopped`.
  - `def kingmanWindow ... : Prop` in [KingmanOrbit.lean](CKMA/Dynamics/Ergodic/Pointwise/KingmanOrbit.lean) (line 32) → `IsKingmanWindow` or `HasKingmanWindow`.
  - `def kingmanExcursion ... : Prop` in [KingmanLimit.lean](CKMA/Dynamics/Ergodic/Pointwise/KingmanLimit.lean) (line 33) → `HasKingmanExcursion`.
  - `private def incrementTail ... : Prop` in [HolderPath.lean](CKMA/Probability/BrownianTheory/HolderPath.lean) (line 239) → `HasIncrementTail`.
- **Value/function `def`s using uppercase or underscores instead of `lowerCamelCase`**:
  - `def X` and `def Y` in [YoungIntegral.lean](CKMA/Analysis/RoughPath/Sewing/YoungIntegral.lean) (lines 75–77, single capital letters exported in `CKMA.YoungLoeve`).
  - `def hilbertBasis_star` and `def hilbertBasis_prod` in [HilbertSchmidt.lean](CKMA/Analysis/IntegralEquation/HilbertSchmidt.lean) (lines 238, 361) → `hilbertBasisStar`, `hilbertBasisProd`.
  - Structure field `Carrier : Type u` in [HilbertModel.lean](CKMA/Analysis/InnerProductSpace/HilbertModel.lean) (line 27) → `carrier`.
  - Misleading `CLM` suffix on `private def freqBumpCLM (n : ℕ) : V → ℂ` in [Fourier/Inequalities.lean](CKMA/Analysis/Fourier/Inequalities.lean) (line 611), which is a plain function, not a `ContinuousLinearMap`.
- **Theorem and lemma naming violations (`snake_case` and `conclusion_of_hypothesis`)**:
  - In [YoungIntegral.lean](CKMA/Analysis/RoughPath/Sewing/YoungIntegral.lean) (lines 67–85), 8 public theorems in `CKMA.YoungLoeve` are named like local hypothesis variables: `hab`, `hp`, `hq`, `hpq`, `hX`, `hY`, `hVp`, `hVq`.
  - Multi-conjunct `_properties` theorems in [PolynomialJulia.lean](CKMA/Dynamics/Complex/PolynomialJulia.lean) (lines 76–107): `polynomial_escapeRate_properties` and `mandelbrot_properties` bundle 4–5 distinct results into a conjunction instead of separate lemmas (`continuous_polynomialEscapeRate`, `isCompact_mandelbrotSet`, etc.).
  - `camelCase` embedded inside theorem names where no matching definition exists: `hardSphere_hTheorem` ([Boltzmann.lean](CKMA/Analysis/PDE/Boltzmann.lean), line 78), `meyers_higherIntegrability` ([EllipticEstimates.lean](CKMA/Analysis/PDE/EllipticEstimates.lean), line 58), `wave_finitePropagation` ([Wave.lean](CKMA/Analysis/PDE/Wave.lean), line 75), `exists_minimalIsometricDilationData` ([Minimal.lean](CKMA/Analysis/Operator/Dilation/Minimal.lean), line 239).
  - Non-descriptive theorem names: `klmn` ([ClosedForms.lean](CKMA/Analysis/Operator/ClosedForms.lean), line 89), `numerous_progression_three` and `numerous_progression_long` ([Multiple.lean](CKMA/Dynamics/Ergodic/Recurrence/Multiple.lean), lines 415, 808), `complex_norm_le_div_nat_zero` ([Factorization.lean](CKMA/Analysis/BanachAlgebra/Factorization.lean), line 57; should be `eq_zero_of_norm_le_div_nat`).

---

## 4. Declaration and Structure Field Docstrings

Out of 4,448 top-level declarations, 98.4% have `/-- ... -/` docstrings. The missing docstrings are concentrated in a few files:

- **56 public declarations missing docstrings**:
  - [Variation.lean](CKMA/Analysis/RoughPath/Sewing/Variation.lean) (lines 60–627): 32 public lemmas (`pathVariationPower_eq_iSup`, `variationSum_point`, `pathVariationPower_point`, `variationReal_point`, `nodeSeq_of_le`, `nodeSeq_zero`, `nodeSeq_size`, `monotone_nodeSeq`, `variationSum_eq_stepSum`, `variationSum_concat`, `oneStep_le`, `variationReal_mono`, `variationReal_superadd`, `norm_increment_le`, `norm_le_variationReal`, `dropNode_of_lt`, `dropNode_of_ge`, `monotone_dropNode`, `youngPartial_succ`, `youngPartial_pos_term`, `summable_youngLoose`, `youngPartial_le_loose`, `youngPartial_step`, `youngTheta_pos`, `youngAlpha_pos`, `youngBeta_pos`, `youngAlpha_add_beta`, `youngCtrl_nonneg`, `youngModulus_nonneg`, `youngModulus_eq_ctrl_pow`, `youngCtrl_superadd`, `youngCtrl_mono`).
  - [YoungIntegral.lean](CKMA/Analysis/RoughPath/Sewing/YoungIntegral.lean) (lines 91–898): 19 public lemmas (`monotone_gridNode`, `gridNode_zero`, `gridNode_last`, `youngGrid_eq_step`, `tendsto_youngGrid`, `youngLimit_same`, `continuous_equalNode`, `equalNode_mapsTo`, `continuousOn_youngPiece`, `continuousOn_youngGrid`, `continuousOn_youngLimit`, `youngCtrl_same`, `continuousOn_ctrl_right`, `two_rpow_neg`, `sewingConstant_shift`, `norm_youngLimit_sharp`, `youngLimit_seq`, `youngLimit_nodes`, `partition_step_le_mesh`).
  - [VariationEstimate.lean](CKMA/Analysis/RoughPath/Sewing/VariationEstimate.lean) (line 156): `norm_young_defect`.
  - [Wold.lean](CKMA/Analysis/Operator/Dilation/Wold.lean) (lines 154, 316): `woldShift_apply` and `inner_woldShift_woldCoefficient`.
  - [Representation.lean](CKMA/Analysis/CStarAlgebra/Representation.lean) (line 63): `cyclicOrbit_apply`.
  - [LpUniform.lean](CKMA/Analysis/FunctionalAnalysis/WeakCompactness/LpUniform.lean) (line 211): `phaseQuotient_zero`.
- **14 `private` declarations missing docstrings**:
  - [Korovkin.lean](CKMA/Analysis/Approximation/Korovkin.lean) (lines 73–232): `unitIntervalQuadratic_apply`, `unitIntervalQuadratic_nonneg`, `eval_unitIntervalQuadratic`, `korovkinDeviation_tendsto_zero`, `one_nonneg_unitInterval`, `norm_sub_le_korovkin`.
  - [Representation.lean](CKMA/Analysis/CStarAlgebra/Representation.lean) (lines 113, 149): `cyclicRepresentationIsometry_apply` and `cyclicRepresentationEquiv_apply`.
  - [Pattern.lean](CKMA/Analysis/Real/Dini/Pattern.lean) (lines 37–84): `right_le`, `left_le`, `ne_zero_of_top`, `ne_zero_of_bot`.
  - [Covering.lean](CKMA/Analysis/Real/Dini/Covering.lean) (line 68): `finset_packing_lower_aux`.
  - [Fourier/Inequalities.lean](CKMA/Analysis/Fourier/Inequalities.lean) (line 52): `pi_pos_four`.
- **18 structure/class fields missing docstrings**:
  - [YoungIntegral.lean](CKMA/Analysis/RoughPath/Sewing/YoungIntegral.lean) (lines 41–54): all 14 fields of `class YoungData` (`a`, `b`, `p`, `q`, `hab`, `hp`, `hq`, `hpq`, `X`, `Y`, `hX`, `hY`, `hVp`, `hVq`).
  - [Multiple.lean](CKMA/Dynamics/Ergodic/Recurrence/Multiple.lean) (lines 258–261): all 4 fields of `private structure IndexAP` (`i`, `u`, `hu`, `hiu`).

---

## 5. Namespaces

- All declarations in all 235 implementation files live inside the `CKMA` namespace (the 4 top-level umbrella files [Analysis.lean](CKMA/Analysis.lean), [Dynamics.lean](CKMA/Dynamics.lean), [MeasureTheory.lean](CKMA/MeasureTheory.lean), and [Probability.lean](CKMA/Probability.lean) only re-export imports).
- **Sub-namespace consistency**:
  - 18 files open domain or type sub-namespaces under `CKMA`: `CKMA.WeakCompactness`, `CKMA.EberleinSmulian`, `CKMA.Bohr`, `CKMA.Sewing`, `CKMA.YoungLoeve`, `CKMA.OrderUnitSpace`, `CKMA.ClosedPrincipalBand`, `CKMA.OpenInterval`, `CKMA.RatInterval`, `CKMA.OpenRectangle`, `CKMA.RatRectangle`, and `CKMA.TimePartition`.
  - By contrast, the internal files of `CKMA/Analysis/Real/Dini/` ([Assembly.lean](CKMA/Analysis/Real/Dini/Assembly.lean), line 29; [Infinite.lean](CKMA/Analysis/Real/Dini/Infinite.lean), lines 136–315; [FiniteGap.lean](CKMA/Analysis/Real/Dini/FiniteGap.lean), lines 81–401; [Young.lean](CKMA/Analysis/Real/Dini/Young.lean), line 33) place generic helper names (`exceptional`, `leftSteep`, `infiniteUp`, `infiniteDown`, `finiteGap`, `finiteStrict`, `uniformCross`) directly into the root `CKMA` namespace rather than `CKMA.Dini` or `private`.

---

## 6. Module System (`module` Keyword and `public import` vs `import`)

- **Every file (239 / 239) is a `module`** beginning with `module`.
- **Overuse of `public import` for proof-only dependencies**:
  - `public import` should be used only for what declaration statements need, and plain `import` for proof-only dependencies. Almost every file in `CKMA` uses `public import` for all imports, including heavy proof-only dependencies and even `public import Mathlib.Tactic` in 7 files ([ClassicalSequences.lean](CKMA/Analysis/Inequalities/ClassicalSequences.lean), line 11; [OrthogonalPolynomial/Basic.lean](CKMA/Analysis/OrthogonalPolynomial/Basic.lean), line 21; [Baire.lean](CKMA/Analysis/Real/Baire.lean), line 12; [Covering.lean](CKMA/Analysis/Real/Dini/Covering.lean), line 12; [FiniteGap.lean](CKMA/Analysis/Real/Dini/FiniteGap.lean), line 12; [Infinite.lean](CKMA/Analysis/Real/Dini/Infinite.lean), line 12; and [MountainPass.lean](CKMA/Analysis/Variational/MountainPass.lean), line 11).

---

## 7. Module Docstrings (`/-! ... -/`)

- Every file (239 / 239) has a `/-! ... -/` module docstring with `# Title` and a `Source: GAPS ...` citation.
- **Missing `## Main definitions`, `## Main results`, and `## Notation` sections**:
  - None of the 239 module docstrings use `## Main definitions` or `## Main results` headings; all are written as 1–2 short prose paragraphs.
  - Several module docstrings are very brief (5–7 lines) or incomplete—most notably [GaussianLogSobolev/OneDim.lean](CKMA/Probability/GaussianLogSobolev/OneDim.lean) (lines 25–30), whose 6-line docstring mentions only Gaussian integration by parts (lines 41–166) and omits the Ornstein–Uhlenbeck semigroup, generator identity, and Fisher information theory that occupy lines 243–1022 (~80% of the file).

---

## 8. Simplifying or Breaking Up Long Proofs

There are 223 proofs of 70+ lines across `CKMA/`, including 15 proofs between 260 and 501 lines:

- [Upper.lean](CKMA/Analysis/Approximation/InterpolationStability/Upper.lean) (lines 547–1046, `lebesgueFunction_chebyshev_midpoint_ge`, **501 lines**, requires `set_option maxHeartbeats 1000000`): Contains 5 self-contained intermediate steps (`hrecip` lines 641–655, `hdef` lines 656–713, `herr` lines 714–751, `hmain` lines 752–845, `hcorr` lines 846–1038) that can be extracted into separate lemmas, eliminating the `maxHeartbeats` bump.
- [Upper.lean](CKMA/Analysis/Approximation/InterpolationStability/Upper.lean) (lines 55–463, `sum_chebyshevLebesgueCorr_le`, **409 lines**): Extract `hdrop` (lines 89–148), `hleftInt` (lines 200–356), and `hrightInt` (lines 357–446).
- [Multiple.lean](CKMA/Dynamics/Ergodic/Recurrence/Multiple.lean) (lines 415–805, `numerous_progression_three`, **391 lines**): Split the double-counting Cauchy–Schwarz step from the Varnavides window-lifting step.
- [Freudenthal.lean](CKMA/Analysis/OrderedSpace/Bands/Freudenthal.lean) (lines 128–505, `freudenthal_components`, **379 lines**): Extract dyadic partition of unity (`∑ P_k = id`), band projection orthogonality, and scalar sandwiching into 3 helper lemmas.
- [Norming.lean](CKMA/Analysis/FunctionalAnalysis/WeakCompactness/Norming.lean) (lines 51–389, `exists_list_norming`, **339 lines**): Proving `hTlin_le` (lines 104–129) before `hlip` (lines 59–102) makes `hlip` a 2-line corollary (`simpa [map_sub] using hTlin_le (c - d)`), and using `Submodule.liftQ` replaces the manual `Quotient.lift` block at lines 140–188.
- [Kirszbraun.lean](CKMA/Analysis/Real/Kirszbraun.lean) (lines 176–494, `exists_iInter_closedBall_of_forall_finset`, **320 lines**; and lines 498–805, `exists_common_point_closedBall_of_dist_le`, **309 lines**): Using `exists_norm_eq_iInf_of_complete_convex` (already imported and used on line 597) in `exists_iInter_closedBall_of_forall_finset` avoids the `+ 1/(n+1)` slack and eliminates a 60-line parallelogram-law block that is repeated twice (lines 290–391 and 426–484).
- [KingmanClosure.lean](CKMA/Dynamics/Ergodic/Pointwise/KingmanClosure.lean) (lines 105–408, `kingman_limit_of_measurable`, **304 lines**) and [KingmanLimit.lean](CKMA/Dynamics/Ergodic/Pointwise/KingmanLimit.lean) (lines 147–432, `kingmanLiminfReal_integral_eq`, **286 lines**).
- [LargeDeviations.lean](CKMA/Probability/LargeDeviations.lean) (lines 224–522, `limsup_laplaceRate_le`, **300 lines**): Extract the compact-set finite covering and open-slice rate bound.
- [Boettcher.lean](CKMA/Dynamics/Complex/Linearization/Boettcher.lean) (lines 84–382, `exists_boettcher_data`, **299 lines**): Split convergence, analyticity, derivative at `0`, and functional equation into separate lemmas.
- [KKT.lean](CKMA/Analysis/Convex/Duality/KKT.lean) (lines 345–630, `exists_kkt_weights`, **287 lines**), [Accretive.lean](CKMA/Analysis/Semigroup/Accretive.lean) (lines 261–544, `accretiveSemigroup_add_domain`, **285 lines**), [MountainPass.lean](CKMA/Analysis/Variational/MountainPass.lean) (lines 355–638, `exists_small_fderiv_of_slope`, **285 lines**), and [Symmetrization.lean](CKMA/Probability/Symmetrization.lean) (lines 358–635, `expectedSup_ghost_le_twice_signed`, **278 lines**, requires `maxHeartbeats 2000000`).

---

## 9. Replacing Proofs or Elements of Proofs with Mathlib, TauCeti, or Existing CKMA Results

1. **Brouwer's fixed-point theorem is proved in [Monotone.lean](CKMA/Analysis/Nonlinear/Monotone.lean) (lines 50–393) while `sorry`-admitted in [FixedPoint.lean](CKMA/Analysis/Nonlinear/FixedPoint.lean) (lines 35–38)**:
   - [FixedPoint.lean](CKMA/Analysis/Nonlinear/FixedPoint.lean) (lines 35–38) admits `exists_fixedPoint_brouwer` with `sorry`, while [Monotone.lean](CKMA/Analysis/Nonlinear/Monotone.lean) (lines 300–391) proves the **exact same statement** as `private theorem exists_fixedPoint_compact_convex` (in a 344-line `section FixedPoint`, lines 50–393). Moving `section FixedPoint` into `FixedPoint.lean` immediately resolves `exists_fixedPoint_brouwer` and shrinks `Monotone.lean` from 950 lines to ~610 lines.
2. **Direct duplication of TauCeti**:
   - [Planar/Basic.lean](CKMA/Dynamics/ODE/Planar/Basic.lean) (lines 263–290, `isPreconnected_iInter_of_directed`) re-proves `TauCeti.isPreconnected_iInter_of_directed` (noted in its docstring at line 262).
   - [Clarke/Representation.lean](CKMA/Analysis/Convex/Clarke/Representation.lean) (lines 66–95, `finiteDimensional_strongDual`, `finrank_strongDual`, `exists_strongDual_eq_apply`) manually proves finite-dimensional reflexivity facts already in `TauCeti.Analysis.Normed.Module.Dual.Reflexive.Basic` (which is imported in [Renorming.lean](CKMA/Analysis/BanachSpace/Renorming.lean)).
3. **Direct duplications of Mathlib lemmas**:
   - `convexOn_sum` in [SpecialFunctions/Classical.lean](CKMA/Analysis/SpecialFunctions/Classical.lean) (lines 222–233) → Mathlib's `ConvexOn.sum`.
   - `continuous_finset_sum_apply` in [Monotone.lean](CKMA/Analysis/Nonlinear/Monotone.lean) (lines 458–470) and `continuous_finset_sum'` in [PeriodicAndSturm.lean](CKMA/Analysis/ODE/PeriodicAndSturm.lean) (lines 284–294) → Mathlib's `continuous_finset_sum`.
   - `measurable_finset_sum` in [BrownianQuadraticVariation.lean](CKMA/Probability/BrownianQuadraticVariation.lean) (lines 305–316) and `measurable_partialSum` in [LimitTheorems/LargeDeviations.lean](CKMA/Probability/LimitTheorems/LargeDeviations.lean) (lines 353–365) → Mathlib's `Finset.measurable_sum`.
   - `measurable_abs` in [Symmetrization.lean](CKMA/Probability/Symmetrization.lean) (lines 172–175) → `continuous_abs.measurable` / `Measurable.abs`.
   - `integral_id_zero_one` in [Newton.lean](CKMA/Analysis/Nonlinear/Newton.lean) (lines 398–407) → Mathlib's `integral_id`.
   - `le_of_forall_pos_le_add` in [Representation/AM.lean](CKMA/Analysis/OrderedSpace/Representation/AM.lean) (lines 363–366) → Mathlib's `le_of_forall_pos_le_add`.
   - `harmonic_mono` in [InterpolationStability/Estimates.lean](CKMA/Analysis/Approximation/InterpolationStability/Estimates.lean) (lines 756–762) → `Mathlib.NumberTheory.Harmonic.Bounds`.
   - `circleIntegral_inv_of_inside` in [Laurent.lean](CKMA/Analysis/Complex/Laurent.lean) (lines 179–181) → `circleIntegral.integral_sub_inv_of_mem_ball`.
   - `integral_comp_measurePreserving` in [Maximal.lean](CKMA/Dynamics/Ergodic/Pointwise/Maximal.lean) (lines 199–205) → `MeasurePreserving.integral_comp'`.
   - `symm_iterate_apply` and `iterate_symm_apply` in [Recurrence.lean](CKMA/Dynamics/Ergodic/Recurrence.lean) (lines 72–95) → `Equiv.symm_iterate`.
   - `ereal_max_eq_sup` and `ereal_coe_max` in [KingmanFull.lean](CKMA/Dynamics/Ergodic/Pointwise/KingmanFull.lean) (lines 42–66) → `max_eq_sup` and `EReal.coe_max`.
   - `OrderUnitSpace` ([AL.lean](CKMA/Analysis/OrderedSpace/Representation/AL.lean), lines 546–662) and `ClosedPrincipalBand` ([Gluing.lean](CKMA/Analysis/OrderedSpace/Representation/AL/Gluing.lean), lines 452–633) manually construct ~120 lines each of `AddCommGroup`/`Module`/`CompleteSpace` subtype instances; defining `principalOrderIdeal u` as a `Submodule ℝ E` and `ClosedPrincipalBand u` via `Submodule.topologicalClosure` lets Mathlib synthesize these instances automatically.

---

## 10. Excessively Long Files (>1,000 Lines and >1,500-Line Hard Limit)

Per [AGENTS.md](AGENTS.md), ~1,000 lines is a candidate for splitting along a natural mathematical seam, and **1,500 lines is the hard limit**.

### A. Exceeding or At the 1,500-Line Hard Limit (Immediate Splits Required)

1. **[SpectralDynamics.lean](CKMA/Analysis/Operator/SpectralDynamics.lean) (1,585 lines — EXCEEDS 1,500-LINE HARD LIMIT)**:
   - Split along its natural seams: (1) Birman–Schwinger principle (lines 74–152, GAPS 22.38), (2) Lorentz CFC approximants and spectral measure atoms (lines 274–812, `SpectralDynamics/Lorentz.lean`), and (3) Cesàro phase averages and RAGE theorems (lines 153–273, 813–1585). Also deduplicate the ~90-line precompact cover proof shared between `tendsto_cesaro_normSq_compact` and `rage_purePoint`.
2. **[Concentration.lean](CKMA/Probability/Concentration.lean) (1,500 lines — AT THE HARD LIMIT, with blank lines between declarations stripped from line 838 to 1500 to fit in 1,500 lines)**:
   - Split into: (1) `Concentration/Basic.lean` (sub-Gaussian predicates and equivalence chain, GAPS 48.62, lines 58–79, 193–256, 452–837), (2) `Concentration/Bernstein.lean` (Bernstein's inequality, GAPS 48.61, lines 81–192, 258–451), and (3) `Concentration/JohnsonLindenstrauss.lean` (Rademacher chaos and JL lemma, GAPS 46.15, lines 838–1500).

### B. Files Between 1,000 and 1,500 Lines (15 Candidates for Splitting)

- [BrownianQuadraticVariation.lean](CKMA/Probability/BrownianQuadraticVariation.lean) (**1,343 lines**): Split out `TimePartition` (lines 59–303) and the general finite-sum Kolmogorov maximal inequality (`measure_max_partialSum_ge_le`, lines 304–715) from the Brownian $L^2$/a.s. quadratic variation proofs (lines 716–1343).
- [RoughPath/Sewing/Construction.lean](CKMA/Analysis/RoughPath/Sewing/Construction.lean) (**1,331 lines**): Split dyadic construction and Hölder bound (`sewnIncrement`, lines 1–593) from uniform-grid additivity and partition convergence (lines 594–1331).
- [SpecialFunctions/Classical.lean](CKMA/Analysis/SpecialFunctions/Classical.lean) (**1,300 lines**): Contains three completely disjoint topics: Gauss gamma multiplication (lines 57–584, GAPS 49.6), Gauss hypergeometric ODE and Kummer transformation (lines 586–937, GAPS 49.13), and Bessel generating series and integral representation (lines 938–1300, GAPS 49.30).
- [Approximation/Polynomial.lean](CKMA/Analysis/Approximation/Polynomial.lean) (**1,252 lines**): Split the Chebyshev `ExtremalChain` alternation proof (lines 45–1190) into `Approximation/Polynomial/Chebyshev.lean`.
- [Dynamics/Ergodic/Recurrence/Multiple.lean](CKMA/Dynamics/Ergodic/Recurrence/Multiple.lean) (**1,251 lines**): Split the purely finitary Varnavides/Roth combinatorics (lines 1–813, which uses no measure theory) from the ergodic Cesàro averages (lines 814–1251).
- [Inequalities/ClassicalSequences.lean](CKMA/Analysis/Inequalities/ClassicalSequences.lean) (**1,214 lines**): Contains two independent sections with zero shared declarations: Newton–Maclaurin inequalities (lines 51–580, GAPS 11.9) and the discrete Hardy inequality (lines 582–1214, GAPS 11.32).
- [Fourier/Inequalities.lean](CKMA/Analysis/Fourier/Inequalities.lean) (**1,187 lines**): Split smooth coordinate integration-by-parts and $L^1 \cap L^2$ Fourier inversion (lines 46–893) from the cutoff commutator and Heisenberg uncertainty proof (lines 894–1187).
- [Fourier/Sampling.lean](CKMA/Analysis/Fourier/Sampling.lean) (**1,186 lines**): Split periodic frequency-domain partial sums on `AddCircle (2 * B)` (lines 36–579) from the Shannon sampling theorem (lines 580–1186).
- [Approximation/InterpolationStability/Estimates.lean](CKMA/Analysis/Approximation/InterpolationStability/Estimates.lean) (**1,170 lines**) and [Upper.lean](CKMA/Analysis/Approximation/InterpolationStability/Upper.lean) (**1,048 lines**).
- [OrderedSpace/Representation/AL/Gluing.lean](CKMA/Analysis/OrderedSpace/Representation/AL/Gluing.lean) (**1,142 lines**): Split `posBandPart`, `ClosedPrincipalBand`, and `bandProjection` (lines 120–858) into `BandProjection.lean`.
- [RoughPath/Sewing/YoungIntegral.lean](CKMA/Analysis/RoughPath/Sewing/YoungIntegral.lean) (**1,058 lines**): Split uniform-grid limit and additivity (lines 1–687) from sharp defect iteration and partition convergence (lines 688–1058).
- [ODE/PeriodicAndSturm.lean](CKMA/Analysis/ODE/PeriodicAndSturm.lean) (**1,028 lines**): Split Floquet theory and Liouville's formula (lines 72–372, GAPS 31.17) from Sturm separation and comparison (lines 374–1028, GAPS 31.20).
- [Semigroup/Approximation.lean](CKMA/Analysis/Semigroup/Approximation.lean) (**1,026 lines**): Split Duhamel variation of constants and integrated solutions (lines 44–996, GAPS 24.13) into `Semigroup/Inhomogeneous.lean`, leaving Trotter–Kato and Chernoff (lines 997–1026) in `Approximation.lean`.
- [Probability/GaussianLogSobolev/OneDim.lean](CKMA/Probability/GaussianLogSobolev/OneDim.lean) (**1,022 lines**): Split 1D Gaussian integration by parts (lines 1–242) from the Ornstein–Uhlenbeck semigroup and Fisher information (lines 243–1022).

---

## 11. File Organization and Cross-Section Imports

1. **Cross-section imports not going through `<Section>/Basic.lean` ([AGENTS.md](AGENTS.md))**:
   - Currently only 6 sections (`Analysis/Complex`, `Analysis/Convex`, `Analysis/IntegralEquation`, `Analysis/Interpolation`, `Analysis/OrthogonalPolynomial`, `Probability/InfinitelyDivisible`) have a `<Section>/Basic.lean` file. As a result, cross-section imports pull in full implementation files:
     - [BanachSpace/Geometry.lean](CKMA/Analysis/BanachSpace/Geometry.lean) (lines 8–9) imports `CKMA.Analysis.FunctionalAnalysis.WeakCompactness` and `CKMA.Analysis.InnerProductSpace.HilbertModel`.
     - [CStarAlgebra/Representation.lean](CKMA/Analysis/CStarAlgebra/Representation.lean) (line 9), [Representation/Faithful.lean](CKMA/Analysis/CStarAlgebra/Representation/Faithful.lean) (line 8), and [Operator/Dilation/Minimal.lean](CKMA/Analysis/Operator/Dilation/Minimal.lean) (line 8) import `CKMA.Analysis.InnerProductSpace.HilbertModel`.
     - [Fourier/Gabor.lean](CKMA/Analysis/Fourier/Gabor.lean) (line 8) and [Fourier/NonuniformSampling.lean](CKMA/Analysis/Fourier/NonuniformSampling.lean) (line 9) import `CKMA.Analysis.InnerProductSpace.L2FunctionFamilies`.
     - [ComplexGeometry/Beltrami.lean](CKMA/Analysis/ComplexGeometry/Beltrami.lean) (line 8) imports `CKMA.Analysis.Complex.Hardy` solely for `complexUnitDisk` and `isOpen_complexUnitDisk` (which belong in [Complex/Basic.lean](CKMA/Analysis/Complex/Basic.lean)).
     - [IntegralEquation/Mercer.lean](CKMA/Analysis/IntegralEquation/Mercer.lean) (line 8) imports `CKMA.Analysis.Operator.TraceIdeals`.
     - [Operator/Dilation.lean](CKMA/Analysis/Operator/Dilation.lean) (line 8) imports `CKMA.Analysis.CStarAlgebra.Representation`.
     - [Microlocal/Symbols.lean](CKMA/Analysis/Microlocal/Symbols.lean) (line 8) and [Sobolev/CapacityAndBBM.lean](CKMA/Analysis/Sobolev/CapacityAndBBM.lean) (lines 8–9) import `CKMA.Analysis.PDE.Euclidean` and `CKMA.Analysis.Potential.Cutoff`.
     - [HansonWright.lean](CKMA/Probability/HansonWright.lean) (line 10), [HansonWright/Estimates.lean](CKMA/Probability/HansonWright/Estimates.lean) (line 8), and [HansonWright/OffDiagonal.lean](CKMA/Probability/HansonWright/OffDiagonal.lean) (line 10) import the 1,500-line `CKMA.Probability.Concentration` (pulling in Bernstein and Johnson–Lindenstrauss just to access `HasPsiTwoBound` and `psiTwoGauge`).
     - [BrownianTheory/Existence.lean](CKMA/Probability/BrownianTheory/Existence.lean) (line 9) imports `CKMA.Probability.ProjectiveLimit`, and [LimitTheorems/LargeDeviations.lean](CKMA/Probability/LimitTheorems/LargeDeviations.lean) (line 8) imports `CKMA.Probability.LargeDeviations`.
2. **Disconnected submodule in `GaussianLogSobolev`**:
   - [GaussianLogSobolev.lean](CKMA/Probability/GaussianLogSobolev.lean) does not import `CKMA.Probability.GaussianLogSobolev.OneDimLSI` (or `OneDim` / `Entropy`), leaving the 2,628 lines in `GaussianLogSobolev/{OneDim,Entropy,OneDimLSI}.lean` disconnected from `GaussianLogSobolev.lean`, and duplicating `nonnegativeFunctionEntropy` ([GaussianLogSobolev.lean](CKMA/Probability/GaussianLogSobolev.lean), line 38) as `entropyExpr` ([OneDimLSI.lean](CKMA/Probability/GaussianLogSobolev/OneDimLSI.lean), line 39).
3. **Unused or duplicate imports**:
   - [CKMA/Analysis.lean](CKMA/Analysis.lean) (lines 178–181) duplicates `public import CKMA.Analysis.InnerProductSpace.HilbertModel` (already at line 76) and `public import CKMA.Analysis.Potential.Cutoff` (already at line 135).
   - [EntireGrowth.lean](CKMA/Analysis/Complex/EntireGrowth.lean) (line 8) has an unused `public import CKMA.Analysis.Complex.PlaneApproximation`.
   - [Fock.lean](CKMA/Analysis/Complex/Fock.lean) (line 8) has an unused `public import CKMA.Analysis.Complex.Hardy`.
   - [SpectralDynamics.lean](CKMA/Analysis/Operator/SpectralDynamics.lean) (line 8) has an unused `public import CKMA.Analysis.Operator.TraceIdeals`.

---

## 12. Repeated Proof Blocks and Duplicated Definitions That Should Be Turned into Lemmas

1. **Exact duplicate theorems and definitions**:
   - [Polydisc.lean](CKMA/Analysis/Complex/Polydisc.lean) (lines 502–506, `norm_polydiscTaylorCoefficient_le`) is an exact duplicate of `norm_polydiscTaylorCoefficient_le_of_bound` (lines 441–499).
   - [Duality.lean](CKMA/Analysis/Convex/Duality.lean) (lines 44–52, `exists_choquetMeasure`) is an exact duplicate of `exists_choquetMeasure_of_compact` ([Choquet.lean](CKMA/Analysis/Convex/Duality/Choquet.lean), lines 934–944).
   - `diniQuotient_bddAbove` and `diniQuotient_bddBelow` are proved identically in [Pattern.lean](CKMA/Analysis/Real/Dini/Pattern.lean) (lines 28–35) and [Young.lean](CKMA/Analysis/Real/Dini/Young.lean) (lines 173–180); move to [Dini/Basic.lean](CKMA/Analysis/Real/Dini/Basic.lean).
   - `subadditiveMeanRate` ([Pointwise.lean](CKMA/Dynamics/Ergodic/Pointwise.lean), line 75) and `kingmanFekete` ([KingmanFull.lean](CKMA/Dynamics/Ergodic/Pointwise/KingmanFull.lean), line 37) are identical definitions.
   - `multipleRecurrenceSet` and `multipleRecurrenceAverage` ([Recurrence.lean](CKMA/Dynamics/Ergodic/Recurrence.lean), lines 816–822) duplicate `progressionHit` and `progressionReturnAverage` ([Multiple.lean](CKMA/Dynamics/Ergodic/Recurrence/Multiple.lean), lines 946, 1098).
   - Positive real power wrapper `if 0 < x then Real.exp (c * Real.log x) else 0` and its 4 basic lemmas are defined three times: `rpowPos` in [Inequalities/Hilbert.lean](CKMA/Analysis/Inequalities/Hilbert.lean) (lines 53–76), `kernelPow` in [IntegralEquation/Basic.lean](CKMA/Analysis/IntegralEquation/Basic.lean) (lines 55–76), and `dualPower` in [WeightedMaximal.lean](CKMA/Analysis/Fourier/WeightedMaximal.lean) (lines 345–365).
2. **Repeated proof blocks within the same file or module**:
   - **[Newton.lean](CKMA/Analysis/Nonlinear/Newton.lean) (lines 570–736)**: In `newton_kantorovich`, the 45-line derivation of `‖x (n + 1) - x n‖ ≤ t (n + 1) - t n` at lines 570–610 is copy-pasted verbatim at lines 692–736. Adding it to the induction invariant `invar` deletes 45 lines.
   - **[CounterexampleSum.lean](CKMA/Analysis/Real/RectangularDifferentiation/CounterexampleSum.lean) (lines 273–462) and [Counterexample.lean](CKMA/Analysis/Real/RectangularDifferentiation/Counterexample.lean) (lines 444–472)**: A 23-line proof that `Finset.univ.filter (fun z : Fin (m + 1) => z.val ≤ 1) = {z0, z1}` appears 4 times verbatim (lines 273–295, 394–416, 440–462 in `CounterexampleSum.lean` and lines 444–472 in `Counterexample.lean`).
   - **[SpectralDynamics.lean](CKMA/Analysis/Operator/SpectralDynamics.lean) (lines 1168–1578)**: `tendsto_cesaro_normSq_compact` (lines 1168–1291) and `rage_purePoint` (lines 1459–1578) repeat ~90 lines of identical precompact finite-cover and Cesàro limsup squeezing.
   - **[CommutantLift.lean](CKMA/Analysis/Operator/Dilation/CommutantLift.lean) (lines 153–239)**: In `cauchySeq_commutantPartial`, the `m ≤ n` case (lines 153–195) and `n ≤ m` case (lines 196–239) are 43 lines of copy-pasted code differing only by `dist_comm`.
   - **[Fourier/Sampling.lean](CKMA/Analysis/Fourier/Sampling.lean) (lines 762–856) and [Fourier/Inequalities.lean](CKMA/Analysis/Fourier/Inequalities.lean) (lines 840–892)**: Both prove (~75 and ~50 lines) that for $f \in L^1(\mathbb{R}) \cap L^2(\mathbb{R})$, the integral inverse Fourier transform agrees a.e. with the $L^2$ Plancherel inverse transform.
   - **[BrownianQuadraticVariation.lean](CKMA/Probability/BrownianQuadraticVariation.lean) (lines 857–989)**: Repeats the same 12-line proof of `MemLp (Y i) 4 μ` and `MemLp (fun ω ↦ Y i ω ^ 2) 2 μ` three times (lines 857–871, 962–972, 980–989).
   - **[GaussianLogSobolev/OneDim.lean](CKMA/Probability/GaussianLogSobolev/OneDim.lean) (lines 295–1003) and [Entropy.lean](CKMA/Probability/GaussianLogSobolev/Entropy.lean) (lines 51–408)**: Over 25 lemmas repeat the unbundled triple of existential hypotheses `(hB : ∃ B, ∀ y, |deriv f y| ≤ B) (hB2 : ∃ B2, ∀ y, |deriv (deriv f) y| ≤ B2) (hM : ∃ M, ∀ y, |f y| ≤ M)` and unpack them in every proof; bundling into a single `HasBoundedC2Deriv f` structure or predicate will clean up both files significantly.
