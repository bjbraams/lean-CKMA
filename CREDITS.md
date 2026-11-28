# Formalization credits

The mathematical selection follows [GAPS.md](GAPS.md), [GAPS_EASY.md](GAPS_EASY.md)
and their stable SYNOPSIS identifiers. [FORMALIZATION.md](FORMALIZATION.md) and
[formalization.json](formalization.json) record the exact scope, representative
conventions and audited proof status of the local declarations.

The compiled library uses Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`,
TauCeti `d91980bdc255e6e50506be147ad9bcb88eb9fcc0` and Lean `v4.36.0`.
The coverage inventories retain their separate source baselines. The toolchain and
manifest setup derives from the sibling `lean-DLMF` project; its additional
project-specific dependencies are not part of this library. Sources use the
Apache 2.0 license in [LICENSE](LICENSE).

## Mathlib interfaces and adapters

Mathlib supplies the normed, inner-product, ordered, topological, measure-theoretic,
probability, calculus and analytic structures used throughout the library. Specific
local identifications and proof ingredients include:

- The interpolation cardinal polynomials and interpolants are adapters to
  `Lagrange.basis` and `Lagrange.interpolate`.
- Positivity of additive maps uses `monotone_iff_map_nonneg`. The operator
  commutant uses `Set.centralizer`; compact Hausdorff carriers use `CompHaus`.
- Weak convergence uses `WeakSpace` and
  `WeakBilin.tendsto_iff_forall_eval_tendsto`; weak-operator convergence and closure
  adapters use `ContinuousLinearMapWOT` and its matrix-coefficient API.
- Raw L² family coefficients are identified with Hilbert inner products through
  `L2.inner_def` and `MemLp.coeFn_toLp`. Essential suprema use `MeasureTheory.essSup`.
- Smooth tests are related to `TestFunction`; the Euclidean coordinate contraction
  is related to `InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`.
- Convexity supplies finite-dimensional continuity through `ConvexOn.continuousOn`
  and `ConcaveOn.continuousOn`. Finite moments supply finite measure through
  `integrable_const_iff_isFiniteMeasure`.
- The Baire derivative proof uses slope limits and distance-to-closed-set lemmas.
  The weak Euler–Lagrange adapter uses differentiation at a local minimum.
- Brownian process predicates are Mathlib's, while the canonical law is stated
  on `ContinuousMap` with its Borel sigma-algebra. Ergodic interfaces use Birkhoff
  sums and averages, invariant sigma-algebras and conditional expectations.
- Relative entropy is `InformationTheory.klDiv`; nonnegative function entropy uses
  `klFun`. Fourier transforms, Haar measures, characters, Gaussian laws, Gamma and
  Bessel functions, polynomial iteration and derivatives use the imported Mathlib
  conventions specified in the mathematical module headers.
- Ordered summability is `Summable` along `SummationFilter.conditional`. On `ℕ`
  that filter is the limit of sums over `Finset.range`.
- Watson's lemma uses Mathlib's Gamma integral, its power-rescaling formula, and
  integrability of exponentially weighted functions with an exponential bound.
  The interior Laplace asymptotic uses Mathlib's second-order Taylor limit,
  dominated convergence, and Gaussian integral.
- The Browder–Göhde–Kirk proof applies
  `exists_forall_closed_ball_dist_add_le_two_sub` to pairs of approximate centers of an orbit.
  Newtonian capacity uses `IsCompact.elim_directed_family_closed` for continuity from
  above on compact sets.

## TauCeti interfaces and proof provenance

Atkinson's theorem is the Tau Ceti contributors'
`TauCeti.isFredholm_iff_exists_isCompactOperator_comp_sub_one` in
`TauCeti/Analysis/Fredholm/CompactPerturbation.lean`, over any complete nontrivially normed
field; the essential-spectrum results use the same file and the closed-range adjoint theorem in
`TauCeti/Analysis/Fredholm/Adjoint.lean`. The arbitrary-pairing bipolar proof transports
`StrongDual.bipolar_eq_closedAbsConvexHull` through Mathlib's
`LinearMap.dualEmbedding_surjective`. The Kato–Rellich corollary combines TauCeti's
self-adjointness theorem with the local graph-norm comparison for cores.

Other imported infrastructure includes:

- Convex subdifferentials and conjugates; absolutely summing gauges; canonical
  bidual maps and `completeSpace_of_surjective_inclusionInDoubleDual`.
- Courant–Fischer eigenvalues, singular values, Fan dominance, Schatten ideals,
  Hilbert–Schmidt operators and normal-operator interfaces.
- Real and complex strongly continuous semigroups, growth bounds and generators.
  The imported semigroup sources credit mrdouglasny/hille-yosida.
  The Trotter–Kato proof uses the generator resolvent's Laplace representation and
  Hille–Yosida bound, and compares orbits through TauCeti's inhomogeneous Cauchy
  problem and Duhamel formula.
- The real Grothendieck inequality uses `Matrix.abs_sum_sum_mul_inner_le_eight_mul`
  from `TauCeti/Analysis/Matrix/Grothendieck.lean`.
- The forward implication of Kwapień's theorem uses the Hilbert-space type and cotype
  lemmas and their transport across continuous linear equivalences in
  `TauCeti/Analysis/Normed/Module/RademacherSum/TypeCotype.lean`.
- Prescribed holomorphic zero divisors use the elementary Weierstrass factors in
  `TauCeti/Analysis/Complex/CanonicalProduct/ElementaryFactor.lean` and the locally uniform
  product and analytic-order theorems in `TauCeti/Analysis/Complex/InfiniteProd.lean`.
- Empirical probability measures from `Probability.Process.EmpiricalMeasure`;
  countable projective limits from `MeasureTheory.Measure.ProjectiveLimit.Countable`.
- Weak derivatives and the actual `W1p` value/gradient projections; total variation,
  perimeter, maximal functions, the Euclidean fundamental solution and Perron envelopes.
- Polydisc Cauchy integration and the analytic interfaces identified in the imports.
- Weierstrass preparation and division combine the existence theorems in
  `TauCeti/Analysis/Complex/Weierstrass.lean` with germ uniqueness from
  `TauCeti/Geometry/Manifold/Complex/StructureSheaf/Weierstrass.lean`.
- Runge approximation uses TauCeti's `IsCompact.exists_norm_sub_sum_mul_sub_inv_smul_le`
  and adapts the spectral argument in `TauCeti/Analysis/Complex/Runge/SimpleFraction.lean`.
  Mathlib's `Subalgebra.spectrum_sUnion_connectedComponentIn` and
  `Subalgebra.spectrum_isBounded_connectedComponentIn` control the poles.
- Mittag–Leffler uses `TauCeti.exists_meromorphic_principalPart_eq` and
  `TauCeti.hasPrescribedSingularities_eval_inv_sub_iff` after identifying the local finiteness
  condition with a codiscrete complement within the domain.
- Abelian Haar amenability averages the translates of normalized integration over a compact
  neighborhood. The proof uses `Amenable.of_commGroup`,
  `amenable_iff_exists_boundedContinuousFunction_mean`, `Set.setIntegralLp`, and
  `PositiveLinearMap.continuous_lpTop` from TauCeti.
- Pietsch domination uses the two implications in
  `TauCeti/Analysis/Normed/Operator/AbsolutelySumming/Pietsch.lean`.
  Mathlib's `borel_comap` identifies the measurable-space presentations of the dual unit ball.
- The wave existence proof uses Mathlib's Lax–Milgram theorem for the resolvent and
  TauCeti's Hilbert-space generation, bounded perturbation and Duhamel theorems for the
  phase-space trajectory.
- `exists_fixedPoint_schauder` is `TauCeti.schauderFixedPoint_closedConvex`.
  `exists_fixedPoint_brouwer` is `TauCeti.brouwerFixedPoint_compactConvex`.
- The squared `L²` identity used for Nash's inequality is
  `MeasureTheory.Lp.integral_norm_sq_eq_norm_sq`.
- The genus-`p` Weierstrass factors are TauCeti's `Complex.weierstrassFactor`, with the
  bound `Complex.norm_weierstrassFactor_sub_one_le` and the logarithmic Taylor identity
  `neg_logTaylor_succ_neg_eq_sum`.
- Real and complex interpolation use TauCeti's compatible couples, `K`-functional, `K`-method
  norm and complex-method spaces (`CompatibleCouple` in `TauCeti.Analysis.Normed.Interpolation`).
  The complex interpolation theorem (26.54) is `CompatibleCouple.ComplexMethodSpace.norm_map_le`.
- BV functions are TauCeti's `MemBV`, and the coarea formula (37.30) is TauCeti's
  `totalVariationOn_eq_lintegral_perimeter`.
- Asymptotic scales and expansions are TauCeti's `Asymptotics.IsAsymptoticScale` and
  `Asymptotics.HasAsymptoticExpansion`; coefficient uniqueness is
  `Asymptotics.HasAsymptoticExpansion.unique`.
- Continuity of the modular character and the inversion identity for regular Haar measures
  (28.2) are TauCeti's `continuous_modularCharacter` and
  `MeasureTheory.Measure.inv_eq_withDensity_modularCharacter_of_regular`.
- Inequality proofs use TauCeti's real-power integrals (`Pow.Integral`) and
  `Multiset.esymm_cons`; sums of the largest coordinates are TauCeti's `prefixSum`.
- Cauchy interlacing is TauCeti's `LinearMap.IsSymmetric.eigenvalues_le_eigenvalues_of_isometry`
  and its primed form; Weyl's inequality is `LinearMap.IsSymmetric.eigenvalues_add_le`; the
  Frobenius norm is `UnitarilyInvariantSeminorm.frobenius`.
- Convolution powers are TauCeti's `MeasureTheory.Measure.convolutionPower`, with
  `Measure.charFun_convolutionPower`. Compound Poisson laws are
  `TauCeti.Probability.compoundPoissonMeasure`, with `charFun_compoundPoissonMeasure`.
- Large-deviation principles and good rate functions are TauCeti's
  `TauCeti.Probability.HasLDP` and `TauCeti.Probability.IsGoodRateFunction`.
- The Ornstein–Uhlenbeck semigroup is identified with TauCeti's Mehler semigroup
  `TauCeti.Probability.mehler`, and the Gaussian log-Sobolev inequality is stated through
  TauCeti's `LogSobolevInequality`. Gaussian integration by parts is
  `TauCeti.Probability.integral_mul_eq_integral_deriv_gaussianReal`, absolute Gaussian
  integrability is `TauCeti.Probability.integrable_abs_gaussianReal`, and the integral
  Cauchy–Schwarz inequality is `TauCeti.sq_integral_mul_le_integral_sq_mul_integral_sq`.
- Free independence is TauCeti's `IsFreelyIndependent`; finite representability is TauCeti's
  `FinitelyRepresentable`.

Imported prerequisites are not counted as completed local targets merely because
their names exist. The axiom audit includes all transitive dependencies. Local
bridges and elementary proofs have module-level and declaration-level attribution;
no upstream package source or dependency pin is modified by this development.

## Proof interfaces

The frame analysis and synthesis proofs use Mathlib's `Memℓp`, `lp` norm formulas,
`lp.hasSum_single`, continuous-linear-map summation and adjoint identities.
`ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map` supplies Hilbert coercivity,
and `ContinuousLinearMap.exists_preimage_norm_le` supplies the open-mapping estimate.
These proofs retain arbitrary index types and real or complex scalars.

Proximal characterization uses TauCeti's finite-domain subdifferential conversion,
supporting inequalities and monotonicity from `Analysis.Convex.Subdifferential`.
The finite-segment limit and firm nonexpansiveness arguments are local proofs.

Other proof ingredients include:

- The compact-attractor argument uses Mathlib's Hausdorff metric on nonempty
  compact sets, nearest-point attainment and `ContractingWith.fixedPoint`.
  The invariant probability is the pushforward of the fixed point of the weight
  mixture on TauCeti's 1-Wasserstein space of that attractor, using
  `wassersteinEDist_finset_sum_smul_rpow_le` and `wassersteinEDist_map_le_mul`.
- Approximate continuity uses
  `VitaliFamily.ae_tendsto_measure_inter_div_of_measurableSet`, the uniformly
  locally doubling closed-ball filter adapter, and countably many rational intervals.
- The Hankel quadratic-form identity uses `Polynomial.lsum`, finite polynomial
  expansions and Mathlib's positive-semidefinite quadratic-form criteria.
- The near-best interpolation estimate uses `Lagrange.eq_interpolate`, compact
  suprema and direct comparison with the infimum of polynomial approximation errors.
- Exponential-square concentration uses Lebesgue Markov and exponential/real-power
  inequalities. AL-space monotone convergence uses real monotone convergence and
  completeness of Cauchy sequences. The general AL representation sums the real L¹
  spaces of the closed principal bands of a maximal positive disjoint family, with
  no σ-finiteness restriction.
- Bernstein's inequality compares the exponential series with a geometric remainder
  of ratio `1/3`, then uses independence to factor the moment generating function.
- The coordinate Heisenberg inequality is the commutator of multiplication by `x`
  and differentiation, at Mathlib's `2π` Fourier normalization. The Gaussian
  `exp(-π x²)` is its own transform and saturates the constant `1/(4π)`.
- Kirszbraun's theorem extends a Lipschitz map into a Hilbert space with the same
  constant. Finite collections of target balls meet by minimizing a squared-distance
  penalty, and Zorn's lemma adds one point at a time.
- The mountain-pass critical point is selected by TauCeti's Ekeland principle on
  the space of continuous paths. A straight-line push by a continuous pathwise
  pseudogradient lowers the maximum, and Palais–Smale compactness at the minimax
  level produces a critical point.
- Gauss multiplication is TauCeti's `Complex.prod_Gamma_add_div`, restated as a product over
  `Fin m`.
- Hausdorff–Young fails for every exponent above 2. Finitely many spatially separated
  modulated Schwartz bumps have disjoint supports, and the modulations put their
  Fourier mass on disjoint frequency balls, so the norm ratio grows like `N^{1-2/p}`.
- The Chebyshev-extrema Lebesgue constant is `(2/π) log(n+1)` plus a uniform slack.
  The nodal polynomial supplies the cardinal weights, and the harmonic-number
  comparison absorbs the endpoint correction, including degree zero.
- Kolmogorov extension for an arbitrary index extends `projectiveFamilyContent` by
  `AddContent.measure`. A decreasing sequence of cylinders depends on countably many
  coordinates, where TauCeti's countable theorem gives continuity from above.
  Uniqueness is Mathlib's `IsProjectiveLimit.unique`.
- The discrete spectrum of a bounded self-adjoint operator is read from the Fredholm
  essential spectrum. TauCeti's `orthogonalKerEquivRange` inverts the operator on the
  orthogonal complement of a finite-dimensional eigenspace, and Mathlib's continuous
  functional calculus supplies the spectral projection of an isolated eigenvalue.
- Nash's inequality splits the Plancherel integral at a frequency radius chosen from
  the Dirichlet integral. The weak derivative is read through TauCeti's tempered
  distribution, and the constant uses the Euclidean ball volume.
- A Kato–Rellich core is preserved because the graph norms of `A` and `A + B` are
  equivalent when the relative bound is strictly less than one. TauCeti's
  self-adjointness theorem makes the perturbed operator closed, so graph density
  is the core identity.
- Johnson–Lindenstrauss is a finite Rademacher projection. Linear forms have a
  sub-Gaussian moment generating function, squares concentrate by a Chernoff bound,
  and a union bound over the pairs leaves a positive-probability matrix.
- Fejér means are convolution against TauCeti's `fejerKernel`, a positive kernel of mass
  one that concentrates at the identity. Continuous functions converge uniformly, finite `Lᵖ` follows by
  density and contraction, and the same kernel controls every circle Lebesgue point.
- Rokhlin's lemma takes a nearly maximal measurable tower in a separable measure
  algebra. Aperiodicity supplies a positive-measure refinement of any large
  uncovered set, and null pieces are trimmed so the levels are strictly disjoint.
- Newton's inequalities for normalized elementary symmetric means are a sum of
  squares in the variables. Maclaurin's root chain follows by multiplying the
  resulting antitone ratios, with zero means handled before any division.
- Crandall–Liggett generation uses the Banach convex-combination inequality for
  m-accretive resolvents. Product estimates make the implicit Euler scheme Cauchy
  on the graph domain, and contractions extend the limit semigroup to the closure.
- The Clarke support function equals the generalized directional derivative. Local
  Lipschitz continuity makes that derivative a real sublinear function, and the
  analytic Hahn–Banach theorem supplies a dual element attaining it.
- Varadhan's lemma for a bounded continuous function uses the open-set lower bound
  on a continuity neighborhood and the closed-set upper bound on finitely many
  superlevel sets of the function. Goodness of the rate is not used.
- Newton–Kantorovich compares the iterates with the scalar majorant whose root is
  `kantorovichRadius`. The rescaled derivative is Lipschitz, so the remainder is
  quadratic, and the case `L = 0` is affine. Local quadratic convergence is the same
  remainder at a simple zero.
- Collectively compact strong approximation preserves invertibility of `1 - T`. A
  unit sequence with `(1 - Kₙ) xₙ → 0` would produce a fixed point of `T`, and each
  `1 - Kₙ` is a compact perturbation of the identity. Solution convergence is the
  resolvent identity.
- Symmetrization compares a centered empirical supremum with an independent Rademacher
  average by a ghost sample and Fubini. Countability makes the supremum measurable, and
  the integrable envelope dominates it.
- Hilbert's inequality is the Schur bound for the kernel `1/(x+y)`. The constant
  `π / sin(π/p)` is the Beta integral `Β(1/p, 1-1/p)`, evaluated by Euler's reflection
  formula. The discrete form compares with that integral.
- Chebyshev's theorem characterizes the unique best uniform polynomial approximation on
  `[-1,1]`: a finite-dimensional coefficient embedding gives existence, and the error
  of a best approximation attains its maximum at `n+2` points with alternating signs.
- Hausdorff's theorem identifies completely monotone sequences with moments of a finite
  measure on `[0,1]`. Forward differences are moments of `x^n (x-1)^k`, the Bernstein
  weights build tight approximants, and polynomials separate those measures.
- Discrete Hardy bounds partial averages by Young's inequality and an absorption step
  for the power `p`. Sharpness uses the finitely supported weights `(n+1)^(-1/p)`.
- Carleman's inequality uses weighted AM-GM, `Real.log_le_sub_one_of_pos`,
  Stirling's `factorial_isEquivalent_stirling`, and divergence of the harmonic series.
- Korovkin's theorem on `[0,1]` uses uniform continuity on a compact interval and
  the norm topology of `C(Icc, ℝ)`.
- Orthogonal roots are separated by a sign-changing factor and vanishing of a
  nonnegative integral. The Gaussian weights are the reciprocal diagonal values of
  the Christoffel kernel, identified through Mathlib's Lagrange basis.
- The rank-perturbation shift of the eigenvalues uses TauCeti's Courant–Fischer bounds on
  Rayleigh quotients.
- An L² Riesz basis has bounded synthesis on finitely supported coefficients. The
  extension to `ℓ²` is bounded below, its adjoint is analysis, and completeness makes
  that adjoint bounded below, which is the frame inequality.
- The Shannon series is the Fourier expansion of the bandlimited representative.
  Samples are the coefficients, the basis vectors invert to normalized sincs
  (`Real.sinc (Real.pi * ·)`), and an L² remainder is bounded in sup norm by
  Cauchy–Schwarz on `[-B,B]`.
- Laurent coefficients, Laurent's theorem and the independence of the circle are TauCeti's
  `circleLaurentCoeff`, `DifferentiableOn.hasLaurentSeriesOnAnnulus` and
  `HasLaurentSeriesOnAnnulus.circleLaurentCoeff_eq`. Normal convergence on compact subsets and
  uniqueness, which integrates the monomials termwise, are local.
- An analytic solution of Gauss's equation has Taylor coefficients fixed by the
  hypergeometric recurrence. The equation for the ordinary series is TauCeti's
  `ordinaryHypergeometric_gaussEquation_of_norm_lt_one`.
- The Bessel generating series rearranges the product of two exponential series
  against Mathlib's hypergeometric formula for integer-order `besselJ`, using
  `besselJ_neg_int` for negative orders.
- Two cyclic realizations of one functional have equal orbit inner products, so the
  orbit map extends to a unitary intertwiner. The cyclic vector is matched by
  those inner products, without a unit in the algebra.
- Lyapunov decrease uses the chain rule `HasFDerivAt.comp_hasDerivAt` along the
  existing flow. LaSalle identifies the omega-limit set through Mathlib's compact
  absorbing-set lemmas and puts it in the largest invariant subset of the
  zero-derivative locus.
- An `L²` kernel determines its Hilbert–Schmidt operator by Cauchy–Schwarz and
  Fubini. The energy identity uses Parseval on the product Hilbert basis built from
  the supplied basis and its scalar star.
- Hoffman–Wielandt compares squared eigenvalue gaps with the Frobenius energy
  through the doubly stochastic overlap matrix of the two eigenbases and
  Mathlib's Birkhoff theorem. The Frobenius energy is the sum of squared
  singular values.
- Hardy–Littlewood–Pólya separates the permutohedron by
  `geometric_hahn_banach_closed_point` and applies the same Birkhoff theorem.
  Karamata's inequality is Jensen's inequality on the rows
  (`ConvexOn.map_sum_le`); equality for a strictly convex function uses
  `StrictConvexOn.map_sum_eq_iff'`.
- The Mittag–Leffler specialization uses `Complex.Gamma_nat_eq_factorial` and
  `NormedSpace.exp_eq_tsum_div`. Gauss regular singularities use explicit analytic
  regularizations. Koebe sharpness uses the quotient derivative, injectivity
  factorization and the omitted point `-1/4`, without the quarter theorem itself.
- Unique continuous solvability of a second-kind Volterra equation extends the
  continuous triangular kernel by `ContinuousMap.exists_restrict_eq`. Each iterate
  has Lipschitz constant `(‖c‖ M T)^n / n!` by `integral_pow`, and
  `ContractingWith.isFixedPt_fixedPoint_iterate` supplies the fixed point. For
  `T < 0` the time interval is empty.
- The weighted monomial norm on the disk is the Beta integral in polar coordinates.
  TauCeti's `integral_rpow_mul_one_sub_rpow` and Mathlib's `ProbabilityTheory.beta` identify
  `∫₀¹ xⁿ (1 - x)^α` for `α > -1`; TauCeti's `add_polarCoord_symm_eq_circleMap` and
  `MeasureTheory.integral_comp_rpow_Ioi_of_pos` convert the area integral.
  `Real.rpow` of a nonpositive base is zero; the radial integral runs over `(0, 1)`.
  Circular Fourier coefficients are Cauchy's formula
  `DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul`. The kernel series
  is `one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`, with coefficients from
  `Complex.Gamma_add_nat_div_Gamma_eq`, matched to Taylor coefficients by
  `taylorSeries_eq_on_ball'`. Closedness uses locally uniform convergence on the
  disk and `tendstoInMeasure_of_tendsto_Lp`. The orthogonal projection is
  `Submodule.starProjection`; the constants lie in the subspace, so its norm is `1`.
- The polynomial escape rate is a uniform limit of continuous approximants. Outside
  an escape radius the orbit grows at least geometrically, the successive
  logarithms form a Cauchy sequence by `cauchySeq_of_dist_le_of_summable` and a
  real geometric series, and `continuous_of_uniform_approx_of_continuous` gives
  continuity. Logarithms are applied only to `max 1 ‖·‖`. An attracting periodic
  point is interior to the filled set by local contraction of the return map; the
  degree is not used.
- Euler–Maclaurin summation with an exact periodic remainder, for Banach-valued functions, is
  derived from TauCeti's even-order `TauCeti.sum_Icc_eq_eulerMaclaurin` by separating the
  `r = p` boundary term from its remainder.
- The sharp Markov bound is attained by the Chebyshev polynomial `T ℝ n`, using
  `Polynomial.Chebyshev.abs_iterate_derivative_T_real_le` and `T_derivative_eq_U`.
- The Mittag–Leffler series `E_{α,β}` is entire by
  `FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto` and
  `FormalMultilinearSeries.ofScalars_sum_eq`. The coefficient growth uses TauCeti's
  `TauCeti.abs_log_norm_Gamma_sub_stirling_le`. The Airy initial series is majorized
  by `Real.summable_pow_div_factorial` and differentiated by
  `hasDerivAt_tsum_of_isPreconnected`. The differentiated series satisfies Airy's
  equation by the coefficient recurrence.
- The classical Aleksandrov–Bakelman–Pucci bound is
  `TauCeti.PDE.le_add_mul_eLpNorm_negPart_div_det_rpow`. The coefficient is
  replaced by `TauCeti.PDE.coefficientSymmetricPart`; positive-definiteness and
  the determinant bound are `TauCeti.PDE.UniformlyEllipticOn.posDef` and
  `TauCeti.PDE.UniformlyEllipticOn.pow_card_le_det`. The contraction identity is
  `TauCeti.PDE.sum_coefficientSymmetricPart_mul_fderiv_fderiv`.
- The classical Krylov–Safonov Hölder estimate is
  `TauCeti.PDE.exists_holderOnWith_of_sum_mul_fderiv_fderiv_eq`, with exponent
  half the TauCeti exponent. The Harnack inequality chains
  `TauCeti.PDE.exists_eLpNorm_le_mul_rpow_mul_add_eLpNorm_posPart` on balls of
  radius `1/2` with `TauCeti.PDE.exists_le_mul_rpow_mul_eLpNorm_posPart_add` on
  the ball of radius `(1/2)/(16√d)`, across sixteen steps in `ball 0 1`.
  Measurability of the coefficient is not used.
- Cohen–Hewitt factorization, with the norm bound and the closeness estimate, is TauCeti's
  `ContinuousLinearMap.exists_apply_eq_of_mem_topologicalClosure_span` from
  `TauCeti/Analysis/Normed/Module/CohenFactorization`. It does not require a regular norm.
- A compact group is amenable because the normalized Haar integral is a
  left-invariant mean. Left invariance is `MeasureTheory.map_mul_left_eq_self`
  and `Topology.IsClosedEmbedding.integral_map`. Hausdorff separation is not
  required. Closed subgroups are stated with TauCeti's `Amenable`, and
  `isHaarAmenable_iff_amenable` identifies the Haar-`L∞` predicate with it for regular Haar
  measures.

The extended-real Ekeland principle reduces to the Tau Ceti contributors' real-valued
`LowerSemicontinuous.exists_add_mul_dist_le_and_lt_add_mul_dist` in
`TauCeti.Topology.MetricSpace.Ekeland`, on a complete closed finite sublevel.
Proximal existence uses `TauCeti.exists_affine_le_of_lt` from
`TauCeti.Analysis.Convex.FenchelMoreau`, then a Hilbert midpoint identity and a
Cauchy minimizing sequence; it does not assume compactness or finite dimension.

The algebraic Birman–Schwinger transport uses the Tau Ceti contributors'
`Module.End.eigenspaceCompEquiv`; invertibility of the positive shift follows from
Mathlib's `ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map`.
Abel inversion uses TauCeti's beta integral `integral_rpow_mul_one_sub_rpow`, Fubini on the
triangle, and Mathlib's fundamental theorem for absolutely continuous functions.
The polydisc coefficient bound uses Mathlib's `norm_torusIntegral_le_of_norm_le_const`
and TauCeti's `torusMap_mem_pi_sphere`, with explicit normalization cancellation.
The full-polydisc series uses TauCeti's
`DifferentiableOn.torusIntegral_prod_sub_inv_smul`. The Weierstrass theorem on a ball uses
TauCeti's `TendstoUniformlyOn.differentiableOn`.
Koenigs linearization uses Mathlib's locally uniform limit of holomorphic functions and the
analytic inverse-function theorem. Böttcher's coordinate uses `Complex.log` near one and the
same locally uniform sum.
Eckart–Young minimality uses TauCeti's `ContinuousLinearMap.singularValue_add_index_le` and
`UnitarilyInvariantSeminorm.map_le_of_kyFanSum_le`.
The real interpolation bound is TauCeti's `CompatibleCouple.kMethodENorm_map_le` for positive
endpoint constants; vanishing constants are reached by an `ε`-limit.
Hanson–Wright splits the quadratic form into diagonal and off-diagonal sums and uses the
sub-Gaussian moment generating function from `CKMA.Probability.Concentration`.
The isometric Gelfand–Naimark representation is derived from TauCeti's
`CStarAlgebra.exists_faithful_nondegenerate_representation`, since an injective ⋆-homomorphism
of C⋆-algebras is isometric.
The fractional translation weight is the integrable kernel `|exp(2πi ⟨h, ξ⟩) - 1|² / |h|^{d+2s}`.
Rotation through `Submodule.reflection` and Haar scaling by `t^{2s}` reduce its integral to a
positive multiple of `‖ξ‖^{2s}`.

Band projections in a Dedekind-complete Riesz space are the linear extensions of the
order supremum of the positive band slice. Freudenthal approximation builds disjoint
components from the principal projection property. The Riesz–Kantorovich supremum of two
order-bounded operators is the least positive upper bound given on each order interval by
`S y + T (x - y)`.

The sewing lemma builds the primitive by dyadic increments. Additivity and the mesh
estimate give uniqueness, the remainder `sewingConstant γ * C`, and convergence along
every ordered partition, including repeated nodes. Hölder Young integration is the
sewing lemma applied to `Y s (X t - X s)`, whose defect is `(Y s - Y u) (X t - X u)`.

The Clarke support identity extends a partial linear functional dominated by the
generalized directional derivative. In finite dimensions the reachable derivatives have
that same support function, by the linewise fundamental theorem, and a separating
hyperplane identifies their closed convex hull with the generalized gradient.

Eberlein–Šmulian metrizes the weak closure of a sequence inside a separable closed real
subspace. The converse uses Whitley's finite-dimensional norming lemma: a weak-star cluster
point of the canonical bidual image already lies in that image. The Mazur identification of
a weak limit with the closed real convex hull is proved from Mathlib's
`Convex.toWeakSpace_closure`.

Young integration for complementary finite `p`- and `q`-variation uses the control
`V_p(X)^{1/p} V_q(Y)^{1/q}`. Deletion along every second node and continuity of finite
variation produce the Young–Loeve bound with constant `sewingConstant (p⁻¹ + q⁻¹)`.

Birkhoff's theorem identifies the almost-everywhere limit of the ergodic averages with the
conditional expectation on the invariant σ-algebra. Kingman's theorem truncates a
subadditive process to a linear lower bound. The set where the limsup is `-∞` is null,
and the Fekete mean is the almost-everywhere and `L¹` limit. In the ergodic case that
limit is the constant mean rate.

Denjoy–Young–Saks assigns exactly one of the four extended Dini patterns to an arbitrary
finite real function, almost everywhere, with no measurability assumption. The left
derivatives use the same difference quotient at negative increments. The argument compares
the rising-sun lemma with a Vitali covering of the infinite and finite-gap patterns.

The strong maximal inequality iterates the one-dimensional weak-type bound. Its Orlicz
form controls `u(1+log⁺u)^{d-1}` for axis-aligned rectangles of unrestricted eccentricity.
Almost-everywhere rectangular differentiation of that local class follows by approximation
with continuous compactly supported functions.

Choquet representation produces a probability measure on a compact metrizable convex set,
carried by the extreme points and tested by continuous affine scalar maps. The
Fenchel–Rockafellar theorem gives dual attainment at a finite primal value. The convex
KKT multiplier theorem records complementary slackness for finite inequality and equality
constraints, including the empty lists. The subdifferential sum rule uses a common point of
continuity on the finite domain.

Converse sub-Gaussian estimates use Mathlib's layer-cake and improper-integral APIs,
exponential series, factorial estimates and Lebesgue monotone summation. The centered
MGF bound uses `Complex.norm_exp_sub_sum_le_norm_mul_exp`, Young's inequality and
`Real.add_one_le_exp`, with the stated variance proxy unchanged.
Gauss's ODE uses Mathlib's regularized-hypergeometric coefficient recurrence,
power-series differentiation, radius bounds and the Gamma scaling relation to
ordinary hypergeometric functions. Terminating upper parameters are included.

Scalar `Lp` uniform convexity follows Hanche-Olsen's argument for real or complex
scalars, an arbitrary measure, and every exponent strictly between one and infinity,
including two. A Young defect controls thin slices of the unit ball, and a general
slice is reduced to a probability space by the measure `‖v‖ ^ p ∂μ`.

Dunford–Pettis identifies relative weak compactness in scalar `L¹` on a finite measure
space with Mathlib's uniform integrability, including its uniform `L¹` bound. Uniform
integrability gives relative weak compactness by truncating into a ball of reflexive
`L²` and using weak-to-weak continuity of the inclusion `L² → L¹`. The converse
metrizes measurable sets by the symmetric-difference measure, obtains uniform absolute
continuity of the set integrals from the Baire property of that complete pseudometric
space, and passes from signed integrals to the norm by splitting real and imaginary
parts. Eberlein–Šmulian extracts a weakly convergent subsequence from any sequence in
the relatively weakly compact set.

Rectangular differentiation of the local `L(log⁺L)^{d-1}` class uses the endpoint strong
maximal inequality. The counterexample sums rectangular spikes. The sum is integrable,
and on a limsup of positive measure a witness rectangle has average at least the stage
height while its total width tends to zero.

A real probability law is infinitely divisible exactly when its characteristic function
is the exponential of a unique Lévy triplet. The exponent uses the truncation `|x| ≤ 1`
for the drift compensation, a nonnegative Gaussian coefficient, and a jump measure with
no atom at zero whose truncated square is integrable.

A normalized complex-linear functional on a unital complex Banach algebra that does not
vanish on units is multiplicative, with no continuity or commutativity hypothesis. A
uniformly closed point-separating subalgebra of `C(K)` on a compact Hausdorff space has a
smallest closed norming boundary, with the supremum convention on the empty carrier.

There is a probability measure on the continuous real paths whose coordinate process is
Brownian; it is a projective limit by Mathlib's `isProjectiveLimit_projectiveLimit`. A
pre-Brownian process has a continuous modification that is locally Hölder of
every exponent below one half. For a strictly positive level, the probability that the
path meets the level by time `t` is twice the probability that the position at time `t`
is at least that level, including time zero. The almost-sure dyadic increment bounds come from
TauCeti's Kolmogorov edge estimate `IsAEKolmogorovProcess.ae_exists_edist_le_mul_pow_rpow` and
`isKolmogorovProcess_of_hasLaw_sub_gaussianReal`; the dyadic chaining is local. The strong
Markov property specializes TauCeti's strong Markov theorems in
`TauCeti.Probability.BrownianMotion.StrongMarkov`.

An isometry of a complex Hilbert space splits into a unitary part and a shift whose
coefficients lie in the kernel of the adjoint. A contraction has a minimal unitary power
dilation, unique up to an intertwining isometry, and a minimal co-invariant isometric
dilation. An operator commuting with the contraction lifts to an operator of the same norm
commuting with that isometric dilation.

Quadratic variation of one-dimensional Brownian motion along completed-interval partitions
converges to time, uniformly for times up to a fixed horizon: in probability when the mesh
tends to zero, and almost surely when the meshes are summable. For finitely many independent
Brownian motions, the covariation converges in probability to time on the diagonal and to
zero off the diagonal. The estimates are TauCeti's Doob maximal inequality for the
time-centered quadratic sums at the partition nodes
(`TauCeti.Probability.BrownianMotion.PartitionMaximal`) and Borel–Cantelli for the summable
meshes.

For integrable forcing on a compact interval, the variation-of-constants trajectory of a
strongly continuous semigroup is the unique continuous integrated solution. It is built on
TauCeti's inhomogeneous Cauchy problem (`CauchyProblem.Inhomogeneous`): existence is TauCeti's
mild solution `isForcedMildSolution_realOperator_add_duhamel` for the forcing extended by zero,
and uniqueness applies `eqOn_realOperator_sub_add_setIntegral_of_generator_setIntegral_eq` to the
difference of two solutions.

On a compact interval, two solutions of the same regular Sturm–Liouville equation have
interlacing zeros when their Wronskian is not identically zero. For two equations with the
same positive leading coefficient and the same positive weight, a strictly larger spectral
parameter forces a zero of the higher mode between consecutive zeros of the lower mode.
