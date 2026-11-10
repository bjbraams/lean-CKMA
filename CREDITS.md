# Formalization credits

The mathematical selection follows [GAPS.md](GAPS.md), [GAPS_EASY.md](GAPS_EASY.md)
and their stable SYNOPSIS identifiers. [FORMALIZATION.md](FORMALIZATION.md) and
[formalization.json](formalization.json) record the exact scope, representative
conventions and audited proof status of the local declarations.

The compiled library uses Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca`,
TauCeti `a049b4264d2cf4dbf4720796f844a3a3764914a5` and Lean `v4.36.0-rc1`.
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

## TauCeti interfaces and proof provenance

The Atkinson proof adapts the kernel/cokernel squeezing argument of the Tau Ceti
contributors in `TauCeti/Analysis/Fredholm/CompactPerturbation.lean`, using its
compact-perturbation theorem and the finite-rank compactness API. The proof is
uniform over real or complex scalars. The arbitrary-pairing bipolar proof transports
`StrongDual.bipolar_eq_closedAbsConvexHull` through Mathlib's
`LinearMap.dualEmbedding_surjective`. The Kato–Rellich corollary uses TauCeti's
self-adjointness theorem with an explicitly admitted local core prerequisite.

Other imported infrastructure includes:

- Convex subdifferentials and conjugates; absolutely summing gauges; canonical
  bidual maps and `completeSpace_of_surjective_inclusionInDoubleDual`.
- Courant–Fischer eigenvalues, singular values, Fan dominance, Schatten ideals,
  Hilbert–Schmidt operators and normal-operator interfaces.
- Real and complex strongly continuous semigroups, growth bounds and generators.
  The imported semigroup sources credit mrdouglasny/hille-yosida.
- Empirical probability measures from `Probability.Process.EmpiricalMeasure`;
  countable projective limits from `MeasureTheory.Measure.ProjectiveLimit.Countable`.
- Weak derivatives and the actual `W1p` value/gradient projections; total variation,
  perimeter, maximal functions, the Euclidean fundamental solution and Perron envelopes.
- Polydisc Cauchy integration and the analytic interfaces identified in the imports.

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
- Approximate continuity uses
  `VitaliFamily.ae_tendsto_measure_inter_div_of_measurableSet`, the uniformly
  locally doubling closed-ball filter adapter, and countably many rational intervals.
- The Hankel quadratic-form identity uses `Polynomial.lsum`, finite polynomial
  expansions and Mathlib's positive-semidefinite quadratic-form criteria.
- The near-best interpolation estimate uses `Lagrange.eq_interpolate`, compact
  suprema and direct comparison with the infimum of polynomial approximation errors.
- Coefficient uniqueness uses Mathlib's little-o subtraction, congruence and bound APIs.
- Exponential-square concentration uses Lebesgue Markov and exponential/real-power
  inequalities. AL-space monotone convergence uses real monotone convergence and
  completeness of Cauchy sequences.
- The Mittag–Leffler specialization uses `Complex.Gamma_nat_eq_factorial` and
  `NormedSpace.exp_eq_tsum_div`. Gauss regular singularities use explicit analytic
  regularizations. Koebe sharpness uses the quotient derivative, injectivity
  factorization and the omitted point `-1/4`, without the quarter theorem itself.

The extended-real Ekeland principle reduces to the Tau Ceti contributors' real-valued
`LowerSemicontinuous.exists_add_mul_dist_le_and_lt_add_mul_dist` in
`TauCeti.Topology.MetricSpace.Ekeland`, on a complete closed finite sublevel.
Proximal existence uses `TauCeti.exists_affine_le_of_lt` from
`TauCeti.Analysis.Convex.FenchelMoreau`, then a Hilbert midpoint identity and a
Cauchy minimizing sequence; it does not assume compactness or finite dimension.

The algebraic Birman–Schwinger transport uses the Tau Ceti contributors'
`Module.End.eigenspaceCompEquiv`; invertibility of the positive shift follows from
Mathlib's `ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map`.
The polydisc coefficient bound uses Mathlib's `norm_torusIntegral_le_of_norm_le_const`
and TauCeti's `torusMap_mem_pi_sphere`, with explicit normalization cancellation.

Converse sub-Gaussian estimates use Mathlib's layer-cake and improper-integral APIs,
exponential series, factorial estimates and Lebesgue monotone summation. The centered
MGF bound uses `Complex.norm_exp_sub_sum_le_norm_mul_exp`, Young's inequality and
`Real.add_one_le_exp`, with the stated variance proxy unchanged.
Gauss's ODE uses Mathlib's regularized-hypergeometric coefficient recurrence,
power-series differentiation, radius bounds and the Gamma scaling relation to
ordinary hypergeometric functions. Terminating upper parameters are included.
