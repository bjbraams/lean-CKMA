# CKMA formalization

The library represents **242 of the 603 selected gaps** in [GAPS.md](GAPS.md),
including all 59 entries of [GAPS_EASY.md](GAPS_EASY.md). The entry statuses are
91 statements, 86 partial interfaces, 65 proved entries and
361 entries without a local statement. These units are catalogue entries,
not individual Lean declarations.

A target containing `sorry` is admitted. A partial interface records precisely the
represented clauses and the remaining scope; it does not establish the omitted
clauses. [formalization.json](formalization.json) records all 603 stable identifiers,
the selected declarations, their source locations, source hashes and audited axiom
dependencies. The coverage inventories retain their own library baselines and count
rules; this document describes the compiled local formalization.

## Layout and mathematical conventions

[CKMA.lean](CKMA.lean) re-exports [analysis](CKMA/Analysis.lean),
[probability](CKMA/Probability.lean), [dynamics](CKMA/Dynamics.lean) and
[Haar measure](CKMA/MeasureTheory.lean). All authored mathematical constants use
the `CKMA` namespace. Files are organized by subject, with catalogue identifiers in
docstrings and the index. Every implementation module has a mathematical summary
and exposes its concrete public definitions for use by downstream proofs.

Common foundation modules include scalar-parametrized Hilbert carriers in
[HilbertModel.lean](CKMA/Analysis/InnerProductSpace/HilbertModel.lean), smooth
capacity tests in [Cutoff.lean](CKMA/Analysis/Potential/Cutoff.lean), and
[flow](CKMA/Dynamics/Flow.lean) and [bounded-orbit](CKMA/Dynamics/Orbit.lean)
interfaces. The principal operator, matrix and trace APIs use `RCLike` scalars where
the mathematics is uniform over the real and complex fields.

The canonical Brownian measure is stated on the Borel space of continuous paths;
continuous modifications of arbitrary pre-Brownian processes are separate results.
Ordered random-series convergence is distinguished from unconditional summability.
Normal summability includes boundedness on compact sets, density-zero predicates
record finite small-ball masses, and genuine inverse poles have positive order and
nonzero analytic regularization. Fourier, entropy, Haar and Lévy conventions are
specified in their module headers.

Interpolation and Bergman carriers have concrete gauges and theorem interfaces;
a complete bundled normed-space API is a separate mathematical construction.
Weak equations use actual weak derivatives and explicit representative conventions.
Finite-dimensional normal eigenbases are supplied in the real/complex conditional
Hoffman–Wielandt interface; unconditional existence for normal operators is a complex
statement. The scope list below records these distinctions entry by entry.

## Completed proofs and admissions

There are **3196 inventoried public declarations**: 1172 theorems, 1118 lemmas
and 906 definitions, abbreviations or structures. **200** depend on `sorryAx`
(191 direct admissions). The other **2996** declarations use only standard axioms.
Every lemma, definition, abbreviation and structure is free of `sorryAx`. The
standard axioms are `propext`, `Classical.choice` and `Quot.sound`, or subsets of
these.

The fully proved selected entries are:

- **05.7 Baire classification of derivatives**.
- **05.10 Denjoy–Young–Saks theorem**.
- **05.30 Approximate continuity**.
- **05.31 Rectangular differentiation**.
- **05.33 Kirszbraun's theorem**.
- **06.1 Kolmogorov extension theorem**.
- **06.51 Lévy–Khintchine formula**.
- **06.62 Varadhan's integral lemma**.
- **07.4 Bernstein's inequality**.
- **07.43 Hanson–Wright inequality**.
- **07.47 Johnson–Lindenstrauss lemma**.
- **08.1 Brownian construction and continuous modification**.
- **08.4 Reflection principle**.
- **09.21 Young's integration theorem**.
- **09.22 Sewing lemma**.
- **10.5 Birkhoff pointwise theorem**.
- **10.7 Kingman's subadditive theorem**.
- **10.9 Rokhlin tower lemma**.
- **11.9 Newton and Maclaurin inequalities**.
- **11.22 Hardy–Littlewood–Pólya characterization**.
- **11.24 Karamata's inequality**.
- **11.32 Discrete Hardy inequality**.
- **11.38 Carleman's inequality**.
- **12.9 Choquet representation**.
- **12.32 Everywhere-defined proximal mapping**.
- **12.39 Fenchel–Rockafellar duality**.
- **12.40 Slater and KKT conditions**.
- **12.45 Ekeland variational principle**.
- **12.50 Clarke gradient representation**.
- **13.7 Cauchy interlacing**.
- **13.8 Weyl inequalities**.
- **13.10 Hoffman–Wielandt inequality**.
- **13.18 Eckart–Young–Mirsky theorem**.
- **14.40 Nash inequality**.
- **15.28 Eberlein–Šmulian theorem**.
- **15.33 Uniform convexity of $L^p$**.
- **16.13 Bipolar theorem for dual pairs**.
- **17.23 Dunford–Pettis compactness in $L^1$**.
- **19.5 Band projections**.
- **20.19 Gleason–Kahane–Żelazko theorem**.
- **20.23 Shilov boundary theorem**.
- **21.11 Atkinson theorem**.
- **21.16 Discrete spectrum of self-adjoint operators**.
- **21.26 Wold decomposition**.
- **21.30 Unitary dilation theorem**.
- **21.37 Commutant lifting**.
- **22.22 KLMN theorem**.
- **22.32 Kato–Rellich theorem: cores**.
- **24.52 Crandall–Liggett generation**.
- **25.3 Hilbert–Schmidt kernels**.
- **25.23 Abel inversion**.
- **25.47 Collectively compact approximation theorem**.
- **29.58 Shannon sampling theorem**.
- **31.20 Sturm separation and comparison**.
- **31.26 LaSalle invariance principle**.
- **36.35 Mountain-pass theorem**.
- **39.73 Self-similar attractors**.
- **46.10 Koenigs linearization**.
- **46.11 Böttcher's theorem**.
- **47.17 Korovkin theorem**.
- **47.35 Chebyshev interpolation stability**.
- **48.6 Real and simple zeros**.
- **48.34 Hausdorff theorem**.
- **49.13 Gauss equation**.
- **49.30 Bessel generating function**.

The complete frame module proves bounded analysis, the operator and synthesis
criteria, reciprocal canonical-dual bounds and both unconditional expansions.
Entries 29.2 and 29.3 retain partial status because the explicit operator-order
equivalence and optimality of the bounds are not stated. Other supporting proofs
include proximal existence, subgradient characterization, firm nonexpansiveness and uniqueness,
Ekeland's extended-real variational principle,
AL-space monotone convergence, Hankel positivity,
near-best interpolation, asymptotic coefficient uniqueness, Koebe sharpness, Gauss's ODE and
regular singularities, the Mittag–Leffler exponential specialization and the
quantitative sub-Gaussian scale implications and centered MGF bounds. The bounded-operator
Birman–Schwinger kernel equivalence, the polydisc coefficient bound, and the fact that an
L² Riesz basis is a frame are also proved.

Private proof helpers have registered docstrings and are separate from the public
index inventory. Their proof role does not introduce additional assumptions or admissions.

The Gabor critical-density corollary, Kato–Rellich core self-adjointness corollary
and maximal-monotone resolvent-existence corollary retain admitted dependencies.
The Euler–Lagrange adapter assumes an explicitly justified variation-derivative
identity; deriving it from growth conditions and obtaining the classical PDE is
outside that proved adapter's conclusion.

## Toolchain, provenance and validation

The pins are Lean `v4.36.0-rc1`, Mathlib
`911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti
`a049b4264d2cf4dbf4720796f844a3a3764914a5`. [CREDITS.md](CREDITS.md)
records the imported interfaces and adapted proof provenance. The library uses
`127` Lean modules and `12259` source lines; the largest file has
`477` lines. No file approaches the 1,000-line size guideline.

The ordinary build is `lake build > /tmp/ckma-build.log 2>&1`. The checker
`python3 scripts/check_formalization.py` validates catalogue membership, locations,
source hashes and entry-module imports. Its `--check-lean` mode checks every source
with both implicit-variable options disabled; `--audit` records fresh transitive
axiom dependencies. After source edits, rebuild, refresh the index and repeat the
audit. The inventory scanner masks comments and strings before recognizing the
project's declaration syntax.

## Scope by catalogue entry

The following list includes every started entry. `statement` denotes a typed target,
`partial` an explicitly limited interface, and `proved` a selected entry whose
listed assertions have no admitted dependencies.

- **04.39 Duality** — statement; [CKMA.Analysis.Measure.LpDuality](CKMA/Analysis/Measure/LpDuality.lean).
- **05.7 Baire classification of derivatives** — proved; [CKMA.Analysis.Real.Baire](CKMA/Analysis/Real/Baire.lean). Open subsets of the real line, including disconnected sets and the empty set.
- **05.10 Denjoy–Young–Saks theorem** — proved; [CKMA.Analysis.Real.Dini](CKMA/Analysis/Real/Dini.lean). All finite real functions, with no measurability assumption, and exactly one of four extended Dini types almost everywhere. Left limits use negative increments in the same difference quotient.
- **05.30 Approximate continuity** — proved; [CKMA.Analysis.Real.ApproximateContinuity](CKMA/Analysis/Real/ApproximateContinuity.lean). Finite measurable real functions on a second-countable Borel space, for a locally finite uniformly locally doubling measure, are approximately continuous almost everywhere. Euclidean volume is included.
- **05.31 Rectangular differentiation** — proved; [CKMA.Analysis.Real.RectangularDifferentiation](CKMA/Analysis/Real/RectangularDifferentiation.lean). The endpoint strong maximal inequality and almost-everywhere differentiation of the local `L(log⁺L)^{d-1}` class are proved for open axis-aligned rectangles with no eccentricity bound, in dimension at least two. An integrable function fails to be differentiated on a set of positive measure. Positive integrals and maximal values retain infinity.
- **05.33 Kirszbraun's theorem** — proved; [CKMA.Analysis.Real.Kirszbraun](CKMA/Analysis/Real/Kirszbraun.lean). Exact Lipschitz constant on arbitrary subsets of a real inner-product domain into a complete real Hilbert target; empty subsets and zero constants are included.
- **06.1 Kolmogorov extension theorem** — proved; [CKMA.Probability.ProjectiveLimit](CKMA/Probability/ProjectiveLimit.lean). Unique probability projective limit of a consistent family of finite-dimensional probabilities on standard Borel coordinates, for an arbitrary index.
- **06.23 Kolmogorov three-series theorem** — statement; [CKMA.Probability.LimitTheorems.IndependentSums](CKMA/Probability/LimitTheorems/IndependentSums.lean). Ordinary sequence-order convergence, not unconditional Summable, for the random series and the truncated mean series; variances and probability tails have nonnegative summability.
- **06.27 Hartman–Wintner iterated-logarithm law** — statement; [CKMA.Probability.LimitTheorems.IndependentSums](CKMA/Probability/LimitTheorems/IndependentSums.lean). IID centered real variables of strictly positive finite variance; extended-real limsup/liminf and an index shift avoid small logarithm exceptions.
- **06.34 Lindeberg–Feller theorem** — statement; [CKMA.Probability.LimitTheorems.IndependentSums](CKMA/Probability/LimitTheorems/IndependentSums.lean). Independent centered rows of square-integrable real variables with positive row variances. Feller infinitesimality is imposed only for the reverse implication.
- **06.36 Berry–Esseen bound** — statement; [CKMA.Probability.LimitTheorems.IndependentSums](CKMA/Probability/LimitTheorems/IndependentSums.lean). Kolmogorov distance of laws, positive variance and finite absolute third moment; explicit nonoptimal universal constant 100.
- **06.51 Lévy–Khintchine formula** — proved; [CKMA.Probability.InfinitelyDivisible](CKMA/Probability/InfinitelyDivisible.lean). Probability convolution roots and actual Levy triplets with no atom at zero. The compensated exponent uses truncation x*1_{|x|<=1}, which fixes uniqueness.
- **06.60 Cramér's theorem** — statement; [CKMA.Probability.LimitTheorems.LargeDeviations](CKMA/Probability/LimitTheorems/LargeDeviations.lean). Reuses the existing LDP predicates at speed n+1; the rate is the Legendre transform of the extended-log MGF, retaining infinite exponential moments.
- **06.61 Sanov's theorem** — statement; [CKMA.Probability.LimitTheorems.LargeDeviations](CKMA/Probability/LimitTheorems/LargeDeviations.lean). Polish state spaces, weak topology on ProbabilityMeasure, TauCeti finite empirical probabilities, and Mathlib relative entropy.
- **06.62 Varadhan's integral lemma** — proved; [CKMA.Probability.LargeDeviations](CKMA/Probability/LargeDeviations.lean). Full open-lower/closed-upper LDP at speed n+1 and bounded continuous test functions, without goodness of the rate. Zero probabilities and infinite rates use extended logarithms and suprema.
- **07.4 Bernstein's inequality** — proved; [CKMA.Probability.Concentration](CKMA/Probability/Concentration.lean).
- **07.6 Equivalent sub-Gaussian descriptions** — partial; [CKMA.Probability.Concentration](CKMA/Probability/Concentration.lean). Concrete extended gauge and quantitative scale implications; the MGF-to-gauge adapter and the exact infimum-gauge equivalence remain.
- **07.17 Gaussian logarithmic Sobolev inequality** — statement; [CKMA.Probability.GaussianLogSobolev](CKMA/Probability/GaussianLogSobolev.lean). Smooth real functions in Gaussian L2 on arbitrary finite-dimensional real Hilbert spaces; normalized KL-integrand entropy retains infinite entropy and has the exact factor two.
- **07.33 Symmetrization** — partial; [CKMA.Probability.Symmetrization](CKMA/Probability/Symmetrization.lean). Nonempty countable function classes with a measurable integrable envelope; signs on an independent product factor. The general measurable-supremum formulation remains.
- **07.43 Hanson–Wright inequality** — proved; [CKMA.Probability.HansonWright](CKMA/Probability/HansonWright.lean). A constant uniform over dimensions, probability spaces, coordinate laws and real matrices; concrete Euclidean operator and Frobenius norms. No symmetry restriction on the real matrix is needed.
- **07.47 Johnson–Lindenstrauss lemma** — proved; [CKMA.Probability.Concentration](CKMA/Probability/Concentration.lean). Uses log(2 max(N,1)) to include the empty configuration.
- **08.1 Brownian construction and continuous modification** — proved; [CKMA.Probability.BrownianTheory](CKMA/Probability/BrownianTheory.lean). Canonical probability law on the Borel space of continuous real paths; continuous modifications of pre-Brownian processes on their original probability space and every positive local Holder exponent below one half.
- **08.3 Strong Markov property** — partial; [CKMA.Probability.BrownianTheory](CKMA/Probability/BrownianTheory.lean). Finite-valued stopping times for the raw natural filtration; the post-stopping process is Brownian and finite-dimensional events are independent of Mathlib's stopping-time sigma-algebra. The completed right-continuous augmented-filtration interface remains.
- **08.4 Reflection principle** — proved; [CKMA.Probability.BrownianTheory](CKMA/Probability/BrownianTheory.lean). Strictly positive barrier, nonnegative observation time including zero, and a path-supremum event expressed by existence of a hitting time.
- **08.7 Quadratic variation** — partial; [CKMA.Probability.BrownianQuadraticVariation](CKMA/Probability/BrownianQuadraticVariation.lean). Completed-interval sums are proved: scalar UCP and summable-mesh a.s. convergence, and independent-coordinate UCP covariation. The a.s. cross-coordinate statement and a bundled bracket process remain.
- **09.21 Young's integration theorem** — proved; [CKMA.Analysis.RoughPath.Sewing](CKMA/Analysis/RoughPath/Sewing.lean). Operator-valued integrands and Banach-valued integrators and outputs on a finite interval. The Hölder criterion and the complementary finite `p,q`-variation criterion are proved, including all-partition convergence and the Young–Loeve remainder. The sewing primitive is normalized and defined only on its interval.
- **09.22 Sewing lemma** — proved; [CKMA.Analysis.RoughPath.Sewing](CKMA/Analysis/RoughPath/Sewing.lean). Continuous increment fields with diagonal zero and defect exponent greater than one; a unique normalized continuous interval primitive and convergence along arbitrary ordered partitions, including degenerate intervals.
- **10.5 Birkhoff pointwise theorem** — proved; [CKMA.Dynamics.Ergodic.Pointwise](CKMA/Dynamics/Ergodic/Pointwise.lean). Arbitrary probability-preserving measurable systems and integrable real observables; finite maximal ergodic inequality, a.e. invariant-conditional-expectation limit, and ergodic scalar-mean limit. No standard-Borel restriction is needed here.
- **10.7 Kingman's subadditive theorem** — proved; [CKMA.Dynamics.Ergodic.Pointwise](CKMA/Dynamics/Ergodic/Pointwise.lean). Integrable positive-length subadditive real processes with a uniform lower bound on mean rates; invariant integrable limit, a.e. and L1 convergence, expectation-infimum formula, and ergodic constant limit.
- **10.9 Rokhlin tower lemma** — proved; [CKMA.Dynamics.Ergodic.Recurrence](CKMA/Dynamics/Ergodic/Recurrence.lean). Positive finite heights in an aperiodic standard-Borel probability system, with a bimeasurable measure-preserving automorphism; pairwise disjoint image levels and near-full union mass.
- **10.48 Furstenberg multiple recurrence** — statement; [CKMA.Dynamics.Ergodic.Recurrence](CKMA/Dynamics/Ergodic/Recurrence.lean). Positive-liminf arithmetic-progression recurrence at lengths k>=2, the selected nontrivial gap beyond k=1.
- **11.9 Newton and Maclaurin inequalities** — proved; [CKMA.Analysis.Inequalities.ClassicalSequences](CKMA/Analysis/Inequalities/ClassicalSequences.lean). Nonnegative finite tuples, normalized Mathlib multiset elementary symmetric polynomials, Newton log-concavity and the full Maclaurin root chain.
- **11.22 Hardy–Littlewood–Pólya characterization** — proved; [CKMA.Analysis.Convex.Majorization](CKMA/Analysis/Convex/Majorization.lean).
- **11.24 Karamata's inequality** — proved; [CKMA.Analysis.Convex.Majorization](CKMA/Analysis/Convex/Majorization.lean).
- **11.32 Discrete Hardy inequality** — proved; [CKMA.Analysis.Inequalities.ClassicalSequences](CKMA/Analysis/Inequalities/ClassicalSequences.lean). Extended nonnegative sums for arbitrary nonnegative sequences; sharpness already on finitely supported inputs, for every real exponent p>1.
- **11.37 Hilbert's integral inequality** — partial; [CKMA.Analysis.Inequalities.Hilbert](CKMA/Analysis/Inequalities/Hilbert.lean). Integral and discrete upper bounds with the sharp proposed constant; the optimality assertions remain unstated.
- **11.38 Carleman's inequality** — proved; [CKMA.Analysis.Inequalities.Carleman](CKMA/Analysis/Inequalities/Carleman.lean). Nonnegative summable sequences; the constant e is optimal already for finitely supported sequences.
- **12.9 Choquet representation** — proved; [CKMA.Analysis.Convex.Duality](CKMA/Analysis/Convex/Duality.lean). Compact metrizable convex subsets of locally convex Hausdorff real spaces; probability on the subset, carried by its extreme points, tested by continuous affine maps.
- **12.21 Subdifferential sum rule** — partial; [CKMA.Analysis.Convex.Duality](CKMA/Analysis/Convex/Duality.lean). The Banach sum rule under a common finite-domain continuity qualification is proved. The finite-dimensional relative-interior alternative remains.
- **12.32 Everywhere-defined proximal mapping** — proved; [CKMA.Analysis.Convex.Proximal](CKMA/Analysis/Convex/Proximal.lean). Proper lower semicontinuous convex extended-real functions on real Hilbert spaces: proximal existence and uniqueness, subdifferential characterization, firm nonexpansiveness and a guarded totalized proximal map.
- **12.39 Fenchel–Rockafellar duality** — proved; [CKMA.Analysis.Convex.Duality](CKMA/Analysis/Convex/Duality.lean). Proper lower-semicontinuous convex Banach-space functions, a common finite continuity point, finite primal value; equality and dual attainment, without primal attainment.
- **12.40 Slater and KKT conditions** — proved; [CKMA.Analysis.Convex.Duality](CKMA/Analysis/Convex/Duality.lean). Finite-dimensional Slater/KKT necessity, and sufficiency in arbitrary real normed spaces; explicit subgradient and complementary-slackness data, including empty finite constraint lists.
- **12.45 Ekeland variational principle** — proved; [CKMA.Analysis.Convex.Ekeland](CKMA/Analysis/Convex/Ekeland.lean). Extended-real proper l.s.c. bounded-below functions on complete metric spaces; positive error epsilon and distance scale, finite initial value. Epsilon positivity is essential for the strict variational inequality.
- **12.50 Clarke gradient representation** — proved; [CKMA.Analysis.Convex.Clarke](CKMA/Analysis/Convex/Clarke.lean). The support identity is proved for a locally Lipschitz function on any real normed space. In finite dimensions, under Lipschitz control on one ball, the generalized gradient is nonempty, compact, and convex, and equals the closed convex hull of reachable derivatives.
- **13.7 Cauchy interlacing** — proved; [CKMA.Analysis.InnerProductSpace.MatrixInequalities](CKMA/Analysis/InnerProductSpace/MatrixInequalities.lean). Real or complex finite-dimensional Hilbert endomorphisms. Compression is supplied by a linear isometry; symmetry of the compression is derived internally.
- **13.8 Weyl inequalities** — proved; [CKMA.Analysis.InnerProductSpace.MatrixInequalities](CKMA/Analysis/InnerProductSpace/MatrixInequalities.lean). Real or complex Hermitian endomorphisms with zero-based sorted indices. Symmetry of the sum follows from the two summands.
- **13.10 Hoffman–Wielandt inequality** — proved; [CKMA.Analysis.InnerProductSpace.MatrixInequalities](CKMA/Analysis/InnerProductSpace/MatrixInequalities.lean). Real or complex operators with supplied orthonormal eigenbases; unconditional normal eigenbasis existence is a complex-space fact supplied by TauCeti.
- **13.13 Von Neumann trace inequality** — statement; [CKMA.Analysis.InnerProductSpace.MatrixInequalities](CKMA/Analysis/InnerProductSpace/MatrixInequalities.lean).
- **13.18 Eckart–Young–Mirsky theorem** — proved; [CKMA.Analysis.InnerProductSpace.MatrixInequalities](CKMA/Analysis/InnerProductSpace/MatrixInequalities.lean). SVD truncation of rank at most k is minimal for every unitarily invariant seminorm. The operator-norm error equals the singular value of index k, and the squared Frobenius error is the tail of squares from that index.
- **14.40 Nash inequality** — proved; [CKMA.Analysis.Sobolev.Nash](CKMA/Analysis/Sobolev/Nash.lean). Real scalar L1 ∩ H1 with a supplied weak Frechet derivative; positive dimension.
- **15.28 Eberlein–Šmulian theorem** — proved; [CKMA.Analysis.FunctionalAnalysis.WeakCompactness](CKMA/Analysis/FunctionalAnalysis/WeakCompactness.lean). Real or complex Banach spaces; relative compactness is closure-compactness in the actual weak topology, and subsequence limits are allowed in the ambient space.
- **15.29 James compactness theorem, sufficiency** — statement; [CKMA.Analysis.FunctionalAnalysis.WeakCompactness](CKMA/Analysis/FunctionalAnalysis/WeakCompactness.lean). Real Banach spaces: a norm-closed convex set is weakly compact when every continuous linear functional attains its supremum. Attainment supplies nonemptiness and boundedness.
- **15.33 Uniform convexity of $L^p$ away from the Hilbert case** — proved; [CKMA.Analysis.FunctionalAnalysis.WeakCompactness](CKMA/Analysis/FunctionalAnalysis/WeakCompactness.lean). Mathlib UniformConvexSpace for scalar Lp over any measure, real or complex scalars, 1<p<infinity. The Hilbert exponent is included in the general interface.
- **16.13 Bipolar theorem for dual pairs** — proved; [CKMA.Analysis.LocallyConvex.Bipolar](CKMA/Analysis/LocallyConvex/Bipolar.lean). In fact no separating hypothesis is needed when the closure is explicitly in WeakBilin B.
- **17.21 Rosenthal $\ell^1$ theorem** — partial; [CKMA.Analysis.BanachSpace.Geometry](CKMA/Analysis/BanachSpace/Geometry.lean). Real Banach spaces; weak Cauchy subsequence versus a subsequence satisfying two-sided l1 finite-coefficient estimates. The complex-scalar version and a bundled Schauder-span equivalence remain.
- **17.23 Dunford–Pettis compactness in $L^1$** — proved; [CKMA.Analysis.FunctionalAnalysis.WeakCompactness](CKMA/Analysis/FunctionalAnalysis/WeakCompactness.lean). Finite measure spaces and real/complex scalar L1; reuses Mathlib UniformIntegrable, whose predicate already includes uniform L1 boundedness.
- **17.38 Kwapień theorem** — partial; [CKMA.Analysis.BanachSpace.Geometry](CKMA/Analysis/BanachSpace/Geometry.lean). Real Banach spaces, actual isomorphism to a bundled complete real Hilbert space, and uniform finite Rademacher second-moment type/cotype constants. The complex version remains.
- **17.39 Dvoretzky theorem** — partial; [CKMA.Analysis.BanachSpace.Geometry](CKMA/Analysis/BanachSpace/Geometry.lean). Real infinite-dimensional Banach spaces; scaled embeddings of every finite Euclidean space with distortion at most 1+epsilon. The complex version and an explicit Banach-Mazur-distance declaration remain.
- **17.46 Superreflexive renorming theorem** — partial; [CKMA.Analysis.BanachSpace.Renorming](CKMA/Analysis/BanachSpace/Renorming.lean). Real Banach spaces; finite representability is concrete via almost-isometric finite-dimensional embeddings, reflexivity uses the canonical bidual map, and renormings are actual Seminorm objects with positive two-sided comparison and explicit convexity/smoothness inequalities. Bundled normed-space instances and complex analogues remain.
- **17.54 Pietsch domination theorem** — partial; [CKMA.Analysis.BanachSpace.Pietsch](CKMA/Analysis/BanachSpace/Pietsch.lean). Real operators and every finite p>=1; exact-constant domination by an inner-regular Borel probability on the actual weak-star dual unit ball. Reuses TauCeti summingENorm, including its infimal constant, rather than defining another summing gauge. The complex version remains.
- **17.57 Grothendieck inequality** — partial; [CKMA.Analysis.BanachSpace.Geometry](CKMA/Analysis/BanachSpace/Geometry.lean). The real scalar-field inequality with a universal constant, finite matrices, and finite-dimensional Euclidean vectors; arbitrary finite Hilbert families reduce to their span. The complex scalar version remains.
- **19.5 Band projections** — proved; [CKMA.Analysis.OrderedSpace.Bands](CKMA/Analysis/OrderedSpace/Bands.lean). An algebraic real Riesz space with Dedekind completeness on the chosen order; range, disjoint-complement kernel, idempotence, positivity, domination by identity, and positive-vector supremum characterization.
- **19.8 Freudenthal spectral theorem** — partial; [CKMA.Analysis.OrderedSpace.Bands](CKMA/Analysis/OrderedSpace/Bands.lean). The order-error approximation by finite disjoint components of a positive element is proved, under the stated Archimedean hypothesis and principal positive band projections, with a concrete principal ideal and order-unit gauge. The gauge API and an abstract order-unit normed-space packaging remain.
- **19.20 Riesz–Kantorovich theorem** — partial; [CKMA.Analysis.OrderedSpace.Bands](CKMA/Analysis/OrderedSpace/Bands.lean). The equivalence of order-bounded and regular operators into a Dedekind-complete real Riesz space is proved, as is the binary supremum and its Riesz–Kantorovich formula. Bundling the full Dedekind-complete operator lattice and the operator-modulus formula remain.
- **19.27 Kakutani representation of AM spaces with unit** — partial; [CKMA.Analysis.OrderedSpace.Representation](CKMA/Analysis/OrderedSpace/Representation.lean). AM Banach lattice with a unit represented by a lattice isometric linear equivalence to real C(K), taking the unit to one; K may be empty for the zero space. The C(K)-is-AM converse is not yet separately stated.
- **19.29 Kakutani representation of AL spaces** — partial; [CKMA.Analysis.OrderedSpace.Representation](CKMA/Analysis/OrderedSpace/Representation.lean). Real AL Banach lattice representation as a lattice-isometric L1 space and the KB consequence. The representing measure is not restricted to sigma-finite measures. Full net-based order continuity remains.
- **20.19 Gleason–Kahane–Żelazko theorem** — proved; [CKMA.Analysis.BanachAlgebra.Factorization](CKMA/Analysis/BanachAlgebra/Factorization.lean). Unital complex Banach algebras; algebraic normalized functional, no continuity or commutativity assumed.
- **20.23 Shilov boundary theorem** — proved; [CKMA.Analysis.BanachAlgebra.Factorization](CKMA/Analysis/BanachAlgebra/Factorization.lean). Closed point-separating subalgebra of C(K), compact Hausdorff K; smallest closed norming boundary. Supremum convention includes empty K.
- **20.40 Wiener lemma** — statement; [CKMA.Analysis.BanachAlgebra.Wiener](CKMA/Analysis/BanachAlgebra/Wiener.lean).
- **20.41 Wiener Tauberian theorem** — partial; [CKMA.Analysis.BanachAlgebra.Factorization](CKMA/Analysis/BanachAlgebra/Factorization.lean). Real-line L1 translates and the Fourier-integral nonvanishing criterion. General LCA groups and the convolution-ideal adapter remain.
- **20.47 Cohen–Hewitt factorization** — partial; [CKMA.Analysis.BanachAlgebra.Factorization](CKMA/Analysis/BanachAlgebra/Factorization.lean). Genuinely nonunital real or complex Banach algebras with a bounded directed left approximate identity acting strongly on the module. The essential-module characterization and norm control on the factor y remain.
- **21.11 Atkinson theorem** — proved; [CKMA.Analysis.Operator.Fredholm](CKMA/Analysis/Operator/Fredholm.lean). Operators between real or complex Banach spaces, uniformly over RCLike scalars; no quotient Calkin algebra is introduced.
- **21.15 Analytic Fredholm theorem** — partial; [CKMA.Analysis.Operator.AnalyticFredholm](CKMA/Analysis/Operator/AnalyticFredholm.lean). Invertibility at one point gives isolated exceptional parameters, analytic inverse elsewhere and genuine positive-order inverse poles with nonzero analytic regularizations. Finite-rank principal parts remain.
- **21.16 Discrete spectrum of self-adjoint operators** — proved; [CKMA.Analysis.Operator.Fredholm](CKMA/Analysis/Operator/Fredholm.lean). The essential spectrum is the Fredholm essential spectrum. Compact-perturbation invariance and the characterization by isolated eigenvalues of finite multiplicity are proved.
- **21.22 Schatten Hölder inequality** — partial; [CKMA.Analysis.Operator.TraceIdeals](CKMA/Analysis/Operator/TraceIdeals.lean). Sharp constant-one finite real exponents p,q,r>=1, using TauCeti Schatten gauges on arbitrary Hilbert spaces. Infinite-exponent endpoints remain.
- **21.23 Trace and cyclicity** — statement; [CKMA.Analysis.Operator.TraceIdeals](CKMA/Analysis/Operator/TraceIdeals.lean). Absolute convergence, basis independence, trace-norm bound and bounded-product cyclicity, with the actual upstream Schatten-one gauge.
- **21.26 Wold decomposition** — proved; [CKMA.Analysis.Operator.Dilation](CKMA/Analysis/Operator/Dilation.lean). Isometries on complex Hilbert spaces; wandering coefficient space ker(V*), invariant-surjective unitary part, pairwise orthogonal forward wandering spaces and unconditional decompositions.
- **21.30 Unitary dilation theorem** — proved; [CKMA.Analysis.Operator.Dilation](CKMA/Analysis/Operator/Dilation.lean). Minimal unitary power dilation and unique intertwining isometry for contractions; larger representation space bundled as ComplexHilbertSpace.
- **21.37 Commutant lifting** — proved; [CKMA.Analysis.Operator.Dilation](CKMA/Analysis/Operator/Dilation.lean). Existence of the minimal co-invariant isometric dilation and the norm-preserving commuting coextension, expressed with actual adjoints and operator norms.
- **22.19 First representation theorem** — statement; [CKMA.Analysis.Operator.ClosedForms](CKMA/Analysis/Operator/ClosedForms.lean). Densely defined complex sesquilinear form with explicit lower bound; completeness is in its form graph norm, not the ambient Hilbert norm. Unique self-adjoint representing partial map with matching lower bound.
- **22.21 Friedrichs extension** — partial; [CKMA.Analysis.Operator.ClosedForms](CKMA/Analysis/Operator/ClosedForms.lean). Friedrichs existence/lower-bound clause for a densely defined semibounded symmetric operator; the canonical form completion and uniqueness characterization remain.
- **22.22 KLMN theorem** — proved; [CKMA.Analysis.Operator.ClosedForms](CKMA/Analysis/Operator/ClosedForms.lean). Symmetric relative-form perturbation of a nonnegative closed form, relative bound 0<=a<1 and lower constant c>=0; same domain and explicit lower bound -c.
- **22.32 Kato–Rellich theorem: cores** — proved; [CKMA.Analysis.Operator.KatoRellich](CKMA/Analysis/Operator/KatoRellich.lean). Every core of a self-adjoint operator remains a core of a symmetric relatively bounded perturbation with relative bound strictly less than one, and restriction to that core is essentially self-adjoint.
- **22.34 Analytic isolated eigenvalues** — partial; [CKMA.Analysis.Operator.AnalyticFredholm](CKMA/Analysis/Operator/AnalyticFredholm.lean). Bounded type-(A) families near zero, algebraically simple eigenpair specified by a rank-one reduced resolvent; actual holomorphic eigenvalue and eigenvector branches. Finite clusters, Riesz projections and unbounded type-(A)/(B) families remain.
- **22.38 Birman–Schwinger principle** — partial; [CKMA.Analysis.Operator.SpectralDynamics](CKMA/Analysis/Operator/SpectralDynamics.lean). Bounded-operator kernel equivalence for a positive self-adjoint free operator and positive shift; the factor need not be compact or self-adjoint. The unbounded form setting and eigenvalue counting statements remain.
- **22.63 RAGE theorem** — partial; [CKMA.Analysis.Operator.SpectralDynamics](CKMA/Analysis/Operator/SpectralDynamics.lean). Bounded self-adjoint generators: continuous-subspace compact-observation time averages and pure-point relative compactness of full unitary orbits. Unbounded generators remain.
- **23.9 GNS cyclic vector and uniqueness** — partial; [CKMA.Analysis.CStarAlgebra.Representation](CKMA/Analysis/CStarAlgebra/Representation.lean). Uniqueness of cyclic realizations, including nonunital representations. Existence of the nonunital cyclic vector remains.
- **23.10 Gelfand–Naimark theorem** — partial; [CKMA.Analysis.CStarAlgebra.Representation](CKMA/Analysis/CStarAlgebra/Representation.lean). An isometric representation with closed range is proved for every C*-algebra, including a nonunital one, by an ℓ² sum of one GNS representation for each algebra element and restriction from the unitization. The universal direct sum over all states remains.
- **23.21 Bicommutant theorem** — statement; [CKMA.Analysis.CStarAlgebra.OperatorClosures](CKMA/Analysis/CStarAlgebra/OperatorClosures.lean). Unital star subalgebra, with explicit finite-vector and finite-matrix-coefficient neighborhood definitions of the strong and weak operator closures.
- **23.22 Kaplansky density theorem** — partial; [CKMA.Analysis.CStarAlgebra.OperatorClosures](CKMA/Analysis/CStarAlgebra/OperatorClosures.lean). Possibly nonunital norm-closed star algebra acting nondegenerately; general and self-adjoint unit-ball strong density. Positive unit-ball version remains.
- **23.65 Free central limit theorem** — statement; [CKMA.Analysis.CStarAlgebra.FreeProbability](CKMA/Analysis/CStarAlgebra/FreeProbability.lean). Normalized positive algebraic state and identically distributed free centered variance-one self-adjoint variables; convergence of all normalized-sum moments to explicit semicircle (Catalan) moments.
- **23.68 R-transform linearization** — statement; [CKMA.Analysis.CStarAlgebra.FreeProbability](CKMA/Analysis/CStarAlgebra/FreeProbability.lean). Concrete triangular cumulant recursion, coefficient additivity for free variables, and R-transform series convergence/additivity on a common disk for bounded variables and a bounded normalized functional.
- **24.13 Variation of constants** — statement; [CKMA.Analysis.Semigroup.Approximation](CKMA/Analysis/Semigroup/Approximation.lean). Uses pinned TauCeti C0 semigroups and generators; unique continuous integrated solution for L1 forcing and classical interior-time regularity for C1 forcing/domain initial data.
- **24.17 Trotter–Kato approximation** — statement; [CKMA.Analysis.Semigroup.Approximation](CKMA/Analysis/Semigroup/Approximation.lean). One sufficiently large real resolvent parameter and a common exponential bound; equivalent uniform-on-bounded-time strong convergence.
- **24.18 Chernoff product formula** — statement; [CKMA.Analysis.Semigroup.Approximation](CKMA/Analysis/Semigroup/Approximation.lean). Stable strongly continuous product family with tangency on an actual generator core; uniform convergence on bounded nonnegative time intervals.
- **24.20 Analytic generation theorem** — statement; [CKMA.Analysis.Semigroup.Sectorial](CKMA/Analysis/Semigroup/Sectorial.lean). Closed densely defined partial operators, explicit spectral sectors/resolvent estimates, actual bounded operator-valued holomorphic extensions, and negative-generator sign convention.
- **24.23 Balakrishnan formula** — partial; [CKMA.Analysis.Semigroup.Sectorial](CKMA/Analysis/Semigroup/Sectorial.lean). Actual normalized resolvent integral on D(B), integrability, and existence of its closed fractional-power graph. A full named fractional-power/domain calculus remains.
- **24.35 Analytic spectral mapping** — partial; [CKMA.Analysis.Semigroup.Sectorial](CKMA/Analysis/Semigroup/Sectorial.lean). Eventually norm-continuous complex semigroups, with zero removed from the semigroup spectrum. An explicit analytic-extension-to-norm-continuity adapter remains.
- **24.39 Gearhart–Prüss theorem** — statement; [CKMA.Analysis.Semigroup.Stability](CKMA/Analysis/Semigroup/Stability.lean). Bounded C0 semigroups on complex Hilbert spaces and the uniform imaginary-axis generator resolvent criterion.
- **24.40 Arendt–Batty–Lyubich–Vũ theorem** — partial; [CKMA.Analysis.Semigroup.Stability](CKMA/Analysis/Semigroup/Stability.lean). Reflexive complex normed-space branch, with completeness derived from surjectivity of the bidual inclusion, countable imaginary-axis spectrum and no generator eigenvalues there. The general Banach-adjoint criterion remains.
- **24.52 Crandall–Liggett generation** — proved; [CKMA.Analysis.Semigroup.Accretive](CKMA/Analysis/Semigroup/Accretive.lean). Concrete multivalued accretive graph and guarded resolvent; nonlinear contraction semigroup on the domain closure, Euler convergence there, and uniform time convergence on the actual domain.
- **25.3 Hilbert–Schmidt kernels** — proved; [CKMA.Analysis.IntegralEquation.HilbertSchmidt](CKMA/Analysis/IntegralEquation/HilbertSchmidt.lean). Real or complex scalars. Sigma-finite measures with a supplied Hilbert basis; exact Hilbert-Schmidt energy and scalar-star adjoint kernel.
- **25.8 Mercer theorem** — statement; [CKMA.Analysis.IntegralEquation.Mercer](CKMA/Analysis/IntegralEquation/Mercer.lean). Continuous positive-semidefinite kernel on compact Hausdorff D with finite full-support Borel measure; trace-class kernel operator, nonnegative eigenvalues, continuous normalized eigenfunctions, unconditional expansion and uniform absolute tails, including finite-rank/zero kernels.
- **25.18 Volterra solvability** — partial; [CKMA.Analysis.IntegralEquation.Basic](CKMA/Analysis/IntegralEquation/Basic.lean). Existence and uniqueness for continuous triangular kernels. Successive-substitution convergence and continuous data dependence remain.
- **25.23 Abel inversion** — proved; [CKMA.Analysis.IntegralEquation.Basic](CKMA/Analysis/IntegralEquation/Basic.lean). Real integrable functions on a bounded interval `(0,T)`. The semigroup law, the range characterization, and differentiation inversion hold almost everywhere. Vanishing at zero is the value of the absolutely continuous representative.
- **25.47 Collectively compact approximation theorem** — proved; [CKMA.Analysis.IntegralEquation.CollectiveCompactness](CKMA/Analysis/IntegralEquation/CollectiveCompactness.lean). Strong collectively compact approximation on a real or complex Banach space.
- **26.16 Failure of the critical $L^\infty$ embedding** — statement; [CKMA.Analysis.Sobolev.Critical](CKMA/Analysis/Sobolev/Critical.lean). Any nonempty open Euclidean domain, dimension at least two; essential unboundedness is stated by failure of MemLp at infinity.
- **26.31 Quasicontinuity** — statement; [CKMA.Analysis.Sobolev.CapacityAndBBM](CKMA/Analysis/Sobolev/CapacityAndBBM.lean). Inhomogeneous C1,p capacity from smooth compact tests and open outer approximation; real weak first-order functions with finite p>1, including quasi-everywhere uniqueness.
- **26.37 Fractional Hilbert identity** — statement; [CKMA.Analysis.Sobolev.Fractional](CKMA/Analysis/Sobolev/Fractional.lean). Extended square energies and their quantitative comparison, on L2; bundling the two Sobolev spaces is separate infrastructure.
- **26.42 Bourgain–Brezis–Mironescu limit** — statement; [CKMA.Analysis.Sobolev.CapacityAndBBM](CKMA/Analysis/Sobolev/CapacityAndBBM.lean). Real scalar W1,p functions, all finite p>=1; exact constant expressed by a unit-ball moment, equivalent to the sphere constant by radial integration.
- **26.53 Real interpolation theorem** — partial; [CKMA.Analysis.Interpolation.Bounds](CKMA/Analysis/Interpolation/Bounds.lean). The exact K-method gauge bound, including exponent infinity, is proved for compatible Banach couples in their canonical normed sum. Endpoint constants need no sign hypothesis. Bundled interpolation normed spaces, completeness, and construction from arbitrary compatible embeddings remain.
- **26.54 Complex interpolation theorem** — partial; [CKMA.Analysis.Interpolation.Bounds](CKMA/Analysis/Interpolation/Bounds.lean). The exact Calderón gauge bound is proved. Endpoint constants need no sign hypothesis. Bundled normed spaces, completeness, and extension from arbitrary ambient embeddings remain.
- **27.4 Hausdorff–Young inequality** — partial; [CKMA.Analysis.Fourier.HausdorffYoung](CKMA/Analysis/Fourier/HausdorffYoung.lean). Failure above `p = 2` is proved for Schwartz functions. The `L¹ ∩ Lᵖ` inequality remains admitted. Extension to a bounded Fourier map on all of `Lᵖ` remains.
- **27.13 Heisenberg uncertainty** — partial; [CKMA.Analysis.Fourier.Inequalities](CKMA/Analysis/Fourier/Inequalities.lean). Uncentered coordinate inequality with explicit L2 moment assumptions; centered versions and Gaussian equality classification remain.
- **27.17 Fejér summation** — partial; [CKMA.Analysis.Fourier.CircleConvergence](CKMA/Analysis/Fourier/CircleConvergence.lean). One-dimensional probability circle: finite-p convergence, uniform convergence for continuous functions, and every lifted Lebesgue point. The product-kernel multidimensional interface remains.
- **27.22 Carleson–Hunt theorem** — statement; [CKMA.Analysis.Fourier.CircleSummation](CKMA/Analysis/Fourier/CircleSummation.lean). Actual symmetric Fourier sums using Mathlib coefficients and circle characters; extended maximal pth-moment bound and almost-everywhere Fourier convergence for every 1<p<infinity.
- **27.35 Hilbert transform as a principal-value integral** — statement; [CKMA.Analysis.Fourier.HilbertTransform](CKMA/Analysis/Fourier/HilbertTransform.lean). Concrete symmetric-distance truncations, principal-value limit, a.e. convergence for finite p>=1, identification with the -i sign multiplier on L2, and actual weak (1,1) control.
- **27.44 Weighted maximal theorem** — statement; [CKMA.Analysis.Fourier.WeightedMaximal](CKMA/Analysis/Fourier/WeightedMaximal.lean). Ball-based A_p and A_1 characteristics, positive locally integrable weights, weighted Haar densities, and TauCeti centered maximal function. Ball/cube classes are mathematically equivalent, but an explicit cube-comparison adapter remains.
- **28.2 The modular homomorphism** — partial; [CKMA.MeasureTheory.Group.Modular](CKMA/MeasureTheory/Group/Modular.lean). Continuity for locally compact Hausdorff groups; the inversion measure identity currently assumes second countability. General Haar inversion and explicit integral adapters remain.
- **28.24 Pontryagin duality** — statement; [CKMA.Analysis.Fourier.LocallyCompactAbelian](CKMA/Analysis/Fourier/LocallyCompactAbelian.lean). General locally compact Hausdorff abelian groups; evaluation formula specifies the topological double-dual equivalence using Mathlib compact-open duals.
- **28.29 Plancherel theorem** — partial; [CKMA.Analysis.Fourier.LocallyCompactAbelian](CKMA/Analysis/Fourier/LocallyCompactAbelian.lean). Second-countable LCA groups, normalized dual Haar measure, a Plancherel isometry equivalence with the L1 Fourier integral on L1∩L2, and Hausdorff-Young bounds on L1∩Lp. General non-sigma-compact groups and bundled all-Lp extensions remain.
- **28.58 Amenability and invariant means** — partial; [CKMA.Analysis.Fourier.InvariantMean](CKMA/Analysis/Fourier/InvariantMean.lean). Actual positive normalized bounded functionals on Haar L-infinity, a.e.-intrinsic left invariance, compact and abelian amenability, and closed-subgroup inheritance. Extension permanence and comparison to other amenability models remain.
- **29.2 Frame operator criterion** — partial; [CKMA.Analysis.InnerProductSpace.Frame](CKMA/Analysis/InnerProductSpace/Frame.lean). Concrete coefficient energies, Bessel/frame predicates, analysis criterion and synthesis-surjectivity criterion. The explicit operator-order equivalence remains.
- **29.3 Canonical dual reconstruction** — partial; [CKMA.Analysis.InnerProductSpace.Frame](CKMA/Analysis/InnerProductSpace/Frame.lean). Reciprocal reversed bounds and both unconditional expansions; optimality of those bounds is not stated.
- **29.46 Density obstruction** — partial; [CKMA.Analysis.Fourier.Gabor](CKMA/Analysis/Fourier/Gabor.lean). Rectangular one-dimensional single-window Gabor families: frame and Riesz-sequence density bounds and the critical-density basis corollary. Higher dimensions remain. The corollary inherits admitted dependencies.
- **29.51 Balian–Low theorem** — statement; [CKMA.Analysis.Fourier.Gabor](CKMA/Analysis/Fourier/Gabor.lean). L2 Gabor Riesz bases, concrete time-frequency translates, and the incompatibility of finite second moments on both the window and its L2 Fourier transform.
- **29.58 Shannon sampling theorem** — proved; [CKMA.Analysis.Fourier.Sampling](CKMA/Analysis/Fourier/Sampling.lean). Inverse-integral representatives formed by restricting arbitrary L2 frequency data to [-B,B], B>0, with normalized sinc. Outside-band data are irrelevant to these representative-only conclusions.
- **29.61 Kadec's one-quarter theorem** — statement; [CKMA.Analysis.Fourier.NonuniformSampling](CKMA/Analysis/Fourier/NonuniformSampling.lean). Equivalent normalized exponential Riesz basis on the frequency interval, a uniform perturbation bound strictly below one quarter, and a sharpness counterexample for every larger threshold.
- **29.62 Landau's necessary densities** — statement; [CKMA.Analysis.Fourier.NonuniformSampling](CKMA/Analysis/Fourier/NonuniformSampling.lean). Uniformly separated sample sets, extended lower/upper Beurling densities, and stable sampling/interpolation for inverse-integral bandlimited representatives.
- **29.68 Stable recovery from restricted isometry** — statement; [CKMA.Analysis.Approximation.CompressedSensing](CKMA/Analysis/Approximation/CompressedSensing.lean). Concrete finite-coordinate l1 norms, sparsity, best sparse error and basis-pursuit minimizers. Uniform constants depend only on an admissible delta_(2s)<sqrt(2)-1; positive sparsity and nonnegative noise are explicit.
- **30.27 Calderón–Vaillancourt theorem** — partial; [CKMA.Analysis.Microlocal.Symbols](CKMA/Analysis/Microlocal/Symbols.lean). Finite-derivative L2 estimate on the dense Schwartz class for actual physical-convention left quantization. A bundled extension to all L2 inputs remains.
- **30.28 Sobolev mapping theorem** — partial; [CKMA.Analysis.Microlocal.Symbols](CKMA/Analysis/Microlocal/Symbols.lean). Global S1,0 symbol class and quantitative Sobolev energy estimate on Schwartz functions. Bounded completed-space maps and properly supported local interfaces remain.
- **30.31 Sharp Gårding inequality** — statement; [CKMA.Analysis.Microlocal.Symbols](CKMA/Analysis/Microlocal/Symbols.lean). Nonnegative real scalar global S1,0 symbols and the sharp (m-1)/2 Sobolev-order lower bound on Schwartz inputs; physical exp(ix dot xi) normalization.
- **31.17 Floquet theorem** — statement; [CKMA.Analysis.ODE.PeriodicAndSturm](CKMA/Analysis/ODE/PeriodicAndSturm.lean). Normalized fundamental operator curves for finite-dimensional real/complex spaces; complex period T and real period 2T factorizations with invertible C1 periodic factors.
- **31.20 Sturm separation and comparison** — proved; [CKMA.Analysis.ODE.PeriodicAndSturm](CKMA/Analysis/ODE/PeriodicAndSturm.lean). Classical regular interval equations with positive leading coefficient, positive weight for spectral comparison, consecutive lower-mode zeros, and a Wronskian independence test for separation.
- **31.24 Lyapunov's direct theorem** — partial; [CKMA.Dynamics.Lyapunov](CKMA/Dynamics/Lyapunov.lean). Local stability and attraction for an existing global flow. The strict criterion assumes continuity of the vector field. Local ODE construction, continuation and proper global variants remain.
- **31.26 LaSalle invariance principle** — proved; [CKMA.Dynamics.Lyapunov](CKMA/Dynamics/Lyapunov.lean). A compact positively invariant subset of an existing global flow, with no finite-rest-set assumption.
- **31.38 Poincaré–Bendixson theorem** — statement; [CKMA.Dynamics.ODE.Planar](CKMA/Dynamics/ODE/Planar.lean). Existing global C1 planar flow with an orbit in a compact forward absorbing set; no equilibrium in its omega-limit set, which is identified with a whole periodic orbit.
- **32.50 Wave Cauchy problem in energy spaces** — statement; [CKMA.Analysis.PDE.Wave](CKMA/Analysis/PDE/Wave.lean). Actual TauCeti W1,2 position states and L2 velocities, continuous on a compact time interval; positive wave speed, L1-in-time L2 forcing, integrated weak velocity equation, and unique time-interval curves.
- **32.52 Finite propagation speed** — statement; [CKMA.Analysis.PDE.Wave](CKMA/Analysis/PDE/Wave.lean). Two energy solutions whose initial positions agree a.e. on a ball, whose initial velocities agree there, and whose forcing agrees in the backward shrinking cone have agreeing position components, as TauCeti W1p values, a.e. on later shrinking balls.
- **33.9 Higher integrability of the gradient** — statement; [CKMA.Analysis.PDE.EllipticEstimates](CKMA/Analysis/PDE/EllipticEstimates.lean). Actual W1,2 weak gradients and bounded measurable uniformly elliptic divergence coefficients; homogeneous and divergence-forcing local Meyers estimate on concentric unit/two balls.
- **33.14 Alexandrov–Bakelman–Pucci estimate** — partial; [CKMA.Analysis.PDE.EllipticEstimates](CKMA/Analysis/PDE/EllipticEstimates.lean). Classical C2-in-domain, continuous-up-to-boundary ABP inequality on bounded domains with extended source norm; the W2,n strong-solution interface remains.
- **33.15 Krylov–Safonov theorem** — partial; [CKMA.Analysis.PDE.EllipticEstimates](CKMA/Analysis/PDE/EllipticEstimates.lean). Uniform Harnack and interior Holder estimates for classical C2 solutions with merely measurable uniformly elliptic coefficients. The general strong-solution formulation remains.
- **33.16 Interior Schauder estimate** — statement; [CKMA.Analysis.PDE.EllipticEstimates](CKMA/Analysis/PDE/EllipticEstimates.lean). Localized C2,alpha a priori gauge estimate for general Holder coefficients including drift and zeroth order terms, with explicit coefficient-gauge finiteness.
- **33.18 Interior $W^{2,p}$ estimates** — partial; [CKMA.Analysis.PDE.EllipticEstimates](CKMA/Analysis/PDE/EllipticEstimates.lean). Classical a priori interior Hessian Lp bound with continuous leading and bounded measurable lower coefficients. The full strong W2,p realization remains.
- **33.23 Comparison and uniqueness** — statement; [CKMA.Analysis.PDE.Viscosity](CKMA/Analysis/PDE/Viscosity.lean). Actual semicontinuous upper/lower contact definitions; comparison for gamma u+G0(Du,D2u)=f on bounded domains with gamma>0 and autonomous continuous degenerate elliptic G0.
- **33.30 Evans–Krylov theorem** — statement; [CKMA.Analysis.PDE.Viscosity](CKMA/Analysis/PDE/Viscosity.lean). Actual viscosity solutions of a convex or concave uniformly elliptic Hessian equation; C2,beta interior regularity and quantitative gauge estimate with Holder forcing.
- **33.34 $p$-harmonic regularity** — statement; [CKMA.Analysis.PDE.EllipticEstimates](CKMA/Analysis/PDE/EllipticEstimates.lean). Actual W1,p weak p-harmonicity at finite p>1, locally C1,alpha representatives and a nonnegative Harnack estimate on concentric balls.
- **34.9 Kružkov existence and uniqueness** — partial; [CKMA.Analysis.PDE.Entropy](CKMA/Analysis/PDE/Entropy.lean). Concrete entropy inequalities with initial trace term, bounded existence, maximum principle, L1-local trace, and spacetime-a.e. uniqueness. Local finite-speed stability remains.
- **34.14 Hopf–Lax formula** — partial; [CKMA.Analysis.PDE.Entropy](CKMA/Analysis/PDE/Entropy.lean). Concrete extended Legendre transform and Hopf-Lax infimum, finiteness, first-order viscosity solution and initial attainment for superlinear convex Hamiltonians. Spatial derivative/entropy bridge remains.
- **34.24 Homogeneous Strichartz estimate** — partial; [CKMA.Analysis.PDE.Schrodinger](CKMA/Analysis/PDE/Schrodinger.lean). All admissible exponent pairs including infinity and the forbidden-endpoint exclusion; global mixed-norm estimate for the actual free Fourier evolution of Schwartz data. L2 operator extension remains.
- **34.32 Virial blowup criterion** — partial; [CKMA.Analysis.PDE.Schrodinger](CKMA/Analysis/PDE/Schrodinger.lean). Exact focusing virial identity for jointly C3 Schwartz slices with locally uniform rapid derivative decay. Energy-class finite-variance approximation and finite-time breakdown conclusion remain.
- **34.54 Leray–Hopf existence** — partial; [CKMA.Analysis.PDE.NavierStokes](CKMA/Analysis/PDE/NavierStokes.lean). Global Euclidean three-dimensional existence with actual L2 velocity curves, distributional incompressibility/momentum, weak spatial derivatives, finite dissipation, weak continuity and energy inequalities. Torus variant remains.
- **34.55 Two-dimensional viscous uniqueness** — partial; [CKMA.Analysis.PDE.NavierStokes](CKMA/Analysis/PDE/NavierStokes.lean). Global Euclidean two-dimensional energy-class existence and uniqueness of the nonnegative-time velocity curve; gradient representatives are existential a.e. data. Positive-time smoothness interface remains.
- **34.70 Boltzmann's $H$ theorem** — partial; [CKMA.Analysis.PDE.Boltzmann](CKMA/Analysis/PDE/Boltzmann.lean). Hard-sphere collision operator and exact negative entropy-production identity for positive measurable densities under explicit four-log absolute integrability, with probability-normalized angular measure. Zero-density extension and spatial transport entropy remain.
- **35.9 Newton–Kantorovich convergence** — partial; [CKMA.Analysis.Nonlinear.Newton](CKMA/Analysis/Nonlinear/Newton.lean). Real or complex scalars. Concrete totalized Newton iteration, majorant-radius convergence including the L=0 limiting radius, and local quadratic convergence. The initial step is controlled by a norm bound. A separate affine one-step corollary is not stated.
- **35.12 Brouwer fixed-point theorem** — statement; [CKMA.Analysis.Nonlinear.FixedPoint](CKMA/Analysis/Nonlinear/FixedPoint.lean).
- **35.13 Schauder fixed-point theorem** — statement; [CKMA.Analysis.Nonlinear.FixedPoint](CKMA/Analysis/Nonlinear/FixedPoint.lean). Nonempty closed convex subset of a Banach space and continuous self-map with relatively compact total image; the domain may be unbounded.
- **35.15 Kakutani–Fan–Glicksberg theorem** — statement; [CKMA.Analysis.Nonlinear.FixedPoint](CKMA/Analysis/Nonlinear/FixedPoint.lean). Upper-hemicontinuous multifunction on a nonempty compact convex set in a locally convex Hausdorff space, with nonempty closed convex values in that set.
- **35.21 Browder–Göhde–Kirk theorem** — statement; [CKMA.Analysis.Nonlinear.FixedPoint](CKMA/Analysis/Nonlinear/FixedPoint.lean). Nonempty closed bounded convex subset of a uniformly convex real Banach space; no compactness of the map.
- **35.32 Minty's range theorem** — statement; [CKMA.Analysis.Nonlinear.Monotone](CKMA/Analysis/Nonlinear/Monotone.lean). Hilbert graphs and positive-scale resolvent fibers; one/every scale equivalence. Fiber uniqueness from monotonicity is proved independently; the existence corollary depends on the admitted Minty theorem.
- **35.40 Browder–Minty surjectivity** — statement; [CKMA.Analysis.Nonlinear.Monotone](CKMA/Analysis/Nonlinear/Monotone.lean). Bounded-on-bounded, hemicontinuous monotone dual-valued map on a reflexive real Banach space, with coercivity in the dual pairing; strict-monotonicity injectivity is proved.
- **35.45 Existence for variational inequalities** — statement; [CKMA.Analysis.Nonlinear.Monotone](CKMA/Analysis/Nonlinear/Monotone.lean). Both bounded closed convex and unbounded coercive variants in reflexive real Banach spaces; explicit forcing and basepoint-relative coercivity.
- **36.1 Euler–Lagrange equation** — partial; [CKMA.Analysis.Variational.EulerLagrange](CKMA/Analysis/Variational/EulerLagrange.lean). Proved conditional weak first variation: local minimality plus a justified derivative-of-action identity. Derivation from growth bounds and the classical Euler-Lagrange PDE remain.
- **36.35 Mountain-pass theorem** — proved; [CKMA.Analysis.Variational.MountainPass](CKMA/Analysis/Variational/MountainPass.lean). Concrete continuous path class and real minimax level; C1 Banach functional with the Palais-Smale condition only at that level.
- **37.4 Frostman's lemma** — partial; [CKMA.Analysis.GeometricMeasure.Dimension](CKMA/Analysis/GeometricMeasure/Dimension.lean). Positive Hausdorff measure on a compact Euclidean set, at a strictly positive exponent, iff there is a supported Frostman probability. This positivity is mathematically equivalent to positive Hausdorff content; a separate content definition and explicit dimension corollary remain.
- **37.8 Projection dimension theorem** — partial; [CKMA.Analysis.GeometricMeasure.Dimension](CKMA/Analysis/GeometricMeasure/Dimension.lean). Planar Borel sets and angular projections to a line, including positive projected length above dimension one. Higher-dimensional Grassmannian formulations remain.
- **37.21 Besicovitch–Federer projection theorem** — partial; [CKMA.Analysis.GeometricMeasure.Dimension](CKMA/Analysis/GeometricMeasure/Dimension.lean). Planar Borel sets of finite one-dimensional Hausdorff measure; pure unrectifiability is tested on actual Lipschitz curves, and projected length vanishes almost everywhere. Higher dimensions remain.
- **37.24 BV compactness** — partial; [CKMA.Analysis.BoundedVariation.Compactness](CKMA/Analysis/BoundedVariation/Compactness.lean). Whole-space BV families supported in a fixed compact set, uniform L1-plus-variation bound, strong L1 subsequence convergence, and lower semicontinuity. Uses TauCeti variation. The global bounded-Lipschitz-domain extension/compactness interface remains.
- **37.30 Coarea for BV** — statement; [CKMA.Analysis.BoundedVariation.Compactness](CKMA/Analysis/BoundedVariation/Compactness.lean). Scalar measurable BV functions on any Euclidean open set, actual TauCeti total variation and perimeter, and the extended integral over superlevel sets.
- **38.17 Equilibrium measure** — statement; [CKMA.Analysis.Potential.Capacity](CKMA/Analysis/Potential/Capacity.lean). Variational compact and outer Newtonian capacities, positive potentials and energies retaining infinity at the kernel pole; unique equilibrium charge for compact sets including zero capacity, in dimension at least three.
- **38.20 Choquet properties** — partial; [CKMA.Analysis.Potential.Capacity](CKMA/Analysis/Potential/Capacity.lean). Monotonicity is proved; continuity below, compact continuity above, countable subadditivity and Borel capacitability are targets. The stronger analytic-set capacitability clause is not stated.
- **38.28 Perron–Wiener resolutivity** — partial; [CKMA.Analysis.Potential.Capacity](CKMA/Analysis/Potential/Capacity.lean). Lower/upper Perron equality and unique probability harmonic-measure representation on bounded open Euclidean sets of dimension at least two, allowing disconnected sets and irregular boundary. Null-set independence from the pole remains unstated.
- **38.30 Wiener's criterion** — statement; [CKMA.Analysis.Potential.Capacity](CKMA/Analysis/Potential/Capacity.lean). Bounded open Euclidean sets in dimension at least three, without connectedness; boundary regularity is actual Perron attainment, with concrete annular pieces and divergent capacity series.
- **39.73 Self-similar attractors** — proved; [CKMA.Dynamics.IteratedFunctionSystem](CKMA/Dynamics/IteratedFunctionSystem.lean). Nonempty complete metric ambient space and finite contractions; the compact attractor uses a nonempty family. Invariant probabilities allow nonnegative weights summing to one, including zeros, and uniqueness is among all invariant Borel probabilities.
- **40.25 Laurent expansion** — partial; [CKMA.Analysis.Complex.Laurent](CKMA/Analysis/Complex/Laurent.lean). Finite-radius annuli with nonnegative inner radius. A direct infinite-outer-radius interface remains.
- **40.29 Great Picard theorem** — partial; [CKMA.Analysis.Complex.PlaneApproximation](CKMA/Analysis/Complex/PlaneApproximation.lean). Holomorphic punctured-disk Great Picard, every finite value infinitely often with at most one exception. The meromorphic spherical two-exception version remains.
- **40.60 Runge approximation on compact sets** — partial; [CKMA.Analysis.Complex.PlaneApproximation](CKMA/Analysis/Complex/PlaneApproximation.lean). Prescribed finite poles meet every bounded complementary component; infinity is always permitted through a polynomial part. The formulation where infinity is forbidden remains.
- **40.62 Mergelyan's theorem** — statement; [CKMA.Analysis.Complex.PlaneApproximation](CKMA/Analysis/Complex/PlaneApproximation.lean).
- **40.63 Mittag–Leffler theorem** — statement; [CKMA.Analysis.Complex.PlaneApproximation](CKMA/Analysis/Complex/PlaneApproximation.lean). Arbitrary compact-locally-finite pole data on a nonempty connected plane domain; principal parts are finite reciprocal-coordinate polynomials with zero constant term. Identities use analytic germs on punctured neighborhoods.
- **40.64 Weierstrass zero theorem** — statement; [CKMA.Analysis.Complex.PlaneApproximation](CKMA/Analysis/Complex/PlaneApproximation.lean). Exact zero sets and prescribed positive analytic orders on locally finite data in a plane domain.
- **41.10 Hadamard factorization** — statement; [CKMA.Analysis.Complex.EntireGrowth](CKMA/Analysis/Complex/EntireGrowth.lean). Nonzero entire functions of finite real growth order; fixed genus and polynomial degree bounded by the order, an optional zero list allowing finite lists, explicit summability and locally uniform product convergence.
- **41.26 Cartwright zero distribution** — statement; [CKMA.Analysis.Complex.EntireGrowth](CKMA/Analysis/Complex/EntireGrowth.lean). Exponential-type Cartwright functions, multiplicity counting and real-axis-sector concentration. Extended logarithms retain negative infinity at zeros in the indicator.
- **41.38 Logarithmic derivative lemma** — partial; [CKMA.Analysis.Complex.EntireGrowth](CKMA/Analysis/Complex/EntireGrowth.lean). Every fixed positive derivative order for entire nonconstant functions, using Mathlib Nevanlinna proximity/characteristic and a finite-linear-measure exceptional set. General meromorphic functions and finite-order O(log r) sharpening remain.
- **41.48 Five-value theorem** — partial; [CKMA.Analysis.Complex.EntireGrowth](CKMA/Analysis/Complex/EntireGrowth.lean). Nonconstant entire functions sharing four distinct finite preimage sets; their common omitted spherical value infinity gives the fifth shared value. The general meromorphic theorem and pole fibers remain.
- **42.1 Hardy boundary realization beyond radial $H^2$ convergence** — statement; [CKMA.Analysis.Complex.Hardy](CKMA/Analysis/Complex/Hardy.lean). Concrete analytic Hardy gauges with normalized angular measure; finite positive p have nontangential limits, exact norm and radial Lp convergence. Infinity has nontangential limits and its norm identity, without a false L-infinity radial-convergence assertion.
- **42.7 Canonical factorization** — partial; [CKMA.Analysis.Complex.Hardy](CKMA/Analysis/Complex/Hardy.lean). Canonical factorization existence with actual Blaschke products, finite singular angular measures, outer integrals, and a unimodular phase. Uniqueness up to the appropriate phases remains.
- **42.20 Carleson embedding theorem** — statement; [CKMA.Analysis.Complex.CarlesonInterpolation](CKMA/Analysis/Complex/CarlesonInterpolation.lean). Finite measures supported in the disk, explicit normalized-arc Carleson boxes, and every positive finite Hardy exponent.
- **42.24 Carleson interpolation theorem** — statement; [CKMA.Analysis.Complex.CarlesonInterpolation](CKMA/Analysis/Complex/CarlesonInterpolation.lean). Distinct disk sequences; separation products are infima of finite nonnegative products, avoiding arbitrary infinite-product junk values. Interpolation uses a common norm bound for data of sup norm at most one.
- **42.26 Nevanlinna–Pick theorem** — statement; [CKMA.Analysis.Complex.CarlesonInterpolation](CKMA/Analysis/Complex/CarlesonInterpolation.lean). Complex positive-semidefinite Pick matrices; arbitrary finite data, including the empty index type and target values on the unit circle.
- **42.27 Corona theorem** — statement; [CKMA.Analysis.Complex.CarlesonInterpolation](CKMA/Analysis/Complex/CarlesonInterpolation.lean). Nonempty finite families with uniform bound M and positive corona lower bound delta; solution bounds depend only on n, delta and M.
- **42.51 Bergman kernel** — partial; [CKMA.Analysis.Complex.Bergman](CKMA/Analysis/Complex/Bergman.lean). Normalized weighted measure, principal-power kernel, reproduction, monomial norms and closed holomorphic L2 carrier. Orthonormal-basis and coefficient-completeness interfaces remain.
- **42.52 Bergman projection** — partial; [CKMA.Analysis.Complex.Bergman](CKMA/Analysis/Complex/Bergman.lean). L2 orthogonal projection with integral kernel and all-p boundedness estimate targets. The all-p analytic range/surjectivity interface remains. The all-p estimate is not a GAPS_EASY consequence.
- **42.82 Fock sampling density** — statement; [CKMA.Analysis.Complex.Fock](CKMA/Analysis/Complex/Fock.lean). Entire Gaussian-square-integrable functions; uniformly separated planar node sets, extended counting and lower uniform density, with the sharp strict sampling threshold alpha/pi.
- **43.1 Grönwall area theorem** — statement; [CKMA.Analysis.Complex.Univalent](CKMA/Analysis/Complex/Univalent.lean). Exterior schlicht functions normalized at infinity, actual contour-defined Laurent coefficients, nonnegative coefficient energy and the omitted Lebesgue area.
- **43.3 Koebe quarter theorem** — statement; [CKMA.Analysis.Complex.Univalent](CKMA/Analysis/Complex/Univalent.lean). Normalized analytic schlicht functions on the disk; sharpness witnessed by the explicit Koebe function.
- **43.5 Distortion theorem** — statement; [CKMA.Analysis.Complex.Univalent](CKMA/Analysis/Complex/Univalent.lean).
- **43.8 de Branges's theorem** — statement; [CKMA.Analysis.Complex.Univalent](CKMA/Analysis/Complex/Univalent.lean). Every coefficient n>=2 and rigidity at any equality coefficient, with equality to a Koebe rotation on the disk.
- **43.21 Loewner–Kufarev equation** — statement; [CKMA.Analysis.Complex.Univalent](CKMA/Analysis/Complex/Univalent.lean). Concrete radial chains with nested images and local time absolute continuity uniform on compact subdisks; a measurable normalized Herglotz field and a common almost-everywhere time set.
- **43.31 Nehari sufficient bound** — partial; [CKMA.Analysis.Complex.Univalent](CKMA/Analysis/Complex/Univalent.lean). Locally univalent holomorphic disk functions and the exact Schwarzian bound two. The meromorphic spherical formulation remains.
- **44.38 Measurable Riemann mapping theorem** — statement; [CKMA.Analysis.ComplexGeometry.Beltrami](CKMA/Analysis/ComplexGeometry/Beltrami.lean). Weak W^(1,2)-local Beltrami solutions among plane homeomorphisms, normalized at zero and one; a plane homeomorphism fixes infinity on one-point compactification. The quasiconformal constant is (1+k)/(1-k).
- **44.49 Astala area distortion** — partial; [CKMA.Analysis.ComplexGeometry.Beltrami](CKMA/Analysis/ComplexGeometry/Beltrami.lean). Disk self-maps fixing zero that are restrictions of plane homeomorphisms, with the 1/K area exponent. Exponent optimality and a standalone disk-homeomorphism API remain.
- **45.1 Hartogs separate analyticity** — statement; [CKMA.Analysis.ComplexGeometry.HartogsWeierstrass](CKMA/Analysis/ComplexGeometry/HartogsWeierstrass.lean). Separate coordinate holomorphy on open subsets of finite complex coordinate spaces, without assumed continuity; includes zero-dimensional spaces.
- **45.2 Polydisk Taylor expansion and estimates** — partial; [CKMA.Analysis.Complex.Polydisc](CKMA/Analysis/Complex/Polydisc.lean). Unequal-polyradius normal series, contour coefficients, coefficient Cauchy estimates, and the Weierstrass theorem are proved. The mixed-derivative/coefficient identity remains.
- **45.5 Hartogs extension** — statement; [CKMA.Analysis.ComplexGeometry.HartogsWeierstrass](CKMA/Analysis/ComplexGeometry/HartogsWeierstrass.lean). Compact holes in connected domains of dimension at least two, with connected complement. Uniqueness is equality on the domain rather than equality of arbitrary global extensions.
- **45.7 Weierstrass preparation** — statement; [CKMA.Analysis.ComplexGeometry.HartogsWeierstrass](CKMA/Analysis/ComplexGeometry/HartogsWeierstrass.lean). Convergent complex germs on a product of base coordinates and one final coordinate, finite final-coordinate order, monic distinguished polynomial and holomorphic unit. Uniqueness is germ equality; degree zero is allowed.
- **45.8 Weierstrass division** — statement; [CKMA.Analysis.ComplexGeometry.HartogsWeierstrass](CKMA/Analysis/ComplexGeometry/HartogsWeierstrass.lean). Analytic quotient and polynomial remainder germs for concrete distinguished coefficients, with unique germ data and degree-zero edge case.
- **45.20 Oka–Weil approximation** — partial; [CKMA.Analysis.ComplexGeometry.HartogsWeierstrass](CKMA/Analysis/ComplexGeometry/HartogsWeierstrass.lean). Polynomially convex compact subsets of affine C^n, actual multivariate polynomial hulls and polynomial approximants. General Stein manifolds remain.
- **46.6 Repelling cycles are dense** — partial; [CKMA.Dynamics.Complex.PolynomialJulia](CKMA/Dynamics/Complex/PolynomialJulia.lean). Polynomial maps of degree at least two, with Julia set defined as the boundary of the bounded-orbit filled set. General rational maps and the normal-family identification remain.
- **46.10 Koenigs linearization** — proved; [CKMA.Dynamics.Complex.Linearization](CKMA/Dynamics/Complex/Linearization.lean). Coordinates are germs of analytic maps at a fixed point; uniqueness is eventual equality, with nonzero multiplier of norm different from one.
- **46.11 Böttcher's theorem** — proved; [CKMA.Dynamics.Complex.Linearization](CKMA/Dynamics/Complex/Linearization.lean). Exact order is expressed by f=z^k*g near zero, with g analytic and g(0) nonzero; the prescribed derivative c satisfies c^(k-1)=g(0).
- **46.29 Connectedness criterion** — statement; [CKMA.Dynamics.Complex.PolynomialJulia](CKMA/Dynamics/Complex/PolynomialJulia.lean). Filled and boundary Julia connectedness and boundedness of all finite critical orbits. Actual orbit, escape-rate and filled-set definitions and supporting targets are included.
- **46.40 Mandelbrot connectedness** — statement; [CKMA.Dynamics.Complex.PolynomialJulia](CKMA/Dynamics/Complex/PolynomialJulia.lean). Quadratic critical-orbit definition, compactness, connectedness, closed radius-two escape bound and equivalence with Julia connectedness.
- **46.58 Eremenko escaping theorem** — partial; [CKMA.Dynamics.Complex.PolynomialJulia](CKMA/Dynamics/Complex/PolynomialJulia.lean). Transcendental entire maps: nonempty escaping set and unboundedness of every connected component of its closure. The boundary-equals-nonnormality-Julia assertion remains.
- **47.6 Chebyshev alternation theorem** — partial; [CKMA.Analysis.Approximation.Polynomial](CKMA/Analysis/Approximation/Polynomial.lean). Uniform polynomial approximation on [-1,1], including existence/uniqueness and alternation; the generalized Haar-space criterion remains.
- **47.13 Müntz–Szász theorem** — statement; [CKMA.Analysis.Approximation.Polynomial](CKMA/Analysis/Approximation/Polynomial.lean). Real continuous functions on [0,1]; the span includes one and positive real powers. The reciprocal divergence is expressed as nonsummability.
- **47.17 Korovkin theorem** — proved; [CKMA.Analysis.Approximation.Korovkin](CKMA/Analysis/Approximation/Korovkin.lean). Real continuous functions on [0,1]; the complex-linear extension by components is not separately stated.
- **47.20 Jackson's trigonometric theorem** — partial; [CKMA.Analysis.Approximation.Trigonometric](CKMA/Analysis/Approximation/Trigonometric.lean). Concrete angular trigonometric polynomials, extended Lp errors and moduli for 1<=p<=infinity; this interface assumes continuous periodic representatives even at finite p. Extension to all periodic Lp classes remains.
- **47.21 Inverse trigonometric estimate** — partial; [CKMA.Analysis.Approximation.Trigonometric](CKMA/Analysis/Approximation/Trigonometric.lean). Inverse smoothness estimate with constants uniform in 1<=p<=infinity, currently on continuous periodic functions. The general finite-p Lp interface remains.
- **47.23 Bernstein derivative inequality** — statement; [CKMA.Analysis.Approximation.Trigonometric](CKMA/Analysis/Approximation/Trigonometric.lean). All derivative orders and degrees, including constants and order zero, with period 2*pi and angular frequencies exp(ikx).
- **47.24 Markov inequality** — statement; [CKMA.Analysis.Approximation.Polynomial](CKMA/Analysis/Approximation/Polynomial.lean). Full [-1,1] bound including interior points, plus attainment of the n^2 constant.
- **47.35 Chebyshev interpolation stability** — proved; [CKMA.Analysis.Approximation.InterpolationStability](CKMA/Analysis/Approximation/InterpolationStability.lean). Chebyshev-extrema Lebesgue constants and the general Lebesgue near-best interpolation inequality; log(n+1) includes degree zero.
- **47.40 Newman's theorem** — statement; [CKMA.Analysis.Approximation.Polynomial](CKMA/Analysis/Approximation/Polynomial.lean). Pole-free real type-(n,n) rational approximation to abs(x), with two-sided root-exponential rates and the corresponding polynomial rate 1/n.
- **48.4 Favard's theorem** — partial; [CKMA.Analysis.OrthogonalPolynomial.MomentExistence](CKMA/Analysis/OrthogonalPolynomial/MomentExistence.lean). Actual monic Jacobi recurrence and existence of a probability orthogonality measure with infinite support and all finite moments. The separate assertion that coefficients and total mass determine every moment remains.
- **48.6 Real and simple zeros** — proved; [CKMA.Analysis.OrthogonalPolynomial.Basic](CKMA/Analysis/OrthogonalPolynomial/Basic.lean).
- **48.14 Gauss quadrature** — partial; [CKMA.Analysis.OrthogonalPolynomial.Basic](CKMA/Analysis/OrthogonalPolynomial/Basic.lean). Positive unique weights at prescribed distinct roots, exactness and Christoffel formula; uniqueness with varying nodes up to permutation remains.
- **48.32 Hamburger theorem** — statement; [CKMA.Analysis.OrthogonalPolynomial.MomentExistence](CKMA/Analysis/OrthogonalPolynomial/MomentExistence.lean). All finite Hankel matrices are positive semidefinite iff a finite positive Borel measure represents every real moment. Zero mass is included.
- **48.33 Stieltjes theorem** — statement; [CKMA.Analysis.OrthogonalPolynomial.MomentExistence](CKMA/Analysis/OrthogonalPolynomial/MomentExistence.lean). Both unshifted and once-shifted Hankel positivity, with support on [0,infinity).
- **48.34 Hausdorff theorem** — proved; [CKMA.Probability.Moments.Hausdorff](CKMA/Probability/Moments/Hausdorff.lean). Finite measures, including mass zero; concrete forward differences, Bernstein weights and discrete approximants.
- **48.36 Moment Carleman criteria** — statement; [CKMA.Analysis.OrthogonalPolynomial.MomentExistence](CKMA/Analysis/OrthogonalPolynomial/MomentExistence.lean). Extended-real Carleman sums include zero moments via infinite inverse powers. Uniqueness is among existing representing measures, on the correct support.
- **49.6 Gamma multiplication beyond duplication** — partial; [CKMA.Analysis.SpecialFunctions.Classical](CKMA/Analysis/SpecialFunctions/Classical.lean). The off-pole product identity is proved for every positive integer multiplier. The explicit global meromorphic-continuation identity remains.
- **49.13 Gauss equation** — proved; [CKMA.Analysis.SpecialFunctions.Classical](CKMA/Analysis/SpecialFunctions/Classical.lean). Denominator parameter avoids nonpositive integers; regular singularity allows removable/ordinary degenerate cases.
- **49.26 Second solution** — statement; [CKMA.Analysis.SpecialFunctions.BesselAiryMittagLeffler](CKMA/Analysis/SpecialFunctions/BesselAiryMittagLeffler.lean). Concrete connection formula, totalized order-limit at integers, incoming/outgoing Hankel functions and principal-slit-plane ODE/Wronskian targets. The noninteger formula is proved.
- **49.30 Bessel generating function** — proved; [CKMA.Analysis.SpecialFunctions.Classical](CKMA/Analysis/SpecialFunctions/Classical.lean).
- **49.36 Airy representation** — statement; [CKMA.Analysis.SpecialFunctions.BesselAiryMittagLeffler](CKMA/Analysis/SpecialFunctions/BesselAiryMittagLeffler.lean). Actual normalized Airy power series and truncated oscillatory real-axis integral. The improper integral is a limit, rather than a totalized Bochner integral on the half-line.
- **49.76 Mittag–Leffler entire functions** — partial; [CKMA.Analysis.SpecialFunctions.BesselAiryMittagLeffler](CKMA/Analysis/SpecialFunctions/BesselAiryMittagLeffler.lean). Concrete series, convergence, entireness and E_(1,1)=exp for positive real alpha and complex beta. The exact entire-function order 1/alpha remains.
- **50.6 Borel–Ritt theorem** — statement; [CKMA.Analysis.Asymptotics.Expansions](CKMA/Analysis/Asymptotics/Expansions.lean). Concrete rotated sectors and uniform all-order power remainders on every closed proper subsector, for opening strictly between zero and 2*pi.
- **50.9 Watson's lemma** — partial; [CKMA.Analysis.Asymptotics.Expansions](CKMA/Analysis/Asymptotics/Expansions.lean). Finite-order and full complex-amplitude Laplace expansions for positive real alpha, with explicit local integrability and exponential tail bounds. Complex alpha with positive real part remains.
- **50.11 Interior Laplace minimum** — partial; [CKMA.Analysis.Asymptotics.Expansions](CKMA/Analysis/Asymptotics/Expansions.lean). Leading one-dimensional interior-minimum Laplace asymptotic on a finite interval, with phase C2 only on that interval. A scaled limit permits zero amplitude at the minimum; higher coefficients and remainder expansions remain.
- **50.23 Euler–Maclaurin formula** — statement; [CKMA.Analysis.Asymptotics.EulerMaclaurin](CKMA/Analysis/Asymptotics/EulerMaclaurin.lean). Positive truncation order p; globally C^(2p) real functions; integer endpoints m ≤ n, including equality. The displayed remainder is false at p=0, which is excluded.
- **50.29 Karamata Tauberian theorem** — statement; [CKMA.Analysis.Asymptotics.Expansions](CKMA/Analysis/Asymptotics/Expansions.lean). Locally finite positive measures supported on the nonnegative half-line, all positive Laplace transforms integrable, and measurable slowly varying functions. Includes rho=0.
- **50.45 Borel–Laplace theorem** — statement; [CKMA.Analysis.Asymptotics.BorelLaplace](CKMA/Analysis/Asymptotics/BorelLaplace.lean). Actual formal Borel series, directional Laplace integral, analytic continuation of opening β with exponential growth, uniform Gevrey-one estimates, and a holomorphic sum on the sector of opening π+β. Agreement with the original ray holds on the convergence sector of opening π.
