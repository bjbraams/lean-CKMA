# lean-CKMA code review — 28 November 2026

This review covers the Lean library `CKMA/` at commit fd4e137: 294 modules and the root
`CKMA.lean`, about 117,000 lines, about 115 admitted theorems. It applies the owner's twelve
criteria and the shared rules (`../lean-codes/AGENTS.common.md`). It was done read only: no source
was edited and nothing was built. Statements were tested in scratch files elaborated against the
current oleans, and numerically in Python.

The detailed findings, with `file:line` references, the checks run and the concrete fixes, are in
eight parts. They are kept outside this repository, in
`/ufs/braams/TauCetiRoadmap/scratch_ckma/code-review/`:

- `part1.md`: Analysis/Real, Inequalities, BoundedVariation, Measure, MeasureTheory, Asymptotics,
  Interpolation (37 files, 14,582 lines, 3 admissions).
- `part2.md`: Analysis/Operator, BanachAlgebra, CStarAlgebra, FunctionalAnalysis, BanachSpace,
  InnerProductSpace (42 files, about 15,600 lines, 10 admissions).
- `part3.md`: Analysis/Fourier, Sobolev, Microlocal, PDE (39 files, about 14,300 lines, 35).
- `part4.md`: Analysis/Complex, SpecialFunctions, OrthogonalPolynomial, ComplexGeometry,
  Potential, Approximation (49 files, 14,433 lines, 49).
- `part5.md`: Analysis/OrderedSpace, Convex, Variational, Nonlinear (32 files, 14,464 lines, 1).
- `part6.md`: Analysis/Semigroup, RoughPath, IntegralEquation, ODE, and the five entry modules
  (20 files and the entry modules, 12,052 lines, 8).
- `part7.md`: Dynamics, Probability/BrownianTheory, Probability/BrownianQuadraticVariation
  (43 files, 16,894 lines, 6).
- `part8.md`: the rest of Probability (36 files, 14,492 lines, 2).

Finding IDs are `<part>-<kind><n>`: G generality, H hypotheses, N names, D documentation, S
namespaces, modules and organization, P proofs, reuse and repetition. Each finding says whether it
was verified in Lean, verified numerically, or judged by reading. The scratch files are in `work/`
beside the parts.

## Method

Per part: `#lint only docBlame unusedArguments synTaut simpNF`, `#print axioms` on the main
theorems, `#min_imports` on samples, scripted inventories (docstrings, line lengths, file lengths,
`@[expose]`, imports, names, long proofs), small-case tests of the admitted statements and of
suspicious hypotheses, and greps of Mathlib and TauCeti at the project pins. Several TauCeti
modules that the reuse findings point to have no oleans in the shared build (among them the
asymptotic-expansion, interpolation-space, BV-space, uncentred maximal function, Mehler, large
deviations, GNS, Gamma multiplication, ordinary hypergeometric, polynomial hull and Bergman
modules). Those comparisons were made by reading the TauCeti source or against verbatim local
copies; adopting the modules means building them.

## Answers to the questions

**Most general appropriate setting?** Mostly adequate, with recurring narrowness:

- Results fixed to `EuclideanSpace ℝ (Fin d)` that hold on any finite-dimensional inner product
  space (3-G).
- ℂ-valued or sequential forms where the standard ones are vector-valued or filter-based: Laurent,
  the locally uniform limit theorem, Mittag-Leffler with polynomial principal parts, Korovkin on
  `[0, 1]` (4-G1–G5).
- Scalar-only Volterra equations and Riemann–Liouville integrals (6-G1, 6-G2); Crandall–Liggett
  convergence only on the graph domain (6-G3).
- Lindeberg–Feller restricted to `Fin (k n)` rows on one probability space (8-G1).
- The measure-preserving change of variables needs only a.e. measurability and a normed target
  (7-G1).
- KLMN and closed forms cannot express positive lower bounds (part 2).

**Hypotheses appropriate?** No statement in the library was found false, and no admitted
statement is vacuous; every degenerate case tried already carries the hypothesis its junk value
needs. One definition is wrong and several hypotheses are redundant or too strong:

- 6-H1: `IsSturmLiouvilleSolutionOn` imposes the equation at the endpoints with the two-sided
  `deriv`, so it depends on the extension outside the interval (`cosh` extended by `1` solves
  `-v'' + v = 0` on `[0, 1]` but fails the predicate at `0`). Use `derivWithin` or the interior.
- 5-H1: `integral_firstVariation_eq_zero` is `IsLocalMin.hasDerivAt_eq_zero` renamed; its `hdiff`
  hypothesis assumes the differentiation under the integral that is the content of the result.
- 1-H2, 1-P3: `bv_coarea` holds from `IntegrableOn` alone (Lean).
- 4-P1: the Gauss multiplication formula holds for every `s : ℂ`; the nonpolar hypothesis is
  redundant. 4-H1: `hadamard_factorization` needs only an upper bound on the order. 4-H2: `hc` is
  redundant in `gauss_regularized_hypergeometric_ode`.
- 1-H1: Newton's inequality needs neither nonnegativity nor `k < n` (Python, about 100,000 cases).
  1-H3: the real interpolation bound needs only `q ≠ 0`.
- 5-H2: Karamata's `hx` is redundant and survives only through `And.intro ?_ hx` (Lean). 5-H3: the
  primal value `≠ ⊤` in Fenchel–Rockafellar is redundant (Lean). 5-H5: `[CompleteSpace E]` follows
  from reflexivity in the variational-inequality and Browder–Minty theorems.
- 6-H2: the collectively compact theorems use only injectivity of `1 - T`, not invertibility.
- 7-H1: `2 ≤ k` is redundant in Furstenberg's theorem; 7-H2: `hf_meas` in `Maximal.lean`.
- Part 2: redundant completeness in Dvoretzky and Rosenthal, redundant `0 ≤ C` in Pietsch, junk
  integrals possible in `IsL2CompleteFamily`. Part 3: five redundant `0 < d`.
- `#lint unusedArguments`: 4 (part 3), 4 (part 4), 38 (part 2, 4 on public declarations),
  11 (part 5), 6 (part 7), 10 (part 8).

**Mathlib naming?** Capitalization and underscores are consistent. Defects: names that clash with
or shadow Mathlib (`CKMA.gauge_*`, `CKMA.abs_smul`, 5-N1, 5-N2); namespaces that imitate Mathlib's
and block dot notation (`CKMA.Integrable`, `CKMA.Lp`, `CKMA.ConvexOn`, 3-S1, 5-N2); name segments
naming definitions that do not exist (`hasLaw_ouMehler`, 8-N1; `CKMA.operatorSector_def`, 6-S1);
generic public names in `CKMA.Brownian` (`good`, `version`, `approx`, `grid`, `past`, 7-N1); a
misnamed namespace (`CKMA.Bohr`, 1-N1) and file (`Dini/RisingSun.lean`, which is not the rising
sun lemma); five-conjunct bundles such as `polynomial_escapeRate_properties` (7-N5).

**Formal docstrings, and appropriate?** Coverage is essentially complete (`docBlame` clean in seven
parts; one public theorem without a docstring in part 2). Inaccurate or improper docstrings:

- 3-D1: the docstrings of `criticalSobolevProfile` and `logLog` say `Real.log` of a negative
  number is `0`; `Real.log` is even (Lean).
- 6-D1: the `YoungData` field docstrings swap integrand and integrator.
- 4-D1: 15 docstrings describe development status ("remains", "retained for compatibility").
- 7-D1: the module docstring of `BrownianTheory.lean` misplaces `exists_brownianMeasure`; 5-P1:
  the module docstring of `FixedPoint.lean` describes a dead construction.

**Namespaces?** Everything public is under `CKMA`, with no root-level pollution. Besides the
imitating namespaces above, part 8 finds inconsistent namespaces and about 25 public scaffolding
definitions in `InfinitelyDivisible/` (8-S5); part 6 finds private objects reachable only through
`∃` statements (the Crandall–Liggett semigroup, the Hilbert–Schmidt integral operator, 6-S2).

**Every file a module?** Yes: every file starts with `module` and uses `public section`, and no
section carries a blanket `@[expose]`. Instead about 906 definitions carry their own `@[expose]`,
so importers can unfold them (checked from importing modules in several parts). The shared rules
also ask for a defining lemma plus introduction and elimination lemmas for each definition, so
that users never depend on unfolding. Almost none exist: 105 of 109 definitions lack one in
part 1, about 94 in part 2, 110 of 126 in part 3, about 140 of 159 in part 4, about 80 in part 5,
70 of 74 in part 6, most in part 7, about 58 of 60 in part 8. This is the most widespread fix.

Imports: `public import` used only by proofs (1-S2 and others); `public import Mathlib.Tactic` or
`import Mathlib.Tactic` in `IndependentSums.lean` and five Duality files (8-S2, 5-S1); unused
imports found by `#min_imports` (1-S2, 6-S4, 3-S2); four files import
`InnerProductSpace.Basic` for `HilbertModel` alone, dragging in frames and L² measure theory
(part 2). The entry modules import all 294 modules exactly once, with no orphans (part 6).

**Module docstrings?** All files have one. Several lack a "Main results" section (seven in part 3)
or describe content no longer present (5-P1, 7-D1).

**Long proofs?** About 170 proofs exceed 80 lines (24, 14, 20, 27, 13, 20, 28, 21 per part). The
longest are `exists_log_norm_tprod_lower` (319 lines, 4-P8) and the proof of
`polynomial_escapeRate_properties` (292 lines, 7-P6). Gaussian integration by parts (97 lines)
is a library lemma (8-P6).

**Mathlib or TauCeti replacements?** This is the main finding of the review. TauCeti has grown
since most files were written, and much of the library now duplicates it:

- Interpolation spaces: all of `Analysis/Interpolation/` duplicates TauCeti's `CompatibleCouple`,
  `KMethodSpace`, `ComplexMethodSpace` and their bounds, which are more general (1-P1).
- Asymptotics: `IsAsymptoticScale` and `HasAsymptoticExpansion` duplicate TauCeti's; Watson's lemma
  then follows from `watson_laplace_remainder` (1-P2). Euler–Maclaurin re-derives
  `TauCeti.sum_Icc_eq_eulerMaclaurin` (1-P4).
- BV: `IsBVFunctionOn` is `TauCeti.MemBV`, and `bv_coarea` restates TauCeti's coarea theorem
  (1-P3).
- Operators: Atkinson's theorem has the statement of
  `TauCeti.isFredholm_iff_exists_isCompactOperator_comp_sub_one`, which is more general (2-P1);
  Weyl's inequality, the Frobenius norm and Cauchy interlacing are TauCeti's (2-P2, 2-G1); the
  faithful representation (308 lines) follows from `exists_faithful_nondegenerate_representation`
  and `NonUnitalStarAlgHom.norm_map`, at universe `u` instead of `u+1` (2-P3); Kaplansky re-proves
  TauCeti's `piLpEntry_*` lemmas; finite representability and Rademacher type and cotype
  duplicate TauCeti definitions.
- Harmonic analysis: invariant means duplicate TauCeti's amenability theory (3-P1); the Fejér
  kernel of order `N` is `TauCeti.fejerKernel (N+1)` (3-P2); the symbol classes and quantization
  rebuild TauCeti's, and the Sobolev-mapping target is `exists_quantizeUniformSobolev` (3-H3,
  3-P3); the Hilbert-transform targets overlap `rieszTransform` (3-P4); the A_p definitions
  exist twice (3-P5).
- Complex analysis and special functions: Gauss multiplication is `Complex.prod_Gamma_add_div`
  (4-P1, 559 lines); the hypergeometric ODE is
  `TauCeti.ordinaryHypergeometric_gaussEquation_of_norm_lt_one` (4-P2); three Weierstrass
  elementary factors and three slope-factor definitions, with a bound weaker than TauCeti's sharp
  one (4-P3); `laurentCoefficient` is `TauCeti.circleLaurentCoeff`, `diskHerglotzKernel` is
  `herglotzRieszKernel`, `schwarzianDerivative` is `TauCeti.schwarzian`, `complexPolynomialHull` is
  `TauCeti.polynomialHull`, and `bergmanTaylorCoeff` and `schlichtCoefficient` are the same function
  (4-P4–P6).
- Convexity and fixed points: about 215 lines of dead Schauder code duplicating
  `exists_dist_le_of_isCompact_closure_image` (5-P1); `sumInitial` is `prefixSum`;
  `IsProximalPoint` duplicates `moreauYosidaResolvent` (5-P2–P5).
- Semigroups: `Semigroup/Inhomogeneous.lean` (946 lines) duplicates TauCeti's
  `CauchyProblem/Inhomogeneous.lean` and could shrink to about 100 lines (6-P1).
- Brownian motion: `BrownianTheory.lean` duplicates TauCeti's strong Markov property, which proves
  full-path independence (7-P1); `KolmogorovMaximal.lean` and `quadraticVariation_measure_le`
  duplicate TauCeti's `PartitionMaximal` with Mathlib's Doob inequality (7-P2); Kolmogorov edge
  estimates (7-P3).
- Probability: `CKMA.convolutionPower` is TauCeti's, and all of `InfinitelyDivisible/` is built on
  the copy (8-P1); `ProjectiveLimit.lean` (289 lines) follows in four lines from Mathlib's
  `isProjectiveLimit_projectiveLimit` (8-P2); the good rate function and the LDP are TauCeti's,
  the LDP without lower semicontinuity (8-P3); `ouSemigroup` is TauCeti's `mehler` (8-P4);
  `compoundPoisson` is TauCeti's (8-P7).
- Mathlib: `lastCoordEquiv` is `piFinSuccAbove`, `max 0 (log u)` is `Real.posLog`, `OpenRectangle`
  is `BoxIntegral.Box` (1-P5); `norm_add₃_le` and `norm_add₄_le` (6-P2).
- Admissions with library proof routes: Meyers from `exists_memLp_gradient_ball_divergence`, and
  Schauder and W^{2,p} from the TauCeti `Regularity/Hessian` files (3-H1, 3-H2).

**Excessively long files?** Over the 1000-line threshold: `BanachAlgebra/Factorization.lean`
(1426, four unrelated topics, 2-S1), `Complex/EntireGrowth/Factor.lean` (1403),
`Complex/Bergman.lean` (1310), `IntegralEquation/Basic.lean` (1220),
`Semigroup/Approximation.lean` (1199) and `PDE/Wave.lean` (1040). None exceeds 1500.

**File organization?** Hub files that restate theorems under new names (Choquet, sum rule,
Fenchel, KKT, Freudenthal, AL/AM; 5-S2–S4); definitions placed in entry files so that their bodies
are spelled out as hypotheses dozens of times (`IsALSpace` about 45 times, 5-S; the subadditivity
hypothesis 34 times instead of `IsSubadditiveProcess`, 7-P4, 7-S3); the general entropy defined
in a one-dimensional proof file (8-S4); re-export shims (`Basic.lean` files in Flow, Orbit and
large deviations, 7-S1, 8-S3); misplaced files (`Combinatorics.lean` and the Rokhlin part of
`Recurrence.lean`, 7-S2); `Viscosity.lean` imports all of `EllipticEstimates` for four
definitions (3-S2).

**Repeated proof fragments?** About 300 lines of parallel instances for two hand-built sublattice
subtypes, and a projection hypothesis pair repeated about 25 times (5-P6, 5-P7); three parallel
grid constructions in the rough-path and sewing files; a rational-perturbation lemma written three
times (1-P5); Floquet invertibility proved twice (6-P3); repeated private norm lemmas (6-P2).

**Smaller defects.** A duplicate global instance `Fact (1 ≤ ∞)` that shadows Mathlib's;
`set_option warn.sorry false` hiding the finite-propagation admission (part 3); about 50
deprecated aliases in part 7 and three in part 3.

## The earlier structural assessment

The previous version of this file (12 November) is out of date. Its module count (240) and
largest file (477 lines) are wrong, and its claims of no parallel local infrastructure, no
redundant caller hypotheses, no unused arguments and no misleading extension namespaces are
refuted by the findings above. Its claims of complete docstrings, `CKMA` namespacing, line
lengths and exposed definitions hold.

## Priorities

1. Fix 6-H1 (`IsSturmLiouvilleSolutionOn`) and 5-H1 (the first-variation theorem), and correct the
   false docstring 3-D1.
2. Replace the duplicates of TauCeti and Mathlib, starting with the largest: Interpolation,
   InfinitelyDivisible, BrownianTheory and KolmogorovMaximal, Semigroup/Inhomogeneous,
   GammaMultiplication and Hypergeometric, ProjectiveLimit, the representation files, the dead
   Schauder code. This needs the TauCeti modules listed under Method to be built.
3. Add defining lemmas throughout.
4. Drop the redundant hypotheses and generalize the narrow statements.
5. Split the six long files, remove proof-only `public import`s and `Mathlib.Tactic` imports,
   move definitions out of entry files, and remove shims and deprecated aliases.
6. Correct the remaining docstrings and add main-results lists to module docstrings.

Files needing the most work: `Analysis/Interpolation/*`, `Probability/InfinitelyDivisible/*`,
`Probability/BrownianTheory.lean` with `BrownianQuadraticVariation` and `KolmogorovMaximal`,
`Analysis/Semigroup/Inhomogeneous.lean` and `Approximation.lean`, `Analysis/Complex/EntireGrowth/*`,
`Analysis/BanachAlgebra/Factorization.lean`, `Analysis/Nonlinear/FixedPoint.lean`, the AL
representation subtree in `Analysis/OrderedSpace`, `Analysis/Fourier/InvariantMean.lean`,
`Analysis/Microlocal/Symbols.lean`, and the Kingman cluster in `Dynamics/Ergodic`.
