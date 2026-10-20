# Core Knowledge of Mathematical Analysis

This project describes the core knowledge of mathematical analysis at the
level of graduate students and beginning researchers. It compares that core
with the results proved in the Lean libraries Mathlib and TauCeti. The
subject is organized by the [bibliography](CKMA-bib.md), whose topical
sections are numbered 1–55; the mathematical descriptions and the library
comparison cover the fifty areas 04–53.

## Main documents

- [SYNOPSIS.md](SYNOPSIS.md) is the index of the synopses. Each
  `SYNOPSISdd.md` describes the definitions, conventions and principal
  theorems of area `dd` in numbered entries. Entry `dd.k` is result `k` of
  `SYNOPSISdd.md`, and these identifiers are stable.
- [STRUCTURE.md](STRUCTURE.md) is the index of the coverage inventories. It
  records the Mathlib and TauCeti revisions used. Each `STRUCTUREdd.md`
  records the coverage in Mathlib and TauCeti of the entries of
  `SYNOPSISdd.md`, with declarations, source locations and hypotheses, and
  classifies each entry as covered, partly covered or not covered.
- [GAPS.md](GAPS.md) selects the principal theorems of the synopses that
  neither library proves and assesses them area by area.
- [GAPS_EASY.md](GAPS_EASY.md) gives short derivations from library
  results for those entries of `GAPS.md` that have one.

Supporting files:

- [CKMA-MSC2020.md](CKMA-MSC2020.md), the MSC2020 and cross-subject index
  for the bibliography.
- [MathlibCoverage.md](MathlibCoverage.md) and
  [TauCetiCoverage.md](TauCetiCoverage.md), section-by-section summaries of
  each library's coverage.

## Synopses and coverage inventories by area

| Area | Subject | Synopsis | Coverage |
|---|---|---|---|
| 04 | Real analysis, measure, and integration | [SYNOPSIS04.md](SYNOPSIS04.md) | [STRUCTURE04.md](STRUCTURE04.md) |
| 05 | Differentiation and the fine structure of real functions | [SYNOPSIS05.md](SYNOPSIS05.md) | [STRUCTURE05.md](STRUCTURE05.md) |
| 06 | Probability: measure-theoretic foundations and limit theory | [SYNOPSIS06.md](SYNOPSIS06.md) | [STRUCTURE06.md](STRUCTURE06.md) |
| 07 | Concentration, high-dimensional probability, and empirical processes | [SYNOPSIS07.md](SYNOPSIS07.md) | [STRUCTURE07.md](STRUCTURE07.md) |
| 08 | Stochastic processes, martingales, and stochastic calculus | [SYNOPSIS08.md](SYNOPSIS08.md) | [STRUCTURE08.md](STRUCTURE08.md) |
| 09 | Malliavin calculus, rough paths, and stochastic partial differential equations | [SYNOPSIS09.md](SYNOPSIS09.md) | [STRUCTURE09.md](STRUCTURE09.md) |
| 10 | Ergodic theory and measurable dynamics | [SYNOPSIS10.md](SYNOPSIS10.md) | [STRUCTURE10.md](STRUCTURE10.md) |
| 11 | Classical inequalities, means, majorization, and rearrangement | [SYNOPSIS11.md](SYNOPSIS11.md) | [STRUCTURE11.md](STRUCTURE11.md) |
| 12 | Convexity, convex analysis, optimization, and variational analysis | [SYNOPSIS12.md](SYNOPSIS12.md) | [STRUCTURE12.md](STRUCTURE12.md) |
| 13 | Matrix analysis, operator monotonicity, and noncommutative inequalities | [SYNOPSIS13.md](SYNOPSIS13.md) | [STRUCTURE13.md](STRUCTURE13.md) |
| 14 | Functional, isoperimetric, and geometric inequalities | [SYNOPSIS14.md](SYNOPSIS14.md) | [STRUCTURE14.md](STRUCTURE14.md) |
| 15 | Core Banach and Hilbert space theory | [SYNOPSIS15.md](SYNOPSIS15.md) | [STRUCTURE15.md](STRUCTURE15.md) |
| 16 | Locally convex spaces, duality, and distributions | [SYNOPSIS16.md](SYNOPSIS16.md) | [STRUCTURE16.md](STRUCTURE16.md) |
| 17 | Banach space geometry, bases, and operator ideals | [SYNOPSIS17.md](SYNOPSIS17.md) | [STRUCTURE17.md](STRUCTURE17.md) |
| 18 | Vector-valued analysis and analysis in Banach spaces | [SYNOPSIS18.md](SYNOPSIS18.md) | [STRUCTURE18.md](STRUCTURE18.md) |
| 19 | Banach lattices, positive operators, and ordered structures | [SYNOPSIS19.md](SYNOPSIS19.md) | [STRUCTURE19.md](STRUCTURE19.md) |
| 20 | Banach algebras | [SYNOPSIS20.md](SYNOPSIS20.md) | [STRUCTURE20.md](STRUCTURE20.md) |
| 21 | Bounded operator theory, spectra, and functional models | [SYNOPSIS21.md](SYNOPSIS21.md) | [STRUCTURE21.md](STRUCTURE21.md) |
| 22 | Unbounded operators, spectral theory, and mathematical physics | [SYNOPSIS22.md](SYNOPSIS22.md) | [STRUCTURE22.md](STRUCTURE22.md) |
| 23 | Operator algebras, operator spaces, free probability, and noncommutative geometry | [SYNOPSIS23.md](SYNOPSIS23.md) | [STRUCTURE23.md](STRUCTURE23.md) |
| 24 | Semigroups, evolution equations, and functional calculus | [SYNOPSIS24.md](SYNOPSIS24.md) | [STRUCTURE24.md](STRUCTURE24.md) |
| 25 | Integral equations and classical operator methods | [SYNOPSIS25.md](SYNOPSIS25.md) | [STRUCTURE25.md](STRUCTURE25.md) |
| 26 | Sobolev spaces, smoothness scales, and interpolation | [SYNOPSIS26.md](SYNOPSIS26.md) | [STRUCTURE26.md](STRUCTURE26.md) |
| 27 | Fourier analysis and real-variable harmonic analysis | [SYNOPSIS27.md](SYNOPSIS27.md) | [STRUCTURE27.md](STRUCTURE27.md) |
| 28 | Abstract harmonic analysis on groups | [SYNOPSIS28.md](SYNOPSIS28.md) | [STRUCTURE28.md](STRUCTURE28.md) |
| 29 | Wavelets, frames, time–frequency analysis, and sampling | [SYNOPSIS29.md](SYNOPSIS29.md) | [STRUCTURE29.md](STRUCTURE29.md) |
| 30 | Distributions, pseudodifferential operators, microlocal and semiclassical analysis | [SYNOPSIS30.md](SYNOPSIS30.md) | [STRUCTURE30.md](STRUCTURE30.md) |
| 31 | Ordinary differential equations and dynamical systems | [SYNOPSIS31.md](SYNOPSIS31.md) | [STRUCTURE31.md](STRUCTURE31.md) |
| 32 | Partial differential equations — general and linear theory | [SYNOPSIS32.md](SYNOPSIS32.md) | [STRUCTURE32.md](STRUCTURE32.md) |
| 33 | Elliptic and parabolic equations — regularity, free boundaries, and viscosity solutions | [SYNOPSIS33.md](SYNOPSIS33.md) | [STRUCTURE33.md](STRUCTURE33.md) |
| 34 | Hyperbolic equations, conservation laws, dispersive PDE, fluids, and kinetic theory | [SYNOPSIS34.md](SYNOPSIS34.md) | [STRUCTURE34.md](STRUCTURE34.md) |
| 35 | Nonlinear functional analysis, monotone operators, and fixed points | [SYNOPSIS35.md](SYNOPSIS35.md) | [STRUCTURE35.md](STRUCTURE35.md) |
| 36 | Calculus of variations, Γ-convergence, and homogenization | [SYNOPSIS36.md](SYNOPSIS36.md) | [STRUCTURE36.md](STRUCTURE36.md) |
| 37 | Geometric measure theory, BV, rectifiability, and currents | [SYNOPSIS37.md](SYNOPSIS37.md) | [STRUCTURE37.md](STRUCTURE37.md) |
| 38 | Potential theory and capacity | [SYNOPSIS38.md](SYNOPSIS38.md) | [STRUCTURE38.md](STRUCTURE38.md) |
| 39 | Metric measure spaces, Dirichlet forms, heat kernels, optimal transport, and fractals | [SYNOPSIS39.md](SYNOPSIS39.md) | [STRUCTURE39.md](STRUCTURE39.md) |
| 40 | One complex variable — general theory | [SYNOPSIS40.md](SYNOPSIS40.md) | [STRUCTURE40.md](STRUCTURE40.md) |
| 41 | Classical function theory — entire and meromorphic functions, value distribution | [SYNOPSIS41.md](SYNOPSIS41.md) | [STRUCTURE41.md](STRUCTURE41.md) |
| 42 | Hardy, Bergman, and model spaces; operators on analytic function spaces | [SYNOPSIS42.md](SYNOPSIS42.md) | [STRUCTURE42.md](STRUCTURE42.md) |
| 43 | Univalent functions, conformal mapping, and extremal methods | [SYNOPSIS43.md](SYNOPSIS43.md) | [STRUCTURE43.md](STRUCTURE43.md) |
| 44 | Riemann surfaces, quasiconformal mappings, and Teichmüller theory | [SYNOPSIS44.md](SYNOPSIS44.md) | [STRUCTURE44.md](STRUCTURE44.md) |
| 45 | Several complex variables, complex manifolds, pluripotential theory, and CR analysis | [SYNOPSIS45.md](SYNOPSIS45.md) | [STRUCTURE45.md](STRUCTURE45.md) |
| 46 | Complex dynamics | [SYNOPSIS46.md](SYNOPSIS46.md) | [STRUCTURE46.md](STRUCTURE46.md) |
| 47 | Approximation theory | [SYNOPSIS47.md](SYNOPSIS47.md) | [STRUCTURE47.md](STRUCTURE47.md) |
| 48 | Orthogonal polynomials, moment problems, and spectral recurrences | [SYNOPSIS48.md](SYNOPSIS48.md) | [STRUCTURE48.md](STRUCTURE48.md) |
| 49 | Special functions, integral transforms, and classical formulae | [SYNOPSIS49.md](SYNOPSIS49.md) | [STRUCTURE49.md](STRUCTURE49.md) |
| 50 | Asymptotic analysis, resurgence, and perturbation | [SYNOPSIS50.md](SYNOPSIS50.md) | [STRUCTURE50.md](STRUCTURE50.md) |
| 51 | Integrable systems and Riemann–Hilbert methods | [SYNOPSIS51.md](SYNOPSIS51.md) | [STRUCTURE51.md](STRUCTURE51.md) |
| 52 | Geometric analysis on manifolds | [SYNOPSIS52.md](SYNOPSIS52.md) | [STRUCTURE52.md](STRUCTURE52.md) |
| 53 | Elliptic operators on manifolds, index theory, and spectral geometry | [SYNOPSIS53.md](SYNOPSIS53.md) | [STRUCTURE53.md](STRUCTURE53.md) |
