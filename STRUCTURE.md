# Core knowledge in mathematical analysis: Mathlib and TauCeti coverage

The fifty files `STRUCTURE04.md`–`STRUCTURE53.md` describe relevant definitions,
structures, and proved results in Mathlib and TauCeti. Their topical order follows
the corresponding [mathematical synopses](SYNOPSIS.md) and the current
[bibliography](CKMA-bib.md), including the lettered subdivisions. The
[MSC2020 index](CKMA-MSC2020.md) supplies classification and cross-area routes.

Each inventory distinguishes Mathlib from TauCeti within a mathematical topic.
It retains concrete source locations, declaration names, hypotheses, and scope
qualifications. Supporting constructions are identified as such: an abstract
evolution theorem requires a suitable generator, a scalar spectral measure is
a different object from a projection-valued spectral resolution, and a theorem
about an existing EVI solution does not supply its existence. Definitions and
unproved conjecture statements, where retained for orientation, are explicitly
labelled. Placement under a synopsis heading does not claim that every numbered
result under that heading is formalized.

These files are self-contained coverage inventories, and they supersede the
earlier per-section `MathlibNN.md` notes. Each section corresponds to one
heading of the synopsis and ends with a **Synopsis entries** line that sorts
every numbered entry under that heading into *covered* (the result as stated,
with its hypotheses, is proved in Mathlib or TauCeti, possibly in an equivalent
formulation), *partly covered* (with a note on what is present), or *not
covered*. The separate [gap inventory](GAPS.md) selects the principal missing
results and assesses them. Other numbered sections provide additional detail
about shared foundations; these are linked where useful.

## Source baseline and conventions

The coverage statements were checked on **2026-10-19** against local checkouts
of the following revisions, both of 2026-10-18:

- **Mathlib:** commit
  [`911003dd6dea5df215dff57f2717be762e11a6ca`](https://github.com/leanprover-community/mathlib4/tree/911003dd6dea5df215dff57f2717be762e11a6ca),
  using Lean `v4.36.0-rc1`.
- **TauCeti:** commit
  [`5cdecf40e99d5a5ad0833afff31f5b007d68a149`](https://github.com/TauCetiProject/TauCeti/tree/5cdecf40e99d5a5ad0833afff31f5b007d68a149).

These are the revisions against which [GAPS.md](GAPS.md) was reviewed. The
check was by source inspection: cited files and declarations were located and
their hypotheses compared with the synopsis statements. A TauCeti result is
recorded as proved only when the cited declaration does not rely on `sorry`,
`admit`, or an added axiom, as far as can be seen in its source. No build or
axiom-dependency check was run for this revision. The earlier inventories were
audited against Mathlib `f039e1b8a616d45782a5c7fc5e7909249c36b8ea` and TauCeti
`6ebb29f84b4d6e2019233da0718776a6e32e1526`.

Mathlib paths such as `Analysis/ODE/PicardLindelof.lean` are relative to
[`Mathlib/` at the recorded revision](https://github.com/leanprover-community/mathlib4/tree/911003dd6dea5df215dff57f2717be762e11a6ca/Mathlib).
`Mathlib/Probability/...` includes that prefix explicitly. `Archive/` and
`Wanted/` are relative to the repository root. Short filenames in a paragraph
refer to the directory identified there. A source file `Mathlib/A/B/C.lean`
is imported as `import Mathlib.A.B.C`; dotted source-area names can also denote
directory prefixes, so the individual `.lean` files cited in the entries are
the precise import entry points. Deprecated module names, where mentioned,
identify compatibility exports rather than separate theories.

TauCeti source links are pinned to its recorded commit. A file
`TauCeti/A/B/C.lean` is imported as `import TauCeti.A.B.C` in the matching
dependency environment. Declaration names and namespaces provide search terms;
the full hypotheses of the cited declaration govern reuse. A human-readable
summary is not a replacement for checking those hypotheses in Lean.

## Topical inventories

- [04. Real analysis, measure, and integration](STRUCTURE04.md)
- [05. Differentiation and the fine structure of real functions](STRUCTURE05.md)
- [06. Probability: foundations and limit theory](STRUCTURE06.md) — 06A–D
- [07. Concentration, high-dimensional probability, and random matrices](STRUCTURE07.md) — 07A–B
- [08. Stochastic processes, stochastic calculus, and control](STRUCTURE08.md) — 08A–C
- [09. Malliavin calculus, rough paths, and stochastic PDE](STRUCTURE09.md) — 09A–C
- [10. Ergodic theory and measurable dynamics](STRUCTURE10.md)
- [11. Classical inequalities, means, majorization, and rearrangement](STRUCTURE11.md)
- [12. Convexity, convex analysis, optimization, and variational analysis](STRUCTURE12.md)
- [13. Matrix analysis and noncommutative inequalities](STRUCTURE13.md)
- [14. Functional, isoperimetric, and geometric inequalities](STRUCTURE14.md)
- [15. Core Banach and Hilbert space theory](STRUCTURE15.md)
- [16. Locally convex spaces, duality, and distributions](STRUCTURE16.md)
- [17. Banach space geometry, bases, and operator ideals](STRUCTURE17.md)
- [18. Vector-valued analysis and analysis in Banach spaces](STRUCTURE18.md)
- [19. Banach lattices, positive operators, and ordered structures](STRUCTURE19.md)
- [20. Banach algebras](STRUCTURE20.md)
- [21. Bounded operators, spectra, and model theory](STRUCTURE21.md)
- [22. Unbounded operators, spectral theory, and mathematical physics](STRUCTURE22.md)
- [23. Operator algebras, operator spaces, free probability, and noncommutative geometry](STRUCTURE23.md)
- [24. Semigroups, evolution equations, and functional calculus](STRUCTURE24.md)
- [25. Integral equations and classical operator methods](STRUCTURE25.md)
- [26. Sobolev spaces, smoothness scales, and interpolation](STRUCTURE26.md)
- [27. Fourier analysis and real-variable harmonic analysis](STRUCTURE27.md)
- [28. Abstract harmonic analysis on groups](STRUCTURE28.md)
- [29. Wavelets, frames, time–frequency analysis, and sampling](STRUCTURE29.md)
- [30. Distributions, pseudodifferential operators, microlocal and semiclassical analysis](STRUCTURE30.md)
- [31. Ordinary differential equations and dynamical systems](STRUCTURE31.md)
- [32. Partial differential equations: general and linear theory](STRUCTURE32.md)
- [33. Elliptic and parabolic equations](STRUCTURE33.md)
- [34. Hyperbolic equations, dispersive PDE, fluids, and kinetic theory](STRUCTURE34.md) — 34A–D
- [35. Nonlinear functional analysis, monotone operators, and fixed points](STRUCTURE35.md)
- [36. Calculus of variations, Γ-convergence, and homogenization](STRUCTURE36.md)
- [37. Geometric measure theory, BV, rectifiability, and currents](STRUCTURE37.md)
- [38. Potential theory and capacity](STRUCTURE38.md)
- [39. Metric measure spaces, Dirichlet forms, optimal transport, and fractals](STRUCTURE39.md) — 39A–C
- [40. One complex variable: general theory](STRUCTURE40.md)
- [41. Entire and meromorphic functions and value distribution](STRUCTURE41.md)
- [42. Hardy, Bergman, and model spaces](STRUCTURE42.md)
- [43. Univalent functions, conformal mapping, and extremal methods](STRUCTURE43.md)
- [44. Riemann surfaces, quasiconformal mappings, and Teichmüller theory](STRUCTURE44.md)
- [45. Several complex variables, complex manifolds, pluripotential theory, and CR analysis](STRUCTURE45.md) — 45A–D
- [46. Complex dynamics](STRUCTURE46.md)
- [47. Approximation theory](STRUCTURE47.md)
- [48. Orthogonal polynomials, moment problems, and spectral recurrences](STRUCTURE48.md)
- [49. Special functions, integral transforms, and classical formulae](STRUCTURE49.md)
- [50. Asymptotic analysis, resurgence, and perturbation](STRUCTURE50.md)
- [51. Integrable systems and Riemann–Hilbert methods](STRUCTURE51.md)
- [52. Geometric analysis on manifolds](STRUCTURE52.md)
- [53. Elliptic operators on manifolds, index theory, and spectral geometry](STRUCTURE53.md)
