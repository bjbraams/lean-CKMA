# Mathlib coverage of Sections 4–53

Survey of what the local Mathlib checkout already contains for Sections 4 through 53 of `CoreKnowledgeMathematicalAnalysis.md`. This file is the index for the later prose notes `Mathlib04.md` through `Mathlib53.md`. It records libraries and named theorems that were seen in source. It is not itself the prose summary.

## Pin

- Checkout: `.lake/packages/mathlib`, symlink `.lake` → `/export/scratch1/braams/lean-codes-lake`
- Commit: `065356127b1dc0016f66b7283ce0ce2c4055aa55`
- Commit date: 2026-09-16
- Toolchain: `leanprover/lean4:v4.35.0-rc2` (`chore: bump toolchain to v4.35.0-rc2`)
- The lake directory is shared and was only read.

Verdicts use three words.

- **Substantial.** A graduate core of the section is formalized. The note still lists gaps.
- **Partial.** A real cluster of definitions and theorems is formalized, and the section as a whole is not.
- **Thin.** A few neighboring ingredients exist, or none of the section’s own theorems were found.

“Absent” means no module turned up under a direct name in this pass. A later reading of a prose file can move a line if a theorem is found under an unexpected name. Status of the prose files: Sections 4–53 are **drafted** in `Mathlib04.md` through `Mathlib53.md`.

| § | Title | Verdict |
|---|---|---|
| 4 | Real analysis, measure, and integration | substantial |
| 5 | Differentiation and the fine structure of real functions | partial |
| 6 | Probability: measure-theoretic foundations and limit theory | substantial |
| 7 | Concentration, high-dimensional probability, and empirical processes | partial |
| 8 | Stochastic processes, martingales, and stochastic calculus | partial |
| 9 | Malliavin calculus, rough paths, and stochastic PDE | thin |
| 10 | Ergodic theory and measurable dynamics | partial |
| 11 | Classical inequalities, means, majorization, and rearrangement | partial |
| 12 | Convexity, convex analysis, and variational analysis | partial |
| 13 | Matrix analysis, operator monotonicity, and noncommutative inequalities | partial |
| 14 | Functional, isoperimetric, and geometric inequalities | thin |
| 15 | Core Banach and Hilbert space theory | substantial |
| 16 | Locally convex spaces, duality, and distributions | substantial |
| 17 | Banach space geometry, bases, and operator ideals | thin |
| 18 | Vector-valued analysis and analysis in Banach spaces | partial |
| 19 | Banach lattices, positive operators, and ordered structures | thin |
| 20 | Banach algebras and commutative harmonic analysis of algebras | partial |
| 21 | Operator theory: bounded operators, spectra, and model theory | partial |
| 22 | Unbounded operators, spectral theory, and mathematical physics | partial |
| 23 | Operator algebras, operator spaces, free probability, and noncommutative geometry | partial |
| 24 | Semigroups, evolution equations, and functional calculus | thin |
| 25 | Integral equations and classical operator methods | thin |
| 26 | Sobolev spaces, smoothness scales, and interpolation | partial |
| 27 | Fourier analysis and real-variable harmonic analysis | partial |
| 28 | Abstract harmonic analysis on groups | partial |
| 29 | Wavelets, frames, time–frequency analysis, and sampling | thin |
| 30 | Distributions, pseudodifferential operators, microlocal and semiclassical analysis | partial |
| 31 | Ordinary differential equations and dynamical systems | partial |
| 32 | Partial differential equations: general and linear theory | thin |
| 33 | Elliptic and parabolic equations: regularity, free boundaries, and viscosity | thin |
| 34 | Hyperbolic equations, conservation laws, dispersive PDE, fluids, and kinetic theory | thin |
| 35 | Nonlinear functional analysis, monotone operators, and fixed points | partial |
| 36 | Calculus of variations, Γ-convergence, and homogenization | thin |
| 37 | Geometric measure theory, BV, rectifiability, and currents | partial |
| 38 | Potential theory and capacity | thin |
| 39 | Metric measure spaces, Dirichlet forms, heat kernels, optimal transport, and fractals | partial |
| 40 | One complex variable | substantial |
| 41 | Entire and meromorphic functions, value distribution | partial |
| 42 | Hardy, Bergman, and model spaces; operators on analytic function spaces | thin |
| 43 | Univalent functions, conformal mapping, and extremal methods | thin |
| 44 | Riemann surfaces, quasiconformal mappings, and Teichmüller theory | thin |
| 45 | Several complex variables, complex manifolds, pluripotential theory, and CR | thin |
| 46 | Complex dynamics | thin |
| 47 | Approximation theory | partial |
| 48 | Orthogonal polynomials, moment problems, and spectral recurrences | partial |
| 49 | Special functions, integral transforms, and classical formulae | partial |
| 50 | Asymptotic analysis, resurgence, and perturbation | partial |
| 51 | Integrable systems and Riemann–Hilbert methods | thin |
| 52 | Geometric analysis on manifolds | partial |
| 53 | Elliptic operators on manifolds, index theory, and spectral geometry | thin |

## 4. Real analysis, measure, and integration

**Substantial.** `Mathlib/MeasureTheory` is a developed measure theory: measurable spaces, outer measure, content, Lebesgue measure, product measure, Bochner and Lebesgue integrals, dominated convergence, Radon–Nikodym, regularity and tightness, Riesz–Markov–Kakutani, `L^p`, simple functions and their density, Egorov, convergence in measure, Haar measure, Hausdorff measure. Differentiation of measures sits in `MeasureTheory/Covering` (Vitali, Besicovitch, the density theorem, Lebesgue differentiation).

Lusin’s separation theorem for analytic sets, and the Lusin–Souslin theorem, are in `MeasureTheory/Constructions/Polish/Basic.lean`. Approximation of a measurable function by a continuous function was not found under the name Lusin.

**Status.** Drafted in `Mathlib04.md`.

## 5. Differentiation and the fine structure of real functions

**Partial.** Lebesgue differentiation, Vitali and Besicovitch coverings, Rademacher’s theorem (`Analysis/Calculus/Rademacher.lean`), bounded variation (`Analysis/BoundedVariation.lean` and the vector-measure variant), absolute continuity, and the fundamental theorem for the interval integral.

The classical fine structure is missing: Denjoy–Young–Saks, approximate continuity as a theory, Zahorski’s characterization. The Henstock–Kurzweil and McShane integrals are present as box integrals; see `Mathlib05.md`.

**Status.** Drafted in `Mathlib05.md`.

## 6. Probability: measure-theoretic foundations and limit theory

**Substantial.** `Mathlib/Probability`: independence and the Kolmogorov zero–one law, Borel–Cantelli, conditional expectation and probability, kernels and disintegration (including standard Borel spaces), Ionescu–Tulcea, characteristic functions, Lévy’s continuity theorem, the portmanteau theorem, Prokhorov’s theorem and the Lévy–Prokhorov metric, convergence in distribution, Cramér–Wold, moments and the moment generating function.

Named limit theorems that were read: the strong law in Etemadi’s pairwise-independent form, an `L^p` strong law, and a Banach-valued extension by simple approximation (`Probability/StrongLaw.lean`); the central limit theorem in dimension one (`Probability/CentralLimitTheorem.lean`). Named laws include Gaussian measures on second-countable normed spaces, with Fernique’s theorem, and the usual discrete and continuous textbook laws.

The law of the iterated logarithm, a local CLT, and stable laws were not found. The multidimensional CLT is not a separate theorem; Cramér–Wold is.

**Status.** Drafted in `Mathlib06.md`.

## 7. Concentration, high-dimensional probability, and empirical processes

**Partial.** Sub-Gaussian random variables are developed in the sense of Vershynin’s five equivalent tail conditions (`Probability/Moments/SubGaussian.lean`). Covering and packing numbers are in `Topology/MetricSpace/CoveringNumbers.lean`. Fernique’s theorem is the Gaussian tail input.

Concentration of measure, logarithmic Sobolev inequalities, hypercontractivity, generic chaining, empirical processes, and VC theory were not found. Of Vershynin’s five sub-Gaussian conditions, the moment-generating bound is defined; the other four are left open in that file.

**Status.** Drafted in `Mathlib07.md`.

## 8. Stochastic processes, martingales, and stochastic calculus

**Partial.** Discrete-time martingales: convergence, upcrossings, optional stopping, optional sampling (`Probability/Martingale`). Processes: filtrations, adapted and predictable processes, stopping times, hitting times. `Probability/Process/Kolmogorov.lean` defines the Kolmogorov moment condition and says that it is the hypothesis of the Kolmogorov–Chentsov theorem; the continuity theorem itself is not claimed there. Brownian motion: finite-dimensional laws, the continuous-path predicate, the Gaussian covariance characterization, and the weak Markov property (`Probability/BrownianMotion`).

The stochastic integral, quadratic variation, Itô’s formula, Girsanov’s theorem, and stochastic differential equations were not found. Kolmogorov’s extension theorem is explicitly absent; the Brownian finite-dimensional distributions are shown to be a projective family.

**Status.** Drafted in `Mathlib08.md`.

## 9. Malliavin calculus, rough paths, and stochastic PDE

**Thin.** No module for Malliavin calculus, rough paths, regularity structures, paracontrolled distributions, or singular stochastic PDE. Brownian motion is recorded under Section 8. Fernique’s theorem cites Hairer’s stochastic-PDE notes only as a reference for the Gaussian estimate.

**Status.** Drafted in `Mathlib09.md`.

## 10. Ergodic theory and measurable dynamics

**Partial.** `Dynamics/Ergodic`: measure-preserving maps, ergodicity and quasi-ergodicity, conservative maps, Poincaré recurrence, circle rotations, and actions. Birkhoff sums and averages (`Dynamics/BirkhoffSum`). The von Neumann mean ergodic theorem for a contraction of a Hilbert space (`Analysis/InnerProductSpace/MeanErgodic.lean`). Topological side: entropy, minimality, transitivity, the translation number of a degree-one lift, symbolic dynamics. Følner sequences are in `MeasureTheory/Group/FoelnerFilter.lean`.

The pointwise Birkhoff theorem, Kolmogorov–Sinai entropy, and multiple recurrence were not found.

**Status.** Drafted in `Mathlib10.md`.

## 11. Classical inequalities, means, majorization, and rearrangement

**Partial.** Jensen, Hölder, and Minkowski through `Analysis/MeanInequalities.lean`, `Analysis/MeanInequalitiesPow.lean`, and the integral and `L^p` forms. Chebyshev’s sum inequality (`Algebra/Order/Chebyshev.lean`). The rearrangement inequality (`Algebra/Order/Rearrangement.lean`). Doubly stochastic matrices and Birkhoff’s theorem on them (`Analysis/Convex`).

Karamata’s inequality as a theory, the Brunn–Minkowski inequality, and geometric isoperimetry were not found.

**Status.** Drafted in `Mathlib11.md`.

## 12. Convexity, convex analysis, and variational analysis

**Partial.** `Analysis/Convex` is large: convex sets and functions, Jensen’s inequality, gauges, hulls, extreme points, the Krein–Milman theorem, Carathéodory, cones, exposed faces, strict convexity, simplicial complexes, and derivatives of convex functions. There is a separate `Geometry/Convex`.

Fenchel–Moreau duality, subdifferentials, proximal mappings, and monotone operators were not found. The variational-analysis half of the section is open.

**Status.** Drafted in `Mathlib12.md`.

## 13. Matrix analysis, operator monotonicity, and noncommutative inequalities

**Partial.** Hermitian functional calculus, singular values (`Analysis/InnerProductSpace/SingularValues.lean`), `C⋆`-matrices, doubly stochastic matrices, and the continuous functional calculus for `C⋆`-algebras (real powers, positive part, exponential and logarithm).

Operator monotonicity is proved for real powers on \([0,1]\), the logarithm, inversion on the positive cone, and powers of contractions. Löwner’s characterization of operator-monotone functions, and the Golden–Thompson inequality, were not found.

**Status.** Drafted in `Mathlib13.md`.

## 14. Functional, isoperimetric, and geometric inequalities

**Thin.** The rearrangement inequality and the Gagliardo–Nirenberg–Sobolev inequality (Section 26) are the nearest results. No isoperimetric inequality, Brunn–Minkowski inequality, or Gaussian isoperimetry.

**Status.** Drafted in `Mathlib14.md`.

## 15. Core Banach and Hilbert space theory

**Substantial.** Normed spaces and operator norms, Hahn–Banach in normed and polynormable settings, the Banach–Steinhaus theorem, compact operators, Fredholm operators between Hausdorff topological vector spaces (with the Fredholm alternative for compact operators), `L^p` and `ℓ^p`. Hilbert space: orthonormal sets, orthogonal projection, the adjoint, and the Fréchet–Riesz representation theorem (`Analysis/InnerProductSpace/Dual.lean`).

The Banach open-mapping theorem and the closed-graph theorem are in `Analysis/Normed/Operator/Banach.lean`. `Topology/Algebra/Group/OpenMapping.lean` is the open-mapping theorem for morphisms of σ-compact groups. Banach–Alaoglu and Schauder bases, including unconditional bases, are present.

**Status.** Drafted in `Mathlib15.md`.

## 16. Locally convex spaces, duality, and distributions

**Substantial.** `Analysis/LocallyConvex`: seminorms, Hahn–Banach for polynormable spaces, separation, polars, weak and strong topologies, barrelled spaces, Montel spaces, the weak operator topology. Distributions on open subsets of finite-dimensional spaces (`Analysis/Distribution/Distribution.lean`), test functions, Schwartz space, tempered distributions, and the Fourier transform on Schwartz functions, including Plancherel for Schwartz functions.

Nuclear spaces and the Schwartz kernel theorem were not found. Distribution theory is on finite-dimensional vector spaces, not on manifolds.

**Status.** Drafted in `Mathlib16.md`.

## 17. Banach space geometry, bases, and operator ideals

**Thin.** Schauder bases and unconditional bases are present and are written with Section 15. No type or cotype, approximation property, or Schatten classes. Compact and Fredholm operators are recorded under Sections 15 and 21.

**Status.** Drafted in `Mathlib17.md`.

## 18. Vector-valued analysis and analysis in Banach spaces

**Partial.** The Bochner integral is developed (`MeasureTheory/Integral/Bochner`), including the fundamental theorem and continuity under continuous linear maps. Vector measures have a Radon–Nikodym theorem and bounded variation. The strong law has a Banach-valued form obtained from the real case by simple approximation.

The Pettis integral, UMD spaces, and radonifying operators were not found.

**Status.** Drafted in `Mathlib18.md`.

## 19. Banach lattices, positive operators, and ordered structures

**Thin.** No Banach-lattice library. Ordered normed spaces exist (`Analysis/Normed/Order`). Positive and completely positive maps exist in the `C⋆` library (Section 23), not as a lattice theory.

**Status.** Drafted in `Mathlib19.md`.

## 20. Banach algebras and commutative harmonic analysis of algebras

**Partial.** Spectrum, the Gelfand formula, and Gelfand–Mazur (`Analysis/Normed/Algebra`). Finite abelian Fourier analysis and Pontryagin duality (`Analysis/Fourier/FiniteAbelian`). Haar measure, the modular character, group convolution, and Følner sequences.

Peter–Weyl theory was not found. The Gelfand duality file in the tree is the `C⋆` statement (Section 23).

**Status.** Drafted in `Mathlib20.md`.

## 21. Operator theory: bounded operators, spectra, and model theory

**Partial.** Bounded and compact operators, Fredholm operators and the Fredholm alternative, the spectrum of a Banach-algebra element, and a large continuous functional calculus. For self-adjoint operators, real eigenvalues and orthogonal eigenspaces are general. `Analysis/InnerProductSpace/Spectrum.lean` proves the finite-dimensional diagonalization and the compact case: the eigenspaces of a compact self-adjoint operator have trivial orthogonal complement, and the nonzero eigenspaces are finite-dimensional. The spectral theorem for a general bounded self-adjoint operator is marked there as future work. Singular values are defined.

The model theory of contractions (characteristic functions, Sz.-Nagy–Foiaş) and the essential spectrum were not found. There is no spectral measure for a general normal operator on Hilbert space beyond the continuous functional calculus in a `C⋆`-algebra.

**Status.** Drafted in `Mathlib21.md`.

## 22. Unbounded operators, spectral theory, and mathematical physics

**Partial.** Partially defined operators on Hilbert space: formal adjoints and the adjoint (`Analysis/InnerProductSpace/LinearPMap.lean`). The Euclidean Laplacian as a differential operator (`Analysis/InnerProductSpace/Laplacian.lean`). The Lax–Milgram theorem.

The spectral theorem for unbounded self-adjoint operators, spectral measures, Stone’s theorem, and scattering theory were not found.

**Status.** Drafted in `Mathlib22.md`.

## 23. Operator algebras, operator spaces, free probability, and noncommutative geometry

**Partial.** `Analysis/CStarAlgebra` is a real theory: the spectrum, continuous functional calculus, Gelfand–Naimark–Segal, Gelfand duality, positive and completely positive maps, approximate units, projections, unitization, multipliers, and Fuglede’s theorem. `Analysis/VonNeumannAlgebra/Basic.lean` gives Sakai’s abstract definition and the concrete commutant definition. The file says that the equivalence of the two definitions, and the double commutant theorem, are still ahead.

Operator spaces, free probability, Tomita–Takesaki theory, and spectral triples were not found.

**Status.** Drafted in `Mathlib23.md`.

## 24. Semigroups, evolution equations, and functional calculus

**Thin.** No strongly continuous semigroups, Hille–Yosida, or Lumer–Phillips. The functional calculus that exists is the continuous functional calculus of Sections 21 and 23, not a sectorial calculus. Ordinary differential equations are recorded under Section 31. Algebraic semigroups are not this section.

**Status.** Drafted in `Mathlib24.md`.

## 25. Integral equations and classical operator methods

**Thin.** The Fredholm alternative for compact operators is the nearest result (Section 21). No Volterra theory and no Fredholm determinants.

**Status.** Drafted in `Mathlib25.md`.

## 26. Sobolev spaces, smoothness scales, and interpolation

**Partial.** The Gagliardo–Nirenberg–Sobolev inequality for compactly supported `C¹` functions (`Analysis/FunctionalSpaces/SobolevInequality.lean`). Bessel potential spaces `H^{s,p}` of tempered distributions, bundled in `Analysis/FunctionalSpaces/BesselPotentialSpace.lean` and unbundled in `Analysis/Distribution/Sobolev.lean`. A pointwise Hölder condition `C^{k+α}` (`Analysis/Calculus/ContDiffHolder/Pointwise.lean`).

Sobolev spaces `W^{k,p}` on domains, traces, extension operators, real interpolation, Besov spaces, and Triebel–Lizorkin spaces were not found.

**Status.** Drafted in `Mathlib26.md`.

## 27. Fourier analysis and real-variable harmonic analysis

**Partial.** The Euclidean Fourier transform, inversion (`Analysis/Fourier/Inversion.lean`), the Riemann–Lebesgue lemma, convolution, Poisson summation, and an `L^p` Fourier file. Schwartz functions carry a Fourier transform that is a continuous linear equivalence, with Plancherel for Schwartz functions. Finite abelian groups and the circle (`AddCircle`) are included. The Gaussian Fourier transform is in `Analysis/SpecialFunctions/Gaussian`.

The Hardy–Littlewood maximal function, Calderón–Zygmund theory, Littlewood–Paley theory, BMO, and Carleson’s theorem were not found. `Analysis/Fourier/LpSpace.lean` is Plancherel’s theorem for \(L^2\). Hausdorff–Young was not found.

**Status.** Drafted in `Mathlib27.md`.

## 28. Abstract harmonic analysis on groups

**Partial.** Haar measure: existence, uniqueness, quotients, and the case of normed spaces (`MeasureTheory/Measure/Haar`). The modular character, group convolution, and Følner sequences. Pontryagin duality and Fourier analysis for finite abelian groups. Fourier analysis on the circle.

Peter–Weyl theory and the representation theory of compact groups, as harmonic analysis, were not found.

**Status.** Drafted in `Mathlib28.md`.

## 29. Wavelets, frames, time–frequency analysis, and sampling

**Thin.** No wavelets, Gabor systems, or sampling theorems. The name “frame” occurs for vector-bundle frames and for order-theoretic frames. Reproducing-kernel Hilbert spaces (`Analysis/InnerProductSpace/Reproducing.lean`, Moore’s theorem) are the nearest neighboring theory.

**Status.** Drafted in `Mathlib29.md`.

## 30. Distributions, pseudodifferential operators, microlocal and semiclassical analysis

**Partial.** Distributions, test functions, Schwartz space, tempered distributions, and Fourier multipliers are the Section 16 library. Pseudodifferential operators, wavefront sets, Fourier integral operators, and semiclassical measures were not found.

**Status.** Drafted in `Mathlib30.md`.

## 31. Ordinary differential equations and dynamical systems

**Partial.** Picard–Lindelöf, an existence-and-uniqueness file, and Gronwall’s inequality (`Analysis/ODE`). Flows, ω-limit sets, periodic points, circle dynamics and rotation number, topological entropy, symbolic dynamics, and integral curves on manifolds. The Banach fixed-point theorem is in `Topology/MetricSpace/Contracting.lean` (Section 35).

Stable and unstable manifolds, hyperbolicity, KAM theory, and bifurcations were not found.

**Status.** Drafted in `Mathlib31.md`.

## 32. Partial differential equations: general and linear theory

**Thin.** The divergence theorem (`MeasureTheory/Integral/DivergenceTheorem.lean` and `Analysis/BoxIntegral`), differential forms, and Lax–Milgram are tools. Harmonic functions are recorded under Section 33. There is no Cauchy–Kowalevski theorem, no energy-estimate calculus, and no general theory of linear PDE.

**Status.** Drafted in `Mathlib32.md`.

## 33. Elliptic and parabolic equations

**Thin.** Harmonic functions on finite-dimensional inner product spaces and on plane disks: the mean-value property, Liouville, and the Poisson integral formula (`Analysis/Complex/Harmonic`, `Analysis/InnerProductSpace/Harmonic`). The Euclidean Laplacian and Lax–Milgram.

Schauder estimates, De Giorgi–Nash–Moser theory, viscosity solutions, free boundaries, and parabolic equations were not found.

**Status.** Drafted in `Mathlib33.md`.

## 34. Hyperbolic equations, conservation laws, dispersive PDE, fluids, and kinetic theory

**Thin.** No module for these subjects.

**Status.** Drafted in `Mathlib34.md`.

## 35. Nonlinear functional analysis, monotone operators, and fixed points

**Partial.** The Banach fixed-point theorem for contracting maps on complete metric spaces, with a rate and continuity of the fixed-point map (`Topology/MetricSpace/Contracting.lean`).

Brouwer’s theorem, Schauder’s theorem, topological degree, and monotone operators were not found.

**Status.** Drafted in `Mathlib35.md`.

## 36. Calculus of variations, Γ-convergence, and homogenization

**Thin.** No direct method, Γ-convergence, homogenization, or Young measures. Convex integral functionals and the manifold library are neighboring material, not this theory.

**Status.** Drafted in `Mathlib36.md`.

## 37. Geometric measure theory, BV, rectifiability, and currents

**Partial.** Hausdorff measure (`MeasureTheory/Measure/Hausdorff.lean`) and Hausdorff dimension. Gromov–Hausdorff distance. Bounded variation of functions and of vector measures. The differentiation theory of Section 5 (density, Vitali).

Sets of finite perimeter, rectifiability, currents, varifolds, and Allard’s theorem were not found.

**Status.** Drafted in `Mathlib37.md`.

## 38. Potential theory and capacity

**Thin.** No capacity and no classical potential theory. The Poisson integral of Section 33 is the nearest result.

**Status.** Drafted in `Mathlib38.md`.

## 39. Metric measure spaces, Dirichlet forms, heat kernels, optimal transport, and fractals

**Partial.** Doubling measures, Hausdorff dimension, Gromov–Hausdorff space, and Delone sets (`Analysis/AperiodicOrder/Delone`). Gaussian measures and Fernique’s theorem.

Dirichlet forms, heat kernels, curvature-dimension conditions, optimal transport, and the Wasserstein metric were not found.

**Status.** Drafted in `Mathlib39.md`.

## 40. One complex variable

**Substantial.** Holomorphic and analytic functions, Cauchy theory (`Analysis/Complex/CauchyIntegral.lean`), Liouville, the open mapping theorem, Schwarz, Phragmén–Lindelöf, removable singularities, local uniform limits, the identity theorem through isolated zeros, Jensen’s formula, and the calculus of meromorphic functions (orders, divisors, normal forms). Harmonic functions on disks with the Poisson integral. The unit disk and the upper half-plane as geometries.

`Analysis/Complex/RiemannMapping.lean` states that it holds only lemmas strictly weaker than the Riemann mapping theorem, kept private, while a complete proof is still being merged. The residue theorem, the argument principle, and Laurent series were not found under those names. A Montel theorem for holomorphic families was not found. Montel spaces in Section 16 are a different notion.

**Status.** Drafted in `Mathlib40.md`.

## 41. Entire and meromorphic functions, value distribution

**Partial.** Jensen’s formula. Nevanlinna data: the characteristic, the proximity function, and the integrated counting function (`Analysis/Complex/ValueDistribution`). The first main theorem is proved in the form of invariance of the characteristic under `f ↦ f⁻¹` and under `f ↦ f - c`.

`SecondMainTheorem.lean` says that it collects material for a future proof and that a full formalization lives outside this checkout. Hadamard factorization was not found.

**Status.** Drafted in `Mathlib41.md`.

## 42. Hardy, Bergman, and model spaces

**Thin.** No Hardy spaces, Bergman spaces, model spaces, Toeplitz operators, or Hankel operators. Reproducing-kernel Hilbert spaces (Section 29) and the geometry of the disk and the half-plane are the neighboring files.

**Status.** Drafted in `Mathlib42.md`.

## 43. Univalent functions, conformal mapping, and extremal methods

**Thin.** The Riemann mapping theorem is not in the library (Section 40). Local conformality exists (`Analysis/Complex/Conformal.lean`, `Analysis/Calculus/Conformal`). No univalent-function theory and no Koebe or Bieberbach theorem.

**Status.** Drafted in `Mathlib43.md`.

## 44. Riemann surfaces, quasiconformal mappings, and Teichmüller theory

**Thin.** No Riemann surfaces, quasiconformal maps, Beltrami equation, or Teichmüller theory. The name Teichmüller occurs for the Teichmüller–Tukey lemma and for Witt vectors.

**Status.** Drafted in `Mathlib44.md`.

## 45. Several complex variables, complex manifolds, pluripotential theory, and CR analysis

**Thin.** `Geometry/Manifold/Complex.lean` proves a maximum principle for holomorphic functions on boundaryless complex manifolds. It is not several complex variables, and the boundary models in the library are real. No plurisubharmonic functions, domains of holomorphy, or CR manifolds.

**Status.** Drafted in `Mathlib45.md`.

## 46. Complex dynamics

**Thin.** No Fatou–Julia theory. Circle dynamics and periodic points are real or topological (Section 31).

**Status.** Drafted in `Mathlib46.md`.

## 47. Approximation theory

**Partial.** The Stone–Weierstrass theorem (`Topology/ContinuousMap/StoneWeierstrass.lean`) and the Weierstrass approximation theorem. Smooth approximation appears as `Analysis/Normed/Lp/SmoothApprox.lean`. Chebyshev polynomials have an extremal file (Section 48). Convolution is available.

Jackson theorems, splines, and nonlinear approximation were not found.

**Status.** Drafted in `Mathlib47.md`.

## 48. Orthogonal polynomials, moment problems, and spectral recurrences

**Partial.** Chebyshev polynomials: definition, roots and extrema, orthogonality, and Gauss quadrature (`Analysis/SpecialFunctions/Trigonometric/Chebyshev`). Hermite polynomials, including a Gaussian file, and shifted Legendre polynomials live under `RingTheory/Polynomial` and are algebraic as much as analytic.

No general theory of orthogonal polynomials, no moment problem, and no Jacobi operators.

**Status.** Drafted in `Mathlib48.md`.

## 49. Special functions, integral transforms, and classical formulae

**Partial.** The Gamma function, including the Bohr–Mollerup theorem, the digamma function, and the Beta function. Stirling’s formula for `n!`. The Gaussian integral and its Fourier transform. The ordinary hypergeometric series and, from it, the Bessel function of the first kind (`Analysis/SpecialFunctions/Bessel.lean`). The Weierstrass elliptic function. The Mellin transform and the Mellin inversion formula. Frullani integrals. Trigonometric and exponential functions are in place.

Airy functions and the classical tables (Bateman, Gradshteyn–Ryzhik) as a corpus were not found. Bessel theory here is the series definition, not the handbook of identities.

**Status.** Drafted in `Mathlib49.md`.

## 50. Asymptotic analysis, resurgence, and perturbation

**Partial.** `Analysis/Asymptotics` is the calculus of little-o, big-O, and asymptotic equivalence, with growth and decay lemmas. `Tactic/ComputeAsymptotics` holds the multiseries and the lemmas described as the `compute_asymptotics` procedure; a tactic syntax of that name was not found.

Resurgence, Borel summation, and Gevrey classes were not found.

**Status.** Drafted in `Mathlib50.md`.

## 51. Integrable systems and Riemann–Hilbert methods

**Thin.** No Riemann–Hilbert correspondence and no integrable PDE. `Algebra/Lie/Sl2.lean` is the Lie algebra.

**Status.** Drafted in `Mathlib51.md`.

## 52. Geometric analysis on manifolds

**Partial.** The smooth-manifold library is developed: charted spaces, `C^n` and smooth maps, the Fréchet derivative on manifolds, vector bundles, immersions, submersions, embeddings, partitions of unity, bump functions, vector fields, and integral curves. The Whitney embedding theorem is proved for compact manifolds (`Geometry/Manifold/WhitneyEmbedding.lean`); the σ-compact case is a TODO in that file. Riemannian geometry is a definition of the metric and of path length (`Geometry/Manifold/Riemannian`). Algebraic inputs: the spin group and the Hodge star on exterior algebras. Differential forms and the divergence theorem are present. `Geometry/Manifold/PoincareConjecture.lean` only points at `proof_wanted` statements.

Curvature, Ricci flow, minimal surfaces, mean curvature flow, and harmonic maps were not found.

**Status.** Drafted in `Mathlib52.md`.

## 53. Elliptic operators on manifolds, index theory, and spectral geometry

**Thin.** Fredholm operators between topological vector spaces are a prerequisite (Section 21), and the Euclidean Laplacian is a differential operator (Section 22). No elliptic operators on manifolds, no Atiyah–Singer index theorem, no Hodge theory on Riemannian manifolds, and no Weyl law.

**Status.** Drafted in `Mathlib53.md`.

## Next prose file

`Mathlib04.md` through `Mathlib53.md` are drafted. Each prose file begins with the commit, the import roots, and the namespaces, then states the theorems in mathematical prose with module paths in parentheses. When a PDF is compared later, add that comparison to the section file rather than to this index, and record only a status change here.
