# 46. Complex Dynamics

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. There is no root for Fatou–Julia theory. The real and topological dynamics that sit next to this section, and that belong to Section 31 rather than here, are `Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber` and `Mathlib.Dynamics.PeriodicPts.Defs`.

**Namespaces.** The translation number is defined on `CircleDeg1Lift`, the bundled monotone maps of the line that commute with translation by one. A periodic point is a point fixed by some positive iterate. Neither namespace is a Fatou set or a Julia set.

Fatou–Julia theory was not found. A search for the Fatou set, the Julia set, the Mandelbrot set, and holomorphic motions returns nothing in that sense.

Circle dynamics, rotation numbers, and periodic points are real or topological and belong to Section 31. What is proved for the circle is the translation number of a monotone lift: if \(f:\mathbb{R}\to\mathbb{R}\) is monotone and satisfies \(f(x+1)=f(x)+1\), the limit of \((f^n(x)-x)/n\) exists and is independent of \(x\), and a continuous lift has a point of period \(n\) with displacement \(m\) if and only if the translation number equals \(m/n\) (`Dynamics/Circle/RotationNumber/TranslationNumber.lean`). A periodic point of a self-map is a point fixed by a positive iterate (`Dynamics/PeriodicPts/Defs.lean`).

`Dynamics/Newton.lean` defines the algebraic Newton map \(x\mapsto x-P(x)/P'(x)\) of a polynomial and uses it for nilpotent perturbations of roots. It is not a convergence theorem, and it is not complex dynamics.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

For a holomorphic self-map of the unit disc, Schwarz–Pick gives contraction in the disc geometry and its equality/automorphism rigidity. In particular, a self-map fixing two distinct interior points is the identity; a nonidentity self-map has at most one interior fixed point ([fixed-point theorem](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Conformal/SchwarzPick/FixedPoint.lean), [rigidity](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Conformal/SchwarzPick/Rigidity.lean)). These are genuine results relevant to holomorphic dynamics, but no Fatou/Julia theory, Denjoy–Wolff iteration theorem, or local analytic linearization/classification theorem was located.

## Topics of Section 46 not found in either inspected library

- The Fatou set, the Julia set, and the Mandelbrot set.
- Holomorphic motions, the \(\lambda\)-lemma, and Sullivan’s no-wandering-domains theorem.
- Local analytic classification of attracting, repelling, parabolic, and indifferent fixed points, Siegel discs, and periodic Fatou components. Schwarz–Pick rigidity and uniqueness of an interior disc fixed point are proved in TauCeti.
- Convergence of Newton’s method as a dynamical system in the plane. The Newton file is an algebraic identity used for Hensel’s lemma and the Jordan–Chevalley decomposition, not an iterative convergence theorem.
