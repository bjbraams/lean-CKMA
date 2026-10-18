# 46. Complex Dynamics

Checked against Mathlib commit `f039e1b8a616d45782a5c7fc5e7909249c36b8ea` (2026-10-18, Lean `v4.36.0-rc1`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. There is no root for Fatou–Julia theory. The real and topological dynamics that sit next to this section, and that belong to Section 31 rather than here, are `Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber` and `Mathlib.Dynamics.PeriodicPts.Defs`.

**Namespaces.** The translation number is defined on `CircleDeg1Lift`, the bundled monotone maps of the line that commute with translation by one. A periodic point is a point fixed by some positive iterate. Neither namespace is a Fatou set or a Julia set.

Fatou–Julia theory was not found. A search for the Fatou set, the Julia set, the Mandelbrot set, and holomorphic motions returns nothing in that sense.

Circle dynamics, rotation numbers, and periodic points are real or topological and belong to Section 31. What is proved for the circle is the translation number of a monotone lift: if \(f:\mathbb{R}\to\mathbb{R}\) is monotone and satisfies \(f(x+1)=f(x)+1\), the limit of \((f^n(x)-x)/n\) exists and is independent of \(x\), and a continuous lift has a point of period \(n\) with displacement \(m\) if and only if the translation number equals \(m/n\) (`Dynamics/Circle/RotationNumber/TranslationNumber.lean`). A periodic point of a self-map is a point fixed by a positive iterate (`Dynamics/PeriodicPts/Defs.lean`).

Topological entropy is defined for a self-map of a uniform space, through dynamical covers and nets (`Dynamics/TopologicalEntropy/CoverEntropy.lean`, `NetEntropy.lean`), with monotonicity in the subset and behaviour under semiconjugacy. No entropy of a rational map is computed, and there is no measure of maximal entropy.

`Dynamics/Newton.lean` defines the algebraic Newton map \(x\mapsto x-P(x)/P'(x)\) of a polynomial and uses it for nilpotent perturbations of roots. It is not a convergence theorem, and it is not complex dynamics.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6ebb29f84b4d`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

For a holomorphic self-map of the unit disc, Schwarz–Pick gives contraction in the disc geometry and its equality/automorphism rigidity: equality at a single pair of distinct points forces a disc automorphism. In particular, a self-map fixing two distinct interior points is the identity; a nonidentity self-map has at most one interior fixed point ([fixed-point theorem](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Complex/Conformal/SchwarzPick/FixedPoint.lean), [rigidity](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Complex/Conformal/SchwarzPick/Rigidity.lean)).

The normal-family tools on which iteration theory rests are partly present. Montel's selection theorem holds for locally bounded families of holomorphic maps on an open subset of \(\mathbb C\) with values in a proper complex normed space ([Montel](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Complex/Conformal/Montel/Basic.lean)). Vitali's theorem upgrades pointwise convergence on a set with an accumulation point to locally uniform convergence for locally bounded sequences on a domain ([Vitali](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Complex/Conformal/Vitali.lean)). Hurwitz's theorem holds in both directions: a locally uniform limit of zero-free holomorphic functions on a domain is zero-free or identically zero, and each isolated zero of the limit is approached by zeros of the approximants ([Hurwitz](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Complex/Conformal/Hurwitz.lean)). These are genuine results relevant to holomorphic dynamics, but no Fatou/Julia theory, Montel's theorem for families omitting two values, Denjoy–Wolff iteration theorem, or local analytic linearization/classification theorem was located.

## Topics of Section 46 not found in either inspected library

- The Fatou set, the Julia set, density of repelling cycles, the filled Julia set and the connectedness criterion, and the Mandelbrot set and its connectedness.
- Montel's theorem for families omitting two values, the normality criterion on which Fatou–Julia theory rests. TauCeti proves Montel's theorem for locally bounded families, Vitali's theorem, and Hurwitz's theorem.
- Holomorphic motions, the \(\lambda\)-lemma, polynomial-like maps and straightening, Sullivan’s no-wandering-domains theorem, and Thurston's characterization of postcritically finite maps.
- Local analytic classification of attracting, repelling, parabolic, and indifferent fixed points (Koenigs, Böttcher, the Leau–Fatou flower theorem), Siegel discs, the classification of periodic Fatou components, and hyperbolicity criteria. Schwarz–Pick rigidity and uniqueness of an interior disc fixed point are proved in TauCeti.
- Polynomial Green functions, the equilibrium (Brolin–Lyubich) measure and the measure of maximal entropy, thermodynamic formalism and Bowen's dimension formula, and the escaping set of transcendental entire maps. Mathlib defines topological entropy but computes none of these.
- Convergence of Newton’s method as a dynamical system in the plane. The Newton file is an algebraic identity used for Hensel’s lemma and the Jordan–Chevalley decomposition, not an iterative convergence theorem.
