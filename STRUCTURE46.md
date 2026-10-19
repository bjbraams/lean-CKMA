# Structure 46: Complex dynamics

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS46.md); [bibliographical scope](CKMA-bib.md#ckma-46); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** There is no root for Fatou–Julia theory. Adjacent material: `Mathlib.Dynamics.PeriodicPts.Defs`, `Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber`, `Mathlib.Dynamics.TopologicalEntropy.CoverEntropy`, `Mathlib.Analysis.Complex.CoveringMap`, `Mathlib.NumberTheory.Height.Projectivization`, `Mathlib.NumberTheory.Height.Northcott`.

**Namespaces.** The translation number is defined on `CircleDeg1Lift`, the bundled monotone maps of the line commuting with translation by one. Periodic-point declarations use `Function`. TauCeti's normal-family and disc results are in the `TauCeti` namespace.

## Julia sets and global iteration

[Mathematical scope](SYNOPSIS46.md#julia-sets-and-global-iteration).

Neither library defines the Fatou set or the Julia set of a rational map; a search for the Fatou set, the Julia set, the Mandelbrot set, and holomorphic motions returns nothing in that sense.

### Mathlib

Supporting material only. A periodic point of a self-map is a point fixed by a positive iterate (`Function.IsPeriodicPt`, `Dynamics/PeriodicPts/Defs.lean`). `Dynamics/Newton.lean` defines the algebraic Newton map \(x\mapsto x-P(x)/P'(x)\) of a polynomial and uses it for nilpotent perturbations of roots; it is not a convergence theorem and not complex dynamics.

### TauCeti

Supporting material only: the normal-family tools on which the definition of the Fatou set rests are partly present. Montel's selection theorem holds for locally bounded families of holomorphic maps on an open subset of \(\mathbb C\) with values in a proper complex normed space (`TauCeti.montel`, [Montel](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Montel/Basic.lean)), and local boundedness is equivalent to relative compactness in the compact-open topology ([precompactness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Montel/Precompact.lean)). Vitali's theorem upgrades pointwise convergence on a set with an accumulation point to locally uniform convergence for locally bounded sequences on a domain (`TauCeti.vitali`, [Vitali](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Vitali.lean)). Hurwitz's theorem holds in both directions: a locally uniform limit of zero-free holomorphic functions on a domain is zero-free or identically zero, and each isolated zero of the limit is approached by zeros of the approximants ([Hurwitz](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Hurwitz.lean)). Normality in the spherical metric and Montel's theorem for families omitting two values, used in 46.5, are not present.

**Synopsis entries.** Not covered: 46.1–46.9.

## Local normal forms and small divisors

[Mathematical scope](SYNOPSIS46.md#local-normal-forms-and-small-divisors).

**Synopsis entries.** Not covered: 46.10–46.16.

## Fatou components and hyperbolicity

[Mathematical scope](SYNOPSIS46.md#fatou-components-and-hyperbolicity).

### Mathlib

Supporting material only. Circle dynamics is real or topological and belongs to Section 31. What is proved is the translation number of a monotone lift: if \(f:\mathbb{R}\to\mathbb{R}\) is monotone and satisfies \(f(x+1)=f(x)+1\), the limit of \((f^n(x)-x)/n\) exists and is independent of \(x\), and a continuous lift has a point of period \(n\) with displacement \(m\) if and only if the translation number equals \(m/n\) (`CircleDeg1Lift.tendsto_translationNumber`, `CircleDeg1Lift.translationNumber_eq_rat_iff` in `Dynamics/Circle/RotationNumber/TranslationNumber.lean`). Rotation domains of rational maps are not treated.

**Synopsis entries.** Not covered: 46.17–46.27, 46.69.

## Polynomial Green functions, rays, and equilibrium measures

[Mathematical scope](SYNOPSIS46.md#polynomial-green-functions-rays-and-equilibrium-measures).

Topological entropy of a self-map of a uniform space is defined in Mathlib (see the next section), but the entropy of a rational map is not computed, and there is no equilibrium or maximal-entropy measure.

**Synopsis entries.** Not covered: 46.28–46.39.

## Parameter spaces, deformation, and renormalization

[Mathematical scope](SYNOPSIS46.md#parameter-spaces-deformation-and-renormalization).

**Synopsis entries.** Not covered: 46.40–46.48.

## Conformal repellers and thermodynamic formalism

[Mathematical scope](SYNOPSIS46.md#conformal-repellers-and-thermodynamic-formalism).

### Mathlib

Supporting material only. Topological entropy is defined for a self-map of a uniform space, through dynamical covers and nets (`Dynamics/TopologicalEntropy/CoverEntropy.lean`, `Dynamics/TopologicalEntropy/NetEntropy.lean`), with monotonicity in the subset and behaviour under semiconjugacy. These are general dynamical tools; their detailed statements are in [Section 31](STRUCTURE31.md). Pressure, transfer operators, and Gibbs states are not defined.

**Synopsis entries.** Not covered: 46.50–46.55.

## Transcendental entire dynamics

[Mathematical scope](SYNOPSIS46.md#transcendental-entire-dynamics).

### Mathlib

`Analysis/Complex/CoveringMap.lean` proves that \(\exp:\mathbb C\to\mathbb C\setminus\{0\}\) is a covering map (`Complex.isCoveringMapOn_exp`, `Complex.isCoveringMap_exp`). Since the singular set of \(\exp\) is \(\{0\}\), this is the case \(f=\exp\) of 46.56. The polynomial analogue, that a polynomial is a covering map over the complement of its critical values, is `Polynomial.isCoveringMapOn_eval`. The general theorem for transcendental entire functions is not present.

**Synopsis entries.** Partly covered: 46.56 (the exponential function only). Not covered: 46.57–46.61.

## Several-variable holomorphic dynamics

[Mathematical scope](SYNOPSIS46.md#several-variable-holomorphic-dynamics).

**Synopsis entries.** Not covered: 46.62–46.68.

## Self-maps of the disk

[Mathematical scope](SYNOPSIS46.md#self-maps-of-the-disk).

### TauCeti

For a holomorphic self-map of the unit disc, Schwarz–Pick gives contraction in the disc geometry and its equality/automorphism rigidity: equality at a single pair of distinct points forces a disc automorphism ([rigidity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/SchwarzPick/Rigidity.lean)). In particular, a self-map fixing two distinct interior points is the identity, and a self-map other than the identity has at most one interior fixed point (`TauCeti.eqOn_id_of_isFixedPt_of_isFixedPt`, `TauCeti.eqOn_id_or_subsingleton_inter_fixedPoints`, [fixed-point theorem](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/SchwarzPick/FixedPoint.lean)). These are ingredients of the Denjoy–Wolff theorem; the convergence of iterates, Wolff's lemma, and angular derivatives are not proved.

**Synopsis entries.** Not covered: 46.70, 46.71.

## Arithmetic and non-Archimedean dynamics

[Mathematical scope](SYNOPSIS46.md#arithmetic-and-non-archimedean-dynamics).

### Mathlib

Supporting material only. The multiplicative and logarithmic Weil heights of points of a finite-dimensional projective space over a field with admissible absolute values are defined (`Projectivization.mulHeight`, `Projectivization.logHeight` in `NumberTheory/Height/Projectivization.lean`), and the Northcott property is transferred from `mulHeight₁` to `logHeight₁` (`NumberTheory/Height/Northcott.lean`); the Northcott property for heights on projective space is listed there as future work. No canonical height of a morphism is defined.

### TauCeti

Supporting material only. The Néron–Tate canonical height of an elliptic curve is constructed as \(\lim_n h(2^nP)/4^n\), satisfies \(\hat h(2P)=4\hat h(P)\), and vanishes exactly on torsion points (`WeierstrassCurve.Affine.Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder`, [canonical height](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/AlgebraicGeometry/EllipticCurve/CanonicalHeight/Basic.lean)). This is the Tate averaging argument for the doubling map of an elliptic curve, not the Call–Silverman height of a morphism of \(\mathbb P^N\).

**Synopsis entries.** Not covered: 46.72–46.74.
