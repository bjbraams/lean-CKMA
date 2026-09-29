# 14. Functional, Isoperimetric, and Geometric Inequalities

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The roots for this section are `Mathlib.Algebra.Order.Rearrangement` and `Mathlib.Analysis.FunctionalSpaces.SobolevInequality`.

**Namespaces.** The rearrangement inequality is stated for `Monovary` and `Antivary`, as in Section 11. The Sobolev inequality is in `MeasureTheory`.

This note records the discrete rearrangement inequality and the Sobolev and bounded-support Poincaré estimates relevant to this section. The geometric and isoperimetric inequalities searched for below were not found.

## Rearrangement

The rearrangement inequality of Section 11 compares \(\sum_i f_i g_{\sigma i}\) with \(\sum_i f_i g_i\): the sum is maximized when \(f\) and \(g\) monovary and minimized when they antivary, for a permutation that moves only points of the set of summation (`Algebra/Order/Rearrangement.lean`).

## The Gagliardo–Nirenberg–Sobolev inequality

The full development belongs to Section 26. The statements proved in `Analysis/FunctionalSpaces/SobolevInequality.lean` are as follows. On \(\iota\to\mathbb{R}\) with \(\iota\) finite of cardinality \(n\ge 2\), if \(p\) is the Hölder conjugate of \(n\) and \(u\) is a \(C^1\) compactly supported map into a real normed space, then
\[
\int^- \|u\|^p\le\Bigl(\int^- \|Du\|\Bigr)^p,
\]
with constant \(1\), using the coordinate sup norm on \(\iota\to\mathbb R\) and its induced operator norm on \(Du\). The integrals are lower integrals of extended norms. On a finite-dimensional real normed space of dimension \(n\ge 2\), with a Haar measure, the same comparison holds with a constant that depends only on the space, the measure, and \(p\); the constant comes from the comparison of Haar measure with Lebesgue measure on \(\mathbb{R}^n\) and from the operator norm of a chosen linear equivalence with \(\mathbb{R}^n\). Equivalently, the \(L^p\) norm of \(u\) is at most a constant times the \(L^1\) norm of its Fréchet derivative.

If the codomain is a real inner product space, \(1\le p<n\), and \(p'=np/(n-p)>0\) is the Sobolev conjugate defined by \((p')^{-1}=p^{-1}-n^{-1}\), then the \(L^{p'}\) norm of a \(C^1\) compactly supported \(u\) is at most a constant, depending on the measure and on \(p\), times the \(L^p\) norm of the derivative. If instead the codomain is finite-dimensional, the support of \(u\) lies in a bounded set \(s\), and \(1\le p<n\), then the \(L^p\) norm of \(u\) is at most a constant, depending on the codomain, the measure, \(s\), and \(p\), times the \(L^p\) norm of the derivative. This last statement is a Poincaré inequality for functions supported in a fixed bounded set.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti extends the smooth-function Sobolev estimates to actual weak Sobolev spaces. For \(1\le p<n\), it proves \(W^{1,p}_0(\Omega)\hookrightarrow L^{np/(n-p)}(\Omega)\), with a gradient-norm bound ([Sobolev embedding](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Sobolev/Embedding.lean)). For \(n<p<\infty\), it constructs a continuous linear embedding of whole-space \(W^{1,p}(\mathbb R^n)\) into the global Hölder space of exponent \(1-n/p\) ([Morrey embedding](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Sobolev/W1p/HolderEmbedding.lean)). The zero-boundary condition in the first result and the whole-space domain in the second are part of the statements. Section 26 records the underlying spaces and compactness results; no Brunn–Minkowski, Prékopa–Leindler, or isoperimetric theorem was located.

A Poincaré inequality is proved on \(W^{1,p}_0(\Omega)\), \(1\le p<\infty\), when \(\Omega\) lies in a slab of width \(b-a\): \(\|u\|_p\le(b-a)\|\nabla u\|_p\). A ball-containment version follows ([Poincaré](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Sobolev/Poincare/W1p0.lean)).

## Topics of Section 14 not found in either inspected library

- The Brunn–Minkowski inequality.
- The Euclidean isoperimetric inequality, and isoperimetric inequalities on manifolds.
- Gaussian isoperimetry. The Gaussian integral and the Fourier transform of a Gaussian are present; they are not an isoperimetric theorem.
- The Prékopa–Leindler inequality.
- Sobolev inequalities on Riemannian manifolds. The Euclidean Gagliardo–Nirenberg–Sobolev inequality above is the Sobolev inequality in this checkout, and it is written out in Section 26.
