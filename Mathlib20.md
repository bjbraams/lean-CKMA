# 20. Banach Algebras and Commutative Harmonic Analysis of Algebras

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Some roots below are directory prefixes; the individual `.lean` files cited are the importable modules. The roots for this section are `Mathlib.Analysis.Normed.Algebra`, `Mathlib.Topology.Algebra.Module.Spaces.CharacterSpace`, `Mathlib.Analysis.Fourier.FiniteAbelian`, `Mathlib.Analysis.Fourier`, `Mathlib.Analysis.Convolution`, `Mathlib.Analysis.LConvolution`, `Mathlib.MeasureTheory.Group.Convolution`, and `Mathlib.MeasureTheory.Group.FoelnerFilter`.

**Namespaces.** `spectrum`, `quasispectrum`, `AlgHom`, `Subalgebra`, `WeakDual` with nested `CharacterSpace`, `SpectrumRestricts`, `QuasispectrumRestricts`, `NormedSpace`, `NormedAlgebra` with nested `Complex` and `Real`, `Unitization`, `WithLp`, `AddChar`, `ZMod`, `DirichletCharacter`, `MeasureTheory` with nested `Measure`, `IsFoelner` and the additive `IsAddFoelner`, `Real`, `SchwartzMap`, and `Ideal`.

This note records the spectrum and the exponential in a Banach algebra, the finite abelian Fourier analysis, and the convolution algebra of a group. Haar measure itself is the sketch in `Mathlib04.md`. The star-isometric Gelfand duality for commutative C⋆-algebras is section 23.

## Spectrum and spectral radius

The spectrum and resolvent are developed for an element of a complete normed algebra over a normed field. In the non-unital setting the same results use the quasispectrum, and they ask in addition that the scalar field be complete. The spectral radius is the supremum, in the extended nonnegative reals, of the norms of points of the quasispectrum. It may be infinite if the quasispectrum is unbounded, but in a Banach algebra the quasispectrum is bounded. When the algebra is unital, the quasispectrum is the spectrum together with \(0\), and the two radii agree. The resolvent set is open, the spectrum and the quasispectrum are closed, and each lies in the closed disk of radius \(\lVert a\rVert\,\lVert 1\rVert\), or of radius \(\lVert a\rVert\) when \(\lVert 1\rVert = 1\). If the scalar field is a proper metric space, the spectrum and the quasispectrum are compact. The spectral radius is at most the norm. If the quasispectrum over a larger scalar field restricts to a smaller one, the two spectral radii agree (`Analysis/Normed/Algebra/Spectrum.lean`).

Compactness in the non-unital case is obtained by passing to the unitization equipped with the \(\ell^1\) norm \(\lVert(k,a)\rVert = \lVert k\rVert + \lVert a\rVert\) (`Analysis/Normed/Algebra/UnitizationL1.lean`).

Over \(\mathbb{C}\), in a complete normed algebra, the resolvent is differentiable on the resolvent set. Gelfand’s formula: the spectral radius of \(a\) is the limit of \(\lVert a^n\rVert_+^{1/n}\) in the extended nonnegative reals. If the algebra is nontrivial, the spectrum of every element is nonempty, the spectral radius is attained, and polynomials obey the spectral mapping theorem: the spectrum of \(p(a)\) is the image of the spectrum of \(a\) under \(p\) (`Analysis/Normed/Algebra/GelfandFormula.lean`).

## Gelfand–Mazur

For a complete normed algebra over \(\mathbb{C}\) in which the nonzero elements are precisely the units, the scalar map \(\mathbb{C}\to A\) is an algebra isomorphism. Its inverse sends \(a\) to the unique point of the spectrum of \(a\). The file records that this map is an isometry. The hypothesis is a complete normed ring with submultiplicative norm, rather than a normed division ring, so that the theorem applies to a quotient by a maximal ideal (`Analysis/Normed/Algebra/GelfandFormula.lean`).

A second form, for a nontrivial normed \(\mathbb{C}\)-algebra whose norm is multiplicative, gives a \(\mathbb{C}\)-algebra equivalence with \(\mathbb{C}\) and does not ask for completeness. If a normed field is a normed algebra over \(\mathbb{R}\), it is isomorphic as an \(\mathbb{R}\)-algebra either to \(\mathbb{R}\) or to \(\mathbb{C}\) (`Analysis/Normed/Algebra/GelfandMazur.lean`).

## Characters and the Gelfand transform

An algebra homomorphism from a complete normed algebra into its scalar field is continuous. Its operator norm is at most \(\lVert 1\rVert\), and equals \(1\) when \(\lVert 1\rVert = 1\) and the scalar field is nontrivially normed. The character space, the nonzero multiplicative elements of the weak dual, is compact when the scalar field is proper (`Analysis/Normed/Algebra/Basic.lean`, `Analysis/Normed/Algebra/Spectrum.lean`, `Topology/Algebra/Module/Spaces/CharacterSpace.lean`).

The Gelfand transform of a topological algebra is the algebra homomorphism into the continuous scalar functions on the character space given by evaluation. In a commutative complete normed algebra over \(\mathbb{C}\), every maximal ideal determines a character through the quotient and the Gelfand–Mazur theorem, a scalar lies in the spectrum of \(a\) if and only if some character takes that value on \(a\), and the Gelfand transform preserves spectra (`Analysis/CStarAlgebra/GelfandDuality.lean`). The star-isometric equivalence of a commutative unital complex C⋆-algebra with \(C(X)\) is section 23.

If \(S\) is a closed subalgebra of a Banach algebra and \(x\in S\), the frontier of the spectrum of \(x\) computed in \(S\) lies in the spectrum of \(x\) computed in the ambient algebra. When the scalar field is nontrivially normed and the complement of the ambient spectrum is preconnected, the two spectra agree (`Analysis/Normed/Algebra/Spectrum.lean`).

## Unitization norms

Let \(A\) be a non-unital normed algebra over a nontrivially normed field, with regular norm, meaning that left multiplication is an isometric embedding into the bounded operators on \(A\). The unitization then carries the pullback of the product norm along the split multiplication map \((k,a)\mapsto (k,\, k\cdot 1 + L_a)\). This norm satisfies \(\lVert 1\rVert = 1\), the inclusion of \(A\) is an isometry, and the unitization is complete when the scalar field and \(A\) are (`Analysis/Normed/Algebra/Unitization.lean`).

The same unitization with the \(\ell^1\) norm \(\lVert(k,a)\rVert = \lVert k\rVert + \lVert a\rVert\) is a Banach algebra without a regularity hypothesis, and the inclusion of \(A\) is again an isometry (`Analysis/Normed/Algebra/UnitizationL1.lean`). The module commentary identifies the \(\ell^1\) norm as maximal, and the split-multiplication pullback as minimal, among norms on the unitization with \(\lVert 1\rVert = 1\) and isometric inclusion of \(A\). The additive equivalence from the minimal unitization to the product of the scalar field with \(A\), carrying the maximum norm, is Lipschitz and antilipschitz with constant \(2\).

## Exponential and logarithm

The exponential in a topological algebra is the sum of the series \(\sum_n (1/n!)\, x^n\). Where the algebra admits no algebra structure over \(\mathbb{Q}\), the definition returns \(1\). Over \(\mathbb{R}\) or \(\mathbb{C}\), on a normed algebra, the series has infinite radius of convergence. On a complete normed algebra, \(\exp(x+y) = \exp x\cdot\exp y\) whenever \(x\) and \(y\) commute, and hence for every pair when the algebra is commutative. In a complete normed division algebra, \(\exp(-x) = (\exp x)^{-1}\). If the star is continuous, the exponential of a skew-adjoint element is unitary (`Analysis/Normed/Algebra/Exponential.lean`).

For \(\mathbb{R}\) or \(\mathbb{C}\), in a complete normed algebra, the ordinary exponential sends the spectrum of \(a\) into the spectrum of \(\exp a\) (`Analysis/Normed/Algebra/Spectrum.lean`). The resulting maps \(t\mapsto\exp(ta)\) are the norm-continuous groups recorded as related material in section 24.

The logarithm is the series \(\log x = \sum_{n\ge 1} ((-1)^{n+1}/n)\,(x-1)^n\). Where there is no algebra structure over \(\mathbb{Q}\), or the series fails to converge, the definition returns \(0\). The file proves \(\log 1 = 0\), compatibility with the opposite multiplication and with a continuous star, and that the logarithm of a commuting pair remains in a closed subring and commutes. Convergence, analyticity, and the identities \(\exp(\log x) = x\) and \(\log(\exp x) = x\) are left unproved (`Analysis/Normed/Algebra/Logarithm.lean`).

## Finite abelian Fourier analysis

Characters of a finite abelian group, with values in \(\mathbb{R}\) or \(\mathbb{C}\), are orthogonal for the normalized inner product: the inner product of two characters is \(1\) if they agree and \(0\) otherwise. They are linearly independent, and there are at most as many as the group has elements (`Analysis/Fourier/FiniteAbelian/Orthogonality.lean`).

For complex characters the count is exact. The complex characters of a finite abelian group form a basis of the functions from the group to \(\mathbb{C}\). The canonical embedding of the group into the character group of its complex character group is a group isomorphism: this is Pontryagin duality for finite abelian groups. The indexing \(x\mapsto (y\mapsto e^{2\pi i xy/n})\) is a noncanonical isomorphism from \(\mathbb{Z}/n\mathbb{Z}\) onto its complex character group (`Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean`).

On \(\mathbb{Z}/N\mathbb{Z}\), with \(N\neq 0\), and with values in any complex vector space \(E\), the discrete Fourier transform
\[
(\mathcal{F}\Phi)(k) = \sum_{j\bmod N} e^{-2\pi i jk/N}\,\Phi(j)
\]
is a complex-linear equivalence of \(E\)-valued functions. Its inverse is \(N^{-1}\) times \(\mathcal{F}\) evaluated at \(-k\), and \(\mathcal{F}(\mathcal{F}\Phi)(j) = N\,\Phi(-j)\). When \(E\) is a complete normed complex space, this agrees with the integral Fourier transform against counting measure. For a primitive Dirichlet character \(\chi\), \(\mathcal{F}\chi\) is \(\chi^{-1}\), evaluated at \(-k\), times the Gauss sum of \(\chi\) (`Analysis/Fourier/ZMod.lean`).

## Convolution

Multiplicative convolution of measures on a monoid with measurable multiplication is the pushforward of the product measure under multiplication, and the additive convolution is the same construction for addition. Convolution of s-finite measures is associative. Dirac measure at the identity is a unit for s-finite measures. Convolution is commutative when the monoid is commutative and both measures are s-finite. The convolution of two probability measures is a probability measure. If the right factor is absolutely continuous with respect to a left-invariant measure, the convolution is absolutely continuous with respect to that measure (`MeasureTheory/Group/Convolution.lean`).

Convolution of functions uses a continuous bilinear multiplication \(L\) of the values. On an additive group,
\[
(f\star_{[L,\mu]} g)(x) = \int L(f(t),\, g(x-t))\,d\mu(t).
\]
If \(\mu\) is right-invariant, integrable functions convolve to an integrable function, and convolution is associative under the stated integrability and measurability hypotheses. If \(\mu\) is left-invariant and inversion-invariant and \(p,q\) are Hölder conjugates, the convolution of an \(L^p\) function and an \(L^q\) function exists everywhere and satisfies
\[
\lVert (f\star g)(x)\rVert_e \le \lVert L\rVert_e\,\lVert f\rVert_p\,\lVert g\rVert_q.
\]
These are the algebra and Young inequalities for the convolution. The library does not package \(L^1\) as a normed ring under convolution (`Analysis/Convolution.lean`).

For functions with values in the extended nonnegative reals, the Lebesgue-integral convolution is associative when the measure is left-invariant and s-finite and the functions are almost everywhere measurable, and it is commutative when the group is commutative and the measure is also inversion-invariant (`Analysis/LConvolution.lean`).

On a finite-dimensional real inner product space, for integrable functions with values in complete normed complex spaces and a continuous bilinear multiplication \(B\), the Fourier transform turns convolution into that multiplication: \(\mathcal{F}(f_1\star_{[B]} f_2)(\xi) = B(\mathcal{F}f_1(\xi),\,\mathcal{F}f_2(\xi))\). The same identity holds for the convolution of Schwartz functions (`Analysis/Fourier/Convolution.lean`).

## Følner filters

A family of sets \(F\), indexed by a filter, is Følner for a group action on a measure space when the sets are eventually measurable and of finite positive measure, and
\[
\frac{\mu((g\cdot F_i)\,\triangle\, F_i)}{\mu(F_i)}\to 0
\]
for every group element \(g\). The same definition is given for an additive action. If the measure is invariant and the filter is nontrivial, the ultralimit of densities along \(F\) is a finitely additive probability, invariant under the action. The library takes this existence as the meaning of amenability of the action. A definition of amenability for groups, as opposed to actions, is explicitly left unchosen (`MeasureTheory/Group/FoelnerFilter.lean`).

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

The Banach-algebra logarithm series is developed, and the exponential and \(\log(1+x)\) are proved inverse on explicit neighbourhoods of zero in a real Banach algebra ([logarithm series](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Normed/Algebra/LogOneAdd/Basic.lean), [local inverse identities](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Normed/Algebra/LogOneAdd/Inverse.lean)). Thus the absence of logarithm-series convergence and local exponential/logarithm identities is no longer a gap across both libraries.

TauCeti also proves Peter–Weyl for compact groups, constructing the normalized irreducible matrix coefficients as an \(L^2\) Hilbert basis ([Peter–Weyl](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/RepresentationTheory/Compact/PeterWeyl.lean); Section 28). Its positive-definite-function and Bochner theory is relevant to commutative harmonic analysis, but a general nonfinite Pontryagin duality theorem was not located.

The local Baker–Campbell–Hausdorff map is defined analytically by \(\log(\exp x\exp y)\) near \((0,0)\), with its exponential identity, uniqueness as a germ, and naturality under continuous algebra homomorphisms ([local BCH](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Normed/Algebra/BCH/Local.lean)). This result does not assert a full formal Lie-series coefficient expansion.

## Topics of Section 20 not found in either inspected library

- The general identification of an archimedean normed field with a normed \(\mathbb{R}\)-algebra, which the real Gelfand–Mazur file leaves as future work. Ostrowski’s classification of nontrivial real-valued absolute values on \(\mathbb{Q}\), up to equivalence, **is** proved in `NumberTheory/Ostrowski.lean` (`Rat.AbsoluteValue.equiv_real_or_padic`).
- An \(L^1\) Banach-algebra structure built from convolution. Associativity and the Young bound are proved.
- Pontryagin duality for groups that are not finite.
