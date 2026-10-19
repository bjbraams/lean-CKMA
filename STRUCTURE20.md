# Structure 20: Banach algebras

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS20.md); [bibliographical scope](CKMA-bib.md#ckma-20); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.Normed.Ring.Units`, `Mathlib.Algebra.Algebra.Spectrum`, `Mathlib.Analysis.Normed.Algebra`, `Mathlib.RingTheory.Jacobson`, `Mathlib.RingTheory.SimpleModule`, `Mathlib.Topology.Algebra.Module.Spaces.CharacterSpace`, `Mathlib.Analysis.CStarAlgebra.GelfandDuality`, `Mathlib.Topology.ContinuousMap.StoneWeierstrass`, `Mathlib.Topology.ContinuousMap.Ideals`, `Mathlib.Analysis.Fourier.FiniteAbelian`, `Mathlib.Analysis.Fourier`, `Mathlib.Analysis.Convolution`, `Mathlib.Analysis.LConvolution`, `Mathlib.MeasureTheory.Group.Convolution`, `Mathlib.MeasureTheory.Group.FoelnerFilter`.

**Namespaces.** `spectrum`, `quasispectrum`, `Units`, `NormedRing`, `AlgHom`, `Subalgebra`, `WeakDual` with nested `CharacterSpace`, `SpectrumRestricts`, `QuasispectrumRestricts`, `NormedSpace`, `NormedAlgebra` with nested `Complex` and `Real`, `Unitization`, `WithLp`, `Ideal`, `ContinuousMap`, `AddChar`, `ZMod`, `DirichletCharacter`, `MeasureTheory` with nested `Measure`, `IsFoelner` and the additive `IsAddFoelner`, `Real`, and `SchwartzMap`.

## Invertibility, spectra, and holomorphic calculus

[Mathematical scope](SYNOPSIS20.md#invertibility-spectra-and-holomorphic-calculus).

### Mathlib

**Neumann series and the group of units.**

In a normed ring in which geometric series are summable (for instance a complete one), \(\sum_n x^n\) is a two-sided inverse of \(1-x\) when \(\lVert x\rVert<1\) (`geom_series_mul_neg`, `mul_neg_geom_series`, `Analysis/SpecificLimits/Normed.lean`). In a complete normed ring the units form an open set (`Units.isOpen`), ring inversion is continuous at every unit (`NormedRing.inverse_continuousAt`), with explicit first- and higher-order expansions (`NormedRing.inverse_add_norm_diff_first_order`, `NormedRing.inverse_add_norm_diff_nth_order`), and it is analytic at every unit (`analyticAt_inverse`) (`Analysis/Normed/Ring/Units.lean`, `Analysis/Analytic/Constructions.lean`). Maximal ideals are closed (`Ideal.IsMaximal.isClosed`).

**Spectrum and spectral radius.**

The spectrum and resolvent are developed for an element of a complete normed algebra over a normed field. In the non-unital setting the same results use the quasispectrum, and they ask in addition that the scalar field be complete. The spectral radius is the supremum, in the extended nonnegative reals, of the norms of points of the quasispectrum. It may be infinite if the quasispectrum is unbounded, but in a Banach algebra the quasispectrum is bounded. When the algebra is unital, the quasispectrum is the spectrum together with \(0\), and the two radii agree. The resolvent set is open, the spectrum and the quasispectrum are closed, and each lies in the closed disk of radius \(\lVert a\rVert\,\lVert 1\rVert\), or of radius \(\lVert a\rVert\) when \(\lVert 1\rVert = 1\). If the scalar field is a proper metric space, the spectrum and the quasispectrum are compact. The spectral radius is at most the norm. If the quasispectrum over a larger scalar field restricts to a smaller one, the two spectral radii agree (`Analysis/Normed/Algebra/Spectrum.lean`).

Compactness in the non-unital case is obtained by passing to the unitization equipped with the \(\ell^1\) norm \(\lVert(k,a)\rVert = \lVert k\rVert + \lVert a\rVert\) (`Analysis/Normed/Algebra/UnitizationL1.lean`).

Over \(\mathbb{C}\), in a complete normed algebra, the resolvent is differentiable on the resolvent set. Gelfand’s formula: the spectral radius of \(a\) is the limit of \(\lVert a^n\rVert_+^{1/n}\) in the extended nonnegative reals. If the algebra is nontrivial, the spectrum of every element is nonempty, the spectral radius is attained, and polynomials obey the spectral mapping theorem: the spectrum of \(p(a)\) is the image of the spectrum of \(a\) under \(p\) (`Analysis/Normed/Algebra/GelfandFormula.lean`).

In any seminormed ring the Gelfand radius \(\rho(a)=\lim_k\lVert a^k\rVert^{1/k}\) is defined, the limit existing by subadditivity of \(k\mapsto\log\lVert a^k\rVert\). It satisfies \(\rho(a)\le\lVert a\rVert\), \(\rho(a^n)=\rho(a)^n\) when \(\lVert1\rVert=1\), \(\lVert a^n\rVert\le C r^n\) for every \(r>\rho(a)\), and \(\rho(a+b)\le\rho(a)+\rho(b)\), \(\rho(ab)\le\rho(a)\rho(b)\) for commuting \(a,b\) (`Analysis/Normed/Algebra/GelfandRadius.lean`, `gelfandRadius`, `Commute.gelfandRadius_add_le`, `Commute.gelfandRadius_mul_le`). In a complex Banach algebra it equals the spectral radius (`spectralRadius_eq_gelfandRadius`), so the spectral radius is subadditive and submultiplicative on commuting pairs.

The map \(a\mapsto\sigma(a)\) is upper hemicontinuous, for the spectrum over a proper scalar field and for the quasispectrum (`upperHemicontinuous_spectrum`, `upperHemicontinuous_quasispectrum`, `Analysis/Normed/Algebra/Spectrum.lean`); this is Newburgh's upper semicontinuity. The algebraic resolvent identity is the second one, \(R(r,a)-R(r,b)=R(r,a)(a-b)R(r,b)\) (`spectrum.resolvent_sub_resolvent`, `Algebra/Algebra/Spectrum/Basic.lean`); the first resolvent identity of result 4 is the case \(b=a+(r-s)1\). The Gelfand radius bounds \(\rho(a)\le\lVert a^n\rVert^{1/n}\) for every \(n\ge1\) (`gelfandRadius_le_norm_pow`) give the infimum form of the spectral radius formula.

**Change of ambient algebra.**

If \(S\) is a closed subalgebra of a Banach algebra and \(x\in S\), the frontier of the spectrum of \(x\) computed in \(S\) lies in the spectrum of \(x\) computed in the ambient algebra. When the scalar field is nontrivially normed and the complement of the ambient spectrum is preconnected, the two spectra agree (`Analysis/Normed/Algebra/Spectrum.lean`). For C⋆-subalgebras the spectra always agree (`StarSubalgebra.spectrum_eq`, spectral permanence; Section 23).

**Gelfand–Mazur.**

For a complete normed algebra over \(\mathbb{C}\) in which the nonzero elements are precisely the units, the scalar map \(\mathbb{C}\to A\) is an algebra isomorphism. Its inverse sends \(a\) to the unique point of the spectrum of \(a\). The file records that this map is an isometry. The hypothesis is a complete normed ring with submultiplicative norm, rather than a normed division ring, so that the theorem applies to a quotient by a maximal ideal (`Analysis/Normed/Algebra/GelfandFormula.lean`).

A second form, for a nontrivial normed \(\mathbb{C}\)-algebra whose norm is multiplicative, gives a \(\mathbb{C}\)-algebra equivalence with \(\mathbb{C}\) and does not ask for completeness. If a normed field is a normed algebra over \(\mathbb{R}\), it is isomorphic as an \(\mathbb{R}\)-algebra either to \(\mathbb{R}\) or to \(\mathbb{C}\) (`Analysis/Normed/Algebra/GelfandMazur.lean`).

**Unitization norms.**

Let \(A\) be a non-unital normed algebra over a nontrivially normed field, with regular norm, meaning that left multiplication is an isometric embedding into the bounded operators on \(A\). The unitization then carries the pullback of the product norm along the split multiplication map \((k,a)\mapsto (k,\, k\cdot 1 + L_a)\). This norm satisfies \(\lVert 1\rVert = 1\), the inclusion of \(A\) is an isometry, and the unitization is complete when the scalar field and \(A\) are (`Analysis/Normed/Algebra/Unitization.lean`).

The same unitization with the \(\ell^1\) norm \(\lVert(k,a)\rVert = \lVert k\rVert + \lVert a\rVert\) is a Banach algebra without a regularity hypothesis, and the inclusion of \(A\) is again an isometry (`Analysis/Normed/Algebra/UnitizationL1.lean`). The module commentary identifies the \(\ell^1\) norm as maximal, and the split-multiplication pullback as minimal, among norms on the unitization with \(\lVert 1\rVert = 1\) and isometric inclusion of \(A\). The additive equivalence from the minimal unitization to the product of the scalar field with \(A\), carrying the maximum norm, is Lipschitz and antilipschitz with constant \(2\).

**Exponential and logarithm.**

The exponential in a topological algebra is the sum of the series \(\sum_n (1/n!)\, x^n\). Where the algebra admits no algebra structure over \(\mathbb{Q}\), the definition returns \(1\). Over \(\mathbb{R}\) or \(\mathbb{C}\), on a normed algebra, the series has infinite radius of convergence. On a complete normed algebra, \(\exp(x+y) = \exp x\cdot\exp y\) whenever \(x\) and \(y\) commute, and hence for every pair when the algebra is commutative. In a complete normed division algebra, \(\exp(-x) = (\exp x)^{-1}\). If the star is continuous, the exponential of a skew-adjoint element is unitary (`Analysis/Normed/Algebra/Exponential.lean`).

For \(\mathbb{R}\) or \(\mathbb{C}\), in a complete normed algebra, the ordinary exponential sends the spectrum of \(a\) into the spectrum of \(\exp a\) (`Analysis/Normed/Algebra/Spectrum.lean`). The resulting maps \(t\mapsto\exp(ta)\) are the norm-continuous groups recorded as related material in section 24.

The logarithm is the series \(\log x = \sum_{n\ge 1} ((-1)^{n+1}/n)\,(x-1)^n\). Where there is no algebra structure over \(\mathbb{Q}\), or the series fails to converge, the definition returns \(0\). The file proves \(\log 1 = 0\), compatibility with the opposite multiplication and with a continuous star, and that the logarithm of a commuting pair remains in a closed subring and commutes. Sources: `Analysis/Normed/Algebra/Logarithm.lean`.

**Jacobson radical and density.**

The Jacobson radical of a ring is the intersection of its maximal left ideals (`Ideal.jacobson`, with the two-sided version `TwoSidedIdeal.jacobson`); membership is characterized algebraically by left invertibility of the elements \(1+yx\) (`Ideal.mem_jacobson_iff`, and `Ideal.mem_jacobson_bot` in the commutative case) (`RingTheory/Jacobson/Ideal.lean`). Its closedness in a Banach algebra and the relation with quasinilpotence are not formalized. The algebraic Jacobson density theorem is proved for semisimple modules: every endomorphism commuting with \(\operatorname{End}_R(M)\) agrees with the action of a ring element on any finite set (`jacobson_density`, `RingTheory/SimpleModule/Basic.lean`). The Banach-algebra input that the commutant of an irreducible module is \(\mathbb C\) is not formalized.

### TauCeti

The Banach-algebra logarithm series is developed: in a Banach algebra over a characteristic-zero normed field its radius of convergence is at least one, it represents Mathlib's `NormedSpace.log` on the unit ball about \(1\), and \(\log(1+u)-(u-u^2/2)=O(\lVert u\rVert^3)\). In a complete normed \(\mathbb Q\)-algebra, \(\log(\exp x)=x\) near \(0\) and \(\exp(\log x)=x\) near \(1\), and continuous ring homomorphisms commute with \(\log\) on the unit ball about \(1\) ([logarithm series](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Algebra/Logarithm/Basic.lean), [local inverse identities](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Algebra/Logarithm/Inverse.lean), [naturality](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Algebra/Logarithm/Naturality.lean)). In a real Banach algebra, every element near \(1\) has a unique square root near \(1\), depending smoothly on the element ([square roots near the identity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Algebra/SquareRoot.lean), `TauCeti.sqrtNearOne`).

The local Baker–Campbell–Hausdorff map is defined analytically by \(\log(\exp x\exp y)\) near \((0,0)\), with its exponential identity, uniqueness as a germ, and naturality under continuous algebra homomorphisms ([local BCH](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Algebra/BCH/Local.lean)). This result does not assert a full formal Lie-series coefficient expansion. In a normed ring with integer-homogeneous norm, the only subgroup of units inside the closed ball of radius \(1/2\) about \(1\) is trivial ([no small subgroups](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Algebra/NoSmallSubgroups.lean)).

**Synopsis entries.** Covered: 20.1–20.4, 20.9 (Mathlib). Partly covered: 20.5 (polynomial spectral mapping over \(\mathbb C\); the rational case is absent), 20.6 (complex case for complete algebras whose nonzero elements are units, or for multiplicative norms without completeness; over \(\mathbb R\) only normed fields, giving \(\mathbb R\) or \(\mathbb C\), so \(\mathbb H\) is absent), 20.10 (the algebraic Jacobson radical and its unit characterization; closedness, semisimple quotient, and quasinilpotence are absent), 20.65 (algebraic density theorem for semisimple modules; the commutant statement and the matrix-algebra corollary are absent). Not covered: 20.7, 20.8, 20.64.

## Numerical range and Hermitian elements

[Mathematical scope](SYNOPSIS20.md#numerical-range-and-hermitian-elements).

**Synopsis entries.** Not covered: 20.66–20.68.

## Characters and the Gelfand representation

[Mathematical scope](SYNOPSIS20.md#characters-and-the-gelfand-representation).

### Mathlib

An algebra homomorphism from a complete normed algebra into its scalar field is continuous. Its operator norm is at most \(\lVert 1\rVert\), and equals \(1\) when \(\lVert 1\rVert = 1\) and the scalar field is nontrivially normed. The character space, the nonzero multiplicative elements of the weak dual, is compact when the scalar field is proper (`Analysis/Normed/Algebra/Basic.lean`, `Analysis/Normed/Algebra/Spectrum.lean`, `Topology/Algebra/Module/Spaces/CharacterSpace.lean`).

The Gelfand transform of a topological algebra is the algebra homomorphism into the continuous scalar functions on the character space given by evaluation. In a commutative complete normed algebra over \(\mathbb{C}\), every maximal ideal determines a character through the quotient and the Gelfand–Mazur theorem, a scalar lies in the spectrum of \(a\) if and only if some character takes that value on \(a\), and the Gelfand transform preserves spectra (`Analysis/CStarAlgebra/GelfandDuality.lean`). The star-isometric equivalence of a commutative unital complex C⋆-algebra with \(C(X)\) is section 23. The character attached to a maximal ideal is `Ideal.toCharacterSpace`, which vanishes on the ideal (`Ideal.toCharacterSpace_apply_eq_zero_of_mem`). The non-unital correspondence with maximal modular ideals and the locally compact character space of a non-unital algebra are not formalized.

### TauCeti

For a unital commutative C⋆-algebra \(A\) with character space \(\Delta\), every linear functional nonnegative on all \(a^\ast a\) is integration \(f(a)=\int_\Delta\omega(a)\,d\mu(\omega)\) against a finite inner regular positive measure; for a closed commutative star algebra of operators on a Hilbert space this applies to each vector functional \(a\mapsto\langle\xi,a\xi\rangle\), and the measure computes \(\lVert a\xi\rVert^2\) as the \(L^2(\mu)\) norm of the Gelfand transform ([character-space measures](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/CStarAlgebra/CharacterSpaceMeasure.lean), `LinearMap.exists_isFiniteMeasure_integral_characterSpace_eq`).

An algebra homomorphism from a noetherian nonarchimedean Banach algebra into a finite-dimensional topological algebra is automatically continuous ([automatic continuity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Algebra/AutomaticContinuity.lean)). This is a nonarchimedean automatic-continuity result; Shilov's and Johnson's theorems of result 18 are not formalized.

**Synopsis entries.** Covered: 20.11 (Mathlib). Partly covered: 20.12 (unital case only), 20.13 (unital case: compact character space and the Gelfand transform into \(C(\Delta(A))\)), 20.14 (unital case: the spectrum is the range of the Gelfand transform). Not covered: 20.15–20.17, 20.26, 20.18, 20.69, 20.19, 20.21.

## Uniform algebras, boundaries, and representing measures

[Mathematical scope](SYNOPSIS20.md#uniform-algebras-boundaries-and-representing-measures).

### Mathlib

The Stone–Weierstrass theorem is proved for compact Hausdorff \(X\): a subalgebra of \(C(X,\mathbb R)\) separating points is dense (`ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`), and a conjugation-closed point-separating subalgebra of \(C(X,\mathbb K)\), \(\mathbb K=\mathbb R\) or \(\mathbb C\), is dense (`ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`) (`Topology/ContinuousMap/StoneWeierstrass.lean`). Uniform algebras, Shilov boundaries, and representing measures are not formalized.

**Synopsis entries.** Covered: 20.22 (Mathlib). Not covered: 20.23–20.25, 20.27, 20.28.

## Regularity, ideals, and spectral synthesis

[Mathematical scope](SYNOPSIS20.md#regularity-ideals-and-spectral-synthesis).

### Mathlib

For compact Hausdorff \(X\) and \(\mathbb K=\mathbb R\) or \(\mathbb C\), every closed ideal of \(C(X,\mathbb K)\) is the ideal of functions vanishing on a closed set, and the closed ideals correspond to open subsets of \(X\) by a Galois insertion (`ContinuousMap.idealOfSet`, `ContinuousMap.idealOfSet_ofIdeal_isClosed`, `ContinuousMap.idealOpensGI`, `Topology/ContinuousMap/Ideals.lean`). The quotient identification with \(C(F)\), the locally compact case \(C_0(K)\), hulls and kernels in general algebras, and spectral synthesis are not formalized.

**Synopsis entries.** Partly covered: 20.31 (compact \(K\): closed ideals are the ideals of closed sets; the quotient isometry and \(C_0(K)\) are absent). Not covered: 20.30, 20.32–20.36.

## Convolution algebras and Fourier transforms

[Mathematical scope](SYNOPSIS20.md#convolution-algebras-and-fourier-transforms).

### Mathlib

**Finite abelian Fourier analysis.**

Characters of a finite abelian group, with values in \(\mathbb{R}\) or \(\mathbb{C}\), are orthogonal for the normalized inner product: the inner product of two characters is \(1\) if they agree and \(0\) otherwise. They are linearly independent, and there are at most as many as the group has elements (`Analysis/Fourier/FiniteAbelian/Orthogonality.lean`).

For complex characters the count is exact. The complex characters of a finite abelian group form a basis of the functions from the group to \(\mathbb{C}\). The canonical embedding of the group into the character group of its complex character group is a group isomorphism: this is Pontryagin duality for finite abelian groups. The indexing \(x\mapsto (y\mapsto e^{2\pi i xy/n})\) is a noncanonical isomorphism from \(\mathbb{Z}/n\mathbb{Z}\) onto its complex character group (`Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean`).

On \(\mathbb{Z}/N\mathbb{Z}\), with \(N\neq 0\), and with values in any complex vector space \(E\), the discrete Fourier transform
\[
(\mathcal{F}\Phi)(k) = \sum_{j\bmod N} e^{-2\pi i jk/N}\,\Phi(j)
\]
is a complex-linear equivalence of \(E\)-valued functions. Its inverse is \(N^{-1}\) times \(\mathcal{F}\) evaluated at \(-k\), and \(\mathcal{F}(\mathcal{F}\Phi)(j) = N\,\Phi(-j)\). When \(E\) is a complete normed complex space, this agrees with the integral Fourier transform against counting measure. For a primitive Dirichlet character \(\chi\), \(\mathcal{F}\chi\) is \(\chi^{-1}\), evaluated at \(-k\), times the Gauss sum of \(\chi\) (`Analysis/Fourier/ZMod.lean`).

**Convolution.**

Multiplicative convolution of measures on a monoid with measurable multiplication is the pushforward of the product measure under multiplication, and the additive convolution is the same construction for addition. Convolution of s-finite measures is associative. Dirac measure at the identity is a unit for s-finite measures. Convolution is commutative when the monoid is commutative and both measures are s-finite. The convolution of two probability measures is a probability measure. If the right factor is absolutely continuous with respect to a left-invariant measure, the convolution is absolutely continuous with respect to that measure (`MeasureTheory/Group/Convolution.lean`).

Convolution of functions uses a continuous bilinear multiplication \(L\) of the values. On an additive group,
\[
(f\star_{[L,\mu]} g)(x) = \int L(f(t),\, g(x-t))\,d\mu(t).
\]
If \(\mu\) is right-invariant, integrable functions convolve to an integrable function, and convolution is associative under the stated integrability and measurability hypotheses. If \(\mu\) is left-invariant and inversion-invariant and \(p,q\) are Hölder conjugates, the convolution of an \(L^p\) function and an \(L^q\) function exists everywhere and satisfies
\[
\lVert (f\star g)(x)\rVert_e \le \lVert L\rVert_e\,\lVert f\rVert_p\,\lVert g\rVert_q.
\]
This is the endpoint \(r=\infty\) of Young's inequality, obtained from Hölder's inequality. TauCeti's Schur test gives the case \(\|f\star g\|_p\le\|f\|_1\|g\|_p\) for nonnegative functions (Section 11). Sources: `Analysis/Convolution.lean`.

Discrete convolution over a monoid, through a bilinear map of the values, is defined with its unit and summability conditions; it is the multiplication of the group algebra in the \(\ell^1\) setting (`Topology/Algebra/InfiniteSum/DiscreteConvolution.lean`).

For functions with values in the extended nonnegative reals, the Lebesgue-integral convolution is associative when the measure is left-invariant and s-finite and the functions are almost everywhere measurable, and it is commutative when the group is commutative and the measure is also inversion-invariant (`Analysis/LConvolution.lean`).

On a finite-dimensional real inner product space, for integrable functions with values in complete normed complex spaces and a continuous bilinear multiplication \(B\), the Fourier transform turns convolution into that multiplication: \(\mathcal{F}(f_1\star_{[B]} f_2)(\xi) = B(\mathcal{F}f_1(\xi),\,\mathcal{F}f_2(\xi))\). The same identity holds for the convolution of Schwartz functions (`Analysis/Fourier/Convolution.lean`).

### TauCeti

For a strongly continuous, uniformly bounded representation \(\pi\) of a topological group, the integrated form \(\pi(f)=\int f(g)\pi(g)\,d\mu(g)\) is a continuous linear map \(L^1(G)\to\mathcal L(E)\) with \(\lVert\pi(f)\rVert\le C\lVert f\rVert_1\), turning convolution into composition and, for unitary \(\pi\) and inversion-invariant \(\mu\), the involution \(f^\ast(g)=\overline{f(-g)}\) into the adjoint ([integrated form](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/RepresentationTheory/Continuous/Integrated/Basic.lean)). For abelian \(G\), a character of a complete star algebra containing the integrated operators and nonzero on one of them determines a unique continuous unitary character \(\chi\) of \(G\) with \(\omega(\pi(g)\pi(f))=\chi(g)\,\omega(\pi(f))\), and \(\omega\mapsto\chi\) is continuous ([detected characters](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/RepresentationTheory/Continuous/Pontryagin/Basic.lean), [continuity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/RepresentationTheory/Continuous/Pontryagin/Continuity.lean)). This is the Gelfand-theoretic route to the cyclic SNAG theorem: for a strongly continuous unitary representation of a locally compact abelian group, each diagonal matrix coefficient \(g\mapsto\langle\xi,\pi(g)\xi\rangle\) is the Fourier–Stieltjes transform of a finite inner regular measure on the Pontryagin dual ([cyclic SNAG theorem](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Pontryagin/StronglyContinuous.lean), `ContRepresentation.exists_pontryaginMeasureTransform_eq_inner`).

Bochner's theorem holds on every locally compact abelian group \(G\), without countability assumptions: a positive-definite function continuous at \(0\) is the Fourier–Stieltjes transform \(\varphi(g)=\int\chi(g)\,d\mu(\chi)\) of a unique finite inner regular positive measure on \(\widehat G\), and conversely such transforms are continuous and positive definite; on discrete groups no continuity hypothesis is needed ([Bochner on LCA groups](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Bochner/LocallyCompactGroup.lean), [discrete groups](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Bochner/DiscreteGroup.lean), [uniqueness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Pontryagin/Uniqueness.lean)). Convolution with an integrable kernel on a finite-dimensional real normed space with Haar measure is a bounded operator on \(L^p\), \(1\le p<\infty\), with \(\lVert k\star f\rVert_p\le\lVert k\rVert_1\lVert f\rVert_p\) and \((k_1\star k_2)\star f=k_1\star(k_2\star f)\) ([convolution on \(L^p\)](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/Lp/Convolution.lean)); smooth approximate identities converge strongly to the identity on these \(L^p\) spaces, and every neighbourhood of the identity of a compact group carries a nonnegative symmetric unit-mass mollifying kernel ([\(L^p\) approximate identities](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/Lp/ApproximateIdentity.lean), [compact groups](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/RepresentationTheory/Compact/ApproximateIdentity.lean)).

TauCeti also proves Peter–Weyl for compact groups, constructing the normalized irreducible matrix coefficients as an \(L^2\) Hilbert basis ([Peter–Weyl](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/RepresentationTheory/Compact/PeterWeyl.lean); Section 28).

**Synopsis entries.** Partly covered: 20.37 (TauCeti: approximate identities acting strongly on \(L^p(\mathbb R^n)\), including \(p=1\), and mollifying kernels on compact groups; the Banach-algebra structure of \(L^1(G)\) and its embedding in \(M(G)\) are not built), 20.38 (convolution theorem \(\widehat{f*g}=\widehat f\,\widehat g\) on finite-dimensional real inner-product spaces, and Pontryagin duality for finite abelian groups; the identification \(\Delta(L^1(G))\cong\widehat G\) is absent). Not covered: 20.40–20.44, 20.48, 20.45, 20.46.

## Approximate identities, modules, and derivations

[Mathematical scope](SYNOPSIS20.md#approximate-identities-modules-and-derivations).

**Synopsis entries.** Not covered: 20.47, 20.49.

## Amenability and its harmonic-analytic characterizations

[Mathematical scope](SYNOPSIS20.md#amenability-and-its-harmonic-analytic-characterizations).

### Mathlib

A family of sets \(F\), indexed by a filter, is Følner for a group action on a measure space when the sets are eventually measurable and of finite positive measure, and
\[
\frac{\mu((g\cdot F_i)\,\triangle\, F_i)}{\mu(F_i)}\to 0
\]
for every group element \(g\). The same definition is given for an additive action. If the measure is invariant and the filter is nontrivial, the ultralimit of densities along \(F\) is a finitely additive probability, invariant under the action. The library takes this existence as the meaning of amenability of the action. A definition of amenability for groups, as opposed to actions, is explicitly left unchosen (`MeasureTheory/Group/FoelnerFilter.lean`). This is supporting material: amenable Banach algebras, amenable locally compact groups, and the Fourier algebra are not defined.

**Synopsis entries.** Not covered: 20.50–20.56, 20.58, 20.60.

## Bidual multiplication and weak compactness

[Mathematical scope](SYNOPSIS20.md#bidual-multiplication-and-weak-compactness).

**Synopsis entries.** Not covered: 20.61–20.63.
