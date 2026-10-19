# Structure 25: Integral equations and classical operator methods

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS25.md); [bibliographical scope](CKMA-bib.md#ckma-25); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative`, `Mathlib.Analysis.Normed.Operator.Fredholm`, `Mathlib.Analysis.Normed.Ring.Units`, `Mathlib.Analysis.SpecificLimits.Normed`, `Mathlib.Analysis.InnerProductSpace.Spectrum`, `Mathlib.Analysis.InnerProductSpace.Reproducing`, `Mathlib.Analysis.InnerProductSpace.LaxMilgram`, `Mathlib.Analysis.ODE`.

**Namespaces.** The compact-operator Fredholm alternative uses `IsCompactOperator`, Fredholm operators use `ContinuousLinearMap.IsFredholm`, inversion in normed rings uses `NormedRing` and `Units`, reproducing kernels use `RKHS`, and Lax–Milgram uses `IsCoercive`. The Picard–Lindelöf predicate is `IsPicardLindelof`. TauCeti's declarations lie mainly in `TauCeti`, `ContinuousLinearMap`, `IsCompactOperator`, `HilbertBasis`, `IsCoercive`, and `LinearMap`.

## Kernel operators and elementary solution methods

[Mathematical scope](SYNOPSIS25.md#kernel-operators-and-elementary-solution-methods).

### Mathlib

In a complete normed ring, \(1-x\) is invertible for \(\|x\|<1\), with inverse the norm-convergent Neumann series (`Units.oneSub`, `geom_series_eq_inverse`, `hasSum_geom_series_inverse` in `Analysis/SpecificLimits/Normed.lean`; `NormedRing.inverse_one_sub` in `Analysis/Normed/Ring/Units.lean`); applied to the algebra of bounded operators this is 25.6 under the norm condition. The spectral-radius form follows from Gelfand's formula (`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` in `Analysis/Normed/Algebra/GelfandFormula.lean`) but is not stated as a Neumann-series theorem.

**Supporting operator constructions.** Vector-valued reproducing kernel Hilbert spaces are defined, the kernel of such a space is positive semidefinite (`RKHS.posSemidef_kernel`), and conversely every positive semidefinite kernel is the kernel of a constructed RKHS (`RKHS.kernel_ofKernel`, essentially Moore's theorem), in `Analysis/InnerProductSpace/Reproducing.lean`. This is not Mercer's theorem.

### TauCeti

Schur's test is proved for a jointly measurable nonnegative kernel on \(s\)-finite measure spaces whose row integrals are bounded by \(A\) and column integrals by \(B\): for \(1\le p<\infty\) its integral operator satisfies the \(L^p\) estimate with constant \(A^{1-1/p}B^{1/p}\) (`TauCeti.lintegral_rpow_lintegral_mul_le`); \(p=2\) gives \(\sqrt{AB}\), and a signed kernel is handled through \(|k|\). More generally, for \(1\le p\le q\) and \(1/p+1/r=1+1/q\), the same bounds on the row and column integrals of \(k^r\) give an \(L^p\to L^q\) bound with constant \(A^{1-1/p}B^{1/q}\) (`TauCeti.lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq`, Young's inequality for integral operators, applicable to weakly singular kernels on bounded sets). The formal statements are inequalities of lower Lebesgue integrals, with the bounds required almost everywhere ([Schur's test](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/SchurTest.lean)). Boundedness of weakly singular kernels thus follows; their compactness (25.4) is not proved.

The Hilbert–Schmidt norm of a bounded operator between Hilbert spaces is defined by \(\sum_i\|Tb_i\|^2\) in a Hilbert basis (`ContinuousLinearMap.hilbertSchmidtNorm`); it is basis-independent, invariant under adjoints, dominates the operator norm, satisfies \(\|ATB\|_{HS}\le\|A\|\,\|T\|_{HS}\|B\|\), and is invariant under left composition with isometries and right composition with coisometries ([Hilbert–Schmidt norm](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/HilbertSchmidt/Basic.lean), [isometric invariance](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/HilbertSchmidt/Isometry.lean)). Operators of finite Hilbert–Schmidt norm correspond to \(\ell^2\) families of columns and are compact (`HilbertBasis.range_columnOperator`, [columns and compactness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/HilbertSchmidt/Columns.lean)). The identification of an integral operator with \(L^2\) kernel as Hilbert–Schmidt with \(\|K\|_{S^2}=\|k\|_{L^2}\) is not proved.

For a continuous kernel \(k\) on a compact group, the convolution operator \(f\mapsto\int k(xy^{-1})f(y)\,dy\) maps \(L^2(G)\) boundedly into \(C(G)\), is compact on \(L^2(G)\), and is self-adjoint for symmetric kernels (`TauCeti.isCompactOperator_convolutionOperator`, `TauCeti.isSelfAdjoint_convolutionOperator`, [convolution operators](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/RepresentationTheory/Compact/Convolution.lean)). This is a special case of 25.1, for convolution kernels with Haar measure.

**Synopsis entries.** Covered: 25.2 (TauCeti). Partly covered: 25.1 (convolution kernels on compact groups only), 25.3 (abstract Hilbert–Schmidt norm and compactness; not the kernel identification), 25.6 (the condition \(|\lambda|\|K\|<1\); the spectral-radius condition only through Gelfand's formula). Not covered: 25.4, 25.5, 25.7, 25.8.

## Fredholm theory and spectral expansions

[Mathematical scope](SYNOPSIS25.md#fredholm-theory-and-spectral-expansions).

### Mathlib

The Fredholm alternative for a compact operator on a Banach space is Section 21: if \(T\) is compact and \(\mu\neq 0\), then \(\mu\) is an eigenvalue or \(\mu\) is in the resolvent set (`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`), and the nonzero spectrum consists exactly of the nonzero eigenvalues (`IsCompactOperator.hasEigenvalue_iff_mem_spectrum`), in `Analysis/Normed/Operator/Compact/FredholmAlternative.lean` (the older module `Analysis/Normed/Operator/FredholmAlternative.lean` is deprecated). Thus the noninvertible parameters \(\lambda\neq0\) of \(I-\lambda K\) are the reciprocals of the nonzero eigenvalues; isolation and finiteness of algebraic multiplicity are not proved there.

The group of units of a complete normed ring is open and inversion is continuous on it (`Units.isOpen`, `NormedRing.inverse_continuousAt` in `Analysis/Normed/Ring/Units.lean`); in the algebra of bounded operators this is the stability statement 25.15.

For a compact self-adjoint operator on a Hilbert space the eigenspaces have trivial joint orthogonal complement and the eigenspaces at nonzero eigenvalues are finite-dimensional (`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`, `ContinuousLinearMap.finite_dimensional_eigenspace` in `Analysis/InnerProductSpace/Spectrum.lean`).

**Supporting operator constructions.** Fredholm operators between Hausdorff topological vector spaces over a complete nontrivially normed field are defined as strict maps with closed finite-codimensional range and complemented finite-dimensional kernel (`ContinuousLinearMap.IsFredholm` in `Analysis/Normed/Operator/Fredholm/Basic.lean`). Between Banach spaces the Fredholm operators form an open set on which the index is locally constant (`isOpen_setOfPred_isFredholm`, `index_continuousOn_isFredholm` in `Analysis/Normed/Operator/Fredholm/Open.lean`).

### TauCeti

For a compact operator \(K\) on a Banach space, \(I-K\) has finite-dimensional kernel, closed range and finite-dimensional cokernel ([Riesz theory](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Operator/Compact/RieszTheory.lean)), so it is Fredholm of index zero (`TauCeti.isFredholm_one_sub`, `ContinuousLinearMap.index_one_sub_eq_zero`, [compact perturbations](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fredholm/CompactPerturbation.lean)). Every finite stage \(\ker(T-\mu)^n\) of the generalized eigenspace of a compact operator at \(\mu\neq0\) is finite-dimensional (`IsCompactOperator.finiteDimensional_genEigenspace_nat`, [eigenspaces](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Operator/Compact/Eigenspace.lean)); stabilization of the chain, that is, finite algebraic multiplicity, is not stated separately. A compact self-adjoint operator on a Hilbert space has an orthonormal basis of eigenvectors (`ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector`, [eigenbases](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Spectrum.lean)); the componentwise solution of \((I-\lambda K)u=f\) is not written out.

For a bounded coercive form \(B\) on a real Hilbert space \(V\) and a compact map \(J:V\to H\) into an inner-product space, the Lax–Milgram operator \(K\) with \(B(Ku,v)=\langle Ju,Jv\rangle\) is compact, and \(I-\kappa K\) satisfies the Fredholm alternative with finite-dimensional kernel (`IsCoercive.fredholmAlternative_formPerturbation`, [variational Fredholm alternative](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Variational/Fredholm.lean)); the application to the Dirichlet problem on bounded domains is in Section 32. The abstract Neumann series \(R(\mu)=\sum_n(\lambda-\mu)^nR(\lambda)^{n+1}\) for \(|\mu-\lambda|\,\|R(\lambda)\|<1\) is proved for partial operators on Banach spaces ([Neumann series](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Operator/Resolvent/NeumannSeries.lean)).

TauCeti's Fredholm characteristic power series of infinite matrices over complete ultrametric rings concerns Serre's nonarchimedean theory, not the Fredholm determinant of an integral operator ([characteristic power series](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Matrix/CharPowerSeries/Basic.lean)).

**Synopsis entries.** Covered: 25.15 (Mathlib). Partly covered: 25.11 (exceptional parameters are reciprocals of nonzero eigenvalues, with finite-dimensional generalized eigenspace stages; isolation is not proved), 25.14 (eigenbasis of a compact self-adjoint operator; the reduced equations are not stated). Not covered: 25.13, 25.16.

## Volterra equations and fractional integration

[Mathematical scope](SYNOPSIS25.md#volterra-equations-and-fractional-integration).

### Mathlib

**Supporting operator constructions.** The integral equation attached to a Lipschitz vector field is the integral form of an ordinary differential equation; existence and uniqueness for it are the Picard–Lindelöf theorem of Section 31 (`Analysis/ODE/PicardLindelof.lean`, `Analysis/ODE/ExistUnique.lean`). Grönwall's inequality, which bounds solutions of Volterra-type integral inequalities, is in `Analysis/ODE/Gronwall.lean`, with a discrete form in `Analysis/ODE/DiscreteGronwall.lean`.

### TauCeti

For a linear equation \(x'=M(t)x+F(t)\) on a Banach space, with \(M\) strongly measurable and essentially bounded and \(F\) integrable on \([a,b]\), the integrated (Carathéodory) equation \(x(t)=x_0+\int_a^t(M(s)x(s)+F(s))\,ds\) has a unique continuous solution (`TauCeti.exists_continuousOn_eq_forall_mem_Icc_eq_picard`, `TauCeti.eqOn_of_forall_mem_Icc_eq_picard`, [linear Carathéodory equations](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/Caratheodory.lean)). Fundamental matrices and Liouville's determinant formula are not formalized. The primitive operator \(f\mapsto\int_a^tf\) on continuous paths over a compact interval is a bounded operator of norm at most \(b-a\) (`ContinuousMap.intervalIntegralOperator`, `ContinuousMap.norm_intervalIntegralOperator_le`, [integration operator](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/ContinuousMap.lean)); it is the Volterra operator with kernel \(1\), and no iterate bound or resolvent theory for general Volterra kernels is given.

**Synopsis entries.** Partly covered: 25.20 (existence and uniqueness for the integrated linear equation with bounded measurable coefficients; no fundamental matrix). Not covered: 25.17, 25.18, 25.21–25.24.

## Cauchy singular integrals and factorization

[Mathematical scope](SYNOPSIS25.md#cauchy-singular-integrals-and-factorization).

### TauCeti

**Supporting material.** The single-point Cauchy principal value of \((\gamma(t)-s)^{-1}\gamma'(t)\) exists along a piecewise \(C^1\) immersed curve (`Contour.IsPwC1ImmersionOn.cauchyPVExistsAt_inv_sub`, [Cauchy principal value](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Contour/InvSubCPVExistence.lean)); see Section 40. This is the winding-number integral, not a singular integral operator on densities. Toeplitz operators on the boundary Hardy space \(H^2\) of the circle are defined for bounded symbols, with matrix entries \(\hat a(i-j)\), adjoint, norm bound \(\|T_a\|\le\|a\|_\infty\) and injectivity of the symbol map ([Toeplitz operators](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Hardy/Toeplitz.lean)), together with Hankel operators and the semicommutator identity ([Hankel operators](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Hardy/Hankel.lean)); the Fredholm index theorem and Wiener–Hopf factorization are not formalized.

**Synopsis entries.** Not covered: 25.25–25.30.

## Laplace layer potentials and boundary operators

[Mathematical scope](SYNOPSIS25.md#laplace-layer-potentials-and-boundary-operators).

Nearest supporting material: TauCeti's Newtonian kernel, Newtonian potential, and the Green and Poisson kernels of balls (Section 32); no layer potential on a general boundary is defined.

**Synopsis entries.** Not covered: 25.31–25.41, 25.61.

## Helmholtz scattering and boundary integral equations

[Mathematical scope](SYNOPSIS25.md#helmholtz-scattering-and-boundary-integral-equations).

**Synopsis entries.** Not covered: 25.42–25.46.

## Electromagnetic and inverse obstacle scattering

[Mathematical scope](SYNOPSIS25.md#electromagnetic-and-inverse-obstacle-scattering).

**Synopsis entries.** Not covered: 25.62–25.65.

## Galerkin, quadrature, and operator approximation

[Mathematical scope](SYNOPSIS25.md#galerkin-quadrature-and-operator-approximation).

Nearest supporting material: TauCeti proves that operator-norm limits of finite-rank operators are compact ([finite rank](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Operator/Compact/FiniteRank.lean)); the converse direction needed for 25.48 is absent.

**Synopsis entries.** Not covered: 25.47–25.49, 25.51.

## Ill-posed equations and regularization

[Mathematical scope](SYNOPSIS25.md#ill-posed-equations-and-regularization).

### TauCeti

The Moore–Penrose inverse is defined through the four Penrose conditions for linear maps between inner product spaces, where it is unique when it exists (`LinearMap.IsMoorePenroseInverse`); for finite-dimensional spaces it is constructed from the singular system, \(A^+y=\sum_i\sigma_i^{-1}\langle u_i,y\rangle v_i\) (`LinearMap.moorePenroseInverse`, [Moore–Penrose inverse](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/MoorePenrose.lean)), using finite-dimensional singular systems ([singular values](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/SingularValues.lean)). Its least-squares characterization and the closed-range criterion for boundedness are not formalized.

**Synopsis entries.** Partly covered: 25.53 (finite-dimensional singular-system construction and uniqueness only). Not covered: 25.52, 25.54–25.60.
