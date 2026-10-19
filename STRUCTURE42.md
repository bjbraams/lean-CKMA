# Structure 42: Hardy, Bergman, and model spaces; operators on analytic function spaces

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS42.md); [bibliographical scope](CKMA-bib.md#ckma-42); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis. The closing line of each section sorts the numbered synopsis entries under that heading.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.Complex.CanonicalDecomposition`, `Mathlib.Analysis.Complex.Poisson`, `Mathlib.Analysis.Complex.Harmonic.Poisson`, `Mathlib.Analysis.InnerProductSpace.Reproducing`, `Mathlib.Analysis.InnerProductSpace.Symmetric`, `Mathlib.Analysis.Normed.Operator.Fredholm`.

**Namespaces.** Canonical factors are `Complex`; reproducing-kernel Hilbert spaces are `RKHS`; Fredholm operators are `ContinuousLinearMap.IsFredholm`. The symmetric-operator result in `Analysis/InnerProductSpace/Symmetric.lean` is the Hellinger–Toeplitz theorem, a general operator theorem. TauCeti’s boundary Hardy space, Toeplitz and Hankel operators, and the Herglotz representation are in the namespace `TauCeti`, with disc functions under `TauCeti.HardySpace`. Neither library has Hardy spaces \(H^p\) of holomorphic functions for general \(p\), inner functions, Bergman, Dirichlet, de Branges–Rovnyak, or Fock spaces.

## Hardy spaces, boundary values, and factorization

[Mathematical scope](SYNOPSIS42.md#hardy-spaces-boundary-values-and-factorization).

### Mathlib

**Finite canonical factors.** The one construction that uses the name of a Blaschke product is the finite canonical decomposition of a meromorphic function on a disc. The factor \((R^2-\overline{w}\,z)/(R(z-w))\) is meromorphic and, for \(R>0\) and \(|w|<R\), has a single pole at \(w\) and modulus one on the circle of radius \(R\) (`Complex.canonicalFactor`, `Complex.norm_canonicalFactor_eval_circle_eq_one`). A finite product of such factors rewrites a meromorphic function on a closed disc, up to an analytic factor without zeros (`MeromorphicOn.exists_canonicalDecomp`, `MeromorphicOn.exists_ecanonicalDecomp`, `Analysis/Complex/CanonicalDecomposition.lean`). The file uses this for the counting formulae of Section 41. This is supporting material: no infinite Blaschke product, inner or outer function, or Hardy-space factorization is defined.

**Poisson integral formula.** A function complex-differentiable on a disc and continuous on its closure, and a function harmonic on the closed disc, are recovered from their boundary values by the Poisson kernel, written as the real part of the Herglotz–Riesz kernel (`DiffContOnCl.circleAverage_poissonKernel_smul`, `Analysis/Complex/Poisson.lean`; `HarmonicContOnCl.circleAverage_poissonKernel_smul`, `Analysis/Complex/Harmonic/Poisson.lean`). This reproduces functions regular up to the boundary; boundary values of \(H^p\) functions are not treated.

**Reproducing kernels.** Reproducing-kernel Hilbert spaces, in the abstract sense of a Hilbert space of functions with continuous point evaluations, kernel functions, and the kernel as a positive semidefinite matrix, are Section 29 (`RKHS`, `Analysis/InnerProductSpace/Reproducing.lean`). The Szegő kernel of \(H^2\) is not constructed.

### TauCeti

**Boundary Hardy space.** The boundary Hardy space \(H^2\) is the closed subspace of \(L^2(\mathbb T)\), with normalized Haar measure, spanned by the nonnegative Fourier modes; equivalently its elements are the functions with vanishing negative Fourier coefficients (`TauCeti.hardySubmodule`, `TauCeti.mem_hardySubmodule_iff`). The nonnegative modes form a Hilbert basis, identifying \(H^2\) isometrically with \(\ell^2\) (`TauCeti.hardyBasis`), and the orthogonal projection onto \(H^2\) and its complement of negative modes are available (`TauCeti.hardySubmodule_orthogonal_eq`, [boundary Hardy space](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Hardy/Basic.lean)). For \(x\in H^2\) with coefficients \(\hat x(n)\), the disc function \(F_x(w)=\sum_n\hat x(n)w^n\) is holomorphic on the unit disc, satisfies \(|F_x(w)|\le\|x\|/\sqrt{1-|w|^2}\), and its circle restrictions \(t\mapsto F_x(re(t))\) converge to \(x\) in \(L^2\) as \(r\to1^-\) (`TauCeti.HardySpace.diskFunction`, `TauCeti.HardySpace.norm_diskFunction_le`, `TauCeti.HardySpace.tendsto_eLpNorm_diskFunction_sub`, [disc function](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Hardy/DiskFunction.lean)). The space is defined on the boundary, so the holomorphic \(H^2\) of the synopsis is reached through the disc function; the converse identification (every holomorphic function with bounded \(L^2\) means arises this way), almost-everywhere nontangential limits, and every \(p\neq2\) are not treated.

**Boundary measures.** The Herglotz representation is proved: if \(F\) is holomorphic on the unit disc with nonnegative real part, then
\[
 F(w)=\int_{|z|=1}\frac{z+w}{z-w}\,d\mu(z)+i\operatorname{Im}F(0)
\]
for a finite positive measure \(\mu\), and conversely such transforms have those properties (`TauCeti.exists_isFiniteMeasure_eq_herglotzTransform_add`, [Herglotz](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Herglotz.lean)). This is the boundary-measure theory behind singular inner factors and Clark measures, but neither is constructed. Its half-plane counterpart, the representation of Pick functions, is recorded in Section 13 ([Pick functions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Pick/Basic.lean)). The planar Poisson integral of integrable real boundary data on a circle is harmonic in the disc, and for continuous data it tends to the boundary value at each boundary point, which solves the Dirichlet problem on a disc ([Poisson integral](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Poisson/Integral.lean)).

**Synopsis entries.** Partly covered: 42.1 (\(L^2\) radial convergence for \(p=2\) only), 42.2 (\(p=2\) only: \(H^2\) is a closed subspace of \(L^2\) and the disc function obeys \(|F_x(w)|\le(1-|w|^2)^{-1/2}\|x\|\)), 42.4 (\(p=2\) only: the analytic monomials form a Hilbert basis of boundary \(H^2\)), 42.13 (only the orthogonal projection onto \(H^2\) in \(L^2\)), 42.14 (Parseval for \(H^2\) through the Hilbert basis; Hardy's inequality is not proved). Not covered: 42.3, 42.5–42.12, 42.15, 42.84, 42.16–42.19, 42.28.

## Carleson measures, BMO, and interpolation

[Mathematical scope](SYNOPSIS42.md#carleson-measures-bmo-and-interpolation).

**Synopsis entries.** Not covered: 42.20–42.27.

## Toeplitz and Hankel operators

[Mathematical scope](SYNOPSIS42.md#toeplitz-and-hankel-operators).

### Mathlib

Fredholm operators between topological vector spaces are defined with their equivalent characterizations (`ContinuousLinearMap.IsFredholm`, `Analysis/Normed/Operator/Fredholm/Basic.lean`); this is supporting material for the Toeplitz index theorem, which is not proved.

### TauCeti

For an essentially bounded symbol \(a\), the Toeplitz operator \(T_a=PM_a|_{H^2}\) is a bounded linear function of \(a\) with \(\|T_a\|\le\|a\|_\infty\); its matrix in the basis \(e_0,e_1,\dots\) has entries \(\hat a(i-j)\), its adjoint is \(T_{\bar a}\), and the symbol is determined by the operator (`TauCeti.toeplitz`, `TauCeti.norm_toeplitz_le`, `TauCeti.inner_hardyBasis_toeplitz_hardyBasis`, `TauCeti.adjoint_toeplitz`, `TauCeti.toeplitz_injective`, [Toeplitz operators](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Hardy/Toeplitz.lean)). The Hankel operator \(H_a\) of \(a\) is multiplication followed by projection onto the orthogonal complement of \(H^2\), with norm at most \(\|a\|_\infty\) (`TauCeti.hankel`, `TauCeti.norm_hankel_le`). The semicommutator identity \(T_aT_b-T_{ab}=-H_{\bar a}^*H_b\) is proved (`TauCeti.toeplitz_comp_sub_toeplitz`), and with the Fourier characterization of vanishing Hankel operators (`TauCeti.hankel_eq_zero_iff`) it gives \(T_aT_b=T_{ab}\) when \(b\) is analytic or \(a\) is coanalytic (`TauCeti.toeplitz_comp_of_analytic`, `TauCeti.toeplitz_comp_of_coanalytic`, [Hankel operators](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Hardy/Hankel.lean)). The Brown–Halmos characterization \(S^*TS=T\), the norm equality \(\|T_\phi\|=\|\phi\|_\infty\), Fredholm and spectral theory of Toeplitz operators, and Nehari's distance formula are not proved.

**Synopsis entries.** Covered: 42.30 (TauCeti). Partly covered: 42.29 (adjoint formula, uniqueness of the symbol, and \(\|T_\phi\|\le\|\phi\|_\infty\); neither the \(S^*TS=T\) characterization nor norm equality). Not covered: 42.31–42.36, 42.90, 42.37–42.39.

## Model spaces and compressed shifts

[Mathematical scope](SYNOPSIS42.md#model-spaces-and-compressed-shifts).

**Synopsis entries.** Not covered: 42.40–42.49.

## Cauchy transforms and subnormal operators

[Mathematical scope](SYNOPSIS42.md#cauchy-transforms-and-subnormal-operators).

**Synopsis entries.** Not covered: 42.85–42.89.

## Bergman and Bloch spaces

[Mathematical scope](SYNOPSIS42.md#bergman-and-bloch-spaces).

**Synopsis entries.** Not covered: 42.50–42.61.

## Dirichlet and de Branges–Rovnyak spaces

[Mathematical scope](SYNOPSIS42.md#dirichlet-and-de-brangesrovnyak-spaces).

**Synopsis entries.** Not covered: 42.62–42.72.

## Composition operators

[Mathematical scope](SYNOPSIS42.md#composition-operators).

### TauCeti

As supporting material, TauCeti develops disc automorphisms and the Schwarz–Pick contraction for holomorphic self-maps of the disc ([Schwarz–Pick](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/SchwarzPick/Basic.lean); see [Section 43](STRUCTURE43.md)). No composition operator on a function space is defined.

**Synopsis entries.** Not covered: 42.73–42.77.

## Fock spaces and planar sampling

[Mathematical scope](SYNOPSIS42.md#fock-spaces-and-planar-sampling).

**Synopsis entries.** Not covered: 42.78–42.83.

## Supporting structures and related formalizations

The following entries supply related foundations. Their stated scope determines how they can be used in this sub-area.

### Mathlib

The disc and the upper half-plane, including the Poincaré metric and the invariant measure on the half-plane, are Section 40. The Hellinger–Toeplitz theorem, that a symmetric everywhere-defined operator on a Hilbert space is bounded (`Analysis/InnerProductSpace/Symmetric.lean`), is a general operator theorem and concerns no space of holomorphic functions.
