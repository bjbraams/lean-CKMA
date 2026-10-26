# Structure 29: Wavelets, frames, time–frequency analysis, and sampling

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS29.md); [bibliographical scope](CKMA-bib.md#ckma-29); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.Normed.Module.Bases`, `Mathlib.Analysis.InnerProductSpace.l2Space`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc`, `Mathlib.Analysis.Fourier.LpSpace`, `Mathlib.Analysis.InnerProductSpace.Reproducing`, `Mathlib.Analysis.InnerProductSpace.Reproducing.Operations`.

**Namespaces.** Bases in normed spaces are `GeneralSchauderBasis`, with the abbreviations `SchauderBasis` and `UnconditionalSchauderBasis` and the construction `RankOneDecomposition`; the sinc function is `Real.sinc`; the Fourier transform on \(L^2\) is `MeasureTheory.Lp.fourierTransformₗᵢ`. The reproducing-kernel theory is `RKHS`, with the kernel construction in `RKHS.OfKernel` and the sum of kernels in `RKHS.Add'`. TauCeti declarations cited here are in `TauCeti`, except the Kolmogorov realization in `Matrix.PosSemidef`.

## Frames, bases, and stable reconstruction

[Mathematical scope](SYNOPSIS29.md#frames-bases-and-stable-reconstruction).

### Mathlib

**Schauder bases and the sinc function.**

`Analysis/Normed/Module/Bases.lean` defines a generalized Schauder basis of a normed space \(X\), indexed by a type \(\beta\) and a summation filter: a family \(b_i\) with continuous coordinate functionals \(b_i^*\) such that \(b_i^*(b_j)=\delta_{ij}\) and \(x=\sum_ib_i^*(x)b_i\) along the filter. The classical Schauder basis (`SchauderBasis`) uses partial sums along \(\mathbb N\), and the unconditional basis (`UnconditionalSchauderBasis`) uses the net of finite subsets. A basis is linearly independent; the finite coordinate projections \(P_A\) satisfy \(P_AP_B=P_{A\cap B}\), have range the span of \(\{b_i:i\in A\}\), and converge strongly to the identity. In a Banach space they are uniformly bounded (the basis constant, by Banach–Steinhaus; `GeneralSchauderBasis.exists_norm_proj_le`, `SchauderBasis.exists_norm_proj_le`). Conversely, projections \(P_n\) of rank \(n\) with \(P_0=0\), \(P_nP_m=P_{\min(n,m)}\) and \(P_n\to I\) strongly yield a Schauder basis (`RankOneDecomposition.basis`). In `Analysis/InnerProductSpace/l2Space.lean`, a Hilbert basis is an unconditional Schauder basis with coordinates \(x\mapsto\langle b_i,x\rangle\) (`HilbertBasis.toUnconditionalSchauderBasis`, and `HilbertBasis.toSchauderBasis` for index \(\mathbb N\)). Frames, Bessel sequences, Riesz bases, and bases of exponentials or wavelets are not treated.

`Real.sinc` is defined as \(\sin x/x\) with value \(1\) at \(0\) (`Analysis/SpecialFunctions/Trigonometric/Sinc.lean`), with continuity, evenness, positivity on \((-\pi,\pi)\), and the bounds \(|\mathop{\mathrm{sinc}}x|\le1\) and \(\sin x/x\le|x|^{-1}\). Note the unnormalized convention \(\sin x/x\), against \(\sin(\pi u)/(\pi u)\) in the synopsis. No interpolation series of sinc translates is formalized.

### TauCeti

TauCeti develops finite frames in an inner product space over \(\mathbb R\) or \(\mathbb C\) ([finite frames](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Frame.lean)). For a finite family \((v_i)\), the analysis map \(x\mapsto(\langle v_i,x\rangle)_i\) and the synthesis map \(a\mapsto\sum_ia_iv_i\) (`TauCeti.analysisMap`, `TauCeti.synthesisMap`) are mutually adjoint, and \(\|\text{analysis}(x)\|^2=\sum_i|\langle v_i,x\rangle|^2\). The frame operator \(S=\sum_i\langle v_i,\cdot\rangle v_i\) and the Gram operator (`TauCeti.frameOperator`, `TauCeti.gramOperator`) are positive, an orthonormal basis has \(S=I\) (`OrthonormalBasis.frameOperator_eq_id`), and for finite-dimensional \(E\) the sorted spectra of \(S\) and of the Gram operator agree through the smaller dimension. A lower frame bound \(a\|x\|^2\le\sum_i|\langle v_i,x\rangle|^2\) holds for all \(x\) exactly when the Gram eigenvalues below \(\dim E\) are at least \(a\), provided the family has at least \(\dim E\) members (`TauCeti.le_eigenvalues_gramOperator`, `TauCeti.mul_norm_sq_le_sum_norm_inner_sq_of_le_eigenvalues_gramOperator`). Infinite frames, the dual frame \(S^{-1}v_i\), and frame reconstruction are absent.

On top of Mathlib's Schauder bases, TauCeti proves the principle of small perturbations: if \(b\) is a generalized Schauder basis of a Banach space and \(\delta=\sum_i\|b_i^*\|\,\|b_i-c_i\|<1\), then a bounded linear equivalence of norm at most \(1+\delta\), with inverse of norm at most \((1-\delta)^{-1}\), maps \(b_i\) to \(c_i\), so \((c_i)\) is a basis with the same summation filter ([perturbation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Bases/Perturbation.lean)). It also treats transport of bases by bounded linear equivalences ([transport](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Bases/Map.lean)), subsequences as bases of their closed span ([subsequences](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Bases/Subsequence.lean)), monotone renorming ([renorming](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Bases/Monotone.lean)), the dual basic sequence and the equivalence of shrinking bases with boundedly complete dual sequences ([duality](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Bases/Dual/Basic.lean), [bounded completeness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Bases/Dual/BoundedlyComplete.lean)), James's characterization of reflexivity by shrinking and boundedly complete bases ([reflexivity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Bases/Reflexive.lean)), and the bounded approximation property of spaces with a basis ([approximation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Bases/Approximation.lean)). For \(1\le p<\infty\), the unit coordinate vectors form an unconditional Schauder basis of \(\ell^p\) whose finite coordinate projections are contractions ([\(\ell^p\) basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Lp/Basis.lean)). These are abstract Banach-space results; the small-perturbation principle for Schauder bases is not the frame-perturbation theorem of the synopsis.

**Synopsis entries.** Partly covered: 29.1 (finite families only, TauCeti), 29.2 (finite families in finite-dimensional spaces: lower frame bound equivalent to a lower bound on the Gram spectrum, TauCeti), 29.11 (TauCeti: the frame operator \(\sum_kf_kf_k^*\) with its quadratic form, and \(S=I\) for an orthonormal basis; the tightness criterion and \(A=N/d\) are not stated). Not covered: 29.3–29.10, 29.12.

## Multiresolution and orthonormal wavelets

[Mathematical scope](SYNOPSIS29.md#multiresolution-and-orthonormal-wavelets).

**Synopsis entries.** Not covered: 29.13–29.26, 29.70.

## Function spaces and approximation through wavelets

[Mathematical scope](SYNOPSIS29.md#function-spaces-and-approximation-through-wavelets).

**Synopsis entries.** Not covered: 29.27–29.32.

## Continuous wavelets and short-time Fourier analysis

[Mathematical scope](SYNOPSIS29.md#continuous-wavelets-and-short-time-fourier-analysis).

### Mathlib

As supporting infrastructure only, Mathlib defines the Fourier transform on \(L^2\) of a finite-dimensional real inner product space as a linear isometry equivalence (Plancherel), agreeing with the Fourier transform on Schwartz functions and on tempered distributions (`MeasureTheory.Lp.fourierTransformₗᵢ`, `SchwartzMap.toLp_fourier_eq`; `Analysis/Fourier/LpSpace.lean`). The short-time Fourier transform, the continuous wavelet transform, the Wigner distribution, and the uncertainty principles are not defined.

### TauCeti

TauCeti adds a concrete orthogonal decomposition relevant to time–frequency analysis: the normalized Hermite functions form a Hilbert basis of \(L^2(\mathbb R)\) (`TauCeti.hermiteHilbertBasis`; [Hermite basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Function/HilbertBasis.lean)). The rescaled Hermite functions adapted to the \(e^{-2\pi ix\xi}\) convention form a Hilbert basis in which Mathlib's unitary Fourier transform on \(L^2(\mathbb R;\mathbb C)\) is diagonal with eigenvalue \((-i)^n\) on the \(n\)-th vector, so the fourth power of the Fourier transform is the identity (`TauCeti.twoPiHermiteHilbertBasis`, `TauCeti.fourier_twoPiHermiteFunctionLp`, `TauCeti.hasSum_fourier_twoPiHermiteFunctionLp`, `TauCeti.fourier_fourier_fourier_fourier`; [Fourier basis description](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Fourier/HilbertBasis.lean)). Products of Hermite functions give a Hilbert basis of \(L^2(\mathbb R^n)\) (`TauCeti.hermiteFunctionPiBasis`; [multi-index basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Pi/Basis.lean)). These are orthonormal bases, not Gabor-frame or sampling theorems, and the Bargmann transform and Fock space are absent.

**Synopsis entries.** Partly covered: 29.71 (TauCeti: in dimension one, the Hermite functions are an orthonormal basis of \(L^2(\mathbb R)\) and eigenfunctions of the Fourier transform with eigenvalues \((-i)^n\); no Bargmann transform or Fock space). Not covered: 29.35–29.42.

## Gabor systems and modulation spaces

[Mathematical scope](SYNOPSIS29.md#gabor-systems-and-modulation-spaces).

**Synopsis entries.** Not covered: 29.43–29.54, 29.72.

## Time–frequency localization and Weyl operators

[Mathematical scope](SYNOPSIS29.md#timefrequency-localization-and-weyl-operators).

**Synopsis entries.** Not covered: 29.73–29.75.

## Bandlimited and nonuniform sampling

[Mathematical scope](SYNOPSIS29.md#bandlimited-and-nonuniform-sampling).

### Mathlib

**Reproducing-kernel Hilbert spaces (supporting infrastructure).** The general theory below is the natural starting point for 29.56 and 29.59–29.60, but the Paley–Wiener space \(PW_B\) and its sinc kernel are not constructed.

A reproducing-kernel Hilbert space on a set \(X\), with values in a Hilbert space \(V\) over \(\mathbb{R}\) or \(\mathbb{C}\), is a Hilbert space \(H\) of functions \(X\to V\) in the following sense: the inclusion of \(H\) into the space of all functions is an injective continuous linear map (`RKHS`). Point evaluation is then continuous (`Analysis/InnerProductSpace/Reproducing.lean`).

The kernel function at \(x\in X\) is the adjoint of evaluation at \(x\), a continuous linear map \(V\to H\) (`RKHS.kerFun`). The kernel (`RKHS.kernel`) is the matrix of operators \(V\to V\) whose \((x,y)\)-entry is the composite of the kernel function at \(y\) with the adjoint of the kernel function at \(x\). The reproducing identity is
\[
\langle k_x v,\, f\rangle_H=\langle v,\, f(x)\rangle_V.
\]
Evaluation is bounded by the diagonal of the kernel, \(\|f(x)\|\leq\|f\|\sqrt{\|K(x,x)\|}\) (`RKHS.norm_apply_le`). If the kernel functions are uniformly bounded on a set, norm convergence in \(H\) implies uniform convergence of the functions on that set. Continuity of the kernel, of the kernel functions, and of evaluation are related (`RKHS.continuous_kernel_tfae`). The linear span of the kernel functions is dense (`RKHS.kerFun_dense`). The kernel is a positive semidefinite, Hermitian matrix of operators (`RKHS.posSemidef_kernel`).

Moore’s theorem, in the form proved here: every positive semidefinite matrix \(K\) of continuous linear maps \(V\to V\), indexed by \(X\times X\), is the kernel of a reproducing-kernel Hilbert space. The space (`RKHS.OfKernel`) is the completion of the finitely supported functions \(X\times V\to\mathbb{k}\) for the seminorm coming from \(K\), and the kernel of this space is exactly \(K\) (`RKHS.kernel_ofKernel`). If two such spaces have the same kernel, they are linearly isometric by an isometry that matches kernel functions with kernel functions (`RKHS.equiv`).

A closed subspace of a reproducing-kernel Hilbert space, with the restricted inclusion, is again a reproducing-kernel Hilbert space. Its kernel functions are the orthogonal projections of the original kernel functions, its kernel is obtained by inserting the corresponding orthogonal projection, and the kernel of the orthogonal complement is the difference of kernels (`RKHS.kernel_orthogonal`). A function \(f:X\to V\) determines a rank-one positive semidefinite kernel with entries \(\langle f(y),\cdot\rangle f(x)\) (`RKHS.outerKernel`).

The sum of two spaces and of two kernels is treated in `Analysis/InnerProductSpace/Reproducing/Operations.lean`. The space \(H+H'\) of sums \(f_1+f_2\) is a reproducing-kernel Hilbert space with kernel \(K_H+K_{H'}\) (`RKHS.Add'.kernel_sum_eq_sum_of_kernel`); its norm satisfies \(\|f\|^2=\min\{\|f_1\|^2+\|f_2\|^2: f=f_1+f_2\}\), the minimum being attained (`RKHS.Add'.exists_eq_add_and_norm_sq_eq_add`, `RKHS.Add'.norm_sq_le`). The reproducing-kernel space of \(K+K'\) is isometrically isomorphic to the quotient of the product of the spaces of \(K\) and of \(K'\) by the pairs with zero sum (`RKHS.Add'.OfKernelAddEquiv`).

### TauCeti

For scalar positive-definite kernels TauCeti packages a minimal Kolmogorov Hilbert-space realization \(\langle\Phi(a),\Phi(b)\rangle=K(a,b)\) with dense span and its universal isometry, using Mathlib's RKHS construction (`Matrix.PosSemidef.KolmogorovSpace`, `Matrix.PosSemidef.kolmogorovIsometry`; [kernel realization](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PositiveDefinite/Kernel/Kolmogorov.lean)). This too is general kernel theory, not bandlimited sampling.

**Synopsis entries.** Not covered: 29.56–29.64, 29.76–29.77.

## Sparse recovery and redundant dictionaries

[Mathematical scope](SYNOPSIS29.md#sparse-recovery-and-redundant-dictionaries).

**Synopsis entries.** Not covered: 29.65–29.68.
