# Structure 30: Distributions, pseudodifferential operators, microlocal and semiclassical analysis

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS30.md); [bibliographical scope](CKMA-bib.md#ckma-30); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.Distribution` (in particular `TestFunction`, `ContDiffMapSupportedIn`, `Distribution`, `Support`, `AEEqOfIntegralContDiff`, `SchwartzSpace`, `TemperateGrowth`, `TemperedDistribution`, `FourierMultiplier`, `Sobolev`), `Mathlib.Analysis.Fourier.LpSpace`, `Mathlib.Analysis.Fourier.Convolution`, `Mathlib.Analysis.LocallyConvex`.

**Namespaces.** Test functions are `TestFunction` and `ContDiffMapSupportedIn`, distributions are `Distribution`, Schwartz functions are `SchwartzMap`, and tempered distributions are `TemperedDistribution`. Temperate growth is `Function.HasTemperateGrowth` and `MeasureTheory.Measure.HasTemperateGrowth`. Bessel potentials and Sobolev membership are `TemperedDistribution.besselPotential` and `TemperedDistribution.MemSobolev`. TauCeti's weak derivatives are `TauCeti.HasWeakLineDerivOn`, and its elliptic regularity theory is in `TauCeti.PDE`.

## Distributions and Fourier analysis for PDE

[Mathematical scope](SYNOPSIS30.md#distributions-and-fourier-analysis-for-pde).

### Mathlib

**Distributions.**

A test function of order \(n\) on an open set \(\Omega\) in a real normed space is a \(C^n\) map of compact support contained in \(\Omega\). Functions supported in a fixed compact carry the locally convex topology of uniform convergence of derivatives. The full test-function space carries the finest locally convex topology making every inclusion of such a subspace continuous, and a linear map into a locally convex space is continuous exactly when each of those restrictions is continuous (`Analysis/Distribution/TestFunction.lean`, `Analysis/Distribution/ContDiffMapSupportedIn.lean`).

An \(F\)-valued distribution on \(\Omega\) is a continuous real-linear map from the real test functions into a real topological vector space \(F\), with the topology of compact convergence (`Distribution`); complex distributions are distributions with values in \(\mathbb C\), tested against real test functions. The text of the file specializes to finite-dimensional domains and locally convex values; those hypotheses are not part of the type. They are used where stated below. Distributions of order at most \(n\) form a separate space. The file's comparison of this topology with the strong dual topology relies on the Montel property of test functions, which is not a theorem here (`Analysis/Distribution/Distribution.lean`). There is no space of distributions on a manifold, and the Schwartz kernel theorem is named in that file only as future work.

The Dirac mass evaluates at a point, and vanishes if the point lies outside \(\Omega\) (`Distribution.delta`). The directional derivative is defined by transposition, \(\langle\partial_v T,\varphi\rangle=\langle T,-\partial_v\varphi\rangle\) (`Distribution.lineDerivCLM`, `Distribution.lineDerivOp_apply_apply`); it is continuous and linear in \(T\) and in \(v\), and iterated derivatives are available through the generic iterated line derivative (`Analysis/Distribution/DerivNotation.lean`). The operator from order \(k\) to order \(n\) is zero unless \(k+1\le n\). A locally integrable function induces a distribution by integration against test functions, the zero distribution if it is not locally integrable (`Distribution.ofFun`). On a finite-dimensional Borel domain, with complete normed values, the distribution determines the function almost everywhere on \(\Omega\) (`Distribution.ofFun_injective`). The same almost-everywhere conclusion holds for a locally integrable function on a finite-dimensional real manifold. The support is the smallest closed set outside which the distribution vanishes; differentiation does not enlarge it; and in finite dimensions the support of a Dirac mass in \(\Omega\) is the point (`Analysis/Distribution/Distribution.lean`, `Analysis/Distribution/AEEqOfIntegralContDiff.lean`, `Analysis/Distribution/Support.lean`).

**Schwartz space and tempered distributions.**

A Schwartz function is a smooth function between real normed spaces whose derivatives decay faster than every power of the norm. The countable family of seminorms expressing those bounds makes the space a first countable locally convex space; completeness, the Fréchet property, and the Montel property are not proved. Smooth compactly supported functions are Schwartz. Against a measure of temperate growth — some negative power of \(1+\lVert x\rVert\) is integrable — Schwartz functions are integrable, the integral is continuous and linear, and for \(p\ge 1\) they map continuously into \(L^p\). On a finite-dimensional domain, with the measure finite on compact sets, they are dense in \(L^p\) for finite \(p\) (`SchwartzMap.denseRange_toLpCLM`; `Analysis/Distribution/SchwartzSpace/Basic.lean`, `Analysis/Distribution/TemperateGrowth.lean`).

On a finite-dimensional real inner product space the Fourier transform is a continuous linear endomorphism of Schwartz space. If the values are complete, inversion holds and the transform is a continuous linear equivalence. Derivatives pass through the transform as multiplication by \(\pm 2\pi i\langle\cdot,m\rangle\) (`SchwartzMap.fourier_lineDerivOp_eq`, `SchwartzMap.lineDerivOp_fourier_eq`), and integration by parts holds for directional derivatives and the Laplacian (`Analysis/Distribution/SchwartzSpace/Deriv.lean`). Plancherel for Schwartz functions with values in a complete complex inner product space preserves the integrated inner product and the \(L^2\) norms; the pointwise bound on the transform is the \(L^1\) norm (`Analysis/Distribution/SchwartzSpace/Fourier.lean`). The Fourier transform extends to a linear isometric equivalence of \(L^2\), compatible with the transforms on Schwartz functions and on tempered distributions (`MeasureTheory.Lp.fourierTransformₗᵢ`, `Analysis/Fourier/LpSpace.lean`). Convolution of Schwartz functions is a Schwartz function whose transform is the product of the transforms (`SchwartzMap.convolution`, `Analysis/Fourier/Convolution.lean`); convolution of distributions is not defined.

A tempered distribution is a continuous complex-linear map on complex Schwartz space, topologized by pointwise convergence rather than by the strong dual topology. Temperate measures, temperate functions, Schwartz functions, and \(L^p\) functions for \(p\ge 1\) embed into tempered distributions; the \(L^p\) embedding is injective in finite dimensions when the measure is locally finite. The Fourier transform, defined by transposition, is a continuous linear equivalence of tempered distributions and agrees on Schwartz functions with the function transform. The transform of the Dirac mass at the origin is Lebesgue measure (`TemperedDistribution.fourier_delta_zero`). Multiplication by a temperate function, differentiation, and the Laplacian are continuous, and the first two do not enlarge support (`Analysis/Distribution/TemperedDistribution.lean`, `Analysis/Distribution/Support.lean`).

### TauCeti

TauCeti proves that directional derivatives of test functions commute and agree pointwise with classical derivatives (`TestFunction.lineDerivOp_comm`; [test-function derivatives](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Distribution/TestFunction/LineDeriv.lean)). For weak directional derivatives of locally integrable functions on an open set, a classical directional derivative is a weak one (`TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt`; [weak derivatives](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/WeakDeriv/Basic.lean)), mixed weak derivatives commute as soon as one exists (`TauCeti.HasWeakLineDerivOn.comm`; [symmetry](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/WeakDeriv/Symmetry.lean)), and on the whole space, for \(L^p\) functions with \(L^q\) candidate derivatives, the weak derivative is the derivative of the associated tempered distribution (`TauCeti.hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_eq`; [weak and tempered derivatives](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/WeakDeriv/TemperedDistribution.lean)). These statements concern weak derivatives and test functions; commutation of derivatives on Mathlib's space of distributions, and compatibility of `Distribution.lineDerivOp` with `Distribution.ofFun`, are not stated.

Further tools: the du Bois-Reymond lemma (a locally integrable function on an interval with vanishing distributional derivative is a.e. constant; [du Bois-Reymond](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Distribution/DuBoisReymond.lean)), the determination of tempered distributions by real compactly supported test functions ([test functions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Distribution/TemperedDistribution/TestFunction.lean)), the a.e. determination of \(L^p\) functions by their pairings with Schwartz functions ([\(L^p\) embedding](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Distribution/TemperedDistribution/Lp.lean)), and convergence of compactly supported smooth cutoffs in the Schwartz topology, with explicit estimates in each Schwartz seminorm, hence density of smooth compactly supported functions in Schwartz space on finite-dimensional spaces ([cutoff approximation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Distribution/SchwartzSpace/Cutoff.lean)). Distributional fundamental-solution identities for the Euclidean Laplacian are recorded in Sections 26, 32 and 38.

**Synopsis entries.** Partly covered: 30.1 (Mathlib: distributional directional derivatives of all orders by transposition on open sets of finite-dimensional spaces; TauCeti: commutation for test functions and for weak derivatives, and agreement of weak with tempered-distributional derivatives; commutation on the space of distributions itself is not stated).

## Wavefront sets and operations on singular distributions

[Mathematical scope](SYNOPSIS30.md#wavefront-sets-and-operations-on-singular-distributions).

Neither library defines singular support or wavefront sets; the only support notion is Mathlib's distributional support (`Analysis/Distribution/Support.lean`), recorded above.

**Synopsis entries.** Not covered: 30.11–30.20.

## Symbols, quantization, and the operator calculus

[Mathematical scope](SYNOPSIS30.md#symbols-quantization-and-the-operator-calculus).

### Mathlib

**Fourier multipliers and Bessel-potential spaces.** These are \(x\)-independent symbols only; no symbol class \(S^m_{\rho,\delta}\), Kohn–Nirenberg or Weyl quantization is defined.

A Fourier multiplier by a scalar function \(g\) is \(\mathcal{F}^{-1}\circ(g\cdot)\circ\mathcal{F}\), on Schwartz functions and on tempered distributions. The multiplication is zero unless \(g\) has temperate growth. Multipliers compose by multiplication of symbols. The directional derivative and the Laplacian are multipliers, by \(2\pi i\langle\cdot,m\rangle\) and by \(-(2\pi)^2\lVert x\rVert^2\) respectively (`Analysis/Distribution/FourierMultiplier.lean`). Bessel-potential Sobolev spaces are built from multipliers (`Analysis/Distribution/Sobolev.lean`). The Bessel potential of order \(s\) is the multiplier with symbol \((1+\lVert\xi\rVert^2)^{s/2}\), and a tempered distribution lies in \(H^{s,p}\) when its Bessel potential of order \(s\) is an \(L^p\) function. The Bessel potential of order \(r\) maps \(H^{s,p}\) onto \(H^{s-r,p}\) (`TemperedDistribution.memSobolev_besselPotential_iff`). Schwartz functions lie in every \(H^{s,p}\); \(H^{s,2}\) is characterized by a weighted \(L^2\) condition on the Fourier transform; for \(2s>\dim E\) the transform of an \(H^{s,2}\) element is integrable (`TemperedDistribution.MemSobolev.fourier_memL1`); multipliers with bounded symbols preserve \(H^{s,2}\) (`TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_bounded`); \(H^{s,2}\subseteq H^{s',2}\) for \(s'\le s\); and directional derivatives and the Laplacian lower the order by one and two (`TemperedDistribution.MemSobolev.lineDerivOp`, `TemperedDistribution.MemSobolev.laplacian`).

### TauCeti

TauCeti carries the constant-coefficient multiplier theory to \(L^p\). For an essentially bounded symbol \(m\), the \(L^2\) Fourier multiplier \(T_m=\mathcal F^{-1}(m\,\mathcal F\cdot)\) is bounded with \(\|T_m\|\le\|m\|_\infty\) ([\(L^2\) multipliers](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/L2Multiplier.lean)). The Mihlin–Hörmander multiplier theorem is proved: on a real inner product space of dimension \(n\ge1\), if \(m\) is smooth away from the origin with \(\|D^km(\xi)\|\le A\|\xi\|^{-k}\) for \(k\le N\) and \(2N>n\), then \(\|T_mf\|_p\le CA\|f\|_p\) for \(1<p<\infty\) with \(C\) independent of \(m\) and \(A\) (`TauCeti.exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le`), and for symbols of temperate growth the tempered-distribution multiplier maps \(L^p\) to \(L^p\) with the same bound ([Mihlin–Hörmander](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/MihlinHormander.lean)). The proof uses Littlewood–Paley pieces of the symbol, the identification of multipliers with Schwartz symbols as convolutions, weighted Plancherel bounds on their kernels, and the Calderón–Zygmund theorem under Hörmander's condition ([Littlewood–Paley pieces](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Distribution/SchwartzSpace/LittlewoodPaley.lean), [band-limited kernels](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Distribution/SchwartzSpace/BandLimited.lean), [convolution kernels](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Distribution/SchwartzSpace/Convolution.lean), [weighted Plancherel](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Distribution/SchwartzSpace/WeightedPlancherel.lean)).

On Mathlib's Bessel-potential spaces, TauCeti proves for \(1<p<\infty\) that Mihlin multipliers and real symbols of order \(0\) preserve \(H^{s,p}\), that \(H^{s,p}\subseteq H^{s',p}\) for \(s'\le s\), that \(\partial_m\) maps \(H^{s,p}\) to \(H^{s-1,p}\), and that \(f\in H^{s+1,p}\) exactly when \(f\) and all its first directional derivatives (equivalently, those along an orthonormal basis) lie in \(H^{s,p}\) (`TemperedDistribution.memSobolev_add_one_iff`); the Bessel potential of order \(2\) is \(1-(2\pi)^{-2}\Delta\) ([Bessel-potential regularity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Distribution/Sobolev.lean)). For natural \(k\) and \(1<p<\infty\), \(H^{k,p}(\mathbb R^n)\) coincides with the weak-derivative space \(W^{k,p}(\mathbb R^n)\) (Calderón; `MeasureTheory.Lp.memSobolev_natCast_iff_exists_wkp_value_eq`; [Bessel and weak Sobolev spaces](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/BesselPotential/Basic.lean)).

**Synopsis entries.** Partly covered: 30.28 (\(x\)-independent symbols only: Bessel potentials, bounded and derivative multipliers on \(H^{s,2}\) in Mathlib, Mihlin multipliers on \(H^{s,p}\) in TauCeti). Not covered: 30.21–30.27, 30.29–30.32, 30.66.

## Ellipticity, hypoellipticity, and singularity propagation

[Mathematical scope](SYNOPSIS30.md#ellipticity-hypoellipticity-and-singularity-propagation).

### TauCeti

For second-order divergence-form operators TauCeti proves interior regularity by difference quotients: a weak solution \(u\in H^1(\Omega)\) of \(-\partial_j(a^{ij}\partial_iu)=f\) with uniformly elliptic coefficients is in \(H^2_{\mathrm{loc}}\) for locally Lipschitz \(a\) and \(f\in L^2\) (with bounded lower-order terms allowed), in \(H^{k+2}_{\mathrm{loc}}\) for smooth \(a\) and \(f\in W^{k,2}\), and agrees a.e. with a smooth function when \(a\) and \(f\) are smooth (`TauCeti.PDE.UniformlyEllipticOn.exists_contDiffOn_ae_eq_of_contDiffOn`; [interior \(H^2\)](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/Interior.lean), [interior \(H^k\)](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/HigherOrder.lean), [smoothness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/Smooth.lean)); this theory is recorded in Sections 32 and 33. The multiplier \(\partial_v\partial_w\Delta^{-1}\), with symbol \(\langle\xi,v\rangle\langle\xi,w\rangle/\|\xi\|^2\), gives \(\|\partial_v\partial_wu\|_{L^2}\le\|v\|\|w\|\|\Delta u\|_{L^2}\) for Schwartz \(u\) ([Hessian multiplier](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/HessianMultiplier.lean)). There is no parametrix, hypoellipticity, or microlocal propagation theory.

**Synopsis entries.** Partly covered: 30.35 (TauCeti: second-order divergence-form operators only, interior \(H^{k+2}\) regularity on integer Sobolev scales and the smoothness bootstrap). Not covered: 30.33–30.34, 30.39–30.44, 30.67–30.68.

## Fourier integral operators and canonical transformations

[Mathematical scope](SYNOPSIS30.md#fourier-integral-operators-and-canonical-transformations).

**Synopsis entries.** Not covered: 30.45–30.51.

## Semiclassical operators and phase-space limits

[Mathematical scope](SYNOPSIS30.md#semiclassical-operators-and-phase-space-limits).

**Synopsis entries.** Not covered: 30.52–30.64.

## Scattering resonances

[Mathematical scope](SYNOPSIS30.md#scattering-resonances).

**Synopsis entries.** Not covered: 30.69–30.70.
