# Structure 33: Elliptic and parabolic equations — regularity, free boundaries, and viscosity solutions

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS33.md); [bibliographical scope](CKMA-bib.md#ckma-33); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.InnerProductSpace.LaxMilgram`, `Mathlib.Analysis.InnerProductSpace.Projection.Minimal`. The Mathlib Laplacian, harmonic functions, and the planar mean-value, Liouville and Poisson theorems are recorded in [STRUCTURE32.md](STRUCTURE32.md), under the Laplacian.

**Namespaces.** The Lax–Milgram equivalence is `IsCoercive`; the projection theorems are in the root namespace. TauCeti places the De Giorgi–Nash–Moser theory, the maximum principles for general operators, and the Schauder and Calderón–Zygmund estimates in `TauCeti.PDE`, and the Monge–Ampère theory in `TauCeti`.

## Weak solutions and rough-coefficient elliptic regularity

[Mathematical scope](SYNOPSIS33.md#weak-solutions-and-rough-coefficient-elliptic-regularity).

### Mathlib

The Lax–Milgram theorem on a real Hilbert space (`Analysis/InnerProductSpace/LaxMilgram.lean`), stated in [STRUCTURE32.md](STRUCTURE32.md), is the only Mathlib existence theorem near a linear elliptic variational problem. It is not a regularity theorem, and it is not specialized to any differential operator.

### TauCeti

Existence and uniqueness for coercive divergence-form weak Dirichlet problems, Gårding's inequality, the compact solution operator, the symmetric Dirichlet spectral theorem, and interior \(H^2\), \(H^k\) and \(C^\infty\) regularity are described in [STRUCTURE32.md](STRUCTURE32.md). For a Lipschitz uniformly elliptic field on \(\mathbb{R}^n\), weak solutions of \(-\partial_j(a^{ij}\partial_iu)=f\) with \(f\in L^2\) lie in \(H^2(\mathbb{R}^n)\) with an explicit estimate ([whole-space regularity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/Basic.lean)).

**Weak comparison.** For a coercive divergence-form energy form, a weak subsolution with \((u-v)^+\in H^1_0(\Omega)\) relative to a supersolution satisfies \(u\le v\) almost everywhere; uniform ellipticity, bounded measurable coefficients, \(c\ge0\) and a drift smallness condition relative to a Poincaré constant suffice (`TauCeti.PDE.value_le_of_energyFormH1_le`; [weak maximum principle](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/MaximumPrinciple/Weak.lean)). On open sets of finite measure the maximum principle holds with bounded drift and no smallness condition ([bounded drift](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/MaximumPrinciple/Drift.lean)), and Stampacchia's global bound \(u\le k+C\|f\|_{L^r}\lambda^{-1}|\Omega|^{2/n-1/r}\) holds for subsolutions with \(f\in L^r\), \(r>\max(1,n/2)\) ([global boundedness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/MaximumPrinciple/GlobalBoundedness.lean)).

**De Giorgi–Nash–Moser theory.** For measurable uniformly elliptic principal coefficients, the Caccioppoli inequality \(\int\zeta^2|\nabla u|^2\le(2\Lambda/\lambda)^2\int|\nabla\zeta|^2u^2+(2/\lambda)\int\zeta^2fu\) holds for weak solutions with \(f\in L^2\), and its analogue for positive-part truncations of weak subsolutions, also with bounded drift and mass terms ([energy estimate](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Caccioppoli/Basic.lean), [truncations](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Caccioppoli/Truncation.lean), [lower-order terms](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Caccioppoli/LowerOrder.lean)). De Giorgi's local boundedness holds for weak subsolutions, \(u\le k+DR^{-n/2}\|(u-k)^+\|_{L^2(B_R)}\) on \(B_{R/2}\), also with bounded drift and \(c\ge0\) ([local boundedness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/LocalBoundedness/Basic.lean), [lower-order terms](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/LocalBoundedness/LowerOrder.lean)); oscillation decay gives De Giorgi's theorem that weak solutions of \(-\partial_j(a^{ij}\partial_iu)=0\) have a locally Hölder continuous representative, with exponent depending only on \(\lambda,\Lambda,n\) (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative`; [oscillation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/Oscillation.lean), [Hölder continuity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/HolderContinuity.lean)), and the same holds with a right-hand side \(f\in L^r\), \(r>\max(1,n/2)\) (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_memLp`; [inhomogeneous equation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/Inhomogeneous.lean)). Moser's iteration gives reverse Hölder inequalities for powers of positive supersolutions ([reverse Hölder](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/ReverseHolder.lean), [negative powers](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/Supersolution/Lp.lean)). The weak Harnack inequality holds for nonnegative weak supersolutions: \((\fint_{B(x_0,r)}u^s)^{1/s}\le C\mathop{\mathrm{ess\,inf}}_{B(x_0,r)}u\) for every \(s>0\) with \((n-2)s<n\) when \(B(x_0,12\sqrt n\,r)\subseteq\Omega\); and the Harnack inequality: a nonnegative weak solution satisfies \(\mathop{\mathrm{ess\,sup}}_{B(x_0,r)}u\le C\mathop{\mathrm{ess\,inf}}_{B(x_0,r)}u\) whenever \(B(x_0,24\sqrt n\,r)\subseteq\Omega\), in every dimension \(n\ge1\), with \(C\) depending only on \(\lambda,\Lambda,n\) (`TauCeti.PDE.exists_ae_ae_value_le_mul_value`; [Harnack inequality](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/Harnack.lean)). A strong maximum principle for weak subsolutions follows ([strong maximum principle](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/MaximumPrinciple/Strong.lean)). An explicit discontinuous-coefficient example illustrates the theorem ([jump coefficient](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/JumpCoefficient.lean)). The theory is scalar; systems, higher integrability of the gradient, and variational integrands are not treated.

**Synopsis entries.** Covered: 33.2–33.7 (TauCeti; weak comparison under coercivity or on sets of finite measure, Harnack with the larger ball \(B(x_0,24\sqrt n\,r)\)). Not covered: 33.8–33.11.

## Classical estimates and nondivergence equations

[Mathematical scope](SYNOPSIS33.md#classical-estimates-and-nondivergence-equations).

### TauCeti

Harmonic functions (mean value, Weyl's lemma, Harnack, maximum principles for the Laplacian, Poisson integrals and Green kernels) are recorded in [STRUCTURE32.md](STRUCTURE32.md).

**Maximum principles.** For the nondivergence operator \(Lu=\sum a^{ij}\partial_{ij}u+b^i\partial_iu\) on a compact set \(K\), with variable elliptic \(a\) (no regularity, not necessarily symmetric), drift bounded by \(\beta\), and \(c\ge0\), a function continuous on \(K\) and \(C^2\) in its interior with \(cu\le Lu\) is bounded by any nonnegative bound of its frontier values; the minimum principle, comparison, Dirichlet uniqueness, and the quantitative bound \(u\le m+(e^{(\beta/\lambda+1)\mathop{\mathrm{diam}}K}-1)F/\lambda\) for \(cu-F\le Lu\) follow ([non-divergence form](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/MaximumPrinciple/NonDivergence.lean)). This is the synopsis convention with \(c\) replaced by \(-c\); it is not the Alexandrov–Bakelman–Pucci \(L^n\) estimate. For the Laplacian with drift and a nonnegative zeroth-order term the weak maximum principle is proved separately, with a proof that the sign condition on \(c\) is necessary ([lower-order terms](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Laplacian/LowerOrderMaximumPrinciple.lean), [sign condition](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Laplacian/SignCondition.lean)). Hopf's boundary-point lemma and the strong maximum principle are proved for \(-\Delta-b\cdot\nabla+c\) with bounded drift and bounded \(c\ge0\), at an interior-sphere boundary point and on preconnected open sets ([Hopf lemma](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Laplacian/HopfLemma.lean), [strong maximum principle](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Laplacian/StrongMaximumPrinciple.lean)); variable principal coefficients are not covered by these two results.

**Schauder estimates.** For a constant elliptic matrix \(A\) and \(0<\alpha<1\), a \(C^2\) solution of \(\sum A_{ij}\partial_{ij}u=f\) with \(f\) \(\alpha\)-Hölder on an \(R\)-thickening of \(S\) has \(D^2u\) \(\alpha\)-Hölder on \(S\), with an explicit constant in \(\lambda,\Lambda\), the Hölder constant of \(f\), and \(R^{-(n+1)/2-\alpha}\|D^2u\|_{L^2}\) ([interior Schauder](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/Hessian/Schauder/Basic.lean)). For weak solutions of Poisson's equation \(-\Delta u=f\) with \(f\) \(\alpha\)-Hölder, the second derivatives are interior \(\alpha\)-Hölder ([Poisson \(C^{2,\alpha}\)](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/Hessian/Holder.lean)). For Hölder coefficients of small oscillation, without lower-order terms, a global a priori Schauder estimate is proved, while localization and covering are not ([variable coefficients](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/Hessian/Schauder/VariableCoefficient.lean)). Weak solutions of \(-\Delta u=-\mathop{\mathrm{div}}G\) have \(\nabla u\) Hölder where \(G\) is ([gradient Hölder](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/GradientHolder.lean)); the Campanato ingredients for variable coefficients (frozen-coefficient comparison, harmonic replacement, constant-coefficient decay) are proved ([frozen coefficients](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/FrozenCoefficient.lean), [harmonic replacement](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/HarmonicReplacement.lean), [constant-coefficient decay](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/ConstantCoefficientDecay.lean)), but the divergence-form \(C^{1,\alpha}\) estimate for variable Hölder \(A\) is not assembled.

**Calderón–Zygmund estimates.** For \(1<p<\infty\), \(\|D^2u\|_p\le C\|\Delta u\|_p\) on \(\mathbb R^n\) ([Calderón–Zygmund](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/Hessian/Lp.lean)), and \(\|D^2u\|_p\le(C/\lambda)\|L_Au\|_p\) uniformly over constant matrices with lower ellipticity constant \(\lambda\) ([constant coefficients](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/Hessian/ConstantCoefficient.lean)). The \(W^{2,p}(\mathbb R^n)\) estimate holds for constant coefficients ([strong solutions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/Hessian/Sobolev.lean)) and for measurable coefficients within \(\delta\lambda\) of a constant matrix (`TauCeti.PDE.exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq_of_abs_sub_le`; [small oscillation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/Hessian/VariableCoefficient.lean)), and a cutoff form on domains bounds \(\|\zeta D^2u\|_p\) by \(\|\zeta f\|_p\), \(\|\nabla u\|_p\) and \(\|u\|_p\) ([localization](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Regularity/Hessian/Localization.lean)). The covering and interpolation argument for continuous coefficients is not carried out.

**Supporting material.** The Euclidean Yamabe bubbles \(U_{t,b}\) are shown to solve \(a_n(-\Delta U)=n(n-1)U^{(n+2)/(n-2)}\) for \(n\ne2\) ([bubbles](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Yamabe/Bubble.lean)); the Liouville and symmetry classification of 33.21 is not proved.

**Synopsis entries.** Covered: 33.12 (TauCeti, classical \(C^2\) functions). Partly covered: 33.13 (Hopf lemma and strong maximum principle with the Laplacian as principal part), 33.16 (constant-coefficient interior estimate, Poisson's equation, and a global a priori estimate for small-oscillation coefficients without lower-order terms), 33.18 (whole-space and cutoff estimates for coefficients of small oscillation; no covering argument), 33.19 (the Laplacian, \(-\Delta u=-\mathop{\mathrm{div}}G\), only). Not covered: 33.14, 33.15, 33.17, 33.20, 33.21.

## Quasilinear equations

[Mathematical scope](SYNOPSIS33.md#quasilinear-equations).

**Synopsis entries.** Not covered: 33.73–33.76.

## Viscosity and fully nonlinear equations

[Mathematical scope](SYNOPSIS33.md#viscosity-and-fully-nonlinear-equations).

Viscosity solutions are defined only for the Monge–Ampère equation (see the Monge–Ampère section below); no general theory of viscosity solutions or fully nonlinear equations is present.

**Synopsis entries.** Not covered: 33.22–33.31.

## First-order Hamilton–Jacobi equations

[Mathematical scope](SYNOPSIS33.md#first-order-hamiltonjacobi-equations).

**Synopsis entries.** Not covered: 33.77–33.80.

## Degenerate elliptic and Monge–Ampère equations

[Mathematical scope](SYNOPSIS33.md#degenerate-elliptic-and-mongeampère-equations).

### TauCeti

**Monge–Ampère.** On a finite-dimensional real inner product space, the Aleksandrov Monge–Ampère measure of a convex function is defined as the measure of the subgradient image, \(MA_f(s)=\mu(\partial f(s\cap D))\), for Haar measure and for measures absolutely continuous with respect to it (`TauCeti.mongeAmpereMeasure`; [measure](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/MongeAmpere/Basic.lean)); the measure of a cone is a multiple of the Dirac mass at its vertex ([cone](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/MongeAmpere/Cone.lean)). On a bounded open convex \(\Omega\), for convex \(u,v\) continuous on the closure, \(MA_u\le MA_v\) and \(v\le u\) on \(\partial\Omega\) imply \(v\le u\), so solutions with given measure and boundary values are unique (`TauCeti.le_of_mongeAmpereMeasure_le_of_le_frontier`, `TauCeti.eqOn_of_mongeAmpereMeasure_eq_of_eqOn_frontier`; [comparison](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/MongeAmpere/Comparison.lean)). Under locally uniform convergence of convex functions on an open set, the measures converge weakly ([convergence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/MongeAmpere/Convergence.lean)). By Alexandrov's theorem, convex functions are twice differentiable almost everywhere ([Alexandrov's theorem](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Alexandrov.lean)), and the absolutely continuous part of the Monge–Ampère measure is the Alexandrov Hessian determinant, so an Aleksandrov solution of \(\det D^2f=h\) solves it almost everywhere ([decomposition](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/MongeAmpere/Decomposition.lean)). Viscosity sub- and supersolutions of \(\det D^2u=f\) are defined, and Aleksandrov solutions with continuous nonnegative \(f\) are viscosity solutions ([viscosity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/MongeAmpere/Viscosity.lean)). The weighted measure gives the weak form of the optimal-transport Jacobian equation ([transport](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/MongeAmpere/Transport.lean), [interpolation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/MongeAmpere/Interpolation.lean)). No existence theorem for the Dirichlet problem and no interior regularity theorem is proved. The \(p\)-Laplacian is not treated.

**Synopsis entries.** Covered: 33.36 (TauCeti; comparison on bounded open convex domains). Partly covered: 33.37 (uniqueness by comparison; no existence). Not covered: 33.32–33.35, 33.38, 33.39.

## Parabolic regularity and nonlinear diffusion

[Mathematical scope](SYNOPSIS33.md#parabolic-regularity-and-nonlinear-diffusion).

The Gaussian heat kernel, the heat semigroup on \(L^p\), the classical parabolic weak maximum principle for \(\partial_t-\Delta-b\cdot\nabla\), and existence and uniqueness for the weak parabolic Dirichlet problem with bounded measurable coefficients are described in [STRUCTURE32.md](STRUCTURE32.md). The heat kernel is treated only for the Laplacian; parabolic regularity theory, Gaussian bounds for variable coefficients, and nonlinear diffusion are not present.

**Synopsis entries.** Not covered: 33.41–33.54.

## The classical obstacle problem

[Mathematical scope](SYNOPSIS33.md#the-classical-obstacle-problem).

### Mathlib

The abstract form of a variational inequality is the projection onto a closed convex set. In a real inner product space, a nonempty complete convex set \(K\) contains a point nearest to any \(u\) (`exists_norm_eq_iInf_of_complete_convex`), and \(v\in K\) is that point exactly when \(\langle u-v,w-v\rangle\le0\) for every \(w\in K\) (`norm_eq_iInf_iff_real_inner_le_zero`, `Analysis/InnerProductSpace/Projection/Minimal.lean`). This is not instantiated for an obstacle set in a Sobolev space.

**Synopsis entries.** Partly covered: 33.55 (abstract Hilbert-space projection and its variational inequality; not instantiated for the obstacle problem). Not covered: 33.56–33.62.

## One-phase free boundaries and nonlocal regularity

[Mathematical scope](SYNOPSIS33.md#one-phase-free-boundaries-and-nonlocal-regularity).

**Synopsis entries.** Not covered: 33.63–33.72.
