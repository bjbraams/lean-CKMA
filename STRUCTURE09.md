# Structure 09: Malliavin calculus, rough paths, and stochastic partial differential equations

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS09.md); [bibliographical scope](CKMA-bib.md#ckma-09); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Probability.Distributions.Gaussian`, `Mathlib.Probability.BrownianMotion`, `Mathlib.Probability.Process`, `Mathlib.RingTheory.Polynomial.Hermite`, `Mathlib.Topology.EMetricSpace.BoundedVariation`, `Mathlib.Topology.MetricSpace.Holder`. There is no aggregate module for this subject.

**Namespaces.** Gaussian measures and processes are in `ProbabilityTheory`, with the predicate `IsGaussian` and Fernique's theorem in `ProbabilityTheory.IsGaussian`; Hermite polynomials are in `Polynomial`. The TauCeti declarations are in `TauCeti` and are identified by name below.

Filename and text searches in both libraries for Malliavin calculus, isonormal processes, the Cameron–Martin space, the Ornstein–Uhlenbeck semigroup, Young and rough integration, the sewing lemma, regularity structures, paracontrolled calculus, Poisson random measures, stochastic integrals, and stochastic PDE found no development of these theories. The recorded material consists of finite-dimensional Gaussian analysis, Fernique's theorem, and deterministic supporting structures.

<a id="structure-09a"></a>

## 09A. Malliavin Calculus and Infinite-Dimensional Analysis

The recorded Gaussian-analysis material consists of Hermite expansions in finitely many Gaussian coordinates and Fernique's theorem.

### Wiener chaos and differential calculus on Gaussian space

[Mathematical scope](SYNOPSIS09.md#wiener-chaos-and-differential-calculus-on-gaussian-space).

#### Mathlib

Mathlib has the probabilists' Hermite polynomials and their Gaussian-derivative formula, `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian` and `Polynomial.hermite_eq_deriv_gaussian` (`RingTheory/Polynomial/Hermite/Gaussian.lean`), but not their orthogonality or basis property.

**Supporting foundations.** Supporting stochastic-process structures are the Gaussian-process predicate `IsGaussianProcess` (`Probability/Distributions/Gaussian/IsGaussianProcess/Def.lean`), the real pre-Brownian and Brownian motion predicates `IsPreBrownianReal` and `IsBrownianReal` in `Probability/BrownianMotion/Basic.lean`, with the characterization of centered Gaussian processes of covariance \(\min(s,t)\) (`IsGaussianProcess.isPreBrownianReal_of_covariance`), and predictable processes in `Probability/Process/Predictable.lean`. Their detailed coverage is in [Section 08](STRUCTURE08.md). `Archive/Hairer.lean` in the Mathlib repository constructs a compactly supported smooth function whose integral against polynomials of bounded degree recovers evaluation at the origin; this is a deterministic test-function construction, not stochastic analysis.

#### TauCeti

One finite-dimensional ingredient of Gaussian analysis is present. The Hermite orthogonality relation \(\int H_mH_n\,d\gamma=\delta_{mn}\,n!\) for the standard Gaussian measure \(\gamma\) on the line is `TauCeti.integral_hermite_mul_hermite_gaussianReal` ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Orthogonality.lean)). The normalized Hermite polynomials \(H_n/\sqrt{n!}\) form a Hilbert basis of \(L^2(\gamma)\), with scalars in any `RCLike` field, and their tensor products form a Hilbert basis of \(L^2(\gamma^{\otimes\iota})\) on a finite product ([one dimension](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Distributions/Gaussian/Hermite/Basis.lean), `TauCeti.gaussianHermiteHilbertBasis`; [finite products](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Distributions/Gaussian/Hermite/Pi/Basis.lean), `TauCeti.gaussianHermitePiBasis` for a `Fintype` index). The coefficient formulas, Parseval identities, and \(L^2\)-convergent expansions are `TauCeti.gaussianHermiteHilbertBasis_repr_apply`, `TauCeti.tsum_norm_sq_integral_hermite_mul_gaussianReal`, `TauCeti.hasSum_gaussianHermite_expansion`, and their product versions `TauCeti.gaussianHermitePiBasis_repr_apply`, `TauCeti.tsum_norm_sq_integral_prod_hermite_mul_pi_gaussianReal`, and `TauCeti.hasSum_gaussianHermitePi_expansion` ([one dimension](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Distributions/Gaussian/Hermite/Parseval.lean), [finite products](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Distributions/Gaussian/Hermite/Pi/Parseval.lean)). This is the Wiener chaos decomposition for an isonormal process on a finite-dimensional \(H\), expressed in Hermite coordinates; multiple Wiener integrals and the infinite-dimensional case are absent.

**Synopsis entries.** Partly covered: 09.1 (finitely many Gaussian coordinates only, TauCeti), 09.2 (Hermite orthogonality and the orthonormal tensor Hermite basis in finitely many coordinates, TauCeti; no multiple Wiener integrals). Not covered: 09.3–09.9.

### Ornstein–Uhlenbeck analysis, densities, and normal approximation

[Mathematical scope](SYNOPSIS09.md#ornsteinuhlenbeck-analysis-densities-and-normal-approximation).

**Synopsis entries.** Not covered: 09.11–09.20.

### Gaussian measures on Banach spaces

[Mathematical scope](SYNOPSIS09.md#gaussian-measures-on-banach-spaces).

#### Mathlib

A Gaussian measure on a real topological vector space is the class `ProbabilityTheory.IsGaussian`: every continuous linear functional has a real Gaussian law, possibly degenerate (`Probability/Distributions/Gaussian/Basic.lean`). Fernique's theorem is `ProbabilityTheory.IsGaussian.exists_integrable_exp_sq`: for a Gaussian measure on a complete real normed space with its Borel σ-algebra, there is \(C>0\) with \(x\mapsto\exp(C\|x\|^2)\) integrable; centering is not assumed. With second countability added, `ProbabilityTheory.IsGaussian.memLp_id` gives moments of every finite order, and `IsGaussian.integral_dual` identifies \(\int\ell\,d\gamma\) with \(\ell\) applied to the mean (`Probability/Distributions/Gaussian/Fernique.lean`). The sharp exponent \(1/(2\sigma^2)\) and the version for measurable seminorms are not proved. The Cameron–Martin space, abstract Wiener spaces, and the Feldman–Hájek dichotomy were not found. Further detail on Gaussian measures is in [Section 06](STRUCTURE06.md).

**Synopsis entries.** Partly covered: 09.61 (existence of some \(\alpha>0\) and moments of all orders, Mathlib; not the sharp constant or the seminorm version). Not covered: 09.62–09.65.

### Analysis on Poisson space

[Mathematical scope](SYNOPSIS09.md#analysis-on-poisson-space).

Neither library has Poisson random measures, the difference operator, or the Mecke equation; only the scalar Poisson distribution is present (Mathlib `Probability/Distributions/Poisson/Basic.lean`), as supporting material.

**Synopsis entries.** Not covered: 09.66, 09.67.

<a id="structure-09b"></a>

## 09B. Rough Paths and Singular-Equation Methods

No rough-path, sewing, regularity-structure, or paracontrolled material was found in either library.

### Young integration and the algebra of rough paths

[Mathematical scope](SYNOPSIS09.md#young-integration-and-the-algebra-of-rough-paths).

The nearest supporting material is deterministic: the variation `eVariationOn` (`Topology/EMetricSpace/BoundedVariation.lean`) and Hölder continuity `HolderWith` (`Topology/MetricSpace/Holder.lean`) in Mathlib, with the further variation and absolutely-continuous-curve material recorded in [Section 05](STRUCTURE05.md).

**Synopsis entries.** Not covered: 09.21–09.24.

### Controlled integration and rough differential equations

[Mathematical scope](SYNOPSIS09.md#controlled-integration-and-rough-differential-equations).

The nearest supporting material is the deterministic ODE existence, uniqueness, and flow theory recorded in [Section 31](STRUCTURE31.md).

**Synopsis entries.** Not covered: 09.25–09.35.

### Distributional products and the entrance to singular SPDE

[Mathematical scope](SYNOPSIS09.md#distributional-products-and-the-entrance-to-singular-spde).

**Synopsis entries.** Not covered: 09.54–09.60.

<a id="structure-09c"></a>

## 09C. Stochastic Partial Differential Equations

Neither library has a Hilbert-space stochastic integral, a cylindrical Wiener process, or Walsh integration. The supporting structures recorded here are deterministic.

### Hilbert-space stochastic integration and evolution equations

[Mathematical scope](SYNOPSIS09.md#hilbert-space-stochastic-integration-and-evolution-equations).

#### TauCeti

The deterministic part of the mild formulation is present. The [abstract Cauchy problem file](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Semigroups/CauchyProblem/Basic.lean) defines classical and mild solutions of \(u'=Au\), \(u(0)=x\), for a linear operator \(A\) on a real normed space (`TauCeti.IsClassicalSolution`, `TauCeti.IsMildSolution`), and proves, on a real Banach space, that every orbit of a strongly continuous semigroup is a mild solution and that orbits from the generator domain are classical solutions (`TauCeti.isMildSolution_realOperator`, `TauCeti.isClassicalSolution_realOperator`). The [uniqueness file](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Semigroups/CauchyProblem/Uniqueness.lean) shows that every classical or mild solution agrees with the semigroup orbit on \([0,\infty)\) (`TauCeti.IsMildSolution.eq_realOperator`, `TauCeti.IsMildSolution.unique`). These are linear deterministic evolution equations without forcing.

**Supporting foundations.** The Hilbert–Schmidt norm of a bounded operator between Hilbert spaces, defined by a basis-independent sum over a Hilbert basis, is `ContinuousLinearMap.hilbertSchmidtNorm` ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/HilbertSchmidt/Basic.lean)), with the ideal inequality; the triangle inequality and the space \(L_2(U,H)\) as a Hilbert space are not established there. Detailed semigroup coverage is in [Section 24](STRUCTURE24.md).

**Synopsis entries.** Not covered: 09.36–09.41, 09.68.

### Variational solutions and invariant measures

[Mathematical scope](SYNOPSIS09.md#variational-solutions-and-invariant-measures).

#### TauCeti

The deterministic variational framework is present as supporting material. The [Gelfand triple file](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/GelfandTriple.lean) defines the map \(H\to V^*\) induced by a continuous linear \(\iota:V\to H\) (`ContinuousLinearMap.gelfandDual`) and proves its injectivity for dense range. The energy space of \(u\in L^2(a,b;V)\) with weak time derivative in \(L^2(a,b;V^*)\) is `TauCeti.EvolutionSpace`, with continuous representatives in \(C([a,b];H)\) ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/EvolutionSpace/Basic.lean)). For the linear deterministic problem \(u'+A(t)u=f\) with bounded \(A(t):V\to V^*\) satisfying Gårding's inequality, \(f\in L^2(a,b;V^*)\), and \(u_0\in H\), the [existence file](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Parabolic/Existence.lean) proves existence of a variational solution in \(L^2(a,b;V)\) (`TauCeti.exists_memLp_forall_setIntegral_eq_add_inner`) and, for separable \(V\), its weak time derivative (`TauCeti.hasWeakLineDerivOn_gelfandDual_of_forall_setIntegral_eq_add_inner`). These are the linear deterministic analogues of the setting of 09.42–09.43; there is no stochastic term, nonlinear monotone operator, Markov semigroup, or invariant measure.

**Synopsis entries.** Not covered: 09.42–09.47.

### Random-field SPDE and spatial regularity

[Mathematical scope](SYNOPSIS09.md#random-field-spde-and-spatial-regularity).

#### TauCeti

As supporting material, the heat kernel \(p_t(x)=(4\pi t)^{-n/2}e^{-|x|^2/(4t)}\) on a finite-dimensional real inner product space is `TauCeti.heatKernel`, with positivity, unit mass, the semigroup identity, and the heat equation ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/HeatKernel/Basic.lean)), and the heat semigroup on \(L^p\), \(1\le p<\infty\), is a strongly continuous contraction semigroup (`TauCeti.heatSemigroup`, [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/HeatKernel/Semigroup.lean)). There is no stochastic convolution against white noise.

**Synopsis entries.** Not covered: 09.48–09.53.
