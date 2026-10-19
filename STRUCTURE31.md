# Structure 31: Ordinary differential equations and dynamical systems

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS31.md); [bibliographical scope](CKMA-bib.md#ckma-31); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.ODE.Basic`, `Mathlib.Analysis.ODE.Gronwall`, `Mathlib.Analysis.ODE.DiscreteGronwall`, `Mathlib.Analysis.ODE.PicardLindelof`, `Mathlib.Analysis.ODE.ExistUnique`, `Mathlib.Analysis.ODE.Transform`, `Mathlib.Geometry.Manifold.IntegralCurve.Basic`, `Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique`, `Mathlib.Geometry.Manifold.IntegralCurve.UniformTime`, `Mathlib.Geometry.Manifold.IntegralCurve.Transform`, `Mathlib.Dynamics.Flow`, `Mathlib.Dynamics.OmegaLimit`, `Mathlib.Dynamics.Transitive`, `Mathlib.Dynamics.Minimal`, `Mathlib.Dynamics.PeriodicPts.Defs`, `Mathlib.Dynamics.FixedPoints.Defs`, `Mathlib.Dynamics.FixedPoints.Topology`, `Mathlib.Dynamics.FixedPoints.Support`, `Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber`, `Mathlib.Dynamics.TopologicalEntropy.CoverEntropy`, `Mathlib.Dynamics.TopologicalEntropy.NetEntropy`, `Mathlib.Dynamics.TopologicalEntropy.Semiconj`, `Mathlib.Dynamics.SymbolicDynamics.Basic`, `Mathlib.Analysis.SpecialFunctions.Exponential`.

**Namespaces.** `IsPicardLindelof` and `ODE` for the Euclidean initial-value theory, with the continuously differentiable case under `ContDiffAt`. Flows are `Flow`. Topological entropy is `Dynamics`. Lifts of monotone circle maps are `CircleDeg1Lift`. Fixed and periodic points are `Function`. Minimal and topologically transitive actions are `MulAction` and `AddAction`. Symbolic dynamics is `SymbolicDynamics`, with nested `FullShift` and `Pattern`. TauCeti's ODE results are in `ODE`, `TauCeti` and `ContinuousLinearMap`, its flows in `Flow` and `TauCeti`, and its Morse-theoretic gradient flows in `TauCeti`.

## Existence, uniqueness, and dependence

[Mathematical scope](SYNOPSIS31.md#existence-uniqueness-and-dependence).

### Mathlib

**Integral curves in a normed space.**

Let \(E\) be a real normed space and let \(v\) be a time-dependent vector field on \(E\). A curve \(\gamma\) is an integral curve of \(v\) on a set of times when, at each such time, the derivative of \(\gamma\) within that set equals \(v\) evaluated along \(\gamma\). It is a local integral curve at \(t_0\) when this holds throughout some neighborhood of \(t_0\), and a global integral curve when it holds at every real time. On an open set of times the restricted and local notions agree. An integral curve is continuous on its interval of definition (`Analysis/ODE/Basic.lean`).

Translating or scaling the time parameter produces an integral curve of the correspondingly translated or scaled field. If the field vanishes at every time at a point, the constant curve at that point is a global integral curve (`Analysis/ODE/Transform.lean`).

The set-of-times predicate `IsIntegralCurveOn` is explicitly defined and uses the derivative within that set.

**Grönwall’s inequality.**

The comparison function used throughout is
\[
G(\delta,K,\varepsilon,x)=
\begin{cases}
\delta+\varepsilon x & \text{if }K=0,\\
\delta\,e^{Kx}+\dfrac{\varepsilon}{K}\bigl(e^{Kx}-1\bigr) & \text{if }K\neq 0.
\end{cases}
\]
If \(f:\mathbb{R}\to E\) is continuous on \([a,b]\), has a right derivative \(f'\) at each point of \([a,b)\), satisfies \(\|f(a)\|\le\delta\), and satisfies \(\|f'(x)\|\le K\|f(x)\|+\varepsilon\) on \([a,b)\), then \(\|f(x)\|\le G(\delta,K,\varepsilon,x-a)\) for every \(x\in[a,b]\). The real-valued form that feeds the proof uses a right liminf of difference quotients in place of a derivative (`Analysis/ODE/Gronwall.lean`).

If \(f(a)=0\) and \(\|f'(x)\|\le K\|f(x)\|\) on \([a,b)\), then \(f\) vanishes on \([a,b]\).

The same bound controls ODEs. If two curves are continuous on \([a,b]\), have right derivatives on \([a,b)\), remain in a time-dependent set on which \(v(t,\cdot)\) is Lipschitz with constant \(K\), and each derivative approximates \(v\) along the curve up to errors \(\varepsilon_f\) and \(\varepsilon_g\), and if their distance at time \(a\) is at most \(\delta\), then their distance at time \(t\in[a,b]\) is at most \(G(\delta,K,\varepsilon_f+\varepsilon_g,t-a)\). For exact solutions the errors vanish and the distance is at most \(\delta\,e^{K(t-a)}\). The same statements hold when the Lipschitz condition is global rather than restricted to a time-dependent set.

An inequality with a time-dependent coefficient \(K(x)\) is explicitly left open.

The discrete inequality is separate (`Analysis/ODE/DiscreteGronwall.lean`). Over an ordered commutative semiring, if \(u(n+1)\le c(n)\,u(n)+b(n)\) and \(c(n)\ge 0\) for \(n\ge n_0\), then
\[
u(n)\le u(n_0)\prod_{i\in[n_0,n)}c(i)+\sum_{k\in[n_0,n)}b(k)\prod_{i\in[k+1,n)}c(i).
\]
Over \(\mathbb{R}\), if \(u(n+1)\le\bigl(1+c(n)\bigr)u(n)+b(n)\) with \(u(n_0)\), \(b\), and \(c\) nonnegative, then
\[
u(n)\le\Bigl(u(n_0)+\sum_{k\in[n_0,n)}b(k)\Bigr)\exp\Bigl(\sum_{i\in[n_0,n)}c(i)\Bigr).
\]
A uniform bound of the same shape holds for all \(n\) in a half-open integer interval, with the sums extended to the right endpoint of that interval.

**Picard–Lindelöf.**

The contraction-mapping theorem used in the existence proof is the Banach fixed-point theorem of section 35 (`Topology/MetricSpace/Contracting.lean`); it is not restated here.

Let \(E\) be a real normed space and let \(f\) be a time-dependent vector field. The Picard–Lindelöf package on a closed time interval \([t_{\min},t_{\max}]\) about a time \(t_0\), centered at a point \(x_0\), with nonnegative constants \(a,r,L,K\), consists of four hypotheses: \(f(t,\cdot)\) is \(K\)-Lipschitz on the closed ball of radius \(a\) about \(x_0\), for every \(t\) in the interval; \(t\mapsto f(t,x)\) is continuous on the interval, for every \(x\) in that ball; \(\|f(t,x)\|\le L\) throughout the same set; and \(L\) times the larger of \(t_{\max}-t_0\) and \(t_0-t_{\min}\) is at most the truncated difference \(a-r\) of nonnegative reals (`Analysis/ODE/PicardLindelof.lean`). A time-independent field that is \(K\)-Lipschitz and bounded by \(L\) on the ball satisfies the package. A time-independent field of class \(C^1\) at \(x_0\) satisfies the package on some symmetric open time interval, for a positive radius \(r\) of initial data.

If \(E\) is complete, every initial value \(x\) in the closed ball of radius \(r\) about \(x_0\) admits a curve \(\alpha\) on \([t_{\min},t_{\max}]\) with \(\alpha(t_0)=x\) and
\[
\alpha(t)=x+\int_{t_0}^{t}f(\tau,\alpha(\tau))\,d\tau.
\]
Equivalently, \(\alpha\) has derivative \(f(t,\alpha(t))\) within the closed interval (`Analysis/ODE/ExistUnique.lean`). The solutions may be chosen as a local flow of the initial condition. That flow is Lipschitz in the initial condition, uniformly for each fixed time in the interval, and the joint map \((x,t)\mapsto\alpha(x,t)\) is continuous on the product of the closed ball with the closed interval.

If the field is time-independent and merely of class \(C^1\) at \(x_0\), completeness of \(E\) again gives an open interval about any prescribed initial time on which every initial value in some closed ball has a solution, and a flow defined on a neighborhood of \((x_0,t_0)\) in \(E\times\mathbb{R}\).

Uniqueness does not use completeness. If \(v(t,\cdot)\) is Lipschitz on a time-dependent set, and two curves are continuous on a closed interval, have the ODE as a right derivative on the half-open interval, remain in that set, and agree at the left endpoint, then they agree throughout the closed interval. The time-reversed statement, with left derivatives and the right endpoint as the initial time, is included. If the initial time lies in the open interval and the curves are genuinely differentiable there, they agree on the whole closed interval, hence on the open interval. Local uniqueness follows: near a time at which the field is Lipschitz in space, two solutions that remain in the Lipschitz set and share an initial value agree on a neighborhood of that time. A globally Lipschitz field has unique solutions on every compact time interval with a prescribed initial value, and a field that is Lipschitz in space at every time, on a time-dependent set that traps both solutions, has at most one global solution with a given initial value.

The estimates give continuous dependence of exact solutions at an exponential rate, but Mathlib has no continuation theorem up to the boundary of the domain.

**Integral curves on manifolds.**

On a \(C^1\) manifold, an integral curve of a vector field is a curve whose tangent vector equals the field along the curve, either globally, on a prescribed set of times, or on a neighborhood of one time (`Geometry/Manifold/IntegralCurve/Basic.lean`). Time translation and scaling act as in the vector-space case. A constant curve at a zero of the field is a global integral curve (`Geometry/Manifold/IntegralCurve/Transform.lean`).

Local existence: if the model space is a Banach space, the manifold is \(C^1\), the point is an interior point, and the vector field is \(C^1\) at that point as a map into the tangent bundle, then some local integral curve passes through the point at any prescribed time. On a manifold without boundary every point is interior, so the interior hypothesis drops (`Geometry/Manifold/IntegralCurve/ExistUnique.lean`). The argument is Picard–Lindelöf in a chart. Curves that meet the boundary are not treated; that case is left open.

Local uniqueness: two local integral curves of a vector field that is \(C^1\) at an interior point, and that pass through the same point at the same time, agree on a neighborhood of that time. On a manifold without boundary the interior hypothesis drops.

If the manifold is Hausdorff, the field is \(C^1\) everywhere, and two integral curves on an open interval take values in the interior and agree at one time of the interval, then they agree on the whole interval. Global integral curves that remain in the interior, and that agree at one time, are identical. On a manifold without boundary the interior hypothesis drops, so global integral curves of a \(C^1\) field are unique given one point of the trajectory. A global integral curve that returns to a point is periodic with the corresponding period, and a global integral curve is either injective or periodic with some positive period.

The uniform-time lemma assumes a boundaryless Hausdorff \(C^1\) manifold and a globally \(C^1\) vector field (`Geometry/Manifold/IntegralCurve/UniformTime.lean`). If one \(\varepsilon>0\) serves for every point, in the sense that every point lies on an integral curve defined at least on \((-\varepsilon,\varepsilon)\), then every point lies on a global integral curve. Overlapping integral curves on open intervals that agree at one common time may be patched.

### TauCeti

For globally Lipschitz autonomous vector fields on a real Banach space, TauCeti constructs unique solutions for all real times, with the flow law, joint continuity, and exponential dependence estimates (`ODE.globalSolution`, `ODE.eq_globalSolution`; [global solutions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/GlobalSolution.lean)); these solutions form a Mathlib `Flow` (`TauCeti.flowOfLipschitz`), which is \(C^{n+1}\) when the field is (`TauCeti.contDiff_flowOfLipschitz`), and whose derivative \(D\varphi_t(x)\) solves the variational equation \(\frac{d}{dt}D\varphi_t(x)=Dv(\varphi_tx)\circ D\varphi_t(x)\), \(D\varphi_0(x)=I\) (`TauCeti.hasDerivAt_fderiv_flowOfLipschitz`); for a flow with differentiable time maps, \(D\varphi_t(x)\) is invertible with inverse \(D\varphi_{-t}(\varphi_tx)\) ([flow](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Dynamics/Flow/OfLipschitz.lean), [variational equation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Dynamics/Flow/Variational.lean)). Orbits of such flows depend locally uniformly on the initial point ([convergence of orbits](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Dynamics/Flow/Convergence.lean)).

Smooth dependence on data is proved. For a smooth parametrized autonomous field on Banach spaces, local solutions of the Picard equation depend smoothly on the parameter, by an implicit-function argument (`ODE.exists_contDiffOn_picard_solution_of_contDiff`); a change of variables turns the initial condition into a parameter, so the global solution of a globally Lipschitz \(C^{n+1}\) field is \(C^{n+1}\) jointly in initial condition and time (`ODE.contDiff_globalSolution`; [parameters](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/SmoothParameter.lean), [initial conditions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/InitialCondition.lean)). A solution gains one derivative over a right-hand side differentiable on its range ([regularity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/Regularity.lean)). Mathlib's Picard–Lindelöf theorem by itself gives only Lipschitz dependence on the initial condition.

Linear equations \(x'=M(t)x+F(t)\) on \([a,b]\) in a Banach space, with \(M\) strongly measurable and essentially bounded and \(F\) integrable, have a unique continuous solution of the integral (Carathéodory) equation (`TauCeti.exists_continuousOn_eq_forall_mem_Icc_eq_picard`, `TauCeti.eqOn_of_forall_mem_Icc_eq_picard`; [Carathéodory](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/Caratheodory.lean)); nonlinear Carathéodory equations are not treated. The integral form of Grönwall's inequality is proved: a continuous \(\varphi\) with \(\varphi(t)\le c+K\int_a^t\varphi\), \(K\ge0\), satisfies \(\varphi(t)\le ce^{K(t-a)}\) (`TauCeti.le_mul_exp_of_le_add_mul_integral`; [integral Grönwall](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/Gronwall.lean)). The local Frobenius theorem for total differential equations \(Du(x)=f(x,u(x))\) gives local existence and uniqueness under the integrability (symmetry) condition, with solutions depending smoothly on their initial value ([Frobenius](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/Frobenius.lean)). For a \(C^1\) autonomous field there are a radius and a uniform time such that every initial point in the ball has a solution on that time interval staying in a prescribed neighbourhood ([uniform time](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/UniformTime.lean)).

On manifolds without boundary TauCeti constructs maximal integral curves, proves extension through finite endpoints when an accumulation point exists, and proves global existence when a curve remains in a compact set ([maximal curves](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/IntegralCurve/Maximal.lean), [extension](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/IntegralCurve/Extension.lean)). Presented as a partial flow, the maximal flow satisfies the domain-aware group law, and a maximal trajectory approaching a finite right endpoint eventually leaves every compact set (`TauCeti.eventually_flowOf_notMem`); for finite-dimensional models the flow domain is open and the flow is jointly \(C^n\) for a \(C^n\) field ([maximal flow](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/Flow/Basic.lean), [smooth dependence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/IntegralCurve/SmoothDependence.lean), [smooth flow](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/IntegralCurve/SmoothFlow.lean), [flow law](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/IntegralCurve/Flow.lean)). Compact boundaryless manifolds therefore have complete \(C^1\) vector fields, as does a \(C^1\) field vanishing outside a compact set on any boundaryless Banach manifold, and the maximal integral curves of a complete field assemble into a Mathlib `Flow` ([compact support](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/IntegralCurve/CompactSupport.lean), [complete fields](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/Flow/Complete.lean), [global flow](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/IntegralCurve/GlobalFlow.lean)). Integral curves gain one derivative over a \(C^n\) field ([regularity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/IntegralCurve/Regularity.lean)).

**Synopsis entries.** Partly covered: 31.2 (Mathlib: local existence by Picard iteration and uniqueness for fields Lipschitz in space; maximal solutions only in TauCeti, for autonomous \(C^1\) fields on boundaryless manifolds), 31.3 (TauCeti: linear equations with bounded measurable coefficients only), 31.4 (TauCeti: autonomous \(C^1\) fields on boundaryless manifolds), 31.5 (TauCeti: globally Lipschitz autonomous fields), 31.7 (Mathlib: Lipschitz dependence on the initial condition on the Picard–Lindelöf interval and exponential Grönwall bounds; TauCeti: smooth parameter dependence), 31.8 (TauCeti: autonomous fields, globally Lipschitz on Banach spaces or local on finite-dimensional manifolds; variational equation for the initial derivative only), 31.9 (time maps of global flows are homeomorphisms with inverse the negative-time map, with invertible derivatives for differentiable flows; no flow-box theorem). Not covered: 31.1, 31.10–31.12.

## Linear systems, periodic coefficients, and boundary problems

[Mathematical scope](SYNOPSIS31.md#linear-systems-periodic-coefficients-and-boundary-problems).

### Mathlib

As supporting infrastructure, \(t\mapsto\exp(tA)\) is differentiable with derivative \(A\exp(tA)\) for \(A\) in a complete normed algebra (`hasDerivAt_exp_smul_const`, `Analysis/SpecialFunctions/Exponential.lean`). Fundamental matrices, Liouville's formula, Floquet theory, and Sturm theory are absent.

### TauCeti

The Carathéodory theorem above gives existence and uniqueness for \(x'=M(t)x+F(t)\) with essentially bounded measurable \(M\); the evolution-operator formulation is not stated. For a bounded operator \(B\) on a real Banach space and continuous forcing, \(u'=Bu+f\) has the unique global solution given by the integrating-factor formula \(\exp(tB)(\exp(-t_0B)x+\int_{t_0}^t\exp(-sB)f(s)\,ds)\) ([inhomogeneous equations](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/Inhomogeneous.lean)). For linear systems, \(t\mapsto\exp(tA)x\) is the flow of a bounded operator (`ContinuousLinearMap.flow`), and for a symmetric operator \(T\) in finite dimension the solutions decaying in forward or backward time are exactly the negative and positive spectral subspaces (`LinearMap.IsSymmetric.stableSet_flow_eq_negativeSpectralSubspace`; [linear flows](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/Linear.lean)), with explicit exponential dichotomy estimates ([symmetric dichotomy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/ExponentialDichotomy.lean)). Under forward and backward exponential estimates for a projection, the Lyapunov–Perron integral is a bounded linear operator on bounded continuous forcing on the half-line, of norm at most \(2K/\alpha\) (`ContinuousLinearMap.norm_lyapunovPerronIntegralCLM_le`; [linear Lyapunov–Perron operator](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/LyapunovPerron/Linear.lean)).

For the trajectory operator \(D_A=d/ds+A(s)\) on the line, with \(A\) an essentially bounded family of operators, TauCeti proves boundedness from the first-order weak-derivative space to \(L^p\) ([trajectory operator](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/TrajectoryOperator.lean)); for a \(C^1\) family of symmetric operators on a finite-dimensional space with invertible limits at \(\pm\infty\) and \(A'\to0\), energy estimates give a finite-dimensional kernel and closed range on \(W^{1,2}(\mathbb R,E)\) (`TauCeti.WeakDerivStep.finiteDimensional_ker_trajectoryOperator`, `TauCeti.WeakDerivStep.isClosed_range_trajectoryOperator`; [energy estimates](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/EnergyEstimate/Basic.lean), [global estimates](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/EnergyEstimate/Global.lean), [adjoint](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/EnergyEstimate/Adjoint.lean), [Sobolev realization](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/EnergyEstimate/Sobolev.lean)). The full Fredholm property is not asserted.

For the regular Sturm–Liouville problem TauCeti has the Dirichlet case through its elliptic theory: for a coercive symmetric divergence-form operator on a bounded open set, the Dirichlet eigenvalues are positive, with finite-dimensional eigenspaces and an orthonormal eigenbasis of \(L^2\) ([Dirichlet spectrum](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Spectrum/Basic.lean)); on an interval \((a,b)\) the Dirichlet spectrum of \(-d^2/dx^2\) is exactly \(\{(k\pi/(b-a))^2:k\ge1\}\) with sine eigenfunctions (`TauCeti.PDE.isDirichletEigenvalue_laplacian_intervalDomain_iff`; [interval spectrum](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Spectrum/Interval.lean)).

**Synopsis entries.** Partly covered: 31.13 (TauCeti: existence and uniqueness for linear systems with bounded measurable coefficients; no fundamental-matrix statement), 31.14 (TauCeti: constant bounded operator), 31.16 (solutions \(e^{tA}x_0\); for symmetric \(A\) the decaying solutions are the negative spectral subspace; no eigenvalue stability criterion), 31.19 (TauCeti: exponential dichotomies for symmetric operators and the half-line Lyapunov–Perron operator), 31.21 (TauCeti: Dirichlet conditions with weight one, real positive eigenvalues of finite multiplicity and an orthonormal eigenbasis; explicit spectrum only for \(-u''\); simplicity and the asymptotics not stated). Not covered: 31.15, 31.17–31.18, 31.20, 31.22, 31.65.

## Stability, invariant manifolds, and limit sets

[Mathematical scope](SYNOPSIS31.md#stability-invariant-manifolds-and-limit-sets).

### Mathlib

**Flows, limit sets, and recurrence.**

A flow of an additive topological monoid on a topological space is a jointly continuous monoid action (`Dynamics/Flow.lean`). The nonnegative times give a forward flow. Orbits and forward orbits are invariant and forward-invariant respectively. An invariant set inherits a flow. A continuous self-map determines a flow of \(\mathbb{N}\), and a homeomorphism determines a flow of \(\mathbb{Z}\). When the time monoid is a group, each time map is a homeomorphism, with inverse given by the opposite time, and the flow may be reversed. A semiconjugacy intertwines two flows of the same time monoid, and factors are the existence of such a map.

The \(\omega\)-limit of a set under a time-dependent map, relative to a filter of times, is the intersection of the closures of the forward images along sets in the filter (`Dynamics/OmegaLimit.lean`). It is closed. A point lies in it precisely when every neighborhood of the point meets the image of the set at times that occur arbitrarily late in the filter. Finite unions pass inside the limit set exactly, and arbitrary unions pass in one direction. On a compact space, the \(\omega\)-limit of a nonempty set along a proper filter is nonempty. More generally it is nonempty when the forward images are eventually trapped in a compact set. For a flow, if the filter is invariant under time translation, the \(\omega\)-limit is invariant, and pushing the set forward by a fixed time does not change it.

A monoid action is minimal when every orbit is dense (`Dynamics/Minimal.lean`). A nonempty invariant set is then dense, and a closed invariant set is empty or everything. For a group acting minimally, the translates of a nonempty open set cover the space. If the action is also continuous, finitely many translates cover any compact set.

A monoid action is topologically transitive when every pair of nonempty open sets has some translate of the first meeting the second (`Dynamics/Transitive.lean`). Equivalently, the union of the translates of any nonempty open set is dense, and so is the union of its preimages.


### TauCeti

For a bounded linear part \(A\) on a Banach space with forward and backward exponential estimates for a projection \(P\) (an exponential dichotomy) and a globally Lipschitz nonlinearity \(N\) of small constant, the Lyapunov–Perron construction describes the initial values of the solutions of \(y'=Ay+N(y)\) that stay bounded in forward time as a Lipschitz graph over the range of \(P\) ([Lyapunov–Perron fixed point](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/LyapunovPerron/Basic.lean), [graph](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/LyapunovPerron/Graph.lean)). Cutting off a nonlinearity that is only small near the equilibrium gives the local version: the forward trajectories confined to a small ball form the graph of a map over a ball in the stable subspace (`ContinuousLinearMap.setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image`); if \(N(0)=0\) and \(N\) is \(C^1\) with uniformly continuous derivative near \(0\), the graph map is \(C^1\) (`ContinuousLinearMap.contDiffAt_localStableGraphMap`) with derivative zero at \(0\), hence tangent to the stable subspace, and the same holds for unstable graphs; the graphs are topological embeddings, and remain so when transported along a flow ([local graphs](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/LyapunovPerron/Local.lean), [\(C^1\) dependence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/LyapunovPerron/Smooth.lean), [embedding](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/LyapunovPerron/Embedding.lean), [transport](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Dynamics/Flow/Graph.lean)). The dichotomy estimates themselves are supplied only for symmetric operators in finite dimension, as recorded in the previous section. Stable and unstable sets of a general real flow are invariant and can be nonempty only at fixed points ([stable sets](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Dynamics/Flow/Stable.lean)), and flows can be transported along homeomorphisms ([conjugacy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Dynamics/Flow/Conjugacy.lean)).

**Gradient flows.** Along a negative gradient trajectory in a real Hilbert space, \(\frac{d}{dt}f(\gamma(t))=-\|\nabla f(\gamma(t))\|^2\), with the energy identity \(\int_a^b\|\nabla f(\gamma)\|^2=f(\gamma(a))-f(\gamma(b))\); a periodic trajectory is constant ([gradient trajectories](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Morse/GradientFlow.lean)). A forward trajectory confined to a compact set on which \(f\) has finitely many critical points converges to a critical point, and the convergence is exponential at a nondegenerate one ([convergence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Morse/Convergence.lean), [exponential convergence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Morse/ExponentialConvergence.lean)). At a nondegenerate critical point the Hessian splitting gives an exponential dichotomy, local stable and unstable graphs are assembled explicitly, and when \(f\) is \(C^2\) with globally Lipschitz gradient on a finite-dimensional space the global stable and unstable sets are embedded \(C^1\) submanifolds of dimensions \(n-\operatorname{ind}\) and \(\operatorname{ind}\) ([local invariant manifolds](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Morse/LocalInvariantManifold.lean), [global charts](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Morse/GlobalChart.lean), [manifold structure](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Morse/Manifold.lean)). On a compact boundaryless manifold, the flow of a pseudo-gradient adapted to a Morse function has every orbit converging forward and backward to critical points, and the stable and unstable sets are smooth submanifolds ([pseudo-gradient flow](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/Morse/PseudoGradient/Flow.lean), [stable manifolds](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/Morse/Stable/Manifold.lean)).

**Lyapunov functions and ω-limits.** For a real flow on a compact Hausdorff space and a continuous \(g\) antitone along every orbit, if the points along whose orbits \(g\) is constant lie in a finite set \(C\), every orbit converges in forward time to a point of \(C\) (`Flow.exists_tendsto_atTop_of_antitone`); a strict maximum of \(g\) is a fixed point with trivial stable set ([Lyapunov functions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Dynamics/Flow/Lyapunov.lean)). The ω-limit set of a curve \(u:[a,\infty)\to X\), as its set of cluster points at \(+\infty\), is the intersection of the closures of its tails, and is preconnected when the curve is continuous and confined to a compact subset of a Hausdorff space (`TauCeti.isPreconnected_setOf_mapClusterPt_atTop`; [ω-limits of curves](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Topology/OmegaLimit.lean)); Mathlib's `mem_omegaLimit_singleton_iff_mapClusterPt` identifies this set with Mathlib's ω-limit of a single orbit.

**Synopsis entries.** Covered: 31.32 (Mathlib, TauCeti). Partly covered: 31.26 (TauCeti: compact Hausdorff phase space and finitely many points with \(g\)-constant orbits), 31.27 (TauCeti: \(C^1\) local graphs under an exponential dichotomy with small nonlinearity, dichotomies supplied for symmetric linear parts and gradient flows; no \(C^r\), \(r\ge2\)), 31.33 (TauCeti: finitely many critical points in the compact region, exponential rate at nondegenerate ones; no Łojasiewicz theorem). Not covered: 31.23–31.25, 31.28–31.31.

## Periodic orbits and planar dynamics

[Mathematical scope](SYNOPSIS31.md#periodic-orbits-and-planar-dynamics).

### Mathlib

As supporting material, a global integral curve of a \(C^1\) field on a boundaryless Hausdorff manifold is either injective or periodic with some positive period (`Geometry/Manifold/IntegralCurve/ExistUnique.lean`, recorded above). Return maps, Floquet multipliers of periodic orbits, and planar topology of flows are absent.

### TauCeti

For a globally Lipschitz Hamiltonian vector field on a finite-dimensional symplectic vector space the Hamiltonian is constant along each orbit (`TauCeti.SymplecticForm.hamiltonianFlow_conserves`; see the last section).

**Synopsis entries.** Partly covered: 31.42 (TauCeti: conservation of energy for globally Lipschitz Hamiltonian fields; periodicity of compact regular energy curves not stated). Not covered: 31.34–31.41.

## Normal forms, local bifurcations, and averaging

[Mathematical scope](SYNOPSIS31.md#normal-forms-local-bifurcations-and-averaging).

**Synopsis entries.** Not covered: 31.43–31.51, 31.72.

## Hyperbolicity and complex orbit structure

[Mathematical scope](SYNOPSIS31.md#hyperbolicity-and-complex-orbit-structure).

### Mathlib

**Topological entropy and symbolic dynamics (supporting material).**

Topological entropy is the Bowen–Dinaburg entropy of a self-map of a uniform space, valued in the extended reals, and defined for an arbitrary subset rather than only for an invariant set (`Dynamics/TopologicalEntropy/CoverEntropy.lean`). Dynamical balls are the entourages of pairs whose first \(n\) iterates remain in a given entourage (`Dynamics/TopologicalEntropy/DynamicalEntourage.lean`). Cover entropy is the exponential growth, as \(n\to\infty\), of the least cardinality of a dynamical cover, first along one entourage and then as a supremum over entourages. Both a liminf and a limsup are defined. The empty set has entropy \(-\infty\). On a subset invariant under the map, the liminf and limsup entropies agree. Net entropy is the same construction with separated sets in place of covers (`Dynamics/TopologicalEntropy/NetEntropy.lean`). Cover entropy equals the supremum, over entourages, of the net entropy along those entourages, both for the liminf and for the limsup. A uniformly continuous semiconjugacy does not increase cover entropy, and the entropy of the restriction of a map to an invariant set equals the entropy of that set (`Dynamics/TopologicalEntropy/Semiconj.lean`). The uniform-space definition applies to pseudo-metric spaces too. A separate presentation through metric dynamical balls is left open.

On a left-cancellative monoid, the full shift is the space of functions from the monoid to an alphabet, with the product topology and the translation action (`Dynamics/SymbolicDynamics/Basic.lean`). Cylinders and occurrence sets of finite patterns are clopen when the alphabet is discrete. A subshift is a closed translation-invariant subset. Forbidding a family of patterns defines a subshift, including the special case of a finite forbidden list. The module comment names “subshift of finite type”, but no separate predicate or bundled definition for it is declared. The language of a subshift on a finite window is the set of patterns realized by its configurations. Geometry special to \(\mathbb{Z}^d\), including box entropy, is deferred by the file itself.

### TauCeti

For negative gradient flows TauCeti formulates the Morse–Smale transversality condition (`TauCeti.IsMorseSmale`) and proves its local consequences: near a point of \(W^u(p)\cap W^s(q)\) the intersection is an embedded \(C^1\) submanifold of the expected dimension ([Morse–Smale condition](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Morse/MorseSmale/Basic.lean), [transversality](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Morse/Transversality.lean)). Sequences of trajectories converge to broken trajectories through intermediate rest points (`Flow.exists_tendsto_mem_unstableSet_of_tendsto_mem_stableSet`; [breaking](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Dynamics/Flow/Breaking.lean)), and nonconstant orbits with a limit are injectively parametrized ([connecting orbits](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Dynamics/Flow/ConnectingOrbit.lean)). For a \(C^2\) function on an open subset of a finite-dimensional space, almost every linear perturbation is Morse ([genericity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Morse/Generic.lean)). These concern gradient flows; hyperbolic sets, shadowing, Markov partitions, and structural stability are absent.

**Synopsis entries.** Not covered: 31.52–31.59, 31.73.

## One-dimensional dynamics

[Mathematical scope](SYNOPSIS31.md#one-dimensional-dynamics).

### Mathlib

**Circle maps.**

A monotone lift of a degree-one circle map is a monotone map \(f:\mathbb{R}\to\mathbb{R}\) with \(f(x+1)=f(x)+1\) (`Dynamics/Circle/RotationNumber/TranslationNumber.lean`). Such maps form a monoid, and the bijective ones are order automorphisms of the line. The translation number is
\[
\tau(f)=\lim_{n\to\infty}\frac{f^n(x)-x}{n},
\]
and the limit exists for every \(x\). It is monotone in \(f\), additive on commuting pairs, and changes sign under inversion. For a continuous lift there is a point with \(f(x)=x+\tau(f)\). For continuous \(f\), the translation number is an integer if and only if \(f(x)=x+m\) for some \(x\) and that integer \(m\), and it equals \(m/n\), \(n>0\), if and only if \(f^n(x)=x+m\) for some \(x\) (`CircleDeg1Lift.translationNumber_eq_rat_iff`). Two bijective lifts with the same translation number are semiconjugate by a monotone degree-one lift, not necessarily continuous or bijective (`CircleDeg1Lift.semiconj_of_bijective_of_translationNumber_eq`); in particular a bijective lift is semiconjugate in this sense to the translation by its translation number. Continuity of the translation number in \(f\) is not proved. A rotation number of an actual circle homeomorphism, as an object distinct from \(\tau\) of a lift, is marked as future work in the file.

**Periodic and fixed points (supporting material).**

A point is periodic of period \(n\) for a self-map when the \(n\)-th iterate fixes it. The definition allows \(n=0\), for which every point qualifies. The minimal period is the least positive such \(n\), or zero if the point is not periodic for any positive \(n\). The point has period \(n\) if and only if the minimal period divides \(n\). The map is bijective on the set of points of each fixed period and on the set of all periodic points (`Dynamics/PeriodicPts/Defs.lean`).

On a Hausdorff space, the fixed-point set of a continuous self-map is closed. If the iterates of a point converge to \(y\) and the map is continuous at \(y\), then \(y\) is fixed (`Dynamics/FixedPoints/Topology.lean`). The fixed support, meaning the closure of the set of non-fixed points, and the condition that this support be compact, are recorded (`Dynamics/FixedPoints/Support.lean`).

**Synopsis entries.** Partly covered: 31.61 (Mathlib, at the level of lifts: existence and independence of the translation number, the rational case \(f^n(x)=x+m\) for continuous lifts, and semiconjugacy of bijective lifts with equal translation number; no rotation number of the circle map, continuity in \(f\), or Denjoy theorem). Not covered: 31.60.

## Hamiltonian structure and further continuations

[Mathematical scope](SYNOPSIS31.md#hamiltonian-structure-and-further-continuations).

### TauCeti

For a constant symplectic form on a finite-dimensional real space, the Hamiltonian vector field of \(H\) is defined by \(\omega(X_H(x),v)=dH(x)v\), and its linearization is infinitesimally symplectic for \(C^2\) \(H\) ([Hamiltonian fields](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Symplectic/Hamiltonian/Basic.lean)). When \(X_H\) is globally Lipschitz it has a global flow (`TauCeti.SymplecticForm.hamiltonianFlow`) along which \(H\) is constant (`TauCeti.SymplecticForm.hamiltonianFlow_conserves`), and for \(C^2\) \(H\) every time map preserves the symplectic form on tangent vectors (`TauCeti.SymplecticForm.apply_fderiv_hamiltonianFlow`; [Hamiltonian flows](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Symplectic/Hamiltonian/Flow.lean)).

**Synopsis entries.** Partly covered: 31.62 (TauCeti: globally Lipschitz Hamiltonian fields on symplectic vector spaces; conservation of \(H\) and of the symplectic form; Liouville volume and the absence of asymptotically stable sets not stated). Not covered: 31.64, 31.66–31.71.
