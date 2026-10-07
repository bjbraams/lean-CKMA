# 31. Ordinary Differential Equations and Dynamical Systems

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The roots for this section are `Mathlib.Analysis.ODE.Basic`, `Mathlib.Analysis.ODE.Gronwall`, `Mathlib.Analysis.ODE.DiscreteGronwall`, `Mathlib.Analysis.ODE.PicardLindelof`, `Mathlib.Analysis.ODE.ExistUnique`, `Mathlib.Analysis.ODE.Transform`, `Mathlib.Geometry.Manifold.IntegralCurve.Basic`, `Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique`, `Mathlib.Geometry.Manifold.IntegralCurve.UniformTime`, `Mathlib.Geometry.Manifold.IntegralCurve.Transform`, `Mathlib.Dynamics.Flow`, `Mathlib.Dynamics.OmegaLimit`, `Mathlib.Dynamics.Transitive`, `Mathlib.Dynamics.Minimal`, `Mathlib.Dynamics.PeriodicPts.Defs`, `Mathlib.Dynamics.FixedPoints.Defs`, `Mathlib.Dynamics.FixedPoints.Topology`, `Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber`, `Mathlib.Dynamics.TopologicalEntropy.CoverEntropy`, `Mathlib.Dynamics.TopologicalEntropy.NetEntropy`, and `Mathlib.Dynamics.SymbolicDynamics.Basic`.

**Namespaces.** `IsPicardLindelof` and `ODE` for the Euclidean initial-value theory, with the continuously differentiable case under `ContDiffAt`. Flows are `Flow`. Topological entropy is `Dynamics`. Lifts of monotone circle maps are `CircleDeg1Lift`. Fixed and periodic points are `Function`. Minimal and topologically transitive actions are `MulAction` and `AddAction`. Symbolic dynamics is `SymbolicDynamics`, with nested `FullShift` and `Pattern`.

This note records local existence and uniqueness for Lipschitz ODEs, the same theory for integral curves on manifolds, and the elementary topological dynamics that sits beside them.

## Integral curves in a normed space

Let \(E\) be a real normed space and let \(v\) be a time-dependent vector field on \(E\). A curve \(\gamma\) is an integral curve of \(v\) on a set of times when, at each such time, the derivative of \(\gamma\) within that set equals \(v\) evaluated along \(\gamma\). It is a local integral curve at \(t_0\) when this holds throughout some neighborhood of \(t_0\), and a global integral curve when it holds at every real time. On an open set of times the restricted and local notions agree. An integral curve is continuous on its interval of definition (`Analysis/ODE/Basic.lean`).

Translating or scaling the time parameter produces an integral curve of the correspondingly translated or scaled field. If the field vanishes at every time at a point, the constant curve at that point is a global integral curve (`Analysis/ODE/Transform.lean`).

The set-of-times predicate `IsIntegralCurveOn` is explicitly defined and uses the derivative within that set.

## Grönwall’s inequality

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

## Picard–Lindelöf

The contraction-mapping theorem used in the existence proof is the Banach fixed-point theorem of section 35 (`Topology/MetricSpace/Contracting.lean`); it is not restated here.

Let \(E\) be a real normed space and let \(f\) be a time-dependent vector field. The Picard–Lindelöf package on a closed time interval \([t_{\min},t_{\max}]\) about a time \(t_0\), centered at a point \(x_0\), with nonnegative constants \(a,r,L,K\), consists of four hypotheses: \(f(t,\cdot)\) is \(K\)-Lipschitz on the closed ball of radius \(a\) about \(x_0\), for every \(t\) in the interval; \(t\mapsto f(t,x)\) is continuous on the interval, for every \(x\) in that ball; \(\|f(t,x)\|\le L\) throughout the same set; and \(L\) times the larger of \(t_{\max}-t_0\) and \(t_0-t_{\min}\) is at most the truncated difference \(a-r\) of nonnegative reals (`Analysis/ODE/PicardLindelof.lean`). A time-independent field that is \(K\)-Lipschitz and bounded by \(L\) on the ball satisfies the package. A time-independent field of class \(C^1\) at \(x_0\) satisfies the package on some symmetric open time interval, for a positive radius \(r\) of initial data.

If \(E\) is complete, every initial value \(x\) in the closed ball of radius \(r\) about \(x_0\) admits a curve \(\alpha\) on \([t_{\min},t_{\max}]\) with \(\alpha(t_0)=x\) and
\[
\alpha(t)=x+\int_{t_0}^{t}f(\tau,\alpha(\tau))\,d\tau.
\]
Equivalently, \(\alpha\) has derivative \(f(t,\alpha(t))\) within the closed interval (`Analysis/ODE/ExistUnique.lean`). The solutions may be chosen as a local flow of the initial condition. That flow is Lipschitz in the initial condition, uniformly for each fixed time in the interval, and the joint map \((x,t)\mapsto\alpha(x,t)\) is continuous on the product of the closed ball with the closed interval.

If the field is time-independent and merely of class \(C^1\) at \(x_0\), completeness of \(E\) again gives an open interval about any prescribed initial time on which every initial value in some closed ball has a solution, and a flow defined on a neighborhood of \((x_0,t_0)\) in \(E\times\mathbb{R}\).

Uniqueness does not use completeness. If \(v(t,\cdot)\) is Lipschitz on a time-dependent set, and two curves are continuous on a closed interval, have the ODE as a right derivative on the half-open interval, remain in that set, and agree at the left endpoint, then they agree throughout the closed interval. The time-reversed statement, with left derivatives and the right endpoint as the initial time, is included. If the initial time lies in the open interval and the curves are genuinely differentiable there, they agree on the whole closed interval, hence on the open interval. Local uniqueness follows: near a time at which the field is Lipschitz in space, two solutions that remain in the Lipschitz set and share an initial value agree on a neighborhood of that time. A globally Lipschitz field has unique solutions on every compact time interval with a prescribed initial value, and a field that is Lipschitz in space at every time, on a time-dependent set that traps both solutions, has at most one global solution with a given initial value.

Global existence on an arbitrary time interval is not proved. The estimates give continuous dependence of exact solutions at an exponential rate, but no continuation theorem up to the boundary of the domain.

## Integral curves on manifolds

On a \(C^1\) manifold, an integral curve of a vector field is a curve whose tangent vector equals the field along the curve, either globally, on a prescribed set of times, or on a neighborhood of one time (`Geometry/Manifold/IntegralCurve/Basic.lean`). Time translation and scaling act as in the vector-space case. A constant curve at a zero of the field is a global integral curve (`Geometry/Manifold/IntegralCurve/Transform.lean`).

Local existence: if the model space is a Banach space, the manifold is \(C^1\), the point is an interior point, and the vector field is \(C^1\) at that point as a map into the tangent bundle, then some local integral curve passes through the point at any prescribed time. On a manifold without boundary every point is interior, so the interior hypothesis drops (`Geometry/Manifold/IntegralCurve/ExistUnique.lean`). The argument is Picard–Lindelöf in a chart. Curves that meet the boundary are not treated; that case is left open.

Local uniqueness: two local integral curves of a vector field that is \(C^1\) at an interior point, and that pass through the same point at the same time, agree on a neighborhood of that time. On a manifold without boundary the interior hypothesis drops.

If the manifold is Hausdorff, the field is \(C^1\) everywhere, and two integral curves on an open interval take values in the interior and agree at one time of the interval, then they agree on the whole interval. Global integral curves that remain in the interior, and that agree at one time, are identical. On a manifold without boundary the interior hypothesis drops, so global integral curves of a \(C^1\) field are unique given one point of the trajectory. A global integral curve that returns to a point is periodic with the corresponding period, and a global integral curve is either injective or periodic with some positive period.

The uniform-time lemma assumes a boundaryless Hausdorff \(C^1\) manifold and a globally \(C^1\) vector field (`Geometry/Manifold/IntegralCurve/UniformTime.lean`). If one \(\varepsilon>0\) serves for every point, in the sense that every point lies on an integral curve defined at least on \((-\varepsilon,\varepsilon)\), then every point lies on a global integral curve. Overlapping integral curves on open intervals that agree at one common time may be patched. The lemma does not deduce the uniform \(\varepsilon\) from compactness of the manifold, so global existence on a compact manifold is not a theorem of this checkout.

## Flows, limit sets, and recurrence

A flow of an additive topological monoid on a topological space is a jointly continuous monoid action (`Dynamics/Flow.lean`). The nonnegative times give a forward flow. Orbits and forward orbits are invariant and forward-invariant respectively. An invariant set inherits a flow. A continuous self-map determines a flow of \(\mathbb{N}\), and a homeomorphism determines a flow of \(\mathbb{Z}\). When the time monoid is a group, each time map is a homeomorphism, with inverse given by the opposite time, and the flow may be reversed. A semiconjugacy intertwines two flows of the same time monoid, and factors are the existence of such a map.

The \(\omega\)-limit of a set under a time-dependent map, relative to a filter of times, is the intersection of the closures of the forward images along sets in the filter (`Dynamics/OmegaLimit.lean`). It is closed. A point lies in it precisely when every neighborhood of the point meets the image of the set at times that occur arbitrarily late in the filter. Finite unions pass inside the limit set exactly, and arbitrary unions pass in one direction. On a compact space, the \(\omega\)-limit of a nonempty set along a proper filter is nonempty. More generally it is nonempty when the forward images are eventually trapped in a compact set. For a flow, if the filter is invariant under time translation, the \(\omega\)-limit is invariant, and pushing the set forward by a fixed time does not change it.

A monoid action is minimal when every orbit is dense (`Dynamics/Minimal.lean`). A nonempty invariant set is then dense, and a closed invariant set is empty or everything. For a group acting minimally, the translates of a nonempty open set cover the space. If the action is also continuous, finitely many translates cover any compact set. A minimal set, as a subset, is not defined; only the minimal action is.

A monoid action is topologically transitive when every pair of nonempty open sets has some translate of the first meeting the second (`Dynamics/Transitive.lean`). Equivalently, the union of the translates of any nonempty open set is dense, and so is the union of its preimages.

A point is periodic of period \(n\) for a self-map when the \(n\)-th iterate fixes it. The definition allows \(n=0\), for which every point qualifies. The minimal period is the least positive such \(n\), or zero if the point is not periodic for any positive \(n\). The point has period \(n\) if and only if the minimal period divides \(n\). The map is bijective on the set of points of each fixed period and on the set of all periodic points (`Dynamics/PeriodicPts/Defs.lean`).

On a Hausdorff space, the fixed-point set of a continuous self-map is closed. If the iterates of a point converge to \(y\) and the map is continuous at \(y\), then \(y\) is fixed (`Dynamics/FixedPoints/Topology.lean`). The fixed support, meaning the closure of the set of non-fixed points, and the condition that this support be compact, are recorded (`Dynamics/FixedPoints/Support.lean`).

## Circle maps, entropy, and symbolic dynamics

A monotone lift of a degree-one circle map is a monotone map \(f:\mathbb{R}\to\mathbb{R}\) with \(f(x+1)=f(x)+1\) (`Dynamics/Circle/RotationNumber/TranslationNumber.lean`). Such maps form a monoid, and the bijective ones are order automorphisms of the line. The translation number is
\[
\tau(f)=\lim_{n\to\infty}\frac{f^n(x)-x}{n},
\]
and the limit exists for every \(x\). It is monotone in \(f\), additive on commuting pairs, and changes sign under inversion. For a continuous lift there is a point with \(f(x)=x+\tau(f)\). For continuous \(f\), the translation number is an integer if and only if \(f(x)=x+m\) for some \(x\) and that integer \(m\), and it is rational if and only if some positive iterate differs from the identity by an integer translation. Two bijective lifts with the same translation number are semiconjugate by another such lift. A rotation number of an actual circle homeomorphism, as an object distinct from \(\tau\) of a lift, is marked as future work in the file.

Topological entropy is the Bowen–Dinaburg entropy of a self-map of a uniform space, valued in the extended reals, and defined for an arbitrary subset rather than only for an invariant set (`Dynamics/TopologicalEntropy/CoverEntropy.lean`). Dynamical balls are the entourages of pairs whose first \(n\) iterates remain in a given entourage (`Dynamics/TopologicalEntropy/DynamicalEntourage.lean`). Cover entropy is the exponential growth, as \(n\to\infty\), of the least cardinality of a dynamical cover, first along one entourage and then as a supremum over entourages. Both a liminf and a limsup are defined. The empty set has entropy \(-\infty\). On a subset invariant under the map, the liminf and limsup entropies agree. Net entropy is the same construction with separated sets in place of covers (`Dynamics/TopologicalEntropy/NetEntropy.lean`). Cover entropy equals the supremum, over entourages, of the net entropy along those entourages, both for the liminf and for the limsup. A uniformly continuous semiconjugacy does not increase cover entropy, and the entropy of the restriction of a map to an invariant set equals the entropy of that set (`Dynamics/TopologicalEntropy/Semiconj.lean`). The uniform-space definition applies to pseudo-metric spaces too. A separate presentation through metric dynamical balls is left open.

On a left-cancellative monoid, the full shift is the space of functions from the monoid to an alphabet, with the product topology and the translation action (`Dynamics/SymbolicDynamics/Basic.lean`). Cylinders and occurrence sets of finite patterns are clopen when the alphabet is discrete. A subshift is a closed translation-invariant subset. Forbidding a family of patterns defines a subshift, including the special case of a finite forbidden list. The module comment names “subshift of finite type”, but no separate predicate or bundled definition for it is declared. The language of a subshift on a finite window is the set of patterns realized by its configurations. No entropy, mixing, or classification theorem for subshifts is proved. Geometry special to \(\mathbb{Z}^d\), including box entropy, is deferred by the file itself.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

For globally Lipschitz autonomous vector fields on a real Banach space, TauCeti constructs unique solutions for all real times, with the flow law, joint continuity, and exponential dependence estimates ([global solutions](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/ODE/GlobalSolution.lean)). On manifolds without boundary it constructs maximal integral curves, proves extension through finite endpoints when an accumulation point exists, and proves global existence when a curve remains in a compact set; compact manifolds therefore have complete \(C^1\) vector fields ([extension](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Geometry/Manifold/IntegralCurve/Extension.lean), [maximal curves](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Geometry/Manifold/IntegralCurve/Maximal.lean)).

Smooth dependence on data is proved. For a smooth parametrized autonomous field on Banach spaces, local solutions of the Picard equation depend smoothly on the parameter, by an implicit-function argument; a change of variables turns the initial condition into a parameter, so the solution is smooth jointly in initial condition and time near time zero, of the same order as the field ([parameters](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/ODE/SmoothParameter.lean), [initial conditions](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/ODE/InitialCondition.lean)). On a finite-dimensional manifold without boundary, a smooth vector field has local integral curves depending smoothly on the initial point and time, and maximal integral curves satisfy the flow law ([manifold flows](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Geometry/Manifold/IntegralCurve/SmoothFlow.lean), [flow law](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Geometry/Manifold/IntegralCurve/Flow.lean)). Mathlib's Picard–Lindelöf theorem gives only Lipschitz dependence on the initial condition. For linear systems, \(t\mapsto\exp(tA)x\) is the flow of a bounded operator, and for a symmetric operator in finite dimension the forward- and backward-decaying solutions are exactly the negative and positive spectral subspaces ([linear flows](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/ODE/Linear.lean)).

For a bounded linear part with an exponential dichotomy and a sufficiently small Lipschitz nonlinear remainder, the Lyapunov–Perron construction describes stable initial values as a Lipschitz graph. Cutoff gives a local graph and tangency at the equilibrium when the remainder has derivative zero there ([local graph theorem](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/ODE/LyapunovPerron/Local.lean)). For negative-gradient flows at finite-dimensional nondegenerate critical points, the stable and unstable spectral splittings and graph theorems are assembled explicitly ([Morse critical points](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Calculus/Morse/LocalInvariantManifold.lean)). These files establish Lipschitz graphs differentiable at the equilibrium, not full smooth embedded stable manifolds.

## Topics of Section 31 not found in either inspected library

- Smooth embedded stable-manifold theorems, hyperbolic sets, Hartman–Grobman, KAM theory, and bifurcations. TauCeti proves local stable/unstable Lipschitz graph results with tangency at the equilibrium.
- Continuation theory at a manifold boundary. Finite-endpoint extension within a manifold without boundary and global existence on compact manifolds are proved in TauCeti.
- Integral curves that meet the boundary of a manifold, and integral curves constrained to a subset of the manifold.
- Grönwall’s inequality with a variable coefficient \(K(x)\).
- Lyapunov stability theory and Lyapunov functions, the Poincaré–Bendixson theorem, Floquet theory, Sturm comparison and oscillation theorems, and the analytic theory of linear equations in the complex domain (regular singular points, monodromy).
- A rotation number of a circle homeomorphism separate from the translation number of a lift. The limit defining the translation number is proved.
- Metric, as opposed to uniform, formulations of topological entropy.
