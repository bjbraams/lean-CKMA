# 35. Nonlinear Functional Analysis, Monotone Operators, and Fixed Points

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Sources include `Mathlib.Topology.MetricSpace.Contracting`, `Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`, `Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff`, and `Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate`.

**Namespaces.** Contractions and the fixed-point construction are `ContractingWith`.

This note records the Banach fixed-point theorem, including rates and dependence on the map, and the inverse and implicit function theorems in Banach spaces. Topological fixed-point theorems and monotone operators were not found.

## The contraction mapping theorem

A map of an extended metric space is contracting with constant \(K\) when \(K < 1\) and the map is Lipschitz with constant \(K\). On a complete extended metric space, if the distance from a point \(x\) to its image is finite, the iterates of \(x\) converge to a fixed point \(y\), and
\[
d(f^{n}(x), y) \le d(x, f(x))\, K^{n}/(1-K).
\]
Two fixed points are equal or lie at infinite distance. The fixed point constructed from \(x\) is the only fixed point at finite distance from \(x\). The same statement holds for a map that contracts a complete forward-invariant subset, and the fixed point lies in that subset (`Topology/MetricSpace/Contracting.lean`).

On a nonempty complete metric space the fixed point is unique, and the iterates starting at any point converge to it. The a priori rate is
\[
d(f^{n}(x), x_\star) \le d(x, f(x))\, K^{n}/(1-K),
\]
and the a posteriori rate is
\[
d(f^{n}(x), x_\star) \le d(f^{n}(x), f^{n+1}(x))/(1-K).
\]
If two maps are contracting with the same constant \(K\) and are uniformly at most \(C\) apart, their fixed points are at most \(C/(1-K)\) apart. If some iterate \(f^{n}\) is contracting, the fixed point of that iterate is a fixed point of \(f\) (`Topology/MetricSpace/Contracting.lean`).

## Inverse and implicit function theorems

A strictly differentiable map between Banach spaces whose derivative at a point is a continuous linear equivalence has a local inverse. The inverse is strictly differentiable at the image point, with derivative the inverse linear map (`Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`). Over \(\mathbb R\) or \(\mathbb C\), a \(C^r\) map, \(r\ge1\), with invertible derivative has a \(C^r\) local inverse (`Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`).

For a map \(f:E_1\times E_2\to F\) of real or complex Banach spaces, the implicit function theorem constructs a local graph \(y=\psi(x)\) for the level set through \((x_0,y_0)\) when the partial derivative in \(y\) is invertible. The bivariate version assumes that both partial derivatives exist near the point and are continuous at it. It proves local uniqueness of the graph and the strict derivative formula
\[
D\psi(x_0)=-(D_yf(x_0,y_0))^{-1}\circ D_xf(x_0,y_0)
\]
(`Analysis/Calculus/ImplicitFunction/ProdDomain.lean`, `Analysis/Calculus/ImplicitFunction/Bivariate.lean`). Lagrange multipliers for constrained extrema are also proved; see Section 36.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti develops nonlinear Fredholm analysis, including a Lyapunov–Schmidt local normal form and Sard–Smale residuality of regular values for maps on open subsets of separable real Banach spaces ([normal form](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Fredholm/NormalForm.lean), [Sard–Smale](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Fredholm/SardSmale.lean)). The finite-regularity theorem uses the sufficient bound \(k\ge(\dim\ker Df_x)^2+1\) at each point, not Smale's sharp index threshold; smooth maps satisfy this automatically. The target is Banach, and second countability of the domain is used for the global residuality conclusion.

There is also a Morse–Palais lemma for smooth functions with Hessian inducing a continuous linear equivalence to the dual ([Morse normal form](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Calculus/Morse/NormalForm.lean)), and the convex subdifferential/Fenchel–Young theory of Section 12. Neither supplies Brouwer or Schauder fixed points, topological degree, or the Minty–Browder theorem, which were not located.

## Topics of Section 35 not found in either inspected library

- The Brouwer fixed-point theorem.
- The Schauder fixed-point theorem and the Leray–Schauder degree.
- Topological degree.
- Monotone operators in the Minty–Browder sense.
- The Ky Fan inequality and the Kakutani fixed-point theorem.
- Newton’s method as a convergence theorem in a Banach space. The Newton map in `Dynamics/Newton.lean` is algebraic: a fixed point is a root when the derivative is a unit, and the surrounding results are nilpotent perturbation and Hensel’s lemma.
