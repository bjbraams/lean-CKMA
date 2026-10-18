# 35. Nonlinear Functional Analysis, Monotone Operators, and Fixed Points

Checked against Mathlib commit `f039e1b8a616d45782a5c7fc5e7909249c36b8ea` (2026-10-18, Lean `v4.36.0-rc1`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Sources include `Mathlib.Topology.MetricSpace.Contracting`, `Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`, `Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff`, and `Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate`.

**Namespaces.** Contractions and the fixed-point construction are `ContractingWith`.

This note records the Banach fixed-point theorem, including rates and dependence on the map, the inverse and implicit function theorems in Banach spaces, hemicontinuity of set-valued maps with Michael's selection theorem, and the metric projection onto a closed convex set. Topological fixed-point theorems and monotone operators were not found.

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

Two further forms are present. The surjective version, in the tradition of Lyusternik and Graves: a map between Banach spaces strictly differentiable at \(a\) with surjective derivative sends neighbourhoods of \(a\) onto neighbourhoods of \(f(a)\), and a map that is uniformly close to a surjective linear map on an open set is locally onto (`HasStrictFDerivAt.map_nhds_eq_of_surj` in `Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`, `Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`). The implicit function theorem for a strictly differentiable map with surjective derivative and complemented kernel, automatic when the target is finite-dimensional, parametrizes the level set near \(a\) (`Analysis/Calculus/Implicit.lean`), with a \(C^n\) version in `Analysis/Calculus/ImplicitContDiff.lean`. Local inverses of analytic maps are analytic (`Analysis/Calculus/InverseFunctionTheorem/Analytic.lean`).

## Set-valued maps and convex projection

Upper and lower hemicontinuity of a correspondence \(f:\alpha\to\mathcal P(\beta)\), at a point, within a set and globally, are defined with their characterizations by open sets (`UpperHemicontinuous`, `LowerHemicontinuous`; `Topology/Semicontinuity/Hemicontinuity.lean`). Michael's selection theorem is proved: a lower hemicontinuous correspondence from a paracompact normal space to a Fréchet space with nonempty, convex, closed values has a continuous selection (`LowerHemicontinuous.exists_continuous_selection`, with the approximate version `HasOpenLowerSections.exists_continuous_selection` for correspondences with open lower sections; `Topology/Semicontinuity/Michael.lean`). No set-valued fixed-point theorem is built on these notions.

In a real inner product space, a nonempty complete convex set \(K\) contains a nearest point to every \(u\) (`exists_norm_eq_iInf_of_complete_convex`), and \(v\in K\) is nearest exactly when \(\langle u-v,w-v\rangle\le0\) for all \(w\in K\) (`norm_eq_iInf_iff_real_inner_le_zero`; `Analysis/InnerProductSpace/Projection/Minimal.lean`). This is the variational inequality of the projection; existence for variational inequalities with a general (monotone or coercive) operator is not formalized.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6ebb29f84b4d`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti develops nonlinear Fredholm analysis, including a Lyapunov–Schmidt local normal form and Sard–Smale residuality of regular values for maps on open subsets of separable real Banach spaces ([normal form](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Fredholm/NormalForm.lean), [Sard–Smale](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Fredholm/SardSmale.lean)). The finite-regularity theorem uses the sufficient bound \(k\ge(\dim\ker Df_x)^2+1\) at each point, not Smale's sharp index threshold; smooth maps satisfy this automatically. The target is Banach, and second countability of the domain is used for the global residuality conclusion. Regular level sets of Fredholm maps are submanifolds, with the kernel of the derivative as tangent space, and a global parametric transversality theorem for universal Fredholm families is proved ([level sets](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Fredholm/LevelSet/Manifold.lean), [parametric transversality](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Fredholm/LevelSet/GlobalParametric.lean)); a map with upper semi-Fredholm derivative is locally proper ([properness](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Fredholm/Proper.lean)).

There is also a Morse–Palais lemma for smooth functions with Hessian inducing a continuous linear equivalence to the dual ([Morse normal form](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Calculus/Morse/NormalForm.lean)), and the convex subdifferential/Fenchel–Young theory of Section 12. On a finite-dimensional inner product space the subdifferential of a convex function is monotone in the quantitative form that its resolvent \((I+\partial f)^{-1}\) is \(1\)-Lipschitz: \(y_i\in\partial f(x_i)\) implies \(\|x_1-x_2\|\le\|(x_1+y_1)-(x_2+y_2)\|\) (`TauCeti.norm_sub_le_norm_add_sub_add_of_mem_subdifferential`; [source](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Convex/Alexandrov.lean)); this is used for Alexandrov's theorem and is not part of a theory of maximal monotone operators.

The geometry of Banach spaces used in nonlinear analysis is partly present. The Milman–Pettis theorem states that a uniformly convex Banach space is reflexive (`TauCeti.surjective_inclusionInDoubleDual_of_uniformConvexSpace`; [source](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Convex/Uniform.lean)). Mazur's lemma gives, for a weakly convergent sequence \(u_n\rightharpoonup x\) in a seminormed space, convex combinations of the tails \(u_n,u_{n+1},\dots\) converging in norm to \(x\) (`TauCeti.exists_tendsto_sum_smul_of_tendsto_weak`; [source](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Normed/Module/Mazur.lean)). Lions' representation theorem is the linear existence theorem behind evolution problems: for a form \(E(\varphi,u)\) continuous in \(u\in H\) (Hilbert) and coercive on the diagonal, \(c\,p(\varphi)^2\le E(\varphi,j\varphi)\), every functional bounded by \(p\) is represented by some \(u\in H\), without uniqueness ([source](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/InnerProductSpace/Lions.lean)). Its monotone nonlinear analogue (Browder–Minty) is not present.

For topological methods, TauCeti computes singular homology of spheres and of complements of embedded spheres, including the Jordan–Brouwer separation theorem (`TauCeti.reducedSingularHomologyComplRangeSphereIso`; [source](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/AlgebraicTopology/Singular/JordanBrouwer.lean)), and the effect of the collapse map \(\mathbb{RP}^n\to S^n\) on top homology ([source](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/AlgebraicTopology/Cellular/RealProjective/Sphere.lean)). The no-retraction theorem, the Brouwer fixed-point theorem and the degree of a map are not derived from these computations. Neither library supplies Schauder fixed points, Leray–Schauder degree, or the Minty–Browder theorem.

## Topics of Section 35 not found in either inspected library

- The Brouwer fixed-point theorem.
- The Schauder fixed-point theorem and the Leray–Schauder degree.
- Topological degree (Brouwer degree and its axioms). TauCeti's homology of spheres and the Jordan–Brouwer separation theorem do not yield the degree of a map.
- Monotone operators in the Minty–Browder sense, maximal monotone operators, and nonlinear contraction semigroups (Brezis, Barbu). Linear m-dissipative operators and their semigroups are in TauCeti (Section 24).
- Critical point theory: the mountain pass theorem, the Palais–Smale condition, and Lusternik–Schnirelmann theory.
- Existence theorems for variational inequalities with monotone or coercive operators (Hartman–Stampacchia, Lions–Stampacchia); only the projection onto a closed convex set and its variational characterization are present.
- Bifurcation theory, including the Crandall–Rabinowitz theorem; the Lyapunov–Schmidt normal form above is its first step.
- Metric fixed-point theory for nonexpansive maps (Browder–Göhde–Kirk).
- The Ky Fan inequality and the Kakutani (Fan–Glicksberg) fixed-point theorem. Mathlib has hemicontinuity of correspondences and Michael's selection theorem, but no set-valued fixed point.
- Newton’s method as a convergence theorem in a Banach space. The Newton map in `Dynamics/Newton.lean` is algebraic: a fixed point is a root when the derivative is a unit, and the surrounding results are nilpotent perturbation and Hensel’s lemma; TauCeti's Newton iteration in adic completions ([source](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/RingTheory/AdicCompletion/Newton.lean)) is likewise algebraic. There is no Newton–Kantorovich theorem.
