# Structure 35: Nonlinear functional analysis, monotone operators, and fixed points

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS35.md); [bibliographical scope](CKMA-bib.md#ckma-35); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.Calculus.FDeriv.Comp`, `Mathlib.Analysis.Calculus.ContDiff.Comp`, `Mathlib.Analysis.Calculus.MeanValue`, `Mathlib.Analysis.Calculus.Deriv.MeanValue`, `Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`, `Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff`, `Mathlib.Analysis.Calculus.Implicit`, `Mathlib.Analysis.Calculus.ImplicitContDiff`, `Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate`, `Mathlib.MeasureTheory.Function.LpSpace.Basic`, `Mathlib.Topology.MetricSpace.Contracting`, `Mathlib.Topology.Semicontinuity.Hemicontinuity`, `Mathlib.Topology.Semicontinuity.Michael`, `Mathlib.Analysis.InnerProductSpace.Projection.Minimal`, `Mathlib.Analysis.InnerProductSpace.LaxMilgram`.

**Namespaces.** Contractions and the fixed-point construction are `ContractingWith`; implicit functions are `ImplicitFunctionData` and `HasStrictFDerivAt`; correspondences are `UpperHemicontinuous` and `LowerHemicontinuous`; Lax–Milgram is `IsCoercive`. In TauCeti, Fredholm normal forms are under `ContinuousLinearMap.FredholmPackage`, and the Sard–Smale theorem, subdifferentials, and evolution variational inequalities (`TauCeti.IsEVISolution`) are in `TauCeti`.

## Nonlinear calculus and reduction of equations

[Mathematical scope](SYNOPSIS35.md#nonlinear-calculus-and-reduction-of-equations).

### Mathlib

**Chain rule and mean-value estimates.**

Fréchet derivatives compose by the chain rule (`HasFDerivAt.comp` in `Analysis/Calculus/FDeriv/Comp.lean`), and compositions of \(C^n\) maps are \(C^n\) (`ContDiff.comp` in `Analysis/Calculus/ContDiff/Comp.lean`). On a convex set where \(\|Df\|\le C\), a differentiable map satisfies \(\|f(y)-f(x)\|\le C\|y-x\|\) (`Convex.norm_image_sub_le_of_norm_fderiv_le` in `Analysis/Calculus/MeanValue.lean`), and Lagrange's mean value theorem for real functions is `exists_hasDerivAt_eq_slope` (`Analysis/Calculus/Deriv/MeanValue.lean`); the integral formula for the difference follows from the fundamental theorem of calculus (`MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`).

**Inverse and implicit function theorems.**

A strictly differentiable map between Banach spaces whose derivative at a point is a continuous linear equivalence has a local inverse. The inverse is strictly differentiable at the image point, with derivative the inverse linear map (`Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`). Over \(\mathbb R\) or \(\mathbb C\), a \(C^r\) map, \(r\ge1\), with invertible derivative has a \(C^r\) local inverse (`Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`).

For a map \(f:E_1\times E_2\to F\) of real or complex Banach spaces, the implicit function theorem constructs a local graph \(y=\psi(x)\) for the level set through \((x_0,y_0)\) when the partial derivative in \(y\) is invertible, and \(\psi\) is \(C^n\) when \(f\) is (`Analysis/Calculus/ImplicitContDiff.lean`). The bivariate version assumes that both partial derivatives exist near the point and are continuous at it. It proves local uniqueness of the graph and the strict derivative formula
\[
D\psi(x_0)=-(D_yf(x_0,y_0))^{-1}\circ D_xf(x_0,y_0)
\]
(`Analysis/Calculus/ImplicitFunction/ProdDomain.lean`, `Analysis/Calculus/ImplicitFunction/Bivariate.lean`). Lagrange multipliers for constrained extrema are also proved; see Section 36.

Two further forms are present. The surjective version, in the tradition of Lyusternik and Graves: a map between Banach spaces strictly differentiable at \(a\) with surjective derivative sends neighbourhoods of \(a\) onto neighbourhoods of \(f(a)\), and a map that is uniformly close to a surjective linear map on an open set is locally onto (`HasStrictFDerivAt.map_nhds_eq_of_surj` in `Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`, `Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`). The implicit function theorem for a strictly differentiable map with surjective derivative and complemented kernel, automatic when the target is finite-dimensional, parametrizes the level set near \(a\) by the kernel (`Analysis/Calculus/Implicit.lean`), with a \(C^n\) version in `Analysis/Calculus/ImplicitContDiff.lean`; Mathlib does not package the level set as a Banach submanifold. Local inverses of analytic maps are analytic (`Analysis/Calculus/InverseFunctionTheorem/Analytic.lean`).

**Superposition operators.** Composition with a Lipschitz map \(g\) satisfying \(g(0)=0\) defines a Lipschitz, hence continuous, map \(L^p\to L^p\) (`LipschitzWith.compLp`, `LipschitzWith.continuous_compLp` in `MeasureTheory/Function/LpSpace/Basic.lean`). This is an autonomous, Lipschitz special case of Nemytskii continuity.

### TauCeti

TauCeti develops nonlinear Fredholm analysis. The Lyapunov–Schmidt local normal form writes a map with Fredholm derivative at a point, in suitable local coordinates, as \((r,k)\mapsto r+q(r,k)\) with \(q\) valued in a finite-dimensional complement of the range, and the coordinates and obstruction are \(C^k\) when the map is ([normal form](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fredholm/NormalForm.lean), `ContinuousLinearMap.FredholmPackage.normalFormOpenPartialHomeomorph`, `ContinuousLinearMap.FredholmPackage.obstructionMap`). The Sard–Smale theorem states that the critical values of a Fredholm map on a Lindelöf subset of a real Banach space (for instance any subset of a separable Banach space) form a meagre set, and the regular values are dense (`TauCeti.isMeagre_image_criticalPoints_of_isFredholm`, `TauCeti.dense_compl_image_criticalPoints_of_isFredholm`; [Sard–Smale](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fredholm/SardSmale.lean)). The regularity hypothesis is the sufficient pointwise bound \(k\ge(\dim\ker Df_x)^2+1\), not Smale's sharp index threshold; smooth maps satisfy it automatically. The domain is a subset of a Banach space, not a general Banach manifold. Regular level sets of Fredholm maps are submanifolds, with the kernel of the derivative as tangent space, and a global parametric transversality theorem for universal Fredholm families is proved ([level sets](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fredholm/LevelSet/Manifold.lean), [parametric transversality](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fredholm/LevelSet/GlobalParametric.lean)); a map with upper semi-Fredholm derivative is locally proper ([properness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fredholm/Proper.lean)).

There is also a Morse–Palais lemma for smooth functions with Hessian inducing a continuous linear equivalence to the dual ([Morse normal form](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Morse/NormalForm.lean)). For superposition operators, TauCeti proves measurability of Carathéodory compositions \(t\mapsto g(t,u(t))\) for a.e. strongly measurable \(u\) (`MeasureTheory.AEStronglyMeasurable.apply_of_forall_of_continuous`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/StronglyMeasurable/Caratheodory.lean)); this is the measurability step of Nemytskii theory, without growth conditions or \(L^p\to L^q\) continuity.

**Synopsis entries.** Covered: 35.1–35.4 (Mathlib), 35.6 (TauCeti). Partly covered: 35.5 (local parametrization of the level set by the kernel in Mathlib; submanifold structure only for Fredholm maps in TauCeti), 35.8 (on subsets of separable Banach spaces, with the non-sharp regularity bound \(k\ge(\dim\ker)^2+1\)), 35.10 (Lipschitz autonomous \(L^p\to L^p\) case and Carathéodory measurability only). Not covered: 35.7, 35.9, 35.66.

## Topological and metric fixed-point theorems

[Mathematical scope](SYNOPSIS35.md#topological-and-metric-fixed-point-theorems).

### Mathlib

**The contraction mapping theorem.**

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
If two maps are contracting with the same constant \(K\) and are uniformly at most \(C\) apart, their fixed points are at most \(C/(1-K)\) apart. If some iterate \(f^{n}\) is contracting, the fixed point of that iterate is a fixed point of \(f\) (`ContractingWith.apriori_dist_iterate_fixedPoint_le`, `ContractingWith.aposteriori_dist_iterate_fixedPoint_le`, `ContractingWith.fixedPoint_lipschitz_in_map`, `ContractingWith.isFixedPt_fixedPoint_iterate`; `Topology/MetricSpace/Contracting.lean`).

**Set-valued maps (supporting material).** Upper and lower hemicontinuity of a correspondence \(f:\alpha\to\mathcal P(\beta)\), at a point, within a set and globally, are defined with their characterizations by open sets (`UpperHemicontinuous`, `LowerHemicontinuous`; `Topology/Semicontinuity/Hemicontinuity.lean`). Michael's selection theorem is proved: a lower hemicontinuous correspondence from a paracompact normal space to a Fréchet space with nonempty, convex, closed values has a continuous selection (`LowerHemicontinuous.exists_continuous_selection`, with the approximate version `HasOpenLowerSections.exists_continuous_selection` for correspondences with open lower sections; `Topology/Semicontinuity/Michael.lean`). No set-valued fixed-point theorem is built on these notions.

**Synopsis entries.** Covered: 35.11 (Mathlib). Not covered: 35.12–35.22.

## Degree, continuation, and topological obstructions

[Mathematical scope](SYNOPSIS35.md#degree-continuation-and-topological-obstructions).

### TauCeti

For topological methods, TauCeti computes singular homology of spheres and of complements of embedded spheres, including the Jordan–Brouwer separation theorem (`TauCeti.reducedSingularHomologyComplRangeSphereIso`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/AlgebraicTopology/Singular/JordanBrouwer.lean)), and the effect of the collapse map \(\mathbb{RP}^n\to S^n\) on top homology ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/AlgebraicTopology/Cellular/RealProjective/Sphere.lean)). In dimension one, the degree (winding number) of a loop in the circle is defined through lifts and shown to be invariant under free homotopy and additive under concatenation and pointwise product (`Circle.degree`, `Circle.degree_eq_of_homotopy`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Topology/Circle/Degree.lean)). These are supporting computations: the no-retraction theorem, the Brouwer fixed-point theorem, and the Brouwer degree of a map \(\overline\Omega\to\mathbb R^n\) are not derived from them.

**Synopsis entries.** Not covered: 35.23–35.31, 35.65.

## Monotone operators and variational inequalities

[Mathematical scope](SYNOPSIS35.md#monotone-operators-and-variational-inequalities).

### Mathlib

**Convex projection.** In a real inner product space, a nonempty complete convex set \(K\) contains a nearest point to every \(u\) (`exists_norm_eq_iInf_of_complete_convex`), and \(v\in K\) is nearest exactly when \(\langle u-v,w-v\rangle\le0\) for all \(w\in K\) (`norm_eq_iInf_iff_real_inner_le_zero`; `Analysis/InnerProductSpace/Projection/Minimal.lean`). This is the variational inequality of the projection, \(u-P_Ku\in N_K(P_Ku)\); the normal-cone operator itself is not defined as a monotone graph.

**Lax–Milgram.** A bounded coercive bilinear form on a real Hilbert space induces a continuous linear equivalence (`IsCoercive.continuousLinearEquivOfBilin`, with antilipschitz bound `IsCoercive.antilipschitz`; `Analysis/InnerProductSpace/LaxMilgram.lean`). This is the linear case of the strong-monotonicity theorem.

### TauCeti

For a function \(f:E\to\overline{\mathbb R}\) on a real inner product space, the subdifferential is monotone, \(\langle x_2-x_1,y_2-y_1\rangle\ge0\) for \(y_i\in\partial f(x_i)\) (`TauCeti.apply_le_apply_of_mem_subdifferential`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Subdifferential.lean)), and its resolvent \((I+\partial f)^{-1}\) is single-valued and \(1\)-Lipschitz on its domain: \(y_i\in\partial f(x_i)\) implies \(\|x_1-x_2\|\le\|(x_1+y_1)-(x_2+y_2)\|\) (`TauCeti.norm_sub_le_norm_add_sub_add_of_mem_subdifferential`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Alexandrov.lean)). This is used for Alexandrov's theorem and is not part of a theory of maximal monotone operators; neither firm nonexpansiveness nor surjectivity of \(I+\partial f\) is proved. The convex subdifferential and Fenchel–Young theory are recorded in Section 12. The proximal (Moreau–Yosida) step, a minimizer of \(\varphi(y)+d(x,y)^2/2\tau\), exists on metric spaces under lower-semicontinuity and compactness hypotheses (`TauCeti.moreauYosidaResolvent_nonempty`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/GradientFlow/MoreauYosida/Existence.lean)); uniqueness and maximal monotonicity of \(\partial\varphi\) are not proved.

The geometry of Banach spaces used in nonlinear analysis is partly present. The Milman–Pettis theorem states that a uniformly convex Banach space is reflexive (`TauCeti.surjective_inclusionInDoubleDual_of_uniformConvexSpace`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Uniform.lean)). Mazur's lemma gives, for a weakly convergent sequence \(u_n\rightharpoonup x\) in a seminormed space, convex combinations of the tails \(u_n,u_{n+1},\dots\) converging in norm to \(x\) (`TauCeti.exists_tendsto_sum_smul_of_tendsto_weak`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Mazur.lean)). Lions' representation theorem is the linear existence theorem behind evolution problems: for a form \(E(\varphi,u)\) continuous in \(u\in H\) (Hilbert) and coercive on the diagonal, \(c\,p(\varphi)^2\le E(\varphi,j\varphi)\), every functional bounded by \(p\) is represented by some \(u\in H\), without uniqueness (`LinearMap.exists_forall_apply_eq_and_norm_le_of_coercive`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Lions.lean)). Its monotone nonlinear analogue (Browder–Minty) is not present.

**Synopsis entries.** Partly covered: 35.33 (nonexpansiveness, not firm nonexpansiveness, of \((I+\partial f)^{-1}\) on its domain, TauCeti), 35.38 (existence of the proximal minimizer under compactness hypotheses, TauCeti; no maximality), 35.41 (linear case: Lax–Milgram, Mathlib), 35.46 (projection onto a closed convex set and its variational characterization, Mathlib; no normal-cone operator). Not covered: 35.32, 35.34–35.37, 35.39, 35.40, 35.42–35.45, 35.47.

## Accretive evolution and nonlinear contraction semigroups

[Mathematical scope](SYNOPSIS35.md#accretive-evolution-and-nonlinear-contraction-semigroups).

### TauCeti

The linear case of generation is in TauCeti: by the Lumer–Phillips theorem, an operator on a real Banach space generates a strongly continuous contraction semigroup exactly when it is densely defined and m-dissipative (`TauCeti.Semigroups.exists_contractionSemigroup_generator_eq_iff`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Semigroups/Generation/LumerPhillips.lean)), and orbits starting in the generator domain are classical solutions of the abstract Cauchy problem (`TauCeti.Semigroups.StronglyContinuousSemigroup.isClassicalSolution_realOperator`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Semigroups/CauchyProblem/Basic.lean)); see [Section 24](STRUCTURE24.md).

For nonlinear gradient flows, TauCeti works with the evolution variational inequality on a metric space: `TauCeti.IsEVISolution λ φ u` states \(\tfrac12\frac{d^+}{dt}d(u_t,y)^2+\tfrac\lambda2d(u_t,y)^2\le\varphi(y)-\varphi(u_t)\) for every \(y\) of finite energy, which in a Hilbert space is the variational form of \(-u'\in\partial\varphi(u)\) for \(\lambda\)-convex \(\varphi\) ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/GradientFlow/EVI/Basic.lean)). For a lower semicontinuous energy, EVI solutions have nonincreasing energy, satisfy the integrated inequality and the regularization estimate \(\varphi(u_t)\le\varphi(y)+d(u_0,y)^2/(2t)\) when \(\lambda=0\) (`TauCeti.IsEVISolution.apply_le`), the \(\lambda\)-contraction \(d(u_t,v_t)\le e^{-\lambda t}d(u_0,v_0)\) (`TauCeti.IsEVISolution.dist_le`), and uniqueness; they are locally Lipschitz curves of maximal slope satisfying the energy identity \(\varphi(u_s)=\varphi(u_t)+\tfrac12\int_s^t|u'|^2+\tfrac12\int_s^t|\partial\varphi|^2(u)\) (`TauCeti.IsEVISolution.apply_eq_add_dissipation`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/GradientFlow/EVI/MaximalSlope.lean)). The solutions define a continuous contraction semiflow on the set of initial points from which a solution starts (`TauCeti.eviSemiflow`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/GradientFlow/EVI/Semigroup.lean)). Existence of EVI solutions, in particular for the subdifferential of a convex lower semicontinuous function on a Hilbert space, is not proved.

**Synopsis entries.** Partly covered: 35.48 (linear densely defined case: Lumer–Phillips generation; no nonlinear exponential formula), 35.49 (linear case: generator-domain orbits are classical solutions), 35.51 (the inequality is the defining property of TauCeti's EVI solutions; that subgradient flows satisfy it is not proved), 35.52 (energy identity and regularization estimate for EVI solutions, whose existence is assumed), 35.53 (exponential contraction for EVI\(_\lambda\) solutions of \(\lambda\)-convex energies only). Not covered: 35.50.

## Nonexpansive iteration and operator splitting

[Mathematical scope](SYNOPSIS35.md#nonexpansive-iteration-and-operator-splitting).

**Synopsis entries.** Not covered: 35.54–35.58.

## Local and global bifurcation

[Mathematical scope](SYNOPSIS35.md#local-and-global-bifurcation).

### Mathlib

The implicit function theorem recorded above, with its local uniqueness of the solution graph (`ImplicitFunctionData`, `implicitFunctionOfBivariate` in `Analysis/Calculus/ImplicitFunction/Bivariate.lean`), excludes nontrivial zeros of \(F(\lambda,u)\) near \((\lambda_0,0)\) when \(D_uF(\lambda_0,0)\) is invertible. No bifurcation statement is formulated.

### TauCeti

The Lyapunov–Schmidt normal form recorded above is the first step of the Crandall–Rabinowitz argument; no bifurcation theorem is derived from it.

**Synopsis entries.** Covered: 35.59 (Mathlib, as the local uniqueness part of the implicit function theorem). Not covered: 35.60–35.64.

## Supporting structures and related formalizations

The following entries supply additional foundations or related constructions. Their stated scope determines how they can be used in this sub-area.

### Mathlib

The Newton map in `Dynamics/Newton.lean` is algebraic: a fixed point is a root when the derivative is a unit, and the surrounding results are nilpotent perturbation and Hensel's lemma. It is not a Newton–Kantorovich convergence theorem in a Banach space.

### TauCeti

TauCeti's Newton iteration in adic completions ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/RingTheory/AdicCompletion/Newton.lean)) is likewise algebraic.
