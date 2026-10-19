# Structure 12: Convexity, convex analysis, optimization, and variational analysis

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS12.md); [bibliographical scope](CKMA-bib.md#ckma-12); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.Convex`, `Mathlib.Geometry.Convex`, `Mathlib.Analysis.LocallyConvex.Separation`, `Mathlib.Analysis.LocallyConvex.WeakSpace`, `Mathlib.Analysis.InnerProductSpace.Projection.Minimal`, `Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional`, `Mathlib.Topology.Sion`, `Mathlib.Analysis.Calculus.LagrangeMultipliers`, `Mathlib.Analysis.Calculus.InverseFunctionTheorem`.

**Namespaces.** `Convex` contains Radon’s theorem and Helly’s theorem. `Caratheodory` contains the minimal affine-independent subset used for Carathéodory. Exposed sets are `IsExposed`. One-sided derivatives of convex functions of a real variable are developed in `ConvexOn`, `StrictConvexOn`, `ConcaveOn`, and `StrictConcaveOn`. Proper cones are `ProperCone`; pointed cones and their algebraic duals are `PointedCone`. Simplicial complexes are `Geometry.SimplicialComplex`. The norm-free convex-combination calculus is `Convexity`, with nested `StdSimplex`. Sion's theorem is in `Sion`. The geometric Hahn–Banach theorems are in the root namespace, with complex versions in `RCLike`. The TauCeti declarations are in `TauCeti`, except for a few stated in Mathlib namespaces such as `ConvexOn`, `StrongConvexOn`, `AbsConvex`, and `StrongDual`.

## Separation and convex geometry

[Mathematical scope](SYNOPSIS12.md#separation-and-convex-geometry).

### Mathlib

**Separation.**

The geometric Hahn–Banach theorems are in `Analysis/LocallyConvex/Separation.lean`. In a real locally convex topological vector space, a point outside a closed convex set is strictly separated from it by a continuous linear functional (`geometric_hahn_banach_point_closed`, `geometric_hahn_banach_closed_point`), and a compact convex set disjoint from a closed convex set is strictly separated from it (`geometric_hahn_banach_compact_closed`, `geometric_hahn_banach_closed_compact`). No Hausdorff hypothesis is needed. Without local convexity, an open convex set is separated from a disjoint convex set (`geometric_hahn_banach_open`). If a convex set \(A\) has nonempty interior and \(x\notin\operatorname{int}A\), some nonzero continuous linear functional attains its maximum over \(A\) at \(x\) (`geometric_hahn_banach_of_nonempty_interior_point`); this is the supporting-hyperplane theorem for convex sets with nonempty interior in a topological vector space. Complex versions are in the namespace `RCLike`.

**The Minkowski functional.**

The gauge of a set \(s\) in a real vector space is
\[
\operatorname{gauge}_s(x)=\inf\{r>0:x\in r\cdot s\}.
\]
If \(s\) is convex and absorbent, the gauge is subadditive. If it is also balanced, the gauge is a seminorm. If \(s\) is a convex neighborhood of the origin in a topological real vector space, the gauge is continuous, the open sublevel set \(\{\operatorname{gauge}_s<1\}\) is the interior of \(s\), the closed sublevel set \(\{\operatorname{gauge}_s\le 1\}\) is the closure, and the level set \(\{\operatorname{gauge}_s=1\}\) is the frontier. In a normed space the gauge of a convex neighborhood of the origin is Lipschitz, and the gauge of the open unit ball is the norm (`Analysis/Convex/Gauge.lean`).

**Carathéodory, Radon, and Helly.**

Over a field that is a strict ordered ring, the convex hull of a set is the union of the convex hulls of its affine-independent finite subsets. A point of the hull is a convex combination, with strictly positive weights summing to \(1\), of an affine-independent family taken from the set (`convexHull_eq_union`, `eq_pos_convex_span_of_mem_convexHull`, `Analysis/Convex/Caratheodory.lean`). An affine-independent family has at most \(\dim+1\) members, where \(\dim\) is the dimension of the vector span of the family (`AffineIndependent.card_le_finrank_succ`, `LinearAlgebra/AffineSpace/FiniteDimensional.lean`). Together these give Carathéodory's bound \(n+1\), and the bound by the dimension of the affine hull.

Radon’s theorem: an affinely dependent family can be split into a set and its complement whose convex hulls meet (`radon_partition`). In finite dimension \(d\) this applies to any \(d+2\) points, which are affinely dependent (`Analysis/Convex/Radon.lean`).

Helly’s theorem, for a finite family of convex sets in a finite-dimensional space of dimension \(d\): if every subfamily of size at most \(d+1\) has nonempty intersection, the whole family does (`Convex.helly_theorem'`). The classical finite form assumes at least \(d+1\) sets and assumes the intersections only for subfamilies of size exactly \(d+1\) (`Convex.helly_theorem`). For a possibly infinite family of compact convex sets in a Hausdorff finite-dimensional space, the same numerical hypotheses imply that the whole family meets (`Convex.helly_theorem_compact'`, `Convex.helly_theorem_compact`). The file gives both the indexed form and the form for a set of sets; the classical compact form uses cardinality, or encard, at least \(d+1\).

**Extreme points, exposed sets, and Krein–Milman.**

A subset \(B\subseteq A\) is extreme when a point of \(B\) that lies on an open segment with ends in \(A\) forces the left endpoint, and hence the right endpoint, into \(B\). An extreme point of \(A\) lies on an open segment in \(A\) only in the trivial case (`Analysis/Convex/Extreme.lean`).

A set \(B\) is exposed in \(A\) when, as soon as \(B\) is nonempty, it is exactly the set of maximizers in \(A\) of some continuous linear functional. The empty set is exposed. An exposed set is extreme, and exposed points are extreme points (`Analysis/Convex/Exposed.lean`).

In a real locally convex Hausdorff topological vector space, a nonempty compact set has an extreme point, and a compact convex set is the closure of the convex hull of its extreme points (`IsCompact.extremePoints_nonempty`, `closure_convexHull_extremePoints`). Every extreme point of the image of a compact set under a continuous affine map has an extreme-point preimage. In symbols, \(\operatorname{ext}(f(K))\subseteq f(\operatorname{ext}K)\). This inclusion can be strict: an extreme point of \(K\) need not map to an extreme point of its image (`Analysis/Convex/KreinMilman.lean`). The file states that the finite-dimensional form without the closure, the Minkowski–Carathéodory theorem, is not in the library. The interior of a set in a nontrivial topological vector space contains no extreme point, and the extreme points of a strictly convex set in a nontrivial normed space are exactly its points outside the interior (`Analysis/Convex/Strict/Extreme.lean`).

**Cones, Farkas, and Stone separation.**

A pointed cone in a module over an ordered ring is a submodule for the nonnegative scalars (`Geometry/Convex/Cone/Pointed.lean`). A proper cone in the analytic development is a closed submodule over \(\mathbb{R}_{\ge 0}\), that is, a closed pointed cone in this terminology (`Analysis/Convex/Cone/Basic.lean`). Here “pointed” means that the cone contains the origin; it does not impose the usual additional condition that the cone contain no nontrivial line. A cone is dually finitely generated when it is the dual of a finite set, an intersection of finitely many half-spaces (`PointedCone.DualFG`, `Geometry/Convex/Cone/DualFinite.lean`); the file notes that equivalence with finite generation is the Minkowski–Weyl theorem, which is not proved there.

Farkas’ lemma, in a real locally convex space: if a proper cone is disjoint from a compact convex set, some continuous linear functional is nonnegative on the cone and strictly negative on the set. A point outside the cone is separated in the same way (`ProperCone.hyperplane_separation`, `ProperCone.hyperplane_separation_point`). For a continuous perfect pairing, the double dual of a proper cone is the cone (`Analysis/Convex/Cone/Dual.lean`). The algebraic dual, consisting of the vectors nonnegative on a set for a bilinear pairing, is developed without topology in `Geometry/Convex/Cone/Dual.lean`. In a complete real inner product space the inner dual of a closed convex cone has the cone as its own double dual, and a point outside such a cone is separated from it by a vector of the inner dual. For a continuous linear map \(f\) and a proper cone \(C\), a vector \(b\) lies in the closure of \(f(C)\) exactly when \(\langle b,y\rangle\ge0\) for every \(y\) with \(f^*y\) in the inner dual of \(C\) (`ProperCone.relative_hyperplane_separation`, `Analysis/Convex/Cone/InnerDual.lean`). The M. Riesz extension theorem for linear functionals nonnegative on a convex cone, and the algebraic Hahn–Banach theorem with a sublinear bound, are in `Analysis/Convex/Cone/Extension.lean`.

Stone’s separation theorem, for a module over an ordered field: two disjoint convex sets are contained, one in a convex set and the other in its complement, with that complement itself convex (`exists_convex_convex_compl_subset`, `Analysis/Convex/StoneSeparation.lean`).

**Simplicial complexes and norm-free convexity (supporting).**

A simplicial complex in a module over the scalar field is a down-closed family of nonempty finite sets of vertices, each affinely independent, such that the convex hulls of two faces meet inside the convex hull of the intersection of their vertex sets. For faces \(s\) and \(t\),
\[
\operatorname{conv}(s)\cap\operatorname{conv}(t)=\operatorname{conv}(s\cap t).
\]
The textbook alternative, that two faces are disjoint or meet in a face, is deduced from that identity (`Analysis/Convex/SimplicialComplex/Basic.lean`).

`Geometry/Convex` builds convexity from convex combinations alone. The standard simplex on a type \(X\) is the set of finitely supported nonnegative weights on \(X\) summing to \(1\). A convex space is a type equipped with an operation taking such a weight system to a point, equal to the point itself on a Dirac weight, and associative in the monadic sense. A set is convex when it contains every convex combination of its points, and the folder has its own convex hull. Star-convex sets are included. Cones, faces, simplicial cones, and duals along a bilinear pairing stay algebraic (`Geometry/Convex/README.md`, `Geometry/Convex/ConvexSpace/Defs.lean`, `Geometry/Convex/Set.lean`). `Analysis/Convex` adds the structure that needs a topology, a norm, or an inner product: continuity and Lipschitz estimates, gauges, strict and uniform convexity of spaces, strong convexity, integral Jensen, and the locally convex separation used for Krein–Milman and Farkas (`Analysis/Convex/README.md`).

### TauCeti

TauCeti defines convex polyhedra as finite intersections of closed affine half-spaces, with closure under finite intersection and affine preimage ([polyhedra](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Polyhedron/Basic.lean), `TauCeti.IsConvexPolyhedron`), and shows that the convex hull of an affinely independent family in a finite-dimensional real normed space is a convex polyhedron ([simplices](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Polyhedron/Simplex.lean)). This is a special case of one direction of Minkowski–Weyl; the theorem itself is not proved.

A compact set with full affine span in an \(n\)-dimensional real space can be moved by an affine equivalence to lie between two balls whose radii depend only on the space; the construction uses a simplex of maximal volume (`TauCeti.exists_affineEquiv_ball_subset_image_subset_ball`, [affine normalization](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/AffineNormalization.lean)). This is supporting material for John's theorem, with non-sharp constants and no ellipsoid.

For Choquet theory, TauCeti proves only that the measures in a set vanishing on a fixed set form a face, with the corresponding extreme points ([faces of measure sets](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Measure/Face.lean)).

**Synopsis entries.** Covered: 12.1, 12.3, 12.4, 12.5 (Mathlib). Partly covered: 12.2 (supporting functionals for convex sets with nonempty interior in a topological vector space; the relative-interior form in \(\mathbb R^n\) and Bishop–Phelps are absent), 12.6 (Krein–Milman with the closure; the closure-free finite-dimensional form with \(n+1\) extreme points is absent). Not covered: 12.7, 12.9, 12.10, 12.11.

## Convex functions, derivatives, and conjugacy

[Mathematical scope](SYNOPSIS12.md#convex-functions-derivatives-and-conjugacy).

### Mathlib

**Convex sets, hulls, and convex functions.**

A set is convex when it is star-convex at each of its points, equivalently when it contains the segment between any two of its points. The convex hull is the closure operator generated by that predicate (`Analysis/Convex/Basic.lean`, `Analysis/Convex/Hull.lean`).

A real-valued function on a convex set is convex when
\[
f(a x+b y)\le a\,f(x)+b\,f(y)
\]
for \(a,b\ge 0\) with \(a+b=1\). It is strictly convex when the inequality is strict for \(a,b>0\) and \(x\neq y\). Concavity and strict concavity reverse the inequality (`Analysis/Convex/Function.lean`).

On a nonempty open convex set in a real normed space, local Lipschitz continuity, continuity, continuity at a single point, and local boundedness above are equivalent for a convex function, and likewise for local boundedness of the absolute value (`ConvexOn.continuousOn_tfae`). In finite dimension a real-valued convex function is automatically locally Lipschitz, hence continuous, on the interior of its domain (`ConvexOn.locallyLipschitzOn_interior`); continuity also holds on the relative interior (`ConvexOn.locallyLipschitzOn_intrinsicInterior`). The same holds for concave functions. In infinite dimension the equivalences require one of the continuity or boundedness conditions; convexity alone does not imply continuity (`Analysis/Convex/Continuous.lean`).

A local minimum of a convex function on a convex set is a global minimum (`IsMinOn.of_isLocalMinOn_of_convexOn`, `Analysis/Convex/Extrema.lean`). The set of functions convex on a given set is closed in the topology of pointwise convergence (`Analysis/Convex/FunctionTopology.lean`). In a real locally convex space, a real function that is convex and lower semicontinuous on a closed convex set is the supremum of the restrictions of continuous affine functions below it, and of a countable such family when the space is hereditarily Lindelöf (`sSup_affine_eq`, `sSup_of_countable_affine_eq`, `Analysis/Convex/Approximation.lean`). This is the real-valued affine-minorant half of Fenchel–Moreau; Mathlib defines no Legendre–Fenchel conjugate.

**Jensen.**

The finite and integral forms of Jensen’s inequality, including the equality cases for strictly convex and strictly concave functions and the maximum principle on a convex hull, are stated in Section 11. The finite form lives in `Analysis/Convex/Jensen.lean`: nonnegative weights summing to \(1\), points in the convex domain, and \(f(\sum w_i p_i)\le\sum w_i f(p_i)\). The integral form, in `Analysis/Convex/Integral.lean`, needs a complete normed real space, a closed convex set, a continuous convex integrand, a finite nonzero measure, and integrability of \(f\) and of \(g\circ f\).

**Strict, uniform, and strong convexity.**

A set is strictly convex when the open segment between any two distinct points lies in its interior. An open convex set is strictly convex. A real normed space is strictly convex when the closed balls of positive radius about the origin are strictly convex sets; every closed ball is then strictly convex. In such a space, \(\|x+y\|<\|x\|+\|y\|\) if and only if \(x\) and \(y\) do not lie on the same ray (`Analysis/Convex/Strict.lean`, `Analysis/Convex/StrictConvexSpace.lean`).

A seminormed space is uniformly convex when, for every \(\varepsilon>0\), some \(\delta>0\) has the property that unit vectors with \(\|x-y\|\ge\varepsilon\) satisfy \(\|x+y\|\le 2-\delta\). The same modulus controls pairs of vectors in the closed unit ball, and a scaled form controls pairs of norm at most \(r\) (`Analysis/Convex/Uniform.lean`). Milman–Pettis and Hanner’s inequalities are marked there as future work; Milman–Pettis is proved in TauCeti (next section).

A function on a convex set in a real normed space is uniformly convex with modulus \(\varphi\) when
\[
f(ax+by)\le a f(x)+b f(y)-ab\,\varphi(\|x-y\|)
\]
for \(a,b\ge 0\) summing to \(1\). It is \(m\)-strongly convex when the modulus is \((m/2)r^2\). On a real inner product space this is equivalent to convexity of \(x\mapsto f(x)-(m/2)\|x\|^2\) (`strongConvexOn_iff_convex`). A positive strong-convexity constant implies strict convexity (`Analysis/Convex/Strong.lean`). Derivative criteria for strongly convex functions are a TODO in that file.

**Derivatives of convex functions of one variable.**

If \(f:\mathbb{R}\to\mathbb{R}\) is continuous on a convex set, differentiable on the interior, and the derivative is monotone on the interior, then \(f\) is convex. A strictly monotone derivative yields strict convexity; continuity on the domain is assumed, and strict monotonicity of the derivative supplies differentiability except at most at one point. A nonnegative second derivative on the interior, with the function and its first derivative differentiable there, yields convexity. A strictly positive second derivative yields strict convexity, again without a separate twice-differentiability hypothesis beyond what the sign of the second derivative gives. Antitone derivatives and nonpositive second derivatives give concavity (`Analysis/Convex/Deriv.lean`).

Conversely, a convex function on a real interval has left and right derivatives at each interior point: the right derivative is the infimum of the right-hand slopes, the left derivative is the supremum of the left-hand slopes, the left derivative is at most the right derivative, and both are monotone on the interior. If the function is differentiable on a subset of the domain, the derivative is monotone there. A sign change of the one-sided derivatives at an interior point, left derivative nonpositive and right derivative nonnegative, is a minimum on the domain. Where the function is differentiable, slopes compare with the derivative in the expected way, and strict convexity makes those comparisons strict. The concave statements are dual. These one-variable results are the only directional-derivative theory for convex functions; the max formula \(f'(x;d)=\max_{u\in\partial f(x)}\langle u,d\rangle\) is not stated.

**Polars of cones.**

The bipolar theorem for closed convex cones is the double-dual identity recorded under Farkas' lemma in the previous section (`Analysis/Convex/Cone/Dual.lean`, `Analysis/Convex/Cone/InnerDual.lean`). The absolute polar for a bilinear pairing, with its basic calculus (`LinearMap.polar`, `subset_bipolar`, `tripolar_eq_polar`), is in `Analysis/LocallyConvex/Polar.lean`.

### TauCeti

**Conjugates and the Fenchel–Moreau theorem.**

The extended-real Legendre–Fenchel conjugate is defined for a real bilinear dual pairing. TauCeti proves Fenchel–Young, the order-reversing conjugacy relation, \(f^{**}\le f\), and \(f^{***}=f^*\), as well as convexity and lower semicontinuity of the conjugate when the pairing functionals are continuous ([conjugacy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Conjugate.lean)).

The Fenchel–Moreau theorem is proved. Let \(E\) be a real locally convex topological vector space and \(f:E\to[-\infty,\infty]\) convex (convex real epigraph), lower semicontinuous, and never \(-\infty\). For every \(x_0\) and real \(t<f(x_0)\) there is a continuous affine minorant of \(f\) taking the value \(t\) at \(x_0\) (`TauCeti.exists_affine_le_of_lt`); hence, for a pairing \(B\) that represents every continuous linear functional on \(E\), \(f^{**}=f\) (`TauCeti.fenchelConjugate_flip_fenchelConjugate_eq`). If in addition the functionals \(B(\cdot,y)\) are continuous, \(f^{**}=f\) holds exactly when \(f\) is convex, lower semicontinuous, and either never \(-\infty\) or identically \(-\infty\) (`TauCeti.fenchelConjugate_flip_fenchelConjugate_eq_iff`). No Hausdorff hypothesis is needed. The inner-product form on a complete real inner product space is `TauCeti.fenchelConjugate_innerₗ_fenchelConjugate_innerₗ` ([Fenchel–Moreau](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/FenchelMoreau.lean)).

**Subdifferentials.**

The subdifferential is defined by supporting affine functions at points where the function is finite. Its values are convex, and closed when the pairing functionals are continuous. Equality in Fenchel–Young characterizes subgradients (`TauCeti.mem_subdifferential_iff_add_fenchelConjugate_eq`), and conjugate-subgradient reciprocity is proved: \(y\in\partial f(x)\) implies \(x\in\partial f^*(y)\), with the converse at every point where \(f^{**}(x)=f(x)\) (`TauCeti.mem_subdifferential_fenchelConjugate_iff`), in particular for every proper lower semicontinuous convex \(f\) by Fenchel–Moreau ([subdifferentials](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Subdifferential.lean)). The only calculus rule is that adding an affine function translates the subdifferential (`TauCeti.mem_subdifferential_add_affine_iff`).

In a finite-dimensional real inner product space, a convex \(f:E\to(-\infty,\infty]\) has a nonempty subdifferential at every interior point of its effective domain (`TauCeti.nonempty_subdifferential_of_mem_interior`); its subgradients are bounded on compact subsets of that interior, and the subgradient image of a compact subset of the interior is compact ([subgradient images](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/SubgradientImage.lean)).

**Differentiability.**

A real convex function on a finite-dimensional real normed space is differentiable at almost every interior point of its domain, by Rademacher's theorem and local Lipschitz continuity (`ConvexOn.ae_differentiableAt_of_mem_interior`, [Rademacher](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Rademacher.lean)); the extended-real form is `TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal`. At a point of differentiability, every subgradient represents the derivative and the derivative is a subgradient, so the subdifferential is the singleton of the gradient (`TauCeti.hasFDerivAt_apply_eq_of_mem_subdifferential`, `TauCeti.mem_subdifferential_of_hasFDerivAt`); a subgradient selection continuous at a point is the gradient there (`TauCeti.hasGradientAt_toReal_of_continuousAt_subgradient`, [differentiability](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Differentiability.lean)). The converse, that a singleton subdifferential implies differentiability, is not stated.

The Hessian of a convex function, where it exists, is a positive operator, and a function on an open convex set whose gradient has a positive semidefinite derivative everywhere is convex (`ConvexOn.isPositive_of_hasFDerivAt_gradient`, `TauCeti.convexOn_of_hasFDerivAt_gradient`, [Hessians](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Hessian.lean)).

Alexandrov's theorem is proved. Let \(E\) be a finite-dimensional real inner product space with an additive Haar measure. For a real function \(u\) convex on a set \(\Omega\), at almost every \(x\in\Omega\) the function \(u\) is differentiable and there is a unique positive operator \(A\) with
\[
u(x')=u(x)+\langle\nabla u(x),x'-x\rangle+\tfrac12\langle A(x'-x),x'-x\rangle+o(\|x'-x\|^2)
\]
(`ConvexOn.ae_existsUnique_isPositive_isLittleO`); the same holds for an extended-real convex function at almost every point of its effective domain (`TauCeti.ae_existsUnique_isPositive_isLittleO`), and the subdifferential itself is differentiable there with derivative \(A\) ([Alexandrov](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Alexandrov.lean)).

**Conjugates of superlinear functions.**

Let \(h\) be a strictly convex real function on a finite-dimensional real inner product space with \(h(x)/\|x\|\to\infty\). Then the conjugate \(h^*\) is continuously differentiable on the whole space, and \(y\in\partial h(x)\) exactly when \(x=\nabla h^*(y)\); no differentiability of \(h\) is assumed (`TauCeti.contDiff_fenchelConjugate_toReal_of_superlinear`, `TauCeti.mem_subdifferential_iff_eq_gradient_fenchelConjugate_of_superlinear`, [superlinear conjugates](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Superlinear.lean)). This is the finite-valued case of one half of the Legendre-type duality.

**Polars and recession.**

The bipolar theorem is proved for the absolute polar: in a real or complex locally convex space, the bipolar of a set is its closed absolutely convex hull after adjoining zero (`StrongDual.bipolar_eq_closedAbsConvexHull`, `AbsConvex.bipolar_eq_closure`, [bipolar](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/LocallyConvex/Bipolar.lean)). The one-sided polar \(\{u:\langle u,x\rangle\le1\}\) of the synopsis, with \(\overline{\operatorname{conv}}(C\cup\{0\})\), is not treated.

The recession constant \(U'(\infty)=\limsup_{s\to\infty}U(s)/s\) of a function on the half-line is defined, and for \(U\) convex on \([0,\infty)\) the quotient \(U(s)/s\) converges to it (`TauCeti.recessionConstant`, `ConvexOn.tendsto_div_recessionConstant`, [recession constant](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/RecessionConstant.lean)). This is a one-variable special case of the recession function.

**Related material.** Bernstein's theorem on completely monotone functions, in the Hausdorff–Bernstein–Widder form, from Simon's *Convexity: An Analytic Viewpoint*, is proved: a function continuous on \([0,\infty)\) and completely monotone on \((0,\infty)\) is the Laplace transform of a unique finite positive measure ([Hausdorff–Bernstein–Widder](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/CompletelyMonotone/Bernstein/HausdorffBernsteinWidder.lean); details in Section 49).

**Synopsis entries.** Covered: 12.12 (Mathlib), 12.17, 12.18, 12.19 (TauCeti). Partly covered: 12.13 (TauCeti: interior of the effective domain in finite dimension; the relative-interior and Banach-space forms are absent), 12.15 (TauCeti: subdifferential equal to the gradient at differentiability points, almost-everywhere differentiability, and the Hessian criterion; Mathlib: the one-variable monotone-derivative criterion; the singleton criterion and the monotone-gradient criterion in several variables are absent), 12.20 (TauCeti: differentiability of \(h^*\) and \(\nabla h^*=(\partial h)^{-1}\) for finite strictly convex superlinear \(h\) in finite dimension), 12.25 (Mathlib: closed convex cones; TauCeti: absolute polars), 12.26 (TauCeti: one-variable recession constant). Not covered: 12.14, 12.21, 12.22, 12.67, 12.23, 12.24.

## Minimizers, projections, and monotone operators

[Mathematical scope](SYNOPSIS12.md#minimizers-projections-and-monotone-operators).

### Mathlib

The Hilbert projection theorem gives a unique nearest point in a nonempty complete convex subset of a real inner product space (`exists_norm_eq_iInf_of_complete_convex`), and the nearest point \(v\in K\) to \(u\) is characterized by the variational inequality \(\langle u-v,w-v\rangle\le0\) for all \(w\in K\) (`norm_eq_iInf_iff_real_inner_le_zero`, `Analysis/InnerProductSpace/Projection/Minimal.lean`). This is the statement \(u-v\in N_K(v)\) behind \(J_{\gamma N_C}=P_C\); normal cones and resolvents are not defined.

In a locally convex space the closure of a convex set in the original topology equals its weak closure (`Convex.toWeakSpace_closure`, `Analysis/LocallyConvex/WeakSpace.lean`), so closed convex sets, and the sublevel sets of lower semicontinuous convex functions, are weakly closed. TauCeti proves that bounded sets in a reflexive normed space have weakly compact closure, and that norm-closed bounded convex sets are weakly compact (`TauCeti.isCompact_toWeakSpace_of_isClosed_of_convex_of_isBounded`, [weak compactness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Dual/Reflexive/WeakCompact.lean)). The resulting direct method for coercive convex functions is not stated, but follows by a short argument.

The strong-convexity definitions are recorded in the previous section (`Analysis/Convex/Strong.lean`).

### TauCeti

**Fermat's rule and monotonicity.** For a real function, \(y\in\partial f(x)\) exactly when \(x\) is a global minimizer of \(f-\langle\cdot,y\rangle\) (`TauCeti.mem_subdifferential_coe_iff_isMinOn_sub`); with \(y=0\) this is the Fermat rule, and for extended-real \(f\) it is immediate from the definition. The subdifferential is monotone: \(y_i\in\partial f(x_i)\) implies \(\langle x_2-x_1,y_2-y_1\rangle\ge0\) (`TauCeti.apply_le_apply_of_mem_subdifferential`, [subdifferentials](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Subdifferential.lean)). The resolvent \((I+\partial f)^{-1}\) of the subdifferential of a convex function on a real inner product space is \(1\)-Lipschitz on its range: \(y_i\in\partial f(x_i)\) implies \(\|x_1-x_2\|\le\|(x_1+y_1)-(x_2+y_2)\|\) (`TauCeti.norm_sub_le_norm_add_sub_add_of_mem_subdifferential`, [Alexandrov](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Alexandrov.lean)).

**Strong convexity.** A function that is \(m\)-strongly convex on a set in Mathlib's sense lies above its tangent paraboloids: if \(f\) has derivative \(f'\) within \(s\) at \(x\in s\), then \(f(x)+f'(y-x)+\tfrac m2\|y-x\|^2\le f(y)\) for \(y\in s\) (`StrongConvexOn.add_add_le_of_hasFDerivWithinAt`, [strong convexity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Strong.lean)). At a minimizer of a differentiable strongly convex function this is the quadratic-growth estimate.

**Moreau–Yosida approximation and resolvents.** On an extended metric space, for an energy \(\varphi\) and a time step \(\tau>0\), TauCeti defines the Moreau–Yosida approximation \(\varphi_\tau(x)=\inf_y(\varphi(y)+d(x,y)^2/(2\tau))\) and the resolvent, the set of its minimizers (`TauCeti.moreauYosida`, `TauCeti.moreauYosidaResolvent`, [Moreau–Yosida approximation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/GradientFlow/MoreauYosida/Basic.lean)). The approximation lies below \(\varphi\) and is nonincreasing in \(\tau\) (`TauCeti.moreauYosida_le_self`, `TauCeti.antitone_moreauYosida`); for \(\varphi\) lower semicontinuous at \(x\) with \(\varphi_\sigma(x)>-\infty\) for some \(\sigma>0\), \(\varphi_\tau(x)\to\varphi(x)\) as \(\tau\downarrow0\), and its derivative in \(\tau\) is computed (`TauCeti.tendsto_moreauYosida_nhdsGT_zero`, `TauCeti.hasDerivAt_toReal_moreauYosida`, [derivative in the time step](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/GradientFlow/MoreauYosida/Derivative.lean)). On a real inner product space the resolvent and approximation of \(\|\cdot\|^2/2\) are computed explicitly.

The resolvent is nonempty under the Ambrosio–Gigli–Savaré hypotheses (lower semicontinuity for an auxiliary convergence, relative compactness of bounded sublevels, and coercivity), in particular for a lower-semicontinuous energy on a proper metric space with \(\varphi_{\tau_0}(x_0)>-\infty\) for some \(\tau_0>\tau\) (`TauCeti.moreauYosidaResolvent_nonempty`, `TauCeti.moreauYosidaResolvent_nonempty_of_lowerSemicontinuous`, [Moreau–Yosida existence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/GradientFlow/MoreauYosida/Existence.lean); gradient flows are in Section 36). For a proper lower semicontinuous convex function on a finite-dimensional space this gives existence of proximal points. The single-valued, firmly nonexpansive proximal map on a general Hilbert space, its identification with \(J_{\gamma\partial f}\), and the differentiability of the Moreau envelope are not developed.

**Uniformly convex spaces.** The Milman–Pettis theorem is proved: a uniformly convex real Banach space is reflexive, its canonical image in the bidual being norm dense by Goldstine's theorem and closed by completeness; uniform convexity passes to subspaces (`TauCeti.surjective_inclusionInDoubleDual_of_uniformConvexSpace`, [Milman–Pettis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Uniform.lean)).

**Synopsis entries.** Covered: 12.27 (TauCeti). Partly covered: 12.28 (Mathlib: weak closedness of closed convex sets; TauCeti: weak compactness of bounded closed convex sets in reflexive spaces; the existence theorem is not stated but follows directly), 12.29 (Mathlib: definition and the equivalence with convexity of \(f-\frac\mu2\|\cdot\|^2\); TauCeti: the tangent-paraboloid bound for differentiable \(f\); existence of minimizers and strong monotonicity of \(\partial f\) are absent), 12.31 (Mathlib: the variational characterization of the nearest point, without normal cones or resolvents), 12.32 (TauCeti: existence of minimizers on proper metric spaces, hence in finite dimension, and nonexpansiveness of \((I+\partial f)^{-1}\) on its range; Hilbert-space existence, uniqueness, and the identification with \(J_{\gamma\partial f}\) are not stated, but follow by the direct method from TauCeti's affine minorants and weak compactness and a first-order argument), 12.33 (TauCeti: the envelope lies below \(f\), is monotone in \(\gamma\), and converges to \(f\) at lower semicontinuity points; differentiability, the gradient formula, and the equality of infima and minimizers are absent). Not covered: 12.66, 12.34, 12.38.

## Duality and optimality conditions

[Mathematical scope](SYNOPSIS12.md#duality-and-optimality-conditions).

### Mathlib

**Sion's minimax theorem.**

Sion's theorem is proved in `Topology/Sion.lean`, with quasiconvexity from `Analysis/Convex/Quasiconvex.lean`. For nonempty convex sets \(X,Y\) in real topological vector spaces, with \(X\) compact, lower-semicontinuous quasiconvex sections in \(x\) and upper-semicontinuous quasiconcave sections in \(y\) give the minimax equality (`Sion.minimax`, `Sion.minimax'`), formulated using order bounds and complete-order versions. When both sets are compact, the corresponding saddle-point existence theorem is available (`Sion.exists_isSaddlePointOn`). This contains the convex minimax theorem.

**Farkas' lemma.** The geometric Farkas lemma for proper cones, and its relative form \(b\in\overline{f(C)}\iff(\forall y,\ f^*y\in C^*\Rightarrow\langle b,y\rangle\ge0)\) in Hilbert spaces, are recorded in the first section. With \(C\) the nonnegative orthant this is the Farkas alternative up to the closure of \(A(\mathbb R^n_{\ge0})\); closedness of finitely generated cones is not proved. Primal and dual cone programs, weak and strong conic duality, and linear-programming duality are listed as next steps in `Analysis/Convex/Cone/Basic.lean` and are not theorems.

### TauCeti

Among theorems of the alternative, Gordan's, Stiemke's, and Tucker's theorems are proved for finite families of vectors over an arbitrary linearly ordered field, with an integral form of Tucker's theorem for finite free \(\mathbb Z\)-modules (`TauCeti.exists_forall_dual_pos_iff`, `Submodule.exists_pos_dotProduct_eq_zero_iff`, `TauCeti.exists_nonneg_sum_smul_eq_zero_and_forall_coeff_add_dual_pos`, [alternatives](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Convex/Cone/Alternative.lean)). Stiemke's lemma for a subspace of \(\mathbb R^\iota\) and its lattice version for subgroups of \(\mathbb Z^\iota\) are also in [Stiemke](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Stiemke.lean). In a locally convex ordered space with closed positive cone, the monotone continuous linear functionals determine the order ([positive dual](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Cone/PositiveDual.lean)).

**Synopsis entries.** Covered: 12.44 (Mathlib). Partly covered: 12.41 (Mathlib: Farkas with the closure of the image cone; TauCeti: the Gordan, Stiemke, and Tucker alternatives). Not covered: 12.39, 12.40, 12.42, 12.43.

## Variational convergence, nonsmooth calculus, and regularity

[Mathematical scope](SYNOPSIS12.md#variational-convergence-nonsmooth-calculus-and-regularity).

### Mathlib

Graves's open-mapping form of local surjectivity is proved: if \(f\) between Banach spaces has a surjective strict derivative at \(a\), then \(f\) maps the neighbourhood filter of \(a\) onto that of \(f(a)\) (`HasStrictFDerivAt.map_nhds_eq_of_surj`, `Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`). Quantitatively, a map approximated on a set by a continuous linear map with a nonlinear right inverse maps each closed ball in the set onto a closed ball of proportional radius (`ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse`, `Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`). The distance estimate of metric regularity is not stated.

Upper and lower hemicontinuity of correspondences are defined, with sequential characterizations, in `Topology/Semicontinuity/Defs.lean` and `Topology/Semicontinuity/Hemicontinuity.lean`. This is supporting material for Berge's theorem, which is not proved.

### TauCeti

**Γ-convergence.** TauCeti defines sequential Γ-convergence of extended-real functionals on a topological space, the lower and upper Γ-limits, and equicoercivity ([Γ-convergence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Topology/Semicontinuity/GammaConvergence.lean), `TauCeti.TendstoGamma`, `TauCeti.Equicoercive`). On a first-countable space Γ-limits are lower semicontinuous, cluster points of exact minimizers minimize the limit, and for an equicoercive sequence the infima converge to the infimum of the limit, which is attained (`TauCeti.TendstoGamma.isMinOn_of_tendsto`, `TauCeti.TendstoGamma.tendsto_iInf`, `TauCeti.TendstoGamma.exists_isMinOn`). In \(\mathbb R^n\) Γ-convergence is epi-convergence. Sequences of bounded energy have convergent subsequences (`TauCeti.TendstoGamma.exists_tendsto_subseq`), but the conclusion for \(\varepsilon_n\)-minimizers is not stated.

Γ-convergence in a pseudometric space, together with equicoercivity of the penalized energies, implies convergence of the Moreau–Yosida approximations and of resolvent steps (`TauCeti.TendstoGamma.tendsto_moreauYosida`, `TauCeti.TendstoGamma.exists_tendsto_mem_moreauYosidaResolvent`, [resolvent stability](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/GradientFlow/MoreauYosida/GammaConvergence.lean)). This is one direction of Attouch's theorem in a metric setting; Mosco convergence and the converse are not present.

**Hoffman's bound.** The homogeneous case of Hoffman's error bound is proved: for finitely many linear functionals \(a_j\) on a finite-dimensional space over a linearly ordered field, a vector with \(a_j(w)\ge-c\) for all \(j\) lies within \(O(c)\), measured by any finite family of test functionals, of the cone \(\{a_j\ge0\}\) (`TauCeti.exists_forall_abs_apply_sub_le_of_forall_neg_le`, [error bound](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Convex/Cone/ErrorBound.lean)).

**Synopsis entries.** Partly covered: 12.47 (TauCeti: convergence of infima, attainment, and minimality of cluster points of exact minimizers), 12.48 (TauCeti: Γ-convergence with equicoercivity implies convergence of the Moreau–Yosida approximations), 12.54 (Mathlib: Graves's local surjectivity, without the metric-regularity estimate), 12.55 (TauCeti: the homogeneous case). Not covered: 12.45, 12.68, 12.46, 12.49, 12.50, 12.51, 12.52, 12.53.

## Limiting subdifferentials and nonlinear programming

[Mathematical scope](SYNOPSIS12.md#limiting-subdifferentials-and-nonlinear-programming).

### Mathlib

Lagrange multiplier theorems for smooth equality-constrained extrema are in `Analysis/Calculus/LagrangeMultipliers.lean`. If \(\varphi\) has a local extremum at \(x_0\) on a level set of \(f=(f_1,\dots,f_n)\), with strict derivatives on a complete space, then the differentials of \(\varphi\) and the \(f_i\) are linearly dependent; the multiplier of \(\varphi\) may vanish (`IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`, `IsLocalExtrOn.linear_dependent_of_hasStrictFDerivAt`). This is the Fritz John condition for equality constraints only. The Karush–Kuhn–Tucker theorem is a TODO in that file; Section 36 states the hypotheses.

**Synopsis entries.** Partly covered: 12.74 (Mathlib: the Fritz John condition for equality constraints). Not covered: 12.70–12.73, 12.75.

## Basic convergence theorems for convex algorithms

[Mathematical scope](SYNOPSIS12.md#basic-convergence-theorems-for-convex-algorithms).

The nearest supporting material is TauCeti's minimizing-movement theory (Section 36): iterated resolvent steps exist under the hypotheses above, and the energy decreases along them with the discrete estimate \(\varphi(u_N)+\sum_{n<N}d(u_n,u_{n+1})^2/(2\tau)\le\varphi(u_0)\) (`TauCeti.apply_add_sum_le_of_forall_mem_moreauYosidaResolvent`). No convergence theorem for a convex algorithm is proved.

**Synopsis entries.** Not covered: 12.57–12.63.

## Further conjugacy and subgradient structure

[Mathematical scope](SYNOPSIS12.md#further-conjugacy-and-subgradient-structure).

### TauCeti

Rockafellar's theorem is proved in algebraic form on a real dual pair: a set is cyclically monotone exactly when it lies in the graph of the subdifferential of a Legendre–Fenchel conjugate, a convex function that is lower semicontinuous for every topology compatible with the pairing and is never \(-\infty\) when the set is nonempty (`TauCeti.isCyclicallyMonotone_pairingCost_iff_exists_fenchelConjugate`, `TauCeti.IsCyclicallyMonotone.exists_fenchelConjugate_subset_subdifferential`, [Rockafellar](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/OptimalTransport/CTransform/Rockafellar.lean)). The general Rockafellar–Rüschendorf theorem for \(c\)-cyclically monotone sets is in [cyclical monotonicity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/OptimalTransport/CTransform/CyclicalMonotonicity.lean). Equality for maximally cyclically monotone relations and uniqueness of the potential up to a constant are not stated.

The superlinear-conjugate results of the second section give differentiability of \(f^*\) for finite strictly convex superlinear \(f\) in finite dimension, a class containing the finite strongly convex functions; the Lipschitz constant \(1/\mu\) and the converse are not proved.

**Synopsis entries.** Partly covered: 12.64 (TauCeti: \(f^*\) is \(C^1\) for finite strictly convex superlinear \(f\) in finite dimension, without the Lipschitz bound or the converse), 12.69 (TauCeti: cyclically monotone sets are exactly the subsets of subdifferential graphs of conjugates). Not covered: 12.65.
