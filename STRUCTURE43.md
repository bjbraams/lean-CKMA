# Structure 43: Univalent functions, conformal mapping, and extremal methods

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS43.md); [bibliographical scope](CKMA-bib.md#ckma-43); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis. The closing line of each section sorts the numbered synopsis entries under that heading.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.Normed.Operator.Conformal`, `Mathlib.Analysis.Calculus.Conformal.NormedSpace`, `Mathlib.Analysis.Complex.Conformal`, `Mathlib.Analysis.InnerProductSpace.ConformalLinearMap`, `Mathlib.Geometry.Euclidean.Angle.Unoriented.Conformal`, `Mathlib.Geometry.Manifold.ConformalGroupoid`.

**Namespaces.** Conformality of a continuous linear map is `IsConformalMap`. Conformality of a differentiable map at a point is `ConformalAt`, and conformality at every point is `Conformal`. The conformal maps of a normed space form `conformalGroupoid`. TauCeti's conformal-mapping declarations are in the namespace `TauCeti`, in the directory `TauCeti/Analysis/Complex/Conformal/`.

## Schlicht functions and sharp distortion

[Mathematical scope](SYNOPSIS43.md#schlicht-functions-and-sharp-distortion).

### Mathlib

**Supporting foundations: conformal linear maps.** A continuous linear map between normed spaces over a normed field is conformal when it is a nonzero scalar multiple of a linear isometry (`IsConformalMap`, `Analysis/Normed/Operator/Conformal.lean`). A map between real normed spaces is conformal at a point when it is real-differentiable there and its differential is a conformal linear map. Compositions of conformal maps are conformal, and so is multiplication by a nonzero constant (`ConformalAt`, `Analysis/Calculus/Conformal/NormedSpace.lean`). Between real inner-product spaces, a linear map is conformal if and only if it multiplies the inner product by a positive constant, and the differential of a map conformal at a point preserves angles (`Analysis/InnerProductSpace/ConformalLinearMap.lean`, `Geometry/Euclidean/Angle/Unoriented/Conformal.lean`).

For the complex plane the criterion is Cauchy–Riemann. A nonzero complex-linear map from \(\mathbb{C}\) into a complex normed space is conformal, and so is its composition with complex conjugation. A real-linear map from \(\mathbb{C}\) to itself is conformal if and only if it is nonzero and is either complex-linear or complex-linear after conjugation (`isConformalMap_iff_is_complex_or_conj_linear`). A map from the plane, complex-differentiable at a point with nonvanishing derivative, is conformal there (`DifferentiableAt.conformalAt`); a map \(\mathbb{C}\to\mathbb{C}\) is conformal at a point if and only if it is holomorphic or antiholomorphic there with nonvanishing derivative (`conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj`, `Analysis/Complex/Conformal.lean`). Antiholomorphic maps, including complex conjugation, are counted as conformal. The file records as a TODO that a map conformal at every point of a connected open set is holomorphic throughout or antiholomorphic throughout. None of this concerns the class \(\mathcal S\).

### TauCeti

**Supporting foundations: Riemann mapping and the disc.** The Riemann mapping theorem is proved for simply connected open proper subsets of \(\mathbb{C}\), with its holomorphic inverse, a homeomorphism and conformal-equivalence packaging, and the normalization \(f(z_0)=0\), \(f'(z_0)>0\) with uniqueness (`TauCeti.riemannMapping`, `TauCeti.riemannMapping_normalized`; [existence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/RiemannMapping/Existence.lean), [normalization](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/RiemannMapping/Normalization.lean), [uniqueness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/RiemannMapping/Uniqueness.lean), [homeomorphism](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/RiemannMapping/Conformal.lean)). Every biholomorphic self-map of the disc is \(z\mapsto u(z-a)/(1-\bar az)\) with \(|u|=1\) ([classification](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/UnitDisc/Automorphism/Classification.lean)), the hyperbolic distance \(\operatorname{artanh}|(z-w)/(1-\bar wz)|\) is defined ([hyperbolic distance](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Hyperbolic/Distance.lean)), and Schwarz–Pick contraction, the derivative bound \(|f'(z)|(1-|z|^2)\le1-|f(z)|^2\), and rigidity are proved (`TauCeti.norm_deriv_div_one_sub_norm_sq_le`; [derivative bound](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/SchwarzPick/Derivative.lean), [Schwarz–Pick](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/SchwarzPick/Basic.lean), [rigidity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/SchwarzPick/Rigidity.lean)). These are first-course mapping theorems (Section 40), recorded here as the starting point.

Two names require care. `Koebe.lean` proves the Koebe square-root step of the Riemann mapping proof, not Koebe's one-quarter theorem ([Koebe step](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Koebe.lean)). `ExtremalFamily.lean` shows that \(|f'(z_0)|\) attains its maximum over holomorphic injections of a domain into the disc fixing a base point, using Montel and Hurwitz's theorem that a locally uniform limit of injective holomorphic maps on a connected open set is injective or constant (`TauCeti.hurwitz_injOn`; [extremal family](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/ExtremalFamily.lean), [Hurwitz](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Hurwitz.lean)); this is the injectivity ingredient of the compactness of \(\mathcal S\), not that compactness, which also needs the growth theorem.

**Area formula.** For a holomorphic map injective on a set \(s\), \(\operatorname{area}f(s)=\int_s|f'|^2\), with the weighted change-of-variables formula \(\int_{f(s)}g=\int_s|f'|^2\,g\circ f\) (`TauCeti.volume_image_eq_lintegral_enorm_deriv_sq`, `TauCeti.integral_image_eq_integral_norm_deriv_sq_smul`, [area identity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Area.lean)). The coefficient form \(\pi\sum n|a_n|^2r^{2n}\) and the Grönwall area theorem for \(\Sigma\) are not derived.

**Synopsis entries.** Partly covered: 43.11 (the area formula \(\operatorname{area}f(B_r)=\int_{B_r}|f'|^2\) in TauCeti; not its coefficient expansion). Not covered: 43.1–43.10, 43.33, 43.73, 43.74, 43.80.

## Geometric subclasses, positive real part, and subordination

[Mathematical scope](SYNOPSIS43.md#geometric-subclasses-positive-real-part-and-subordination).

### TauCeti

**Herglotz representation.** A function holomorphic on the unit disc with nonnegative real part is the Herglotz transform \(\int(\zeta+z)/(\zeta-z)\,d\mu(\zeta)\) of a finite positive measure on the circle plus an imaginary constant, and conversely every such transform is holomorphic with nonnegative real part (`TauCeti.exists_isFiniteMeasure_eq_herglotzTransform_add`, `TauCeti.differentiableOn_and_re_nonneg_iff_exists_eq_herglotzTransform_add`, [Herglotz](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Herglotz.lean)). Uniqueness of the representing measure is not stated, and the Carathéodory coefficient bounds are not derived.

**Univalence criterion.** A function on a convex set whose derivative, after a fixed rotation, has positive real part is injective (Noshiro–Warschawski; `TauCeti.injOn_of_re_mul_deriv_pos`, [univalence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Univalence.lean)). This is the case \(g(z)=z\) of the close-to-convex criterion, on any convex domain. Starlike and convex classes, subordination, and Bohr's theorem are not formalized.

**Synopsis entries.** Partly covered: 43.15 (existence of the Herglotz representation and its converse; uniqueness of \(\mu\) not stated), 43.18 (the Noshiro–Warschawski case \(g(z)=z\) on convex domains). Not covered: 43.12–43.14, 43.16, 43.17, 43.19, 43.20.

## Multivalent functions

[Mathematical scope](SYNOPSIS43.md#multivalent-functions).

**Synopsis entries.** Not covered: 43.75, 43.79.

## Loewner theory and the Schwarzian

[Mathematical scope](SYNOPSIS43.md#loewner-theory-and-the-schwarzian).

### TauCeti

As supporting material, the pre-Schwarzian derivative \(f''/f'\) has a composition rule, and two holomorphic functions with nonvanishing derivatives and equal pre-Schwarzian on a domain differ by an affine postcomposition (`TauCeti.logDeriv_deriv_comp`, `TauCeti.exists_eqOn_const_mul_add_iff_logDeriv_deriv_eqOn`, [pre-Schwarzian](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/PreSchwarzian.lean)). The Schwarzian derivative \(Sf\) itself, its Möbius invariance, and the Kraus, Nehari and Becker criteria are not formalized; nor are Loewner chains, the radial or chordal Loewner equations, or half-plane capacity.

**Synopsis entries.** Not covered: 43.21–43.32.

## Extremal length, moduli, and capacities

[Mathematical scope](SYNOPSIS43.md#extremal-length-moduli-and-capacities).

### TauCeti

As supporting material, the length–area method is proved: for a holomorphic map with finite Dirichlet integral, the lengths \(\ell(\rho)\) of the images of circles satisfy \(\int\ell(\rho)^2\,d\rho/\rho\le2\pi\operatorname{area}f(s)\), and Wolff's lemma gives, on every annulus, a circle whose image is short in terms of the area and \(\log(R/r)\), for an arbitrary measurable weight in the measure-theoretic form (`TauCeti.exists_circleImageLength_lt_of_lintegral_ne_top`; [holomorphic length–area](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/LengthArea.lean), [measure-theoretic form](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/CircleLIntegral.lean)). Extremal length of curve families, moduli of quadrilaterals and rings, conformal radius, and logarithmic capacity are not defined.

**Synopsis entries.** Not covered: 43.34–43.47.

## Boundary correspondence and harmonic measure

[Mathematical scope](SYNOPSIS43.md#boundary-correspondence-and-harmonic-measure).

### TauCeti

**Carathéodory's theorems.** A holomorphic injection of a disc onto a bounded region extends continuously to the closed disc if and only if the boundary of the region is locally connected (`TauCeti.exists_continuousOn_closedBall_eqOn_iff_locallyConnectedSpace_frontier`); for a bounded domain with Jordan-curve frontier the extension maps the closed disc onto the closure (`TauCeti.exists_continuousOn_closedBall_bijOn_ball_of_isJordanCurve_frontier`). Sources: [Carathéodory](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Caratheodory.lean), [boundary correspondence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/BoundaryCorrespondence.lean). A Jordan domain has preconnected approach regions at every boundary point, by Janiszewski's theorem; hence the extended Riemann map of a bounded Jordan domain is injective on the closed disc and **extends to a homeomorphism of the closures**, unconditionally (`TauCeti.injOn_closedBall_of_isJordanCurve_frontier`, `TauCeti.exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier`, [Jordan approach regions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Jordan/Approach.lean)). The earlier conditional route, injectivity from connected boundary fibres, remains as a separate characterization ([monotone extension](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/MonotoneExtension.lean)). Conversely, a bounded domain carried by a conformal map onto a disc, with continuous injective extension to the closure, is a Jordan domain (`TauCeti.IsJordanDomain`, [Jordan domains](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Jordan/Domain.lean)). For two conformal maps of the upper half-plane onto a bounded Jordan domain, the boundary correspondence is a real Möbius map, preserves cross-ratios, distinct real points have distinct boundary limits, and three matching boundary limits force equality ([three-point normalization](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Jordan/CrossRatio.lean)); the analogous two-point normalization holds for unbounded Jordan domains ([two-point normalization](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Jordan/TwoPointNormalization.lean)).

**Supporting boundary material.** Crosscuts of a domain and their separation properties are defined ([crosscuts](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/PrimeEnd/Crosscut/Basic.lean)); prime ends and the prime-end compactification are not constructed. A holomorphic function on a disc that extends continuously to a relatively open arc of the circle and is constant there is constant, so boundary fibres of a conformal map have empty interior (`TauCeti.eqOn_const_ball_of_eqOn_const_inter_sphere`, [arc constancy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/ArcConstancy.lean)); this is weaker than Privalov's uniqueness theorem.

**Corners.** A holomorphic injection of a half-disc neighbourhood that meets the two rays of a sector of opening \(\beta\pi\), \(0<\beta<2\), has the form \(h^\beta\) with \(h\) holomorphic across the boundary and with a simple zero at the prevertex (`TauCeti.exists_differentiableOn_injOn_cpow_eq_of_sector`, [power coordinates](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Reflection/Corner.lean)). This is the corner asymptotics for corners formed by straight segments; corners formed by general analytic arcs are not treated. Harmonic measure, its Brownian representation, and boundary-regularity theorems of Kellogg–Warschawski type are not formalized.

**Synopsis entries.** Covered: 43.50, 43.51 (TauCeti). Partly covered: 43.57 (corners between straight sides only). Not covered: 43.48, 43.49, 43.52–43.56, 43.58–43.61, 43.78.

## Multiply connected domains and explicit polygonal mapping

[Mathematical scope](SYNOPSIS43.md#multiply-connected-domains-and-explicit-polygonal-mapping).

### TauCeti

**Schwarz–Christoffel formula.** A locally conformal map of the upper half-plane with prescribed straight sides, corners of interior angle \((e_i+1)\pi\), and ends is \(AF+B\), \(A\ne0\), where \(F\) is the primitive of \(\prod_i(z-a_i)^{e_i}\) (`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary`, [formula](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Formula.lean)); the pre-Schwarzian equation \(F''/F'=\sum_ie_i/(z-a_i)\) characterizes these maps ([integration](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Converse.lean)).

**Parameter theorem.** If \(U\) is a bounded domain whose frontier is a Jordan curve and which is polygonal, coinciding near each vertex \(v_i\) with a sector of opening \((e_i+1)\pi\), \(e_i\in(-1,1)\), and with a half-plane near every other boundary point, then there are distinct real prevertices \(a_i\) and constants \(A\neq0\), \(B\) such that \(AF+B\) maps the upper half-plane bijectively onto \(U\) and sends \(a_i\) to \(v_i\); the exponents sum to \(-2\). Analogous statements hold for unbounded polygonal domains with a sector, half-strip or half-strip-exterior end (`TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_frontier`, `TauCeti.exponent_sum_eq_neg_two_of_isJordanCurve_frontier`, [polygonal Jordan domains](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/JordanPolygon.lean)). The prevertices are unique up to an automorphism of the half-plane (`TauCeti.eq_and_eqOn_of_bijOn_schwarzChristoffelPrimitive`, [prevertex uniqueness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/PrevertexUniqueness.lean)), and one prevertex can be placed at \(0\) and a second at distance \(1\) ([normalization](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/ParameterNormalization.lean)). The existence statement does not compute the prevertices from the polygon.

**Disc form and constructive direction.** The disc primitive of \(\prod_i(1-\zeta/w_i)^{e_i}\) is defined, and every half-plane Schwarz–Christoffel bijection transfers through the Cayley transform to a disc Schwarz–Christoffel bijection, the additional prevertex \(1\) receiving exponent \(-\sum_ie_i-2\), which vanishes for bounded polygons (`TauCeti.exists_bijOn_const_mul_schwarzChristoffelDiscPrimitive_add_with_infty_of_bijOn`, [disc form](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Disc/Basic.lean)). For given prevertices and exponents with \(\sum_i|e_i|\le1\) the primitive is injective (`TauCeti.injOn_schwarzChristoffelPrimitive_of_sum_abs_le_one`, [univalence criterion](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Univalence.lean)), and finite signed-height checks on the vertices certify a simple nonconvex polygon, possibly with reentrant corners, onto whose interior the primitive maps bijectively ([nonconvex mapping](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Polygon/Nonconvex/Mapping.lean)). The reduction of the four-vertex integral to elliptic integrals, and Koebe's canonical circle and slit domains, are not formalized.

**Synopsis entries.** Covered: 43.63, 43.64, 43.65 (TauCeti). Not covered: 43.62, 43.66.

## Circle packing

[Mathematical scope](SYNOPSIS43.md#circle-packing).

**Synopsis entries.** Not covered: 43.76, 43.77.

## Conformally invariant Loewner evolution

[Mathematical scope](SYNOPSIS43.md#conformally-invariant-loewner-evolution).

**Synopsis entries.** Not covered: 43.67–43.72.

## Supporting structures and related formalizations

The following entries supply related foundations. Their stated scope determines how they can be used in this sub-area.

### Mathlib

The conformal local homeomorphisms of a normed space are the morphisms of a structure groupoid, used as the atlas of a conformal manifold (`conformalGroupoid`, `Geometry/Manifold/ConformalGroupoid.lean`).
