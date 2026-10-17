# Synopsis: Univalent functions, conformal mapping, and extremal methods

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects recurring material from Section 43 of
[CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md).
It develops quantitative univalence, extremal length and capacity, boundary
geometry and harmonic measure, explicit mapping, and Loewner evolution.
The first-course mapping theorems are recalled where their quantitative
versions are needed. Quasiconformal deformation and Teichmüller theory
are treated in Section 44.

A function is **univalent** if it is holomorphic and injective.
Let $\mathcal S$ consist of univalent
$f(z)=z+a_2z^2+\cdots$ on $\mathbb D$, and let $\Sigma$ consist
of univalent $g(z)=z+b_0+b_1z^{-1}+\cdots$ on $|z|>1$.
The **Koebe function** is $k(z)=z/(1-z)^2$.
All conformal maps preserve orientation.

## Schlicht functions and sharp distortion

* **1. Grönwall area theorem.** If $g\in\Sigma$, then
  $\sum_{n\geq1}n|b_n|^2\leq1$. The area of the omitted compact
  set is $\pi(1-\sum n|b_n|^2)$.
* **2. Second coefficient theorem.** Every $f\in\mathcal S$
  satisfies $|a_2|\leq2$, with equality exactly for rotations
  $e^{-i\theta}k(e^{i\theta}z)$ of the Koebe function.
* **3. Koebe quarter theorem.** Every $f\in\mathcal S$ maps
  $\mathbb D$ onto a domain containing $B(0,1/4)$.
  The constant $1/4$ is sharp.
* **4. Growth theorem.** For $f\in\mathcal S$ and $|z|=r$,
  $r/(1+r)^2\leq|f(z)|\leq r/(1-r)^2$.
  The Koebe rotations give the extremal cases.
* **5. Distortion theorem.** For $f\in\mathcal S$ and $|z|=r$,
  $(1-r)/(1+r)^3\leq|f'(z)|\leq(1+r)/(1-r)^3$.
* **6. Distance to the image boundary.** If $f$ is univalent on
  $\mathbb D$, then
  $\frac14(1-|z|^2)|f'(z)|\leq\operatorname{dist}(f(z),\partial f(\mathbb D))
  \leq(1-|z|^2)|f'(z)|$.
* **7. Pre-Schwarzian distortion.** Every univalent $f$ satisfies
  $|(1-|z|^2)f''(z)/f'(z)-2\bar z|\leq4$.
  In particular $\sup(1-|z|^2)|f''/f'|\leq6$.
* **8. de Branges's theorem.** For $f\in\mathcal S$,
  $|a_n|\leq n$ for every $n\geq2$. Equality for any such $n$
  forces a Koebe rotation.
* **9. A coefficient functional.** The area theorem applied to
  $1/f(1/z)$ gives $|a_3-a_2^2|\leq1$.
  This illustrates how exterior area controls nonlinear coefficient expressions.
* **10. Compactness of $\mathcal S$.** The normalized univalent
  class is compact for locally uniform convergence. Every continuous
  coefficient functional consequently attains its extrema on it.
* **11. Area and coefficients.** For $0<r<1$,
  $\operatorname{area}f(B_r)=\pi\sum_{n\geq1}n|a_n|^2r^{2n}$.
  Letting $r\uparrow1$ relates finite image area to weighted
  square summability of coefficients.

## Geometric subclasses, positive real part, and subordination

A normalized function is **starlike** if its image is starlike about zero,
and **convex** if its image is convex. Write $f\prec g$ if
$f=g\circ\omega$ for a disk self-map $\omega$ fixing zero.

* **12. Starlikeness criterion.** A normalized holomorphic $f$ is
  starlike and univalent precisely when
  $\Re(zf'(z)/f(z))>0$ throughout the disk, with the removable
  value one at zero.
* **13. Convexity criterion.** A normalized locally univalent $f$
  is convex precisely when $\Re(1+zf''(z)/f'(z))>0$.
* **14. Alexander correspondence.** $f$ is convex exactly when
  $zf'$ is starlike. Integration of a starlike function divided by
  $z$ gives the inverse correspondence.
* **15. Herglotz representation.** A holomorphic $p$ with
  $\Re p\geq0$ has a unique representation
  $p(z)=i\beta+\int_{\mathbb T}(\zeta+z)/(\zeta-z)d\mu(\zeta)$,
  with $\mu\geq0$ and $\beta\in\mathbb R$.
* **16. Carathéodory coefficient bounds.** If $p(0)=1$ and
  $\Re p>0$, its Taylor coefficients satisfy $|p_n|\leq2$.
  The representing measure is a probability measure; point masses
  produce the extremal functions.
* **17. Coefficients of geometric subclasses.** Starlike normalized
  functions satisfy $|a_n|\leq n$, and convex normalized functions
  satisfy $|a_n|\leq1$. Both estimates are sharp within these subclasses.
* **18. Close-to-convex univalence.** If $g$ is convex and
  $\Re(e^{i\beta}f'/g')>0$ for some real $\beta$, then $f$
  is univalent. Such derivative comparisons are a principal analytic
  criterion for close-to-convex mappings.
* **19. Littlewood subordination principle.** If $f\prec g$, then
  $\int|f(re^{it})|^pdt\leq\int|g(re^{it})|^pdt$ for $p>0$.
  More generally the integral-mean comparison holds for subharmonic
  functions composed with the subordinated maps.
* **20. Bohr's coefficient theorem.** If $|f(z)|\leq1$ on the
  disk and $f(z)=\sum a_nz^n$, then
  $\sum|a_n|r^n\leq1$ for $r\leq1/3$.
  The universal radius $1/3$ cannot be increased.

## Loewner theory and the Schwarzian

A **radial Loewner chain** is an increasing family of univalent maps
$f_t$, $f_t(0)=0$, $f_t'(0)=e^t$, with the usual local absolute
continuity in time. A **half-plane hull** $K$ is a bounded relatively
closed subset of $\mathbb H$ whose complement is simply connected.

* **21. Loewner–Kufarev equation.** Such a radial chain satisfies
  $\partial_tf_t(z)=zf_t'(z)p(z,t)$ almost everywhere in $t$,
  where $p(\cdot,t)$ is holomorphic, $\Re p\geq0$, and $p(0,t)=1$.
* **22. Radial embedding theorem.** Every $f\in\mathcal S$ is
  the initial element of a radial Loewner chain. Conversely the
  appropriate Herglotz driving data generate univalent transition maps
  and a normalized chain.
* **23. Herglotz driving measures.** For almost every time,
  $p(z,t)=\int(\zeta+z)/(\zeta-z)d\mu_t(\zeta)$ for a
  probability measure $\mu_t$ on the circle. Slit evolutions are
  described by point-mass driving data.
* **24. Hydrodynamic normalization.** A half-plane hull has a unique
  conformal map $g_K:\mathbb H\setminus K\to\mathbb H$ with
  $g_K(z)=z+a_K/z+O(z^{-2})$ at infinity; $a_K\geq0$ is its
  half-plane capacity. Capacity scales quadratically under dilations.
* **25. Chordal Loewner equation.** A continuous real driver $U_t$
  generates increasing hulls through
  $\partial_tg_t(z)=2/(g_t(z)-U_t)$, $g_0(z)=z$,
  up to swallowing times, with capacity $2t$.
  Continuous driving alone need not produce a curve-generated hull.
* **26. Slit representation.** A simple curve starting on the real
  axis and otherwise in $\mathbb H$, parametrized by half-plane
  capacity, has a continuous driver and satisfies the chordal equation.
  The driver is the image of the growing tip under $g_t$.
* **27. Capacity addition.** For nested hulls, the capacity of the
  larger hull is that of the smaller plus the capacity of the
  remaining hull after applying the smaller hull's normalized map.
* **28. Transition maps.** Radial chain inclusions give disk self-maps
  $\varphi_{s,t}=f_t^{-1}\circ f_s$ with
  $\varphi_{s,t}=\varphi_{u,t}\circ\varphi_{s,u}$ and
  $\varphi_{s,t}'(0)=e^{s-t}$. Schwarz–Pick controls their contraction.
* **29. Schwarzian calculus.** For locally univalent $f$,
  $Sf=f'''/f'-\frac32(f''/f')^2$ satisfies
  $S(f\circ g)=(Sf\circ g)(g')^2+Sg$.
  It vanishes precisely for Möbius transformations.
* **30. Kraus necessary bound.** Univalence on $\mathbb D$ implies
  $\sup_z(1-|z|^2)^2|Sf(z)|\leq6$.
* **31. Nehari sufficient bound.** A locally univalent meromorphic
  function on $\mathbb D$ with
  $\sup_z(1-|z|^2)^2|Sf(z)|\leq2$ is univalent.
* **32. Grunsky criterion.** For a holomorphic exterior map
  $g(z)=z+b_0+\cdots$, define $b_{mn}$ by
  $\log[(g(z)-g(w))/(z-w)]=-\sum_{m,n\geq1}b_{mn}z^{-m}w^{-n}$
  near infinity. It is univalent on $|z|>1$ exactly when
  $|\sum\sqrt{mn}\,b_{mn}x_mx_n|\leq\sum|x_n|^2$ for every
  finite complex sequence. These inequalities contain the area theorem.

## Extremal length, moduli, and capacities

For a family $\Gamma$ of rectifiable curves in a plane domain, define
$$
\Lambda(\Gamma)=\sup_{\rho\geq0}
\frac{(\inf_{\gamma\in\Gamma}\int_\gamma\rho\,ds)^2}
{\iint\rho^2dA},
$$
using Borel metrics of finite positive area. Its reciprocal is the
$2$-modulus of the curve family. For a simply connected proper domain
$D$ and $a\in D$, the **conformal radius** is $r_D(a)=|f'(0)|$
for $f:\mathbb D\to D$, $f(0)=a$.

* **33. Conformal invariance.** Extremal length is unchanged by a
  conformal map, because metric lengths and metric areas transform
  with matching derivative factors.
* **34. Quadrilateral theorem.** A Jordan domain with four ordered
  marked boundary points is conformal to a rectangle, uniquely up to
  similarity with the corners matched. For curves joining the vertical
  sides of a rectangle of width $a$ and height $b$, $\Lambda=a/b$.
* **35. Conjugate-family reciprocity.** The extremal lengths of the
  two opposite-side curve families in a quadrilateral multiply to one.
* **36. Annular modulus.** Curves joining the two boundaries of
  $r<|z|<R$ have extremal length $(2\pi)^{-1}\log(R/r)$.
  Essential closed curves have the reciprocal extremal length.
* **37. Monotonicity and comparison.** Enlarging a curve family
  decreases its extremal length. If every curve in one family contains
  a subcurve from another, the corresponding comparison follows by
  the admissible-length inequality.
* **38. Series and parallel principles.** If every connecting curve
  crosses disjoint regions successively, its extremal length is at
  least the sum of their crossing extremal lengths. For curve families
  confined to disjoint parallel regions, reciprocal extremal lengths add.
* **39. Condenser duality.** For a ring domain, the minimum
  $\int|\nabla u|^2dA$ over potentials with boundary values zero
  and one equals the reciprocal of the connecting extremal length.
  The minimizer is the harmonic capacitary potential.
* **40. Reduced modulus.**
  $\lim_{\varepsilon\downarrow0}[\operatorname{mod}(D\setminus
  \overline B(a,\varepsilon))+(2\pi)^{-1}\log\varepsilon]
  =(2\pi)^{-1}\log r_D(a)$.
  Conformal radius is monotone under domain inclusion, strictly unless
  the simply connected domains agree.
* **41. Capacity and diameter.** A nondegenerate planar continuum
  $E$ has logarithmic capacity at least $\operatorname{diam}(E)/4$.
  Segments attain equality. The exterior normalized map has leading
  coefficient equal to the continuum's capacity when its complement is simply connected.
* **42. Symmetrization of energy.** Steiner and circular symmetrization
  decrease the Dirichlet energy of the corresponding rearranged
  admissible functions. They therefore give condenser-capacity and
  extremal-length comparison inequalities, with plate constraints symmetrized together.
* **43. Circular symmetrization and conformal radius.** Circular
  symmetrization of a domain containing zero increases its conformal
  radius at zero. The comparison follows from the Green-function
  or reduced-modulus formulation, including the standard simply connected case.
* **44. Lavrentiev's inequality.** For disjoint simply connected
  plane domains $D_1,D_2$ and $a_j\in D_j$,
  $r_{D_1}(a_1)r_{D_2}(a_2)\leq|a_1-a_2|^2$.
  Complementary half-planes with symmetric marked points give equality.

## Boundary correspondence and harmonic measure

Prime ends describe boundary approaches by nested crosscuts. For a
simply connected proper domain they form the natural boundary circle.
For bounded $D$, **harmonic measure** $\omega_D^a$ represents the
harmonic extension functional at $a$.

* **45. Carathéodory kernel theorem.** Normalized Riemann maps
  converge locally uniformly to the normalized map of a nondegenerate
  proper kernel domain exactly when the image domains converge in
  the kernel sense. This requires the same kernel for every subsequence.
* **46. Prime-end correspondence.** A Riemann map extends to a
  homeomorphism from the closed disk to the prime-end compactification
  of its image domain. A singleton prime-end impression gives an
  ordinary boundary limit at the corresponding circle point.
* **47. Local connectivity criterion.** A Riemann map onto a bounded
  simply connected domain extends continuously to the closed disk
  exactly when the boundary is locally connected.
* **48. Jordan correspondence.** For a Jordan domain, this extension
  is a homeomorphism. Local connectivity alone permits different
  circle points to have the same boundary image.
* **49. Almost everywhere limits and uniqueness.** A univalent disk
  map has finite nontangential limits almost everywhere.
  More generally, a meromorphic disk function with angular limit zero
  on a positive-arclength set is identically zero (Privalov uniqueness).
* **50. Hardy integrability of univalent maps.** Every univalent
  function on the disk belongs to $H^p$ for $0<p<1/2$.
  The Koebe function shows that the universal endpoint cannot be included.
* **51. Rectifiable boundaries.** For a bounded Jordan domain and
  Riemann map $f$, its boundary is rectifiable exactly when
  $f'\in H^1$. The boundary parametrization is then absolutely
  continuous and its length is $\int_0^{2\pi}|f'^*(e^{it})|dt$.
* **52. F. and M. Riesz boundary theorem.** On a rectifiable Jordan
  curve, harmonic measure and arclength are mutually absolutely
  continuous. Under $f(0)=a$, harmonic measure is the pushforward
  of normalized circle arclength, while boundary arclength has weight $|f'^*|$.
* **53. Kellogg–Warschawski regularity.** If a Jordan boundary is
  $C^{1,\alpha}$, $0<\alpha<1$, its Riemann map has a
  $C^{1,\alpha}$ extension with nonvanishing boundary derivative.
  Higher smoothness gives the corresponding higher derivative regularity.
* **54. Analytic corners.** At a corner of angle $\pi\alpha$ formed
  by analytic boundary arcs, a conformal map has leading behavior
  $f(z)-w_0\sim c(z-\zeta)^\alpha$, $c\ne0$.
  Thus its derivative has the corresponding power singularity or zero.
* **55. Conformal invariance of harmonic measure.** A conformal map
  pushes harmonic measure to harmonic measure, interpreted on prime
  ends if the ordinary boundary map is not single-valued. On the
  disk the measure at $a$ has Poisson-kernel density.
* **56. Brownian representation.** On a bounded domain, harmonic
  measure is the distribution of the exit point of planar Brownian
  motion. Conformal invariance follows from the conformal time change
  of Brownian motion.
* **57. Beurling estimate.** If a closed connected set joins zero
  to $\partial B(0,R)$, a Brownian motion started at $|x|\leq r<R$
  avoids that set until exiting the ball with probability at most
  $C\sqrt{r/R}$. This controls harmonic measure near connected obstacles.
* **58. Makarov's dimension theorem.** Harmonic measure on the
  boundary of a bounded simply connected plane domain has Hausdorff
  dimension one: the infimum of the dimensions of its full-measure
  Borel sets is one. The boundary itself can have larger dimension.

## Explicit polygonal mapping

* **59. Schwarz–Christoffel formula.** If $f:\mathbb H\to P$
  maps onto a polygon with angles $\pi\alpha_j$ and the last
  vertex corresponds to infinity, then
  $f(z)=A+C\int^z\prod_{j=1}^{n-1}(\zeta-x_j)^{\alpha_j-1}d\zeta$
  for ordered real prevertices and consistently chosen branches.
* **60. Schwarz–Christoffel parameter theorem.** A prescribed simple
  polygon determines prevertices, a scale, and a translation realizing
  the map. The prevertices are unique up to the automorphisms of
  $\mathbb H$, and three normalizations remove this freedom.
* **61. Disk polygon formula.** For a conformal map of the disk
  onto a bounded polygon with prevertices $\zeta_j\in\mathbb T$,
  $f'(z)=C\prod_j(1-\bar\zeta_jz)^{\alpha_j-1}$.
  The angle identity $\sum\alpha_j=n-2$ is the compatibility
  condition at the boundary.
* **62. Rectangle and elliptic integrals.** The four-vertex
  Schwarz–Christoffel integral reduces to an elliptic integral.
  Its two complete real periods determine the rectangle's side ratio,
  hence its quadrilateral modulus and extremal metric.

## Conformally invariant Loewner evolution

**Chordal $SLE_\kappa$** in $\mathbb H$ from zero to infinity is
the chordal Loewner chain driven by $U_t=\sqrt\kappa B_t$.
Maps to other simply connected domains specify two boundary prime ends.

* **63. Schramm characterization.** A conformally invariant family
  of chordal Loewner laws with the domain Markov property, reflection
  symmetry, and continuous driving has Brownian driving with some
  variance $\kappa$. Scaling and the Markov property force this form.
* **64. Existence of the trace.** For every $\kappa\geq0$,
  $SLE_\kappa$ is almost surely generated by a continuous curve.
  This is a special property of Brownian driving, beyond general
  continuous-driver Loewner existence.
* **65. SLE phase transitions.** For $0\leq\kappa\leq4$ the trace
  is simple; for $4<\kappa<8$ it has self-contacts and boundary
  contacts but is not space-filling; for $\kappa\geq8$ it is
  space-filling. The trace tends to its target prime end.
* **66. SLE dimension.** Almost surely,
  $\dim_H\gamma=\min\{1+\kappa/8,2\}$.
* **67. Locality of $SLE_6$.** Removing a hull away from the starting
  point does not change the law of $SLE_6$ before it encounters
  that hull, after conformal mapping and time change.
* **68. Restriction of $SLE_{8/3}$.** For a half-plane hull $A$
  away from zero and a normalized map
  $\Phi_A:\mathbb H\setminus A\to\mathbb H$ fixing zero and
  having derivative one at infinity,
  $\mathbb P(\gamma\cap A=\varnothing)=\Phi_A'(0)^{5/8}$.
  Conditional on avoidance, the mapped trace has the original law.

## Reference guide

Duren, Pommerenke, Goluzin, Nehari, and Jenkins share the coefficient,
distortion, Loewner, and extremal-method core. Ahlfors and the geometric
function-theory handbooks organize the modulus viewpoint; Dubinin and
Baernstein explain capacities and symmetrization. Pommerenke and
Garnett–Marshall supply the overlapping prime-end, boundary, and harmonic
measure theory. Driscoll–Trefethen develops the explicit polygon maps.
Lawler, Kemppainen, and Beliaev continue Loewner theory into SLE.
The selection stops at the foundational theorems of that continuation;
specific lattice-model convergence theorems, circle-packing theory, and
Liouville quantum gravity are not added as independent inventories here.

Local full-text sources consulted:

* [Pommerenke, *Boundary Behaviour of Conformal Maps*](References/Pommerenke1992BoundaryBehaviourConformalMaps-SpringerGL299.pdf).
* [Dubinin, *Condenser Capacities and Symmetrization in Geometric Function Theory*](References/Dubinin2014CondenserCapacitiesSymmetrizationGeometricFunctionTheory-Birkhauser.pdf).
* [Baernstein, *Symmetrization in Analysis*](ReferencesSuppl/BaernsteinDrasinLaugesen2019SymmetrizationAnalysis-Cambridge.NMM36.pdf).
* [Driscoll–Trefethen, *Schwarz–Christoffel Mapping*](References/DriscollTrefethen2002SchwarzChristoffelMapping-CambridgeMonogACM08.pdf).
* [Kemppainen, *Schramm–Loewner Evolution*](References/Kemppainen2017SchrammLoewnerEvolution-SpringerBriefsMathPhys24.pdf).

The local copy of Nehari's *Conformal Mapping* is image-based and was not
used as searchable full text; the statements above were compared with the
other accessible treatments.
