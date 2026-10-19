# Synopsis: Univalent functions, conformal mapping, and extremal methods

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-43);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring material from Section 43 of
[CKMA-bib.md](CKMA-bib.md#ckma-43).
It develops quantitative univalence, multivalent growth, extremal length and
capacity, boundary geometry and harmonic measure, explicit mapping, circle
packing, and Loewner evolution.
The first-course mapping theorems are recalled where their quantitative
versions are needed.

Quasiconformal deformation, Teichmüller theory, and Riemann surfaces are
treated in Section 44, random conformal geometry within
[08B](CKMA-bib.md#ckma-08b), and metric and fractal geometry in
[39A](CKMA-bib.md#ckma-39a). The present selection emphasises conformal maps
and extremal methods.

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
* **33. Grunsky criterion.** For a holomorphic exterior map
  $g(z)=z+b_0+\cdots$, define $b_{mn}$ by
  $\log[(g(z)-g(w))/(z-w)]=-\sum_{m,n\geq1}b_{mn}z^{-m}w^{-n}$
  near infinity. It is univalent on $|z|>1$ exactly when
  $|\sum\sqrt{mn}\,b_{mn}x_mx_n|\leq\sum|x_n|^2$ for every
  finite complex sequence. For univalent $g$ the matrix
  $(\sqrt{mn}\,b_{mn})$ is in fact a contraction on $\ell^2$; its first
  row recovers the area theorem.
* **73. Fekete–Szegő inequality.** For $f\in\mathcal S$ and
  $0\leq\lambda<1$, $|a_3-\lambda a_2^2|\leq1+2e^{-2\lambda/(1-\lambda)}$,
  sharp for every such $\lambda$; as $\lambda\uparrow1$ this recovers
  item 9. In particular $|a_3|\leq3$.
* **10. Compactness of $\mathcal S$.** The normalized univalent
  class is compact for locally uniform convergence. Every continuous
  coefficient functional consequently attains its extrema on it.
* **11. Area and coefficients.** For univalent
  $f(z)=\sum_{n\geq1}a_nz^n$ in $\mathbb D$ (for example $f\in\mathcal S$), $0<r<1$ and $B_r=\{|z|<r\}$,
  $\operatorname{area}f(B_r)=\pi\sum_{n\geq1}n|a_n|^2r^{2n}$.
  Letting $r\uparrow1$ relates finite image area to weighted
  square summability of coefficients.
* **74. Hayman's regularity theorem.** For $f\in\mathcal S$ the limit
  $\alpha=\lim_{r\uparrow1}(1-r)^2M(r,f)$ exists, $0\leq\alpha\leq1$,
  with $\alpha=1$ only for Koebe rotations, and $|a_n|/n\to\alpha$.
  If $\alpha>0$ there is a unique radius $\arg z=\theta_0$ of greatest
  growth, along which $(1-r)^2|f(re^{i\theta_0})|\to\alpha$.
* **80. Integral means spectrum and Brennan's conjecture.** For a
  conformal map $f$ of $\mathbb D$ into $\mathbb C$ set
  $\beta_f(t)=\limsup_{r\uparrow1}\log\int_{\mathbb T}|f'(r\zeta)|^tdm
  /\log\frac1{1-r}$. It is convex in $t$; $\beta_f(t)\leq3t-1$ for
  $t\geq2/5$, sharp for the Koebe function (Feng–MacGregor), and
  $\beta_f(-1)<0.601$. Brennan's conjecture $\beta_f(-2)\leq1$ is
  equivalent to $\int_\Omega|g'|^qdA<\infty$ for $4/3<q<4$ whenever $g$
  maps a simply connected proper subdomain $\Omega\subset\mathbb C$
  conformally onto $\mathbb D$; Brennan proved this for
  $4/3<q<3+\delta$ with some $\delta>0$.

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

## Multivalent functions

A holomorphic $f$ on $\mathbb D$ is **$p$-valent** if it takes no value more
than $p$ times, and **(areally) mean $p$-valent**, $p>0$, if for every
$R>0$ the average over $|w|<R$, with respect to area, of the number of
roots of $f(z)=w$ is at most $p$. Write $f(z)=\sum_{n\geq0}a_nz^n$ and
$\mu_p=\sum_{\nu\leq p}|a_\nu|$.

* **75. Growth of mean $p$-valent functions.** A mean $p$-valent
  function has at most $p$ zeros in $\mathbb D$ and satisfies
  $M(r,f)\leq A(p)\mu_p(1-r)^{-2p}$ (Cartwright for $p$-valent,
  Spencer for mean $p$-valent functions). The limit
  $\alpha=\lim_{r\uparrow1}(1-r)^{2p}M(r,f)$ exists and is finite, and
  for $\alpha>0$ there is a unique radius of greatest growth (Hayman).
  For $p=1$ this gives item 74.
* **79. Coefficients of mean $p$-valent functions.** A mean $p$-valent
  $f$ satisfies $|a_n|\leq A(p)\mu_pn^{2p-1}$ for $p>1/4$ (Biernacki,
  Spencer), $|a_n|\leq A\mu_pn^{-1/2}\log(n+1)$ for $p=1/4$, and
  $a_n=o(n^{-1/2})$ for $p<1/4$. For integer $p$ the exponent $2p-1$ is
  attained by the $p$-valent function $k(z)^p=z^p(1-z)^{-2p}$.

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
  and a normalized chain. Maps onto the plane minus a Jordan arc to
  infinity (slit maps) are dense in $\mathcal S$, which reduces many
  extremal problems to Loewner's equation with a single moving point.
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
  Two locally univalent functions on a connected domain have the same
  Schwarzian exactly when one is a fixed Möbius transformation of the other.
* **30. Kraus necessary bound.** Univalence on $\mathbb D$ implies
  $\sup_z(1-|z|^2)^2|Sf(z)|\leq6$.
* **31. Nehari sufficient bound.** A locally univalent meromorphic
  function on $\mathbb D$ with
  $\sup_z(1-|z|^2)^2|Sf(z)|\leq2$ is univalent.
* **32. Becker's criterion.** A locally univalent holomorphic $f$ on
  $\mathbb D$ with $(1-|z|^2)|zf''(z)/f'(z)|\leq1$ throughout is
  univalent; the constant $1$ is sharp.

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

* **34. Conformal invariance.** Extremal length is unchanged by a
  conformal map, because metric lengths and metric areas transform
  with matching derivative factors.
* **35. Quadrilateral theorem.** A Jordan domain with four ordered
  marked boundary points is conformal to a rectangle, uniquely up to
  similarity with the corners matched. For curves joining the vertical
  sides of a rectangle of width $a$ and height $b$, $\Lambda=a/b$.
* **36. Conjugate-family reciprocity.** The extremal lengths of the
  two opposite-side curve families in a quadrilateral multiply to one.
* **37. Annular modulus.** Curves joining the two boundaries of
  $r<|z|<R$ have extremal length $(2\pi)^{-1}\log(R/r)$.
  Essential closed curves have the reciprocal extremal length.
* **38. Monotonicity and comparison.** Enlarging a curve family
  decreases its extremal length. If every $\gamma\in\Gamma_1$ contains
  some $\gamma'\in\Gamma_2$, then $\Lambda(\Gamma_1)\geq\Lambda(\Gamma_2)$,
  by the admissible-length inequality.
* **39. Series and parallel principles.** If every connecting curve
  crosses disjoint regions successively, its extremal length is at
  least the sum of their crossing extremal lengths. For curve families
  confined to disjoint parallel regions, reciprocal extremal lengths add.
* **40. Condenser duality.** For a ring domain, the minimum
  $\int|\nabla u|^2dA$ over potentials with boundary values zero
  and one equals the reciprocal of the connecting extremal length.
  The minimizer is the harmonic capacitary potential.
* **41. Reduced modulus.**
  $\lim_{\varepsilon\downarrow0}[\operatorname{mod}(D\setminus
  \overline B(a,\varepsilon))+(2\pi)^{-1}\log\varepsilon]
  =(2\pi)^{-1}\log r_D(a)$.
  Conformal radius is monotone under domain inclusion, strictly unless
  the simply connected domains agree.
* **42. Grötzsch and Teichmüller extremal rings.** Among ring domains in
  $\mathbb D$ separating $\{0,r\}$ from $\mathbb T$, the Grötzsch ring
  $\mathbb D\setminus[0,r]$ has the largest modulus, which is less than
  $(2\pi)^{-1}\log(4/r)$. Among rings separating $\{-1,0\}$ from
  $\{w,\infty\}$ with $|w|=P$, the Teichmüller ring
  $\mathbb C\setminus([-1,0]\cup[P,\infty))$ has the largest modulus.
* **43. Capacity and diameter.** A nondegenerate planar continuum
  $E$ has logarithmic capacity at least $\operatorname{diam}(E)/4$.
  Segments attain equality. The exterior normalized map has leading
  coefficient equal to the continuum's capacity when its complement is simply connected.
  For every compact set, logarithmic capacity equals the transfinite
  diameter and the Chebyshev constant (Fekete–Szegő).
* **44. Symmetrization of energy.** Steiner and circular symmetrization
  decrease the Dirichlet energy of the corresponding rearranged
  admissible functions. They therefore give condenser-capacity and
  extremal-length comparison inequalities.
* **45. Circular symmetrization and conformal radius.** Circular
  symmetrization of a domain containing zero increases its conformal
  radius at zero, via the Green-function or reduced-modulus formulation.
* **46. Lavrentiev's inequality.** For disjoint simply connected
  plane domains $D_1,D_2$ and $a_j\in D_j$,
  $r_{D_1}(a_1)r_{D_2}(a_2)\leq|a_1-a_2|^2$.
  Complementary half-planes with symmetric marked points give equality.
* **47. Ahlfors distortion theorem.** Let $f$ map a strip-like domain
  $\{x+iy:\phi_-(x)<y<\phi_+(x)\}$, of width $\theta(x)$, conformally
  onto $\{|\operatorname{Im}w|<\pi/2\}$ with ends corresponding. If
  $\int_{x_1}^{x_2}dx/\theta(x)\geq2$, then the real parts on the
  crosscuts at $x_2$ exceed those at $x_1$ by at least
  $\pi\int_{x_1}^{x_2}dx/\theta(x)-4\pi$. Harmonic measure of a far
  end therefore decays like $\exp(-\pi\int dx/\theta)$.

## Boundary correspondence and harmonic measure

Prime ends describe boundary approaches by nested crosscuts. For a
simply connected proper domain they form the natural boundary circle.
For bounded $D$, **harmonic measure** $\omega_D^a$ represents the
harmonic extension functional at $a$.

* **48. Carathéodory kernel theorem.** Normalized Riemann maps
  converge locally uniformly to the normalized map of a nondegenerate
  proper kernel domain exactly when the image domains converge in
  the kernel sense. This requires the same kernel for every subsequence.
* **49. Prime-end correspondence.** A Riemann map extends to a
  homeomorphism from the closed disk to the prime-end compactification
  of its image domain. A singleton prime-end impression gives an
  ordinary boundary limit at the corresponding circle point.
* **50. Local connectivity criterion.** A Riemann map onto a bounded
  simply connected domain extends continuously to the closed disk
  exactly when the boundary is locally connected.
* **51. Jordan correspondence.** For a Jordan domain, this extension
  is a homeomorphism. Local connectivity alone permits different
  circle points to have the same boundary image.
* **52. Almost everywhere limits and uniqueness.** A univalent disk
  map has finite nontangential limits almost everywhere.
  More generally, a meromorphic disk function with angular limit zero
  on a positive-arclength set is identically zero (Privalov uniqueness).
* **53. Hardy integrability of univalent maps.** Every univalent
  function on the disk belongs to $H^p$ for $0<p<1/2$.
  The Koebe function shows that the universal endpoint cannot be included.
* **54. Rectifiable boundaries.** For a bounded Jordan domain and
  Riemann map $f$, its boundary is rectifiable exactly when
  $f'\in H^1$. The boundary parametrization is then absolutely
  continuous and its length is $\int_0^{2\pi}|f'^*(e^{it})|dt$.
* **55. F. and M. Riesz boundary theorem.** On a rectifiable Jordan
  curve, harmonic measure and arclength are mutually absolutely
  continuous. Under $f(0)=a$, harmonic measure is the pushforward
  of normalized circle arclength, while boundary arclength has weight $|f'^*|$.
* **56. Kellogg–Warschawski regularity.** If a Jordan boundary is
  $C^{1,\alpha}$, $0<\alpha<1$, its Riemann map has a
  $C^{1,\alpha}$ extension with nonvanishing boundary derivative.
  Higher smoothness gives the corresponding higher derivative regularity.
* **57. Analytic corners.** If $f:\mathbb D\to D$ is a conformal map
  onto a Jordan domain $D$ with $f(\zeta)=w_0$, where $w_0$ is a corner
  of angle $\pi\alpha$ formed by analytic boundary arcs, then
  $f(z)-w_0\sim c(z-\zeta)^\alpha$, $c\ne0$, to leading order
  (higher-order terms may involve logarithms).
  Thus its derivative has the corresponding power singularity or zero.
* **58. Conformal invariance of harmonic measure.** A conformal map
  pushes harmonic measure to harmonic measure, interpreted on prime
  ends if the ordinary boundary map is not single-valued. On the
  disk the measure at $a$ has Poisson-kernel density.
* **59. Brownian representation.** On a bounded domain, harmonic
  measure is the distribution of the exit point of planar Brownian
  motion. Conformal invariance follows from the conformal time change
  of Brownian motion.
* **60. Beurling estimate.** If a closed connected set joins zero
  to $\partial B(0,R)$, a Brownian motion started at $|x|\leq r<R$
  avoids that set until exiting the ball with probability at most
  $C\sqrt{r/R}$. This controls harmonic measure near connected obstacles.
* **61. Makarov's dimension theorem.** Harmonic measure on the
  boundary of a bounded simply connected plane domain has Hausdorff
  dimension one: the infimum of the dimensions of its full-measure
  Borel sets is one. The boundary itself can have larger dimension.
* **78. Harmonic measure on arbitrary planar domains.** If
  $\Omega\subset\widehat{\mathbb C}$ is a domain whose complement has
  positive logarithmic capacity, harmonic measure for $\Omega$ is carried
  by a set of Hausdorff dimension at most one (Jones–Wolff; SYNOPSIS38,
  item 36), indeed by a set of $\sigma$-finite length (Wolff). Unlike the
  simply connected case, the dimension can be strictly less than one, for
  example for complements of suitable Cantor sets.

## Multiply connected domains and explicit polygonal mapping

* **62. Koebe's canonical domains.** Every $n$-connected plane domain
  with no point components in its complement is conformally equivalent
  to a domain bounded by $n$ circles, unique up to Möbius maps. If the
  domain contains $\infty$, there is a unique conformal map
  $z+a_1/z+\cdots$ near $\infty$ onto a horizontal parallel-slit domain;
  it maximizes $\operatorname{Re}a_1$ among univalent maps with this normalization.

* **63. Schwarz–Christoffel formula.** If $f:\mathbb H\to P$
  maps onto a polygon with angles $\pi\alpha_j$ and the last
  vertex corresponds to infinity, then
  $f(z)=A+C\int^z\prod_{j=1}^{n-1}(\zeta-x_j)^{\alpha_j-1}d\zeta$
  for ordered real prevertices and consistently chosen branches.
* **64. Schwarz–Christoffel parameter theorem.** A prescribed simple
  polygon determines prevertices, a scale, and a translation realizing
  the map. The prevertices are unique up to the automorphisms of
  $\mathbb H$, and three normalizations remove this freedom.
* **65. Disk polygon formula.** For a conformal map of the disk
  onto a bounded polygon with prevertices $\zeta_j\in\mathbb T$,
  $f'(z)=C\prod_j(1-\bar\zeta_jz)^{\alpha_j-1}$.
  The angle identity $\sum\alpha_j=n-2$ is the compatibility
  condition at the boundary.
* **66. Rectangle and elliptic integrals.** The four-vertex
  Schwarz–Christoffel integral reduces to an elliptic integral.
  Its two complete real periods determine the rectangle's side ratio,
  hence its quadrilateral modulus and extremal metric.

## Circle packing

A **circle packing** is a family of closed disks with disjoint interiors;
its tangency graph has a vertex for each disk and an edge for each tangent
pair.

* **76. Koebe–Andreev–Thurston theorem.** Every finite simple planar graph
  is the tangency graph of a circle packing in the sphere. For a
  triangulation of the sphere the packing is unique up to Möbius and
  anti-Möbius maps; for a triangulation of a closed disk there is a
  maximal packing in $\mathbb D$, with boundary circles internally
  tangent to $\mathbb T$, unique up to disk automorphisms.
* **77. Rodin–Sullivan convergence.** Let $\Omega$ be a bounded simply
  connected domain, $z_0\in\Omega$, and $f:\Omega\to\mathbb D$ the
  Riemann map with $f(z_0)=0$, $f'(z_0)>0$. Approximate $\Omega$ by the
  circles of the regular hexagonal packing of radius $\varepsilon$, map
  them to the maximal packing in $\mathbb D$ of the same combinatorics,
  normalized at the circle nearest $z_0$, and extend piecewise affinely.
  These maps converge to $f$ locally uniformly in $\Omega$ as
  $\varepsilon\downarrow0$ (Thurston's conjecture). The key estimate is
  the ring lemma: the radii of $n$ circles surrounding a given circle are
  bounded below by a constant $c(n)>0$ times its radius.

## Conformally invariant Loewner evolution

**Chordal $SLE_\kappa$** in $\mathbb H$ from zero to infinity is
the chordal Loewner chain driven by $U_t=\sqrt\kappa B_t$.
Maps to other simply connected domains specify two boundary prime ends.

* **67. Schramm characterization.** A conformally invariant family
  of chordal Loewner laws with the domain Markov property, reflection
  symmetry, and continuous driving has Brownian driving with some
  variance $\kappa$. Scaling and the Markov property force this form.
* **68. Existence of the trace.** For every $\kappa\geq0$,
  $SLE_\kappa$ is almost surely generated by a continuous curve
  (Rohde–Schramm for $\kappa\neq8$; Lawler–Schramm–Werner for $\kappa=8$).
  This is a special property of Brownian driving, beyond general
  continuous-driver Loewner existence.
* **69. SLE phase transitions.** For $0\leq\kappa\leq4$ the trace
  is simple; for $4<\kappa<8$ it has self-contacts and boundary
  contacts but is not space-filling; for $\kappa\geq8$ it is
  space-filling. The trace tends to its target prime end.
* **70. SLE dimension.** Almost surely,
  $\dim_H\gamma=\min\{1+\kappa/8,2\}$.
* **71. Locality of $SLE_6$.** Removing a hull away from the starting
  point does not change the law of $SLE_6$ before it encounters
  that hull, after conformal mapping and time change.
* **72. Restriction of $SLE_{8/3}$.** For a half-plane hull $A$
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
measure theory. Goluzin and Nehari treat canonical slit and circle domains
for multiply connected regions; Driscoll–Trefethen develops the explicit polygon maps.
Lawler, Kemppainen, and Beliaev continue Loewner theory into SLE.
The selection stops at the foundational theorems of that continuation;
specific lattice-model convergence theorems and Liouville quantum gravity
are not added as independent inventories here. Hayman's *Multivalent
Functions* supplies the mean $p$-valent growth and coefficient theory and
Hayman's regularity theorem; Stephenson's *Introduction to Circle Packing*
supplies the Koebe–Andreev–Thurston and Rodin–Sullivan theorems, and only
those foundational results are included. Pommerenke's *Boundary Behaviour*
treats integral means and Brennan's conjecture; Garnett–Marshall treats the
Jones–Wolff theorem.

Local full-text sources consulted:

* [Pommerenke, *Boundary Behaviour of Conformal Maps*](References/Pommerenke1992BoundaryBehaviourConformalMaps-SpringerGL299.pdf).
* [Dubinin, *Condenser Capacities and Symmetrization in Geometric Function Theory*](References/Dubinin2014CondenserCapacitiesSymmetrizationGeometricFunctionTheory-Birkhauser.pdf).
* [Baernstein, *Symmetrization in Analysis*](ReferencesSuppl/BaernsteinDrasinLaugesen2019SymmetrizationAnalysis-Cambridge.NMM36.pdf).
* [Driscoll–Trefethen, *Schwarz–Christoffel Mapping*](References/DriscollTrefethen2002SchwarzChristoffelMapping-CambridgeMonogACM08.pdf).
* [Hayman, *Multivalent Functions*](References/Hayman1994MultivalentFunctions-CambridgeTractsMath110.pdf).
* [Kemppainen, *Schramm–Loewner Evolution*](References/Kemppainen2017SchrammLoewnerEvolution-SpringerBriefsMathPhys24.pdf).

The local copy of Nehari's *Conformal Mapping* is image-based and was not
used as searchable full text; the statements above were compared with the
other accessible treatments.
