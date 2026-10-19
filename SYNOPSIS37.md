# Synopsis: Geometric measure theory, BV, rectifiability, and currents

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-37);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring material from Section 37 of
[CKMA-bib.md](CKMA-bib.md#ckma-37).
It treats dimension and density, rectifiable sets, BV and perimeter,
currents, varifolds, geometric minimization, and integral geometry with
tomography. The final results connect
rectifiability to quantitative approximation and harmonic analysis.
Fractal dimension is included as a measure-theoretic foundation, rather
than as a catalogue of particular fractal constructions.

Metric and fractal geometry is identified as [39A](CKMA-bib.md#ckma-39a), and
graph energies and fractal diffusion as [39B](CKMA-bib.md#ckma-39b). The
emphasis here remains geometric measure, rectifiability, integration, and
compactness rather than a catalogue of fractal constructions.

Hausdorff measure $\mathcal H^k$ is normalized to equal $k$-dimensional
Lebesgue measure on a $k$-plane; $\omega_k$ is the unit $k$-ball volume.
Measures are Radon, and rectifiability and boundary identities are understood
up to the appropriate measure-zero sets. Ambient space is $\mathbb R^n$
unless another space is specified.

## Hausdorff measure, dimension, and density

* **1. Hausdorff construction.** Restricting covers to sets of diameter
  at most $\delta$, summing normalized $s$th powers of diameters,
  and letting $\delta\downarrow0$ gives a metric outer measure
  $\mathcal H^s$. Borel sets are measurable for it. With the conventional
  normalization, $\mathcal H^n$ equals Lebesgue measure on $\mathbb R^n$,
  and $\mathcal H^0$ is counting measure.
* **2. Dimension threshold.** For every set $E$ there is a critical
  exponent $\dim_HE$ below which $\mathcal H^s(E)=\infty$ and
  above which it is zero, with the usual empty-set convention.
  Countable unions have dimension the supremum of their dimensions.
  A nonempty open subset of $\mathbb R^n$ has Hausdorff dimension $n$,
  and Lipschitz maps do not increase Hausdorff dimension.
* **3. Lipschitz dimension bound.** A Lipschitz map satisfies
  $\mathcal H^s(f(E))\leq\operatorname{Lip}(f)^s\mathcal H^s(E)$.
  Bi-Lipschitz maps preserve Hausdorff dimension and null sets of each dimension.
  In particular Lipschitz maps $\mathbb R^n\to\mathbb R^n$ have Lusin's
  property (N).
* **4. Frostman's lemma.** For a compact set $E$, positivity of its
  $s$-dimensional Hausdorff content is equivalent to existence of a
  nonzero finite measure supported on $E$ with
  $\mu(B(x,r))\leq Cr^s$. This characterizes lower bounds on dimension.
* **5. Energy and dimension.** Finite Riesz energy
  $\iint|x-y|^{-s}d\mu(x)d\mu(y)$ for a nonzero finite measure
  implies $\dim_H\operatorname{supp}\mu\geq s$.
  Conversely a compact set of dimension greater than $s$ supports
  a probability measure of finite $s$-energy.
* **6. Besicovitch differentiation.** For Radon measures $\mu$ and
  $f\in L^1_{\mathrm{loc}}(\mu)$, averages over centered Euclidean
  balls converge to $f$ at $\mu$-almost every point. Differentiation
  of measures recovers Radon–Nikodym derivatives.
* **7. Density bounds.** If $E$ has finite $\mathcal H^k$ measure,
  its upper density $\limsup_{r\downarrow0}\mathcal H^k(E\cap B(x,r))/(\omega_kr^k)$
  lies in $[2^{-k},1]$ at $\mathcal H^k$-almost every $x\in E$, and
  vanishes $\mathcal H^k$-almost everywhere off $E$. Existence of an exact
  density is a stronger condition linked to rectifiability.
* **8. Projection dimension theorem.** For a Borel set $E$, almost
  every orthogonal projection to a $k$-plane has Hausdorff dimension
  $\min(k,\dim_HE)$. If $\dim_HE>k$, almost every such projection
  has positive $k$-dimensional measure.
* **70. Fourier energy and distance sets.** For a finite positive measure
  $\mu$ on $\mathbb R^n$ and $0<s<n$,
  $\iint|x-y|^{-s}d\mu\,d\mu=c_{n,s}\int|\widehat\mu(\xi)|^2|\xi|^{s-n}d\xi$.
  Consequently the Fourier dimension
  $\sup\{t\le n:|\widehat\mu(\xi)|\leq C|\xi|^{-t/2}$ for some
  $\mu\in\mathcal P(E)\}$ never exceeds $\dim_HE$ (equality defines
  Salem sets). If a Borel set $E\subset\mathbb R^n$, $n\geq2$,
  has $\dim_HE>(n+1)/2$, its distance set $\{|x-y|:x,y\in E\}$ has
  positive Lebesgue measure (Falconer); Falconer's conjectured threshold
  $n/2$ remains open, the best planar threshold being $5/4$
  (Guth–Iosevich–Ou–Wang).

Self-similar sets and their similarity dimension are SYNOPSIS39, item 74.

## Rectifiable sets, tangents, and integration

A set is **countably $k$-rectifiable** if, outside an $\mathcal H^k$-null
set, it is covered by countably many Lipschitz images of subsets of
$\mathbb R^k$. It is **purely $k$-unrectifiable** if its intersection
with every such image has zero $\mathcal H^k$ measure.
Rademacher's theorem and Lipschitz extension are SYNOPSIS05, items 34 and 33.

* **12. Smooth-piece characterization.** Countable rectifiability is
  unchanged if Lipschitz images are replaced, up to null sets, by
  countably many embedded $C^1$ submanifolds.
* **13. Area formula.** For Lipschitz $f:\mathbb R^k\to\mathbb R^n$,
  measurable $A$, and nonnegative measurable $g$,
  $$
  \int_Ag(x)J_kf(x)dx
  =\int_{\mathbb R^n}\sum_{x\in A\cap f^{-1}(y)}g(x)d\mathcal H^k(y).
  $$
  Here $J_kf=\sqrt{\det(Df^TDf)}$; multiplicity cannot generally be omitted.
  For injective maps this is the change-of-variables formula onto the image.
* **14. Coarea formula.** For Lipschitz $f:\mathbb R^n\to\mathbb R^k$,
  $k\leq n$,
  $\int gJ_kf\,dx=\int_{\mathbb R^k}\int_{f^{-1}(y)}
  g\,d\mathcal H^{n-k}dy$, with $J_kf=\sqrt{\det(DfDf^T)}$.
  For $k=1$ the Jacobian is $|\nabla f|$.
* **15. Tangential area and coarea.** On a rectifiable set the same
  formulas hold using the approximate tangent plane and its tangential
  differential. Level slices are rectifiable in the expected dimension
  for almost every level under the coarea hypotheses.
* **16. Approximate tangents.** A locally finite $\mathcal H^k$ set
  is rectifiable exactly when it has an approximate tangent $k$-plane
  almost everywhere, with the positive upper-density condition in
  the tangent definition. On rectifiable sets that plane is unique almost everywhere.
* **17. Unit density.** For a countably $k$-rectifiable set of locally
  finite measure,
  $\mathcal H^k(E\cap B(x,r))/(\omega_kr^k)\to1$
  at $\mathcal H^k$-almost every $x\in E$.
* **18. Preiss's density theorem.** If a Radon measure has a positive
  finite $k$-density at almost every point, it is a $k$-rectifiable
  measure: absolutely continuous with respect to $\mathcal H^k$
  on a countably $k$-rectifiable set.
* **19. Integer dimension of exact densities.** If
  $\lim_{r\downarrow0}\mu(B(x,r))/r^s$ exists and lies in
  $(0,\infty)$ at almost every point of a nonzero Radon measure,
  then $s$ is an integer.
* **20. Rectifiable–unrectifiable decomposition.** A finite
  $\mathcal H^k$ set splits, uniquely modulo null sets, into a
  rectifiable part and a purely unrectifiable part.
* **21. Besicovitch–Federer projection theorem.** A set of finite
  $\mathcal H^k$ measure is purely $k$-unrectifiable exactly when
  almost every projection to a $k$-plane has zero $\mathcal H^k$ measure.
* **22. Tangent measures on rectifiable sets.** If
  $\mu=\theta\mathcal H^k\!\restriction E$ is rectifiable, then
  at almost every point, normalized blowups converge to
  $\theta(x)\mathcal H^k\!\restriction T_xE$.
  General tangent measures are nonzero weak limits of rescaled measures.

## BV functions, traces, and jump structure

A function $u\in L^1(\Omega)$ belongs to **$BV$** if its distributional
gradient $Du$ is a finite vector measure. Its variation is
$|Du|(\Omega)=\sup\{\int u\operatorname{div}\phi:
\phi\in C_c^1(\Omega;\mathbb R^n),\ |\phi|\leq1\}$.

* **23. Lower semicontinuity.** $L^1_{\mathrm{loc}}$ convergence gives
  $|Du|(U)\leq\liminf_j|Du_j|(U)$ for open $U$.
  Bounded variation measures have weak-* convergent subsequences locally.
* **24. BV compactness.** On a bounded Lipschitz domain, bounded sets
  in $BV$ are precompact in $L^1$. Their limits are BV and satisfy
  the variation liminf inequality. Local versions hold on arbitrary open
  sets with uniform local bounds.
* **25. Strict smooth approximation.** Every BV function on an open
  set admits $u_j\in C^\infty\cap BV$ with $u_j\to u$ in $L^1$
  and $\int|\nabla u_j|\to|Du|(\Omega)$.
* **26. Trace theorem.** On a bounded Lipschitz domain there is a
  bounded linear trace $BV(\Omega)\to L^1(\partial\Omega)$.
  The trace is characterized by interior approximate limits at almost
  every boundary point and enters the integration-by-parts formula:
  for $u\in BV(\Omega)$ and $\phi$ continuously differentiable near
  $\overline\Omega$,
  $\int_\Omega u\,\operatorname{div}\phi\,dx+\int_\Omega\phi\cdot dDu
  =\int_{\partial\Omega}\operatorname{Tr}u\,\phi\cdot\nu\,d\mathcal H^{n-1}$,
  with $\nu$ the outward unit normal.
* **27. Jump-set structure.** The approximate jump set $J_u$ is
  countably $(n-1)$-rectifiable and has two one-sided approximate
  values $u^\pm$ and normal $\nu_u$ almost everywhere.
  Approximate discontinuities outside $J_u$ form an
  $\mathcal H^{n-1}$-null set.
* **28. Derivative decomposition.** For scalar BV,
  $Du=\nabla u\,dx+(u^+-u^-)\nu_u\mathcal H^{n-1}\!\restriction J_u+D^cu$.
  The Cantor part is singular to Lebesgue measure and vanishes on
  every set of finite, or sigma-finite, $\mathcal H^{n-1}$ measure.
* **29. BV chain rule.** If $F\in C^1(\mathbb R)$ has bounded derivative
  and $F(0)=0$,
  the diffuse derivative of $F(u)$ is $F'(\widetilde u)$ times
  the diffuse derivative of $u$, and its jump derivative is
  $(F(u^+)-F(u^-))\nu_u\mathcal H^{n-1}\!\restriction J_u$.
  Lipschitz $F$ always gives $|D(F(u))|\leq\operatorname{Lip}(F)|Du|$.
  The normalization $F(0)=0$ ensures $F(u)\in L^1$.
* **30. Coarea for BV.** For scalar $u$,
  $|Du|(\Omega)=\int_{\mathbb R}P(\{u>t\};\Omega)dt$.
  Almost every superlevel set therefore has finite perimeter.
* **31. BV Sobolev inequality.** For $n\geq2$ and
  $u\in BV(\mathbb R^n)$,
  $\|u\|_{n/(n-1)}\leq C_n|Du|(\mathbb R^n)$; by the coarea formula
  the sharp constant $C_n=(n\omega_n^{1/n})^{-1}$ is equivalent to the
  isoperimetric inequality.
  On bounded connected Lipschitz domains the corresponding Poincaré
  estimate applies after subtracting the mean.
* **32. Slicing BV functions.** For almost every line parallel to a
  fixed direction, the restriction is one-dimensional BV. Integrating
  the variations of these slices recovers the variation of the
  directional derivative measure.
* **33. Alberti's rank-one theorem.** For vector-valued BV functions,
  the polar matrix of the singular derivative $D^su$ has rank one
  at $|D^su|$-almost every point.
* **34. SBV compactness.** In **$SBV$**, $D^cu=0$.
  Uniform bounds on $\|u_j\|_\infty$,
  $\int|\nabla u_j|^p$, $p>1$, and $\mathcal H^{n-1}(J_{u_j})$
  on a bounded domain give an $L^1$ convergent subsequence with SBV
  limit, weakly convergent gradients, and lower semicontinuous jump measure.
* **35. Mumford–Shah existence.** For bounded $g$, a bounded Lipschitz
  domain, and $\beta,\lambda>0$, the functional
  $\int|\nabla u|^2+\beta\mathcal H^{n-1}(J_u)
  +\lambda\int|u-g|^2$ has an SBV minimizer. Truncation gives
  $|u|\leq\|g\|_\infty$, and SBV compactness supplies existence.
  Minimizers satisfy $\mathcal H^{n-1}(\Omega\cap\overline{J_u}\setminus J_u)=0$,
  so $(\overline{J_u},u)$ solves the original problem with closed
  discontinuity sets (De Giorgi–Carriero–Leaci).

## Sets of finite perimeter and geometric minimization

A measurable set has **finite perimeter** in $\Omega$ if
$1_E\in BV(\Omega)$, with $P(E;\Omega)=|D1_E|(\Omega)$.
Its **reduced boundary** $\partial^*E$ consists of points with a
measure-theoretic unit normal obtained by differentiation of $D1_E$.
The sharp isoperimetric inequality, with equality exactly for balls, is
SYNOPSIS14, item 1.

* **36. De Giorgi structure theorem.** The reduced boundary is
  countably $(n-1)$-rectifiable and
  $D1_E=-\nu_E\mathcal H^{n-1}\!\restriction\partial^*E$.
  Thus perimeter is exactly reduced-boundary measure.
* **37. Half-space blowup.** At every reduced-boundary point, rescaled
  characteristic functions converge locally in $L^1$ to the
  half-space determined by the measure-theoretic normal.
* **38. Essential boundary.** The essential boundary, consisting of
  points where neither phase has density one, differs from
  $\partial^*E$ by an $\mathcal H^{n-1}$-null set for a
  finite-perimeter set.
* **39. Gauss–Green theorem.** For $X\in C_c^1$,
  $\int_E\operatorname{div}X=\int_{\partial^*E}X\cdot\nu_E
  \,d\mathcal H^{n-1}$. Classical smooth boundaries are unnecessary.
* **40. Perimeter compactness.** Uniformly bounded perimeters and
  volumes give locally $L^1$ convergent subsequences of characteristic
  functions. On a common bounded containing set the convergence is global.
* **42. Relative isoperimetry.** In a ball,
  $\min(|E\cap B_r|,|B_r\setminus E|)^{(n-1)/n}
  \leq C_nP(E;B_r)$. Both phases cannot occupy substantial volume
  without an interior interface.
* **43. Perimeter submodularity.**
  $P(E\cup F;\Omega)+P(E\cap F;\Omega)
  \leq P(E;\Omega)+P(F;\Omega)$.
* **44. Existence of constrained perimeter minimizers.** A nonempty
  class of sets in a common bounded region, closed under $L^1$
  convergence and containing a finite-perimeter competitor, admits a
  perimeter minimizer. Fixed-volume constraints are preserved by that convergence.
* **45. Interior regularity of minimizing boundaries.** A locally
  perimeter-minimizing set has analytic minimal reduced boundary.
  The remaining interior boundary singular set has dimension at most
  $n-8$, and is empty for $n\leq7$, after taking the canonical
  representative of the set. The bound is sharp: the Simons cone
  $\{x\in\mathbb R^8:|x_1|^2+\cdots+|x_4|^2<|x_5|^2+\cdots+|x_8|^2\}$ is
  perimeter-minimizing (Bombieri–De Giorgi–Giusti). Correspondingly,
  entire minimal graphs over $\mathbb R^{n}$ are affine exactly when $n\leq7$
  (Bernstein problem). In terms of the hypersurface dimension $m=n-1$:
  area-minimizing integral hypersurfaces have interior singular set of
  Hausdorff dimension at most $m-7$, are smooth for $m\leq6$, and can
  have isolated singularities for $m=7$.
* **46. First variation.** Smooth stationary hypersurfaces satisfy
  zero mean curvature for unconstrained area minimization and constant
  mean curvature for a fixed-volume constraint. The identities extend
  weakly through perimeter first variation.

## Currents, compactness, and Plateau's problem

An **$m$-current** is a continuous linear functional on compactly supported
smooth $m$-forms. Its boundary is $\partial T(\omega)=T(d\omega)$.
Its **mass** $\mathbf M(T)$ is the dual norm for the comass norm on forms.
A current is **normal** if it and its boundary have finite mass, and
**integral** if it and its boundary are integer-multiplicity rectifiable currents.

* **47. Boundary and pushforward.** $\partial^2T=0$.
  Lipschitz maps proper on the support define pushforwards of normal
  (more generally flat) currents, with
  $\partial(f_\#T)=f_\#\partial T$ and
  $\mathbf M(f_\#T)\leq\operatorname{Lip}(f)^m\mathbf M(T)$.
* **48. Mass lower semicontinuity.** Weak convergence of currents gives
  $\mathbf M(T)\leq\liminf\mathbf M(T_j)$, also locally.
  Boundary commutes with weak convergence.
* **49. Constancy theorem.** An $m$-dimensional integral current on a
  connected oriented $m$-manifold, with zero boundary there, is an
  integer multiple of the fundamental current.
* **50. Slicing theorem.** For an integral $m$-current and a Lipschitz
  map $f$ to $\mathbb R^k$, $k\leq m$, almost every slice is
  an integral $(m-k)$-current and
  $\int\mathbf M(\langle T,f,y\rangle)dy
  \leq\operatorname{Lip}(f)^k\mathbf M(T)$.
* **51. Deformation theorem.** Integral currents can be approximated
  in flat norm by integral polyhedral chains, with controlled mass,
  boundary mass, and support displacement. The flat norm is
  $\mathcal F(T)=\inf_{T=R+\partial S}(\mathbf M(R)+\mathbf M(S))$.
* **52. Federer–Fleming compactness.** Integral currents supported in
  a fixed compact set, with uniformly bounded mass and boundary mass,
  have a subsequence converging weakly and in ambient flat norm to
  an integral current.
* **53. Isoperimetry for integral cycles.** A compact integral
  $m$-cycle, $1\leq m<n$, bounds an integral $(m+1)$-current
  with mass at most $C_{n,m}\mathbf M(T)^{(m+1)/m}$.
* **54. Plateau existence.** A compactly supported integral boundary
  $S$ in Euclidean space has an integral mass-minimizing filling
  $T$ with $\partial T=S$. A minimizer can be chosen supported
  in the convex hull of $\operatorname{supp}S$.
* **55. Calibration criterion.** If a closed differential form has
  comass at most one and equals the oriented volume form along a
  current, that current minimizes mass in its homology class.
* **56. Tangent cones of minimizers.** Interior blowups of an
  area-minimizing integral current have subsequences converging to
  area-minimizing integral cones. Their density is the limiting
  monotone density at the center.
* **57. Higher-codimension interior regularity.** An area-minimizing
  integral $m$-current is locally a smooth minimal submanifold with
  integer multiplicity outside a singular set of Hausdorff dimension
  at most $m-2$ (Almgren; De Lellis–Spadaro). Branch points can occur in
  higher codimension; in codimension one the bound improves to $m-7$
  (entry 45).

## Varifolds and geometric regularity

An **$m$-varifold** is a Radon measure on
$\mathbb R^n\times G(n,m)$, with weight measure $\|V\|$.
Rectifiable varifolds integrate multiplicity over approximate tangent planes;
integer multiplicity makes them integral. Their first variation is
$\delta V(X)=\int\operatorname{div}_S X(x)dV(x,S)$.

* **58. Mean curvature and stationarity.** If
  $\delta V(X)=-\int H\cdot X\,d\|V\|$, then $H$ is the
  generalized mean-curvature vector. Stationarity means $\delta V=0$.
  These formulas agree with smooth submanifold first variation.
* **59. Stationary monotonicity.** For a stationary varifold,
  $r^{-m}\|V\|(B_r(x))$ is nondecreasing while the balls remain
  interior. The difference of two ratios is an integral of squared
  normal radial components; constancy forces conical structure in the annulus.
  The same holds for stationary smooth $m$-dimensional submanifolds while
  the balls avoid the boundary.
* **60. Bounded-curvature monotonicity.** An $L^p$ mean-curvature bound
  with $p>m$ gives an almost-monotonic density formula with an
  error controlled by $r^{1-m/p}\|H\|_{L^p(B_r)}$.
  Consequently the density exists at every interior support point.
* **61. Integral-varifold compactness.** Uniform local bounds on mass
  and total first variation give subsequential varifold convergence;
  limits of integral varifolds remain integral under these bounds.
* **62. Allard regularity.** Let $V$ be a rectifiable $m$-varifold with
  $\Theta\geq1$ $\|V\|$-a.e., $x\in\operatorname{supp}\|V\|$,
  $\|V\|(B_\rho(x))\leq(1+\delta)\omega_m\rho^m$, and
  $\rho^{1-m/p}\|H\|_{L^p(B_\rho(x))}\leq\delta$ for some $p>m$, where
  $\delta=\delta(n,m,p)$ is small. Then near $x$, on a ball of radius
  comparable to $\rho$, $\operatorname{supp}\|V\|$ is a multiplicity-one
  $C^{1,1-m/p}$ graph. No separate tilt-excess hypothesis is needed.
* **63. Minimal-submanifold Sobolev inequality.** On a smooth
  $m$-submanifold, $m\geq2$, compactly supported functions satisfy
  $\|u\|_{m/(m-1)}\leq C_m\int(|\nabla_Mu|+|H||u|)$.
  The same holds for rectifiable varifolds with $\Theta\geq1$.

## Quantitative rectifiability and analytic capacity

A closed set is **$k$-Ahlfors regular** if
$C^{-1}r^k\leq\mathcal H^k(E\cap B(x,r))\leq Cr^k$
for $x\in E$ and $0<r<\operatorname{diam}E$.
It is **uniformly rectifiable** if every such ball captures a fixed
positive proportion of its measure in an $L$-Lipschitz image of a
$k$-ball of comparable radius, with uniform constants.

* **64. Singular-integral characterization.** Uniform rectifiability
  implies countable rectifiability, with uniform constants at all
  locations and scales. A $k$-Ahlfors-regular set is uniformly
  rectifiable exactly when every singular integral with smooth odd
  Calderón–Zygmund kernel is bounded on $L^2(\mathcal H^k\restriction E)$
  (David–Semmes). For $k=n-1$, boundedness of the Riesz transform alone
  suffices (Nazarov–Tolsa–Volberg; for the Cauchy transform in $\mathbb C$,
  Mattila–Melnikov–Verdera).
* **65. Bilateral weak geometric lemma.** For Ahlfors-regular sets,
  uniform rectifiability is equivalent to a Carleson bound on the
  bad scales of bilateral flatness: for every $\varepsilon>0$,
  $$
  \int_{E\cap B(x,R)}\int_0^R
  1_{\{b\beta_E(y,r)>\varepsilon\}}\frac{dr}{r}d\mathcal H^k(y)
  \leq C_\varepsilon R^k.
  $$
  Here $b\beta$ is the infimum over $k$-planes of the two-sided
  normalized distance between the set and plane inside the ball.
* **66. Analyst's traveling-salesman theorem.** A compact set
  $E\subset\mathbb R^n$ lies in a connected curve of finite length
  exactly when $\sum_Q\beta_\infty(E,3Q)^2\operatorname{diam}Q<\infty$,
  over dyadic cubes meeting $E$. The least containing-curve length
  is comparable to this sum plus $\operatorname{diam}E$.
  The beta number is normalized maximal distance to a best-fitting line
  (Jones in $\mathbb R^2$; Okikiolu in $\mathbb R^n$).
* **67. Painlevé's problem for finite length.** If compact
  $E\subset\mathbb C$ has finite $\mathcal H^1$ measure, it is
  removable for bounded holomorphic functions exactly when it is
  purely unrectifiable. Equivalently its analytic capacity is zero.
  This is the link between analytic capacity (Section 38) and
  rectifiability, beyond the polar sets detected by logarithmic capacity.
* **68. Tolsa's theorem.** For compact $E\subset\mathbb C$, the analytic
  capacity $\gamma(E)$ is comparable to
  $\sup\{\mu(E):\operatorname{supp}\mu\subset E,\ \mu(B(x,r))\leq r,\
  c^2(\mu)\leq\mu(E)\}$, where $c^2(\mu)=\iiint c(x,y,z)^2d\mu^3$ and
  $c(x,y,z)$ is the reciprocal circumradius (Menger curvature). Hence
  $\gamma$ is countably semiadditive up to an absolute constant.
* **69. Rectifiability through square functions.** For a Radon measure
  with positive finite upper $k$-density almost everywhere, the
  standard $L^2$ Jones-beta square function
  $\int_0^1\beta_{\mu,2}^k(x,r)^2dr/r<\infty$ almost everywhere
  characterizes $k$-rectifiability (Tolsa; Azzam–Tolsa); finiteness of the
  upper density already gives $\mu\ll\mathcal H^k$. The beta number averages squared
  distance to a best-fitting $k$-plane, normalized by $r^{k+2}$.

## Integral geometry and tomography

$G(n,m)$ carries its rotation-invariant probability measure $\gamma_{n,m}$,
and $P_V$ is orthogonal projection onto $V\in G(n,m)$. A convex body is a
nonempty compact convex set; $\kappa_j=\omega_j$ below.

* **71. Crofton and Cauchy formulas.** If $E\subset\mathbb R^n$ is
  $\mathcal H^m$-measurable and countably $m$-rectifiable, then
  $$
  \int_{G(n,m)}\int_V\#(E\cap P_V^{-1}\{y\})\,d\mathcal H^m(y)\,d\gamma_{n,m}(V)
  =\beta(n,m)\mathcal H^m(E),\qquad
  \beta(n,m)=\frac{\Gamma(\frac{m+1}2)\Gamma(\frac{n-m+1}2)}
  {\Gamma(\frac{n+1}2)\Gamma(\frac12)}
  $$
  (Federer). For purely unrectifiable sets the left side vanishes
  (entry 21), so this integral-geometric measure detects only the
  rectifiable part. In the plane the length of a rectifiable curve is
  $\tfrac12\int_0^\pi\int_{\mathbb R}\#(\gamma\cap\ell_{\theta,p})\,dp\,d\theta$,
  $\ell_{\theta,p}=\{x\cdot(\cos\theta,\sin\theta)=p\}$ (Cauchy–Crofton).
  For a convex body $K\subset\mathbb R^n$ with nonempty interior,
  $\mathcal H^{n-1}(\partial K)=\omega_{n-1}^{-1}\int_{S^{n-1}}
  \mathcal H^{n-1}(P_{u^\perp}K)\,d\mathcal H^{n-1}(u)$ (Cauchy).
* **72. Steiner formula and Hadwiger's theorem.** For a convex body
  $K\subset\mathbb R^n$ and $r\geq0$,
  $|K+rB^n|=\sum_{j=0}^n\kappa_{n-j}V_j(K)r^{n-j}$. The intrinsic volumes
  $V_j$ are continuous in the Hausdorff metric, rigid-motion invariant,
  additive ($V_j(K\cup L)+V_j(K\cap L)=V_j(K)+V_j(L)$ when $K\cup L$ is
  convex), and homogeneous of degree $j$; $V_n$ is volume, $2V_{n-1}$ is
  surface area for $n$-dimensional $K$, and $V_0=1$. Every continuous
  rigid-motion invariant valuation on convex bodies is a linear combination
  of $V_0,\ldots,V_n$ (Hadwiger). Local Steiner formulas define curvature
  measures, and Federer extends them to sets of positive reach.
* **73. Principal kinematic formula.** Let $\mu$ be the Haar measure on
  rigid motions of $\mathbb R^n$ normalized as Lebesgue measure on
  translations times the invariant probability measure on rotations.
  For convex bodies $K,M$,
  $$
  \int\chi(K\cap gM)\,d\mu(g)=\sum_{k=0}^n
  \frac{k!\kappa_k\,(n-k)!\kappa_{n-k}}{n!\kappa_n}V_k(K)V_{n-k}(M),
  $$
  with $\chi$ the Euler characteristic ($1$ for nonempty convex sets, $0$
  for the empty set) (Blaschke, Santaló, Chern). The Crofton formula
  $\int_{A(n,k)}V_j(K\cap E)\,d\mu_k(E)=c\,V_{n-k+j}(K)$ over affine
  $k$-planes is the companion statement for flats.
* **74. Radon transform and projection–slice.** For $f\in L^1(\mathbb R^n)$,
  $Rf(\theta,s)=\int_{x\cdot\theta=s}f\,d\mathcal H^{n-1}$, $\theta\in S^{n-1}$,
  $s\in\mathbb R$. With $\widehat f(\xi)=\int e^{-ix\cdot\xi}f(x)dx$ and the
  one-dimensional transform in $s$, $(Rf(\theta,\cdot))^\wedge(\sigma)
  =\widehat f(\sigma\theta)$, so $R$ is injective on $L^1$. With the
  backprojection $R^\#g(x)=\int_{S^{n-1}}g(\theta,x\cdot\theta)\,d\theta$
  and $\Lambda=(-\partial_s^2)^{1/2}$, Schwartz functions satisfy
  $f=\tfrac12(2\pi)^{1-n}R^\#\Lambda^{n-1}Rf
  =\tfrac12(2\pi)^{1-n}(-\Delta)^{(n-1)/2}R^\#Rf$ (Radon; filtered
  backprojection). For odd $n$ the inversion is local; for even $n$,
  including computerized tomography in the plane, it is not.
* **75. Support, range, and stability.** If $f$ is continuous,
  $|x|^kf(x)$ is bounded for every $k$, and $Rf(\theta,s)=0$ for
  $|s|>A$, then $f=0$ for $|x|>A$ (Helgason's support theorem); without
  the decay hypothesis this fails. For $f\in\mathcal S(\mathbb R^n)$ the
  moments $\int s^kRf(\theta,s)ds$ are restrictions to $S^{n-1}$ of
  homogeneous polynomials of degree $k$, and these conditions
  characterize the range on even Schwartz functions of $(\theta,s)$
  (Helgason–Ludwig). For $f$ supported in a fixed ball,
  $\|Rf\|_{H^{t+(n-1)/2}}$ is comparable to $\|f\|_{H^t}$, so inversion
  is mildly ill-posed of order $(n-1)/2$.
* **76. Uniqueness in geometric tomography.** Two origin-symmetric convex
  bodies whose projections $P_{u^\perp}K$ have equal $(n-1)$-volumes for
  all $u$ coincide (Aleksandrov). Two origin-symmetric star bodies whose
  central sections $K\cap u^\perp$ have equal $(n-1)$-volumes for all $u$
  coincide (Funk), since the spherical Radon transform is injective on
  even functions. Planar convex bodies are determined by their parallel
  X-rays in a finite set of directions exactly when the set is not
  contained in the edge directions of an affinely regular polygon; thus
  four directions whose slopes have transcendental cross ratio suffice,
  while three directions never do (Gardner–McMullen).

## Reference guide

Federer, Simon, Mattila, Krantz–Parks, and Lin–Yang share the geometric
integration and rectifiability foundations; Falconer and Mattila treat
the dimension theory of self-similar sets. Ambrosio–Fusco–Pallara,
Evans–Gariepy, Giusti, and Maggi supply BV and perimeter; Federer and
Simon connect these to currents and varifolds. David–Semmes, De Lellis,
Mattila's later survey, and Tolsa provide the quantitative and
harmonic-analytic continuations. Santaló and Schneider–Weil supply the
kinematic and Crofton formulas, Gardner geometric tomography, Markoe the
analytic Radon transform, and Mattila's *Fourier Analysis and Hausdorff
Dimension* the Fourier-analytic dimension results. Minimal-surface and free-boundary
regularity overlap with Sections 33 and 52, where the PDE and geometric
viewpoints respectively receive more emphasis.

Local source copies consulted:

* [Federer, *Geometric Measure Theory*](References/Federer1996GeometricMeasureTheory-SpringerClassicsMath.pdf).
* [Krantz–Parks, *Geometric Integration Theory*](References/KrantzParks2008GeometricIntegrationTheory-Birkhauser.Cornerstones.pdf).
* [Mattila, *Rectifiability: A Survey*](References/Mattila2023RectifiabilitySurvey-Cambridge.LMSLNS483.pdf).
* [Rindler, *Calculus of Variations*](References/Rindler2018CalculusOfVariations-SpringerUTX.pdf), for the overlapping BV and relaxation material.
* [Tolsa, *Analytic Capacity, the Cauchy Transform, and Non-homogeneous Calderón–Zygmund Theory*](References/Tolsa2014AnalyticCapacityCauchyTransformNonHomogeneousCalderonZygmundTheory-BirkhäuserPM307.pdf).
* [Schneider–Weil, *Stochastic and Integral Geometry*](References/SchneiderWeil2008StochasticIntegralGeometry-SpringerPIA.pdf), for the kinematic and Crofton formulas.
* [Gardner, *Geometric Tomography*](References/Gardner2006GeometricTomography2ndEd-CambridgeEMA58.pdf).
* [Markoe, *Analytic Tomography*](References/Markoe2006AnalyticTomography-CambridgeEMA106.pdf).

The geometric regularity statements were also compared with
Leon Simon's lecture notes *Introduction to Geometric Measure Theory*,
an updated continuation of his listed lectures. The local Evans–Gariepy
copy is incomplete and was not used as evidence for its unavailable BV chapters.
