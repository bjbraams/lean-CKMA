# Synopsis: Geometric analysis on manifolds

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-52);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring material from Section 52 of
[CKMA-bib.md](CKMA-bib.md#ckma-52).
Its organizing question is how curvature, topology, and variational structure
control differential equations and geometric evolution. General elliptic
regularity and geometric measure theory are developed in Sections 33 and 37;
the systematic theory of elliptic complexes, indices, and spectral asymptotics
belongs to Section 53. Some overlap supplies the analytic tools used here.

The current classification distinguishes metric and fractal geometry in
[39A](CKMA-bib.md#ckma-39a), diffusion in [39B](CKMA-bib.md#ckma-39b),
transport in [39C](CKMA-bib.md#ckma-39c), and positivity and Kähler analysis
in [45C](CKMA-bib.md#ckma-45c). The geometric PDE, flow, gauge, and Lorentzian
viewpoints remain here; linear geometric operators and index theory are in Section 53.

Manifolds are connected and smooth, and metrics are smooth. A *closed*
manifold is compact without boundary; *complete* means geodesically complete,
without boundary unless
specified. Write $\Delta=\mathop{\mathrm{div}}\nabla$, so $-\Delta\geq0$,
$dV$ for volume, $\mathop{\mathrm{Ric}}$ for Ricci curvature, and $R$ for
scalar curvature. Constants in local estimates may depend on the indicated
geometric bounds. A uniform estimate over varying metrics requires such
bounds; compactness of each individual manifold is insufficient.

## Geodesics, curvature comparison, and compactness

* **1. Levi-Civita connection.** Every Riemannian metric has a unique
  torsion-free metric connection. Its curvature gives sectional and Ricci
  curvatures; the Bianchi identities imply
  $\mathop{\mathrm{div}}\mathop{\mathrm{Ric}}=\tfrac12dR$.
* **2. Hopf–Rinow theorem.** On a connected Riemannian manifold,
  geodesic completeness, metric completeness, and compactness of closed
  bounded subsets are equivalent. Under these conditions any two points
  are joined by a minimizing geodesic.
* **3. Jacobi fields and second variation.** A geodesic variation has
  variational field satisfying $D_t^2J+\mathrm{Rm}(J,\dot\gamma)
  \dot\gamma=0$. The index form
  $I(V,V)=\int(|D_tV|^2-\langle\mathrm{Rm}(V,\dot\gamma)
  \dot\gamma,V\rangle)dt$ governs minimality and conjugate points.
* **4. Cartan–Hadamard theorem.** If a complete simply connected
  manifold has sectional curvature at most zero, its exponential map at
  every point is a diffeomorphism. Squared distance is convex along
  geodesics in the corresponding comparison sense.
* **5. Rauch comparison.** Upper and lower sectional-curvature
  bounds compare the lengths of perpendicular Jacobi fields with model
  space fields having the same initial data, up to the relevant first
  conjugate point. These comparisons control the exponential map and
  Hessians of distance.
* **6. Toponogov comparison.** Let $M$ be complete with sectional
  curvature at least $k$. For a geodesic triangle with minimizing sides
  (of perimeter less than $2\pi/\sqrt k$ if $k>0$), each angle is at
  least the corresponding angle of the triangle with the same side
  lengths in the simply connected model space of curvature $k$.
  Equivalently, a hinge has its opening distance at most that of the
  model hinge.
* **7. Bonnet–Myers theorem.** A complete $n$-manifold with
  $\mathop{\mathrm{Ric}}\geq(n-1)k g$, $k>0$, is compact with
  diameter at most $\pi/\sqrt k$ and finite fundamental group.
  Equality of the diameter holds only for the round sphere of
  curvature $k$ (Cheng).
* **8. Bishop–Gromov comparison.** If
  $\mathop{\mathrm{Ric}}\geq(n-1)k g$, then
  $\mathop{\mathrm{Vol}}B(p,r)/V_k(r)$ is nonincreasing in $r$,
  within the model radius range. In particular nonnegative Ricci
  curvature gives $\mathop{\mathrm{Vol}}B(p,2r)\leq2^n
  \mathop{\mathrm{Vol}}B(p,r)$.
  Buser's inequality then gives the scale-invariant Neumann Poincaré
  inequality on balls (a local Poincaré inequality, distinct from Buser's
  converse to the Cheeger inequality).
* **9. Laplacian comparison.** Under the same Ricci bound,
  $\Delta r\leq(n-1)s_k'(r)/s_k(r)$ away from the base point and
  cut locus, and in the distributional comparison sense globally off
  the base point. Here $s_k$ solves $s_k''+ks_k=0$,
  $s_k(0)=0$, $s_k'(0)=1$.
* **10. Cheeger–Gromoll splitting.** A complete connected manifold
  with nonnegative Ricci curvature that contains a line is isometric
  to $\mathbb R\times N$. A line is a geodesic minimizing distance
  between each pair of its points.
* **11. Compactness with controlled geometry.** Closed
  $n$-manifolds with $|\mathop{\mathrm{sec}}|\leq C$,
  diameter at most $D$, and volume at least $v>0$ have a
  subsequence converging, after diffeomorphisms, in $C^{1,\alpha}$
  for each $\alpha<1$. Bounds on all covariant derivatives of
  curvature improve this to smooth convergence. The hypotheses also
  yield finiteness of diffeomorphism types.
* **12. Gromov precompactness.** Complete pointed $n$-manifolds with
  $\mathop{\mathrm{Ric}}\geq-(n-1)Kg$ form a precompact family in the
  pointed Gromov–Hausdorff topology, and closed ones with diameter at
  most $D$ are precompact in the Gromov–Hausdorff topology. Bishop–Gromov
  doubling gives the uniform covering bounds; limits are length spaces
  but need not be manifolds.

## Functional inequalities, harmonic functions, and heat

* **13. Sobolev inequalities.** On a closed $n$-manifold, $n>2$,
  $\|u\|_{2n/(n-2)}^2\leq C(\|\nabla u\|_2^2+\|u\|_2^2)$.
  More generally the usual $W^{k,p}$ Sobolev and Morrey embeddings
  hold in local charts and globally on compact manifolds. Bounded
  geometry supplies uniform local versions on complete manifolds.
* **14. Rellich compactness.** On a compact manifold,
  $W^{1,p}\hookrightarrow L^q$ is compact for $q<np/(n-p)$,
  $p<n$, with the corresponding finite-exponent conclusions when
  $p\geq n$. At the critical exponent compactness can fail by concentration.
* **15. Poisson equation.** On a closed connected manifold,
  $-\Delta u=f$ is solvable precisely when $\int f\,dV=0$.
  The solution is unique after prescribing its mean, and smooth for
  smooth $f$; elliptic estimates give its Sobolev and Hölder bounds.
* **16. Maximum principles.** A harmonic function on a closed
  connected manifold is constant. The strong maximum principle and
  Hopf boundary lemma hold locally for uniformly elliptic operators
  with the standard sign condition on the zeroth-order coefficient.
* **17. Bochner identity.** For a smooth function,
  $\tfrac12\Delta|\nabla u|^2=|\nabla^2u|^2+
  \langle\nabla u,\nabla\Delta u\rangle+
  \mathop{\mathrm{Ric}}(\nabla u,\nabla u)$. Integrated on a closed
  manifold, it converts curvature bounds into gradient and spectral estimates.
* **18. Bochner vanishing.** On a closed manifold with
  $\mathop{\mathrm{Ric}}\geq0$, harmonic one-forms are parallel.
  If Ricci curvature is positive definite at one point, the first
  Betti number vanishes.
* **19. Cheng–Yau gradient estimate.** If a complete manifold has
  $\mathop{\mathrm{Ric}}\geq-(n-1)K g$ and $u>0$ is harmonic on
  $B(p,2r)$, then
  $\sup_{B(p,r)}|\nabla\log u|\leq C_n(r^{-1}+\sqrt K)$.
* **20. Positive harmonic Liouville theorem.** Every positive
  harmonic function on a complete connected manifold with
  nonnegative Ricci curvature is constant. Bounded harmonic functions
  are constant as well, by adding a constant and applying the positive case.
* **21. Li–Yau differential estimate.** On a complete manifold with
  nonnegative Ricci curvature, a positive heat solution satisfies
  $|\nabla\log u|^2-\partial_t\log u\leq n/(2t)$.
* **22. Parabolic Harnack inequality.** Under those hypotheses,
  $u(x,s)\leq u(y,t)(t/s)^{n/2}
  \exp[d(x,y)^2/(4(t-s))]$ for $0<s<t$.
  Integration of the differential estimate along space-time paths gives
  this comparison. See the
  Li–Yau paper *On the parabolic kernel of the Schrödinger operator* (Acta Math.
  1986).
* **23. Heat kernel bounds.** For a complete manifold with
  nonnegative Ricci curvature, the minimal heat kernel has two-sided
  Gaussian bounds
  $C^{-1}V(x,\sqrt t)^{-1}e^{-C d(x,y)^2/t}
  \leq p_t(x,y)\leq C V(x,\sqrt t)^{-1}e^{-d(x,y)^2/(Ct)}$,
  with constants depending only on dimension.
* **24. Stochastic completeness criterion.** On a complete manifold,
  $\int^\infty r/\log(2+V(o,r))\,dr=\infty$ implies
  $\int p_t(x,y)dV(y)=1$. In particular nonnegative Ricci curvature
  implies stochastic completeness. Completeness of the metric alone
  does not imply conservation of heat mass.
* **25. Parabolicity from volume growth.** The condition
  $\int^\infty r/V(o,r)\,dr=\infty$ is sufficient for a complete
  noncompact manifold to be parabolic, that is, to have no positive
  Green function.
  These volume tests and their potential-theoretic interpretation are
  discussed in Grigor'yan's lecture *Analysis on Manifolds and Volume Growth*
  (Nankai University, 2019).
* **28. Diameter eigenvalue bound.** If a closed connected manifold
  has nonnegative Ricci curvature and diameter $D$, the classical
  Li–Yau estimate gives $\lambda_1\geq\pi^2/(2D^2)$, and the sharp
  Zhong–Yang estimate gives $\lambda_1\geq\pi^2/D^2$.

## Conformal geometry and critical equations

* **29. Conformal scalar-curvature equation.** For $n\geq3$,
  $\widetilde g=u^{4/(n-2)}g$, $u>0$, satisfies
  $R_{\widetilde g}u^{(n+2)/(n-2)}=L_gu$, where
  $L_g=-4(n-1)(n-2)^{-1}\Delta+R_g$.
  The conformal Laplacian obeys the corresponding conformal covariance law.
* **30. Almost sharp Sobolev inequality.** On a closed manifold,
  for every $\varepsilon>0$,
  $\|u\|_{2n/(n-2)}^2\leq(K_n^2+\varepsilon)
  \|\nabla u\|_2^2+C_\varepsilon\|u\|_2^2$, where $K_n$
  is the best Euclidean Sobolev constant. Euclidean bubbles explain
  the sharp leading constant and loss of critical compactness.
* **31. Yamabe theorem.** Every conformal class on a closed
  $n$-manifold, $n\geq3$, contains a smooth metric of constant scalar
  curvature minimizing the normalized total scalar curvature in that class.
  Equivalently, the Yamabe quotient attains its infimum at a positive
  smooth solution of $L_gu=\lambda u^{(n+2)/(n-2)}$. The Yamabe
  invariant satisfies $Y(M,[g])\leq Y(S^n)$; strict inequality yields
  a minimizer (Aubin), and it holds unless $(M,[g])$ is conformal to the
  round sphere (Aubin for $n\geq6$ not locally conformally flat,
  Schoen otherwise via the positive mass theorem).
* **32. Obata rigidity in a conformal class.** If a closed connected
  Einstein manifold of dimension at least three admits a nonconstant
  conformal factor producing another constant-scalar-curvature metric,
  then it is isometric, up to scaling, to the round sphere.
* **92. Positive mass theorem in dimension three.** A smooth connected
  complete asymptotically flat three-manifold with finitely many ends,
  integrable nonnegative scalar curvature, and decay
  $g_{ij}-\delta_{ij}=O_2(r^{-q})$, $q>1/2$, has nonnegative
  ADM mass at every end. Zero mass at an end forces the manifold
  to be Euclidean space. Here ADM mass is the limit
  $(16\pi)^{-1}\int_{S_r}(\partial_jg_{ij}-\partial_ig_{jj})
  \nu^i\,dS$ in an asymptotically flat chart. See also
  Lee's formulation of positivity and rigidity (arXiv:0705.0677).
* **33. Surface uniformization.** Every conformal class on a closed
  oriented surface contains a constant-Gauss-curvature metric. Its
  curvature sign is that of the Euler characteristic; for nonpositive
  curvature the area-normalized representative is unique.

## Harmonic maps, regularity, and bubbling

For $u:(M,g)\to(N,h)$, put $E(u)=\tfrac12\int|du|^2dV$.
The tension field is $\tau(u)=\mathop{\mathrm{tr}}_g\nabla du$;
harmonic maps are critical points of $E$ and satisfy $\tau(u)=0$.

* **35. First and second variation.** The first variation is
  $\delta E(V)=-\int\langle\tau(u),V\rangle$.
  At a harmonic map the Hessian is
  $\int(|\nabla V|^2-\sum_i\langle R^N(V,du(e_i))du(e_i),V\rangle)$.
  Thus nonpositive target curvature implies stability.
* **36. Harmonic-map Bochner formula.** The identity for
  $\tfrac12\Delta|du|^2$ consists of $|\nabla du|^2$, a
  source-Ricci term, a target-curvature term with opposite sign, and
  $\langle\nabla\tau(u),du\rangle$. Consequently, on a closed
  source with nonnegative Ricci curvature and nonpositive target
  curvature, harmonic maps are totally geodesic; positive source Ricci
  curvature forces them to be constant.
* **37. Eells–Sampson existence.** Every homotopy class of maps
  between closed manifolds has a smooth harmonic representative if
  the target has nonpositive sectional curvature. It minimizes energy
  within the homotopy class.
* **38. Uniqueness in negative curvature.** If the target has
  strictly negative sectional curvature, a harmonic representative whose
  differential has rank at least two somewhere is unique in its
  homotopy class. Constant maps and maps into geodesics explain the
  necessary qualification.
* **39. Small-energy regularity.** For smooth harmonic maps into a
  compact target, sufficiently small scaled energy
  $r^{2-m}\int_{B_r}|du|^2$ gives an interior gradient bound
  $\sup_{B_{r/2}}|du|^2\leq Cr^{-m}\int_{B_r}|du|^2$,
  with the usual controlled source geometry. Minimizing maps have the
  corresponding weak-solution regularity theorem.
* **40. Partial regularity for minimizers.** An energy-minimizing
  $W^{1,2}$ map from an $m$-manifold to a compact smooth target is
  smooth off a closed singular set of Hausdorff dimension at most
  $m-3$; in dimension three the singularities are locally isolated.
  Arbitrary weakly harmonic maps need not satisfy this conclusion.
* **41. Two-dimensional weak regularity.** Every weakly harmonic
  $W^{1,2}$ map from a smooth surface into a compact smooth
  Riemannian manifold is smooth. The conservation-law and moving-frame
  structure supplies the compensation absent from a general quadratic system.
* **42. Removable punctures.** A smooth harmonic map from a
  punctured disk to a compact target with finite energy extends smoothly
  across the puncture. Rescaled concentration limits therefore extend
  to harmonic maps from $S^2$.
* **43. Bubble convergence on surfaces.** A bounded-energy sequence
  of harmonic maps from a fixed closed surface to a compact target has
  a subsequence converging smoothly away from finitely many points.
  Finitely many rescaled harmonic spheres account for all lost energy;
  the limiting energy is the energy of the base map plus their energies.
* **44. Heat-flow dissipation.** Harmonic-map heat flow
  $u_t=\tau(u)$ satisfies
  $dE(u(t))/dt=-\int|\tau(u)|^2dV$ as long as it is smooth.
* **45. Nonpositive-curvature heat flow.** For closed source and
  closed nonpositively curved target, smooth initial data give a global
  smooth heat flow. A sequence of times tending to infinity converges
  smoothly to a harmonic map in the initial homotopy class.
* **46. Surface heat-flow singularities.** For a closed surface and
  compact target there is a global weak harmonic-map heat flow that is
  smooth except at finitely many singular space-time points. Each
  singularity consumes at least the positive minimum bubbling energy;
  rescaling produces nonconstant harmonic spheres.

## Minimal submanifolds and Plateau problems

* **47. First variation of area.** With mean-curvature vector
  $\mathbf H=\mathop{\mathrm{tr}}A$, a compactly supported normal
  variation $V$ gives $\delta\mathop{\mathrm{Area}}=-\int
  \langle\mathbf H,V\rangle$. Thus minimal submanifolds are
  precisely the stationary smooth immersions.
* **48. Stability operator.** For a two-sided minimal hypersurface,
  the second variation in direction $f\nu$ is
  $\int(|\nabla f|^2-(|A|^2+\mathop{\mathrm{Ric}}(\nu,\nu))f^2)$.
  Stability means this quadratic form is nonnegative for all compactly
  supported $f$.
* **49. Minimal graphs.** The graph of $u:\Omega\subset
  \mathbb R^m\to\mathbb R$ is minimal exactly when
  $\mathop{\mathrm{div}}(\nabla u/\sqrt{1+|\nabla u|^2})=0$.
  A smooth solution minimizes area among graph competitors with its
  boundary values, by convexity of the area integrand.
* **50. Conformal harmonic parametrization.** A conformal immersion
  of a surface is minimal if and only if it is harmonic. Allowing
  isolated branch points gives the corresponding statement for
  conformal harmonic parametrized surfaces.
* **51. Weierstrass representation.** Holomorphic one-forms
  $\phi_1,\phi_2,\phi_3$ on a Riemann surface satisfying
  $\sum\phi_j^2=0$, having no common zero, and having purely
  imaginary periods give a conformal minimal immersion
  $X=\mathop{\mathrm{Re}}\int(\phi_1,\phi_2,\phi_3)$ into
  $\mathbb R^3$. Every oriented conformal minimal immersion arises
  in this way; common zeros correspond to branch points.
* **52. Douglas–Radó Plateau theorem.** Every rectifiable Jordan
  curve in Euclidean space spans a least-area disk in the parametric
  class. It admits a conformal harmonic disk parametrization, smooth
  in the interior with possible branch points in general codimension;
  in $\mathbb R^3$ a least-area disk has no interior branch points
  (Osserman, Gulliver, Alt).
* **54. Graphical regularity near a plane.** A stationary integral
  varifold sufficiently close in mass and tilt to a multiplicity-one
  plane in a ball is a $C^{1,\alpha}$ graph in a smaller ball.
  The minimal-surface equation improves the graph to smoothness.
* **55. Stable Bernstein theorem in dimension two.** A complete
  two-sided stable minimal surface in $\mathbb R^3$ is a plane.
  The stability inequality and logarithmic cutoff arguments exclude
  nonzero second fundamental form.
* **56. Bernstein theorem for graphs.** Every smooth entire
  minimal graph $\mathbb R^m\to\mathbb R$ is affine for
  $m\leq7$. Nonaffine entire examples occur in higher dimensions,
  so the dimension restriction is essential.
* **98. Min–max minimal hypersurfaces.** Every closed Riemannian
  $(n+1)$-manifold, $2\leq n\leq6$, contains a smooth closed embedded
  minimal hypersurface, obtained at the positive width of a sweepout by
  Almgren–Pitts min–max with Schoen–Simon regularity; for $n\geq7$ the
  singular set has codimension at least seven. Infinitely many exist
  (Marques–Neves, Song). On $S^3$, sweepouts by level sets realize the
  width by an embedded minimal sphere (Simon–Smith; Colding–Minicozzi).

## Mean curvature flow

Here $F_t:M^m\to\mathbb R^{m+1}$ evolves by $\partial_tF=
\mathbf H$. Write $H$ for scalar mean curvature with a consistent
normal choice, and $A$ for the second fundamental form.

* **58. Short-time existence.** Every smooth closed immersed
  hypersurface has a unique smooth mean curvature flow for a short
  time, up to the usual equivalent parametrized formulations. A graph
  evolves by $u_t=\sqrt{1+|\nabla u|^2}
  \mathop{\mathrm{div}}(\nabla u/\sqrt{1+|\nabla u|^2})$.
* **59. Evolution identities.** Along a Euclidean hypersurface flow,
  $\partial_td\mu=-H^2d\mu$,
  $(\partial_t-\Delta)H=|A|^2H$, and
  $(\partial_t-\Delta)|A|^2=-2|\nabla A|^2+2|A|^4$.
* **60. Avoidance principle.** Two initially disjoint smooth closed
  hypersurfaces remain disjoint while their flows exist. Comparison
  with shrinking spheres gives finite extinction bounds for compact
  flows. See Mantegazza's 2017 Pisa lecture notes on mean curvature flow.
* **61. Huisken monotonicity.** For $t<t_0$ put
  $\rho=(4\pi(t_0-t))^{-m/2}
  e^{-|x-x_0|^2/(4(t_0-t))}$. Then
  $d\int_{M_t}\rho\,d\mu/dt=-\int_{M_t}\rho
  |\mathbf H+(x-x_0)^\perp/(2(t_0-t))|^2d\mu$.
  Equality characterizes self-similar shrinkers about $(x_0,t_0)$;
  see the monotonicity lecture of Mantegazza's notes.
* **62. Convex hypersurface convergence.** A smooth closed strictly
  convex hypersurface in Euclidean space remains convex and shrinks
  to a point in finite time. After recentering and volume or area
  normalization it converges smoothly to a round sphere.
* **63. Curve shortening.** A smooth embedded closed plane curve
  becomes convex under curve shortening and then shrinks to a round
  point; normalized curves converge smoothly to a circle. The convex
  convergence statements are treated in
  the singularity lecture of Mantegazza's notes.
* **64. Extension criterion.** A smooth closed hypersurface flow on
  $[0,T)$ with finite $T$ extends past $T$ if $|A|$ stays
  bounded. Thus a finite maximal time forces curvature blow-up.
* **65. Density regularity.** There is a dimensional
  $\varepsilon>0$ such that Gaussian density ratios sufficiently
  close to one at all scales in a parabolic neighborhood give interior
  curvature bounds for a smooth embedded mean curvature flow.
  Multiplicity-one planar tangent flow therefore implies regularity.

## Ricci flow and curvature normalization

Ricci flow is $\partial_tg=-2\mathop{\mathrm{Ric}}$.
A gradient Ricci soliton satisfies
$\mathop{\mathrm{Ric}}+\nabla^2f=\lambda g$, with positive, zero, or
negative $\lambda$ giving shrinking, steady, or expanding solutions.

* **66. Hamilton–DeTurck existence.** A smooth metric on a closed
  manifold has a unique smooth Ricci flow for a short time. Adding a
  Lie derivative fixes diffeomorphism invariance and gives a strictly
  parabolic system; pulling back recovers Ricci flow.
* **67. Scalar evolution.** Under Ricci flow,
  $\partial_tdV=-R\,dV$ and
  $\partial_tR=\Delta R+2|\mathop{\mathrm{Ric}}|^2$.
  In particular nonnegative scalar curvature is preserved on a closed manifold.
* **68. Curvature maximum principles.** The tensor maximum
  principle preserves nonnegative curvature operator in every
  dimension, and nonnegative Ricci curvature in dimension three.
  These are invariant curvature cones for the reaction equation.
* **69. Shi derivative estimates.** A complete Ricci flow with
  $|\mathrm{Rm}|\leq K$ on $[0,T]$ satisfies
  $|\nabla^j\mathrm{Rm}|\leq C_jK t^{-j/2}$ for positive
  times in a bounded $KT$ range. Local versions require curvature
  control on a suitable parabolic ball.
* **70. Curvature blow-up criterion.** A closed Ricci flow with
  bounded full curvature on a finite time interval extends smoothly
  beyond its endpoint. Finite-time singularities therefore have
  $\sup_M|\mathrm{Rm}|\to\infty$ along a sequence of times.
* **71. Hamilton compactness.** A sequence of complete pointed
  Ricci flows with uniform curvature bounds on compact time intervals
  and a positive injectivity-radius bound at the base points at one
  time has a subsequence converging smoothly on compact subsets,
  after pointed diffeomorphisms. These analytic foundations are
  discussed in Topping's *Lectures on the Ricci Flow*.
* **72. Perelman $\mathcal F$ monotonicity.** For
  $\mathcal F(g,f)=\int(R+|\nabla f|^2)e^{-f}dV$,
  $g_t=-2\mathop{\mathrm{Ric}}$ and
  $f_t=-\Delta f+|\nabla f|^2-R$ give
  $d\mathcal F/dt=2\int|\mathop{\mathrm{Ric}}+\nabla^2f|^2e^{-f}dV$.
* **73. Perelman $\mathcal W$ monotonicity.** Put
  $\mathcal W=\int[\tau(R+|\nabla f|^2)+f-n]
  (4\pi\tau)^{-n/2}e^{-f}dV$, with the weighted measure of mass
  one and $\tau_t=-1$. If
  $f_t=-\Delta f+|\nabla f|^2-R+n/(2\tau)$, then
  $d\mathcal W/dt=2\tau\int|
  \mathop{\mathrm{Ric}}+\nabla^2f-g/(2\tau)|^2
  (4\pi\tau)^{-n/2}e^{-f}dV$.
* **74. No local collapsing.** For a closed Ricci flow on a finite
  time interval there is $\kappa>0$ such that a metric ball of
  radius $r$ with $|\mathrm{Rm}|\leq r^{-2}$ on the appropriate
  parabolic neighborhood has volume at least $\kappa r^n$,
  for bounded scales. Entropy gives the uniform constant; see
  Perelman's paper *The entropy formula for the Ricci flow and its geometric
  applications* (arXiv:math/0211159).
* **75. Hamilton's three-dimensional convergence.** A closed
  three-manifold with positive Ricci curvature evolves under
  volume-normalized Ricci flow to a constant-positive-sectional-curvature
  metric. It is therefore a spherical space form.
* **76. Differentiable sphere theorem.** A closed manifold with
  strictly pointwise quarter-pinched positive sectional curvature is
  diffeomorphic to a spherical space form; if simply connected, to a
  sphere. Ricci-flow pinching improves the curvature to the round case.
* **77. Three-dimensional geometrization.** Every closed oriented
  three-manifold decomposes along spheres into prime pieces and along
  incompressible tori in those pieces into pieces admitting Thurston
  geometries on their interiors. Ricci flow with surgery establishes
  this classification; in particular every closed simply connected three-manifold is
  diffeomorphic to $S^3$.

## Symplectic, gauge, and sub-Riemannian analysis

A symplectic form is a closed nondegenerate two-form $\omega$; an
$\omega$-compatible almost complex structure $J$ makes
$\omega(\cdot,J\cdot)$ a Riemannian metric. A $J$-holomorphic map
satisfies $du\circ j=J\circ du$.

* **78. Cauchy–Riemann Fredholm index.** On a fixed closed genus-$g$
  domain, the linearization at a $J$-holomorphic map to a complex
  $n$-dimensional target is a real elliptic Fredholm operator of index
  $2n(1-g)+2\langle c_1(TM),u_*[\Sigma]\rangle$.
  Surjectivity makes the local parametrized solution space smooth of
  this dimension.
* **79. Energy and sphere bubbling.** For compatible $J$, a
  $J$-holomorphic curve satisfies $E(u)=\int_\Sigma u^*\omega$.
  Bounded-area sequences of such spheres with three marked domain
  points in a closed target have a subsequence converging, after
  reparametrization and extraction of
  bubbles, to a stable tree of spheres with the same total area.
* **80. Symplectic nonsqueezing.** A symplectic embedding of the
  ball $B^{2n}(r)$ into the cylinder
  $B^2(R)\times\mathbb R^{2n-2}$ requires $r\leq R$.
  Holomorphic-curve area bounds give the obstruction.
* **81. Morse homology.** For a Morse function and Morse–Smale
  metric on a closed manifold, counting gradient trajectories of
  index difference one defines a differential with square zero.
  Compactification by broken trajectories proves this identity, and
  the resulting homology is singular homology.
* **82. Hamiltonian Floer continuation.** On a closed symplectically
  aspherical manifold, $\omega|_{\pi_2}=c_1|_{\pi_2}=0$,
  a nondegenerate Hamiltonian has a Floer complex generated by its
  contractible periodic orbits. Finite-energy cylinders define the
  differential, continuation identifies its homology with singular
  homology, and the number of such orbits is at least the sum of
  Betti numbers over a field.

For a connection $A$ on a bundle with compact structure group, let
$F_A=dA+A\wedge A$ and $d_A$ be its covariant exterior derivative.
Gauge transformations change local connection matrices while preserving
curvature norms.

* **83. Yang–Mills equation.** The critical equation for
  $\tfrac12\int|F_A|^2dV$ is $d_A^*F_A=0$; the Bianchi
  identity is $d_AF_A=0$. The energy and equation are gauge invariant.
* **84. Four-dimensional instantons.** On an oriented
  four-manifold, $F_A^+=0$ or $F_A^-=0$ implies Yang–Mills.
  The self-dual decomposition of the energy and the Chern–Weil
  formula show that these connections minimize energy in their
  topological class when they exist.
* **85. Uhlenbeck gauge theorem.** On a four-dimensional ball,
  sufficiently small $\|F_A\|_{L^2}$ permits a Coulomb gauge
  $d^*a=0$ with vanishing normal component at the boundary and
  $\|a\|_{W^{1,2}}\leq C\|F_A\|_2$, in scale-normalized norms.
* **86. Gauge compactness.** On a closed $n$-manifold, curvature
  bounds in $L^p$, $p>n/2$, give weak $W^{1,p}$ compactness
  modulo gauge. For Yang–Mills connections, elliptic regularity improves
  this to smooth compactness modulo gauge. Critical four-dimensional
  $L^2$ bounds instead allow point concentration and bubbling. See
  the introductory statement of the theorems in Wehrheim's *Uhlenbeck Compactness*.
* **93. Seiberg–Witten equations.** On a closed oriented Riemannian
  four-manifold with spin$^c$ structure, spinor bundles $S^\pm$, and
  determinant line $L$, the unknowns are a unitary connection $A$ on $L$
  and $\psi\in\Gamma(S^+)$, with
  $D_A^+\psi=0$ and $\frac12\rho(F_A^+)=(\psi\psi^*)_0$, where
  $\rho:\Lambda^+\to\mathop{\mathrm{End}}(S^+)$ is Clifford multiplication and
  $(\cdot)_0$ the traceless part. The gauge group
  $\mathop{\mathrm{Map}}(X,S^1)$ acts by $u\cdot(A,\psi)=(A-2u^{-1}du,u\psi)$.
  The Weitzenböck formula
  $D_A^-D_A^+=\nabla_A^*\nabla_A+\frac s4+\frac12\rho(F_A^+)$ and the
  maximum principle give $|\psi|^2\leq c\max(0,-\min_Xs)$, with $c$ fixed
  by the normalization; hence elliptic bootstrapping in Coulomb gauge
  makes the moduli space of solutions modulo gauge compact
  (Kronheimer–Mrowka).
* **94. Seiberg–Witten moduli and invariants.** For a generic self-dual
  perturbation $F_A^+\mapsto F_A^++i\eta$, the moduli space of irreducible
  solutions is a compact smooth manifold of dimension
  $\frac14(c_1(L)^2-2\chi(X)-3\sigma(X))$, oriented by a homology
  orientation. If $b^+(X)\geq2$, the resulting count is independent of
  metric and perturbation. Positive scalar curvature forces $\psi=0$
  in entry 93, so the invariants vanish then (Witten).

A Lorentzian manifold is time-oriented with signature $(-,+,\ldots,+)$;
$J^\pm(K)$ is the causal future or past of $K$. It is *globally
hyperbolic* if it is causal and every $J^+(p)\cap J^-(q)$ is compact.
A *normally hyperbolic* operator on sections of a vector bundle has
principal symbol $g^{-1}(\xi,\xi)$, as for the wave operator
$\square_g$ plus lower-order terms.

* **95. Cauchy hypersurfaces and splitting.** A time-oriented
  Lorentzian manifold is globally hyperbolic exactly when it has a Cauchy
  hypersurface, met exactly once by every inextendible timelike curve
  (Geroch). It is then isometric to $\mathbb R\times\Sigma$ with
  $g=-\beta\,dt^2+g_t$, $\beta>0$ smooth, each $\{t\}\times\Sigma$ a
  smooth spacelike Cauchy hypersurface (Bernal–Sánchez).
* **96. Cauchy problem for wave equations.** Let $P$ be normally
  hyperbolic on a globally hyperbolic manifold, $\Sigma$ a smooth
  spacelike Cauchy hypersurface with future unit normal $n$. For
  compactly supported smooth $f$, $u_0$, $u_1$ there is a unique smooth
  $u$ with $Pu=f$, $u|_\Sigma=u_0$, $\nabla_nu|_\Sigma=u_1$; it depends
  continuously on the data, and
  $\mathop{\mathrm{supp}}u\subset J^+(K)\cup J^-(K)$,
  $K=\mathop{\mathrm{supp}}f\cup\mathop{\mathrm{supp}}u_0\cup\mathop{\mathrm{supp}}u_1$
  (finite propagation speed). Energy estimates on the slabs of entry 95
  prove this (Leray; Bär–Ginoux–Pfäffle).
* **97. Green operators.** In that setting $P$ has unique advanced and
  retarded Green operators $G_\pm:C_c^\infty\to C^\infty$, with
  $PG_\pm=G_\pm P=\mathop{\mathrm{id}}$ on $C_c^\infty$ and
  $\mathop{\mathrm{supp}}G_\pm f\subset J^\pm(\mathop{\mathrm{supp}}f)$. The
  causal propagator $G=G_+-G_-$ gives an exact sequence
  $0\to C_c^\infty\xrightarrow{P}C_c^\infty\xrightarrow{G}
  C_{sc}^\infty\xrightarrow{P}C_{sc}^\infty$, $C_{sc}^\infty$ denoting
  sections with spacelike compact support, so every such solution of
  $Pu=0$ is $Gf$, $f\in C_c^\infty$.

A sub-Riemannian structure is an inner product on a bracket-generating
distribution $\mathcal D\subset TM$. Its distance is the infimum of
lengths of curves tangent to $\mathcal D$.

* **87. Rashevskii–Chow theorem.** On a connected bracket-generating
  sub-Riemannian manifold, every two points are joined by a horizontal
  curve. The resulting finite distance induces the manifold topology.
* **88. Pontryagin principle.** A length minimizer, parametrized at
  constant speed, has a nontrivial covector lift satisfying the
  Hamiltonian necessary conditions. Normal extremals follow
  $H(q,p)=\tfrac12\sum_i\langle p,X_i(q)\rangle^2$;
  abnormal extremals require the separate zero-cost multiplier case.
* **89. Ball–box theorem.** In privileged coordinates at an
  equiregular point with weights $w_i$, a sufficiently small metric
  ball is trapped between coordinate boxes $|x_i|\leq c r^{w_i}$
  with two fixed positive constants $c$. Thus its volume is comparable
  to $r^Q$, $Q=\sum_iw_i$.
* **90. Nilpotent tangent geometry.** At an equiregular point, the
  rescaled sub-Riemannian spaces converge to the graded nilpotent
  approximation, a Carnot group. Its homogeneous dimension $Q$ is
  the local Hausdorff dimension, generally exceeding the manifold dimension.

## Reference guide

Jost, Chavel, Petersen, Cheeger–Ebin, and Schoen–Yau share the curvature,
comparison, Bochner, and variational foundations. Li and Grigor'yan develop
harmonic functions and heat kernels on complete manifolds. Aubin, Hebey,
Struwe, and Druet–Hebey–Robert supply the Sobolev and critical-equation
theory. The harmonic-map treatments of Jost, Lin–Wang, and Hélein overlap
on variational structure, regularity, and concentration. Colding–Minicozzi,
Osserman, Lawson, and the Plateau references develop the minimal-surface
branch; minimizing-current regularity is treated further in Section 37.

Topping, Andrews–Hopper, Chow–Lu–Ni, and the multi-volume Ricci-flow
treatise share evolution, maximum principles, compactness, and entropy.
Brendle and Morgan–Tian carry these methods to sphere and geometrization
theorems. Ecker, Mantegazza, and Andrews–Chow–Guenther–Langford supply
the extrinsic flow branch. McDuff–Salamon and Audin–Damian develop
holomorphic curves and Floer analysis; Wehrheim and Rudolph–Schmidt
develop gauge theory, and Kronheimer–Mrowka the Seiberg–Witten equations.
Bär–Ginoux–Pfäffle treat wave equations on globally hyperbolic manifolds. Agrachev–Barilari–Boscain and the Heisenberg-group
text supply sub-Riemannian geometry. Dan Lee's *Geometric Relativity*
places the positive mass theorem in the common variational and curvature
framework. These branches are represented by their overlapping analytic
principles rather than the union of their specialized classification theories.

Local full-text sources consulted:

* [Jost, *Riemannian Geometry and Geometric Analysis*, seventh edition](References/Jost2017RiemannianGeometryGeometricAnalysis7thEd-SpringerUTX.pdf).
* [Chavel, *Riemannian Geometry: A Modern Introduction*, second edition](References/Chavel2006RiemannianGeometryModernIntroduction2ndEd-CambridgeStudiesAM98.pdf).
* [Petersen, *Riemannian Geometry*, third edition](References/Petersen2016RiemannianGeometry3rdEd-SpringerGTM.pdf).
* [Struwe, *Variational Methods*, fourth edition](References/Struwe2008VariationalMethodsApplicationsNonlinearPartialDifferentialEquationsHamiltonianSystems4thEd-SpringerErgebMath3.pdf).
* [Agrachev–Barilari–Boscain, *A Comprehensive Introduction to Sub-Riemannian Geometry*](References/AgrachevBarilariBoscain2020SubRiemannianGeometry-Cambridge.StudAM181.pdf).
* [Rudolph–Schmidt, *Differential Geometry and Mathematical Physics*, II](References/RudolphSchmidt2017DifferentialGeometryMathematicalPhysics2FibreBundlesTopologyGaugeFields-SpringerTMP.pdf).
* [Huybrechts, *Complex Geometry*](References/Huybrechts2005ComplexGeometryIntroduction-SpringerUTX.pdf), for the Kähler continuation shared with Section 45.

The linked Topping notes are the March 2006 author version; Mantegazza's
linked course notes supplement his monograph's flow material. Grigor'yan's
accessible lectures and the Li–Yau and Perelman papers were used for the
specific complete-manifold and entropy statements cited above. Wehrheim's
linked copy contains the introduction and theorem statements, not the
full proofs of the book. These sources are distinguished from full-text
consultation of the corresponding monographs.
