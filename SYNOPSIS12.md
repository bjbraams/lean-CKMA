# Synopsis: Convexity, convex analysis, and variational analysis

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis follows the overlapping core of Section 12 of
[CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md): convex geometry,
conjugate duality, subdifferentials, monotone operators, variational convergence,
and the convergence principles behind first-order methods. Finite-dimensional
statements are distinguished from the Hilbert and Banach formulations where
compactness, continuity qualifications, and weak convergence matter.

A convex function $f:E\to(-\infty,\infty]$ is **proper** if it never takes
$-\infty$ and is finite somewhere. Its **effective domain** is $\operatorname{dom}f$;
it is **lower semicontinuous** when its epigraph is closed. The conjugate is
$f^*(u)=\sup_x(\langle u,x\rangle-f(x))$, with $u$ in the continuous dual.
The **subdifferential** is
$\partial f(x)=\{u:f(y)\geq f(x)+\langle u,y-x\rangle\ \forall y\}$ at
points of finite value, and is empty elsewhere. Unless specified otherwise,
geometric statements are in $\mathbb R^n$.

## Separation and convex geometry

The **convex hull** is the set of finite convex combinations. A point of a
convex set is **extreme** if it lies in no nontrivial open segment of the set.
A **convex body** is a compact convex set with nonempty interior. Relative
interior means interior in the affine hull; it is often the correct
finite-dimensional qualification when ordinary interior is empty.

* **1. Separation.** A point outside a nonempty closed convex set can be
  strictly separated from it by a continuous linear functional. A compact
  convex set and a disjoint closed convex set can be strictly separated.
  These formulations also hold in Hausdorff locally convex spaces.
* **2. Supporting hyperplanes.** Every boundary point of a finite-dimensional
  convex body has a supporting hyperplane. More generally, the same conclusion
  holds for a convex set with nonempty interior at a boundary point belonging
  to its closure.
* **3. Carathéodory's theorem.** Every point of a convex hull in $\mathbb R^n$
  is a convex combination of at most $n+1$ points of the original set. The
  dimension can be replaced by that of its affine hull.
* **4. Radon's theorem.** Any $n+2$ points in $\mathbb R^n$ can be partitioned
  into two nonempty groups with intersecting convex hulls.
* **5. Helly's theorem.** For a finite family of convex sets in $\mathbb R^n$,
  if every subfamily of at most $n+1$ has nonempty intersection, the entire
  family does. An infinite-family version requires compactness hypotheses.
* **6. Finite-dimensional extreme-point representation.** A nonempty compact
  convex set is the convex hull of its extreme points; each point is a convex
  combination of at most $n+1$ of them.
* **7. Krein–Milman theorem.** A nonempty compact convex subset of a Hausdorff
  locally convex space is the closed convex hull of its extreme points.
  Closure cannot generally be omitted in infinite dimensions.
* **8. Choquet representation.** In a compact metrizable convex subset of a
  locally convex space, every point is the barycenter of a probability carried
  by the extreme points. Barycenter means equality after evaluation by every
  continuous affine function.
* **9. Choquet simplex.** For a compact metrizable convex set, uniqueness of
  these extreme-point representing probabilities characterizes a Choquet
  simplex. Thus integral representation can be unique even when the set is
  infinite-dimensional; it is not unique for general compact convex sets.
* **10. John's ellipsoid theorem.** Every convex body has a unique
  maximum-volume inscribed ellipsoid $\mathcal E$. Centering dilations at its
  center, $\mathcal E\subseteq K\subseteq n\mathcal E$. For centrally
  symmetric $K$, the outer factor improves to $\sqrt n$.

## Convex functions, derivatives, and conjugacy

The one-sided **directional derivative** is
$f'(x;d)=\lim_{t\downarrow0}(f(x+td)-f(x))/t$ when interpreted in the extended
sense. The **indicator** $\delta_C$ is zero on $C$ and infinity outside;
the **support function** is $h_C(u)=\sup_{x\in C}\langle u,x\rangle$.

* **11. Continuity on the interior.** A proper convex function in finite
  dimensions is locally Lipschitz on the interior of its domain. On a Banach
  space, a convex function bounded above on a neighborhood is continuous and
  locally Lipschitz there; finiteness alone is not an adequate substitute in
  arbitrary infinite-dimensional settings.
* **12. Existence of subgradients.** A proper convex function has a nonempty
  subdifferential at every point in the relative interior of its domain in
  finite dimensions. For a continuous convex function on an open Banach-space
  domain, continuous supporting subgradients exist at every point.
* **13. Directional derivative and subgradients.** At an interior point of a
  finite-dimensional convex domain,
  $f'(x;d)=\max_{u\in\partial f(x)}\langle u,d\rangle$.
  The directional derivative is sublinear in $d$ and determines the subdifferential.
* **14. Differentiability criterion.** A finite convex function on an open
  subset of $\mathbb R^n$ is differentiable at $x$ exactly when
  $\partial f(x)$ is a singleton. Its gradient is continuous at points of
  differentiability relative to sequences of differentiability points.
* **15. Alexandrov's theorem.** A finite convex function on an open convex
  subset of $\mathbb R^n$ has a second-order Taylor expansion at almost every
  point. Its almost-everywhere Hessian is positive semidefinite.
* **16. Fenchel–Young inequality.**
  $f(x)+f^*(u)\geq\langle u,x\rangle$, with equality exactly when
  $u\in\partial f(x)$.
* **17. Fenchel–Moreau theorem.** A proper lower semicontinuous convex
  function on a Hausdorff locally convex space equals its biconjugate.
  It is therefore the supremum of its continuous affine minorants.
* **18. Inverse subdifferentials.** For such $f$,
  $u\in\partial f(x)$ exactly when $x\in\partial f^*(u)$, using the
  canonical embedding in the bidual when necessary.
* **19. Subdifferential sum rule.** For proper lower semicontinuous convex
  functions on a Banach space, if one is continuous at a point of their common
  domain, then $\partial(f+g)(x)=\partial f(x)+\partial g(x)$.
  In finite dimensions, intersecting relative interiors is a standard
  alternative qualification.
* **20. Linear chain rule.** For bounded linear $A:E\to F$, if $g$ is proper
  lower semicontinuous convex and continuous at some $Ax_0$, then
  $\partial(g\circ A)(x)=A^*\partial g(Ax)$. Without a qualification one
  generally retains only the inclusion from right to left.
* **21. Infimal convolution.** For proper convex $f,g$, if
  $(f\mathbin\square g)(x)=\inf_y(f(y)+g(x-y))$ is proper, then it is convex
  and $(f\mathbin\square g)^*=f^*+g^*$. Lower semicontinuity and attainment
  of the infimum require additional hypotheses.
* **22. Support and indicator duality.** $\delta_C^*=h_C$ and, for nonempty
  $C$, $h_C^*=\delta_{\overline{\operatorname{conv}}C}$.
* **23. Bipolar theorem.** For $C^\circ=\{u:\langle u,x\rangle\leq1\ \forall x\in C\}$,
  $C^{\circ\circ}=\overline{\operatorname{conv}}(C\cup\{0\})$ in finite
  dimensions, and with the corresponding weak topology in dual-pair formulations.
* **24. Recession and bounded sublevels.** For proper closed convex $f$ in
  finite dimensions, its recession function satisfies
  $$f^\infty(d)=\lim_{t\to\infty}\frac{f(x+td)-f(x)}t
    =\sup_{u\in\operatorname{dom}f^*}\langle u,d\rangle,$$
  independently of $x\in\operatorname{dom}f$. All sublevel sets are bounded
  exactly when $f^\infty(d)>0$ for every $d\ne0$.

## Minimizers, projections, and monotone operators

Here $H$ is a real Hilbert space. The **normal cone** to a closed convex $C$
is $N_C(x)=\{u:\langle u,y-x\rangle\leq0\ \forall y\in C\}$ for $x\in C$.
An operator $A:H\rightrightarrows H$ is **monotone** if
$\langle x-y,u-v\rangle\geq0$ on its graph; it is **maximal monotone** if
its graph has no proper monotone enlargement. Its resolvent is
$J_{\gamma A}=(I+\gamma A)^{-1}$.

* **25. Fermat rule.** For convex $f$, $x$ is a global minimizer exactly when
  $0\in\partial f(x)$. Minimization over $C$ is minimization of $f+\delta_C$;
  a sum-rule qualification is needed to replace its subdifferential by
  $\partial f+N_C$.
* **26. Direct method for convex functions.** On a reflexive Banach space,
  a proper norm-lower-semicontinuous convex coercive function attains its minimum.
  Convex norm-closed sublevel sets are weakly closed, and bounded ones are
  weakly compact.
* **27. Strong convexity.** If $f-\frac\mu2\|\cdot\|^2$ is convex,
  $\mu>0$, a minimizer is unique and
  $f(x)-f(x_*)\geq\frac\mu2\|x-x_*\|^2$. Its subdifferential is
  $\mu$-strongly monotone.
* **28. Hilbert projection theorem.** Every nonempty closed convex $C$
  has a unique nearest-point map $P_C$, characterized by
  $\langle x-P_Cx,y-P_Cx\rangle\leq0$ for $y\in C$.
  It is firmly nonexpansive:
  $\|P_Cx-P_Cy\|^2\leq\langle P_Cx-P_Cy,x-y\rangle$.
* **29. Normal-cone resolvent.** $J_{\gamma N_C}=P_C$ for $\gamma>0$;
  equivalently, $u\in N_C(x)$ exactly when $P_C(x+\gamma u)=x$.
* **30. Proximal mapping.** For proper lower semicontinuous convex $f$,
  $$\operatorname{prox}_{\gamma f}(x)=
    \operatorname*{argmin}_y\left(f(y)+\frac{\|x-y\|^2}{2\gamma}\right)$$
  exists uniquely and equals $J_{\gamma\partial f}x$. It is firmly nonexpansive.
* **31. Moreau envelope.** The infimum in result 30 defines a finite convex
  differentiable function $e_\gamma f$, with
  $\nabla e_\gamma f(x)=\gamma^{-1}(x-\operatorname{prox}_{\gamma f}x)$
  and gradient Lipschitz constant $1/\gamma$.
* **32. Moreau decomposition.**
  $\operatorname{prox}_{\gamma f}(x)+
  \gamma\operatorname{prox}_{f^*/\gamma}(x/\gamma)=x$.
  For indicators of closed convex cones, this becomes orthogonal decomposition
  into the cone and its polar.
* **33. Minty's theorem.** A monotone operator is maximal monotone exactly
  when $I+\gamma A$ is onto $H$ for some, equivalently every, $\gamma>0$.
* **34. Maximality of subdifferentials.** The subdifferential of every proper
  lower semicontinuous convex function on $H$ is maximal monotone.
* **35. Resolvent characterization.** Resolvents of maximal monotone
  operators are precisely the everywhere-defined firmly nonexpansive mappings.
  Given such a map $T$, the associated relation is $T^{-1}-I$.
* **36. Baillon–Haddad theorem.** If a convex differentiable function has
  $L$-Lipschitz gradient, $L>0$, then
  $$\langle\nabla f(x)-\nabla f(y),x-y\rangle
    \geq L^{-1}\|\nabla f(x)-\nabla f(y)\|^2.$$

## Duality and optimality conditions

* **37. Fenchel–Rockafellar duality.** For proper closed convex $f,g$ on
  Banach spaces and bounded linear $A$, assume $f(x_0)<\infty$ and $g$ is
  continuous at $Ax_0$. If the primal value is finite, then
  $$\inf_x\{f(x)+g(Ax)\}
    =\max_u\{-f^*(-A^*u)-g^*(u)\}.$$
  Dual attainment is asserted; primal attainment is a separate question.
* **38. Slater and KKT conditions.** For finite convex functions in
  $\mathbb R^n$, constraints $g_i\leq0$, and affine equalities $Ax=b$, a
  strictly feasible point implies that every minimizer has multipliers
  $\lambda_i\geq0,y$ with
  $$0\in\partial f(x_*)+\sum_i\lambda_i\partial g_i(x_*)+A^*y,
    \qquad\lambda_ig_i(x_*)=0.$$
  These conditions are sufficient for optimality even without strict feasibility.
* **39. Farkas alternative.** Exactly one of the following is possible:
  $Ax=b$ with $x\geq0$; or $A^*y\geq0$ with $\langle b,y\rangle<0$.
* **40. Linear-programming strong duality.** A feasible finite-dimensional
  linear program with finite optimum and its standard dual have equal values,
  both attained. Complementary slackness characterizes optimal primal–dual pairs.
* **41. Conic duality.** For a closed convex cone $K$ with nonempty interior,
  the program $\inf\{\langle c,x\rangle:Ax=b,x\in K\}$ has dual
  $\sup\{\langle b,y\rangle:c-A^*y\in K^*\}$.
  Primal strict feasibility and finite primal value imply equality and dual
  attainment. Strict dual feasibility gives the corresponding primal conclusion.
* **42. Convex minimax theorem.** If $X$ is compact convex, $Y$ convex, and
  $F$ is continuous, convex in $x$, and concave in $y$, then
  $\inf_{x\in X}\sup_{y\in Y}F(x,y)=\sup_{y\in Y}\inf_{x\in X}F(x,y)$.
  Semicontinuous quasiconvex–quasiconcave versions are provided by Sion's theorem.

## Variational convergence, nonsmooth calculus, and regularity

**Epi-convergence** $f_n\to f$ means the lower bound
$f(x)\leq\liminf f_n(x_n)$ for every $x_n\to x$, together with a recovery
sequence at each $x$ giving the reverse upper bound. **Mosco convergence** on
a Hilbert space uses weakly convergent sequences for the lower bound and
strongly convergent recovery sequences. For a locally Lipschitz function,
$f^\circ(x;d)=\limsup_{y\to x,t\downarrow0}(f(y+td)-f(y))/t$ and
$\partial_Cf(x)=\{u:\langle u,d\rangle\leq f^\circ(x;d)\ \forall d\}$.

* **43. Ekeland variational principle.** On a complete metric space, let $f$
  be proper lower semicontinuous and bounded below. If
  $f(x_0)\leq\inf f+\varepsilon$, then for every $\lambda>0$ some $x_\varepsilon$
  has $d(x_\varepsilon,x_0)\leq\lambda$, $f(x_\varepsilon)\leq f(x_0)$, and
  $f(y)>f(x_\varepsilon)-(\varepsilon/\lambda)d(y,x_\varepsilon)$ for $y\ne x_\varepsilon$.
* **44. Berge maximum theorem.** A continuous objective over a nonempty
  compact-valued continuous feasible correspondence has continuous optimal
  value and an upper semicontinuous compact-valued optimizer correspondence.
  This formulation concerns continuous parameterized feasible sets, not arbitrary
  pointwise convergence of constraints.
* **45. Fundamental theorem of epi-convergence.** For proper closed functions
  on $\mathbb R^n$, epi-convergence to a proper function and equicoercivity
  imply convergence of minimum values. Approximate minimizers have convergent
  subsequences, and every such limit minimizes the limit function.
* **46. Attouch convergence principle.** Mosco convergence of proper closed
  convex functions on $H$ implies pointwise strong convergence of their
  proximal mappings and convergence of their Moreau envelopes. Resolvent
  convergence alone loses additive constants and does not determine function values.
* **47. Convex-set convergence and projection.** Nonempty closed convex sets
  converge in the Mosco sense exactly when their projections converge strongly
  at every point. In finite dimensions this is the usual inner-and-outer
  Painlevé–Kuratowski convergence of sets.
* **48. Clarke gradient representation.** In finite dimensions, $\partial_Cf(x)$
  is nonempty compact convex and equals the closed convex hull of limits of
  ordinary gradients at differentiability points tending to $x$.
  Its support function is $f^\circ(x;\cdot)$.
* **49. Nonsmooth Fermat rule.** A local minimizer of a locally Lipschitz
  function satisfies $0\in\partial_Cf(x)$. This is necessary, rather than
  sufficient, outside convexity.
* **50. Clarke chain rule.** For $F$ of class $C^1$ and locally Lipschitz $g$,
  $\partial_C(g\circ F)(x)\subseteq DF(x)^*\partial_Cg(F(x))$.
  The convex sum and chain equalities do not extend unchanged to arbitrary
  locally Lipschitz functions.
* **51. Generic differentiability of convex functions.** On a separable
  Banach space, a continuous convex function on an open convex set is Gâteaux
  differentiable on a dense $G_\delta$. On an Asplund space, the corresponding
  generic conclusion is Fréchet differentiability.
  A Banach space is Asplund when every separable subspace has separable dual;
  Hilbert spaces and reflexive Banach spaces are standard examples.
* **52. Lyusternik–Graves theorem.** If a $C^1$ map between Banach spaces has
  surjective derivative at $x_0$, then locally
  $\operatorname{dist}(x,F^{-1}(y))\leq C\|F(x)-y\|$ for $x$ near $x_0$
  and $y$ near $F(x_0)$. Surjectivity gives metric regularity even when a
  single-valued inverse is unavailable.
* **53. Hoffman's error bound.** For a nonempty polyhedron
  $C=\{x:Ax\leq b,Ex=d\}$, there is $\kappa<\infty$ such that
  $\operatorname{dist}(x,C)\leq\kappa(\|(Ax-b)_+\|+\|Ex-d\|)$ for all $x$.

## Basic convergence theorems for convex algorithms

* **54. Proximal point method.** If $\operatorname{argmin}f\ne\varnothing$
  and $\gamma>0$, $x_{n+1}=\operatorname{prox}_{\gamma f}(x_n)$ converges
  weakly in $H$ to a minimizer, with
  $f(x_n)-\min f\leq\|x_0-x_*\|^2/(2\gamma n)$ for $n\geq1$.
* **55. Projected gradient.** For convex $f$ with $L$-Lipschitz gradient and
  nonempty minimizer set on closed convex $C$, the iteration
  $x_{n+1}=P_C(x_n-\gamma\nabla f(x_n))$ converges weakly for $0<\gamma<2/L$.
  For $\gamma\leq1/L$ and $x_0\in C$, objective errors are $O(1/n)$.
* **56. Forward–backward splitting.** For convex $L$-smooth $f$ and proper
  closed convex $g$, assume $\operatorname{argmin}(f+g)\ne\varnothing$.
  The iteration $x_{n+1}=\operatorname{prox}_{\gamma g}
  (x_n-\gamma\nabla f(x_n))$ converges weakly to a minimizer for
  $0<\gamma<2/L$, with the standard $O(1/n)$ objective bound for $\gamma\leq1/L$.
* **57. Accelerated gradient bound.** For a convex $L$-smooth function on
  $\mathbb R^n$, set $t_0=1$, $y_0=x_0$ and
  $$x_{k+1}=y_k-L^{-1}\nabla f(y_k),\quad
    t_{k+1}=\frac{1+\sqrt{1+4t_k^2}}2,\quad
    y_{k+1}=x_{k+1}+\frac{t_k-1}{t_{k+1}}(x_{k+1}-x_k).$$
  If a minimizer $x_*$ exists,
  $f(x_k)-f(x_*)\leq2L\|x_0-x_*\|^2/(k+1)^2$ for $k\geq1$.
* **58. Subgradient complexity bound.** For a convex globally $G$-Lipschitz
  function, projected subgradient steps on $C$ with
  $x_0\in C$, $\|x_0-x_*\|\leq R$, $G,R>0$, and constant step
  $R/(G\sqrt N)$ give a best-iterate,
  and an averaged-iterate, objective gap at most $RG/\sqrt N$ after $N$ steps.
* **59. Alternating projections.** For closed convex $C,D\subset H$ with
  nonempty intersection, $(P_CP_D)^nx_0$ converges weakly to a point of the
  intersection. For closed subspaces it converges strongly to
  $P_{C\cap D}x_0$; the nearest-point conclusion is special to that setting.
* **60. Douglas–Rachford splitting.** In finite dimensions, for proper closed
  convex $f,g$ with $\operatorname{zer}(\partial f+\partial g)\ne\varnothing$,
  $$z_{n+1}=z_n+\operatorname{prox}_{\gamma f}
     (2\operatorname{prox}_{\gamma g}z_n-z_n)
       -\operatorname{prox}_{\gamma g}z_n$$
  converges to a fixed point, and $\operatorname{prox}_{\gamma g}z_n$ converges
  to a minimizer of $f+g$. The zero-set assumption supplies the dual compatibility
  that mere primal attainment would not guarantee.

## Further conjugacy and subgradient structure

An **$\varepsilon$-subgradient** replaces the supporting inequality by
$f(y)\geq f(x)+\langle u,y-x\rangle-\varepsilon$; it allows a controlled
global error. A relation is **cyclically monotone** if every finite cycle in
its graph satisfies
$\sum_i\langle u_i,x_{i+1}-x_i\rangle\leq0$, with $x_{m+1}=x_1$.
Ordinary monotonicity is the two-point case. These notions explain both
approximate optimality and the additional integrability property that makes
a monotone relation the derivative of a convex potential.

* **61. Strong convexity and smooth conjugacy.** For proper closed convex
  functions on $H$, $\mu$-strong convexity of $f$, $\mu>0$, is equivalent to
  $f^*$ being everywhere Fréchet differentiable with $1/\mu$-Lipschitz gradient.
  In particular, strong convexity turns the inverse subdifferential into the
  single-valued map $\nabla f^*$. Dually, an everywhere differentiable
  $L$-smooth closed convex function has $1/L$-strongly convex conjugate.
* **62. Closed perspectives.** For proper closed convex $f$ on $\mathbb R^n$,
  its perspective $p(x,t)=tf(x/t)$, $t>0$, is convex. Its closed extension has
  $p(x,0)=f^\infty(x)$ and value infinity for $t<0$. This identifies the
  recession boundary of a conic formulation and is essential when an auxiliary
  scale tends to zero.
* **63. Tangent and intersection rules.** For closed convex $C$ and $x\in C$,
  the tangent cone is $T_C(x)=\overline{\operatorname{cone}(C-x)}$ and
  $N_C(x)=T_C(x)^\circ$, using the nonpositive polar convention for cones.
  If $\operatorname{ri}C\cap\operatorname{ri}D\ne\varnothing$ in finite
  dimensions, $N_{C\cap D}(x)=N_C(x)+N_D(x)$. The relative-interior hypothesis
  prevents the loss of normal directions that occurs at incompatible intersections.
* **64. Danskin's maximum rule.** Let $K$ be compact and $\phi(x,t)$ be convex
  and $C^1$ in $x\in\mathbb R^n$, with $\phi$ and $\nabla_x\phi$ jointly
  continuous. Then for $f(x)=\max_{t\in K}\phi(x,t)$,
  $$\partial f(x)=\operatorname{conv}\{
     \nabla_x\phi(x,t):\phi(x,t)=f(x)\}.$$
  A unique maximizing gradient gives ordinary differentiability, even if there
  are several active indices producing that same gradient.
* **65. Brøndsted–Rockafellar approximation.** For a proper closed convex
  function on a Banach space, $u\in\partial_\varepsilon f(x)$ and
  $\lambda>0$ admit an exact subgradient $u_\lambda\in\partial f(x_\lambda)$
  with
  $\|x_\lambda-x\|\leq\lambda$ and
  $\|u_\lambda-u\|\leq\varepsilon/\lambda$.
  Thus approximate supporting hyperplanes can be approximated simultaneously
  in base point and slope by genuine ones.
* **66. Rockafellar's cyclic-monotonicity theorem.** Maximally cyclically
  monotone relations on a Hilbert space are exactly subdifferentials of proper
  lower semicontinuous convex functions. General maximal monotone operators
  need not have a convex potential. Cyclic monotonicity is therefore the
  additional condition distinguishing convex minimization from general
  monotone inclusions.

## Reference guide

Rockafellar, Hiriart-Urruty–Lemaréchal, and Borwein–Lewis give overlapping
finite-dimensional developments of separation, conjugacy, subgradients, and
duality. Bauschke–Combettes, Chapters 12–20 and the splitting chapters, provides
the Hilbert-space proximal and monotone-operator framework. Rockafellar–Wets
develops epigraphical limits, normal cones, and variational stability; Clarke,
Penot, Borwein–Zhu, and Dontchev–Rockafellar develop the nonsmooth and
metric-regularity endpoint.

The compact-convex representation material is treated by Simon and Phelps;
the geometric theorems by Webster, Hug–Weil, Gruber, and Barvinok. Boyd–Vandenberghe
and Borwein–Lewis connect duality to linear and conic optimization. The final
algorithmic results recur in Bauschke–Combettes, Beck, Nesterov, and Peypouquet;
their inclusion records mathematical convergence principles, rather than an
inventory of optimization implementations.

Local source anchors:

- [Borwein–Lewis, *Convex Analysis and Nonlinear Optimization*](References/BorweinLewis2006ConvexAnalysisNonlinearOptimizationTheoryExamples2ndEd-SpringerCMSBM.pdf).
- [Bauschke–Combettes, *Convex Analysis and Monotone Operator Theory*](References/BauschkeCombettes2017ConvexAnalysisMonotoneOperatorTheoryHilbertSpace2ndEd-SpringerCMSBM.pdf).
- [Rockafellar–Wets, *Variational Analysis*](References/RockafellarWets1998VariationalAnalysis-SpringerGL317.pdf).
- [Hiriart-Urruty–Lemaréchal, volume I](References/HiriartUrrutyLemaréchal1993ConvexAnalysisMinimizationAlgorithms1Fundamentals-SpringerGL305.pdf).
- [Simon, *Convexity: An Analytic Viewpoint*](References/Simon2011ConvexityAnalyticViewpoint-Cambridge.TractsMath187.pdf).
- [Boyd–Vandenberghe, *Convex Optimization*](References/BoydVandenberghe2004ConvexOptimization-CambridgeUP.pdf).
- [Nesterov, *Lectures on Convex Optimization*](References/Nesterov2018LecturesConvexOptimization2ndEd-SpringerSOIA137.pdf).
