# Synopsis: Calculus of variations, Γ-convergence, and homogenization

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects recurring material from Section 36 of
[CKMA-bib.md](CKMA-bib.md).
It covers classical variations, existence and lower semicontinuity,
quasiconvexity and microstructure, critical-point methods, variational
convergence, and homogenization. BV structure and geometric minimization
are developed further in Section 37. Convex analysis supplies many tools,
but vectorial variational problems require more than convexity.

Unless otherwise stated, $\Omega\subset\mathbb R^d$ is bounded and
Lipschitz, $u:\Omega\to\mathbb R^m$, and $1<p<\infty$.
The model energy is $I(u)=\int_\Omega f(x,u,Du)dx$ on a fixed Sobolev
trace class. Coercivity, growth, and admissibility conditions are part of
the theorem rather than consequences of the notation.

## First and second variations

* **1. Euler–Lagrange equation.** A sufficiently regular local minimizer
  with admissible compactly supported variations satisfies
  $f_u-\operatorname{div}f_{Du}=0$. For Sobolev minimizers this
  holds weakly when derivative growth bounds justify differentiation
  under the integral.
* **2. Natural boundary conditions.** If a smooth minimizer is free on
  a boundary portion and there is no boundary energy, first variation
  gives $f_{Du}\nu=0$ there. Prescribed traces remove those variations.
* **3. Lagrange multipliers.** Under a surjective constraint derivative,
  a constrained extremum satisfies $DI=\lambda\circ DG$.
  Finite-dimensional integral constraints therefore introduce finitely
  many multiplier terms in the Euler–Lagrange equation.
* **4. Nonnegative second variation.** A $C^2$ local minimizer has
  $D^2I(u)[\phi,\phi]\geq0$ for every admissible variation.
  Uniform positive definiteness of the second variation in a norm,
  with a controlled Taylor remainder in that norm, gives a strict local minimum.
* **5. Legendre–Hadamard condition.** For a smooth gradient integrand,
  nonnegative second variation implies
  $D_F^2f(x,u,Du)[a\otimes b,a\otimes b]\geq0$ for all $a,b$.
  Positivity on rank-one directions is weaker than positivity on all matrices.
* **6. Weierstrass necessary condition.** A smooth strong local
  minimizer of a one-dimensional integral has nonnegative excess
  $f(t,u,q)-f(t,u,u')-f_{u'}(t,u,u')\cdot(q-u')$ for every $q$.
  Here strong locality means small uniform perturbations of the path.
* **7. Jacobi condition.** For a regular one-dimensional variational
  problem with positive definite velocity Hessian, a minimizing
  extremal has no conjugate point strictly inside the interval.
  Conversely, an extremal with $f_{u'u'}>0$ along it (strengthened Legendre)
  and no conjugate point in the closed interval is a strict weak local
  minimizer; embedding it in a field of extremals on which the Weierstrass
  excess is nonnegative makes it a strong minimizer (Weierstrass field theory).
* **8. Beltrami identity.** For an autonomous one-dimensional Lagrangian,
  $f-u'\cdot f_{u'}$ is constant along smooth Euler–Lagrange extremals.
* **9. Noether identity.** A differentiable one-parameter symmetry of
  the action gives a conserved quantity along extremals. For a purely
  vertical symmetry $u\mapsto u+\varepsilon v$, invariance implies
  constancy of $f_{u'}\cdot v$.

## The direct method and lower semicontinuity

* **10. Abstract direct method.** A proper sequentially lower
  semicontinuous functional with sequentially compact sublevel sets
  attains its infimum. The topology determining both conditions must
  be fixed in advance.
* **11. Weak Sobolev compactness.** A $p$-coercive bound on $Du$,
  together with fixed trace or a normalization controlling constants,
  bounds minimizing sequences in $W^{1,p}$. Reflexivity gives a
  weakly convergent subsequence with the same trace constraint.
* **12. Convex lower semicontinuity.** Let $f(x,u,F)\geq0$ be
  measurable in $x$, lower semicontinuous in $(u,F)$, and convex in $F$.
  If $u_j\to u$ in $L^1$ and $Du_j\rightharpoonup Du$ in $L^1$, then
  $I(u)\leq\liminf I(u_j)$ (De Giorgi, Ioffe); no growth condition is
  needed. Adding a continuous linear load preserves this property.
* **13. Existence for convex energies.** Coercivity, the preceding
  lower semicontinuity, and a nonempty finite-energy trace class give
  a minimizer. Strict convexity in the gradient gives uniqueness
  after boundary values or constants are fixed.
* **14. Strong convergence from uniform convexity.** If the gradient
  energy controls a uniformly convex $L^p$ norm, weak convergence
  together with convergence of that energy implies strong convergence
  of gradients. This upgrades compactness when no oscillation energy is lost.
* **15. Regularity of minimizers.** In the scalar case $m=1$, if
  $f\in C^\infty$ has $\lambda I\leq D^2f\leq\Lambda I$, minimizers of
  $\int f(Du)$ in $W^{1,2}$ are $C^\infty$: derivatives of $u$ solve
  linear equations with bounded measurable elliptic coefficients, so
  De Giorgi–Nash–Moser gives $C^{1,\alpha}$ and Schauder theory
  bootstraps (Hilbert's nineteenth problem). For systems this fails:
  minimizers of quadratic energies with bounded measurable coefficients
  can be unbounded when $d=m\geq3$ (De Giorgi), and smooth uniformly
  convex integrands can have singular minimizers (Šverák–Yan). Minimizers
  of smooth uniformly strictly quasiconvex integrands with $p$-growth
  are $C^{1,\alpha}$ off a closed null set (Evans; Acerbi–Fusco).

## Quasiconvexity, minors, and relaxation

A finite continuous $f:\mathbb R^{m\times d}\to\mathbb R$ is
**quasiconvex** if
$f(F)\leq\fint_Qf(F+D\phi)$ for $\phi\in W_0^{1,\infty}(Q;\mathbb R^m)$.
It is **rank-one convex** if it is convex on every rank-one line, and
**polyconvex** if it is a convex function of all minors of $F$.

* **16. Convexity hierarchy.** Convexity implies polyconvexity,
  polyconvexity implies quasiconvexity, and quasiconvexity implies
  rank-one convexity. If $m=1$ or $d=1$ all four notions coincide.
  Otherwise polyconvex functions need not be convex, quasiconvex
  functions need not be polyconvex, and for $m\geq3$, $d\geq2$
  rank-one convexity does not imply quasiconvexity (Šverák); the case
  $m=2$ is open.
* **17. Morrey's characterization.** For continuous nonnegative
  $f(F)$ with $p$-growth, $\int f(Du)$ is sequentially weakly
  lower semicontinuous on $W^{1,p}$ exactly when $f$ is quasiconvex
  (Morrey; Acerbi–Fusco, also for $f(x,u,F)$ Carathéodory).
* **18. Null Lagrangians.** Every minor of $Du$ has an integral
  determined by the boundary trace whenever integrability permits.
  Affine combinations of minors are null Lagrangians, with identically
  vanishing interior Euler–Lagrange variation.
* **19. Weak continuity of minors.** If $u_j\rightharpoonup u$ in
  $W^{1,p}$ and $p>k$, the $k$th-order minors converge weakly in
  $L^{p/k}$ to the corresponding minors of $Du$.
  At critical integrability, concentration requires separate treatment.
* **20. Polyconvex existence theorem.** Let $p>\min(m,d)$ and
  $f(F)=g(\text{all minors of }F)$, where $g$ is convex,
  lower semicontinuous, and nonnegative. If $f$ is $p$-coercive,
  a nonempty finite-energy fixed-trace class has a minimizer.
  The conclusion allows extended-valued determinant constraints.
* **21. Quasiconvex relaxation.** For continuous $f$ with
  $0\leq f(F)\leq C(1+|F|^p)$, the weak $W^{1,p}$ lower semicontinuous
  envelope of $\int f(Du)$ is $\int Qf(Du)$, where
  $Qf(F)=\inf_{\phi\in W_0^{1,\infty}(Q)}\fint_Qf(F+D\phi)$.
* **22. Scalar relaxation.** In the scalar case $Qf=f^{**}$, the
  lower convex envelope. Fine oscillations can lower the effective
  energy to this envelope even when no original minimizer exists.
* **23. Rank-one laminates.** If $F_1-F_2=a\otimes b$, alternating
  layers construct gradients with barycenter
  $\theta F_1+(1-\theta)F_2$ and limiting energy
  $\theta f(F_1)+(1-\theta)f(F_2)$. This explains the necessity
  of rank-one convexity for weak lower semicontinuity.
* **24. Geometric rigidity.** On a bounded connected Lipschitz domain
  in $\mathbb R^d$, every $u\in W^{1,2}(\Omega;\mathbb R^d)$
  has a rotation $R\in SO(d)$ with
  $\|Du-R\|_2\leq C\|\operatorname{dist}(Du,SO(d))\|_2$.
  Small elastic strain is close to one rigid rotation.

## Young measures and concentration

A **Young measure** is a weakly measurable field of probability measures
$\nu_x$ recording limiting distributions of oscillating values.

* **25. Fundamental Young-measure compactness.** A bounded sequence
  in $L^p$, $p>1$, has a subsequence generating $\nu_x$.
  For continuous test integrands whose compositions are uniformly
  integrable, their integrals converge to $\int\langle\nu_x,f(x,\cdot)\rangle dx$.
* **26. Barycenter and collapse.** If $v_j\rightharpoonup v$ in $L^p$,
  its Young measure has barycenter $v$. The measure is $\delta_v$
  exactly when the generating sequence converges in measure; adding
  $p$-equiintegrability gives strong $L^p$ convergence.
* **27. Gradient Young-measure Jensen inequality.** A $p$-integrable
  gradient Young measure with barycenter $Du$ satisfies
  $f(Du(x))\leq\langle\nu_x,f\rangle$ for every continuous
  quasiconvex $f$ with $p$-growth. Together with the barycenter and
  moment conditions, these inequalities characterize gradient Young measures.
* **28. Concentration cannot be discarded.** Ordinary Young measures
  describe bounded continuous tests and equiintegrable nonlinear
  quantities. They need not record the limit of a $p$th-power energy
  along merely $L^p$-bounded sequences; generalized Young measures
  add a concentration measure and its direction distribution.
* **29. Div–curl lemma.** If $a_j\rightharpoonup a$ in $L^p$,
  $b_j\rightharpoonup b$ in $L^{p'}$, their divergences and curls
  are locally precompact in the matching negative Sobolev spaces,
  then $a_j\cdot b_j\to a\cdot b$ distributionally.
* **30. Brezis–Lieb splitting.** If $u_j\to u$ almost everywhere
  and $(u_j)$ is bounded in $L^p$, $1<p<\infty$, then
  $\|u_j\|_p^p-\|u_j-u\|_p^p\to\|u\|_p^p$.
* **31. Concentration–compactness vanishing lemma.** A bounded
  $H^1(\mathbb R^d)$ sequence with
  $\sup_y\int_{B_1(y)}|u_j|^2\to0$ converges strongly to zero
  in $L^q$ for $2<q<2^*$, with $2^*=2d/(d-2)$ for $d\geq3$
  and $2^*=\infty$ otherwise.
* **32. Compactness alternatives.** A tightness analysis for probability
  densities yields, after subsequences, compactness up to translation,
  vanishing, or dichotomy. Strict subadditivity of the constrained
  minimum rules out dichotomy in many translation-invariant minimization problems.

## Critical points and minimax methods

For $I\in C^1(X,\mathbb R)$, the **Palais–Smale condition at $c$**
means every sequence with $I(u_j)\to c$ and $DI(u_j)\to0$ has a strongly
convergent subsequence.

* **33. Ekeland's variational principle.** Let $I$ be lower
  semicontinuous, bounded below, and proper on a complete metric space.
  If $I(u_0)\leq\inf I+\varepsilon$ and $\lambda>0$, there is $u$ with
  $I(u)\leq I(u_0)$, $d(u,u_0)\leq\lambda$, and
  $I(v)>I(u)-(\varepsilon/\lambda)d(u,v)$ for every $v\ne u$.
  For differentiable functionals this produces minimizing Palais–Smale sequences.
* **34. Deformation lemma.** If a $C^1$ functional satisfies compactness
  near an energy interval and has no critical point there, a
  continuous descending deformation carries the upper sublevel below
  the lower one while fixing points outside a slightly larger interval.
* **35. Mountain-pass theorem.** If $I(0)=0$, $I\geq\alpha>0$
  on $\|u\|=r$, and $I(e)<0$ for some $\|e\|>r$, then
  $c=\inf_{\gamma(0)=0,\gamma(1)=e}\max_tI(\gamma(t))\geq\alpha$
  is a critical value when Palais–Smale holds at $c$.
* **36. Linking theorem.** A minimax family whose members must
  intersect a set on which $I\geq\alpha$, while its fixed boundary
  has energy below $\alpha$, gives a critical value at least $\alpha$
  under the corresponding Palais–Smale condition. Finite-dimensional
  splitting and degree provide the standard linking construction.
* **37. Symmetric multiplicity.** If an even $C^1$ functional is bounded
  below, satisfies Palais–Smale, has $I(0)=0$, and a symmetric compact
  set of Krasnosel'skii genus at least $k$ on which $I<0$, then it
  has at least $k$ distinct pairs of nonzero critical points.
* **38. Lusternik–Schnirelmann category.** A smooth real function on a
  compact smooth manifold without boundary has at least $\operatorname{cat}(M)$
  critical points. Category is the least size of an open cover whose
  members contract within $M$.
* **39. Nehari natural constraints.** Let
  $G(u)=DI(u)[u]$ and $\mathcal N=\{u\ne0:G(u)=0\}$.
  If $DG(u)[u]\ne0$, a constrained critical point of $I$ on
  $\mathcal N$ is an unconstrained critical point: the multiplier
  vanishes after testing in direction $u$.
* **40. Subcritical semilinear existence.** On a bounded smooth domain,
  $-\Delta u=|u|^{q-2}u$, $u\in H_0^1$, has a nonzero weak
  solution for $2<q<2^*$, obtained by mountain pass or Nehari
  minimization. Compact Sobolev embedding supplies Palais–Smale.
* **41. Pohozaev obstruction.** A classical solution of
  $-\Delta u=f(u)$ with zero Dirichlet data satisfies
  $$
  \frac{d-2}{2}\int|\nabla u|^2-d\int F(u)
  +\frac12\int_{\partial\Omega}(x\cdot\nu)|\partial_\nu u|^2=0,
  \qquad F'=f,\quad F(0)=0.
  $$
  On a strictly star-shaped domain, this excludes nonzero solutions
  of the critical or supercritical pure-power problem under the usual regularity.
* **42. Critical exponent and the Brezis–Nirenberg problem.** For
  $q=2^*$, $d\geq3$, Palais–Smale fails because of concentrating Sobolev
  bubbles but holds for $\frac12\int|\nabla u|^2-\frac\lambda2\int u^2
  -\frac1{2^*}\int|u|^{2^*}$ on $H_0^1$ at levels below $S^{d/2}/d$,
  $S$ the sharp Sobolev constant. Consequently
  $-\Delta u=\lambda u+u^{2^*-1}$, $u>0$, $u=0$ on $\partial\Omega$
  has a solution for $d\geq4$ and $0<\lambda<\lambda_1(\Omega)$; for $d=3$
  only a subinterval of $(0,\lambda_1)$ works (on a ball, $(\lambda_1/4,\lambda_1)$).

## Γ-convergence and variational limits

On a metric space, $F_j$ **Γ-converges** to $F$ if every $x_j\to x$
has $F(x)\leq\liminf F_j(x_j)$ and every $x$ has a **recovery sequence**
$x_j\to x$ with $\limsup F_j(x_j)\leq F(x)$.
Equicoercivity means their sublevels lie in common relatively compact sets.

* **43. Uniqueness and lower semicontinuity.** A Γ-limit is unique
  and lower semicontinuous in the chosen topology. Pointwise convergence
  alone does not determine it.
* **44. Fundamental theorem of Γ-convergence.** For equicoercive
  $F_j$ with Γ-limit $F$, $F$ attains its minimum and
  $\min F=\lim_j\inf F_j$. Every cluster point of a sequence $x_j$ with
  $F_j(x_j)\leq\inf F_j+o(1)$ minimizes $F$.
* **45. Recovery of minimizers.** Every minimizer of the Γ-limit has
  a recovery sequence that is asymptotically minimizing. If its minimizer
  is unique, every equicoercive sequence of approximate minimizers converges to it.
* **46. Γ-compactness.** On a separable metric space, every sequence
  of functionals with values in $[0,\infty]$ has a Γ-convergent
  subsequence. Equicoercivity is additional and controls minimizers,
  rather than being required for this extraction.
* **47. Continuous perturbations.** Adding a fixed finite continuous
  function preserves Γ-convergence and adds that function to the limit.
  Perturbations tending uniformly to zero do not change the Γ-limit.
* **48. Relaxation as a Γ-limit.** The Γ-limit of a constant sequence
  $F_j=F$ is its lower semicontinuous envelope. Recovery sequences
  explicitly realize the relaxed energy.
* **49. Mosco convergence.** For proper lower semicontinuous convex
  functionals on a Hilbert space, a weak liminf inequality plus strong
  recovery is Mosco convergence. It implies strong convergence of
  their proximal resolvents at every point, for each positive resolvent parameter.
* **50. Modica–Mortola theorem.** For $W(s)=s^2(1-s)^2$,
  $\int_\Omega(\varepsilon|\nabla u|^2/2+W(u)/\varepsilon)$
  Γ-converges in $L^1$ to $c_WP(E;\Omega)$ on $u=1_E$,
  and to infinity otherwise, where $c_W=\int_0^1\sqrt{2W(s)}ds$.
* **51. Phase-transition compactness.** Bounded Modica–Mortola energy
  gives $L^1$ precompactness on bounded Lipschitz domains and limits
  taking only the two well values. The limiting perimeter is controlled
  by the energy liminf.
* **52. Higher-order variational selection.** If the leading Γ-limit
  has several minimizers, rescaling the excess energy can distinguish
  among them through a further Γ-limit, provided the rescaled family
  is equicoercive. A first-order Γ-limit alone does not determine that selection.

## Periodic and stochastic homogenization

Let $Y=(0,1)^d$ and $A(y)$ be bounded uniformly elliptic and $Y$-periodic.
Periodic correctors $\chi_i$ have mean zero and belong to $H^1_{\mathrm{per}}(Y)$.

* **53. Cell correctors.** The equation
  $-\operatorname{div}_y(A(y)(e_i+\nabla\chi_i))=0$ has a unique
  mean-zero periodic weak solution. Define
  $A^{\mathrm{hom}}e_i=\int_YA(y)(e_i+\nabla\chi_i)dy$.
* **54. Elliptic homogenization.** Zero-Dirichlet solutions of
  $-\operatorname{div}(A(x/\varepsilon)\nabla u_\varepsilon)=f$,
  $f\in H^{-1}$, converge weakly in $H_0^1$ and strongly in $L^2$
  to the solution with coefficient $A^{\mathrm{hom}}$.
  Fluxes converge weakly in $L^2$ to $A^{\mathrm{hom}}\nabla u$.
* **55. Symmetric cell energy.** For symmetric $A$,
  $\xi\cdot A^{\mathrm{hom}}\xi
  =\min_{\phi\in H^1_{\mathrm{per}}(Y)}\int_Y
  (\xi+\nabla\phi)\cdot A(\xi+\nabla\phi)$.
  Thus the homogenized matrix is symmetric and uniformly elliptic.
* **56. Effective coefficient bounds.** In that symmetric case,
  $(\int_YA^{-1})^{-1}\leq A^{\mathrm{hom}}\leq\int_YA$
  in the quadratic-form order. In one dimension the effective
  coefficient is exactly the harmonic mean $(\int_Ya^{-1})^{-1}$.
* **57. Corrector convergence.** For smooth periodic coefficients and
  a smooth homogenized solution,
  $\nabla u_\varepsilon-(I+\nabla_y\chi(x/\varepsilon))\nabla u
  \to0$ in $L^2_{\mathrm{loc}}$.
  On a smooth bounded domain with $u\in H^2$, the first-order expansion
  satisfies $\|u_\varepsilon-u-\varepsilon\chi(x/\varepsilon)\cdot\nabla u\|_{H^1}
  \leq C\varepsilon^{1/2}$, the loss coming from a boundary layer, and
  $\|u_\varepsilon-u\|_{L^2}\leq C\varepsilon$.
* **58. Energy Γ-limit.** Symmetric uniformly elliptic periodic
  quadratic energies Γ-converge in $L^2$ to the quadratic energy
  with matrix $A^{\mathrm{hom}}$, including fixed Dirichlet data
  formulated on a common affine Sobolev space.
* **59. Two-scale compactness.** Every bounded $L^2(\Omega)$ sequence
  has a subsequence with a two-scale limit in $L^2(\Omega\times Y)$,
  tested against $\phi(x,x/\varepsilon)$ with smooth compact
  spatial support and periodic second variable.
* **60. Two-scale gradients.** A weakly convergent $H^1$ sequence
  has gradient two-scale limit
  $\nabla_xu(x)+\nabla_yu_1(x,y)$, with
  $u_1\in L^2(\Omega;H^1_{\mathrm{per}}(Y)/\mathbb R)$.
* **61. H-compactness.** Every uniformly bounded uniformly elliptic
  sequence of matrix fields has an H-convergent subsequence:
  Dirichlet solutions and their fluxes converge weakly for every
  $H^{-1}$ forcing to those of a limiting elliptic matrix field.
* **62. Nonlinear multicell formula.** For periodic Carathéodory
  $f(y,F)$ with coercive two-sided $p$-growth, the homogenized
  variational density is
  $$
  f_{\mathrm{hom}}(F)=\inf_{k\in\mathbb N}\frac1{k^d}
  \inf_{\phi\in W_0^{1,p}((0,k)^d;\mathbb R^m)}
  \int_{(0,k)^d} f(y,F+D\phi)dy.
  $$
  The energies Γ-converge in $L^p$ to $\int f_{\mathrm{hom}}(Du)$.
  Convexity permits the simpler single periodic-cell formulation.
* **63. Ergodic homogenization.** Stationary ergodic uniformly elliptic
  random coefficients homogenize almost surely to a deterministic
  matrix. Ergodicity removes realization dependence; quantitative
  rates require additional assumptions on correlations.

## Optimal control as variational continuation

* **64. Pontryagin principle with free terminal state.** For a smooth
  finite-horizon problem minimizing
  $\int_0^TL(x,u)dt+g(x(T))$ subject to $\dot x=b(x,u)$,
  with compact control set and the standard existence and boundedness
  hypotheses, an optimum has an adjoint satisfying
  $\dot p=-D_xH$, $p(T)=Dg(x(T))$, and
  $u(t)\in\operatorname*{argmin}_aH(x(t),p(t),a)$ almost everywhere,
  where $H=L+p\cdot b$.
* **65. Dynamic programming and Hamilton–Jacobi.** For bounded smooth
  controlled dynamics and costs with compact control set, the
  finite-horizon value function satisfies dynamic programming and
  is the viscosity solution of
  $V_t+\inf_a\{L(x,a)+b(x,a)\cdot DV\}=0$, $V(T)=g$,
  in the bounded uniformly continuous class under its comparison hypotheses.

## Reference guide

Dacorogna, Morrey, Giaquinta–Hildebrandt, Giusti, Fonseca–Leoni, and
Rindler overlap on existence, lower semicontinuity, and the vectorial
convexity notions; Giaquinta–Hildebrandt and Giusti also develop the
regularity of minimizers. Struwe, Rabinowitz, Willem, and Ambrosetti–Malchiodi
provide the critical-point core, with Struwe treating the limit cases
of the Palais–Smale condition. Dal Maso and Braides give Γ-convergence;
Braides–Defranceschi, Bensoussan–Lions–Papanicolaou, Jikov–Kozlov–Oleinik,
Cioranescu–Donato, and Tartar develop homogenization. Armstrong–Kuusi–Mourrat
provides the stochastic continuation. The control principles recur in
Clarke, Liberzon, and Agrachev–Sachkov. Detailed vortex expansions,
rate-independent evolution, and shape differentiation require additional
specialized selections.

Local source copies consulted:

* [Dacorogna, *Direct Methods in the Calculus of Variations*](References/Dacorogna2008DirectMethodsCalculusOfVariations2ndEd-SpringerAMS.pdf).
* [Rindler, *Calculus of Variations*](References/Rindler2018CalculusOfVariations-SpringerUTX.pdf).
* [Struwe, *Variational Methods*](References/Struwe2008VariationalMethodsApplicationsNonlinearPartialDifferentialEquationsHamiltonianSystems4thEd-SpringerErgebMath3.pdf).
* [Willem, *Minimax Theorems*](References/Willem1996MinimaxTheorems-Birkhauser.PNDEA24.pdf).
* [Braides, *Local Minimization, Variational Evolution and Γ-Convergence*](References/Braides2014LocalMinimizationVariationalEvolutionConvergence-Springer.LNM2094.pdf).
* [Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*](References/ArmstrongKuusiMourrat2019QuantitativeStochasticHomogenizationLargeScaleRegularity-SpringerGL352.pdf).
* [Pavliotis–Stuart, *Multiscale Methods*](References/PavliotisStuart2008MultiscaleMethods-Springer.TAM53.pdf).
* [Clarke, *Functional Analysis, Calculus of Variations and Optimal Control*](References/Clarke2013FunctionalAnalysisCalculusOfVariationsOptimalControl-SpringerGTM.pdf).
* [Agrachev–Sachkov, *Control Theory from the Geometric Viewpoint*](References/Agrachev2004ControlTheoryGeometricViewpoint-SpringerEMS87.pdf).
