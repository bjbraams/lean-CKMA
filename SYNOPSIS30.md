# Synopsis: Distributions, pseudodifferential operators, microlocal and semiclassical analysis

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-30);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring material from Section 30 of
[CKMA-bib.md](CKMA-bib.md#ckma-30). It begins
with distribution theory as used in PDE, then develops symbols, microlocal
regularity, Fourier integral operators, the semiclassical limit, and
scattering resonances.
The broader locally convex theory of distributions is treated in Section 16;
global spectral and geometric consequences also belong to Sections 22 and 53.

The distribution-space foundations remain in Section 16;
[34A](CKMA-bib.md#ckma-34a)–[34B](CKMA-bib.md#ckma-34b) supply hyperbolic and
dispersive applications, while the [inverse-problems
route](CKMA-MSC2020.md#inverse-problems) links Carleman and microlocal methods
across their several homes.

Here $D_j=(1/i)\partial_{x_j}$ and
$\widehat u(\xi)=\int e^{-ix\cdot\xi}u(x)dx$, so Fourier inversion
has factor $(2\pi)^{-d}$. Operators on open sets are properly supported
when needed; assertions on a closed manifold mean a compact smooth manifold
without boundary. Symbols and coefficients are smooth unless specified.

## Distributions and Fourier analysis for PDE

Distribution theory, Fourier transforms, fundamental solutions, and
stationary phase are stated in Sections 16, 27, and 50 (for example
SYNOPSIS16, items 42–66, and SYNOPSIS50, items 13–14); this section
records their microlocal use.

* **1. Distributional differentiation.** Every continuous linear
  functional on $C_c^\infty(\Omega)$ has derivatives of every order,
  defined by $\langle\partial^\alpha u,\phi\rangle
  =(-1)^{|\alpha|}\langle u,\partial^\alpha\phi\rangle$.
  These extend classical and weak derivatives and commute with each other.

## Wavefront sets and operations on singular distributions

The **wavefront set** $\mathrm{WF}(u)\subset T^*\Omega\setminus0$
excludes $(x_0,\xi_0)$ when some cutoff $\chi=1$ near $x_0$ has
$\widehat{\chi u}$ rapidly decreasing in a conic neighborhood of $\xi_0$.
The **Sobolev wavefront set** $\mathrm{WF}^s(u)$ replaces rapid decay
by conic square integrability with weight $\langle\xi\rangle^{2s}$.

* **11. Closedness and singular support.** $\mathrm{WF}(u)$ is closed
  and conic; its projection onto the base is the singular support of $u$.
  A distribution is smooth exactly when its wavefront set is empty.
* **12. Local Sobolev regularity.** $\mathrm{WF}^s(u)$ is empty over an
  open set exactly when $u$ is locally $H^s$ there. Increasing $s$
  can only increase this wavefront set.
* **13. Basic wavefront estimates.**
  $\mathrm{WF}(u+v)\subset\mathrm{WF}(u)\cup\mathrm{WF}(v)$,
  $\mathrm{WF}(au)\subset\mathrm{WF}(u)$ for smooth $a$, and
  $\mathrm{WF}(Pu)\subset\mathrm{WF}(u)$ for differential $P$.
* **14. Coordinate invariance.** If $F$ is a diffeomorphism,
  $\mathrm{WF}(F^*u)=\{(x,dF_x^T\eta):(F(x),\eta)\in\mathrm{WF}(u)\}$.
  Thus the definition is intrinsic on manifolds.
* **15. Pullback theorem.** A smooth map $F:X\to Y$ admits the
  pullback of $u$ if no $(F(x),\eta)\in\mathrm{WF}(u)$ satisfies
  $dF_x^T\eta=0$. Its wavefront set is contained in the transformed
  set in the preceding formula. Pullback by a submersion is always defined.
* **16. Restriction to submanifolds.** The restriction of $u$ to a smooth
  submanifold $S$ is defined if $\mathrm{WF}(u)\cap N^*S=\varnothing$,
  where $N^*S$ is the nonzero conormal bundle. Its possible singular
  covectors are the tangential restrictions of those of $u$.
* **17. Product theorem.** The product $uv$ is defined if there are no
  $(x,\xi)\in\mathrm{WF}(u)$ and $(x,-\xi)\in\mathrm{WF}(v)$.
  Its wavefront set is contained in $\mathrm{WF}(u)\cup\mathrm{WF}(v)$
  together with fiberwise sums of covectors from these two sets.
* **18. Tensor products.** The tensor product of distributions is always
  defined; its wavefront set is contained in the product of
  $\mathrm{WF}(u)$ and $\mathrm{WF}(v)$ with zero covectors over their
  supports adjoined, after removing the total zero covector.
* **19. Pushforward by submersions.** A smooth submersion $F$ proper
  on $\operatorname{supp}u$ admits a distributional pushforward, using
  densities along the fibers. Its wavefront set is contained in
  $\{(y,\eta):\exists x,\ F(x)=y,\ (x,dF_x^T\eta)\in\mathrm{WF}(u)\}$.
* **20. Conormal singularities.** A distribution locally represented
  by $\int e^{i\phi(x,\theta)}a(x,\theta)d\theta$, with phase
  parametrizing the conormal bundle of $S$, has wavefront set contained
  in $N^*S$. Delta distributions on smooth submanifolds are basic examples.

## Symbols, quantization, and the operator calculus

The class $S^m_{1,0}$ consists of symbols with
$|\partial_x^\alpha\partial_\xi^\beta a(x,\xi)|
\leq C_{\alpha\beta}\langle\xi\rangle^{m-|\beta|}$, locally uniformly
in $x$, or globally when global mapping bounds are asserted. Left quantization is
$$
\operatorname{Op}(a)u(x)=(2\pi)^{-d}\iint
 e^{i(x-y)\cdot\xi}a(x,\xi)u(y)dy\,d\xi.
$$
A **classical symbol** has an expansion in terms homogeneous in $\xi$
of degrees $m,m-1,\ldots$ for large $|\xi|$.

* **21. Oscillatory definition.** The displayed operator is well defined
  by cutoff limits and integration by parts, independently of the
  auxiliary cutoff. Symbols of order $-\infty$ give smooth kernels.
* **22. Asymptotic summation.** If $a_j\in S^{m-j}_{1,0}$, there is
  $a\in S^m_{1,0}$ with
  $a-\sum_{j<N}a_j\in S^{m-N}_{1,0}$ for every $N$.
  It is unique modulo $S^{-\infty}$ once the full expansion is fixed.
* **23. Composition formula.** If $A=\operatorname{Op}(a)$ and
  $B=\operatorname{Op}(b)$, then $AB=\operatorname{Op}(a\#b)$ with
  $$
  a\#b\sim\sum_\alpha\frac{1}{i^{|\alpha|}\alpha!}
       (\partial_\xi^\alpha a)(\partial_x^\alpha b).
  $$
  Orders add, and the remainder after $N$ derivative orders has order
  $m+m'-N$.
* **24. Adjoint formula.** Relative to Lebesgue measure, the formal
  adjoint has symbol
  $a^*\sim\sum_\alpha(i^{|\alpha|}\alpha!)^{-1}
  \partial_\xi^\alpha\partial_x^\alpha\overline a$.
  Other smooth densities change lower-order terms.
* **25. Principal symbols and commutators.** The principal symbol
  multiplies under composition. With
  $\{a,b\}=\partial_\xi a\cdot\partial_x b-
  \partial_x a\cdot\partial_\xi b$, the principal symbol of
  $[A,B]$ is $(1/i)\{a,b\}$, of order $m+m'-1$.
* **26. Coordinate invariance.** Changes of smooth coordinates preserve
  the classical pseudodifferential calculus. Principal symbols transform
  as functions on the cotangent bundle; full symbols acquire lower-order
  corrections.
* **27. Calderón–Vaillancourt theorem.** A symbol with bounded derivatives
  $\partial_x^\alpha\partial_\xi^\beta a$, $|\alpha|,|\beta|\leq N(d)$
  (the class $S^0_{0,0}$ suffices), defines a bounded $L^2$ operator.
  The norm is controlled by finitely many of those derivative bounds.
* **66. $S^m_{\rho,\delta}$ calculus.** For $0\leq\delta<\rho\leq1$,
  $S^m_{\rho,\delta}$ consists of symbols with
  $|\partial_x^\alpha\partial_\xi^\beta a|
  \leq C_{\alpha\beta}\langle\xi\rangle^{m-\rho|\beta|+\delta|\alpha|}$.
  Asymptotic summation, the composition and adjoint expansions of 23–24,
  pseudolocality, and $H^s\to H^{s-m}$ boundedness hold, successive
  terms of the expansions decreasing in order by $\rho-\delta$.
  Coordinate invariance holds when also $\delta\geq1-\rho$, which forces
  $\rho>1/2$. Order-zero operators are $L^2$ bounded
  also for $0\leq\delta=\rho<1$ (Calderón–Vaillancourt), but $S^0_{1,1}$
  operators need not be $L^2$ bounded.
* **28. Sobolev mapping theorem.** Globally controlled $S^m_{1,0}$
  operators map $H^s(\mathbb R^d)$ continuously to $H^{s-m}$.
  Properly supported versions give the corresponding local statement.
* **29. Pseudolocality.** Pseudodifferential kernels are smooth off the
  diagonal and $\mathrm{WF}(Au)\subset\mathrm{WF}(u)$.
  More precisely only covectors in the essential symbol support of $A$
  can survive; this is the closed conic set of covectors having no conic
  neighbourhood on which $a$ is of order $-\infty$.
* **30. Microlocal Sobolev mapping.**
  $\mathrm{WF}^{s-m}(Au)\subset\mathrm{WF}^s(u)$ for order $m$.
  If $A$ is elliptic at a covector (that is, $|a(x,\xi)|\geq c|\xi|^m$
  for large $|\xi|$ in a conic neighbourhood of it), membership in these
  two wavefront sets is equivalent there.
* **31. Gårding inequalities.** If $A$ has order $m$ and
  $\operatorname{Re}a_m(x,\xi)\geq c|\xi|^m$ (strong ellipticity), then
  $\operatorname{Re}\langle Au,u\rangle\geq c'\|u\|_{H^{m/2}}^2
  -C\|u\|_{H^{-N}}^2$ for $u$ supported in a fixed compact set
  (Gårding). If a real scalar $a\in S^m_{1,0}$
  is nonnegative, then
  $\operatorname{Re}\langle\operatorname{Op}(a)u,u\rangle
  \geq-C\|u\|_{H^{(m-1)/2}}^2$, locally with compact support or
  globally under uniform symbol bounds.
* **32. Paradifferential decomposition.** Smooth dyadic projections give
  Bony's decomposition $uv=T_uv+T_vu+R(u,v)$, separating low–high,
  high–low, and comparable-frequency products. For $\alpha+\beta>0$,
  $R:C^\alpha\times C^\beta\to C^{\alpha+\beta}$ continuously,
  where these are Hölder–Zygmund spaces.

## Ellipticity, hypoellipticity, and singularity propagation

An order-$m$ symbol is **elliptic** where $|a(x,\xi)|\geq c|\xi|^m$
at large frequencies in the indicated conic region. The complement is
its characteristic set $\operatorname{Char}(A)$.
Global consequences on closed manifolds (Fredholm property, complex powers,
Weyl asymptotics) are stated in Section 53 (SYNOPSIS53, items 5, 11, 24–27).

* **33. Parametrix theorem.** An elliptic operator has a two-sided
  parametrix of order $-m$ modulo smoothing operators. The same
  construction works microlocally in any elliptic conic region.
  Its principal symbol is the reciprocal of the principal symbol of the
  operator.
* **34. Elliptic wavefront identity.**
  $\mathrm{WF}(u)\subset\mathrm{WF}(Au)\cup\operatorname{Char}(A)$.
  Thus $\mathrm{WF}(Au)=\mathrm{WF}(u)$ for elliptic $A$.
* **35. Interior elliptic estimates.** For cutoffs $\chi\prec\widetilde\chi$
  and an elliptic differential operator $A$ of order $m$,
  $\|\chi u\|_{H^{s+m}}\leq C(\|\widetilde\chi Au\|_{H^s}
  +\|\widetilde\chi u\|_{H^{-N}})$, with suitable compact supports.
  Distributional solutions bootstrap to smoothness when $Au$ is smooth.
* **39. Subelliptic sums of squares.** If real smooth vector fields
  $X_1,\ldots,X_r$ and their brackets span every tangent space, then
  $\sum_jX_j^*X_j$ is hypoelliptic. Locally there is a positive
  subelliptic gain controlled by the bracket lengths on the compact set.
  The associated heat operator has a smooth kernel for positive time.
* **67. Hypoelliptic symbols.** Let $a\in S^m_{\rho,\delta}$,
  $0\leq\delta<\rho\leq1$, satisfy, for large $|\xi|$ and locally uniformly
  in $x$, $|a(x,\xi)|\geq c|\xi|^{m'}$ and
  $|\partial_x^\alpha\partial_\xi^\beta a|\leq C_{\alpha\beta}
  |a|\langle\xi\rangle^{-\rho|\beta|+\delta|\alpha|}$. Then
  $\operatorname{Op}(a)$ has a two-sided parametrix in
  $S^{-m'}_{\rho,\delta}$; it is hypoelliptic, and
  $\operatorname{Op}(a)u\in H^s_{\mathrm{loc}}$ implies
  $u\in H^{s+m'}_{\mathrm{loc}}$ (Hörmander). A hypoelliptic
  constant-coefficient $P(D)$ satisfies these bounds with $\delta=0$ and
  some $\rho>0$.
* **68. Hörmander's theorem with drift.** If real smooth vector fields
  $X_0,X_1,\ldots,X_r$ on an open set of $\mathbb R^n$ together with
  their iterated brackets span every tangent space, then
  $\sum_{j=1}^rX_j^2+X_0+c$ is hypoelliptic for smooth $c$. The Kolmogorov
  operator $\partial_t+v\cdot\nabla_x-\Delta_v$ on
  $\mathbb R_t\times\mathbb R^d_x\times\mathbb R^d_v$, and the kinetic
  Fokker–Planck operators obtained by adding terms $b(v)\cdot\nabla_v+c$,
  are examples:
  $[\partial_{v_j},\partial_t+v\cdot\nabla_x]=\partial_{x_j}$ supplies
  the missing directions. Global subelliptic estimates for kinetic
  Fokker–Planck operators with confining potentials give compact
  resolvent and a spectral gap (Hérau–Nier, Helffer–Nier); the resulting return to equilibrium is
  stated in Section 34 (SYNOPSIS34, item 75).
* **40. Propagation of singularities.** Let $P$ be properly supported
  with real principal symbol $p$ homogeneous of degree $m$. Then
  $\mathrm{WF}(u)\setminus\mathrm{WF}(Pu)\subset p^{-1}(0)$ and is
  invariant under the flow of the Hamilton field
  $H_p=\partial_\xi p\cdot\partial_x-\partial_xp\cdot\partial_\xi$ there,
  whose integral curves in $p^{-1}(0)$ are the null bicharacteristics
  (Duistermaat–Hörmander). Likewise,
  on a bicharacteristic interval where $Pu\in H^s$ microlocally,
  $u\in H^{s+m-1}$ microlocally at one point implies it on the whole
  interval.
* **41. Real-principal-type normal form.** Microlocally near a point
  of $p=0$ where the Hamilton field is not radial, homogeneous canonical
  coordinates reduce $p$ to a nonzero elliptic factor times one momentum
  coordinate. Elliptic Fourier integral conjugations reduce $P$ to the
  corresponding model derivative modulo lower-order corrections.
* **42. Sharpness of propagation.** Under the hypotheses of the
  preceding propagation theorem, for every compact interval $I$ of a null
  bicharacteristic with injective projection to the cosphere bundle,
  there is $u$ with $\mathrm{WF}(u)$ the cone over $I$ and
  $\mathrm{WF}(Pu)$ the cone over its endpoints. Singularities in the
  characteristic set are thus genuinely transported, not removable.
* **43. Local solvability.** The Lewy operator
  $\partial_{x_1}+i\partial_{x_2}-2i(x_1+ix_2)\partial_{x_3}$ on
  $\mathbb R^3$ is not locally solvable: for most smooth $f$, $Lu=f$ has
  no distributional solution near any point. For operators of principal
  type ($dp$ never proportional to $\xi\,dx$ on $p^{-1}(0)$),
  local solvability is equivalent to the Nirenberg–Trèves condition
  $(\Psi)$ (sufficiency by Dencker): for every smooth nonvanishing $q$,
  $\operatorname{Im}(qp)$ does not change sign from $-$ to $+$ along
  bicharacteristics of $\operatorname{Re}(qp)$. In particular $\operatorname{Im}p$
  must not change sign from $-$ to $+$ along bicharacteristics of
  $\operatorname{Re}p$, which excludes Hörmander's condition
  $\{\operatorname{Re}p,\operatorname{Im}p\}>0$ at a characteristic point.
* **44. Uniqueness and unique continuation.** If $P$ has analytic
  coefficients and $S$ is a noncharacteristic $C^1$ hypersurface, a
  distribution solution of $Pu=0$ vanishing on one side of $S$ vanishes
  near $S$ (Holmgren). For second-order elliptic operators with real
  Lipschitz principal coefficients and bounded lower-order coefficients on
  a connected open set, a solution vanishing to infinite order at a point
  vanishes identically (Aronszajn–Krzywicki–Szarski). Such results rest
  on Carleman estimates
  $\tau^{3/2}\|e^{\tau\varphi}u\|_2+\tau^{1/2}\|e^{\tau\varphi}\nabla u\|_2
  \leq C\|e^{\tau\varphi}Pu\|_2$ for $u\in C_c^\infty$ of small support
  and $\tau$ large, with weights satisfying Hörmander's strong
  pseudoconvexity condition.

## Fourier integral operators and canonical transformations

A nondegenerate homogeneous phase $\phi(x,y,\theta)$ defines a canonical
relation by $\partial_\theta\phi=0$ and covectors
$(x,\partial_x\phi;y,-\partial_y\phi)$. A **Fourier integral operator**
(FIO) has kernel given locally by oscillatory integrals with such phases.
A canonical relation is Lagrangian for the difference of the two
cotangent symplectic forms: that form vanishes on it and its dimension
is half the ambient dimension. The Hamilton field is
$H_p=\partial_\xi p\cdot\partial_x-\partial_xp\cdot\partial_\xi$.
Use the usual operator order in which order-zero canonical-graph FIOs on
equal-dimensional manifolds are locally $L^2$ bounded.

* **45. Wavefront mapping.** A properly supported FIO associated to
  $C\subset(T^*X\setminus0)\times(T^*Y\setminus0)$ satisfies
  $\mathrm{WF}(Au)\subset C\circ\mathrm{WF}(u)$.
* **46. Phase independence.** Equivalent nondegenerate parametrizations
  of a Lagrangian define the same class of Lagrangian distributions.
  Their leading amplitudes transform as half-densities with the
  corresponding Maslov factors.
* **47. Composition and adjoints.** For transverse canonical relations,
  FIO composition has the composed relation and the sum of the orders.
  Clean composition with excess $e$ adds $e/2$ to that order.
  Adjoints reverse the canonical relation.
* **48. $L^2$ boundedness for canonical graphs.** A compactly localized
  order-zero FIO associated to a canonical graph is $L^2$ bounded.
  Order-$m$ graph FIOs map $H^s_{\mathrm{comp}}$ to
  $H^{s-m}_{\mathrm{loc}}$.
* **49. Elliptic FIO inversion.** An elliptic FIO on a canonical graph
  has a microlocal inverse on the inverse graph, modulo smoothing errors.
  It transports microlocal regularity in both directions.
* **50. Egorov's theorem.** Conjugation of a pseudodifferential
  operator by an elliptic FIO quantizing a canonical transformation
  gives a pseudodifferential operator whose principal symbol is the
  original symbol transported by that transformation.
  For example, conjugation of an order-zero operator by the half-wave
  group $e^{it\sqrt\Delta}$ on a closed Riemannian manifold transports its
  principal symbol by the geodesic flow, for each fixed time.
* **51. Wave parametrices.** For a positive elliptic first-order
  self-adjoint operator $P$, the local propagator $e^{-itP}$ is an
  FIO associated to its Hamilton flow. Local phase representations
  solve the eikonal and transport equations; canonical relations continue
  through caustics even when a single phase chart fails.

## Semiclassical operators and phase-space limits

For $0<h\leq1$, Weyl quantization is
$$
\operatorname{Op}_h^w(a)u(x)=(2\pi h)^{-d}\iint
 e^{i(x-y)\cdot\xi/h}a((x+y)/2,\xi;h)u(y)dy\,d\xi.
$$
Unless indicated otherwise, semiclassical statements use symbols with
uniformly bounded derivatives, or compact phase-space support, and appropriate
self-adjoint realizations. Semiclassical Sobolev norms use $\langle hD\rangle^s$.

* **52. Uniform boundedness.** The Calderón–Vaillancourt estimate for
  $\operatorname{Op}_h^w(a)$ is uniform as $h\downarrow0$ when the
  required symbol seminorms are uniform.
* **53. Semiclassical Weyl calculus.**
  $\operatorname{Op}_h^w(a)\operatorname{Op}_h^w(b)
  =\operatorname{Op}_h^w(a\#_hb)$ with
  $a\#_hb=ab+(h/2i)\{a,b\}+O(h^2)$ in the symbol class.
  Thus $[\operatorname{Op}_h^w(a),\operatorname{Op}_h^w(b)]
  =(h/i)\operatorname{Op}_h^w(\{a,b\})+O(h^3)$ for uniform smooth symbols.
* **54. Weyl adjoints and positivity.**
  $\operatorname{Op}_h^w(a)^*=\operatorname{Op}_h^w(\overline a)$.
  If $a\geq0$ is a uniform order-zero symbol, sharp Gårding gives
  $\langle\operatorname{Op}_h^w(a)u,u\rangle\geq-Ch\|u\|_2^2$;
  the scalar Fefferman–Phong estimate improves this to $-Ch^2\|u\|_2^2$.
* **55. Semiclassical elliptic inversion.** If $|a|\geq c>0$ in a
  region, there is a symbol inverse there modulo $O(h^\infty)$.
  On a globally elliptic order-zero problem this gives a bounded inverse
  for small $h$, up to the stated negligible remainders.
* **56. Semiclassical wavefront set.** An $h$-tempered family has no
  semiclassical wavefront at $(x,\xi)$ if an elliptic cutoff there
  sends it to $O(h^\infty)$ in local Sobolev norms.
  Here $h$-tempered means polynomially bounded in $h^{-1}$. Unlike ordinary wavefront sets, the zero section is included, and
  fiber infinity is treated through the chosen symbol compactification.
* **57. Defect-measure compactness.** Every $L^2$-bounded family $u_h$
  has a subsequence $h_j\downarrow0$ and a positive Radon measure $\mu$
  with $\langle\operatorname{Op}_{h_j}^w(a)u_{h_j},u_{h_j}\rangle
  \to\int a\,d\mu$ for each compactly supported smooth symbol.
  Mass can escape in space or frequency unless tightness is assumed.
* **58. Characteristic support of measures.** If
  $P_hu_h=o(1)$ in $L^2$ and $P_h$ has principal symbol $p$,
  then every defect measure is supported on $p=0$, under the usual
  uniform symbol bounds and microlocal localization.
* **59. Hamiltonian invariance.** If $P_h$ is self-adjoint with real
  principal symbol $p$ and $P_hu_h=o(h)$, then
  $\int\{p,a\}d\mu=0$ for all compactly supported $a$.
  Thus $\mu$ is invariant under the Hamilton flow where it is defined.
* **60. Semiclassical Egorov theorem.** For
  $U_h(t)=e^{-itP_h/h}$ with self-adjoint $P_h$ and principal symbol $p$,
  $$
  U_h(t)^*\operatorname{Op}_h^w(a)U_h(t)
  =\operatorname{Op}_h^w(a\circ\Phi_t)+O(h)
  $$
  in $L^2$ operator norm on fixed time intervals with controlled flow
  and symbols. Here $\Phi_t$ is the $H_p$ flow.
* **61. Coherent states.** Normalized Gaussian packets centered at
  $(x_0,\xi_0)$ on spatial scale $\sqrt h$ have defect measure
  $\delta_{(x_0,\xi_0)}$, while WKB states $a(x)e^{i\varphi(x)/h}$
  have measure $|a(x)|^2\,dx\otimes\delta_{\xi=\nabla\varphi(x)}$.
* **62. Functional calculus.** If $P_h=\operatorname{Op}_h^w(p)$ is
  self-adjoint with real symbol $p$ in a uniform elliptic class and
  $f\in C_c^\infty(\mathbb R)$, then $f(P_h)$ is a semiclassical
  pseudodifferential operator with principal symbol $f\circ p$, as follows
  from the Helffer–Sjöstrand formula
  $f(P)=-\pi^{-1}\int\bar\partial\widetilde f(z)(z-P)^{-1}dm(z)$
  with an almost analytic extension $\widetilde f$.
* **63. Semiclassical trace formula.** A smooth symbol of compact
  phase-space support gives a trace-class Weyl operator with
  $\operatorname{Tr}\operatorname{Op}_h^w(a)
  =(2\pi h)^{-d}\int a(x,\xi)dx\,d\xi$.
  On closed manifolds the corresponding leading formula is invariantly
  expressed using Liouville measure.
* **64. Semiclassical Weyl law.** For
  $P_h=-h^2\Delta_g+V$ on a closed manifold and an interval $[a,b]$
  whose boundary energy surfaces have Liouville measure zero,
  $$
  \#\{\text{eigenvalues of }P_h\text{ in }[a,b]\}
  =(2\pi h)^{-d}\operatorname{vol}\{a\leq|\xi|_g^2+V(x)\leq b\}
  +o(h^{-d}).
  $$

## Scattering resonances

For real $V\in L^\infty_{\mathrm{comp}}(\mathbb R^d)$ write
$R_V(\lambda)=(-\Delta+V-\lambda^2)^{-1}$; it is a bounded operator on
$L^2$ for $\operatorname{Im}\lambda>0$ except at the finitely many
$\lambda\in i(0,\infty)$ with $\lambda^2$ a negative eigenvalue.

* **69. Meromorphic continuation.** For odd $d$, $R_V(\lambda)$ continues
  from the upper half-plane to a meromorphic family
  $L^2_{\mathrm{comp}}\to L^2_{\mathrm{loc}}$ on $\mathbb C$, with
  poles of finite rank; for even $d$ the continuation is to the
  logarithmic cover of $\mathbb C\setminus0$. The poles are the
  **resonances** (scattering poles). Resonances in the lower half-plane
  correspond to outgoing solutions of $(-\Delta+V-\lambda^2)u=0$ and
  govern the local decay of waves, the real part as frequency and
  $-\operatorname{Im}\lambda$ as decay rate.
* **70. Counting resonances.** For $d=1$ and $V\ne0$ with convex hull
  of support of length $L$, the number of resonances with
  $|\lambda|\leq r$, counted with multiplicity, is
  $(2L/\pi)r+o(r)$ (Zworski). For odd $d\geq3$ it is $O(r^d)$
  (Melrose for obstacles, Zworski for potentials).

## Reference guide

Hörmander's first volume supplies distributional operations, Fourier analysis,
and wavefront sets; his later volumes and the books of Taylor, Trèves,
Grigis–Sjöstrand, and Shubin overlap on the calculus and elliptic theory.
Duistermaat, Hörmander, and Trèves provide the FIO viewpoint. Zworski,
Dimassi–Sjöstrand, and Martinez give the semiclassical calculus, measures,
and dynamics. Paradifferential methods also recur in Taylor and
Alinhac–Gérard. Hörmander's third volume and Shubin treat the
$S^m_{\rho,\delta}$ classes and hypoelliptic parametrices, Helffer–Nier the
Fokker–Planck estimates, and Dyatlov–Zworski the resonance theory.
Specialized boundary calculi, analytic wavefront theory,
resonance expansions, tunneling, and global phase-space symbol metrics
extend this common foundation and are not exhaustively included here.

Local source copies consulted:

* [Hörmander, *The Analysis of Linear Partial Differential Operators*, I](References/Hörmander1998AnalysisLinearPartialDifferentialOperators1DistributionTheoryFourierAnalysis-SpringerGL256.pdf).
* [Hörmander, *The Analysis of Linear Partial Differential Operators*, III](References/Hörmander2007AnalysisLinearPartialDifferentialOperators3PseudoDifferentialOperators-SpringerCLASSICS.pdf).
* [Hörmander, *The Analysis of Linear Partial Differential Operators*, IV](References/Hörmander2009AnalysisLinearPartialDifferentialOperators4FourierIntegralOperators-SpringerCLASSICS.pdf).
* [Grigis–Sjöstrand, *Microlocal Analysis for Differential Operators*](References/GrigisSjöstrand1994MicrolocalAnalysisDifferentialOperatorsIntroduction-CambridgeLMSLNS196.pdf).
* [Zworski, *Semiclassical Analysis*](References/Zworski2012SemiclassicalAnalysis-AMS.GraduateStudies138.pdf).
* [Shubin, *Pseudodifferential Operators and Spectral Theory*](References/Shubin2001PseudodifferentialOperatorsSpectralTheory2ndEd-Springer.pdf).
* [Duistermaat, *Fourier Integral Operators*](References/Duistermaat2011FourierIntegralOperators-BirkhaeuserMBC.pdf).

Orders, Poisson-bracket signs, and Fourier normalization above fix the
conventions needed to compare formulas across these sources.
