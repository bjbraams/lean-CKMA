# Synopsis: Distributions, pseudodifferential operators, microlocal and semiclassical analysis

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects recurring material from Section 30 of
[CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md). It begins
with distribution theory as used in PDE, then develops symbols, microlocal
regularity, Fourier integral operators, and the semiclassical limit.
The broader locally convex theory of distributions is treated in Section 16;
global spectral and geometric consequences also belong to Sections 22 and 53.

Here $D_j=(1/i)\partial_{x_j}$ and
$\widehat u(\xi)=\int e^{-ix\cdot\xi}u(x)dx$, so Fourier inversion
has factor $(2\pi)^{-d}$. Operators on open sets are properly supported
when needed; assertions on a closed manifold mean a compact smooth manifold
without boundary. Symbols and coefficients are smooth unless specified.

## Distributions and Fourier analysis for PDE

* **1. Distributional differentiation.** Every continuous linear
  functional on $C_c^\infty(\Omega)$ has derivatives of every order,
  defined by $\langle\partial^\alpha u,\phi\rangle
  =(-1)^{|\alpha|}\langle u,\partial^\alpha\phi\rangle$.
  These extend classical and weak derivatives and commute with each other.
* **2. Local finite order.** On each fixed compact subset, a distribution
  is bounded by finitely many test-function derivative seminorms.
  Locally it is a finite sum of derivatives of continuous functions.
* **3. Point-supported distributions.** Every distribution supported
  at one point is a finite linear combination of derivatives of the
  Dirac mass at that point.
* **4. Convolution and regularization.** Distributions can be convolved
  when one factor has compact support. Derivatives commute with this
  convolution, and convolution with a test function is smooth.
  Mollification converges in the distribution topology.
* **5. Fourier transformation.** Fourier transformation is an
  automorphism of $\mathcal S$ and $\mathcal S'$, taking $D_j$ to
  multiplication by $\xi_j$ and multiplication by $x_j$ to
  $i\partial_{\xi_j}$.
* **6. Paley–Wiener–Schwartz theorem.** Compactly supported
  distributions have entire Fourier transforms of exponential type;
  a compact convex support $K$ is characterized by bounds
  $|F(z)|\leq C(1+|z|)^N e^{H_K(\operatorname{Im}z)}$.
* **7. Schwartz kernel theorem.** Continuous maps
  $C_c^\infty(Y)\to\mathcal D'(X)$ correspond uniquely to
  distributions on $X\times Y$. Kernel support encodes locality and
  proper support; smooth kernels give regularizing operators locally.
* **8. Malgrange–Ehrenpreis theorem.** Every nonzero constant-coefficient
  differential operator $P(D)$ on $\mathbb R^d$ has a distributional
  fundamental solution $E$, $P(D)E=\delta$.
  Hence $P(D)(E*f)=f$ for compactly supported distributions $f$.
* **9. Elliptic constant-coefficient regularity.** If $P(D)$ is elliptic,
  $P(D)u\in H^s_{\mathrm{loc}}$ implies
  $u\in H^{s+m}_{\mathrm{loc}}$, where $m$ is its order.
  In particular elliptic operators are hypoelliptic.
* **10. Nonstationary and stationary phase.** Smooth compactly supported
  oscillatory integrals decay faster than any power when the phase has
  no stationary point. A nondegenerate stationary point contributes
  a full expansion beginning with
  $(2\pi/\lambda)^{d/2}e^{i\lambda\phi(x_0)+i\pi\operatorname{sgn}\phi''/4}
  a(x_0)/|\det\phi''(x_0)|^{1/2}$ as $\lambda\to+\infty$.

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
* **27. Calderón–Vaillancourt theorem.** A symbol with sufficiently many
  bounded derivatives in both variables defines a bounded $L^2$ operator.
  The norm is controlled by finitely many of those derivative bounds.
* **28. Sobolev mapping theorem.** Globally controlled $S^m_{1,0}$
  operators map $H^s(\mathbb R^d)$ continuously to $H^{s-m}$.
  Properly supported versions give the corresponding local statement.
* **29. Pseudolocality.** Pseudodifferential kernels are smooth off the
  diagonal and $\mathrm{WF}(Au)\subset\mathrm{WF}(u)$.
  More precisely only covectors in the essential symbol support of $A$
  can survive.
* **30. Microlocal Sobolev mapping.**
  $\mathrm{WF}^{s-m}(Au)\subset\mathrm{WF}^s(u)$ for order $m$.
  If $A$ is elliptic at a covector, membership in these two wavefront
  sets is equivalent there.
* **31. Sharp Gårding inequality.** If a real scalar $a\in S^m_{1,0}$
  is nonnegative, then
  $\operatorname{Re}\langle\operatorname{Op}(a)u,u\rangle
  \geq-C\|u\|_{H^{(m-1)/2}}^2$, locally with compact support or
  globally under uniform symbol bounds.
* **32. Paradifferential decomposition.** Smooth dyadic projections give
  Bony's decomposition $uv=T_uv+T_vu+R(u,v)$, separating low–high,
  high–low, and comparable-frequency products. For $\alpha,\beta>0$,
  $R:C^\alpha\times C^\beta\to C^{\alpha+\beta}$ continuously,
  where these are Hölder–Zygmund spaces.

## Ellipticity, hypoellipticity, and singularity propagation

An order-$m$ symbol is **elliptic** where $|a(x,\xi)|\geq c|\xi|^m$
at large frequencies in the indicated conic region. The complement is
its characteristic set $\operatorname{Char}(A)$.

* **33. Parametrix theorem.** An elliptic operator has a two-sided
  parametrix of order $-m$ modulo smoothing operators. The same
  construction works microlocally in any elliptic conic region.
* **34. Elliptic wavefront identity.**
  $\mathrm{WF}(u)\subset\mathrm{WF}(Au)\cup\operatorname{Char}(A)$.
  Thus $\mathrm{WF}(Au)=\mathrm{WF}(u)$ for elliptic $A$.
* **35. Interior elliptic estimates.** For cutoffs $\chi\prec\widetilde\chi$
  and an elliptic differential operator $A$ of order $m$,
  $\|\chi u\|_{H^{s+m}}\leq C(\|\widetilde\chi Au\|_{H^s}
  +\|\widetilde\chi u\|_{H^{-N}})$, with suitable compact supports.
  Distributional solutions bootstrap to smoothness when $Au$ is smooth.
* **36. Fredholm theorem on closed manifolds.** An elliptic operator
  $A:H^{s+m}(M)\to H^s(M)$ is Fredholm, has smooth kernel and
  cokernel, and has index independent of $s$. Solvability is equivalent
  to orthogonality to the kernel of its formal adjoint.
* **37. Complex powers.** A strictly positive self-adjoint elliptic
  classical operator $A$ of positive order $m$ on a closed manifold
  has complex powers $A^z$ in the classical calculus of complex order
  $mz$. Spectral and pseudodifferential definitions agree.
* **38. Elliptic spectral asymptotics.** For a positive self-adjoint
  elliptic operator of order $m>0$ with positive scalar principal symbol,
  $N(\lambda)\sim(2\pi)^{-d}\operatorname{vol}\{(x,\xi):a_m(x,\xi)\leq\lambda\}$.
  The leading growth is $\lambda^{d/m}$.
* **39. Subelliptic sums of squares.** If real smooth vector fields
  $X_1,\ldots,X_r$ and their brackets span every tangent space, then
  $\sum_jX_j^*X_j$ is hypoelliptic. Locally there is a positive
  subelliptic gain controlled by the bracket lengths on the compact set.
* **40. Propagation of singularities.** Let $P$ have real homogeneous
  principal symbol $p$ of principal type, with nonzero Hamilton field
  on the characteristic set. In a region where $Pu$ is smooth,
  $\mathrm{WF}(u)$ is a union of maximally extended null
  bicharacteristics of $H_p$ within that region.
* **41. Real-principal-type normal form.** Microlocally near a point
  of $p=0$ where the Hamilton field is not radial, homogeneous canonical
  coordinates reduce $p$ to a nonzero elliptic factor times one momentum
  coordinate. Elliptic Fourier integral conjugations reduce $P$ to the
  corresponding model derivative modulo lower-order corrections.
* **42. Characteristic obstruction.** A distributional solution may
  have singularities along the characteristic set even when its forcing
  is smooth. For the wave operator these covectors travel along null
  bicharacteristics, rather than being removed by an elliptic parametrix.

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

* **43. Wavefront mapping.** A properly supported FIO associated to
  $C\subset(T^*X\setminus0)\times(T^*Y\setminus0)$ satisfies
  $\mathrm{WF}(Au)\subset C\circ\mathrm{WF}(u)$.
* **44. Phase independence.** Equivalent nondegenerate parametrizations
  of a Lagrangian define the same class of Lagrangian distributions.
  Their leading amplitudes transform as half-densities with the
  corresponding Maslov factors.
* **45. Composition and adjoints.** For transverse canonical relations,
  FIO composition has the composed relation and the sum of the orders.
  Clean composition with excess $e$ adds $e/2$ to that order.
  Adjoints reverse the canonical relation.
* **46. $L^2$ boundedness for canonical graphs.** A compactly localized
  order-zero FIO associated to a canonical graph is $L^2$ bounded.
  Order-$m$ graph FIOs map $H^s_{\mathrm{comp}}$ to
  $H^{s-m}_{\mathrm{loc}}$.
* **47. Elliptic FIO inversion.** An elliptic FIO on a canonical graph
  has a microlocal inverse on the inverse graph, modulo smoothing errors.
  It transports microlocal regularity in both directions.
* **48. Egorov's theorem.** Conjugation of a pseudodifferential
  operator by an elliptic FIO quantizing a canonical transformation
  gives a pseudodifferential operator whose principal symbol is the
  original symbol transported by that transformation.
* **49. Wave parametrices.** For a positive elliptic first-order
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

* **50. Uniform boundedness.** The Calderón–Vaillancourt estimate for
  $\operatorname{Op}_h^w(a)$ is uniform as $h\downarrow0$ when the
  required symbol seminorms are uniform.
* **51. Semiclassical Weyl calculus.**
  $\operatorname{Op}_h^w(a)\operatorname{Op}_h^w(b)
  =\operatorname{Op}_h^w(a\#_hb)$ with
  $a\#_hb=ab+(h/2i)\{a,b\}+O(h^2)$ in the symbol class.
  Thus $[\operatorname{Op}_h^w(a),\operatorname{Op}_h^w(b)]
  =(h/i)\operatorname{Op}_h^w(\{a,b\})+O(h^3)$ for uniform smooth symbols.
* **52. Weyl adjoints and positivity.**
  $\operatorname{Op}_h^w(a)^*=\operatorname{Op}_h^w(\overline a)$.
  If $a\geq0$ is a uniform order-zero symbol, sharp Gårding gives
  $\langle\operatorname{Op}_h^w(a)u,u\rangle\geq-Ch\|u\|_2^2$;
  the scalar Fefferman–Phong estimate improves this to $-Ch^2\|u\|_2^2$.
* **53. Semiclassical elliptic inversion.** If $|a|\geq c>0$ in a
  region, there is a symbol inverse there modulo $O(h^\infty)$.
  On a globally elliptic order-zero problem this gives a bounded inverse
  for small $h$, up to the stated negligible remainders.
* **54. Semiclassical wavefront set.** An $h$-tempered family has no
  semiclassical wavefront at $(x,\xi)$ if an elliptic cutoff there
  sends it to $O(h^\infty)$ in local Sobolev norms.
  Here $h$-tempered means polynomially bounded in $h^{-1}$ in the
  relevant distribution seminorms.
  Unlike ordinary wavefront sets, the zero section is included, and
  fiber infinity is treated through the chosen symbol compactification.
* **55. Defect-measure compactness.** Every $L^2$-bounded family $u_h$
  has a subsequence $h_j\downarrow0$ and a positive Radon measure $\mu$
  with $\langle\operatorname{Op}_{h_j}^w(a)u_{h_j},u_{h_j}\rangle
  \to\int a\,d\mu$ for each compactly supported smooth symbol.
  Mass can escape in space or frequency unless tightness is assumed.
* **56. Characteristic support of measures.** If
  $P_hu_h=o(1)$ in $L^2$ and $P_h$ has principal symbol $p$,
  then every defect measure is supported on $p=0$, under the usual
  uniform symbol bounds and microlocal localization.
* **57. Hamiltonian invariance.** If $P_h$ is self-adjoint with real
  principal symbol $p$ and $P_hu_h=o(h)$, then
  $\int\{p,a\}d\mu=0$ for all compactly supported $a$.
  Thus $\mu$ is invariant under the Hamilton flow where it is defined.
* **58. Semiclassical Egorov theorem.** For
  $U_h(t)=e^{-itP_h/h}$ with self-adjoint $P_h$ and principal symbol $p$,
  $$
  U_h(t)^*\operatorname{Op}_h^w(a)U_h(t)
  =\operatorname{Op}_h^w(a\circ\Phi_t)+O(h)
  $$
  in $L^2$ operator norm on fixed time intervals with controlled flow
  and symbols. Here $\Phi_t$ is the $H_p$ flow.
* **59. Coherent states.** Normalized Gaussian packets centered at
  $(x_0,\xi_0)$ on spatial scale $\sqrt h$ have defect measure
  $\delta_{(x_0,\xi_0)}$. The uncertainty scale is therefore compatible
  with point concentration in the semiclassical phase-space limit.
* **60. Semiclassical trace formula.** A smooth symbol of compact
  phase-space support gives a trace-class Weyl operator with
  $\operatorname{Tr}\operatorname{Op}_h^w(a)
  =(2\pi h)^{-d}\int a(x,\xi)dx\,d\xi$.
  On closed manifolds the corresponding leading formula is invariantly
  expressed using Liouville measure.
* **61. Semiclassical Weyl law.** For
  $P_h=-h^2\Delta_g+V$ on a closed manifold and an interval $[a,b]$
  whose boundary energy surfaces have Liouville measure zero,
  $$
  \#\{\text{eigenvalues of }P_h\text{ in }[a,b]\}
  =(2\pi h)^{-d}\operatorname{vol}\{a\leq|\xi|_g^2+V(x)\leq b\}
  +o(h^{-d}).
  $$
* **62. Quantum ergodicity.** If the geodesic flow on the unit cosphere
  of a closed Riemannian manifold is ergodic, every orthonormal
  Laplace eigenbasis has a subsequence of density one whose
  order-zero pseudodifferential expectations converge to the normalized
  Liouville average of the principal symbol.

## Reference guide

Hörmander's first volume supplies distributional operations, Fourier analysis,
and wavefront sets; his later volumes and the books of Taylor, Trèves,
Grigis–Sjöstrand, and Shubin overlap on the calculus and elliptic theory.
Duistermaat, Hörmander, and Trèves provide the FIO viewpoint. Zworski,
Dimassi–Sjöstrand, and Martinez give the semiclassical calculus, measures,
and dynamics. Paradifferential methods also recur in Taylor and
Alinhac–Gérard. Specialized boundary calculi, analytic wavefront theory,
resonance expansions, tunneling, and global phase-space symbol metrics
extend this common foundation and are not exhaustively included here.

Local source copies consulted:

* [Hörmander, *The Analysis of Linear Partial Differential Operators*, I](References/Hörmander1998AnalysisLinearPartialDifferentialOperators1DistributionTheoryFourierAnalysis-SpringerGL256.pdf).
* [Hörmander, *The Analysis of Linear Partial Differential Operators*, III](References/Hörmander2007AnalysisLinearPartialDifferentialOperators3PseudoDifferentialOperators-SpringerCLASSICS.pdf).
* [Grigis–Sjöstrand, *Microlocal Analysis for Differential Operators*](References/GrigisSjöstrand1994MicrolocalAnalysisDifferentialOperatorsIntroduction-CambridgeLMSLNS196.pdf).
* [Zworski, *Semiclassical Analysis*](References/Zworski2012SemiclassicalAnalysis-AMS.GraduateStudies138.pdf).
* [Shubin, *Pseudodifferential Operators and Spectral Theory*](References/Shubin2001PseudodifferentialOperatorsSpectralTheory2ndEd-Springer.pdf).
* [Duistermaat, *Fourier Integral Operators*](References/Duistermaat2011FourierIntegralOperators-BirkhaeuserMBC.pdf).

Orders, Poisson-bracket signs, and Fourier normalization above fix the
conventions needed to compare formulas across these sources.
