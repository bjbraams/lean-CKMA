# Synopsis: One complex variable — graduate courses

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects the recurring graduate-course material of Section 40 of
[CKMA-bib.md](CKMA-bib.md).
It treats the local and global theory of holomorphic functions, contour
integration, harmonic functions, normal families, conformal mapping,
approximation, and analytic continuation. Sections 41–44 develop the
specialist theories of growth and values, analytic function spaces,
univalent maps, and Riemann surfaces.

A **domain** $\Omega\subset\mathbb C$ is nonempty, connected, and open.
Write $\mathcal O(\Omega)$ for its holomorphic functions,
$\mathbb D=\{|z|<1\}$, and $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$.
Contours and cycles are piecewise $C^1$ unless otherwise specified.
The winding number is
$\operatorname{Ind}(\gamma,a)=(2\pi i)^{-1}\int_\gamma dz/(z-a)$.
Convergence in $\mathcal O(\Omega)$ means uniform convergence on compact sets.

## Holomorphy, integration, and power series

A function is **holomorphic** if it has a complex derivative at every
point. With $z=x+iy$, put
$\partial_z=\frac12(\partial_x-i\partial_y)$ and
$\partial_{\bar z}=\frac12(\partial_x+i\partial_y)$.

* **1. Cauchy–Riemann characterization.** A $C^1$ function is
  holomorphic precisely when $\partial_{\bar z}f=0$, equivalently
  $u_x=v_y$ and $u_y=-v_x$ for $f=u+iv$. Its real differential
  is then multiplication by $f'(z)$.
* **2. Power-series differentiation.** A power series converges
  absolutely and locally uniformly inside its circle of convergence,
  is holomorphic there, and may be differentiated term by term.
  Its radius satisfies $R^{-1}=\limsup|a_n|^{1/n}$.
* **3. Cauchy–Goursat theorem.** The integral of a holomorphic
  function around a triangle whose closed interior lies in its domain
  is zero. No continuity assumption on the derivative is required.
* **4. Primitives and periods.** A holomorphic function has a primitive
  exactly when all its integrals over closed curves vanish. In particular,
  every holomorphic function on a simply connected domain has a primitive.
* **5. Homological Cauchy theorem.** If a cycle $\gamma$ in $\Omega$
  has index zero at every point outside $\Omega$, then
  $\int_\gamma f\,dz=0$ for every $f\in\mathcal O(\Omega)$.
* **6. Cauchy integral formula.** Under the same cycle condition,
  $\operatorname{Ind}(\gamma,a)f(a)
  =(2\pi i)^{-1}\int_\gamma f(z)/(z-a)\,dz$ for
  $a\in\Omega\setminus\gamma$.
* **7. Analyticity and higher derivatives.** Every holomorphic
  function has a convergent Taylor expansion on each disk contained
  in its domain. Moreover
  $f^{(k)}(a)=k!(2\pi i)^{-1}\int_{|z-a|=r}f(z)/(z-a)^{k+1}dz$.
* **8. Cauchy estimates.** If $|f|\leq M$ on $|z-a|=r$ and
  $f$ is holomorphic on a neighborhood of the closed disk, then
  $|f^{(k)}(a)|\leq k!M/r^k$. Local supremum bounds thus control
  all derivatives on smaller compact sets.
* **9. Morera's theorem.** A continuous function whose integral around
  every sufficiently small triangle is zero is holomorphic.
* **10. Weierstrass convergence theorem.** A locally uniform limit
  of holomorphic functions is holomorphic, and all derivatives converge
  locally uniformly. Locally uniformly absolutely convergent series may
  be integrated and differentiated termwise.
* **11. Holomorphic parameter integrals.** An integral of functions
  holomorphic in a parameter is holomorphic when locally dominated by
  an integrable function; parameter differentiation then passes under
  the integral, with the corresponding local domination.
* **12. Distributional holomorphy.** If $f\in L^1_{\mathrm{loc}}$
  and $\partial_{\bar z}f=0$ distributionally, $f$ agrees almost
  everywhere with a holomorphic function.

## Zeros, local mapping, and maximum principles

* **13. Isolated zeros and identity.** A nonzero holomorphic function
  has isolated zeros of finite multiplicity. Two holomorphic functions
  agreeing on a set with an interior accumulation point agree throughout
  their common domain.
* **14. Local normal form.** Near $a$, a nonconstant holomorphic
  function can be written $f(z)=f(a)+\phi(z)^m$, where $\phi$
  is a local holomorphic coordinate vanishing at $a$ and
  $m=\operatorname{ord}_a(f-f(a))$.
* **15. Open mapping theorem.** Every nonconstant holomorphic
  function maps open sets to open sets. Its local mapping degree is
  the multiplicity in the preceding normal form.
* **16. Holomorphic inverse theorem.** If $f'(a)\ne0$, $f$ has
  a local holomorphic inverse with derivative $1/f'(a)$. A globally
  injective holomorphic function has nonvanishing derivative and a
  holomorphic inverse onto its image.
* **17. Maximum modulus principle.** An interior local maximum of
  $|f|$ forces $f$ to be constant. On a bounded domain, a function
  holomorphic inside and continuous on the closure is bounded by its
  boundary supremum.
* **18. Minimum modulus principle.** If $f$ is holomorphic and
  zero-free on a domain and $|f|$ has a local minimum, then $f$ is
  constant. Hence a nonconstant $f$ continuous on the closure of a bounded
  domain and holomorphic inside attains $\min|f|$ on the boundary or at a zero.
* **19. Liouville and polynomial growth.** A bounded entire function
  is constant. An entire function satisfying
  $|f(z)|\leq C(1+|z|)^N$ is a polynomial of degree at most $N$.
* **20. Fundamental theorem of algebra.** Every nonconstant complex
  polynomial has a zero and factors into linear factors with multiplicity.
* **21. Logarithms and roots.** A zero-free $f\in\mathcal O(\Omega)$
  has a holomorphic logarithm exactly when all periods of $f'/f$
  vanish. It has a holomorphic $k$th root exactly when
  $(2\pi i)^{-1}\int_\gamma f'/f$ lies in $k\mathbb Z$ for every
  closed curve. Simply connected domains satisfy both conclusions.
* **22. Schwarz lemma.** If $f:\mathbb D\to\mathbb D$ and $f(0)=0$,
  then $|f(z)|\leq|z|$ and $|f'(0)|\leq1$; equality at a nonzero
  point or in the derivative forces $f(z)=e^{i\theta}z$.
* **23. Schwarz–Pick theorem.** Holomorphic self-maps of $\mathbb D$
  contract its pseudohyperbolic distance and satisfy
  $|f'(z)|/(1-|f(z)|^2)\leq1/(1-|z|^2)$.
  Equality at one pair of distinct points or one derivative point forces
  a disk automorphism.
* **24. Three-circles theorem.** For a holomorphic function on an
  annulus, $\log M(r)$ is convex as a function of $\log r$.
  Hadamard's three-lines theorem gives the corresponding log-convex
  bounds for bounded holomorphic functions on a strip.

## Isolated singularities, residues, and counting

A function is **meromorphic** if it is holomorphic except at isolated
poles, equivalently a holomorphic map into $\widehat{\mathbb C}$ that is
not constantly infinity. The **residue** is the coefficient of $(z-a)^{-1}$
in its Laurent expansion.

* **25. Laurent expansion.** A holomorphic function on
  $r<|z-a|<R$ has a unique Laurent series, normally convergent
  on compact subannuli, with coefficients given by contour integrals
  over any intervening circle.
* **26. Classification of isolated singularities.** An isolated
  singularity is removable, a pole, or essential according as its
  principal part is zero, finite and nonzero, or infinite.
* **27. Removable singularity theorem.** A holomorphic function bounded
  near a puncture extends holomorphically across it. More generally,
  $(z-a)f(z)\to0$ suffices.
* **28. Casorati–Weierstrass theorem.** The image of every punctured
  neighborhood of an essential singularity is dense in $\mathbb C$.
* **29. Great Picard theorem.** Near an essential singularity a
  holomorphic function takes every complex value infinitely often
  with at most one exception. For meromorphic functions the corresponding
  statement on the sphere permits at most two exceptions.
* **30. Residue theorem.** For a cycle null-homologous in the ambient
  domain and avoiding the isolated singularities of $f$,
  $\int_\gamma f\,dz=2\pi i\sum_a\operatorname{Ind}(\gamma,a)
  \operatorname{Res}_a f$, where only finitely many terms contribute.
* **31. Residues at infinity.** A meromorphic differential on the
  sphere has total residue zero. In coordinates,
  $\operatorname{Res}_\infty f(z)dz=-\operatorname{Res}_{w=0}
  f(1/w)w^{-2}dw$.
* **32. Rationality on the sphere.** Every meromorphic function on
  $\widehat{\mathbb C}$ is rational. An entire function with a pole
  at infinity is polynomial; an essential singularity there characterizes
  transcendental entire functions.
* **33. Argument principle.** If a meromorphic $f$ has no zero or
  pole on a positively oriented Jordan contour enclosing a region on
  which it is meromorphic, then
  $(2\pi i)^{-1}\int f'/f=N-P$, counting multiplicities.
* **34. Rouché's theorem.** If $f,g$ are holomorphic near a closed
  Jordan region and $|f-g|<|f|$ on its boundary, then they have
  the same number of zeros inside, with multiplicity.
* **35. Hurwitz's theorem.** For locally uniformly convergent
  holomorphic functions with nonzero limit, zeros of the limit persist
  nearby with their multiplicities. In particular a limit of zero-free
  functions is zero-free or identically zero.
* **36. Stability of univalence.** A locally uniform limit of injective
  holomorphic functions on a domain is injective or constant.
* **37. Jensen's formula.** If $f$ is holomorphic near the closed
  disk of radius $r$ and $f(0)\ne0$, then
  $$
  \log|f(0)|+\sum_{|a_j|<r}\log\frac r{|a_j|}
  =\frac1{2\pi}\int_0^{2\pi}\log|f(re^{it})|dt.
  $$
  Multiplicities are included; zeros on $|z|=r$ are allowed, since
  $\log|f|$ is then still integrable on the circle.

## Harmonic functions and boundary values

A real $C^2$ function is **harmonic** if $\Delta u=0$.
A function is **subharmonic** if it is upper semicontinuous, locally
integrable, and satisfies the sub-mean inequality, allowing the constant
$-\infty$ separately. The Poisson kernel is
$P_r(t)=(1-r^2)/(1-2r\cos t+r^2)$.

* **38. Harmonic conjugates.** The real and imaginary parts of a
  holomorphic function are harmonic. A harmonic function has a local
  harmonic conjugate; a global conjugate exists exactly when the periods
  of $-u_y\,dx+u_x\,dy$ vanish, hence always on simply connected domains.
* **39. Mean values and harmonic maximum principle.** Harmonic
  functions equal their circle and disk averages. Conversely a continuous
  function with the local mean-value property is harmonic. Interior
  extrema force constancy.
* **40. Poisson solution.** For $h\in C(\partial\mathbb D)$,
  $u(re^{i\theta})=(2\pi)^{-1}\int P_r(\theta-t)h(e^{it})dt$
  is the unique harmonic function continuous on the closed disk with
  boundary values $h$.
* **41. Positive harmonic representation.** Every positive harmonic
  function in $\mathbb D$ is the Poisson integral of a unique finite
  positive boundary measure. Its mass is $u(0)$.
* **42. Harnack inequality and convergence.** Positive harmonic
  functions satisfy $(1-r)/(1+r)\,u(0)\leq u(z)
  \leq(1+r)/(1-r)\,u(0)$ for $|z|\leq r$.
  Increasing harmonic sequences either diverge everywhere to infinity
  or converge locally uniformly to a harmonic function.
* **43. Subharmonic logarithms.** For holomorphic $f$,
  $\log|f|$ and $|f|^p$, $p>0$, are subharmonic; $\log|f|$
  is harmonic away from its zeros. Subharmonic functions obey the
  maximum principle and the comparison principle against harmonic functions.
* **44. Fatou boundary theorem.** The Poisson integral of an $L^1$
  boundary function converges nontangentially to that function almost
  everywhere. Bounded holomorphic functions therefore have almost
  everywhere nontangential boundary limits.
* **45. Schwarz reflection.** A holomorphic function continuous to
  a real boundary interval and real-valued there extends by
  $f(\bar z)=\overline{f(z)}$. Reflection across analytic arcs follows
  after holomorphic changes of coordinates; zero-boundary harmonic
  functions admit odd reflection across a line.
* **46. Dirichlet problem on Jordan domains.** A bounded Jordan
  domain admits a unique continuous harmonic extension of every
  continuous boundary function. A Riemann map transfers the Poisson
  solution using its boundary homeomorphism.
* **47. Perron method.** On a bounded domain, the supremum of subharmonic
  functions lying below continuous boundary data $h$ on $\partial\Omega$ is
  harmonic. It attains the value $h(\zeta)$ at every regular boundary point
  $\zeta$, and $\zeta$ is regular exactly when a barrier exists there. If no
  component of $\widehat{\mathbb C}\setminus\Omega$ is a single point,
  every boundary point is regular and the Dirichlet problem is solvable.

## Normal families and conformal mapping

A family is **normal** if every sequence has a subsequence converging
locally uniformly in the spherical metric to a meromorphic function or
the constant infinity. For locally bounded holomorphic families ordinary
locally uniform convergence suffices.

* **48. Montel compactness.** Every locally bounded family of
  holomorphic functions is relatively compact for locally uniform
  convergence. Cauchy estimates give the required equicontinuity.
* **49. Montel omission criterion.** A family of meromorphic functions
  omitting the same three distinct spherical values is normal.
  Holomorphic functions omitting two fixed finite values form a normal
  family in the spherical sense.
* **50. Vitali convergence.** A locally bounded holomorphic sequence
  converging pointwise on a set with an accumulation point in the
  domain converges locally uniformly throughout the domain.
* **51. Riemann mapping theorem.** Every simply connected proper
  plane domain is biholomorphic to $\mathbb D$. Given $a\in\Omega$,
  the map with $f(a)=0$ and $f'(a)>0$ is unique.
* **52. Characterizations of simple connectivity.** For a plane domain
  $\Omega$ the following are equivalent: $\widehat{\mathbb C}\setminus\Omega$
  is connected; every cycle in $\Omega$ is null-homologous; every
  holomorphic function has a primitive; every zero-free holomorphic
  function has a holomorphic logarithm; every harmonic function has a
  harmonic conjugate; $\Omega$ is $\mathbb C$ or biholomorphic to $\mathbb D$.
* **53. Disk and half-plane automorphisms.** The disk automorphisms
  are $e^{i\theta}(z-a)/(1-\bar az)$; the upper-half-plane
  automorphisms are real Möbius transformations of positive determinant.
  Sphere automorphisms are all complex Möbius transformations.
* **54. Finite Blaschke products.** If $f$ is holomorphic in $\mathbb D$,
  continuous on its closure, and $|f|=1$ on $\partial\mathbb D$, then $f$
  is a unimodular constant times a finite product
  $\prod_j(z-a_j)/(1-\bar a_jz)$. These are exactly the proper
  holomorphic self-maps of $\mathbb D$.
* **55. Carathéodory extension theorem.** A conformal map between
  Jordan domains extends to a homeomorphism between their closures.
  For general simply connected domains the natural replacement uses prime ends.
* **56. Classification of annuli.** Every doubly connected plane
  domain whose complementary components are nondegenerate is conformal
  to $r<|z|<1$ for a unique $0<r<1$. Its conformal modulus is
  $(2\pi)^{-1}\log(1/r)$.
* **57. Little Picard theorem.** A nonconstant entire function omits
  at most one complex value. A nonconstant meromorphic function on
  $\mathbb C$ omits at most two values of the sphere.
* **58. Bloch's theorem.** There is an absolute $b>0$ such that
  every holomorphic $f$ on $\mathbb D$ with $f'(0)=1$ has an
  image containing a disk of radius $b$ on which a holomorphic inverse
  branch exists. The disk need not be centered at $f(0)$.
* **59. Phragmén–Lindelöf principle.** If a function holomorphic in
  a sector of opening $\alpha$ is continuous on its boundary, bounded
  there by $M$, and grows at most $C\exp(C|z|^\rho)$ with
  $\rho<\pi/\alpha$, then it is bounded by $M$ throughout the sector.

## Approximation, prescribed data, and continuation

* **60. Runge approximation on compact sets.** If $K\subset\mathbb C$
  is compact and $f$ is holomorphic near $K$, it is uniformly
  approximable there by rational functions with poles in any prescribed
  set meeting every component of $\widehat{\mathbb C}\setminus K$.
  A pole at infinity means a polynomial part.
* **61. Runge domains.** Every holomorphic function on a plane domain
  is locally uniformly approximable by rational functions with poles
  outside the domain. Polynomial approximation for all such functions
  holds exactly when its spherical complement is connected.
* **62. Mergelyan's theorem.** If compact $K\subset\mathbb C$ has
  connected complement, every continuous function on $K$ holomorphic
  on its interior is uniformly approximable by polynomials.
* **63. Mittag–Leffler theorem.** On a plane domain, arbitrarily
  prescribed finite principal parts at a discrete set are the principal
  parts of a meromorphic function having no other poles.
* **64. Weierstrass zero theorem.** Any discrete set in a plane domain,
  with assigned positive integer multiplicities, is exactly the zero
  divisor of a holomorphic function there.
* **65. Entire canonical products.** For a sequence $a_j\to\infty$,
  suitable elementary factors
  $E_p(w)=(1-w)\exp(w+\cdots+w^p/p)$ give a normally convergent
  product with precisely those zeros. For $p=0$ use $E_0(w)=1-w$.
* **66. Quotients and divisors.** Every meromorphic function on a
  plane domain is a quotient of two holomorphic functions. Two
  holomorphic functions with the same zero divisor differ by a
  zero-free holomorphic factor, which is an exponential on simply
  connected domains.
* **67. Holomorphic interpolation.** Arbitrary finite jets prescribed
  at points of a discrete subset of a plane domain are realized by
  a holomorphic function.
* **68. Uniqueness of continuation.** A holomorphic germ has at most
  one analytic continuation along a fixed path. Continuations along
  homotopic paths with fixed endpoints agree when continuation is
  possible throughout the homotopy.
* **69. Monodromy theorem.** A germ continuable along every path of
  a simply connected domain defines a single-valued holomorphic
  function on that domain.
* **70. Natural boundaries exist.** A power series can have its entire
  convergence circle as a natural boundary. For example
  $\sum_{j\geq0}z^{2^j}$ has the unit circle as a natural boundary.
* **71. Mittag–Leffler expansions and products.** Normal convergence
  of regularized partial-fraction series and canonical products permits
  logarithmic differentiation away from their divisors. In particular
  $$
  \sin\pi z=\pi z\prod_{n=1}^\infty(1-z^2/n^2),\qquad
  \pi\cot\pi z=\frac1z+\sum_{n=1}^\infty\frac{2z}{z^2-n^2}.
  $$

## Standard global examples and analytic techniques

These examples recur across the broad courses; their systematic special-function
theory belongs to Section 49.

* **72. Gamma continuation.** The integral
  $\Gamma(z)=\int_0^\infty e^{-t}t^{z-1}dt$ for $\Re z>0$
  continues meromorphically to $\mathbb C$, has no zeros, and has
  simple poles at $-n$ with residues $(-1)^n/n!$.
  It satisfies $\Gamma(z+1)=z\Gamma(z)$.
* **73. Beta and reflection formulas.** For $\Re z,\Re w>0$,
  $B(z,w)=\Gamma(z)\Gamma(w)/\Gamma(z+w)$, and meromorphic
  continuation gives $\Gamma(z)\Gamma(1-z)=\pi/\sin\pi z$.
* **74. Stirling asymptotics.** Uniformly in
  $|\arg z|\leq\pi-\varepsilon$,
  $\Gamma(z)=\sqrt{2\pi}\,z^{z-1/2}e^{-z}(1+O_\varepsilon(|z|^{-1}))$
  as $|z|\to\infty$, with the principal logarithm in the power.
* **75. Fourier decay from contour shifting.** If $f$ is holomorphic
  on $|\Im z|<a$ and, for each $b<a$, satisfies
  $|f(x+iy)|\leq C_b(1+|x|)^{-1-\delta_b}$ uniformly for
  $|y|\leq b$, with $\delta_b>0$, then its Fourier transform
  $\widehat f(\xi)=\int f(x)e^{-ix\xi}dx$ decays like
  $O_b(e^{-b|\xi|})$ for every $0<b<a$.
* **76. Elliptic residue constraint.** A meromorphic function periodic
  under a rank-two lattice has equally many zeros and poles in a
  fundamental parallelogram, with multiplicities, and total residue zero.
  A holomorphic doubly periodic function is constant.
* **77. Weierstrass $\wp$-function.** For a lattice $\Lambda$,
  $\wp(z)=z^{-2}+\sum_{\omega\in\Lambda\setminus0}
  ((z-\omega)^{-2}-\omega^{-2})$ is even, $\Lambda$-periodic, with double
  poles at $\Lambda$, and satisfies $\wp'^2=4\wp^3-g_2\wp-g_3$ with
  $g_2=60\sum'\omega^{-4}$, $g_3=140\sum'\omega^{-6}$. Every
  $\Lambda$-elliptic function is a rational function of $\wp$ and $\wp'$.
* **78. Local solvability of $\bar\partial$.** For compactly supported
  smooth $g$ on $\mathbb C$,
  $u(z)=\pi^{-1}\int_{\mathbb C}g(\zeta)/(z-\zeta)\,dA(\zeta)$
  satisfies $\partial_{\bar z}u=g$. It comes from the Cauchy–Pompeiu
  formula: for $f\in C^1(\overline\Omega)$ on a bounded domain with
  piecewise $C^1$ boundary and $z\in\Omega$,
  $f(z)=\frac1{2\pi i}\int_{\partial\Omega}\frac{f(\zeta)}{\zeta-z}d\zeta
  -\frac1\pi\int_\Omega\frac{\partial_{\bar\zeta}f(\zeta)}{\zeta-z}dA(\zeta)$.

## Reference guide

Conway I, Gamelin, Remmert, Ahlfors, and the other first graduate texts
share the Cauchy, local mapping, residue, normal-family, and approximation
core. Conway II and Burckel enlarge the harmonic and boundary theory.
Stein–Shakarchi, Lang, Freitag–Busam, and Taylor emphasize global examples,
Fourier methods, and special functions. Remmert's companion volume gives
particularly detailed treatments of prescribed zeros, principal parts,
interpolation, products, and continuation. The results above occur across
these families; the specialist books of the following sections determine
the finer theories rather than extending this course indefinitely.

Local full-text sources consulted:

* [Conway, *Functions of One Complex Variable I*](References/Conway1978FunctionsOfOneComplexVariable1-SpringerGTM11.pdf).
* [Conway, *Functions of One Complex Variable II*](References/Conway1995FunctionsOfOneComplexVariable2-SpringerGTM159.pdf).
* [Gamelin, *Complex Analysis*](References/Gamelin2001ComplexAnalysis-Springer.UTM.pdf).
* [Stein–Shakarchi, *Complex Analysis*](References/SteinShakarchi2003PrincetonLecturesAnalysis2ComplexAnalysis-PrincetonUniversityPress.pdf).
* [Remmert, *Classical Topics in Complex Function Theory*](References/Remmert1998ClassicalTopicsComplexFunctionTheory-SpringerGTM172.pdf).
