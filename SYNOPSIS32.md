# Synopsis: Partial differential equations — general and linear theory

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-32);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects the recurring core of Section 32 of
[CKMA-bib.md](CKMA-bib.md#ckma-32):
characteristics and local solvability, the Laplace, heat, and wave equations,
weak formulations, linear elliptic boundary problems, energy methods,
linear systems, and symmetry methods. Sections 33 and 34 develop the
specialized regularity, nonlinear, and dispersive theories; Section 30 develops the full microlocal
calculus. Some overlap is retained because these are the basic mechanisms
by which PDE are solved.

The current neighbouring subdivisions separate hyperbolic systems
([34A](CKMA-bib.md#ckma-34a)), dispersive and geometric waves
([34B](CKMA-bib.md#ckma-34b)), fluids ([34C](CKMA-bib.md#ckma-34c)), and
kinetic equations ([34D](CKMA-bib.md#ckma-34d)). Section 33 retains nonlinear
elliptic and parabolic regularity, free boundaries, and viscosity methods.

Write $\Delta=\sum_j\partial_j^2$, so $-\Delta$ is nonnegative, and
$D_j=(1/i)\partial_j$. Unless explicitly relaxed, domains and coefficients
are smooth and boundary domains are bounded. Sobolev spaces are defined
using distributional derivatives; $H_0^1(\Omega)$ imposes zero trace.
For inequalities and maximum principles, solutions are real valued.

## Classification, Cauchy problems, and local solvability

For $P=\sum_{|\alpha|\leq m}a_\alpha(x)D^\alpha$, its **principal
symbol** is $p_m(x,\xi)=\sum_{|\alpha|=m}a_\alpha(x)\xi^\alpha$.
A hypersurface $\phi=0$ is **noncharacteristic** where
$p_m(x,d\phi)\ne0$. Ellipticity means this symbol is nonzero for every
nonzero real covector. Hyperbolicity concerns real characteristic roots in
a chosen time direction; parabolicity combines first-order time evolution
with elliptic spatial diffusion.

Fundamental solutions (SYNOPSIS16, item 63), Lewy's nonsolvability
example and local solvability (SYNOPSIS30, item 43), Holmgren uniqueness and
unique continuation (SYNOPSIS30, item 44), and propagation of singularities
(SYNOPSIS30, item 40) are stated in Sections 16 and 30.

* **1. Coordinate invariance of characteristics.** The principal symbol
  transforms as a homogeneous function on the cotangent bundle.
  Noncharacteristic hypersurfaces and ellipticity are therefore
  independent of the chosen coordinates.
* **2. Linear transport.** For $u_t+b(t,x)\cdot\nabla u=f$ with a
  smooth complete characteristic flow $X(t;s,x)$,
  $u(t,X(t;0,x))=u_0(x)+\int_0^tf(s,X(s;0,x))ds$.
  This gives existence and uniqueness while the flow remains defined.
* **3. Quasilinear characteristics.** For
  $a(x,u)\cdot\nabla u=b(x,u)$, sufficiently smooth data on a
  noncharacteristic hypersurface yield a unique local classical solution
  by the characteristic ODEs. The construction remains valid until
  its projection to the base ceases to be invertible.
* **67. Fully nonlinear first-order equations.** For $F(Du,u,x)=0$
  with smooth $F$, the characteristic system
  $\dot x=D_pF$, $\dot z=D_pF\cdot p$,
  $\dot p=-D_xF-D_zF\,p$ propagates $(x,z,p)=(x,u,Du)$ along
  characteristics. Smooth data on a hypersurface with admissible initial
  $p$ (satisfying $F=0$ and the tangential compatibility conditions)
  that is noncharacteristic, $D_pF\cdot\nu\ne0$, give a unique local
  $C^2$ solution. For Hamilton–Jacobi equations $u_t+H(Du,x)=0$ this is
  Hamilton's system $\dot x=D_pH$, $\dot p=-D_xH$; crossing
  characteristics end classical solvability in finite time in general,
  and the global theory uses viscosity solutions (Section 33).
* **4. Characteristic data and compatibility.** Prescribing Cauchy data
  on a characteristic hypersurface imposes tangential compatibility
  relations. Even compatible data need not determine a unique solution;
  the noncharacteristic condition is essential in the standard local theorem.
* **5. Cauchy–Kowalevski theorem.** An analytic PDE solved for its
  highest normal derivative, with analytic right-hand side depending on
  derivatives of no higher total order and strictly lower normal order,
  has a unique local analytic solution for analytic Cauchy data.
* **6. Hadamard's elliptic Cauchy example.** Analytic local solvability
  does not imply continuous dependence in smooth or Sobolev norms.
  Solutions
  $u_n(x,t)=e^{-\sqrt n}\sin(nx)\sinh(nt)/n$ of
  $u_{xx}+u_{tt}=0$ have Cauchy data at $t=0$ tending to zero in every
  $C^k$ norm, while their size at any fixed $t>0$ is unbounded.
* **9. Fourier solution of constant-coefficient equations.** Fourier
  transformation turns $P(D)u=f$ into $P(\xi)\widehat u=\widehat f$;
  zeros of $P$ require distributional inverses or additional prescriptions.
  For $\partial_tu=a(D)u$ on $\mathbb R^d$ the solution is
  $\widehat u(t,\xi)=e^{ta(\xi)}\widehat u_0(\xi)$, and the Cauchy
  problem is well posed in every $H^s$ exactly when
  $\sup_\xi\operatorname{Re}a(\xi)<\infty$ (Petrowsky condition):
  heat and Schrödinger equations satisfy it, the backward heat equation
  does not.

## The Laplacian and classical potential methods

* **10. Fundamental solution of $-\Delta$.** For $d\geq3$,
  $\Gamma(x)=((d-2)|S^{d-1}|)^{-1}|x|^{2-d}$ satisfies
  $-\Delta\Gamma=\delta$. In dimension two use
  $\Gamma(x)=-(2\pi)^{-1}\log|x|$.
* **11. Newtonian potentials.** For $f\in C_c^\infty$, $\Gamma*f$
  is smooth and solves $-\Delta u=f$. If $f$ is bounded, compactly
  supported, and locally $C^{0,\alpha}$, $0<\alpha<1$, then
  $\Gamma*f\in C^{2,\alpha}_{\mathrm{loc}}$ solves $-\Delta u=f$
  classically; for merely continuous $f$ it need not be $C^2$.
* **12. Mean-value characterization.** A continuous function is harmonic
  exactly when its value at each point equals its average over every
  sufficiently small centered sphere, or equivalently ball.
* **13. Weyl's lemma.** Every distributional solution of $\Delta u=0$
  is represented by a smooth harmonic function. Harmonic functions
  are real analytic.
* **14. Maximum principles.** A harmonic function continuous on the
  closure of a bounded domain attains its maximum and minimum on the
  boundary. On a connected domain an interior extremum forces constancy.
  Subharmonic functions satisfy the corresponding upper maximum principle.
* **15. Harnack inequality.** For a nonnegative harmonic function on
  a ball, $\sup_{B_r}u\leq C_d\inf_{B_r}u$ when the concentric
  ball $B_{2r}$ lies in the domain. Chains of balls give compact-set
  versions on connected domains.
* **16. Interior derivative estimates.** Harmonic functions satisfy
  $\sup_{B_r}|\partial^\alpha u|
  \leq C_{d,\alpha}r^{-|\alpha|}\sup_{B_{2r}}|u|$.
  These estimates imply local compactness of locally bounded harmonic families.
* **17. Liouville theorems.** A bounded harmonic function on all of
  $\mathbb R^d$ is constant. More generally a harmonic function with
  polynomial growth of degree at most $m$ is a harmonic polynomial
  of degree at most $m$.
* **18. Poisson formula.** Continuous boundary data on a ball have a
  unique harmonic extension continuous to the boundary, represented
  by the Poisson kernel. In the upper half-space the kernel is
  $P_t(x)=c_dt/(t^2+|x|^2)^{(d+1)/2}$, normalized to integral one
  for $x\in\mathbb R^d$. For the ball $B_R\subset\mathbb R^d$ the kernel
  is $(R^2-|x|^2)/(|S^{d-1}|R|x-y|^d)$ with respect to surface measure.
* **19. Green's identities.** For smooth $u,v$,
  $\int_\Omega\nabla u\cdot\nabla v
  =-\int_\Omega u\Delta v+\int_{\partial\Omega}u\partial_\nu v$.
  Antisymmetrization gives the second identity and Green representation
  using a fundamental solution or a domain Green function.
* **20. Dirichlet Green function.** A smooth bounded domain has a
  Dirichlet Green kernel for $-\Delta$, positive off the diagonal and
  symmetric in its variables. It represents zero-boundary Poisson
  solutions and determines the harmonic-measure boundary kernel.
* **21. Layer potentials and jumps.** Single- and double-layer harmonic
  potentials are smooth away from a smooth boundary. The single layer
  has continuous trace and a jump of normal derivative; the double
  layer has a jump of trace. With consistent normal orientation the
  two traces differ by the density, and their averages are boundary
  integral operators.
* **22. Classical Dirichlet and Neumann solvability.** On a smooth
  bounded connected domain, smooth Dirichlet data determine a unique
  harmonic function. The problem $-\Delta u=f$, $\partial_\nu u=g$
  is solvable precisely when $\int_\Omega f+\int_{\partial\Omega}g=0$,
  and then is unique modulo constants.
* **23. Perron's method and regular points.** On a bounded domain the
  supremum of subharmonic functions lying below continuous boundary data
  is harmonic. It attains the data at every boundary point admitting a
  barrier, so the Dirichlet problem is solvable for all continuous data
  exactly when every boundary point is regular. An exterior cone condition
  gives regularity; regularity is characterized by Wiener's capacity test,
  and for $d\geq3$ the Lebesgue spine shows that some boundary points are
  irregular. In the plane every boundary point of a complementary
  component that is a nondegenerate continuum is regular.

## Weak elliptic problems and boundary regularity

Consider
$Lu=-\partial_i(a^{ij}\partial_ju)+b^i\partial_iu+c u$ on a bounded
domain, with bounded real coefficients and
uniform ellipticity $a^{ij}\xi_i\xi_j\geq\lambda|\xi|^2$; $c$ may have
either sign. Repeated indices are summed. The associated form is
$a(u,v)=\int a^{ij}\partial_ju\,\partial_i\overline v
+b^i\partial_iu\,\overline v+c u\overline v$.
Symmetry is assumed only where explicitly stated. Caccioppoli and Schauder
estimates are stated in Section 33 (SYNOPSIS33, items 3 and 16–17).

* **24. Weak Dirichlet existence.** If $b=0$ and $c\geq0$, then for
  $f\in H^{-1}(\Omega)$,
  Lax–Milgram gives a unique $u\in H_0^1$ with
  $a(u,v)=\langle f,v\rangle$ and
  $\|u\|_{H^1}\leq C\|f\|_{H^{-1}}$.
  Only bounded measurability and uniform ellipticity of the coefficients
  are needed, and $\Omega$ may be any bounded open set.
* **25. Nonzero boundary data.** If $\partial\Omega$ is Lipschitz and
  $g\in H^{1/2}(\partial\Omega)$, choose an $H^1$ lifting of $g$
  and solve the zero-trace equation for the remainder. This gives
  existence, uniqueness, and continuous dependence in $H^1$.
* **26. Dirichlet principle.** If $a^{ij}=a^{ji}$, $b=0$ and $c\geq0$,
  the weak solution
  uniquely minimizes
  $\tfrac12a(u,u)-\operatorname{Re}\langle f,u\rangle$
  among functions with the prescribed trace.
* **27. Gårding coercivity after a shift.** Uniformly elliptic forms
  with bounded lower-order terms satisfy
  $\operatorname{Re}a(u,u)\geq c\|u\|_{H^1}^2-C\|u\|_2^2$.
  Adding a sufficiently large positive multiple of the $L^2$ inner
  product makes the form coercive.
* **28. Fredholm alternative.** On a bounded domain, compactness of
  $H_0^1\hookrightarrow L^2$ and a coercive shift imply that the
  Dirichlet problem for $L$ is Fredholm. It is solvable exactly when
  the forcing annihilates the adjoint homogeneous kernel.
* **30. Interior $H^2$ regularity.** For locally Lipschitz leading
  coefficients and $f\in L^2_{\mathrm{loc}}$, a weak solution of
  $Lu=f$ belongs to $H^2_{\mathrm{loc}}$, with local estimates
  controlled by $\|f\|_2$ and $\|u\|_{H^1}$ on a larger set.
* **31. Higher elliptic regularity.** Smooth elliptic coefficients give
  $Lu\in H^s_{\mathrm{loc}}\Rightarrow u\in H^{s+2}_{\mathrm{loc}}$
  for distributions $u$. Smooth forcing therefore gives smooth interior
  solutions.
* **32. Boundary $H^2$ regularity.** On a bounded $C^{1,1}$ domain,
  Lipschitz leading coefficients, bounded $b,c$, zero Dirichlet trace,
  and $f\in L^2$ give $u\in H^2$ with the corresponding estimate.
  Smooth coefficients, boundary, and compatible data yield higher
  boundary regularity.
* **33. $L^p$ elliptic estimates.** On a smooth bounded domain with
  smooth uniformly elliptic coefficients, the Dirichlet problem has
  $\|u\|_{W^{2,p}}\leq C(\|Lu\|_p+\|u\|_p)$ for
  $u\in W^{2,p}\cap W_0^{1,p}$, $1<p<\infty$.
  The second term can be removed when the homogeneous problem is injective.
* **35. Maximum and Hopf principles for elliptic equations.** For
  $L=-a^{ij}\partial_{ij}+b^i\partial_i+c$, $c\geq0$ (Section 33 uses
  the opposite sign, $a^{ij}u_{ij}+b^iu_i+cu$ with $c\leq0$), comparison
  holds for classical sub- and supersolutions. A nonconstant solution
  attaining a nonnegative maximum at an interior-sphere boundary point
  has strictly positive outward normal derivative under the usual
  maximum-principle inequality $Lu\leq0$. Consequently, on a connected
  domain a solution of $Lu\leq0$ attaining a nonnegative interior maximum
  is constant (strong maximum principle).
* **36. Dirichlet spectral theorem.** A symmetric uniformly elliptic
  Dirichlet realization has compact resolvent and an orthonormal $L^2$
  eigenbasis, with real eigenvalues tending to infinity. For smooth
  coefficients and boundary its eigenfunctions are smooth up to the boundary.
* **37. Min–max and the first eigenvalue.** Eigenvalues of a coercive
  symmetric Dirichlet form satisfy the Courant–Fischer variational
  principle. On a connected domain, the first eigenvalue of the scalar
  uniformly elliptic operator has a positive eigenfunction and is simple.
* **38. Boundary singularities.** Smooth forcing does not imply global
  $H^2$ regularity on arbitrary Lipschitz domains. Near a planar corner
  of opening $\omega$, harmonic Dirichlet modes include
  $r^{\pi/\omega}\sin(\pi\theta/\omega)$; a reentrant corner
  $\omega>\pi$ exhibits the loss of second-derivative square integrability.

## Heat equations and parabolic energy methods

* **39. Gaussian heat kernel.**
  $G_t(x)=(4\pi t)^{-d/2}e^{-|x|^2/(4t)}$ solves
  $\partial_tG_t=\Delta G_t$, has mass one, and satisfies
  $G_t*G_s=G_{t+s}$.
* **40. Heat Cauchy problem.** For $u_0\in L^p(\mathbb R^d)$,
  $1\leq p<\infty$, $u(t)=G_t*u_0$ is smooth for $t>0$,
  solves the heat equation, and tends to $u_0$ in $L^p$.
  It is the unique solution in $C([0,T];L^p)$. For classical solutions,
  uniqueness holds under the growth bound $|u|\leq Ce^{a|x|^2}$, but fails
  without growth restrictions (Tychonoff).
* **41. Heat smoothing estimates.** For $1\leq p\leq q\leq\infty$,
  $\|\partial^\alpha(G_t*f)\|_q
  \leq Ct^{-|\alpha|/2-(d/2)(1/p-1/q)}\|f\|_p$.
* **42. Heat comparison principle.** On a bounded space–time cylinder,
  a classical subsolution attains its upper bound on the initial or
  lateral boundary. This gives positivity preservation, uniqueness,
  and supremum-norm contraction for homogeneous boundary conditions.
* **43. Heat energy identity.** For zero Dirichlet boundary data,
  $\tfrac12\frac d{dt}\|u(t)\|_2^2+\|\nabla u(t)\|_2^2
  =\langle f(t),u(t)\rangle$ for $u_t-\Delta u=f$,
  interpreted by time integration for energy solutions.
* **44. Weak parabolic existence.** For bounded measurable uniformly
  elliptic $a^{ij}(t,x)$ and bounded nonnegative $c$, initial data in
  $L^2$, and $f\in L^2(0,T;H^{-1})$, the zero-Dirichlet equation
  $u_t+L(t)u=f$ has a unique solution
  $u\in L^2(0,T;H_0^1)$, $u_t\in L^2(0,T;H^{-1})$.
  The solution satisfies the usual energy estimate.
* **45. Time traces of energy solutions.** If
  $u\in L^2(0,T;V)$ and $u_t\in L^2(0,T;V^*)$ for a dense
  Hilbert triple $V\subset H\subset V^*$, then
  $u\in C([0,T];H)$ and
  $d\|u\|_H^2/dt=2\operatorname{Re}\langle u_t,u\rangle$
  distributionally. This justifies initial data and energy identities.
* **46. Duhamel formula.** If $L$ is the positive Dirichlet elliptic
  realization, then
  $u(t)=e^{-tL}u_0+\int_0^te^{-(t-s)L}f(s)ds$ solves
  $u_t+Lu=f$ in the appropriate mild or weak sense.
* **47. Heat eigenfunction expansion.** For a positive self-adjoint
  elliptic Dirichlet operator,
  $e^{-tL}u_0=\sum_ke^{-t\lambda_k}\langle u_0,\phi_k\rangle\phi_k$.
  In particular $\|u(t)\|_2\leq e^{-\lambda_1t}\|u_0\|_2$.
* **48. Instantaneous propagation.** For nonnegative nonzero integrable
  initial data on $\mathbb R^d$, the heat solution is positive at every
  point for every $t>0$, by strict positivity of the Gaussian kernel.
* **49. Backward-heat instability.** Inverting heat evolution multiplies
  the $k$th elliptic eigenmode by $e^{t\lambda_k}$.
  The backward problem therefore has no continuous solution map on $L^2$
  for positive elapsed time; generic terminal data do not admit a backward
  solution in that space.

## Waves, finite propagation, and hyperbolic systems

* **50. Wave Cauchy problem in energy spaces.** The equation
  $u_{tt}-c^2\Delta u=f$ on $\mathbb R^d$, $c>0$, has a unique
  solution $u\in C([0,T];H^1)$, $u_t\in C([0,T];L^2)$
  for initial data $(u_0,u_1)\in H^1\times L^2$ and
  $f\in L^1(0,T;L^2)$.
* **51. Wave energy.** For homogeneous forcing,
  $E(t)=\tfrac12\int(|u_t|^2+c^2|\nabla u|^2)$ is conserved.
  With forcing, $E'(t)=\operatorname{Re}\int f\,\overline{u_t}$, giving continuous dependence
  and uniqueness by an energy estimate.
* **52. Finite propagation speed.** A wave solution at $(t,x)$ depends
  only on initial data in $B(x,ct)$ and forcing in its backward cone.
  Compactly supported data propagate no faster than speed $c$.
* **53. D'Alembert formula.** In one dimension,
  $u(t,x)=\tfrac12(u_0(x-ct)+u_0(x+ct))
  +(2c)^{-1}\int_{x-ct}^{x+ct}u_1(y)dy$ for the homogeneous equation.
* **54. Kirchhoff formula and spherical means.** In three dimensions
  with $c=1$,
  $u(t,x)=\partial_t(tM_tu_0(x))+tM_tu_1(x)$,
  where $M_t$ is the spherical average of radius $t$.
  Descent gives the two-dimensional Poisson formula.
* **55. Huygens principle for the Euclidean wave equation.** In odd
  spatial dimensions at least three, the forward fundamental solution
  is supported on the light cone. In even dimensions it has an interior
  tail; finite propagation alone does not imply the sharp Huygens property.
* **56. Spectral wave formula.** For a nonnegative self-adjoint spatial
  operator $L$,
  $u(t)=\cos(t\sqrt L)u_0+
  (\sin(t\sqrt L)/\sqrt L)u_1$ solves $u_{tt}+Lu=0$.
  The quotient is interpreted as $t$ at spectral value zero.
* **57. Forced waves and boundary conditions.** Adding
  $\int_0^t\sin((t-s)\sqrt L)L^{-1/2}f(s)ds$ gives Duhamel's formula.
  Dirichlet or Neumann self-adjoint realizations yield the corresponding
  bounded-domain solutions and energy identities.
* **58. Free Schrödinger equation.** For $i\partial_tu+\Delta u=0$ on
  $\mathbb R^d$, $u(t)=e^{it\Delta}u_0$ is unitary on every $H^s$, with
  kernel $(4\pi it)^{-d/2}e^{i|x-y|^2/(4t)}$ for $t\ne0$. Hence
  $\|e^{it\Delta}u_0\|_\infty\leq(4\pi|t|)^{-d/2}\|u_0\|_1$: unlike the
  wave equation there is no finite propagation speed, and dispersion
  replaces it.
* **59. Symmetric hyperbolic energy estimate.** For
  $A^0u_t+\sum_jA^ju_{x_j}+Bu=f$, with Hermitian smooth matrices,
  $A^0$ uniformly positive and coefficients and their needed derivatives
  bounded, integration by parts gives
  $\|u(t)\|_2\leq Ce^{Ct}(\|u(0)\|_2+\int_0^t\|f(s)\|_2ds)$.
* **60. Symmetric hyperbolic well-posedness.** Under smooth bounded
  coefficient bounds, the system is well posed in $H^s$ on finite
  time intervals, with
  $u\in C(H^s)\cap C^1(H^{s-1})$ for initial data in $H^s$ and
  forcing continuous in time with values in $H^s$.
  Commuted energy estimates control derivatives, and characteristic
  speeds bound the domain of dependence.
* **61. Strictly hyperbolic Cauchy problems.** A smooth scalar order-$m$
  operator with distinct real time-characteristic roots is locally
  well posed on a noncharacteristic time slice in the Sobolev Cauchy
  scale $\partial_t^ju(0)\in H^{s+m-1-j}$, $0\leq j<m$.
  The solution has the corresponding local-in-time derivative regularity.

## General methods and structural conclusions

* **63. Galerkin construction.** Coercive elliptic and energy-controlled
  linear evolution problems admit finite-dimensional approximations
  with uniform energy bounds. Weak compactness gives solutions;
  uniqueness identifies limits and often gives strong convergence in
  the energy norm when the energy identities converge.
* **64. Duality and transposition.** If the adjoint boundary problem
  has an estimate, pairing data with its solution defines solutions
  for rougher forcing or boundary data by transposition. The resulting
  distributional solution agrees with a weak or classical solution
  whenever both are defined.
* **65. Interior regularity versus boundary compatibility.** For smooth
  linear parabolic or hyperbolic problems, interior smoothness follows
  from smooth data. Smoothness up to a space–time corner additionally
  requires agreement of the initial trace and its PDE-generated time
  derivatives with the imposed boundary values to the desired order.
* **66. Complementing boundary conditions.** For a smooth scalar strongly
  elliptic operator of order $2m$, a system of $m$ boundary operators
  $B_j$ of orders $m_j\leq2m-1$ satisfying the Lopatinskii–Shapiro
  complementing condition gives a Fredholm map
  $u\mapsto(Lu,(B_ju)_j)$ from $H^{s+2m}(\Omega)$ to
  $H^s(\Omega)\oplus\bigoplus_jH^{s+2m-m_j-1/2}(\partial\Omega)$,
  for $s\geq0$. Principal-symbol ellipticity alone does not guarantee
  an arbitrary choice of boundary conditions is valid.
* **68. Infinitesimal symmetry criterion.** Let a system
  $\Delta(x,u^{(n)})=0$ of differential equations be of maximal rank and
  locally solvable (nondegenerate). A connected local group of
  transformations of the independent and dependent variables is a
  symmetry group (mapping solutions to solutions) exactly when the $n$th prolongation of each of
  its infinitesimal generators $v$ satisfies
  $\operatorname{pr}^{(n)}v(\Delta)=0$ on the solution set (Lie).
  The symmetries form a Lie algebra computed from linear determining
  equations; group-invariant solutions solve a reduced system in fewer
  variables (Olver).
* **69. Symmetries of the heat equation.** The symmetry algebra of
  $u_t=u_{xx}$ is spanned by $\partial_x$, $\partial_t$, $u\partial_u$,
  $x\partial_x+2t\partial_t$, $2t\partial_x-xu\partial_u$,
  $4tx\partial_x+4t^2\partial_t-(x^2+2t)u\partial_u$, and the
  infinite-dimensional family $\alpha(x,t)\partial_u$ with $\alpha$ a
  solution. Invariance under the scaling field gives the similarity
  solutions, and the last finite generator followed by a time translation
  maps a constant solution to the fundamental solution
  $(4\pi t)^{-1/2}e^{-x^2/(4t)}$.

## Reference guide

Evans, Folland, John, Renardy–Rogers, and McOwen share the model
equations, characteristics, and weak-solution foundations. Folland and
Taylor connect these to distributions, spectral methods, and elliptic
operators; John, Rauch, and Mizohata emphasize characteristics, energy,
and hyperbolic well-posedness. Lions–Magenes supplies the systematic
boundary and evolution-space framework. Grisvard and Maz'ya's boundary
problem monographs explain why geometric boundary hypotheses cannot be
omitted from regularity statements. Rough-coefficient nonlinear regularity,
free boundaries, dispersive decay estimates, and nonlinear conservation laws
are reserved for the neighboring subject inventories.
Evans treats first-order nonlinear characteristics, and Olver and Stormark
the Lie symmetry method.

Local source copies consulted:

* [Folland, *Introduction to Partial Differential Equations*](References/Folland1995IntroductionPartialDifferentialEquations-PrincetonUniversityPress.pdf).
* [John, *Partial Differential Equations*](References/John1978PartialDifferentialEquations3rdEd-SpringerAMS01.pdf).
* [Taylor, *Partial Differential Equations*, I](References/Taylor2011PartialDifferentialEquations1BasicTheory2ndEd-SpringerAMS115.pdf).

These substantial texts supply complementary classical, Fourier, and
energy-method treatments rather than a catalogue limited to one course's
chapter sequence.
