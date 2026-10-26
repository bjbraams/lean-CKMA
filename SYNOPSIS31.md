# Synopsis: Ordinary differential equations and dynamical systems

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-31);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring core material from Section 31 of
[CKMA-bib.md](CKMA-bib.md#ckma-31). It covers
existence and dependence, linear equations, stability and invariant manifolds,
planar dynamics, bifurcations, hyperbolicity, and perturbation of Hamiltonian
systems. Linear boundary problems and dissipative dynamics provide two
further recurring continuations. Measure-theoretic dynamics is treated in
Section 10, and detailed asymptotic expansions in Section 50.

Ergodic structure is developed in Section 10, holomorphic iteration in Section
46, and integrability in Section 51. Concrete hyperbolic, dispersive, fluid,
and kinetic evolution is organised in
[34A](CKMA-bib.md#ckma-34a)–[34D](CKMA-bib.md#ckma-34d).

The basic equation is $\dot x=F(t,x,\mu)$ in finite-dimensional Euclidean
space or a smooth manifold. A **flow** satisfies
$\varphi_{t+s}=\varphi_t\circ\varphi_s$ on its domain.
Equilibria satisfy $F(x)=0$; periodic orbits are nonconstant closed trajectories.
Smoothness and completeness are imposed in the statements that need them.

## Existence, uniqueness, and dependence

Grönwall's inequality, used throughout, is stated in Section 11
(SYNOPSIS11, item 40).

* **1. Peano existence.** Continuous $F$ admits a local solution through
  every interior initial point. Continuity alone does not imply uniqueness.
* **2. Picard–Lindelöf theorem.** If $F$ is continuous in $t$ and
  locally Lipschitz in $x$, locally uniformly in $t$, every initial
  condition has a unique maximal solution. Successive approximation
  converges on sufficiently short intervals.
* **3. Carathéodory equations.** Local existence of absolutely continuous
  solutions persists when $F$ is measurable in $t$, continuous in $x$
  for almost every $t$, and locally bounded by an integrable function
  of $t$. A local Lipschitz bound in $x$ with integrable coefficient
  gives uniqueness.
* **4. Continuation alternative.** A maximal solution with finite endpoint
  leaves every compact subset of the equation's space–time domain as
  the endpoint is approached. If the domain is all of $\mathbb R\times
  \mathbb R^n$, finite-time failure requires unbounded $|x(t)|$.
* **5. Linear-growth global existence.** A bound
  $|F(t,x)|\leq a(t)+b(t)|x|$ with locally integrable $a,b$ prevents
  finite-time blowup. Under uniqueness this yields a global evolution
  for all finite times on which the coefficients are defined.
* **7. Continuous dependence.** Solutions depend continuously on initial
  conditions and parameters on every compact interval contained in the
  limiting solution's existence interval, when the local continuity and
  Lipschitz bounds hold uniformly.
* **8. Smooth dependence and variational equations.** For $C^r$ vector
  fields, $r\geq1$, the local flow is $C^r$. Its initial derivative
  solves $\dot Y=D_xF(t,x(t))Y$, $Y(t_0)=I$; parameter derivatives
  solve the corresponding inhomogeneous variational equations.
* **9. Flow inverses and the flow box.** For an autonomous $C^1$ field,
  each defined time map is a local diffeomorphism with inverse the
  negative-time map. Near a point where $F\ne0$, a smooth coordinate
  change straightens the vector field to a constant coordinate vector.
* **10. Analytic dependence.** Analytic vector fields have locally
  analytic solutions and analytic dependence on initial data and analytic
  parameters. The analogous local theorem holds for holomorphic ODEs
  in a complex time variable.
* **11. Invariant regions.** For locally Lipschitz autonomous $F$, a
  closed set $K$ is forward invariant exactly when $F(x)$ lies in the
  Bouligand tangent cone of $K$ at every $x\in K$ (Nagumo, Bony–Brezis).
  For $K=\{g\leq0\}$ with $g\in C^1$ and $\nabla g\ne0$ on $\{g=0\}$,
  the condition is $\nabla g\cdot F\leq0$ there.
* **12. Scalar comparison.** For a scalar locally Lipschitz equation,
  subsolutions starting below supersolutions remain below them while
  both exist. In particular distinct scalar solution trajectories cannot cross.

## Linear systems, periodic coefficients, and boundary problems

* **13. Fundamental matrices.** For continuous $A(t)$, the solution
  space of $\dot x=A(t)x$ has dimension $n$. A fundamental matrix
  $\Phi$ is invertible everywhere, and the evolution is
  $U(t,s)=\Phi(t)\Phi(s)^{-1}$.
* **65. Regular singular points.** For $zY'=A(z)Y$ with analytic $A$,
  a fundamental solution admits convergent power-series factors and
  powers $z^\lambda$ with possible logarithmic factors determined by
  resonances. Analytic continuation around the singular point gives
  the monodromy operator.
* **14. Variation of constants.** For $\dot x=A(t)x+f(t)$,
  $x(t)=U(t,s)x(s)+\int_s^tU(t,\tau)f(\tau)d\tau$.
* **15. Liouville's formula.**
  $\det U(t,s)=\exp(\int_s^t\mathop{\mathrm{tr}}A(\tau)d\tau)$.
  For a nonlinear flow the same formula applies with
  $A(t)=DF(\varphi_t(x))$, determining volume distortion.
* **16. Constant coefficients and spectral stability.** Solutions of
  $\dot x=Ax$ are $e^{tA}x_0$. Exponential asymptotic stability is
  equivalent to all eigenvalues having negative real part.
  Lyapunov stability holds exactly when all eigenvalues have
  nonpositive real part and those on the imaginary axis are semisimple.
* **17. Floquet theorem.** If $A(t+T)=A(t)$, a fundamental matrix
  has the form $P(t)e^{tB}$ with complex $T$-periodic $P$.
  For real $A$, a real factorization can be obtained with $2T$-periodic
  $P$. The eigenvalues of $U(T,0)$ are the Floquet multipliers.
* **18. Floquet stability criterion.** A periodic linear system is
  exponentially stable exactly when every multiplier has modulus below
  one. It is stable exactly when multipliers have modulus at most one
  and the unit-modulus multipliers are semisimple.
* **19. Exponential dichotomy.** A dichotomy splits the evolution into
  uniformly exponentially decaying forward stable and backward unstable
  parts. On the whole real line it gives a unique bounded solution
  for every bounded forcing through the stable–unstable Green operator.
* **20. Sturm separation and comparison.** For real scalar
  second-order equations in regular Sturm–Liouville form, zeros of
  linearly independent solutions at the same spectral parameter interlace.
  Increasing the spectral parameter increases oscillation in the usual
  comparison sense when the weight and leading coefficient are positive.
* **21. Regular Sturm–Liouville spectrum.** On a compact interval with
  positive continuous leading coefficient and weight, real continuous
  potential, and separated self-adjoint regular boundary conditions,
  the eigenvalues are real, simple, discrete, bounded below, and tend
  to infinity. Eigenfunctions form an orthonormal basis in weighted $L^2$.
  For $-(pu')'+qu=\lambda wu$ the eigenvalues satisfy
  $\lambda_k\sim(k\pi/L)^2$ as $k\to\infty$, where
  $L=\int_a^b\sqrt{w/p}$.
  Singular endpoints, the Weyl limit-point/limit-circle alternative, and
  the Weyl–Titchmarsh function are stated in Section 22 (SYNOPSIS22,
  items 52 and 55).
* **22. Sturm oscillation.** With those hypotheses, the eigenfunction
  for the $(k+1)$st eigenvalue has exactly $k$ interior zeros, all simple.

## Stability, invariant manifolds, and limit sets

An equilibrium is **Lyapunov stable** if every neighborhood contains a
smaller neighborhood whose positive trajectories remain in the first; it is
**asymptotically stable** if nearby trajectories also converge to it.
A **hyperbolic equilibrium** has no eigenvalue of $DF$ on the imaginary axis.

* **23. Linearized stability and instability.** For $C^1$ fields, a
  linearization with all eigenvalues in the left half-plane gives local
  exponential stability. Any eigenvalue with positive real part gives
  instability. Purely imaginary or zero eigenvalues require further analysis.
* **24. Lyapunov's direct theorem.** A positive definite $C^1$ function
  $V$ with $\dot V=\nabla V\cdot F\leq0$ near an equilibrium proves
  stability. Strict negative definiteness of $\dot V$ proves asymptotic
  stability. Proper global versions give global conclusions when solutions exist.
  Conversely, an asymptotically stable equilibrium of a locally Lipschitz
  field has a smooth strict Lyapunov function on its basin
  (Massera, Kurzweil).
* **25. Quadratic Lyapunov equations.** A real matrix $A$ is Hurwitz
  exactly when, for every positive definite $Q$, the equation
  $A^TP+PA=-Q$ has a unique positive definite solution,
  $P=\int_0^\infty e^{tA^T}Qe^{tA}dt$.
* **26. LaSalle invariance principle.** On a compact positively invariant
  set where $\dot V\leq0$, every trajectory approaches the largest
  invariant subset of $\{\dot V=0\}$.
* **27. Stable and unstable manifolds.** At a hyperbolic equilibrium
  of a $C^r$ field, $r\geq1$, there are local $C^r$ invariant stable
  and unstable manifolds tangent to the corresponding spectral subspaces.
  They consist locally of the trajectories converging exponentially
  in positive and negative time respectively.
* **28. Hartman–Grobman theorem.** Near a hyperbolic equilibrium, the
  nonlinear flow is locally topologically conjugate to its linearization.
  The conjugacy need not be differentiable. If no resonance
  $\lambda_j=\alpha\cdot\lambda$, $|\alpha|\geq2$, holds, a $C^\infty$
  field is locally $C^\infty$-linearizable (Sternberg); in the plane a
  $C^2$ field is $C^1$-linearizable at a hyperbolic equilibrium (Hartman).
* **29. Center manifolds.** For any fixed finite differentiability order,
  a sufficiently smooth vector field has a local center manifold tangent
  to its center spectral subspace. It contains all sufficiently small
  full trajectories that stay nearby for all time, and is generally nonunique.
* **30. Reduction principle.** If all noncenter eigenvalues are stable,
  stability or asymptotic stability of the equilibrium for the reduced
  center-manifold dynamics implies the corresponding stability in the
  full system. Instability of the reduced dynamics implies instability.
* **31. Normal hyperbolicity.** A compact invariant submanifold whose
  transverse contraction and expansion dominate its tangent dynamics
  persists under small smooth perturbations. Stable and unstable
  foliations persist with regularity controlled by the domination inequalities.
* **32. Omega-limit sets.** A precompact positive orbit of a continuous
  flow has a nonempty compact connected invariant omega-limit set.
  The orbit approaches that set; the analogous assertion holds backward in time.
* **33. Gradient dynamics.** Along $\dot x=-\nabla V$, one has
  $\dot V=-|\nabla V|^2$. A precompact orbit has omega-limit set
  contained in the critical set of $V$; if that critical set is discrete
  in the relevant compact region, the trajectory converges to one equilibrium.
  For real-analytic $V$ every precompact orbit converges to a single
  critical point (Łojasiewicz gradient inequality), although smooth
  counterexamples exist.

## Periodic orbits and planar dynamics

* **34. Poincaré return maps.** Near a periodic orbit, a transverse
  section has a smooth local return map. Nearby periodic trajectories
  correspond to its periodic points, and orbital stability is governed
  by the fixed point of the first-return map.
* **35. Nontrivial Floquet multipliers.** The full variational equation
  along a periodic orbit has a multiplier one in the flow direction.
  The remaining multipliers are the eigenvalues of the return-map derivative.
* **36. Stability and persistence of periodic orbits.** If all nontrivial
  multipliers have modulus below one, the orbit is orbitally exponentially
  asymptotically stable. A multiplier outside the unit circle gives
  instability. If none lies on the unit circle, the orbit persists
  uniquely nearby under small perturbation, up to phase.
* **37. Planar divergence formula.** For a planar periodic orbit
  $\gamma$ of period $T$, the nontrivial multiplier is
  $\exp(\int_0^T\mathop{\mathrm{div}}F(\gamma(t))dt)$.
* **38. Poincaré–Bendixson theorem.** A nonempty compact omega-limit
  set of a $C^1$ planar flow containing no equilibrium is a periodic orbit.
  If it contains only finitely many equilibria, it is an equilibrium, a
  periodic orbit, or a finite union of equilibria and orbits connecting
  them. The same holds on the sphere.
* **39. Bendixson–Dulac criterion.** On a simply connected planar domain,
  if $\mathop{\mathrm{div}}(BF)$ has one sign and is not identically zero
  on any open subset, for a $C^1$ scalar multiplier $B$, there is no
  periodic orbit lying in the domain.
* **40. Planar index theorem.** A simple periodic orbit has vector-field
  index one. If it encloses finitely many isolated equilibria, their
  indices sum to one. A nondegenerate saddle has index $-1$;
  nondegenerate nodes and foci have index $+1$.
* **41. Trapping annuli.** A compact positively invariant planar annulus
  containing no equilibrium contains a periodic orbit: apply
  Poincaré–Bendixson to a positive trajectory in the annulus.
* **42. One-degree-of-freedom Hamiltonian systems.** For
  $\dot q=\partial_pH$, $\dot p=-\partial_qH$, energy is conserved.
  A compact connected regular energy curve is a periodic orbit;
  separatrices can occur at critical energy levels.

## Normal forms, local bifurcations, and averaging

A **bifurcation** is a parameter value at which the local qualitative
orbit structure changes. Nondegeneracy hypotheses in these theorems exclude
higher-codimension cases; center-manifold reduction applies to higher-dimensional
systems with the stated simple critical spectrum.

* **43. Poincaré–Dulac normal forms.** Near an equilibrium of a smooth
  vector field, polynomial
  changes of variables eliminate nonresonant terms to any fixed finite
  order. For eigenvalues $\lambda_j$, the monomial $x^\alpha e_j$
  is resonant when $\lambda_j=\alpha\cdot\lambda$.
  Formal normal-form existence does not itself assert convergence.
  For analytic fields, nonresonant eigenvalues whose convex hull omits $0$
  (Poincaré domain) give convergent linearization (Poincaré); in the
  Siegel domain a Diophantine condition (Siegel), more generally the
  Brjuno condition (Brjuno), suffices.
* **44. Saddle-node bifurcation.** For scalar $\dot x=f(x,\mu)$,
  $f=f_x=0$, $f_{xx}\ne0$, $f_\mu\ne0$ at the origin give the
  local orbit structure of $\dot y=\nu\pm y^2$: two equilibria
  coalesce and disappear across the critical parameter.
* **45. Transcritical bifurcation.** If $f(0,\mu)=0$,
  $f_x(0,0)=0$, $f_{x\mu}(0,0)\ne0$, and $f_{xx}(0,0)\ne0$,
  two equilibrium branches cross and exchange stability, as in
  $\dot y=\nu y-y^2$.
* **46. Symmetric pitchfork bifurcation.** For odd $f$ in $x$,
  $f_x(0,0)=0$, $f_{x\mu}(0,0)\ne0$, and $f_{xxx}(0,0)\ne0$,
  the local structure is $\dot y=\nu y\pm y^3$.
  Two symmetric nonzero equilibria branch from the persistent zero solution.
* **47. Hopf bifurcation.** A simple conjugate pair crossing the imaginary
  axis transversely at $\pm i\omega$, $\omega>0$, with no other
  imaginary spectrum and nonzero first Lyapunov coefficient, produces
  a branch of small periodic orbits. Their amplitude is of order
  $\sqrt{|\mu|}$; the cubic normal-form coefficient determines the
  side of existence and radial stability.
* **48. Period doubling.** A simple return-map multiplier crossing
  $-1$, with the standard nonzero parameter derivative and cubic
  coefficient and no other unit-circle spectrum, gives a branch of
  two-cycles. For a flow these are periodic orbits of approximately
  twice the original period.
* **72. Bogdanov–Takens bifurcation.** Let a planar system with two
  parameters have at $\mu=0$ an equilibrium with a double zero eigenvalue
  and nonzero (nilpotent) linear part. Under two nondegeneracy conditions
  on the quadratic terms and a transversality condition in the parameters,
  it is locally topologically equivalent to an unfolding of
  $\dot y_1=y_2$, $\dot y_2=\beta_1+\beta_2y_1+y_1^2+sy_1y_2$,
  $s=\pm1$ (Bogdanov, Takens). Its bifurcation set near $\beta=0$ consists
  of a saddle-node curve, a Hopf curve, and a curve of saddle homoclinic
  orbits, all emanating from the origin.
* **49. First-order averaging.** For smooth $T$-periodic $f$ in
  $\dot x=\varepsilon f(t,x)$, solutions remain $O(\varepsilon)$
  close to those of $\dot y=\varepsilon\bar f(y)$ over times
  $O(\varepsilon^{-1})$, while both stay in a fixed controlled compact
  domain and start $O(\varepsilon)$ close. Here
  $\bar f=T^{-1}\int_0^Tf(t,\cdot)dt$.
  Equivalently, for each fixed $L>0$, $|x-y|\leq C_L\varepsilon$ for
  $0\leq t\leq L/\varepsilon$.
* **50. Periodic solutions from averaging.** A nondegenerate zero of
  $\bar f$ gives a nearby $T$-periodic solution for small nonzero
  $\varepsilon$. Hyperbolicity of that zero determines its stability
  through the averaged linearization.
  When the relevant eigenvalues $\lambda_j$ of the averaged linearization
  are simple, the Floquet multipliers are
  $1+\varepsilon T\lambda_j+O(\varepsilon^2)$.
* **51. Melnikov criterion.** For a smooth periodically perturbed planar
  Hamiltonian system with an unperturbed homoclinic orbit $z_0(t)$
  to a hyperbolic saddle, the first-order splitting is measured by
  $M(t_0)=\int_{-\infty}^{\infty}\nabla H(z_0(t))\cdot
  g(z_0(t),t+t_0)dt$. A simple zero of $M$ gives a transverse
  homoclinic intersection for sufficiently small perturbation.

## Hyperbolicity and complex orbit structure

A compact invariant set of a diffeomorphism is **hyperbolic** if its tangent
bundle splits continuously into invariant uniformly contracting and expanding
bundles. For flows without equilibria, include the one-dimensional flow direction.

* **52. Hyperbolic stable manifolds.** Each point of a hyperbolic set
  has local stable and unstable manifolds tangent to the invariant
  bundles, with uniform exponential contraction and expansion estimates.
* **53. Shadowing lemma.** Every sufficiently accurate pseudo-orbit
  near a compact hyperbolic set is uniformly close to an actual orbit.
  On a locally maximal hyperbolic set the shadowing orbit can be taken
  in the set. For flows one allows a small time reparametrization.
* **54. Hyperbolic continuation.** A compact locally maximal hyperbolic
  set of a diffeomorphism has a conjugate continuation under small
  $C^1$ perturbations. Anosov diffeomorphisms are structurally stable;
  Anosov flows have the corresponding orbital stability.
* **55. Hyperbolic closing lemma.** A sufficiently close return in a
  compact hyperbolic set is shadowed by a nearby periodic orbit,
  in the locally maximal setting. For a flow the period may change slightly.
* **56. Smale–Birkhoff homoclinic theorem.** A transverse homoclinic
  point of a hyperbolic periodic point yields, for an iterate, a compact
  invariant horseshoe conjugate to the full shift on two symbols.
  There are consequently infinitely many periodic orbits and positive
  topological entropy.
* **73. Shilnikov saddle-focus theorem.** Let a smooth three-dimensional
  flow have a saddle-focus equilibrium with eigenvalues $\lambda_1>0$
  and $-\rho\pm i\omega$, $\omega\ne0$, and a homoclinic orbit to it.
  If $0<\rho<\lambda_1$, every neighbourhood of the homoclinic loop
  contains infinitely many saddle periodic orbits and, for the return map,
  horseshoes conjugate to shifts; this persists for small perturbations
  that need not preserve the homoclinic orbit (Shilnikov).
* **57. Markov partitions.** Compact locally maximal hyperbolic sets
  admit finite Markov partitions of arbitrarily small diameter.
  The resulting symbolic system is a subshift of finite type mapping
  onto the hyperbolic set by a finite-to-one semiconjugacy.
* **58. Spectral decomposition.** The nonwandering set in a compact
  locally maximal hyperbolic set decomposes into finitely many basic
  pieces on which the dynamics is transitive; each has a finite cyclic
  decomposition for which an iterate is topologically mixing.

* **59. Structural stability.** Morse–Smale vector fields on a closed
  manifold (finitely many hyperbolic equilibria and periodic orbits
  forming the nonwandering set, with transverse stable and unstable
  manifolds) are structurally stable (Palis–Smale). On closed orientable
  surfaces they are exactly the structurally stable $C^1$ fields and form
  an open dense set (Peixoto). A $C^1$ diffeomorphism of a closed manifold
  is structurally stable exactly when it satisfies Axiom A and the strong
  transversality condition (Robbin, Robinson, Mañé).

## One-dimensional dynamics

* **60. Sharkovskii theorem.** Order the positive integers as
  $3\rhd5\rhd7\rhd\cdots\rhd2\cdot3\rhd2\cdot5\rhd\cdots\rhd
  2^2\cdot3\rhd\cdots\rhd2^3\rhd2^2\rhd2\rhd1$. If a continuous map of
  an interval has a periodic point of least period $m$ and $m\rhd n$,
  it has one of least period $n$. Every tail of the ordering is the set
  of periods of some continuous map; in particular period three implies
  all periods.
* **61. Circle homeomorphisms.** An orientation-preserving homeomorphism
  $f$ of $\mathbb R/\mathbb Z$ with lift $F$ has rotation number
  $\rho(f)=\lim_n(F^n(x)-x)/n\bmod1$, independent of $x$ and continuous
  in $f$. It is rational exactly when $f$ has a periodic orbit. If
  $\rho(f)$ is irrational, $f$ is semiconjugate to the rotation by
  $\rho(f)$, and conjugate to it when $f$ is a $C^1$ diffeomorphism with
  $f'$ of bounded variation (Denjoy); $C^1$ examples with wandering
  intervals exist.

## Hamiltonian structure and further continuations

Integrable systems and action–angle coordinates (Liouville–Arnold) are
stated in Section 51 (SYNOPSIS51, item 35).

* **62. Symplectic and volume preservation.** A Hamiltonian flow preserves
  the symplectic form and hence Liouville volume, as well as its autonomous
  Hamiltonian. A volume-preserving flow has no asymptotically stable
  equilibrium or periodic orbit.
* **64. KAM persistence.** Let $H_0(I)$ be analytic with
  $\det\partial_I^2H_0\ne0$ on a bounded action domain.
  A sufficiently small analytic perturbation preserves invariant
  Lagrangian tori with prescribed Diophantine unperturbed frequencies
  $|k\cdot\omega|\geq\gamma|k|^{-\tau}$, $\tau>n-1$, away from
  the domain boundary. The surviving Cantor family has positive measure,
  and its relative measure tends to one as the perturbation tends to zero
  with suitably shrinking $\gamma$.
* **68. Poincaré–Birkhoff theorem.** Let $f$ be an orientation- and
  area-preserving homeomorphism of the closed annulus
  $\mathbb R/\mathbb Z\times[0,1]$, preserving each boundary circle,
  with a lift that moves the two boundary circles in opposite directions.
  Then $f$ has at least two fixed points (Birkhoff; Brown–Neumann).
  Consequently, for each rational $p/q$ strictly between the rotation
  numbers of the boundary circles, $f$ has at least two periodic orbits
  of rotation number $p/q$.
* **69. Moser twist theorem.** Let
  $f(\theta,r)=(\theta+\alpha(r)+F(\theta,r),\,r+G(\theta,r))$ on
  $\mathbb R/\mathbb Z\times[a,b]$, with $\alpha'\geq\nu>0$ (twist),
  and suppose every closed curve near a circle $r=\mathrm{const}$
  meets its image (for example $f$ exact area-preserving). For each
  $\omega\in(\alpha(a),\alpha(b))$ with
  $|\omega-p/q|\geq\gamma q^{-\tau}$ for all $p/q$, $\tau>2$, there is
  $\varepsilon>0$ such that $\|F\|_{C^\ell}+\|G\|_{C^\ell}<\varepsilon$,
  $\ell$ large enough, gives an $f$-invariant closed curve
  $r=u(\theta)$ on which $f$ is conjugate to rotation by $\omega$
  (Moser; $\ell>3$ suffices by Rüssmann and Herman).
* **70. Stability of elliptic fixed points.** An elliptic fixed point of a
  smooth area-preserving planar map, with eigenvalues
  $e^{\pm2\pi i\theta}$, $e^{2\pi ik\theta}\ne1$ for $k=1,2,3,4$, and
  nonzero first Birkhoff twist coefficient, is surrounded by invariant
  closed curves accumulating on it and is therefore Lyapunov stable
  (Moser). For isoenergetically nondegenerate near-integrable systems
  with two degrees of freedom, KAM tori likewise confine orbits on each
  energy level (Arnold).
* **71. Nekhoroshev theorem.** Let $H(I,\varphi)=h(I)+\varepsilon f(I,\varphi)$
  be real analytic on a complex neighbourhood of
  $B\times\mathbb T^n$, $B\subset\mathbb R^n$ bounded, with $h$ steep,
  for example strictly convex. Then there are $a,b,C,\varepsilon_0>0$
  such that for $0<\varepsilon<\varepsilon_0$ every solution satisfies
  $|I(t)-I(0)|\leq C\varepsilon^b$ for
  $|t|\leq C\exp(C^{-1}\varepsilon^{-a})$, as long as it stays over $B$.
  For convex $h$ one may take $a=b=1/(2n)$ (Lochak, Pöschel). For $n\geq3$
  invariant tori do not separate energy levels, and actions can drift
  over longer times (Arnold diffusion).
* **66. Global attractor criterion.** A continuous semiflow on a complete
  metric space with a bounded absorbing set and asymptotic compactness
  has a compact invariant global attractor attracting every bounded set.
  It consists of points on bounded complete trajectories.
* **67. Delay-equation solution spaces.** For a fixed delay $r>0$,
  a locally Lipschitz equation $\dot x(t)=F(x_t)$, with
  $x_t(\theta)=x(t+\theta)$ on $[-r,0]$, defines a continuous local
  semiflow on $C([-r,0],\mathbb R^n)$. Its linearization is governed
  by a characteristic equation with generally infinitely many roots;
  finite-dimensional ODE phase space is replaced by a history space.

## Reference guide

Coddington–Levinson, Hartman, Hale, and Teschl share the existence, linear,
and stability foundations. Perko, Chicone, Hirsch–Smale–Devaney, and
Hale–Koçak supply the finite-dimensional qualitative and planar core.
Kuznetsov, Wiggins, and Guckenheimer–Holmes develop the bifurcation and
perturbation results, including the Bogdanov–Takens and Shilnikov theorems.
Katok–Hasselblatt and Robinson give the hyperbolic and symbolic theory;
Arnold and the Hamiltonian references give the integrable and KAM
continuation, and Siegel–Moser, Moser–Zehnder, Meyer–Offin, and
Arnold–Kozlov–Neishtadt the twist-map, Moser stability, and Nekhoroshev
results. The concluding results indicate the
recurring boundary-value, analytic, delay, and dissipative directions without
attempting a full account of each research specialization.

Local source copies consulted:

* [Perko, *Differential Equations and Dynamical Systems*](References/Perko2001DifferentialEquationsDynamicalSystems-SpringerTextsAM07.pdf).
* [Chicone, *Ordinary Differential Equations with Applications*](References/Chicone1999OrdinaryDifferentialEquationsApplications-SpringerTextsAM34.pdf).
* [Hale–Koçak, *Dynamics and Bifurcations*](References/HaleKoçak1991DynamicsBifurcations-SpringerTextsAM03.pdf).
* [Katok–Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*](References/KatokHasselblatt1995IntroductionModernTheoryDynamicalSystems-CambridgeEMA54.pdf).
* [Sanders–Verhulst–Murdock, *Averaging Methods in Nonlinear Dynamical Systems*](References/SandersVerhulstMurdock2007AveragingMethodsNonlinearDynamicalSystems2ndEd-SpringerAMS59.pdf).
* [Smith, *An Introduction to Delay Differential Equations with Applications to the Life Sciences*](References/Smith2011DelayDifferentialEquationsApplicationsLifeSciences-Springer.TAM57.pdf).

The author's freely accessible edition of Teschl's *Ordinary Differential
Equations and Dynamical Systems*,
especially Chapters 4–5 and Section 8.6, was also consulted for the
regular-singular, Sturm–Liouville, and Hamiltonian continuation.

The regular-singular, KAM, attractor, and delay statements are shared
continuations in the dedicated references, beyond the scope of a basic
planar-dynamics course.
