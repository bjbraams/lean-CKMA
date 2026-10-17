# Synopsis: Elliptic operators on manifolds, index theory, and spectral geometry

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects recurring content from Section 53 of
[CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md).
The central connections are between elliptic estimates and topology,
heat asymptotics and characteristic classes, and the spectrum and geometry
of a manifold. Sections 22, 30, and 52 supply complementary operator,
microlocal, and curvature theories. Boundary conditions, noncompact ends,
and coverings require separate hypotheses and are identified explicitly.

Unless specified otherwise, $M$ is a smooth closed connected Riemannian
$n$-manifold and vector bundles are smooth Hermitian bundles with compatible
connections. Write $\Delta_k=dd^*+d^*d$ for the nonnegative Hodge
Laplacian and $\Delta=\Delta_0=-\operatorname{div}\nabla$ on functions.
Scalar eigenvalues are $0=\lambda_0^2<\lambda_1^2\leq\cdots$,
counted with multiplicity; thus $\lambda$ denotes frequency, not energy.
Characteristic forms use the usual Chern–Weil normalization, so that
$\operatorname{ch}(E)=\operatorname{tr}\exp(iF^E/(2\pi))$ and
their cohomology classes are independent of the chosen connections.

## Elliptic operators and global analysis

* **1. Principal symbol.** An order-$m$ differential operator
  $P:C^\infty(E)\to C^\infty(F)$ has a homogeneous bundle symbol
  $\sigma_m(P)(x,\xi)$. Ellipticity means this is invertible for
  every $\xi\ne0$; composition multiplies principal symbols.
* **2. Parametrix theorem.** An elliptic classical operator has a
  pseudodifferential parametrix $Q$ of order $-m$ with $QP-I$
  and $PQ-I$ smoothing. Its principal symbol is $\sigma_m(P)^{-1}$.
* **3. Elliptic regularity.** If $Pu\in H^s$ distributionally,
  then $u\in H^{s+m}$ locally. In particular distributional
  nullsolutions are smooth; the same conclusion holds globally on a
  closed manifold.
* **4. Global estimate.** For each $s$ and a fixed sufficiently
  low Sobolev order $-N$,
  $\|u\|_{H^{s+m}}\leq C(\|Pu\|_{H^s}+\|u\|_{H^{-N}})$.
  On the complement of the kernel one can remove the lower-order term
  after choosing compatible Hilbert-space realizations.
* **5. Fredholm alternative.** The map
  $P:H^{s+m}(E)\to H^s(F)$ is Fredholm. Its kernel and cokernel
  are finite-dimensional smooth spaces, and
  $Pu=f$ is solvable precisely when $f$ annihilates $\ker P^*$.
* **6. Index stability.** The integer
  $\operatorname{ind}P=\dim\ker P-\dim\ker P^*$ is independent
  of Sobolev order, invariant under continuous elliptic deformations,
  and unchanged by lower-order perturbations. Indices add under
  composition and direct sum.
* **7. Symbol class.** The invertible symbol away from the zero
  section defines $[\sigma(P)]\in K_c^0(T^*M)$. Homotopic
  symbol classes have the same analytic index; stabilization by trivial
  invertible operators does not change that class.
* **8. Self-adjoint realizations.** A symmetric elliptic differential
  operator on a closed manifold is essentially self-adjoint on smooth
  sections, with domain $H^m$ for positive order $m$. Its resolvent
  is compact and its eigensections are smooth.
* **9. Complete Dirac operators.** A symmetric Dirac-type operator
  on a complete manifold is essentially self-adjoint on compactly
  supported smooth sections. Compact resolvent and a finite-dimensional
  kernel do not follow from completeness alone.
* **10. Spectral decomposition.** A positive elliptic operator on a
  closed manifold has a complete orthonormal eigenbasis with eigenvalues
  tending to infinity. Its heat operator is smoothing and trace class
  for positive time.
* **11. Complex powers.** For a strictly positive elliptic operator
  $P$ of order $m$, spectral powers $P^z$ form a holomorphic
  family of classical pseudodifferential operators of order $m\operatorname{Re}z$,
  with leading symbol $\sigma_m(P)^z$. A kernel can be removed by
  restricting to its orthogonal complement or adding its projection.

## Elliptic complexes and Hodge theory

An elliptic complex consists of differential operators $d_j$ with
$d_{j+1}d_j=0$ whose symbol sequence is exact at nonzero covectors.
For the first-order complexes here, its Laplacians are
$L_j=d_j^*d_j+d_{j-1}d_{j-1}^*$.

* **12. Hodge theorem for elliptic complexes.** On a closed manifold,
  each complex cohomology class has a unique representative in
  $\ker L_j$. Thus all cohomology groups are finite-dimensional.
* **13. Orthogonal decomposition.** For differential forms,
  $\Omega^k=\mathcal H^k\oplus d\Omega^{k-1}\oplus
  d^*\Omega^{k+1}$, with smooth summands and orthogonality in
  $L^2$. The harmonic space $\mathcal H^k$ is naturally
  $H^k_{\mathrm{dR}}(M)$.
* **14. Green operator.** There is an order-$-2$ Green operator
  $G_k$ with $\Delta_kG_k=G_k\Delta_k=I-\Pi_k$, where
  $\Pi_k$ projects onto harmonic forms. It commutes with $d,d^*$
  in the appropriate degrees and gives explicit solutions of exact
  and coexact equations.
* **15. Hodge star and duality.** On an oriented manifold, the
  Hodge star identifies $\mathcal H^k$ with $\mathcal H^{n-k}$.
  The integration pairing on complementary de Rham degrees is
  nondegenerate, giving Poincaré duality and $b_k=b_{n-k}$.
* **16. Hodge theory with boundary.** On a compact manifold with
  smooth boundary, harmonic forms satisfying absolute conditions
  $\iota_\nu\alpha=\iota_\nu d\alpha=0$ represent
  $H^k(M)$; relative conditions
  $\nu^\flat\wedge\alpha=\nu^\flat\wedge d^*\alpha=0$
  represent $H^k(M,\partial M)$. The Hodge star exchanges the two.
* **17. Weitzenböck identity.** A Hodge Laplacian is
  $\nabla^*\nabla+\mathcal R_k$, with $\mathcal R_k$ an
  algebraic curvature action. Nonnegative $\mathcal R_k$ makes
  harmonic forms parallel; positive definiteness everywhere forces
  their vanishing.
* **18. Kähler Hodge decomposition.** On a compact Kähler
  manifold, $\Delta_d=2\Delta_{\bar\partial}=2\Delta_\partial$.
  Consequently $H^k(M;\mathbb C)=\bigoplus_{p+q=k}H^{p,q}(M)$
  and $h^{p,q}=h^{q,p}$.
* **19. Hard Lefschetz theorem.** For a compact Kähler manifold of
  complex dimension $d$, multiplication by $[\omega]^{d-k}$
  is an isomorphism $H^k(M;\mathbb C)\to H^{2d-k}(M;\mathbb C)$
  for $k\leq d$. The Lefschetz decomposition reduces cohomology
  to primitive classes.
* **20. Witten deformation and Morse inequalities.** For a Morse
  function $f$, $d_t=e^{-tf}de^{tf}$ has the same cohomology as
  $d$. Its degree-$k$ Laplacian has, for large $t$, one small
  eigenvalue per index-$k$ critical point, while the remaining spectrum
  is separated by a gap of order $t$. This yields the weak and strong
  Morse inequalities and the alternating Euler-characteristic identity.

## Heat coefficients, Weyl laws, and spectral invariants

* **21. Local heat expansion.** A Laplace-type operator on a
  closed manifold has a smooth heat kernel with diagonal expansion
  $K_t(x,x)\sim(4\pi t)^{-n/2}\sum_{j=0}^\infty t^ja_j(x)$,
  valid with all derivatives after finite truncation and the corresponding
  remainder bounds. Each coefficient is a universal local curvature expression.
* **22. Heat trace.** Integrating gives
  $\operatorname{Tr}e^{-tP}\sim(4\pi t)^{-n/2}
  \sum_jt^j\int_M\operatorname{tr}a_j(x)dV$.
  For the scalar Laplacian, $a_0=1$ and $a_1=R/6$.
* **23. First curvature invariants.** For the scalar Laplacian on
  a closed manifold, the integrated coefficient of $t^2$ inside
  the heat-trace brackets is
  $\tfrac1{360}\int(5R^2-2|\operatorname{Ric}|^2+
  2|\mathrm{Rm}|^2)dV$. The omitted pointwise divergence term
  integrates to zero.
* **24. Weyl law.** For
  $N(\Lambda)=\#\{j:\lambda_j\leq\Lambda\}$,
  $N(\Lambda)\sim(2\pi)^{-n}\omega_n\operatorname{Vol}(M)
  \Lambda^n$. More generally a positive scalar elliptic operator
  of order $m$ has counting asymptotic given by the cotangent
  volume of $\{\sigma_m(P)\leq1\}$ times $\Lambda^{n/m}$
  when its eigenvalues are counted by energy.
* **25. Local Weyl law.** The spectral projector satisfies
  $\sum_{\lambda_j\leq\Lambda}|\phi_j(x)|^2=
  (2\pi)^{-n}\omega_n\Lambda^n+O(\Lambda^{n-1})$
  uniformly in $x$. Inserting an order-zero pseudodifferential operator
  replaces the leading density by the integral of its principal symbol.
* **26. Sharp closed-manifold remainder.** On a smooth closed
  manifold, $N(\Lambda)=c_M\Lambda^n+O(\Lambda^{n-1})$.
  Large eigenspace multiplicities on the round sphere show that this
  remainder order cannot generally be improved.
* **27. Nonperiodic improvement.** If the set of periodic geodesics
  has Liouville measure zero in $S^*M$, the remainder is
  $o(\Lambda^{n-1})$. This conclusion is a dynamical refinement of
  the local wave-parametrix argument.
* **28. Two-term boundary Weyl law.** On a compact manifold with
  smooth boundary, if periodic billiard trajectories have measure zero,
  the Dirichlet and Neumann counting functions satisfy
  $N_{D/N}(\Lambda)=c_M\Lambda^n
  \mp\tfrac14(2\pi)^{-(n-1)}\omega_{n-1}
  \operatorname{Area}(\partial M)\Lambda^{n-1}
  +o(\Lambda^{n-1})$. The dynamical hypothesis is essential to
  this standard sharp two-term formulation.
* **29. Boundary heat term.** Without that billiard hypothesis, a
  smooth compact boundary still gives a full heat-trace expansion in
  half-integer powers. For the scalar Laplacian the first two terms are
  $(4\pi t)^{-n/2}[\operatorname{Vol}(M)
  \mp(\sqrt\pi/2)\operatorname{Area}(\partial M)t^{1/2}+O(t)]$
  for Dirichlet/Neumann conditions.
* **30. Spectral zeta function.** For a positive elliptic operator,
  $\zeta_P(s)=\sum_{\mu_j>0}\mu_j^{-s}$ converges initially
  in a right half-plane and extends meromorphically by the Mellin
  transform of its heat trace. It is regular at zero for classical
  elliptic differential operators on closed manifolds.
* **31. Zeta determinant and scaling.** The reduced determinant is
  $\det'P=\exp[-\zeta'_P(0)]$. For $c>0$,
  $\det'(cP)=c^{\zeta_P(0)}\det'P$; the kernel is omitted
  consistently in both zeta functions.
* **32. Eta invariant.** For a self-adjoint first-order elliptic
  differential operator on a closed manifold,
  $\eta_D(s)=\sum_{\mu\ne0}\operatorname{sign}(\mu)|\mu|^{-s}$
  has meromorphic continuation regular at zero. The reduced invariant
  is $\bar\eta(D)=(\eta_D(0)+\dim\ker D)/2$; one may also
  regard its value modulo integers.
* **33. Analytic torsion.** For an acyclic orthogonal flat bundle
  on a closed odd-dimensional manifold,
  $\log T_{\mathrm{RS}}=\tfrac12\sum_k(-1)^kk\zeta'_{\Delta_k}(0)$
  is independent of the Riemannian metric. With cohomology present,
  the natural invariant is a metric on the determinant line of cohomology.
* **34. Cheeger–Müller theorem.** Ray–Singer analytic torsion agrees
  with Reidemeister torsion for orthogonal flat bundles on closed
  manifolds, with the corresponding identification of determinant-line
  metrics in the nonacyclic case.

## Dirac operators and index theorems

A Clifford action satisfies $c(\xi)c(\eta)+c(\eta)c(\xi)
=-2\langle\xi,\eta\rangle I$. A compatible connection on a Clifford
module gives $D=\sum_jc(e^j)\nabla_{e_j}$. In even dimension the
spinor bundle splits as $S^+\oplus S^-$ and $D$ is odd.

* **35. Dirac symbol and square.** The symbol of $D$ is
  $ic(\xi)$, so $D$ is elliptic and $D^2$ is of Laplace type.
  A compatible Dirac operator is formally self-adjoint.
* **36. Spin obstruction.** An oriented real vector bundle admits
  a spin structure if and only if its second Stiefel–Whitney class
  vanishes. When structures exist, their isomorphism classes form a
  torsor for $H^1(M;\mathbb Z/2)$.
* **37. Classical Dirac realizations.** The de Rham operator
  $d+d^*$ on exterior forms is a Dirac operator with square
  $\Delta$. On a Kähler manifold the canonical spin-$c$ Dirac
  operator on $(0,*)$-forms is
  $\sqrt2(\bar\partial+\bar\partial^*)$.
* **38. Schrödinger–Lichnerowicz formula.** For spinors,
  $D^2=\nabla^*\nabla+R/4$. Twisting by $E$ adds the Clifford
  contraction of its curvature, so scalar-curvature positivity alone
  need not imply vanishing for an arbitrary twist.
* **39. Positive-scalar-curvature obstruction.** If $R\geq0$
  and is positive somewhere on a closed connected spin manifold,
  $\ker D=0$. In even dimension its $\widehat A$ genus is
  therefore zero; a nonzero spin index obstructs positive scalar curvature.
* **40. Friedrich inequality.** For a closed spin $n$-manifold,
  $n\geq2$, every Dirac eigenvalue satisfies
  $\mu^2\geq n\min R/[4(n-1)]$.
  Equality with positive lower bound gives a real Killing spinor and
  in particular an Einstein metric.
* **41. McKean–Singer identity.** For an odd self-adjoint Dirac
  operator on a graded bundle,
  $\operatorname{ind}D^+=\operatorname{Str}e^{-tD^2}$ for every
  $t>0$. Nonzero eigenvalues cancel between the two gradings.
* **42. Local index theorem.** For a twisted spin Dirac operator,
  the supertrace of the diagonal heat kernel, multiplied by $dV$,
  converges as $t\downarrow0$
  to the top-degree form $[\widehat A(TM,\nabla)\operatorname{ch}
  (E,\nabla^E)]_n$. Getzler rescaling identifies the local density
  and explains cancellation of the apparently divergent heat terms.
* **43. Atiyah–Singer theorem.** The analytic index of an elliptic
  operator on a closed manifold equals the topological pushforward
  $\operatorname{ind}_{\mathrm{top}}[\sigma(P)]\in K^0(\mathrm{pt})
  =\mathbb Z$. The pushforward is defined by embedding, the Thom
  isomorphism, and Bott periodicity; it depends only on the symbol class.
* **44. Spin index formula.** On a closed even-dimensional spin
  manifold,
  $\operatorname{ind}D_E^+=\langle\widehat A(TM)
  \operatorname{ch}(E),[M]\rangle$.
* **45. Spin-$c$ formula.** If the spin-$c$ determinant line is
  $L$, then
  $\operatorname{ind}D_E^+=\langle e^{c_1(L)/2}
  \widehat A(TM)\operatorname{ch}(E),[M]\rangle$.
* **46. Chern–Gauss–Bonnet theorem.** On a closed oriented
  even-dimensional manifold, the Euler characteristic is the integral
  of the Euler curvature form, the normalized Pfaffian of curvature.
  It is the index of the even-to-odd de Rham operator.
* **47. Hirzebruch signature theorem.** On a closed oriented
  $4k$-manifold, the signature of the middle-dimensional intersection
  form is $\langle L(TM),[M]\rangle$, the index of the signature
  operator with its chirality grading.
* **48. Hirzebruch–Riemann–Roch theorem.** For a holomorphic bundle
  $E$ on a compact complex manifold,
  $\sum_q(-1)^q\dim H^{0,q}(M,E)=
  \langle\operatorname{Td}(T^{1,0}M)\operatorname{ch}(E),[M]\rangle$.
* **49. Families index theorem.** A smooth family of elliptic
  operators over a compact parameter space has an index class in
  $K^0(B)$, even when kernel dimensions jump. For an even-dimensional
  spin fibration, its Chern character is the fiber integral
  $\int_{M/B}\widehat A(T(M/B))\operatorname{ch}(E)$.
* **50. Lefschetz fixed-point formula.** For a smooth self-map of
  a closed manifold with isolated nondegenerate fixed points,
  $\sum_k(-1)^k\operatorname{tr}(f^*:H^k(M)\to H^k(M))
  =\sum_{f(x)=x}\operatorname{sign}\det(I-df_x)$.
  Equivariant elliptic complexes have the analogous local fixed-set
  index formulas.

## Boundary operators, spectral flow, coverings, and positive bundles

* **51. Complementing boundary condition.** A smooth boundary
  problem for an elliptic operator is regular elliptic when its frozen
  boundary symbol is invertible on decaying solutions of the normal
  half-line equation. The resulting Sobolev estimates imply Fredholmness
  and regularity up to the boundary.
* **52. Calderón projector.** A first-order elliptic operator has a
  pseudodifferential projection onto its boundary Cauchy data. Its
  principal symbol is the projection onto decaying normal modes;
  this describes which boundary subspaces give elliptic realizations.
* **53. APS boundary condition.** For a product Dirac operator
  $D=c(du)(\partial_u+B)$ near the boundary, requiring
  $\Pi_{\geq0}(B)(s|_{\partial M})=0$ gives a nonlocal elliptic
  Fredholm problem. Zero modes require a specified convention or
  finite-dimensional boundary subspace.
* **54. Atiyah–Patodi–Singer formula.** In the product convention
  for this APS condition,
  $\operatorname{ind}D^+_{\mathrm{APS}}=
  \int_M\widehat A(TM)\operatorname{ch}(E)
  -[\eta_B(0)+\dim\ker B]/2$.
  For nonproduct geometry the local integral acquires a boundary
  transgression correction.
* **55. Spectral flow as index.** For a smooth periodic family
  $B_t$ of self-adjoint elliptic operators, spectral flow, counting
  crossings from negative to positive, equals the index of
  $\partial_t+B_t$ on the mapping torus. Interval formulations use
  the corresponding endpoint spectral boundary conditions.
* **56. Eta variation.** Along a smooth Dirac-type family with no
  zero crossing, the variation of reduced eta is given by local heat
  coefficients. Crossings add integer jumps, so eta modulo integers
  varies by the local transgression formula.
* **57. Cylindrical ends.** On an even-dimensional manifold with
  product cylindrical ends, a graded Dirac operator whose limiting
  tangential operators are invertible is Fredholm between its $L^2$
  Sobolev spaces. The index of $D^+$
  agrees with the APS index of a compact truncation. Tangential zero
  modes can put zero in the essential spectrum.
* **58. Atiyah's $L^2$ index theorem.** Lift an elliptic operator
  from a closed manifold to a regular covering with deck group
  $\Gamma$. The difference of the von Neumann dimensions of its
  two $L^2$ kernels equals the ordinary index downstairs. These
  dimensions can be finite even when the ordinary kernel dimensions
  upstairs are infinite.
* **59. Higher index and positive curvature.** Twisting the spin
  Dirac operator by the flat Mishchenko bundle of a regular
  $\Gamma$-covering gives an index in $K_*(C_r^*\Gamma)$.
  A positive-scalar-curvature metric makes the operator invertible and
  forces that index to vanish. This retains information lost by the
  scalar trace giving the ordinary or $L^2$ index.
* **60. Bergman kernel asymptotics.** Let $L$ be a positive
  Hermitian holomorphic line bundle on a compact complex
  $d$-manifold, normalized by $(i/2\pi)R^L=\omega$, and use
  volume $\omega^d/d!$. For the projection onto $H^0(M,L^p)$,
  $B_p(x,x)\sim p^d+b_1(x)p^{d-1}+\cdots$ in every $C^k$
  norm. Integration recovers Riemann–Roch growth, and the higher
  coefficient functions are local curvature invariants.

## Eigenvalue inequalities and nodal geometry

* **61. Min–max principle.** Eigenvalues of a semibounded
  self-adjoint elliptic realization with compact resolvent are the
  successive minima of its Rayleigh quotient over finite-dimensional
  subspaces of the quadratic-form domain. Dirichlet and Neumann
  conditions differ through those form domains.
* **62. Dirichlet domain monotonicity.** If
  $\Omega_1\subset\Omega_2$, then
  $\mu_j^D(\Omega_2)\leq\mu_j^D(\Omega_1)$ for eigenvalues
  counted by energy. The same inclusion monotonicity does not hold
  for general Neumann eigenvalues.
* **63. Hadamard variation.** For a simple Dirichlet eigenvalue
  $\mu$ and an $L^2$-normalized eigenfunction $u$, a smooth
  outward boundary velocity $V\cdot\nu$ gives
  $\mu'=-\int_{\partial\Omega}(\partial_\nu u)^2
  (V\cdot\nu)dS$. Multiple eigenvalues split according to the
  corresponding finite-dimensional quadratic form.
* **64. Faber–Krahn theorem.** Among bounded Euclidean domains
  of a fixed volume, the ball minimizes the first Dirichlet
  eigenvalue. For smooth connected domains, equality requires a ball.
* **65. Szegő–Weinberger theorem.** Among bounded connected smooth Euclidean
  domains of fixed volume, the ball maximizes the first positive
  Neumann eigenvalue. This is the counterpart of the Dirichlet
  minimization theorem with the opposite extremal direction.
* **66. Cheeger spectral bound.** On a closed connected manifold,
  $\lambda_1^2\geq h(M)^2/4$, with $h$ the separating
  area-to-volume isoperimetric constant. For Dirichlet domains use
  the corresponding domain Cheeger constant.
* **67. Curvature eigenvalue bound.** If
  $\operatorname{Ric}\geq(n-1)k g$, $k>0$, then
  $\lambda_1^2\geq nk$; equality characterizes the round sphere.
  Its proof combines the integrated Bochner formula with the Hessian
  inequality and the equality-case rigidity theorem.
* **68. Steklov spectrum.** On a compact connected manifold with
  smooth nonempty boundary, the Dirichlet-to-Neumann operator for
  harmonic functions is a nonnegative self-adjoint elliptic operator
  of order one, with principal symbol $|\xi|$.
  Its counting function is
  $N_S(\sigma)\sim(2\pi)^{-(n-1)}\omega_{n-1}
  \operatorname{Area}(\partial M)\sigma^{n-1}$ for $n\geq2$.
* **69. Courant nodal theorem.** The $j$th eigenfunction in an
  ordered real orthonormal basis, with eigenvalues indexed starting
  at one, has at most $j$ nodal domains. This formulation also
  covers multiplicities by fixing the ordered basis.
* **70. Unique continuation and vanishing order.** A nonzero
  Laplace eigenfunction cannot vanish on an open set or to infinite
  order at a point. Quantitatively, at frequency $\lambda\geq1$
  its vanishing order is at most $C_M\lambda$.
* **71. Analytic nodal-volume bounds.** On a closed real analytic
  manifold of dimension $n\geq2$, a real nonconstant eigenfunction
  satisfies $c_M\lambda\leq\mathcal H^{n-1}
  (\{\phi_\lambda=0\})\leq C_M\lambda$.
  The analytic upper bound is not a consequence of smooth elliptic
  regularity alone.
* **72. Sogge eigenfunction bounds.** For $\|\phi_\lambda\|_2=1$,
  $\|\phi_\lambda\|_p\leq C\lambda^{\delta(p)}$, $2\leq p\leq\infty$,
  where $\delta(p)=\max\{\tfrac{n-1}{2}(\tfrac12-\tfrac1p),
  n(\tfrac12-\tfrac1p)-\tfrac12\}$, $n\geq2$.
  Zonal functions and highest-weight harmonics on spheres show the
  sharpness of the two regimes.
* **73. Doubling estimate.** There are $C,r_0>0$ depending on
  the closed smooth manifold such that
  $\int_{B(x,2r)}|\phi_\lambda|^2\leq
  e^{C(1+\lambda)}\int_{B(x,r)}|\phi_\lambda|^2$
  for $0<r<r_0$. This controls small-scale concentration and
  implies the vanishing-order bound.

## Geodesic dynamics, trace formulas, and scattering

* **74. Semiclassical measures.** For normalized eigenfunctions with
  $h=\lambda^{-1}\to0$, subsequential limits of
  $\langle\operatorname{Op}_h(a)\phi_\lambda,\phi_\lambda\rangle$
  define probability measures on $S^*M$. These measures are invariant
  under geodesic flow, by the eigenfunction equation and the
  pseudodifferential commutator formula.
* **75. Egorov theorem.** Conjugation of an order-zero operator
  $A$ by the half-wave group $e^{it\sqrt\Delta}$ transports
  its principal symbol by geodesic flow, for each fixed time.
  Lower-order terms are determined by the symbol calculus.
* **76. Quantum ergodicity.** If the geodesic flow is ergodic with
  respect to Liouville measure, every orthonormal eigenbasis has a
  density-one subsequence whose expectations against all order-zero
  observables tend to the normalized Liouville average of their symbols.
  The theorem permits an exceptional density-zero subsequence.
* **77. Wave trace and lengths.** The distribution
  $\operatorname{Tr}e^{it\sqrt\Delta}$ is smooth away from zero
  and the signed lengths of closed geodesics. For clean nondegenerate
  families the leading singular terms are determined by the linearized
  return map and Maslov data. Cancellation can prevent an arbitrary
  closed-geodesic length from being visible as a singularity.
* **78. Selberg trace formula.** For a closed hyperbolic surface,
  write $\lambda_j^2=1/4+r_j^2$ and take an admissible even test
  function $h$, with $g(\ell)=(2\pi)^{-1}\int h(r)e^{-ir\ell}dr$.
  Then
  $\sum_jh(r_j)=\operatorname{Area}(M)(4\pi)^{-1}
  \int_{\mathbb R}r\tanh(\pi r)h(r)dr+
  \sum_{\gamma\ \mathrm{primitive}}\sum_{k\geq1}
  \ell_\gamma g(k\ell_\gamma)/(2\sinh(k\ell_\gamma/2))$.
  The primitive geodesics use the standard conjugacy-class convention;
  cusps introduce additional continuous-spectrum and scattering terms.
* **79. Hyperbolic resonances.** For an infinite-area convex-cocompact hyperbolic
  surface, the resolvent $(\Delta-s(1-s))^{-1}$ continues
  meromorphically from its initial half-plane as an operator from
  compactly supported smooth functions to smooth functions locally.
  Its finite-rank poles define resonances. The continuous spectrum is
  $[1/4,\infty)$, with only finitely many $L^2$ eigenvalues below
  $1/4$; poles on other sheets encode scattering rather than ordinary
  $L^2$ eigenfunctions.
* **80. Spectral information and nonuniqueness.** The scalar spectrum
  determines dimension, volume, integrated scalar curvature, and the
  higher integrated heat coefficients. It does not determine the
  isometry class: closed nonisometric isospectral manifolds exist,
  including flat tori in suitable dimensions and hyperbolic surfaces.

## Reference guide

Taylor, Warner, Nicolaescu, and Shubin share global elliptic estimates,
Fredholm theory, and Hodge theory. Gilkey, Roe, Berline–Getzler–Vergne,
and Lawson–Michelsohn develop the heat and index core, with Friedrich
emphasizing spinor estimates. Booss-Bavnbek–Wojciechowski and Melrose
provide the systematic boundary, spectral-flow, and cylindrical-end
continuations. Bleecker–Booss-Bavnbek gives several index constructions;
Higson–Roe, Willett–Yu, and Lück develop the operator-algebraic and
covering-space branches.

Chavel, Bérard, Levitin–Mangoubi–Polterovich, and Henrot share variational
spectral geometry. Ivrii, Sogge, and Zelditch supply sharp asymptotics,
wave methods, eigenfunction estimates, and geodesic dynamics. Bergeron,
Iwaniec, and Borthwick develop hyperbolic trace and scattering theories;
Ma–Marinescu develops positive-bundle heat and Bergman asymptotics.
Bismut–Lebeau gives the deeper analytic-torsion continuation. Specialized
higher-index conjectures, refined inverse problems, and flexibility theory
are outside the selected common core.

Local full-text sources consulted:

* [Taylor, *Partial Differential Equations I*, second edition](References/Taylor2011PartialDifferentialEquations1BasicTheory2ndEd-SpringerAMS115.pdf).
* [Taylor, *Partial Differential Equations II*, second edition](References/Taylor2011PartialDifferentialEquations2QualitativeStudies2ndEd-SpringerAMS116.pdf).
* [Shubin, *Pseudodifferential Operators and Spectral Theory*, second edition](References/Shubin2001PseudodifferentialOperatorsSpectralTheory2ndEd-Springer.pdf).
* [Lawson–Michelsohn, *Spin Geometry*](References/LawsonMichelsohn1989SpinGeometry-PrincetonUP.pdf).
* [Sogge, *Hangzhou Lectures on Eigenfunctions of the Laplacian*](References/Sogge2014HangzhouLecturesEigenfunctionsLaplacian-PrincetonAnnalsMathStud188.pdf).
* [Zelditch, *Eigenfunctions of the Laplacian on a Riemannian Manifold*, author copy](References/Zelditch2017EigenfunctionsLaplacianRiemannianManifold-AuthorCopy.AMS.CBMS125.pdf).
* [Ma–Marinescu, *Holomorphic Morse Inequalities and Bergman Kernels*](References/MaMarinescu2007HolomorphicMorseInequalitiesBergmanKernels-Birkhauser.PM254.pdf).
* [Lück, *L²-Invariants*](References/Luck2002L2Invariants-Springer.Ergeb44.pdf).
* [Bergeron, *The Spectrum of Hyperbolic Surfaces*](References/Bergeron2016SpectrumHyperbolicSurfaces-SpringerUTX.pdf).
* [Borthwick, *Spectral Theory of Infinite-Area Hyperbolic Surfaces*, second edition](References/Borthwick2016SpectralTheoryInfiniteAreaHyperbolicSurfaces2ndEd-Birkhauser.PM318.pdf).

Gilkey's [authorized electronic first edition](https://pages.uoregon.edu/gilkey/dirPDF/InvarianceTheory1Ed.pdf)
was consulted for the eta regularity and boundary-condition discussion;
it is distinct from later editions. The boundary index formula was also
checked against [Atiyah–Patodi–Singer, *Spectral Asymmetry and Riemannian Geometry I*](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/aps001.pdf).
For the spectral-flow/index correspondence, see also
[Robbin–Salamon, *The Spectral Flow and the Maslov Index*](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/robbsala1.pdf),
with the sign fixed here by the operator $\partial_t+B_t$.
These accessible sources supplement the boundary monographs named above.
