# Synopsis: Elliptic operators on manifolds, index theory, and spectral geometry

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-53);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring content from Section 53 of
[CKMA-bib.md](CKMA-bib.md#ckma-53).
The central connections are between elliptic estimates and topology,
heat asymptotics and characteristic classes, and the spectrum and geometry
of a manifold. Sections 22, 30, and 52 supply complementary operator,
microlocal, and curvature theories. Boundary conditions, noncompact ends,
and coverings require separate hypotheses and are identified explicitly.

The current neighbouring divisions identify heat kernels and diffusion as
[39B](CKMA-bib.md#ckma-39b) and complex-manifold and Kähler material as
[45B](CKMA-bib.md#ckma-45b)–[45C](CKMA-bib.md#ckma-45c). The [inverse-problems
route](CKMA-MSC2020.md#inverse-problems) links geometric tomography with
operator, integral, and PDE methods elsewhere.

Unless specified otherwise, $M$ is a smooth closed connected Riemannian
$n$-manifold and vector bundles are smooth Hermitian bundles with compatible
connections. Write $\Delta_k=dd^*+d^*d$ for the nonnegative Hodge
Laplacian and $\Delta=\Delta_0=-\mathop{\mathrm{div}}\nabla$ on functions.
Scalar eigenvalues are $0=\lambda_0^2<\lambda_1^2\leq\cdots$,
counted with multiplicity; thus $\lambda$ denotes frequency, not energy.
Characteristic forms use the usual Chern–Weil normalization, so that
$\mathop{\mathrm{ch}}(E)=\mathop{\mathrm{tr}}\exp(iF^E/(2\pi))$ and
their cohomology classes are independent of the chosen connections.

## Elliptic operators and global analysis

The pseudodifferential parametrix of an elliptic operator is SYNOPSIS30,
item 33.

* **1. Principal symbol.** An order-$m$ differential operator
  $P:C^\infty(E)\to C^\infty(F)$ has a homogeneous bundle symbol
  $\sigma_m(P)(x,\xi)$. Ellipticity means this is invertible for
  every $\xi\ne0$; composition multiplies principal symbols.
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
  The index depends only on the homotopy class of the principal symbol among
  elliptic symbols and vanishes for self-adjoint operators.
* **6. Index stability.** The integer
  $\mathop{\mathrm{ind}}P=\dim\ker P-\dim\ker P^*$ is independent
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
  family of classical pseudodifferential operators of order $m\mathop{\mathrm{Re}}z$,
  with leading symbol $\sigma_m(P)^z$. A kernel can be removed by
  restricting to its orthogonal complement or adding its projection.
  Spectral and pseudodifferential definitions agree.

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
  $\mathop{\mathrm{Tr}}e^{-tP}\sim(4\pi t)^{-n/2}
  \sum_jt^j\int_M\mathop{\mathrm{tr}}a_j(x)dV$.
  For the scalar Laplacian, $a_0=1$ and $a_1=R/6$.
* **23. First curvature invariants.** For the scalar Laplacian on
  a closed manifold, the integrated coefficient of $t^2$ inside
  the heat-trace brackets is
  $\tfrac1{360}\int(5R^2-2|\mathop{\mathrm{Ric}}|^2+
  2|\mathrm{Rm}|^2)dV$. The omitted pointwise divergence term
  integrates to zero.
* **24. Weyl law.** For
  $N(\Lambda)=\#\{j:\lambda_j\leq\Lambda\}$,
  $N(\Lambda)\sim(2\pi)^{-n}\omega_n\mathop{\mathrm{Vol}}(M)
  \Lambda^n$. More generally a positive scalar elliptic operator
  of order $m$ has counting asymptotic
  $(2\pi)^{-n}\mathop{\mathrm{vol}}\{(x,\xi)\in T^*M:\sigma_m(P)(x,\xi)\leq1\}\,\Lambda^{n/m}$
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
  The sharp remainder is due to Avakumović, Levitan, and Hörmander; for a
  positive classical elliptic operator of order $m$ with positive scalar
  principal symbol it is $O(\Lambda^{(n-1)/m})$ in the counting function of
  entry 24.
* **27. Nonperiodic improvement.** If the set of periodic geodesics
  has Liouville measure zero in $S^*M$, the remainder is
  $o(\Lambda^{n-1})$ (Duistermaat–Guillemin, Ivrii).
* **28. Two-term boundary Weyl law.** On a compact manifold with
  smooth boundary, if periodic billiard trajectories have measure zero,
  the Dirichlet and Neumann counting functions satisfy
  $N_{D/N}(\Lambda)=c_M\Lambda^n
  \mp\tfrac14(2\pi)^{-(n-1)}\omega_{n-1}
  \mathop{\mathrm{Area}}(\partial M)\Lambda^{n-1}
  +o(\Lambda^{n-1})$. The dynamical hypothesis is essential to
  this standard sharp two-term formulation.
* **29. Boundary heat term.** Without that billiard hypothesis, a
  smooth compact boundary still gives a full heat-trace expansion in
  half-integer powers. For the scalar Laplacian the first two terms are
  $(4\pi t)^{-n/2}[\mathop{\mathrm{Vol}}(M)
  \mp(\sqrt\pi/2)\mathop{\mathrm{Area}}(\partial M)t^{1/2}+O(t)]$
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
  $\eta_D(s)=\sum_{\mu\ne0}\mathop{\mathrm{sign}}(\mu)|\mu|^{-s}$
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
  $\mathop{\mathrm{ind}}D^+=\mathop{\mathrm{Str}}e^{-tD^2}$ for every
  $t>0$. Nonzero eigenvalues cancel between the two gradings.
* **42. Local index theorem.** For a twisted spin Dirac operator
  on an even-dimensional closed spin manifold,
  the supertrace of the diagonal heat kernel, multiplied by $dV$,
  converges as $t\downarrow0$
  to the top-degree form $[\widehat A(TM,\nabla)\mathop{\mathrm{ch}}
  (E,\nabla^E)]_n$, with the Chern–Weil normalization fixed above.
  Getzler rescaling identifies the local density
  and explains cancellation of the apparently divergent heat terms.
* **43. Atiyah–Singer theorem.** The analytic index of an elliptic
  operator on a closed manifold equals the topological pushforward
  $\mathop{\mathrm{ind}}_{\mathrm{top}}[\sigma(P)]\in K^0(\mathrm{pt})
  =\mathbb Z$. The pushforward is defined by embedding, the Thom
  isomorphism, and Bott periodicity; it depends only on the symbol class.
* **44. Spin index formula.** On a closed even-dimensional spin
  manifold,
  $\mathop{\mathrm{ind}}D_E^+=\langle\widehat A(TM)
  \mathop{\mathrm{ch}}(E),[M]\rangle$.
* **45. Spin-$c$ formula.** If the spin-$c$ determinant line is
  $L$, then
  $\mathop{\mathrm{ind}}D_E^+=\langle e^{c_1(L)/2}
  \widehat A(TM)\mathop{\mathrm{ch}}(E),[M]\rangle$.
* **46. Chern–Gauss–Bonnet theorem.** On a closed oriented
  even-dimensional manifold, the Euler characteristic is the integral
  of the Euler curvature form, the normalized Pfaffian of curvature.
  It is the index of the even-to-odd de Rham operator. For a compact
  surface with boundary, $\int_MK\,dA+\int_{\partial M}k_g\,ds=2\pi\chi(M)$;
  for a closed four-manifold,
  $\chi(M)=(32\pi^2)^{-1}\int(|\mathrm{Rm}|^2-4|\mathop{\mathrm{Ric}}|^2+R^2)dV$.
* **47. Hirzebruch signature theorem.** On a closed oriented
  $4k$-manifold, the signature of the middle-dimensional intersection
  form is $\langle L(TM),[M]\rangle$, the index of the signature
  operator with its chirality grading.
* **48. Hirzebruch–Riemann–Roch theorem.** For a holomorphic bundle
  $E$ on a compact complex manifold,
  $\sum_q(-1)^q\dim H^{0,q}(M,E)=
  \langle\mathop{\mathrm{Td}}(T^{1,0}M)\mathop{\mathrm{ch}}(E),[M]\rangle$.
* **49. Families index theorem.** A smooth family of elliptic
  operators over a compact parameter space has an index class in
  $K^0(B)$, even when kernel dimensions jump. For an even-dimensional
  spin fibration, its Chern character is the fiber integral
  $\int_{M/B}\widehat A(T(M/B))\mathop{\mathrm{ch}}(E)$.
* **50. Lefschetz fixed-point formula.** For a smooth self-map of
  a closed manifold with isolated nondegenerate fixed points,
  $\sum_k(-1)^k\mathop{\mathrm{tr}}(f^*:H^k(M)\to H^k(M))
  =\sum_{f(x)=x}\mathop{\mathrm{sign}}\det(I-df_x)$.
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
  $\mathop{\mathrm{ind}}D^+_{\mathrm{APS}}=
  \int_M\widehat A(TM)\mathop{\mathrm{ch}}(E)
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
* **84. Holomorphic Morse inequalities.** Let $L$ be a Hermitian
  holomorphic line bundle with Chern curvature $R^L$ on a compact complex
  $d$-manifold, $E$ a holomorphic vector bundle, and $M(q)$ the open set
  where $iR^L$ is nondegenerate with exactly $q$ negative eigenvalues.
  As $p\to\infty$,
  $\dim H^q(M,L^p\otimes E)\leq\mathop{\mathrm{rk}}(E)\frac{p^d}{d!}
  \int_{M(q)}(-1)^q(\tfrac i{2\pi}R^L)^d+o(p^d)$, with strong forms for
  alternating partial sums (Demailly). The proof localizes the low
  spectrum of the Kodaira Laplacian through the Bochner–Kodaira–Nakano
  formula and harmonic-oscillator models (Ma–Marinescu). For positive $L$,
  $M(q)=\emptyset$ for $q>0$, so higher cohomology is $o(p^d)$ and
  $\dim H^0(M,L^p\otimes E)\sim\mathop{\mathrm{rk}}(E)\frac{p^d}{d!}
  \int_M(\tfrac i{2\pi}R^L)^d$.

## Eigenvalue inequalities and nodal geometry

The min–max principle is SYNOPSIS22, item 27; the Cheeger, Faber–Krahn,
Szegő–Weinberger, and Lichnerowicz–Obata bounds are SYNOPSIS14, items 20–22
and 49.

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
* **68. Steklov spectrum.** On a compact connected manifold with
  smooth nonempty boundary, the Dirichlet-to-Neumann operator for
  harmonic functions is a nonnegative self-adjoint elliptic operator
  of order one, with principal symbol $|\xi|$.
  Its counting function is
  $N_S(\sigma)\sim(2\pi)^{-(n-1)}\omega_{n-1}
  \mathop{\mathrm{Area}}(\partial M)\sigma^{n-1}$ for $n\geq2$.
* **69. Courant nodal theorem.** The $j$th eigenfunction in an
  ordered real orthonormal basis, with eigenvalues indexed starting
  at one, has at most $j$ nodal domains. This formulation also
  covers multiplicities by fixing the ordered basis. For Dirichlet
  domains in the plane, Pleijel's theorem shows that equality holds for
  only finitely many $j$.
* **70. Unique continuation and vanishing order.** A nonzero
  Laplace eigenfunction cannot vanish on an open set or to infinite
  order at a point. Quantitatively, at frequency $\lambda\geq1$
  its vanishing order is at most $C_M\lambda$.
* **71. Analytic nodal-volume bounds.** On a closed real analytic
  manifold of dimension $n\geq2$, a real nonconstant eigenfunction
  satisfies $c_M\lambda\leq\mathcal H^{n-1}
  (\{\phi_\lambda=0\})\leq C_M\lambda$.
  (Donnelly–Fefferman). For smooth metrics the lower bound
  $c_M\lambda$ holds, and the upper bound is known only with a
  polynomial power $\lambda^{\alpha}$, $\alpha=\alpha(n)$ (Logunov).
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

Egorov's theorem for the propagation of symbols is SYNOPSIS30, item 50.

* **74. Semiclassical measures.** For normalized eigenfunctions with
  $h=\lambda^{-1}\to0$, subsequential limits of
  $\langle\mathop{\mathrm{Op}}_h(a)\phi_\lambda,\phi_\lambda\rangle$
  define probability measures on $S^*M$. These measures are invariant
  under geodesic flow, by the eigenfunction equation and the
  pseudodifferential commutator formula.
* **76. Quantum ergodicity.** If the geodesic flow is ergodic with
  respect to Liouville measure, every orthonormal eigenbasis has a
  density-one subsequence whose expectations against all order-zero
  observables tend to the normalized Liouville average of their symbols.
  The theorem permits an exceptional density-zero subsequence.
  (Shnirelman, Zelditch, Colin de Verdière.)
* **77. Wave trace and lengths.** The distribution
  $\mathop{\mathrm{Tr}}e^{it\sqrt\Delta}$ is smooth away from zero
  and the signed lengths of closed geodesics. For clean nondegenerate
  families the leading singular terms are determined by the linearized
  return map and Maslov data. Cancellation can prevent an arbitrary
  closed-geodesic length from being visible as a singularity.
* **78. Selberg trace formula.** For a closed hyperbolic surface,
  write $\lambda_j^2=1/4+r_j^2$ and take an admissible even test
  function $h$, with $g(\ell)=(2\pi)^{-1}\int h(r)e^{-ir\ell}dr$.
  Then
  $\sum_jh(r_j)=\mathop{\mathrm{Area}}(M)(4\pi)^{-1}
  \int_{\mathbb R}r\tanh(\pi r)h(r)dr+
  \sum_{\gamma\ \mathrm{primitive}}\sum_{k\geq1}
  \ell_\gamma g(k\ell_\gamma)/(2\sinh(k\ell_\gamma/2))$.
  The primitive geodesics use the standard conjugacy-class convention;
  cusps introduce additional continuous-spectrum and scattering terms.
  Consequences: the Laplace spectrum and the length spectrum with
  multiplicities determine each other (Huber), and the number of
  primitive closed geodesics of length at most $L$ is asymptotic to
  $e^L/L$ (prime geodesic theorem).
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
  including flat tori in suitable dimensions (Milnor) and hyperbolic
  surfaces, and Sunada's method produces isospectral pairs, among them
  nonisometric planar domains (Gordon–Webb–Wolpert).
* **81. Geodesic X-ray transform on simple manifolds.** A compact connected
  manifold with smooth boundary is *simple* if it is nontrapping, has
  strictly convex boundary, and has no conjugate points; equivalently,
  given strictly convex boundary, each $\exp_x$ is a diffeomorphism from
  its maximal domain onto $M$. For $f\in C^\infty(M)$ put
  $If(x,v)=\int_0^{\tau(x,v)}f(\gamma_{x,v}(t))dt$ on the inward-pointing
  unit vectors $\partial_+SM$, $\tau$ the exit time. On a simple manifold
  $\|f\|_{L^2(M)}\leq C\|If\|_{H^1(\partial_+SM)}$, so $I$ is injective; if
  $I(f+\alpha)=0$ for a $1$-form $\alpha$, then $f=0$ and $\alpha=dh$ with
  $h|_{\partial M}=0$ (Mukhometov, Anikonov–Romanov; Pestov energy
  identity). On simple surfaces solenoidal injectivity holds for symmetric
  tensors of every order (Paternain–Salo–Uhlmann).
* **82. Boundary rigidity.** The boundary distance function
  $d_g|_{\partial M\times\partial M}$ is unchanged by diffeomorphisms
  fixing $\partial M$. Two simple metrics on a compact surface with the
  same boundary distance function differ by such a diffeomorphism
  (Pestov–Uhlmann), and two conformal simple metrics with the same boundary
  distance function coincide in every dimension (Mukhometov, Croke).
  Simplicity cannot simply be dropped: enlarging a hemisphere metric in a
  small interior region leaves boundary distances unchanged. The
  linearized problem is solenoidal injectivity of $I$ on symmetric
  $2$-tensors (entry 81).
* **83. Anisotropic Calderón problem.** The Dirichlet-to-Neumann map
  $\Lambda_g$ of $\Delta_g$ (entry 68) is unchanged by diffeomorphisms
  fixing $\partial M$ and, in dimension two, by conformal factors equal
  to one on $\partial M$. For real-analytic compact connected $(M,g)$ of
  dimension $n\geq3$, $\Lambda_g$ determines $(M,g)$ up to isometry
  (Lee–Uhlmann, Lassas–Uhlmann); in dimension two it determines the
  conformal class (Lassas–Uhlmann). The smooth case for $n\geq3$ remains
  open in general.

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
Bismut–Lebeau gives the deeper analytic-torsion continuation.
Paternain–Salo–Uhlmann develop the geometric inverse problems of entries
81–83. Specialized higher-index conjectures, refined inverse problems beyond
those entries, and flexibility theory are outside the selected common core.

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

The first edition of Gilkey's *Invariance Theory, the Heat Equation, and the
Atiyah–Singer Index Theorem*
was consulted for the eta regularity and boundary-condition discussion;
it is distinct from later editions. The boundary index formula was also
checked against Atiyah–Patodi–Singer, *Spectral Asymmetry and Riemannian Geometry I* (Math. Proc.
Cambridge Philos. Soc. 1975).
For the spectral-flow/index correspondence, see also
Robbin–Salamon, *The Spectral Flow and the Maslov Index* (Bull. London Math.
Soc. 1995),
with the sign fixed here by the operator $\partial_t+B_t$.
These accessible sources supplement the boundary monographs named above.
