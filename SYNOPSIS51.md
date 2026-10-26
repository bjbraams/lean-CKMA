# Synopsis: Integrable systems and Riemann–Hilbert methods

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-51);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring content from Section 51 of
[CKMA-bib.md](CKMA-bib.md#ckma-51): analytic
factorization, inverse scattering, Hamiltonian and algebraic integrability,
isomonodromic deformation, and nonlinear asymptotics. The emphasis is on
usable mathematical structures and representative theorems shared by several
treatments. General dispersive well-posedness, orthogonal-polynomial theory,
and ordinary asymptotic methods are developed further in Sections 34, 48,
and 50; the Painlevé property of complex ODEs is in Section 41.

General dispersive and nonlinear-wave estimates are identified as
[34B](CKMA-bib.md#ckma-34b), random matrix ensembles as
[07B](CKMA-bib.md#ckma-07b), and orthogonal-polynomial theory as Section 48.
The [inverse-problems route](CKMA-MSC2020.md#inverse-problems) distinguishes
integrable inverse scattering from broader inverse and regularization
problems.

An oriented contour has its positive side on the left. A normalized matrix
Riemann–Hilbert problem asks for $M$ holomorphic off the contour, with
$M_+=M_-v$ and $M(\infty)=I$, together with specified endpoint and pole
conditions. Boundary values are nontangential; statements in $L^2$ use the
Cauchy-transform class $M-I=Cf$, $f\in L^2$, rather than arbitrary
holomorphic functions with almost-everywhere boundary traces. For scattering
formulas below, the potential is real and Schwartz unless stated otherwise.
We normalize KdV as $u_t-6uu_x+u_{xxx}=0$ and its spectral operator as
$L=-\partial_x^2+u$.

## Cauchy operators and analytic factorization

* **1. Sokhotski–Plemelj formulas.** On a smooth closed contour, or on
  $\mathbb R$, $Cf(z)=(2\pi i)^{-1}\int f(s)/(s-z)\,ds$ has bounded
  boundary operators on $L^p$, $1<p<\infty$, and
  $C_\pm=\pm\frac12I+\frac12S$, with $S$ the principal-value operator
  $Sf(t)=(\pi i)^{-1}\mathrm{p.v.}\int f(s)/(s-t)\,ds$; thus
  $C_+-C_-=I$. On a closed contour $C_\pm$ also preserve Hölder classes
  $C^{0,\alpha}$, $0<\alpha<1$ (Plemelj–Privalov). On the line, $C_+$
  and $-C_-$ are complementary Hardy projections.
* **2. Additive jump problem.** The solution of $F_+-F_-=f$ that
  vanishes at infinity in the corresponding Cauchy class is $F=Cf$.
  Polynomial growth at infinity introduces a polynomial ambiguity.
* **3. Scalar multiplicative factorization.** If a nonvanishing Hölder
  jump $v$ on a smooth Jordan curve has winding number zero, a continuous
  logarithm gives $\delta=\exp C(\log v)$, with
  $\delta_+=\delta_-v$ and exterior normalization one. Nonzero winding
  requires an explicit power factor.
* **4. Matrix partial indices.** An invertible Hölder matrix loop on
  the unit circle admits a Birkhoff factorization
  $v=v_-^{-1}\mathop{\mathrm{diag}}(z^{\kappa_1},\ldots,z^{\kappa_r})v_+$
  with holomorphically invertible inside and outside factors. The integer
  partial indices govern homogeneous solutions and solvability;
  $\sum\kappa_j=\mathop{\mathrm{wind}}\det v$ does not determine them separately.
* **5. Determinant and uniqueness.** If $\det v=1$ and endpoint
  conditions make the determinant singularities removable, a normalized
  solution has determinant one. The quotient of two solutions is entire
  and equal to $I$ by Liouville's theorem, provided its endpoint
  singularities are likewise removable.
* **6. Singular-integral formulation.** For $v-I\in L^2\cap L^\infty$,
  the equation $\mu=I+C_-(\mu(v-I))$ gives
  $M=I+C(\mu(v-I))$. Solutions correspond when the products belong to
  the stated boundary spaces and the contour Cauchy operators are bounded.
* **7. Beals–Coifman factorization.** Writing
  $v=(I-w_-)^{-1}(I+w_+)$ gives the boundary equation
  $(I-C_w)\mu=I$, where
  $C_wf=C_+(fw_-)+C_-(fw_+)$. This separates jump factors supported
  on different analytic sides.
* **8. Small-norm theorem.** On a fixed contour with bounded $L^2$
  Cauchy operators, $\|v-I\|_\infty$ sufficiently small makes
  $I-C_{v-I}$ invertible by a Neumann series. If also $v-I\in L^2$,
  then $\|\mu-I\|_2\leq C\|v-I\|_2$; the Cauchy representation
  controls the solution away from the contour. More generally, an
  invertible problem stays invertible under small operator-norm
  perturbations of the jump, with solution change bounded by the
  resolvent identity.
* **9. Analytic Fredholm principle.** An analytic family of Fredholm
  boundary operators of index zero, invertible at one parameter, has a
  meromorphic inverse. Exceptional parameters are discrete in one complex
  dimension; their occurrence must be excluded before asserting global
  solvability of a parameter-dependent Riemann–Hilbert problem.
* **10. Positivity vanishing lemma.** On $\mathbb R$, a continuous
  bounded invertible jump with $v+v^*\geq cI$, $c>0$, and sufficient
  decay to $I$ has no nonzero homogeneous Hardy-class solution vanishing
  at infinity. Together with Fredholm index zero this proves existence
  and uniqueness of the normalized problem.
* **11. Rational dressing.** Multiplying a known solution by a rational
  matrix inserts prescribed simple poles. Rank-one residue constraints
  reduce the dressing problem to finite linear algebra; invertibility
  of that finite system is the condition for the dressed solution.

## Nonlinear steepest descent

* **12. Contour deformation and lenses.** A factorization of a jump
  into matrices holomorphic in adjacent regions permits an equivalent
  Riemann–Hilbert problem on a deformed contour. Reconstruction preserves
  the original solution outside the deformation regions.
* **13. Scalar phase normalization.** A scalar $g$-function chosen
  with appropriate sum and difference conditions on spectral bands
  converts large exponential jumps into bounded oscillatory or decaying
  ones. For orthogonal polynomials these conditions are the
  Euler–Lagrange conditions for logarithmic equilibrium (entry 60).
* **14. Parametrix error theorem.** Suppose an outer model and local
  models are uniformly invertible and match by $I+O(\varepsilon)$
  on fixed disk boundaries, while remaining jumps are small in
  $L^2\cap L^\infty$. Their quotient with the exact solution solves a
  small-norm problem, giving controlled asymptotics and, with stronger
  expansions of the jumps, successive correction terms.
* **15. Universal local models.** Nondegenerate quadratic stationary
  phases lead to parabolic-cylinder problems; regular soft endpoints
  lead to Airy problems; algebraic hard endpoints lead to Bessel
  problems. Coalescing critical points require different, often Painlevé,
  models. These reductions require the corresponding phase and weight
  nondegeneracy assumptions. See the
  Deift–Zhou paper *A steepest descent method for oscillatory Riemann–Hilbert
  problems* (Ann. of Math. 1993)
  and Deift's lectures (arXiv:1903.08304).

## Direct and inverse scattering on the line

* **16. Jost solutions.** For real $u\in L^1((1+|x|)\,dx)$,
  $Lf=k^2f$ has solutions $f_\pm(x,k)\sim e^{\pm ikx}$ at
  the corresponding ends. After removal of these exponentials they
  extend analytically to $\mathop{\mathrm{Im}}k>0$ and continuously to
  nonzero real $k$, by Volterra integral equations.
* **17. Scattering unitarity.** Transmission and left/right reflection
  coefficients obey $|T(k)|^2+|R_\pm(k)|^2=1$ for real $k\ne0$,
  with conjugation symmetries imposed by reality of $u$. Wronskians
  yield the relations between the two reflection coefficients.
* **18. Discrete spectrum.** The negative eigenvalues are simple and
  finite in number, $-\kappa_j^2$, $\kappa_j>0$; they correspond to
  zeros of the analytic inverse transmission coefficient in the upper
  half-plane. The positive norming constants
  $c_j=\big(\int_{\mathbb R}f_+(x,i\kappa_j)^2dx\big)^{-1}$ (right
  convention) complete the discrete data.
* **19. Uniqueness from scattering data.** One reflection coefficient,
  all negative eigenvalues, and the associated norming constants
  determine a real short-range potential uniquely. Reflection data
  alone are insufficient when bound states are present.
* **20. Marchenko reconstruction.** For admissible right scattering
  data put $F(s)=(2\pi)^{-1}\int R_+(k)e^{iks}\,dk+
  \sum c_je^{-\kappa_js}$. The equation
  $K(x,y)+F(x+y)+\int_x^\infty K(x,s)F(s+y)\,ds=0$, $y\geq x$,
  has a unique solution and reconstructs
  $u(x)=-2\,dK(x,x)/dx$.
* **21. Trace identities.** Factoring the analytic transmission
  coefficient into its zeros and boundary modulus expresses the
  conserved integrals of the potential through reflection and discrete
  data. In particular
  $\int u\,dx=-4\sum_j\kappa_j-
  \pi^{-1}\int_{\mathbb R}\log(1-|R_+(k)|^2)\,dk$.
* **22. KdV Lax pair.** With
  $P=-4\partial_x^3+6u\partial_x+3u_x$, the identity $L_t=[P,L]$
  is equivalent to the stated KdV equation. Evolution of eigenfunctions
  by $\psi_t=P\psi$ preserves their spectral parameter.
* **23. Linear evolution of scattering data.** For this KdV
  normalization, $R_+(k,t)=R_+(k,0)e^{8ik^3t}$,
  $\kappa_j(t)=\kappa_j(0)$, and
  $c_j(t)=c_j(0)e^{8\kappa_j^3t}$ in the right Marchenko convention.
  Evolving these data and reconstructing solves the Schwartz-class
  Cauchy problem.
* **24. One-soliton solution.** A single eigenvalue and zero reflection
  give $u(x,t)=-2\kappa^2\mathop{\mathrm{sech}}^2
  (\kappa(x-4\kappa^2t-x_0))$.
* **25. Multisoliton determinant.** Reflectionless data give
  $u=-2\partial_x^2\log\det(I+A)$, where
  $A_{ij}=\sqrt{c_i(t)c_j(t)}e^{-(\kappa_i+\kappa_j)x}/
  (\kappa_i+\kappa_j)$. Positivity of $I+A$ gives a smooth real
  solution for positive $c_j$ and distinct positive $\kappa_j$.
* **68. Hirota bilinear form and tau functions.** With the Hirota
  derivative $D_x^mD_t^n\,a\cdot b=(\partial_x-\partial_{x'})^m
  (\partial_t-\partial_{t'})^na(x,t)b(x',t')|_{x'=x,t'=t}$, the
  substitution $u=-2\partial_x^2\log\tau$ turns KdV into
  $(D_xD_t+D_x^4)\,\tau\cdot\tau=0$ (sufficient, and necessary up to
  integration constants fixed by decay). The $N$-soliton tau function is
  $\tau=\sum_{\mu\in\{0,1\}^N}\exp\bigl(\sum_i\mu_i\eta_i
  +\sum_{i<j}\mu_i\mu_jA_{ij}\bigr)$, $\eta_i=k_ix-k_i^3t+\eta_i^0$,
  $e^{A_{ij}}=((k_i-k_j)/(k_i+k_j))^2$; with $k_i=2\kappa_i$ it equals
  $\det(I+A)$ of entry 25 after renormalizing the phases. In Sato's
  theory, tau functions of the KP hierarchy form the orbit of an
  infinite-dimensional Grassmannian, the Hirota bilinear identities are
  its Plücker relations, and KdV is the reduction to $\tau$ independent of
  the even times.
* **26. Elastic soliton scattering.** As $t\to\pm\infty$, an
  $N$-soliton resolves into the same individual amplitudes and speeds.
  Each collision changes only position; the pairwise shift has magnitude
  $\kappa_i^{-1}\log|(\kappa_i+\kappa_j)/
  (\kappa_i-\kappa_j)|$, advancing the faster and retarding the slower soliton.
* **27. Conservation laws.** Smooth rapidly decaying KdV solutions
  conserve $\int u$, $\int u^2$, and
  $\int(\tfrac12u_x^2+u^3)$. Expansion of the spectral Riccati
  equation supplies infinitely many local conservation laws.
* **28. Miura transformation.** If
  $v_t-6v^2v_x+v_{xxx}=0$, then $u=v_x+v^2$ solves KdV.
  The factorization
  $-\partial_x^2+u=(\partial_x+v)(-\partial_x+v)$ explains the
  transformation and its positivity consequences on the line.
* **29. Darboux transformation.** A nonvanishing solution
  $L\phi=\lambda_0\phi$ yields
  $\widetilde u=u-2\partial_x^2\log\phi$ and an intertwining
  operator $\partial_x-\phi_x/\phi$. Zeros of $\phi$ produce poles;
  regularity requires their exclusion on the domain considered.
* **69. Bäcklund transformation and permutability.** For sine-Gordon
  $u_{xt}=\sin u$ and $a\ne0$, the system
  $\frac12(u'-u)_x=a\sin\frac{u'+u}2$,
  $\frac12(u'+u)_t=a^{-1}\sin\frac{u'-u}2$ is compatible exactly when
  $u$ and $u'$ both solve the equation. From $u=0$ it gives the kink
  $u'=4\arctan e^{ax+t/a+c}$. If $u_1,u_2$ arise from $u$ with parameters
  $a_1\ne a_2$, Bianchi's permutability theorem gives a common
  $u_{12}$ algebraically:
  $\tan\frac{u_{12}-u}4=\frac{a_1+a_2}{a_1-a_2}\tan\frac{u_1-u_2}4$;
  iteration builds multisolitons and breathers without quadratures.
  For KdV the Darboux transformation of entry 29 plays the same role
  (Rogers–Schief).
* **30. AKNS compatibility.** For $\Psi_x=U(\lambda)\Psi$,
  $\Psi_t=V(\lambda)\Psi$, compatibility is
  $U_t-V_x+[U,V]=0$. Polynomial choices of $V$ for
  $U=-i\lambda\sigma_3+\begin{pmatrix}0&q\\r&0\end{pmatrix}$
  produce the AKNS hierarchy, including focusing and defocusing NLS
  after the respective reality reductions.
* **70. Zakharov–Shabat direct scattering.** For complex $q\in L^1(\mathbb R)$
  and the focusing system $v_x=\begin{pmatrix}-i\lambda&q\\-\bar q&i\lambda
  \end{pmatrix}v$, Jost solutions normalized at $\mp\infty$ exist for
  $\mathop{\mathrm{Im}}\lambda\geq0$, and their Wronskian $a(\lambda)$ is
  analytic in the upper half-plane, continuous up to $\mathbb R$, and tends
  to $1$ at infinity; on $\mathbb R$, $|a|^2+|b|^2=1$, with $r=b/a$.
  The $L^2$ eigenvalues are the zeros of $a$ in
  $\mathop{\mathrm{Im}}\lambda>0$, finitely many when $a$ has no real zeros;
  there are none if $\|q\|_{L^1}<\pi/2$, and for real nonnegative
  single-lobe $q$ they are simple, purely imaginary, and
  $\lfloor\|q\|_{L^1}/\pi+\frac12\rfloor$ in number when
  $\|q\|_{L^1}/\pi+\frac12\notin\mathbb Z$ (Klaus–Shaw; for
  $q=A\mathop{\mathrm{sech}}x$, Satsuma–Yajima).
  Under the NLS flow of entry 31, $a$ is conserved and $b$ and the norming
  constants evolve by explicit exponential factors in $\lambda^2t$.
* **31. Focusing NLS soliton.** For
  $iq_t+q_{xx}+2|q|^2q=0$,
  $q=\eta\mathop{\mathrm{sech}}(\eta(x-2\xi t-x_0))
  e^{i(\xi x+(\eta^2-\xi^2)t+\theta_0)}$ is a soliton.
  Simple discrete Zakharov–Shabat data give its multisoliton extensions.
* **32. Defocusing spectral distinction.** With zero boundary data,
  the defocusing Zakharov–Shabat operator is self-adjoint; for Schwartz
  potentials its scattering problem has no discrete soliton eigenvalues.
  Dark solitons instead belong to nonzero-background scattering.
* **33. Riemann–Hilbert problem for defocusing NLS.** For
  $iq_t+q_{xx}-2|q|^2q=0$ with Schwartz data and reflection coefficient
  $r$, $\sup|r|<1$, let $\theta=kx+2k^2t$. The normalized problem on
  $\mathbb R$ with jump
  $v=\begin{pmatrix}1-|r|^2&-\bar re^{-2i\theta}\\re^{2i\theta}&1\end{pmatrix}$
  has a unique solution for all $(x,t)$ (entry 10 applies, since $v+v^*>0$),
  and $q(x,t)=2i\lim_{k\to\infty}kM_{12}(k;x,t)$.
  The $(x,t)$ dependence enters only through the explicit phase.
* **34. Nonlinear stationary phase.** In that setting, with
  $k_0=-x/(4t)$ and $\nu=-(2\pi)^{-1}\log(1-|r(k_0)|^2)$,
  nonlinear steepest descent gives
  $q(x,t)=t^{-1/2}\alpha(k_0)e^{ix^2/(4t)-i\nu\log(8t)}+O(t^{-1}\log t)$
  uniformly on $|x/t|\leq C$, where $|\alpha(k_0)|^2=\nu/2$ and
  $\arg\alpha$ is explicit in $r$ and $\Gamma(i\nu)$. The linear
  dispersive rate survives while the phase acquires a logarithmic correction.

## Hamiltonian structure, finite-gap solutions, and lattices

* **35. Liouville–Arnold theorem.** On a $2n$-dimensional symplectic
  manifold, $n$ independent commuting first integrals make each compact
  connected regular common level a torus. Near it, action–angle
  coordinates turn the commuting flows into linear translations.
  Here $F$ is conserved by the flow of $H$ exactly when $\{F,H\}=0$,
  and Poisson-commuting Hamiltonians generate commuting flows.
  In action–angle coordinates $H=H(I)$, $\dot\theta=\nabla H(I)$, $\dot I=0$.
* **36. KdV Hamiltonian pair.** The compatible Poisson operators
  $J_1=\partial_x$ and
  $J_2=-\partial_x^3+2(u\partial_x+\partial_xu)$ give
  $u_t=J_1\delta\int(\tfrac12u_x^2+u^3)/\delta u
  =J_2\delta\int\tfrac12u^2/\delta u$.
  Here $\partial_xu$ in $J_2$ denotes composition with multiplication by $u$.
* **37. Lenard recursion.** The relation
  $J_1\delta H_{j+1}=J_2\delta H_j$ constructs the KdV hierarchy.
  For periodic functions or rapidly decaying functions, integration by
  parts and compatibility show that its Hamiltonians are in involution.
* **38. Classical $r$-matrix mechanism.** A Poisson relation
  $\{L_1,L_2\}=[r_{12},L_1]-[r_{21},L_2]$
  implies $\{\mathop{\mathrm{tr}}L^j,\mathop{\mathrm{tr}}L^k\}=0$.
  A suitable classical Yang–Baxter identity ensures Jacobi for the
  associated bracket; independence of the integrals remains a separate issue.
* **39. Periodic spectral bands.** For a real periodic Schrödinger
  operator, the spectrum is $\{\lambda:|\Delta(\lambda)|\leq2\}$,
  where $\Delta$ is the Floquet discriminant. Band endpoints are
  periodic or antiperiodic eigenvalues; closed gaps are double endpoints.
* **40. Commuting differential operators.** Commuting ordinary
  differential operators with analytic coefficients satisfy a polynomial
  relation. In the stationary KdV case the relation between the
  second-order operator and an odd-order commuting operator defines a
  hyperelliptic spectral curve.
* **41. Baker–Akhiezer construction.** A smooth genus-$g$ spectral
  curve, marked point with local parameter, and generic nonspecial
  degree-$g$ divisor determine a normalized Baker–Akhiezer function
  with prescribed poles and exponential singularity. The reconstructed
  potential is meromorphic in $(x,t)$, with poles where the linearly
  moving Jacobian point of entry 43 meets the theta divisor.
* **42. Abelian linearization.** The Abel image of the moving
  spectral divisor evolves linearly in the Jacobian under the commuting
  hierarchy flows. Jacobi inversion reconstructs the divisor and the
  corresponding potential.
* **43. Theta-function solutions.** Finite-gap KdV potentials have
  the form $u=C-2\partial_x^2\log\theta(Ux+Vt+D)$, with vectors
  fixed by normalized differentials of the spectral curve. Appropriate
  real branch points and admissible real divisor data give smooth real
  quasiperiodic solutions; arbitrary complex data need not do so.
* **44. Finite-gap trace formula.** For spectrum
  $[E_0,E_1]\cup\cdots\cup[E_{2g},\infty)$ and Dirichlet divisor
  coordinates $\mu_j(x)$, the potential satisfies
  $u(x)=\sum_{m=0}^{2g}E_m-2\sum_{j=1}^g\mu_j(x)$.
* **45. Finite Toda Hamiltonian.** The open chain
  $H=\tfrac12\sum_{j=1}^Np_j^2+
  \sum_{j=1}^{N-1}e^{q_j-q_{j+1}}$ has a global Hamiltonian flow.
  Its spectral invariants supply complete integrability after the
  center-of-mass coordinate is included.
* **46. Toda Lax equations.** With
  $a_j=\tfrac12e^{(q_j-q_{j+1})/2}$, $b_j=-p_j/2$,
  $\dot a_j=a_j(b_{j+1}-b_j)$ and
  $\dot b_j=2(a_j^2-a_{j-1}^2)$. The Jacobi matrix $J$ satisfies
  $\dot J=[B,J]$, with $B$ its strictly upper part minus its
  strictly lower part, and hence is isospectral.
* **47. Toda spectral measure.** For the finite open chain, if
  $\rho_0$ is the spectral measure at the first coordinate, then
  $d\rho_t(\lambda)=e^{2t\lambda}d\rho_0(\lambda)/
  \int e^{2t\lambda}d\rho_0(\lambda)$. Orthogonalization recovers
  the evolving Jacobi coefficients from this elementary weight deformation.
* **48. Continuous and discrete hierarchies.** Higher KdV and Toda
  flows arise from suitable differential or triangular parts of powers
  of the Lax operator. Their zero-curvature identities give commuting
  evolutions with the same spectral curve.
* **71. Multidimensional consistency.** A quad equation
  $Q(x,x_1,x_2,x_{12};\alpha_1,\alpha_2)=0$ on $\mathbb Z^2$, affine
  in each corner value, is consistent around the cube when, imposed on
  the three coordinate planes of $\mathbb Z^3$, the three values of
  $x_{123}$ computed from $x,x_1,x_2,x_3$ coincide. Consistency
  yields a Lax pair (zero-curvature representation) and Bäcklund
  transformations as the third lattice direction. Example: the discrete
  potential KdV equation $(x-x_{12})(x_1-x_2)=\alpha_1-\alpha_2$, for
  which $x_{123}$ is moreover independent of $x$. Adler–Bobenko–Suris
  classified consistent quad equations with the symmetry and tetrahedron
  properties (Bobenko–Suris, Hietarinta–Joshi–Nijhoff).
* **49. Soliton degeneration.** Coalescence of suitable branch-point
  pairs degenerates finite-gap theta solutions into finite exponential
  determinant solutions. Under the real nonsingularity conditions this
  recovers multisolitons from the algebro-geometric construction.

## Isomonodromy and Painlevé equations

Monodromy data include connection matrices, local exponents, and, at
irregular singularities, Stokes matrices. Isomonodromic deformations preserve
these data while singularity positions or irregular types vary.

* **50. Schlesinger equations.** For the Fuchsian system
  $Y_z=\sum_i A_i/(z-a_i)Y$, compatibility with
  $Y_{a_j}=-A_jY/(z-a_j)$ gives
  $\partial_{a_j}A_i=[A_i,A_j]/(a_i-a_j)$ for $i\ne j$ and
  $\partial_{a_i}A_i=-\sum_{j\ne i}[A_i,A_j]/(a_i-a_j)$.
  These equations preserve monodromy; the converse needs the usual
  nonresonance or prescribed local-normalization assumptions.
* **51. Painlevé VI reduction.** Rank-two Fuchsian systems on the
  sphere with four singularities reduce, after fixing conjugacy classes
  and quotienting by gauge, to Painlevé VI. Its four parameters are
  determined by local exponent differences.
* **52. Irregular reductions.** Compatibility of rank-two systems
  with irregular singularities produces the other Painlevé equations.
  Two standard normalizations are
  $q''=6q^2+x$ for PI and $q''=2q^3+xq+\alpha$ for PII.
  Their monodromy representations are replaced by Stokes data at the
  irregular points.
* **53. Painlevé property.** Solutions of PI, PII, and PIV extend
  meromorphically over the finite independent-variable plane. For the
  remaining classical equations the corresponding statement holds on
  the universal cover of the plane with their fixed singularities
  removed. Movable singularities are poles, with the appropriate
  meromorphic interpretation in the dependent variable.
* **54. Hastings–McLeod solution.** PII with $\alpha=0$ has a
  distinguished real pole-free solution satisfying
  $q(x)\sim\mathop{\mathrm{Ai}}(x)$ as $x\to+\infty$ and
  $q(x)\sim\sqrt{-x/2}$ as $x\to-\infty$. The positive Airy
  normalization selects it uniquely.
* **55. Bäcklund transformations.** Rational transformations of
  $(q,q',x)$ map Painlevé solutions to solutions with shifted or
  reflected parameters. Their identities hold meromorphically across
  apparent denominator zeros; parameter shifts generate the classical
  rational and special-function solution families from seed solutions.
* **56. Isomonodromic tau function.** The isomonodromic Hamiltonian
  one-form is closed along the deformation equations. Locally it is
  $d\log\tau$; for Schlesinger deformations its coefficients are
  $H_i=\sum_{j\ne i}\mathop{\mathrm{tr}}(A_iA_j)/(a_i-a_j)$.
  The tau function is determined up to a nonzero multiplicative constant.
* **57. Discrete isomonodromy.** Rational gauge transformations that
  shift characteristic exponents by integers preserve monodromy and
  induce birational transformations of the deformation variables.
  Compatibility between successive shifts yields discrete Painlevé
  equations in the classical isomonodromic constructions.
* **72. Discrete Painlevé I from a Freud weight.** For the weight
  $e^{-x^4}$ on $\mathbb R$, the orthonormal recurrence
  $xp_n=a_{n+1}p_{n+1}+a_np_{n-1}$, $a_0=0$, has $x_n=a_n^2$ satisfying
  the string equation $4x_n(x_{n-1}+x_n+x_{n+1})=n$, a discrete
  Painlevé I equation. The recurrence coefficients form its unique
  positive solution with $x_0=0$, and $a_n\sim(n/12)^{1/4}$. The
  Riemann–Hilbert problem of entry 58 supplies its Lax pair
  (Fokas–Its–Kitaev; Joshi).

## Orthogonal polynomials, kernels, and boundary transforms

For the varying weight $e^{-nV}$, let $p_{j,n}$ be orthonormal and put
$K_n(x,y)=e^{-n(V(x)+V(y))/2}\sum_{j=0}^{n-1}p_{j,n}(x)p_{j,n}(y)$.

* **58. Fokas–Its–Kitaev characterization.** For a positive Schwartz
  weight $w$ on $\mathbb R$, the unique problem
  $Y_+=Y_-\begin{pmatrix}1&w\\0&1\end{pmatrix}$,
  $Y=(I+O(z^{-1}))\mathop{\mathrm{diag}}(z^n,z^{-n})$
  has $Y_{11}$ equal to the monic orthogonal polynomial of degree $n$.
  Its other entries are neighboring polynomials and their Cauchy transforms.
  This gives the analytic route to strong asymptotics.
* **59. Kernel recovery.** The Christoffel–Darboux kernel is a
  bilinear expression in $Y(y)^{-1}Y(x)/(x-y)$ with the weight
  factors attached. Consequently uniform matrix asymptotics imply
  asymptotics of correlation kernels and their diagonal limits.
* **60. Equilibrium measure.** For continuous $V$ with
  $V(x)-2\log|x|\to+\infty$, the logarithmic energy
  $\iint\log|x-y|^{-1}d\mu(x)d\mu(y)+\int V\,d\mu$
  has a unique minimizing probability measure. Its potential satisfies
  $2\int\log|x-y|d\mu(y)-V(x)=\ell$ quasi-everywhere on the
  support and is at most $\ell$ off it. For $V(x)=2x^2$ the minimizer is
  the semicircle law $(2/\pi)\sqrt{1-x^2}\,dx$ on $[-1,1]$.
* **61. Regular one-cut asymptotics.** For real analytic confining
  $V$ whose equilibrium measure has one interval of support, positive
  interior density, square-root endpoints, and strict exterior
  variational inequality, the orthogonal-polynomial problem for
  $e^{-nV}$ reduces to an explicit outer model and Airy endpoint
  models with an $O(n^{-1})$ error problem.
* **62. Bulk universality.** In that setting, the weighted correlation
  kernel satisfies
  $[n\rho(x_0)]^{-1}K_n(x_0+u/(n\rho(x_0)),
  x_0+v/(n\rho(x_0)))\to\sin(\pi(u-v))/(\pi(u-v))$
  at each interior point with $\rho(x_0)>0$, locally uniformly in $u,v$.
* **63. Soft-edge universality.** At a regular right endpoint $b$,
  an appropriate positive constant $c$ gives
  $(cn^{2/3})^{-1}K_n(b+u/(cn^{2/3}),b+v/(cn^{2/3}))
  \to K_{\mathrm{Ai}}(u,v)$, where
  $K_{\mathrm{Ai}}(u,v)=[\mathop{\mathrm{Ai}}(u)\mathop{\mathrm{Ai}}'(v)
  -\mathop{\mathrm{Ai}}'(u)\mathop{\mathrm{Ai}}(v)]/(u-v)$.
* **64. Integrable kernels.** For a trace-class kernel with smooth
  compactly supported vector functions $f,g$ on $\mathbb R$,
  $K(x,y)=f(x)^Tg(y)/(x-y)$ with $f(x)^Tg(x)=0$,
  invertibility of $I-K$ produces a resolvent of the same form.
  The transformed vector functions solve an associated matrix
  Riemann–Hilbert problem, linking Fredholm determinants and isomonodromy.
* **65. Tracy–Widom formula.** The Airy-kernel determinant on
  $L^2(s,\infty)$ is
  $F_2(s)=\exp[-\int_s^\infty(x-s)q(x)^2\,dx]$, with $q$
  the Hastings–McLeod solution. It is the limiting largest-eigenvalue
  distribution at a regular soft edge of unitary-invariant ($\beta=2$)
  ensembles after centering and scaling.
* **66. Longest increasing subsequences.** If $L_N$ is the longest
  increasing subsequence of a uniformly random permutation of $N$
  letters, then $(L_N-2\sqrt N)/N^{1/6}$ converges in distribution
  to $F_2$. Orthogonal-polynomial and Fredholm determinant formulations
  connect this theorem to the same Painlevé asymptotics.
* **67. Global relation for a boundary transform.** For
  $q_t=q_{xx}$ on $x>0$, write
  $\widehat q(k,t)=\int_0^\infty e^{-ikx}q(x,t)\,dx$ and
  $\widetilde g_j(k,t)=\int_0^t e^{k^2s}\partial_x^jq(0,s)\,ds$.
  For smooth decaying data and $\mathop{\mathrm{Im}}k\leq0$,
  $e^{k^2t}\widehat q(k,t)=\widehat q(k,0)-
  \widetilde g_1(k,t)-ik\widetilde g_0(k,t)$.
  Analytic continuation and contour deformation eliminate unknown
  boundary transforms; analogous compatibility relations are the
  starting point of the unified transform for integrable boundary problems.

## Reference guide

Ablowitz–Fokas supplies scalar and matrix factorization and inverse scattering;
Ablowitz's dispersive-wave text and Faddeev–Takhtajan overlap on Lax pairs,
scattering evolution, solitons, and conserved Hamiltonians. Marchenko and
the founding soliton treatise provide the inverse-spectral continuation.
Gesztesy–Holden and its discrete companion, together with Natanzon and
Babelon–Bernard–Talon, develop spectral curves and commuting hierarchies.
Deift and Fokas–Its–Kapaev–Novokshenov organize the Riemann–Hilbert and
isomonodromic branches; Conte–Musette supplies the differential-equation
and transformation viewpoint. Trogdon–Olver emphasizes singular-integral
stability and computation. Baik–Deift–Suidan and Romik connect kernels and
Painlevé functions to probability; the boundary-value books of Fokas and
Pelloni develop the global-relation method. Rogers–Schief treat Bäcklund
and Darboux transformations; Bobenko–Suris, Hietarinta–Joshi–Nijhoff, and
Joshi treat multidimensional consistency and discrete Painlevé equations.
The selection states the consistency principle (entry 71) but does not
attempt to enumerate every integrable hierarchy or discrete surface
classification.

Local full-text sources consulted:

* [Ablowitz–Fokas, *Complex Variables*, second edition](References/AblowitzFokas2003ComplexVariables2ndEd-CambridgeTextsAM35.pdf).
* [Ablowitz, *Nonlinear Dispersive Waves*](References/Ablowitz2011NonlinearDispersiveWaves-Cambridge.TextsAM.pdf).
* [Faddeev–Takhtajan, *Hamiltonian Methods in the Theory of Solitons*](References/FaddeevTakhtajan2007HamiltonianMethodsTheorySolitons-SpringerCLASSICS.pdf).
* [Gesztesy–Holden, *Soliton Equations and Their Algebro-Geometric Solutions*, I](References/GesztesyHolden2003SolitonEquationsAlgebroGeometricSolutionsVol1-Cambridge.StudAM79.pdf).
* [Gesztesy–Holden–Michor–Teschl, *Soliton Equations and Their Algebro-Geometric Solutions*, II](References/GesztesyHoldenMichorTeschl2008SolitonEquationsAlgebroGeometricSolutionsVol2-Cambridge.StudAM114.pdf).
* [Natanzon, *Complex Analysis, Riemann Surfaces and Integrable Systems*](References/Natanzon2019ComplexAnalysisRiemannSurfacesIntegrableSystems-Springer.MoscowLectures03.pdf).
* [Conte–Musette, *The Painlevé Handbook*, second edition](References/ConteMusette2020PainleveHandbook2ndEd-Springer.MathPhysStud.pdf).
* [Romik, *The Surprising Mathematics of Longest Increasing Subsequences*](References/Romik2014SurprisingMathematicsLongestIncreasingSubsequences-Cambridge.IMSTextbooks.pdf).

The linked Deift–Zhou paper identifies the original steepest-descent source;
Deift's accessible lectures were consulted as a supplementary treatment,
not as a full-text copy of either of the two principal Riemann–Hilbert books.
