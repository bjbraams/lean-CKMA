# Synopsis: Hyperbolic equations, conservation laws, dispersive PDE, fluids, and kinetic theory

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-34);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis follows Section 34's four subdivisions: hyperbolic systems and
conservation laws ([34A](CKMA-bib.md#ckma-34a)), dispersive equations and
nonlinear waves ([34B](CKMA-bib.md#ckma-34b)), mathematical fluid dynamics
([34C](CKMA-bib.md#ckma-34c)), and kinetic equations
([34D](CKMA-bib.md#ckma-34d)). Supplementary structural results are placed
with the equations they concern. Section 32 supplies general linear energy
theory, Sections 26–30 the analytic tools, Section 09 stochastic
counterparts, and Section 51 the integrable models and inverse scattering
on which the KdV entries border. Classical, energy, entropy, and
renormalized solutions retain their distinct hypotheses and meanings.

Spatial domains are $\mathbb R^d$ or a flat torus unless specified.
Sobolev spaces are $L^2$ based; $\dot H^s$ denotes the homogeneous scale.
Integrations by parts assume the displayed regularity, decay, periodicity,
or boundary conditions. Existence statements for weak solutions do not imply
uniqueness unless uniqueness is expressly asserted.

Lettered headings match the bibliography. Numbered results retain their
existing identifiers, including after moves between topical groups, so the
labels remain usable from the gap inventory; they need not run in increasing
order within the file.

<a id="synopsis-34a"></a>

## 34A. Hyperbolic Systems and Conservation Laws

Hyperbolic propagation, shock formation, entropy admissibility, and
conservation-law semigroups follow 34A. Compressible-flow examples here
emphasise their hyperbolic structure; viscous fluid existence and limits are
in 34C.

### Quasilinear hyperbolicity and the formation of shocks

A first-order system $U_t+\sum_jA^j(U)\partial_jU=0$ is
**symmetrizable hyperbolic** if a smooth positive definite matrix $S(U)$
makes all $S(U)A^j(U)$ symmetric. A one-dimensional conservation law is
$U_t+F(U)_x=0$. Strict hyperbolicity means that $DF(U)$ has distinct
real eigenvalues $\lambda_1<\cdots<\lambda_m$.
A family with eigenvector $r_k$ is genuinely nonlinear if
$D\lambda_k\cdot r_k$ never vanishes, and linearly degenerate if it vanishes identically.

* **1. Smooth local well-posedness.** Symmetrizable hyperbolic systems
  with smooth coefficients and initial data in $H^s$, $s>d/2+1$,
  have a unique local solution in $C(H^s)\cap C^1(H^{s-1})$,
  while values stay in the symmetrizable state region.

* **2. Continuation criterion.** Such solutions extend beyond $T$ if
  their values remain in a compact admissible state region and
  $\int_0^T\|\nabla U(t)\|_\infty dt<\infty$, with the usual
  uniform coefficient bounds. Loss of a spatial derivative bound is
  therefore a principal mechanism of breakdown.

* **3. Finite speed of propagation.** Smooth symmetric hyperbolic
  solutions have domains of dependence bounded by the maximal
  characteristic speed in the relevant state region.

* **4. Scalar characteristic breakdown.** For $u_t+f(u)_x=0$ in one
  dimension, $u(t,x)=u_0(\xi)$ with
  $x=\xi+tf'(u_0(\xi))$ while the characteristic map is invertible.
  For $f\in C^2$ and bounded $u_0\in C^1$ with bounded derivative, if
  $m=\inf_\xi\partial_\xi[f'(u_0(\xi))]<0$, the classical solution
  exists exactly on $[0,T^*)$, $T^*=-1/m$, and $u_x$ blows up as $t\uparrow T^*$;
  if $m\geq0$ it is global.

* **5. Rankine–Hugoniot condition.** A discontinuity moving with speed
  $s$ is a weak solution across the front exactly when
  $s(U_R-U_L)=F(U_R)-F(U_L)$. In several dimensions the normal
  flux satisfies the corresponding space–time jump relation.

* **6. Entropy production at a shock.** An entropy pair satisfies
  $Dq=D\eta\,DF$. The inequality $\eta(U)_t+q(U)_x\leq0$
  imposes $[q]-s[\eta]\leq0$ at a shock, where brackets mean
  right value minus left value.

* **7. Convex entropy and symmetrization.** If $D^2\eta$ is positive
  definite, the entropy compatibility makes $D^2\eta\,DF$ symmetric.
  Strictly convex entropy therefore supplies a symmetrizer and an energy.

* **8. Relative-entropy stability.** For a smooth reference solution and
  a bounded entropy weak solution in a compact state region with a
  uniformly convex entropy, the relative-entropy integral obeys a
  Grönwall estimate. Equal initial data imply weak–strong uniqueness
  within that entropy class on the smooth solution's lifespan.

### Scalar entropy solutions and one-dimensional systems

For scalar laws, the **Kružkov entropy inequalities** use
$\eta_k(u)=|u-k|$ and
$q_k(u)=\operatorname{sgn}(u-k)(f(u)-f(k))$ for all real $k$.

* **9. Kružkov existence and uniqueness.** For smooth scalar flux and
  bounded initial data on $\mathbb R^d$, there is a unique bounded
  entropy solution attaining the initial data in $L^1_{\mathrm{loc}}$.
  It satisfies the maximum principle and local finite-speed stability.

* **10. $L^1$ contraction and order.** For entropy solutions whose
  initial difference is integrable,
  $\|u(t)-v(t)\|_1\leq\|u_0-v_0\|_1$.
  Ordered initial data remain ordered, giving a contraction semigroup.

* **11. Vanishing viscosity.** Solutions of
  $u_t+\operatorname{div}f(u)=\varepsilon\Delta u$ with suitably
  approximated bounded initial data converge in $L^1_{\mathrm{loc}}$
  to the entropy solution as $\varepsilon\downarrow0$.

* **12. BV persistence.** Scalar entropy evolution does not increase
  spatial total variation. In particular one-dimensional BV initial
  data remain BV, providing compactness for approximation schemes.

* **13. Oleinik's one-sided estimate.** If $f''\geq c>0$ on the
  bounded range of a one-dimensional entropy solution, then
  $u(t,y)-u(t,x)\leq(y-x)/(ct)$ for $x<y$, in its one-sided
  representative sense. Positive slopes are regularized even when shocks remain.

* **14. Hopf–Lax formula.** For a convex superlinear Hamiltonian $H$
  with Legendre transform $L$ and Lipschitz initial $v_0$,
  $v(t,x)=\inf_y\{v_0(y)+tL((x-y)/t)\}$ is the viscosity solution
  (in the sense of Section 33) of $v_t+H(v_x)=0$. Its spatial derivative $u=v_x$ is the entropy
  solution of $u_t+H(u)_x=0$ with data $v_0'$ (Lax–Oleinik formula).

* **15. Convex scalar Riemann problem.** For strictly convex flux,
  $u_L>u_R$ produces the entropy shock with Rankine–Hugoniot speed;
  $u_L<u_R$ produces the centered rarefaction determined by
  $f'(u)=x/t$ between the two endpoint characteristic speeds.

* **16. Lax shock inequalities.** An admissible small $k$-shock in a
  genuinely nonlinear strictly hyperbolic system satisfies
  $\lambda_k(U_R)<s<\lambda_k(U_L)$ and
  $\lambda_{k-1}(U_L)<s<\lambda_{k+1}(U_R)$, omitting absent
  endpoint families.

* **17. Rarefactions and contact discontinuities.** Integral curves of
  an eigenvector field give centered rarefaction waves when the family
  is genuinely nonlinear. For a linearly degenerate family,
  $D\lambda_k\cdot r_k=0$, its elementary waves are contact discontinuities.

* **18. Local system Riemann solver.** Near a strictly hyperbolic state,
  if every characteristic family is genuinely nonlinear or linearly
  degenerate, sufficiently close left and right states are joined
  uniquely by the ordered sequence of small elementary Lax waves.

* **19. Glimm's small-BV theorem.** Under those hypotheses, sufficiently
  small total variation about a constant state yields a global entropy
  weak solution in one space dimension, with uniformly small total variation.

* **20. Standard Riemann semigroup.** On the small-BV domain there is
  a semigroup Lipschitz in $L^1$ and time, consistent with the local
  Riemann solvers, and unique among such semigroups (Bressan).
  Entropy weak solutions of small total variation satisfying a tame
  oscillation or tame variation condition coincide with its trajectories
  (Bressan–Goatin, Bressan–LeFloch).

* **21. Front-tracking convergence.** Piecewise constant approximate
  solutions built from approximate Riemann solvers converge to that
  semigroup. Interaction estimates control total wave strength and
  prevent cumulative growth from wave collisions.

* **22. Compensated compactness.** If $u_n\rightharpoonup u$,
  $v_n\rightharpoonup v$ in $L^2_{\mathrm{loc}}(\mathbb R^N;\mathbb R^N)$
  with $\{\operatorname{div}u_n\}$ and $\{\operatorname{curl}v_n\}$ precompact
  in $H^{-1}_{\mathrm{loc}}$, then $u_n\cdot v_n\to u\cdot v$ in
  distributions (Murat–Tartar div–curl lemma). Applied to entropy pairs
  of vanishing-viscosity approximations, it yields Tartar's commutation
  relation for Young measures, which reduces them to Dirac masses for
  genuinely nonlinear scalar laws, for genuinely nonlinear $2\times2$
  systems (DiPerna), and for isentropic gas dynamics with any $\gamma>1$
  (DiPerna for $\gamma=1+2/(2n+1)$; Ding–Chen–Luo;
  Lions–Perthame–Tadmor; Lions–Perthame–Souganidis), giving $L^\infty$ entropy solutions
  without BV bounds.

<a id="synopsis-34b"></a>

## 34B. Dispersive Equations and Nonlinear Waves

Dispersive estimates, nonlinear Schrödinger and wave equations, KdV, and
geometric wave systems follow 34B. The geometric Einstein Cauchy statements
are placed here with the bibliography's general-relativity references.

### Dispersive estimates and nonlinear Schrödinger equations

Mixed norms are $\|u\|_{L_t^qL_x^r}$. A Schrödinger-admissible pair
satisfies $q,r\geq2$, $2/q+d/r=d/2$, excluding $(q,r,d)=(2,\infty,2)$.
Use $iu_t+\Delta u=\sigma|u|^{p-1}u$, $p>1$, where
$\sigma=+1$ is defocusing and $\sigma=-1$ focusing.

* **23. Schrödinger dispersive estimate.** For $t\ne0$,
  $\|e^{it\Delta}f\|_\infty\leq(4\pi|t|)^{-d/2}\|f\|_1$.
  The group is unitary on every $H^s$.

* **24. Homogeneous Strichartz estimate.** For admissible $(q,r)$,
  $\|e^{it\Delta}f\|_{L_t^qL_x^r(\mathbb R\times\mathbb R^d)}
  \leq C\|f\|_2$.

* **25. Retarded Strichartz estimate.** For any two admissible pairs
  $(q,r),(\widetilde q,\widetilde r)$, endpoints included,
  $\|\int_{s<t}e^{i(t-s)\Delta}F(s)ds\|_{L_t^qL_x^r}
  \leq C\|F\|_{L_t^{\widetilde q'}L_x^{\widetilde r'}}$
  (Keel–Tao; off the endpoints it also follows from entry 24 by
  $TT^*$ and the Christ–Kiselev lemma).

* **26. Local smoothing.** Free Schrödinger waves gain half a
  derivative locally in space, averaged in time:
  $\sup_{x_0,R}R^{-1}\int_{\mathbb R}\int_{|x-x_0|<R}
  ||\nabla|^{1/2}e^{it\Delta}f|^2dx\,dt\leq C\|f\|_2^2$.
  For the Airy group, $\|\partial_xe^{-t\partial_x^3}f\|_{L^\infty_xL^2_t}
  =c\|f\|_2$ (Kato smoothing), the gain that makes the derivative
  nonlinearities of KdV-type equations tractable.

* **27. Subcritical $H^1$ well-posedness.** NLS is locally well posed
  in $H^1$ for $1<p<1+4/(d-2)$ when $d\geq3$, and every finite
  $p>1$ when $d\leq2$. The solution belongs to the accompanying
  Strichartz class; finite maximal lifespan requires an unbounded $H^1$ norm.

* **28. NLS mass and energy.** Smooth solutions conserve
  $M(u)=\int|u|^2$ and
  $E(u)=\int(\tfrac12|\nabla u|^2+\sigma|u|^{p+1}/(p+1))$.
  Approximation extends these identities to the subcritical energy solutions.

* **29. Scaling and critical exponents.**
  $u_\lambda(t,x)=\lambda^{2/(p-1)}u(\lambda^2t,\lambda x)$
  preserves NLS. The invariant homogeneous regularity is
  $s_c=d/2-2/(p-1)$; $p=1+4/d$ is mass-critical and
  $p=1+4/(d-2)$ is energy-critical for $d\geq3$.

* **30. Defocusing subcritical global existence.** In the range of
  entry 27, conservation and the positive energy imply global $H^1$
  solutions for every $H^1$ datum in the defocusing case.

* **31. Small-data critical scattering.** The cubic NLS on $\mathbb R^3$
  has global solutions for sufficiently small $\dot H^{1/2}$ data,
  for either sign. They scatter to free Schrödinger solutions in
  $\dot H^{1/2}$ as $t\to\pm\infty$.

* **32. Virial blowup criterion.** For focusing NLS in the $H^1$
  subcritical or critical range with $p\geq1+4/d$, negative energy
  and finite variance $\int|x|^2|u_0|^2<\infty$ imply finite-time
  breakdown. The variance's second derivative is strictly negative
  under these hypotheses.

* **33. Mass-critical ground-state threshold.** Let $Q>0$ solve
  $-\Delta Q+Q=Q^{1+4/d}$. The sharp Gagliardo–Nirenberg inequality
  gives global $H^1$ existence for focusing mass-critical NLS when
  $\|u_0\|_2<\|Q\|_2$, through coercivity of the conserved energy.
  The threshold is sharp: the pseudo-conformal transform of the solitary
  wave $e^{it}Q$ blows up in finite time with mass exactly $\|Q\|_2$.

* **34. Morawetz estimates and intercritical scattering.** For
  defocusing NLS with $d\geq3$, finite-energy solutions satisfy
  $\int_{\mathbb R}\int|u|^{p+1}|x|^{-1}dx\,dt\leq
  C\sup_t\|u(t)\|_{\dot H^{1/2}}^2$ (Lin–Strauss). With this
  decay, every $H^1$ solution in the intercritical range
  $1+4/d<p<1+4/(d-2)$ scatters in $H^1$ in both time directions
  (Ginibre–Velo); interaction Morawetz estimates extend this to all $d$.

* **83. Bourgain spaces $X^{s,b}$.** With the spacetime Fourier
  transform $\widetilde u(\tau,\xi)$, set
  $\|u\|_{X^{s,b}}=\|\langle\xi\rangle^s\langle\tau+|\xi|^2\rangle^b
  \widetilde u\|_{L^2_{\tau,\xi}}$ for $iu_t+\Delta u=0$ (for the Airy
  equation $u_t+u_{xxx}=0$ the weight is $\langle\tau-\xi^3\rangle^b$).
  For $b>1/2$, $X^{s,b}\hookrightarrow C_tH^s$; for a time cutoff $\eta$,
  $\|\eta(t)e^{it\Delta}f\|_{X^{s,b}}\leq C\|f\|_{H^s}$ and the Duhamel
  term gains $\|\eta(t/T)\int_0^te^{i(t-t')\Delta}F\,dt'\|_{X^{s,b}}
  \leq CT^{1-b+b'}\|F\|_{X^{s,b'}}$ for $-1/2<b'\leq0\leq b\leq b'+1$.
  Free estimates transfer: a Strichartz bound for $e^{it\Delta}$ implies
  the same bound by $\|u\|_{X^{0,b}}$, $b>1/2$. Multilinear estimates in
  these spaces give low-regularity well-posedness where Strichartz
  estimates are unavailable: on $\mathbb T$,
  $\|u\|_{L^4_{t,x}}\leq C\|u\|_{X^{0,3/8}}$ makes cubic NLS globally well
  posed in $L^2(\mathbb T)$, and the bilinear bound
  $\|\partial_x(uv)\|_{X^{s,b-1}}\leq C\|u\|_{X^{s,b}}\|v\|_{X^{s,b}}$,
  $s>-3/4$, underlies entry 42 (Bourgain; Kenig–Ponce–Vega).

### Nonlinear waves and KdV

* **35. Wave dispersive estimate.** For $d\geq2$,
  $\|e^{it|D|}f\|_\infty\leq
  C|t|^{-(d-1)/2}\|f\|_{\dot B^{(d+1)/2}_{1,1}}$.
  The Besov derivative loss reflects the geometry of the wave cone.

* **36. Wave Strichartz estimates.** If $q\geq2$, $2\leq r<\infty$,
  $1/q+(d-1)/(2r)\leq(d-1)/4$, and
  $\gamma=d/2-d/r-1/q$, the free wave satisfies
  $\|u\|_{L_t^qL_x^r}\leq
  C(\|u_0\|_{\dot H^\gamma}+\|u_1\|_{\dot H^{\gamma-1}})$
  in the standard nontrivial admissible range, $d\geq2$.

* **37. Semilinear wave energy theory.** For
  $u_{tt}-\Delta u+|u|^{p-1}u=0$ in three dimensions,
  $1<p<5$, initial data in $H^1\times L^2$ give a unique global
  energy solution. Local existence uses Strichartz estimates and
  global continuation uses conserved positive energy and control of $\|u\|_2$.

* **38. Defocusing critical waves.** In three dimensions,
  $u_{tt}-\Delta u+u^5=0$ is globally well posed in
  $\dot H^1\times L^2$, and every finite-energy solution scatters
  to free waves in both time directions.

* **84. Profile decomposition.** Let $(u_{0,n},u_{1,n})$ be bounded in
  $\dot H^1\times L^2(\mathbb R^3)$ and $S(t)$ the free wave group.
  After passing to a subsequence there are free waves $V^j$ and
  parameters $(\lambda_n^j,t_n^j,x_n^j)\in(0,\infty)\times\mathbb R\times\mathbb R^3$,
  pairwise orthogonal in the sense
  $\lambda_n^j/\lambda_n^k+\lambda_n^k/\lambda_n^j
  +(|t_n^j-t_n^k|+|x_n^j-x_n^k|)/\lambda_n^j\to\infty$ for $j\ne k$,
  such that for every $J$
  $$
  S(t)(u_{0,n},u_{1,n})=\sum_{j=1}^J(\lambda_n^j)^{-1/2}
  V^j\Big(\frac{t-t_n^j}{\lambda_n^j},\frac{x-x_n^j}{\lambda_n^j}\Big)+w_n^J(t),
  $$
  with $\lim_{J\to\infty}\limsup_n\|w_n^J\|_{L^5_tL^{10}_x}=0$ and
  $\|(u_{0,n},u_{1,n})\|_{\dot H^1\times L^2}^2
  =\sum_{j\leq J}\|\vec V^j(0)\|_{\dot H^1\times L^2}^2
  +\|\vec w_n^J(0)\|_{\dot H^1\times L^2}^2+o(1)$ (Bahouri–Gérard).
  Analogous decompositions hold for $\dot H^1$ Schrödinger data (Keraani)
  and, with additional Galilean frequency parameters, for $L^2$ data
  (Merle–Vega). They quantify the defect of compactness of Strichartz
  estimates, modulo the symmetry group.

* **85. Concentration compactness and rigidity.** For the focusing
  energy-critical wave equation $u_{tt}-\Delta u=|u|^{4/(d-2)}u$,
  $d=3,4,5$, let $W(x)=(1+|x|^2/(d(d-2)))^{-(d-2)/2}$ be the static
  solution and $E(u,u_t)=\int(\tfrac12|\nabla u|^2+\tfrac12u_t^2
  -\tfrac{d-2}{2d}|u|^{2d/(d-2)})$. If $E(u_0,u_1)<E(W,0)$, then
  $\|\nabla u_0\|_2<\|\nabla W\|_2$ gives a global solution that scatters
  in both time directions, while $\|\nabla u_0\|_2>\|\nabla W\|_2$ gives
  finite-time blowup in both directions (Kenig–Merle). The focusing
  energy-critical NLS $iu_t+\Delta u=-|u|^{4/(d-2)}u$ obeys the same
  dichotomy for radial $\dot H^1$ data, $d=3,4,5$, with blowup on the
  second branch for radial finite-mass or finite-variance data. Method: if the threshold failed,
  the profile decomposition (entry 84) would produce a minimal-energy
  nonscattering critical element whose trajectory is precompact modulo
  symmetries; virial and Morawetz identities show that no such solution
  exists.

* **86. Vector fields and the Klainerman–Sobolev inequality.** The
  fields $Z\in\{\partial_\alpha,\ x_i\partial_j-x_j\partial_i,\
  t\partial_i+x_i\partial_t,\ t\partial_t+x\cdot\nabla\}$ generate the
  Poincaré group with scaling; they commute with $\square=\partial_t^2-\Delta$,
  except $[\square,t\partial_t+x\cdot\nabla]=2\square$. For smooth $u$ decaying
  in $x$,
  $(1+t+|x|)^{(d-1)/2}(1+|t-|x||)^{1/2}|u(t,x)|
  \leq C\sum_{|I|\leq\lfloor d/2\rfloor+1}\|Z^Iu(t,\cdot)\|_2$
  (Klainerman). Energy estimates for $Z^Iu$ thus give the
  $t^{-(d-1)/2}$ decay without Fourier representation: quadratic
  nonlinearities give small-data global existence for $d\geq4$, and in
  $d=3$ the extra decay of null forms in the good derivatives proves
  entry 39.

* **39. The null condition.** Small smooth compactly supported data
  give global solutions of three-dimensional semilinear wave systems
  whose nonlinearities are constant linear combinations of the null forms
  $Q_0(u,v)=u_tv_t-\nabla u\cdot\nabla v$ and
  $Q_{\alpha\beta}(u,v)=\partial_\alpha u\partial_\beta v
  -\partial_\beta u\partial_\alpha v$ (Klainerman, Christodoulou; also
  for quasilinear systems). Without the null condition the conclusion
  fails: $\square u=u_t^2$ blows up for suitable small data (John), while
  general quadratic nonlinearities give only almost global existence,
  with lifespan $\geq e^{c/\varepsilon}$ for data of size $\varepsilon$.

* **40. KdV conservation laws.** For $u_t+6uu_x+u_{xxx}=0$,
  sufficiently regular decaying solutions conserve
  $\int u$, $\int u^2$, and $\int(\tfrac12u_x^2-u^3)$.

* **41. KdV solitons.** For every $c>0$,
  $u(t,x)=\tfrac c2\operatorname{sech}^2(\tfrac{\sqrt c}{2}(x-ct-x_0))$
  is a traveling-wave solution. Solitons are orbitally stable in $H^1$:
  solutions starting near a soliton stay close, for all time, to its
  family of translates (Benjamin, Bona, Weinstein).

* **42. KdV global $L^2$ evolution.** The KdV Cauchy problem on
  $\mathbb R$ is globally well posed in $L^2$; local low-regularity
  theory and the conserved $L^2$ norm yield global continuation.

### Critical Schrödinger evolution and geometric hyperbolic equations

* **80. Defocusing critical Schrödinger evolution.** On $\mathbb R^3$,
  $iu_t+\Delta u=|u|^4u$ is globally well posed for
  $u_0\in\dot H^1$. Every such solution scatters in $\dot H^1$
  in both time directions; this requires global spacetime estimates
  beyond conservation of energy alone.
  See the [Colliander–Keel–Staffilani–Takaoka–Tao theorem](https://arxiv.org/abs/math/0402129).

* **81. Einstein constraint propagation and local existence.** Smooth
  Riemannian initial data $(g,k)$ satisfying
  $R_g-|k|_g^2+(\operatorname{tr}_gk)^2=0$ and
  $\operatorname{div}_g(k-(\operatorname{tr}_gk)g)=0$ admit a local
  vacuum Einstein development. Hyperbolic gauge reduction and the
  contracted Bianchi identity propagate the constraints.

* **82. Maximal globally hyperbolic development.** Vacuum initial data
  satisfying those constraints have a maximal globally hyperbolic
  development unique up to an isometry fixing the initial data.
  Maximality in this class does not assert geodesic completeness or
  exclude other extensions across a Cauchy horizon.

<a id="synopsis-34c"></a>

## 34C. Mathematical Fluid Dynamics

Euler, Navier–Stokes, and compressible-flow results follow 34C. Transport
renormalization, energy conservation at low regularity, and inviscid limits
are grouped with the fluid equations they support; transport also connects
with 34D.

### Incompressible Euler flow

The incompressible equations are
$u_t+u\cdot\nabla u+\nabla p=\nu\Delta u$, $\operatorname{div}u=0$,
with $\nu=0$ for Euler and $\nu>0$ for Navier–Stokes.

* **43. Leray projection.** On $\mathbb R^d$, the orthogonal projection
  onto divergence-free fields has Fourier matrix
  $I-\xi\otimes\xi/|\xi|^2$ and is bounded on $L^p$,
  $1<p<\infty$. Applying it eliminates pressure from the evolution.

* **44. Pressure recovery.** Smooth incompressible solutions satisfy
  $-\Delta p=\partial_i\partial_j(u_i u_j)$.
  Pressure is determined up to its normalization by the velocity
  through Riesz transforms, or the corresponding torus formula.

* **45. Euler local well-posedness.** Divergence-free data in $H^s$,
  $s>d/2+1$, give a unique local Euler solution of that regularity,
  continuously dependent on the data.

* **46. Vorticity transport and stretching.** In three dimensions,
  $\omega=\nabla\times u$ satisfies
  $\omega_t+u\cdot\nabla\omega=\omega\cdot\nabla u$.
  In two dimensions vorticity is scalar and the stretching term vanishes.

* **47. Biot–Savart reconstruction.** On $\mathbb R^3$, a decaying
  divergence-free velocity is $u=\nabla\times(-\Delta)^{-1}\omega$.
  In two dimensions it is $\nabla^\perp\Delta^{-1}\omega$ with
  $\nabla^\perp=(-\partial_2,\partial_1)$ and the usual scalar curl.

* **48. Beale–Kato–Majda criterion.** A three-dimensional smooth Euler
  solution in $H^s$, $s>5/2$, continues past $T$ if
  $\int_0^T\|\omega(t)\|_\infty dt<\infty$.

* **49. Two-dimensional smooth global flow.** Euler solutions with
  $H^s$ initial data, $s>2$, exist globally on $\mathbb R^2$ or
  $\mathbb T^2$. Conservation of the vorticity supremum prevents
  the three-dimensional stretching mechanism.

* **50. Yudovich uniqueness.** On $\mathbb T^2$, bounded initial
  vorticity and a prescribed mean velocity give a unique global weak
  Euler solution in the bounded-vorticity class. Its velocity is
  log-Lipschitz, so its particle trajectories are unique.

* **51. Kelvin's circulation theorem.** For smooth Euler flow,
  circulation $\oint_{\gamma_t}u\cdot dx$ is constant along every
  closed material curve transported by the flow.

* **52. Euler energy and helicity.** Smooth incompressible Euler flow
  conserves $\tfrac12\int|u|^2$; in three dimensions it also conserves
  helicity $\int u\cdot\omega$ under periodicity or sufficient decay.

### Navier–Stokes and compressible flow

* **53. Viscous energy identity.** Smooth unforced solutions satisfy
  $\tfrac12\|u(t)\|_2^2+\nu\int_0^t\|\nabla u\|_2^2
  =\tfrac12\|u_0\|_2^2$. Leray–Hopf solutions satisfy the
  corresponding inequality.

* **54. Leray–Hopf existence.** In three dimensions every divergence-free
  $L^2$ datum on $\mathbb R^3$ or $\mathbb T^3$ has a global weak
  solution in $L_t^\infty L_x^2\cap L_t^2\dot H_x^1$, weakly
  continuous in $L^2$, satisfying the energy inequality.

* **55. Two-dimensional viscous uniqueness.** In dimension two,
  energy-class Navier–Stokes solutions are unique and global.
  Smooth data give smooth solutions for every positive time.

* **56. Three-dimensional strong local solutions.** Initial data in
  divergence-free $H^1$ give a unique local strong Navier–Stokes
  solution. It agrees with every Leray–Hopf solution from the same
  data while the strong solution exists.

* **57. Prodi–Serrin criterion.** A three-dimensional Leray–Hopf solution
  satisfying $u\in L^q(0,T;L^r)$, $r>3$,
  $2/q+3/r\leq1$, is regular on positive times through $T$ and
  unique in the energy class on its interval of regularity. The
  endpoint $u\in L^\infty(0,T;L^3)$ also suffices
  (Escauriaza–Seregin–Šverák).

* **58. Small critical data.** Sufficiently small divergence-free data
  in $\dot H^{1/2}(\mathbb R^3)$ give a unique global mild
  Navier–Stokes solution in the associated critical evolution class.

* **59. Two-dimensional viscous vorticity bounds.** Vorticity satisfies
  $\omega_t+u\cdot\nabla\omega=\nu\Delta\omega$, so each
  $L^p$ vorticity norm, $1\leq p\leq\infty$, is nonincreasing
  whenever the initial norm is finite.

* **60. Suitable weak-solution partial regularity.** Three-dimensional
  suitable weak solutions satisfy a local energy inequality. Their
  interior singular set has zero one-dimensional parabolic Hausdorff
  measure, by the Caffarelli–Kohn–Nirenberg theorem.

* **61. The Stokes problem.** On a smooth bounded domain, the
  divergence-free zero-trace variational formulation of
  $-\nu\Delta u+\nabla p=f$, $\operatorname{div}u=0$, gives a
  unique velocity in $H_0^1$ and pressure in $L^2$ modulo constants
  for $f\in H^{-1}$. The inf–sup condition controls pressure.

* **62. Compressible Euler energy.** For smooth barotropic flow,
  $\rho_t+\operatorname{div}(\rho u)=0$ and
  $(\rho u)_t+\operatorname{div}(\rho u\otimes u)+\nabla p(\rho)=0$
  conserve $\int(\tfrac12\rho|u|^2+H(\rho))$, where
  $\rho H'(\rho)-H(\rho)=p(\rho)$. Positive sound speed gives
  symmetrizability away from vacuum.

* **63. Renormalized continuity equation.** Sufficiently regular
  solutions of the continuity equation obey
  $\partial_tb(\rho)+\operatorname{div}(b(\rho)u)
  +(\rho b'(\rho)-b(\rho))\operatorname{div}u=0$.
  Weak solutions satisfying this identity for all $C^1$ functions $b$
  with compactly supported derivative are called renormalized; this
  property is part of the compressible viscous existence theory.

* **64. Compressible viscous global existence.** In a smooth bounded
  three-dimensional domain with no-slip boundary, barotropic
  Navier–Stokes with $p(\rho)=a\rho^\gamma$, $a>0$, $\gamma>3/2$,
  $\mu>0$, and $\lambda+2\mu/3\geq0$ admits global finite-energy
  weak solutions from finite-energy data, including vacuum.
  The continuity equation is renormalized and the energy is dissipated.

### Transport renormalization, energy, and inviscid limits

* **77. DiPerna–Lions transport renormalization.** A vector field $w$ in
  $L^1_tW^{1,1}_{\mathrm{loc}}$ with divergence in $L^1_tL^\infty$
  and $w/(1+|x|)\in L^1_t(L^1_x+L^\infty_x)$ has unique
  renormalized transport solutions in $L^\infty_t(L^1\cap L^\infty)$
  for initial data in $L^1\cap L^\infty$. Commutator estimates justify the
  chain rule despite the absence of classical trajectories.

* **78. Energy equality beyond smooth flow.** On the torus, a weak
  Euler solution in $L^3_t C^\alpha_x$ with $\alpha>1/3$
  conserves kinetic energy (Constantin–E–Titi), by decay of the mollified
  nonlinear energy flux. Conversely, for every $\alpha<1/3$ there are
  weak solutions in $C_{t,x}^\alpha$ on $\mathbb T^3$ with strictly decreasing
  energy (convex integration; Isett, Buckmaster–De Lellis–Székelyhidi–Vicol),
  settling Onsager's conjecture.

* **79. Inviscid limit before smooth breakdown.** On a boundaryless
  domain, Navier–Stokes solutions with common smooth initial data
  converge to the smooth Euler solution on each compact time interval
  before Euler breakdown in $C_tL^2_x$, with convergence in lower
  Sobolev norms when the data have higher regularity. Physical
  boundaries require additional boundary-layer analysis.

<a id="synopsis-34d"></a>

## 34D. Kinetic Equations

Transport in phase space, Vlasov and Boltzmann equations, collision
invariants, entropy, hypocoercivity, and hydrodynamic limits follow 34D. The
limiting incompressible fluid equations are developed in 34C.

### Transport and kinetic equations

A kinetic density is $f(t,x,v)\geq0$. Collisionless transport is
$f_t+v\cdot\nabla_xf+E\cdot\nabla_vf=0$. The Boltzmann equation adds
$Q(f,f)$ on the right, where elastic binary collisions preserve
$v+v_*$ and $|v|^2+|v_*|^2$.

* **65. Characteristic transport.** For a smooth force field, $f$
  is constant along $\dot X=V$, $\dot V=E(t,X)$.
  The phase-space flow preserves Lebesgue measure, giving conservation
  of all finite $L^p$ norms and of $\int\Phi(f)$ when integrable.

* **66. Vlasov–Poisson invariants.** For repulsive Vlasov–Poisson on
  $\mathbb R^3$, $E=-\nabla\phi$, $-\Delta\phi=\int f\,dv$,
  smooth decaying solutions conserve mass, momentum, and
  $\tfrac12\iint|v|^2f+\tfrac12\int|E|^2$.

* **67. Global classical Vlasov–Poisson solutions.** Nonnegative smooth
  compactly supported data for the three-dimensional repulsive
  Vlasov–Poisson system generate a unique global classical solution.
  Control of velocity growth is the principal a priori step.

* **68. Velocity averaging.** If $f,g\in L^2$ solve
  $(\partial_t+v\cdot\nabla_x)f=g$, then
  $\int f(t,x,v)\psi(v)dv$ belongs locally to
  $H^{1/2}_{t,x}$ for $\psi\in C_c^\infty$.
  This yields compactness of velocity moments despite weak kinetic convergence.

* **69. Collision invariants.** For elastic Boltzmann collisions,
  $\int Q(f,f)\{1,v,|v|^2\}\,dv=0$ under the required integrability.
  These identities give local mass, momentum, and energy balance laws.

* **70. Boltzmann's $H$ theorem.**
  $\int Q(f,f)\log f\,dv\leq0$; the entropy production is an
  integral of $(a-b)\log(a/b)\geq0$ with the collision measure.
  Transport preserves total entropy in the absence of boundary flux.

* **71. Maxwellian equilibria.** Positive integrable velocity densities
  with zero entropy production are Maxwellians
  $M(v)=\rho(2\pi T)^{-d/2}e^{-|v-U|^2/(2T)}$,
  with $\rho,T>0$. They are exactly the positive equilibria of the
  elastic collision operator under its usual nondegeneracy assumptions.

* **72. Linearized collision coercivity.** For hard-sphere collisions,
  writing $f=M(1+h)$ gives a nonnegative self-adjoint linearized
  operator on $L^2(M\,dv)$. Its kernel is
  $\operatorname{span}\{1,v_1,\ldots,v_d,|v|^2\}$ and it has a
  positive spectral gap on the orthogonal complement.

* **73. Renormalized Boltzmann existence.** For hard-sphere collisions
  on the spatial torus, finite mass, energy, and entropy initial data
  admit global nonnegative renormalized solutions satisfying the
  entropy inequality. Admissible renormalizations, for example satisfying
  $|\beta'(z)|\leq C/(1+z)$, make $\beta'(f)Q(f,f)$ meaningful.

* **74. Entropy controls distance from equilibrium.** For probability
  densities $f,M$, $\|f-M\|_1^2\leq2\int f\log(f/M)$.
  Thus decay of relative entropy gives strong convergence in mass norm.

* **75. Hypocoercive kinetic relaxation.** On $\mathbb T^d_x\times
  \mathbb R^d_v$, the equation
  $f_t+v\cdot\nabla_xf=\Delta_vf+\operatorname{div}_v(vf)$
  converges exponentially in $L^2(M^{-1}dx\,dv)$ to its mass-matched
  spatially uniform Gaussian equilibrium for data in that space.
  Transport couples the undiffused variables to the velocity dissipation.

* **76. Incompressible Navier–Stokes limit.** On $\mathbb T^3$, let $f_\varepsilon$
  be renormalized solutions of
  $\varepsilon\partial_tf+v\cdot\nabla_xf=\varepsilon^{-1}Q(f,f)$ for
  cutoff hard potentials, with $f_\varepsilon=M(1+\varepsilon g_\varepsilon)$ and initial
  relative entropy $O(\varepsilon^2)$. Then the moments
  $\int g_\varepsilon\,v\,M\,dv$ and $\int g_\varepsilon(|v|^2/5-1)M\,dv$
  converge, along subsequences, to a Leray solution of the
  incompressible Navier–Stokes–Fourier system (Golse–Saint-Raymond).

## Reference guide

### Correspondence with the subdivisions

- **[34A](#synopsis-34a)**: Dafermos, Bressan, Serre, Lax, and Holden–Risebro
  supply the hyperbolic and conservation-law core.
- **[34B](#synopsis-34b)**: The dispersive, nonlinear-wave, and
  general-relativity references support both the analytic estimates and the
  geometric Cauchy statements.
- **[34C](#synopsis-34c)**: The Euler, Navier–Stokes, and compressible-flow
  references support smooth and weak solutions, transport, conservation, and
  fluid limits.
- **[34D](#synopsis-34d)**: Cercignani–Illner–Pulvirenti, Glassey, Villani,
  and Saint-Raymond supply kinetic and hydrodynamic-limit viewpoints.

### Source comparisons and local copies

Dafermos, Bressan, Serre, Lax, and Holden–Risebro overlap on entropy,
Riemann problems, and small-BV systems; Dafermos and Serre also treat
compensated compactness. Tao, Cazenave, Linares–Ponce,
Sogge, and Bahouri–Chemin–Danchin provide the dispersive and nonlinear-wave
core; Bourgain and Erdoğan–Tzirakis develop the $X^{s,b}$ method, Sogge the
vector-field method, and Kenig and Krieger–Schlag the concentration-compactness
and rigidity route. Majda–Bertozzi, Chemin, Temam, Galdi, and the later Navier–Stokes
texts distinguish smooth incompressible dynamics from weak viscous theory.
Lions and Feireisl–Novotný provide compressible existence theory.
Cercignani–Illner–Pulvirenti, Glassey, Villani, and Saint-Raymond supply
the kinetic viewpoints. The Einstein Cauchy theorems are the common
starting point of the listed general-relativity monographs; their detailed
stability, shock, and black-hole theorems are further specialized inventories.

Local source copies consulted:

* [Dafermos, *Hyperbolic Conservation Laws in Continuum Physics*](References/Dafermos2016HyperbolicConservationLawsContinuumPhysics4thEd-SpringerGL325.pdf).
* [Serre, *Systems of Conservation Laws*, I](References/Serre1999SystemsConservationLaws1HyperbolicityEntropiesShockWaves-Cambridge.pdf).
* [Holden–Risebro, *Front Tracking for Hyperbolic Conservation Laws*](References/HoldenRisebro2015FrontTrackingHyperbolicConservationLaws2ndEd-SpringerAMS152.pdf).
* [Linares–Ponce, *Introduction to Nonlinear Dispersive Equations*](References/LinaresPonce2015IntroductionNonlinearDispersiveEquations2ndEd-SpringerUTX.pdf).
* [Bahouri–Chemin–Danchin, *Fourier Analysis and Nonlinear Partial Differential Equations*](References/BahouriCheminDanchin2011FourierAnalysisNonlinearPartialDifferentialEquations-SpringerGL343.pdf).
* [Majda–Bertozzi, *Vorticity and Incompressible Flow*](References/MajdaBertozzi2001VorticityIncompressibleFlow-CambridgeTextsAM27.pdf).
* [Robinson–Rodrigo–Sadowski, *The Three-Dimensional Navier–Stokes Equations*](References/RobinsonRodrigoSadowski2016ThreeDimensionalNavierStokesEquations-CambridgeStudiesAM157.pdf).
* [Feireisl–Novotný, *Singular Limits in Thermodynamics of Viscous Fluids*](References/FeireislNovotny2017SingularLimitsThermodynamicsViscousFluids2ndEd-SpringerAMFM.pdf).
* [Saint-Raymond, *Hydrodynamic Limits of the Boltzmann Equation*](References/SaintRaymond2009HydrodynamicLimitsBoltzmannEquation-SpringerLNM1971.pdf).

The geometric Cauchy statements were also checked against
[Chruściel–Galloway–Pollack, *Mathematical General Relativity: A Sampler*, Sections 4–6](https://www.math.miami.edu/~galloway/papers/cgpbams.pdf).
The dispersive selection was compared with
[Tao's author-posted *Nonlinear Dispersive Equations*](https://www.math.ucla.edu/~tao/preprints/chapter.pdf).
