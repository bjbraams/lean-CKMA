# Synopsis: Potential theory and capacity

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-38);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring material from Section 38 of
[CKMA-bib.md](CKMA-bib.md#ckma-38).
It covers harmonic and superharmonic functions, equilibrium and capacity,
the Dirichlet problem and boundary regularity, probabilistic representations,
nonlinear potentials, Riesz potentials, logarithmic and analytic capacity,
harmonic approximation, and the axiomatic viewpoint. Metric-space
diffusion and Dirichlet forms receive a separate treatment in Section 39.

The current subdivision [39B](CKMA-bib.md#ckma-39b) collects Dirichlet forms,
heat kernels, and diffusion on graphs and fractals;
[08B](CKMA-bib.md#ckma-08b) supplies the stochastic-process viewpoint and
[39C](CKMA-bib.md#ckma-39c) the transport and gradient-flow connections.

For Newtonian theory assume $n\geq3$ and use
$$
\Gamma(x)=\frac{|x|^{2-n}}{(n-2)|S^{n-1}|},\qquad -\Delta\Gamma=\delta_0.
$$
Thus $U^\mu=\Gamma*\mu$ and $I(\mu)=\iint\Gamma(x-y)d\mu(x)d\mu(y)$.
Planar logarithmic theory has its own normalization below. A property holds
**quasi-everywhere** when its exceptional set has zero capacity of the
specified kind. Domains are connected; boundary domains are bounded unless
another assumption is stated.

## Harmonic, subharmonic, and superharmonic functions

* **1. Mean values and maximum principles.** Harmonic functions equal
  their spherical and ball averages. A continuous function with the
  local mean-value property is harmonic, and so is every distribution
  $u$ with $\Delta u=0$ (Weyl's lemma). Interior extrema force
  constancy, and continuous Dirichlet solutions are unique on bounded domains.
* **2. Poisson representation on balls.** Continuous data on a sphere
  have a unique continuous harmonic extension given by the Poisson
  integral. Every positive harmonic function in a ball is the Poisson
  integral of a unique finite positive boundary measure.
* **3. Fatou's theorem.** The Poisson integral of a finite signed
  measure $\mu$ on the unit sphere has nontangential limit
  $d\mu/d\sigma$ at $\sigma$-almost every boundary point. Hence
  positive and bounded harmonic functions in the ball have nontangential
  boundary values almost everywhere; for Lipschitz domains the analogue
  holds with respect to harmonic measure (Hunt–Wheeden).
* **4. Harnack inequality.** Positive harmonic functions satisfy
  $\sup_Ku\leq C_K\inf_Ku$ on compact subsets connected by a
  fixed chain of interior balls. A nonnegative harmonic function is
  either strictly positive or zero, and a harmonic function on
  $\mathbb R^n$ bounded below (or above) is constant (Liouville).
* **5. Harnack convergence.** An increasing sequence of harmonic
  functions is either locally uniformly divergent to infinity or
  converges locally uniformly to a harmonic function on the domain.
* **6. Interior estimates and analyticity.** Harmonic derivatives of
  order $k$ on a smaller ball are bounded by $C_kr^{-k}$ times
  the supremum on a larger ball. Harmonic functions are analytic,
  and locally bounded families are locally precompact in every $C^k$ norm.
* **7. Kelvin transformation.** For $n\geq3$,
  $Ku(x)=|x|^{2-n}u(x/|x|^2)$ preserves harmonicity on inverted
  domains away from zero. It converts behavior at infinity into
  behavior near an isolated point.
* **8. Bôcher's theorem.** A positive harmonic function on a punctured
  ball is $c\Gamma+h$, $c\geq0$, with $h$ harmonic across the
  puncture. In two dimensions the singular term is a nonnegative
  multiple of $\log(1/|x|)$.
* **9. Distributional characterization.** A subharmonic function is
  upper semicontinuous, locally integrable, not identically $-\infty$,
  and satisfies the sub-mean inequality; equivalently its distributional
  Laplacian is a positive measure, with the canonical representative.
  Superharmonic functions have the opposite signs and lower semicontinuity.
* **10. Riesz decomposition.** A nonnegative superharmonic function on
  a Greenian domain has a unique decomposition $u=G\mu+h$,
  where $\mu=-\Delta u$, $h\geq0$ is harmonic, and $G\mu$
  is a Green potential. Local versions hold on relatively compact subdomains.
* **11. Superharmonic minimum principle.** A superharmonic function
  bounded below on a bounded domain, with nonnegative boundary
  liminf, is nonnegative. Finite minima of superharmonic functions
  remain superharmonic; arbitrary infima require lower regularization.
* **12. Green functions.** Every bounded domain in $\mathbb R^n$,
  $n\geq2$, has a positive Green function for $-\Delta$.
  It is harmonic off its pole and vanishes at regular boundary points.
  A general domain admitting such a function is called Greenian.
* **13. Green symmetry and domain monotonicity.**
  $G_\Omega(x,y)=G_\Omega(y,x)$, and
  $G_{\Omega_1}\leq G_{\Omega_2}$ if $\Omega_1\subset\Omega_2$.
  Increasing exhaustion of a Greenian domain gives increasing
  convergence of the Green kernels.
* **14. Potential domination.** For a positive compactly supported
  finite-energy Newtonian measure $\mu$ and any positive measure $\nu$
  with $U^\nu\not\equiv\infty$, $U^\mu\leq U^\nu+c$
  $\mu$-almost everywhere, $c\geq0$, implies that inequality
  everywhere. In particular a potential bounded by a constant on
  its supporting charge is bounded by that constant everywhere.
* **15. Continuity principle.** If $\mu\geq0$ has compact support and
  the restriction of $U^\mu$ to $\operatorname{supp}\mu$ is finite and
  continuous, then $U^\mu$ is continuous on $\mathbb R^n$
  (Evans–Vasilesco). Every finite-energy measure is an increasing limit
  of measures with continuous potentials.

## Newtonian capacity, equilibrium, and thinness

For compact $K$ define
$\operatorname{Cap}(K)=\inf\{\int_{\mathbb R^n}|\nabla\phi|^2:
\phi\in C_c^\infty,\ \phi\geq1\text{ near }K\}$.
Extend first to open sets by compact exhaustion and then to arbitrary
sets by outer approximation.

* **16. Energy duality.**
  $\operatorname{Cap}(K)^{-1}=\inf_{\mu(K)=1,\,\mu\geq0}I(\mu)$,
  with $1/0=\infty$. Positive capacity is equivalent to supporting
  a nonzero finite-energy measure.
* **17. Equilibrium measure.** If $K$ has positive capacity, there is
  a unique equilibrium charge $\nu_K$ supported on $K$ such that
  $\nu_K(K)=\operatorname{Cap}(K)$,
  $U^{\nu_K}=1$ quasi-everywhere on $K$, and $U^{\nu_K}\leq1$
  everywhere. Its energy is $I(\nu_K)=\operatorname{Cap}(K)$.
  For a zero-capacity compact set the capacitary measure and potential are zero.
* **18. Variational capacitary potential.** The equilibrium potential
  minimizes Dirichlet energy among homogeneous $H^1$ functions at
  least one quasi-everywhere on $K$. Its energy is the capacity;
  it is harmonic outside $K$ and decays at infinity.
* **19. Ball capacity and scaling.**
  $\operatorname{Cap}(\overline B_r)=(n-2)|S^{n-1}|r^{n-2}$ and
  $\operatorname{Cap}(aK)=a^{n-2}\operatorname{Cap}(K)$ for $a>0$.
* **20. Choquet properties.** Capacity is monotone, continuous on
  increasing sequences of sets and decreasing sequences of compact
  sets, and countably subadditive. Analytic sets, in particular Borel
  sets, are capacitable: outer capacity equals the supremum of compact
  subcapacities.
* **21. Polar sets.** A set has zero Newtonian capacity exactly when
  it is contained in the infinity set of a positive superharmonic
  function, locally in the ambient domain. Such sets are called polar.
* **22. Finite-energy measures avoid polar sets.** A positive measure
  of finite Newtonian energy charges no set of zero capacity.
  Its potential is finite quasi-everywhere and has a quasi-continuous representative.
* **23. Quasi-continuity.** Sobolev and finite-energy potential
  representatives are continuous outside open sets of arbitrarily
  small capacity. Equal Sobolev elements have representatives equal
  quasi-everywhere, a stronger precision than almost-everywhere equality.
* **24. Fine topology and thinness.** The fine topology is the coarsest
  topology making superharmonic functions continuous. A set $E$ is
  thin at $x$ exactly when it fails to accumulate there or a
  superharmonic $v$ satisfies
  $v(x)<\liminf_{E\setminus\{x\}\ni y\to x}v(y)$.
  Fine neighborhoods have thin complements.
* **25. Reduction and sweeping.** For nonnegative superharmonic $u$,
  the lower semicontinuous regularization of
  $\inf\{v\geq0:v\text{ superharmonic},\ v\geq u\text{ on }E\}$
  is the balayage of $u$ onto $E$. It is at most $u$, agrees with
  it quasi-everywhere on $E$, and is harmonic outside $\overline E$.
* **26. Balayage of charges.** Sweeping a compactly supported positive
  charge onto a compact set gives a charge there whose potential
  agrees with the original potential quasi-everywhere on the set and
  is no larger elsewhere. The swept mass does not exceed the original mass.
* **27. Removability.** A bounded harmonic function off a relatively
  closed polar subset of a domain extends uniquely harmonically across
  it. Polar exceptional sets are therefore invisible to bounded
  harmonic Dirichlet theory.

## The Dirichlet problem, harmonic measure, and ideal boundaries

* **28. Perron–Wiener solution.** Upper superharmonic and lower
  subharmonic envelopes agree for continuous boundary data on a bounded
  domain. Their common value is harmonic even if some boundary points
  are irregular.
* **29. Barrier criterion.** A boundary point is regular for every
  continuous datum exactly when it admits a positive local superharmonic
  barrier tending to zero there and bounded away from zero outside
  each smaller neighborhood.
* **30. Wiener's criterion.** For $n\geq3$, a boundary point $x_0$
  is regular exactly when
  $\sum_{k\geq1}2^{k(n-2)}\operatorname{Cap}(E_k)=\infty$,
  where $E_k=(\mathbb R^n\setminus\Omega)\cap
  \{2^{-k-1}\leq|x-x_0|\leq2^{-k}\}$. Equivalently, $x_0$ is
  regular exactly when $\mathbb R^n\setminus\Omega$ is not thin at $x_0$;
  Wiener's series is a capacitary test for thinness.
* **31. Geometric sufficient conditions.** An exterior cone at a
  boundary point supplies a barrier. In particular Lipschitz domains
  are regular, whereas for $n\geq3$ a sufficiently thin exterior cusp
  (Lebesgue's spine) can be irregular. In the plane, a boundary point
  lying in a nondegenerate continuum of the complement is regular.
* **32. Kellogg's theorem.** The irregular boundary points form a
  polar set. Thus every continuous boundary datum is attained
  quasi-everywhere on the boundary.
* **33. Harmonic measure.** For each $x\in\Omega$, there is a
  probability measure $\omega^x$ on $\partial\Omega$ such that
  $H_f(x)=\int f\,d\omega^x$ for continuous $f$.
  Null sets of harmonic measure are independent of the pole in a
  connected domain.
* **34. Boundary Harnack principle.** In a Lipschitz domain, positive
  harmonic functions vanishing on a common boundary patch have
  comparable ratios on smaller patches after interior normalization.
  The ratio extends Hölder continuously to the smaller boundary patch.
* **35. Dahlberg's theorem.** On a bounded Lipschitz domain, harmonic
  measure and surface measure are mutually absolutely continuous.
  The Poisson kernel satisfies quantitative local reverse Hölder
  estimates, equivalently the local $A_\infty$ property of harmonic measure.
* **36. Planar harmonic measure.** For a simply connected planar domain
  bounded by a rectifiable Jordan curve, harmonic measure and arc length
  are mutually absolutely continuous (F. and M. Riesz). For every simply
  connected planar domain, harmonic measure is carried by a set of
  $\sigma$-finite length and vanishes on sets of Hausdorff dimension
  less than one (Makarov); for arbitrary planar domains it is carried
  by a set of dimension at most one (Jones–Wolff).
* **37. Martin representation.** Fixing $x_*\in\Omega$, the normalized
  kernels $G(x,y)/G(x_*,y)$ define the Martin compactification.
  Every positive harmonic function has a unique representation as
  an integral of normalized minimal kernels over the minimal Martin
  boundary; the representing mass is $h(x_*)$.
* **38. Smooth-domain Martin boundary.** For bounded $C^{1,1}$ domains,
  the Martin boundary identifies with the Euclidean boundary, and
  Martin kernels are normalized Poisson kernels. The identification
  persists for bounded Lipschitz domains (Hunt–Wheeden) and NTA domains
  (Jerison–Kenig), with kernels $d\omega^x/d\omega^{x_*}$. In general the
  Euclidean boundary may not parametrize all minimal harmonic functions.

## Brownian interpretations

Brownian motion here has generator $\tfrac12\Delta$, whereas Green
functions above invert $-\Delta$. This accounts for the factor two below.
The Brownian solution of the Dirichlet problem (harmonic measure as exit
distribution) and recurrence and transience are SYNOPSIS08, items 58 and 5.

* **40. Occupation kernel.** For nonnegative Borel $f$,
  $\mathbb E_x\int_0^{\tau_\Omega}f(B_t)dt
  =2\int_\Omega G_\Omega(x,y)f(y)dy$.
* **41. Equilibrium as hitting probability.** For compact $K$ in
  $\mathbb R^n$, $n\geq3$, its equilibrium potential equals
  $\mathbb P_x(\tau_K<\infty)$ outside $K$.
  A compact polar set is hit with probability zero from outside it.

## Riesz potentials and stable processes

For $0<\alpha<n$ let
$k_\alpha(x)=c_{n,\alpha}|x|^{\alpha-n}$,
$c_{n,\alpha}=\Gamma(\tfrac{n-\alpha}2)/(2^\alpha\pi^{n/2}\Gamma(\tfrac\alpha2))$,
so that $\widehat{k_\alpha}(\xi)=|\xi|^{-\alpha}$ and $k_\alpha*$ inverts
$(-\Delta)^{\alpha/2}$; $k_2=\Gamma$ for $n\geq3$. Write
$U_\alpha^\mu=k_\alpha*\mu$ and $I_\alpha(\mu)=\iint k_\alpha(x-y)d\mu\,d\mu$.

* **68. Riesz composition and energy.** $k_\alpha*k_\beta=k_{\alpha+\beta}$
  for $\alpha+\beta<n$. For signed measures of finite energy,
  $I_\alpha(\mu)=(2\pi)^{-n}\int|\widehat\mu(\xi)|^2|\xi|^{-\alpha}d\xi\geq0$,
  with equality only for $\mu=0$; the energy is a scalar product, and the
  cone of positive finite-energy measures is complete in its norm
  (Cartan for $\alpha=2$; Landkof). The whole space of signed
  finite-energy measures is not complete.
* **69. Riesz capacity and equilibrium.** For compact $K$ set
  $C_\alpha(K)=(\inf_{\mu\in\mathcal P(K)}I_\alpha(\mu))^{-1}$; then
  $C_\alpha(aK)=a^{n-\alpha}C_\alpha(K)$, and $C_\alpha(E)=0$ when
  $\mathcal H^{n-\alpha}(E)<\infty$, while compact sets of dimension
  greater than $n-\alpha$ have positive capacity (cf. SYNOPSIS37, item 5).
  For $0<\alpha\leq2$ the Frostman maximum principle holds: $U_\alpha^\mu\leq1$
  on $\operatorname{supp}\mu$ implies $U_\alpha^\mu\leq1$ everywhere. Hence
  a compact $K$ of positive capacity has an equilibrium measure $\lambda_K$
  with $\lambda_K(K)=C_\alpha(K)$, $U_\alpha^{\lambda_K}=1$ quasi-everywhere
  on $K$, and $U_\alpha^{\lambda_K}\leq1$ everywhere. For $2<\alpha<n$ the
  maximum principle holds only with the constant $2^{n-\alpha}$. For
  $0<\alpha<2$ the equilibrium measure of a closed ball has density
  proportional to $(r^2-|x|^2)^{-\alpha/2}$ on the ball, not on its sphere
  (M. Riesz).
* **70. Stable processes and $\alpha$-harmonic functions.** For
  $0<\alpha<2$, $-(-\Delta)^{\alpha/2}$ generates the rotation-invariant
  $\alpha$-stable Lévy process $X$, transient when $\alpha<n$, with
  occupation kernel $k_\alpha$ and
  $\mathbb P_x(T_K<\infty)=U_\alpha^{\lambda_K}(x)$ for the hitting time of
  compact $K$. A function is $\alpha$-harmonic in $D$ if
  $u(x)=\mathbb E_xu(X_{\tau_D})$; since $X$ jumps, Dirichlet data are
  prescribed on all of $\mathbb R^n\setminus D$. For the ball $B_r$ the exit
  distribution has density
  $P_r(x,y)=\Gamma(\tfrac n2)\pi^{-n/2-1}\sin(\tfrac{\pi\alpha}2)
  \big(\tfrac{r^2-|x|^2}{|y|^2-r^2}\big)^{\alpha/2}|x-y|^{-n}$ for
  $|x|<r<|y|$ (M. Riesz). Nonnegative $\alpha$-harmonic functions satisfy
  Harnack and boundary Harnack principles, the latter on Lipschitz and
  indeed arbitrary open sets (Bogdan; Bogdan–Kulczycki–Kwaśnicki).

## Sobolev capacity and nonlinear potential theory

For $1<p<\infty$, the relative **$p$-capacity** is
$\operatorname{cap}_p(K,\Omega)=\inf\int_\Omega|\nabla\phi|^p$,
over $\phi\in C_c^\infty(\Omega)$ at least one near $K$.
A **$p$-superharmonic function** is lower semicontinuous, finite on a
dense set, and satisfies comparison with continuous $p$-harmonic functions
on relatively compact subdomains. Quasicontinuity of Sobolev functions and
the capacitary description of $W_0^{1,p}$ are SYNOPSIS26, items 31 and 33.

* **43. Capacitary minimization.** For compact $K\Subset\Omega$,
  minimization over $W_0^{1,p}$ functions at least one quasi-everywhere
  on $K$ gives the unique capacitary potential. It is $p$-harmonic
  outside $K$ and has energy $\operatorname{cap}_p(K,\Omega)$.
* **45. Nonlinear comparison.** Weak $p$-harmonic solutions with ordered
  Sobolev boundary data are ordered. The comparison definition extends
  the theory to $p$-superharmonic functions outside the energy class.
* **46. Nonlinear Perron theory.** Continuous boundary data on bounded
  domains are resolutive for the $p$-Laplace equation. Perron solutions
  attain them at regular points. For $p\ne2$ this solution operator
  is nonlinear and does not define an additive harmonic measure.
* **47. Nonlinear Wiener criterion.** A boundary point $x_0$ is
  regular exactly when
  $$
  \int_0^{r_0}\left(
  \frac{\operatorname{cap}_p((\mathbb R^n\setminus\Omega)\cap\overline B_r(x_0),B_{2r}(x_0))}
       {\operatorname{cap}_p(\overline B_r(x_0),B_{2r}(x_0))}
  \right)^{1/(p-1)}\frac{dr}{r}=\infty.
  $$
  Sufficiency is due to Maz'ya and necessity to Kilpeläinen–Malý.
* **48. Nonlinear fundamental solution and scaling.** For $1<p<n$,
  a normalized positive multiple of $|x|^{(p-n)/(p-1)}$ solves
  $-\Delta_pu=\delta_0$, and
  $\operatorname{cap}_p(\overline B_r,B_{2r})=C_{n,p}r^{n-p}$.
  At $p=n$ the fundamental singularity is logarithmic. For $p>n$ the
  fundamental solution is bounded and continuous at the origin, and
  points have positive $p$-capacity.
* **49. Wolff potential estimates.** For $1<p<n$ define
  $\mathbf W_{1,p}^\mu(x,R)=\int_0^R
  (\mu(B_r(x))/r^{n-p})^{1/(p-1)}dr/r$.
  If $u\geq0$ is $p$-superharmonic and $-\Delta_pu=\mu$,
  then $\mathbf W_{1,p}^\mu(x,R)\leq Cu(x)$ and
  $u(x)\leq C\inf_{B_R(x)}u+C\mathbf W_{1,p}^\mu(x,2R)$
  when $B_{2R}(x)$ is interior.
* **50. Capacitary strong estimate.** For $u\in C_c^\infty(\Omega)$,
  $\int_0^\infty\operatorname{cap}_p(\{|u|>t\},\Omega)
  \,d(t^p)\leq C_p\int|\nabla u|^p$.
  Truncation turns energy control into control of exceptional level sets.
* **51. Dimension thresholds.** If $1<p<n$, sets of dimension
  strictly below $n-p$ have zero $p$-capacity; compact sets of
  dimension strictly above $n-p$ have positive capacity. More
  precisely, $\mathcal H^{n-p}(E)<\infty$ implies zero $p$-capacity,
  while zero $p$-capacity implies $\mathcal H^s(E)=0$ for every $s>n-p$;
  for $p=2$ these are the Newtonian thresholds.
* **52. Removable $p$-polar singularities.** A bounded $p$-harmonic
  function off a relatively closed set of zero $p$-capacity extends
  uniquely $p$-harmonically across that set.

The **Bessel capacity** $C_{\alpha,p}$ is the infimum of $\|f\|_p^p$
over nonnegative $f$ with $G_\alpha*f\geq1$ on the set, where
$\widehat G_\alpha(\xi)=(1+|\xi|^2)^{-\alpha/2}$ using $e^{-ix\cdot\xi}$.

* **53. Bessel–Sobolev correspondence.** Bessel capacities control
  exceptional sets of Bessel potential spaces $H^{\alpha,p}$.
  At integer order one they agree, up to fixed constants on bounded
  regions, with the inhomogeneous Sobolev capacity; local relative
  capacities give the zero-boundary counterpart.
* **54. Absorption equations with measure data.** On a bounded smooth
  domain, for $q>1$ and finite positive $\mu$, the zero-Dirichlet
  problem $-\Delta u+u^q=\mu$ has a nonnegative weak solution
  exactly when $\mu$ vanishes on sets of zero $C_{2,q'}$ capacity.
  This is the capacitary criterion for admissible measure data.

## Logarithmic potentials and equilibrium in the plane

For compact $K\subset\mathbb C$, set
$I_{\log}(\mu)=\iint\log(1/|z-w|)d\mu(z)d\mu(w)$,
$V_K=\inf_{\mu\in\mathcal P(K)}I_{\log}(\mu)$, and
$\operatorname{cap}_{\log}(K)=e^{-V_K}$. The Bernstein–Walsh inequality
is SYNOPSIS47, item 37.

* **55. Jensen's formula for subharmonic functions.** If
  $\mu=(2\pi)^{-1}\Delta u$ and $u(0)>-\infty$, then
  $\fint_{|z|=r}u-u(0)=\int_0^r\mu(B_t)dt/t$
  for admissible radii in the disk. For $u=\log|f|$, this counts
  analytic zeros with multiplicity.
* **56. Logarithmic equilibrium.** A compact set of positive logarithmic
  capacity has a unique probability measure minimizing logarithmic energy.
  Sets of zero capacity are precisely planar polar sets.
* **57. Frostman's theorem.** The equilibrium potential satisfies
  $U^{\mu_K}_{\log}=V_K$ quasi-everywhere on $K$ and
  $U^{\mu_K}_{\log}\leq V_K$ everywhere in the plane.
* **58. Green function with pole at infinity.** On the unbounded
  complementary component of $K$,
  $g_K(z,\infty)=V_K-U^{\mu_K}_{\log}(z)$ and
  $g_K(z,\infty)=\log|z|-\log\operatorname{cap}_{\log}(K)+o(1)$
  at infinity.
* **59. Conformal characterization.** If that component is simply
  connected and its conformal map to $|w|>1$ is
  $\phi(z)=z/c+O(1)$ at infinity, $c>0$, then
  $g_K=\log|\phi|$ and $\operatorname{cap}_{\log}(K)=c$.
  A radius-$R$ disk has capacity $R$; an interval of length $\ell$
  has capacity $\ell/4$.
* **60. Transfinite diameter.**
  $\lim_{N\to\infty}\max_{z_1,\ldots,z_N\in K}
  \prod_{i<j}|z_i-z_j|^{2/(N(N-1))}=\operatorname{cap}_{\log}(K)$.
* **61. Fekete-point distribution.** For positive-capacity compact
  $K$, empirical measures of maximizing Fekete configurations converge
  weakly to $\mu_K$. Discrete repulsion selects the continuous
  equilibrium charge.
* **62. Weighted equilibrium.** For a lower semicontinuous
  external field $Q:K\to\mathbb R\cup\{\infty\}$ on compact $K$,
  with a finite weighted-energy competitor,
  $I_{\log}(\mu)+2\int Qd\mu$ has a unique minimizer.
  Its potential satisfies $U^\mu_{\log}+Q\geq F$ quasi-everywhere
  on $K$ and equality $\mu$-almost everywhere, for a constant $F$.

## Analytic capacity and removability

For compact $E\subset\mathbb C$, **analytic capacity** is
$\gamma(E)=\sup|f'(\infty)|$, over holomorphic functions on
$\widehat{\mathbb C}\setminus E$ with $|f|\leq1$ and $f(\infty)=0$,
where $f'(\infty)=\lim_{z\to\infty}zf(z)$. Removability of compact sets
of finite length (Painlevé's problem) is SYNOPSIS37, item 67.

* **64. Analytic removability criterion.** $\gamma(E)=0$ exactly when
  $E$ is removable for bounded holomorphic functions. Analytic capacity
  is monotone and scales by $\gamma(aE+b)=|a|\gamma(E)$.
* **65. Positive-measure characterization.** Analytic capacity is
  comparable, with absolute constants, to the supremum of $\mu(E)$
  over positive measures supported on $E$ whose Cauchy transform
  $\int(z-w)^{-1}d\mu(w)$ is bounded in absolute value by one
  at Lebesgue-almost every point of the plane.
* **66. Countable semiadditivity.** There is an absolute $C$ such that
  $\gamma(\bigcup_jE_j)\leq C\sum_j\gamma(E_j)$, with the
  standard inner-capacity extension to noncompact Borel sets $E_j$.

## Harmonic approximation

For compact $K\subset\mathbb R^n$, $\widehat K$ is the union of $K$ with the
bounded components of $\mathbb R^n\setminus K$, and $\Omega^*$ is the
one-point compactification of an open set $\Omega$.

* **71. Compact sets.** If $\mathbb R^n\setminus K$ is connected, every
  function harmonic on a neighborhood of $K$ is a uniform limit on $K$ of
  harmonic polynomials (Walsh); unlike Runge's theorem, connectedness is
  sufficient but not necessary, and the exact condition is that
  $\mathbb R^n\setminus\widehat K$ and $\mathbb R^n\setminus K$ are thin at
  the same points of $K$ (Gardiner). Every $u\in C(K)$ harmonic on the
  interior $K^\circ$ is a uniform limit on $K$ of functions harmonic on
  neighborhoods of $K$ exactly when $\mathbb R^n\setminus K$ and
  $\mathbb R^n\setminus K^\circ$ are thin at the same points of $K$
  (Keldysh; Deny). Fine potential theory thus replaces the topological
  conditions of complex approximation.
* **72. Closed sets.** Let $\Omega\subset\mathbb R^n$ be open and
  $E\subset\Omega$ relatively closed. If $\Omega^*\setminus E$ is connected
  and locally connected, every function harmonic on an open set containing
  $E$ is, for each $\varepsilon>0$, within $\varepsilon$ of a function
  harmonic on $\Omega$ uniformly on $E$ (Gauthier–Goldstein–Ow), the
  harmonic analogue of Arakelyan's theorem. As for compact sets, the
  condition is sufficient but not necessary; Gardiner characterizes the
  sets admitting such approximation through thinness.

## Axiomatic potential theory

* **73. Harmonic spaces.** A Brelot harmonic space is a locally compact,
  connected, locally connected space with a sheaf of vector spaces of
  continuous harmonic functions such that regular open sets, those with a
  solvable Dirichlet problem given by positive harmonic measures, form a
  base, and such that increasing limits of harmonic functions on a domain
  are harmonic when finite on a dense set (Brelot convergence). Solutions
  of second-order elliptic equations with Hölder coefficients form such a
  space. Superharmonic functions, Perron–Wiener–Brelot solutions,
  balayage, thinness, and fine topology are developed from these axioms;
  Bauer's weaker convergence axiom admits the heat equation.
* **74. Hunt's theorem.** Let $E$ be locally compact with countable base
  and $V$ a positive linear operator from $C_c(E)$ to $C_0(E)$ with dense
  range. If $V$ satisfies the complete maximum principle — for
  $f,g\in C_c^+(E)$ and $a\geq0$, $Vf\leq Vg+a$ on $\{f>0\}$ implies
  $Vf\leq Vg+a$ on $E$ — then $V=\int_0^\infty P_t\,dt$ for a unique
  Feller semigroup $(P_t)$ (Hunt). Potential kernels thus correspond to
  transient Markov processes: Newtonian and Riesz kernels with
  $\alpha\leq2$ arise from Brownian motion and stable processes, and on
  locally compact abelian groups the convolution version characterizes
  potential kernels of transient convolution semigroups (Berg–Forst).

## Reference guide

Helms, Armitage–Gardiner, Axler–Bourdon–Ramey, Landkof, and Doob
overlap on classical potentials and boundary theory. Doob and Port–Stone
develop the probabilistic counterpart. Adams–Hedberg and Ponce connect
capacity to Sobolev spaces and measure data; Heinonen–Kilpeläinen–Martio
and Björn–Björn give the nonlinear continuation. Ransford, Tsuji, and
Saff–Totik develop planar logarithmic theory, while Tolsa supplies the
analytic-capacity continuation. Landkof treats Riesz kernels and capacities,
Bogdan et al. the potential theory of stable processes, Gardiner harmonic
approximation, and Brelot, Doob, and Berg–Forst the axiomatic and
kernel-semigroup viewpoints. Non-Euclidean geometries and stable-process
potential theory extend these foundations without changing the distinctions
among the capacities used here.

Local source copies consulted:

* [Helms, *Potential Theory*](References/Helms2014PotentialTheory2ndEd-SpringerUTX.pdf).
* [Armitage–Gardiner, *Classical Potential Theory*](References/ArmitageGardner2001ClassicalPotentialTheory-SpringerMonogMath.pdf).
* [Axler–Bourdon–Ramey, *Harmonic Function Theory*](References/AxlerBourdonRamey2001HarmonicFunctionTheory2ndEd-SpringerGTM137.pdf).
* [Doob, *Classical Potential Theory and Its Probabilistic Counterpart*](References/Doob1984ClassicalPotentialTheoryProbabilisticCounterpart-SpringerGL262.pdf).
* [Gardiner, *Harmonic Approximation*](References/Gardiner1995HarmonicApproximation-CambridgeLMSLNS221.pdf).
* [Tolsa, *Analytic Capacity, the Cauchy Transform, and Non-homogeneous Calderón–Zygmund Theory*](References/Tolsa2014AnalyticCapacityCauchyTransformNonHomogeneousCalderonZygmundTheory-BirkhäuserPM307.pdf).

Additional primary expositions consulted were
Ponce's lecture notes preceding his *Elliptic PDEs, Measures and Capacities* (arXiv:1204.0668),
Kilpeläinen's survey of $p$-Laplace equations with measures (arXiv:math/0304392),
and Saff's survey of logarithmic potential theory (arXiv:1010.3760).
They supplement the local texts for the nonlinear capacitary criteria
and weighted equilibrium statements.
