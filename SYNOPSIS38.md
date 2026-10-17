# Synopsis: Potential theory and capacity

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects recurring material from Section 38 of
[CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md).
It covers harmonic and superharmonic functions, equilibrium and capacity,
the Dirichlet problem and boundary regularity, probabilistic representations,
nonlinear potentials, and logarithmic and analytic capacity. Metric-space
diffusion and Dirichlet forms receive a separate treatment in Section 39.

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
  local mean-value property is harmonic. Interior extrema force
  constancy, and continuous Dirichlet solutions are unique on bounded domains.
* **2. Poisson representation on balls.** Continuous data on a sphere
  have a unique continuous harmonic extension given by the Poisson
  integral. Every positive harmonic function in a ball is the Poisson
  integral of a unique finite positive boundary measure.
* **3. Harnack inequality.** Positive harmonic functions satisfy
  $\sup_Ku\leq C_K\inf_Ku$ on compact subsets connected by a
  fixed chain of interior balls. A nonnegative harmonic function is
  either strictly positive or zero.
* **4. Harnack convergence.** An increasing sequence of harmonic
  functions is either locally uniformly divergent to infinity or
  converges locally uniformly to a harmonic function, assuming a
  common lower harmonic bound.
* **5. Interior estimates and analyticity.** Harmonic derivatives of
  order $k$ on a smaller ball are bounded by $C_kr^{-k}$ times
  the supremum on a larger ball. Harmonic functions are analytic,
  and locally bounded families are locally precompact in every $C^k$ norm.
* **6. Kelvin transformation.** For $n\geq3$,
  $Ku(x)=|x|^{2-n}u(x/|x|^2)$ preserves harmonicity on inverted
  domains away from zero. It converts behavior at infinity into
  behavior near an isolated point.
* **7. Bôcher's theorem.** A positive harmonic function on a punctured
  ball is $c\Gamma+h$, $c\geq0$, with $h$ harmonic across the
  puncture. In two dimensions the singular term is a nonnegative
  multiple of $\log(1/|x|)$.
* **8. Distributional characterization.** A subharmonic function is
  upper semicontinuous, locally integrable, not identically $-\infty$,
  and satisfies the sub-mean inequality; equivalently its distributional
  Laplacian is a positive measure, with the canonical representative.
  Superharmonic functions have the opposite signs and lower semicontinuity.
* **9. Riesz decomposition.** A nonnegative superharmonic function on
  a Greenian domain has a unique decomposition $u=G\mu+h$,
  where $\mu=-\Delta u$, $h\geq0$ is harmonic, and $G\mu$
  is a Green potential. Local versions hold on relatively compact subdomains.
* **10. Superharmonic minimum principle.** A superharmonic function
  bounded below on a bounded domain, with nonnegative boundary
  liminf, is nonnegative. Finite minima of superharmonic functions
  remain superharmonic; arbitrary infima require lower regularization.
* **11. Green functions.** Every bounded domain in $\mathbb R^n$,
  $n\geq2$, has a positive Green function for $-\Delta$.
  It is harmonic off its pole and vanishes at regular boundary points.
  A general domain admitting such a function is called Greenian.
* **12. Green symmetry and domain monotonicity.**
  $G_\Omega(x,y)=G_\Omega(y,x)$, and
  $G_{\Omega_1}\leq G_{\Omega_2}$ if $\Omega_1\subset\Omega_2$.
  Increasing exhaustion of a Greenian domain gives increasing
  convergence of the Green kernels.
* **13. Potential domination.** For positive compactly supported
  finite-energy Newtonian measures, $U^\mu\leq U^\nu+c$
  $\mu$-almost everywhere, $c\geq0$, implies that inequality
  everywhere. In particular a potential bounded by a constant on
  its supporting charge is bounded by that constant everywhere.

## Newtonian capacity, equilibrium, and thinness

For compact $K$ define
$\operatorname{Cap}(K)=\inf\{\int_{\mathbb R^n}|\nabla\phi|^2:
\phi\in C_c^\infty,\ \phi\geq1\text{ near }K\}$.
Extend first to open sets by compact exhaustion and then to arbitrary
sets by outer approximation.

* **14. Energy duality.**
  $\operatorname{Cap}(K)^{-1}=\inf_{\mu(K)=1,\,\mu\geq0}I(\mu)$,
  with $1/0=\infty$. Positive capacity is equivalent to supporting
  a nonzero finite-energy measure.
* **15. Equilibrium measure.** If $K$ has positive capacity, there is
  a unique equilibrium charge $\nu_K$ supported on $K$ such that
  $\nu_K(K)=\operatorname{Cap}(K)$,
  $U^{\nu_K}=1$ quasi-everywhere on $K$, and $U^{\nu_K}\leq1$
  everywhere. Its energy is $I(\nu_K)=\operatorname{Cap}(K)$.
  For a zero-capacity compact set the capacitary measure and potential are zero.
* **16. Variational capacitary potential.** The equilibrium potential
  minimizes Dirichlet energy among homogeneous $H^1$ functions at
  least one quasi-everywhere on $K$. Its energy is the capacity;
  it is harmonic outside $K$ and decays at infinity.
* **17. Ball capacity and scaling.**
  $\operatorname{Cap}(\overline B_r)=(n-2)|S^{n-1}|r^{n-2}$ and
  $\operatorname{Cap}(aK)=a^{n-2}\operatorname{Cap}(K)$ for $a>0$.
* **18. Choquet properties.** Capacity is monotone, continuous on
  increasing sequences of sets and decreasing sequences of compact
  sets, and countably subadditive. Analytic sets, in particular Borel
  sets, are capacitable: outer capacity equals the supremum of compact
  subcapacities.
* **19. Polar sets.** A set has zero Newtonian capacity exactly when
  it is contained in the infinity set of a positive superharmonic
  function, locally in the ambient domain. Such sets are called polar.
* **20. Finite-energy measures avoid polar sets.** A positive measure
  of finite Newtonian energy charges no set of zero capacity.
  Its potential is finite quasi-everywhere and has a quasi-continuous representative.
* **21. Quasi-continuity.** Sobolev and finite-energy potential
  representatives are continuous outside open sets of arbitrarily
  small capacity. Equal Sobolev elements have representatives equal
  quasi-everywhere, a stronger precision than almost-everywhere equality.
* **22. Fine topology and thinness.** The fine topology is the coarsest
  topology making superharmonic functions continuous. A set $E$ is
  thin at $x$ exactly when it fails to accumulate there or a
  superharmonic $v$ satisfies
  $v(x)<\liminf_{E\setminus\{x\}\ni y\to x}v(y)$.
  Fine neighborhoods have thin complements.
* **23. Reduction and sweeping.** For nonnegative superharmonic $u$,
  the lower semicontinuous regularization of
  $\inf\{v\geq0:v\text{ superharmonic},\ v\geq u\text{ on }E\}$
  is the balayage of $u$ onto $E$. It is at most $u$, agrees with
  it quasi-everywhere on $E$, and is harmonic outside $\overline E$.
* **24. Balayage of charges.** Sweeping a compactly supported positive
  charge onto a compact set gives a charge there whose potential
  agrees with the original potential quasi-everywhere on the set and
  is no larger elsewhere. The swept mass does not exceed the original mass.
* **25. Removability.** A bounded harmonic function off a relatively
  closed polar subset of a domain extends uniquely harmonically across
  it. Polar exceptional sets are therefore invisible to bounded
  harmonic Dirichlet theory.

## The Dirichlet problem, harmonic measure, and ideal boundaries

* **26. Perron–Wiener solution.** Upper superharmonic and lower
  subharmonic envelopes agree for continuous boundary data on a bounded
  domain. Their common value is harmonic even if some boundary points
  are irregular.
* **27. Barrier criterion.** A boundary point is regular for every
  continuous datum exactly when it admits a positive local superharmonic
  barrier tending to zero there and bounded away from zero outside
  each smaller neighborhood.
* **28. Wiener's criterion.** For $n\geq3$, a boundary point $x_0$
  is regular exactly when
  $\sum_{k\geq1}2^{k(n-2)}\operatorname{Cap}(E_k)=\infty$,
  where $E_k=(\mathbb R^n\setminus\Omega)\cap
  \{2^{-k-1}\leq|x-x_0|\leq2^{-k}\}$.
* **29. Geometric sufficient conditions.** An exterior cone at a
  boundary point supplies a barrier. In particular Lipschitz domains
  are regular, whereas an arbitrarily thin exterior cusp need not be.
* **30. Kellogg's theorem.** The irregular boundary points form a
  polar set. Thus every continuous boundary datum is attained
  quasi-everywhere on the boundary.
* **31. Harmonic measure.** For each $x\in\Omega$, there is a
  probability measure $\omega^x$ on $\partial\Omega$ such that
  $H_f(x)=\int f\,d\omega^x$ for continuous $f$.
  Null sets of harmonic measure are independent of the pole in a
  connected domain.
* **32. Boundary Harnack principle.** In a Lipschitz domain, positive
  harmonic functions vanishing on a common boundary patch have
  comparable ratios on smaller patches after interior normalization.
  The ratio extends Hölder continuously to the smaller boundary patch.
* **33. Dahlberg's theorem.** On a bounded Lipschitz domain, harmonic
  measure and surface measure are mutually absolutely continuous.
  The Poisson kernel satisfies quantitative local reverse Hölder
  estimates, equivalently the local $A_\infty$ property of harmonic measure.
* **34. Martin representation.** Fixing $x_*\in\Omega$, the normalized
  kernels $G(x,y)/G(x_*,y)$ define the Martin compactification.
  Every positive harmonic function has a unique representation as
  an integral of normalized minimal kernels over the minimal Martin
  boundary; the representing mass is $h(x_*)$.
* **35. Smooth-domain Martin boundary.** For bounded $C^{1,1}$ domains,
  the Martin boundary identifies with the Euclidean boundary, and
  Martin kernels are normalized Poisson kernels. In general the
  Euclidean boundary may not parametrize all minimal harmonic functions.

## Brownian interpretations

Brownian motion here has generator $\tfrac12\Delta$, whereas Green
functions above invert $-\Delta$. This accounts for the factor two below.

* **36. Exit distribution.** For a bounded domain and Brownian exit
  time $\tau_\Omega$, $H_f(x)=\mathbb E_xf(B_{\tau_\Omega})$.
  Harmonic measure is the exit distribution, and barriers determine
  continuity of this expectation at boundary points.
* **37. Occupation kernel.** For nonnegative Borel $f$,
  $\mathbb E_x\int_0^{\tau_\Omega}f(B_t)dt
  =2\int_\Omega G_\Omega(x,y)f(y)dy$.
* **38. Equilibrium as hitting probability.** For compact $K$ in
  $\mathbb R^n$, $n\geq3$, its equilibrium potential equals
  $\mathbb P_x(\tau_K<\infty)$ outside $K$.
  A compact polar set is hit with probability zero from outside it.
* **39. Recurrence and transience.** Planar Brownian motion returns
  to every nonempty open disk almost surely. Brownian motion in
  dimensions at least three is transient and has Newtonian occupation
  potential. Individual points are polar in every dimension at least two.

## Sobolev capacity and nonlinear potential theory

For $1<p<\infty$, the relative **$p$-capacity** is
$\operatorname{cap}_p(K,\Omega)=\inf\int_\Omega|\nabla\phi|^p$,
over $\phi\in C_c^\infty(\Omega)$ at least one near $K$.
A **$p$-superharmonic function** is lower semicontinuous, finite on a
dense set, and satisfies comparison with continuous $p$-harmonic functions
on relatively compact subdomains.

* **40. Capacitary minimization.** For compact $K\Subset\Omega$,
  minimization over $W_0^{1,p}$ functions at least one quasi-everywhere
  on $K$ gives the unique capacitary potential. It is $p$-harmonic
  outside $K$ and has energy $\operatorname{cap}_p(K,\Omega)$.
* **41. Sobolev quasi-continuity.** Every $W^{1,p}$ function has a
  $p$-quasi-continuous representative, unique quasi-everywhere.
  For arbitrary open $\Omega$, membership in $W_0^{1,p}(\Omega)$
  is equivalent to the zero extension belonging to $W^{1,p}(\mathbb R^n)$
  and its quasi-continuous representative vanishing $p$-quasi-everywhere
  on the complement.
* **42. Nonlinear comparison.** Weak $p$-harmonic solutions with ordered
  Sobolev boundary data are ordered. The comparison definition extends
  the theory to $p$-superharmonic functions outside the energy class.
* **43. Nonlinear Perron theory.** Continuous boundary data on bounded
  domains are resolutive for the $p$-Laplace equation. Perron solutions
  attain them at regular points. For $p\ne2$ this solution operator
  is nonlinear and does not define an additive harmonic measure.
* **44. Nonlinear Wiener criterion.** A boundary point $x_0$ is
  regular exactly when
  $$
  \int_0^{r_0}\left(
  \frac{\operatorname{cap}_p((\mathbb R^n\setminus\Omega)\cap\overline B_r(x_0),B_{2r}(x_0))}
       {\operatorname{cap}_p(\overline B_r(x_0),B_{2r}(x_0))}
  \right)^{1/(p-1)}\frac{dr}{r}=\infty.
  $$
* **45. Nonlinear fundamental solution and scaling.** For $1<p<n$,
  a normalized positive multiple of $|x|^{(p-n)/(p-1)}$ solves
  $-\Delta_pu=\delta_0$, and
  $\operatorname{cap}_p(\overline B_r,B_{2r})=C_{n,p}r^{n-p}$.
  At $p=n$ the fundamental singularity is logarithmic.
* **46. Wolff potential estimates.** For $1<p<n$ define
  $\mathbf W_{1,p}^\mu(x,R)=\int_0^R
  (\mu(B_r(x))/r^{n-p})^{1/(p-1)}dr/r$.
  If $u\geq0$ is $p$-superharmonic and $-\Delta_pu=\mu$,
  then $\mathbf W_{1,p}^\mu(x,R)\leq Cu(x)$ and
  $u(x)\leq C\inf_{B_R(x)}u+C\mathbf W_{1,p}^\mu(x,2R)$
  when $B_{2R}(x)$ is interior.
* **47. Capacitary strong estimate.** For $u\in C_c^\infty(\Omega)$,
  $\int_0^\infty\operatorname{cap}_p(\{|u|>t\},\Omega)
  \,d(t^p)\leq C_p\int|\nabla u|^p$.
  Truncation turns energy control into control of exceptional level sets.
* **48. Dimension thresholds.** If $1<p<n$, sets of dimension
  strictly below $n-p$ have zero $p$-capacity; compact sets of
  dimension strictly above $n-p$ have positive capacity.
  The critical dimension requires finer size information.
* **49. Removable $p$-polar singularities.** A bounded $p$-harmonic
  function off a relatively closed set of zero $p$-capacity extends
  uniquely $p$-harmonically across that set.

The **Bessel capacity** $C_{\alpha,p}$ is the infimum of $\|f\|_p^p$
over nonnegative $f$ with $G_\alpha*f\geq1$ on the set, where
$\widehat G_\alpha(\xi)=(1+|\xi|^2)^{-\alpha/2}$ using $e^{-ix\cdot\xi}$.

* **50. Bessel–Sobolev correspondence.** Bessel capacities control
  exceptional sets of Bessel potential spaces $H^{\alpha,p}$.
  At integer order one they agree, up to fixed constants on bounded
  regions, with the inhomogeneous Sobolev capacity; local relative
  capacities give the zero-boundary counterpart.
* **51. Absorption equations with measure data.** On a bounded smooth
  domain, for $q>1$ and finite positive $\mu$, the zero-Dirichlet
  problem $-\Delta u+u^q=\mu$ has a nonnegative weak solution
  exactly when $\mu$ vanishes on sets of zero $C_{2,q'}$ capacity.
  This is the capacitary criterion for admissible measure data.

## Logarithmic potentials and equilibrium in the plane

For compact $K\subset\mathbb C$, set
$I_{\log}(\mu)=\iint\log(1/|z-w|)d\mu(z)d\mu(w)$,
$V_K=\inf_{\mu\in\mathcal P(K)}I_{\log}(\mu)$, and
$\operatorname{cap}_{\log}(K)=e^{-V_K}$.

* **52. Jensen's formula for subharmonic functions.** If
  $\mu=(2\pi)^{-1}\Delta u$ and $u(0)>-\infty$, then
  $\fint_{|z|=r}u-u(0)=\int_0^r\mu(B_t)dt/t$
  for admissible radii in the disk. For $u=\log|f|$, this counts
  analytic zeros with multiplicity.
* **53. Logarithmic equilibrium.** A compact set of positive logarithmic
  capacity has a unique probability measure minimizing logarithmic energy.
  Sets of zero capacity are precisely planar polar sets.
* **54. Frostman's theorem.** The equilibrium potential satisfies
  $U^{\mu_K}_{\log}=V_K$ quasi-everywhere on $K$ and
  $U^{\mu_K}_{\log}\leq V_K$ everywhere in the plane.
* **55. Green function with pole at infinity.** On the unbounded
  complementary component of $K$,
  $g_K(z,\infty)=V_K-U^{\mu_K}_{\log}(z)$ and
  $g_K(z,\infty)=\log|z|-\log\operatorname{cap}_{\log}(K)+o(1)$
  at infinity.
* **56. Conformal characterization.** If that component is simply
  connected and its conformal map to $|w|>1$ is
  $\phi(z)=z/c+O(1)$ at infinity, $c>0$, then
  $g_K=\log|\phi|$ and $\operatorname{cap}_{\log}(K)=c$.
  A radius-$R$ disk has capacity $R$; an interval of length $\ell$
  has capacity $\ell/4$.
* **57. Transfinite diameter.**
  $\lim_{N\to\infty}\max_{z_1,\ldots,z_N\in K}
  \prod_{i<j}|z_i-z_j|^{2/(N(N-1))}=\operatorname{cap}_{\log}(K)$.
* **58. Fekete-point distribution.** For positive-capacity compact
  $K$, empirical measures of maximizing Fekete configurations converge
  weakly to $\mu_K$. Discrete repulsion selects the continuous
  equilibrium charge.
* **59. Weighted equilibrium.** For a lower semicontinuous
  external field $Q:K\to\mathbb R\cup\{\infty\}$ on compact $K$,
  with a finite weighted-energy competitor,
  $I_{\log}(\mu)+2\int Qd\mu$ has a unique minimizer.
  Its potential satisfies $U^\mu_{\log}+Q\geq F$ quasi-everywhere
  on $K$ and equality $\mu$-almost everywhere, for a constant $F$.
* **60. Bernstein–Walsh inequality.** For a polynomial of degree at
  most $N$ and a nonpolar compact $K$,
  $|P(z)|\leq\|P\|_K e^{Ng_K(z,\infty)}$ on the unbounded
  complementary component. Capacity and Green functions therefore
  control polynomial growth away from the approximation set.

## Analytic capacity and removability

For compact $E\subset\mathbb C$, **analytic capacity** is
$\gamma(E)=\sup|f'(\infty)|$, over holomorphic functions on
$\widehat{\mathbb C}\setminus E$ with $|f|\leq1$ and $f(\infty)=0$,
where $f'(\infty)=\lim_{z\to\infty}zf(z)$.

* **61. Analytic removability criterion.** $\gamma(E)=0$ exactly when
  $E$ is removable for bounded holomorphic functions. Analytic capacity
  is monotone and scales by $\gamma(aE+b)=|a|\gamma(E)$.
* **62. Positive-measure characterization.** Analytic capacity is
  comparable, with absolute constants, to the supremum of $\mu(E)$
  over positive measures supported on $E$ whose Cauchy transform
  $\int(z-w)^{-1}d\mu(w)$ is bounded in absolute value by one
  at Lebesgue-almost every point of the plane.
* **63. Countable semiadditivity.** There is an absolute $C$ such that
  $\gamma(\bigcup_jE_j)\leq C\sum_j\gamma(E_j)$, with the
  standard inner-capacity extension to noncompact Borel sets $E_j$.
* **64. Finite-length removability.** For compact sets of finite
  $\mathcal H^1$ measure, zero analytic capacity is equivalent to
  pure unrectifiability. This is the link with the rectifiability
  theory in Section 37, beyond the polar sets detected by logarithmic capacity.

## Reference guide

Helms, Armitage–Gardiner, Axler–Bourdon–Ramey, Landkof, and Doob
overlap on classical potentials and boundary theory. Doob and Port–Stone
develop the probabilistic counterpart. Adams–Hedberg and Ponce connect
capacity to Sobolev spaces and measure data; Heinonen–Kilpeläinen–Martio
and Björn–Björn give the nonlinear continuation. Ransford, Tsuji, and
Saff–Totik develop planar logarithmic theory, while Tolsa supplies the
analytic-capacity continuation. Non-Euclidean geometries and stable-process
potential theory extend these foundations without changing the distinctions
among the capacities used here.

Local source copies consulted:

* [Helms, *Potential Theory*](References/Helms2014PotentialTheory2ndEd-SpringerUTX.pdf).
* [Armitage–Gardiner, *Classical Potential Theory*](References/ArmitageGardner2001ClassicalPotentialTheory-SpringerMonogMath.pdf).
* [Axler–Bourdon–Ramey, *Harmonic Function Theory*](References/AxlerBourdonRamey2001HarmonicFunctionTheory2ndEd-SpringerGTM137.pdf).
* [Doob, *Classical Potential Theory and Its Probabilistic Counterpart*](References/Doob1984ClassicalPotentialTheoryProbabilisticCounterpart-SpringerGL262.pdf).
* [Tolsa, *Analytic Capacity, the Cauchy Transform, and Non-homogeneous Calderón–Zygmund Theory*](References/Tolsa2014AnalyticCapacityCauchyTransformNonHomogeneousCalderonZygmundTheory-BirkhäuserPM307.pdf).

Additional primary expositions consulted were
[Ponce's author-posted precursor to his measure-data book](https://arxiv.org/pdf/1204.0668),
[Kilpeläinen's survey of $p$-Laplace equations with measures](https://arxiv.org/pdf/math/0304392),
and [Saff's account of logarithmic potential theory](https://arxiv.org/pdf/1010.3760).
They supplement the local texts for the nonlinear capacitary criteria
and weighted equilibrium statements.
