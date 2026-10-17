# Synopsis: Semigroups, evolution equations, and functional calculus

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects the recurring core of Section 24 of
[CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md): generation,
perturbation, approximation, smoothing, functional calculus, asymptotics,
forms, nonlinear evolution, and the basic control-theoretic interface.
Banach-valued multiplier techniques appear in Section 18; here their role
is the solvability and regularity of evolution equations.

A **$C_0$-semigroup** on a Banach space $X$ is a family $T(t)$ of bounded
linear maps with $T(0)=I$, $T(t+s)=T(t)T(s)$, and $T(t)x\to x$ as
$t\downarrow0$ for every $x$. Its **generator** is
$Ax=\lim_{t\downarrow0}(T(t)x-x)/t$ on the vectors where this limit
exists. Thus the evolution convention is $u'=Au$. For sectorial calculus
and parabolic equations we instead write $B=-A$, so $u'+Bu=f$.

## Generators and resolvents

* **1. Exponential boundedness.** Every $C_0$-semigroup satisfies
  $\|T(t)\|\leq Me^{\omega t}$ for some $M\geq1$, $\omega\in\mathbb R$.
  Strong continuity at zero implies strong continuity everywhere.
* **2. Generator structure.** The generator is closed and densely
  defined. Its domain is invariant under $T(t)$, and for $x\in D(A)$,
  $AT(t)x=T(t)Ax$ and $dT(t)x/dt=AT(t)x$.
* **3. Integrated generator identity.** For $x\in X$,
  $\int_0^tT(s)x\,ds\in D(A)$ and
  $A\int_0^tT(s)x\,ds=T(t)x-x$. This provides dense domain elements
  without requiring differentiability of the initial vector.
* **4. Uniqueness and uniform continuity.** A generator determines its
  semigroup uniquely. A semigroup is continuous in operator norm at zero
  exactly when its generator is bounded, and then $T(t)=e^{tA}$.
* **5. Laplace resolvent formula.** If $\|T(t)\|\leq Me^{\omega t}$,
  then for $\operatorname{Re}\lambda>\omega$,
  $$R(\lambda,A)x=\int_0^\infty e^{-\lambda t}T(t)x\,dt,
    \qquad\|R(\lambda,A)\|\leq\frac M{\operatorname{Re}\lambda-\omega}.$$
* **6. Hille–Yosida theorem.** A densely defined closed $A$ generates
  a semigroup with bound $Me^{\omega t}$ exactly when
  $(\omega,\infty)\subset\rho(A)$ and
  $\|R(\lambda,A)^n\|\leq M(\lambda-\omega)^{-n}$ for every
  $\lambda>\omega$ and integer $n\geq1$.
* **7. Lumer–Phillips theorem.** A densely defined operator generates
  a contraction semigroup exactly when it is dissipative and
  $\lambda I-A$ is onto for some $\lambda>0$.
  Dissipativity means $\|x-tAx\|\geq\|x\|$ for $t>0$.
* **8. Hilbert space dissipativity.** On a Hilbert space, dissipativity
  is equivalent to $\operatorname{Re}\langle Ax,x\rangle\leq0$.
  A densely defined closed operator is a contraction generator if both
  $A$ and $A^*$ are dissipative.
* **9. Yosida approximations.** For a contraction generator,
  $A_\lambda=\lambda AR(\lambda,A)$ is bounded,
  $e^{tA_\lambda}$ is contractive, and $e^{tA_\lambda}x\to T(t)x$
  uniformly on bounded time intervals as $\lambda\to\infty$.
* **10. Exponential formula.** For a contraction generator,
  $T(t)x=\lim_{n\to\infty}(I-tA/n)^{-n}x$, uniformly for $t$ in
  compact nonnegative intervals. This is implicit Euler convergence.
* **11. Group generation.** If both $A$ and $-A$ generate $C_0$-semigroups,
  they combine into a $C_0$-group. On Hilbert space, skew-adjoint
  generators give exactly the unitary groups.

## Cauchy problems and perturbations

A **classical solution** is differentiable in $X$, lies in $D(A)$, and
satisfies the equation there. A **mild solution** uses the variation-of-constants
formula and need not be differentiable.

* **12. Homogeneous well-posedness.** For $x\in D(A)$, $u(t)=T(t)x$
  is the unique classical solution of $u'=Au$, $u(0)=x$.
  For arbitrary $x\in X$ it is the unique continuous integrated solution
  satisfying $u(t)=x+A\int_0^tu(s)\,ds$.
* **13. Variation of constants.** For $f\in L^1(0,T;X)$ and $x\in X$,
  $$u(t)=T(t)x+\int_0^tT(t-s)f(s)\,ds$$
  is the unique mild solution. If $x\in D(A)$ and $f$ is continuously
  differentiable, it is classical.
* **14. Bounded perturbation theorem.** If $A$ generates a semigroup
  bounded by $Me^{\omega t}$ and $K\in\mathcal L(X)$, then $A+K$
  generates a semigroup bounded by $M e^{(\omega+M\|K\|)t}$.
* **15. Dyson–Phillips expansion.** The perturbed semigroup is
  $S(t)=\sum_{n\geq0}S_n(t)$, where $S_0(t)=T(t)$ and
  $S_{n+1}(t)=\int_0^tT(t-s)KS_n(s)\,ds$. The series converges in
  operator norm uniformly on bounded time intervals.
* **16. Miyadera–Voigt perturbation.** Let $K:D(A)\to X$ be bounded
  for the graph norm. If for some $t_0>0$ and $q<1$,
  $\int_0^{t_0}\|KT(t)x\|dt\leq q\|x\|$ for $x\in D(A)$,
  then $A+K$ on $D(A)$ generates a $C_0$-semigroup.
* **17. Trotter–Kato approximation.** Suppose $A_n,A$ generate semigroups
  with one common exponential bound. Strong convergence
  $R(\lambda,A_n)x\to R(\lambda,A)x$ for one sufficiently large
  real $\lambda$ is equivalent to $T_n(t)x\to T(t)x$ uniformly on
  bounded time intervals.
* **18. Chernoff product formula.** Let $F(0)=I$, $F$ be strongly
  continuous, and $\|F(t)^n\|\leq Me^{\omega nt}$. If
  $F'(0)x=Ax$ on a core of a generator $A$, then
  $F(t/n)^nx\to T(t)x$ uniformly on bounded time intervals.
* **19. Lie–Trotter formula.** If $A,B$ generate semigroups, the closure
  of $A+B$ on $D(A)\cap D(B)$ generates $S(t)$, and the products
  $[e^{tA/n}e^{tB/n}]^n$ satisfy a common exponential bound, then those
  products converge strongly to $S(t)$, uniformly on bounded time intervals.

## Analyticity, smoothing, and fractional powers

A semigroup is **bounded analytic** if it extends holomorphically and
boundedly to a sector around the positive time axis, strongly continuous
at zero on smaller sectors. A densely defined closed $B$ is **sectorial**
of angle $\theta$ if its spectrum lies in the closed sector
$\overline{\Sigma_\theta}$ and $z(z-B)^{-1}$ is bounded outside every
strictly larger sector.

* **20. Analytic generation theorem.** $-B$ generates a bounded analytic
  semigroup exactly when $B$ is sectorial of angle less than $\pi/2$.
  Shifts allow the corresponding exponentially bounded formulation.
* **21. Analytic smoothing.** For a bounded analytic semigroup,
  $T(t)X\subset D(A^k)$ and $\|A^kT(t)\|\leq C_kt^{-k}$ for
  every positive integer $k$ and $t>0$.
* **22. Fractional smoothing.** For sectorial $B$ of angle below $\pi/2$
  and $\alpha\geq0$, $\|B^\alpha e^{-tB}\|\leq C_\alpha t^{-\alpha}$.
  Thus positive time gains fractional domain regularity.
* **23. Balakrishnan formula.** For $0<\alpha<1$ and sectorial $B$,
  $$B^\alpha x=\frac{\sin\pi\alpha}{\pi}
      \int_0^\infty t^{\alpha-1}B(t+B)^{-1}x\,dt\qquad(x\in D(B)).$$
  Closure yields the fractional power on its full domain.
* **24. Moment inequality.** For $0<\alpha<1$,
  $\|B^\alpha x\|\leq C\|x\|^{1-\alpha}\|Bx\|^\alpha$
  on $D(B)$, with the usual shifted version for nonhomogeneous graph norms.
* **25. Fractional domains and real interpolation.** For invertible
  sectorial $B$ and $0<\alpha<1$,
  $(X,D(B))_{\alpha,1}\hookrightarrow D(B^\alpha)
  \hookrightarrow(X,D(B))_{\alpha,\infty}$ continuously.
* **26. Bounded imaginary powers.** If an invertible sectorial $B$ has
  bounded imaginary powers with at most exponential growth, then
  $D(B^\alpha)=[X,D(B)]_\alpha$ for $0<\alpha<1$, with equivalent norms.
* **27. Semigroup interpolation norm.** For bounded analytic
  $e^{-tB}$, $0<\theta<1$, and $1\leq q\leq\infty$, an equivalent
  norm on $(X,D(B))_{\theta,q}$ is
  $\|x\|+\|t^{1-\theta}Be^{-tB}x\|_{L^q((0,1),dt/t;X)}$.

## Holomorphic calculus and maximal regularity

For suitable holomorphic $f$ on a sector containing $\sigma(B)$,
$f(B)=(2\pi i)^{-1}\int_\Gamma f(z)(z-B)^{-1}dz$.
A **bounded $H^\infty$ calculus** satisfies
$\|f(B)\|\leq C\|f\|_\infty$, initially for functions decaying at
zero and infinity and then by regularization. **R-sectoriality** replaces
the sectorial resolvent bound by an R-bound on the entire family.

* **28. Calculus laws.** The sectorial calculus is independent of its
  admissible contour and respects products, resolvents, and composition
  wherever defined. It recovers fractional powers and analytic semigroups.
* **29. Hilbert square-function criterion.** For an invertible sectorial
  $B$ on Hilbert space, bounded $H^\infty$ calculus is equivalent to
  $$\int_0^\infty\|tB(I+tB)^{-2}x\|^2\frac{dt}{t}\leq C\|x\|^2$$
  and the corresponding estimate for $B^*$ (McIntosh).
* **30. de Simon maximal regularity.** On Hilbert space, an invertible
  sectorial $B$ of angle below $\pi/2$ gives, for $1<p<\infty$,
  the unique zero-initial-value solution of $u'+Bu=f$ with
  $\|u'\|_{L^p}+\|Bu\|_{L^p}\leq C\|f\|_{L^p}$ on the half-line.
* **31. Weis characterization.** On UMD spaces, the same maximal
  regularity property for an invertible sectorial operator is equivalent
  to R-sectoriality with angle below $\pi/2$, and is independent of
  $p\in(1,\infty)$.
* **32. Calculus sufficient condition.** On a UMD space, an invertible
  operator with bounded $H^\infty$ calculus of angle below $\pi/2$
  has maximal $L^p$ regularity. A bounded analytic semigroup alone is
  insufficient on general UMD spaces.
* **33. Initial trace theorem.** On a finite interval, the trace space
  of $W^{1,p}(0,T;X)\cap L^p(0,T;D(B))$ is
  $(X,D(B))_{1-1/p,p}$. Under maximal regularity, these and exactly
  these initial values admit solutions of that regularity for every $L^p$ forcing.

## Spectra, stability, and long-time behavior

The **growth bound** $\omega_0$ is the infimum of admissible exponential
exponents; the **spectral bound** is
$s(A)=\sup\{\operatorname{Re}z:z\in\sigma(A)\}$.
**Strong stability** means $T(t)x\to0$ for each $x$;
**exponential stability** means $\|T(t)\|\leq Me^{-\varepsilon t}$.

* **34. Spectral inclusion.** For every $C_0$-semigroup,
  $e^{t\sigma(A)}\subset\sigma(T(t))\setminus\{0\}$ and
  $s(A)\leq\omega_0$. Equality and the reverse spectral inclusion
  require further hypotheses.
* **35. Analytic spectral mapping.** For analytic semigroups,
  $\sigma(T(t))\setminus\{0\}=e^{t\sigma(A)}$ for $t>0$.
  The same conclusion holds for eventually norm-continuous semigroups.
* **36. Growth bound from the semigroup.** For every fixed $t>0$,
  $r(T(t))=e^{t\omega_0}$. Consequently eventually norm-continuous
  semigroups satisfy $s(A)=\omega_0$.
* **37. Datko–Pazy theorem.** A $C_0$-semigroup is exponentially stable
  exactly when, for some $1\leq p<\infty$,
  $\int_0^\infty\|T(t)x\|^pdt\leq C\|x\|^p$ for all $x$.
* **38. Gearhart–Prüss theorem.** A bounded $C_0$-semigroup on Hilbert
  space is exponentially stable exactly when $i\mathbb R\subset\rho(A)$
  and $\sup_{\beta\in\mathbb R}\|R(i\beta,A)\|<\infty$.
* **39. Arendt–Batty–Lyubich–Vũ theorem.** A bounded semigroup is
  strongly stable if $\sigma(A)\cap i\mathbb R$ is countable and
  $A^*$ has no eigenvalues on $i\mathbb R$. On reflexive spaces it
  suffices to exclude eigenvalues of $A$ there.
* **40. Quasicompact asymptotics.** If a semigroup has negative essential
  growth bound, its part in any sufficiently far right half-plane is a
  finite sum of exponential-polynomial terms from isolated finite-rank
  spectral projections, plus an exponentially decaying remainder.
* **41. Mean ergodic theorem.** A bounded semigroup on a reflexive
  Banach space has strongly convergent Cesàro averages
  $t^{-1}\int_0^tT(s)x\,ds$. Their limit projects onto $\ker A$
  along $\overline{\operatorname{ran}A}$.
* **42. Positive semigroup criterion.** On a Banach lattice, a generated
  semigroup is positive exactly when $R(\lambda,A)$ is positive for
  every sufficiently large real $\lambda$. Bounded positive perturbations
  preserve positivity and give dominating semigroups.

## Form methods, products, and subordination

* **43. Sectorial form generation.** A densely defined closed accretive
  sectorial form on Hilbert space determines an m-sectorial operator $B$;
  $-B$ generates a holomorphic contraction semigroup. The form domain
  supplies its weak variational formulation.
* **44. Invariance of convex sets.** Let $a$ be such a form with domain
  $V$, and let the metric projection $P_C$ onto a closed convex set
  preserve $V$. Then $C$ is semigroup invariant exactly when
  $\operatorname{Re}a(P_Cu,u-P_Cu)\geq0$ for all $u\in V$.
* **45. Positivity from a real form.** For a real accretive form on
  $L^2$ whose domain is stable under positive parts, its semigroup is
  positive exactly when $a(u^+,u^-)\leq0$ for every real $u$ in the
  form domain. Here $u^-=\max(-u,0)$.
* **46. Form-sum product formula.** For nonnegative self-adjoint $B,C$
  with dense intersection of form domains, the operator $D$ associated
  with their form sum satisfies
  $e^{-tD}x=\lim_n(e^{-tB/n}e^{-tC/n})^nx$.
* **47. Bernstein subordination.** If $f$ is a Bernstein function with
  $f(0)=0$, its convolution semigroup of probability measures $\mu_t$
  satisfies $\int e^{-\lambda s}d\mu_t(s)=e^{-tf(\lambda)}$.
  For a bounded $C_0$-semigroup, $S(t)x=\int T(s)x\,d\mu_t(s)$ is
  a bounded $C_0$-semigroup with generator $-f(-A)$.
* **48. Fractional heat evolution.** Taking $f(\lambda)=\lambda^\alpha$,
  $0<\alpha<1$, subordinates the heat semigroup to
  $e^{-t(-\Delta)^\alpha}$. Positivity and contractivity pass through
  this probability average.

## Nonlinear and Volterra evolution

For a possibly multivalued operator $B\subset X\times X$,
**accretivity** means $\|x-y\|\leq\|x-y+\lambda(u-v)\|$ for
$(x,u),(y,v)\in B$, $\lambda>0$. It is **m-accretive** if also
$\operatorname{ran}(I+\lambda B)=X$ for every $\lambda>0$.

* **49. Nonlinear resolvent contraction.** For m-accretive $B$,
  $J_\lambda=(I+\lambda B)^{-1}$ is single valued and nonexpansive
  on all of $X$. Resolvent identities hold in their nonlinear form.
* **50. Crandall–Liggett generation.** An m-accretive $B$ generates a
  nonlinear contraction semigroup on $\overline{D(B)}$ by
  $S(t)x=\lim_n(I+tB/n)^{-n}x$. For $x\in D(B)$, convergence is
  uniform on bounded time intervals; extension gives every initial value
  in the domain closure.
* **51. Subgradient generation.** The subdifferential of a proper lower
  semicontinuous convex function on a Hilbert space is maximal monotone,
  hence m-accretive. Its semigroup gives the unique convex gradient flow
  with contraction in the initial value.
* **52. Gradient-flow energy identity.** Along that flow, at positive
  times where the derivatives exist,
  $-\frac d{dt}\Phi(u(t))=\|u'(t)\|^2$; integration gives the
  energy dissipation identity on intervals where the endpoint energy is finite.
* **53. Semilinear local well-posedness.** If $F:X\to X$ is Lipschitz
  on every bounded ball, $u'=Au+F(u)$ has a unique maximal mild solution
  for each initial value. A finite maximal time forces its norm to become unbounded;
  global Lipschitz $F$ gives global existence.
* **54. Volterra resolvent, bounded-operator case.** For bounded $A$ and
  scalar $k\in L^1_{\rm loc}(\mathbb R_+)$, the equation
  $S(t)=I+\int_0^tk(t-s)AS(s)ds$ has a unique strongly continuous
  resolvent family. Successive convolutions construct it locally, and it
  solves the corresponding linear Volterra equation.

## Observation and control

For Hilbert spaces $X,U,Y$ and bounded $B:U\to X$, $C:X\to Y$,
consider $x'=Ax+Bu$, $y=Cx$. The **controllability map** at time $T$
is $\mathcal W_Tu=\int_0^TT(T-s)Bu(s)ds$; the **observation map**
is $\mathcal O_Tx=CT(\cdot)x$. Exact controllability means
$\operatorname{ran}\mathcal W_T=X$, and approximate controllability
means its range is dense.

* **55. Input–state formula.** For $u\in L^2(0,T;U)$, the controlled
  mild solution is $x(t)=T(t)x_0+\int_0^tT(t-s)Bu(s)ds$.
  Its terminal dependence on $u$ is bounded and linear.
* **56. Controllability–observability duality.** Exact controllability
  is equivalent to
  $\int_0^T\|B^*T(t)^*x\|^2dt\geq c\|x\|^2$.
  Approximate controllability is equivalent to the same integral vanishing
  only for $x=0$.
* **57. Gramian criterion.** The controllability Gramian
  $G_T=\int_0^TT(t)BB^*T(t)^*dt$ is bounded positive.
  Exact controllability is equivalent to $G_T\geq cI$, and approximate
  controllability to $\ker G_T=0$.
* **58. Minimum-energy control.** Under exact controllability, the
  minimum-norm control reaching $x_T$ from zero is
  $u(s)=B^*T(T-s)^*G_T^{-1}x_T$, and its squared energy is
  $\langle G_T^{-1}x_T,x_T\rangle$.
* **59. Compactness obstruction.** On infinite-dimensional $X$, if
  $T(t)$ is compact for every $t>0$ and $B$ is bounded, then
  $\mathcal W_T$ is compact. Therefore such a system cannot be exactly
  controllable with $L^2$ controls, though approximate controllability can hold.
* **60. Admissible unbounded observation.** A graph-norm bounded
  $C:D(A)\to Y$ extends to a bounded observation map
  $X\to L^2(0,T;Y)$ exactly when
  $\int_0^T\|CT(t)x\|^2dt\leq K_T\|x\|^2$ for $x\in D(A)$.
  This admissibility condition allows boundary observations beyond bounded $C$.

## Reference guide

Engel–Nagel supplies generation, perturbation, approximation, spectral
mapping, and stability. Arendt–Batty–Hieber–Neubrander independently develops
the resolvent and Laplace-transform approach and the Tauberian stability
theorems. Hytönen–van Neerven–Veraar–Weis supplies the functional-calculus
and maximal-regularity interface; Lunardi gives interpolation and trace
spaces. The form and nonlinear sections recur in Ouhabaz, Barbu, Amann,
and the parabolic references. Tucsnak–Weiss and Curtain–Zwart supply the
control interface. Nonautonomous evolution and free-boundary applications
require additional regularity and compatibility hypotheses.

Local source copies consulted:

* [Engel–Nagel, A Short Course on Operator Semigroups](References/EngelNagel2006ShortCourseOperatorSemigroups-SpringerUTX.pdf).
* [Arendt–Batty–Hieber–Neubrander, Vector-Valued Laplace Transforms and Cauchy Problems](References/ArendtBattyHieberNeubrander2011VectorValuedLaplaceTransformsCauchyProblems-Birkhauser.MMA96.pdf).
* [Hytönen–van Neerven–Veraar–Weis, Analysis in Banach Spaces II](References/HytönenVanNeervenVeraarWeis2017AnalysisInBanachSpacesVol2ProbabilisticMethodsOperatorTheory-SpringerEMG.pdf).
* [Lunardi, Interpolation Theory](References/Lunardi2018InterpolationTheory-SpringerLNSNS16.pdf).
* [Barbu, Nonlinear Differential Equations of Monotone Types in Banach Spaces](References/Barbu2010NonlinearDifferentialEquationsMonotoneTypesBanachSpaces-Springer.SMM.pdf).
* [Tucsnak–Weiss, Observation and Control for Operator Semigroups](References/TucsnakWeiss2009ObservationControlOperatorSemigroups-Birkhauser.BAT.pdf).
