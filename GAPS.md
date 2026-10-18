# Principal gaps in the core knowledge of mathematical analysis

This catalogue compares the mathematical core described in `SYNOPSIS04.md` through
`SYNOPSIS53.md` with the combined coverage recorded in the corresponding Mathlib
and TauCeti inventories. It selects **645 principal theorem statements and theorem
families**, distributed unevenly across all fifty areas. Its emphasis is on
substantial missing mathematics: central representation and existence theorems,
analytic estimates, structural equivalences, and the theories they organize.
It does not attempt to list every omitted lemma or every result in the reference books.

The coverage assessment uses the **September 2026 inspections** documented in
[TauCetiCoverage.md](TauCetiCoverage.md), including the additions and narrowed gap
lists in each `Mathlibxx.md`. An entry means that the combined inventories do not
report the stated theorem at the indicated generality. This is a synthesis of
those inspections, rather than a new search of later library versions or a claim
that no equivalent formulation can be derived from existing results. Where an
entire theory was not located, its principal theorems specify the mathematical
content of the gap; they are not separate certificates of exhaustive source searches.

Numbers retain the synopsis provenance: **26.23** means result 23 of
`SYNOPSIS26.md`. They are deliberately nonconsecutive. Statements have occasionally
been combined with neighboring hypotheses or reformulated to stand alone. Each
field links to its mathematical synopsis and coverage inventory; its synopsis
also supplies the reference-text guide. Definitions and conventions recalled here
may themselves already be available. The **numbered assertions**, at the scope
specified in each assessment, are the selected gaps. Endpoint cases or special
settings may already be covered even when the displayed general theorem is missing.
Counts refer to selected statements or families, not to independent theorems or
percentages of a subject.

## Where the largest gaps lie

The foundation is much stronger than the upper layers. Measure construction,
scalar Radon–Nikodým theory, basic Banach and Hilbert principles, Euclidean Fourier
isometry, compact self-adjoint spectral theory, and much of classical contour
analysis are already present. TauCeti materially changes the picture through
maximal inequalities, Peter–Weyl, semigroup generation, weak Sobolev theory,
coercive variational PDE, optimal transportation, and one-variable complex analysis.
The remaining gaps should be assessed relative to that combined foundation.

| Areas | Selected statements | Mathematical assessment |
| :--- | ---: | :--- |
| 04–11: Real analysis, probability, dynamics, and inequalities | 76 | Scalar integration and classical inequalities are broad; refined limit theory, stochastic calculus, chaining, and pointwise dynamics remain major gaps. |
| 12–19: Convexity and functional analysis | 72 | Basic linear principles are broad; representation, weak compactness, nuclearity, Banach-space geometry, and ordered-space theory have substantial gaps. |
| 20–25: Algebras, spectra, semigroups, and integral equations | 67 | Abstract spectra, compact Fredholm theory, and semigroup generation are present; spectral measures, forms, operator algebras, and boundary integral operators remain large missing bodies. |
| 26–30: Sobolev, harmonic, and microlocal analysis | 56 | Several Euclidean estimates and compact-group harmonic analysis are present; trace theory, singular integrals, wavelets, LCA duality, and microlocal calculi are missing. |
| 31–34: Differential equations and dynamics | 62 | Local ODE theory and coercive weak elliptic existence are present; qualitative dynamics, regularity, dispersive estimates, and nonlinear evolution are largely undeveloped. |
| 35–39: Nonlinear, variational, geometric, and metric analysis | 75 | Smooth nonlinear calculus and several optimal-transport existence theorems are present; degree, relaxation, geometric measure theory, capacity, and metric diffusion remain large gaps. |
| 40–44: One-variable and global complex analysis | 52 | Classical contour theory and Riemann mapping are broad; global approximation, analytic function spaces, uniformization, and Teichmüller theory are major gaps. |
| 45–46: Several complex variables and complex dynamics | 36 | One-variable prerequisites are present; the higher-dimensional holomorphic, pluripotential, and iteration theories are largely missing. |
| 47–51: Approximation, special functions, asymptotics, and integrability | 77 | Concrete functions and bases are present; quantitative approximation, general recurrences, asymptotic methods, and integrable systems have extensive gaps. |
| 52–53: Geometric analysis and global spectral theory | 72 | Differential-geometric infrastructure is present; curvature estimates, geometric flows, manifold elliptic theory, Hodge theory, and index formulas form the largest missing layers. |

Several omissions are especially consequential because they connect many areas:

* **Duality and weak compactness:** scalar and vector-valued $L^p$ duality,
  reflexivity criteria, distribution structure, and nuclear kernel theorems connect
  the established linear foundations to variational and operator methods.
* **Singular integrals and boundary regularity:** Calderón–Zygmund and
  Littlewood–Paley theory, traces, and extensions connect Fourier analysis to
  elliptic estimates, boundary integral equations, and nonlinear PDE.
* **Continuous-time probability:** Brownian construction, martingale
  decomposition, Itô integration, and change of measure underpin diffusion,
  Malliavin calculus, rough paths, and stochastic PDE.
* **Spectral measures and forms:** the general spectral theorem and closed-form
  representation connect abstract operators to Schrödinger equations, Dirichlet
  forms, manifold heat kernels, and geometric spectral invariants.
* **Nonlinear compactness and geometry:** topological degree, maximal
  monotonicity, quasiconvex relaxation, Γ-convergence, BV, currents, and varifolds
  supply complementary existence and limiting principles.
* **Global complex and geometric analysis:** analytic boundary spaces, Stein and
  Dolbeault theory, curvature estimates, Hodge theory, and index formulas remain
  large missing bodies even though their elementary algebraic and differential
  prerequisites are often available.

The detailed selection follows the established field numbering. Related results
are normally assigned one principal home; distinct generalizations are retained
when their hypotheses and conclusions represent separate substantial gaps.

## 04. Real analysis, measure, and integration

The construction of measures, convergence theorems, scalar Radon–Nikodým theory, differentiation of measures, Haar measure, and weak convergence are broadly covered. TauCeti also supplies maximal estimates and smooth approximation. Two particularly consequential omissions are Lusin approximation and the surjectivity statement in scalar $L^p$ duality. The integral pairing alone supplies only one direction of that duality.

Sources: [mathematical synopsis](SYNOPSIS04.md); [combined coverage inventory](Mathlib04.md).

Throughout, $(X,\mathcal A,\mu)$ is a measure space; functions are real or complex
unless indicated otherwise, and equality in $L^p$ means equality almost
everywhere. Measures are positive unless explicitly called signed or complex.
Euclidean measure is denoted by $m$ or $\mathcal L^n$.

A **null set** is a measurable set of measure zero; a property holds almost
everywhere if it fails only on a null set. A measure is **locally finite** on
a topological space if every point has a neighborhood of finite measure.
The **Borel $\sigma$-algebra** is generated by the open sets. It is distinct
from its completion: for example, Lebesgue measurable subsets of Euclidean
space need not be Borel, although each differs from a Borel set by a null set.
Countable additivity implies continuity from below for increasing sets, and
continuity from above for decreasing sets when the first set has finite measure.

### Modes of convergence and approximation

**Convergence in measure** means
$\mu\{|f_n-f|>\varepsilon\}\to0$ for every $\varepsilon>0$.
On a finite measure space a family $\mathcal F\subseteq L^1$ is **uniformly
integrable** if
$\sup_{f\in\mathcal F}\int_{\{|f|>R\}}|f|\,d\mu\to0$ as $R\to\infty$.
On such a space, uniform integrability is equivalently a uniform $L^1$ bound
together with uniform absolute continuity of the integrals over sets of small
measure. For infinite measure spaces, global $L^1$ convergence additionally
requires control of mass escaping through the underlying space; local
convergence in measure by itself cannot supply this.

* **04.20. Lusin's theorem.** If $\mu$ is a finite Radon measure on a locally compact
  Hausdorff space and $f$ is finite-valued and measurable for its completion,
  then for every $\varepsilon>0$ there is a compact $K$ with
  $\mu(X\setminus K)<\varepsilon$ such that $f|_K$ is continuous.

### $L^p$ spaces and the analytic operations on them

For $1\leq p<\infty$, $L^p(\mu)$ consists of measurable functions modulo null
sets with norm $\|f\|_p=(\int|f|^p\,d\mu)^{1/p}$; $L^\infty$ has the essential
supremum norm. Exponents $p,q$ are **conjugate** if $1/p+1/q=1$.

* **04.39. Duality.** On a $\sigma$-finite space and for $1\leq p<\infty$,
  every continuous linear functional on $L^p$ has the form
  $f\mapsto\int f\overline g\,d\mu$ for a unique $g\in L^q$, and its norm is
  $\|g\|_q$. Over the real scalars the conjugation is omitted.

## 05. Differentiation and the fine structure of real functions

Ordinary and Fréchet differentiation, almost-everywhere differentiability of monotone and Lipschitz maps, absolute continuity, and covering theorems are established. TauCeti supplies the full Morse–Sard theorem. The remaining selection concerns the fine structure of derivatives, differentiation by rectangles, and extension between Hilbert spaces with the exact Lipschitz constant.

Sources: [mathematical synopsis](SYNOPSIS05.md); [combined coverage inventory](Mathlib05.md).

Here $I$ is a real interval, $U\subseteq\mathbb R^n$ is open, $\mathcal L^n$ is
Lebesgue measure, and $\mathcal H^s$ is Hausdorff measure, normalized so that
$\mathcal H^k$ agrees with $k$-dimensional volume on $k$-planes. Almost-everywhere
statements refer to Lebesgue measure unless another measure is specified.

### Derivatives as real functions: continuity, category, and Dini derivatives

The **upper and lower right Dini derivatives** are
$D^+f(x)=\limsup_{h\downarrow0}(f(x+h)-f(x))/h$ and $D_+f(x)$ with $\liminf$;
$D^-f,D_-f$ use $h\uparrow0$. Values in the extended real line are allowed.
A function is of **Baire class one** if it is a pointwise limit of continuous
functions. A **Darboux function** has the intermediate value property on intervals.

* **05.7. Baire classification of derivatives.** If $f$ is differentiable on an
  open interval, $f'$ is of Baire class one, as follows by taking continuous
  difference quotients locally.

* **05.10. Denjoy–Young–Saks theorem.** For any finite real function on an interval,
  almost every interior point has exactly one of the following types:
  all four Dini derivatives are the same finite number;
  $D^+=D^-=+\infty$ and $D_+=D_-=-\infty$;
  $D^+=+\infty$, $D_-=-\infty$, and $D_+=D^-$ is finite;
  or $D^-=+\infty$, $D_+=-\infty$, and $D_-=D^+$ is finite.

### Coverings, maximal functions, and differentiation bases

A **Vitali covering** of $E$ by balls supplies balls containing each point with
arbitrarily small radii. A **differentiation basis** assigns shrinking measurable
neighborhoods to each point and asks whether their averages recover a function.
The centered **Hardy–Littlewood maximal function** is
$$Mf(x)=\sup_{r>0}\frac1{|B(x,r)|}\int_{B(x,r)}|f(y)|\,dy.$$

* **05.30. Approximate continuity.** Every finite measurable function is
  approximately continuous almost everywhere: for almost every $x$ and every
  $\varepsilon>0$, the set $\{y:|f(y)-f(x)|>\varepsilon\}$ has density zero at $x$.

* **05.31. Rectangular differentiation.** In dimension $n\geq2$, averages over all
  axis-parallel rectangles shrinking to $x$, with unrestricted eccentricity,
  differentiate $L(\log^+L)^{n-1}_{\mathrm{loc}}$. They do not differentiate
  all of $L^1_{\mathrm{loc}}$. The associated strong maximal operator satisfies
  the endpoint bound
  $$|\{M_{\!S}f>\lambda\}|\leq C_n\int
    \frac{|f|}{\lambda}
    \left(1+\log^+\frac{|f|}{\lambda}\right)^{n-1}dx.$$

### Lipschitz functions and approximate differentiation

A map is **$L$-Lipschitz** if $|f(x)-f(y)|\leq L|x-y|$.
A measurable $f:U\to\mathbb R^m$ is **approximately differentiable** at $x$ if
some linear $A$ satisfies
$\operatorname*{ap\,lim}_{y\to x}|f(y)-f(x)-A(y-x)|/|y-x|=0$; an approximate
limit excludes a set of density zero. A **weak derivative** $D_i f=g$ satisfies
$\int f\partial_i\phi=-\int g\phi$ for all $\phi\in C_c^\infty(U)$.
The **Sobolev space** $W^{1,p}(U)$ consists of $L^p$ functions whose first weak
derivatives are in $L^p$; its local version imposes this on relatively compact
open subsets. Classical differentiability specifies behavior along every
approach to a point. Approximate differentiability specifies it on a set of
density one. The latter is therefore meaningful for almost-everywhere
equivalence classes, and the approximate derivative is unique wherever the
point has full density in the domain.

* **05.33. Kirszbraun's theorem.** An $L$-Lipschitz map from a subset of Euclidean
  space to another Euclidean space extends with the same constant. The theorem
  also holds for real Hilbert spaces.

## 06. Probability, measure-theoretic foundations, and limit theory

Independence, conditioning, disintegration, the strong law, the scalar central limit theorem, weak convergence, and substantial exchangeability theory are available. The principal omissions concern refined limit theory, functional limits, and large deviations. In 06.1 the missing generality is an arbitrary index set: countable standard-Borel extension is already covered, as are arbitrary independent product measures.

Sources: [mathematical synopsis](SYNOPSIS06.md); [combined coverage inventory](Mathlib06.md).

Throughout, $(\Omega,\mathcal F,\mathbb P)$ is a probability space,
$\mathbb E$ denotes integration against $\mathbb P$, and random variables are
measurable maps. Statements about distributions on general state spaces use
standard Borel spaces, or Polish spaces when topology is involved. Write
$X_n\Rightarrow X$ for convergence in distribution and
$S_n=\sum_{j=1}^nX_j$ for partial sums.

A **distribution function** is $F(x)=\mathbb P(X\leq x)$: it is increasing,
right-continuous, and has limits zero and one at the two infinities. Its jumps
are precisely the atoms of the law. The expectation of an integrable variable
is its first moment; centered second moments give variance and covariance.
**Identically distributed** means equality of laws, without asserting
independence. For a sequence, **exchangeability** means invariance of every
finite-dimensional law under permutations. These distinctions matter: laws of
large numbers, central limits, and mixture representations require different
forms of control of dependence.

### Independence, construction, and zero–one laws

The **law** of $X$ is $\mathbb P\circ X^{-1}$. A family of $\sigma$-fields is
**independent** if the probabilities of finite intersections factor; random
variables are independent when their generated $\sigma$-fields are. The
**tail $\sigma$-field** of a sequence is
$\bigcap_n\sigma(X_n,X_{n+1},\ldots)$.

* **06.1. Kolmogorov extension theorem.** A consistent family of finite-dimensional
  probability distributions with standard Borel coordinate spaces determines a
  unique law on the product $\sigma$-algebra. In particular, independent
  sequences with prescribed marginal laws can be constructed.

### Independent sums, random series, and laws of large numbers

* **06.22. Kolmogorov three-series theorem.** For independent real $X_n$ and any
  fixed $A>0$, put $Y_n=X_n1_{\{|X_n|\leq A\}}$. The series $\sum X_n$
  converges almost surely exactly when
  $$\sum_n\mathbb P(|X_n|>A)<\infty,\qquad
    \sum_n\mathbb E Y_n\text{ converges},\qquad
    \sum_n\operatorname{Var}(Y_n)<\infty.$$

* **06.26. Hartman–Wintner iterated-logarithm law.** For independent identically
  distributed centered $X_n$ with variance $0<\sigma^2<\infty$,
  $$\limsup_n\frac{S_n}{\sqrt{2\sigma^2n\log\log n}}=1,
    \qquad\liminf_n\frac{S_n}{\sqrt{2\sigma^2n\log\log n}}=-1
    \quad\text{almost surely}.$$

### Characteristic functions and classical distributional limits

The **characteristic function** of a real random variable is
$\varphi_X(t)=\mathbb E e^{itX}$. For a vector use $e^{i\langle t,X\rangle}$.
The law $N(m,\Sigma)$ has characteristic function
$\exp(i\langle t,m\rangle-\frac12t^{\mathsf T}\Sigma t)$.

* **06.32. Lindeberg–Feller theorem.** Let each row of a triangular array
  $X_{n,k}$ be independent and centered, and let
  $s_n^2=\sum_k\mathbb E X_{n,k}^2>0$. If for every $\varepsilon>0$,
  $$s_n^{-2}\sum_k\mathbb E\!
    \left[X_{n,k}^2 1_{\{|X_{n,k}|>\varepsilon s_n\}}\right]\longrightarrow0,$$
  then $s_n^{-1}\sum_kX_{n,k}\Rightarrow N(0,1)$. Under
  $\max_k\operatorname{Var}(X_{n,k})/s_n^2\to0$, this condition is also necessary.

* **06.34. Berry–Esseen bound.** For independent identically distributed centered
  variables with variance $\sigma^2>0$ and third absolute moment $\rho<\infty$,
  $$\sup_x\left|\mathbb P\{S_n/(\sigma\sqrt n)\leq x\}-\Phi(x)\right|
    \leq C\rho/(\sigma^3\sqrt n),$$
  where $C$ is universal and $\Phi$ is the standard normal distribution function.

### Gaussian laws, infinite divisibility, and random measures

A family is **Gaussian** if all finite real linear combinations are normally
distributed. A law is **infinitely divisible** if for every positive integer
$n$ it is the $n$-fold convolution of some law. A **Poisson random measure**
$N$ of intensity $\mu$ has independent counts on disjoint sets, with
$N(A)\sim\operatorname{Poisson}(\mu(A))$ when $\mu(A)<\infty$.

* **06.47. Lévy–Khintchine formula.** A real law is infinitely divisible exactly
  when its characteristic function is
  $$\exp\left(ibt-\tfrac12at^2+
    \int_{\mathbb R\setminus\{0\}}
    (e^{itx}-1-itx1_{\{|x|\leq1\}})\,\nu(dx)\right),$$
  where $a\geq0$, $b\in\mathbb R$, and
  $\int(1\wedge x^2)\,\nu(dx)<\infty$. This triplet is unique for the specified
  truncation convention.

### Functional limits and empirical distributions

For independent identically distributed real observations with distribution
function $F$, the **empirical distribution function** is
$F_n(x)=n^{-1}\sum_{j\leq n}1_{\{X_j\leq x\}}$. A **Brownian bridge** $B^0$
is the centered continuous Gaussian process on $[0,1]$ with covariance
$\min(s,t)-st$.

* **06.53. Donsker invariance principle.** For independent identically distributed
  centered variables with unit variance, the linearly interpolated partial-sum
  process $n^{-1/2}S_{\lfloor nt\rfloor}$ converges in law in $C[0,1]$ to
  standard Brownian motion. The displayed expression specifies the grid values;
  interpolation defines the continuous process between them.

### Large deviations and a basic branching model

A sequence of laws satisfies a **large deviation principle** with speed $n$
and **rate function** $I$ if $I$ is lower semicontinuous and
$$-\inf_{A^\circ}I\leq\liminf_n n^{-1}\log\mathbb P(X_n\in A)
  \leq\limsup_n n^{-1}\log\mathbb P(X_n\in A)
  \leq-\inf_{\overline A}I.$$
The rate is **good** when its sublevel sets are compact.
The relative entropy used below is nonnegative and vanishes exactly when its
two arguments are the same probability. It is defined using the density with
respect to the second measure; no density with respect to Lebesgue measure is
required. A large deviation principle estimates logarithmic probabilities at
exponential scale, while a central limit theorem describes fluctuations at
square-root scale. Neither statement alone supplies the uniform error bound
of a quantitative approximation such as Berry–Esseen.

The relative entropy is $D(\nu\|\mu)=\int\log(d\nu/d\mu)\,d\nu$ for $\nu\ll\mu$, and $+\infty$ otherwise.

* **06.56. Cramér's theorem.** For independent identically distributed real
  variables whose log moment generating function
  $\Lambda(t)=\log\mathbb E e^{tX_1}$ is finite near zero, $S_n/n$ satisfies a
  large deviation principle with good rate
  $I(x)=\sup_t\{tx-\Lambda(t)\}$.

* **06.57. Sanov's theorem.** For independent observations of law $\mu$ on a
  Polish space, the empirical measures satisfy a large deviation principle in
  the weak topology, with good rate
  $$H(\nu\mid\mu)=\int\log\frac{d\nu}{d\mu}\,d\nu$$
  when $\nu\ll\mu$, and $+\infty$ otherwise.

* **06.58. Varadhan's integral lemma.** If $X_n$ satisfies a large deviation
  principle with good rate $I$, then for bounded continuous $f$,
  $$\lim_n n^{-1}\log\mathbb E e^{nf(X_n)}=\sup_x(f(x)-I(x)).$$

## 07. Concentration, high-dimensional probability, and empirical processes

Sub-Gaussian moment-generating estimates, Hoeffding, Azuma–Hoeffding, McDiarmid, and the combinatorial Sauer–Shelah theorem are covered. The missing analytic steps are sharp geometric concentration, chaining, empirical-process estimates, and random-matrix asymptotics. Finite-dimensional Gaussian and Wishart laws supply examples and exact distributions, without establishing the asymptotic theorems below.

Sources: [mathematical synopsis](SYNOPSIS07.md); [combined coverage inventory](Mathlib07.md).

Random variables are real unless matrices are explicitly used. Constants $c,C$
are positive and universal unless dependence is indicated; their values can
change between statements. Suprema of processes are assumed measurable through
separability. For function classes one may, for example, assume a countable
pointwise-dense subclass; weak convergence in $\ell^\infty$ uses the customary
outer-probability formulation when necessary.

### Exponential moments and scalar deviations

A centered variable $X$ is **sub-Gaussian with variance proxy $v$** if
$\mathbb E e^{\lambda X}\leq e^{v\lambda^2/2}$ for all real $\lambda$.
The **Orlicz norms** used below are
$$\|X\|_{\psi_\alpha}=\inf\{s>0:
  \mathbb E\exp(|X|^\alpha/s^\alpha)\leq2\},\qquad\alpha=1,2.$$
Finite $\psi_2$ norm means sub-Gaussian tails; finite $\psi_1$ norm means
**sub-exponential** tails.

These norms concern tail size, not a particular distributional family. A bounded
variable is sub-Gaussian; a product or square of Gaussian variables is generally
only sub-exponential. Centering changes either norm by at most a universal
factor. Integrating tail bounds gives moments, while optimizing the
moment-generating-function bound gives tails. The distinction between a variance
proxy and the actual variance is essential: they need not be equal, and most
dimension-independent bounds retain the proxy supplied by the hypotheses.

* **07.4. Bernstein's inequality.** For independent centered $X_i$ with
  $|X_i|\leq b$ and $v=\sum_i\mathbb EX_i^2$,
  $$\mathbb P\left(\left|\sum_iX_i\right|\geq t\right)
    \leq2\exp\left(-\frac{t^2}{2(v+bt/3)}\right).$$

* **07.6. Equivalent sub-Gaussian descriptions.** Up to universal changes of
  constants, $\|X\|_{\psi_2}\leq K$ is equivalent to
  $\mathbb P(|X|>t)\leq2e^{-ct^2/K^2}$ and to
  $(\mathbb E|X|^p)^{1/p}\leq CK\sqrt p$ for $p\geq1$. For centered $X$ it
  is also equivalent to a Gaussian moment-generating-function bound.

### Product spaces, entropy, and geometric concentration

For $Z\geq0$, its **entropy** is
$\operatorname{Ent}(Z)=\mathbb E(Z\log Z)-\mathbb EZ\log\mathbb EZ$.
A probability $\mu$ satisfies a **Poincaré inequality** with constant $C$ if
$\operatorname{Var}_\mu f\leq C\int|\nabla f|^2d\mu$, and a
**logarithmic Sobolev inequality** with constant $C$ if
$\operatorname{Ent}_\mu(g^2)\leq2C\int|\nabla g|^2d\mu$.

$\gamma_d$ is standard Gaussian probability on $\mathbb R^d$ and $\Phi$ is the standard one-dimensional Gaussian distribution function.

* **07.16. Gaussian logarithmic Sobolev inequality.** For smooth $g$,
  $\operatorname{Ent}_{\gamma_d}(g^2)\leq2\int|\nabla g|^2d\gamma_d$.

* **07.19. Gaussian isoperimetry.** If $A$ is Borel and $A_r$ its open Euclidean
  $r$-neighborhood, then for $r>0$,
  $$\gamma_d(A_r)\geq\Phi(\Phi^{-1}(\gamma_d(A))+r).$$
  Halfspaces give equality. The formula is interpreted by limits for mass zero
  or one.

### Metric entropy, Gaussian comparison, and chaining

For a pseudometric space $(T,d)$, the **covering number** $N(T,d,\varepsilon)$
is the least number of $\varepsilon$-balls covering it. A centered process has
**sub-Gaussian increments** for $d$ if
$\|X_s-X_t\|_{\psi_2}\leq C d(s,t)$. For a Gaussian process its canonical
pseudometric is $d(s,t)=(\mathbb E|X_s-X_t|^2)^{1/2}$.

The **generic chaining functional** is
$$\gamma_2(T,d)=\inf_{(T_k)}\sup_{t\in T}
  \sum_{k\geq0}2^{k/2}d(t,T_k),\qquad
  |T_0|=1,\quad |T_k|\leq2^{2^k},$$
where the infimum runs over such sequences of subsets.

* **07.25. Dudley's entropy bound.** For a separable centered process with
  sub-Gaussian increments controlled by $d$,
  $$\mathbb E\sup_{t\in T}(X_t-X_{t_0})
    \leq C\int_0^{\operatorname{diam}T}
      \sqrt{\log N(T,d,\varepsilon)}\,d\varepsilon.$$
  Finiteness together with the corresponding vanishing small-scale entropy
  integral gives a bounded uniformly continuous version under the usual
  completion of the index space.

* **07.30. Majorizing measure theorem.** For a centered separable Gaussian
  process with canonical metric $d$,
  $$c\gamma_2(T,d)\leq\mathbb E\sup_tX_t\leq C\gamma_2(T,d).$$
  Thus multiscale chaining gives the correct size of every Gaussian supremum,
  up to universal constants.

### Empirical processes, combinatorial dimension, and uniform laws

For independent observations of law $P$, write
$P_nf=n^{-1}\sum_{i=1}^nf(X_i)$ and
$\mathbb G_nf=\sqrt n(P_n-P)f$. An **envelope** $F$ satisfies $|f|\leq F$ for
all $f\in\mathcal F$. A set class has **VC dimension** $v$ if $v$ is the largest
number of points on which it realizes every subset. A **bracket** $[l,u]$ is
the set of functions between $l$ and $u$; $N_{[]}(\varepsilon,\mathcal F,L^p(P))$
is the least number of brackets of $L^p(P)$ width at most $\varepsilon$ needed
to cover the class. A class is **$P$-Donsker** if $\mathbb G_n$ converges to the
tight centered Gaussian process of covariance $P(fg)-PfPg$ in
$\ell^\infty(\mathcal F)$.

* **07.31. Symmetrization.** For independent Rademacher signs $\varepsilon_i$,
  independent of the data,
  $$\mathbb E\sup_{f\in\mathcal F}|(P_n-P)f|
    \leq2\mathbb E\sup_{f\in\mathcal F}
      \left|\frac1n\sum_i\varepsilon_i f(X_i)\right|.$$

* **07.35. Uniform deviations for VC classes.** For a measurable VC set class
  of dimension $v\geq1$,
  $$\mathbb E\sup_{A\in\mathcal A}|P_n(A)-P(A)|
    \leq C\sqrt{v/n}.$$
  With probability at least $1-e^{-t}$, the supremum is at most
  $C\sqrt{v/n}+\sqrt{t/(2n)}$. In particular, the class is uniformly
  Glivenko–Cantelli.

### Random matrices and high-dimensional geometry

For a matrix $A$, write $\|A\|$ for its Euclidean operator norm and
$\|A\|_F$ for its Frobenius norm. A centered random vector is **isotropic** if
$\mathbb E XX^{\mathsf T}=I$; its sub-Gaussian norm is
$\sup_{|u|=1}\|\langle u,X\rangle\|_{\psi_2}$.
The **empirical spectral measure** of a self-adjoint $d\times d$ matrix is
$d^{-1}\sum_{j=1}^d\delta_{\lambda_j}$.

For a nonempty bounded set $T\subseteq\mathbb R^d$, its **Gaussian width** is
$w(T)=\mathbb E\sup_{x\in T}\langle G,x\rangle$, with standard Gaussian $G$.
For example, the width of the unit ball is $\mathbb E|G|$, of order $\sqrt d$;
the width of a finite collection of unit vectors is at most of order
$\sqrt{\log(2|T|)}$. Width measures the size of the relevant set of directions,
which can be much smaller than the ambient dimension. Net arguments control
all directions at one scale, while chaining and Gaussian comparison retain the
geometry across scales.

* **07.41. Hanson–Wright inequality.** If $X_i$ are independent centered
  sub-Gaussian variables with $\|X_i\|_{\psi_2}\leq K$, then for fixed real $A$,
  $$\mathbb P(|X^{\mathsf T}AX-\mathbb EX^{\mathsf T}AX|>t)
    \leq2\exp\left[-c\min\left(
      \frac{t^2}{K^4\|A\|_F^2},\frac{t}{K^2\|A\|}\right)\right].$$

* **07.42. Matrix Bernstein inequality.** For independent centered self-adjoint
  $d\times d$ matrices $Y_i$ with $\|Y_i\|\leq L$, put
  $v=\|\sum_i\mathbb E Y_i^2\|$. Then
  $$\mathbb P\left(\left\|\sum_iY_i\right\|\geq t\right)
    \leq2d\exp\left(-\frac{t^2}{2(v+Lt/3)}\right).$$

* **07.45. Johnson–Lindenstrauss lemma.** For $N$ points in Euclidean space and
  $0<\varepsilon<1$, a linear map into dimension
  $m\leq C\varepsilon^{-2}\log(2N)$ preserves all pairwise squared distances
  within factors $1-\varepsilon$ and $1+\varepsilon$.

* **07.48. Wigner semicircle law.** Let $W_d$ be symmetric with entries on and
  above the diagonal taken from an infinite independent identically distributed
  real array of mean zero, variance one, and finite fourth moment. The empirical
  spectral measures of $W_d/\sqrt d$ converge almost surely weakly to
  $$\frac1{2\pi}\sqrt{4-x^2}\,1_{[-2,2]}(x)\,dx.$$

* **07.49. Marchenko–Pastur law.** Let $X$ be $N\times d$ with independent
  identically distributed mean-zero, unit-variance real entries of finite fourth
  moment, taken consistently from an infinite array, and suppose $d/N\to y>0$.
  The empirical spectral measure of $N^{-1}X^{\mathsf T}X$ converges almost
  surely to
  $$\left(1-\frac1y\right)_+\delta_0+
    \frac{\sqrt{(b-x)(x-a)}}{2\pi yx}1_{[a,b]}(x)\,dx,
    \quad a=(1-\sqrt y)^2,\ b=(1+\sqrt y)^2.$$

## 08. Stochastic processes, martingales, and stochastic calculus

Discrete-time martingale convergence and sampling, kernels, and some Markov-chain constructions are available. The missing core is continuous-time probability: existence of Brownian motion, quadratic variation, stochastic integration, and diffusion theory. Definitions of Brownian finite-dimensional laws and localizing sequences do not give these existence, decomposition, or calculus theorems.

Sources: [mathematical synopsis](SYNOPSIS08.md); [combined coverage inventory](Mathlib08.md).

Unless stated otherwise, a filtered probability space satisfies the **usual
conditions**: the filtration is right-continuous and the initial $\sigma$-field
contains all null sets. Processes are identified up to indistinguishability when
appropriate. A **càdlàg** path is right-continuous with left limits. A process
is **adapted** if $X_t$ is $\mathcal F_t$-measurable, and **predictable** if it
is measurable for the $\sigma$-field generated by adapted left-continuous
processes. Write $M_t^*=\sup_{s\leq t}|M_s|$.

Two processes are **modifications** if they agree almost surely at each fixed
time; they are **indistinguishable** if, outside one null set, they agree at
all times. For continuous or càdlàg processes, equality on a countable dense
set of times promotes modification to indistinguishability. A sequence of
processes converges **uniformly on compact time intervals in probability**
when $\sup_{t\leq T}|X_t^n-X_t|\to0$ in probability for every finite $T$.
This mode of convergence is used for quadratic variations and stochastic
integral approximations; it is stronger than convergence at each individual time.

### Brownian motion and its sample paths

A **standard $d$-dimensional Brownian motion** $B$ starts at zero, has continuous
paths, and has increments $B_t-B_s$ independent of $\mathcal F_s$ with law
$N(0,(t-s)I_d)$ for $t\geq s$. Equivalently its coordinates are independent
standard real Brownian motions.

* **08.1. Existence and uniqueness in law.** Brownian motion exists as the
  continuous version of the centered Gaussian process of covariance
  $\mathbb E[B_s^iB_t^j]=\delta_{ij}\min(s,t)$. These finite-dimensional laws
  determine a unique probability law on continuous path space.

* **08.3. Strong Markov property.** For an almost surely finite stopping time $T$,
  $(B_{T+t}-B_T)_{t\geq0}$ is standard Brownian motion independent of
  $\mathcal F_T$.

* **08.4. Reflection principle.** For real Brownian motion and $a>0$,
  $$\mathbb P\left(\sup_{s\leq t}B_s\geq a\right)
    =2\mathbb P(B_t\geq a).$$
  Reflection after the first hit of $a$ preserves Brownian law.

* **08.7. Quadratic variation.** Along deterministic partitions with mesh tending
  to zero, sums of squared Brownian increments converge in probability to elapsed
  time, uniformly on compact time intervals. Along dyadic partitions convergence
  holds almost surely. Thus $[B^i,B^j]_t=\delta_{ij}t$.

### Continuous-time martingales and quadratic variation

A **local martingale** is an adapted càdlàg process admitting stopping times
$T_n\uparrow\infty$ almost surely such that each stopped process is a
martingale. A process is of **class $D$** on $[0,T]$ if its values at all
stopping times bounded by $T$ form a uniformly integrable family. A continuous
**semimartingale** is $X=X_0+M+A$, with $M_0=A_0=0$, $M$ a continuous local
martingale and $A$ adapted continuous of finite variation on compact intervals.

For continuous local martingales the quadratic variation $[M]$ and predictable
bracket $\langle M\rangle$ coincide. With jumps they need not: for a compensated
Poisson process the former is $N_t$ and the latter is $\lambda t$. In general,
for a locally square-integrable càdlàg martingale, the predictable bracket is
the predictable compensator of $[M]$. This distinction determines which
quantity appears in isometries and which appears in the pathwise jump term
of Itô's formula.

* **08.13. Doob–Meyer decomposition.** A càdlàg submartingale of class $D$ on a
  finite horizon has a unique decomposition $X=M+A$, with $M$ a uniformly
  integrable martingale and $A$ a predictable integrable increasing process,
  $A_0=0$.

### Stochastic integration and Itô's formula

For an elementary predictable process,
$H\cdot M=\sum_iH_i(M_{t\wedge t_{i+1}}-M_{t\wedge t_i})$.
The **Itô integral** extends this construction by isometry and localization.
A general càdlàg **semimartingale** is a sum of a local martingale and an
adapted finite-variation process; predictable locally bounded integrands are
always integrable against it.

* **08.17. Itô isometry.** For a square-integrable continuous martingale $M$ with
  $M_0=0$, predictable $H$ satisfying
  $\mathbb E\int_0^TH_s^2d\langle M\rangle_s<\infty$ has a square-integrable
  martingale integral and
  $$\mathbb E\left(\int_0^TH_s\,dM_s\right)^2
    =\mathbb E\int_0^TH_s^2d\langle M\rangle_s.$$

* **08.21. Itô's formula for continuous semimartingales.** For $X$ in
  $\mathbb R^d$ and $f\in C^{1,2}$,
  $$df(t,X_t)=\partial_tf(t,X_t)\,dt+
    \sum_i\partial_if(t,X_t)\,dX_t^i+
    \tfrac12\sum_{i,j}\partial_{ij}f(t,X_t)\,d[X^i,X^j]_t.$$

* **08.23. Burkholder–Davis–Gundy inequalities.** For each $p>0$ there are
  $c_p,C_p>0$ such that every continuous local martingale starting at zero
  satisfies
  $$c_p\mathbb E\langle M\rangle_T^{p/2}
    \leq\mathbb E(M_T^*)^p
    \leq C_p\mathbb E\langle M\rangle_T^{p/2}.$$
  Stopping times are allowed, with infinite expectations interpreted by localization.

* **08.26. Brownian martingale representation.** In the augmented natural
  filtration of $d$-dimensional Brownian motion, every square-integrable
  $\mathcal F_T$-measurable $\xi$ has a unique representation
  $$\xi=\mathbb E\xi+\int_0^TH_s\,dB_s,
    \qquad\mathbb E\int_0^T|H_s|^2ds<\infty.$$
  Uniqueness is modulo $dt\,d\mathbb P$-null sets.

### Stochastic exponentials and change of measure

For a continuous local martingale $M$ with $M_0=0$, its **stochastic
exponential** is $\mathcal E(M)_t=\exp(M_t-\frac12\langle M\rangle_t)$.

* **08.29. Girsanov's theorem.** If
  $$Z_T=\exp\left(\int_0^T\theta_s\,dB_s-
                      \tfrac12\int_0^T|\theta_s|^2ds\right)$$
  is a martingale density and $d\mathbb Q=Z_Td\mathbb P$, then
  $B_t-\int_0^t\theta_sds$ is Brownian motion under $\mathbb Q$ on $[0,T]$.
  More generally, continuous local martingales acquire the covariation drift
  prescribed by the logarithmic stochastic integral of the density.

### Stochastic differential equations and their analytic equations

An **Itô SDE** is
$$dX_t=b(t,X_t)\,dt+\sigma(t,X_t)\,dB_t.$$
A **strong solution** is constructed for the given driving Brownian motion
and initial data; a **weak solution** includes a choice of probability space
and driving motion. **Pathwise uniqueness** compares solutions with the same
noise and initial data; **uniqueness in law** compares distributions.

$a=\sigma\sigma^{\mathsf T}$ and $L=b\cdot\nabla+\tfrac12\operatorname{tr}(aD^2)$ denote the diffusion matrix and generator in the time-homogeneous case.

* **08.31. Existence and pathwise uniqueness for Lipschitz coefficients.** If
  $b,\sigma$ are measurable in time, globally Lipschitz in space, and of linear
  growth, uniformly on bounded time intervals, then for square-integrable
  initial data independent of future Brownian increments there is a unique
  strong continuous solution on every finite horizon.

* **08.33. Yamada–Watanabe principle.** Weak existence together with pathwise
  uniqueness implies strong existence and uniqueness in law. Thus the analytic
  construction of a weak solution can be combined with a separate pathwise
  uniqueness argument.

* **08.36. Feynman–Kac formula.** Let a diffusion have smooth bounded coefficients
  with uniformly elliptic $a$, let $V$ be smooth bounded real-valued, and let
  $g$ be smooth with bounded derivatives. Then
  $$u(t,x)=\mathbb E_x\left[e^{-\int_0^tV(X_s)ds}g(X_t)\right]$$
  is the bounded classical solution of
  $\partial_tu=Lu-Vu$, $u(0,\cdot)=g$. Uniqueness follows from Itô's formula;
  versions with forcing and exit-time boundary data follow by the same argument.

### Local time, occupation, and reflection

For a real continuous semimartingale $X$, its **local time** $L_t^a$ is the
occupation density with respect to quadratic variation, with normalization fixed by the occupation identity below. For a general semimartingale a right-local-time
version can be chosen; for Brownian motion the spatial versions coincide.

* **08.41. Occupation density formula.** For nonnegative Borel $f$,
  $$\int_0^tf(X_s)\,d[X]_s=\int_{\mathbb R}f(a)L_t^a\,da.$$
  In particular, for Brownian motion $L_t^a$ measures occupation per unit
  spatial length and can be obtained as the limit of normalized times spent
  in shrinking intervals about $a$.

### Poisson integration and Lévy processes

A **Lévy process** starts at zero, has stationary independent increments, is
stochastically continuous, and is taken in its càdlàg version. A Poisson random
measure $N(dt,dz)$ of intensity $dt\,\nu(dz)$ counts jumps; its compensated
version is $\widetilde N=N-dt\,\nu$ when defined through integrable truncations.
The Brownian and Poisson noises used with a filtration have future increments
independent of its present $\sigma$-field.

* **08.54. Lévy–Itô decomposition.** A real Lévy process has the representation
  $$X_t=bt+\sigma B_t+
    \int_0^t\int_{|z|>1}z\,N(ds,dz)+
    \lim_{\varepsilon\downarrow0}
      \int_0^t\int_{\varepsilon<|z|\leq1}z\,\widetilde N(ds,dz),$$
  where $\int(1\wedge z^2)\nu(dz)<\infty$, Brownian motion and the Poisson
  random measure are independent, and the compensated small-jump limit exists
  in $L^2$ at each finite time and uniformly on compact time intervals in
  probability. Its characteristic exponent is the Lévy–Khintchine exponent.

## 09. Malliavin calculus, rough paths, and stochastic partial differential equations

Finite-dimensional Hermite chaos is covered. The selected chaos theorem concerns a general isonormal Gaussian family, including infinitely many coordinates. Beyond that specialization, Malliavin calculus, rough integration, stochastic evolution equations, and renormalized stochastic PDE are missing as developed theories. Their elementary Gaussian and deterministic functional-analytic prerequisites are present in neighboring sections.

Sources: [mathematical synopsis](SYNOPSIS09.md); [combined coverage inventory](Mathlib09.md).

Hilbert spaces are real and separable. On a Gaussian probability space,
$W:H\to L^2(\Omega)$ is **isonormal** if it is linear, centered Gaussian, and
$\mathbb E[W(h)W(k)]=\langle h,k\rangle_H$. Random variables in the Gaussian
parts are measurable with respect to $W$. On Wiener space,
$H=L^2([0,T];\mathbb R^d)$ and $W(h)=\int h\,dB$. Its associated
Cameron–Martin paths are $t\mapsto\int_0^th(s)ds$.

### Wiener chaos and differential calculus on Gaussian space

A **smooth cylindrical functional** is
$F=f(W(h_1),\ldots,W(h_n))$, with smooth $f$ and sufficient moment bounds.
Its **Malliavin derivative** is
$DF=\sum_i\partial_if(W(h_1),\ldots,W(h_n))h_i$.
The **Wiener chaos** of order $q$ is the closed span of degree-$q$ Hermite
polynomials of Gaussian coordinates, orthogonalized against lower degrees.
Write $I_q(f)$ for the multiple Wiener integral of a symmetric tensor
$f\in H^{\odot q}$, with $I_0(c)=c$.

* **09.1. Wiener chaos decomposition.** Every $F\in L^2(\Omega)$ has a unique
  expansion $F=\sum_{q\geq0}I_q(f_q)$, convergent in $L^2$, and
  $\mathbb EF^2=\sum_{q\geq0}q!\|f_q\|^2$.

* **09.4. Closability and Sobolev spaces.** The cylindrical derivative is closable
  from $L^p(\Omega)$ to $L^p(\Omega;H)$ for $1<p<\infty$. Its iterates define
  the Banach spaces $\mathbb D^{k,p}$ with norm
  $\|F\|_{k,p}^p=\mathbb E|F|^p+\sum_{j=1}^k\mathbb E\|D^jF\|^p$.

### Ornstein–Uhlenbeck analysis, densities, and normal approximation

The **Ornstein–Uhlenbeck generator** is $LI_q(f)=-qI_q(f)$; on its domain
$L=-\delta D$. The pseudo-inverse is
$L^{-1}F=-\sum_{q\geq1}q^{-1}I_q(f_q)$, annihilating constants.
For $F=(F_1,\ldots,F_m)$, its **Malliavin covariance matrix** is
$\gamma_F=(\langle DF_i,DF_j\rangle_H)_{i,j}$.

The divergence $\delta$ is the adjoint of $D$: $\mathbb E[F\delta(u)]=\mathbb E\langle DF,u\rangle_H$ on its domain.

* **09.10. Mehler formula.** The chaos semigroup $P_tI_q=e^{-qt}I_q$ is
  $$P_tF(W)=\mathbb E'[F(e^{-t}W+\sqrt{1-e^{-2t}}W')],$$
  where $W'$ is an independent copy. It is a symmetric Markov contraction
  semigroup and $DP_tF=e^{-t}P_tDF$.

* **09.13. Clark–Ocone representation.** In the augmented Brownian filtration,
  for $F\in\mathbb D^{1,2}$,
  $$F=\mathbb EF+\int_0^T\mathbb E[D_tF\mid\mathcal F_t]\,dB_t.$$
  Thus differentiating the terminal functional identifies its martingale
  representation integrand.

* **09.15. Smooth-density criterion and integration by parts.** If
  $F_i\in\mathbb D^\infty=\bigcap_{k,p>1}\mathbb D^{k,p}$ and
  $\mathbb E(\det\gamma_F)^{-p}<\infty$ for every $p>1$, then $F$ has a
  smooth density. For sufficiently regular $G$,
  $$\mathbb E[\partial_i\phi(F)G]
    =\mathbb E\!\left[\phi(F)\delta\left(
      G\sum_j(\gamma_F^{-1})_{ij}DF_j\right)\right],$$
  and iteration yields higher density derivatives.

* **09.17. Hörmander's density theorem.** For a Stratonovich SDE with
  $C_b^\infty$ vector fields, assume the diffusion fields and their iterated
  brackets with the diffusion and drift fields span the tangent space at every
  point. Then the law at each positive time, from a fixed starting point, has
  a smooth density. The drift field alone is not included as a spanning direction.

### Young integration and the algebra of rough paths

For a continuous path $X$, write $X_{s,t}=X_t-X_s$.
For $1/3<\alpha\leq1/2$, an **$\alpha$-Hölder rough path** is a pair
$\mathbf X=(X,\mathbb X)$ with
$|X_{s,t}|\lesssim|t-s|^\alpha$, $|\mathbb X_{s,t}|\lesssim|t-s|^{2\alpha}$,
and **Chen's relation**
$\mathbb X_{s,t}=\mathbb X_{s,u}+\mathbb X_{u,t}+X_{s,u}\otimes X_{u,t}$.
It is **weakly geometric** when
$\operatorname{Sym}\mathbb X_{s,t}=\frac12X_{s,t}^{\otimes2}$.
Geometric rough paths are limits of iterated-integral lifts of smooth paths
in the corresponding rough-path topology.

* **09.20. Young's integration theorem.** If $X$ is $\alpha$-Hölder and $Y$ is
  $\beta$-Hölder with $\alpha+\beta>1$, Riemann sums define $\int Y\,dX$ and
  $$\left|\int_s^tY\,dX-Y_sX_{s,t}\right|
    \leq C\|Y\|_\beta\|X\|_\alpha|t-s|^{\alpha+\beta}.$$
  The analogous criterion is $1/p+1/q>1$ for finite variation exponents.

* **09.21. Sewing lemma.** If a continuous two-parameter increment $A_{s,t}$,
  zero on the diagonal, has defect
  $|A_{s,t}-A_{s,u}-A_{u,t}|\leq C|t-s|^\gamma$, $\gamma>1$, then there is
  a unique additive increment $I_{s,t}$ with
  $|I_{s,t}-A_{s,t}|\leq C_\gamma C|t-s|^\gamma$. Partition sums of $A$
  converge to $I$.

### Controlled integration and rough differential equations

A path $Y$ is **controlled by $X$** if
$Y_{s,t}=Y'_sX_{s,t}+R^Y_{s,t}$, with $Y'$ $\alpha$-Hölder and $R^Y$
$2\alpha$-Hölder. An **RDE** $dY=V(Y)\,d\mathbf X$ is an equation in this
controlled-path space, rather than an equation based only on the first-level path.

* **09.24. Controlled rough integration.** For a controlled pair $(Y,Y')$, sewing
  $Y_sX_{s,t}+Y'_s\mathbb X_{s,t}$ defines the integral, with error of order
  $|t-s|^{3\alpha}$. The integral is again controlled, with derivative $Y$.

* **09.27. RDE existence and uniqueness.** For $V\in C_b^3$ and
  $1/3<\alpha\leq1/2$, every initial value and $\alpha$-Hölder rough path
  determine a unique global RDE solution on a finite interval. For general
  finite $p$-variation, $\operatorname{Lip}^\gamma$ vector fields with
  $\gamma>p$ give the corresponding theorem.

### Hilbert-space stochastic integration and evolution equations

Let $U,H$ be Hilbert spaces. A **cylindrical Wiener process** on $U$ is the
formal series $W_t=\sum_k\beta_k(t)e_k$; its coordinates exist even when the
series does not converge in $U$. The Hilbert–Schmidt operators from $U$ to $H$
form $L_2(U,H)$. For an evolution semigroup $S(t)$ with generator $A$, a
**mild solution** of $dX=(AX+F(X))dt+B(X)dW$ satisfies the variation-of-constants
formula in result 09.39.

* **09.39. Lipschitz mild equations.** If $S$ is a strongly continuous contraction semigroup
  and $F:H\to H$, $B:H\to L_2(U,H)$ are globally Lipschitz, square-integrable
  initial data give a unique adapted continuous mild solution
  $$X_t=S(t)X_0+\int_0^tS(t-s)F(X_s)ds+
                     \int_0^tS(t-s)B(X_s)dW_s.$$
  It has finite $\mathbb E\sup_{t\leq T}\|X_t\|^2$ and continuous dependence
  on its initial data.

### Random-field SPDE and spatial regularity

**Space-time white noise** is the centered Gaussian random distribution with
covariance $\mathbb E[\xi(\phi)\xi(\psi)]=\int\phi\psi$.
The **Walsh integral** integrates predictable functions against the associated
orthogonal martingale measure. For the heat operator $\Delta$, write
$p_t(x)=(4\pi t)^{-d/2}e^{-|x|^2/(4t)}$.

* **09.49. Dalang's condition.** For temporally white Gaussian noise whose
  spatial covariance is a nonnegative tempered measure with spectral measure
  $\mu$, the heat stochastic convolution exists at a point exactly when
  $$\int_{\mathbb R^d}\frac{\mu(d\zeta)}{1+|\zeta|^2}<\infty.$$
  This condition also gives the standard Lipschitz semilinear random-field
  existence theory for bounded initial data.

### Distributional products and the entrance to singular SPDE

Write $\mathcal C^\alpha=B_{\infty,\infty}^\alpha$ for Hölder–Besov spaces,
using parabolic scaling when time is present. A **regularity structure** consists
of a graded space of local expansion symbols and a group transporting such
expansions between base points. A **model** $(\Pi_x,\Gamma_{xy})$ realizes the
symbols as distributions and satisfies compatibility
$\Pi_x\Gamma_{xy}=\Pi_y$ with the prescribed scaling bounds. A
**modelled distribution** of regularity $\gamma$ has local coefficients whose
transported differences in homogeneity $\beta$ are $O(|x-y|^{\gamma-\beta})$.

* **09.55. Reconstruction theorem.** For a model and a modelled distribution
  $f$ of regularity $\gamma>0$, there is a unique distribution $\mathcal Rf$
  satisfying
  $$|\langle\mathcal Rf-\Pi_xf(x),\phi_x^\lambda\rangle|
    \lesssim\lambda^\gamma$$
  locally, uniformly over normalized smooth test functions at scale $\lambda$.
  Test regularity exceeds the negative of the lowest homogeneity.
  Reconstruction is locally continuous jointly in the model and coefficients.

* **09.56. Renormalized two-dimensional cubic equation.** On the two-dimensional
  torus, smooth initial data and mollified space-time white noise yield solutions
  of
  $$\partial_tu_\varepsilon=(\Delta-1)u_\varepsilon
     -u_\varepsilon^3+3C_\varepsilon u_\varepsilon+\xi_\varepsilon,$$
  where $C_\varepsilon$ is the variance of the stationary mollified linear
  convolution. With this Wick normalization the solutions converge in
  probability on finite horizons in $C([0,T];\mathcal C^{-\kappa})$,
  $\kappa>0$, to a mollifier-independent solution. The divergent linear
  counterterm is part of the equation's definition.

## 10. Ergodic theory and measurable dynamics

Poincaré recurrence, elementary ergodicity, topological entropy, and Hilbert-space mean ergodic convergence are covered; TauCeti identifies the $L^2$ limit with invariant conditional expectation. The missing core includes pointwise averages, measurable entropy, ergodic decomposition, and smooth ergodic theory. Characterization of ergodic measures as extreme points does not by itself supply decomposition.

Sources: [mathematical synopsis](SYNOPSIS10.md); [combined coverage inventory](Mathlib10.md).

A **probability-preserving system** $(X,\mathcal B,\mu,T)$ consists of a standard
probability space and a measurable transformation satisfying
$\mu(T^{-1}A)=\mu(A)$. Invertibility is assumed when negative iterates, unitary
spectral theory, or two-sided generators are used. Its **invariant
$\sigma$-field** is $\mathcal I=\{A:T^{-1}A=A\bmod\mu\}$.
The system is **ergodic** if $\mathcal I$ is trivial. A **factor** is a
probability-preserving quotient $\pi$ satisfying $\pi T=S\pi$ almost everywhere;
an **isomorphism** is an invertible such map modulo null sets.

The invariant measure is part of the system: one topological transformation
can support many mutually singular ergodic probabilities with different
entropies and recurrence statistics. A periodic orbit carries an invariant
atomic probability, while a mixing system need not have any periodic points
in a particular measurable model. Accordingly, statements about orbit counts
below have explicit topological or symbolic hypotheses; measurable isomorphism
preserves entropy and spectral structure, but it does not preserve arbitrary
features of a chosen topology.

### Recurrence, induction, and the ergodic theorems

For $A$ of positive measure, its **first return time** is
$\tau_A(x)=\inf\{n\geq1:T^nx\in A\}$ on $A$; the induced transformation is
$T_Ax=T^{\tau_A(x)}x$. Write
$A_Nf=N^{-1}\sum_{n=0}^{N-1}f\circ T^n$.

* **10.5. Birkhoff pointwise theorem.** For $f\in L^1$,
  $A_Nf\to\mathbb E[f\mid\mathcal I]$ almost everywhere and in $L^1$.
  In an ergodic system the limit is $\int f\,d\mu$. For $f\in L^p$,
  $1\leq p<\infty$, convergence also holds in $L^p$.

* **10.7. Kingman's subadditive theorem.** If integrable $f_n$ satisfy
  $f_{n+m}\leq f_n+f_m\circ T^n$ and
  $\inf_n n^{-1}\int f_n\,d\mu>-\infty$, then $f_n/n$ converges almost
  everywhere and in $L^1$ to an invariant integrable function. In the ergodic
  case the limit is $\inf_n n^{-1}\int f_n\,d\mu$.

* **10.8. Ergodic decomposition.** A probability-preserving standard system
  decomposes into ergodic invariant probabilities $\mu_\omega$ with
  $\mu=\int\mu_\omega\,d\eta(\omega)$. For integrable $f$, the component
  integrals realize $\mathbb E[f\mid\mathcal I]$. The decomposition is unique
  in its standard measure-theoretic sense.

* **10.9. Rokhlin tower lemma.** For an invertible aperiodic standard probability
  system, every height $n$ and $\varepsilon>0$ admit a measurable base $B$
  with $B,TB,\ldots,T^{n-1}B$ disjoint and union of measure greater than
  $1-\varepsilon$.

### Entropy and measurable classification

For a finite or countable partition $\mathcal P$, define
$H_\mu(\mathcal P)=-\sum_{P\in\mathcal P}\mu(P)\log\mu(P)$, with
$0\log0=0$, and
$\mathcal P_0^{n-1}=\bigvee_{j=0}^{n-1}T^{-j}\mathcal P$.
The **entropy rate** is
$h_\mu(T,\mathcal P)=\lim_n n^{-1}H_\mu(\mathcal P_0^{n-1})$.
The **Kolmogorov–Sinai entropy** $h_\mu(T)$ is the supremum of these rates over
finite partitions. Natural logarithms are used.

* **10.20. Kolmogorov–Sinai generator theorem.** If $H(\mathcal P)<\infty$ and
  $\bigvee_{n\in\mathbb Z}T^{-n}\mathcal P$ generates the measurable sets
  modulo null sets, then $h_\mu(T)=h_\mu(T,\mathcal P)$.

* **10.21. Shannon–McMillan–Breiman theorem.** For an ergodic system and a
  partition of finite entropy,
  $$-\frac1n\log\mu(\mathcal P_0^{n-1}(x))
    \longrightarrow h_\mu(T,\mathcal P)$$
  almost everywhere and in $L^1$. Typical length-$n$ names therefore have
  probability on the exponential scale $e^{-nh}$.

* **10.26. Ornstein isomorphism theorem.** Two two-sided Bernoulli shifts of the
  same entropy are measurably isomorphic, including the standard infinite-entropy
  case. Entropy is thus a complete invariant within this class, although it is
  not a complete invariant for arbitrary ergodic transformations.

### Topological dynamics and thermodynamic formalism

Here $T:X\to X$ is continuous on a compact metric space. Set
$d_n(x,y)=\max_{j<n}d(T^jx,T^jy)$; an $(n,\varepsilon)$-separated set has
pairwise $d_n$ distances greater than $\varepsilon$. Topological entropy is the
exponential growth rate of maximal separated sets as $n\to\infty$ followed by
$\varepsilon\downarrow0$. For continuous $\phi$, **pressure** weights each
point by $\exp(S_n\phi(x))$, where $S_n\phi=\sum_{j<n}\phi\circ T^j$.

* **10.32. Variational principle for entropy.**
  $h_{\mathrm{top}}(T)=\sup_{\mu\in\mathcal M_T}h_\mu(T)$.
  The supremum need not be attained without further hypotheses.

* **10.34. Ruelle–Perron–Frobenius theorem.** On a mixing one-sided finite-type
  shift and for Hölder $\phi$, the transfer operator
  $\mathcal L_\phi f(x)=\sum_{Ty=x}e^{\phi(y)}f(y)$ has a simple positive
  leading eigenvalue $e^{P(\phi)}$, a positive Hölder eigenfunction, and an
  eigenmeasure. The remaining spectrum on the Hölder space is separated from
  the leading eigenvalue; their normalized product is the unique equilibrium state.

### Lyapunov exponents and smooth ergodic theory

A **linear cocycle** is $A^{(n)}(x)=A(T^{n-1}x)\cdots A(x)$.
Its Lyapunov exponents describe exponential growth of vectors and singular
values. For a diffeomorphism the principal example is $A(x)=DT_x$.
The multiplicity $m_i$ is the dimension of the exponent space.

* **10.38. Oseledets multiplicative ergodic theorem.** For an invertible ergodic
  base, $A(x)\in GL(d,\mathbb R)$, and integrable
  $\log^+\|A\|+\log^+\|A^{-1}\|$, there are exponents
  $\lambda_1>\cdots>\lambda_r$ and a measurable invariant splitting
  $\mathbb R^d=\bigoplus_iE_i(x)$ with
  $n^{-1}\log|A^{(n)}(x)v|\to\lambda_i$ for nonzero $v\in E_i(x)$.

### Joinings, recurrence, and nonconventional averages

A **joining** is an invariant probability on a product system with the given
marginals. Two systems are **disjoint** if their product measure is their only
joining. The terminology concerns stationary couplings, rather than
independence of random variables already placed on one probability space.

* **10.46. Furstenberg multiple recurrence.** If $\mu(A)>0$ and $k\geq1$, then
  $$\liminf_{N\to\infty}\frac1N\sum_{n=1}^N
    \mu(A\cap T^{-n}A\cap\cdots\cap T^{-kn}A)>0.$$

## 11. Classical inequalities, means, majorization, and rearrangement

The classical finite-sum inequalities, Jensen, Hölder, Minkowski, finite rearrangement, and the Birkhoff theorem on doubly stochastic matrices are covered. The principal gaps here are the majorization theorem linking such matrices to ordered vectors and the classical Hardy–Hilbert inequalities. Geometric and function-rearrangement consequences are selected in Sections 14, 27, and 37.

Sources: [mathematical synopsis](SYNOPSIS11.md); [combined coverage inventory](Mathlib11.md).

Weights $w_i$ are positive and sum to one unless stated otherwise; means are
initially defined for positive $x_i$. Conjugate exponents satisfy
$1/p+1/p'=1$. Integrals of nonnegative functions may be infinite unless a
finite bound is asserted. Sharp constants are identified where they are a
standard part of the theorem, rather than supplied for every variant.

### Convexity and means

A function is **convex** if
$\phi((1-t)x+ty)\leq(1-t)\phi(x)+t\phi(y)$ for $0\leq t\leq1$.
For $r\ne0$ the **power mean** is
$M_r(x;w)=(\sum_iw_ix_i^r)^{1/r}$; its continuous value at $r=0$ is
$M_0=\prod_i x_i^{w_i}$. The limiting means $M_{-\infty},M_\infty$ are the
minimum and maximum. The arithmetic, geometric, and harmonic means are
$M_1,M_0,M_{-1}$.

A **quasi-arithmetic mean** replaces a number by an increasing continuous
coordinate, takes the weighted arithmetic mean there, and transforms back.
Different coordinates can give the same mean: replacing a generator
$\phi$ by $a\phi+b$, $a\ne0$, leaves its mean unchanged. For means on an
interval, **internality** means lying between the smallest and largest input;
the power and quasi-arithmetic means are internal. Homogeneity and invariance
under simultaneous translations are distinct properties and are not satisfied
by every mean in the same family.

* **11.9. Newton and Maclaurin inequalities.** If $e_k$ is the $k$th elementary
  symmetric polynomial of nonnegative $x_1,\ldots,x_n$ and
  $E_k=e_k/\binom nk$, then $E_k^2\geq E_{k-1}E_{k+1}$ for $1\leq k<n$.
  Consequently $E_1\geq E_2^{1/2}\geq\cdots\geq E_n^{1/n}$.

### Majorization, convex order, and entropy

Write $x\prec y$ if
$\sum_{i=1}^k x_i^\downarrow\leq\sum_{i=1}^k y_i^\downarrow$ for $k<n$ and
the total sums agree. A **doubly stochastic matrix** is nonnegative with each
row and column sum one. A function is **Schur-convex** if $x\prec y$ implies
$\Phi(x)\leq\Phi(y)$. For integrable random variables,
$X\leq_{\mathrm{cx}}Y$ means that convex expectations are ordered whenever
defined, allowing extended values under the usual common affine lower bounds.

Majorization compares vectors of the same total mass; weak majorization omits
that equality and is tested by increasing convex functions. For probability
vectors it measures departure from uniformity. Convex order compares laws
with equal first moment, rather than an order of individual outcomes. The
martingale coupling formulation makes clear that a distribution can become
more spread out while preserving its mean, without either random variable
being pointwise larger than the other.

* **11.21. Hardy–Littlewood–Pólya characterization.** $x\prec y$ exactly when
  $x=Dy$ for a doubly stochastic matrix, and exactly when $x$ belongs to the
  convex hull of the permutations of $y$.

* **11.23. Karamata's inequality.** If $x\prec y$ and $\phi$ is convex on an
  interval containing their entries, then $\sum_i\phi(x_i)\leq\sum_i\phi(y_i)$.
  For strictly convex $\phi$, equality requires $x$ and $y$ to be permutations.

### Hardy, Hilbert, and differential inequalities

* **11.31. Discrete Hardy inequality.** For nonnegative $a_n$ and $1<p<\infty$,
  $$\sum_{n\geq1}\left(\frac{a_1+\cdots+a_n}{n}\right)^p
    \leq(p')^p\sum_{n\geq1}a_n^p.$$
  The constant is optimal.

* **11.36. Hilbert's integral inequality.** For $1<p<\infty$, $p'=p/(p-1)$, and nonnegative $f\in L^p(0,\infty)$,
  $g\in L^{p'}(0,\infty)$,
  $$\int_0^\infty\!\int_0^\infty\frac{f(x)g(y)}{x+y}dxdy
    \leq\frac{\pi}{\sin(\pi/p)}\|f\|_p\|g\|_{p'}.$$
  The same optimal constant holds in the discrete sum with denominator $m+n$,
  $m,n\geq1$.

* **11.37. Carleman's inequality.** For a nonnegative summable sequence,
  $\sum_{n\geq1}(a_1\cdots a_n)^{1/n}\leq e\sum_{n\geq1}a_n$.
  The constant $e$ is optimal.

## 12. Convexity, convex analysis, and variational analysis

Separation, finite-dimensional convex geometry, Krein–Milman, and convex minimax are well represented. TauCeti defines conjugates and subdifferentials and proves Fenchel–Young. The missing bridges are biconjugate equality, subdifferential calculus, proximal minimization, strong duality, and variational principles. Definitions of these convex objects do not supply the corresponding existence and representation theorems.

Sources: [mathematical synopsis](SYNOPSIS12.md); [combined coverage inventory](Mathlib12.md).

A convex function $f:E\to(-\infty,\infty]$ is **proper** if it never takes
$-\infty$ and is finite somewhere. Its **effective domain** is $\operatorname{dom}f$;
it is **lower semicontinuous** when its epigraph is closed. The conjugate is
$f^*(u)=\sup_x(\langle u,x\rangle-f(x))$, with $u$ in the continuous dual.
The **subdifferential** is
$\partial f(x)=\{u:f(y)\geq f(x)+\langle u,y-x\rangle\ \forall y\}$ at
points of finite value, and is empty elsewhere. Unless specified otherwise,
geometric statements are in $\mathbb R^n$.

### Separation and convex geometry

The **convex hull** is the set of finite convex combinations. A point of a
convex set is **extreme** if it lies in no nontrivial open segment of the set.
A **convex body** is a compact convex set with nonempty interior. Relative
interior means interior in the affine hull; it is often the correct
finite-dimensional qualification when ordinary interior is empty.

* **12.8. Choquet representation.** In a compact metrizable convex subset of a
  locally convex space, every point is the barycenter of a probability carried
  by the extreme points. Barycenter means equality after evaluation by every
  continuous affine function.

### Convex functions, derivatives, and conjugacy

The one-sided **directional derivative** is
$f'(x;d)=\lim_{t\downarrow0}(f(x+td)-f(x))/t$ when interpreted in the extended
sense. The **indicator** $\delta_C$ is zero on $C$ and infinity outside;
the **support function** is $h_C(u)=\sup_{x\in C}\langle u,x\rangle$.

* **12.15. Alexandrov's theorem.** A finite convex function on an open convex
  subset of $\mathbb R^n$ has a second-order Taylor expansion at almost every
  point. Its almost-everywhere Hessian is positive semidefinite.

* **12.17. Fenchel–Moreau theorem.** A proper lower semicontinuous convex
  function on a Hausdorff locally convex space equals its biconjugate.
  It is therefore the supremum of its continuous affine minorants.

* **12.19. Subdifferential sum rule.** For proper lower semicontinuous convex
  functions on a Banach space, if one is continuous at a point of their common
  domain, then $\partial(f+g)(x)=\partial f(x)+\partial g(x)$.
  In finite dimensions, intersecting relative interiors is a standard
  alternative qualification.

### Minimizers, projections, and monotone operators

Here $H$ is a real Hilbert space. The **normal cone** to a closed convex $C$
is $N_C(x)=\{u:\langle u,y-x\rangle\leq0\ \forall y\in C\}$ for $x\in C$.
An operator $A:H\rightrightarrows H$ is **monotone** if
$\langle x-y,u-v\rangle\geq0$ on its graph; it is **maximal monotone** if
its graph has no proper monotone enlargement. Its resolvent is
$J_{\gamma A}=(I+\gamma A)^{-1}$.

* **12.30. Proximal mapping.** For proper lower semicontinuous convex $f$,
  $$\operatorname{prox}_{\gamma f}(x)=
    \operatorname*{argmin}_y\left(f(y)+\frac{\|x-y\|^2}{2\gamma}\right)$$
  exists uniquely and equals $J_{\gamma\partial f}x$. It is firmly nonexpansive.

* **12.32. Moreau decomposition.**
  $\operatorname{prox}_{\gamma f}(x)+
  \gamma\operatorname{prox}_{f^*/\gamma}(x/\gamma)=x$.
  For indicators of closed convex cones, this becomes orthogonal decomposition
  into the cone and its polar.

### Duality and optimality conditions

* **12.37. Fenchel–Rockafellar duality.** For proper closed convex $f,g$ on
  Banach spaces and bounded linear $A$, assume $f(x_0)<\infty$ and $g$ is
  continuous at $Ax_0$. If the primal value is finite, then
  $$\inf_x\{f(x)+g(Ax)\}
    =\max_u\{-f^*(-A^*u)-g^*(u)\}.$$
  Dual attainment is asserted; primal attainment is a separate question.

* **12.38. Slater and KKT conditions.** For finite convex functions in
  $\mathbb R^n$, constraints $g_i\leq0$, and affine equalities $Ax=b$, a
  strictly feasible point implies that every minimizer has multipliers
  $\lambda_i\geq0,y$ with
  $$0\in\partial f(x_*)+\sum_i\lambda_i\partial g_i(x_*)+A^*y,
    \qquad\lambda_ig_i(x_*)=0.$$
  These conditions are sufficient for optimality even without strict feasibility.

### Variational convergence, nonsmooth calculus, and regularity

**Epi-convergence** $f_n\to f$ means the lower bound
$f(x)\leq\liminf f_n(x_n)$ for every $x_n\to x$, together with a recovery
sequence at each $x$ giving the reverse upper bound. **Mosco convergence** on
a Hilbert space uses weakly convergent sequences for the lower bound and
strongly convergent recovery sequences. For a locally Lipschitz function,
$f^\circ(x;d)=\limsup_{y\to x,t\downarrow0}(f(y+td)-f(y))/t$ and
$\partial_Cf(x)=\{u:\langle u,d\rangle\leq f^\circ(x;d)\ \forall d\}$.

* **12.43. Ekeland variational principle.** On a complete metric space, let $f$
  be proper lower semicontinuous and bounded below. If
  $f(x_0)\leq\inf f+\varepsilon$, then for every $\lambda>0$ some $x_\varepsilon$
  has $d(x_\varepsilon,x_0)\leq\lambda$, $f(x_\varepsilon)\leq f(x_0)$, and
  $f(y)>f(x_\varepsilon)-(\varepsilon/\lambda)d(y,x_\varepsilon)$ for $y\ne x_\varepsilon$.

* **12.48. Clarke gradient representation.** In finite dimensions, $\partial_Cf(x)$
  is nonempty compact convex and equals the closed convex hull of limits of
  ordinary gradients at differentiability points tending to $x$.
  Its support function is $f^\circ(x;\cdot)$.

## 13. Matrix analysis, operator monotonicity, and noncommutative inequalities

Finite-dimensional spectral constructions, singular values, positive matrix order, several operator-monotone functions, and the positive geometric mean are covered. TauCeti also supplies Pick-function representations. The outstanding results are variational eigenvalue comparison, singular-value inequalities, the characterization linking matrix monotonicity to Pick functions, and the trace and entropy inequalities below.

Sources: [mathematical synopsis](SYNOPSIS13.md); [combined coverage inventory](Mathlib13.md).

Matrices are complex unless specified otherwise, $A^*$ is the adjoint, and
$A\geq0$ means positive semidefinite; $A>0$ means positive definite.
The **Loewner order** is $A\leq B$ when $B-A\geq0$. Hermitian eigenvalues
$\lambda_1(A)\geq\cdots\geq\lambda_n(A)$ and singular values
$s_1(A)\geq\cdots\geq s_n(A)\geq0$ are in decreasing order.
The operator norm is $\|A\|=s_1(A)$; the Schatten norm is
$\|A\|_p=(\operatorname{tr}|A|^p)^{1/p}$, $|A|=(A^*A)^{1/2}$.

Products of positive matrices need not be Hermitian or positive, so their
order cannot be compared directly without an appropriate symmetric placement
of factors. Congruence $A\mapsto C^*AC$ preserves positivity; similarity
$A\mapsto C^{-1}AC$ preserves eigenvalues but generally does not preserve
Hermitian structure. Trace cyclicity permits cyclic permutations of factors,
rather than arbitrary permutations. These distinctions account for the
sandwiches, congruences, and trace expressions in the statements below.

### Spectral structure and variational comparison

* **13.5. Courant–Fischer principle.** For Hermitian $A$,
  $$\lambda_k(A)=\max_{\dim V=k}\min_{\substack{x\in V\\|x|=1}}x^*Ax
    =\min_{\dim V=n-k+1}\max_{\substack{x\in V\\|x|=1}}x^*Ax.$$

* **13.7. Cauchy interlacing.** Eigenvalues of a Hermitian compression to a
  codimension-one subspace interlace those of the original matrix. For a
  rank-$k$ perturbation this yields the corresponding index-shift bounds.

* **13.8. Weyl inequalities.** For Hermitian $A,B$,
  $\lambda_{i+j-1}(A+B)\leq\lambda_i(A)+\lambda_j(B)$ when $i+j-1\leq n$.
  In particular $|\lambda_i(A)-\lambda_i(B)|\leq\|A-B\|$.

* **13.10. Hoffman–Wielandt inequality.** For normal $A,B$, some matching of
  their eigenvalues satisfies
  $\sum_i|\lambda_i(A)-\lambda_{\pi(i)}(B)|^2\leq\|A-B\|_2^2$.
  For Hermitian matrices the decreasing-order matching works.

### Singular values, norms, and determinant inequalities

A norm is **unitarily invariant** if $\|UAV\|_{\!u}=\|A\|_{\!u}$ for unitary
$U,V$. Such norms correspond to symmetric gauge norms of the singular-value
vector. **Weak majorization** $a\prec_w b$ means all decreasing partial sums
of $a$ are bounded by those of $b$, without equality of total sums.

* **13.11. Von Neumann trace inequality.**
  $|\operatorname{tr}(A^*B)|\leq\sum_i s_i(A)s_i(B)$.

* **13.16. Eckart–Young–Mirsky theorem.** Truncating the SVD after $k$ terms
  gives a best rank-at-most-$k$ approximation in every unitarily invariant
  norm. Its operator error is $s_{k+1}$, and its squared Frobenius error is
  $\sum_{j>k}s_j^2$.

### Operator monotonicity and convexity

A real function on an interval is **operator monotone** if $A\leq B$ implies
$f(A)\leq f(B)$ in every matrix dimension. It is **operator convex** if
$f((1-t)A+tB)\leq(1-t)f(A)+tf(B)$ in every dimension. Scalar monotonicity or
convexity alone does not imply these stronger properties.

* **13.30. Loewner's theorem.** A function on an open real interval is operator
  monotone exactly when it is the real restriction of an analytic Pick
  function with nonnegative imaginary part on the upper half-plane, extending
  analytically across that interval. Real constants are included.

* **13.33. Choi–Davis–Jensen inequality.** For a unital positive linear map and
  operator-convex $f$, $f(\Phi(A))\leq\Phi(f(A))$ when the spectra lie in
  its interval of definition.

### Trace inequalities

* **13.44. Golden–Thompson inequality.** For Hermitian $H,K$,
  $\operatorname{tr}e^{H+K}\leq\operatorname{tr}(e^He^K)$.

* **13.45. Lieb concavity theorem.** For fixed $K$ and $0\leq t\leq1$,
  $(A,B)\mapsto\operatorname{tr}(K^*A^tKB^{1-t})$ is jointly concave on
  positive matrices, with endpoint zeroth powers interpreted as the identity.

### Completely positive maps and quantum entropy

A map $\Phi$ is **completely positive** if $I_k\otimes\Phi$ preserves
positivity for every $k$. A **quantum channel** is a completely positive
trace-preserving map. The von Neumann entropy is
$S(\rho)=-\operatorname{tr}\rho\log\rho$, in natural-logarithm units.
Partial traces define reduced density matrices such as $\rho_{AB}$ and $\rho_B$.

A **density matrix** is a positive semidefinite matrix of trace one. Its relative entropy is $D(\rho\|\sigma)=\operatorname{tr}\rho(\log\rho-\log\sigma)$ if $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$, and $+\infty$ otherwise; zero eigenvalues use the limiting convention.

* **13.56. Data processing.** Every quantum channel satisfies
  $D(\Phi(\rho)\|\Phi(\sigma))\leq D(\rho\|\sigma)$.
  Partial trace is an important special case.

* **13.58. Strong subadditivity.** For a tripartite state,
  $S(\rho_{ABC})+S(\rho_B)\leq S(\rho_{AB})+S(\rho_{BC})$.
  This is the nonnegativity of conditional mutual information.

## 14. Functional, isoperimetric, and geometric inequalities

Euclidean Sobolev embeddings, whole-space Morrey estimates, zero-boundary Poincaré estimates, and convex-domain Poincaré–Wirtinger estimates are available. The missing selection concerns critical and sharp inequalities, symmetrization and isoperimetry, and the curvature–dimension method. Existing Sobolev estimates should therefore be distinguished from sharp constants, extremizers, and endpoint exponential integrability.

Sources: [mathematical synopsis](SYNOPSIS14.md); [combined coverage inventory](Mathlib14.md).

Write $\omega_n=|B_1(0)|$, $p^*=np/(n-p)$ for $p<n$, and
$\mathcal E(f,f)=\int\Gamma(f)\,d\mu$ for a Dirichlet energy. A probability
measure satisfies **Poincaré with constant $C_P$** if
$\operatorname{Var}_\mu f\leq C_P\mathcal E(f,f)$, and **logarithmic Sobolev
with constant $C_{LS}$** if
$\operatorname{Ent}_\mu(f^2)\leq2C_{LS}\mathcal E(f,f)$.
Here $\operatorname{Ent}_\mu h=\int h\log(h/\int h\,d\mu)d\mu$.
The heat generator throughout is $\Delta$, rather than $\frac12\Delta$.

An inequality is **sharp** when its constant cannot be improved; this does
not imply that an admissible nonzero function attains equality. A **stability
inequality** controls distance from the family of extremizers by the deficit
in the sharp inequality. A **defective** functional inequality has an extra
lower-order term, often needed on finite-volume spaces where constants have
zero gradient. Scaling, boundary conditions, and normalization of total mass
must therefore be fixed before comparing constants from different formulations.

### Sobolev, interpolation, and singular-weight inequalities

The space $W^{1,p}(\Omega)$ consists of functions with themselves and their
weak first derivatives in $L^p$; $W_0^{1,p}$ is the closure of compactly
supported smooth functions. The homogeneous energy space on $\mathbb R^n$
is the completion in the gradient norm where the Sobolev inequality makes
this a function space. Constants below are finite and positive unless indicated.

* **14.3. Sharp quadratic Sobolev inequality.** For $n\geq3$, the best constant $S_n$ in $\|u\|_{2^*}\leq S_n\|\nabla u\|_2$, $2^*=2n/(n-2)$, is attained in the homogeneous space by
  $U(x)=(1+|x|^2)^{-(n-2)/2}$. Thus
  $S_n=\|U\|_{2^*}/\|\nabla U\|_2$; all nonzero real extremizers are its
  scalar multiples, translations, and dilations (Aubin–Talenti theorem).

* **14.8. Moser–Trudinger inequality.** If $n\geq2$, $|\Omega|<\infty$, and
  $u\in W_0^{1,n}(\Omega)$ with $\|\nabla u\|_n\leq1$, then
  $$\int_\Omega\exp(\alpha_n|u|^{n/(n-1)})dx\leq C_n|\Omega|,
    \qquad\alpha_n=n|S^{n-1}|^{1/(n-1)}.$$
  Increasing $\alpha_n$ makes the uniform bound false.

* **14.9. Hardy inequality.** For $1<p<n$,
  $\int|\nabla u|^p\geq((n-p)/p)^p\int|u|^p/|x|^p$ on
  $C_c^\infty(\mathbb R^n)$. The scale-invariant constant is optimal.

* **14.12. Hardy–Littlewood–Sobolev inequality.** If $0<\lambda<n$ and
  $1/p+1/q+\lambda/n=2$ with $p,q>1$, then
  $\iint |f(x)g(y)|/|x-y|^\lambda\,dxdy\leq C\|f\|_p\|g\|_q$.

### Capacity, perimeter, and spectral optimization

For compact $K\subset\Omega$, the relative **$p$-capacity** is
$\operatorname{cap}_p(K,\Omega)=\inf\int_\Omega|\nabla v|^p$, over
$v\in C_c^\infty(\Omega)$ at least one near $K$.
Perimeter is the total variation of the distributional gradient of an indicator;
it is meaningful for nonsmooth sets. The first Dirichlet eigenvalue is the
infimum of $\int|\nabla u|^2/\int u^2$ over nonzero $H_0^1(\Omega)$.

* **14.19. Faber–Krahn inequality.** A ball minimizes the first Dirichlet
  eigenvalue among open sets of fixed finite volume.

* **14.22. Quantitative isoperimetry.** For $n\geq2$ and finite positive-volume
  finite-perimeter $E$,
  $$\frac{P(E)}{n\omega_n^{1/n}|E|^{(n-1)/n}}-1
    \geq c_n\mathcal A(E)^2,$$
  where $\mathcal A(E)=\inf_{|B|=|E|}|E\triangle B|/|E|$ over balls.
  The quadratic asymmetry scale is sharp.

### Geometric inequalities for Gaussian, curved, and convex models

* **14.26. Brunn–Minkowski inequality.**
  $|A+B|^{1/n}\geq|A|^{1/n}+|B|^{1/n}$ for nonempty compact Euclidean sets.
  Convex bodies of positive volume have equality exactly when homothetic.

* **14.27. Prékopa–Leindler inequality.** If
  $h((1-t)x+ty)\geq f(x)^{1-t}g(y)^t$, $0<t<1$, then
  $\int h\geq(\int f)^{1-t}(\int g)^t$ for nonnegative integrable functions.
  This is a functional strengthening of Brunn–Minkowski.

### Functional inequalities and symmetric Markov semigroups

Let $(P_t)$ be a conservative symmetric Markov semigroup with generator $L$
and invariant measure $\mu$. A **Dirichlet form** is its closed energy
$\mathcal E(f,f)=-\langle f,Lf\rangle$. In diffusion settings
$\Gamma(f,g)=\frac12(L(fg)-fLg-gLf)$ and $\Gamma(f)=\Gamma(f,f)$.
Identities are first read on a smooth core and extended by closure;
probability is assumed when variance or normalized entropy is used.

* **14.38. Nash inequality.** On $\mathbb R^n$,
  $\|f\|_2^{2+4/n}\leq C_n\|\nabla f\|_2^2\|f\|_1^{4/n}$.
  This interpolates mass, energy, and square-integrability.

### Curvature–dimension calculus and Riemannian comparison

On a complete connected Riemannian manifold with smooth weight,
$L=\Delta-\nabla V\cdot\nabla$ is symmetric for $e^{-V}d\mathrm{vol}$.
Assume conservativity when using its semigroup. Set
$\Gamma_2(f)=\frac12L\Gamma(f)-\Gamma(f,Lf)$.
The **curvature–dimension condition** $CD(\kappa,N)$ is
$\Gamma_2(f)\geq\kappa\Gamma(f)+(Lf)^2/N$; the last term is zero for
$N=\infty$. Global probability inequalities below use normalized invariant mass.

The convention for $C_{LS}$ is $\operatorname{Ent}_\mu(f^2)\leq2C_{LS}\int\Gamma(f)\,d\mu$, with $\operatorname{Ent}_\mu(g)=\int g\log g\,d\mu-(\int g\,d\mu)\log\int g\,d\mu$.

* **14.46. Bakry–Émery logarithmic Sobolev inequality.** For a normalized invariant diffusion measure satisfying $CD(\kappa,\infty)$ with $\kappa>0$, $C_{LS}\leq1/\kappa$. For $V(x)=|x|^2/2$ this is
  the sharp Gaussian logarithmic Sobolev inequality.

## 15. Core Banach and Hilbert space theory

Hahn–Banach, Banach–Alaoglu, uniform boundedness, open mapping, Hilbert projection, Lax–Milgram, and substantial Fredholm theory are covered. Weak compactness and reflexivity still lack several central equivalences. In 15.46 the gap is the Banach-space closed-range theorem; TauCeti already proves its Hilbert-space counterpart. Scalar $L^p$ duality is listed once in Section 04.

Sources: [mathematical synopsis](SYNOPSIS15.md); [combined coverage inventory](Mathlib15.md).

Scalars are $\mathbb R$ or $\mathbb C$ unless a statement specifies otherwise.
A **Banach space** is a complete normed vector space; a **Hilbert space** is
complete for the norm induced by an inner product. Write $B_X$ for the closed
unit ball, $X^*$ for the continuous linear dual, and $\mathcal L(X,Y)$ for
bounded linear operators with the operator norm. An **isomorphism** is a bounded
linear bijection with bounded inverse; an **isometry** preserves the norm.
Hilbert inner products are linear in the first variable.

### Hahn–Banach, separation, and duality

For $A\subset X$ let $A^\perp=\{f\in X^*:f|_A=0\}$. The canonical
map $J:X\to X^{**}$ is $(Jx)(f)=f(x)$. A real function $p$ is
**sublinear** if it is subadditive and positively homogeneous.

* **15.15. Goldstine theorem.** $J(B_X)$ is weak-star dense in $B_{X^{**}}$.
  This is a density statement about the entire ball, even when $X$ is
  nonreflexive and $J(X)$ is a proper norm-closed subspace of $X^{**}$.

### Weak topologies, compactness, and reflexivity

The **weak topology** $\sigma(X,X^*)$ is pointwise convergence against
$X^*$; the **weak-star topology** $\sigma(X^*,X)$ is pointwise convergence
on $X$. A Banach space is **reflexive** if $J$ is onto. Compactness below is
topological compactness, which must be distinguished from sequential
compactness until the relevant theorem is invoked.

* **15.26. Reflexivity and weak compactness.** A Banach space is reflexive
  exactly when $B_X$ is weakly compact. Closed subspaces and quotients of
  reflexive spaces are reflexive, and $X$ is reflexive exactly when $X^*$ is.

* **15.27. Eberlein–Šmulian theorem.** A subset of a Banach space is relatively
  weakly compact exactly when every sequence in it has a weakly convergent
  subsequence with limit in the ambient space. In particular, bounded
  sequences in reflexive spaces have weakly convergent subsequences.

* **15.28. James compactness theorem.** A Banach space is reflexive exactly
  when every $f\in X^*$ attains its norm on $B_X$. More generally,
  a closed bounded convex set is weakly compact exactly when every
  continuous real linear functional attains its supremum there.

* **15.32. Uniform convexity and reflexivity.** If for each $\varepsilon>0$
  there is $\delta>0$ such that unit-ball vectors with distance at least
  $\varepsilon$ have midpoint norm at most $1-\delta$, then $X$ is
  reflexive (Milman–Pettis). In particular, $L^p$ is reflexive for $1<p<\infty$.

### Adjoints, compactness, and the Fredholm alternative

The **Banach adjoint** is $T^*f=f\circ T$. On Hilbert spaces it corresponds
to the operator determined by $\langle Tx,y\rangle=\langle x,T^*y\rangle$.
An operator is **compact** if it maps bounded sets to relatively compact
sets; **weakly compact** uses relative weak compactness instead.

* **15.46. Closed range theorem.** For bounded maps between Banach spaces,
  $\operatorname{ran}T$ is norm closed exactly when $\operatorname{ran}T^*$
  is norm closed. In Hilbert spaces this yields
  $\operatorname{ran}T=(\ker T^*)^\perp$ and
  $\operatorname{ran}T^*=(\ker T)^\perp$ when the ranges are closed.

## 16. Locally convex spaces, duality, and distributions

Seminorm topologies, separation, elementary tensor constructions, test functions, distributions, and Schwartz Fourier operations are available. The missing bridges are full dual-pair topology, nuclearity, the structure of distributions, and kernel representation. A projective tensor seminorm or a distribution space alone does not establish any of these representation theorems.

Sources: [mathematical synopsis](SYNOPSIS16.md); [combined coverage inventory](Mathlib16.md).

A **topological vector space** has continuous addition and scalar
multiplication. It is **locally convex** if zero has a base of convex
neighborhoods. A **seminorm** is subadditive and absolutely homogeneous.
A subset $B$ is **bounded** if every zero-neighborhood absorbs it; it is
**absolutely convex** if it is convex and balanced. The continuous dual is
$E'$. Completeness refers to the natural translation-invariant uniformity;
it is not in general the same as sequential completeness.

### Separation and compatible dual topologies

A **dual pair** $(E,F)$ is a bilinear pairing separating both spaces. Write
$\sigma(E,F)$ for pointwise convergence on $F$, $\beta(E,F)$ for uniform
convergence on $\sigma(F,E)$-bounded sets, and $\tau(E,F)$ for uniform
convergence on absolutely convex $\sigma(F,E)$-compact sets. For $A\subset E$,
$A^\circ=\{f\in F:|\langle a,f\rangle|\leq1\ (a\in A)\}$.

* **16.13. Bipolar theorem for dual pairs.** $A^{\circ\circ}$ is the
  $\sigma(E,F)$-closed absolutely convex hull of $A\cup\{0\}$. In particular,
  absolutely convex weakly closed sets are recovered exactly from their polars.

* **16.15. Mackey–Arens theorem.** The locally convex topologies on $E$ whose
  continuous dual is exactly $F$ are precisely those between
  $\sigma(E,F)$ and $\tau(E,F)$. In particular, $\tau(E,F)$ is the
  strongest topology compatible with the dual pair.

### Tensor products and nuclear spaces

For Banach spaces, the **projective norm** is
$\pi(u)=\inf\sum_j\|x_j\|\|y_j\|$ over $u=\sum_jx_j\otimes y_j$;
the **injective norm** is
$\varepsilon(u)=\sup_{f\in B_{X^*},g\in B_{Y^*}}|(f\otimes g)(u)|$.
Locally convex projective and injective tensor topologies are defined by the
corresponding seminorms. A continuous map to a Banach space is **nuclear**
if it has a representation $Tx=\sum_j\lambda_j f_j(x)y_j$ with
$\sum_j|\lambda_j|<\infty$, equicontinuous $(f_j)$, and bounded $(y_j)$.
A locally convex space is nuclear if all its continuous maps into Banach
spaces are nuclear.

* **16.31. Nuclear tensor characterization.** $E$ is nuclear exactly when,
  for every locally convex $F$, the projective and injective topologies on
  $E\otimes F$ coincide.

* **16.33. Nuclear Fréchet compactness.** Every nuclear Fréchet space is
  Montel, and hence reflexive; its bounded sets are relatively compact.
  This explains compactness properties of smooth-function spaces that
  cannot hold in infinite-dimensional Banach spaces.

### Test functions and the local structure of distributions

For open $\Omega\subset\mathbb R^n$, let
$\mathcal E(\Omega)=C^\infty(\Omega)$ with uniform convergence of all
derivatives on compact sets. Let $\mathcal D_K$ consist of smooth functions
supported in compact $K\Subset\Omega$, with seminorms
$\max_{|\alpha|\leq m}\|\partial^\alpha\phi\|_\infty$;
$\mathcal D(\Omega)=C_c^\infty(\Omega)$ has its strict inductive limit
topology over a compact exhaustion. A **distribution** is an element of
$\mathcal D'(\Omega)$, acting linearly, without complex conjugation, on
test functions. The **support** is the complement of the largest open set
where it vanishes.

* **16.42. Distributions supported at a point.** If $\operatorname{supp}T
  \subset\{a\}$, then $T=\sum_{|\alpha|\leq m}c_\alpha\partial^\alpha\delta_a$
  for finitely many coefficients. Thus point-supported singularities have
  no further distributional forms.

* **16.43. Local structure theorem.** On each relatively compact open subset,
  every distribution is a finite sum of distributional derivatives of
  continuous functions. Its singularity can therefore be measured by the
  number of derivatives needed, rather than pointwise growth alone.

### Differentiation, regularization, and convolution

Set $(\partial^\alpha T)(\phi)=(-1)^{|\alpha|}T(\partial^\alpha\phi)$
and $(aT)(\phi)=T(a\phi)$ for smooth $a$. A **mollifier** is
$\rho\in C_c^\infty(\mathbb R^n)$ with integral one, with
$\rho_\varepsilon(x)=\varepsilon^{-n}\rho(x/\varepsilon)$.

* **16.51. Schwartz kernel theorem.** Every continuous linear map
  $A:\mathcal D(\Lambda)\to\mathcal D'(\Omega)$ has a unique
  $K\in\mathcal D'(\Omega\times\Lambda)$ such that
  $(A\psi)(\phi)=K(\phi\otimes\psi)$. Conversely every such kernel
  defines a continuous map. Differential operators and the identity have
  kernels supported on the diagonal.

### Tempered distributions and Fourier transforms

The **Schwartz space** $\mathcal S$ consists of smooth functions with
$\sup_x|x^\alpha\partial^\beta f(x)|<\infty$ for every pair of
multiindices. Its continuous dual $\mathcal S'$ consists of **tempered
distributions**. Use $\widehat f(\xi)=\int e^{-ix\cdot\xi}f(x)\,dx$;
thus $f(x)=(2\pi)^{-n}\int e^{ix\cdot\xi}\widehat f(\xi)\,d\xi$.
On distributions, $\widehat T(\phi)=T(\widehat\phi)$.

* **16.58. Paley–Wiener–Schwartz theorem.** For compact convex
  $K\subset\mathbb R^n$, Fourier transforms of distributions supported in
  $K$ are exactly the entire functions $F$ on $\mathbb C^n$ satisfying
  $$|F(z)|\leq C(1+|z|)^N e^{H_K(\operatorname{Im}z)},
    \qquad H_K(\eta)=\sup_{x\in K}x\cdot\eta,$$
  for some $C,N$. The distribution is unique.

### Fundamental solutions and elementary regularity

A **fundamental solution** for $P(\partial)$ is a distribution $E$ with
$P(\partial)E=\delta_0$. An operator is **hypoelliptic** if smoothness of
$Pu$ on an open subset implies smoothness of $u$ there.

* **16.62. Malgrange–Ehrenpreis theorem.** Every nonzero constant-coefficient
  linear differential operator on $\mathbb R^n$ has a distributional
  fundamental solution. The solution need not be tempered.

## 17. Banach space geometry, bases, and operator ideals

Schauder and unconditional bases, complemented subspaces, and elementary normed-space constructions are covered. The major gaps lie in weak-sequence structure, the approximation property, type and cotype, local Euclidean geometry, renorming, and summing operators. The results selected here connect those subjects rather than enumerate every classical Banach-space example.

Sources: [mathematical synopsis](SYNOPSIS17.md); [combined coverage inventory](Mathlib17.md).

Write $[x_n]$ for the closed linear span of a sequence. A **Schauder basis**
$(e_n)$ gives a unique norm-convergent expansion
$x=\sum_ne_n^*(x)e_n$ for every $x$; a **basic sequence** is a basis for
its own closed span. Two basic sequences are **equivalent** if the map
taking corresponding vectors to each other extends to an isomorphism of
their spans. Equivalent norms preserve the Banach space isomorphism class,
but can change its metric geometry considerably.

### Bases, block sequences, and duality

The partial-sum projections are $P_nx=\sum_{j\leq n}e_j^*(x)e_j$.
A **block sequence** has vectors supported on successive disjoint finite
intervals of a basis. A basis is **unconditional** if every expansion
converges under every permutation, and **shrinking** if $(e_n^*)$ is a
basis of $X^*$. It is **boundedly complete** if bounded partial sums
$\sum_{j\leq n}a_je_j$ always converge.

* **17.10. James basis theorem.** A Banach space with a Schauder basis is
  reflexive exactly when the basis is both shrinking and boundedly complete.

### Weak sequences and unconditional series

A series $\sum x_n$ is **weakly unconditionally Cauchy** if
$\sum_n|f(x_n)|<\infty$ for every $f\in X^*$. A sequence is **weakly
Cauchy** if every scalar sequence $f(x_n)$ is Cauchy. These conditions do
not themselves assert convergence to a vector of $X$.

* **17.21. Rosenthal $\ell^1$ theorem.** Every bounded sequence in a Banach
  space has either a weakly Cauchy subsequence or a subsequence equivalent
  to the standard basis of $\ell^1$.

* **17.22. Dunford–Pettis compactness in $L^1$.** On a finite measure space,
  a bounded subset of $L^1$ is relatively weakly compact exactly when it is
  uniformly integrable. The result separates weak compactness from norm
  compactness in this nonreflexive space.

### Classical subspaces, quotients, and complemented copies

* **17.29. Enflo approximation counterexample.** There exist separable Banach
  spaces without the approximation property, hence without a Schauder basis.
  Not every compact operator between Banach spaces is a norm limit of
  finite-rank operators.

### Local geometry, random sums, and finite representability

Let $(r_j)$ be independent symmetric signs. $X$ has **type $p$**,
$1\leq p\leq2$, if
$(\mathbb E\|\sum r_jx_j\|^2)^{1/2}\leq T(\sum\|x_j\|^p)^{1/p}$;
it has **cotype $q$**, $2\leq q<\infty$, if
$(\sum\|x_j\|^q)^{1/q}\leq C(\mathbb E\|\sum r_jx_j\|^2)^{1/2}$.
The **Banach–Mazur distance** between finite-dimensional isomorphic spaces
is $d(X,Y)=\inf_T\|T\|\|T^{-1}\|$. $Y$ is **finitely representable**
in $X$ if each finite-dimensional subspace of $Y$ embeds into $X$ with
distortion at most $1+\varepsilon$, for every $\varepsilon>0$.

* **17.34. Kwapień theorem.** A Banach space is isomorphic to a Hilbert space
  exactly when it has both type two and cotype two.

* **17.35. Dvoretzky theorem.** Every infinite-dimensional Banach space
  contains, for every $n$ and $\varepsilon>0$, an $n$-dimensional subspace
  with Banach–Mazur distance at most $1+\varepsilon$ from $\ell_2^n$.
  Equivalently, $\ell^2$ is finitely representable in every such space.

### Convexity, smoothness, and Radon–Nikodým geometry

The **modulus of convexity** is
$\delta_X(\varepsilon)=\inf\{1-\|(x+y)/2\|:x,y\in B_X,
\|x-y\|\geq\varepsilon\}$. The **modulus of smoothness** is
$\rho_X(t)=\sup_{\|x\|=\|y\|=1}(\|x+ty\|+\|x-ty\|)/2-1$.
Uniform convexity means $\delta_X(\varepsilon)>0$ for $\varepsilon>0$;
uniform smoothness means $\rho_X(t)/t\to0$. A space is **superreflexive**
if every Banach space finitely representable in it is reflexive.

The **Radon–Nikodým property** means that every countably additive
$X$-valued measure of bounded variation, absolutely continuous with respect
to a finite positive measure, has a Bochner integrable density.

* **17.42. Superreflexive renorming theorem.** A Banach space is superreflexive
  exactly when it admits an equivalent uniformly convex norm, and exactly
  when it admits an equivalent uniformly smooth norm.

### Summing operators, tensor norms, and approximation

The **approximation property** means that the identity can be approximated
uniformly on each compact subset by finite-rank operators. The **bounded
approximation property** requires such operators with a common operator-norm
bound.

An operator $T:X\to Y$ is **absolutely $p$-summing**, $1\leq p<\infty$,
if the least constant $\pi_p(T)$ in
$$\Big(\sum_j\|Tx_j\|^p\Big)^{1/p}
 \leq\pi_p(T)\sup_{f\in B_{X^*}}
                  \Big(\sum_j|f(x_j)|^p\Big)^{1/p}$$
is finite. An **operator ideal** is stable under addition and composition
on either side by bounded maps. A **nuclear operator** has a representation
$Tx=\sum_j f_j(x)y_j$ with $\sum_j\|f_j\|\|y_j\|<\infty$.

* **17.50. Pietsch domination theorem.** $T$ is $p$-summing exactly when
  some regular Borel probability measure $\mu$ on weak-star compact
  $B_{X^*}$ satisfies
  $$\|Tx\|\leq C\left(\int_{B_{X^*}}|f(x)|^p\,d\mu(f)\right)^{1/p}.$$
  The optimal domination constant equals $\pi_p(T)$.

* **17.53. Grothendieck inequality.** There is a scalar-field-dependent
  universal $K_G$ such that for every finite scalar matrix $(a_{ij})$ and
  unit vectors $u_i,v_j$ in a Hilbert space,
  $$\left|\sum_{i,j}a_{ij}\langle u_i,v_j\rangle\right|
    \leq K_G\sup_{|s_i|,|t_j|\leq1}
                 \left|\sum_{i,j}a_{ij}s_it_j\right|.$$

## 18. Vector-valued analysis and analysis in Banach spaces

Bochner integration, measurability, dominated convergence, and Banach-valued smoothing are covered. The missing core is geometric vector-valued analysis: duality and Radon–Nikodým phenomena, UMD spaces, operator-valued multipliers, Gaussian radonification, and maximal regularity. The vector-measure density theorem below requires substantive geometric hypotheses on its target space.

Sources: [mathematical synopsis](SYNOPSIS18.md); [combined coverage inventory](Mathlib18.md).

For a complete measure space $(S,\Sigma,\mu)$, a function $f:S\to X$ is
**strongly measurable** if it is an almost-everywhere limit of measurable
simple functions, and **weakly measurable** if $x^*f$ is measurable for every
$x^*\in X^*$. The Bochner space $L^p(S;X)$ uses the norm
$(\int\|f\|^p)^{1/p}$, with the usual essential-supremum modification.
Probability filtrations are increasing unless stated otherwise.

### Bochner integration, duality, and differentiation

* **18.5. Vector-valued Hölder duality.** Integration gives an isometric
  embedding $L^{p'}(S;X^*)\hookrightarrow L^p(S;X)^*$ for $1\leq p<\infty$
  on a $\sigma$-finite space. It is onto if $X^*$ has the Radon–Nikodým
  property; conversely, surjectivity on $[0,1]$ characterizes that property.

### Vector measures and the Radon–Nikodým property

A countably additive $X$-valued measure $\nu$ has **bounded variation** if
$|\nu|(S)=\sup\sum_j\|\nu(A_j)\|<\infty$, over finite measurable
partitions. $X$ has the **Radon–Nikodým property** (RNP) if every such
measure absolutely continuous with respect to a finite positive measure
has a Bochner integrable density.

* **18.10. Vector Radon–Nikodým theorem.** Every reflexive Banach space has RNP. In particular, in a reflexive space, or more generally an RNP space, $\nu\ll\mu$
  of bounded variation has a unique density $f\in L^1(\mu;X)$, with
  $\nu(A)=\int_A f\,d\mu$ and $|\nu|(A)=\int_A\|f\|\,d\mu$.

* **18.13. Martingale characterization of RNP.** $X$ has RNP exactly when
  every uniformly integrable $X$-valued martingale converges in $L^1$ and
  almost surely in norm. It is enough to test the dyadic filtration on
  $[0,1]$.

### Fourier analysis and randomized Littlewood–Paley theory

Use $\widehat f(\xi)=\int e^{-ix\cdot\xi}f(x)\,dx$ on Bochner
integrable functions. For a symbol $m(\xi)\in\mathcal L(X,Y)$, a
**Fourier multiplier** is the extension of
$T_mf=\mathcal F^{-1}(m\widehat f)$ to the indicated $L^p$ spaces.

A Banach space $X$ is **UMD** if, for one (equivalently every) $1<p<\infty$, all finite $X$-valued martingale-difference sequences satisfy
$\|\sum_j\varepsilon_jd_j\|_{L^p(X)}\leq C\|\sum_jd_j\|_{L^p(X)}$
uniformly over signs $\varepsilon_j\in\{-1,1\}$.
A family $\mathcal T\subset\mathcal L(X,Y)$ is **R-bounded** if
$\bigl(\mathbb E\|\sum_jr_jT_jx_j\|^2\bigr)^{1/2}\leq C\bigl(\mathbb E\|\sum_jr_jx_j\|^2\bigr)^{1/2}$
for all finite choices $T_j\in\mathcal T$, $x_j\in X$, with independent Rademacher signs $r_j$.

* **18.33. Hilbert transform characterization.** $X$ is UMD exactly when
  $Hf(x)=\operatorname{p.v.}\,\pi^{-1}\int f(x-y)/y\,dy$ is bounded on
  $L^p(\mathbb R;X)$ for one, hence every, $1<p<\infty$.

* **18.36. Operator-valued Mihlin theorem on the line.** If $X,Y$ are UMD,
  $m\in C^1(\mathbb R\setminus\{0\};\mathcal L(X,Y))$, and
  $\{m(\xi),\xi m'(\xi):\xi\ne0\}$ is R-bounded, then $T_m$ is bounded
  from $L^p(\mathbb R;X)$ to $L^p(\mathbb R;Y)$ for $1<p<\infty$.

### Gaussian radonifying operators and stochastic integration

For real Hilbert $H$, the space $\gamma(H,X)$ is the completion of
finite-rank maps in the norm
$\|T\|_\gamma^2=\mathbb E\|\sum_j\gamma_jTh_j\|^2$, with $(h_j)$
orthonormal on their finite-dimensional support. These are the
**$\gamma$-radonifying operators**. Complex spaces may be regarded as real
for this construction. A cylindrical Brownian motion $W_H$ has independent
scalar Brownian coordinates along an orthonormal basis of $H$.

For a function $\phi:S\to X$, its radonifying function norm means the
norm of the integral operator $R_\phi g=\int_Sg(s)\phi(s)\,d\mu(s)$
from $L^2(S)$ to $X$, initially interpreted by scalar duality when needed.
For operator-valued $\Phi$, similarly
$R_\Phi g=\int_0^T\Phi(t)g(t)\,dt$ on $L^2(0,T;H)$.

* **18.42. Basis independence and Gaussian realization.** The radonifying
  norm is independent of the orthonormal basis. For separable $H$, a bounded
  $T:H\to X$ is radonifying exactly when $\sum_j\gamma_jTh_j$ converges
  in $L^2(\Omega;X)$; the sum realizes a Radon Gaussian variable with
  covariance $TT^*$.

* **18.50. UMD Itô isomorphism.** For adapted elementary $\Phi$ in a UMD
  space and $1<p<\infty$,
  $$\mathbb E\sup_{t\leq T}\left\|\int_0^t\Phi\,dW_H\right\|^p
       \asymp_{p,X}\mathbb E\|R_\Phi\|_{\gamma(L^2(0,T;H),X)}^p.$$
  Completion gives the stochastic integral for limits in this norm
  ([van Neerven–Veraar–Weis, Theorem 5.5](https://arxiv.org/abs/1304.7575)).

### Laplace transforms, functional calculus, and maximal regularity

For an exponentially bounded function, its **Laplace transform** is
$\mathcal Lf(\lambda)=\int_0^\infty e^{-\lambda t}f(t)\,dt$ on a right
half-plane. A densely defined closed operator $A$ is **sectorial** of
angle $\omega<\pi$ if its spectrum lies in $\overline{\Sigma_\omega}$,
$\Sigma_\theta=\{z\ne0:|\arg z|<\theta\}$, and
$\lambda(\lambda-A)^{-1}$ is uniformly bounded outside every larger sector.
Replacing these bounds by R-bounds defines **R-sectoriality**.

**Maximal $L^p$ regularity** for $A$ means that $u'+Au=f$, $u(0)=0$, has a unique solution with $u',Au\in L^p(0,T;X)$ and $\|u'\|_p+\|Au\|_p\leq C_T\|f\|_p$. The characterization below uses a densely defined closed sectorial $A$, with $-A$ generating a bounded analytic semigroup, and regularity on $\mathbb R_+$, equivalently the estimates above uniformly over finite $T$.

* **18.57. Weis characterization.** On a UMD space, maximal $L^p$ regularity
  is equivalent to R-sectoriality with angle below $\pi/2$; it is then
  independent of $p\in(1,\infty)$
  ([Kunstmann–Weis, Theorem 1.11](https://www.karlin.mff.cuni.cz/~barta/ToDownload/Kunstmann-Weis2004.pdf)).

## 19. Banach lattices, positive operators, and ordered structures

Ordered-vector-space identities and solid lattice norms are present, with a small positive Koopman-operator construction. The absent body is the representation and operator theory of Banach lattices: bands, regular operators, AM/AL representations, and positive spectral structure. Matrix Perron–Frobenius is a finite-dimensional predecessor of the Krein–Rutman statements selected here.

Sources: [mathematical synopsis](SYNOPSIS19.md); [combined coverage inventory](Mathlib19.md).

A **vector lattice**, or **Riesz space**, is an ordered vector space in
which each pair has a supremum $x\vee y$ and infimum $x\wedge y$.
Write $x^+=x\vee0$, $x^-=(-x)\vee0$, and $|x|=x\vee(-x)$.
Vectors are **disjoint**, $x\perp y$, if $|x|\wedge|y|=0$.
A **Banach lattice** is a vector lattice with a complete norm satisfying
$|x|\leq|y|\Rightarrow\|x\|\leq\|y\|$. Its positive cone $E_+$ is
closed and generates $E$.

### Lattice structure, ideals, and bands

An **ideal** is a linear subspace $I$ such that $|x|\leq|y|$, $y\in I$,
implies $x\in I$. A **band** is an ideal closed under suprema of its
positive subsets whenever those suprema exist in the ambient space.
The disjoint complement is $A^d=\{x:x\perp a\text{ for all }a\in A\}$.
The space is **Archimedean** if $nx\leq y$ for all positive integers $n$
implies $x\leq0$, and **Dedekind complete** if every nonempty order-bounded
above subset has a supremum.

* **19.5. Band projections.** In a Dedekind complete vector lattice,
  every band $B$ gives $E=B\oplus B^d$. Its projection satisfies
  $0\leq P_B\leq I$ and
  $P_Bx=\sup\{y\in B:0\leq y\leq x\}$ for $x\geq0$.

* **19.8. Freudenthal spectral theorem.** In a Dedekind complete vector
  lattice, an element of the principal ideal generated by $u\geq0$ can
  be approximated uniformly in the order-unit norm by finite linear
  combinations of pairwise disjoint components of $u$.

### Norms, order continuity, and monotone completeness

The **principal ideal** $E_u=\{x:|x|\leq cu\text{ for some }c\}$ has
order-unit norm $\|x\|_u=\inf\{c:|x|\leq cu\}$. A positive $u$ is a
**strong unit** if $E_u=E$, and a **quasi-interior point** if $E_u$ is
norm dense. The norm is **order continuous** if
$x_\alpha\downarrow0\Rightarrow\|x_\alpha\|\to0$, for nets.
A **KB space** is a Banach lattice in which every increasing norm-bounded
positive sequence converges in norm.

* **19.15. Reflexivity criterion.** $E$ is reflexive exactly when both $E$
  and $E^*$ are KB spaces. Equivalently, $E$ contains neither $c_0$ nor
  $\ell^1$ as a lattice-isomorphic closed sublattice (Lozanovsky).

### Order duality and positive operators

A linear operator is **positive** if $T(E_+)\subset F_+$, **regular** if
it is a difference of positive operators, and **order bounded** if it maps
order-bounded sets to order-bounded sets. The **order dual** $E^\sim$
consists of order-bounded scalar functionals. An operator is **order
continuous** if it preserves decreasing nets with infimum zero.

* **19.20. Riesz–Kantorovich theorem.** If $F$ is Dedekind complete, the
  order-bounded maps $E\to F$ form a Dedekind complete vector lattice
  and are exactly the regular maps. For $x\geq0$,
  $$(S\vee T)x=\sup_{0\leq y\leq x}\{Sy+T(x-y)\},
    \qquad |T|x=\sup_{|y|\leq x}|Ty|.$$

### Representation and lattice functional calculus

An **AM space** satisfies $\|x\vee y\|=\max(\|x\|,\|y\|)$ for
$x,y\geq0$; an **AL space** satisfies
$\|x+y\|=\|x\|+\|y\|$ for $x,y\geq0$. An AM space **with unit**
has an element $e$ whose order interval $[-e,e]$ is its unit ball.

* **19.27. Kakutani representation of AM spaces with unit.** Every AM space
  with unit is lattice isometric to $C(K)$ for a compact Hausdorff $K$,
  taking its unit to the constant one. Conversely every such $C(K)$ is
  an AM space with unit.

* **19.29. Kakutani representation of AL spaces.** Every AL space is lattice
  isometric to an $L^1$ space for a suitable measure space. AL spaces
  are KB spaces and have order continuous norm.

### Positive spectra and Perron–Frobenius theory

A positive operator is **ideal irreducible** if it leaves no nonzero proper
closed ideal invariant. It is **strongly positive** when the cone has
nonempty interior and it maps each nonzero positive vector into that interior.
For these statements $E$ is nonzero and spectra are taken in its
complexification.

* **19.47. Krein–Rutman existence theorem.** If $T$ is compact positive and
  $r(T)>0$, then $r(T)$ is an eigenvalue of both $T$ and $T^*$ with
  nonzero positive eigenvectors. Compactness alone does not guarantee
  $r(T)>0$.

* **19.48. Strong positivity and a spectral gap.** If $T$ is compact and
  strongly positive on a Banach lattice with solid cone, then $r(T)>0$
  is algebraically simple, its eigenvector is interior, and every other
  spectral value has modulus strictly less than $r(T)$.

## 20. Banach algebras and commutative harmonic analysis of algebras

Spectrum, spectral radius, characters, the Gelfand transform, continuous functional calculus in the C*-setting, and local exponential/logarithm identities are covered. The missing analytic extensions include general holomorphic calculus, Tauberian inversion, boundaries of uniform algebras, and Banach-algebra amenability. General locally compact group duality is selected in Section 28.

Sources: [mathematical synopsis](SYNOPSIS20.md); [combined coverage inventory](Mathlib20.md).

A **Banach algebra** is a complex Banach space with associative bilinear
multiplication satisfying $\|ab\|\leq\|a\|\|b\|$. Identities, when present,
are normalized to have norm one. For a nonunital algebra use the
**unitization** $A^\#=A\oplus\mathbb C1$, with the usual product and
sum norm. Spectra of nonunital elements are taken in this unitization.
Write $A^{-1}$ for the invertible group of a unital algebra and
$\sigma_A(a)=\{\lambda:\lambda1-a\notin A^{-1}\}$.
A **C*-algebra** has a conjugate-linear involution $a\mapsto a^*$ with
$(ab)^*=b^*a^*$ and $\|a^*a\|=\|a\|^2$.

### Invertibility, spectra, and holomorphic calculus

* **20.7. Holomorphic functional calculus.** A function holomorphic on a
  neighborhood of $\sigma(a)$ defines
  $f(a)=(2\pi i)^{-1}\int_\Gamma f(z)(z1-a)^{-1}\,dz$.
  This is independent of admissible contours, is a unital algebra
  homomorphism in $f$, and satisfies $\sigma(f(a))=f(\sigma(a))$.

### Characters and the Gelfand representation

A **character** is a nonzero multiplicative complex linear functional.
The **character space** $\Delta(A)$ has the weak-star topology, and
$\widehat a(\varphi)=\varphi(a)$ is the **Gelfand transform**.
An algebra is **semisimple** if its Jacobson radical is zero. The next
statements assume commutativity unless indicated otherwise.

* **20.18. Gleason–Kahane–Żelazko theorem.** If a complex linear functional
  $F$ on a unital Banach algebra satisfies $F(1)=1$ and never vanishes
  on invertible elements, then it is multiplicative. Neither continuity
  nor commutativity need be assumed.

### Uniform algebras, boundaries, and representing measures

A **uniform algebra** on compact Hausdorff $K$ is a closed subalgebra
$A\subset C(K)$ containing constants and separating points. It is
**natural** if every character is evaluation at a point of $K$.
A closed **boundary** $F\subset K$ satisfies
$\|f\|_K=\max_F|f|$ for all $f\in A$; the smallest such boundary
is the **Shilov boundary**.

* **20.22. Shilov boundary theorem.** Every uniform algebra has a smallest
  closed boundary. Restricting to that boundary is an isometric algebra
  embedding, though the character space can be larger than the boundary.

### Convolution algebras and Fourier transforms

Let $G$ be a locally compact group with left Haar measure. The group algebra
$L^1(G)$ has convolution
$(f*g)(x)=\int f(y)g(y^{-1}x)\,dy$; $M(G)$ is the algebra of finite
regular measures with convolution and identity $\delta_e$. When $G$ is
abelian, its dual group $\widehat G$ consists of continuous unitary
characters, and $\widehat f(\gamma)=\int f(x)\overline{\gamma(x)}\,dx$.

* **20.38. Wiener lemma.** If $f\in C(\mathbb T)$ has an absolutely
  convergent Fourier series and no zeros on $\mathbb T$, then $1/f$ also
  has an absolutely convergent Fourier series. More generally a holomorphic
  function of $f$ near its range belongs to the same Wiener algebra.

* **20.39. Wiener Tauberian theorem.** For abelian $G$ and $f\in L^1(G)$,
  the closed span of the translates of $f$ is all of $L^1(G)$ exactly
  when $\widehat f$ has no zero on $\widehat G$. Equivalently, the
  closed convolution ideal generated by $f$ is the entire algebra.

### Approximate identities, modules, and derivations

A **bounded approximate identity** is a bounded net $(e_\alpha)$ with
$e_\alpha a\to a$ and $ae_\alpha\to a$. A left Banach $A$-module $X$
is **essential** if $\overline{AX}=X$. A bounded **derivation** into a
bimodule satisfies $D(ab)=a\cdot D(b)+D(a)\cdot b$; it is **inner**
if $D(a)=a\cdot x-x\cdot a$ for some fixed $x$.

* **20.45. Cohen–Hewitt factorization.** If $A$ has a bounded left
  approximate identity and $X$ is an essential left Banach module, then
  each $x\in X$ has the form $x=ay$ with $a\in A$, $y\in X$.
  In particular $A=A^2$ when $A$ has a bounded approximate identity.

### Amenability and its harmonic-analytic characterizations

A Banach algebra $A$ is **amenable** if every bounded derivation into
every dual Banach bimodule is inner. A locally compact group is
**amenable** if $L^\infty(G)$ admits a positive normalized left-invariant
mean. These are different definitions connected by a theorem below.
The projective tensor product $A\widehat\otimes_\pi A$ carries the
outer bimodule actions, and $m(a\otimes b)=ab$.

* **20.55. Johnson group algebra theorem.** For every locally compact group
  $G$, the Banach algebra $L^1(G)$ is amenable exactly when $G$ is amenable.
  All abelian and compact groups are amenable; the discrete free group
  on two generators is not.

## 21. Bounded operator theory, spectra, and functional models

Adjoints, compact self-adjoint spectral theory, abstract Fredholmness, compact-perturbation invariance, and local constancy of index are covered. The selected omissions concern essential spectrum, trace ideals, dilation, and contraction models. The bounded normal spectral-measure theorem is included here; 22.9 gives the unbounded self-adjoint theorem with its domain characterization.

Sources: [mathematical synopsis](SYNOPSIS21.md); [combined coverage inventory](Mathlib21.md).

Unless indicated otherwise, $H$ is a nonzero complex Hilbert space,
$\mathcal B(H)$ denotes its bounded operators, and inner products are linear
in the first variable. The **spectrum** is
$\sigma(T)=\{z:zI-T\text{ is not invertible}\}$, the **resolvent** is
$R(z,T)=(zI-T)^{-1}$, and $r(T)=\max_{z\in\sigma(T)}|z|$.
A subspace is **invariant** if $TM\subset M$, and **reducing** if it is
invariant for both $T$ and $T^*$.

### Spectral measures of bounded normal operators

A bounded operator is **normal** if $T^*T=TT^*$. A projection-valued measure here is defined on Borel subsets of $\sigma(T)\subset\mathbb C$, is countably additive in the strong operator topology, and has total mass $I$.

* **21.6. Normal spectral theorem.** A normal $T$ has a projection-valued
  measure $E$ with $T=\int z\,dE(z)$, and bounded Borel functions define
  $f(T)=\int f\,dE$. In particular
  $\|R(z,T)\|=\operatorname{dist}(z,\sigma(T))^{-1}$ off the spectrum.

### Fredholm operators and essential spectra

A bounded map $T:X\to Y$ between Banach spaces is **Fredholm** if its
range is closed and both $\ker T$ and $Y/\operatorname{ran}T$ are finite
dimensional. Its **index** is
$\operatorname{ind}T=\dim\ker T-\dim(Y/\operatorname{ran}T)$.
The **Calkin algebra** is $\mathcal B(H)/\mathcal K(H)$, where
$\mathcal K(H)$ is the compact ideal; the **essential spectrum** here means
$\sigma_{\rm ess}(T)=\{z:T-zI\text{ is not Fredholm}\}$.

* **21.9. Atkinson theorem.** $T$ is Fredholm exactly when it has a bounded
  inverse modulo compact operators. For endomorphisms this says that its
  image in the Calkin algebra is invertible.

* **21.13. Analytic Fredholm theorem.** If $K(z)$ is a norm-holomorphic
  compact-operator family on a connected plane domain, then either
  $I-K(z)$ is nowhere invertible or its inverse is meromorphic, with
  discrete poles and finite-rank principal parts.

* **21.14. Essential spectral invariance.** Compact perturbations preserve
  $\sigma_{\rm ess}$. For bounded self-adjoint $T$, the complement of
  its essential spectrum in its spectrum consists exactly of isolated
  eigenvalues of finite multiplicity.

### Compact operators, singular values, and trace ideals

For compact $T$, the **singular values** $s_n(T)$ are the eigenvalues of
$|T|$ in decreasing order, repeated by multiplicity and padded by zeros.
The **Schatten class** $S^p$ has $\sum_ns_n(T)^p<\infty$,
$1\leq p<\infty$. $S^2$ and $S^1$ are the Hilbert–Schmidt and trace
classes, respectively.

* **21.17. Singular value approximation.**
  $s_n(T)=\inf_{\operatorname{rank}F<n}\|T-F\|$. Singular value
  decompositions therefore give optimal finite-rank approximation in
  operator norm.

* **21.18. Ideal inequalities.** $\|ATB\|_p\leq\|A\|\|T\|_p\|B\|$,
  and Schatten Hölder gives $\|ST\|_r\leq\|S\|_p\|T\|_q$ when
  $1/r=1/p+1/q$ and $p,q,r\geq1$. In particular, products of two
  Hilbert–Schmidt maps are trace class.

* **21.19. Trace and cyclicity.** For $T\in S^1$,
  $\operatorname{tr}T=\sum_j\langle Te_j,e_j\rangle$ is absolutely
  convergent and basis independent. If $A$ is bounded,
  $\operatorname{tr}(AT)=\operatorname{tr}(TA)$ and
  $|\operatorname{tr}T|\leq\|T\|_1$.

### Isometries, contractions, and functional models

The unilateral shift on $H^2(E)$ is $Sf(z)=zf(z)$, where $H^2(E)$
consists of analytic $E$-valued functions with square-summable Taylor
coefficients. A contraction is **completely nonunitary** if it has no
nonzero reducing subspace on which it is unitary. Its defect operators and
spaces are $D_T=(I-T^*T)^{1/2}$ and
$\mathcal D_T=\overline{\operatorname{ran}D_T}$.

* **21.21. Wold decomposition.** Every isometry is the orthogonal sum of
  a unitary operator and a unilateral shift. The shift multiplicity is
  $\dim\ker V^*$; its shift part is
  $\bigoplus_{n\geq0}V^n\ker V^*$.

* **21.25. Unitary dilation theorem.** Every contraction has a unitary power
  dilation $U$ with $T^n=P_HU^n|_H$ for $n\geq0$, unique under
  $K=\overline{\operatorname{span}}\{U^nH:n\in\mathbb Z\}$.

* **21.29. Characteristic function.** The analytic contractive function
  $$\Theta_T(z)=\left[-T+zD_{T^*}(I-zT^*)^{-1}D_T\right]|_{\mathcal D_T}
      :\mathcal D_T\to\mathcal D_{T^*}$$
  is a complete unitary invariant for completely nonunitary contractions,
  up to constant unitary identifications of the two defect spaces.

* **21.32. Commutant lifting.** If $X$ commutes with a contraction $T$,
  it lifts to an operator $Y$ commuting with the minimal isometric dilation
  $V$, with $P_HY|_H=X$ and $\|Y\|=\|X\|$.

## 22. Unbounded operators, spectral theory, and mathematical physics

Closed operators and resolvents, nonreal resolvent estimates, and Stone’s theorem are available. TauCeti supplies a Dirichlet eigenbasis through a compact variational inverse on bounded domains. The major omissions are the general unbounded spectral theorem, form representation and extensions, perturbation, Schrödinger realizations, Sturm–Liouville theory, and scattering. The full min–max principle below is stronger than the implemented first-eigenvalue Rayleigh formula.

Sources: [mathematical synopsis](SYNOPSIS22.md); [combined coverage inventory](Mathlib22.md).

Throughout, $H$ is a complex Hilbert space with inner product linear in
the first variable. An **unbounded operator** includes its linear domain
$D(A)\subset H$. It is **closed** if its graph is closed, **closable** if
its graph closure is a graph, **symmetric** if
$\langle Au,v\rangle=\langle u,Av\rangle$ on $D(A)$, and
**self-adjoint** if $A=A^*$ including equality of domains. A **core** is
a subspace dense in $D(A)$ for the graph norm $\|u\|+\|Au\|$.

### Adjoints, extensions, and unitary dynamics

* **22.5. von Neumann extension theorem.** A closed densely defined symmetric
  $A$ has self-adjoint extensions exactly when its deficiency indices
  $n_\pm=\dim\ker(A^*\mp i)$ agree. Its self-adjoint extensions are
  parametrized by unitaries between the two deficiency spaces.

### Spectral measures and functional calculus

A **projection-valued measure** $E$ is countably additive in the strong
operator topology, with orthogonal projections as values and $E(\mathbb R)=I$.
Set $\mu_u(B)=\langle E(B)u,u\rangle$. The scalar spectral measures
decompose into atomic, absolutely continuous, and singular continuous parts.

* **22.9. Unbounded spectral theorem.** Every self-adjoint operator has a
  unique representation
  $$A=\int_{\mathbb R}\lambda\,dE(\lambda),\qquad
    D(A)=\left\{u:\int\lambda^2\,d\mu_u(\lambda)<\infty\right\}.$$
  The support of $E$ is $\sigma(A)\subset\mathbb R$.

### Closed quadratic forms and self-adjoint realizations

A densely defined symmetric form $q$ is **lower semibounded** if
$q[u]\geq-c\|u\|^2$. It is **closed** if its domain $Q(q)$ is complete
for $(q[u]+(c+1)\|u\|^2)^{1/2}$, and **closable** if it has a closed
extension obtained by completing its graph in this form norm.

* **22.19. First representation theorem.** Every densely defined closed
  lower-semibounded form determines a unique self-adjoint lower-semibounded
  $A$ with $D(A)\subset Q(q)$ and $q(u,v)=\langle Au,v\rangle$
  for $u\in D(A)$, $v\in Q(q)$.

* **22.21. Friedrichs extension.** Every densely defined lower-semibounded
  symmetric operator has a canonical self-adjoint extension obtained by
  closing its quadratic form. Its form domain is the completion of the
  original domain in the form norm.

* **22.22. KLMN theorem.** If $q\geq0$ is closed and a symmetric form $b$
  on $Q(q)$ satisfies $|b[u]|\leq a q[u]+c\|u\|^2$ with $a<1$,
  then $q+b$ is closed and lower semibounded on the same form domain.

### Variational principles and essential spectrum

The **discrete spectrum** consists of isolated eigenvalues of finite
multiplicity; the **essential spectrum** is the rest of the spectrum.
For self-adjoint operators this agrees with the Fredholm definition.

* **22.27. Min–max principle.** The numbers
  $$\lambda_n=\inf_{\substack{L\subset Q(q)\\\dim L=n}}
                 \sup_{0\ne u\in L}\frac{q[u]}{\|u\|^2}$$
  enumerate the eigenvalues below $\inf\sigma_{\rm ess}(A)$, with
  multiplicity, and equal that threshold once there are fewer than $n$
  such eigenvalues. The threshold is $+\infty$ for compact resolvent.

### Perturbation theory

$B$ is **$A$-bounded** if $D(A)\subset D(B)$ and
$\|Bu\|\leq a\|Au\|+b\|u\|$. It is **$A$-compact** if it is compact
from the graph-norm domain to $H$. A holomorphic family of **type (A)**
has a common domain and holomorphic $A(z)u$ there; a **type (B)** family
is obtained from closed sectorial forms with common domain and holomorphic
form values.

* **22.33. Kato–Rellich theorem.** If $A$ is self-adjoint and $B$ symmetric
  with $A$-bound less than one, $A+B$ is self-adjoint on $D(A)$ and
  essentially self-adjoint on every core of $A$.

* **22.35. Analytic isolated eigenvalues.** For a holomorphic type (A) or
  type (B) family, an isolated spectral cluster of finite multiplicity has
  a locally holomorphic Riesz projection. A simple isolated eigenvalue
  and its eigenvector can be chosen holomorphically locally.

* **22.39. Birman–Schwinger principle.** If $H_0\geq0$, $V\geq0$, and
  $K_E=V^{1/2}(H_0+E)^{-1}V^{1/2}$ is a well-defined compact operator,
  then $-E<0$ is an eigenvalue of the form sum $H_0-V$ exactly when
  one is an eigenvalue of $K_E$, with the same multiplicity.
  Moreover $N(H_0-V<-E)=N(K_E>1)$.

### Schrödinger operators and eigenvalue estimates

Write $H_V=-\Delta+V$ on $L^2(\mathbb R^d)$, with form realization when
needed, and $V_- =\max(-V,0)$. The form statements assume $V_+$ is
locally integrable and the negative part satisfies the stated relative
form bounds, so the form domain is dense and the operator is well defined.

* **22.40. Free Laplacian.** $-\Delta$ is self-adjoint on $H^2(\mathbb R^d)$,
  essentially self-adjoint on $C_c^\infty$, and unitarily equivalent by
  Fourier transformation to multiplication by $|\xi|^2$. Its spectrum
  is purely absolutely continuous and equals $[0,\infty)$.

### Sturm–Liouville operators and quantum graphs

For the one-dimensional expression $\tau u=-u''+Vu$ with real
$V\in L^1_{\rm loc}(a,b)$, the maximal domain consists of $u,u'$
locally absolutely continuous with $u,\tau u\in L^2$. A singular
endpoint is **limit circle** if all solutions for nonreal spectral
parameter are square integrable near it, and **limit point** otherwise.

* **22.51. Weyl alternative.** At each endpoint the limit-point/limit-circle
  classification is independent of the nonreal parameter. A limit-circle
  endpoint requires one self-adjoint boundary condition; a limit-point
  endpoint requires none. The minimal operator is essentially self-adjoint
  exactly when both endpoints are limit point.

### Scattering, spectral dynamics, and stability

For self-adjoint $A,A_0$, the **wave operators** are
$W_\pm=\operatorname{s-lim}_{t\to\pm\infty}e^{itA}e^{-itA_0}P_{\rm ac}(A_0)$,
when they exist. They are **complete** if their ranges equal $H_{\rm ac}(A)$.

* **22.59. Kato–Rosenblum theorem.** A trace-class self-adjoint perturbation
  preserves the absolutely continuous part up to unitary equivalence:
  if $A-A_0$ is bounded trace class, both wave operators exist and are
  complete. Singular spectral parts need not be preserved.

* **22.61. RAGE theorem.** A vector $u$ belongs to the continuous spectral
  subspace exactly when for every compact $C$,
  $T^{-1}\int_0^T\|Ce^{-itA}u\|^2dt\to0$. A vector belongs to the
  pure point subspace exactly when its unitary orbit is relatively compact
  ([Teschl, Chapter 5](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf)).

## 23. Operator algebras, operator spaces, free probability, and noncommutative geometry

There is substantial C*-algebraic infrastructure, including continuous functional calculus, positivity, commutative representation, and parts of GNS. The GNS gap below is the cyclic vector-state realization for an arbitrary state. Beyond it, the principal missing theories are completely positive dilation, von Neumann representation and modular theory, K-theory, operator spaces, and free probability.

Sources: [mathematical synopsis](SYNOPSIS23.md); [combined coverage inventory](Mathlib23.md).

A **C*-algebra** is a complex Banach star algebra satisfying
$\|a^*a\|=\|a\|^2$. A **representation** is a star homomorphism into
$\mathcal B(H)$. A **von Neumann algebra** is a unital star subalgebra of
$\mathcal B(H)$ closed in the weak operator topology. Write $M'$ for the
commutant and $Z(M)=M\cap M'$ for the center. A **state** is a positive
linear functional of norm one; a **trace** also satisfies $\tau(ab)=\tau(ba)$.
Hilbert inner products are linear in the first variable.

### C*-algebras, positivity, and representations

* **23.9. GNS construction.** Every state has a cyclic representation
  $(\pi_\varphi,H_\varphi,\Omega_\varphi)$ with
  $\varphi(a)=\langle\pi_\varphi(a)\Omega_\varphi,\Omega_\varphi\rangle$,
  unique up to a unitary preserving the cyclic vector.

* **23.10. Gelfand–Naimark theorem.** Every C*-algebra has a faithful
  isometric representation as a norm-closed star algebra of operators.
  The direct sum of its state GNS representations is faithful.

### Completely positive maps and dilations

A map $\Phi:A\to B$ is **completely positive** (CP) if
$\Phi_n:M_n(A)\to M_n(B)$, acting entrywise, is positive for every $n$.
An **operator system** is a unital self-adjoint subspace of a C*-algebra.

* **23.17. Stinespring theorem.** A CP map $\Phi:A\to\mathcal B(H)$ on
  a unital C*-algebra is $\Phi(a)=V^*\pi(a)V$ for a representation
  $\pi$ on $K$. The realization is unique up to unitary equivalence when
  $K=\overline{\pi(A)VH}$; $V$ is isometric if $\Phi$ is unital.

* **23.18. Arveson extension theorem.** Every CP map from an operator
  system $S\subset A$ into $\mathcal B(H)$ extends to a CP map on $A$.
  Unitality is preserved.

### Von Neumann algebras and projection structure

A functional on a von Neumann algebra is **normal** if it is ultraweakly
continuous; for positive functionals this is equivalent to preserving
bounded increasing suprema. A projection $p$ is **finite** if it is not
equivalent to a proper subprojection, where $p\sim q$ means
$v^*v=p$, $vv^*=q$ for a partial isometry $v$ in the algebra.
A **factor** has center $\mathbb C1$.

* **23.21. Bicommutant theorem.** A unital star algebra has the same strong
  and weak operator closures, both equal to its bicommutant. Thus
  $M=M''$ characterizes von Neumann algebras.

* **23.22. Kaplansky density theorem.** If a C*-algebra acts nondegenerately,
  its unit ball is strongly dense in the unit ball of its bicommutant.
  The same holds for self-adjoint and positive unit balls.

* **23.23. Predual theorem.** Every von Neumann algebra has a unique Banach
  predual, consisting of its normal functionals. For $\mathcal B(H)$
  this is trace class, paired by $\operatorname{tr}(Ta)$.

* **23.27. Type decomposition.** A von Neumann algebra splits uniquely by
  central projections into types I, II, and III. Type I has abelian
  projections with central support one; type II is semifinite without
  nonzero abelian projections; type III has no nonzero finite projections.

### Modular theory, equilibrium, and subfactors

For a cyclic separating unit vector $\Omega$ of $M$, put
$\varphi(a)=\langle a\Omega,\Omega\rangle$ and close the antilinear
operator $S_0(a\Omega)=a^*\Omega$ and write $S=J\Delta^{1/2}$.
Here $J$ is the **modular conjugation** and $\Delta$ the **modular
operator**. A II$_1$ **subfactor** is a unital inclusion of II$_1$ factors.

* **23.33. Tomita theorem.** $JMJ=M'$ and
  $\Delta^{it}M\Delta^{-it}=M$. Thus
  $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$ is a one-parameter automorphism
  group intrinsic to the faithful normal vector state.

* **23.38. Jones index theorem.** For an inclusion $N\subset M$ of II$_1$
  factors, $[M:N]=\dim_NL^2(M)$ lies in
  $\{4\cos^2(\pi/n):n=3,4,\ldots\}\cup[4,\infty]$.
  Each listed value is realized by a subfactor.

### Tensor products, nuclearity, and approximation

The **minimal tensor norm** on $A\odot B$ comes from faithful spatial
representations; the **maximal norm** is the supremum over pairs of
commuting representations. $A$ is **nuclear** if these norms agree for
every C*-algebra $B$, and **exact** if minimal tensoring by $A$ preserves
short exact sequences.

* **23.40. Completely positive approximation theorem.** $A$ is nuclear
  exactly when its identity is a point-norm limit of compositions
  $A\to M_{n_i}\to A$ of completely positive contractions.

### K-theory, extensions, and crossed products

$K_0(A)$ is formed from stable Murray–von Neumann classes of matrix
projections by group completion; $K_1(A)$ uses stable homotopy classes
of matrix unitaries. Nonunital groups are defined through the unitization
and the kernel of the scalar map. The **suspension** is $SA=C_0(\mathbb R)\otimes A$.
An **AF algebra** is an inductive limit of finite-dimensional C*-algebras.

* **23.47. Bott periodicity.** $K_i(S^2A)\cong K_i(A)$ naturally. Together
  with $K_i(SA)=K_{1-i}(A)$ this makes complex C*-algebra K-theory
  two-periodic.

* **23.48. Six-term exact sequence.** A short exact sequence
  $0\to I\to A\to B\to0$ yields the cyclic exact sequence
  $$K_0(I)\to K_0(A)\to K_0(B)\xrightarrow{\partial}
       K_1(I)\to K_1(A)\to K_1(B)\xrightarrow{\partial}K_0(I).$$

### Operator spaces and completely bounded maps

An **operator space** is a closed linear subspace $E\subset\mathcal B(H)$
with its induced matrix norms. A linear map is **completely bounded** if
$\|T\|_{\rm cb}=\sup_n\|T_n\|<\infty$. A **complete isometry** preserves
all matrix norms, not merely the norm on $E$.

* **23.54. Ruan representation theorem.** Abstract matrix norms come from
  a concrete operator space exactly when
  $\|x\oplus y\|=\max(\|x\|,\|y\|)$ and
  $\|\alpha x\beta\|\leq\|\alpha\|\|x\|\|\beta\|$ for scalar
  matrices of compatible sizes.

### Free probability and random matrix limits

A **noncommutative probability space** is a unital algebra with a unital
linear functional $\varphi$, positive in the star setting. Unital subalgebras
are **free** if $\varphi(a_1\cdots a_n)=0$ whenever successive factors
come from different subalgebras and each has zero expectation. A
**distribution** records all joint star moments. $NC(n)$ denotes the
noncrossing partitions of $\{1,\ldots,n\}$.

The scalar **free cumulants** of a law are determined by $\varphi(a^n)=\sum_{\pi\in NC(n)}\prod_{B\in\pi}\kappa_{|B|}$. Free additive convolution $\mu\boxplus\nu$ is the distribution of a sum of freely independent self-adjoint variables with laws $\mu,\nu$.

* **23.61. Free central limit theorem.** For identically distributed free
  self-adjoint variables of mean zero and variance one, normalized sums
  converge in moments to the semicircle law
  $(2\pi)^{-1}\sqrt{4-x^2}\,1_{[-2,2]}dx$.

* **23.64. R-transform linearization.** For a compactly supported law,
  $R(w)=\sum_{n\geq1}\kappa_nw^{n-1}$ near zero. Free additive
  convolution satisfies $R_{\mu\boxplus\nu}=R_\mu+R_\nu$.

* **23.67. Asymptotic freeness of Gaussian matrices.** Independent GUE
  matrices with variance normalization $1/N$ converge jointly in normalized
  trace moments, almost surely, to a free variance-one semicircular family.

## 24. Semigroups, evolution equations, and functional calculus

Strongly continuous semigroups, generators, Hille–Yosida, Lumer–Phillips, homogeneous well-posedness, bounded perturbations, and Yosida approximation are covered. The remaining selection starts with forcing and approximation and proceeds to analytic generation, fractional powers, regularity, stability, and nonlinear generation. These gaps should not be described as absence of semigroup theory altogether.

Sources: [mathematical synopsis](SYNOPSIS24.md); [combined coverage inventory](Mathlib24.md).

A **$C_0$-semigroup** on a Banach space $X$ is a family $T(t)$ of bounded
linear maps with $T(0)=I$, $T(t+s)=T(t)T(s)$, and $T(t)x\to x$ as
$t\downarrow0$ for every $x$. Its **generator** is
$Ax=\lim_{t\downarrow0}(T(t)x-x)/t$ on the vectors where this limit
exists. Thus the evolution convention is $u'=Au$. For sectorial calculus
and parabolic equations we instead write $B=-A$, so $u'+Bu=f$.

### Cauchy problems and perturbations

A **classical solution** is differentiable in $X$, lies in $D(A)$, and
satisfies the equation there. A **mild solution** uses the variation-of-constants
formula and need not be differentiable.

* **24.13. Variation of constants.** For $f\in L^1(0,T;X)$ and $x\in X$,
  $$u(t)=T(t)x+\int_0^tT(t-s)f(s)\,ds$$
  is the unique mild solution. If $x\in D(A)$ and $f$ is continuously
  differentiable, it is classical.

* **24.17. Trotter–Kato approximation.** Suppose $A_n,A$ generate semigroups
  with one common exponential bound. Strong convergence
  $R(\lambda,A_n)x\to R(\lambda,A)x$ for one sufficiently large
  real $\lambda$ is equivalent to $T_n(t)x\to T(t)x$ uniformly on
  bounded time intervals.

* **24.18. Chernoff product formula.** Let $F(0)=I$, $F$ be strongly
  continuous, and $\|F(t)^n\|\leq Me^{\omega nt}$. If
  $F'(0)x=Ax$ on a core of a generator $A$, then
  $F(t/n)^nx\to T(t)x$ uniformly on bounded time intervals.

### Analyticity, smoothing, and fractional powers

A semigroup is **bounded analytic** if it extends holomorphically and
boundedly to a sector around the positive time axis, strongly continuous
at zero on smaller sectors. A densely defined closed $B$ is **sectorial**
of angle $\theta$ if its spectrum lies in the closed sector
$\overline{\Sigma_\theta}$ and $z(z-B)^{-1}$ is bounded outside every
strictly larger sector.

* **24.20. Analytic generation theorem.** $-B$ generates a bounded analytic
  semigroup exactly when $B$ is sectorial of angle less than $\pi/2$.
  Shifts allow the corresponding exponentially bounded formulation.

* **24.23. Balakrishnan formula.** For $0<\alpha<1$ and sectorial $B$,
  $$B^\alpha x=\frac{\sin\pi\alpha}{\pi}
      \int_0^\infty t^{\alpha-1}B(t+B)^{-1}x\,dt\qquad(x\in D(B)).$$
  Closure yields the fractional power on its full domain.

### Holomorphic calculus and maximal regularity

For suitable holomorphic $f$ on a sector containing $\sigma(B)$,
$f(B)=(2\pi i)^{-1}\int_\Gamma f(z)(z-B)^{-1}dz$.
A **bounded $H^\infty$ calculus** satisfies
$\|f(B)\|\leq C\|f\|_\infty$, initially for functions decaying at
zero and infinity and then by regularization. **R-sectoriality** replaces
the sectorial resolvent bound by an R-bound on the entire family.

* **24.30. de Simon maximal regularity.** On Hilbert space, an invertible
  sectorial $B$ of angle below $\pi/2$ gives, for $1<p<\infty$,
  the unique zero-initial-value solution of $u'+Bu=f$ with
  $\|u'\|_{L^p}+\|Bu\|_{L^p}\leq C\|f\|_{L^p}$ on the half-line.

### Spectra, stability, and long-time behavior

The **growth bound** $\omega_0$ is the infimum of admissible exponential
exponents; the **spectral bound** is
$s(A)=\sup\{\operatorname{Re}z:z\in\sigma(A)\}$.
**Strong stability** means $T(t)x\to0$ for each $x$;
**exponential stability** means $\|T(t)\|\leq Me^{-\varepsilon t}$.

* **24.35. Analytic spectral mapping.** For analytic semigroups,
  $\sigma(T(t))\setminus\{0\}=e^{t\sigma(A)}$ for $t>0$.
  The same conclusion holds for eventually norm-continuous semigroups.

* **24.38. Gearhart–Prüss theorem.** A bounded $C_0$-semigroup on Hilbert
  space is exponentially stable exactly when $i\mathbb R\subset\rho(A)$
  and $\sup_{\beta\in\mathbb R}\|R(i\beta,A)\|<\infty$.

* **24.39. Arendt–Batty–Lyubich–Vũ theorem.** A bounded semigroup is
  strongly stable if $\sigma(A)\cap i\mathbb R$ is countable and
  $A^*$ has no eigenvalues on $i\mathbb R$. On reflexive spaces it
  suffices to exclude eigenvalues of $A$ there.

### Nonlinear and Volterra evolution

For a possibly multivalued operator $B\subset X\times X$,
**accretivity** means $\|x-y\|\leq\|x-y+\lambda(u-v)\|$ for
$(x,u),(y,v)\in B$, $\lambda>0$. It is **m-accretive** if also
$\operatorname{ran}(I+\lambda B)=X$ for every $\lambda>0$.

* **24.50. Crandall–Liggett generation.** An m-accretive $B$ generates a
  nonlinear contraction semigroup on $\overline{D(B)}$ by
  $S(t)x=\lim_n(I+tB/n)^{-n}x$. For $x\in D(B)$, convergence is
  uniform on bounded time intervals; extension gives every initial value
  in the domain closure.

## 25. Integral equations and classical operator methods

Schur estimates for nonnegative kernels and the abstract compact-operator alternative are available. The missing content concerns integral kernels themselves, Volterra inversion, singular boundary operators, and regularization of ill-posed equations. The abstract alternative is therefore excluded from the gap list; compact-kernel and boundary-mapping theorems remain substantial missing steps.

Sources: [mathematical synopsis](SYNOPSIS25.md); [combined coverage inventory](Mathlib25.md).

A **Fredholm equation of the second kind** is $(I-\lambda K)u=f$;
an equation of the **first kind** is $Ku=f$. A **Volterra equation**
has integration over the past, for example
$u(t)-\int_0^tk(t,s)u(s)ds=f(t)$. Kernels may be functions or
singular integral kernels; a singular kernel requires a specified limiting
interpretation, not merely a formal integral sign.

### Kernel operators and elementary solution methods

* **25.3. Hilbert–Schmidt kernels.** If $k\in L^2(D\times D)$, its
  integral operator is Hilbert–Schmidt, hence compact, and
  $\|K\|_{S^2}=\|k\|_{L^2}$. Its adjoint has kernel
  $\overline{k(y,x)}$.

* **25.8. Mercer theorem.** A continuous positive definite Hermitian kernel
  on compact $D$ with finite measure of full support has
  $k(x,y)=\sum_n\lambda_ne_n(x)\overline{e_n(y)}$, absolutely and
  uniformly, using its nonzero $L^2$ eigenvalues and continuous eigenfunctions.
  The operator is positive trace class and
  $\sum_n\lambda_n=\int_Dk(x,x)dx$.

### Volterra equations and fractional integration

For $\alpha>0$, the **Riemann–Liouville integral** is
$I^\alpha f(t)=\Gamma(\alpha)^{-1}\int_0^t(t-s)^{\alpha-1}f(s)ds$.

* **25.17. Volterra solvability.** For $Ku(t)=\int_0^t k(t,s)u(s)\,ds$ on $C[0,T]$, with $k$ continuous on $0\leq s\leq t\leq T$, $I-\lambda K$
  is invertible for every complex $\lambda$, and successive substitution
  converges uniformly. The solution depends continuously on the data on
  every bounded time interval.

* **25.21. Abel inversion.** For $0<\alpha<1$, $I^\alpha u=f$ is
  inverted by $u=(d/dt)I^{1-\alpha}f$ whenever
  $I^{1-\alpha}f$ is absolutely continuous and vanishes at zero.
  These conditions characterize the range on $L^1(0,T)$.

### Cauchy singular integrals and factorization

Let $\Gamma$ be a smooth positively oriented simple closed plane curve.
Set $C\phi(z)=(2\pi i)^{-1}\int_\Gamma\phi(\zeta)/(\zeta-z)d\zeta$
off the curve and
$S\phi=(\pi i)^{-1}\operatorname{p.v.}\int_\Gamma
\phi(\zeta)/(\zeta-\cdot)d\zeta$ on it. Interior and exterior traces
are denoted by $C_+$ and $C_-$ in this subsection only.

* **25.23. Plemelj–Sokhotski formulas.** For Hölder densities,
  $C_+\phi=\frac12(I+S)\phi$ and
  $C_-\phi=\frac12(S-I)\phi$. Thus the jump is $\phi$ and the
  average is the principal-value integral.

### Laplace layer potentials and boundary operators

Here $\Omega\subset\mathbb R^3$ is bounded with connected smooth
boundary $\Gamma$, outward normal $n$, and
$\Phi(x,y)=1/(4\pi|x-y|)$, so $-\Delta\Phi=\delta$.
Define $S\mu(x)=\int_\Gamma\Phi(x,y)\mu(y)dS_y$ and
$D\eta(x)=\int_\Gamma\partial_{n_y}\Phi(x,y)\eta(y)dS_y$.
Now superscripts $-$ and $+$ mean interior and exterior traces,
respectively, and both normal derivatives use the same outward $n$.
Let $V=\gamma S$, $K$ be the averaged trace of $D$, $K'$ the averaged
normal derivative of $S$, and $W=-\partial_nD$.

* **25.31. Sobolev mapping properties.**
  $V:H^{-1/2}(\Gamma)\to H^{1/2}(\Gamma)$,
  $K:H^{1/2}\to H^{1/2}$,
  $K':H^{-1/2}\to H^{-1/2}$, and
  $W:H^{1/2}\to H^{-1/2}$ are bounded. These energy-space mappings
  and jump formulas also hold on bounded Lipschitz boundaries.

* **25.34. Calderón projector.** The matrix
  $$\mathcal C^-=
     \begin{pmatrix}\frac12I-K&V\\W&\frac12I+K'\end{pmatrix}$$
  is a bounded projection onto interior harmonic Cauchy data. In
  particular $KV=VK'$, $WK=K'W$, and $K^2+VW=\frac14I$.

### Galerkin, quadrature, and operator approximation

* **25.43. Collectively compact approximation theorem.** Suppose $K_nx\to Kx$
  for every $x$, and $\bigcup_nK_n(B_X)$ is relatively compact.
  If $I-K$ is invertible, then $I-K_n$ is eventually invertible with
  uniformly bounded inverses, and their solutions converge for convergent data.

### Ill-posed equations and regularization

Let $K:X\to Y$ be compact between Hilbert spaces, with nonzero singular
system $Ke_j=s_jf_j$, $K^*f_j=s_je_j$. The **minimum-norm solution**
of $Ku=f$ is the solution orthogonal to $\ker K$. Noisy data satisfy
$\|f^\delta-f\|\leq\delta$.

* **25.50. Tikhonov minimization.** For $\alpha>0$,
  $\|Ku-f^\delta\|^2+\alpha\|u\|^2$ has the unique minimizer
  $u_\alpha^\delta=(K^*K+\alpha I)^{-1}K^*f^\delta$.

## 26. Sobolev spaces, smoothness scales, and interpolation

Weak $W^{k,p}$ spaces, completeness, mollification, basic calculus, several embeddings, and zero-boundary/local compactness are covered. The major missing extensions are general boundary traces and extension, critical and fractional smoothness, fine representatives, Bessel-potential identification, and interpolation of spaces. Extension by zero for $W_0^{1,p}$ does not provide extension of arbitrary $W^{1,p}$ functions.

Sources: [mathematical synopsis](SYNOPSIS26.md); [combined coverage inventory](Mathlib26.md).

For open $\Omega\subset\mathbb R^d$, $W^{m,p}(\Omega)$ consists of
$L^p$ functions with distributional derivatives through integer order $m$
in $L^p$. The norm sums those derivative norms; $H^m=W^{m,2}$.
$W_0^{m,p}$ is the closure of $C_c^\infty(\Omega)$.
Unless specified otherwise $1\leq p<\infty$; statements using duality,
Bessel potentials, or singular-integral characterizations usually assume
$1<p<\infty$ explicitly. Spaces are inhomogeneous unless marked otherwise.

### Weak derivatives and approximation

* **26.12. Extension theorem.** On a bounded Lipschitz domain there is a
  bounded linear extension $W^{m,p}(\Omega)\to W^{m,p}(\mathbb R^d)$
  for each nonnegative integer $m$, including $p=1,\infty$.
  Consequently restrictions of globally smooth functions are dense for finite $p$.

### Embeddings, norm inequalities, and compactness

* **26.15. Critical embedding.** On bounded Lipschitz domains,
  $W^{1,d}\hookrightarrow L^q$ for every finite $q$.
  For $d\geq2$ it does not embed into $L^\infty$; the endpoint
  exponential integrability is given by Moser–Trudinger.

### Traces and zero boundary values

* **26.23. First-order trace theorem.** For bounded Lipschitz $\Omega$ and
  $1<p<\infty$, restriction extends to a bounded surjection
  $W^{1,p}(\Omega)\to B^{1-1/p}_{p,p}(\partial\Omega)$ with a bounded
  linear right inverse. For $p=2$ the range is $H^{1/2}$.

* **26.25. Kernel of the trace.** For bounded Lipschitz domains,
  $W_0^{1,p}=\ker\gamma$ for $1<p<\infty$. On smooth domains,
  $W_0^{m,p}$ is characterized by vanishing of all normal traces
  of orders $0,\ldots,m-1$.

### Capacity and fine representatives

For $1<p<\infty$, **Sobolev capacity** $C_{1,p}(E)$ is the outer
capacity generated by the infimum of $\|v\|_{W^{1,p}(\mathbb R^d)}^p$
over smooth functions at least one near a compact set. A property holds
**quasi-everywhere** if its exceptional set has zero capacity.

* **26.29. Quasicontinuity.** Every $W^{1,p}(\mathbb R^d)$ function has
  a representative continuous outside an open set of arbitrarily small
  $C_{1,p}$ capacity. This representative is unique quasi-everywhere.

### Fractional Sobolev spaces and nonlocal energies

For $0<s<1$ and finite $p$, define
$$[u]_{W^{s,p}(\Omega)}^p=
  \iint_{\Omega\times\Omega}\frac{|u(x)-u(y)|^p}{|x-y|^{d+sp}}dxdy,$$
with norm $\|u\|_p+[u]_{W^{s,p}}$. The Bessel potential space
$H^{s,p}(\mathbb R^d)$ is defined by
$\|(I-\Delta)^{s/2}u\|_p<\infty$ through tempered distributions.

* **26.35. Fractional Hilbert identity.** $W^{s,2}(\mathbb R^d)=H^{s,2}$
  with equivalent norms; the Gagliardo energy equals a positive constant
  times $\int|\xi|^{2s}|\widehat u(\xi)|^2d\xi$.

* **26.40. Bourgain–Brezis–Mironescu limit.** For $u\in W^{1,p}(\mathbb R^d)$,
  $$\lim_{s\uparrow1}(1-s)[u]_{W^{s,p}}^p
     =\frac1p\left(\int_{S^{d-1}}|\omega_1|^pd\omega\right)
                       \int|\nabla u|^p.$$
  This identifies the normalized nonlocal energy with the local gradient energy.

### Besov and Triebel–Lizorkin scales

Choose a smooth inhomogeneous dyadic partition $(\varphi_j)_{j\geq0}$
in frequency and set $\Delta_ju=\mathcal F^{-1}(\varphi_j\widehat u)$.
The **Besov norm** is
$\|u\|_{B^s_{p,q}}=\|(2^{js}\|\Delta_ju\|_p)_j\|_{\ell^q}$;
the **Triebel–Lizorkin norm** is
$\|u\|_{F^s_{p,q}}=\|(\sum_j|2^{js}\Delta_ju|^q)^{1/q}\|_p$.
Use the supremum for $q=\infty$. Below Besov parameters are at least one,
and Triebel–Lizorkin assertions use $1<p<\infty$, unless otherwise stated.

* **26.44. Bessel and Sobolev identifications.**
  $H^{s,p}=F^s_{p,2}$ for real $s$ and $1<p<\infty$;
  for nonnegative integer $m$, $W^{m,p}=H^{m,p}$.
  For $p\ne2$, fractional Gagliardo and Bessel spaces need not coincide.

### Real and complex interpolation

A **Banach couple** $(X_0,X_1)$ embeds both spaces into one Hausdorff
vector space. Define
$K(t,x)=\inf_{x=x_0+x_1}(\|x_0\|_{X_0}+t\|x_1\|_{X_1})$.
The **real interpolation space** $(X_0,X_1)_{\theta,q}$ has norm
$\|t^{-\theta}K(t,x)\|_{L^q(\mathbb R_+,dt/t)}$.
The **complex interpolation space** $[X_0,X_1]_\theta$ consists of
values at $\theta$ of bounded analytic strip functions with boundary
values in $X_0$ and $X_1$, with the infimum boundary norm.

* **26.51. Real interpolation theorem.** An operator bounded
  $X_i\to Y_i$ with norms $M_i$ acts boundedly between the real
  interpolation spaces with bound at most $M_0^{1-\theta}M_1^\theta$.

* **26.52. Complex interpolation theorem.** The same operator bound holds
  between complex interpolation spaces, by the three-lines theorem.

## 27. Fourier analysis and real-variable harmonic analysis

Euclidean and torus Fourier analysis, Schwartz and $L^2$ transforms, maximal inequalities, and approximate identities are covered. The missing bridges are intermediate-exponent Fourier estimates, singular integrals, frequency decompositions, weights, boundary-function spaces, and restriction. Wiener–Ikehara is available; the general Wiener Tauberian theorem is selected separately in Section 20.

Sources: [mathematical synopsis](SYNOPSIS27.md); [combined coverage inventory](Mathlib27.md).

On $\mathbb R^d$ use
$$
\widehat f(\xi)=\int f(x)e^{-2\pi i x\cdot\xi}\,dx,
\qquad f*g(x)=\int f(x-y)g(y)\,dy.
$$
The torus is $\mathbb T^d=\mathbb R^d/\mathbb Z^d$ with probability
measure. $H^s$ denotes the $L^2$ Bessel potential space. Constants in
estimates may depend on dimension and exponents.
Results stated on $L^p$ mean bounded extensions from an appropriate dense
test class when an integral is not initially defined pointwise.

### The Fourier transform and translation-invariant operators

* **27.4. Hausdorff–Young inequality.** For $1\leq p\leq2$ and
  $p'=p/(p-1)$, $\|\widehat f\|_{p'}\leq\|f\|_p$.
  In general no corresponding bounded map $L^p\to L^{p'}$ exists for
  $p>2$ on Euclidean space.

* **27.13. Heisenberg uncertainty.** For $\|f\|_2=1$ with finite
  second moments, $\|x_jf\|_2\|\xi_j\widehat f\|_2\geq1/(4\pi)$.
  Translations and modulations give the centered version, with Gaussian
  equality cases.

### Fourier series, summation, and convergence

Write $\widehat f(k)=\int_{\mathbb T^d}f(x)e^{-2\pi i k\cdot x}dx$.
On $\mathbb T$, $S_Nf=\sum_{|k|\leq N}\widehat f(k)e^{2\pi ikx}$.

* **27.17. Fejér summation.** The Cesàro means
  $\sigma_Nf=(N+1)^{-1}\sum_{n=0}^NS_nf$ converge in $L^p$ for
  $1\leq p<\infty$, uniformly for continuous $f$, and to $f(x)$ at
  every Lebesgue point. Product Fejér kernels give the analogous
  multidimensional assertions.

* **27.22. Carleson–Hunt theorem.** For $1<p<\infty$,
  $\|\sup_N|S_Nf|\|_p\leq C_p\|f\|_p$; in particular ordinary
  Fourier series converge almost everywhere for $f\in L^p$.

### Maximal functions and fractional integration

The **Hardy–Littlewood maximal function** is
$Mf(x)=\sup_{Q\ni x}|Q|^{-1}\int_Q|f|$, over axis-parallel cubes.

* **27.28. Calderón–Zygmund decomposition.** For $f\in L^1$ and
  $\lambda>0$, there are disjoint dyadic cubes $Q_j$ and $f=g+\sum b_j$
  with $\|g\|_\infty\leq C_d\lambda$, $\|g\|_1\leq C\|f\|_1$,
  $\operatorname{supp}b_j\subset Q_j$, $\int b_j=0$,
  $\sum\|b_j\|_1\leq C\|f\|_1$, and
  $\sum|Q_j|\leq\|f\|_1/\lambda$.

### Singular integrals and Fourier multipliers

A **standard Calderón–Zygmund operator** is $L^2$ bounded and represented
off the support of $f$ by a kernel $K(x,y)$ with size
$|K(x,y)|\leq C|x-y|^{-d}$ and Hölder regularity of some order
$0<\delta\leq1$ in each variable away from the diagonal.

* **27.33. Calderón–Zygmund theorem.** Such an operator is weak type
  $(1,1)$ and bounded on $L^p$ for $1<p<\infty$.

* **27.35. Hilbert transform.**
  $Hf(x)=\operatorname{pv}\pi^{-1}\int f(y)/(x-y)dy$ has multiplier
  $-i\operatorname{sgn}\xi$. It is bounded on $L^p$, $1<p<\infty$,
  weak type $(1,1)$, and satisfies $H^2=-I$ on $L^2(\mathbb R)$.

* **27.38. Mihlin multiplier theorem.** If a bounded $m$ is smooth off
  zero and $|\partial^\alpha m(\xi)|\leq C_\alpha|\xi|^{-|\alpha|}$
  for $|\alpha|\leq\lfloor d/2\rfloor+1$, then $T_m$ is bounded
  on every $L^p$, $1<p<\infty$.

### Weights and endpoint spaces

For $1<p<\infty$, a positive locally integrable **$A_p$ weight** satisfies
$$
[w]_{A_p}=\sup_Q\left(\frac1{|Q|}\int_Qw\right)
 \left(\frac1{|Q|}\int_Qw^{-1/(p-1)}\right)^{p-1}<\infty.
$$
For $A_1$ use $Mw\leq Cw$ almost everywhere. Write
$\|f\|_{L^p(w)}=(\int|f|^pw)^{1/p}$.

The real-variable **Hardy space** $H^1(\mathbb R^d)$ consists of integrable $f$ for which $\sup_{t>0}|P_t*f|\in L^1$, where $P_t$ is the Poisson kernel; this maximal-function norm defines its norm. It is distinct from the holomorphic disk spaces in Section 42.

* **27.44. Weighted maximal theorem.** $M$ is bounded on $L^p(w)$,
  $1<p<\infty$, exactly when $w\in A_p$. For $w\in A_1$, it is
  weak type $(1,1)$ with respect to $w(x)dx$.

* **27.49. John–Nirenberg inequality.** For
  $\|b\|_{\mathrm{BMO}}=\sup_Q|Q|^{-1}\int_Q|b-b_Q|$,
  $|\{x\in Q:|b-b_Q|>t\}|\leq C|Q|e^{-ct/\|b\|_{\mathrm{BMO}}}$.
  All finite mean-oscillation exponents give equivalent seminorms.

* **27.52. Hardy–BMO duality.** $(H^1(\mathbb R^d))^*=\mathrm{BMO}/\mathbb C$
  through the extension of $\int fb$ from test functions. The dual norm
  is equivalent to the BMO seminorm.

### Frequency decompositions and oscillation

Let $\Delta_j$ be smooth annular Fourier projections forming a homogeneous
resolution away from zero. Homogeneous distribution identities are understood
modulo polynomials when needed.

* **27.55. Littlewood–Paley theorem.** For $1<p<\infty$,
  $\|f\|_p\asymp\|(\sum_{j\in\mathbb Z}|\Delta_jf|^2)^{1/2}\|_p$.
  The analogous inhomogeneous result includes a low-frequency projection.

* **27.66. Stein–Tomas restriction theorem.** For $d\geq2$ and a smooth
  compact hypersurface $S$ with nonzero Gaussian curvature,
  $\|\widehat f|_S\|_{L^2(S)}\leq C\|f\|_p$ for
  $1\leq p\leq2(d+1)/(d+3)$. Equivalently its extension operator
  maps $L^2(S)$ to $L^{2(d+1)/(d-1)}(\mathbb R^d)$.

## 28. Abstract harmonic analysis on groups

Haar measure and finite abelian Fourier analysis are covered, and TauCeti supplies full compact-group Peter–Weyl theory with Schur orthogonality and characters. The gaps concern general locally compact groups: quotient integration, Pontryagin duality, LCA inversion and Plancherel, representation induction, and amenability. The general Bochner theorem below extends beyond TauCeti’s finite-dimensional Euclidean result.

Sources: [mathematical synopsis](SYNOPSIS28.md); [combined coverage inventory](Mathlib28.md).

Groups are Hausdorff and locally compact. Statements using measurable fields
of representations assume second countability. Haar measure is left Haar
measure, and the modular function is normalized by
$$
\int_G f(xy)\,dx=\Delta_G(y)^{-1}\int_G f(x)\,dx.
$$
Representations are strongly continuous and unitary on complex Hilbert spaces
unless specified otherwise. Compact groups have Haar measure of mass one.

### Haar measure, convolution, and homogeneous spaces

* **28.2. The modular homomorphism.** $\Delta_G:G\to(0,\infty)$ is
  a continuous homomorphism. Inversion carries left Haar measure to
  right Haar measure, with
  $\int f(x^{-1})dx=\int f(x)\Delta_G(x^{-1})dx$.

* **28.10. Weil's integration formula.** For a closed subgroup $H$ with $\Delta_G|_H=\Delta_H$,
  Haar and quotient measures can be normalized so that
  $\int_G f(x)dx=\int_{G/H}\int_Hf(xh)dh\,d(xH)$ for $f\in C_c(G)$.
  General closed subgroups admit a quasi-invariant quotient measure and
  an integration formula with a positive continuous rho-function.

### Locally compact abelian groups

For abelian $G$, the **dual group** $\widehat G$ consists of continuous
characters $\chi:G\to\mathbb T$, with the compact-open topology.
Set $\widehat f(\chi)=\int_Gf(x)\overline{\chi(x)}dx$.

* **28.23. Pontryagin duality.** The evaluation map
  $G\to\widehat{\widehat G}$, $x\mapsto(\chi\mapsto\chi(x))$,
  is a topological group isomorphism.

* **28.28. Plancherel theorem.** With dual Haar measure normalized by Fourier inversion, Fourier
  transformation extends to a unitary $L^2(G)\to L^2(\widehat G)$.
  For $1\leq p\leq2$, it also satisfies
  $\|\widehat f\|_{p'}\leq\|f\|_p$.

* **28.29. Bochner's theorem.** Continuous positive definite functions on
  $G$ are exactly $\phi(x)=\int_{\widehat G}\chi(x)d\mu(\chi)$
  for finite positive measures $\mu$, uniquely determined, with
  $\mu(\widehat G)=\phi(e)$.

### Induction and noncompact representation theory

For closed $H\subset G$, **unitary induction** constructs
$\operatorname{Ind}_H^G\sigma$ from measurable sections of the bundle
$G\times_H H_\sigma\to G/H$, with the quotient measure and its
Radon–Nikodym correction. For invariant quotient measure, sections can
be written $F(xh)=\sigma(h)^{-1}F(x)$ with square-integrable quotient norm.

* **28.47. Mackey's imprimitivity theorem.** A unitary representation
  equipped with a projection-valued measure on $G/H$ satisfying
  $U(x)E(B)U(x)^*=E(xB)$ is unitarily equivalent to the canonical
  system attached to a representation induced from $H$.

* **28.50. Stone–von Neumann theorem.** For the real Heisenberg group,
  every irreducible unitary representation with a fixed nontrivial central
  character is equivalent to the Schrödinger representation with that
  character. The remaining irreducibles are characters of the abelian quotient.

### Convolution algebras, amenability, and spherical analysis

The **Fourier–Stieltjes algebra** $B(G)$ consists of coefficients of unitary
representations, with its norm as $C^*(G)^*$. The **Fourier algebra**
$A(G)$ consists of coefficients of the left regular representation, with
its canonical coefficient norm. For LCA groups these identify respectively
with $M(\widehat G)$ and $L^1(\widehat G)$ under inverse Fourier transform.

* **28.55. Amenability and invariant means.** A locally compact group is
  amenable exactly when there is a positive normalized left-invariant
  mean on $L^\infty(G)$. Compact and abelian groups are amenable;
  amenability is preserved under extensions and passage to closed subgroups.

## 29. Wavelets, frames, time–frequency analysis, and sampling

Abstract reproducing-kernel Hilbert spaces and concrete Hermite bases are available. General Hilbert frames, wavelet constructions, Gabor analysis, and band-limited sampling are missing as theories. The selected results distinguish reconstruction, existence of localized bases, density obstructions, and stable recovery; a single orthonormal basis does not establish these general statements.

Sources: [mathematical synopsis](SYNOPSIS29.md); [combined coverage inventory](Mathlib29.md).

Inner products are linear in the first variable. Use
$\widehat f(\xi)=\int f(t)e^{-2\pi it\cdot\xi}dt$,
$T_xf(t)=f(t-x)$, and $M_\omega f(t)=e^{2\pi i\omega\cdot t}f(t)$.
Wavelet and sampling formulas are one dimensional unless stated otherwise;
frame and short-time Fourier-transform results apply in arbitrary dimension.

### Frames, bases, and stable reconstruction

A sequence $(f_k)$ in a Hilbert space $H$ is a **frame** if
$A\|f\|^2\leq\sum_k|\langle f,f_k\rangle|^2\leq B\|f\|^2$
for constants $0<A\leq B<\infty$. The upper bound alone defines a
**Bessel sequence**. A **Riesz basis** is the image of an orthonormal
basis under a bounded invertible operator. A frame is **tight** if $A=B$,
and **Parseval** if $A=B=1$. A **Riesz sequence** is a Riesz basis
for its closed linear span.

The analysis operator is $Cf=(\langle f,f_k\rangle)_k$ and its adjoint is synthesis $C^*c=\sum_kc_kf_k$; the frame operator is $S=C^*C$.

* **29.2. Frame operator criterion.** A Bessel sequence is a frame exactly
  when $S=C^*C$ is boundedly invertible; equivalently
  $AI\leq S\leq BI$. It is also equivalent to synthesis being onto $H$.

* **29.3. Canonical dual reconstruction.** The sequence
  $\widetilde f_k=S^{-1}f_k$ is a frame, and
  $f=\sum_k\langle f,\widetilde f_k\rangle f_k
  =\sum_k\langle f,f_k\rangle\widetilde f_k$ unconditionally in $H$.
  Its optimal bounds are the reciprocals of the original optimal bounds,
  in reverse order.

### Multiresolution and orthonormal wavelets

An **orthonormal dyadic wavelet** is a function $\psi$ for which
$\psi_{j,k}(t)=2^{j/2}\psi(2^jt-k)$, $j,k\in\mathbb Z$, is an
orthonormal basis of $L^2(\mathbb R)$. A **multiresolution analysis**
(MRA) is a nested family $V_j$ with dense union, zero intersection,
$f\in V_j\iff f(2\cdot)\in V_{j+1}$, and an orthonormal basis
$(\phi(\cdot-k))_k$ of $V_0$.

The scaling filter $h_k$ is defined by $\phi(t)=\sqrt2\sum_kh_k\phi(2t-k)$, and $W_0=V_1\ominus V_0$.

* **29.16. Wavelet construction from an MRA.** Setting
  $g_k=(-1)^k\overline{h_{1-k}}$ and
  $\psi(t)=\sqrt2\sum_kg_k\phi(2t-k)$ gives an orthonormal
  basis $(\psi(\cdot-k))_k$ of $W_0$ and hence an orthonormal wavelet.

* **29.19. Compactly supported wavelets.** For every positive integer $N$
  there are real compactly supported orthonormal wavelets with $N$
  vanishing moments and finite refinement filters. The attainable
  regularity tends to infinity with appropriate increasing filter orders.

### Function spaces and approximation through wavelets

Use an inhomogeneous system consisting of scaling functions at scale zero
and wavelets for $j\geq0$. The following statements require smoothness,
decay, and vanishing moments sufficiently large for the indicated parameters.
Compactly supported wavelets with more than $|s|$ derivatives and moments
suffice in the Banach ranges below.

* **29.25. Unconditional $L^p$ bases.** A sufficiently regular orthonormal
  wavelet basis is unconditional in $L^p(\mathbb R)$ for $1<p<\infty$.
  Its square function
  $(\sum_{j,k}|c_{j,k}|^2 2^j1_{[2^{-j}k,2^{-j}(k+1))})^{1/2}$
  has norm equivalent to $\|f\|_p$, with the low-frequency part added.

### Continuous wavelets and short-time Fourier analysis

The **short-time Fourier transform** (STFT) with window $g$ is
$V_gf(x,\omega)=\langle f,M_\omega T_xg\rangle$.
For continuous wavelets write
$\psi_{a,b}(t)=|a|^{-1/2}\psi((t-b)/a)$ with $a\ne0$.

* **29.35. STFT orthogonality.** For $f,h,g,k\in L^2(\mathbb R^d)$,
  $\int V_gf\overline{V_kh}=\langle f,h\rangle\langle k,g\rangle$.
  In particular $\|V_gf\|_2=\|g\|_2\|f\|_2$.

### Gabor systems and modulation spaces

A rectangular **Gabor system** is
$\mathcal G(g,a,b)=\{M_{bn}T_{ak}g:k,n\in\mathbb Z^d\}$,
where $a,b>0$.

* **29.41. Density obstruction.** A rectangular single-window Gabor
  frame requires $(ab)^d\leq1$; a Gabor Riesz sequence requires
  $(ab)^d\geq1$. A Gabor Riesz basis therefore has $ab=1$.

* **29.46. Balian–Low theorem.** If $\mathcal G(g,a,b)$ is a Riesz
  basis of $L^2(\mathbb R)$, then $tg(t)$ and
  $\xi\widehat g(\xi)$ cannot both belong to $L^2$.

### Bandlimited and nonuniform sampling

Let $PW_B=\{f\in L^2(\mathbb R):\operatorname{supp}\widehat f
\subset[-B,B]\}$, $B>0$, with its continuous entire representative.
Sampling is **stable** on a set $\Lambda$ if
$A\|f\|_2^2\leq\sum_{\lambda\in\Lambda}|f(\lambda)|^2\leq B_0\|f\|_2^2$.

* **29.52. Shannon sampling theorem.** For $f\in PW_B$,
  $$
  f(t)=\sum_{k\in\mathbb Z}f(k/(2B))\operatorname{sinc}(2Bt-k),
  \qquad \|f\|_2^2=(2B)^{-1}\sum_k|f(k/(2B))|^2.
  $$
  The series converges in $L^2$ and uniformly on the real axis.

* **29.55. Kadec's one-quarter theorem.** If
  $\sup_{k\in\mathbb Z}|2B\lambda_k-k|<1/4$, the sampling kernels
  at $\lambda_k$ form a Riesz basis of $PW_B$. The universal
  constant $1/4$ cannot be enlarged.

* **29.56. Landau's necessary densities.** For a uniformly separated set,
  stable sampling for $PW_B$ requires $D^-(\Lambda)\geq2B$;
  stable interpolation requires $D^+(\Lambda)\leq2B$, where
  $D^-=\liminf_{R\to\infty}\inf_x\#(\Lambda\cap[x,x+R])/R$
  and $D^+$ uses $\limsup$ and $\sup$.

### Sparse recovery and redundant dictionaries

For $A\in\mathbb C^{m\times N}$, a vector is **$s$-sparse** if it has
at most $s$ nonzero coordinates. Write
$\sigma_s(x)_1=\inf_{\#\operatorname{supp}z\leq s}\|x-z\|_1$.
The **restricted isometry constant** $\delta_s$ is the least $\delta$
with $(1-\delta)\|x\|_2^2\leq\|Ax\|_2^2\leq(1+\delta)\|x\|_2^2$
for every $s$-sparse $x$.

* **29.62. Stable recovery from restricted isometry.** For example,
  $\delta_{2s}<\sqrt2-1$ guarantees that every minimizer
  $\widehat x$ of $\|z\|_1$ subject to $\|Az-y\|_2\leq\eta$,
  with $\|Ax-y\|_2\leq\eta$, obeys
  $\|x-\widehat x\|_2\leq C\sigma_s(x)_1/\sqrt s+D\eta$.
  Constants depend only on the restricted isometry bound.

## 30. Distributions, pseudodifferential operators, microlocal and semiclassical analysis

Distributional operations, Fourier multipliers on Schwartz functions, and some Sobolev and Laplacian results are present. Symbol classes, pseudodifferential and Fourier-integral calculi, wavefront geometry, and semiclassical analysis are missing. The selection gives the central mapping, composition, inversion, and propagation theorems; the kernel and fundamental-solution gaps are listed in Section 16.

Sources: [mathematical synopsis](SYNOPSIS30.md); [combined coverage inventory](Mathlib30.md).

Here $D_j=(1/i)\partial_{x_j}$ and
$\widehat u(\xi)=\int e^{-ix\cdot\xi}u(x)dx$, so Fourier inversion
has factor $(2\pi)^{-d}$. Operators on open sets are properly supported
when needed; assertions on a closed manifold mean a compact smooth manifold
without boundary. Symbols and coefficients are smooth unless specified.

### Wavefront sets and operations on singular distributions

The **wavefront set** $\mathrm{WF}(u)\subset T^*\Omega\setminus0$
excludes $(x_0,\xi_0)$ when some cutoff $\chi=1$ near $x_0$ has
$\widehat{\chi u}$ rapidly decreasing in a conic neighborhood of $\xi_0$.
The **Sobolev wavefront set** $\mathrm{WF}^s(u)$ replaces rapid decay
by conic square integrability with weight $\langle\xi\rangle^{2s}$.

* **30.15. Pullback theorem.** A smooth map $F:X\to Y$ admits the
  pullback of $u$ if no $(F(x),\eta)\in\mathrm{WF}(u)$ satisfies
  $dF_x^T\eta=0$. Its wavefront set is contained in $\{(x,dF_x^T\eta):(F(x),\eta)\in\mathrm{WF}(u)\}$. Pullback by a submersion is always defined.

* **30.17. Product theorem.** The product $uv$ is defined if there are no
  $(x,\xi)\in\mathrm{WF}(u)$ and $(x,-\xi)\in\mathrm{WF}(v)$.
  Its wavefront set is contained in $\mathrm{WF}(u)\cup\mathrm{WF}(v)$
  together with fiberwise sums of covectors from these two sets.

### Symbols, quantization, and the operator calculus

The class $S^m_{1,0}$ consists of symbols with
$|\partial_x^\alpha\partial_\xi^\beta a(x,\xi)|
\leq C_{\alpha\beta}\langle\xi\rangle^{m-|\beta|}$, locally uniformly
in $x$, or globally when global mapping bounds are asserted. Left quantization is
$$
\operatorname{Op}(a)u(x)=(2\pi)^{-d}\iint
 e^{i(x-y)\cdot\xi}a(x,\xi)u(y)dy\,d\xi.
$$
A **classical symbol** has an expansion in terms homogeneous in $\xi$
of degrees $m,m-1,\ldots$ for large $|\xi|$.

* **30.23. Composition formula.** If $A=\operatorname{Op}(a)$ and
  $B=\operatorname{Op}(b)$, then $AB=\operatorname{Op}(a\#b)$ with
  $$
  a\#b\sim\sum_\alpha\frac{1}{i^{|\alpha|}\alpha!}
       (\partial_\xi^\alpha a)(\partial_x^\alpha b).
  $$
  Orders add, and the remainder after $N$ derivative orders has order
  $m+m'-N$.

* **30.27. Calderón–Vaillancourt theorem.** A symbol with sufficiently many
  bounded derivatives in both variables defines a bounded $L^2$ operator.
  The norm is controlled by finitely many of those derivative bounds.

* **30.28. Sobolev mapping theorem.** Globally controlled $S^m_{1,0}$
  operators map $H^s(\mathbb R^d)$ continuously to $H^{s-m}$.
  Properly supported versions give the corresponding local statement.

* **30.31. Sharp Gårding inequality.** If a real scalar $a\in S^m_{1,0}$
  is nonnegative, then
  $\operatorname{Re}\langle\operatorname{Op}(a)u,u\rangle
  \geq-C\|u\|_{H^{(m-1)/2}}^2$, locally with compact support or
  globally under uniform symbol bounds.

### Ellipticity, hypoellipticity, and singularity propagation

An order-$m$ symbol is **elliptic** where $|a(x,\xi)|\geq c|\xi|^m$
at large frequencies in the indicated conic region. The complement is
its characteristic set $\operatorname{Char}(A)$.

* **30.33. Parametrix theorem.** An elliptic operator has a two-sided
  parametrix of order $-m$ modulo smoothing operators. The same
  construction works microlocally in any elliptic conic region.

* **30.39. Subelliptic sums of squares.** If real smooth vector fields
  $X_1,\ldots,X_r$ and their brackets span every tangent space, then
  $\sum_jX_j^*X_j$ is hypoelliptic. Locally there is a positive
  subelliptic gain controlled by the bracket lengths on the compact set.

* **30.40. Propagation of singularities.** Let $P$ have real homogeneous
  principal symbol $p$ of principal type, with nonzero Hamilton field
  on the characteristic set. In a region where $Pu$ is smooth,
  $\mathrm{WF}(u)$ is a union of maximally extended null
  bicharacteristics of $H_p$ within that region.

### Fourier integral operators and canonical transformations

A nondegenerate homogeneous phase $\phi(x,y,\theta)$ defines a canonical
relation by $\partial_\theta\phi=0$ and covectors
$(x,\partial_x\phi;y,-\partial_y\phi)$. A **Fourier integral operator**
(FIO) has kernel given locally by oscillatory integrals with such phases.
A canonical relation is Lagrangian for the difference of the two
cotangent symplectic forms: that form vanishes on it and its dimension
is half the ambient dimension. The Hamilton field is
$H_p=\partial_\xi p\cdot\partial_x-\partial_xp\cdot\partial_\xi$.
Use the usual operator order in which order-zero canonical-graph FIOs on
equal-dimensional manifolds are locally $L^2$ bounded.

* **30.45. Composition and adjoints.** For transverse canonical relations,
  FIO composition has the composed relation and the sum of the orders.
  Clean composition with excess $e$ adds $e/2$ to that order.
  Adjoints reverse the canonical relation.

* **30.46. $L^2$ boundedness for canonical graphs.** A compactly localized
  order-zero FIO associated to a canonical graph is $L^2$ bounded.
  Order-$m$ graph FIOs map $H^s_{\mathrm{comp}}$ to
  $H^{s-m}_{\mathrm{loc}}$.

* **30.48. Egorov's theorem.** Conjugation of a pseudodifferential
  operator by an elliptic FIO quantizing a canonical transformation
  gives a pseudodifferential operator whose principal symbol is the
  original symbol transported by that transformation.

### Semiclassical operators and phase-space limits

For $0<h\leq1$, Weyl quantization is
$$
\operatorname{Op}_h^w(a)u(x)=(2\pi h)^{-d}\iint
 e^{i(x-y)\cdot\xi/h}a((x+y)/2,\xi;h)u(y)dy\,d\xi.
$$
Unless indicated otherwise, semiclassical statements use symbols with
uniformly bounded derivatives, or compact phase-space support, and appropriate
self-adjoint realizations. Semiclassical Sobolev norms use $\langle hD\rangle^s$.

* **30.55. Defect-measure compactness.** Every $L^2$-bounded family $u_h$
  has a subsequence $h_j\downarrow0$ and a positive Radon measure $\mu$
  with $\langle\operatorname{Op}_{h_j}^w(a)u_{h_j},u_{h_j}\rangle
  \to\int a\,d\mu$ for each compactly supported smooth symbol.
  Mass can escape in space or frequency unless tightness is assumed.

## 31. Ordinary differential equations and dynamical systems

Picard–Lindelöf, smooth dependence, maximal curves, and complete flows under appropriate hypotheses are covered. TauCeti constructs stable and unstable Lipschitz graphs tangent at equilibria. The gap in 31.27 is the full smooth embedded stable-manifold theorem. The other selected gaps concern periodic coefficients, qualitative stability, planar dynamics, bifurcation, and invariant tori.

Sources: [mathematical synopsis](SYNOPSIS31.md); [combined coverage inventory](Mathlib31.md).

The basic equation is $\dot x=F(t,x,\mu)$ in finite-dimensional Euclidean
space or a smooth manifold. A **flow** satisfies
$\varphi_{t+s}=\varphi_t\circ\varphi_s$ on its domain.
Equilibria satisfy $F(x)=0$; periodic orbits are nonconstant closed trajectories.
Smoothness and completeness are imposed in the statements that need them.

### Linear systems, periodic coefficients, and boundary problems

* **31.17. Floquet theorem.** If $A(t+T)=A(t)$, a fundamental matrix
  has the form $P(t)e^{tB}$ with complex $T$-periodic $P$.
  For real $A$, a real factorization can be obtained with $2T$-periodic
  $P$. The eigenvalues of $U(T,0)$ are the Floquet multipliers.

* **31.20. Sturm separation and comparison.** For real scalar
  second-order equations in regular Sturm–Liouville form, zeros of
  linearly independent solutions at the same spectral parameter interlace.
  Increasing the spectral parameter increases oscillation in the usual
  comparison sense when the weight and leading coefficient are positive.

### Stability, invariant manifolds, and limit sets

An equilibrium is **Lyapunov stable** if every neighborhood contains a
smaller neighborhood whose positive trajectories remain in the first; it is
**asymptotically stable** if nearby trajectories also converge to it.
A **hyperbolic equilibrium** has no eigenvalue of $DF$ on the imaginary axis.

* **31.24. Lyapunov's direct theorem.** A positive definite $C^1$ function
  $V$ with $\dot V=\nabla V\cdot F\leq0$ near an equilibrium proves
  stability. Strict negative definiteness of $\dot V$ proves asymptotic
  stability. Proper global versions give global conclusions when solutions exist.

* **31.26. LaSalle invariance principle.** On a compact positively invariant
  set where $\dot V\leq0$, every trajectory approaches the largest
  invariant subset of $\{\dot V=0\}$.

* **31.27. Stable and unstable manifolds.** At a hyperbolic equilibrium
  of a $C^r$ field, $r\geq1$, there are local $C^r$ invariant stable
  and unstable manifolds tangent to the corresponding spectral subspaces.
  They consist locally of the trajectories converging exponentially
  in positive and negative time respectively.

* **31.28. Hartman–Grobman theorem.** Near a hyperbolic equilibrium, the
  nonlinear flow is locally topologically conjugate to its linearization.
  The conjugacy need not be differentiable.

* **31.29. Center manifolds.** For any fixed finite differentiability order,
  a sufficiently smooth vector field has a local center manifold tangent
  to its center spectral subspace. It contains all sufficiently small
  full trajectories that stay nearby for all time, and is generally nonunique.

### Periodic orbits and planar dynamics

* **31.38. Poincaré–Bendixson theorem.** A nonempty compact omega-limit
  set of a $C^1$ planar flow containing no equilibrium is a periodic orbit.
  This excludes the corresponding higher-dimensional chaotic limit-set
  behavior in such planar regions.

### Normal forms, local bifurcations, and averaging

A **bifurcation** is a parameter value at which the local qualitative
orbit structure changes. Nondegeneracy hypotheses in these theorems exclude
higher-codimension cases; center-manifold reduction applies to higher-dimensional
systems with the stated simple critical spectrum.

* **31.47. Hopf bifurcation.** A simple conjugate pair crossing the imaginary
  axis transversely at $\pm i\omega$, $\omega>0$, with no other
  imaginary spectrum and nonzero first Lyapunov coefficient, produces
  a branch of small periodic orbits. Their amplitude is of order
  $\sqrt{|\mu|}$; the cubic normal-form coefficient determines the
  side of existence and radial stability.

### Hamiltonian structure and further continuations

* **31.61. KAM persistence.** Let $H_0(I)$ be analytic with
  $\det\partial_I^2H_0\ne0$ on a bounded action domain.
  A sufficiently small analytic perturbation preserves invariant
  Lagrangian tori with prescribed Diophantine unperturbed frequencies
  $|k\cdot\omega|\geq\gamma|k|^{-\tau}$, $\tau>n-1$, away from
  the domain boundary. The surviving Cantor family has positive measure,
  and its relative measure tends to one as the perturbation tends to zero
  with suitably shrinking $\gamma$.

## 32. Partial differential equations — general and linear theory

Coercive weak zero-boundary Dirichlet existence, compact variational spectrum, and constant-principal-coefficient interior $H^2$ regularity are available. The missing selection concerns general analytic Cauchy problems, transport, classical boundary solvability, variable coefficients, heat and wave evolution, and boundary symbols. In 32.30 the new scope is a variable Lipschitz principal matrix; the constant-matrix case is already covered.

Sources: [mathematical synopsis](SYNOPSIS32.md); [combined coverage inventory](Mathlib32.md).

Write $\Delta=\sum_j\partial_j^2$, so $-\Delta$ is nonnegative, and
$D_j=(1/i)\partial_j$. Unless explicitly relaxed, domains and coefficients
are smooth and boundary domains are bounded. Sobolev spaces are defined
using distributional derivatives; $H_0^1(\Omega)$ imposes zero trace.
For inequalities and maximum principles, solutions are real valued.

### Classification, Cauchy problems, and local solvability

For $P=\sum_{|\alpha|\leq m}a_\alpha(x)D^\alpha$, its **principal
symbol** is $p_m(x,\xi)=\sum_{|\alpha|=m}a_\alpha(x)\xi^\alpha$.
A hypersurface $\phi=0$ is **noncharacteristic** where
$p_m(x,d\phi)\ne0$. Ellipticity means this symbol is nonzero for every
nonzero real covector. Hyperbolicity concerns real characteristic roots in
a chosen time direction; parabolicity combines first-order time evolution
with elliptic spatial diffusion.

* **32.2. Linear transport.** For $u_t+b(t,x)\cdot\nabla u=f$ with a
  smooth complete characteristic flow $X(t;s,x)$,
  $u(t,X(t;0,x))=u_0(x)+\int_0^tf(s,X(s;0,x))ds$.
  This gives existence and uniqueness while the flow remains defined.

* **32.5. Cauchy–Kowalevski theorem.** An analytic PDE solved for its
  highest normal derivative, with analytic right-hand side depending on
  derivatives of no higher total order and strictly lower normal order,
  has a unique local analytic solution for analytic Cauchy data.

* **32.9. Lewy's nonsolvability theorem.** There are smooth complex
  first-order linear differential operators and smooth right-hand sides
  for which no distributional solution exists in any neighborhood of
  a specified point. Variable-coefficient local solvability requires
  more than a nonzero principal symbol somewhere.

### The Laplacian and classical potential methods

* **32.19. Poisson formula.** Continuous boundary data on a ball have a
  unique harmonic extension continuous to the boundary, represented
  by the Poisson kernel. In the upper half-space the kernel is
  $P_t(x)=c_dt/(t^2+|x|^2)^{(d+1)/2}$, normalized to integral one
  for $x\in\mathbb R^d$.

* **32.20. Green's identities.** For smooth $u,v$,
  $\int_\Omega\nabla u\cdot\nabla v
  =-\int_\Omega u\Delta v+\int_{\partial\Omega}u\partial_\nu v$.
  Antisymmetrization gives the second identity and Green representation
  using a fundamental solution or a domain Green function.

* **32.23. Classical Dirichlet and Neumann solvability.** On a smooth
  bounded connected domain, smooth Dirichlet data determine a unique
  harmonic function. The problem $-\Delta u=f$, $\partial_\nu u=g$
  is solvable precisely when $\int_\Omega f+\int_{\partial\Omega}g=0$,
  and then is unique modulo constants.

### Weak elliptic problems and boundary regularity

Consider
$Lu=-\partial_i(a^{ij}\partial_ju)+c u$, with bounded real coefficients,
uniform ellipticity $a^{ij}\xi_i\xi_j\geq\lambda|\xi|^2$, and
$c\geq0$. Repeated indices are summed. The associated form is
$a(u,v)=\int a^{ij}\partial_ju\,\partial_i\overline v+c u\overline v$.
Symmetry is assumed only where explicitly stated.

* **32.25. Nonzero boundary data.** If $\partial\Omega$ is Lipschitz and
  $g\in H^{1/2}(\partial\Omega)$, choose an $H^1$ lifting of $g$
  and solve the zero-trace equation for the remainder. This gives
  existence, uniqueness, and continuous dependence in $H^1$.

* **32.30. Interior $H^2$ regularity.** For locally Lipschitz leading
  coefficients and $f\in L^2_{\mathrm{loc}}$, a weak solution of
  $Lu=f$ belongs to $H^2_{\mathrm{loc}}$, with local estimates
  controlled by $\|f\|_2$ and $\|u\|_{H^1}$ on a larger set.

* **32.32. Boundary $H^2$ regularity.** On a bounded $C^{1,1}$ domain,
  Lipschitz leading coefficients, bounded $c$, zero Dirichlet trace,
  and $f\in L^2$ give $u\in H^2$ with the corresponding estimate.
  Smooth coefficients, boundary, and compatible data yield higher
  boundary regularity.

### Heat equations and parabolic energy methods

* **32.39. Gaussian heat kernel.**
  $G_t(x)=(4\pi t)^{-d/2}e^{-|x|^2/(4t)}$ solves
  $\partial_tG_t=\Delta G_t$, has mass one, and satisfies
  $G_t*G_s=G_{t+s}$.

* **32.44. Weak parabolic existence.** For bounded measurable uniformly
  elliptic $a^{ij}(t,x)$ and bounded nonnegative $c$, initial data in
  $L^2$, and $f\in L^2(0,T;H^{-1})$, the zero-Dirichlet equation
  $u_t+L(t)u=f$ has a unique solution
  $u\in L^2(0,T;H_0^1)$, $u_t\in L^2(0,T;H^{-1})$.

### Waves, finite propagation, and hyperbolic systems

* **32.50. Wave Cauchy problem in energy spaces.** The equation
  $u_{tt}-c^2\Delta u=f$ on $\mathbb R^d$, $c>0$, has a unique
  solution $u\in C([0,T];H^1)$, $u_t\in C([0,T];L^2)$
  for initial data $(u_0,u_1)\in H^1\times L^2$ and
  $f\in L^1(0,T;L^2)$.

* **32.52. Finite propagation speed.** A wave solution at $(t,x)$ depends
  only on initial data in $B(x,ct)$ and forcing in its backward cone.
  Compactly supported data propagate no faster than speed $c$.

### General methods and structural conclusions

* **32.65. Complementing boundary conditions.** For a smooth scalar strongly
  elliptic operator of order $2m$, a system of $m$ boundary operators
  $B_j$ of orders $m_j\leq2m-1$ satisfying the Lopatinskii–Shapiro
  complementing condition gives a Fredholm map
  $u\mapsto(Lu,(B_ju)_j)$ from $H^{s+2m}(\Omega)$ to
  $H^s(\Omega)\oplus\bigoplus_jH^{s+2m-m_j-1/2}(\partial\Omega)$,
  for $s\geq0$. Principal-symbol ellipticity alone does not guarantee
  an arbitrary choice of boundary conditions is valid.

## 33. Elliptic and parabolic equations — regularity, free boundaries, and viscosity solutions

Harmonic mean values and Harnack comparison, classical Laplacian maximum principles, Caccioppoli estimates, weak comparison, and constant-coefficient $H^2$ estimates are covered. The missing body is variable-coefficient regularity, fully nonlinear and viscosity theory, nonlinear degenerate diffusion, and free-boundary regularity. In particular, an energy estimate is available before the still-missing De Giorgi–Moser regularity argument.

Sources: [mathematical synopsis](SYNOPSIS33.md); [combined coverage inventory](Mathlib33.md).

Write $\Delta=\sum_i\partial_i^2$. Uniform ellipticity of a matrix means
$\lambda|\xi|^2\leq a^{ij}(x)\xi_i\xi_j$ and $|A(x)|\leq\Lambda$,
with $0<\lambda\leq\Lambda<\infty$. Repeated indices are summed.
Unless stated otherwise, estimates are local on concentric interior balls;
constants depend on dimension, ellipticity, the indicated coefficient norms,
and the separation of the two balls. Hölder exponents lie in $(0,1)$.

### Weak solutions and rough-coefficient elliptic regularity

Here the scalar weak equation is $-\operatorname{div}(A\nabla u)=0$, with bounded measurable uniformly elliptic $A$, unless a right-hand side is explicitly displayed.

* **33.6. De Giorgi–Nash–Moser Harnack inequality.** A nonnegative weak
  solution satisfies $\operatorname*{ess\,sup}_{B_r}u
  \leq C\operatorname*{ess\,inf}_{B_r}u$ if $B_{2r}\Subset\Omega$.
  Only bounded measurability of the scalar equation's coefficients is needed.

* **33.8. Higher integrability of the gradient.** There is $\varepsilon>0$
  depending only on dimension and ellipticity such that homogeneous
  weak solutions have $\nabla u\in L^{2+\varepsilon}_{\mathrm{loc}}$,
  with reverse Hölder bounds. The inhomogeneous estimate applies to
  $-\operatorname{div}(A\nabla u)=\operatorname{div}f$ for
  $f\in L^{2+\varepsilon}$ in the corresponding local range.

### Classical estimates and nondivergence equations

In this subsection $Lu=a^{ij}u_{ij}+b^iu_i+cu$ is a scalar nondivergence-form operator; its leading matrix is uniformly elliptic.

* **33.13. Alexandrov–Bakelman–Pucci estimate.** For $u\in W^{2,n}(\Omega)
  \cap C(\overline\Omega)$, $\Omega$ bounded, and uniformly elliptic $A$,
  $\sup_\Omega u\leq\sup_{\partial\Omega}u^+
  +C\operatorname{diam}(\Omega)\|(a^{ij}u_{ij})^-\|_{L^n(\Omega)}$.

* **33.14. Krylov–Safonov theorem.** Nonnegative strong solutions of
  $a^{ij}(x)u_{ij}=0$ with measurable uniformly elliptic coefficients
  satisfy interior Harnack inequalities. General solutions have interior
  Hölder estimates with universal positive exponent.

* **33.15. Interior Schauder estimate.** If $a^{ij},b^i,c,f\in C^{0,\alpha}$
  and $Lu=f$, then on $\Omega'\Subset\Omega$,
  $\|u\|_{C^{2,\alpha}(\Omega')}\leq
  C(\|u\|_{C^0(\Omega)}+\|f\|_{C^{0,\alpha}(\Omega)})$.

* **33.16. Boundary Schauder theory.** On a bounded $C^{2,\alpha}$ domain,
  the preceding coefficient assumptions and $C^{2,\alpha}$ Dirichlet
  data give a global estimate of the same order. With $c\leq0$,
  the Dirichlet problem is uniquely solvable in $C^{2,\alpha}$.

* **33.17. Interior $W^{2,p}$ estimates.** For $1<p<\infty$, continuous
  uniformly elliptic leading coefficients and bounded lower-order
  coefficients give local $W^{2,p}$ estimates for strong solutions,
  controlled by $\|Lu\|_p$ and $\|u\|_p$ on a larger set.
  A coefficient modulus of continuity enters the estimate.

### Viscosity and fully nonlinear equations

For a continuous **proper degenerate elliptic** operator $G(x,r,p,X)$,
$G$ is nondecreasing in $r$ and nonincreasing in the symmetric matrix $X$.
An upper semicontinuous $u$ is a **viscosity subsolution** of $G=0$ if
$G(x,u,D\phi,D^2\phi)\leq0$ whenever $\phi\in C^2$ touches $u$ from
above. Supersolutions use lower semicontinuity, touching from below, and
the reverse inequality; a continuous solution is both.

* **33.21. Comparison and uniqueness.** For continuous viscosity sub- and
  supersolutions of $\gamma u+G_0(Du,D^2u)=f(x)$, $\gamma>0$,
  continuous $f$, and continuous degenerate elliptic $G_0$, ordered
  boundary values imply ordered solutions on a bounded domain.

* **33.28. Evans–Krylov theorem.** If $F$ is uniformly elliptic and convex
  or concave, solutions of $F(D^2u)=f$ with Hölder $f$ have interior
  $C^{2,\beta}$ estimates for some $\beta>0$ controlled by the
  ellipticity and data regularity.

### Degenerate elliptic and Monge–Ampère equations

The **$p$-Laplacian** is
$\Delta_pu=\operatorname{div}(|\nabla u|^{p-2}\nabla u)$, $1<p<\infty$.
A function is $p$-harmonic when this vanishes weakly.

For convex $u$, the **Alexandrov Monge–Ampère measure** is $\operatorname{MA}_u(E)=|\partial u(E)|$, the Lebesgue measure of the subgradient image. For $C^2$ convex $u$ this is $\det D^2u\,dx$; an Alexandrov solution has the prescribed measure.

* **33.32. $p$-harmonic regularity.** Weak $p$-harmonic functions are
  locally $C^{1,\alpha}$ for some $\alpha=\alpha(n,p)>0$.
  Nonnegative ones satisfy scale-invariant Harnack estimates.

* **33.35. Alexandrov Dirichlet problem.** On a bounded strictly convex
  domain, continuous boundary data and a finite nonnegative interior
  measure determine a unique continuous convex Alexandrov solution.

* **33.36. Interior Monge–Ampère regularity.** Strictly convex Alexandrov
  solutions with $0<\lambda\leq f\leq\Lambda$ are locally
  $C^{1,\alpha}$; Hölder $f$ gives local $C^{2,\alpha}$ regularity.
  Section geometry and strict convexity enter the estimates.

### Parabolic regularity and nonlinear diffusion

Parabolic cylinders use time scale $r^2$. The Hölder space
$C^{\alpha,\alpha/2}$ measures space with exponent $\alpha$ and time with
exponent $\alpha/2$; $W^{2,1}_p$ controls two spatial derivatives and one
time derivative in $L^p$.

* **33.44. Gaussian fundamental-solution bounds.** For
  $u_t=\operatorname{div}(A(t,x)\nabla u)$ on all of $\mathbb R^n$,
  bounded measurable uniformly elliptic $A$ gives a positive kernel
  bounded above and below by constant multiples of
  $(t-s)^{-n/2}\exp(-c|x-y|^2/(t-s))$, with different positive constants.

* **33.51. Porous-medium contraction and propagation.** For
  $u_t=\Delta(u^m)$, $m>1$, nonnegative $L^1$ data generate an
  $L^1$ contraction evolution preserving mass. Bounded compactly
  supported data remain compactly supported for finite times.

### The classical obstacle problem

For a smooth obstacle $\psi$ and compatible trace $g\geq\psi$, minimize
$\int_\Omega(\tfrac12|\nabla u|^2-fu)$ over
$K=\{u\in H^1:u|_{\partial\Omega}=g,\ u\geq\psi\}$.
The **contact set** is $\{u=\psi\}$ and the **free boundary** is its
boundary inside $\Omega$. The normalized local model is
$u\geq0$, $\Delta u=1_{\{u>0\}}$.

* **33.53. Variational inequality.** The minimizer exists uniquely and
  satisfies $\int\nabla u\cdot\nabla(v-u)\geq\int f(v-u)$
  for every $v\in K$. This is equivalent to minimization.

* **33.55. Optimal solution regularity.** For smooth forcing and a
  $C^{1,1}$ obstacle, the solution is locally $C^{1,1}$.
  Second derivatives can jump across the free boundary, so higher
  global regularity is not generally available.

* **33.59. Regular free boundary.** Near a point with half-space blowup,
  the free boundary is $C^{1,\alpha}$, and is smooth for the smooth
  classical model. Regular points form a relatively open subset.

## 34. Hyperbolic equations, conservation laws, dispersive PDE, fluids, and kinetic theory

The inventories report general semigroup prerequisites but no developed theory of the particular hyperbolic, dispersive, fluid, or kinetic equations selected here. This is consequently a large gap extending from model evolution estimates to global weak solutions and conditional regularity. Every global statement below has its stated dimension, sign, size, or regularity restrictions.

Sources: [mathematical synopsis](SYNOPSIS34.md); [combined coverage inventory](Mathlib34.md).

Spatial domains are $\mathbb R^d$ or a flat torus unless specified.
Sobolev spaces are $L^2$ based; $\dot H^s$ denotes the homogeneous scale.
Integrations by parts assume the displayed regularity, decay, periodicity,
or boundary conditions. Existence statements for weak solutions do not imply
uniqueness unless uniqueness is expressly asserted.

### Quasilinear hyperbolicity and the formation of shocks

A first-order system $U_t+\sum_jA^j(U)\partial_jU=0$ is
**symmetrizable hyperbolic** if a smooth positive definite matrix $S(U)$
makes all $S(U)A^j(U)$ symmetric. A one-dimensional conservation law is
$U_t+F(U)_x=0$. Strict hyperbolicity means that $DF(U)$ has distinct
real eigenvalues $\lambda_1<\cdots<\lambda_m$.
A family with eigenvector $r_k$ is genuinely nonlinear if
$D\lambda_k\cdot r_k$ never vanishes, and linearly degenerate if it vanishes identically.

* **34.1. Smooth local well-posedness.** Symmetrizable hyperbolic systems
  with smooth coefficients and initial data in $H^s$, $s>d/2+1$,
  have a unique local solution in $C(H^s)\cap C^1(H^{s-1})$,
  while values stay in the symmetrizable state region.

### Scalar entropy solutions and one-dimensional systems

For scalar laws, the **Kružkov entropy inequalities** use
$\eta_k(u)=|u-k|$ and
$q_k(u)=\operatorname{sgn}(u-k)(f(u)-f(k))$ for all real $k$.

* **34.9. Kružkov existence and uniqueness.** For smooth scalar flux and
  bounded initial data on $\mathbb R^d$, there is a unique bounded
  entropy solution attaining the initial data in $L^1_{\mathrm{loc}}$.
  It satisfies the maximum principle and local finite-speed stability.

* **34.14. Hopf–Lax formula.** For a convex superlinear Hamiltonian $H$
  with Legendre transform $L$ and Lipschitz initial $v_0$,
  $v(t,x)=\inf_y\{v_0(y)+tL((x-y)/t)\}$ is the viscosity solution
  of $v_t+H(v_x)=0$. Its spatial derivative solves the associated
  scalar entropy conservation law almost everywhere.

* **34.19. Glimm's small-BV theorem.** For a smooth strictly hyperbolic one-dimensional system whose characteristic families are all genuinely nonlinear or linearly degenerate, sufficiently
  small total variation about a constant state yields a global entropy
  weak solution in one space dimension, with uniformly small total variation.

### Dispersive estimates and nonlinear Schrödinger equations

Mixed norms are $\|u\|_{L_t^qL_x^r}$. A Schrödinger-admissible pair
satisfies $q,r\geq2$, $2/q+d/r=d/2$, excluding $(q,r,d)=(2,\infty,2)$.
Use $iu_t+\Delta u=\sigma|u|^{p-1}u$, $p>1$, where
$\sigma=+1$ is defocusing and $\sigma=-1$ focusing.

* **34.22. Schrödinger dispersive estimate.** For $t\ne0$,
  $\|e^{it\Delta}f\|_\infty\leq(4\pi|t|)^{-d/2}\|f\|_1$.
  The group is unitary on every $H^s$.

* **34.23. Homogeneous Strichartz estimate.** For admissible $(q,r)$,
  $\|e^{it\Delta}f\|_{L_t^qL_x^r(\mathbb R\times\mathbb R^d)}
  \leq C\|f\|_2$.

* **34.29. Small-data critical scattering.** The cubic NLS on $\mathbb R^3$
  has global solutions for sufficiently small $\dot H^{1/2}$ data,
  for either sign. They scatter to free Schrödinger solutions in
  $\dot H^{1/2}$ as $t\to\pm\infty$.

* **34.30. Virial blowup criterion.** For focusing NLS in the $H^1$
  subcritical or critical range with $p\geq1+4/d$, negative energy
  and finite variance $\int|x|^2|u_0|^2<\infty$ imply finite-time
  breakdown. The variance's second derivative is strictly negative
  under these hypotheses.

### Nonlinear waves and KdV

* **34.35. Defocusing critical waves.** In three dimensions,
  $u_{tt}-\Delta u+u^5=0$ is globally well posed in
  $\dot H^1\times L^2$, and every finite-energy solution scatters
  to free waves in both time directions.

* **34.39. KdV global $L^2$ evolution.** The KdV Cauchy problem $u_t+6uu_x+u_{xxx}=0$ on
  $\mathbb R$ is globally well posed in $L^2$; local low-regularity
  theory and the conserved $L^2$ norm yield global continuation.

### Incompressible Euler flow

The incompressible equations are
$u_t+u\cdot\nabla u+\nabla p=\nu\Delta u$, $\operatorname{div}u=0$,
with $\nu=0$ for Euler and $\nu>0$ for Navier–Stokes.

The vorticity is $\omega=\nabla\times u$ in dimension three and $\omega=\partial_1u_2-\partial_2u_1$ in dimension two.

* **34.42. Euler local well-posedness.** Divergence-free data in $H^s$,
  $s>d/2+1$, give a unique local Euler solution of that regularity,
  continuously dependent on the data.

* **34.45. Beale–Kato–Majda criterion.** A three-dimensional smooth Euler
  solution in $H^s$, $s>5/2$, continues past $T$ if
  $\int_0^T\|\omega(t)\|_\infty dt<\infty$.

* **34.47. Yudovich uniqueness.** On $\mathbb T^2$, bounded initial
  vorticity and a prescribed mean velocity give a unique global weak
  Euler solution in the bounded-vorticity class. Its velocity is
  log-Lipschitz, so its particle trajectories are unique.

### Navier–Stokes and compressible flow

* **34.51. Leray–Hopf existence.** In three dimensions every divergence-free
  $L^2$ datum on $\mathbb R^3$ or $\mathbb T^3$ has a global weak
  solution in $L_t^\infty L_x^2\cap L_t^2\dot H_x^1$, weakly
  continuous in $L^2$, satisfying the energy inequality.

* **34.52. Two-dimensional viscous uniqueness.** In dimension two,
  energy-class Navier–Stokes solutions are unique and global.
  Smooth data give smooth solutions for every positive time.

* **34.54. Prodi–Serrin criterion.** A three-dimensional Leray–Hopf solution
  satisfying $u\in L^q(0,T;L^r)$, $r>3$,
  $2/q+3/r\leq1$, is regular on positive times through $T$ and
  unique in the energy class on its interval of regularity.

* **34.57. Suitable weak-solution partial regularity.** Three-dimensional
  suitable weak solutions satisfy a local energy inequality. Their
  interior singular set has zero one-dimensional parabolic Hausdorff
  measure, by the Caffarelli–Kohn–Nirenberg theorem.

### Transport and kinetic equations

A kinetic density is $f(t,x,v)\geq0$. Collisionless transport is
$f_t+v\cdot\nabla_xf+E\cdot\nabla_vf=0$. The Boltzmann equation adds
$Q(f,f)$ on the right, where elastic binary collisions preserve
$v+v_*$ and $|v|^2+|v_*|^2$.

* **34.64. Global classical Vlasov–Poisson solutions.** Nonnegative smooth
  compactly supported data for the three-dimensional repulsive
  Vlasov–Poisson system generate a unique global classical solution.
  Control of velocity growth is the principal a priori step.

* **34.67. Boltzmann's $H$ theorem.**
  $\int Q(f,f)\log f\,dv\leq0$; the entropy production is an
  integral of $(a-b)\log(a/b)\geq0$ with the collision measure.
  Transport preserves total entropy in the absence of boundary flux.

* **34.70. Renormalized Boltzmann existence.** For hard-sphere collisions
  on the spatial torus, finite mass, energy, and entropy initial data
  admit global nonnegative renormalized solutions satisfying the
  entropy inequality. Admissible renormalizations, for example satisfying
  $|\beta'(z)|\leq C/(1+z)$, make $\beta'(f)Q(f,f)$ meaningful.

### Structural links and geometric hyperbolic equations

* **34.73. DiPerna–Lions transport renormalization.** A vector field in
  $L^1_tW^{1,1}_{\mathrm{loc}}$ with divergence in $L^1_tL^\infty$
  and $b/(1+|x|)\in L^1_t(L^1_x+L^\infty_x)$ has unique
  renormalized transport solutions in $L^\infty_t(L^1\cap L^\infty)$
  for initial data in $L^1\cap L^\infty$. Commutator estimates justify the
  chain rule despite the absence of classical trajectories.

## 35. Nonlinear functional analysis, monotone operators, and fixed points

Inverse and implicit function theory, Lyapunov–Schmidt reduction, Morse–Palais, and nonlinear Fredholm transversality are covered. The missing core is fixed-point existence beyond contractions, topological degree, maximal-monotone surjectivity, and bifurcation. The Sard–Smale and normal-form additions are excluded from the gaps; they remain useful prerequisites for several statements below.

Sources: [mathematical synopsis](SYNOPSIS35.md); [combined coverage inventory](Mathlib35.md).

Spaces are real unless stated otherwise. $X^*$ is the continuous dual of
a Banach space $X$, and $H$ is a Hilbert space identified with its dual.
A set-valued operator is identified with its graph; $y\in Ax$ is written
$(x,y)\in A$. Compact nonlinear maps are continuous maps taking bounded
sets into relatively compact sets, unless compactness of the entire image
is explicitly specified.

### Nonlinear calculus and reduction of equations

The **Fréchet derivative** $DF(x)$ is the bounded linear map satisfying
$F(x+h)=F(x)+DF(x)h+o(\|h\|)$. A Gâteaux derivative tests directional
limits and need not by itself give Fréchet differentiability.

* **35.8. Newton–Kantorovich convergence.** Let $DF(x_0)$ be invertible,
  $\|DF(x_0)^{-1}F(x_0)\|\leq\eta$, and
  $\|DF(x_0)^{-1}(DF(x)-DF(y))\|\leq L\|x-y\|$ on a suitable
  ball. If $L\eta<1/2$ and that ball contains the majorant radius
  $(1-\sqrt{1-2L\eta})/L$, Newton iterates converge to a zero.
  Near a zero with invertible derivative and Lipschitz derivative,
  convergence is quadratic.
  For $L=0$ the radius is interpreted by its limit $\eta$, and
  Newton's method solves the affine problem in one step.

### Topological and metric fixed-point theorems

* **35.11. Brouwer fixed-point theorem.** A continuous self-map of a
  nonempty compact convex subset of $\mathbb R^n$ has a fixed point.

* **35.12. Schauder fixed-point theorem.** If $C$ is nonempty closed
  convex in a Banach space and $T:C\to C$ is continuous with
  relatively compact image, then $T$ has a fixed point.
  In particular this applies to compact maps on bounded $C$.

* **35.14. Kakutani–Fan–Glicksberg theorem.** An upper semicontinuous
  set-valued self-map of a nonempty compact convex subset of a locally
  convex Hausdorff space has a fixed point if all values are nonempty,
  closed, and convex.

* **35.19. Browder–Göhde–Kirk theorem.** A nonexpansive self-map of a
  nonempty closed bounded convex subset of a uniformly convex Banach
  space has a fixed point. Compactness of the map is unnecessary.

### Degree, continuation, and topological obstructions

For bounded open $\Omega\subset\mathbb R^n$, continuous
$F:\overline\Omega\to\mathbb R^n$, and $y\notin F(\partial\Omega)$,
the **Brouwer degree** is the integer $\deg(F,\Omega,y)$.

* **35.21. Degree axioms.** Degree is normalized by
  $\deg(I,\Omega,y)=1$ for $y\in\Omega$, is additive over
  disjoint open subsets containing the relevant inverse image, and
  is invariant under homotopies avoiding $y$ on the boundary.

* **35.26. Leray–Schauder degree.** For compact $K:\overline\Omega\to X$,
  $x\ne Kx$ on $\partial\Omega$, finite-dimensional approximation
  defines $\deg(I-K,\Omega,0)$. It has normalization, additivity,
  homotopy invariance, and the nonzero-degree existence property.

### Monotone operators and variational inequalities

An operator $A:X\rightrightarrows X^*$ is **monotone** if
$\langle a-b,x-y\rangle\geq0$ for all graph pairs $(x,a),(y,b)$.
It is **maximal monotone** if no strictly larger monotone graph contains it.
A single-valued map is **hemicontinuous** if its restrictions to line
segments are weakly continuous in the dual pairing.

* **35.29. Minty's range theorem.** On $H$, a monotone graph $A$ is
  maximal monotone exactly when $\operatorname{Ran}(I+\lambda A)=H$
  for one, equivalently every, $\lambda>0$.

* **35.37. Browder–Minty surjectivity.** On a reflexive Banach space,
  an everywhere-defined bounded-on-bounded-sets, hemicontinuous,
  monotone map $A:X\to X^*$ with
  $\langle Ax,x\rangle/\|x\|\to\infty$ is onto $X^*$.
  Strict monotonicity makes its inverse single-valued.

* **35.42. Existence for variational inequalities.** On a reflexive space,
  a nonempty closed bounded convex $C$ and a bounded hemicontinuous
  monotone $A$ admit a point $u\in C$ satisfying $\langle Au-f,v-u\rangle\geq0$ for every $v\in C$, for each $f\in X^*$. Unbounded $C$
  is allowed under coercivity relative to one point of $C$.

### Local and global bifurcation

* **35.58. Crandall–Rabinowitz simple-eigenvalue theorem.** Suppose $F$
  is $C^2$, $F(\lambda,0)=0$, and $L=D_uF(\lambda_0,0)$ is
  Fredholm of index zero with kernel $\mathbb R\phi$.
  If $D_\lambda D_uF(\lambda_0,0)\phi\notin\operatorname{Ran}L$,
  all nearby nontrivial zeros form a smooth curve
  $(\lambda(s),s\phi+o(s))$ through $(\lambda_0,0)$.

## 36. Calculus of variations, Γ-convergence, and homogenization

Smooth multiplier methods, Morse normal forms, the first geodesic variation, optimal-plan existence, and a quadratic Rayleigh principle are covered. General integral-functional existence and relaxation, concentration, critical-point existence, Γ-convergence, and homogenization are missing. A concrete variational minimization theorem does not supply these broader compactness and convergence principles.

Sources: [mathematical synopsis](SYNOPSIS36.md); [combined coverage inventory](Mathlib36.md).

Unless otherwise stated, $\Omega\subset\mathbb R^d$ is bounded and
Lipschitz, $u:\Omega\to\mathbb R^m$, and $1<p<\infty$.
The model energy is $I(u)=\int_\Omega f(x,u,Du)dx$ on a fixed Sobolev
trace class. Coercivity, growth, and admissibility conditions are part of
the theorem rather than consequences of the notation.

### First and second variations

* **36.1. Euler–Lagrange equation.** A sufficiently regular local minimizer
  with admissible compactly supported variations satisfies
  $f_u-\operatorname{div}f_{Du}=0$. For Sobolev minimizers this
  holds weakly when derivative growth bounds justify differentiation
  under the integral.

### The direct method and lower semicontinuity

* **36.12. Convex integral lower semicontinuity.** A nonnegative
  Carathéodory integrand convex in $F$ gives weak lower
  semicontinuity of $\int f(x,Du)$ under the standard $p$-growth
  hypotheses. A continuous linear load preserves this property.

### Quasiconvexity, minors, and relaxation

A finite continuous $f:\mathbb R^{m\times d}\to\mathbb R$ is
**quasiconvex** if
$f(F)\leq\fint_Qf(F+D\phi)$ for $\phi\in W_0^{1,\infty}(Q;\mathbb R^m)$.
It is **rank-one convex** if it is convex on every rank-one line, and
**polyconvex** if it is a convex function of all minors of $F$.

* **36.17. Morrey's characterization.** For continuous nonnegative
  $f(F)$ with $p$-growth, $\int f(Du)$ is sequentially weakly
  lower semicontinuous on $W^{1,p}$ exactly when $f$ is quasiconvex.

* **36.20. Polyconvex existence theorem.** Let $p>\min(m,d)$ and
  $f(F)=g(\text{all minors of }F)$, where $g$ is convex,
  lower semicontinuous, and nonnegative. If $f$ is $p$-coercive,
  a nonempty finite-energy fixed-trace class has a minimizer.
  The conclusion allows extended-valued determinant constraints.

* **36.21. Quasiconvex relaxation.** For continuous $f$ with two-sided
  coercive $p$-growth, the weak $W^{1,p}$ lower semicontinuous
  envelope of $\int f(Du)$ is $\int Qf(Du)$, where
  $Qf(F)=\inf_{\phi\in W_0^{1,\infty}(Q)}\fint_Qf(F+D\phi)$.

### Young measures and concentration

A **Young measure** is a weakly measurable field of probability measures
$\nu_x$ recording limiting distributions of oscillating values.

* **36.25. Fundamental Young-measure compactness.** A bounded sequence
  in $L^p$, $p>1$, has a subsequence generating $\nu_x$.
  For continuous test integrands whose compositions are uniformly
  integrable, their integrals converge to $\int\langle\nu_x,f(x,\cdot)\rangle dx$.

* **36.29. Div–curl lemma.** If $a_j\rightharpoonup a$ in $L^p$,
  $b_j\rightharpoonup b$ in $L^{p'}$, their divergences and curls
  are locally precompact in the matching negative Sobolev spaces,
  then $a_j\cdot b_j\to a\cdot b$ distributionally.

* **36.31. Concentration–compactness vanishing lemma.** A bounded
  $H^1(\mathbb R^d)$ sequence with
  $\sup_y\int_{B_1(y)}|u_j|^2\to0$ converges strongly to zero
  in $L^q$ for $2<q<2^*$, with $2^*=2d/(d-2)$ for $d\geq3$
  and $2^*=\infty$ otherwise.

### Critical points and minimax methods

For $I\in C^1(X,\mathbb R)$, the **Palais–Smale condition at $c$**
means every sequence with $I(u_j)\to c$ and $DI(u_j)\to0$ has a strongly
convergent subsequence.

* **36.35. Mountain-pass theorem.** If $I(0)=0$, $I\geq\alpha>0$
  on $\|u\|=r$, and $I(e)<0$ for some $\|e\|>r$, then
  $c=\inf_{\gamma(0)=0,\gamma(1)=e}\max_tI(\gamma(t))\geq\alpha$
  is a critical value when Palais–Smale holds at $c$.

### Γ-convergence and variational limits

On a metric space, $F_j$ **Γ-converges** to $F$ if every $x_j\to x$
has $F(x)\leq\liminf F_j(x_j)$ and every $x$ has a **recovery sequence**
$x_j\to x$ with $\limsup F_j(x_j)\leq F(x)$.
Equicoercivity means their sublevels lie in common relatively compact sets.

* **36.43. Fundamental theorem of Γ-convergence.** For equicoercive
  $F_j$ with a proper Γ-limit and finite infima, minimum values converge.
  Every limit of approximate minimizers minimizes $F$; existence of
  minimizers follows with the usual lower semicontinuity of the $F_j$.

* **36.49. Modica–Mortola theorem.** For $W(s)=s^2(1-s)^2$,
  $\int_\Omega(\varepsilon|\nabla u|^2/2+W(u)/\varepsilon)$
  Γ-converges in $L^1$ to $c_WP(E;\Omega)$ on $u=1_E$,
  and to infinity otherwise, where $c_W=\int_0^1\sqrt{2W(s)}ds$.

### Periodic and stochastic homogenization

Let $Y=(0,1)^d$ and $A(y)$ be bounded uniformly elliptic and $Y$-periodic.
Periodic correctors $\chi_i$ have mean zero and belong to $H^1_{\mathrm{per}}(Y)$.

The effective matrix is $A^{\mathrm{hom}}e_i=\int_Y A(y)(e_i+\nabla\chi_i)\,dy$, where $-\operatorname{div}_y(A(y)(e_i+\nabla\chi_i))=0$ periodically.

* **36.53. Elliptic homogenization.** Zero-Dirichlet solutions of
  $-\operatorname{div}(A(x/\varepsilon)\nabla u_\varepsilon)=f$,
  $f\in H^{-1}$, converge weakly in $H_0^1$ and strongly in $L^2$
  to the solution with coefficient $A^{\mathrm{hom}}$.
  Fluxes converge weakly in $L^2$ to $A^{\mathrm{hom}}\nabla u$.

* **36.58. Two-scale compactness.** Every bounded $L^2(\Omega)$ sequence
  has a subsequence with a two-scale limit in $L^2(\Omega\times Y)$,
  tested against $\phi(x,x/\varepsilon)$ with smooth compact
  spatial support and periodic second variable.

## 37. Geometric measure theory, BV, rectifiability, and currents

Hausdorff measure and dimension, differentiation, Rademacher, and injective equal-dimensional change of variables are covered. TauCeti adds finite Lipschitz parametrizations and a holomorphic area identity. The missing theory begins with multiplicities, coarea, BV structure, and rectifiability and extends to perimeter, currents, and varifolds. These are structural extensions of the available measure theory.

Sources: [mathematical synopsis](SYNOPSIS37.md); [combined coverage inventory](Mathlib37.md).

Hausdorff measure $\mathcal H^k$ is normalized to equal $k$-dimensional
Lebesgue measure on a $k$-plane; $\omega_k$ is the unit $k$-ball volume.
Measures are Radon, and rectifiability and boundary identities are understood
up to the appropriate measure-zero sets. Ambient space is $\mathbb R^n$
unless another space is specified.

### Hausdorff measure, dimension, and density

* **37.4. Frostman's lemma.** For a compact set $E$, positivity of its
  $s$-dimensional Hausdorff content is equivalent to existence of a
  nonzero finite measure supported on $E$ with
  $\mu(B(x,r))\leq Cr^s$. This characterizes lower bounds on dimension.

* **37.8. Projection dimension theorem.** For a Borel set $E$, almost
  every orthogonal projection to a $k$-plane has Hausdorff dimension
  $\min(k,\dim_HE)$. If $\dim_HE>k$, almost every such projection
  has positive $k$-dimensional measure.

### Rectifiable sets, tangents, and integration

A set is **countably $k$-rectifiable** if, outside an $\mathcal H^k$-null
set, it is covered by countably many Lipschitz images of subsets of
$\mathbb R^k$. It is **purely $k$-unrectifiable** if its intersection
with every such image has zero $\mathcal H^k$ measure.

* **37.11. Area formula.** For Lipschitz $f:\mathbb R^k\to\mathbb R^n$,
  measurable $A$, and nonnegative measurable $g$,
  $$
  \int_Ag(x)J_kf(x)dx
  =\int_{\mathbb R^n}\sum_{x\in A\cap f^{-1}(y)}g(x)d\mathcal H^k(y).
  $$
  Here $J_kf=\sqrt{\det(Df^TDf)}$; multiplicity cannot generally be omitted.

* **37.12. Coarea formula.** For Lipschitz $f:\mathbb R^n\to\mathbb R^k$,
  $k\leq n$,
  $\int gJ_kf\,dx=\int_{\mathbb R^k}\int_{f^{-1}(y)}
  g\,d\mathcal H^{n-k}dy$, with $J_kf=\sqrt{\det(DfDf^T)}$.

* **37.16. Preiss's density theorem.** If a Radon measure has a positive
  finite $k$-density at almost every point, it is a $k$-rectifiable
  measure: absolutely continuous with respect to $\mathcal H^k$
  on a countably $k$-rectifiable set.

* **37.19. Besicovitch–Federer projection theorem.** A set of finite
  $\mathcal H^k$ measure is purely $k$-unrectifiable exactly when
  almost every projection to a $k$-plane has zero $\mathcal H^k$ measure.

### BV functions, traces, and jump structure

A function $u\in L^1(\Omega)$ belongs to **$BV$** if its distributional
gradient $Du$ is a finite vector measure. Its variation is
$|Du|(\Omega)=\sup\{\int u\operatorname{div}\phi:
\phi\in C_c^1(\Omega;\mathbb R^n),\ |\phi|\leq1\}$.

* **37.22. BV compactness.** On a bounded Lipschitz domain, bounded sets
  in $BV$ are precompact in $L^1$. Their limits are BV and satisfy
  the variation liminf inequality.

* **37.25. Jump-set structure.** The approximate jump set $J_u$ is
  countably $(n-1)$-rectifiable and has two one-sided approximate
  values $u^\pm$ and normal $\nu_u$ almost everywhere.
  Approximate discontinuities outside $J_u$ form an
  $\mathcal H^{n-1}$-null set.

* **37.28. Coarea for BV.** For scalar $u$,
  $|Du|(\Omega)=\int_{\mathbb R}P(\{u>t\};\Omega)dt$.
  Almost every superlevel set therefore has finite perimeter.

### Sets of finite perimeter and geometric minimization

A measurable set has **finite perimeter** in $\Omega$ if
$1_E\in BV(\Omega)$, with $P(E;\Omega)=|D1_E|(\Omega)$.
Its **reduced boundary** $\partial^*E$ consists of points with a
measure-theoretic unit normal obtained by differentiation of $D1_E$.

* **37.34. De Giorgi structure theorem.** The reduced boundary is
  countably $(n-1)$-rectifiable and
  $D1_E=-\nu_E\mathcal H^{n-1}\!\restriction\partial^*E$.
  Thus perimeter is exactly reduced-boundary measure.

* **37.37. Gauss–Green theorem.** For $X\in C_c^1$,
  $\int_E\operatorname{div}X=\int_{\partial^*E}X\cdot\nu_E
  \,d\mathcal H^{n-1}$. Classical smooth boundaries are unnecessary.

* **37.43. Interior regularity of minimizing boundaries.** A locally
  perimeter-minimizing set has analytic minimal reduced boundary.
  The remaining interior boundary singular set has dimension at most
  $n-8$, and is empty for $n\leq7$, after taking the canonical
  representative of the set.

### Currents, compactness, and Plateau's problem

An **$m$-current** is a continuous linear functional on compactly supported
smooth $m$-forms. Its boundary is $\partial T(\omega)=T(d\omega)$.
Its **mass** $\mathbf M(T)$ is the dual norm for the comass norm on forms.
A current is **normal** if it and its boundary have finite mass, and
**integral** if it and its boundary are integer-multiplicity rectifiable currents.

* **37.50. Federer–Fleming compactness.** Integral currents supported in
  a fixed compact set, with uniformly bounded mass and boundary mass,
  have a subsequence converging weakly and in ambient flat norm to
  an integral current.

* **37.52. Plateau existence.** A compactly supported integral boundary
  $S$ in Euclidean space has an integral mass-minimizing filling
  $T$ with $\partial T=S$. A minimizer can be chosen supported
  in the convex hull of $\operatorname{supp}S$.

* **37.55. Higher-codimension interior regularity.** An area-minimizing
  integral $m$-current is locally a smooth minimal submanifold with
  integer multiplicity outside a singular set of Hausdorff dimension
  at most $m-2$. Branch points can occur in higher codimension.

### Varifolds and geometric regularity

An **$m$-varifold** is a Radon measure on
$\mathbb R^n\times G(n,m)$, with weight measure $\|V\|$.
Rectifiable varifolds integrate multiplicity over approximate tangent planes;
integer multiplicity makes them integral. Their first variation is
$\delta V(X)=\int\operatorname{div}_S X(x)dV(x,S)$.

* **37.57. Stationary monotonicity.** For a stationary varifold,
  $r^{-m}\|V\|(B_r(x))$ is nondecreasing while the balls remain
  interior. The difference of two ratios is an integral of squared
  normal radial components; constancy forces conical structure in the annulus.

* **37.60. Allard regularity.** Near an interior support point, an integral
  varifold with mass ratio close to one, sufficiently small tilt excess,
  and sufficiently small scaled
  $L^p$ mean curvature, $p>m$, is a multiplicity-one $C^{1,1-m/p}$
  graph on a smaller ball. The smallness threshold is dimensional
  and depends on $p$.

### Quantitative rectifiability and analytic capacity

A closed set is **$k$-Ahlfors regular** if
$C^{-1}r^k\leq\mathcal H^k(E\cap B(x,r))\leq Cr^k$
for $x\in E$ and $0<r<\operatorname{diam}E$.
It is **uniformly rectifiable** if every such ball captures a fixed
positive proportion of its measure in an $L$-Lipschitz image of a
$k$-ball of comparable radius, with uniform constants.

* **37.64. Analyst's traveling-salesman theorem.** A compact set
  $E\subset\mathbb R^n$ lies in a connected curve of finite length
  exactly when $\sum_Q\beta_\infty(E,3Q)^2\operatorname{diam}Q<\infty$,
  over dyadic cubes meeting $E$. The least containing-curve length
  is comparable to this sum plus $\operatorname{diam}E$.
  The beta number is normalized maximal distance to a best-fitting line.

* **37.65. Painlevé's problem for finite length.** If compact
  $E\subset\mathbb C$ has finite $\mathcal H^1$ measure, it is
  removable for bounded holomorphic functions exactly when it is
  purely unrectifiable. Equivalently its analytic capacity is zero.

## 38. Potential theory and capacity

Newtonian and logarithmic fundamental kernels, ball Green kernels, harmonic Harnack estimates, and classical maximum principles are available. The missing core is measure-valued potential representation, capacity and equilibrium, boundary regularity criteria, harmonic and Martin measures, and nonlinear potentials. The Poisson solution formula is listed in Section 32; existing kernel formulas alone do not solve the full boundary problem.

Sources: [mathematical synopsis](SYNOPSIS38.md); [combined coverage inventory](Mathlib38.md).

For Newtonian theory assume $n\geq3$ and use
$$
\Gamma(x)=\frac{|x|^{2-n}}{(n-2)|S^{n-1}|},\qquad -\Delta\Gamma=\delta_0.
$$
Thus $U^\mu=\Gamma*\mu$ and $I(\mu)=\iint\Gamma(x-y)d\mu(x)d\mu(y)$.
Planar logarithmic theory has its own normalization below. A property holds
**quasi-everywhere** when its exceptional set has zero capacity of the
specified kind. Domains are connected; boundary domains are bounded unless
another assumption is stated.

### Harmonic, subharmonic, and superharmonic functions

* **38.8. Distributional characterization.** A subharmonic function is
  upper semicontinuous, locally integrable, not identically $-\infty$,
  and satisfies the sub-mean inequality; equivalently its distributional
  Laplacian is a positive measure, with the canonical representative.
  Superharmonic functions have the opposite signs and lower semicontinuity.

* **38.9. Riesz decomposition.** A nonnegative superharmonic function on
  a Greenian domain has a unique decomposition $u=G\mu+h$,
  where $\mu=-\Delta u$, $h\geq0$ is harmonic, and $G\mu$
  is a Green potential. Local versions hold on relatively compact subdomains.

### Newtonian capacity, equilibrium, and thinness

For compact $K$ define
$\operatorname{Cap}(K)=\inf\{\int_{\mathbb R^n}|\nabla\phi|^2:
\phi\in C_c^\infty,\ \phi\geq1\text{ near }K\}$.
Extend first to open sets by compact exhaustion and then to arbitrary
sets by outer approximation.

* **38.15. Equilibrium measure.** If $K$ has positive capacity, there is
  a unique equilibrium charge $\nu_K$ supported on $K$ such that
  $\nu_K(K)=\operatorname{Cap}(K)$,
  $U^{\nu_K}=1$ quasi-everywhere on $K$, and $U^{\nu_K}\leq1$
  everywhere. Its energy is $I(\nu_K)=\operatorname{Cap}(K)$.
  For a zero-capacity compact set the capacitary measure and potential are zero.

* **38.18. Choquet properties.** Capacity is monotone, continuous on
  increasing sequences of sets and decreasing sequences of compact
  sets, and countably subadditive. Analytic sets, in particular Borel
  sets, are capacitable: outer capacity equals the supremum of compact
  subcapacities.

### The Dirichlet problem, harmonic measure, and ideal boundaries

* **38.26. Perron–Wiener solution.** Upper superharmonic and lower
  subharmonic envelopes agree for continuous boundary data on a bounded
  domain. Their common value is harmonic even if some boundary points
  are irregular.

* **38.28. Wiener's criterion.** For $n\geq3$, a boundary point $x_0$
  is regular exactly when
  $\sum_{k\geq1}2^{k(n-2)}\operatorname{Cap}(E_k)=\infty$,
  where $E_k=(\mathbb R^n\setminus\Omega)\cap
  \{2^{-k-1}\leq|x-x_0|\leq2^{-k}\}$.

* **38.31. Harmonic measure.** For each $x\in\Omega$, there is a
  probability measure $\omega^x$ on $\partial\Omega$ such that
  $H_f(x)=\int f\,d\omega^x$ for continuous $f$.
  Null sets of harmonic measure are independent of the pole in a
  connected domain.

* **38.34. Martin representation.** Fixing $x_*\in\Omega$, the normalized
  kernels $G(x,y)/G(x_*,y)$ define the Martin compactification.
  Every positive harmonic function has a unique representation as
  an integral of normalized minimal kernels over the minimal Martin
  boundary; the representing mass is $h(x_*)$.

### Sobolev capacity and nonlinear potential theory

For $1<p<\infty$, the relative **$p$-capacity** is
$\operatorname{cap}_p(K,\Omega)=\inf\int_\Omega|\nabla\phi|^p$,
over $\phi\in C_c^\infty(\Omega)$ at least one near $K$.
A **$p$-superharmonic function** is lower semicontinuous, finite on a
dense set, and satisfies comparison with continuous $p$-harmonic functions
on relatively compact subdomains.

* **38.44. Nonlinear Wiener criterion.** A boundary point $x_0$ is
  regular exactly when
  $$
  \int_0^{r_0}\left(
  \frac{\operatorname{cap}_p((\mathbb R^n\setminus\Omega)\cap\overline B_r(x_0),B_{2r}(x_0))}
       {\operatorname{cap}_p(\overline B_r(x_0),B_{2r}(x_0))}
  \right)^{1/(p-1)}\frac{dr}{r}=\infty.
  $$

* **38.46. Wolff potential estimates.** For $1<p<n$ define
  $\mathbf W_{1,p}^\mu(x,R)=\int_0^R
  (\mu(B_r(x))/r^{n-p})^{1/(p-1)}dr/r$.
  If $u\geq0$ is $p$-superharmonic and $-\Delta_pu=\mu$,
  then $\mathbf W_{1,p}^\mu(x,R)\leq Cu(x)$ and
  $u(x)\leq C\inf_{B_R(x)}u+C\mathbf W_{1,p}^\mu(x,2R)$
  when $B_{2R}(x)$ is interior.

### Logarithmic potentials and equilibrium in the plane

For compact $K\subset\mathbb C$, set
$I_{\log}(\mu)=\iint\log(1/|z-w|)d\mu(z)d\mu(w)$,
$V_K=\inf_{\mu\in\mathcal P(K)}I_{\log}(\mu)$, and
$\operatorname{cap}_{\log}(K)=e^{-V_K}$.

Whenever an equilibrium measure $\mu_K$ is used, assume $\operatorname{cap}_{\log}(K)>0$; $\mu_K$ minimizes $I_{\log}$ over probability measures on $K$.

* **38.54. Frostman's theorem.** The equilibrium potential satisfies
  $U^{\mu_K}_{\log}=V_K$ quasi-everywhere on $K$ and
  $U^{\mu_K}_{\log}\leq V_K$ everywhere in the plane.

* **38.57. Transfinite diameter.**
  $\lim_{N\to\infty}\max_{z_1,\ldots,z_N\in K}
  \prod_{i<j}|z_i-z_j|^{2/(N(N-1))}=\operatorname{cap}_{\log}(K)$.

* **38.59. Weighted equilibrium.** For a lower semicontinuous
  external field $Q:K\to\mathbb R\cup\{\infty\}$ on compact $K$,
  with a finite weighted-energy competitor,
  $I_{\log}(\mu)+2\int Qd\mu$ has a unique minimizer.
  Its potential satisfies $U^\mu_{\log}+Q\geq F$ quasi-everywhere
  on $K$ and equality $\mu$-almost everywhere, for a constant $F$.

## 39. Metric measure spaces, Dirichlet forms, heat kernels, optimal transport, and fractals

Optimal-plan existence, compact-space duality, Wasserstein completeness and convergence, Kantorovich–Rubinstein duality, and one-dimensional optimal rearrangement are covered. The general duality gap in 39.36 is the Polish-space extension. Brenier’s theorem still requires removal of an assumed dual certificate. Dirichlet forms, metric differentiation, heat-kernel characterizations, synthetic curvature, gradient flows, and fractal energy theories remain missing.

Sources: [mathematical synopsis](SYNOPSIS39.md); [combined coverage inventory](Mathlib39.md).

Unless specified otherwise, $(X,d,m)$ is complete and separable, $m$ is a
Radon measure of full support, and $0<m(B(x,r))<\infty$. Write
$V(x,r)=m(B(x,r))$. A measure is **doubling** if
$V(x,2r)\leq C_DV(x,r)$. A space is **Ahlfors $Q$-regular** if
$V(x,r)\asymp r^Q$ for $0<r<\operatorname{diam}X$.
All comparison constants are uniform on the scales under consideration.

### Upper gradients and metric Sobolev spaces

A Borel function $g\geq0$ is an **upper gradient** of $u$ if
$|u(\gamma(b))-u(\gamma(a))|\leq\int_\gamma g\,ds$ for every
rectifiable curve. The **$p$-modulus** of a curve family is
$$
\operatorname{Mod}_p\Gamma=\inf\left\{\int\rho^p\,dm:
\rho\geq0,\ \int_\gamma\rho\,ds\geq1\quad(\gamma\in\Gamma)\right\}.
$$
A **$p$-weak upper gradient** may fail on a family of zero $p$-modulus.
The **Newtonian space** $N^{1,p}(X)$ has norm
$\|u\|_{N^{1,p}}^p=\|u\|_p^p+\inf_g\|g\|_p^p$, with the
usual identification of zero-norm differences. A **$(1,p)$-Poincaré
inequality** means
$$
\fint_B|u-u_B|\,dm\leq Cr_B\left(\fint_{\lambda B}g^p\,dm\right)^{1/p}.
$$

* **39.4. Minimal upper gradients.** For $1\leq p<\infty$, every Newtonian
  function has a minimal $p$-weak upper gradient $g_u\in L^p$,
  unique almost everywhere and bounded above almost everywhere by every
  other $L^p$ weak upper gradient.

* **39.13. Cheeger differentiation.** A complete doubling Poincaré space
  admits countably many measurable charts of uniformly bounded finite
  dimension in which every real Lipschitz function has an almost
  everywhere unique measurable differential.

### Dirichlet forms and symmetric processes

A **Dirichlet form** $(\mathcal E,\mathcal F)$ is a densely defined
closed nonnegative symmetric form on $L^2(m)$ with the Markov property:
normal contractions decrease energy. It is **regular** on a locally compact
separable space if $\mathcal F\cap C_c(X)$ is dense in both $\mathcal F$
for $\mathcal E_1=\mathcal E+\|\cdot\|_2^2$ and $C_0(X)$ uniformly.
It is **strongly local** if $\mathcal E(u,v)=0$ whenever $u$ is constant
near the compact support of $v$.

* **39.15. Form–operator correspondence.** A closed nonnegative form
  determines a unique nonnegative self-adjoint operator $A$ with
  $\mathcal F=D(A^{1/2})$ and
  $\mathcal E(u,v)=\langle A^{1/2}u,A^{1/2}v\rangle$.
  Its semigroup is $P_t=e^{-tA}$.

* **39.16. Beurling–Deny criterion.** The Markov property of the form
  is equivalent to $P_t$ being positivity preserving and
  $0\leq P_tf\leq1$ whenever $0\leq f\leq1$.
  Thus Dirichlet forms and symmetric sub-Markov semigroups correspond.

* **39.19. Process representation.** Every regular Dirichlet form has
  an associated symmetric Hunt process, unique up to the appropriate
  capacity-zero exceptional sets. Its transition semigroup represents
  $P_t$ using quasi-continuous versions.

* **39.20. Beurling–Deny decomposition.** A regular symmetric form
  decomposes uniquely into a strongly local energy, a symmetric jump
  energy off the diagonal, and a nonnegative killing measure.
  Strong locality excludes both jump and killing parts.

### Heat kernels, inequalities, and curvature

When $P_t$ has a density write
$P_tf(x)=\int p_t(x,y)f(y)\,dm(y)$. In the diffusion estimates below,
the **intrinsic distance** is the distance obtained from form functions
with $d\Gamma(u)\leq dm$. Compatibility of that distance with the topology
and completeness are explicit assumptions, not automatic consequences of regularity.

The diffusion setting in 39.29 assumes a regular strongly local Dirichlet form with a complete intrinsic metric inducing the topology, and the usual cutoff/locality hypotheses for the intrinsic balls. The Poincaré inequality is the local scale-invariant $L^2$ inequality for its energy measure $\Gamma$.

* **39.29. Parabolic Harnack equivalence.** In this diffusion setting,
  doubling plus Poincaré is equivalent to the scale-invariant parabolic
  Harnack inequality. Positive caloric functions on a cylinder are bounded
  above on an earlier interior subcylinder by their infimum on a later one.

### Optimal transportation and Wasserstein geometry

For probability measures $\mu,\nu$, a **coupling** is a probability
measure $\pi$ on $X\times X$ with these marginals; write $\Pi(\mu,\nu)$.
The Kantorovich cost is $\inf_{\pi\in\Pi}\int c\,d\pi$.
For $1\leq p<\infty$, $\mathcal P_p(X)$ consists of probabilities
with finite $p$th moment and
$W_p(\mu,\nu)^p=\inf_\pi\int d(x,y)^p\,d\pi$.
The Monge problem restricts to couplings $(\mathrm{id},T)_\#\mu$.

* **39.36. Kantorovich duality.** For lower semicontinuous nonnegative
  costs, the primal value equals
  $\sup_{\phi(x)+\psi(y)\leq c(x,y)}(\int\phi\,d\mu+\int\psi\,d\nu)$
  in the standard integrable dual class. For compact spaces and continuous
  costs, optimal continuous potentials exist.

* **39.42. Brenier's theorem.** For $\mu,\nu\in\mathcal P_2(\mathbb R^n)$
  with $\mu$ absolutely continuous, the quadratic optimal plan is unique
  and induced by $T=\nabla\phi$, with $\phi$ convex and $T$
  unique $\mu$-almost everywhere.

* **39.45. Benamou–Brenier formula.** On $\mathbb R^n$,
  $$
  W_2(\mu_0,\mu_1)^2=\inf\int_0^1\int|v_t|^2\,d\mu_t\,dt,
  \qquad \partial_t\mu_t+\nabla\cdot(v_t\mu_t)=0,
  $$
  over distributional solutions with the prescribed endpoints.

* **39.47. Displacement convexity.** On $\mathbb R^n$, for convex
  $U$ with $U(0)=0$, $\mu\mapsto\int U(\rho)dx$ is displacement convex if
  $s\mapsto s^nU(s^{-n})$ is convex and nonincreasing, with the
  usual lower semicontinuous extension to singular measures.
  Entropy and powers $U(r)=r^q/(q-1)$, $q>1$, are examples.

* **39.49. Ricci curvature and entropy.** On a complete weighted manifold
  $m=e^{-V}\mathrm{vol}$, $\operatorname{Ric}+D^2V\geq K$
  is equivalent to $K$-displacement convexity of relative entropy.
  This motivates the synthetic condition $CD(K,\infty)$.

### Metric gradient flows and synthetic diffusion

For a lower semicontinuous energy $F$, its **descending slope** is
$|\partial F|(x)=\limsup_{y\to x}(F(x)-F(y))_+/d(x,y)$.
The implicit step minimizes $F(y)+d(y,x)^2/(2\tau)$.
An **$EVI_\lambda$ flow** obeys, for every admissible comparison point $v$,
$$
\frac12\frac d{dt}d(u_t,v)^2+\frac\lambda2d(u_t,v)^2+F(u_t)\leq F(v).
$$

* **39.53. EVI uniqueness and contraction.** Two $EVI_\lambda$ flows
  satisfy $d(u_t,v_t)\leq e^{-\lambda t}d(u_0,v_0)$.
  They are unique and, when defined for all initial data, form a semigroup.

* **39.55. Wasserstein minimizing movements.** A proper lower semicontinuous
  energy on $\mathcal P_2(\mathbb R^n)$, $\lambda$-convex along
  generalized geodesics, generates an $EVI_\lambda$ flow if its
  penalized minimization problems attain their infima for all sufficiently
  small steps. The transport implicit scheme converges to this flow.

* **39.59. Riemannian synthetic curvature.** On an $RCD(K,\infty)$ probability space,
  namely a $CD(K,\infty)$ space with quadratic Cheeger energy,
  $L^2$ heat flow agrees with the $EVI_K$ entropy flow in $W_2$.
  It contracts $W_2$ by $e^{-Kt}$ for finite-second-moment initial
  measures, starting first with finite entropy and extending by closure.

### Networks, resistance, and fractal diffusion

A weighted graph has symmetric conductances $b(x,y)\geq0$,
$b(x,x)=0$, $\sum_yb(x,y)<\infty$, vertex masses $m(x)>0$,
and possibly killing $c(x)\geq0$. Its energy and formal Laplacian are
$$
\mathcal E(u)=\frac12\sum_{x,y}b(x,y)|u(x)-u(y)|^2+
\sum_xc(x)|u(x)|^2,\qquad
Au(x)=\frac{\sum_yb(x,y)(u(x)-u(y))+c(x)u(x)}{m(x)}.
$$
A **resistance form** is a Markov energy on pointwise functions, Hilbert
modulo constants, separating points, with finite effective resistances.
The **walk dimension** $d_w$ describes time scale $r^{d_w}$; the
volume dimension $d_f$ describes $V(x,r)\asymp r^{d_f}$.

* **39.66. Resistance-form realization.** A regular resistance form on
  a locally compact resistance space, together with a full-support
  Radon measure, gives a regular Dirichlet form by closure on $L^2$.
  A local resistance form yields a diffusion.

* **39.67. Self-similar attractors.** A finite family of strict contractions
  has a unique nonempty compact invariant set, the fixed point of the
  union map on compact sets with the Hausdorff metric. Positive weights
  summing to one similarly determine a unique invariant probability measure.

* **39.68. Similarity dimension.** For Euclidean similarities with ratios
  $r_i$ satisfying the open set condition, the attractor has Hausdorff
  and box dimensions $s$ determined by $\sum_i r_i^s=1$,
  and $0<\mathcal H^s(K)<\infty$.

* **39.71. Sub-Gaussian kernels.** Conservative gasket diffusion satisfies, at small
  times and in its Euclidean metric, with $\Phi=(d(x,y)^{d_w}/t)^{1/(d_w-1)}$,
  $$
  c_1t^{-d_f/d_w}e^{-c_2\Phi}\leq p_t(x,y)
  \leq c_3t^{-d_f/d_w}e^{-c_4\Phi}.
  $$
  All four constants are strictly positive and independent of $t,x,y$.

## 40. One complex variable — graduate courses

Classical one-variable analysis is comparatively well covered: Cauchy theory, residues, Rouché, Hurwitz, locally bounded Montel, monodromy, Schwarz–Pick, and Riemann mapping are available. The selected omissions are annular Laurent expansion, Picard, approximation, and prescribed divisors. A local finite meromorphic principal part is a weaker statement than the Laurent theorem selected here.

Sources: [mathematical synopsis](SYNOPSIS40.md); [combined coverage inventory](Mathlib40.md).

A **domain** $\Omega\subset\mathbb C$ is nonempty, connected, and open.
Write $\mathcal O(\Omega)$ for its holomorphic functions,
$\mathbb D=\{|z|<1\}$, and $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$.
Contours and cycles are piecewise $C^1$ unless otherwise specified.
The winding number is
$\operatorname{Ind}(\gamma,a)=(2\pi i)^{-1}\int_\gamma dz/(z-a)$.
Convergence in $\mathcal O(\Omega)$ means uniform convergence on compact sets.

### Isolated singularities, residues, and counting

A function is **meromorphic** if it is holomorphic except at isolated
poles, equivalently a holomorphic map into $\widehat{\mathbb C}$ that is
not constantly infinity. The **residue** is the coefficient of $(z-a)^{-1}$
in its Laurent expansion.

* **40.25. Laurent expansion.** A holomorphic function on
  $r<|z-a|<R$ has a unique Laurent series, normally convergent
  on compact subannuli, with coefficients given by contour integrals
  over any intervening circle.

* **40.29. Great Picard theorem.** Near an essential singularity a
  holomorphic function takes every complex value infinitely often
  with at most one exception. For meromorphic functions the corresponding
  statement on the sphere permits at most two exceptions.

### Approximation, prescribed data, and continuation

* **40.57. Runge approximation on compact sets.** If $K\subset\mathbb C$
  is compact and $f$ is holomorphic near $K$, it is uniformly
  approximable there by rational functions with poles in any prescribed
  set meeting every component of $\widehat{\mathbb C}\setminus K$.
  A pole at infinity means a polynomial part.

* **40.59. Mergelyan's theorem.** If compact $K\subset\mathbb C$ has
  connected complement, every continuous function on $K$ holomorphic
  on its interior is uniformly approximable by polynomials.

* **40.60. Mittag–Leffler theorem.** On a plane domain, arbitrarily
  prescribed finite principal parts at a discrete set are the principal
  parts of a meromorphic function having no other poles.

* **40.61. Weierstrass zero theorem.** Any discrete set in a plane domain,
  with assigned positive integer multiplicities, is exactly the zero
  divisor of a holomorphic function there.

## 41. Classical function theory — entire and meromorphic functions, value distribution

Zero and pole counting, parts of the first-main-theorem framework, local meromorphic data, and Herglotz/Pick representation are present. The missing core is global entire factorization and growth, completed value-distribution estimates, normal-family rescaling, and maximum-term asymptotics. Picard itself is listed in Section 40 rather than repeated as a consequence of value distribution.

Sources: [mathematical synopsis](SYNOPSIS41.md); [combined coverage inventory](Mathlib41.md).

Functions are nonconstant unless otherwise indicated. Zeros and poles are
counted with multiplicity, except where a bar denotes reduced counting.
For entire $f$, put $M(r,f)=\max_{|z|=r}|f(z)|$ and define its **order**
and, when $0<\rho<\infty$, its **type** by
$$
\rho=\limsup_{r\to\infty}\frac{\log\log M(r,f)}{\log r},\qquad
\tau=\limsup_{r\to\infty}\frac{\log M(r,f)}{r^\rho}.
$$
An entire function is of **exponential type at most $\sigma$** if
$|f(z)|\leq C_\varepsilon e^{(\sigma+\varepsilon)|z|}$ for every
$\varepsilon>0$. This includes order below one.

### Growth, zeros, and canonical products

* **41.10. Hadamard factorization.** An entire function of finite order
  $\rho$ admits a fixed-genus factorization $z^me^{Q(z)}P(z)$
  with $Q$ polynomial of degree at most $\rho$ and $P$ a
  canonical product of genus at most $\lfloor\rho\rfloor$.

### Angular growth and exponential type

For an entire function of order $\rho>0$ and finite type, its
**indicator** is $h(\theta)=\limsup_{r\to\infty}
r^{-\rho}\log|f(re^{i\theta})|$.
The **Cartwright class** consists of exponential-type entire functions with
$\int_{\mathbb R}\log^+|f(x)|/(1+x^2)\,dx<\infty$.
Write $PW_\sigma$ for exponential-type-at-most-$\sigma$ entire functions
whose restrictions to $\mathbb R$ lie in $L^2$.

* **41.23. Cartwright zero distribution.** Put
  $\sigma_+=h(\pi/2)$ and $\sigma_-=h(-\pi/2)$.
  A Cartwright function has
  $n(r)=(\sigma_++\sigma_-)r/\pi+o(r)$, and only $o(r)$ zeros
  outside any fixed pair of sectors about the positive and negative
  real axes. Multiplicities are included.

### The second main theorem, defects, and uniqueness

Here $f$ is transcendental meromorphic on $\mathbb C$.
Write $S(r,f)=O(\log^+T(r,f)+\log r)$ outside a set of finite
linear measure; in particular $S=o(T)$ there. For finite-order
functions the logarithmic derivative estimate improves to $O(\log r)$.

Here $m(r,f)=(2\pi)^{-1}\int_0^{2\pi}\log^+|f(re^{it})|\,dt$,
$N(r,\infty;f)=\int_0^r[n(t,\infty;f)-n(0,\infty;f)]\,dt/t+n(0,\infty;f)\log r$,
and $T(r,f)=m(r,f)+N(r,\infty;f)$. For finite $a$, use the zeros of $f-a$ to define $N(r,a;f)$ and use $m(r,1/(f-a))$ for proximity. A bar over $N$ counts each preimage once.

* **41.35. Logarithmic derivative lemma.**
  $m(r,f'/f)=S(r,f)$. More generally
  $m(r,f^{(k)}/f)=S(r,f)$ for each fixed positive integer $k$.

* **41.37. Second main theorem.** For distinct fixed spherical values
  $a_1,\ldots,a_q$, $q\geq3$,
  $$
  (q-2)T(r,f)\leq\sum_{j=1}^q\overline N(r,a_j;f)+S(r,f).
  $$
  Reduced counting makes ramification part of the inequality.

* **41.44. Five-value theorem.** If two nonconstant meromorphic
  functions on $\mathbb C$ have the same preimage sets for five
  distinct spherical values, ignoring multiplicity, they are identical.

### Normality, rescaling, and uniqueness sets

The spherical metric is the natural metric at poles. A family is
**normal** if every sequence has a locally spherically convergent subsequence
with meromorphic or constant-infinity limit.

* **41.48. Zalcman's rescaling lemma.** Failure of normality at $z_0$
  yields $f_j$, $z_j\to z_0$, and $r_j\downarrow0$ such that
  $f_j(z_j+r_jz)$ converges locally spherically on $\mathbb C$
  to a nonconstant meromorphic function with bounded spherical derivative.

### Growth methods for complex differential equations

A **differential polynomial** in $f$ is a polynomial in
$f,f',\ldots,f^{(k)}$ with specified meromorphic coefficients.
Such coefficients are called **small** relative to $f$ when their
characteristics are $o(T(r,f))$ outside the stated exceptional set.

For $f(z)=\sum_na_nz^n$, the **central index** $\nu(r)$ is the largest index maximizing $|a_n|r^n$.

* **41.55. Wiman–Valiron approximation.** For a transcendental entire
  series, let $\nu(r)$ be its central index and choose
  $|z_r|=r$, $|f(z_r)|=M(r)$.
  Outside radii of finite logarithmic measure, for each fixed $k$,
  $f^{(k)}(z_r)\sim(\nu(r)/z_r)^kf(z_r)$.
  Local versions hold in appropriately shrinking disks about $z_r$.

## 42. Hardy, Bergman, and model spaces; operators on analytic function spaces

General RKHS constructions and Herglotz representation are covered, while the analytic Hardy, Bergman, Dirichlet, and model-space theories are largely missing. The selection emphasizes boundary realization, factorization, interpolation, corona and Carleson theorems, analytic operator theory, and projection estimates. These are assertions about specific function spaces and norms, not merely abstract positive kernels.

Sources: [mathematical synopsis](SYNOPSIS42.md); [combined coverage inventory](Mathlib42.md).

Put $\mathbb T=\partial\mathbb D$, $dm=dt/(2\pi)$ on $\mathbb T$,
and $dA_0=dx\,dy/\pi$ on $\mathbb D$. For $0<p<\infty$,
$$
H^p=\left\{f\in\mathcal O(\mathbb D):
\|f\|_p^p=\sup_{r<1}\int_{\mathbb T}|f(r\zeta)|^pdm(\zeta)<\infty\right\};
$$
$H^\infty$ has the supremum norm. For $\alpha>-1$,
$A_\alpha^p=\mathcal O(\mathbb D)\cap L^p(dA_\alpha)$, where
$dA_\alpha=(\alpha+1)(1-|z|^2)^\alpha dA_0$.
Inner products are linear in the first variable.

### Hardy spaces, boundary values, and factorization

An **inner function** is a bounded holomorphic function with boundary
modulus one almost everywhere. An **outer function** is, up to a unimodular
constant,
$\exp\int_{\mathbb T}(\zeta+z)/(\zeta-z)\log h(\zeta)dm(\zeta)$,
where $h>0$, $\log h\in L^1$, with the additional integrability
required by the space under consideration.

* **42.1. Boundary realization.** Every $f\in H^p$, $0<p<\infty$,
  has nontangential limits $f^*$ almost everywhere,
  $\|f\|_p=\|f^*\|_{L^p}$, and $f(r\cdot)\to f^*$ in $L^p$.
  For $p=\infty$, boundary limits identify the supremum and essential-supremum norms.

* **42.6. Canonical factorization.** Every nonzero $f\in H^p$ has
  a factorization $f=BS_\mu O$, unique up to unimodular constants,
  where $B$ is Blaschke, $O$ is outer, and
  $S_\mu(z)=\exp[-\int(\zeta+z)/(\zeta-z)d\mu(\zeta)]$
  for a finite positive singular measure $\mu$.

* **42.10. F. and M. Riesz theorem.** A finite complex measure on
  $\mathbb T$ whose negative Fourier coefficients vanish is
  absolutely continuous, with density in $H^1$.

* **42.15. Beurling's invariant-subspace theorem.** Every nonzero closed
  subspace of $H^2$ invariant under multiplication by $z$ is
  $\theta H^2$ for an inner $\theta$, unique up to a unimodular constant.

### Carleson measures, BMO, and interpolation

For an arc $I$ of normalized length $|I|$, let
$S(I)=\{r\zeta:\zeta\in I,\ 1-|I|<r<1\}$.
A finite positive measure is **Carleson** if $\mu(S(I))\leq C|I|$.
The analytic space **BMOA** consists of $H^1$ functions whose boundary
values have bounded mean oscillation; **VMOA** uses vanishing mean oscillation.

* **42.18. Carleson embedding theorem.** For every $0<p<\infty$,
  $\int_{\mathbb D}|f|^pd\mu\leq C\|f\|_{H^p}^p$ for all
  $f\in H^p$ exactly when $\mu$ is Carleson.

* **42.22. Carleson interpolation theorem.** A sequence of distinct
  $a_j\in\mathbb D$ interpolates every bounded scalar sequence
  by an $H^\infty$ function exactly when
  $\inf_j\prod_{k\ne j}|(a_j-a_k)/(1-\bar a_ka_j)|>0$.

* **42.24. Nevanlinna–Pick theorem.** Given distinct $z_i\in\mathbb D$
  and prescribed $w_i$, a function $f$ with $\|f\|_\infty\leq1$
  and $f(z_i)=w_i$ exists exactly when
  $[(1-w_i\bar w_j)/(1-z_i\bar z_j)]$ is positive semidefinite.

* **42.25. Corona theorem.** If $f_1,\ldots,f_n\in H^\infty$ and
  $\sum|f_j(z)|\geq\delta>0$ throughout $\mathbb D$, there
  are $g_j\in H^\infty$ with $\sum f_jg_j=1$.
  The bounds depend only on the stated data.

### Toeplitz and Hankel operators

For $\phi\in L^\infty(\mathbb T)$ define
$T_\phi f=P_+(\phi f)$ on $H^2$ and
$H_\phi f=(I-P_+)(\phi f)$ with values in
$H^2_-=L^2\ominus H^2$.

$P_+$ is the orthogonal projection from $L^2(\mathbb T)$ onto the nonnegative Fourier modes $H^2$.

* **42.30. Toeplitz Fredholm index.** If $\phi\in C(\mathbb T)$,
  $T_\phi$ is Fredholm exactly when $\phi$ never vanishes;
  its index is $-\operatorname{wind}(\phi,0)$ and its essential
  spectrum is $\phi(\mathbb T)$.

* **42.31. Nehari's theorem.** Every bounded Hankel matrix has a bounded
  symbol, and $\|H_\phi\|=\operatorname{dist}_{L^\infty}(\phi,H^\infty)$.

### Bergman and Bloch spaces

The **Bloch space** consists of holomorphic $g$ with
$\|g\|_{\mathcal B}=|g(0)|+\sup_z(1-|z|^2)|g'(z)|<\infty$;
the **little Bloch space** has the weighted derivative tending to zero
at the boundary.

* **42.46. Bergman kernel.** $A_\alpha^2$ has kernel
  $K_\alpha(z,w)=(1-z\bar w)^{-\alpha-2}$.
  For $\alpha=0$, the normalized monomials are $\sqrt{n+1}z^n$.

* **42.47. Bergman projection.**
  $P_\alpha f(z)=\int K_\alpha(z,w)f(w)dA_\alpha(w)$
  is the orthogonal projection on $L^2(dA_\alpha)$ and extends
  boundedly from $L^p(dA_\alpha)$ onto $A_\alpha^p$ for $1<p<\infty$.

### Dirichlet and de Branges–Rovnyak spaces

Use the Dirichlet norm
$\|f\|_{\mathcal D}^2=\|f\|_{H^2}^2+\int|f'|^2dA_0
=\sum_{n\geq0}(n+1)|a_n|^2$.
For $b\in H^\infty$, $\|b\|_\infty\leq1$, the space
$\mathcal H(b)$ is the range of $(I-T_bT_b^*)^{1/2}$ with its
range norm: the norm of the least-norm preimage.

* **42.60. Stegenga's embedding theorem.** A finite positive measure
  embeds $\mathcal D$ into $L^2(\mu)$ exactly when
  $\mu(\bigcup_jS(I_j))\leq C\operatorname{Cap}(\bigcup_j I_j)$
  for all finite families of disjoint boundary arcs. Here
  $\operatorname{Cap}$ is the boundary Sobolev capacity of order
  $1/2$, comparable to the reciprocal of the minimum probability
  energy for the kernel $\log(e/|\zeta-\eta|)$ on the set.
  It is not the exponential logarithmic capacity used for planar compact sets.

### Composition operators

For a holomorphic self-map $\phi$ of the disk, let $C_\phi f=f\circ\phi$.

* **42.70. Shapiro compactness criterion.** Define
  $N_\phi(w)=\sum_{\phi(z)=w}\log(1/|z|)$ with multiplicity,
  away from $\phi(0)$. Then $C_\phi$ is compact on $H^2$
  exactly when $N_\phi(w)/\log(1/|w|)\to0$ as $|w|\to1$.

### Fock spaces and planar sampling

For $\alpha>0$, the **Fock space** $\mathcal F_\alpha^2$ consists
of entire functions square-integrable for
$d\lambda_\alpha=(\alpha/\pi)e^{-\alpha|z|^2}dx\,dy$.
For a separated sequence $\Lambda\subset\mathbb C$, define
$D^\pm(\Lambda)=\lim_{R\to\infty}\{\inf,\sup\}_{z\in\mathbb C}
\#(\Lambda\cap B(z,R))/(\pi R^2)$, respectively using lower
and upper limits if necessary.

The sampling norm is $\sum_{\lambda\in\Lambda}|f(\lambda)|^2e^{-\alpha|\lambda|^2}$.

* **42.77. Fock sampling density.** A separated $\Lambda$ gives a
  sampling norm equivalent to $\|f\|^2$ exactly when
  $D^-(\Lambda)>\alpha/\pi$. The strict inequalities distinguish
  sampling and interpolation even for regular lattices.

## 43. Univalent functions, conformal mapping, and extremal methods

Riemann mapping, Schwarz–Pick, substantial Schwarz–Christoffel constructions, continuous Jordan-domain boundary extension, and length–area estimates are covered. The major gaps are coefficient geometry, distortion, extremal length, Loewner evolution, and prime ends. In 43.48 the missing conclusion is the unconditional homeomorphism of closures; the recorded injectivity upgrade assumes a boundary-fibre condition.

Sources: [mathematical synopsis](SYNOPSIS43.md); [combined coverage inventory](Mathlib43.md).

A function is **univalent** if it is holomorphic and injective.
Let $\mathcal S$ consist of univalent
$f(z)=z+a_2z^2+\cdots$ on $\mathbb D$, and let $\Sigma$ consist
of univalent $g(z)=z+b_0+b_1z^{-1}+\cdots$ on $|z|>1$.
The **Koebe function** is $k(z)=z/(1-z)^2$.
All conformal maps preserve orientation.

### Schlicht functions and sharp distortion

* **43.1. Grönwall area theorem.** If $g\in\Sigma$, then
  $\sum_{n\geq1}n|b_n|^2\leq1$. The area of the omitted compact
  set is $\pi(1-\sum n|b_n|^2)$.

* **43.3. Koebe quarter theorem.** Every $f\in\mathcal S$ maps
  $\mathbb D$ onto a domain containing $B(0,1/4)$.
  The constant $1/4$ is sharp.

* **43.5. Distortion theorem.** For $f\in\mathcal S$ and $|z|=r$,
  $(1-r)/(1+r)^3\leq|f'(z)|\leq(1+r)/(1-r)^3$.

* **43.8. de Branges's theorem.** For $f\in\mathcal S$,
  $|a_n|\leq n$ for every $n\geq2$. Equality for any such $n$
  forces a Koebe rotation.

### Loewner theory and the Schwarzian

A **radial Loewner chain** is an increasing family of univalent maps
$f_t$, $f_t(0)=0$, $f_t'(0)=e^t$, with the usual local absolute
continuity in time. A **half-plane hull** $K$ is a bounded relatively
closed subset of $\mathbb H$ whose complement is simply connected.

The **Schwarzian derivative** is $Sf=f'''/f'-\tfrac32(f''/f')^2$.

* **43.21. Loewner–Kufarev equation.** Such a radial chain satisfies
  $\partial_tf_t(z)=zf_t'(z)p(z,t)$ almost everywhere in $t$,
  where $p(\cdot,t)$ is holomorphic, $\Re p\geq0$, and $p(0,t)=1$.

* **43.31. Nehari sufficient bound.** A locally univalent meromorphic
  function on $\mathbb D$ with
  $\sup_z(1-|z|^2)^2|Sf(z)|\leq2$ is univalent.

### Extremal length, moduli, and capacities

For a family $\Gamma$ of rectifiable curves in a plane domain, define
$$
\Lambda(\Gamma)=\sup_{\rho\geq0}
\frac{(\inf_{\gamma\in\Gamma}\int_\gamma\rho\,ds)^2}
{\iint\rho^2dA},
$$
using Borel metrics of finite positive area. Its reciprocal is the
$2$-modulus of the curve family. For a simply connected proper domain
$D$ and $a\in D$, the **conformal radius** is $r_D(a)=|f'(0)|$
for $f:\mathbb D\to D$, $f(0)=a$.

* **43.33. Conformal invariance.** Extremal length is unchanged by a
  conformal map, because metric lengths and metric areas transform
  with matching derivative factors.

### Boundary correspondence and harmonic measure

Prime ends describe boundary approaches by nested crosscuts. For a
simply connected proper domain they form the natural boundary circle.
For bounded $D$, **harmonic measure** $\omega_D^a$ represents the
harmonic extension functional at $a$.

* **43.46. Prime-end correspondence.** A Riemann map extends to a
  homeomorphism from the closed disk to the prime-end compactification
  of its image domain. A singleton prime-end impression gives an
  ordinary boundary limit at the corresponding circle point.

* **43.48. Jordan correspondence.** For a Jordan domain, this extension
  is a homeomorphism. Local connectivity alone permits different
  circle points to have the same boundary image.

## 44. Riemann surfaces, quasiconformal mappings, and Teichmüller theory

Particular Fuchsian-quotient surfaces and local mapping multiplicities are covered. The missing core is global surface uniformization, divisor and period theory, Beltrami solvability, quasiconformal distortion, and Teichmüller geometry. Local multiplicity under composition does not supply Riemann–Hurwitz, and constructing quotient atlases does not supply uniformization of arbitrary surfaces.

Sources: [mathematical synopsis](SYNOPSIS44.md); [combined coverage inventory](Mathlib44.md).

A **Riemann surface** is a connected, second-countable Hausdorff
one-dimensional complex manifold. An **open surface** means a noncompact
surface without boundary. Unless otherwise stated, compact surfaces have
no boundary and genus $g$. Holomorphic $1$-forms are sections of the
canonical bundle $K_X$; quadratic differentials are sections of $K_X^2$.
The detailed Teichmüller statements below concern closed oriented surfaces
of genus $g\geq2$, with the torus case stated separately.

### Holomorphic maps, coverings, and uniformization

* **44.3. Riemann–Hurwitz formula.** For a nonconstant holomorphic map $f:X\to Y$ between compact Riemann surfaces, of degree $d$ and local degrees $e_x$,
  $2g_X-2=d(2g_Y-2)+\sum_{x\in X}(e_x-1)$.

* **44.7. Uniformization.** Every simply connected Riemann surface is
  biholomorphic to exactly one of $\widehat{\mathbb C}$,
  $\mathbb C$, and $\mathbb D$. General surfaces are quotients
  of these universal covers by freely acting deck groups.

### Divisors, line bundles, and Riemann–Roch

A **divisor** is a finite integral sum $D=\sum n_pp$; its degree
is $\sum n_p$. A **principal divisor** is $(f)$ for a nonzero
meromorphic function. Set
$L(D)=\{f:(f)+D\geq0\}\cup\{0\}$ and $\ell(D)=\dim L(D)$.
The line bundle $\mathcal O(D)$ has these meromorphic functions as
its holomorphic sections.

* **44.12. Riemann–Roch theorem.**
  $\ell(D)-\ell(K_X-D)=\deg D+1-g$.
  Equivalently, $h^0(L)-h^1(L)=\deg L+1-g$ for a line bundle $L$.

* **44.13. Serre duality.** $H^1(X,L)$ is naturally dual to
  $H^0(X,K_X\otimes L^{-1})$, through integration or residue pairing.

### Harmonic forms, periods, and the Jacobian

In this subsection assume $g\geq1$.
Choose a symplectic homology basis $a_1,b_1,\ldots,a_g,b_g$.
Normalize holomorphic forms by $\int_{a_j}\omega_i=\delta_{ij}$
and set $\tau_{ij}=\int_{b_j}\omega_i$.

Write $A_j(\alpha)=\int_{a_j}\alpha$, $B_j(\alpha)=\int_{b_j}\alpha$, and $J(X)=\mathbb C^g/(\mathbb Z^g+\tau\mathbb Z^g)$ for the Jacobian.

* **44.26. Riemann bilinear relations.** For closed $1$-forms,
  $\int_X\alpha\wedge\beta=\sum_j(A_j(\alpha)B_j(\beta)
  -B_j(\alpha)A_j(\beta))$. Applied to holomorphic forms and their
  conjugates, this gives the normalization and positivity relations.

* **44.28. Abel's theorem.** A degree-zero divisor $D=\sum n_pp$
  is principal exactly when
  $\sum n_p\int_{p_0}^p(\omega_1,\ldots,\omega_g)=0$ in $J(X)$.

* **44.29. Jacobi inversion.** The Abel map from the $g$th symmetric
  power $X^{(g)}$ onto $J(X)$ is surjective and generically
  one-to-one. Every degree-$g$ divisor class has an effective representative.

### Quasiconformal mappings and measurable complex structures

An orientation-preserving homeomorphism $f:\Omega\to\Omega'$ is
**$K$-quasiconformal** if $f\in W^{1,2}_{\mathrm{loc}}$ and
$|f_{\bar z}|\leq k|f_z|$ almost everywhere, where
$k=(K-1)/(K+1)<1$. Its **Beltrami coefficient** is
$\mu_f=f_{\bar z}/f_z$. A Beltrami differential transforms as
$\mu(z)d\bar z/dz$ under conformal coordinate changes.

* **44.39. Measurable Riemann mapping theorem.** Every measurable
  $\mu$ on the sphere with $\|\mu\|_\infty<1$ is integrated
  by a quasiconformal homeomorphism solving
  $f_{\bar z}=\mu f_z$. Fixing the images of three distinct
  points determines it uniquely.

* **44.50. Astala area distortion.** If $f:\mathbb D\to\mathbb D$
  is $K$-quasiconformal and fixes zero, then
  $|f(E)|\leq C(K)|E|^{1/K}$ for measurable $E$.
  The exponent is sharp.

### Teichmüller spaces and extremal maps

A point of $\mathcal T_g$ is a compact Riemann surface $X$ with
an orientation-preserving marking from a fixed topological surface,
modulo conformal maps compatible with the markings up to isotopy.
The **Teichmüller distance** is
$d_T(X,Y)=\frac12\inf_f\log K(f)$ over maps in the marked class.
Write $Q(X)=H^0(X,K_X^2)$ with $\|q\|_1=\int_X|q|$.

* **44.55. Extremal existence.** The infimum defining $d_T$ is attained
  in each marked homotopy class. If $X\ne Y$, the extremal map
  has coefficient $\mu=k\bar q/|q|$ for a nonzero $q\in Q(X)$,
  $0<k<1$.

* **44.56. Teichmüller uniqueness.** That extremal map is unique in
  its marked class. The initial quadratic differential is unique up
  to positive scalar; away from its zeros the map is affine in
  natural coordinates $w=\int\sqrt q$.

* **44.58. Dimension and contractibility.** $\mathcal T_g$ is a complex
  manifold of dimension $3g-3$, homeomorphic to $\mathbb R^{6g-6}$.
  In particular it is contractible.

* **44.61. Bers embedding.** Fixing a base surface, simultaneous
  uniformization and a Schwarzian derivative embed $\mathcal T_g$
  biholomorphically as a bounded domain in the $3g-3$ dimensional
  space of quadratic differentials on the conjugate base surface.

* **44.63. Extremal-length distance formula.** For essential simple
  closed curves $\alpha$,
  $d_T(X,Y)=\frac12\log\sup_\alpha
  \operatorname{Ext}_Y(\alpha)/\operatorname{Ext}_X(\alpha)$.
  This connects quasiconformal distortion with the extremal metrics
  of Section 43.

### Moduli, mapping classes, and hyperbolic geometry

The **mapping class group** is
$\operatorname{Mod}_g=\pi_0(\operatorname{Homeo}^+(S_g))$;
the moduli space is $\mathcal M_g=\mathcal T_g/\operatorname{Mod}_g$.
For the hyperbolic metric $\rho^2|dz|^2$, the Weil–Petersson
cotangent pairing is $\langle q,p\rangle_{WP}
=\int q\bar p\,\rho^{-2}dx\,dy$.

* **44.72. Mumford compactness.** For each $\varepsilon>0$, the locus
  in $\mathcal M_g$ with hyperbolic systole at least $\varepsilon$
  is compact. Noncompactness of moduli is therefore detected by short geodesics.

## 45. Several complex variables, complex manifolds, pluripotential theory, and CR analysis

The inventories contain one-variable holomorphy, a holomorphic sheaf on the plane, and particular complex curves. The selected several-variable local and global theories remain missing: Hartogs phenomena, Weierstrass division, Stein theory, $\bar\partial$ estimates, pluripotential theory, and complex-geometric vanishing and embedding. Finite-dimensional analytic-map infrastructure is a prerequisite rather than a substitute for these theorems.

Sources: [mathematical synopsis](SYNOPSIS45.md); [combined coverage inventory](Mathlib45.md).

Domains are connected open subsets of $\mathbb C^n$. A function is
**plurisubharmonic** (psh) if it is upper semicontinuous and its restriction
to every complex line is subharmonic or identically $-\infty$; exclude
the identically $-\infty$ function unless expressly allowed. For $C^2$
functions this means that the complex Hessian $(u_{j\bar k})$ is
positive semidefinite. Use
$d^c=\frac{i}{2\pi}(\bar\partial-\partial)$, so
$dd^c=\frac{i}{\pi}\partial\bar\partial$.

### Local holomorphic functions and analytic sets

* **45.1. Hartogs separate analyticity.** A function separately
  holomorphic in each coordinate on an open subset of $\mathbb C^n$
  is jointly holomorphic; no preliminary continuity hypothesis is needed.

* **45.2. Polydisk Cauchy formula.** Iterated one-variable Cauchy
  formulas give convergent multivariable Taylor series, derivative
  estimates, and normal convergence on smaller polydisks.

* **45.5. Hartogs extension.** If $n\geq2$, $K\Subset\Omega$, and
  $\Omega\setminus K$ is connected, every holomorphic function on
  $\Omega\setminus K$ extends uniquely to $\Omega$.

* **45.7. Weierstrass preparation.** If a germ $f(z',z_n)$ has order
  $d$ in $z_n$ at the origin, then $f=uP$, uniquely, where $u$
  is a holomorphic unit and $P$ is monic of degree $d$ in $z_n$
  with holomorphic coefficients vanishing at $z'=0$.

* **45.8. Weierstrass division.** For such a distinguished polynomial
  $P$, every holomorphic germ $g$ has a unique decomposition
  $g=qP+r$, where $r$ is polynomial in $z_n$ of degree less than $d$.

### Pseudoconvexity, Stein spaces, and approximation

A domain is **pseudoconvex** if it admits a continuous psh exhaustion.
For a $C^2$ defining function $\rho$ with domain $\rho<0$, its
**Levi form** is $\sum\rho_{j\bar k}v_j\bar v_k$ restricted to
$\sum\rho_jv_j=0$. Strict pseudoconvexity means positivity there.
A complex manifold is **Stein** if it is holomorphically convex and
global holomorphic functions separate points and furnish local coordinates.
The holomorphic hull of compact $K\subset X$ is
$\widehat K_X=\{x:|f(x)|\leq\sup_K|f|\text{ for all }f\in\mathcal O(X)\}$.

* **45.15. Levi problem.** For domains in $\mathbb C^n$, the following
  are equivalent: pseudoconvexity, being a domain of holomorphy,
  holomorphic convexity, and being Stein.

* **45.20. Oka–Weil approximation.** If $K$ is holomorphically convex
  in a Stein space, functions holomorphic near $K$ are uniformly
  approximable on $K$ by global holomorphic functions.
  For polynomially convex $K\subset\mathbb C^n$, polynomials suffice.

* **45.21. Oka coherence theorem.** The structure sheaf and ideal
  sheaves of analytic subsets are coherent. Kernels of morphisms
  between coherent analytic sheaves are coherent.

* **45.23. Cartan's theorem B.** On a Stein space, coherent analytic
  sheaves satisfy $H^q(X,\mathcal F)=0$ for every $q\geq1$.

### The d-bar equation and the Neumann problem

The **Dolbeault complex** uses
$\bar\partial:A^{p,q}\to A^{p,q+1}$, $\bar\partial^2=0$.
On a Hermitian domain put
$\Box_q=\bar\partial\bar\partial^*+\bar\partial^*\bar\partial$
with its Hilbert-complex boundary conditions. Its inverse on the orthogonal
complement of its kernel is the **$\bar\partial$-Neumann operator** $N_q$.

* **45.30. Local Dolbeault lemma.** Every smooth $\bar\partial$-closed
  $(p,q)$-form with $q\geq1$ is locally $\bar\partial$ of a
  smooth $(p,q-1)$-form.

* **45.33. Hörmander weighted estimate.** On a pseudoconvex domain,
  for $C^2$ strictly psh $\phi$ and $\bar\partial$-closed $(0,1)$-form
  $g$, there is $\bar\partial u=g$ with
  $\int|u|^2e^{-\phi}\leq\int\langle(\phi_{j\bar k})^{-1}g,g\rangle e^{-\phi}$
  whenever the right side is finite.

* **45.39. Strictly pseudoconvex subellipticity.** On a smooth bounded
  strictly pseudoconvex domain, the Neumann quadratic form controls
  the $H^{1/2}$ norm in degrees $q\geq1$. Canonical solutions
  gain half a Sobolev derivative, with the corresponding global estimates.

* **45.41. Ohsawa–Takegoshi extension.** On a bounded pseudoconvex
  domain $\Omega\subset\mathbb C^n$, a holomorphic function on
  $\Omega\cap\{z_n=0\}$ with finite weighted $L^2$ norm extends
  to $F\in\mathcal O(\Omega)$ with
  $\int_\Omega|F|^2e^{-\phi}\leq C\int_{\Omega\cap\{z_n=0\}}|f|^2e^{-\phi}$
  for psh $\phi$; $C$ depends on a bound for the transverse coordinate.

### Positive currents and pluripotential theory

A **positive current** acts nonnegatively on strongly positive test forms.
For locally bounded psh functions, the Bedford–Taylor products
$dd^cu_1\wedge\cdots\wedge dd^cu_k$ are defined recursively by
distributional differentiation of $u_1dd^cu_2\wedge\cdots$.
For a Kähler form $\omega$, $u$ is **$\omega$-psh** if
$\omega+dd^cu\geq0$.

* **45.47. Poincaré–Lelong formula.** For nonzero holomorphic $f$,
  $dd^c\log|f|=[\operatorname{div}f]$ as currents.
  For a Hermitian holomorphic line bundle this becomes the divisor
  current minus its first-Chern curvature form.

* **45.49. Bedford–Taylor products.** Products of $dd^c$ of locally
  bounded psh functions are positive, closed, symmetric, and local.
  In top degree they define positive Monge–Ampère measures.

* **45.54. Monge–Ampère Dirichlet problem.** On a bounded smoothly
  strictly pseudoconvex domain, continuous boundary data and continuous
  nonnegative volume density have a unique continuous psh solution
  of $(dd^cu)^n=f\,dV$ with those boundary values.

* **45.56. Calabi–Yau theorem.** On a compact Kähler manifold,
  each smooth positive volume form of mass $\int\omega^n$ is
  $(\omega+dd^cu)^n$ for a unique smooth $u$ modulo constants,
  with $\omega+dd^cu>0$. Thus a prescribed Ricci form in
  $2\pi c_1(X)$ is realized uniquely in a fixed Kähler class.

### Complex manifolds and Kähler geometry

* **45.58. Dolbeault theorem.** For a holomorphic vector bundle $E$,
  $H^q(X,\Omega^p\otimes E)$ is the cohomology of its smooth
  $\bar\partial$ complex in bidegree $(p,q)$.

* **45.65. Kodaira–Nakano vanishing.** If $L$ is positive on compact
  Kähler $X$, then $H^q(X,\Omega^p\otimes L)=0$ for
  $p+q>n$. In particular $H^q(X,K_X\otimes L)=0$ for $q>0$.

* **45.66. Kodaira embedding theorem.** A compact complex manifold
  with a positive holomorphic line bundle is projective; sufficiently
  high tensor powers give embeddings. Equivalently, a compact Kähler
  manifold with an integral Kähler class is projective.

## 46. Complex dynamics

Disc contraction and fixed-point rigidity are covered. The missing dynamic theory concerns iteration: Julia and Fatou sets, local linearization and parabolic dynamics, classification of stable regions, polynomial parameter spaces, and quasiconformal methods. The selection includes a transcendental escaping theorem to distinguish rational iteration from entire-function dynamics.

Sources: [mathematical synopsis](SYNOPSIS46.md); [combined coverage inventory](Mathlib46.md).

Unless specified otherwise, $f:\widehat{\mathbb C}\to\widehat{\mathbb C}$
is rational of degree $d\geq2$; $f^n$ denotes iteration. The **Fatou set**
$F(f)$ is the open set where $\{f^n\}$ is normal in the spherical metric;
the **Julia set** is its complement $J(f)$. The **postcritical set** is
$P(f)=\overline{\bigcup_{n\geq1}f^n(\operatorname{Crit}f)}$.
The multiplier of a period-$p$ point is $(f^p)'$ in a local coordinate.

### Julia sets and global iteration

* **46.6. Repelling cycles are dense.** Repelling periodic points lie
  in $J(f)$ and are dense there. Attracting periodic points lie in $F(f)$.

### Local normal forms and small divisors

* **46.10. Koenigs linearization.** A germ $f(z)=\lambda z+O(z^2)$
  with $0<|\lambda|\ne1$ is locally conjugate to $z\mapsto\lambda z$.
  The conjugating germ normalized to have derivative one is unique.

* **46.11. Böttcher's theorem.** A superattracting germ
  $f(z)=az^k+O(z^{k+1})$, $k\geq2$, is locally conjugate to
  $z\mapsto z^k$. The coordinate is unique up to a $(k-1)$st root of unity.

* **46.12. Leau–Fatou flower theorem.** For
  $f(z)=z+az^{k+1}+O(z^{k+2})$, $a\ne0$, there are $k$
  attracting and $k$ repelling petals. Their union with the fixed point
  contains a neighborhood of it, and their directions alternate.

### Fatou components and hyperbolicity

* **46.19. Periodic Fatou classification.** A periodic Fatou component
  is an attracting basin, a parabolic basin, a Siegel disk, or a
  Herman ring. On the last two, the first return map is conformally
  conjugate to an irrational rotation of a disk or annulus.

* **46.20. Sullivan's no-wandering-domains theorem.** Every Fatou
  component of a rational map is eventually periodic. Consequently
  the preceding list describes all components after finitely many iterates.

* **46.23. Hyperbolicity criteria.** The following are equivalent:
  $P(f)\cap J(f)=\varnothing$; every critical orbit tends to an
  attracting cycle; and uniform expansion of some iterate on $J(f)$
  in a smooth conformal metric near that set.

### Polynomial Green functions, rays, and equilibrium measures

For a polynomial $p$ of degree $d\geq2$, its **filled Julia set** is
$K(p)=\{z:(p^n(z))\text{ is bounded}\}$ and its escape-rate function is
$G_p(z)=\lim_{n\to\infty}d^{-n}\log^+|p^n(z)|$.
Use $dd^c=\frac{i}{\pi}\partial\bar\partial$.

* **46.29. Connectedness criterion.** $K(p)$, equivalently $J(p)$,
  is connected exactly when every finite critical point has bounded orbit.

* **46.33. Equilibrium measure.** $\mu_p=dd^cG_p$ is a probability
  measure supported on $J(p)$, equal to logarithmic equilibrium
  measure of $K(p)$ and harmonic measure from infinity.
  It satisfies $p_*\mu_p=\mu_p$ and $p^*\mu_p=d\mu_p$.

* **46.35. Maximal entropy.** $h_{\rm top}(f)=\log d$ and $\mu_f$
  is the unique invariant probability measure of entropy $\log d$.
  It is mixing and has no atoms.

### Parameter spaces, deformation, and renormalization

For $p_c(z)=z^2+c$, the **Mandelbrot set** is
$\mathcal M=\{c:(p_c^n(0))\text{ is bounded}\}$.
A **polynomial-like map** is a proper holomorphic map $U\to V$ of
degree at least two, with $U\Subset V$ topological disks; its filled set
consists of points whose iterates remain in $U$.
A **holomorphic motion** is injective at each parameter, holomorphic
in the parameter at each moving point, and the identity at a base parameter.
**Julia stability** means local existence of an equivariant holomorphic
motion of the Julia set.

* **46.40. Mandelbrot connectedness.** $\mathcal M$ is compact and
  connected, and $c\in\mathcal M$ exactly when $J(p_c)$ is connected.
  An escape bound gives $\mathcal M\subset\{|c|\leq2\}$.

* **46.43. Holomorphic-motion extension.** A holomorphic motion of
  a subset of the sphere extends to its closure and, over a disk
  parameter space, to a motion of the whole sphere with quasiconformal slices.

* **46.45. Hybrid straightening.** Every polynomial-like map is
  quasiconformally conjugate near its filled set to a polynomial of
  the same degree, with the conjugacy conformal almost everywhere
  on the filled set. If that set is connected, the polynomial is
  unique up to affine conjugacy.

* **46.48. Thurston characterization.** A postcritically finite
  orientation-preserving branched sphere covering with hyperbolic
  orbifold is equivalent to a rational map exactly when every stable
  essential nonperipheral multicurve has Thurston matrix of spectral
  radius less than one. Matrix entries sum reciprocal covering degrees
  over isotopic inverse curves. The rational map is unique up to Möbius conjugacy.

### Conformal repellers and thermodynamic formalism

Let $f:X\to X$ be a topologically mixing expanding conformal repeller.
For a Hölder potential $\varphi$, write $P(\varphi)$ for pressure and
$\mathcal L_\varphi u(x)=\sum_{f(y)=x}e^{\varphi(y)}u(y)$.

* **46.52. Bowen dimension formula.** The Hausdorff dimension of
  $X$ is the unique zero $s$ of $P(-s\log|f'|)$.
  In particular this computes dimensions of hyperbolic rational Julia sets.

### Transcendental entire dynamics

Here $f:\mathbb C\to\mathbb C$ is transcendental entire.
The **singular set** $S(f)$ is the closure of its finite critical and
finite asymptotic values. The **escaping set** is
$I(f)=\{z:f^n(z)\to\infty\}$.
Class $\mathcal B$ has bounded $S(f)$; class $\mathcal S$ has finite $S(f)$.

* **46.58. Eremenko escaping theorem.** $I(f)$ is nonempty and
  $\partial I(f)=J(f)$. Its closure has no bounded connected component.
  This closure statement does not assert the corresponding property
  for components of $I(f)$ itself.

## 47. Approximation theory

Weierstrass/Stone–Weierstrass density, elementary polynomial algebra, Chebyshev extremality, and $L^p$ smoothing are available. The major gaps are optimality criteria, quantitative direct and inverse estimates, interpolation stability, splines, rational approximation, and widths. Density without a rate is weaker than the Jackson and analyticity characterizations selected below.

Sources: [mathematical synopsis](SYNOPSIS47.md); [combined coverage inventory](Mathlib47.md).

Write $\mathcal P_n$ for polynomials of degree at most $n$ and
$\mathcal T_n$ for trigonometric polynomials of frequencies $|k|\leq n$.
For a normed function space $X$, put
$E_n(f)_X=\inf_{p\in\mathcal P_n}\|f-p\|_X$; a superscript
$\mathrm{trig}$ indicates $\mathcal T_n$. Uniform-approximation statements
use real continuous functions on a compact interval unless specified otherwise.

### Best approximation and alternation

* **47.6. Chebyshev alternation theorem.** A polynomial $p\in\mathcal P_n$
  is the best uniform approximant to $f\notin\mathcal P_n$ exactly
  when $f-p$ takes alternating values $\pm\|f-p\|_\infty$ at
  $n+2$ increasing points. Haar spaces have the analogous $m+1$ point criterion.

### Density and positive approximation operators

* **47.13. Müntz–Szász theorem.** If $0<\lambda_1<\lambda_2<\cdots\to\infty$,
  the span of $1,x^{\lambda_1},x^{\lambda_2},\ldots$ is dense
  in $C[0,1]$ exactly when $\sum_j1/\lambda_j=\infty$.

* **47.17. Korovkin theorem.** Positive linear maps
  $L_n:C[0,1]\to C[0,1]$ converge strongly to the identity
  exactly when they converge uniformly on $1,x,x^2$.

### Smoothness, direct estimates, and inverse estimates

For periodic $f\in L^p$, $1\leq p\leq\infty$, define
$\omega_r(f,t)_p=\sup_{|h|\leq t}\|\Delta_h^rf\|_p$.
At $p=\infty$ use continuous functions. The derivative $K$-functional is
$K_r(f,t^r)_p=\inf_g(\|f-g\|_p+t^r\|g^{(r)}\|_p)$.
For algebraic approximation put $\varphi(x)=\sqrt{1-x^2}$;
the **Ditzian–Totik modulus** uses centered differences with step
$h\varphi(x)$ where all evaluation points remain in $[-1,1]$.

* **47.20. Jackson's trigonometric theorem.**
  $E_n^{\mathrm{trig}}(f)_p\leq C_r\omega_r(f,1/n)_p$.

* **47.21. Inverse trigonometric estimate.**
  $\omega_r(f,1/n)_p\leq C_rn^{-r}
  \sum_{k=0}^n(k+1)^{r-1}E_k^{\mathrm{trig}}(f)_p$.
  Good approximation therefore forces smoothness.

* **47.23. Bernstein derivative inequality.**
  $\|T^{(r)}\|_p\leq n^r\|T\|_p$ for $T\in\mathcal T_n$,
  $1\leq p\leq\infty$.

* **47.24. Markov inequality.** For $P\in\mathcal P_n$ on $[-1,1]$,
  $\|P'\|_\infty\leq n^2\|P\|_\infty$. The exponent and
  first-derivative constant are sharp.

### Chebyshev, analytic, and rational approximation

The **Bernstein ellipse** $E_\rho$, $\rho>1$, is the image of
$|w|=\rho$ under $z=(w+w^{-1})/2$.

In 47.32, assume $f$ is holomorphic on a neighborhood of the closed Bernstein ellipse and $|f|\leq M$ there.

* **47.32. Geometric convergence.** The degree-$n$ Chebyshev truncation
  has error at most $2M\rho^{-n}/(\rho-1)$; interpolation at
  Chebyshev extrema has error at most $4M\rho^{-n}/(\rho-1)$.

* **47.35. Chebyshev interpolation stability.** Its Lebesgue constants
  are $(2/\pi)\log n+O(1)$. Hence interpolation is near-best
  with a logarithmic factor.

* **47.40. Newman's theorem.** Best type-$(n,n)$ rational approximation
  to $|x|$ on $[-1,1]$ has error between
  $c_1e^{-c_2\sqrt n}$ and $c_3e^{-c_4\sqrt n}$ for positive
  constants. Polynomial approximation has order $n^{-1}$ instead.

### Splines and total positivity

An **order-$k$ spline** has polynomial pieces of degree at most $k-1$,
with the continuity prescribed by knot multiplicities. With simple interior
knots it is $C^{k-2}$. Let $N_{i,k}$ be the normalized B-splines for
a nondecreasing knot sequence $t_i$.

* **47.42. B-spline basis.** The $N_{i,k}$ form a basis, are nonnegative,
  have support $[t_i,t_{i+k}]$, and sum to one on the basic interval
  for the usual endpoint-completed knot sequence.

* **47.45. Schoenberg–Whitney theorem.** For increasing interior
  interpolation nodes, the square B-spline collocation matrix is
  nonsingular exactly when nodes and supports satisfy
  $t_i<x_i<t_{i+k}$, with the corresponding endpoint conventions.

* **47.48. Spline Jackson estimates.** For quasiuniform meshes of
  maximum spacing $h$, $f\in W^{s,p}$, and $1\leq s\leq k$,
  some order-$k$ spline satisfies $\|f-s_h\|_p\leq Ch^s\|f^{(s)}\|_p$,
  $1\leq p\leq\infty$, with fixed degree and mesh-ratio bound.

* **47.51. Smoothing-spline representer theorem.** For $\lambda>0$,
  minimizing a positive weighted sum of squared nodal errors plus
  $\lambda\int|u^{(m)}|^2$ gives a natural spline of degree
  $2m-1$ with knots among the data sites. At least $m$ distinct
  sites ensure uniqueness by controlling the polynomial nullspace.

### Nonlinear approximation, widths, and dimension

For a dictionary $\mathcal D$, let $\sigma_m(f)$ be the least error
of linear combinations of at most $m$ dictionary elements. For bounded
$A\subset X$, the **Kolmogorov width** is
$d_m(A;X)=\inf_{\dim V\leq m}\sup_{f\in A}\inf_{v\in V}\|f-v\|$.
A normalized basis is **democratic** when sums over equal-size finite
index sets have comparable norms uniformly.

* **47.65. Sobolev widths.** For the unit ball of $H^s(\mathbb T^d)$
  in $L^2$, $d_m\asymp m^{-s/d}$, $s>0$.
  Frequency counting makes the dependence on dimension explicit.

## 48. Orthogonal polynomials, moment problems, and spectral recurrences

Concrete Chebyshev and Hermite orthogonal bases and several moment-determinacy criteria are covered. The missing core is general recurrence and Jacobi spectral theory, Gaussian quadrature, existence for prescribed moments, and unit-circle recurrence and asymptotics. Determinacy under exponential integrability does not solve Hamburger or Stieltjes moment existence; it also does not supply the general Carleman criterion.

Sources: [mathematical synopsis](SYNOPSIS48.md); [combined coverage inventory](Mathlib48.md).

For real-line orthogonality, $\mu$ is a positive Borel measure with infinite
support and finite moments of all orders. Write $p_n(x)=\kappa_nx^n+\cdots$,
$\kappa_n>0$, for orthonormal polynomials, and $P_n=p_n/\kappa_n$ for
monic ones. Normalize $\mu(\mathbb R)=1$ when discussing its Jacobi
matrix. Put $K_n(x,y)=\sum_{j=0}^np_j(x)\overline{p_j(y)}$.

### Orthogonality, recurrence, and zeros

The recurrence is $xp_n=a_{n+1}p_{n+1}+b_np_n+a_np_{n-1}$, with $a_{n+1}>0$, $b_n\in\mathbb R$, $a_0=0$, $p_{-1}=0$.

* **48.4. Favard's theorem.** Conversely every such real recurrence
  with positive off-diagonal coefficients has a positive orthogonality
  measure with infinite support and all finite moments. The recurrence
  and total mass fix the moments, but need not fix the measure.

* **48.6. Real and simple zeros.** The $n$ zeros of $p_n$ are
  simple and lie in the interior of the convex hull of $\operatorname{supp}\mu$.

* **48.8. Christoffel–Darboux formula.**
  $K_n(x,y)=a_{n+1}[p_{n+1}(x)p_n(y)-p_n(x)p_{n+1}(y)]/(x-y)$
  for real distinct $x,y$; the diagonal value is its derivative limit.

### Gaussian quadrature and Cauchy transforms

* **48.14. Gauss quadrature.** The zeros $x_1,\ldots,x_n$ of $p_n$
  support a unique quadrature rule exact on $\mathcal P_{2n-1}$.
  Its weights are positive and equal $1/K_{n-1}(x_j,x_j)$.

### Jacobi operators and spectral measures

The half-line **Jacobi expression** on $\ell^2(\mathbb N_0)$ is
$(Ju)_n=a_{n+1}u_{n+1}+b_nu_n+a_nu_{n-1}$.
The minimal operator starts on finitely supported vectors.
For a self-adjoint realization set
$m(z)=\langle\delta_0,(J-z)^{-1}\delta_0\rangle$.

* **48.22. Bounded Jacobi correspondence.** Bounded real $b_n$ and
  bounded positive $a_n$ define a bounded self-adjoint operator;
  $\|J\|\leq\sup|b_n|+2\sup a_n$.
  Conversely boundedness bounds every matrix coefficient.

* **48.29. Determinacy correspondence.** The Hamburger moment problem
  associated with the recurrence is determinate exactly when the
  minimal Jacobi operator is essentially self-adjoint.

### Moment existence, uniqueness, and positivity

For a sequence $s=(s_\alpha)$ define the **moment functional**
$L(x^\alpha)=s_\alpha$. A representing measure on closed $K$ satisfies
$L(p)=\int_Kp\,d\mu$. Moment matrices are indexed by monomials;
localizing matrices represent $L(gp\bar q)$.

* **48.31. Hamburger theorem.** A real sequence $(s_n)_{n\geq0}$
  is a moment sequence on $\mathbb R$ exactly when every Hankel
  matrix $[s_{j+k}]$ is positive semidefinite.

* **48.32. Stieltjes theorem.** It is a moment sequence on $[0,\infty)$
  exactly when both $[s_{j+k}]$ and $[s_{j+k+1}]$ are positive
  semidefinite in every finite size.

* **48.33. Hausdorff theorem.** It is a moment sequence on $[0,1]$
  exactly when $(-1)^k\Delta^ks_n\geq0$ for all $n,k\geq0$.
  The representing measure is then unique.

* **48.35. Moment Carleman criteria.**
  $\sum_ns_{2n}^{-1/(2n)}=\infty$ gives Hamburger determinacy;
  $\sum_ns_n^{-1/(2n)}=\infty$ gives Stieltjes determinacy when
  a Stieltjes representing measure exists.

* **48.39. Nevanlinna parametrization.** In an indeterminate Hamburger
  problem, all Cauchy transforms are described by a fractional-linear
  transformation of a Pick-function parameter using four entire
  functions determined by the recurrence. Real constant parameters
  give the canonical self-adjoint-extension measures.

### Orthogonal polynomials on the unit circle

Here $\mu$ is a probability on $\mathbb T$ with infinite support.
Write $\Phi_n$ for its monic orthogonal polynomials,
$\Phi_n^*(z)=z^n\overline{\Phi_n(1/\bar z)}$, and
$\alpha_n=-\overline{\Phi_{n+1}(0)}$.

For a circle weight $w$, put $D_n(w)=\det[\widehat w(j-k)]_{j,k=0}^{n-1}$, and use normalized arc measure $dm$.

* **48.48. Verblunsky theorem.** Infinite-support circle probabilities
  correspond bijectively to arbitrary sequences $\alpha_n\in\mathbb D$.
  Finite support corresponds to termination with a last coefficient on $\mathbb T$.

* **48.52. CMV representation.** Multiplication by $z$ in the
  orthonormal Laurent-polynomial basis is a five-diagonal unitary
  CMV matrix, factored into alternating $2\times2$ unitary blocks
  determined by $\alpha_n$. Its spectral measure at the first basis
  vector is $\mu$. See [Simon's survey](https://arxiv.org/pdf/math/0502485), Section 5.

* **48.53. Szegő theorem.** For $d\mu=w\,dm+d\mu_s$,
  $\prod_{n\geq0}(1-|\alpha_n|^2)=\exp\int\log w\,dm$.
  Thus finite logarithmic integral is equivalent to $\sum|\alpha_n|^2<\infty$.

* **48.56. Strong Szegő theorem.** For a positive smooth circle
  weight $w=e^L$,
  $D_n(w)e^{-n\widehat L(0)}\to
  \exp\sum_{k\geq1}k|\widehat L(k)|^2$.
  The Sobolev-$1/2$ condition on $L$ is the natural sharp finite-constant condition.

### Asymptotics and potential theory

For compact nonpolar real support $K$, call $\mu$ **regular** if
$\kappa_n^{1/n}\to\operatorname{cap}(K)^{-1}$.
Let $\omega_K$ be its logarithmic equilibrium measure and $g_K$
the exterior Green function with pole at infinity.

* **48.59. Equilibrium zero distribution.** For regular $\mu$ on a
  compact subset of $\mathbb R$, the normalized zero-counting
  measures of $p_n$ converge weakly to $\omega_K$.

## 49. Special functions, integral transforms, and classical formulae

Gamma, beta, substantial zeta and Mellin theory, some hypergeometric and Bessel-J material, and several elliptic/theta identities are covered. TauCeti adds error and incomplete functions and Bernstein/Stieltjes representation. The gaps selected here concern missing differential-equation, transform, and classical-family structures. In 49.5 the gap is multiplication beyond the already-covered duplication formula.

Sources: [mathematical synopsis](SYNOPSIS49.md); [combined coverage inventory](Mathlib49.md).

Write $(a)_n=\Gamma(a+n)/\Gamma(a)$, with its polynomial interpretation
at exceptional $a$. In series, denominator parameters are not nonpositive
integers unless a terminating or limiting interpretation is specified.
Identities initially valid in the stated convergence regions continue
meromorphically in their parameters where defined. Noninteger powers use
consistent branches, ordinarily the principal branch on the cut plane.

### Gamma, beta, and zeta functions

* **49.5. Multiplication formula.** For integers $m\geq1$,
  $\prod_{j=0}^{m-1}\Gamma(z+j/m)
  =(2\pi)^{(m-1)/2}m^{1/2-mz}\Gamma(mz)$.

### Hypergeometric and confluent hypergeometric functions

Define
${}_pF_q(a;b;z)=\sum_{n\geq0}(a_1)_n\cdots(a_p)_n
z^n/((b_1)_n\cdots(b_q)_nn!)$.
Write $F(a,b;c;z)={}_2F_1(a,b;c;z)$ and
$M(a,b,z)={}_1F_1(a;b;z)$.

* **49.11. Gauss equation.** $F(a,b;c;z)$ is the solution normalized
  by $F(0)=1$ of
  $z(1-z)y''+[c-(a+b+1)z]y'-aby=0$.
  Its singular points are regular singular at $0,1,\infty$.

### Bessel, Airy, and Gaussian functions

$J_\nu$ is the Bessel function of the first kind, defined by $\sum_{k\geq0}(-1)^k(z/2)^{2k+\nu}/(k!\Gamma(k+\nu+1))$ on a consistent branch.

* **49.24. Second solution.** For noninteger $\nu$,
  $Y_\nu=(\cos\pi\nu\,J_\nu-J_{-\nu})/\sin\pi\nu$;
  integer orders are defined by limits. The outgoing and incoming
  Hankel solutions are $H_\nu^{(1,2)}=J_\nu\pm iY_\nu$.

* **49.28. Bessel generating function.**
  $e^{(z/2)(t-t^{-1})}=\sum_{n\in\mathbb Z}J_n(z)t^n$,
  with normal convergence on compact subsets of $0<|t|<\infty$.

* **49.30. Hankel transform.** For real $\nu\geq-1/2$,
  $\mathcal H_\nu f(s)=\int_0^\infty f(r)J_\nu(rs)r\,dr$
  extends to a unitary involution on $L^2((0,\infty),r\,dr)$.

* **49.34. Airy representation.** The Airy equation is $y''=zy$.
  For real $x$, $\operatorname{Ai}(x)=\pi^{-1}\int_0^\infty
  \cos(t^3/3+xt)dt$, as an oscillatory integral.

### Classical polynomial families and spherical functions

The Jacobi normalization is $P_n^{(\alpha,\beta)}(x)=(\alpha+1)_n\,{}_2F_1(-n,n+\alpha+\beta+1;\alpha+1;(1-x)/2)/n!$. The symbol $P_\ell$ denotes the Legendre polynomial $P_\ell^{(0,0)}$.

* **49.38. Jacobi orthogonality.** For $\alpha,\beta>-1$, these
  polynomials are orthogonal for $(1-x)^\alpha(1+x)^\beta dx$,
  with squared norm
  $\frac{2^{\alpha+\beta+1}\Gamma(n+\alpha+1)\Gamma(n+\beta+1)}
  {(2n+\alpha+\beta+1)n!\Gamma(n+\alpha+\beta+1)}$,
  interpreted continuously at removable parameter cases.

* **49.40. Laguerre system.**
  $L_n^{(\alpha)}(x)=(\alpha+1)_nM(-n,\alpha+1,x)/n!$,
  $\sum_{n\geq0}L_n^{(\alpha)}(x)t^n
  =(1-t)^{-\alpha-1}e^{-xt/(1-t)}$, $|t|<1$.
  For $\alpha>-1$, its squared norm for $x^\alpha e^{-x}dx$
  is $\Gamma(n+\alpha+1)/n!$.

* **49.43. Spherical addition theorem.** For area-orthonormal spherical
  harmonics on $S^2$,
  $\sum_{m=-\ell}^{\ell}Y_{\ell m}(\xi)\overline{Y_{\ell m}(\eta)}
  =(2\ell+1)P_\ell(\xi\cdot\eta)/(4\pi)$.

### Elliptic integrals, elliptic functions, and theta functions

For $0<k<1$, let $k'=\sqrt{1-k^2}$ and
$K(k)=\int_0^{\pi/2}(1-k^2\sin^2t)^{-1/2}dt$,
$E(k)=\int_0^{\pi/2}(1-k^2\sin^2t)^{1/2}dt$.
A prime on $K,E$ below means complementary modulus, not differentiation.

* **49.48. Jacobi elliptic identities.** The inverse elliptic integral
  defines $\operatorname{sn}$, with
  $\operatorname{sn}^2+\operatorname{cn}^2=1$,
  $\operatorname{dn}^2+k^2\operatorname{sn}^2=1$ and derivatives
  $\operatorname{sn}'=\operatorname{cn}\operatorname{dn}$,
  $\operatorname{cn}'=-\operatorname{sn}\operatorname{dn}$,
  $\operatorname{dn}'=-k^2\operatorname{sn}\operatorname{cn}$.

### Laplace, Mellin, and positivity representations

The Laplace transform is $\mathcal Lf(s)=\int_0^\infty e^{-st}f(t)\,dt$ in its half-plane of absolute convergence.

* **49.62. Bromwich inversion.** For a locally piecewise $C^1$
  function of exponential order,
  $\frac12(f(t+)+f(t-))=(2\pi i)^{-1}
  \lim_{T\to\infty}\int_{c-iT}^{c+iT}e^{st}\mathcal Lf(s)ds$
  at $t>0$, with $c$ in the absolute-convergence half-plane.

### Fractional integrals and Mittag–Leffler functions

For $\alpha>0$ define
$I^\alpha f(t)=\Gamma(\alpha)^{-1}\int_0^t(t-s)^{\alpha-1}f(s)ds$.
For $m-1<\alpha<m$, the **Caputo derivative** is
$D_C^\alpha u=I^{m-\alpha}u^{(m)}$; integer orders use ordinary derivatives.

* **49.72. Mittag–Leffler entire functions.** For $\alpha>0$,
  $E_{\alpha,\beta}(z)=\sum_{n\geq0}z^n/\Gamma(\alpha n+\beta)$
  is entire of order $1/\alpha$; $E_{1,1}(z)=e^z$.

## 50. Asymptotic analysis, resurgence, and perturbation

Asymptotic comparison notation and particular special-function asymptotics are available, as are bounded semigroup perturbation and Fredholm perturbation theorems. The missing body is general saddle and endpoint asymptotics, summation of divergent expansions, WKB and turning points, and singular perturbation. Wiener–Ikehara is covered; the regular-variation Tauberian theorem below is a distinct result.

Sources: [mathematical synopsis](SYNOPSIS50.md); [combined coverage inventory](Mathlib50.md).

For an asymptotic scale $\phi_{n+1}=o(\phi_n)$, write
$f\sim\sum a_n\phi_n$ if
$f-\sum_{n=0}^{N-1}a_n\phi_n=o(\phi_{N-1})$ for every $N$.
For power series near zero use the equivalent conventional remainder
$f-\sum_{n<N}a_nz^n=O(z^N)$ when all orders are available.
Sectorial estimates are uniform on closed proper subsectors; estimates
with an additional parameter explicitly require uniform hypotheses.

### Expansions, realization, and nonuniqueness

* **50.6. Borel–Ritt theorem.** Every formal power series is the
  asymptotic expansion of a holomorphic function on any sector of
  opening strictly less than $2\pi$.

### Laplace, oscillatory, and uniform integral methods

The large parameter $\lambda$ tends to $+\infty$. Amplitudes are
smooth and integrable as required; cutoff versions separate a critical
point from all other contributions.

* **50.9. Watson's lemma.** If $a(t)\sim\sum_{n\geq0}a_nt^{n+\alpha-1}$
  at $0+$, $\Re\alpha>0$, and the tail has an exponential bound,
  then $\int_0^\infty e^{-\lambda t}a(t)dt
  \sim\sum a_n\Gamma(n+\alpha)\lambda^{-n-\alpha}$.
  A finite local remainder gives the corresponding integral remainder.

* **50.11. Interior Laplace minimum.** A nondegenerate interior minimum
  $t_0$ contributes
  $e^{-\lambda\phi(t_0)}A(t_0)\sqrt{2\pi/(\lambda\phi''(t_0))}$.
  Taylor expansion after a Morse change of variable gives all higher terms.

* **50.14. Stationary phase.** A nondegenerate critical point with
  real Hessian $H$ contributes
  $e^{i\lambda\phi(x_0)+i\pi\operatorname{sgn}H/4}
  (2\pi/\lambda)^{m/2}A(x_0)/\sqrt{|\det H|}$,
  with subsequent powers of $\lambda^{-1}$ and controlled remainder.

* **50.18. Coalescing saddles.** Two analytic simple saddles coalescing
  to a cubic critical point admit a cubic normal form and a uniform
  expansion in Airy functions and their derivatives. The transition
  scale is $\lambda^{-2/3}$ in the unfolding parameter.

### Summation, Mellin transforms, and regular variation

$B_j$ are Bernoulli numbers and $\widetilde B_j(x)=B_j(\{x\})$ are periodic Bernoulli polynomials. A positive function $L$ is **slowly varying** if $L(tx)/L(x)\to1$ as $x\to\infty$ for each $t>0$. In 50.29, $U$ is the cumulative function of a locally finite positive measure on $[0,\infty)$.

* **50.23. Euler–Maclaurin formula.** For integers $m<n$ and smooth $f$,
  $$
  \sum_{k=m}^nf(k)=\int_m^nf(x)dx+\frac{f(m)+f(n)}2
  +\sum_{r=1}^p\frac{B_{2r}}{(2r)!}
  [f^{(2r-1)}(n)-f^{(2r-1)}(m)]+R_p.
  $$
  Here $R_p=-(2p)!^{-1}\int_m^n\widetilde B_{2p}(x)f^{(2p)}(x)dx$.

* **50.29. Karamata Tauberian theorem.** For a nondecreasing $U$
  with finite Laplace–Stieltjes transform at every positive argument,
  $\int e^{-st}dU(t)\sim s^{-\rho}L(1/s)$ as $s\downarrow0$
  exactly when $U(x)\sim x^\rho L(x)/\Gamma(1+\rho)$,
  where $\rho\geq0$ and $L$ is slowly varying. Positivity supplies
  the Tauberian hypothesis.

### Differential equations, irregular singularities, and WKB

* **50.31. Levelt–Turrittin formal structure.** After finite ramification,
  a meromorphic linear system has a formal fundamental solution
  decomposed into factors $\widehat H(t)e^{Q(t^{-1})}t^L$,
  blockwise, with polynomial exponential parts, constant exponent
  matrices, and invertible formal power-series factors.

* **50.35. Liouville–Green approximation.** On a compact real interval
  where $Q\in C^2$ is positive and bounded away from zero,
  $\varepsilon^2y''=Qy$ has independent solutions
  $Q^{-1/4}\exp[\pm\varepsilon^{-1}\int\sqrt Q]\,(1+O(\varepsilon))$
  uniformly as $\varepsilon\downarrow0$.

* **50.37. Simple turning points.** If analytic $Q$ has a simple
  zero at $a$, the change
  $\frac23\zeta^{3/2}=\int_a^x\sqrt Q$
  transforms the leading equation to Airy form. Uniform solutions
  have leading factors $(\zeta/Q)^{1/4}\operatorname{Ai}
  (\varepsilon^{-2/3}\zeta)$ and the corresponding $\operatorname{Bi}$ term.

### Gevrey series, Borel summation, and resurgence

A **Gevrey-$s$ expansion** obeys
$|f(z)-\sum_{n<N}a_nz^n|\leq CA^N\Gamma(1+sN)|z|^N$.
For $s=1$ use the formal Borel transform and directional Laplace integral
$$
\mathcal B\widehat f(\xi)=\sum_{n\geq1}\frac{a_n\xi^{n-1}}{(n-1)!},
\qquad \mathcal S_\theta\widehat f(z)=a_0+
\int_0^{e^{i\theta}\infty}e^{-\xi/z}\mathcal B\widehat f(\xi)d\xi.
$$
One-summability requires analytic continuation of the Borel germ to a
sector about that ray with at most exponential growth there.

* **50.45. Borel–Laplace theorem.** Under the stated continuation and
  exponential-growth conditions, rotation of the admissible Laplace
  ray gives a holomorphic sum for small $z$ in a sector centered
  at $\theta$ of opening greater than $\pi$. It has the original
  Gevrey-one expansion on proper subsectors.

* **50.51. Ramis–Sibuya theorem.** Bounded holomorphic functions on
  a finite good sectorial covering of a punctured disk, whose
  overlap differences are $O(e^{-c/|z|^k})$, have one common
  Gevrey-$(1/k)$ expansion. Uniform subsector bounds are required.

### Regular and singular perturbation of differential equations

Consider smooth slow–fast systems
$\dot x=f(x,y,\varepsilon)$,
$\varepsilon\dot y=g(x,y,\varepsilon)$.
Their **critical manifold** is $g(x,y,0)=0$; normal attraction means
the fast normal eigenvalues have real parts uniformly below zero.

* **50.58. Tikhonov theorem.** If the critical branch $y=h(x)$ is
  uniformly asymptotically stable for the frozen fast equation,
  the initial fast datum lies in its attraction basin, and the
  reduced solution stays in the regular branch, then $x_\varepsilon$
  converges uniformly to the reduced slow solution on fixed intervals,
  and $y_\varepsilon(t)\to h(x(t))$, where $x(t)$ is the reduced slow trajectory, away from the initial time.

* **50.60. Fenichel persistence.** A compact normally hyperbolic
  critical manifold persists for small $\varepsilon$ as a locally
  invariant slow manifold, $O(\varepsilon)$ close, with the
  differentiability allowed by the vector field and spectral gap.

## 51. Integrable systems and Riemann–Hilbert methods

Linear symplectic geometry and some exact cotangent constructions are present. The inventories report no developed Riemann–Hilbert, inverse-scattering, Lax-pair, or integrable-Hamiltonian theory. The selection follows the principal links from factorization to solitons, isomonodromy, and universal kernels. Cauchy principal-value contour identities alone do not give the singular-integral operator or small-norm theorems.

Sources: [mathematical synopsis](SYNOPSIS51.md); [combined coverage inventory](Mathlib51.md).

An oriented contour has its positive side on the left. A normalized matrix
Riemann–Hilbert problem asks for $M$ holomorphic off the contour, with
$M_+=M_-v$ and $M(\infty)=I$, together with specified endpoint and pole
conditions. Boundary values are nontangential; statements in $L^2$ use the
Cauchy-transform class $M-I=Cf$, $f\in L^2$, rather than arbitrary
holomorphic functions with almost-everywhere boundary traces. For scattering
formulas below, the potential is real and Schwartz unless stated otherwise.
We normalize KdV as $u_t-6uu_x+u_{xxx}=0$ and its spectral operator as
$L=-\partial_x^2+u$.

### Cauchy operators and analytic factorization

$C$ is the contour Cauchy transform $(2\pi i)^{-1}\int_\Gamma f(s)/(s-z)\,ds$, with traces $C_\pm$. Write $C_{v-I}h=C_-(h(v-I))$.

* **51.4. Matrix partial indices.** An invertible Hölder matrix loop on
  the unit circle admits a Birkhoff factorization
  $v=v_-^{-1}\operatorname{diag}(z^{\kappa_1},\ldots,z^{\kappa_r})v_+$
  with holomorphically invertible inside and outside factors. The integer
  partial indices govern homogeneous solutions and solvability;
  $\sum\kappa_j=\operatorname{wind}\det v$ does not determine them separately.

* **51.6. Singular-integral formulation.** For $v-I\in L^2\cap L^\infty$,
  the equation $\mu=I+C_-(\mu(v-I))$ gives
  $M=I+C(\mu(v-I))$. Solutions correspond when the products belong to
  the stated boundary spaces and the contour Cauchy operators are bounded.

* **51.8. Small-norm theorem.** On a fixed contour with bounded $L^2$
  Cauchy operators, $\|v-I\|_\infty$ sufficiently small makes
  $I-C_{v-I}$ invertible by a Neumann series. If also $v-I\in L^2$,
  then $\|\mu-I\|_2\leq C\|v-I\|_2$; the Cauchy representation
  controls the solution away from the contour.

### Nonlinear steepest descent

* **51.15. Parametrix error theorem.** Suppose an outer model and local
  models are uniformly invertible and match by $I+O(\varepsilon)$
  on fixed disk boundaries, while remaining jumps are small in
  $L^2\cap L^\infty$. Their quotient with the exact solution solves a
  small-norm problem, giving controlled asymptotics and, with stronger
  expansions of the jumps, successive correction terms.

### Direct and inverse scattering on the line

The negative eigenvalues are $-\kappa_j^2$, $\kappa_j>0$, $R_+$ is the right reflection coefficient, and $c_j>0$ are its Marchenko norming constants. **Admissible scattering data** means data satisfying the reality, positivity, decay, and compatibility conditions of the inverse-scattering theorem, for example data arising from a real Schwartz potential.

* **51.17. Jost solutions.** For real $u\in L^1((1+|x|)\,dx)$,
  $Lf=k^2f$ has solutions $f_\pm(x,k)\sim e^{\pm ikx}$ at
  the corresponding ends. After removal of these exponentials they
  extend analytically to $\operatorname{Im}k>0$ and continuously to
  nonzero real $k$, by Volterra integral equations.

* **51.21. Marchenko reconstruction.** For admissible right scattering
  data put $F(s)=(2\pi)^{-1}\int R_+(k)e^{iks}\,dk+
  \sum c_je^{-\kappa_js}$. The equation
  $K(x,y)+F(x+y)+\int_x^\infty K(x,s)F(s+y)\,ds=0$, $y\geq x$,
  has a unique solution and reconstructs
  $u(x)=-2\,dK(x,x)/dx$.

* **51.23. KdV Lax pair.** With
  $P=-4\partial_x^3+6u\partial_x+3u_x$, the identity $L_t=[P,L]$
  is equivalent to the stated KdV equation. Evolution of eigenfunctions
  by $\psi_t=P\psi$ preserves their spectral parameter.

* **51.24. Linear evolution of scattering data.** For this KdV
  normalization, $R_+(k,t)=R_+(k,0)e^{8ik^3t}$,
  $\kappa_j(t)=\kappa_j(0)$, and
  $c_j(t)=c_j(0)e^{8\kappa_j^3t}$ in the right Marchenko convention.
  Evolving these data and reconstructing solves the Schwartz-class
  Cauchy problem.

* **51.26. Multisoliton determinant.** Reflectionless data give
  $u=-2\partial_x^2\log\det(I+A)$, where
  $A_{ij}=\sqrt{c_i(t)c_j(t)}e^{-(\kappa_i+\kappa_j)x}/
  (\kappa_i+\kappa_j)$. Positivity of $I+A$ gives a smooth real
  solution for positive $c_j$ and distinct positive $\kappa_j$.

### Hamiltonian structure, finite-gap solutions, and lattices

* **51.35. Liouville–Arnold theorem.** On a $2n$-dimensional symplectic
  manifold, $n$ independent commuting first integrals make each compact
  connected regular common level a torus. Near it, action–angle
  coordinates turn the commuting flows into linear translations.

* **51.44. Theta-function solutions.** Finite-gap KdV potentials have
  the form $u=C-2\partial_x^2\log\theta(Ux+Vt+D)$, with vectors
  fixed by normalized differentials of the spectral curve. Appropriate
  real branch points and admissible real divisor data give smooth real
  quasiperiodic solutions; arbitrary complex data need not do so.

* **51.47. Toda Lax equations.** With
  $a_j=\tfrac12e^{(q_j-q_{j+1})/2}$, $b_j=-p_j/2$,
  $\dot a_j=a_j(b_{j+1}-b_j)$ and
  $\dot b_j=2(a_j^2-a_{j-1}^2)$. The Jacobi matrix $J$ satisfies
  $\dot J=[B,J]$, with $B$ its strictly upper part minus its
  strictly lower part, and hence is isospectral.

### Isomonodromy and Painlevé equations

Monodromy data include connection matrices, local exponents, and, at
irregular singularities, Stokes matrices. Isomonodromic deformations preserve
these data while singularity positions or irregular types vary.

PI and PII are $q''=6q^2+x$ and $q''=2q^3+xq+\alpha$. PI–PVI denote the six classical Painlevé equations, with their usual parameter families; the meromorphic-continuation statement uses each equation on its natural independent-variable domain.

* **51.51. Schlesinger equations.** For the Fuchsian system
  $Y_z=\sum_i A_i/(z-a_i)Y$, compatibility with
  $Y_{a_j}=-A_jY/(z-a_j)$ gives
  $\partial_{a_j}A_i=[A_i,A_j]/(a_i-a_j)$ for $i\ne j$ and
  $\partial_{a_i}A_i=-\sum_{j\ne i}[A_i,A_j]/(a_i-a_j)$.
  These equations preserve monodromy; the converse needs the usual
  nonresonance or prescribed local-normalization assumptions.

* **51.54. Painlevé property.** Solutions of PI, PII, and PIV extend
  meromorphically over the finite independent-variable plane. For the
  remaining classical equations the corresponding statement holds on
  the universal cover of the plane with their fixed singularities
  removed. Movable singularities are poles, with the appropriate
  meromorphic interpretation in the dependent variable.

* **51.55. Hastings–McLeod solution.** PII with $\alpha=0$ has a
  distinguished real pole-free solution satisfying
  $q(x)\sim\operatorname{Ai}(x)$ as $x\to+\infty$ and
  $q(x)\sim\sqrt{-x/2}$ as $x\to-\infty$. The positive Airy
  normalization selects it uniquely.

### Orthogonal polynomials, kernels, and boundary transforms

For the varying weight $e^{-nV}$, let $p_{j,n}$ be orthonormal and put
$K_n(x,y)=e^{-n(V(x)+V(y))/2}\sum_{j=0}^{n-1}p_{j,n}(x)p_{j,n}(y)$.

For 51.63–64 assume real analytic confining $V$, with $V(x)/\log(1+|x|)\to\infty$, whose equilibrium measure has one interval of support, positive interior density $\rho$, regular square-root endpoints, and strict exterior variational inequality. These are the regular one-cut hypotheses.

* **51.59. Fokas–Its–Kitaev characterization.** For a positive Schwartz
  weight $w$ on $\mathbb R$, the unique problem
  $Y_+=Y_-\begin{pmatrix}1&w\\0&1\end{pmatrix}$,
  $Y=(I+O(z^{-1}))\operatorname{diag}(z^n,z^{-n})$
  has $Y_{11}$ equal to the monic orthogonal polynomial of degree $n$.
  Its other entries are neighboring polynomials and their Cauchy transforms.

* **51.63. Bulk universality.** Under the regular one-cut hypotheses, the weighted correlation
  kernel satisfies
  $[n\rho(x_0)]^{-1}K_n(x_0+u/(n\rho(x_0)),
  x_0+v/(n\rho(x_0)))\to\sin(\pi(u-v))/(\pi(u-v))$
  at each interior point with $\rho(x_0)>0$, locally uniformly in $u,v$.

* **51.64. Soft-edge universality.** At a regular right endpoint $b$,
  an appropriate positive constant $c$ gives
  $(cn^{2/3})^{-1}K_n(b+u/(cn^{2/3}),b+v/(cn^{2/3}))
  \to K_{\mathrm{Ai}}(u,v)$, where
  $K_{\mathrm{Ai}}(u,v)=[\operatorname{Ai}(u)\operatorname{Ai}'(v)
  -\operatorname{Ai}'(u)\operatorname{Ai}(v)]/(u-v)$.

* **51.66. Tracy–Widom formula.** The Airy-kernel determinant on
  $L^2(s,\infty)$ is
  $F_2(s)=\exp[-\int_s^\infty(x-s)q(x)^2\,dx]$, with $q$
  the Hastings–McLeod solution. It is the limiting largest-eigenvalue
  distribution at a regular soft edge after centering and scaling.

* **51.67. Longest increasing subsequences.** If $L_N$ is the longest
  increasing subsequence of a uniformly random permutation of $N$
  letters, then $(L_N-2\sqrt N)/N^{1/6}$ converges in distribution
  to $F_2$. Orthogonal-polynomial and Fredholm determinant formulations
  connect this theorem to the same Painlevé asymptotics.

## 52. Geometric analysis on manifolds

Curvature tensors, the Levi-Civita connection, geodesics, Hopf–Rinow, Riemannian volume, and parts of Morse analysis are covered. The missing geometric-analysis layer is much larger: comparison, analytic curvature identities, harmonic maps, minimal submanifolds, geometric flows, and gauge and sub-Riemannian analysis. Integral Stokes and manifold elliptic theory are important intervening prerequisites. Calabi–Yau and Hodge results are assigned to Sections 45 and 53.

Sources: [mathematical synopsis](SYNOPSIS52.md); [combined coverage inventory](Mathlib52.md).

Manifolds are connected and smooth, and metrics are smooth. A *closed*
manifold is compact without boundary; *complete* means geodesically complete,
without boundary unless
specified. Write $\Delta=\operatorname{div}\nabla$, so $-\Delta\geq0$,
$dV$ for volume, $\operatorname{Ric}$ for Ricci curvature, and $R$ for
scalar curvature. Constants in local estimates may depend on the indicated
geometric bounds. A uniform estimate over varying metrics requires such
bounds; compactness of each individual manifold is insufficient.

### Geodesics, curvature comparison, and compactness

* **52.3. Jacobi fields and second variation.** A geodesic variation has
  variational field satisfying $D_t^2J+\mathrm{Rm}(J,\dot\gamma)
  \dot\gamma=0$. The index form
  $I(V,V)=\int(|D_tV|^2-\langle\mathrm{Rm}(V,\dot\gamma)
  \dot\gamma,V\rangle)dt$ governs minimality and conjugate points.

* **52.5. Rauch comparison.** Upper and lower sectional-curvature
  bounds compare the lengths of perpendicular Jacobi fields with model
  space fields having the same initial data, up to the relevant first
  conjugate point. These comparisons control the exponential map and
  Hessians of distance.

* **52.6. Bonnet–Myers theorem.** For $n\geq2$, a complete $n$-manifold with
  $\operatorname{Ric}\geq(n-1)k g$, $k>0$, is compact with
  diameter at most $\pi/\sqrt k$ and finite fundamental group.

* **52.7. Bishop–Gromov comparison.** If
  $\operatorname{Ric}\geq(n-1)k g$, then
  $\operatorname{Vol}B(p,r)/V_k(r)$ is nonincreasing in $r$,
  within the model radius range. In particular nonnegative Ricci
  curvature gives $\operatorname{Vol}B(p,2r)\leq2^n
  \operatorname{Vol}B(p,r)$.

* **52.9. Cheeger–Gromoll splitting.** A complete connected manifold
  with nonnegative Ricci curvature that contains a line is isometric
  to $\mathbb R\times N$. A line is a geodesic minimizing distance
  between each pair of its points.

* **52.10. Compactness with controlled geometry.** Closed
  $n$-manifolds with $|\operatorname{sec}|\leq C$,
  diameter at most $D$, and volume at least $v>0$ have a
  subsequence converging, after diffeomorphisms, in $C^{1,\alpha}$
  for each $\alpha<1$. Bounds on all covariant derivatives of
  curvature improve this to smooth convergence. The hypotheses also
  yield finiteness of diffeomorphism types.

### Functional inequalities, harmonic functions, and heat

* **52.15. Bochner identity.** For a smooth function,
  $\tfrac12\Delta|\nabla u|^2=|\nabla^2u|^2+
  \langle\nabla u,\nabla\Delta u\rangle+
  \operatorname{Ric}(\nabla u,\nabla u)$. Integrated on a closed
  manifold, it converts curvature bounds into gradient and spectral estimates.

* **52.17. Cheng–Yau gradient estimate.** If a complete manifold has
  $\operatorname{Ric}\geq-(n-1)K g$ and $u>0$ is harmonic on
  $B(p,2r)$, then
  $\sup_{B(p,r)}|\nabla\log u|\leq C_n(r^{-1}+\sqrt K)$.

* **52.19. Li–Yau differential estimate.** On a complete manifold with
  nonnegative Ricci curvature, a positive heat solution satisfies
  $|\nabla\log u|^2-\partial_t\log u\leq n/(2t)$.

* **52.25. Lichnerowicz–Obata theorem.** For $n\geq2$, if a closed connected
  $n$-manifold has $\operatorname{Ric}\geq(n-1)k g$, $k>0$,
  then $\lambda_1\geq nk$. Equality characterizes the round sphere
  of sectional curvature $k$.

### Conformal geometry and critical equations

The conformal Laplacian is $L_g=-4(n-1)(n-2)^{-1}\Delta+R_g$.

* **52.29. Yamabe theorem.** Every conformal class on a closed
  $n$-manifold, $n\geq3$, contains a smooth metric of constant scalar
  curvature minimizing the normalized total scalar curvature in that class.
  Equivalently, the Yamabe quotient attains its infimum at a positive
  smooth solution of $L_gu=\lambda u^{(n+2)/(n-2)}$.

### Harmonic maps, regularity, and bubbling

For $u:(M,g)\to(N,h)$, put $E(u)=\tfrac12\int|du|^2dV$.
The tension field is $\tau(u)=\operatorname{tr}_g\nabla du$;
harmonic maps are critical points of $E$ and satisfy $\tau(u)=0$.

* **52.35. Eells–Sampson existence.** Every homotopy class of maps
  between closed manifolds has a smooth harmonic representative if
  the target has nonpositive sectional curvature. It minimizes energy
  within the homotopy class.

* **52.39. Two-dimensional weak regularity.** Every weakly harmonic
  $W^{1,2}$ map from a smooth surface into a compact smooth
  Riemannian manifold is smooth. The conservation-law and moving-frame
  structure supplies the compensation absent from a general quadratic system.

* **52.41. Bubble convergence on surfaces.** A bounded-energy sequence
  of harmonic maps from a fixed closed surface to a compact target has
  a subsequence converging smoothly away from finitely many points.
  Finitely many rescaled harmonic spheres account for all lost energy;
  the limiting energy is the energy of the base map plus their energies.

### Minimal submanifolds and Plateau problems

* **52.46. Stability operator.** For a two-sided minimal hypersurface,
  the second variation in direction $f\nu$ is
  $\int(|\nabla f|^2-(|A|^2+\operatorname{Ric}(\nu,\nu))f^2)$.
  Stability means this quadratic form is nonnegative for all compactly
  supported $f$.

* **52.50. Douglas–Radó Plateau theorem.** Every rectifiable Jordan
  curve in Euclidean space spans a least-area disk in the parametric
  class. It admits a conformal harmonic disk parametrization, smooth
  in the interior with possible branch points in general codimension.

* **52.54. Bernstein theorem for graphs.** Every smooth entire
  minimal graph $\mathbb R^m\to\mathbb R$ is affine for
  $m\leq7$. Nonaffine entire examples occur in higher dimensions,
  so the dimension restriction is essential.

### Mean curvature flow

Here $F_t:M^m\to\mathbb R^{m+1}$ evolves by $\partial_tF=
\mathbf H$. Write $H$ for scalar mean curvature with a consistent
normal choice, and $A$ for the second fundamental form.

* **52.56. Short-time existence.** Every smooth closed immersed
  hypersurface has a unique smooth mean curvature flow for a short
  time, up to the usual equivalent parametrized formulations. A graph
  evolves by $u_t=\sqrt{1+|\nabla u|^2}
  \operatorname{div}(\nabla u/\sqrt{1+|\nabla u|^2})$.

* **52.59. Huisken monotonicity.** For $t<t_0$ put
  $\rho=(4\pi(t_0-t))^{-m/2}
  e^{-|x-x_0|^2/(4(t_0-t))}$. Then
  $d\int_{M_t}\rho\,d\mu/dt=-\int_{M_t}\rho
  |\mathbf H+(x-x_0)^\perp/(2(t_0-t))|^2d\mu$.
  Equality characterizes self-similar shrinkers about $(x_0,t_0)$.

* **52.60. Convex hypersurface convergence.** A smooth closed strictly
  convex hypersurface in Euclidean space remains convex and shrinks
  to a point in finite time. After recentering and volume or area
  normalization it converges smoothly to a round sphere.

### Ricci flow and curvature normalization

Ricci flow is $\partial_tg=-2\operatorname{Ric}$.
A gradient Ricci soliton satisfies
$\operatorname{Ric}+\nabla^2f=\lambda g$, with positive, zero, or
negative $\lambda$ giving shrinking, steady, or expanding solutions.

* **52.64. Hamilton–DeTurck existence.** A smooth metric on a closed
  manifold has a unique smooth Ricci flow for a short time. Adding a
  Lie derivative fixes diffeomorphism invariance and gives a strictly
  parabolic system; pulling back recovers Ricci flow.

* **52.69. Hamilton compactness.** A sequence of complete pointed
  Ricci flows with uniform curvature bounds on compact time intervals
  and a positive injectivity-radius bound at the base points at one
  time has a subsequence converging smoothly on compact subsets,
  after pointed diffeomorphisms.

* **52.71. Perelman $\mathcal W$ monotonicity.** Put
  $\mathcal W=\int[\tau(R+|\nabla f|^2)+f-n]
  (4\pi\tau)^{-n/2}e^{-f}dV$, with the weighted measure of mass
  one and $\tau_t=-1$. If
  $f_t=-\Delta f+|\nabla f|^2-R+n/(2\tau)$, then
  $d\mathcal W/dt=2\tau\int|
  \operatorname{Ric}+\nabla^2f-g/(2\tau)|^2
  (4\pi\tau)^{-n/2}e^{-f}dV$.

* **52.72. No local collapsing.** For a closed Ricci flow on a finite
  time interval there is $\kappa>0$ such that a metric ball of
  radius $r$ with $|\mathrm{Rm}|\leq r^{-2}$ on the appropriate
  parabolic neighborhood has volume at least $\kappa r^n$,
  for bounded scales. Entropy gives the uniform constant.

* **52.73. Hamilton's three-dimensional convergence.** A closed
  three-manifold with positive Ricci curvature evolves under
  volume-normalized Ricci flow to a constant-positive-sectional-curvature
  metric. It is therefore a spherical space form.

* **52.75. Three-dimensional geometrization.** Every closed oriented
  three-manifold decomposes along spheres into prime pieces and along
  incompressible tori in those pieces into pieces admitting Thurston
  geometries on their interiors. Ricci flow with surgery establishes
  this classification; in particular every closed simply connected three-manifold is
  diffeomorphic to $S^3$.

### Symplectic, gauge, and sub-Riemannian analysis

A symplectic form is a closed nondegenerate two-form $\omega$; an
$\omega$-compatible almost complex structure $J$ makes
$\omega(\cdot,J\cdot)$ a Riemannian metric. A $J$-holomorphic map
satisfies $du\circ j=J\circ du$.

* **52.78. Symplectic nonsqueezing.** A symplectic embedding of the
  ball $B^{2n}(r)$ into the cylinder
  $B^2(R)\times\mathbb R^{2n-2}$ requires $r\leq R$.
  Holomorphic-curve area bounds give the obstruction.

* **52.79. Morse homology.** For a Morse function and Morse–Smale
  metric on a closed manifold, counting gradient trajectories of
  index difference one defines a differential with square zero.
  Compactification by broken trajectories proves this identity, and
  the resulting homology is singular homology.

* **52.80. Hamiltonian Floer continuation.** On a closed symplectically
  aspherical manifold, $\omega|_{\pi_2}=c_1|_{\pi_2}=0$,
  a nondegenerate Hamiltonian has a Floer complex generated by its
  contractible periodic orbits. Finite-energy cylinders define the
  differential, continuation identifies its homology with singular
  homology, and the number of such orbits is at least the sum of
  Betti numbers over a field.

For a connection $A$ on a bundle with compact structure group, let
$F_A=dA+A\wedge A$ and $d_A$ be its covariant exterior derivative.
Gauge transformations change local connection matrices while preserving
curvature norms.

* **52.83. Uhlenbeck gauge theorem.** On a four-dimensional ball,
  sufficiently small $\|F_A\|_{L^2}$ permits a Coulomb gauge
  $d^*a=0$ with vanishing normal component at the boundary and
  $\|a\|_{W^{1,2}}\leq C\|F_A\|_2$, in scale-normalized norms.

* **52.84. Gauge compactness.** On a closed $n$-manifold, curvature
  bounds in $L^p$, $p>n/2$, give weak $W^{1,p}$ compactness
  modulo gauge. For Yang–Mills connections, elliptic regularity improves
  this to smooth compactness modulo gauge. Critical four-dimensional
  $L^2$ bounds instead allow point concentration and bubbling.

A sub-Riemannian structure is an inner product on a bracket-generating
distribution $\mathcal D\subset TM$. Its distance is the infimum of
lengths of curves tangent to $\mathcal D$.

* **52.85. Rashevskii–Chow theorem.** On a connected bracket-generating
  sub-Riemannian manifold, every two points are joined by a horizontal
  curve. The resulting finite distance induces the manifold topology.

* **52.87. Ball–box theorem.** In privileged coordinates at an
  equiregular point with weights $w_i$, a sufficiently small metric
  ball is trapped between coordinate boxes $|x_i|\leq c r^{w_i}$
  with two fixed positive constants $c$. Thus its volume is comparable
  to $r^Q$, $Q=\sum_iw_i$.

* **52.90. Positive mass theorem in dimension three.** A smooth connected
  complete asymptotically flat three-manifold with finitely many ends,
  integrable nonnegative scalar curvature, and decay
  $g_{ij}-\delta_{ij}=O_2(r^{-q})$, $q>1/2$, has nonnegative
  ADM mass at every end. Zero mass at an end forces the manifold
  to be Euclidean space. Here ADM mass is the limit
  $(16\pi)^{-1}\int_{S_r}(\partial_jg_{ij}-\partial_ig_{jj})
  \nu^i\,dS$ in an asymptotically flat chart.

## 53. Elliptic operators on manifolds, index theory, and spectral geometry

Abstract Fredholm stability and Euclidean bounded-domain variational eigenbases are covered. The missing manifold layer comprises elliptic realization, Hodge representatives, heat and spectral asymptotics, Dirac operators and index formulas, and geodesic spectral geometry. An abstract index integer does not evaluate an elliptic symbol class. An eigenbasis for one domain problem does not establish the Weyl, nodal, or quantum-ergodic theorems below.

Sources: [mathematical synopsis](SYNOPSIS53.md); [combined coverage inventory](Mathlib53.md).

Unless specified otherwise, $M$ is a smooth closed connected Riemannian
$n$-manifold and vector bundles are smooth Hermitian bundles with compatible
connections. Write $\Delta_k=dd^*+d^*d$ for the nonnegative Hodge
Laplacian and $\Delta=\Delta_0=-\operatorname{div}\nabla$ on functions.
Scalar eigenvalues are $0=\lambda_0^2<\lambda_1^2\leq\cdots$,
counted with multiplicity; thus $\lambda$ denotes frequency, not energy.
Characteristic forms use the usual Chern–Weil normalization, so that
$\operatorname{ch}(E)=\operatorname{tr}\exp(iF^E/(2\pi))$ and
their cohomology classes are independent of the chosen connections.

### Elliptic operators and global analysis

In 53.5, $P:C^\infty(E)\to C^\infty(F)$ is an elliptic differential operator of order $m$ between bundles on the closed manifold; ellipticity means its principal symbol is invertible for every nonzero covector.

* **53.5. Fredholm alternative.** The map
  $P:H^{s+m}(E)\to H^s(F)$ is Fredholm. Its kernel and cokernel
  are finite-dimensional smooth spaces, and
  $Pu=f$ is solvable precisely when $f$ annihilates $\ker P^*$.

* **53.9. Complete Dirac operators.** A symmetric Dirac-type operator
  on a complete manifold is essentially self-adjoint on compactly
  supported smooth sections. Compact resolvent and a finite-dimensional
  kernel do not follow from completeness alone.

### Elliptic complexes and Hodge theory

An elliptic complex consists of differential operators $d_j$ with
$d_{j+1}d_j=0$ whose symbol sequence is exact at nonzero covectors.
For the first-order complexes here, its Laplacians are
$L_j=d_j^*d_j+d_{j-1}d_{j-1}^*$.

* **53.12. Hodge theorem for elliptic complexes.** On a closed manifold,
  each complex cohomology class has a unique representative in
  $\ker L_j$. Thus all cohomology groups are finite-dimensional.

* **53.16. Hodge theory with boundary.** On a compact oriented manifold with
  smooth boundary, harmonic forms satisfying absolute conditions
  $\iota_\nu\alpha=\iota_\nu d\alpha=0$ represent
  $H^k(M)$; relative conditions
  $\nu^\flat\wedge\alpha=\nu^\flat\wedge d^*\alpha=0$
  represent $H^k(M,\partial M)$. The Hodge star exchanges the two.

* **53.18. Kähler Hodge decomposition.** On a compact Kähler
  manifold, $\Delta_d=2\Delta_{\bar\partial}=2\Delta_\partial$.
  Consequently $H^k(M;\mathbb C)=\bigoplus_{p+q=k}H^{p,q}(M)$
  and $h^{p,q}=h^{q,p}$.

* **53.19. Hard Lefschetz theorem.** For a compact Kähler manifold of
  complex dimension $d$, multiplication by $[\omega]^{d-k}$
  is an isomorphism $H^k(M;\mathbb C)\to H^{2d-k}(M;\mathbb C)$
  for $k\leq d$. The Lefschetz decomposition reduces cohomology
  to primitive classes.

* **53.20. Witten deformation and Morse inequalities.** For a Morse
  function $f$, $d_t=e^{-tf}de^{tf}$ has the same cohomology as
  $d$. Its degree-$k$ Laplacian has, for large $t$, one small
  eigenvalue per index-$k$ critical point, while the remaining spectrum
  is separated by a gap of order $t$. This yields the weak and strong
  Morse inequalities and the alternating Euler-characteristic identity.

### Heat coefficients, Weyl laws, and spectral invariants

In 53.28, $c_M=(2\pi)^{-n}\omega_n\operatorname{Vol}(M)$ and $\omega_n$ is the Euclidean unit-ball volume.

* **53.21. Local heat expansion.** A Laplace-type operator on a
  closed manifold has a smooth heat kernel with diagonal expansion
  $K_t(x,x)\sim(4\pi t)^{-n/2}\sum_{j=0}^\infty t^ja_j(x)$,
  valid with all derivatives after finite truncation and the corresponding
  remainder bounds. Each coefficient is a universal local curvature expression.

* **53.24. Weyl law.** For
  $N(\Lambda)=\#\{j:\lambda_j\leq\Lambda\}$,
  $N(\Lambda)\sim(2\pi)^{-n}\omega_n\operatorname{Vol}(M)
  \Lambda^n$. More generally a positive scalar elliptic operator
  of order $m$ has counting asymptotic given by the cotangent
  volume of $\{\sigma_m(P)\leq1\}$ times $\Lambda^{n/m}$
  when its eigenvalues are counted by energy.

* **53.28. Two-term boundary Weyl law.** On a compact manifold with
  smooth boundary, if periodic billiard trajectories have measure zero,
  the Dirichlet and Neumann counting functions satisfy
  $N_{D/N}(\Lambda)=c_M\Lambda^n
  \mp\tfrac14(2\pi)^{-(n-1)}\omega_{n-1}
  \operatorname{Area}(\partial M)\Lambda^{n-1}
  +o(\Lambda^{n-1})$. The dynamical hypothesis is essential to
  this standard sharp two-term formulation.

* **53.30. Spectral zeta function.** For a positive elliptic operator,
  $\zeta_P(s)=\sum_{\mu_j>0}\mu_j^{-s}$ converges initially
  in a right half-plane and extends meromorphically by the Mellin
  transform of its heat trace. It is regular at zero for classical
  elliptic differential operators on closed manifolds.

* **53.32. Eta invariant.** For a self-adjoint first-order elliptic
  differential operator on a closed manifold,
  $\eta_D(s)=\sum_{\mu\ne0}\operatorname{sign}(\mu)|\mu|^{-s}$
  has meromorphic continuation regular at zero. The reduced invariant
  is $\bar\eta(D)=(\eta_D(0)+\dim\ker D)/2$; one may also
  regard its value modulo integers.

* **53.34. Cheeger–Müller theorem.** Ray–Singer analytic torsion agrees
  with Reidemeister torsion for orthogonal flat bundles on closed
  manifolds, with the corresponding identification of determinant-line
  metrics in the nonacyclic case.

### Dirac operators and index theorems

A Clifford action satisfies $c(\xi)c(\eta)+c(\eta)c(\xi)
=-2\langle\xi,\eta\rangle I$. A compatible connection on a Clifford
module gives $D=\sum_jc(e^j)\nabla_{e_j}$. In even dimension the
spinor bundle splits as $S^+\oplus S^-$ and $D$ is odd.

* **53.38. Schrödinger–Lichnerowicz formula.** For spinors,
  $D^2=\nabla^*\nabla+R/4$. Twisting by $E$ adds the Clifford
  contraction of its curvature, so scalar-curvature positivity alone
  need not imply vanishing for an arbitrary twist.

* **53.39. Positive-scalar-curvature obstruction.** If $R\geq0$
  and is positive somewhere on a closed connected spin manifold,
  $\ker D=0$. In even dimension its $\widehat A$ genus is
  therefore zero; a nonzero spin index obstructs positive scalar curvature.

* **53.41. McKean–Singer identity.** For an odd self-adjoint Dirac
  operator on a graded bundle,
  $\operatorname{ind}D^+=\operatorname{Str}e^{-tD^2}$ for every
  $t>0$. Nonzero eigenvalues cancel between the two gradings.

* **53.42. Local index theorem.** For a twisted spin Dirac operator,
  the supertrace of the diagonal heat kernel, multiplied by $dV$,
  converges as $t\downarrow0$
  to the top-degree form $[\widehat A(TM,\nabla)\operatorname{ch}
  (E,\nabla^E)]_n$. Getzler rescaling identifies the local density
  and explains cancellation of the apparently divergent heat terms.

* **53.43. Atiyah–Singer theorem.** The analytic index of an elliptic
  operator on a closed manifold equals the topological pushforward
  $\operatorname{ind}_{\mathrm{top}}[\sigma(P)]\in K^0(\mathrm{pt})
  =\mathbb Z$. The pushforward is defined by embedding, the Thom
  isomorphism, and Bott periodicity; it depends only on the symbol class.

* **53.44. Spin index formula.** On a closed even-dimensional spin
  manifold,
  $\operatorname{ind}D_E^+=\langle\widehat A(TM)
  \operatorname{ch}(E),[M]\rangle$.

* **53.46. Chern–Gauss–Bonnet theorem.** On a closed oriented
  even-dimensional manifold, the Euler characteristic is the integral
  of the Euler curvature form, the normalized Pfaffian of curvature.
  It is the index of the even-to-odd de Rham operator.

* **53.47. Hirzebruch signature theorem.** On a closed oriented
  $4k$-manifold, the signature of the middle-dimensional intersection
  form is $\langle L(TM),[M]\rangle$, the index of the signature
  operator with its chirality grading.

* **53.48. Hirzebruch–Riemann–Roch theorem.** For a holomorphic bundle
  $E$ on a compact complex manifold,
  $\sum_q(-1)^q\dim H^{0,q}(M,E)=
  \langle\operatorname{Td}(T^{1,0}M)\operatorname{ch}(E),[M]\rangle$.

* **53.49. Families index theorem.** A smooth family of elliptic
  operators over a compact parameter space has an index class in
  $K^0(B)$, even when kernel dimensions jump. For an even-dimensional
  spin fibration, its Chern character is the fiber integral
  $\int_{M/B}\widehat A(T(M/B))\operatorname{ch}(E)$.

### Boundary operators, spectral flow, coverings, and positive bundles

For 53.54 take an even-dimensional compact spin manifold with boundary, a twisted Dirac operator having product form $D=c(du)(\partial_u+B)$ near the boundary, and the APS condition $\Pi_{\geq0}(B)(s|_{\partial M})=0$. The induced boundary operator $B$ and the inward collar coordinate use this fixed convention.

* **53.54. Atiyah–Patodi–Singer formula.** In the product convention
  for this APS condition,
  $\operatorname{ind}D^+_{\mathrm{APS}}=
  \int_M\widehat A(TM)\operatorname{ch}(E)
  -[\eta_B(0)+\dim\ker B]/2$.
  For nonproduct geometry the local integral acquires a boundary
  transgression correction.

* **53.55. Spectral flow as index.** For a smooth periodic family
  $B_t$ of self-adjoint elliptic operators, spectral flow, counting
  crossings from negative to positive, equals the index of
  $\partial_t+B_t$ on the mapping torus. Interval formulations use
  the corresponding endpoint spectral boundary conditions.

* **53.58. Atiyah's $L^2$ index theorem.** Lift an elliptic operator
  from a closed manifold to a regular covering with deck group
  $\Gamma$. The difference of the von Neumann dimensions of its
  two $L^2$ kernels equals the ordinary index downstairs. These
  dimensions can be finite even when the ordinary kernel dimensions
  upstairs are infinite.

* **53.60. Bergman kernel asymptotics.** Let $L$ be a positive
  Hermitian holomorphic line bundle on a compact complex
  $d$-manifold, normalized by $(i/2\pi)R^L=\omega$, and use
  volume $\omega^d/d!$. For the projection onto $H^0(M,L^p)$,
  $B_p(x,x)\sim p^d+b_1(x)p^{d-1}+\cdots$ in every $C^k$
  norm. Integration recovers Riemann–Roch growth, and the higher
  coefficient functions are local curvature invariants.

### Eigenvalue inequalities and nodal geometry

* **53.65. Szegő–Weinberger theorem.** Among bounded connected smooth Euclidean
  domains of fixed volume, the ball maximizes the first positive
  Neumann eigenvalue. This is the counterpart of the Dirichlet
  minimization theorem with the opposite extremal direction.

* **53.66. Cheeger spectral bound.** On a closed connected manifold,
  $\lambda_1^2\geq h(M)^2/4$, with $h$ the separating
  area-to-volume isoperimetric constant. For Dirichlet domains use
  the corresponding domain Cheeger constant.

* **53.68. Steklov spectrum.** On a compact connected manifold with
  smooth nonempty boundary, the Dirichlet-to-Neumann operator for
  harmonic functions is a nonnegative self-adjoint elliptic operator
  of order one, with principal symbol $|\xi|$.
  Its counting function is
  $N_S(\sigma)\sim(2\pi)^{-(n-1)}\omega_{n-1}
  \operatorname{Area}(\partial M)\sigma^{n-1}$ for $n\geq2$.

* **53.69. Courant nodal theorem.** The $j$th eigenfunction in an
  ordered real orthonormal basis, with eigenvalues indexed starting
  at one, has at most $j$ nodal domains. This formulation also
  covers multiplicities by fixing the ordered basis.

* **53.71. Analytic nodal-volume bounds.** On a closed real analytic
  manifold of dimension $n\geq2$, a real nonconstant eigenfunction
  satisfies $c_M\lambda\leq\mathcal H^{n-1}
  (\{\phi_\lambda=0\})\leq C_M\lambda$.
  The analytic upper bound is not a consequence of smooth elliptic
  regularity alone.

* **53.72. Sogge eigenfunction bounds.** For $\|\phi_\lambda\|_2=1$,
  $\|\phi_\lambda\|_p\leq C\lambda^{\delta(p)}$, $2\leq p\leq\infty$,
  where $\delta(p)=\max\{\tfrac{n-1}{2}(\tfrac12-\tfrac1p),
  n(\tfrac12-\tfrac1p)-\tfrac12\}$, $n\geq2$.
  Zonal functions and highest-weight harmonics on spheres show the
  sharpness of the two regimes.

### Geodesic dynamics, trace formulas, and scattering

* **53.76. Quantum ergodicity.** If the geodesic flow is ergodic with
  respect to Liouville measure, every orthonormal eigenbasis has a
  density-one subsequence whose expectations against all order-zero
  observables tend to the normalized Liouville average of their symbols.
  The theorem permits an exceptional density-zero subsequence.

* **53.77. Wave trace and lengths.** The distribution
  $\operatorname{Tr}e^{it\sqrt\Delta}$ is smooth away from zero
  and the signed lengths of closed geodesics. For clean nondegenerate
  families the leading singular terms are determined by the linearized
  return map and Maslov data. Cancellation can prevent an arbitrary
  closed-geodesic length from being visible as a singularity.

* **53.78. Selberg trace formula.** For a closed hyperbolic surface,
  write $\lambda_j^2=1/4+r_j^2$ and take an admissible even test
  function $h$, with $g(\ell)=(2\pi)^{-1}\int h(r)e^{-ir\ell}dr$.
  Then
  $\sum_jh(r_j)=\operatorname{Area}(M)(4\pi)^{-1}
  \int_{\mathbb R}r\tanh(\pi r)h(r)dr+
  \sum_{\gamma\ \mathrm{primitive}}\sum_{k\geq1}
  \ell_\gamma g(k\ell_\gamma)/(2\sinh(k\ell_\gamma/2))$.
  The primitive geodesics use the standard conjugacy-class convention;
  cusps introduce additional continuous-spectrum and scattering terms.

* **53.79. Hyperbolic resonances.** For an infinite-area convex-cocompact hyperbolic
  surface, the resolvent $(\Delta-s(1-s))^{-1}$ continues
  meromorphically from its initial half-plane as an operator from
  compactly supported smooth functions to smooth functions locally.
  Its finite-rank poles define resonances. The continuous spectrum is
  $[1/4,\infty)$, with only finitely many $L^2$ eigenvalues below
  $1/4$; poles on other sheets encode scattering rather than ordinary
  $L^2$ eigenfunctions.

* **53.80. Spectral information and nonuniqueness.** The scalar spectrum
  determines dimension, volume, integrated scalar curvature, and the
  higher integrated heat coefficients. It does not determine the
  isometry class: closed nonisometric isospectral manifolds exist,
  including flat tori in suitable dimensions and hyperbolic surfaces.
