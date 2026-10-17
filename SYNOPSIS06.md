# Synopsis: Probability, measure-theoretic foundations, and limit theory

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis describes the common graduate core of Section 06 of
[CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md). It proceeds from
independence and conditioning to laws of large numbers, distributional limits,
martingales, and functional limit theory. Infinitely divisible laws, Poisson
random measures, exchangeability, and the basic large-deviation theorems are
included because they recur across several of the broad courses and monographs.
The more specialized theories of random graphs, Gibbs measures, and spin glasses
listed in this section have their own substantial cores.

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

## Independence, construction, and zero–one laws

The **law** of $X$ is $\mathbb P\circ X^{-1}$. A family of $\sigma$-fields is
**independent** if the probabilities of finite intersections factor; random
variables are independent when their generated $\sigma$-fields are. The
**tail $\sigma$-field** of a sequence is
$\bigcap_n\sigma(X_n,X_{n+1},\ldots)$.

* **1. Kolmogorov extension theorem.** A consistent family of finite-dimensional
  probability distributions with standard Borel coordinate spaces determines a
  unique law on the product $\sigma$-algebra. In particular, independent
  sequences with prescribed marginal laws can be constructed.
* **2. Independence and integration.** Independence of $X,Y$ identifies their
  joint law with the product of their marginal laws. Thus
  $\mathbb E[f(X)g(Y)]=\mathbb E f(X)\mathbb E g(Y)$ for integrable factors;
  conversely, factorization for bounded measurable test functions characterizes
  independence.
* **3. First Borel–Cantelli lemma.** If $\sum_n\mathbb P(A_n)<\infty$, then
  $\mathbb P(A_n\text{ infinitely often})=0$.
* **4. Second Borel–Cantelli lemma.** For independent events, if
  $\sum_n\mathbb P(A_n)=\infty$, then
  $\mathbb P(A_n\text{ infinitely often})=1$.
* **5. Kolmogorov zero–one law.** The tail $\sigma$-field of independent random
  variables is trivial: every tail event has probability zero or one.
* **6. Hewitt–Savage zero–one law.** For an independent identically distributed
  sequence, any event in its generated $\sigma$-field invariant under all finite
  permutations has probability zero or one.

## Conditional expectation and conditional distributions

For $X\in L^1$ and $\mathcal G\subseteq\mathcal F$, the **conditional
expectation** $\mathbb E[X\mid\mathcal G]$ is a $\mathcal G$-measurable
integrable variable $Y$ with $\int_GY\,d\mathbb P=\int_GX\,d\mathbb P$ for all
$G\in\mathcal G$. A **regular conditional distribution** is a probability
kernel representing these conditional probabilities simultaneously.

* **7. Existence and uniqueness of conditioning.** Conditional expectation
  exists and is unique almost surely; it is linear, positive, preserves constants,
  and preserves expectations.
* **8. Tower and pull-out properties.** If $\mathcal H\subseteq\mathcal G$, then
  $\mathbb E[\mathbb E[X\mid\mathcal G]\mid\mathcal H]
  =\mathbb E[X\mid\mathcal H]$. If $Z$ is $\mathcal G$-measurable and bounded,
  $\mathbb E[ZX\mid\mathcal G]=Z\mathbb E[X\mid\mathcal G]$. The same formula
  holds under the usual integrability assumptions on unbounded products.
* **9. Conditional Jensen and contraction.** For convex $\Phi$ with the needed
  integrability,
  $\Phi(\mathbb E[X\mid\mathcal G])\leq\mathbb E[\Phi(X)\mid\mathcal G]$.
  Consequently conditional expectation is a contraction on $L^p$,
  $1\leq p\leq\infty$; on $L^2$ it is orthogonal projection onto
  $L^2(\mathcal G)$.
* **10. Regular conditional laws and disintegration.** For random elements
  $X,Y$ in standard Borel spaces, there is a kernel $K(y,dx)$ such that
  $$\mathbb E[f(X)\mid Y]=\int f(x)K(Y,dx).$$
  It is unique for almost every $y$ under the law of $Y$, and the joint law is
  $\mathbb P_Y(dy)K(y,dx)$.
* **11. Conditioning under independence.** If $X$ is independent of
  $\mathcal G$, then $\mathbb E[f(X)\mid\mathcal G]=\mathbb E f(X)$.
  More generally, if $Y$ is $\mathcal G$-measurable and $X$ independent of it,
  $\mathbb E[h(X,Y)\mid\mathcal G]=\int h(x,Y)\,d\mathbb P_X(x)$ for
  nonnegative measurable or integrable $h$.

## Convergence of random variables and probability laws

**Convergence in probability** is convergence in measure for $\mathbb P$.
**Uniform integrability** of $\{X_n\}$ means
$\sup_n\mathbb E[|X_n|1_{\{|X_n|>R\}}]\to0$ as $R\to\infty$.
Weak convergence of laws is tested against bounded continuous functions.

* **12. Relations among convergences.** Almost-sure convergence and $L^p$
  convergence, $p>0$, each imply convergence in probability, which implies
  convergence in distribution. Convergence in probability is equivalent to
  every subsequence having a further almost-surely convergent subsequence.
* **13. Uniform integrability criterion for $L^1$ convergence.** If
  $X_n\to X$ in probability, then $X_n\to X$ in $L^1$ exactly when $\{X_n\}$ is
  uniformly integrable. A uniform bound on $\mathbb E|X_n|^{1+\delta}$,
  $\delta>0$, is sufficient for uniform integrability.
* **14. Portmanteau theorem.** On a metric space, $\mu_n\Rightarrow\mu$ is
  equivalent to the closed-set upper bound, the open-set lower bound, or
  convergence on all Borel $\mu$-continuity sets.
* **15. Continuous mapping theorem.** If $X_n\Rightarrow X$ and a measurable
  map $g$ is continuous outside a set of $\mathbb P_X$-measure zero, then
  $g(X_n)\Rightarrow g(X)$.
* **16. Slutsky's theorem.** For Euclidean random vectors, if
  $X_n\Rightarrow X$ and $Y_n\to c$ in probability for a constant $c$, then
  $(X_n,Y_n)\Rightarrow(X,c)$. Sums and products have the corresponding limits;
  quotients do also when the limiting denominator is nonzero.
* **17. Prokhorov's theorem.** A family of probability measures on a Polish
  space is relatively compact for weak convergence exactly when it is tight.
* **18. Skorokhod representation.** If $\mu_n\Rightarrow\mu$ on a Polish space,
  there are random elements $Y_n,Y$ on one probability space with these laws
  such that $Y_n\to Y$ almost surely.
* **19. Maximal coupling.** For probabilities $\mu,\nu$ on a standard Borel
  space, every coupling satisfies
  $\sup_A|\mu(A)-\nu(A)|\leq\mathbb P(X\ne Y)$, and some coupling attains
  equality. Thus total variation controls convergence through the probability
  that coupled variables disagree.

## Independent sums, random series, and laws of large numbers

* **20. Kolmogorov maximal inequality.** For independent centered variables
  with finite variances,
  $$\mathbb P\!\left(\max_{k\leq n}|S_k|\geq\lambda\right)
    \leq\lambda^{-2}\sum_{j=1}^n\operatorname{Var}(X_j).$$
* **21. Convergence of centered square-summable series.** If the $X_n$ are
  independent, centered, and $\sum_n\mathbb E X_n^2<\infty$, then
  $\sum_nX_n$ converges almost surely and in $L^2$.
* **22. Kolmogorov three-series theorem.** For independent real $X_n$ and any
  fixed $A>0$, put $Y_n=X_n1_{\{|X_n|\leq A\}}$. The series $\sum X_n$
  converges almost surely exactly when
  $$\sum_n\mathbb P(|X_n|>A)<\infty,\qquad
    \sum_n\mathbb E Y_n\text{ converges},\qquad
    \sum_n\operatorname{Var}(Y_n)<\infty.$$
* **23. Weak law of large numbers.** For independent identically distributed
  integrable real variables with mean $m$, $S_n/n\to m$ in probability.
  For independent variables with finite variances, the sufficient condition
  $n^{-2}\sum_{j\leq n}\operatorname{Var}(X_j)\to0$ gives
  $(S_n-\mathbb ES_n)/n\to0$ in probability.
* **24. Strong law of large numbers.** For independent identically distributed
  $X_n$ with $\mathbb E|X_1|<\infty$, $S_n/n\to\mathbb E X_1$ almost surely.
  For independent centered square-integrable $X_n$, the condition
  $\sum_n\operatorname{Var}(X_n)/n^2<\infty$ also gives $S_n/n\to0$ almost surely.
* **25. Kronecker's lemma.** If $a_n>0$ increases to infinity and
  $\sum_n x_n/a_n$ converges, then $a_n^{-1}\sum_{j\leq n}x_j\to0$.
  Together with random-series convergence this is a standard route to strong laws.
* **26. Hartman–Wintner iterated-logarithm law.** For independent identically
  distributed centered $X_n$ with variance $0<\sigma^2<\infty$,
  $$\limsup_n\frac{S_n}{\sqrt{2\sigma^2n\log\log n}}=1,
    \qquad\liminf_n\frac{S_n}{\sqrt{2\sigma^2n\log\log n}}=-1
    \quad\text{almost surely}.$$
* **27. Elementary renewal theorem.** For independent identically distributed
  strictly positive interarrival times with mean $m\in(0,\infty)$, let
  $N(t)=\max\{n:S_n\leq t\}$. Then $N(t)/t\to1/m$ almost surely and
  $\mathbb EN(t)/t\to1/m$.

## Characteristic functions and classical distributional limits

The **characteristic function** of a real random variable is
$\varphi_X(t)=\mathbb E e^{itX}$. For a vector use $e^{i\langle t,X\rangle}$.
The law $N(m,\Sigma)$ has characteristic function
$\exp(i\langle t,m\rangle-\frac12t^{\mathsf T}\Sigma t)$.

* **28. Fourier uniqueness and inversion.** A probability law is determined
  by its characteristic function. If $\varphi\in L^1(\mathbb R^d)$, the law
  has continuous density
  $$p(x)=(2\pi)^{-d}\int e^{-i\langle t,x\rangle}\varphi(t)\,dt.$$
  For independent variables, characteristic functions multiply under summation.
* **29. Lévy continuity theorem.** Weak convergence implies pointwise
  convergence of characteristic functions. Conversely, a pointwise limit that
  is continuous at zero is a characteristic function and gives weak convergence
  to its law.
* **30. Cramér–Wold device.** Random vectors $X_n$ converge in distribution to
  $X$ exactly when $\langle t,X_n\rangle\Rightarrow\langle t,X\rangle$ for
  every fixed $t$.
* **31. Independent identically distributed central limit theorem.** If
  $\mathbb EX_1=m$ and $\operatorname{Var}(X_1)=\sigma^2\in(0,\infty)$, then
  $(S_n-nm)/(\sigma\sqrt n)\Rightarrow N(0,1)$. For vectors, finite covariance
  gives $n^{-1/2}\sum_{j\leq n}(X_j-\mathbb EX_j)\Rightarrow N(0,\Sigma)$,
  with singular $\Sigma$ allowed.
* **32. Lindeberg–Feller theorem.** Let each row of a triangular array
  $X_{n,k}$ be independent and centered, and let
  $s_n^2=\sum_k\mathbb E X_{n,k}^2>0$. If for every $\varepsilon>0$,
  $$s_n^{-2}\sum_k\mathbb E\!
    \left[X_{n,k}^2 1_{\{|X_{n,k}|>\varepsilon s_n\}}\right]\longrightarrow0,$$
  then $s_n^{-1}\sum_kX_{n,k}\Rightarrow N(0,1)$. Under
  $\max_k\operatorname{Var}(X_{n,k})/s_n^2\to0$, this condition is also necessary.
* **33. Lyapunov criterion.** In result 32, the sufficient condition
  $s_n^{-2-\delta}\sum_k\mathbb E|X_{n,k}|^{2+\delta}\to0$ for some
  $\delta>0$ implies the Lindeberg condition.
* **34. Berry–Esseen bound.** For independent identically distributed centered
  variables with variance $\sigma^2>0$ and third absolute moment $\rho<\infty$,
  $$\sup_x\left|\mathbb P\{S_n/(\sigma\sqrt n)\leq x\}-\Phi(x)\right|
    \leq C\rho/(\sigma^3\sqrt n),$$
  where $C$ is universal and $\Phi$ is the standard normal distribution function.
* **35. Delta method.** If $\sqrt n(T_n-\theta)\Rightarrow Z$ and $g$ is
  differentiable at $\theta$, then
  $\sqrt n(g(T_n)-g(\theta))\Rightarrow Dg(\theta)Z$.
* **36. Poisson limit.** For independent Bernoulli variables in each row, with
  success probabilities $p_{n,k}$, the conditions
  $\max_kp_{n,k}\to0$ and $\sum_kp_{n,k}\to\lambda<\infty$ imply convergence
  of their sum to $\operatorname{Poisson}(\lambda)$.

## Discrete-time martingales

A **filtration** $(\mathcal F_n)$ is an increasing sequence of $\sigma$-fields.
An adapted integrable sequence $M_n$ is a **martingale** if
$\mathbb E[M_{n+1}\mid\mathcal F_n]=M_n$; replacing equality by $\geq$ defines a
submartingale. A **stopping time** $T$ satisfies $\{T\leq n\}\in\mathcal F_n$.

* **37. Doob decomposition.** Every integrable submartingale has a unique
  decomposition $X_n=M_n+A_n$ with $A_0=0$, $A_n$ predictable and increasing,
  and $M_n$ a martingale.
* **38. Upcrossing inequality.** For an integrable submartingale and $a<b$,
  the number $U_N[a,b]$ of completed upcrossings by time $N$ satisfies
  $$(b-a)\mathbb E U_N[a,b]
    \leq\mathbb E(X_N-a)^++\mathbb E(X_0-a)^-.$$
  This form, though not always the sharpest, yields the convergence theorem.
* **39. Martingale convergence.** A submartingale with
  $\sup_n\mathbb E X_n^+<\infty$ converges almost surely to a finite integrable
  limit. In particular, nonnegative supermartingales converge almost surely.
* **40. Doob maximal inequalities.** For a nonnegative submartingale,
  $\lambda\mathbb P(\max_{k\leq n}X_k\geq\lambda)
  \leq\mathbb E[X_n1_{\{\max_{k\leq n}X_k\geq\lambda\}}]$.
  For a martingale and $p>1$,
  $$\left\|\max_{k\leq n}|M_k|\right\|_p
    \leq\frac{p}{p-1}\|M_n\|_p.$$
* **41. Uniform integrability and closing a martingale.** A martingale is
  uniformly integrable exactly when it converges almost surely and in $L^1$
  to an integrable $M_\infty$ and
  $M_n=\mathbb E[M_\infty\mid\mathcal F_n]$. An $L^p$-bounded martingale,
  $p>1$, converges also in $L^p$.
* **42. Lévy upward theorem.** If $\mathcal F_n\uparrow\mathcal F_\infty$
  in the sense that the latter is generated by their union, then
  $\mathbb E[X\mid\mathcal F_n]\to\mathbb E[X\mid\mathcal F_\infty]$
  almost surely and in $L^1$ for $X\in L^1$.
* **43. Reverse martingale theorem.** If $\mathcal G_n$ decreases and
  $\mathcal G_\infty=\bigcap_n\mathcal G_n$, then
  $\mathbb E[X\mid\mathcal G_n]\to\mathbb E[X\mid\mathcal G_\infty]$
  almost surely and in $L^1$.
* **44. Optional sampling.** If $S\leq T$ are bounded stopping times for a
  martingale, $\mathbb E[M_T\mid\mathcal F_S]=M_S$. The same holds for almost
  surely finite $S,T$ when the martingale is uniformly integrable. Suitable
  one-sided inequalities hold for submartingales and supermartingales.

## Gaussian laws, infinite divisibility, and random measures

A family is **Gaussian** if all finite real linear combinations are normally
distributed. A law is **infinitely divisible** if for every positive integer
$n$ it is the $n$-fold convolution of some law. A **Poisson random measure**
$N$ of intensity $\mu$ has independent counts on disjoint sets, with
$N(A)\sim\operatorname{Poisson}(\mu(A))$ when $\mu(A)<\infty$.

* **45. Gaussian independence.** For a jointly Gaussian vector, subvectors are
  independent exactly when all their cross-covariances vanish. The mean and
  covariance determine the law, including degenerate Gaussian laws.
* **46. Gaussian conditioning.** For jointly Gaussian $(X,Y)$ with invertible
  covariance $\Sigma_{YY}$, the conditional law of $X$ given $Y$ is Gaussian
  with mean
  $m_X+\Sigma_{XY}\Sigma_{YY}^{-1}(Y-m_Y)$ and covariance
  $\Sigma_{XX}-\Sigma_{XY}\Sigma_{YY}^{-1}\Sigma_{YX}$.
* **47. Lévy–Khintchine formula.** A real law is infinitely divisible exactly
  when its characteristic function is
  $$\exp\left(ibt-\tfrac12at^2+
    \int_{\mathbb R\setminus\{0\}}
    (e^{itx}-1-itx1_{\{|x|\leq1\}})\,\nu(dx)\right),$$
  where $a\geq0$, $b\in\mathbb R$, and
  $\int(1\wedge x^2)\,\nu(dx)<\infty$. This triplet is unique for the specified
  truncation convention.
* **48. Symmetric stable laws.** For $0<\alpha\leq2$ and $c>0$,
  $e^{-c|t|^\alpha}$ is a characteristic function. Independent variables with
  this law satisfy $X_1+\cdots+X_n\overset d=n^{1/\alpha}X_1$; $\alpha=2$
  gives the centered Gaussian case.
* **49. Poisson Laplace functional.** For a Poisson random measure of
  $\sigma$-finite intensity $\mu$ and measurable $f\geq0$,
  $$\mathbb E\exp\left(-\int f\,dN\right)
    =\exp\left(-\int(1-e^{-f})\,d\mu\right).$$
  This identity characterizes its law.
* **50. Campbell and compensated isometry formulas.** For $f\geq0$,
  $\mathbb E\int f\,dN=\int f\,d\mu$. The compensated integral, initially
  defined on finite-intensity simple functions, extends to $f\in L^2(\mu)$
  with mean zero and variance $\int|f|^2\,d\mu$.
* **51. De Finetti's theorem for Bernoulli sequences.** An infinite
  exchangeable $\{0,1\}$-valued sequence is a mixture of independent identically
  distributed Bernoulli sequences: for a unique probability $\pi$ on $[0,1]$,
  $$\mathbb P(X_1=x_1,\ldots,X_n=x_n)
    =\int_0^1p^{\sum x_i}(1-p)^{n-\sum x_i}\,d\pi(p).$$

## Functional limits and empirical distributions

For independent identically distributed real observations with distribution
function $F$, the **empirical distribution function** is
$F_n(x)=n^{-1}\sum_{j\leq n}1_{\{X_j\leq x\}}$. A **Brownian bridge** $B^0$
is the centered continuous Gaussian process on $[0,1]$ with covariance
$\min(s,t)-st$.

* **52. Kolmogorov continuity criterion.** If a process indexed by $[0,T]$
  satisfies $\mathbb E|X_t-X_s|^\alpha\leq C|t-s|^{1+\beta}$ with
  $\alpha,\beta>0$, it has a modification locally Hölder continuous of every
  order $\gamma<\beta/\alpha$.
* **53. Donsker invariance principle.** For independent identically distributed
  centered variables with unit variance, the linearly interpolated partial-sum
  process $n^{-1/2}S_{\lfloor nt\rfloor}$ converges in law in $C[0,1]$ to
  standard Brownian motion. The displayed expression specifies the grid values;
  interpolation defines the continuous process between them.
* **54. Glivenko–Cantelli theorem.** For every distribution function $F$,
  $\sup_x|F_n(x)-F(x)|\to0$ almost surely.
* **55. Empirical-process central limit theorem.** For independent uniform
  observations on $[0,1]$, $\sqrt n(F_n(t)-t)$ converges to $B^0(t)$ in
  $D[0,1]$ with its Skorokhod topology. For a general distribution function,
  the limit indexed by $x$ is $B^0(F(x))$, interpreted in the usual measurable
  empirical-process framework with the supremum norm.

## Large deviations and a basic branching model

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

* **56. Cramér's theorem.** For independent identically distributed real
  variables whose log moment generating function
  $\Lambda(t)=\log\mathbb E e^{tX_1}$ is finite near zero, $S_n/n$ satisfies a
  large deviation principle with good rate
  $I(x)=\sup_t\{tx-\Lambda(t)\}$.
* **57. Sanov's theorem.** For independent observations of law $\mu$ on a
  Polish space, the empirical measures satisfy a large deviation principle in
  the weak topology, with good rate
  $$H(\nu\mid\mu)=\int\log\frac{d\nu}{d\mu}\,d\nu$$
  when $\nu\ll\mu$, and $+\infty$ otherwise.
* **58. Varadhan's integral lemma.** If $X_n$ satisfies a large deviation
  principle with good rate $I$, then for bounded continuous $f$,
  $$\lim_n n^{-1}\log\mathbb E e^{nf(X_n)}=\sup_x(f(x)-I(x)).$$
* **59. Galton–Watson extinction.** For a branching process starting from one
  ancestor, with independent identically distributed offspring and generating
  function $g(s)=\mathbb E s^\xi$, the extinction probability is the smallest
  solution of $g(s)=s$ in $[0,1]$. If $\mathbb P(\xi=1)<1$, extinction is
  certain when $\mathbb E\xi\leq1$, and has probability less than one when
  $\mathbb E\xi>1$.
* **60. Branching martingale.** If the offspring mean is $m\in(0,\infty)$,
  then $Z_n/m^n$ is a nonnegative martingale and converges almost surely.
  In the supercritical case $m>1$, the condition
  $\mathbb E[\xi\log^+\xi]<\infty$ gives convergence in $L^1$ and a limit
  positive exactly on survival, up to null sets (Kesten–Stigum).

## Approximation principles and extensions of the limit theorems

For probabilities on the real line, write
$d_{\mathrm{TV}}(\mu,\nu)=\sup_A|\mu(A)-\nu(A)|$; this equals one half of the
$L^1$ distance of densities when both have densities relative to a common
measure. Convergence in this distance implies weak convergence but is stronger
than it: discrete laws can converge weakly to a continuous law while remaining
at total variation distance one.

* **61. Converging-together principle.** For random elements in a Polish metric
  space, suppose $X_{n,k}\Rightarrow X^{(k)}$ as $n\to\infty$ for each $k$,
  $X^{(k)}\Rightarrow X$ as $k\to\infty$, and for every $\varepsilon>0$,
  $$\lim_{k\to\infty}\limsup_{n\to\infty}
    \mathbb P\{d(X_{n,k},X_n)>\varepsilon\}=0.$$
  Then $X_n\Rightarrow X$. This permits finite-dimensional, truncated, or
  smoothed approximations to be removed after establishing their limits.
* **62. Le Cam's Poisson approximation.** For independent Bernoulli variables
  $I_i$ of parameters $p_i$, $\lambda=\sum_i p_i$, and $S=\sum_iI_i$,
  $$d_{\mathrm{TV}}(\mathcal L(S),\operatorname{Poisson}(\lambda))
    \leq\sum_i p_i^2.$$
  Consequently rarity of individual events gives a quantitative strengthening
  of the Poisson limit theorem without requiring identical probabilities.
* **63. Gaussian integration by parts and Stein characterization.** If
  $G\sim N(0,\Sigma)$ and $f$ is smooth with bounded first derivatives, then
  $\mathbb E[G_i f(G)]=\sum_j\Sigma_{ij}\mathbb E[\partial_jf(G)]$.
  A real law is $N(0,1)$ exactly when
  $\mathbb E[f'(X)-Xf(X)]=0$ for every $f\in C_c^\infty(\mathbb R)$.
  The latter identity characterizes the target law without referring to its
  density or characteristic function and is the starting point of Stein's method.
* **64. General de Finetti representation.** An infinite exchangeable sequence
  in a standard Borel space has a random probability measure $M$ such that,
  conditionally on $M$, its entries are independent with common law $M$.
  The distribution of $M$ is uniquely determined by the sequence law.
  For each bounded measurable $f$,
  $n^{-1}\sum_{j\leq n}f(X_j)\to\int f\,dM$ almost surely; the exceptional
  null set may depend on $f$.
* **65. Contraction principle.** If $X_n$ satisfies a large deviation principle
  with good rate $I$ and $g$ is continuous, then $g(X_n)$ satisfies a large
  deviation principle with good rate
  $$J(y)=\inf\{I(x):g(x)=y\},\qquad\inf\varnothing=\infty.$$
  Together with exponential approximation, this transfers large deviations
  from elementary random objects to nonlinear observables.
* **66. Gärtner–Ellis theorem.** For $\mathbb R^d$-valued $X_n$, suppose
  $\Lambda(t)=\lim_n n^{-1}\log\mathbb E e^{n\langle t,X_n\rangle}$ exists
  as an extended real function, is finite near zero and lower semicontinuous,
  and is differentiable on the interior of its effective domain. Assume also
  steepness: $|\nabla\Lambda(t_k)|\to\infty$ for interior sequences tending
  to a finite boundary point of that domain. Then $X_n$ satisfies a large
  deviation principle with good rate
  $\Lambda^*(x)=\sup_t(\langle t,x\rangle-\Lambda(t))$.

## Reference guide

Durrett, *Probability: Theory and Examples*, Chapters 1–4, supplies the main
sequence from independence through central limits and martingales; its later
chapters treat branching, invariance principles, and Brownian motion. Klenke,
*Probability Theory*, independently develops this core and includes systematic
treatments of weak convergence, infinite divisibility, exchangeability, the
iterated logarithm, large deviations, and Poisson processes. Kallenberg,
*Foundations of Modern Probability*, supplies the general state-space framework
for kernels, coupling, random measures, and exchangeability.

The same classical core is shared by Billingsley, Williams, Chung, Shiryaev,
Breiman, and the recent courses of Gut and Le Gall. Feller and Petrov develop
the finer limit and renewal theory. For the large-deviation endpoint, the
overlapping references are Dembo–Zeitouni, Deuschel–Stroock, den Hollander,
Rassoul-Agha–Seppäläinen, and Varadhan. Infinite divisibility is developed much
further by Sato, Bertoin, and Applebaum; point-process structure by Kallenberg,
Daley–Vere-Jones, and Last–Penrose.

The final approximation principles recur in Billingsley and Kallenberg for
weak convergence and coupling, in the limit-theorem chapters of Durrett and
Klenke for Poisson approximation, and in the large-deviation monographs for
contraction and Gärtner–Ellis. Gaussian integration by parts connects the
Gaussian-measure references with Chen–Goldstein–Shao's treatment of Stein's
method. General exchangeability is developed in Kallenberg and Klenke.

Local texts directly consulted for this selection:

- [Durrett, *Probability: Theory and Examples*](References/Durrett2019ProbabilityTheoryExamples5thEd-CambridgeSerStatProbMath49.pdf).
- [Klenke, *Probability Theory*](References/Klenke2020ProbabilityTheoryComprehensiveCourse3rdEd-SpringerUTX.pdf).
- [Kallenberg, *Foundations of Modern Probability*](References/Kallenberg2021FoundationsModernProbability3dEd-Springer.PTSM99.pdf).
