# Synopsis: Probability: measure-theoretic foundations and limit theory

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-06);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis follows the current subdivisions of Section 06: probability
foundations and limit theory ([06A](CKMA-bib.md#ckma-06a)), large deviations
([06B](CKMA-bib.md#ckma-06b)), random measures, fields, and stochastic
geometry ([06C](CKMA-bib.md#ckma-06c)), and discrete probability and
statistical mechanics ([06D](CKMA-bib.md#ckma-06d)). The numbered selection
remains concentrated on the common probability core. The final two
subdivisions are represented by Poisson random measures and the Kac–Rice
formula, and by branching, random walk, percolation, and Gibbs measures.

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
finite-dimensional law under permutations.

Lettered headings match the bibliography. Numbered results retain their
existing identifiers, including after moves between topical groups, so the
labels remain usable from the gap inventory; they need not run in increasing
order within the file.

<a id="synopsis-06a"></a>

## 06A. Probability Foundations and Limit Theory

Foundations and limit theory follow bibliography subdivision 06A. Martingales,
Gaussian laws, infinite divisibility, and exchangeability remain here as part
of the general probability toolkit; continuous-time process theory is
developed in Section 08.

### Independence, construction, and zero–one laws

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
  $\mathbb P(A_n\text{ infinitely often})=1$. Pairwise independence suffices,
  and then $\sum_{k\leq n}1_{A_k}/\sum_{k\leq n}\mathbb P(A_k)\to1$ almost
  surely.

* **5. Kolmogorov zero–one law.** The tail $\sigma$-field of independent random
  variables is trivial: every tail event has probability zero or one.

* **6. Hewitt–Savage zero–one law.** For an independent identically distributed
  sequence, any event in its generated $\sigma$-field invariant under all finite
  permutations has probability zero or one.

### Conditional expectation and conditional distributions

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

* **9. Conditional Jensen and contraction.** For integrable $X$ and convex
  $\Phi$ with $\Phi(X)$ integrable,
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

### Convergence of random variables and probability laws

**Convergence in probability** is convergence in measure for $\mathbb P$.
**Uniform integrability** of $\{X_n\}$ means
$\sup_n\mathbb E[|X_n|1_{\{|X_n|>R\}}]\to0$ as $R\to\infty$.
Weak convergence of laws is tested against bounded continuous functions.
For probabilities on a measurable space, write
$d_{\mathrm{TV}}(\mu,\nu)=\sup_A|\mu(A)-\nu(A)|$; this equals one half of the
$L^1$ distance of densities when both have densities relative to a common
measure. Convergence in this distance implies weak convergence but is stronger
than it: discrete laws can converge weakly to a continuous law while remaining
at total variation distance one.

* **12. Relations among convergences.** Almost-sure convergence and $L^p$
  convergence, $p>0$, each imply convergence in probability, which implies
  convergence in distribution. Convergence in probability is equivalent to
  every subsequence having a further almost-surely convergent subsequence.
  Convergence in distribution to a constant implies convergence in probability.

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

* **20. Converging-together principle.** For random elements in a Polish metric
  space, suppose $X_{n,k}\Rightarrow X^{(k)}$ as $n\to\infty$ for each $k$,
  $X^{(k)}\Rightarrow X$ as $k\to\infty$, and for every $\varepsilon>0$,
  $$\lim_{k\to\infty}\limsup_{n\to\infty}
    \mathbb P\{d(X_{n,k},X_n)>\varepsilon\}=0.$$
  Then $X_n\Rightarrow X$. This removes truncations and finite-dimensional
  approximations after their limits are established.

### Independent sums, random series, and laws of large numbers

* **21. Kolmogorov maximal inequality.** For independent centered variables
  with finite variances,
  $$\mathbb P\!\left(\max_{k\leq n}|S_k|\geq\lambda\right)
    \leq\lambda^{-2}\sum_{j=1}^n\mathop{\mathrm{Var}}(X_j).$$

* **22. Convergence of centered square-summable series.** If the $X_n$ are
  independent, centered, and $\sum_n\mathbb E X_n^2<\infty$, then
  $\sum_nX_n$ converges almost surely and in $L^2$. For any independent
  summands, almost-sure convergence, convergence in probability, and
  convergence in distribution of $\sum_nX_n$ are equivalent (Lévy).

* **23. Kolmogorov three-series theorem.** For independent real $X_n$ and any
  fixed $A>0$, put $Y_n=X_n1_{\{|X_n|\leq A\}}$. The series $\sum X_n$
  converges almost surely exactly when
  $$\sum_n\mathbb P(|X_n|>A)<\infty,\qquad
    \sum_n\mathbb E Y_n\text{ converges},\qquad
    \sum_n\mathop{\mathrm{Var}}(Y_n)<\infty.$$

* **24. Weak law of large numbers.** For independent identically distributed
  integrable real variables with mean $m$, $S_n/n\to m$ in probability.
  For independent variables with finite variances, the sufficient condition
  $n^{-2}\sum_{j\leq n}\mathop{\mathrm{Var}}(X_j)\to0$ gives
  $(S_n-\mathbb ES_n)/n\to0$ in probability.

* **25. Strong law of large numbers.** For independent identically distributed
  $X_n$ with $\mathbb E|X_1|<\infty$, $S_n/n\to\mathbb E X_1$ almost surely.
  Pairwise independence suffices (Etemadi). Conversely, if
  $\mathbb E|X_1|=\infty$, then $\limsup_n|S_n|/n=\infty$ almost surely.
  For independent centered square-integrable $X_n$, the condition
  $\sum_n\mathop{\mathrm{Var}}(X_n)/n^2<\infty$ also gives $S_n/n\to0$ almost surely.

* **26. Kronecker's lemma.** If $a_n>0$ increases to infinity and
  $\sum_n x_n/a_n$ converges, then $a_n^{-1}\sum_{j\leq n}x_j\to0$.
  Together with random-series convergence this is a standard route to strong laws.

* **27. Hartman–Wintner iterated-logarithm law.** For independent identically
  distributed centered $X_n$ with variance $0<\sigma^2<\infty$,
  $$\limsup_n\frac{S_n}{\sqrt{2\sigma^2n\log\log n}}=1,
    \qquad\liminf_n\frac{S_n}{\sqrt{2\sigma^2n\log\log n}}=-1
    \quad\text{almost surely}.$$

* **28. Elementary renewal theorem.** For independent identically distributed
  strictly positive interarrival times with mean $m\in(0,\infty)$, let
  $N(t)=\max\{n:S_n\leq t\}$. Then $N(t)/t\to1/m$ almost surely and
  $\mathbb EN(t)/t\to1/m$.

### Characteristic functions and classical distributional limits

The **characteristic function** of a real random variable is
$\varphi_X(t)=\mathbb E e^{itX}$. For a vector use $e^{i\langle t,X\rangle}$.
The law $N(m,\Sigma)$ has characteristic function
$\exp(i\langle t,m\rangle-\frac12t^{\mathsf T}\Sigma t)$.

* **29. Fourier uniqueness and inversion.** A probability law is determined
  by its characteristic function. If $\varphi\in L^1(\mathbb R^d)$, the law
  has continuous density
  $$p(x)=(2\pi)^{-d}\int e^{-i\langle t,x\rangle}\varphi(t)\,dt.$$
  For independent variables, characteristic functions multiply under summation.

* **30. Lévy continuity theorem.** Weak convergence implies pointwise
  convergence of characteristic functions. Conversely, a pointwise limit that
  is continuous at zero is a characteristic function and gives weak convergence
  to its law.

* **31. Cramér–Wold device.** Random vectors $X_n$ converge in distribution to
  $X$ exactly when $\langle t,X_n\rangle\Rightarrow\langle t,X\rangle$ for
  every fixed $t$.

* **32. Method of moments.** If a law $\mu$ on $\mathbb R$ is determined by its
  moments (for instance if $\int e^{\varepsilon|x|}\,d\mu<\infty$ for some
  $\varepsilon>0$, or under Carleman's condition) and
  $\int x^k\,d\mu_n\to\int x^k\,d\mu$ for every $k$, then
  $\mu_n\Rightarrow\mu$. Conversely, weak convergence together with uniform
  integrability of $|x|^k$ gives convergence of the $k$-th moments.

* **33. Independent identically distributed central limit theorem.** If
  $\mathbb EX_1=m$ and $\mathop{\mathrm{Var}}(X_1)=\sigma^2\in(0,\infty)$, then
  $(S_n-nm)/(\sigma\sqrt n)\Rightarrow N(0,1)$. For vectors, finite covariance
  gives $n^{-1/2}\sum_{j\leq n}(X_j-\mathbb EX_j)\Rightarrow N(0,\Sigma)$,
  with singular $\Sigma$ allowed.

* **34. Lindeberg–Feller theorem.** Let each row of a triangular array
  $X_{n,k}$ be independent and centered, and let
  $s_n^2=\sum_k\mathbb E X_{n,k}^2>0$. If for every $\varepsilon>0$,
  $$s_n^{-2}\sum_k\mathbb E\!
    \left[X_{n,k}^2 1_{\{|X_{n,k}|>\varepsilon s_n\}}\right]\longrightarrow0,$$
  then $s_n^{-1}\sum_kX_{n,k}\Rightarrow N(0,1)$. Under
  $\max_k\mathop{\mathrm{Var}}(X_{n,k})/s_n^2\to0$, this condition is also necessary.

* **35. Lyapunov criterion.** In result 34, the sufficient condition
  $s_n^{-2-\delta}\sum_k\mathbb E|X_{n,k}|^{2+\delta}\to0$ for some
  $\delta>0$ implies the Lindeberg condition.

* **36. Berry–Esseen bound.** For independent identically distributed centered
  variables with variance $\sigma^2>0$ and third absolute moment $\rho<\infty$,
  $$\sup_x\left|\mathbb P\{S_n/(\sigma\sqrt n)\leq x\}-\Phi(x)\right|
    \leq C\rho/(\sigma^3\sqrt n),$$
  where $C$ is universal and $\Phi$ is the standard normal distribution function.

* **37. Delta method.** If $\sqrt n(T_n-\theta)\Rightarrow Z$ and $g$ is
  differentiable at $\theta$, then
  $\sqrt n(g(T_n)-g(\theta))\Rightarrow Dg(\theta)Z$.

* **38. Poisson limit.** For independent Bernoulli variables in each row, with
  success probabilities $p_{n,k}$, the conditions
  $\max_kp_{n,k}\to0$ and $\sum_kp_{n,k}\to\lambda<\infty$ imply convergence
  of their sum to $\mathop{\mathrm{Poisson}}(\lambda)$.

* **39. Le Cam's Poisson approximation.** For independent Bernoulli variables
  $I_i$ of parameters $p_i$, $\lambda=\sum_i p_i$, and $S=\sum_iI_i$,
  $$d_{\mathrm{TV}}(\mathcal L(S),\mathop{\mathrm{Poisson}}(\lambda))
    \leq\sum_i p_i^2.$$
  This quantifies the Poisson limit theorem.

### Discrete-time martingales

A **filtration** $(\mathcal F_n)$ is an increasing sequence of $\sigma$-fields.
An adapted integrable sequence $M_n$ is a **martingale** if
$\mathbb E[M_{n+1}\mid\mathcal F_n]=M_n$; replacing equality by $\geq$ defines a
submartingale. A **stopping time** $T$ satisfies $\{T\leq n\}\in\mathcal F_n$.

* **40. Doob decomposition.** Every integrable submartingale has a unique
  decomposition $X_n=M_n+A_n$ with $A_0=0$, $A_n$ predictable and increasing,
  and $M_n$ a martingale.

* **41. Upcrossing inequality.** For an integrable submartingale and $a<b$,
  the number $U_N[a,b]$ of completed upcrossings by time $N$ satisfies
  $$(b-a)\mathbb E U_N[a,b]
    \leq\mathbb E(X_N-a)^+-\mathbb E(X_0-a)^+.$$

* **42. Martingale convergence.** A submartingale with
  $\sup_n\mathbb E X_n^+<\infty$ converges almost surely to a finite integrable
  limit. In particular, nonnegative supermartingales converge almost surely.

* **43. Doob maximal inequalities.** For a nonnegative submartingale,
  $\lambda\mathbb P(\max_{k\leq n}X_k\geq\lambda)
  \leq\mathbb E[X_n1_{\{\max_{k\leq n}X_k\geq\lambda\}}]$.
  For a martingale and $p>1$,
  $$\left\|\max_{k\leq n}|M_k|\right\|_p
    \leq\frac{p}{p-1}\|M_n\|_p.$$

* **44. Uniform integrability and closing a martingale.** A martingale is
  uniformly integrable exactly when it converges almost surely and in $L^1$
  to an integrable $M_\infty$ and
  $M_n=\mathbb E[M_\infty\mid\mathcal F_n]$. An $L^p$-bounded martingale,
  $p>1$, converges also in $L^p$.

* **45. Lévy upward theorem.** If $\mathcal F_n\uparrow\mathcal F_\infty$
  in the sense that the latter is generated by their union, then
  $\mathbb E[X\mid\mathcal F_n]\to\mathbb E[X\mid\mathcal F_\infty]$
  almost surely and in $L^1$ for $X\in L^1$.

* **46. Reverse martingale theorem.** If $\mathcal G_n$ decreases and
  $\mathcal G_\infty=\bigcap_n\mathcal G_n$, then
  $\mathbb E[X\mid\mathcal G_n]\to\mathbb E[X\mid\mathcal G_\infty]$
  almost surely and in $L^1$.

* **47. Optional sampling.** If $S\leq T$ are bounded stopping times for a
  martingale, $\mathbb E[M_T\mid\mathcal F_S]=M_S$. The same holds for almost
  surely finite $S,T$ when the martingale is uniformly integrable. Suitable
  one-sided inequalities hold for submartingales and supermartingales. For
  independent identically distributed integrable $X_j$ and a stopping time $T$
  of their filtration with $\mathbb ET<\infty$, Wald's identity
  $\mathbb ES_T=\mathbb ET\,\mathbb EX_1$ holds.

### Gaussian laws, infinite divisibility, and exchangeability

A family is **Gaussian** if all finite real linear combinations are normally
distributed. A law is **infinitely divisible** if for every positive integer
$n$ it is the $n$-fold convolution of some law.

* **48. Gaussian independence.** For a jointly Gaussian vector, subvectors are
  independent exactly when all their cross-covariances vanish. The mean and
  covariance determine the law, including degenerate Gaussian laws.

* **49. Gaussian conditioning.** For jointly Gaussian $(X,Y)$ with invertible
  covariance $\Sigma_{YY}$, the conditional law of $X$ given $Y$ is Gaussian
  with mean
  $m_X+\Sigma_{XY}\Sigma_{YY}^{-1}(Y-m_Y)$ and covariance
  $\Sigma_{XX}-\Sigma_{XY}\Sigma_{YY}^{-1}\Sigma_{YX}$.

* **50. Gaussian integration by parts and Stein characterization.** If
  $G\sim N(0,\Sigma)$ and $f$ is smooth with bounded first derivatives, then
  $\mathbb E[G_i f(G)]=\sum_j\Sigma_{ij}\mathbb E[\partial_jf(G)]$.
  A real law is $N(0,1)$ exactly when
  $\mathbb E[f'(X)-Xf(X)]=0$ for every $f\in C_c^\infty(\mathbb R)$.
  This characterization is the starting point of Stein's method.

* **51. Lévy–Khintchine formula.** A real law is infinitely divisible exactly
  when its characteristic function is
  $$\exp\left(ibt-\tfrac12at^2+
    \int_{\mathbb R\setminus\{0\}}
    (e^{itx}-1-itx1_{\{|x|\leq1\}})\,\nu(dx)\right),$$
  where $a\geq0$, $b\in\mathbb R$, and
  $\int(1\wedge x^2)\,\nu(dx)<\infty$. This triplet is unique for the specified
  truncation convention.

* **52. Symmetric stable laws.** For $0<\alpha\leq2$ and $c>0$,
  $e^{-c|t|^\alpha}$ is a characteristic function. Independent variables with
  this law satisfy $X_1+\cdots+X_n\overset d=n^{1/\alpha}X_1$; $\alpha=2$
  gives the centered Gaussian case.

* **55. De Finetti's theorem.** An infinite exchangeable sequence in a standard
  Borel space has a random probability measure $M$ such that, conditionally on
  $M$, its entries are independent with common law $M$; the distribution of $M$
  is uniquely determined by the sequence law. For $\{0,1\}$-valued sequences
  this says that, for a unique probability $\pi$ on $[0,1]$,
  $$\mathbb P(X_1=x_1,\ldots,X_n=x_n)
    =\int_0^1p^{\sum x_i}(1-p)^{n-\sum x_i}\,d\pi(p).$$
  For each bounded measurable $f$,
  $n^{-1}\sum_{j\leq n}f(X_j)\to\int f\,dM$ almost surely; the exceptional
  null set may depend on $f$.

### Functional limits and empirical distributions

For independent identically distributed real observations with distribution
function $F$, the **empirical distribution function** is
$F_n(x)=n^{-1}\sum_{j\leq n}1_{\{X_j\leq x\}}$. A **Brownian bridge** $B^0$
is the centered continuous Gaussian process on $[0,1]$ with covariance
$\min(s,t)-st$.

* **57. Donsker invariance principle.** For independent identically distributed
  centered variables with unit variance, the linearly interpolated partial-sum
  process
  $n^{-1/2}\bigl(S_{\lfloor nt\rfloor}+(nt-\lfloor nt\rfloor)X_{\lfloor nt\rfloor+1}\bigr)$
  converges in law in $C[0,1]$ to standard Brownian motion. The step process
  $n^{-1/2}S_{\lfloor nt\rfloor}$ converges in law in the Skorokhod space
  $D[0,1]$.

* **58. Glivenko–Cantelli theorem.** For every distribution function $F$,
  $\sup_x|F_n(x)-F(x)|\to0$ almost surely.

* **59. Empirical-process central limit theorem.** For independent uniform
  observations on $[0,1]$, $\sqrt n(F_n(t)-t)$ converges to $B^0(t)$ in
  $D[0,1]$ with its Skorokhod topology. For a general distribution function,
  the limit indexed by $x$ is $B^0(F(x))$, interpreted in the usual measurable
  empirical-process framework with the supremum norm.

<a id="synopsis-06b"></a>

## 06B. Large Deviations

The large-deviation principles and entropy methods of 06B are collected here.
They use the weak-convergence and probability foundations in 06A.

### Large-deviation principles

A sequence of laws satisfies a **large deviation principle** with speed $n$
and **rate function** $I$ if $I$ is lower semicontinuous and
$$-\inf_{A^\circ}I\leq\liminf_n n^{-1}\log\mathbb P(X_n\in A)
  \leq\limsup_n n^{-1}\log\mathbb P(X_n\in A)
  \leq-\inf_{\overline A}I.$$
The rate is **good** when its sublevel sets are compact.
The relative entropy $H(\nu\mid\mu)$ below is nonnegative and vanishes exactly
when $\nu=\mu$.

* **60. Cramér's theorem.** For independent identically distributed real
  variables whose log moment generating function
  $\Lambda(t)=\log\mathbb E e^{tX_1}$ is finite near zero, $S_n/n$ satisfies a
  large deviation principle with good rate
  $I(x)=\sup_t\{tx-\Lambda(t)\}$. On $\mathbb R$ the principle with this
  rate holds without any moment assumption, the rate then possibly not being
  good.

* **61. Sanov's theorem.** For independent observations of law $\mu$ on a
  Polish space, the empirical measures satisfy a large deviation principle in
  the weak topology, with good rate
  $$H(\nu\mid\mu)=\int\log\frac{d\nu}{d\mu}\,d\nu$$
  when $\nu\ll\mu$, and $+\infty$ otherwise.

* **62. Varadhan's integral lemma.** If $X_n$ satisfies a large deviation
  principle with good rate $I$, then for bounded continuous $f$,
  $$\lim_n n^{-1}\log\mathbb E e^{nf(X_n)}=\sup_x(f(x)-I(x)).$$

* **63. Contraction principle.** If $X_n$ satisfies a large deviation principle
  with good rate $I$ and $g$ is continuous, then $g(X_n)$ satisfies a large
  deviation principle with good rate
  $$J(y)=\inf\{I(x):g(x)=y\},\qquad\inf\varnothing=\infty.$$

* **64. Gärtner–Ellis theorem.** For $\mathbb R^d$-valued $X_n$, suppose
  $\Lambda(t)=\lim_n n^{-1}\log\mathbb E e^{n\langle t,X_n\rangle}$ exists
  as an extended real function, is finite near zero and lower semicontinuous,
  and is differentiable on the interior of its effective domain. Assume also
  steepness: $|\nabla\Lambda(t_k)|\to\infty$ for interior sequences tending
  to a finite boundary point of that domain. Then $X_n$ satisfies a large
  deviation principle with good rate
  $\Lambda^*(x)=\sup_t(\langle t,x\rangle-\Lambda(t))$.

* **67. Schilder's theorem.** For standard $d$-dimensional Brownian motion $W$
  on $[0,1]$, the laws of $\sqrt\varepsilon W$ satisfy, as
  $\varepsilon\downarrow0$ and with $\varepsilon\log$ in place of
  $n^{-1}\log$, a large deviation principle in $C_0([0,1];\mathbb R^d)$ with
  the uniform norm and good rate
  $I(h)=\frac12\int_0^1|h'(t)|^2\,dt$ when $h$ is absolutely continuous with
  $h(0)=0$ and $h'\in L^2$, and $I(h)=+\infty$ otherwise.

* **68. Freidlin–Wentzell theorem.** Let $b$ and $\sigma$ be Lipschitz and let
  $dX^\varepsilon=b(X^\varepsilon)\,dt+\sqrt\varepsilon\,\sigma(X^\varepsilon)\,dW$,
  $X^\varepsilon_0=x$. On $C([0,T];\mathbb R^d)$ the laws of $X^\varepsilon$
  satisfy a large deviation principle at speed $\varepsilon^{-1}$ with good rate
  $$I(f)=\inf\Bigl\{\tfrac12\int_0^T|h'|^2\,dt:\ f'=b(f)+\sigma(f)h',\
    f(0)=x\Bigr\},$$
  the infimum over absolutely continuous $h$ with $h(0)=0$, $h'\in L^2$.
  This is the contraction of Schilder's rate through the skeleton map; it
  governs exit times and exit places from domains of attraction through the
  quasipotential.

<a id="synopsis-06c"></a>

## 06C. Random Measures, Random Fields, and Stochastic Geometry

Poisson random measures and the level-crossing formula for Gaussian fields
provide the selected core of 06C in this synopsis. The broader random-set and
stochastic-geometric theories listed in the bibliography are not developed as
separate theorem inventories here. The Mecke equation characterizing Poisson
processes is stated with Poisson Malliavin calculus in SYNOPSIS09, item 67.

### Poisson random measures

A **Poisson random measure**
$N$ of intensity $\mu$ has independent counts on disjoint sets, with
$N(A)\sim\mathop{\mathrm{Poisson}}(\mu(A))$ when $\mu(A)<\infty$.

* **53. Poisson Laplace functional.** A Poisson random measure with given
  $\sigma$-finite intensity $\mu$ exists, and for measurable $f\geq0$,
  $$\mathbb E\exp\left(-\int f\,dN\right)
    =\exp\left(-\int(1-e^{-f})\,d\mu\right).$$
  This identity characterizes its law.

* **54. Campbell and compensated isometry formulas.** For $f\geq0$,
  $\mathbb E\int f\,dN=\int f\,d\mu$. The compensated integral, initially
  defined on finite-intensity simple functions, extends to $f\in L^2(\mu)$
  with mean zero and variance $\int|f|^2\,d\mu$.

* **69. Mapping, superposition, marking, and thinning.** Let $N$ be Poisson
  with $\sigma$-finite intensity $\mu$ on a standard Borel space. If $T$ is
  measurable and $T_\#\mu$ is $\sigma$-finite, then $T_\#N$ is Poisson with
  intensity $T_\#\mu$. A sum of independent Poisson random measures is Poisson,
  with the summed intensity when this is $\sigma$-finite. Marking the points
  independently according to a probability kernel $K(x,dm)$ gives a Poisson
  random measure with intensity $\mu\otimes K$ on the product space; in
  particular, retaining each point $x$ independently with probability $p(x)$
  splits $N$ into independent Poisson random measures with intensities $p\mu$
  and $(1-p)\mu$.

* **70. Multivariate Mecke equation and Slivnyak's theorem.** For a Poisson
  process $N$ with $\sigma$-finite intensity $\mu$, every $m\geq1$, and
  measurable $h\geq0$,
  $$\mathbb E\int h(x_1,\ldots,x_m,N)\,N^{(m)}(dx)
    =\int\mathbb E\,h\bigl(x_1,\ldots,x_m,N+\delta_{x_1}+\cdots+\delta_{x_m}\bigr)
    \,\mu^{m}(dx),$$
  where $N^{(m)}$ is the $m$-th factorial measure (sum over $m$-tuples of
  distinct points). Equivalently (Slivnyak), the Palm distribution of $N$ at
  $\mu$-almost every $x$ is the law of $N+\delta_x$.

* **71. Rényi's theorem.** If $\mu$ is a diffuse $\sigma$-finite measure and
  $N$ is a simple point process with $\mathbb P(N(B)=0)=e^{-\mu(B)}$ for all
  measurable $B$, then $N$ is Poisson with intensity $\mu$. Simple point
  processes are determined in law by their void probabilities.

### Gaussian random fields

* **72. Kac–Rice formula.** Let $X$ be a Gaussian process on $[a,b]$ with
  continuously differentiable sample paths and $\mathop{\mathrm{Var}}X(t)>0$ for
  every $t$. The number $N_u$ of $t\in[a,b]$ with $X(t)=u$ satisfies
  $$\mathbb EN_u=\int_a^b\mathbb E\bigl[|X'(t)|\bigm|X(t)=u\bigr]\,
    p_{X(t)}(u)\,dt,$$
  with $p_{X(t)}$ the density of $X(t)$. For a centered stationary process with
  $\lambda_0=\mathop{\mathrm{Var}}X(0)$ and $\lambda_2=\mathop{\mathrm{Var}}X'(0)$
  this is Rice's formula
  $\mathbb EN_u=\frac{b-a}{\pi}\sqrt{\lambda_2/\lambda_0}\,e^{-u^2/(2\lambda_0)}$.
  In several parameters, the analogous formula for critical points yields the
  expected Euler characteristic of excursion sets $\{X\geq u\}$ (Adler–Taylor).

<a id="synopsis-06d"></a>

## 06D. Discrete Probability and Probabilistic Statistical Mechanics

The selection represents 06D through branching, simple random walk,
correlation inequalities and percolation, and the basic theory of Gibbs
measures. Spin glasses and the finer critical theory of lattice models are
beyond this synopsis's numbered core.

### Branching processes

* **65. Galton–Watson extinction.** For a branching process starting from one
  ancestor, with independent identically distributed offspring and generating
  function $g(s)=\mathbb E s^\xi$, the extinction probability is the smallest
  solution of $g(s)=s$ in $[0,1]$. If $\mathbb P(\xi=1)<1$, extinction is
  certain when $\mathbb E\xi\leq1$, and has probability less than one when
  $\mathbb E\xi>1$.

* **66. Branching martingale.** If the offspring mean is $m\in(0,\infty)$,
  then $Z_n/m^n$ is a nonnegative martingale and converges almost surely.
  In the supercritical case $m>1$, if $\mathbb E[\xi\log^+\xi]<\infty$ the
  convergence holds in $L^1$ and the limit is positive almost surely on
  survival; otherwise the limit vanishes almost surely (Kesten–Stigum).

### Random walks, correlation inequalities, and percolation

In **bond percolation** on $\mathbb Z^d$ each nearest-neighbour edge is open
independently with probability $p$, giving the product law $\mathbb P_p$ on
$\{0,1\}^E$. With $C(0)$ the open cluster of the origin,
$\theta(p)=\mathbb P_p(|C(0)|=\infty)$ and
$p_c(d)=\sup\{p:\theta(p)=0\}$. An event or function on $\{0,1\}^E$ is
**increasing** if it is preserved when closed edges are opened.

* **73. Pólya's recurrence theorem.** Simple symmetric random walk on
  $\mathbb Z^d$ returns to its starting point with probability one for
  $d=1,2$, and with probability less than one for $d\geq3$; equivalently,
  $\sum_nP^n(0,0)$ diverges exactly when $d\leq2$.

* **74. Harris–FKG inequality.** Increasing events depending on finitely many
  edges are positively correlated under $\mathbb P_p$:
  $\mathbb P_p(A\cap B)\geq\mathbb P_p(A)\mathbb P_p(B)$ (Harris). More
  generally (Fortuin–Kasteleyn–Ginibre), a probability $\mu$ on a finite
  distributive lattice with $\mu(x\vee y)\mu(x\wedge y)\geq\mu(x)\mu(y)$
  makes every pair of increasing functions positively correlated.

* **75. Nontrivial phase transition.** For $d\geq2$, $\theta$ is
  nondecreasing and $0<p_c(d)<1$; more precisely
  $1/(2d-1)\leq p_c(d)\leq p_c(2)\leq2/3$, by counting self-avoiding paths
  and, in the plane, closed dual circuits (Peierls's argument). An infinite open
  cluster exists with probability $0$ when $\theta(p)=0$ and $1$ when
  $\theta(p)>0$.

* **76. Uniqueness and sharpness.** For $\theta(p)>0$ there is almost surely
  exactly one infinite open cluster (Aizenman–Kesten–Newman; Burton–Keane).
  For $p<p_c$ the connection probability
  $\mathbb P_p(0\leftrightarrow\partial[-n,n]^d)$ decays exponentially in
  $n$, and $\theta(p)\geq(p-p_c)/(p(1-p_c))$ for $p>p_c$
  (Menshikov; Aizenman–Barsky; Duminil-Copin–Tassion).

* **77. Harris–Kesten theorem.** For bond percolation on $\mathbb Z^2$,
  $p_c=1/2$ and $\theta(1/2)=0$. The proof combines self-duality of the square
  lattice with the Russo–Seymour–Welsh crossing estimates.

### Gibbs measures and phase transitions

For a finite spin space $S$ and a translation-invariant, absolutely summable
interaction $\Phi$ on $\mathbb Z^d$, a probability on $S^{\mathbb Z^d}$ is a
**Gibbs measure** (DLR condition) if, for every finite $\Lambda$, its
conditional law on $S^\Lambda$ given the configuration outside $\Lambda$ is
the Boltzmann weight $Z^{-1}e^{-\beta H_\Lambda}$ with that boundary
condition. The **Ising model** has $S=\{\pm1\}$ and
$H_\Lambda=-\sum_{\{i,j\}\cap\Lambda\neq\varnothing,\,|i-j|=1}\sigma_i\sigma_j
-h\sum_{i\in\Lambda}\sigma_i$.

* **78. Structure of the Gibbs simplex.** The set of Gibbs measures for a
  given interaction is nonempty, convex, and weak-* compact. It is a simplex
  whose extreme points are exactly the Gibbs measures trivial on the tail
  $\sigma$-algebra, and each extreme point is a limit of finite-volume Gibbs
  measures with suitable boundary conditions.

* **79. Dobrushin's uniqueness theorem.** Let $C_{ij}$ be the supremum of the
  total-variation distance between the single-site conditional laws at $i$
  under two boundary conditions differing only at $j$. If
  $\sup_i\sum_jC_{ij}<1$, there is exactly one Gibbs measure. In particular
  uniqueness holds at sufficiently high temperature (small $\beta$).

* **80. Phase transition in the Ising model.** For the Ising model with $h=0$,
  the Gibbs measure is unique for every $\beta$ when $d=1$. For $d\geq2$
  there is $\beta_c\in(0,\infty)$ such that the plus and minus boundary
  conditions give distinct Gibbs measures $\mu^+\neq\mu^-$, with spontaneous
  magnetization $\mu^+(\sigma_0)>0$, for $\beta>\beta_c$, and the Gibbs
  measure is unique for $\beta<\beta_c$; the large-$\beta$ case is Peierls's
  contour argument. For $d=2$, $\beta_c=\frac12\log(1+\sqrt2)$ (Onsager). For
  $h\neq0$ the Gibbs measure is unique for every $\beta$, a consequence of the
  Lee–Yang theorem.

## Reference guide

### Correspondence with the subdivisions

- **[06A](#synopsis-06a)**: Durrett, Klenke, Kallenberg, and the other broad
  probability courses supply the foundation, martingale, and limit-theorem
  material.
- **[06B](#synopsis-06b)**: The large-deviation monographs supply the entropy
  and exponential-asymptotic endpoint; Schilder's and the Freidlin–Wentzell
  theorems are in Dembo–Zeitouni, Chapter 5.
- **[06C](#synopsis-06c)**: Last–Penrose, Chapters 3–6, supply the Poisson
  mapping, marking, Mecke, and Rényi theorems; Daley–Vere-Jones and Kallenberg
  the general point-process framework; Adler–Taylor, Chapter 11, the Kac–Rice
  formula and excursion sets. Random sets and stochastic geometry extend
  beyond this selection.
- **[06D](#synopsis-06d)**: The branching results are supported by the broad
  probability courses; Lawler–Limic treat random walk; Grimmett's
  *Percolation* and *Probability on Graphs* the correlation inequalities and
  percolation; Georgii and Friedli–Velenik the Gibbs-measure theory and the
  Ising phase transition.

### Source comparisons and local copies

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

The approximation principles (converging together, coupling, Poisson
approximation) recur in Billingsley and Kallenberg for
weak convergence and coupling, in the limit-theorem chapters of Durrett and
Klenke for Poisson approximation, and in the large-deviation monographs for
contraction and Gärtner–Ellis. Gaussian integration by parts connects the
Gaussian-measure references with Chen–Goldstein–Shao's treatment of Stein's
method. General exchangeability is developed in Kallenberg and Klenke. The
method of moments is Billingsley, *Probability and Measure*, Section 30.

Local texts directly consulted for this selection:

- [Durrett, *Probability: Theory and Examples*](References/Durrett2019ProbabilityTheoryExamples5thEd-CambridgeSerStatProbMath49.pdf).
- [Klenke, *Probability Theory*](References/Klenke2020ProbabilityTheoryComprehensiveCourse3rdEd-SpringerUTX.pdf).
- [Kallenberg, *Foundations of Modern Probability*](References/Kallenberg2021FoundationsModernProbability3dEd-Springer.PTSM99.pdf).
- [Billingsley, *Probability and Measure*](References/Billingsley1995ProbabilityMeasure3rdEd-Wiley.SerProbMathStat.pdf).
