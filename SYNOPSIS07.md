# Synopsis: Concentration, high-dimensional probability, and empirical processes

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects a common core from Section 07 of
[CKMA-bib.md](CKMA-bib.md). The principal themes
are nonasymptotic deviations, concentration in product and Gaussian spaces,
suprema of random processes, uniform laws for empirical measures, and the
probabilistic geometry of random matrices. The invariant-ensemble formulas and
fine universality theory in the specialist references go substantially beyond
this core.

Random variables are real unless matrices are explicitly used. Constants $c,C$
are positive and universal unless dependence is indicated; their values can
change between statements. Suprema of processes are assumed measurable through
separability. For function classes one may, for example, assume a countable
pointwise-dense subclass; weak convergence in $\ell^\infty$ uses the customary
outer-probability formulation when necessary.

## Exponential moments and scalar deviations

A centered variable $X$ is **sub-Gaussian with variance proxy $v$** if
$\mathbb E e^{\lambda X}\leq e^{v\lambda^2/2}$ for all real $\lambda$.
The **Orlicz norms** used below are
$$\|X\|_{\psi_\alpha}=\inf\{s>0:
  \mathbb E\exp(|X|^\alpha/s^\alpha)\leq2\},\qquad\alpha=1,2.$$
Finite $\psi_2$ norm means sub-Gaussian tails; finite $\psi_1$ norm means
**sub-exponential** tails.

A bounded variable is sub-Gaussian; a product or square of Gaussian variables
is generally only sub-exponential. Centering changes either norm by at most a
universal factor. A variance proxy dominates the variance but may be much
larger than it.

* **1. Chernoff bound.** If $\Lambda_X(\lambda)=\log\mathbb E e^{\lambda X}$,
  then
  $$\mathbb P(X\geq t)\leq
    \inf_{\lambda>0}\exp(\Lambda_X(\lambda)-\lambda t).$$
  Independence adds log moment generating functions.
* **2. Hoeffding's lemma.** If $a\leq X\leq b$ and $\mathbb EX=0$, then
  $\mathbb E e^{\lambda X}\leq\exp(\lambda^2(b-a)^2/8)$.
* **3. Hoeffding's inequality.** For independent $X_i\in[a_i,b_i]$,
  $$\mathbb P\left(\left|\sum_i(X_i-\mathbb EX_i)\right|\geq t\right)
    \leq2\exp\left(-\frac{2t^2}{\sum_i(b_i-a_i)^2}\right).$$
* **4. Bernstein's inequality.** For independent centered $X_i$ with
  $|X_i|\leq b$ and $v=\sum_i\mathbb EX_i^2$,
  $$\mathbb P\left(\left|\sum_iX_i\right|\geq t\right)
    \leq2\exp\left(-\frac{t^2}{2(v+bt/3)}\right).$$
* **5. Bennett's inequality.** Under the same assumptions and $v>0$,
  $$\mathbb P\left(\sum_iX_i\geq t\right)
    \leq\exp\left[-\frac{v}{b^2}h\left(\frac{bt}{v}\right)\right],
    \qquad h(u)=(1+u)\log(1+u)-u.$$
* **6. Equivalent sub-Gaussian descriptions.** Up to universal changes of
  constants, $\|X\|_{\psi_2}\leq K$ is equivalent to
  $\mathbb P(|X|>t)\leq2e^{-ct^2/K^2}$ and to
  $(\mathbb E|X|^p)^{1/p}\leq CK\sqrt p$ for $p\geq1$. For centered $X$ it
  is also equivalent to a Gaussian moment-generating-function bound.
* **7. Sums of independent sub-Gaussians.** If centered independent $X_i$ have
  variance proxies $v_i$, then $\sum_i a_iX_i$ has proxy $\sum_i a_i^2v_i$.
  In particular its two-sided tail is at most
  $2\exp[-t^2/(2\sum_i a_i^2v_i)]$.
* **8. Products and squares.** Products of sub-Gaussian variables are
  sub-exponential, even without independence:
  $\|XY\|_{\psi_1}\leq C\|X\|_{\psi_2}\|Y\|_{\psi_2}$.
  In particular $X^2-\mathbb EX^2$ has $\psi_1$ norm at most
  $C\|X\|_{\psi_2}^2$.
* **9. Sub-exponential Bernstein inequality.** For independent centered
  $X_i$ with $\|X_i\|_{\psi_1}\leq K$ and fixed coefficients $a_i$,
  $$\mathbb P\left(\left|\sum_i a_iX_i\right|>t\right)
    \leq2\exp\left[-c\min\left(
      \frac{t^2}{K^2\sum_i a_i^2},\frac{t}{K\max_i|a_i|}\right)\right].$$
* **10. Paley–Zygmund inequality.** For nonnegative $Z\in L^2$ with
  $\mathbb EZ^2>0$ and
  $0<\theta<1$,
  $$\mathbb P(Z\geq\theta\mathbb EZ)
    \geq(1-\theta)^2\frac{(\mathbb EZ)^2}{\mathbb EZ^2}.$$
* **11. Khintchine–Kahane inequalities.** For independent Rademacher signs
  $\varepsilon_i$ and $0<p<\infty$ there are $A_p,B_p>0$ with
  $$A_p\Big(\sum_i|a_i|^2\Big)^{1/2}\leq
    \Big(\mathbb E\Big|\sum_ia_i\varepsilon_i\Big|^p\Big)^{1/p}
    \leq B_p\Big(\sum_i|a_i|^2\Big)^{1/2},$$
  with $B_p\leq C\sqrt p$. For vectors $x_i$ in a normed space, all moments
  $(\mathbb E\|\sum_i\varepsilon_ix_i\|^p)^{1/p}$, $0<p<\infty$, are
  equivalent up to constants depending only on $p$ (Kahane).

## Product spaces, entropy, and geometric concentration

For $Z\geq0$, its **entropy** is
$\operatorname{Ent}(Z)=\mathbb E(Z\log Z)-\mathbb EZ\log\mathbb EZ$.
A probability $\mu$ satisfies a **Poincaré inequality** with constant $C$ if
$\operatorname{Var}_\mu f\leq C\int|\nabla f|^2d\mu$, and a
**logarithmic Sobolev inequality** with constant $C$ if
$\operatorname{Ent}_\mu(g^2)\leq2C\int|\nabla g|^2d\mu$.

* **12. Azuma–Hoeffding inequality.** If a martingale has differences bounded
  by $|M_i-M_{i-1}|\leq c_i$, then
  $\mathbb P(|M_n-M_0|\geq t)\leq2\exp[-t^2/(2\sum_i c_i^2)]$.
* **13. Bounded differences.** For independent coordinates, suppose changing
  coordinate $i$ changes $f$ by at most $c_i$. Then
  $$\mathbb P(|f(X)-\mathbb Ef(X)|\geq t)
    \leq2\exp[-2t^2/\sum_i c_i^2].$$
* **14. Efron–Stein inequality.** If $X^{(i)}$ replaces coordinate $i$ by an
  independent copy, then
  $\operatorname{Var}(f(X))\leq\frac12\sum_i
  \mathbb E(f(X)-f(X^{(i)}))^2$.
* **15. Tensorization of entropy.** For a nonnegative function on a product
  probability space,
  $\operatorname{Ent}(Z)\leq\sum_i\mathbb E\operatorname{Ent}_i(Z)$,
  where $\operatorname{Ent}_i$ integrates only coordinate $i$. Logarithmic
  Sobolev inequalities therefore tensorize with the largest coordinate constant.
* **16. Gaussian Poincaré inequality.** For standard Gaussian measure
  $\gamma_d$, $\operatorname{Var}_{\gamma_d}f\leq\int|\nabla f|^2d\gamma_d$.
  The bound is independent of dimension.
* **17. Gaussian logarithmic Sobolev inequality.** For smooth $g$,
  $\operatorname{Ent}_{\gamma_d}(g^2)\leq2\int|\nabla g|^2d\gamma_d$.
* **18. Bakry–Émery criterion.** If $d\mu=e^{-V}dx$ on $\mathbb R^d$ with
  $V$ smooth and $\nabla^2V\geq\kappa I$ for some $\kappa>0$, then $\mu$
  satisfies the logarithmic Sobolev inequality, hence the Poincaré inequality,
  with constant $1/\kappa$. Bounded perturbations $e^{-W}\mu$ retain such
  inequalities with constants worsened by at most $e^{\operatorname{osc}W}$
  (Holley–Stroock).
* **19. Herbst argument.** A logarithmic Sobolev inequality with constant $C$
  implies, for $L$-Lipschitz $f$,
  $$\mathbb E_\mu e^{\lambda(f-\mathbb E_\mu f)}
    \leq e^{CL^2\lambda^2/2}.$$
  In particular, it yields dimension-independent sub-Gaussian concentration.
  A Poincaré inequality with constant $C$ gives only exponential concentration:
  $\mu(|f-\operatorname{med}f|\geq t)\leq2e^{-t/(3L\sqrt C)}$
  (Gromov–Milman).
* **20. Gaussian Lipschitz concentration.** For standard Gaussian $G$ and
  $L$-Lipschitz $f$,
  $\mathbb P(|f(G)-\mathbb Ef(G)|\geq t)\leq2e^{-t^2/(2L^2)}$.
* **21. Gaussian isoperimetry.** If $A$ is Borel and $A_r$ its open Euclidean
  $r$-neighborhood, then for $r>0$,
  $$\gamma_d(A_r)\geq\Phi(\Phi^{-1}(\gamma_d(A))+r).$$
  Halfspaces give equality. The formula is interpreted by limits for mass zero
  or one.
* **22. Concentration on the sphere.** For uniform $U$ on $S^{d-1}$,
  $d\geq2$, an $L$-Lipschitz function for Euclidean distance satisfies
  $\mathbb P(|f(U)-\operatorname{med}f(U)|>t)
  \leq2\exp(-cdt^2/L^2)$, with a universal $c>0$.
* **23. Gaussian transport inequality.** For every probability $\nu$ on
  $\mathbb R^d$,
  $$W_2(\nu,\gamma_d)^2\leq2H(\nu\mid\gamma_d),$$
  where $W_2^2$ is the infimum of $\mathbb E|X-Y|^2$ over couplings and $H$ is
  relative entropy, with infinite values permitted (Talagrand). Such transport
  inequalities tensorize and imply Gaussian concentration (Marton's argument);
  a logarithmic Sobolev inequality with constant $C$ implies
  $W_2^2\leq2CH$ (Otto–Villani).
* **24. Convex Lipschitz concentration on products.** If independent
  $X_i\in[-1,1]$ and $f:\mathbb R^n\to\mathbb R$ is convex and
  $L$-Lipschitz, then
  $\mathbb P(|f(X)-\operatorname{med}f(X)|>t)\leq C e^{-ct^2/L^2}$.
  Convexity removes the dimension factor present in a direct coordinatewise
  bounded-differences estimate.

## Metric entropy, Gaussian comparison, and chaining

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

* **25. Volumetric covering estimate.** The unit ball of any $d$-dimensional
  normed space has an $\varepsilon$-net of cardinality at most
  $(1+2/\varepsilon)^d$.
* **26. Finite maxima.** If centered $X_1,\ldots,X_N$ have sub-Gaussian
  variance proxies at most $\sigma^2$, then
  $\mathbb E\max_i|X_i|\leq\sigma\sqrt{2\log(2N)}$.
  Independence is unnecessary.
* **27. Dudley's entropy bound.** For a separable centered process with
  sub-Gaussian increments controlled by $d$,
  $$\mathbb E\sup_{t\in T}(X_t-X_{t_0})
    \leq C\int_0^{\operatorname{diam}T}
      \sqrt{\log N(T,d,\varepsilon)}\,d\varepsilon.$$
  Finiteness together with the corresponding vanishing small-scale entropy
  integral gives a bounded uniformly continuous version under the usual
  completion of the index space.
* **28. Sudakov minoration.** For a centered Gaussian process and every
  $\varepsilon>0$,
  $\mathbb E\sup_tX_t\geq c\varepsilon
  \sqrt{\log N(T,d,\varepsilon)}$.
* **29. Sudakov–Fernique comparison.** For centered Gaussian processes
  $(X_t),(Y_t)$ on the same finite index set, if
  $\mathbb E(X_s-X_t)^2\leq\mathbb E(Y_s-Y_t)^2$ for every $s,t$, then
  $\mathbb E\sup_tX_t\leq\mathbb E\sup_tY_t$. The separable integrable
  version follows by approximation.
* **30. Borell–Tsirelson–Ibragimov–Sudakov inequality.** If a separable centered
  Gaussian process has integrable supremum and
  $\sigma^2=\sup_t\mathbb EX_t^2<\infty$, then
  $$\mathbb P\left(\left|\sup_tX_t-\mathbb E\sup_tX_t\right|>u\right)
    \leq2e^{-u^2/(2\sigma^2)}.$$
* **31. Generic chaining upper bound.** For a centered separable process with
  sub-Gaussian increments controlled by $d$,
  $\mathbb E\sup_t(X_t-X_{t_0})\leq C\gamma_2(T,d)$.
* **32. Majorizing measure theorem.** For a centered separable Gaussian
  process with canonical metric $d$,
  $$c\gamma_2(T,d)\leq\mathbb E\sup_tX_t\leq C\gamma_2(T,d).$$

## Empirical processes, combinatorial dimension, and uniform laws

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

* **33. Symmetrization.** For independent Rademacher signs $\varepsilon_i$,
  independent of the data,
  $$\mathbb E\sup_{f\in\mathcal F}|(P_n-P)f|
    \leq2\mathbb E\sup_{f\in\mathcal F}
      \left|\frac1n\sum_i\varepsilon_i f(X_i)\right|.$$
* **34. Rademacher contraction.** If $\phi_i(0)=0$ and each $\phi_i$ is
  $L$-Lipschitz, then for fixed data vectors $a(f)$,
  $$\mathbb E_\varepsilon\sup_f
    \left|\sum_i\varepsilon_i\phi_i(a_i(f))\right|
    \leq2L\,\mathbb E_\varepsilon\sup_f
      \left|\sum_i\varepsilon_i a_i(f)\right|.$$
* **35. Sauer–Shelah bound.** A set class of VC dimension $v$ has at most
  $\sum_{j=0}^v\binom nj$ distinct traces on $n$ points. For $1\leq v\leq n$
  this is at most $(en/v)^v$.
* **36. VC entropy bound.** For a set class of VC dimension $v\geq1$ and any
  probability $Q$,
  $$N(\varepsilon,\{1_A:A\in\mathcal A\},L^2(Q))
    \leq(C/\varepsilon)^{Cv},\qquad0<\varepsilon<1.$$
  Corresponding polynomial entropy bounds hold for VC-subgraph function classes
  relative to their envelopes.
* **37. Uniform deviations for VC classes.** For a measurable VC set class
  of dimension $v\geq1$,
  $$\mathbb E\sup_{A\in\mathcal A}|P_n(A)-P(A)|
    \leq C\sqrt{v/n}.$$
  With probability at least $1-e^{-t}$, the supremum is at most
  $C\sqrt{v/n}+\sqrt{t/(2n)}$. In particular, the class is uniformly
  Glivenko–Cantelli.
* **38. Bracketing uniform law.** If
  $N_{[]}(\varepsilon,\mathcal F,L^1(P))<\infty$ for every $\varepsilon>0$
  and the envelope is integrable, then
  $\sup_{f\in\mathcal F}|P_nf-Pf|\to0$ almost surely.
* **39. Dvoretzky–Kiefer–Wolfowitz inequality.** For the empirical distribution
  function of independent observations with any real distribution function $F$,
  $$\mathbb P\left(\sup_x|F_n(x)-F(x)|>\varepsilon\right)
    \leq2e^{-2n\varepsilon^2}.$$
* **40. Uniform-entropy Donsker theorem.** A pointwise measurable class with
  $|f|\leq1$ is $P$-Donsker for every $P$ if
  $$\int_0^1\sup_Q\sqrt{\log N(\varepsilon,\mathcal F,L^2(Q))}
    \,d\varepsilon<\infty,$$
  where $Q$ ranges over finitely supported probabilities. In particular,
  measurable VC set classes are Donsker.
* **41. Bracketing Donsker theorem.** If the envelope is in $L^2(P)$ and
  $$\int_0^1\sqrt{\log N_{[]}(\varepsilon,\mathcal F,L^2(P))}
    \,d\varepsilon<\infty,$$
  then a pointwise measurable class is $P$-Donsker.
* **42. Concentration of empirical suprema.** Let $\mathcal F$ be a countable
  centered class with $|f|\leq b$, $\sup_fPf^2\leq\sigma^2$, and
  $Z=\sup_f\sum_{i=1}^nf(X_i)$; include the zero function. For $t>0$,
  $$\mathbb P\left\{Z\geq\mathbb EZ+
    \sqrt{2(n\sigma^2+2b\mathbb EZ)t}+bt/3\right\}\leq e^{-t}.$$
  This is a standard Bousquet form of Talagrand's empirical-process inequality.

## Random matrices and high-dimensional geometry

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
$\sqrt{\log(2|T|)}$.

* **43. Hanson–Wright inequality.** If $X_i$ are independent centered
  sub-Gaussian variables with $\|X_i\|_{\psi_2}\leq K$, then for fixed real $A$,
  $$\mathbb P(|X^{\mathsf T}AX-\mathbb EX^{\mathsf T}AX|>t)
    \leq2\exp\left[-c\min\left(
      \frac{t^2}{K^4\|A\|_F^2},\frac{t}{K^2\|A\|}\right)\right].$$
* **44. Matrix Bernstein inequality.** For independent centered self-adjoint
  $d\times d$ matrices $Y_i$ with $\|Y_i\|\leq L$, put
  $v=\|\sum_i\mathbb E Y_i^2\|$. Then
  $$\mathbb P\left(\left\|\sum_iY_i\right\|\geq t\right)
    \leq2d\exp\left(-\frac{t^2}{2(v+Lt/3)}\right).$$
* **45. Sub-Gaussian singular values.** If the rows of an $N\times d$ matrix
  $A$ are independent isotropic sub-Gaussian vectors of norm at most $K$,
  then, with probability at least $1-2e^{-ct^2}$,
  $$\sqrt N-C\sqrt d-t\leq s_{\min}(A)
    \leq s_{\max}(A)\leq\sqrt N+C\sqrt d+t,$$
  where $c,C$ depend only on $K$. Here $s_{\min}$ is the infimum over unit
  vectors in $\mathbb R^d$, so it is zero if $N<d$.
* **46. Covariance estimation.** For independent centered isotropic
  sub-Gaussian vectors $X_i\in\mathbb R^d$ of norm at most $K$, their sample
  covariance satisfies, with probability at least $1-2e^{-t}$,
  $$\left\|N^{-1}\sum_iX_iX_i^{\mathsf T}-I\right\|
    \leq CK^2\left(\sqrt{\frac{d+t}{N}}+\frac{d+t}{N}\right).$$
* **47. Johnson–Lindenstrauss lemma.** For $N$ points in Euclidean space and
  $0<\varepsilon<1$, a linear map into dimension
  $m\leq C\varepsilon^{-2}\log(2N)$ preserves all pairwise squared distances
  within factors $1-\varepsilon$ and $1+\varepsilon$.
* **48. Restricted isometry of random matrices.** If an $m\times d$ matrix has
  independent centered unit-variance sub-Gaussian entries, scaled by $m^{-1/2}$,
  then for $1\leq s\leq d$ and $0<\delta<1$,
  $$m\geq C\delta^{-2}s\log(ed/s)$$
  ensures, with probability at least $1-2e^{-c\delta^2m}$,
  $(1-\delta)|x|^2\leq|Ax|^2\leq(1+\delta)|x|^2$ for every $s$-sparse $x$.
  Constants depend only on the entry sub-Gaussian bound.
* **49. Dvoretzky's theorem.** For every $0<\varepsilon<1$, each
  $d$-dimensional normed space, $d\geq2$, contains a subspace of dimension at
  least $c(\varepsilon)\log d$ on which the norm differs from a suitable
  Euclidean norm by a factor at most $1+\varepsilon$.
* **50. Wigner semicircle law.** Let $W_d$ be real symmetric, with entries
  above the diagonal independent identically distributed of mean zero and
  variance one, and independent identically distributed diagonal entries, all
  taken consistently from one infinite independent array. The empirical
  spectral measures of $W_d/\sqrt d$ converge almost surely weakly to
  $$\frac1{2\pi}\sqrt{4-x^2}\,1_{[-2,2]}(x)\,dx.$$
* **51. Marchenko–Pastur law.** Let $X$ be $N\times d$ with independent
  identically distributed mean-zero, unit-variance real entries, taken
  consistently from an infinite array, and suppose $d/N\to y>0$.
  The empirical spectral measure of $N^{-1}X^{\mathsf T}X$ converges almost
  surely to
  $$\left(1-\frac1y\right)_+\delta_0+
    \frac{\sqrt{(b-x)(x-a)}}{2\pi yx}1_{[a,b]}(x)\,dx,
    \quad a=(1-\sqrt y)^2,\ b=(1+\sqrt y)^2.$$
* **52. Spectral edges.** If in addition the entries have finite fourth
  moment, the extreme eigenvalues of $W_d/\sqrt d$ converge almost surely to
  $\pm2$. For the sample-covariance model, the largest eigenvalue converges
  almost surely to $(1+\sqrt y)^2$; when $0<y<1$, the smallest converges to
  $(1-\sqrt y)^2$ (Bai–Yin). Without a finite fourth moment the largest
  eigenvalue is almost surely unbounded along the sequence, so the moment
  condition is sharp.

## Further standard forms of concentration and Gaussian comparison

The semigroup formulation makes concentration compatible with smoothing.
The **Ornstein–Uhlenbeck semigroup** is
$$P_tf(x)=\mathbb E f(e^{-t}x+\sqrt{1-e^{-2t}}G).$$
On the uniform discrete cube $\{-1,1\}^d$, write
$f(x)=\sum_{S\subseteq\{1,\ldots,d\}}\widehat f(S)\prod_{i\in S}x_i$.
The **noise operator** $T_\rho$ multiplies the coefficient of $S$ by
$\rho^{|S|}$. Both operators preserve their underlying probability measure;
their contractivity between different $L^p$ norms is called hypercontractivity.

* **53. Freedman's martingale inequality.** Let $M_0=0$ and let the martingale
  differences satisfy $|D_k|\leq b$. Put
  $V_n=\sum_{k\leq n}\mathbb E[D_k^2\mid\mathcal F_{k-1}]$. For $t,v>0$,
  $$\mathbb P(M_n\geq t,\ V_n\leq v)
    \leq\exp\left(-\frac{t^2}{2(v+bt/3)}\right).$$
* **54. Matrix Chernoff bounds.** If independent positive semidefinite
  $d\times d$ matrices satisfy $0\leq Y_i\leq RI$, set
  $\mu_{\min}=\lambda_{\min}(\sum_i\mathbb EY_i)$ and similarly $\mu_{\max}$.
  Take $R>0$. For $0<\delta<1$,
  $$\mathbb P\{\lambda_{\min}(\sum_iY_i)\leq(1-\delta)\mu_{\min}\}
    \leq d\left[\frac{e^{-\delta}}{(1-\delta)^{1-\delta}}\right]^{\mu_{\min}/R}.$$
  For $\delta>0$, the corresponding upper-tail bound is
  $d[e^\delta/(1+\delta)^{1+\delta}]^{\mu_{\max}/R}$ at
  $(1+\delta)\mu_{\max}$.
* **55. Gaussian hypercontractivity.** If $1<p\leq q<\infty$ and
  $q-1\leq e^{2t}(p-1)$, then
  $\|P_tf\|_{L^q(\gamma_d)}\leq\|f\|_{L^p(\gamma_d)}$.
  This is equivalent to the Gaussian logarithmic Sobolev inequality with its
  stated normalization.
* **56. Bonami–Beckner inequality.** For the uniform cube,
  $\|T_\rho f\|_q\leq\|f\|_p$ whenever $1<p\leq q<\infty$ and
  $0\leq\rho\leq\sqrt{(p-1)/(q-1)}$. It is independent of dimension and
  underlies noise stability and influence estimates for Boolean functions.
* **57. Talagrand's convex-distance inequality.** On a finite product space
  with independent coordinates and nonempty $A$, define
  $$d_T(x,A)=\sup_{\substack{\alpha_i\geq0\\\sum_i\alpha_i^2\leq1}}
    \inf_{y\in A}\sum_i\alpha_i1_{\{x_i\ne y_i\}}.$$
  Then $\mathbb P(A)\mathbb P\{d_T(X,A)\geq t\}\leq e^{-t^2/4}$.
  Result 24 is a consequence.
* **58. Slepian's inequality.** For centered finite Gaussian vectors $X,Y$
  with equal coordinate variances and
  $\mathbb EX_iX_j\geq\mathbb EY_iY_j$ for $i\ne j$,
  $\mathbb P(\max_iX_i\leq u)\geq\mathbb P(\max_iY_i\leq u)$ for every
  $u\in\mathbb R$.
* **59. Gordon's escape inequality.** For an $m\times d$ matrix $A$ with
  independent $N(0,1)$ entries
  and nonempty closed $T\subseteq S^{d-1}$,
  $$\mathbb E\inf_{x\in T}|Ax|\geq\mathbb E|G_m|-w(T).$$
  With probability at least $1-e^{-u^2/2}$, the infimum is at least
  $\mathbb E|G_m|-w(T)-u$. Thus a Gaussian kernel avoids sets whose width is
  sufficiently smaller than $\sqrt m$.
* **60. Small-ball bound for isotropic sub-Gaussians.** If $X$ is isotropic
  and has sub-Gaussian norm at most $K$, then for each unit vector $u$,
  $\mathbb P(|\langle X,u\rangle|\geq1/\sqrt2)\geq c/K^4$.
  This follows from the Paley–Zygmund inequality applied to
  $\langle X,u\rangle^2$.
* **61. Anderson's inequality.** For a centered Gaussian vector $G$, a convex
  centrally symmetric Borel set $C$, and a deterministic vector $h$,
  $\mathbb P(G+h\in C)\leq\mathbb P(G\in C)$. The covariance may be singular.
* **62. Urysohn's inequality.** For a convex body $K\subseteq\mathbb R^d$,
  $$\left(\frac{|K|}{|B_2^d|}\right)^{1/d}
    \leq\frac{w(K)}{\mathbb E|G_d|}.$$
  In particular, Gaussian width bounds the volume radius. For a Euclidean ball
  the inequality is an equality, fixing the normalization of width used here.

## Reference guide

Vershynin, *High-Dimensional Probability*, Chapters 2–9 and 11, supplies the
scalar, matrix, entropy, and geometric sequence. Van Handel, *Probability in
High Dimension*, Chapters 2–8, independently connects Poincaré and entropy
methods with transport, Gaussian processes, and VC theory; Chapter 9 treats
universality and the semicircle law. Giné–Nickl, *Mathematical Foundations of
Infinite-Dimensional Statistical Models*, Chapters 2–3, supplies the Gaussian
and empirical-process statements, including Donsker criteria and measurability.

The same concentration core is developed by Ledoux and by
Boucheron–Lugosi–Massart. Ledoux–Talagrand and Talagrand's chaining monographs
give the deeper process framework; Dudley and van der Vaart–Wellner give
parallel empirical-process treatments. The random-matrix limits and edges are
shared material in Anderson–Guionnet–Zeitouni, Tao, Bai–Silverstein, and
Pastur–Shcherbina; the hypotheses of results 50–52 follow Bai–Silverstein,
Theorems 2.5, 3.6, 5.1, 5.8, and 5.11. Matrix concentration is
also treated systematically by Tropp. The geometric endpoint is developed by
Milman–Schechtman and Artstein-Avidan–Giannopoulos–Milman.

The supplementary forms above are shared across the concentration references:
Freedman's inequality is developed in the martingale treatments of
Bercu–Delyon–Rio and the broad probability texts; matrix Chernoff bounds in
Tropp and the random-matrix toolkits; hypercontractivity in Ledoux,
Van Handel, and O'Donnell. Gaussian comparison and convex distance appear in
Ledoux–Talagrand, Giné–Nickl, and the chaining references. Urysohn's inequality
belongs to the common geometric material of the asymptotic-convexity books.

Local texts directly consulted for the central concentration and process core:

- [Vershynin, *High-Dimensional Probability*](References/Vershynin2018HighDimensionalProbabilityIntroductionApplicationsDataScience-CambridgeSerStatProbMath47.pdf).
- [Van Handel, *Probability in High Dimension*](References/VanHandel2016ProbabilityHighDimension-CourseNotesPrinceton.pdf).
- [Giné–Nickl, *Mathematical Foundations of Infinite-Dimensional Statistical Models*](References/GinéNickl2015MathematicalFoundationsInfiniteDimensionalStatisticalModels-CambridgeSerStatProbMath40.pdf).
- [Anderson–Guionnet–Zeitouni, *An Introduction to Random Matrices*](References/AndersonGuionnetZeitouni2009IntroductionRandomMatrices-CambridgeStudiesAM118.pdf), Chapter 2, for the Wigner model.
- [Bai–Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*](References/BaiSilverstein2010SpectralAnalysisLargeDimensionalRandomMatrices2ndEd-SpringerSSS.pdf), Chapters 3 and 5, for sample-covariance laws and spectral edges.
