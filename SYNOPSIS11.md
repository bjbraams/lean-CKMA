# Synopsis: Classical inequalities, means, majorization, and rearrangement

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-11);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis describes the recurring core of Section 11 of
[CKMA-bib.md](CKMA-bib.md#ckma-11). It follows the
classical progression from convexity and means through finite-dimensional
ordering to integral inequalities and symmetrization. Functional and
geometric inequalities involving derivatives or Minkowski addition, such as
the Euclidean Hardy, Sobolev, Hardy–Littlewood–Sobolev, Pólya–Szegő,
isoperimetric, Brunn–Minkowski, Prékopa–Leindler, Brascamp–Lieb,
Loomis–Whitney, and Faber–Krahn inequalities, are stated in Section 14, where
their connections with capacity, semigroups, and spectral theory become
central.

Weights $w_i$ are positive and sum to one unless stated otherwise; means are
initially defined for positive $x_i$. Conjugate exponents satisfy
$1/p+1/p'=1$. Integrals of nonnegative functions may be infinite unless a
finite bound is asserted. Sharp constants are identified where they are a
standard part of the theorem, rather than supplied for every variant.

## Convexity and means

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
the power and quasi-arithmetic means are internal.

* **1. Young's inequality.** For $a,b\geq0$ and $1<p<\infty$,
  $ab\leq a^p/p+b^{p'}/p'$, with equality exactly when $a^p=b^{p'}$.
  Equivalently, $st\leq\phi(s)+\phi^*(t)$ for a convex function and its
  Legendre conjugate whenever these quantities are defined.
* **2. Weighted arithmetic–geometric mean.**
  $\prod_i x_i^{w_i}\leq\sum_iw_ix_i$, with equality exactly when all $x_i$
  are equal. The inequality extends to nonnegative entries by continuity.
* **3. Power-mean theorem.** If $r<s$, then $M_r\leq M_s$. For positive
  weights equality holds exactly for a constant vector.
* **4. Jensen's inequality.** For convex $\phi$,
  $\phi(\sum_iw_ix_i)\leq\sum_iw_i\phi(x_i)$. On a probability space the
  same assertion holds for expectations under the necessary integrability.
* **5. Equality in Jensen.** For strictly convex $\phi$, equality in Jensen
  holds exactly when the random variable is almost surely constant. More
  generally, equality forces the distribution to lie in a region on which
  an appropriate supporting affine function agrees with $\phi$.
* **6. Hermite–Hadamard inequality.** If $\phi$ is convex on $[a,b]$, $a<b$,
  $$\phi((a+b)/2)\leq\frac1{b-a}\int_a^b\phi(t)dt
    \leq\frac{\phi(a)+\phi(b)}2.$$
* **7. Log-convexity of moments.** For positive $x_i$, the function
  $r\mapsto\log\sum_iw_ix_i^r$ is convex. More generally, Hölder gives
  $\int f^{(1-t)r+ts}\leq(\int f^r)^{1-t}(\int f^s)^t$ when the
  integrals are finite.
* **8. Kantorovich inequality.** If $0<m\leq x_i\leq M$, then
  $$(\sum_iw_ix_i)(\sum_iw_i/x_i)\leq\frac{(M+m)^2}{4Mm}.$$
* **9. Newton and Maclaurin inequalities.** If $e_k$ is the $k$th elementary
  symmetric polynomial of nonnegative $x_1,\ldots,x_n$ and
  $E_k=e_k/\binom nk$, then $E_k^2\geq E_{k-1}E_{k+1}$ for $1\leq k<n$;
  Newton's inequalities hold for arbitrary real $x_i$. For nonnegative $x_i$,
  consequently $E_1\geq E_2^{1/2}\geq\cdots\geq E_n^{1/n}$ (Maclaurin).
* **10. Comparison of quasi-arithmetic means.** For continuous strictly
  increasing generators $\phi,\psi$, put
  $M_\phi=\phi^{-1}(\sum_iw_i\phi(x_i))$. The inequality
  $M_\phi\leq M_\psi$ for all finite positive-weight data in the interval
  holds exactly when $\psi\circ\phi^{-1}$ is convex. Two generators give the
  same mean exactly when $\psi=a\phi+b$ with $a\ne0$. On $(0,\infty)$ the
  positively homogeneous quasi-arithmetic means are exactly the power means
  $M_r$, $-\infty<r<\infty$.
* **11. Logarithmic mean.** For distinct $a,b>0$, put
  $L(a,b)=(a-b)/(\log a-\log b)=\int_0^1a^{1-t}b^t\,dt$. Then
  $\sqrt{ab}<L(a,b)<M_{1/3}(a,b)<(a+b)/2$ for equally weighted power means,
  and $1/3$ is the smallest power-mean index giving the upper bound (Lin).

## Norm inequalities and finite rearrangements

For a finite vector $x$, let $x^\downarrow$ be its decreasing rearrangement.
The same $L^p$ inequalities apply to counting measure, weighted finite spaces,
and general measure spaces with the stated integrability.

* **12. Cauchy–Schwarz.**
  $|\langle x,y\rangle|^2\leq\langle x,x\rangle\langle y,y\rangle$.
  Equality holds exactly for linearly dependent vectors, including the zero cases.
* **13. Hölder.** $\int|fg|\leq\|f\|_p\|g\|_{p'}$, including the
  $1,\infty$ endpoints. For $1<p<\infty$ and nonzero nonnegative factors,
  equality holds exactly when $f^p$ and $g^{p'}$ are proportional almost everywhere.
* **14. Minkowski.** For $1\leq p\leq\infty$,
  $\|f+g\|_p\leq\|f\|_p+\|g\|_p$. For $1<p<\infty$, equality for real
  nonzero functions requires proportionality with the same sign almost everywhere.
* **65. Reverse Minkowski for positive functions.** For $0<p<1$ and
  nonnegative $f,g$ with finite $p$-quasi-norms,
  $\|f+g\|_p\geq\|f\|_p+\|g\|_p$.
  Positivity is essential: the ordinary $L^p$ quasi-triangle inequality for
  signed functions has a different form.
* **15. Generalized Hölder.** If $p_i\in[1,\infty]$ and $\sum_i1/p_i=1$,
  then $\int\prod_i|f_i|\leq\prod_i\|f_i\|_{p_i}$.
* **16. Lyapunov norm inequality.** On a probability space,
  $\|f\|_p\leq\|f\|_q$ for $0<p<q\leq\infty$. On a space of finite
  mass $m$, the factor is $m^{1/p-1/q}$.
* **17. Chebyshev's sum inequality.** For similarly ordered real vectors,
  $\sum_iw_ia_ib_i\geq(\sum_iw_ia_i)(\sum_iw_ib_i)$.
  Opposite ordering reverses the inequality. The weighted version follows
  from the sign of $(a_i-a_j)(b_i-b_j)$.
* **64. Grüss and Popoviciu bounds.** On a probability space, if
  $m\leq f\leq M$, $r\leq g\leq R$, then
  $|\mathbb E(fg)-\mathbb Ef\mathbb Eg|\leq(M-m)(R-r)/4$.
  In particular $\operatorname{Var}f\leq(M-m)^2/4$. Both constants are sharp;
  equal probability at the two endpoints gives the extremal variance.
* **18. Rearrangement inequality.** Among all pairings of two real vectors,
  $\sum_i a_i^\downarrow b_i^\uparrow$ is minimal and
  $\sum_i a_i^\downarrow b_i^\downarrow$ is maximal.
* **73. Abel's inequality.** If $b_1\geq b_2\geq\cdots\geq b_n\geq0$, then
  $|\sum_ia_ib_i|\leq b_1\max_k|\sum_{i\leq k}a_i|$. More precisely,
  $\sum_ia_ib_i$ lies between $b_1\min_kA_k$ and $b_1\max_kA_k$, where
  $A_k=\sum_{i\leq k}a_i$; summation by parts gives the proof.
* **19. Bergström inequality.** For $b_i>0$ and real $a_i$,
  $\sum_i a_i^2/b_i\geq(\sum_i a_i)^2/\sum_i b_i$.
  Equality holds exactly when $a_i/b_i$ is constant.
* **20. Schur's cubic inequality.** For $a,b,c\geq0$,
  $$a(a-b)(a-c)+b(b-a)(b-c)+c(c-a)(c-b)\geq0.$$
* **21. Muirhead inequality.** If exponent vectors $\alpha,\beta\in[0,\infty)^n$
  have equal sum and $\alpha$ is majorized by $\beta$, then for positive $x_i$
  the permutation average of $x_1^{\alpha_1}\cdots x_n^{\alpha_n}$ is no
  larger than the corresponding average with exponents $\beta$. Conversely,
  if this holds for all positive $x$, then $\alpha\prec\beta$.

## Majorization, convex order, and entropy

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

* **22. Hardy–Littlewood–Pólya characterization.** $x\prec y$ exactly when
  $x=Dy$ for a doubly stochastic matrix, and exactly when $x$ belongs to the
  convex hull of the permutations of $y$.
* **23. Birkhoff–von Neumann theorem.** Every doubly stochastic matrix is a
  convex combination of permutation matrices; those matrices are precisely
  the extreme points of the doubly stochastic polytope.
* **24. Karamata's inequality.** If $x\prec y$ and $\phi$ is convex on an
  interval containing their entries, then $\sum_i\phi(x_i)\leq\sum_i\phi(y_i)$.
  For strictly convex $\phi$, equality requires $x$ and $y$ to be permutations.
* **71. Weak majorization (Tomić–Weyl).** For real $x,y\in\mathbb R^n$,
  $x\prec_wy$ (decreasing partial sums of $x$ bounded by those of $y$) holds
  exactly when $\sum_i\phi(x_i)\leq\sum_i\phi(y_i)$ for every increasing
  convex $\phi$, and exactly when $x\leq z$ coordinatewise for some $z\prec y$.
  For nonnegative vectors it is equivalent to $x=Sy$ with $S$ doubly
  substochastic.
* **72. Jensen–Steffensen inequality.** If $x_1\geq\cdots\geq x_n$ lie in an
  interval, $W_k=\sum_{i\leq k}w_i$ satisfies $0\leq W_k\leq W_n$ for all $k$
  and $W_n>0$, and $\phi$ is convex there, then
  $\phi(W_n^{-1}\sum_iw_ix_i)\leq W_n^{-1}\sum_iw_i\phi(x_i)$. Some weights may
  be negative.
* **25. Differential criterion for Schur convexity.** A symmetric $C^1$
  function on an open symmetric convex set is Schur-convex exactly when
  $(x_i-x_j)(\partial_i\Phi-\partial_j\Phi)\geq0$ for every pair $i,j$.
* **26. Doubly stochastic contraction.** For every permutation-invariant norm,
  $\|Dx\|\leq\|x\|$ when $D$ is doubly stochastic. Thus averaging
  coordinates decreases every $\ell^p$ norm, $1\leq p\leq\infty$.
* **27. Stop-loss characterization of convex order.** For integrable real
  $X,Y$, convex order is equivalent to equal means and
  $\mathbb E(X-t)^+\leq\mathbb E(Y-t)^+$ for all real $t$.
* **28. Strassen's martingale coupling.** $X\leq_{\mathrm{cx}}Y$ exactly
  when their laws have a coupling $(X',Y')$ with
  $\mathbb E[Y'\mid X']=X'$. Convex order is therefore the order generated
  by mean-preserving random spread.
* **29. Log-sum inequality.** For nonnegative finite vectors,
  $$\sum_i a_i\log(a_i/b_i)\geq
    (\sum_i a_i)\log\frac{\sum_i a_i}{\sum_i b_i},$$
  with the usual zero and infinity conventions. For positive totals, equality
  means proportional vectors on their supports.
* **30. Gibbs and Pinsker inequalities.** For probability vectors,
  $D(p\|q)=\sum_i p_i\log(p_i/q_i)\geq0$, with equality exactly when $p=q$,
  and $D(p\|q)\geq\frac12\|p-q\|_1^2$.
* **31. Entropy under mixing.** Shannon entropy is Schur-concave:
  $p\prec q$ implies $-\sum p_i\log p_i\geq-\sum q_i\log q_i$.
  A doubly stochastic map therefore increases entropy, and the uniform vector
  maximizes it at $\log n$.

## Hardy, Hilbert, and differential inequalities

The Euclidean Hardy inequality for gradients is SYNOPSIS14, item 9.

* **32. Discrete Hardy inequality.** For nonnegative $a_n$ and $1<p<\infty$,
  $$\sum_{n\geq1}\left(\frac{a_1+\cdots+a_n}{n}\right)^p
    \leq(p')^p\sum_{n\geq1}a_n^p.$$
  The constant is optimal.
* **33. Integral Hardy inequality.** For $f\geq0$,
  $$\int_0^\infty\left(\frac1x\int_0^xf(t)dt\right)^pdx
    \leq(p')^p\int_0^\infty f(x)^pdx,\qquad1<p<\infty.$$
* **34. Dual Hardy inequality.** For $1<p<\infty$,
  $\int_0^\infty(\int_x^\infty f(t)dt/t)^pdx\leq p^p\int_0^\infty f^p$.
  This is the adjoint form of the averaging inequality, with optimal constant.
* **35. Weighted Hardy criterion.** For positive weights $u,v$ and
  $1<p<\infty$, the bound
  $$\left(\int_0^\infty\left|\int_0^xf(t)dt\right|^pu(x)dx\right)^{1/p}
      \leq C\left(\int_0^\infty|f|^pv\right)^{1/p}$$
  holds exactly when
  $B=\sup_{r>0}(\int_r^\infty u)^{1/p}
  (\int_0^rv^{-1/(p-1)})^{1/p'}<\infty$.
  Its optimal norm satisfies $B\leq C\leq p^{1/p}(p')^{1/p'}B$.
* **37. Hilbert's integral inequality.** For $1<p<\infty$ and nonnegative
  $f\in L^p(0,\infty)$, $g\in L^{p'}(0,\infty)$,
  $$\int_0^\infty\!\int_0^\infty\frac{f(x)g(y)}{x+y}dxdy
    \leq\frac{\pi}{\sin(\pi/p)}\|f\|_p\|g\|_{p'}.$$
  The same optimal constant holds in the discrete sum with denominator $m+n$,
  $m,n\geq1$.
* **38. Carleman's inequality.** For a nonnegative summable sequence,
  $\sum_{n\geq1}(a_1\cdots a_n)^{1/n}\leq e\sum_{n\geq1}a_n$.
  The constant $e$ is optimal.
* **39. Continuous geometric-mean inequality.** For positive integrable $f$,
  $$\int_0^\infty\exp\left(\frac1x\int_0^x\log f(t)dt\right)dx
    \leq e\int_0^\infty f(x)dx,$$
  with the exponential interpreted as zero if the logarithmic integral is
  $-\infty$. This is the continuous Carleman–Knopp inequality.
* **40. Grönwall inequality.** If nonnegative continuous $u$ satisfies
  $u(t)\leq a+\int_0^tb(s)u(s)ds$, $a\geq0$, $b\geq0$ integrable, then
  $u(t)\leq a\exp(\int_0^tb)$. The same conclusion holds for measurable
  $u,b\geq0$ with $b\in L^1$ and $bu\in L^1(0,t)$. It gives uniqueness,
  continuous dependence, and perturbation bounds for differential and Volterra
  equations.
* **41. Bihari inequality.** Replace $u$ in the integral by a positive
  increasing continuous $\omega(u)$ and assume $a>0$. With
  $G(s)=\int_{s_0}^sdr/\omega(r)$,
  $u(t)\leq G^{-1}(G(a)+\int_0^tb)$ while the right side is in the inverse
  domain. This includes nonlinear uniqueness criteria through divergence of
  the reciprocal integral at zero.
* **42. Opial inequality.** For absolutely continuous $u$ on $[0,L]$ with
  $u(0)=u(L)=0$ and $u'\in L^2$,
  $\int_0^L|uu'|\leq(L/4)\int_0^L|u'|^2$. The constant is sharp.
* **43. Wirtinger inequalities.** For $u\in H_0^1(0,L)$,
  $\int|u'|^2\geq(\pi/L)^2\int|u|^2$, with equality for multiples of
  $\sin(\pi x/L)$. For a $2\pi$-periodic mean-zero $H^1$ function,
  $\int|u'|^2\geq\int|u|^2$, with equality in the first harmonic space.

## Rearrangement and symmetrization

For $f\geq0$ with finite-measure superlevel sets, its **decreasing
rearrangement** $f^*:(0,\infty)\to[0,\infty]$ has the same distribution
function $|\{f>t\}|$. In $\mathbb R^n$, its **symmetric decreasing
rearrangement** is $f^\#(x)=f^*(\omega_n|x|^n)$, where $\omega_n$ is the
volume of the unit ball, with centered balls as superlevel sets. These operations preserve all $L^p$ norms and all integrals
of nonnegative Borel functions of the values that vanish at zero. The
Pólya–Szegő, Hardy–Littlewood–Sobolev, and sharp Sobolev inequalities are
SYNOPSIS14, items 19, 13, and 3.

* **44. Layer-cake formula.** $f(x)=\int_0^\infty1_{\{f>t\}}(x)dt$, and
  $\int f^p=p\int_0^\infty t^{p-1}|\{f>t\}|dt$ for $p>0$.
* **45. Hardy–Littlewood rearrangement inequality.** For nonnegative $f,g$,
  $\int fg\leq\int_0^\infty f^*(s)g^*(s)ds$; in Euclidean space the latter
  equals $\int f^\#g^\#$.
* **46. Riesz rearrangement inequality.** For nonnegative functions on
  $\mathbb R^n$,
  $$\iint f(x)g(x-y)h(y)dxdy
    \leq\iint f^\#(x)g^\#(x-y)h^\#(y)dxdy.$$
* **48. Steiner symmetrization.** Steiner symmetrization in a hyperplane
  direction preserves volume, maps convex bodies to convex bodies, does not
  increase perimeter or Dirichlet energy, and does not decrease the integrals
  in the Riesz inequality. Suitable sequences of Steiner symmetrizations of a
  compact set converge in the Hausdorff metric to the ball of the same
  volume, giving a common route to the isoperimetric and Riesz inequalities.
* **49. Maximal integral characterization.** For $f\geq0$ and $s>0$ on a
  nonatomic measure space,
  $$\sup_{\mu(E)\leq s}\int_Ef\,d\mu=\int_0^sf^*(t)dt,$$
  extending $f^*$ by zero beyond the total mass. Thus rearrangement describes
  the largest integral that can be captured by a set of prescribed size.
* **62. Bathtub principle.** On a finite measure space, for real $f\in L^1$
  and $0<m<\mu(X)$, the minimum of $\int fg\,d\mu$ under $0\leq g\leq1$,
  $\int g=m$, is attained by filling the lowest values of $f$:
  $g=1_{\{f<t\}}+c1_{\{f=t\}}$ for a suitable threshold and $0\leq c\leq1$.
  Fractional filling allows the statement to include atoms.
* **50. Rearrangement contraction.** For nonnegative $f,g$ on the same
  measure space and $1\leq p<\infty$,
  $\|f^*-g^*\|_{L^p(0,\infty)}\leq\|f-g\|_p$.

## Geometric and convolution consequences

The Brunn–Minkowski, Prékopa–Leindler, geometric Brascamp–Lieb,
Loomis–Whitney, and Faber–Krahn inequalities are SYNOPSIS14, items 28, 29,
31, 32, and 21. A **log-concave function** has convex
superlevel geometry in the stronger sense
$f((1-t)x+ty)\geq f(x)^{1-t}f(y)^t$.

* **56. Young's convolution inequality.** If
  $1+1/r=1/p+1/q$ with exponents in $[1,\infty]$, then
  $\|f*g\|_r\leq\|f\|_p\|g\|_q$ on $\mathbb R^n$.
* **57. Sharp Young inequality.** Its optimal constant is
  $(C_pC_q/C_r)^n$, where
  $C_s=(s^{1/s}/(s')^{1/s'})^{1/2}$ and $C_1=C_\infty=1$.
  For interior exponents, appropriately matched Gaussian functions attain it.
* **60. Prékopa marginal theorem.** Integrating a log-concave nonnegative
  function over some of its variables produces a log-concave marginal,
  provided that marginal is finite. In particular, convolution preserves
  log-concavity for integrable log-concave functions.

## Iterative means, moment inequalities, and interpolation

The arithmetic–geometric mean is SYNOPSIS49, item 49; the Khintchine and
Paley–Zygmund inequalities are SYNOPSIS07, items 11 and 10; the
Hausdorff–Young inequality is SYNOPSIS27, item 4.

* **66. Clarkson inequalities.** For $2\leq p<\infty$,
  $$\left\|\frac{f+g}2\right\|_p^p+
    \left\|\frac{f-g}2\right\|_p^p
      \leq\frac{\|f\|_p^p+\|g\|_p^p}2.$$
  For $1<p\leq2$, the corresponding bound has left exponent $p'$ and right
  side $((\|f\|_p^p+\|g\|_p^p)/2)^{p'/p}$.
  These quantitative midpoint inequalities imply uniform convexity of $L^p$
  throughout $1<p<\infty$.
* **69. Hadamard three-lines theorem.** If $F$ is bounded and continuous on
  $0\leq\operatorname{Re}z\leq1$, holomorphic inside, and
  $|F(it)|\leq M_0$, $|F(1+it)|\leq M_1$, then
  $|F(\theta+it)|\leq M_0^{1-\theta}M_1^\theta$ for $0<\theta<1$.
  Applied to suitable scalar matrix elements, it produces the Riesz–Thorin
  interpolation bound for linear operators.

## Reference guide

Hardy–Littlewood–Pólya, *Inequalities*, Chapters II–III and V–X, gives the
classical spine of means, convexity, sums, integral inequalities, and
rearrangements. Bullen's *Handbook* and Niculescu–Persson develop the mean
and convex-function viewpoints. Marshall–Olkin–Arnold supplies the systematic
majorization and stochastic-order account. Garling, especially Chapters 3–11,
connects these inequalities to $L^p$ analysis and interpolation.

The final Clarkson and three-lines results are developed in Garling,
Chapter 9; Garling, Chapters 12–13, also treats the Khintchine and sharp
Fourier inequalities now stated in Sections 07 and 27. Grüss and related
bounded-range inequalities, Abel's inequality, and the Jensen–Steffensen
inequality are treated systematically by Mitrinović–Pečarić–Fink.

The Hardy and differential inequalities recur in Beckenbach–Bellman,
Mitrinović, Mitrinović–Pečarić–Fink, and the weighted-Hardy and
Balinsky–Evans–Lewis monographs. Lieb–Loss and Baernstein (with Drasin and Laugesen)
develop the rearrangement and sharp-integral endpoint; Schneider and
Burago–Zalgaller develop its convex-geometric side. Some of the later
inequalities have wider generalizations, but the Euclidean formulations here
are the shared working versions.

Local source anchors:

- [Hardy–Littlewood–Pólya, *Inequalities*](References/HardyLittlewoodPólya1934Inequalities-CambridgeUniversityPress.pdf).
- [Marshall–Olkin–Arnold, *Inequalities: Theory of Majorization*](References/MarshallOlkinArnold2011InequalitiesTheoryMajorizationApplications2ndEd-SpringerSSS.pdf).
- [Garling, *Inequalities*](References/Garling2007InequalitiesJourneyLinearAnalysis-Cambridge.pdf).
- [Bullen, *Handbook of Means*](References/Bullen2003HandbookMeansInequalities-SpringerKluwerMAIA560.pdf).
- [Mitrinović–Pečarić–Fink, *Classical and New Inequalities*](References/MitrinovićPečarićFink1993ClassicalNewInequalitiesAnalysis-SpringerKluwerMAEE61.pdf).
- [Balinsky–Evans–Lewis, *Hardy's Inequality*](References/BalinskyEvansLewis2015AnalysisGeometryHardysInequality-SpringerUTX.pdf).
- [Baernstein (with Drasin and Laugesen), *Symmetrization in Analysis*](ReferencesSuppl/BaernsteinDrasinLaugesen2019SymmetrizationAnalysis-Cambridge.NMM36.pdf).
