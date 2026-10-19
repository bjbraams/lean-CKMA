# Synopsis: Classical function theory — entire and meromorphic functions, value distribution

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-41);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring core material from Section 41 of
[CKMA-bib.md](CKMA-bib.md#ckma-41).
It emphasizes growth, canonical products, zeros, exponential type,
quasi-analyticity and completeness of exponentials, real-zero and de Branges
theory, Nevanlinna theory, and their connections with normal families and
differential equations.
The elementary Cauchy theory is in Section 40; Hardy-space and operator
formulations are developed in Section 42. Specialized Painlevé equations and
probabilistic zero processes have their own substantial theories and are not
included merely because one listed monograph treats them.

The function-theoretic core here complements the analytic spaces of Section
42, integrable complex equations in Section 51, and the random matrix methods
represented in [07B](CKMA-bib.md#ckma-07b).

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

## Growth, zeros, and canonical products

* **1. Growth dichotomy.** Polynomial growth characterizes polynomials;
  a transcendental entire function has $\log M(r)/\log r\to\infty$.
  The function $\log M(r)$ is convex in $\log r$.
* **2. Order from Taylor coefficients.** For a transcendental entire
  series $f(z)=\sum a_nz^n$,
  $\rho=\limsup_{n\to\infty}n\log n/\log(1/|a_n|)$,
  ignoring zero coefficients and using extended-value conventions.
* **3. Type from Taylor coefficients.** If $0<\rho<\infty$, then
  $e\rho\tau=\limsup_{n\to\infty}n|a_n|^{\rho/n}$.
  This distinguishes minimal, normal, and maximal type at a fixed order.
* **4. Differentiation preserves order.** A transcendental entire
  function and each of its nonzero derivatives have the same order.
  Entire primitives also have that order; Cauchy estimates give the
  associated upper growth bounds.
* **5. Jensen's zero bound.** If $f(0)\ne0$, then
  $\sum_{|a_j|<r}\log(r/|a_j|)
  =(2\pi)^{-1}\int\log|f(re^{it})|dt-\log|f(0)|$.
  Consequently $n(r,0,f)\log(R/r)\leq\log M(R,f)-\log|f(0)|$.
* **6. Exponent of convergence.** For nonzero zeros $a_j$, let
  $\lambda=\inf\{s>0:\sum_j|a_j|^{-s}<\infty\}$.
  Then $\lambda\leq\rho$. Equivalently,
  $\lambda=\limsup\log n(r,0,f)/\log r$ for an infinite zero sequence.
* **7. Canonical-product convergence.** With
  $E_p(w)=(1-w)\exp(w+\cdots+w^p/p)$ and $E_0(w)=1-w$,
  $\sum|a_j|^{-p-1}<\infty$ implies normal convergence of
  $\prod_jE_p(z/a_j)$, with exactly the prescribed zeros.
* **8. Minimal genus and order.** The canonical product formed with
  the least admissible fixed genus $p$ has order $\lambda$.
  Here $p\leq\lambda\leq p+1$; at integer $\lambda$, convergence
  of the borderline reciprocal-power series determines the least genus.
* **9. Weierstrass factorization.** An arbitrary entire function is
  $z^me^{g(z)}\prod E_{p_j}(z/a_j)$ for an entire $g$ and
  suitable factors. Without a growth assumption, $g$ need not be polynomial.
* **10. Hadamard factorization.** An entire function of finite order
  $\rho$ admits a fixed-genus factorization $z^me^{Q(z)}P(z)$
  with $Q$ polynomial of degree at most $\rho$ and $P$ a
  canonical product of genus at most $\lfloor\rho\rfloor$.
* **11. Zero-free finite-order functions.** A zero-free entire function
  of finite order is $e^Q$ for a polynomial $Q$.
  With finitely many zeros it is a polynomial times $e^Q$.
* **12. Noninteger order is detected by zeros.** If an entire function
  has finite noninteger order $\rho$, its zeros have exponent of
  convergence exactly $\rho$.
* **13. Lindelöf's theorem.** Let $f$ be entire of integer order
  $p\geq1$ with zeros $a_j\ne0$. Then $f$ has finite type exactly when
  $n(r,0,f)=O(r^p)$ and the sums $\sum_{|a_j|<r}a_j^{-p}$ are bounded.
  For noninteger order, finite type is equivalent to $n(r,0,f)=O(r^\rho)$.
* **14. Meromorphic finite-order factorization.** A meromorphic
  finite-order function is $z^me^QP_0/P_\infty$, where the
  canonical products represent its nonzero zeros and poles and have
  order no larger than that of the function.
* **15. Logarithmic differentiation.** Normally convergent canonical
  products may be logarithmically differentiated locally away from their
  zeros. The resulting regularized partial fractions describe $f'/f$
  and identify zero multiplicities as residues.
* **16. The $\cos\pi\rho$ theorem.** If $f$ is entire of order
  $\rho<1$ and $\mu(r,f)=\min_{|z|=r}|f(z)|$, then
  $\limsup_{r\to\infty}\log\mu(r,f)/\log M(r,f)\geq\cos\pi\rho$.
  In particular, for $\rho<1/2$ the minimum modulus is unbounded on a
  sequence of circles (Wiman). The function
  $\prod_n(1+z/n^{1/\rho})$ shows sharpness.

## Angular growth and exponential type

For an entire function of order $\rho>0$ and finite type, its
**indicator** is $h(\theta)=\limsup_{r\to\infty}
r^{-\rho}\log|f(re^{i\theta})|$.
The **Cartwright class** consists of exponential-type entire functions with
$\int_{\mathbb R}\log^+|f(x)|/(1+x^2)\,dx<\infty$.
Write $PW_\sigma$ for exponential-type-at-most-$\sigma$ entire functions
whose restrictions to $\mathbb R$ lie in $L^2$.

* **17. Sectorial Phragmén–Lindelöf theorem.** In a sector of opening
  $\alpha$, a boundary bound propagates inside if the function has
  growth $O(\exp(C|z|^s))$ with $s<\pi/\alpha$.
  The strict inequality is essential without an additional type condition.
  Precisely: if the function is continuous on the closed sector and bounded
  by $M$ on its boundary, it is bounded by $M$ throughout the sector.
* **18. Trigonometric convexity.** Indicators satisfy
  $$
  h(\theta)\leq
  \frac{h(a)\sin\rho(b-\theta)+h(b)\sin\rho(\theta-a)}
  {\sin\rho(b-a)},\qquad a<\theta<b,\quad b-a<\pi/\rho.
  $$
  Thus angular growth is constrained by sectorial maximum principles.
* **19. Pólya's indicator-diagram theorem.** Let
  $f(z)=\sum a_nz^n$ have exponential type and Borel transform
  $B(w)=\sum n!a_nw^{-n-1}$. Then
  $h(\theta)=\max_{w\in I}\operatorname{Re}(we^{-i\theta})$, where
  $I$ is the complex conjugate of the smallest compact convex set outside
  which $B$ continues analytically, and
  $f(z)=(2\pi i)^{-1}\oint B(w)e^{zw}dw$ around the conjugate
  diagram $\overline I$ (the convex set itself).
  Multiplication by $e^{az}$ translates $I$ by $\bar a$.
* **20. Denjoy–Carleman–Ahlfors theorem.** An entire function of finite
  order $\rho$ has at most $2\rho$ distinct finite asymptotic values,
  that is, limits along curves tending to infinity. In particular an entire
  function of order less than $1/2$ has none.
* **21. Paley–Wiener theorem.** With Fourier convention $e^{izt}$,
  $f\in PW_\sigma$ precisely when
  $f(z)=\int_{-\sigma}^{\sigma}g(t)e^{izt}dt$ for some $g\in L^2$.
  Plancherel identifies the norms up to the Fourier normalization.
  Equivalently, $PW_\sigma$ consists of the entire functions of exponential
  type at most $\sigma$ whose restrictions to $\mathbb R$ lie in $L^2$.
* **23. Bernstein inequality.** If $f$ is entire of type at most
  $\sigma$ and bounded on $\mathbb R$, then
  $\|f'\|_{L^\infty(\mathbb R)}\leq\sigma\|f\|_{L^\infty(\mathbb R)}$.
  The $L^p$ version holds for $1\leq p<\infty$ when $f|_{\mathbb R}\in L^p$.
* **25. Cartwright–Krein characterization.** An entire function
  belongs to the Cartwright class exactly when it is of bounded type
  in both half-planes, that is, a quotient of bounded holomorphic
  functions in each. Its indicator diagram is a vertical segment.
* **26. Cartwright zero distribution.** Put
  $\sigma_+=h(\pi/2)$ and $\sigma_-=h(-\pi/2)$.
  A Cartwright function has
  $n(r)=(\sigma_++\sigma_-)r/\pi+o(r)$, and only $o(r)$ zeros
  outside any fixed pair of sectors about the positive and negative
  real axes. Multiplicities are included.
* **27. Logarithmic integrability.** For a nonzero Cartwright function,
  $\int|\log|f(x)||/(1+x^2)dx<\infty$.
  In particular, boundedness or $L^p$ integrability on the real axis,
  together with exponential type, imposes strong restrictions on real-axis decay.
* **28. Beurling–Malliavin multiplier theorem.** If
  $0<w\leq1$, $\log w$ is globally Lipschitz, and
  $\int|\log w(x)|/(1+x^2)dx<\infty$, then for every
  $\varepsilon>0$ there is a nonzero $f\in PW_\varepsilon$ with
  $|f(x)|\leq w(x)$ on $\mathbb R$.
* **29. Proximate order.** Every transcendental entire function of
  finite positive order $\rho$ admits a proximate order $\rho(r)\to\rho$ with
  $r\rho'(r)\log r\to0$ and
  $0<\limsup\log M(r)/r^{\rho(r)}<\infty$.
  This replaces minimal or maximal type by a normal growth scale.
* **56. Carlson's theorem.** Let $f$ be holomorphic in
  $\operatorname{Re}z>0$, continuous on its closure, of exponential type
  there, and satisfy $|f(iy)|\leq Ce^{c|y|}$ with $c<\pi$. If
  $f(n)=0$ for $n=0,1,2,\ldots$, then $f\equiv0$. The function
  $\sin\pi z$ shows that $c<\pi$ cannot be relaxed.

## Quasi-analyticity and completeness of exponentials

For positive $M_0=1,M_1,\ldots$ and an interval $I$, the class
$C_I\{M_n\}$ consists of the $C^\infty$ functions with
$|f^{(n)}|\leq c\,\beta^nM_n$ on $I$ for some $c,\beta$ and all $n$. It is
**quasi-analytic** if $f\in C_I\{M_n\}$ and $f^{(n)}(x_0)=0$ for all
$n$ at one $x_0\in I$ force $f\equiv0$. A family $\{e^{i\lambda t}\}$ is
**complete** in $L^2(-a,a)$ if its linear span is dense.

* **70. Denjoy–Carleman theorem.** If $(M_n)$ is logarithmically convex,
  $C_I\{M_n\}$ is quasi-analytic exactly when
  $\sum_nM_n^{-1/n}=\infty$, equivalently
  $\sum_nM_{n-1}/M_n=\infty$, equivalently
  $\int^\infty\log T(r)\,dr/r^2=\infty$ with
  $T(r)=\sup_nr^n/M_n$. For general $(M_n)$ the same holds with $M_n$
  replaced by its largest log-convex minorant. Thus $M_n=n!$ (real-analytic
  functions) and $M_n=(n\log n)^n$ ($n\geq2$) give quasi-analytic classes, while
  $M_n=n!^{s}$, $s>1$ (Gevrey classes), do not.
* **71. Completeness of exponential systems.** If
  $\lambda_n\in\mathbb R$ and $|\lambda_n-n|\leq1/4$ for all
  $n\in\mathbb Z$, then $\{e^{i\lambda_nt}\}$ is complete in
  $L^2(-\pi,\pi)$ (Levinson); with strict inequality uniformly it is a
  Riesz basis (Kadec, SYNOPSIS29, item 61). At the endpoint $1/4$
  completeness may hold without the Riesz-basis property, as for
  $\lambda_n=n-\frac14\operatorname{sign}n$. Removing one exponential
  from the integer system leaves it complete in $L^2(-a,a)$ only for $a<\pi$.
* **72. Beurling–Malliavin radius of completeness.** For a discrete set
  $\Lambda\subset\mathbb R$, call a sequence of disjoint intervals
  $I_k$ **long** if $\sum_k|I_k|^2/(1+\operatorname{dist}(0,I_k)^2)=\infty$,
  and let $D^*(\Lambda)$ be the supremum of $d$ for which some long
  sequence satisfies $\#(\Lambda\cap I_k)\geq d|I_k|$. Then
  $\{e^{i\lambda t}\}_{\lambda\in\Lambda}$ is complete in
  $L^2(-a,a)$ for $a<\pi D^*(\Lambda)$ and incomplete for
  $a>\pi D^*(\Lambda)$. The proof rests on the multiplier theorem (item 28).

## Real zeros, Hermite–Biehler functions, and de Branges spaces

For entire $F$ write $F^\#(z)=\overline{F(\bar z)}$. An entire $E$ is a
**Hermite–Biehler function** if $|E(\bar z)|<|E(z)|$ for $\Im z>0$;
write $E=A-iB$ with $A=(E+E^\#)/2$ and $B=i(E-E^\#)/2$ real entire.
$H^2(\mathbb C_+)$ is the Hardy space of the upper half-plane.

* **73. Gauss–Lucas and Grace–Walsh–Szegő.** The zeros of $P'$ lie in
  the convex hull of the zeros of a polynomial $P$. If $F$ is a symmetric
  polynomial in $z_1,\ldots,z_n$, of degree at most one in each variable,
  and $\zeta_1,\ldots,\zeta_n$ lie in a closed circular region $C$
  (disk, disk complement, or half-plane), then
  $F(\zeta_1,\ldots,\zeta_n)=F(\zeta,\ldots,\zeta)$ for some
  $\zeta\in C$, provided $C$ is convex or $F$ has total degree $n$.
* **74. Laguerre–Pólya class.** The locally uniform limits of real
  polynomials with only real zeros are exactly the entire functions
  $cz^me^{-az^2+bz}\prod_k(1-z/x_k)e^{z/x_k}$ with $a\geq0$,
  $b,c,x_k\in\mathbb R$, and $\sum_kx_k^{-2}<\infty$. The class is
  closed under differentiation and locally uniform limits.
* **75. Hermite–Biehler theorem.** If $E$ is Hermite–Biehler without
  real zeros, then $A$ and $B$ have only real simple zeros, which
  interlace. Conversely, for real polynomials $A,B$ with real simple
  interlacing zeros, one of $A\pm iB$ has all its zeros in a single open
  half-plane.
* **76. de Branges spaces.** For a Hermite–Biehler $E$, the space
  $\mathcal H(E)$ of entire $F$ with $F/E,F^\#/E\in H^2(\mathbb C_+)$ and
  $\|F\|^2=\int_{\mathbb R}|F/E|^2dx$ is a Hilbert space with
  reproducing kernel
  $$
  K(w,z)=\frac{E(z)\overline{E(w)}-E^\#(z)\overline{E^\#(w)}}{2\pi i(\bar w-z)}
  =\frac{B(z)\overline{A(w)}-A(z)\overline{B(w)}}{\pi(z-\bar w)}.
  $$
  For $E(z)=e^{-i\sigma z}$ it is $PW_\sigma$. For all but at most one
  $\alpha\in[0,\pi)$, the kernels at the real zeros of
  $e^{i\alpha}E-e^{-i\alpha}E^\#$ form an orthogonal basis.
* **77. de Branges axioms and ordering.** A nonzero Hilbert space of
  entire functions is isometrically some $\mathcal H(E)$ exactly when
  evaluations at nonreal points are bounded, $F\mapsto F^\#$ is isometric,
  and $F(w)=0$ implies $F(z)(z-\bar w)/(z-w)$ belongs to the space with
  the same norm. de Branges spaces contained isometrically in a given
  $\mathcal H(E)$ are totally ordered by inclusion: if
  $\mathcal H(E_1),\mathcal H(E_2)\subset\mathcal H(E)$ isometrically,
  $E,E_1,E_2$ have no real zeros, and $E_1/E_2$ has bounded type in
  $\mathbb C_+$, then one of the two spaces contains the other.

## Nevanlinna characteristic and the first main theorem

For a meromorphic function on $\mathbb C$, define
$$
m(r,f)=\frac1{2\pi}\int_0^{2\pi}\log^+|f(re^{it})|dt,\quad
N(r,f)=\int_0^r\frac{n(t,f)-n(0,f)}t\,dt+n(0,f)\log r,
\quad T(r,f)=m(r,f)+N(r,f),
$$
where $n(t,f)$ counts poles. For finite $a$, abbreviate
$N(r,a;f)=N(r,1/(f-a))$ and $m(r,a;f)=m(r,1/(f-a))$;
for $a=\infty$ use the original functions. Reduced counting
$\overline N$ counts each point once. The meromorphic order is
$\rho(f)=\limsup\log T(r,f)/\log r$.

* **30. Poisson–Jensen formula.** On a disk without boundary zeros
  or poles, $\log|f(z)|$ equals the Poisson extension of its boundary
  logarithm minus the sum of disk Green functions at its zeros plus
  the sum at its poles, counting multiplicities.
* **31. First main theorem.** For each fixed $a\in\widehat{\mathbb C}$,
  $m(r,a;f)+N(r,a;f)=T(r,f)+O_a(1)$.
  In particular $T(r,1/f)=T(r,f)+O(1)$.
* **32. Characteristic calculus.**
  $T(r,fg)\leq T(r,f)+T(r,g)$ and
  $T(r,f+g)\leq T(r,f)+T(r,g)+O(1)$.
  Möbius postcomposition changes $T$ by $O(1)$.
* **33. Rational composition.** If $R$ is a rational map of degree
  $d\geq1$, then $T(r,R\circ f)=dT(r,f)+O(1)$.
* **34. Growth and rationality.** A meromorphic function is rational
  exactly when $T(r,f)=O(\log r)$; for a rational map of degree $d$,
  $T(r,f)=d\log r+O(1)$. A transcendental function satisfies
  $T(r,f)/\log r\to\infty$.
* **35. Entire maximum and characteristic.** For entire $f$ and
  $0<r<R$,
  $T(r,f)\leq\log^+M(r,f)$ and
  $\log M(r,f)\leq(R+r)(R-r)^{-1}T(R,f)$.
  Thus the two definitions of entire order agree.
* **36. Ahlfors–Shimizu formula.** With spherical derivative
  $f^\#=|f'|/(1+|f|^2)$, set
  $A(t)=\pi^{-1}\int_{|z|<t}(f^\#)^2dA(z)$.
  Then $T(r,f)=\int_0^r A(t)dt/t+O(1)$ as $r\to\infty$.
  The characteristic is therefore an integrated spherical area.
* **37. Small targets in the first main theorem.** If a meromorphic
  $a$ satisfies $T(r,a)=o(T(r,f))$ off an exceptional set, then
  $T(r,f-a)=T(r,f)+o(T(r,f))$ there. Applying the first main
  theorem to $f-a$ gives the corresponding moving-target counting formula.

## The second main theorem, defects, and uniqueness

Here $f$ is transcendental meromorphic on $\mathbb C$.
Write $S(r,f)=O(\log^+T(r,f)+\log r)$ outside a set of finite
linear measure; in particular $S=o(T)$ there. For finite-order
functions the logarithmic derivative estimate improves to $O(\log r)$.

* **38. Logarithmic derivative lemma.**
  $m(r,f'/f)=S(r,f)$. More generally
  $m(r,f^{(k)}/f)=S(r,f)$ for each fixed positive integer $k$.
* **39. Derivative characteristic bound.**
  $T(r,f')\leq T(r,f)+\overline N(r,f)+S(r,f)
  \leq2T(r,f)+S(r,f)$.
  A meromorphic function and its derivative have the same order.
* **40. Second main theorem.** For distinct fixed spherical values
  $a_1,\ldots,a_q$, $q\geq3$,
  $$
  (q-2)T(r,f)\leq\sum_{j=1}^q\overline N(r,a_j;f)+S(r,f).
  $$
  Reduced counting makes ramification part of the inequality.
* **41. Ramified form.** Let $N_{\rm ram}$ count ramification
  points with local degree minus one, including poles. Then
  $\sum_jm(r,a_j;f)+N_{\rm ram}(r,f)\leq2T(r,f)+S(r,f)$.
* **42. Defect relation.** The deficiencies
  $\delta(a,f)=1-\limsup_{r\to\infty}N(r,a;f)/T(r,f)$
  lie in $[0,1]$ and satisfy
  $\sum_{a\in\widehat{\mathbb C}}\delta(a,f)\leq2$.
  Hence deficient values form a countable set.
* **43. Entire defect budget.** For transcendental entire $f$,
  $\delta(\infty,f)=1$ and the sum of finite deficiencies is at most one.
  An omitted value has deficiency one; the converse need not hold.
* **44. Picard as a value-distribution theorem.** A transcendental
  meromorphic function has at most two values taken only finitely
  often, while a transcendental entire function has at most one finite
  such value. The local great Picard theorem gives the essential-singularity version.
* **45. Ramification inequality.** If all preimages of distinct
  $a_j$ have multiplicity at least $m_j\geq2$, counting omitted
  values as $m_j=\infty$, then $\sum_j(1-1/m_j)\leq2$.
  There are at most four completely ramified values.
* **46. Borel exceptional values.** For a meromorphic function of
  finite positive order $\rho$, all but at most two spherical values
  have preimage sequences of exponent of convergence $\rho$.
  For entire functions at most one finite value is exceptional in this sense.
* **47. Hayman's alternative.** If $f$ is transcendental meromorphic and
  $k\geq1$, then either $f$ assumes every finite value infinitely often or
  $f^{(k)}$ assumes every finite nonzero value infinitely often.
  For transcendental entire $f$ and $n\geq1$, $f^nf'$ also takes every
  nonzero value infinitely often (Hayman, Clunie).
* **48. Five-value theorem.** If two nonconstant meromorphic
  functions on $\mathbb C$ have the same preimage sets for five
  distinct spherical values, ignoring multiplicity, they are identical.
* **49. Four-value theorem.** If distinct nonconstant meromorphic
  functions share four values counting multiplicity, one is a Möbius
  transformation of the other. After relabeling, two shared values are
  omitted and the transformation exchanges them while fixing the other two.
* **50. Fermat obstruction.** There are no nonconstant meromorphic
  functions on $\mathbb C$ satisfying $f^n+g^n=1$ for $n\geq4$.
  The corresponding entire-function obstruction holds already for $n\geq3$.
  These follow from the ramification inequalities, or the genus of the Fermat curve.

## Normality, rescaling, and uniqueness sets

The spherical metric is the natural metric at poles. A family is
**normal** if every sequence has a locally spherically convergent subsequence
with meromorphic or constant-infinity limit.

* **51. Marty's criterion.** A family of meromorphic functions is
  normal exactly when its spherical derivatives are locally uniformly bounded.
* **52. Zalcman's rescaling lemma.** Failure of normality at $z_0$
  yields $f_j$, $z_j\to z_0$, and $r_j\downarrow0$ such that
  $f_j(z_j+r_jz)$ converges locally spherically on $\mathbb C$
  to a nonconstant meromorphic function with bounded spherical derivative.
* **53. Montel's three-value theorem.** Meromorphic functions omitting
  three fixed distinct spherical values form a normal family.
  Under rescaling, Picard's theorem rules out a nonconstant limit.
* **54. Hurwitz under spherical convergence.** If meromorphic
  functions converge locally spherically to a nonconstant limit, then
  zeros and poles converge locally with multiplicity, after choosing
  disks whose boundaries avoid the limit's divisor.
* **55. Bounded spherical derivative and growth.** A meromorphic
  function on $\mathbb C$ with bounded spherical derivative has
  $T(r)=O(r^2)$. For entire functions, bounded spherical derivative
  implies exponential type.
* **57. Hadamard and Fabry gap theorems.** If $\sum a_jz^{n_j}$ has
  radius one and $n_{j+1}/n_j\geq q>1$, the unit circle is a natural
  boundary. Fabry's theorem gives the same conclusion under the weaker
  condition $n_j/j\to\infty$.
* **58. Pólya–Carlson theorem.** A power series with integer
  coefficients and radius of convergence one is either rational or
  has the unit circle as a natural boundary.

## Growth methods for complex differential equations

A **differential polynomial** in $f$ is a polynomial in
$f,f',\ldots,f^{(k)}$ with specified meromorphic coefficients.
Such coefficients are called **small** relative to $f$ when their
characteristics are $o(T(r,f))$ outside the stated exceptional set.

* **59. Wiman–Valiron approximation.** For a transcendental entire
  series, let $\nu(r)$ be its central index and choose
  $|z_r|=r$, $|f(z_r)|=M(r)$.
  Outside radii of finite logarithmic measure, for each fixed $k$,
  $f^{(k)}(z_r)\sim(\nu(r)/z_r)^kf(z_r)$.
  Local versions hold in appropriately shrinking disks about $z_r$.
* **60. Central index and order.** The same central index satisfies
  $\rho(f)=\limsup\log\nu(r)/\log r$.
  Wiman–Valiron substitutions therefore turn differential equations
  into growth restrictions at points of maximum modulus.
* **61. Rational expressions with small coefficients.** If
  $R(z,w)$ is reduced rational in $w$, of degree $d$, with
  coefficients small relative to $f$, then
  $T(r,R(z,f))=dT(r,f)+o(T(r,f))$ off the exceptional set.
* **62. Clunie's lemma.** Let $f$ be transcendental meromorphic with
  $f^nP(z,f)=Q(z,f)$, where $P,Q$ are differential polynomials in $f$
  with small coefficients and the total degree of $Q$ is at most $n$.
  Then $m(r,P(z,f))=S(r,f)$.
* **63. Malmquist's theorem.** If $f'=R(z,f)$, with $R$ rational
  in both variables, has a transcendental meromorphic solution on
  $\mathbb C$, the equation is Riccati:
  $f'=a(z)+b(z)f+c(z)f^2$ with rational coefficients.
* **64. Riccati linearization.** For $c\ne0$, setting
  $f=-u'/(cu)$ reduces the Riccati equation locally to
  $u''-(b+c'/c)u'+ac\,u=0$. Away from fixed coefficient
  singularities, solutions extend meromorphically and movable poles are simple.
* **65. Linear equations with entire coefficients.** A linear
  differential equation with entire coefficients and constant nonzero
  leading coefficient has entire solutions for arbitrary initial data.
  If the coefficients are polynomials, its solutions have finite order.
* **66. Polynomial second-order equations.** If $P$ is a nonzero
  polynomial of degree $m$, every nonzero solution of
  $u''+P(z)u=0$ is entire of order $(m+2)/2$.
* **67. Schwarzian representation.** For locally univalent $f$,
  $Sf=f'''/f'-\frac32(f''/f')^2$.
  Ratios of independent solutions of $u''+Au=0$ satisfy $Sf=2A$;
  conversely they locally represent all solutions of that Schwarzian equation.
* **69. Logarithmic derivatives of differential monomials.** For
  fixed nonnegative integers $\alpha_j$,
  $m(r,\prod_{j\geq1}(f^{(j)}/f)^{\alpha_j})=S(r,f)$.
  Consequently, if $P(f)$ is a differential polynomial in $f$ of total
  degree $d$ (the largest degree of its monomials) with coefficients $a$ satisfying $T(r,a)=S(r,f)$, then
  $m(r,P(f))\leq d\,m(r,f)+S(r,f)$.

## Reference guide

Boas and Levin supply the canonical-product, indicator, exponential-type,
and zero-distribution core. Koosis and Paley–Wiener develop its real-axis,
Fourier, multiplier, and uniqueness consequences; Koosis, Levinson, and
Poltoratski treat quasi-analyticity and the completeness of exponential
systems. de Branges's monograph is the source for Hermite–Biehler functions
and de Branges spaces, Levin and Sheil-Small for real zeros and polynomial
zero location. Nevanlinna, Hayman,
Gol'dberg–Ostrovskii, Cherry–Ye, Zheng, and Steinmetz share the
characteristic, main theorems, defects, and ramification theory.
Laine and Steinmetz connect it with growth and differential equations.
The selected differential-equation results are the recurring tools of that
connection, rather than a catalogue of individual special equations.

Local full-text sources consulted:

* [Koosis, *The Logarithmic Integral I*](References/Koosis1988LogarithmicIntegralVol1-CambridgeStudiesAM12.pdf).
* [Koosis, *The Logarithmic Integral II*](References/Koosis1992LogarithmicIntegralVol2-CambridgeStudiesAM21.pdf).
* [Zheng, *Value Distribution of Meromorphic Functions*](References/Zheng2010ValueDistributionMeromorphicFunctions-Springer.pdf).
* [Steinmetz, *Nevanlinna Theory, Normal Families, and Algebraic Differential Equations*](References/Steinmetz2017NevanlinnaTheoryNormalFamiliesAlgebraicDifferentialEquations-SpringerUTX.pdf).
* [Remmert, *Classical Topics in Complex Function Theory*](References/Remmert1998ClassicalTopicsComplexFunctionTheory-SpringerGTM172.pdf), for the overlapping continuation and natural-boundary theory.

The local supplementary volume
[Gonchar–Havin–Nikolski (eds.), *Complex Analysis I*](ReferencesSuppl/GoncharHavinNikolski1997ComplexAnalysis1EntireMeromorphicFunctionsPolyanalyticFunctionsGeneralizations-SpringerEMS85.pdf),
especially the survey by Gol'dberg–Levin–Ostrovskii, was also used to
compare the growth, indicator, asymptotic-value, Cartwright, and Wiman–Valiron
formulations.
