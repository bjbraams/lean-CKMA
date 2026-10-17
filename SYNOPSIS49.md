# Synopsis: Special functions, integral transforms, and classical formulae

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects recurring core material from Section 49 of
[CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md).
It records the analytic definitions, equations, transformations, integral
representations, and principal identities of the classical families, with
basic hypergeometric and fractional-calculus continuations. Conditions of
convergence and parameter restrictions are part of the statements. General
orthogonality theory is in Section 48, and systematic asymptotic methods
in Section 50.

Write $(a)_n=\Gamma(a+n)/\Gamma(a)$, with its polynomial interpretation
at exceptional $a$. In series, denominator parameters are not nonpositive
integers unless a terminating or limiting interpretation is specified.
Identities initially valid in the stated convergence regions continue
meromorphically in their parameters where defined. Noninteger powers use
consistent branches, ordinarily the principal branch on the cut plane.

## Gamma, beta, and zeta functions

* **1. Euler gamma integral.**
  $\Gamma(z)=\int_0^\infty e^{-t}t^{z-1}dt$, $\Re z>0$,
  is holomorphic there and satisfies $\Gamma(z+1)=z\Gamma(z)$,
  $\Gamma(1)=1$.
* **2. Continuation and divisor.** The recurrence continues
  $\Gamma$ meromorphically to $\mathbb C$, with no zeros and
  simple poles at $-n$, residues $(-1)^n/n!$.
* **3. Weierstrass product.**
  $1/\Gamma(z)=ze^{\gamma z}\prod_{n\geq1}(1+z/n)e^{-z/n}$,
  normally on compact sets. Thus reciprocal gamma is entire.
* **4. Reflection formula.**
  $\Gamma(z)\Gamma(1-z)=\pi/\sin\pi z$, as a meromorphic identity.
* **5. Multiplication formula.** For integers $m\geq1$,
  $\prod_{j=0}^{m-1}\Gamma(z+j/m)
  =(2\pi)^{(m-1)/2}m^{1/2-mz}\Gamma(mz)$.
* **6. Beta integral.** For $\Re a,\Re b>0$,
  $\int_0^1t^{a-1}(1-t)^{b-1}dt=\Gamma(a)\Gamma(b)/\Gamma(a+b)$.
  Substitution also gives the beta integral on $(0,\infty)$.
* **7. Digamma expansion.** For $\psi=\Gamma'/\Gamma$,
  $\psi(z)=-\gamma+\sum_{n\geq0}(1/(n+1)-1/(n+z))$.
  Differentiation gives $\psi^{(m)}(z)=(-1)^{m+1}m!
  \sum_{n\geq0}(n+z)^{-m-1}$ for $m\geq1$ away from poles.
* **8. Stirling expansion.** On $|\arg z|\leq\pi-\varepsilon$,
  $$
  \log\Gamma(z)\sim(z-\tfrac12)\log z-z+\tfrac12\log(2\pi)
  +\sum_{k\geq1}\frac{B_{2k}}{2k(2k-1)z^{2k-1}}.
  $$
  Truncation after $k=N$ has remainder $O_{N,\varepsilon}(|z|^{-2N-1})$.
* **9. Zeta Mellin representation.** For $a>0$, $\Re s>1$,
  $\Gamma(s)\zeta(s,a)=\int_0^\infty t^{s-1}e^{-at}/(1-e^{-t})dt$.
  Subtracting its small-$t$ expansion gives meromorphic continuation;
  the only pole of $\zeta(s,a)$ is simple at $s=1$, residue one.

## Hypergeometric and confluent hypergeometric functions

Define
${}_pF_q(a;b;z)=\sum_{n\geq0}(a_1)_n\cdots(a_p)_n
z^n/((b_1)_n\cdots(b_q)_nn!)$.
Write $F(a,b;c;z)={}_2F_1(a,b;c;z)$ and
$M(a,b,z)={}_1F_1(a;b;z)$.

* **10. Series convergence.** Nonterminating ${}_pF_q$ is entire
  if $p\leq q$, has radius one if $p=q+1$, and radius zero
  if $p>q+1$. At $z=1$ in the middle case, absolute convergence
  holds when $\Re(\sum b_j-\sum a_j)>0$.
* **11. Gauss equation.** $F(a,b;c;z)$ is the solution normalized
  by $F(0)=1$ of
  $z(1-z)y''+[c-(a+b+1)z]y'-aby=0$.
  Its singular points are regular singular at $0,1,\infty$.
* **12. Euler integral.** For $\Re c>\Re b>0$ and $z$ off
  the cut $[1,\infty)$,
  $F(a,b;c;z)=\frac{\Gamma(c)}{\Gamma(b)\Gamma(c-b)}
  \int_0^1t^{b-1}(1-t)^{c-b-1}(1-zt)^{-a}dt$.
* **13. Gauss summation.** If $\Re(c-a-b)>0$,
  $F(a,b;c;1)=\Gamma(c)\Gamma(c-a-b)/[\Gamma(c-a)\Gamma(c-b)]$.
* **14. Euler transformation.**
  $F(a,b;c;z)=(1-z)^{c-a-b}F(c-a,c-b;c;z)$.
* **15. Pfaff transformation.**
  $F(a,b;c;z)=(1-z)^{-a}F(a,c-b;c;z/(z-1))$.
* **16. Connection at one.** If $c-a-b\notin\mathbb Z$, then
  $$
  F(a,b;c;z)=
  \frac{\Gamma(c)\Gamma(c-a-b)}{\Gamma(c-a)\Gamma(c-b)}
  F(a,b;a+b-c+1;1-z)
  +\frac{\Gamma(c)\Gamma(a+b-c)}{\Gamma(a)\Gamma(b)}
  (1-z)^{c-a-b}F(c-a,c-b;c-a-b+1;1-z).
  $$
  Integral exponent differences require limiting logarithmic formulas.
* **17. Chu–Vandermonde summation.** For $n\geq0$,
  $F(-n,b;c;1)=(c-b)_n/(c)_n$.
* **18. Pfaff–Saalschütz summation.**
  ${}_3F_2(a,b,-n;c,1+a+b-c-n;1)
  =(c-a)_n(c-b)_n/[(c)_n(c-a-b)_n]$,
  with no vanishing denominator factors, or by a defined limit.
* **19. Confluent equation and integral.** $M(a,b,z)$ solves
  $zy''+(b-z)y'-ay=0$ and, for $\Re b>\Re a>0$,
  equals $\Gamma(b)[\Gamma(a)\Gamma(b-a)]^{-1}
  \int_0^1e^{zt}t^{a-1}(1-t)^{b-a-1}dt$.
* **20. Kummer transformation.** $M(a,b,z)=e^zM(b-a,b,-z)$.
  Confluence of the Gauss equation produces this equation and its transformations.
* **21. Tricomi solution.** For $\Re a>0$, $\Re z>0$,
  $U(a,b,z)=\Gamma(a)^{-1}\int_0^\infty
  e^{-zt}t^{a-1}(1+t)^{b-a-1}dt$.
  It solves the same equation and satisfies $U(a,b,x)\sim x^{-a}$ for $x\to+\infty$.
* **22. Whittaker reduction.**
  $W_{\kappa,\mu}(z)=e^{-z/2}z^{\mu+1/2}
  U(\mu-\kappa+1/2,1+2\mu,z)$ solves
  $y''+[-1/4+\kappa/z+(1/4-\mu^2)/z^2]y=0$.

## Bessel, Airy, and Gaussian functions

* **23. Bessel series and equation.**
  $J_\nu(z)=\sum_{k\geq0}(-1)^k(z/2)^{2k+\nu}/[k!\Gamma(k+\nu+1)]$
  solves $z^2y''+zy'+(z^2-\nu^2)y=0$ on a chosen branch.
* **24. Second solution.** For noninteger $\nu$,
  $Y_\nu=(\cos\pi\nu\,J_\nu-J_{-\nu})/\sin\pi\nu$;
  integer orders are defined by limits. The outgoing and incoming
  Hankel solutions are $H_\nu^{(1,2)}=J_\nu\pm iY_\nu$.
* **25. Order recurrences.**
  $J_{\nu-1}+J_{\nu+1}=2\nu J_\nu/z$ and
  $J_{\nu-1}-J_{\nu+1}=2J_\nu'$. The same identities hold for $Y$.
* **26. Bessel Wronskian.**
  $J_\nu Y_\nu'-J_\nu'Y_\nu=2/(\pi z)$.
  This fixes the normalization of the independent solutions.
* **27. Modified functions.** The positive-axis solutions
  $I_\nu,K_\nu$ satisfy $z^2y''+zy'-(z^2+\nu^2)y=0$,
  $I_\nu(z)=i^{-\nu}J_\nu(iz)$ on consistent branches, and
  $I_\nu K_\nu'-I_\nu'K_\nu=-1/z$.
* **28. Bessel generating function.**
  $e^{(z/2)(t-t^{-1})}=\sum_{n\in\mathbb Z}J_n(z)t^n$,
  with normal convergence on compact subsets of $0<|t|<\infty$.
* **29. Poisson integral for Bessel functions.** If $\Re\nu>-1/2$,
  $J_\nu(z)=\frac{(z/2)^\nu}{\sqrt\pi\Gamma(\nu+1/2)}
  \int_{-1}^1e^{izt}(1-t^2)^{\nu-1/2}dt$.
  See [DLMF §10.9](https://dlmf.nist.gov/10.9) for its branch conventions.
* **30. Hankel transform.** For real $\nu\geq-1/2$,
  $\mathcal H_\nu f(s)=\int_0^\infty f(r)J_\nu(rs)r\,dr$
  extends to a unitary involution on $L^2((0,\infty),r\,dr)$.
* **31. Fourier–Bessel expansion.** For $\nu>-1$, positive zeros
  $j_{\nu,k}$ are simple, and $J_\nu(j_{\nu,k}x)$ form a
  complete orthogonal system in $L^2((0,1),x\,dx)$, with squared
  norm $J_{\nu+1}(j_{\nu,k})^2/2$.
* **32. Oscillatory Bessel asymptotics.** For fixed real $\nu$ and
  $x\to+\infty$, $J_\nu(x)=\sqrt{2/(\pi x)}
  [\cos(x-\pi\nu/2-\pi/4)+O(x^{-1})]$; $Y_\nu$ has
  the corresponding sine expansion.
* **33. Modified large-argument asymptotics.** For fixed $\nu$,
  $I_\nu(x)\sim e^x/\sqrt{2\pi x}$ and
  $K_\nu(x)\sim\sqrt{\pi/(2x)}e^{-x}$ as $x\to+\infty$.
* **34. Airy representation.** The Airy equation is $y''=zy$.
  For real $x$, $\operatorname{Ai}(x)=\pi^{-1}\int_0^\infty
  \cos(t^3/3+xt)dt$, as an oscillatory integral.
* **35. Airy normalization and asymptotics.**
  $W(\operatorname{Ai},\operatorname{Bi})=1/\pi$ and, for positive large $x$,
  $\operatorname{Ai}(x)\sim x^{-1/4}e^{-2x^{3/2}/3}/(2\sqrt\pi)$,
  $\operatorname{Bi}(x)\sim x^{-1/4}e^{2x^{3/2}/3}/\sqrt\pi$.
* **36. Error function.**
  $\operatorname{erf}z=(2/\sqrt\pi)\int_0^ze^{-t^2}dt$ is entire;
  $\operatorname{erfc}x\sim e^{-x^2}/(\sqrt\pi x)$ as $x\to+\infty$.
  The Gaussian integral is $\int_{\mathbb R}e^{-x^2}dx=\sqrt\pi$.

## Classical polynomial families and spherical functions

* **37. Jacobi hypergeometric representation.**
  $P_n^{(\alpha,\beta)}(x)=\frac{(\alpha+1)_n}{n!}
  F(-n,n+\alpha+\beta+1;\alpha+1;(1-x)/2)$.
* **38. Jacobi orthogonality.** For $\alpha,\beta>-1$, these
  polynomials are orthogonal for $(1-x)^\alpha(1+x)^\beta dx$,
  with squared norm
  $\frac{2^{\alpha+\beta+1}\Gamma(n+\alpha+1)\Gamma(n+\beta+1)}
  {(2n+\alpha+\beta+1)n!\Gamma(n+\alpha+\beta+1)}$,
  interpreted continuously at removable parameter cases.
* **39. Jacobi Rodrigues formula.**
  $P_n^{(\alpha,\beta)}(x)=\frac{(-1)^n}{2^nn!}
  (1-x)^{-\alpha}(1+x)^{-\beta}
  \frac{d^n}{dx^n}[(1-x)^{n+\alpha}(1+x)^{n+\beta}]$.
* **40. Laguerre system.**
  $L_n^{(\alpha)}(x)=(\alpha+1)_nM(-n,\alpha+1,x)/n!$,
  $\sum_{n\geq0}L_n^{(\alpha)}(x)t^n
  =(1-t)^{-\alpha-1}e^{-xt/(1-t)}$, $|t|<1$.
  For $\alpha>-1$, its squared norm for $x^\alpha e^{-x}dx$
  is $\Gamma(n+\alpha+1)/n!$.
* **41. Hermite system.** The physicists' convention is
  $H_n(x)=(-1)^ne^{x^2}(d/dx)^ne^{-x^2}$,
  with $\sum_{n\geq0}H_n(x)t^n/n!=e^{2xt-t^2}$ and orthogonality
  $\int H_nH_me^{-x^2}dx=\sqrt\pi\,2^nn!\delta_{nm}$.
* **42. Gegenbauer generating function.**
  $(1-2xt+t^2)^{-\lambda}=\sum C_n^\lambda(x)t^n$, $|t|<1$.
  For $\lambda>0$ the weight is $(1-x^2)^{\lambda-1/2}$;
  $\lambda=1/2$ gives Legendre polynomials.
* **43. Spherical addition theorem.** For area-orthonormal spherical
  harmonics on $S^2$,
  $\sum_{m=-\ell}^{\ell}Y_{\ell m}(\xi)\overline{Y_{\ell m}(\eta)}
  =(2\ell+1)P_\ell(\xi\cdot\eta)/(4\pi)$.

## Elliptic integrals, elliptic functions, and theta functions

For $0<k<1$, let $k'=\sqrt{1-k^2}$ and
$K(k)=\int_0^{\pi/2}(1-k^2\sin^2t)^{-1/2}dt$,
$E(k)=\int_0^{\pi/2}(1-k^2\sin^2t)^{1/2}dt$.
A prime on $K,E$ below means complementary modulus, not differentiation.

* **44. Elliptic hypergeometric formulas.**
  $K(k)=\frac\pi2F(1/2,1/2;1;k^2)$ and
  $E(k)=\frac\pi2F(-1/2,1/2;1;k^2)$.
* **45. Elliptic derivative relations.**
  $dE/dk=(E-K)/k$ and
  $dK/dk=E/[k(1-k^2)]-K/k$.
* **46. Legendre relation.**
  $K(k)E(k')+E(k)K(k')-K(k)K(k')=\pi/2$.
  See [DLMF §19.7](https://dlmf.nist.gov/19.7).
* **47. Arithmetic–geometric mean.** Iteration
  $a_{n+1}=(a_n+b_n)/2$, $b_{n+1}=\sqrt{a_nb_n}$ for
  positive data has a common limit, and
  $K(k)=\pi/[2\operatorname{AGM}(1,k')]$.
* **48. Jacobi elliptic identities.** The inverse elliptic integral
  defines $\operatorname{sn}$, with
  $\operatorname{sn}^2+\operatorname{cn}^2=1$,
  $\operatorname{dn}^2+k^2\operatorname{sn}^2=1$ and derivatives
  $\operatorname{sn}'=\operatorname{cn}\operatorname{dn}$,
  $\operatorname{cn}'=-\operatorname{sn}\operatorname{dn}$,
  $\operatorname{dn}'=-k^2\operatorname{sn}\operatorname{cn}$.
* **49. Weierstrass equation.** For a lattice $\Lambda$,
  $\wp(z)=z^{-2}+\sum_{\omega\ne0}[(z-\omega)^{-2}-\omega^{-2}]$
  is elliptic and satisfies $(\wp')^2=4\wp^3-g_2\wp-g_3$,
  with $g_2=60\sum\omega^{-4}$, $g_3=140\sum\omega^{-6}$.
* **50. Theta series.** For $|q|<1$,
  $\vartheta_3(z,q)=\sum_{n\in\mathbb Z}q^{n^2}e^{2inz}$
  converges normally in $z$. With $q=e^{\pi i\tau}$ it has
  $\vartheta_3(z+\pi,q)=\vartheta_3(z,q)$ and
  $\vartheta_3(z+\pi\tau,q)=q^{-1}e^{-2iz}\vartheta_3(z,q)$.
* **51. Jacobi imaginary transformation.** Poisson summation gives
  $\vartheta_3(0,e^{-\pi t})=t^{-1/2}\vartheta_3(0,e^{-\pi/t})$,
  $t>0$, with corresponding shifted theta transformations.
* **52. Theta–elliptic relation.** For $q=e^{-\pi K(k')/K(k)}$,
  $K(k)=\frac\pi2\vartheta_3(0,q)^2$ and
  $k=\vartheta_2(0,q)^2/\vartheta_3(0,q)^2$, where
  $\vartheta_2(z,q)=\sum_{n\in\mathbb Z}q^{(n+1/2)^2}e^{i(2n+1)z}$.

## Basic hypergeometric series and q-products

For $0<|q|<1$, set $(a;q)_n=\prod_{j=0}^{n-1}(1-aq^j)$,
$(a_1,\ldots,a_r;q)_n=\prod_i(a_i;q)_n$, and use infinite products
when $n=\infty$. Negative indices use
$(a;q)_{-n}=1/(aq^{-n};q)_n$ when defined. Here
${}_{r+1}\phi_r(a;b;q,z)=\sum_{n\geq0}(a;q)_nz^n/[(b;q)_n(q;q)_n]$,
with products over the listed numerator and denominator parameters.

* **53. q-binomial theorem.**
  $\sum_{n\geq0}(a;q)_nz^n/(q;q)_n
  =(az;q)_\infty/(z;q)_\infty$, $|z|<1$.
* **54. q-Gauss sum.**
  ${}_2\phi_1(a,b;c;q,c/(ab))
  =(c/a,c/b;q)_\infty/(c,c/(ab);q)_\infty$ for $|c/(ab)|<1$.
  See [DLMF §17.6](https://dlmf.nist.gov/17.6).
* **55. Euler q-exponentials.**
  $1/(z;q)_\infty=\sum z^n/(q;q)_n$ for $|z|<1$, and
  $(z;q)_\infty=\sum(-1)^nq^{n(n-1)/2}z^n/(q;q)_n$ for all $z$.
* **56. Jacobi triple product.**
  $\sum_{n\in\mathbb Z}q^{n(n-1)/2}z^n
  =(q,-z,-q/z;q)_\infty$, $z\ne0$.
* **57. Ramanujan bilateral sum.**
  $$
  \sum_{n\in\mathbb Z}\frac{(a;q)_n}{(b;q)_n}z^n
  =\frac{(q,b/a,az,q/(az);q)_\infty}
  {(b,q/a,z,b/(az);q)_\infty},\qquad |b/a|<|z|<1.
  $$
  Denominator and bilateral parameters must be nonsingular;
  see [DLMF §17.8](https://dlmf.nist.gov/17.8).
* **58. q-gamma limit.** For $0<q<1$,
  $\Gamma_q(z)=(1-q)^{1-z}(q;q)_\infty/(q^z;q)_\infty$
  satisfies $\Gamma_q(z+1)=(1-q^z)\Gamma_q(z)/(1-q)$ and
  tends to $\Gamma(z)$ locally uniformly away from its poles as $q\uparrow1$.
* **59. q-Chu–Vandermonde sum.**
  ${}_2\phi_1(q^{-n},b;c;q,cq^n/b)=(c/b;q)_n/(c;q)_n$.
* **60. Askey–Wilson orthogonality.** For real $a,b,c,d$ of
  modulus less than one and $0<q<1$, the degree-$n$ polynomials
  $$
  a^{-n}(ab,ac,ad;q)_n\,
  {}_4\phi_3(q^{-n},abcdq^{n-1},ae^{i\theta},ae^{-i\theta};ab,ac,ad;q,q)
  $$
  in $x=\cos\theta$ are orthogonal on $0<\theta<\pi$ for
  weight $(e^{2i\theta},e^{-2i\theta};q)_\infty/
  (ae^{i\theta},ae^{-i\theta},be^{i\theta},be^{-i\theta},
  ce^{i\theta},ce^{-i\theta},de^{i\theta},de^{-i\theta};q)_\infty$.
  At $a=0$ use the polynomial limit.

## Laplace, Mellin, and positivity representations

* **61. Laplace analyticity and uniqueness.**
  $\mathcal Lf(s)=\int_0^\infty e^{-st}f(t)dt$ is holomorphic
  in its half-plane of absolute convergence. Equality of transforms
  there determines locally integrable functions of exponential order almost everywhere.
* **62. Bromwich inversion.** For a locally piecewise $C^1$
  function of exponential order,
  $\frac12(f(t+)+f(t-))=(2\pi i)^{-1}
  \lim_{T\to\infty}\int_{c-iT}^{c+iT}e^{st}\mathcal Lf(s)ds$
  at $t>0$, with $c$ in the absolute-convergence half-plane.
* **63. Laplace convolution and derivatives.**
  $\mathcal L(f*g)=\mathcal Lf\,\mathcal Lg$ and
  $\mathcal L(f')=s\mathcal Lf-f(0+)$ under the corresponding
  integrability and absolute-continuity hypotheses.
* **64. Mellin inversion.** For
  $\mathcal Mf(s)=\int_0^\infty f(x)x^{s-1}dx$, analyticity
  holds in its fundamental strip, and
  $f(x)=(2\pi i)^{-1}\int_{c-i\infty}^{c+i\infty}
  \mathcal Mf(s)x^{-s}ds$ under Fourier inversion hypotheses on the logarithmic variable.
* **65. Mellin Plancherel.** On $L^2(dx/x)$,
  $\int|f(x)|^2dx/x=(2\pi)^{-1}\int|\mathcal Mf(it)|^2dt$,
  by the $L^2$ extension of the transform. Mellin convolution becomes multiplication.
* **66. Mellin–Barnes representation.** If $x>0$,
  $0<c<\Re a$, then
  $(1+x)^{-a}=[2\pi i\Gamma(a)]^{-1}
  \int_{c-i\infty}^{c+i\infty}\Gamma(s)\Gamma(a-s)x^{-s}ds$.
* **67. Bernstein–Widder theorem.** A smooth $f:(0,\infty)\to\mathbb R$
  is completely monotone, $(-1)^nf^{(n)}\geq0$, exactly when
  $f(x)=\int_{[0,\infty)}e^{-xt}d\mu(t)$ for a unique positive
  measure with finite transform for every $x>0$.
* **68. Bernstein-function representation.** A nonnegative smooth
  function with completely monotone derivative has the unique form
  $f(x)=a+bx+\int_{(0,\infty)}(1-e^{-xt})d\nu(t)$,
  $a,b\geq0$, $\int(1\wedge t)d\nu<\infty$.
* **69. Complete Bernstein and Stieltjes functions.** A Bernstein
  function has completely monotone Lévy density exactly when $f(x)/x$
  is Stieltjes, that is,
  $f(x)/x=a/x+b+\int_{(0,\infty)}(x+t)^{-1}d\sigma(t)$,
  with $a,b\geq0$, $\sigma\geq0$, and $\int(1+t)^{-1}d\sigma<\infty$.

## Fractional integrals and Mittag–Leffler functions

For $\alpha>0$ define
$I^\alpha f(t)=\Gamma(\alpha)^{-1}\int_0^t(t-s)^{\alpha-1}f(s)ds$.
For $m-1<\alpha<m$, the **Caputo derivative** is
$D_C^\alpha u=I^{m-\alpha}u^{(m)}$; integer orders use ordinary derivatives.

* **70. Fractional semigroup.** $I^\alpha I^\beta=I^{\alpha+\beta}$
  for locally integrable functions and positive orders, almost everywhere.
  The Riemann–Liouville derivative is a left inverse on the range
  of its fractional integral with the corresponding regularity.
* **71. Caputo Laplace formula.** For functions with the stated
  initial derivatives and sufficient exponential integrability,
  $\mathcal L(D_C^\alpha u)=s^\alpha\mathcal Lu
  -\sum_{j=0}^{m-1}s^{\alpha-1-j}u^{(j)}(0+)$.
* **72. Mittag–Leffler entire functions.** For $\alpha>0$,
  $E_{\alpha,\beta}(z)=\sum_{n\geq0}z^n/\Gamma(\alpha n+\beta)$
  is entire of order $1/\alpha$; $E_{1,1}(z)=e^z$.
* **73. Mittag–Leffler Laplace transform.** For $\alpha,\beta>0$
  and $\Re s>|\lambda|^{1/\alpha}$,
  $\int_0^\infty e^{-st}t^{\beta-1}E_{\alpha,\beta}(\lambda t^\alpha)dt
  =s^{\alpha-\beta}/(s^\alpha-\lambda)$.
* **74. Fractional relaxation and complete monotonicity.** For
  $0<\alpha\leq1$, $E_{\alpha,1}(-x)$ and
  $E_{\alpha,1}(-t^\alpha)$ are completely monotone on the positive axis.
  The solution of $D_C^\alpha u=\lambda u$, $u(0)=1$, is
  $E_{\alpha,1}(\lambda t^\alpha)$.

## Reference guide

Andrews–Askey–Roy, Whittaker–Watson, Bateman, Lebedev, Temme,
Beals–Wong, and the NIST reference share the classical definitions,
equations, integrals, and transformations. Gasper–Rahman and Ismail
develop the q-series and orthogonal-polynomial continuation. Carlson
and the elliptic-function books supply complementary integral viewpoints.
Widder, Titchmarsh, Sneddon, and Schilling–Song–Vondraček supply
the transform and positivity framework; the fractional-calculus and
Mittag–Leffler references explain the last section. The catalogue avoids
reproducing isolated table entries without their analytic context.

Local full-text sources consulted:

* [Andrews–Askey–Roy, *Special Functions*](References/AndrewsAskeyRoy1999SpecialFunctions-CambridgeEMA71.pdf).
* [Beals–Wong, *Special Functions and Orthogonal Polynomials*, second edition](References/BealsWong2015SpecialFunctionsOrthogonalPolynomials2ndEd-CambridgeStudiesAM153.pdf).
* [Temme, *Special Functions*](References/Temme1996SpecialFunctionsIntroductionClassicalFunctionsMathematicalPhysics-Wiley.pdf).
* [Gasper–Rahman, *Basic Hypergeometric Series*, second edition](References/GasperRahman2004BasicHypergeometricSeries2ndEd-CambridgeEMA96.pdf).
* [Viola, *An Introduction to Special Functions*](References/Viola2016IntroductionToSpecialFunctions-SpringerUnitext.pdf).
* [Schilling–Song–Vondraček, *Bernstein Functions*](References/SchillingSongVondraček2009BernsteinFunctionsTheoryApplications-DeGruyterStudMath37.pdf).
* [Gorenflo–Kilbas–Mainardi–Rogosin, *Mittag-Leffler Functions*, first edition](References/GorenfloKilbasMainardiRogosin2014MittagLefflerFunctionsRelatedTopicsApplications-SpringerSMM.pdf).

The linked DLMF sections were used to check the stated Bessel integral,
elliptic connection, and q-summation normalizations alongside these texts.
