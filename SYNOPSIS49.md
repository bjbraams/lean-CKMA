# Synopsis: Special functions, integral transforms, and classical formulae

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-49);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring core material from Section 49 of
[CKMA-bib.md](CKMA-bib.md#ckma-49).
It records the analytic definitions, equations, transformations, integral
representations, and principal identities of the classical families, with
basic hypergeometric and fractional-calculus continuations. Conditions of
convergence and parameter restrictions are part of the statements. General
orthogonality theory is in Section 48 (the explicit norms and Rodrigues
formulas of the classical families are recorded here as formulae), and
systematic asymptotic methods in Section 50.

The analytic definitions and transform identities here support approximation
in Section 47, orthogonal polynomials in Section 48, asymptotics in Section
50, and integrable methods in Section 51; general reference tables are also
indexed by role in Section 54.

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
  normally on compact sets. Thus reciprocal gamma is entire, and
  Euler's limit $\Gamma(z)=\lim_{n\to\infty}n!\,n^z/[z(z+1)\cdots(z+n)]$
  holds off the poles.
* **4. Bohr–Mollerup theorem.** If $f:(0,\infty)\to(0,\infty)$
  satisfies $f(1)=1$, $f(x+1)=xf(x)$, and $\log f$ is convex,
  then $f=\Gamma$. Euler's limit and the multiplication formula
  follow by checking these three properties.
* **5. Reflection formula.**
  $\Gamma(z)\Gamma(1-z)=\pi/\sin\pi z$, as a meromorphic identity.
* **6. Multiplication formula.** For integers $m\geq1$,
  $\prod_{j=0}^{m-1}\Gamma(z+j/m)
  =(2\pi)^{(m-1)/2}m^{1/2-mz}\Gamma(mz)$.
* **7. Beta integral.** For $\Re a,\Re b>0$,
  $\int_0^1t^{a-1}(1-t)^{b-1}dt=\Gamma(a)\Gamma(b)/\Gamma(a+b)$.
  Substitution also gives the beta integral on $(0,\infty)$.
* **8. Digamma expansion.** For $\psi=\Gamma'/\Gamma$,
  $\psi(z)=-\gamma+\sum_{n\geq0}(1/(n+1)-1/(n+z))$.
  Differentiation gives $\psi^{(m)}(z)=(-1)^{m+1}m!
  \sum_{n\geq0}(n+z)^{-m-1}$ for $m\geq1$ away from poles.
* **9. Stirling expansion.** On $|\arg z|\leq\pi-\varepsilon$,
  $$
  \log\Gamma(z)\sim(z-\tfrac12)\log z-z+\tfrac12\log(2\pi)
  +\sum_{k\geq1}\frac{B_{2k}}{2k(2k-1)z^{2k-1}}.
  $$
  Truncation after $k=N$ has remainder $O_{N,\varepsilon}(|z|^{-2N-1})$.
  Here $t/(e^t-1)=\sum_{n\geq0}B_nt^n/n!$ defines the Bernoulli numbers,
  and $te^{xt}/(e^t-1)=\sum B_n(x)t^n/n!$ the Bernoulli polynomials.
* **10. Zeta Mellin representation.** For $a>0$, $\Re s>1$,
  $\Gamma(s)\zeta(s,a)=\int_0^\infty t^{s-1}e^{-at}/(1-e^{-t})dt$.
  Subtracting its small-$t$ expansion gives meromorphic continuation;
  the only pole of $\zeta(s,a)$ is simple at $s=1$, residue one.
  For integers $n\geq0$, $\zeta(-n,a)=-B_{n+1}(a)/(n+1)$.
* **11. Riemann zeta function.** For $\Re s>1$,
  $\zeta(s)=\sum_{n\geq1}n^{-s}=\prod_p(1-p^{-s})^{-1}$, so
  $\zeta$ has no zeros there. The completed function
  $Z(s)=\pi^{-s/2}\Gamma(s/2)\zeta(s)$ is meromorphic with simple
  poles only at $0,1$ and satisfies $Z(s)=Z(1-s)$ (via the theta transformation, entry 54); and
  $\zeta(2n)=(-1)^{n+1}B_{2n}(2\pi)^{2n}/[2(2n)!]$ for $n\geq1$.
  The trivial zeros are $-2,-4,\ldots$.
* **82. Incomplete gamma and exponential integrals.** For $\Re a>0$,
  $\gamma(a,z)=\int_0^zt^{a-1}e^{-t}dt$; for all $a$ and
  $z\notin(-\infty,0]$, $\Gamma(a,z)=\int_z^\infty t^{a-1}e^{-t}dt$
  along a path in the cut plane, and $\gamma(a,z)+\Gamma(a,z)=\Gamma(a)$.
  Then $\gamma(a,z)=a^{-1}z^aM(a,a+1,-z)$,
  $\Gamma(a,z)=e^{-z}U(1-a,1-a,z)$, and
  $\Gamma(a,z)\sim z^{a-1}e^{-z}\sum_{k\geq0}(a-1)(a-2)\cdots(a-k)z^{-k}$
  as $z\to\infty$ in $|\arg z|\leq3\pi/2-\delta$. Special cases are
  $\operatorname{erfc}z=\pi^{-1/2}\Gamma(\tfrac12,z^2)$ for $\Re z>0$ and
  $E_1(z)=\int_z^\infty e^{-t}t^{-1}dt=\Gamma(0,z)
  =-\gamma-\log z-\sum_{k\geq1}(-z)^k/(k\,k!)$.

## Hypergeometric and confluent hypergeometric functions

Define
${}_pF_q(a;b;z)=\sum_{n\geq0}(a_1)_n\cdots(a_p)_n
z^n/((b_1)_n\cdots(b_q)_nn!)$.
Write $F(a,b;c;z)={}_2F_1(a,b;c;z)$ and
$M(a,b,z)={}_1F_1(a;b;z)$.

* **12. Series convergence.** Nonterminating ${}_pF_q$ is entire
  if $p\leq q$, has radius one if $p=q+1$, and radius zero
  if $p>q+1$. At $z=1$ in the middle case, absolute convergence
  holds when $\Re(\sum b_j-\sum a_j)>0$.
* **13. Gauss equation.** For $c\notin\{0,-1,-2,\ldots\}$,
  $F(a,b;c;z)$ is the unique solution holomorphic at $0$ with
  $y(0)=1$ of
  $z(1-z)y''+[c-(a+b+1)z]y'-aby=0$.
  Its singular points $0,1,\infty$ are regular singular, with exponents
  $\{0,1-c\}$, $\{0,c-a-b\}$, $\{a,b\}$; if $c\notin\mathbb Z$,
  $z^{1-c}F(a-c+1,b-c+1;2-c;z)$ is a second solution at $0$.
  Every second-order Fuchsian equation with exactly three singular points
  reduces to this one by a Möbius map and factors $z^\lambda(1-z)^\mu$
  (Riemann's $P$-symbol), which yields Kummer's 24 solutions.
* **14. Euler integral.** For $\Re c>\Re b>0$ and $z$ off
  the cut $[1,\infty)$,
  $F(a,b;c;z)=\frac{\Gamma(c)}{\Gamma(b)\Gamma(c-b)}
  \int_0^1t^{b-1}(1-t)^{c-b-1}(1-zt)^{-a}dt$.
* **15. Gauss summation.** If $\Re(c-a-b)>0$,
  $F(a,b;c;1)=\Gamma(c)\Gamma(c-a-b)/[\Gamma(c-a)\Gamma(c-b)]$.
* **16. Euler transformation.**
  $F(a,b;c;z)=(1-z)^{c-a-b}F(c-a,c-b;c;z)$.
* **17. Pfaff transformation.**
  $F(a,b;c;z)=(1-z)^{-a}F(a,c-b;c;z/(z-1))$.
* **18. Connection at one.** If $c-a-b\notin\mathbb Z$, then
  $$
  F(a,b;c;z)=
  \frac{\Gamma(c)\Gamma(c-a-b)}{\Gamma(c-a)\Gamma(c-b)}
  F(a,b;a+b-c+1;1-z)
  +\frac{\Gamma(c)\Gamma(a+b-c)}{\Gamma(a)\Gamma(b)}
  (1-z)^{c-a-b}F(c-a,c-b;c-a-b+1;1-z).
  $$
  Integral exponent differences require limiting logarithmic formulas.
* **19. Chu–Vandermonde summation.** For $n\geq0$,
  $F(-n,b;c;1)=(c-b)_n/(c)_n$.
* **20. Pfaff–Saalschütz summation.**
  ${}_3F_2(a,b,-n;c,1+a+b-c-n;1)
  =(c-a)_n(c-b)_n/[(c)_n(c-a-b)_n]$,
  with no vanishing denominator factors, or by a defined limit.
* **83. Contiguous relations and quadratic transformations.** Any three
  functions $F(a+k,b+l;c+m;z)$ with integer shifts satisfy a linear
  relation with coefficients rational in $a,b,c,z$ (Gauss), for example
  $(c-a)F(a-1,b;c;z)+(2a-c+(b-a)z)F(a,b;c;z)+a(z-1)F(a+1,b;c;z)=0$.
  A quadratic transformation exists exactly when two of the numbers
  $\pm(1-c)$, $\pm(a-b)$, $\pm(a+b-c)$ are equal or one of them equals
  $\frac12$ (Kummer, Goursat); for example
  $F(2a,2b;a+b+\frac12;z)=F(a,b;a+b+\frac12;4z(1-z))$ for $\Re z<\frac12$.
* **84. Gauss continued fraction.** The relations
  $F(a,b;c;z)-F(a+1,b;c+1;z)=k_1zF(a+1,b+1;c+2;z)$ and their iterates give
  $$
  \frac{F(a+1,b;c+1;z)}{F(a,b;c;z)}
  =\cfrac{1}{1+\cfrac{k_1z}{1+\cfrac{k_2z}{1+\cdots}}},\qquad
  k_{2j+1}=\frac{(a-c-j)(b+j)}{(c+2j)(c+2j+1)},\quad
  k_{2j}=\frac{(b-c-j)(a+j)}{(c+2j-1)(c+2j)}.
  $$
  For nonterminating parameters with all $k_j\ne0$, the fraction converges
  on $\mathbb C\setminus[1,\infty)$ to the meromorphic ratio, locally
  uniformly away from its poles.
* **21. Confluent equation and integral.** $M(a,b,z)$ solves
  $zy''+(b-z)y'-ay=0$ and, for $\Re b>\Re a>0$,
  equals $\Gamma(b)[\Gamma(a)\Gamma(b-a)]^{-1}
  \int_0^1e^{zt}t^{a-1}(1-t)^{b-a-1}dt$.
* **22. Kummer transformation.** $M(a,b,z)=e^zM(b-a,b,-z)$.
  The confluence limit $M(a,b,z)=\lim_{\beta\to\infty}F(a,\beta;b;z/\beta)$
  holds locally uniformly.
* **23. Tricomi solution.** For $\Re a>0$, $\Re z>0$,
  $U(a,b,z)=\Gamma(a)^{-1}\int_0^\infty
  e^{-zt}t^{a-1}(1+t)^{b-a-1}dt$.
  It solves the same equation and satisfies $U(a,b,x)\sim x^{-a}$ for $x\to+\infty$.
* **24. Whittaker reduction.**
  $W_{\kappa,\mu}(z)=e^{-z/2}z^{\mu+1/2}
  U(\mu-\kappa+1/2,1+2\mu,z)$ solves
  $y''+[-1/4+\kappa/z+(1/4-\mu^2)/z^2]y=0$.
* **81. Parabolic cylinder functions.** Weber's equation
  $y''=(z^2/4+a)y$ has entire solutions. The solution $U(a,z)$ is fixed by
  $U(a,z)\sim z^{-a-1/2}e^{-z^2/4}$ as $z\to\infty$ in
  $|\arg z|<3\pi/4$; for $\Re a>-\frac12$,
  $U(a,z)=\Gamma(a+\frac12)^{-1}e^{-z^2/4}
  \int_0^\infty t^{a-1/2}e^{-t^2/2-zt}dt$, and for $z>0$,
  $U(a,z)=2^{-1/4-a/2}e^{-z^2/4}U(\frac a2+\frac14,\frac12,\frac{z^2}2)$.
  The functions $U(a,\pm z)$, $U(-a,\pm iz)$ solve the equation, and
  $\mathcal W\{U(a,z),U(a,-z)\}=\sqrt{2\pi}/\Gamma(a+\frac12)$.
  Whittaker's $D_\nu(z)=U(-\nu-\frac12,z)$ satisfies
  $D_n(z)=2^{-n/2}e^{-z^2/4}H_n(z/\sqrt2)$ for integers $n\geq0$.

## Bessel, Airy, and Gaussian functions

* **25. Bessel series and equation.**
  $J_\nu(z)=\sum_{k\geq0}(-1)^k(z/2)^{2k+\nu}/[k!\Gamma(k+\nu+1)]$
  solves $z^2y''+zy'+(z^2-\nu^2)y=0$ on a chosen branch.
* **26. Second solution.** For noninteger $\nu$,
  $Y_\nu=(\cos\pi\nu\,J_\nu-J_{-\nu})/\sin\pi\nu$;
  integer orders are defined by limits. The outgoing and incoming
  Hankel solutions are $H_\nu^{(1,2)}=J_\nu\pm iY_\nu$.
* **27. Order recurrences.**
  $J_{\nu-1}+J_{\nu+1}=2\nu J_\nu/z$ and
  $J_{\nu-1}-J_{\nu+1}=2J_\nu'$. The same identities hold for $Y$.
* **28. Bessel Wronskian.**
  $J_\nu Y_\nu'-J_\nu'Y_\nu=2/(\pi z)$.
  This fixes the normalization of the independent solutions.
* **29. Modified functions.** The solutions
  $I_\nu(z)=i^{-\nu}J_\nu(iz)$ (consistent branches) and
  $K_\nu=\frac\pi2(I_{-\nu}-I_\nu)/\sin\pi\nu$ (limits at integer $\nu$)
  of $z^2y''+zy'-(z^2+\nu^2)y=0$ are positive on $(0,\infty)$
  for real $\nu>-1$, respectively real $\nu$, and
  $I_\nu K_\nu'-I_\nu'K_\nu=-1/z$.
* **30. Bessel generating function.**
  $e^{(z/2)(t-t^{-1})}=\sum_{n\in\mathbb Z}J_n(z)t^n$,
  with normal convergence on compact subsets of $0<|t|<\infty$.
  Hence Bessel's integral
  $J_n(z)=\pi^{-1}\int_0^\pi\cos(z\sin\theta-n\theta)d\theta$, $n\in\mathbb Z$.
* **86. Bessel addition and the Euclidean group.** For $\rho>0$, the
  translation $x\mapsto x+(a,0)$ of the plane acts in the irreducible
  unitary representation of $E(2)$ on $L^2(S^1)$ by multiplication by
  $e^{i\rho a\cos\theta}$; by entry 30 its matrix coefficients in the
  basis $e^{in\theta}$ are $i^{m-n}J_{m-n}(\rho a)$. The homomorphism
  property gives the addition theorem
  $J_n(x+y)=\sum_{k\in\mathbb Z}J_k(x)J_{n-k}(y)$; rotations and the
  full group give Graf's addition theorem in the same way (Miller,
  Vilenkin–Klimyk).
* **31. Poisson integral for Bessel functions.** If $\Re\nu>-1/2$,
  $J_\nu(z)=\frac{(z/2)^\nu}{\sqrt\pi\Gamma(\nu+1/2)}
  \int_{-1}^1e^{izt}(1-t^2)^{\nu-1/2}dt$.
* **32. Hankel transform.** For real $\nu>-1$,
  $\mathcal H_\nu f(s)=\int_0^\infty f(r)J_\nu(rs)r\,dr$
  extends to a unitary involution on $L^2((0,\infty),r\,dr)$.
  If $f(x)=f_0(|x|)$ is radial and integrable on $\mathbb R^d$, $d\geq2$,
  then $\int_{\mathbb R^d}f(x)e^{-ix\cdot\xi}dx
  =(2\pi)^{d/2}|\xi|^{1-d/2}\int_0^\infty f_0(r)J_{d/2-1}(r|\xi|)r^{d/2}dr$.
* **33. Fourier–Bessel expansion.** For $\nu>-1$, positive zeros
  $j_{\nu,k}$ are simple, and $J_\nu(j_{\nu,k}x)$ form a
  complete orthogonal system in $L^2((0,1),x\,dx)$, with squared
  norm $J_{\nu+1}(j_{\nu,k})^2/2$.
* **34. Oscillatory Bessel asymptotics.** For fixed real $\nu$ and
  $x\to+\infty$, $J_\nu(x)=\sqrt{2/(\pi x)}
  [\cos(x-\pi\nu/2-\pi/4)+O(x^{-1})]$; $Y_\nu$ has
  the corresponding sine expansion.
* **35. Modified large-argument asymptotics.** For fixed $\nu$,
  $I_\nu(x)\sim e^x/\sqrt{2\pi x}$ and
  $K_\nu(x)\sim\sqrt{\pi/(2x)}e^{-x}$ as $x\to+\infty$.
* **36. Airy representation.** The Airy equation is $y''=zy$.
  For real $x$, $\operatorname{Ai}(x)=\pi^{-1}\int_0^\infty
  \cos(t^3/3+xt)dt$, as an oscillatory integral.
* **37. Airy normalization and asymptotics.**
  $W(\operatorname{Ai},\operatorname{Bi})=1/\pi$ and, for positive large $x$,
  $\operatorname{Ai}(x)\sim x^{-1/4}e^{-2x^{3/2}/3}/(2\sqrt\pi)$,
  $\operatorname{Bi}(x)\sim x^{-1/4}e^{2x^{3/2}/3}/\sqrt\pi$,
  while on the negative axis
  $\operatorname{Ai}(-x)=\pi^{-1/2}x^{-1/4}
  [\sin(\tfrac23x^{3/2}+\tfrac\pi4)+O(x^{-3/2})]$.
* **38. Error function.**
  $\operatorname{erf}z=(2/\sqrt\pi)\int_0^ze^{-t^2}dt$ is entire;
  $\operatorname{erfc}x\sim e^{-x^2}/(\sqrt\pi x)$ as $x\to+\infty$.
  The Gaussian integral is $\int_{\mathbb R}e^{-x^2}dx=\sqrt\pi$.

## Classical polynomial families and spherical functions

* **39. Jacobi hypergeometric representation.**
  $P_n^{(\alpha,\beta)}(x)=\frac{(\alpha+1)_n}{n!}
  F(-n,n+\alpha+\beta+1;\alpha+1;(1-x)/2)$.
* **40. Jacobi orthogonality.** For $\alpha,\beta>-1$, these
  polynomials are orthogonal for $(1-x)^\alpha(1+x)^\beta dx$,
  with squared norm
  $\frac{2^{\alpha+\beta+1}\Gamma(n+\alpha+1)\Gamma(n+\beta+1)}
  {(2n+\alpha+\beta+1)n!\Gamma(n+\alpha+\beta+1)}$,
  interpreted continuously at removable parameter cases.
* **41. Jacobi Rodrigues formula.**
  $P_n^{(\alpha,\beta)}(x)=\frac{(-1)^n}{2^nn!}
  (1-x)^{-\alpha}(1+x)^{-\beta}
  \frac{d^n}{dx^n}[(1-x)^{n+\alpha}(1+x)^{n+\beta}]$.
* **42. Laguerre system.**
  $L_n^{(\alpha)}(x)=(\alpha+1)_nM(-n,\alpha+1,x)/n!$,
  $\sum_{n\geq0}L_n^{(\alpha)}(x)t^n
  =(1-t)^{-\alpha-1}e^{-xt/(1-t)}$, $|t|<1$.
  For $\alpha>-1$, its squared norm for $x^\alpha e^{-x}dx$
  is $\Gamma(n+\alpha+1)/n!$.
* **43. Hermite system.** The physicists' convention is
  $H_n(x)=(-1)^ne^{x^2}(d/dx)^ne^{-x^2}$,
  with $\sum_{n\geq0}H_n(x)t^n/n!=e^{2xt-t^2}$ and orthogonality
  $\int H_nH_me^{-x^2}dx=\sqrt\pi\,2^nn!\delta_{nm}$.
  The Hermite functions $h_n=H_ne^{-x^2/2}$ form a complete orthogonal
  basis of $L^2(\mathbb R)$, satisfy $-h_n''+x^2h_n=(2n+1)h_n$, and
  $\int h_n(x)e^{-ix\xi}dx=\sqrt{2\pi}(-i)^nh_n(\xi)$.
* **44. Gegenbauer generating function.**
  $(1-2xt+t^2)^{-\lambda}=\sum C_n^\lambda(x)t^n$, $|t|<1$.
  For $\lambda>0$ the weight is $(1-x^2)^{\lambda-1/2}$;
  $\lambda=1/2$ gives Legendre polynomials.
* **45. Spherical harmonics and addition theorem.** On $S^{d-1}$,
  $d\geq3$, restrictions of harmonic homogeneous polynomials of degree
  $\ell$ form the eigenspace $\mathcal H_\ell$ of the Laplace–Beltrami
  operator for $-\ell(\ell+d-2)$, of dimension
  $\binom{\ell+d-1}{d-1}-\binom{\ell+d-3}{d-1}$, and
  $L^2(S^{d-1})=\bigoplus_{\ell\geq0}\mathcal H_\ell$. For an
  orthonormal basis $(Y_j)$ of $\mathcal H_\ell$ and $\lambda=(d-2)/2$,
  $\sum_jY_j(\xi)\overline{Y_j(\eta)}
  =\frac{\dim\mathcal H_\ell}{|S^{d-1}|}\,
  \frac{C_\ell^\lambda(\xi\cdot\eta)}{C_\ell^\lambda(1)}$;
  for $d=3$ this is $(2\ell+1)P_\ell(\xi\cdot\eta)/(4\pi)$.
* **79. Legendre functions.** The associated Legendre equation
  $(1-z^2)y''-2zy'+[\nu(\nu+1)-\mu^2/(1-z^2)]y=0$ has regular singular
  points $\pm1,\infty$. Write $\mathbf F(a,b;c;z)=F(a,b;c;z)/\Gamma(c)$,
  entire in $c$. On $-1<x<1$ the Ferrers function
  $\mathsf P_\nu^\mu(x)=\bigl(\frac{1+x}{1-x}\bigr)^{\mu/2}
  \mathbf F(\nu+1,-\nu;1-\mu;\frac{1-x}2)$ solves it; on
  $\mathbb C\setminus(-\infty,1]$ the Legendre function $P_\nu^\mu(z)$ has
  the same formula with $\bigl(\frac{z+1}{z-1}\bigr)^{\mu/2}$. For
  integers $m\geq0$,
  $\mathsf P_\nu^m(x)=(-1)^m(1-x^2)^{m/2}d^m\mathsf P_\nu(x)/dx^m$, and
  $\mathsf P_\nu=\mathsf P_{-\nu-1}$. Laplace's integral is
  $P_\nu(z)=\pi^{-1}\int_0^\pi(z+\sqrt{z^2-1}\cos\theta)^\nu d\theta$,
  $\Re z>0$.
* **80. Legendre eigenvalue problem and second kind.** On $(-1,1)$,
  $\mathsf P_\nu$ is, up to a factor, the solution of the Legendre equation
  ($\mu=0$) bounded at $1$; it is bounded at $-1$ exactly when
  $\nu\in\mathbb Z$, and then it is the Legendre polynomial $P_n$,
  $n=\max(\nu,-\nu-1)$. For integers $0\leq m\leq\ell,k$,
  $\int_{-1}^1\mathsf P_\ell^m\mathsf P_k^mdx
  =\frac2{2\ell+1}\frac{(\ell+m)!}{(\ell-m)!}\delta_{\ell k}$, and
  $\mathsf P_\ell^{|m|}(\cos\theta)e^{im\phi}$, $|m|\leq\ell$, span
  $\mathcal H_\ell$ on $S^2$ (entry 45). For $n\geq0$ and
  $z\notin[-1,1]$, Neumann's integral
  $Q_n(z)=\frac12\int_{-1}^1P_n(t)(z-t)^{-1}dt$ defines the second
  solution recessive at infinity,
  $Q_n(z)\sim n!\sqrt\pi\,(2z)^{-n-1}/\Gamma(n+\frac32)$.

## Elliptic integrals, elliptic functions, and theta functions

For $0<k<1$, let $k'=\sqrt{1-k^2}$ and
$K(k)=\int_0^{\pi/2}(1-k^2\sin^2t)^{-1/2}dt$,
$E(k)=\int_0^{\pi/2}(1-k^2\sin^2t)^{1/2}dt$.
A prime on $K,E$ below means complementary modulus, not differentiation.

* **46. Elliptic hypergeometric formulas.**
  $K(k)=\frac\pi2F(1/2,1/2;1;k^2)$ and
  $E(k)=\frac\pi2F(-1/2,1/2;1;k^2)$.
* **47. Elliptic derivative relations.**
  $dE/dk=(E-K)/k$ and
  $dK/dk=E/[k(1-k^2)]-K/k$.
* **48. Legendre relation.**
  $K(k)E(k')+E(k)K(k')-K(k)K(k')=\pi/2$.
  See DLMF §19.7.
* **49. Arithmetic–geometric mean.** Iteration
  $a_{n+1}=(a_n+b_n)/2$, $b_{n+1}=\sqrt{a_nb_n}$ for
  positive data has a common limit, and
  $K(k)=\pi/[2\operatorname{AGM}(1,k')]$.
  The common limit $\operatorname{AGM}(a,b)$ lies between the initial
  geometric and arithmetic means, is invariant under one iteration, and
  satisfies Gauss's identity $\operatorname{AGM}(a,b)=\frac\pi2\bigl(\int_0^{\pi/2}
  d\theta/\sqrt{a^2\cos^2\theta+b^2\sin^2\theta}\bigr)^{-1}$.
* **85. Carlson symmetric integrals.** For $x,y,z\geq0$, at most one zero,
  $R_F(x,y,z)=\frac12\int_0^\infty[(t+x)(t+y)(t+z)]^{-1/2}dt$ and, for
  $z>0$, $R_D(x,y,z)=\frac32\int_0^\infty(t+x)^{-1/2}(t+y)^{-1/2}
  (t+z)^{-3/2}dt$. Then $K(k)=R_F(0,k'^2,1)$ and
  $E(k)=R_F(0,k'^2,1)-\frac13k^2R_D(0,k'^2,1)$. $R_F$ is symmetric,
  homogeneous of degree $-\frac12$, $R_F(x,x,x)=x^{-1/2}$, and satisfies
  the duplication formula $R_F(x,y,z)=R_F(\frac{x+\lambda}4,
  \frac{y+\lambda}4,\frac{z+\lambda}4)$ with
  $\lambda=\sqrt{xy}+\sqrt{yz}+\sqrt{zx}$, whose iteration converges to
  equal arguments.
* **50. Jacobi elliptic identities.** Inverting
  $u=\int_0^\varphi(1-k^2\sin^2t)^{-1/2}dt$ defines
  $\operatorname{sn}u=\sin\varphi$, $\operatorname{cn}u=\cos\varphi$,
  $\operatorname{dn}u=d\varphi/du=(1-k^2\sin^2\varphi)^{1/2}>0$
  for real $u$ and $0<k<1$; these extend
  to meromorphic elliptic functions, $\operatorname{sn}$ with periods
  $4K$, $2iK'$, with
  $\operatorname{sn}^2+\operatorname{cn}^2=1$,
  $\operatorname{dn}^2+k^2\operatorname{sn}^2=1$ on $\mathbb C$ and derivatives
  $\operatorname{sn}'=\operatorname{cn}\operatorname{dn}$,
  $\operatorname{cn}'=-\operatorname{sn}\operatorname{dn}$,
  $\operatorname{dn}'=-k^2\operatorname{sn}\operatorname{cn}$.
* **51. Weierstrass equation.** For a lattice $\Lambda$,
  $\wp(z)=z^{-2}+\sum_{\omega\ne0}[(z-\omega)^{-2}-\omega^{-2}]$
  is elliptic and satisfies $(\wp')^2=4\wp^3-g_2\wp-g_3$,
  with $g_2=60\sum\omega^{-4}$, $g_3=140\sum\omega^{-6}$.
  It obeys the addition theorem
  $\wp(z+w)=\frac14\bigl(\frac{\wp'(z)-\wp'(w)}{\wp(z)-\wp(w)}\bigr)^2
  -\wp(z)-\wp(w)$ for $z,w,z\pm w\notin\Lambda$.
* **52. Liouville theorems.** A holomorphic elliptic function is
  constant. For a nonconstant elliptic function on a period
  parallelogram, the residues sum to zero, the numbers of zeros and of
  poles agree (with multiplicity, the order being at least two), and
  the sum of zeros minus the sum of poles lies in $\Lambda$. The
  elliptic functions for $\Lambda$ form the field
  $\mathbb C(\wp,\wp')$.
* **53. Theta series.** For $|q|<1$,
  $\vartheta_3(z,q)=\sum_{n\in\mathbb Z}q^{n^2}e^{2inz}$
  converges normally in $z$. With $q=e^{\pi i\tau}$ it has
  $\vartheta_3(z+\pi,q)=\vartheta_3(z,q)$ and
  $\vartheta_3(z+\pi\tau,q)=q^{-1}e^{-2iz}\vartheta_3(z,q)$.
* **54. Jacobi imaginary transformation.** Poisson summation gives
  $\vartheta_3(0,e^{-\pi t})=t^{-1/2}\vartheta_3(0,e^{-\pi/t})$,
  $t>0$, with corresponding shifted theta transformations.
* **55. Theta–elliptic relation.** For $q=e^{-\pi K(k')/K(k)}$,
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

* **56. q-binomial theorem.**
  $\sum_{n\geq0}(a;q)_nz^n/(q;q)_n
  =(az;q)_\infty/(z;q)_\infty$, $|z|<1$.
* **57. q-Gauss sum.**
  ${}_2\phi_1(a,b;c;q,c/(ab))
  =(c/a,c/b;q)_\infty/(c,c/(ab);q)_\infty$ for $|c/(ab)|<1$.
  See DLMF §17.6.
* **58. Euler q-exponentials.**
  $1/(z;q)_\infty=\sum z^n/(q;q)_n$ for $|z|<1$, and
  $(z;q)_\infty=\sum(-1)^nq^{n(n-1)/2}z^n/(q;q)_n$ for all $z$.
* **59. Jacobi triple product.**
  $\sum_{n\in\mathbb Z}q^{n(n-1)/2}z^n
  =(q,-z,-q/z;q)_\infty$, $z\ne0$.
* **60. Rogers–Ramanujan identities.**
  $\sum_{n\geq0}q^{n^2}/(q;q)_n=1/(q,q^4;q^5)_\infty$ and
  $\sum_{n\geq0}q^{n^2+n}/(q;q)_n=1/(q^2,q^3;q^5)_\infty$.
  Equivalently, partitions of $n$ into parts differing by at least two
  are as many as partitions into parts $\equiv\pm1\pmod5$; with all
  parts at least two as well, as many as partitions into parts
  $\equiv\pm2\pmod5$.
* **61. Ramanujan bilateral sum.**
  $$
  \sum_{n\in\mathbb Z}\frac{(a;q)_n}{(b;q)_n}z^n
  =\frac{(q,b/a,az,q/(az);q)_\infty}
  {(b,q/a,z,b/(az);q)_\infty},\qquad |b/a|<|z|<1.
  $$
  Denominator and bilateral parameters must be nonsingular;
  see DLMF §17.8.
* **62. q-gamma limit.** For $0<q<1$,
  $\Gamma_q(z)=(1-q)^{1-z}(q;q)_\infty/(q^z;q)_\infty$
  satisfies $\Gamma_q(z+1)=(1-q^z)\Gamma_q(z)/(1-q)$ and
  tends to $\Gamma(z)$ locally uniformly away from its poles as $q\uparrow1$.
* **63. q-Chu–Vandermonde sum.**
  ${}_2\phi_1(q^{-n},b;c;q,cq^n/b)=(c/b;q)_n/(c;q)_n$.
* **64. Askey–Wilson orthogonality.** For real $a,b,c,d$ of
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

* **65. Laplace analyticity and uniqueness.**
  $\mathcal Lf(s)=\int_0^\infty e^{-st}f(t)dt$ is holomorphic
  in its half-plane of absolute convergence. Equality of transforms
  there determines locally integrable functions of exponential order almost everywhere.
* **66. Bromwich inversion.** For a locally piecewise $C^1$
  function of exponential order,
  $\frac12(f(t+)+f(t-))=(2\pi i)^{-1}
  \lim_{T\to\infty}\int_{c-iT}^{c+iT}e^{st}\mathcal Lf(s)ds$
  at $t>0$, with $c$ in the absolute-convergence half-plane.
* **67. Laplace convolution and derivatives.**
  $\mathcal L(f*g)=\mathcal Lf\,\mathcal Lg$ and
  $\mathcal L(f')=s\mathcal Lf-f(0+)$ under the corresponding
  integrability and absolute-continuity hypotheses.
* **68. Mellin inversion.** For
  $\mathcal Mf(s)=\int_0^\infty f(x)x^{s-1}dx$, analyticity
  holds in its fundamental strip, and
  $f(x)=(2\pi i)^{-1}\int_{c-i\infty}^{c+i\infty}
  \mathcal Mf(s)x^{-s}ds$ under Fourier inversion hypotheses on the logarithmic variable.
* **69. Mellin Plancherel.** On $L^2(dx/x)$,
  $\int|f(x)|^2dx/x=(2\pi)^{-1}\int|\mathcal Mf(it)|^2dt$,
  by the $L^2$ extension of the transform. Mellin convolution becomes multiplication.
* **70. Barnes integrals.** For $|\arg(-z)|<\pi$ and $a,b$ not
  nonpositive integers,
  $$
  \frac{\Gamma(a)\Gamma(b)}{\Gamma(c)}F(a,b;c;z)=\frac1{2\pi i}
  \int_{-i\infty}^{i\infty}\frac{\Gamma(a+s)\Gamma(b+s)\Gamma(-s)}
  {\Gamma(c+s)}(-z)^sds,
  $$
  the contour separating the poles of $\Gamma(a+s)\Gamma(b+s)$
  from those of $\Gamma(-s)$; this continues $F$ to
  $\mathbb C\setminus[1,\infty)$. The case $b=c$ is the Mellin pair
  $\int_0^\infty x^{s-1}(1+x)^{-a}dx=\Gamma(s)\Gamma(a-s)/\Gamma(a)$,
  $0<\Re s<\Re a$.
* **71. Bernstein–Widder theorem.** A smooth $f:(0,\infty)\to\mathbb R$
  is completely monotone, $(-1)^nf^{(n)}\geq0$, exactly when
  $f(x)=\int_{[0,\infty)}e^{-xt}d\mu(t)$ for a unique positive
  measure with finite transform for every $x>0$.
* **72. Bernstein-function representation.** A nonnegative smooth
  function with completely monotone derivative has the unique form
  $f(x)=a+bx+\int_{(0,\infty)}(1-e^{-xt})d\nu(t)$,
  $a,b\geq0$, $\int(1\wedge t)d\nu<\infty$.
* **73. Complete Bernstein and Stieltjes functions.** A Bernstein
  function has completely monotone Lévy density exactly when $f(x)/x$
  is Stieltjes, that is,
  $f(x)/x=a/x+b+\int_{(0,\infty)}(x+t)^{-1}d\sigma(t)$,
  with $a,b\geq0$, $\sigma\geq0$, and $\int(1+t)^{-1}d\sigma<\infty$.

## Fractional integrals and Mittag–Leffler functions

For $\alpha>0$ define
$I^\alpha f(t)=\Gamma(\alpha)^{-1}\int_0^t(t-s)^{\alpha-1}f(s)ds$.
For $m-1<\alpha<m$, the **Riemann–Liouville derivative** is
$D^\alpha u=(d/dt)^mI^{m-\alpha}u$ and the **Caputo derivative** is
$D_C^\alpha u=I^{m-\alpha}u^{(m)}$; integer orders use ordinary derivatives.
For $u\in C^m$ they differ by the polynomial-type terms
$\sum_{j<m}u^{(j)}(0)t^{j-\alpha}/\Gamma(j+1-\alpha)$.

* **74. Fractional semigroup.** $I^\alpha I^\beta=I^{\alpha+\beta}$
  for locally integrable functions and positive orders, almost everywhere.
  The Riemann–Liouville derivative is a left inverse:
  $D^\alpha I^\alpha f=f$ almost everywhere for locally integrable $f$.
* **75. Caputo Laplace formula.** For functions with the stated
  initial derivatives and sufficient exponential integrability,
  $\mathcal L(D_C^\alpha u)=s^\alpha\mathcal Lu
  -\sum_{j=0}^{m-1}s^{\alpha-1-j}u^{(j)}(0+)$.
* **76. Mittag–Leffler entire functions.** For $\alpha>0$,
  $E_{\alpha,\beta}(z)=\sum_{n\geq0}z^n/\Gamma(\alpha n+\beta)$
  is entire of order $1/\alpha$; $E_{1,1}(z)=e^z$.
* **77. Mittag–Leffler Laplace transform.** For $\alpha,\beta>0$
  and $\Re s>|\lambda|^{1/\alpha}$,
  $\int_0^\infty e^{-st}t^{\beta-1}E_{\alpha,\beta}(\lambda t^\alpha)dt
  =s^{\alpha-\beta}/(s^\alpha-\lambda)$.
* **78. Fractional relaxation and complete monotonicity.** For
  $0<\alpha\leq1$, $E_{\alpha,1}(-x)$ and
  $E_{\alpha,1}(-t^\alpha)$ are completely monotone on the positive axis.
  The solution of $D_C^\alpha u=\lambda u$, $u(0)=1$, is
  $E_{\alpha,1}(\lambda t^\alpha)$.

## Reference guide

Andrews–Askey–Roy, Whittaker–Watson, Bateman, Lebedev, Temme,
Beals–Wong, and the NIST reference share the classical definitions,
equations, integrals, and transformations. Gasper–Rahman and Ismail
develop the q-series and orthogonal-polynomial continuation. Carlson
supplies the symmetric integrals of entry 85, and the elliptic-function
books of Section 49 (Takebe, *Elliptic Integrals and Elliptic Functions*;
Roy, *Elliptic and Modular Functions from Gauss to Dedekind to Hecke*;
Weil, *Elliptic Functions according to Eisenstein and Kronecker*) give
complementary analytic, historical, and Eisenstein-series viewpoints;
Miller and Vilenkin–Klimyk give the group-theoretic viewpoint of entry 86.
Widder, Titchmarsh, Sneddon, and Schilling–Song–Vondraček supply
the transform and positivity framework; the fractional-calculus and
Mittag–Leffler references explain the last section. The catalogue avoids
reproducing isolated table entries without their analytic context.

Local full-text sources consulted:

* [Andrews–Askey–Roy, *Special Functions*](References/AndrewsAskeyRoy1999SpecialFunctions-CambridgeEMA71.pdf).
* [Beals–Wong, *Special Functions and Orthogonal Polynomials* (2016), the enlarged second edition of *Special Functions: A Graduate Text*](References/BealsWong2015SpecialFunctionsOrthogonalPolynomials2ndEd-CambridgeStudiesAM153.pdf).
* [Temme, *Special Functions*](References/Temme1996SpecialFunctionsIntroductionClassicalFunctionsMathematicalPhysics-Wiley.pdf).
* [Gasper–Rahman, *Basic Hypergeometric Series*, second edition](References/GasperRahman2004BasicHypergeometricSeries2ndEd-CambridgeEMA96.pdf).
* [Viola, *An Introduction to Special Functions*](References/Viola2016IntroductionToSpecialFunctions-SpringerUnitext.pdf).
* [Schilling–Song–Vondraček, *Bernstein Functions*](References/SchillingSongVondraček2009BernsteinFunctionsTheoryApplications-DeGruyterStudMath37.pdf).
* [Gorenflo–Kilbas–Mainardi–Rogosin, *Mittag-Leffler Functions*, first edition](References/GorenfloKilbasMainardiRogosin2014MittagLefflerFunctionsRelatedTopicsApplications-SpringerSMM.pdf).

The linked DLMF sections were used to check the stated Bessel integral,
elliptic connection, and q-summation normalizations alongside these texts.
