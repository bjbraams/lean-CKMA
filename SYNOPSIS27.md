# Synopsis: Fourier analysis and real-variable harmonic analysis

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-27);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring material from Section 27 of
[CKMA-bib.md](CKMA-bib.md#ckma-27): Fourier
transforms and series, maximal and singular integrals, multipliers, weighted
estimates, Hardy spaces, oscillatory integrals, and the restriction and
Kakeya problems. The last topics belong
to the working core of the advanced monographs, rather than to every first
course. Abstract groups and time–frequency expansions have separate synopses.

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

## The Fourier transform and translation-invariant operators

The extension to tempered distributions and the Paley–Wiener–Schwartz
theorem are stated in SYNOPSIS16, items 53 and 59, and the $L^2$
Paley–Wiener theorem in SYNOPSIS41, item 21.

* **1. Riemann–Lebesgue theorem.** The Fourier transform maps
  $L^1(\mathbb R^d)$ continuously into $C_0(\mathbb R^d)$, with
  $\|\widehat f\|_\infty\leq\|f\|_1$.
* **2. Schwartz isomorphism and inversion.** Fourier transformation is
  a continuous automorphism of the Schwartz space $\mathcal S$, and
  $f(x)=\int\widehat f(\xi)e^{2\pi i x\cdot\xi}\,d\xi$ there.
  If $f,\widehat f\in L^1$, the same formula holds almost everywhere
  and gives the continuous representative of $f$.
* **3. Plancherel theorem.** Fourier transformation extends uniquely to
  a unitary map on $L^2$; $\langle\widehat f,\widehat g\rangle
  =\langle f,g\rangle$. Its inverse has the opposite exponential sign.
  It agrees with the distributional extension.
* **4. Hausdorff–Young inequality.** For $1\leq p\leq2$ and
  $p'=p/(p-1)$, $\|\widehat f\|_{p'}\leq\|f\|_p$.
  In general no corresponding bounded map $L^p\to L^{p'}$ exists for
  $p>2$ on Euclidean space. For $1<p\leq2$ the sharp constant on
  $\mathbb R^d$ is $C_p^d$ with $C_p=(p^{1/p}/p'^{1/p'})^{1/2}$, attained by
  Gaussians (Babenko, Beckner).
* **5. Covariance and differentiation.** Translation by $a$ multiplies
  $\widehat f$ by $e^{-2\pi i a\cdot\xi}$, modulation translates it,
  and $\widehat{\partial_j f}=2\pi i\xi_j\widehat f$.
  For invertible $A$, $\widehat{f(A\cdot)}(\xi)
  =|\det A|^{-1}\widehat f(A^{-T}\xi)$.
* **6. Convolution theorem and Young inequality.** In the usual
  integrability ranges, $\widehat{f*g}=\widehat f\widehat g$ and
  $\|f*g\|_r\leq\|f\|_p\|g\|_q$ when
  $1+1/r=1/p+1/q$, $1\leq p,q,r\leq\infty$.
* **7. Approximate identities.** If $\phi\in L^1$, $\int\phi=1$,
  and $\phi_t(x)=t^{-d}\phi(x/t)$, then $f*\phi_t\to f$ in
  $L^p$ as $t\to0$ for $1\leq p<\infty$. Convergence is uniform for uniformly
  continuous bounded $f$. Suitable radial decreasing majorants also
  give convergence at every Lebesgue point.
* **9. Gaussian transform and semigroups.**
  $\widehat{e^{-\pi a|x|^2}}=a^{-d/2}e^{-\pi|\xi|^2/a}$ for
  $a>0$. The heat kernel has multiplier $e^{-4\pi^2t|\xi|^2}$;
  the Poisson kernel has multiplier $e^{-2\pi t|\xi|}$.
  Both form positive convolution semigroups of mass one.
* **10. Poisson summation.** For $f\in\mathcal S(\mathbb R^d)$,
  $\sum_{k\in\mathbb Z^d}f(k)=\sum_{k\in\mathbb Z^d}\widehat f(k)$,
  with absolute convergence. Translated and lattice versions follow by
  covariance and change of variables. The equivalent identity for Dirac
  combs, $\widehat{\sum_k\delta_k}=\sum_k\delta_k$, holds in $\mathcal S'$.
* **11. Translation-invariant $L^2$ operators.** Every bounded operator
  on $L^2(\mathbb R^d)$ commuting with translations is
  $T_m f=(m\widehat f)^\vee$ for a unique $m\in L^\infty$;
  $\|T_m\|_{2\to2}=\|m\|_\infty$.
* **12. Translation-invariant $L^1$ operators.** Every bounded operator
  on $L^1(\mathbb R^d)$ commuting with translations is convolution
  with a finite complex Borel measure; its norm is the measure's total
  variation. Such convolution is bounded on every $L^p$.
* **13. Heisenberg uncertainty.** For $\|f\|_2=1$ with finite
  second moments, $\|x_jf\|_2\|\xi_j\widehat f\|_2\geq1/(4\pi)$.
  Translations and modulations give the centered version, with Gaussian
  equality cases.

## Fourier series, summation, and convergence

Write $\widehat f(k)=\int_{\mathbb T^d}f(x)e^{-2\pi i k\cdot x}dx$.
On $\mathbb T$, $S_Nf=\sum_{|k|\leq N}\widehat f(k)e^{2\pi ikx}$.

* **15. Completeness and Parseval.** The characters
  $e^{2\pi ik\cdot x}$ form an orthonormal basis of $L^2(\mathbb T^d)$.
  Thus Fourier coefficients identify that space unitarily with
  $\ell^2(\mathbb Z^d)$.
* **16. Uniqueness.** An $L^1$ function whose Fourier coefficients
  vanish is zero almost everywhere. More generally finite measures on
  the torus are determined by their Fourier coefficients.
* **17. Fejér summation.** The Cesàro means
  $\sigma_Nf=(N+1)^{-1}\sum_{n=0}^NS_nf$ converge in $L^p$ for
  $1\leq p<\infty$, uniformly for continuous $f$, and to $f(x)$ at
  every Lebesgue point. Product Fejér kernels give the analogous
  multidimensional assertions.
* **18. Abel summation.** Poisson means
  $\sum_k r^{|k|}\widehat f(k)e^{2\pi ikx}$ on the circle converge
  in $L^p$, $p<\infty$, and at Lebesgue points as $r\uparrow1$.
  They give the harmonic extension with the prescribed boundary data.
* **19. Smoothness and coefficient decay.** Integrable derivatives give
  $\widehat{\partial^\alpha f}(k)=(2\pi ik)^\alpha\widehat f(k)$.
  Consequently sufficiently many integrable derivatives imply absolute
  and uniform convergence of the Fourier series; smooth functions have
  rapidly decreasing coefficients.
* **20. Dirichlet–Jordan theorem.** If $f$ has bounded variation on the
  circle, then $S_Nf(x)\to\tfrac12(f(x+)+f(x-))$ at every point.
* **21. Norm convergence of ordinary sums.** On $\mathbb T$,
  $S_Nf\to f$ in $L^p$ for $1<p<\infty$, with uniformly bounded
  partial-sum operators. The uniform operator bound fails on $L^1$
  and on $C(\mathbb T)$.
* **22. Carleson–Hunt theorem.** For $1<p<\infty$,
  $\|\sup_N|S_Nf|\|_p\leq C_p\|f\|_p$; in particular ordinary
  Fourier series converge almost everywhere for $f\in L^p$.
* **23. Divergence at the integrable endpoint.** There is an
  $f\in L^1(\mathbb T)$ whose ordinary Fourier series diverges
  everywhere (Kolmogorov). There are also continuous functions whose
  Fourier series diverge at a given point (du Bois-Reymond).
* **24. Wiener's inversion theorem.** If
  $\sum_k|\widehat f(k)|<\infty$ and $f$ has no zeros on
  $\mathbb T^d$, then $1/f$ also has absolutely summable Fourier
  coefficients.
* **25. Lacunary series.** If positive integers satisfy
  $n_{j+1}/n_j\geq q>1$, then for every $0<p<\infty$,
  $\|\sum_j a_je^{2\pi in_jx}\|_p\asymp_{p,q}
  (\sum_j|a_j|^2)^{1/2}$ for finite sums. This is the basic
  square-function behavior of lacunary frequencies.

## Maximal functions and fractional integration

The **Hardy–Littlewood maximal function** is
$Mf(x)=\sup_{Q\ni x}|Q|^{-1}\int_Q|f|$, over axis-parallel cubes.

* **26. Weak and strong maximal inequalities.**
  $|\{Mf>\lambda\}|\leq C_d\|f\|_1/\lambda$ and
  $\|Mf\|_p\leq C_{d,p}\|f\|_p$ for $1<p\leq\infty$.
* **27. Lebesgue differentiation.** A locally integrable function equals
  the limit of its averages over shrinking cubes almost everywhere;
  almost every point is a Lebesgue point.
* **28. Calderón–Zygmund decomposition.** For $f\in L^1$ and
  $\lambda>0$, there are disjoint dyadic cubes $Q_j$ and $f=g+\sum b_j$
  with $\|g\|_\infty\leq C_d\lambda$, $\|g\|_1\leq C\|f\|_1$,
  $\operatorname{supp}b_j\subset Q_j$, $\int b_j=0$,
  $\sum\|b_j\|_1\leq C\|f\|_1$, and
  $\sum|Q_j|\leq\|f\|_1/\lambda$.
* **29. Vector-valued maximal inequality.** For $1<p,q<\infty$,
  $\|(\sum_j|Mf_j|^q)^{1/q}\|_p
  \leq C\|(\sum_j|f_j|^q)^{1/q}\|_p$.
* **30. Hardy–Littlewood–Sobolev theorem.** For $0<\alpha<d$,
  the Riesz potential $I_\alpha f=c_{d,\alpha}|x|^{\alpha-d}*f$
  maps $L^p$ to $L^q$ if $1<p<d/\alpha$ and
  $1/q=1/p-\alpha/d$. It maps $L^1$ to weak $L^{d/(d-\alpha)}$.
* **31. Fractional maximal inequality.**
  $M_\alpha f(x)=\sup_{Q\ni x}|Q|^{\alpha/d-1}\int_Q|f|$
  has the same strong and weak exponent ranges as $I_\alpha$.
* **32. Nontangential convergence.** For $f\in L^p$, $1\leq p<\infty$,
  its Poisson extension tends to $f$ almost everywhere inside any fixed
  nontangential cone. The nontangential maximal function is bounded by
  $C Mf$, giving strong $L^p$ control for $p>1$ and weak control for $p=1$.

## Singular integrals and Fourier multipliers

A **standard Calderón–Zygmund operator** is $L^2$ bounded and represented
off the support of $f$ by a kernel $K(x,y)$ with size
$|K(x,y)|\leq C|x-y|^{-d}$ and Hölder regularity of some order
$0<\delta\leq1$ in each variable away from the diagonal.

* **33. Calderón–Zygmund theorem.** Such an operator is weak type
  $(1,1)$ and bounded on $L^p$ for $1<p<\infty$.
* **34. Maximal truncations.** The maximal truncated operator
  $T_*f=\sup_{\varepsilon>0}|\int_{|x-y|>\varepsilon}K(x,y)f(y)dy|$
  is weak type $(1,1)$ and bounded on $L^p$, $1<p<\infty$.
  If the truncations converge almost everywhere on smooth compactly
  supported functions, they consequently converge almost everywhere for
  $f\in L^p$, $1\leq p<\infty$. The usual cancellative homogeneous
  convolution kernels satisfy this additional hypothesis.
* **35. Hilbert transform.**
  $Hf(x)=\operatorname{pv}\pi^{-1}\int f(y)/(x-y)dy$ has multiplier
  $-i\operatorname{sgn}\xi$. It is bounded on $L^p$, $1<p<\infty$,
  weak type $(1,1)$, and satisfies $H^2=-I$ on $L^2(\mathbb R)$.
* **36. Riesz transforms.** The multipliers
  $-i\xi_j/|\xi|$ define operators $R_j$ bounded on $L^p$,
  $1<p<\infty$, and weak type $(1,1)$.
  On $L^2$, $\sum_jR_j^2=-I$.
* **37. Homogeneous convolution kernels.** If
  $\Omega\in C^1(S^{d-1})$ and $\int_{S^{d-1}}\Omega=0$, then
  $\operatorname{pv}\Omega(x/|x|)|x|^{-d}*f$ is a bounded
  Calderón–Zygmund singular integral. Cancellation is essential.
* **38. Mihlin multiplier theorem.** If a bounded $m$ is smooth off
  zero and $|\partial^\alpha m(\xi)|\leq C_\alpha|\xi|^{-|\alpha|}$
  for $|\alpha|\leq\lfloor d/2\rfloor+1$, then $T_m$ is bounded
  on every $L^p$, $1<p<\infty$.
* **39. Hörmander multiplier theorem.** If a smooth annular cutoff
  $\eta$, supported in $1/2<|\xi|<2$ and equal to one on
  $3/4\leq|\xi|\leq3/2$, gives
  $\sup_{t>0}\|\eta(\cdot)m(t\cdot)\|_{H^s}<\infty$
  for some $s>d/2$, then $m$ is an $L^p$ multiplier for all
  $1<p<\infty$.
* **40. Marcinkiewicz multiplier theorem.** A bounded symbol smooth
  off the coordinate hyperplanes is an $L^p$ multiplier if
  $\sup_\xi|\xi_1^{\alpha_1}\cdots\xi_d^{\alpha_d}
  \partial^\alpha m(\xi)|<\infty$ for all $\alpha_j\in\{0,1\}$.
  The conclusion holds for $1<p<\infty$.
* **41. Cotlar–Stein almost orthogonality.** If bounded operators $T_j$
  on a Hilbert space satisfy
  $\sup_j\sum_k\|T_j^*T_k\|^{1/2}\leq A$ and
  $\sup_j\sum_k\|T_jT_k^*\|^{1/2}\leq A$, then every finite sum
  satisfies $\|\sum_jT_j\|\leq A$, and $\sum_jT_j$ converges strongly.
* **42. The $T(1)$ theorem.** A standard singular-integral kernel defines
  an $L^2$ bounded operator precisely when its distributional operator
  satisfies the weak boundedness property and $T1,T^*1\in\mathrm{BMO}$
  (the space of bounded mean oscillation; see 49).
  Weak boundedness means uniform bounds $|\langle T\phi_Q,\psi_Q\rangle|
  \leq C|Q|$ for smooth normalized bumps on each cube.
* **43. Transference to the torus.** If $m$ is a continuous Euclidean
  $L^p$ multiplier, $1\leq p<\infty$, its restriction to
  $\mathbb Z^d$ is a torus multiplier with no larger norm.
* **69. Cauchy integral on Lipschitz curves.** Let $A:\mathbb R\to\mathbb R$
  be Lipschitz and $z(x)=x+iA(x)$. The Cauchy integral
  $C_Af(x)=\operatorname{pv}\frac1{\pi i}\int\frac{f(y)z'(y)}{z(y)-z(x)}dy$
  is bounded on $L^p(\mathbb R)$, $1<p<\infty$ (Calderón for small
  $\|A'\|_\infty$; Coifman–McIntosh–Meyer in general). So are the Calderón
  commutators $\operatorname{pv}\int(\frac{A(x)-A(y)}{x-y})^k
  \frac{f(y)}{x-y}dy$, with norms at most a polynomial in $k$ times
  $C^k\|A'\|_\infty^k$.
  These are the model applications of the $T(1)$ theorem and its accretive
  $T(b)$ variant, and they give the $L^2$ layer-potential theory on
  Lipschitz domains (SYNOPSIS25, item 41).

## Weights and endpoint spaces

For $1<p<\infty$, a positive locally integrable **$A_p$ weight** satisfies
$$
[w]_{A_p}=\sup_Q\left(\frac1{|Q|}\int_Qw\right)
 \left(\frac1{|Q|}\int_Qw^{-1/(p-1)}\right)^{p-1}<\infty.
$$
For $A_1$ use $Mw\leq Cw$ almost everywhere. Write
$\|f\|_{L^p(w)}=(\int|f|^pw)^{1/p}$.

* **44. Weighted maximal theorem.** $M$ is bounded on $L^p(w)$,
  $1<p<\infty$, exactly when $w\in A_p$. For $w\in A_1$, it is
  weak type $(1,1)$ with respect to $w(x)dx$.
* **45. Reverse Hölder and openness.** Every $A_p$ weight satisfies
  $(|Q|^{-1}\int_Qw^{1+\varepsilon})^{1/(1+\varepsilon)}
  \leq C|Q|^{-1}\int_Qw$ for some $\varepsilon>0$.
  If $p>1$, it belongs to $A_{p-\delta}$ for some $0<\delta<p-1$.
* **46. Duality and factorization.** $w\in A_p$ exactly when
  $w^{-1/(p-1)}\in A_{p'}$. Also $w\in A_p$ exactly when
  $w=u v^{1-p}$ for two $A_1$ weights $u,v$.
* **47. Weighted singular integrals.** Every standard
  Calderón–Zygmund operator is bounded on $L^p(w)$ for $w\in A_p$.
  The bound depends only on the exponent, the kernel and $L^2$ bounds,
  and $[w]_{A_p}$; sharply, it is
  $C[w]_{A_p}^{\max(1,1/(p-1))}$ (Hytönen's $A_2$ theorem with
  extrapolation). Lerner's pointwise domination
  $|Tf|\leq C_T\sum_{j=1}^{3^d}\sum_{Q\in\mathcal S_j}\langle|f|\rangle_Q1_Q$,
  with sparse families $\mathcal S_j$ depending on $f$, gives a short proof.
* **48. Rubio de Francia extrapolation.** If a family of nonnegative
  pairs $(f,g)$ satisfies $\|f\|_{L^{p_0}(w)}\leq C([w]_{A_{p_0}})
  \|g\|_{L^{p_0}(w)}$ for every $w\in A_{p_0}$ at one
  $1<p_0<\infty$, then it satisfies the corresponding estimate for
  every $1<p<\infty$ and every $w\in A_p$.
* **49. John–Nirenberg inequality.** For
  $\|b\|_{\mathrm{BMO}}=\sup_Q|Q|^{-1}\int_Q|b-b_Q|$,
  $|\{x\in Q:|b-b_Q|>t\}|\leq C|Q|e^{-ct/\|b\|_{\mathrm{BMO}}}$.
  All finite mean-oscillation exponents give equivalent seminorms.
* **50. Singular-integral endpoints.** Standard Calderón–Zygmund
  operators map $L^\infty$ into BMO, modulo constants, and map
  the real Hardy space $H^1$ (see 52) into $L^1$.
* **51. Sharp maximal function.** With
  $M^\#f(x)=\sup_{Q\ni x}|Q|^{-1}\int_Q|f-f_Q|$, so that
  $\|M^\#f\|_\infty=\|f\|_{\mathrm{BMO}}$, one has
  $\|f\|_p\leq C_{d,p}\|M^\#f\|_p$ whenever $f\in L^{p_0}$ for some
  $p_0\leq p<\infty$ (Fefferman–Stein). This yields interpolation between
  $L^{p_0}$ and BMO for linear operators.
* **52. Atomic decomposition of $H^1$.** The space defined by the
  integrability of a smooth grand maximal function consists exactly of
  sums $f=\sum_j\lambda_ja_j$, $\sum|\lambda_j|<\infty$,
  where each atom is supported in a cube $Q$, has integral zero, and
  satisfies $\|a_j\|_\infty\leq|Q|^{-1}$.
  The infimum coefficient sum is an equivalent norm. The Poisson,
  smooth, and grand maximal functions give the same space for every
  $0<p<\infty$ (Fefferman–Stein), and $H^p=L^p$ for $p>1$.
* **53. Hardy–BMO duality.** $(H^1(\mathbb R^d))^*=\mathrm{BMO}/\mathbb C$
  through the extension of $\int fb$ from test functions. The dual norm
  is equivalent to the BMO seminorm.
* **54. Riesz-transform characterization.** For $f\in L^1$,
  $f\in H^1$ exactly when $R_jf\in L^1$ for every $j$;
  $\|f\|_{H^1}\asymp\|f\|_1+\sum_j\|R_jf\|_1$.
* **55. BMO commutators.** If $b\in\mathrm{BMO}$ and $T$ is a
  standard Calderón–Zygmund operator, then
  $[b,T]f=bTf-T(bf)$ is bounded on $L^p$, $1<p<\infty$,
  with norm at most $C\|b\|_{\mathrm{BMO}}$. Conversely, boundedness of
  all $[b,R_j]$ on some $L^p$ forces $b\in\mathrm{BMO}$
  (Coifman–Rochberg–Weiss).

## Frequency decompositions and oscillation

Let $\Delta_j$ be smooth annular Fourier projections forming a homogeneous
resolution away from zero. Homogeneous distribution identities are understood
modulo polynomials when needed. Nonstationary and stationary phase are
stated in SYNOPSIS50, items 13–14.

* **56. Littlewood–Paley theorem.** For $1<p<\infty$,
  $\|f\|_p\asymp\|(\sum_{j\in\mathbb Z}|\Delta_jf|^2)^{1/2}\|_p$.
  The analogous inhomogeneous result includes a low-frequency projection.
  The upper bound follows from uniform $L^p$ bounds for
  $\sum_j\varepsilon_j\Delta_j$, $\varepsilon_j=\pm1$, and Khintchine's
  inequality; the lower bound follows by duality. Sharp frequency cutoffs
  to dyadic annuli give the same equivalence in one dimension.
* **57. Poisson square functions.** For $1<p<\infty$,
  $\|f\|_p\asymp\|(\int_0^\infty|t\partial_tP_t*f|^2dt/t)^{1/2}\|_p$.
  Lusin area integrals, integrating $|\nabla P_t*f|^2t^{1-d}$ over
  $|y-x|<t$, give equivalent norms, and characterize $H^1$ at $p=1$.
* **58. Bernstein inequalities.** If $\operatorname{supp}\widehat f
  \subset\{|\xi|\leq R\}$ and $1\leq p\leq q\leq\infty$, then
  $\|\partial^\alpha f\|_q\leq
  C R^{|\alpha|+d(1/p-1/q)}\|f\|_p$.
  Annular localization also permits inverse derivative estimates.
* **59. Sobolev square functions.** For $1<p<\infty$ and real $s$,
  the Bessel potential norm is equivalent to the $L^p$ norm of
  $(\sum_{j\geq0}2^{2js}|\Delta_jf|^2)^{1/2}$, with the
  low-frequency term given weight one.
* **60. Coifman–Meyer bilinear multipliers.** A bounded smooth symbol
  $m(\xi,\eta)$ satisfying
  $|\partial_\xi^\alpha\partial_\eta^\beta m|
  \leq C_{\alpha\beta}(|\xi|+|\eta|)^{-|\alpha|-|\beta|}$
  defines $T_m:L^p\times L^q\to L^r$ for $1<p,q<\infty$,
  $1/r=1/p+1/q$. This includes $r<1$ with its quasi-norm.
* **61. Fractional Leibniz inequality.** For $s>0$,
  $1<r,p_1,q_1,p_2,q_2<\infty$ and
  $1/r=1/p_i+1/q_i$,
  $\|D^s(fg)\|_r\leq C(\|D^sf\|_{p_1}\|g\|_{q_1}
  +\|f\|_{p_2}\|D^sg\|_{q_2})$, initially for Schwartz functions.
  Here $D^s$ has multiplier $(2\pi|\xi|)^s$.
* **63. Van der Corput lemma.** On an interval, if
  $|\phi^{(k)}|\geq1$, then
  $|\int e^{i\lambda\phi}a|\leq
  C_k|\lambda|^{-1/k}(\|a\|_\infty+\|a'\|_1)$ for $k\geq2$.
  For $k=1$ the same estimate requires monotonicity of $\phi'$.
* **65. Curvature and Fourier decay.** Smooth compact hypersurface
  measure with smooth density and everywhere nonzero Gaussian curvature
  has transform $O((1+|\xi|)^{-(d-1)/2})$.
* **66. Stein–Tomas restriction theorem.** For $d\geq2$ and a smooth
  compact hypersurface $S$ with nonzero Gaussian curvature,
  $\|\widehat f|_S\|_{L^2(S)}\leq C\|f\|_p$ for
  $1\leq p\leq2(d+1)/(d+3)$. Equivalently its extension operator
  maps $L^2(S)$ to $L^{2(d+1)/(d-1)}(\mathbb R^d)$.
* **67. Bochner–Riesz summation above the integrable-kernel threshold.**
  For $\delta>(d-1)/2$, the inverse transform of
  $(1-|\xi|^2)_+^\delta$ is integrable. Its dilates give uniformly
  bounded Bochner–Riesz means on every $L^p$, converging in norm for
  $1\leq p<\infty$ and at Lebesgue points.
* **68. The ball multiplier obstruction.** For $d\geq2$, the
  characteristic function of the Euclidean ball is an $L^p$ Fourier
  multiplier, $1<p<\infty$, only for $p=2$ (C. Fefferman, via Besicovitch
  sets).

## Geometric maximal functions, restriction, and decoupling

A **Kakeya (Besicovitch) set** in $\mathbb R^d$ is a compact set containing a
unit line segment in every direction. For $0<\delta<1$ a $\delta$-tube is a
cylinder of length $1$ and radius $\delta$; the **Kakeya maximal function** is
$f^*_\delta(\omega)=\sup_T|T|^{-1}\int_T|f|$, $\omega\in S^{d-1}$, over
$\delta$-tubes $T$ with axis parallel to $\omega$. For a compact
hypersurface $S$ with surface measure $\sigma$, the **extension operator** is
$Eg=(g\,d\sigma)^\vee$, the adjoint of restriction $f\mapsto\widehat f|_S$.
The **Bochner–Riesz means** are $S^\delta f=((1-|\xi|^2)_+^\delta\widehat f)^\vee$.

* **70. Besicovitch sets and the Kakeya conjecture.** For every $d\geq2$
  there are Kakeya sets of Lebesgue measure zero (Besicovitch). Every Kakeya
  set in $\mathbb R^2$ has Hausdorff dimension $2$ (Davies). The Kakeya
  conjecture asserts Hausdorff and Minkowski dimension $d$ in every
  dimension; Wolff's hairbrush bound gives Hausdorff dimension at least
  $(d+2)/2$, and Wang and Zahl have proved the case $d=3$ (2025 preprint, arXiv:2502.17655;
  the sticky case appears in *J. Amer. Math. Soc.* 39 (2026)).
* **71. Kakeya maximal estimates.** In $\mathbb R^2$,
  $\|f^*_\delta\|_{L^2(S^1)}\leq C(\log(1/\delta))^{1/2}\|f\|_{L^2}$
  (Córdoba), and the logarithm cannot be removed. The Kakeya maximal
  conjecture asserts
  $\|f^*_\delta\|_{L^d(S^{d-1})}\leq C_\varepsilon\delta^{-\varepsilon}\|f\|_{L^d}$
  for every $\varepsilon>0$; it implies the Kakeya conjecture (Bourgain).
  Kakeya sets of measure zero make the ball multiplier unbounded (68).
* **72. Spherical maximal theorem.** For $d\geq2$ the maximal operator
  $\mathcal Af(x)=\sup_{t>0}|\int_{S^{d-1}}f(x-ty)\,d\sigma(y)|$, with
  normalized surface measure, is bounded on $L^p(\mathbb R^d)$ exactly when
  $p>d/(d-1)$ (Stein for $d\geq3$, Bourgain for $d=2$). Consequently
  spherical means of $f\in L^p$, $p>d/(d-1)$, converge to $f$ almost
  everywhere as $t\to0$.
* **73. Restriction conjecture.** For the unit sphere $S^{d-1}$, or a
  compact piece of the paraboloid, $\|Eg\|_{L^q(\mathbb R^d)}\leq
  C\|g\|_{L^p(S)}$ can hold only if $q>2d/(d-1)$ and
  $q\geq(d+1)p'/(d-1)$; the necessity comes from the decay of
  $\widehat\sigma$ and from Knapp's example. The restriction conjecture
  asserts that these conditions suffice. It holds for $d=2$ (Fefferman,
  Zygmund; Carleson–Sjölin), and for $p=2$ it is the Stein–Tomas theorem
  66. For $d\geq3$ only partial ranges are known, through bilinear,
  multilinear, and polynomial-partitioning methods (Bourgain, Wolff, Tao,
  Bourgain–Guth, Guth). The restriction conjecture implies the Kakeya
  conjecture.
* **74. Bochner–Riesz conjecture.** For $0<\delta\leq(d-1)/2$, boundedness
  of $S^\delta$ on $L^p(\mathbb R^d)$ forces
  $|1/p-1/2|<(2\delta+1)/(2d)$, and the Bochner–Riesz conjecture asserts that
  this suffices. In $\mathbb R^2$ it is a theorem (Carleson–Sjölin): for
  $\delta>0$, $S^\delta$ is bounded on $L^p(\mathbb R^2)$ exactly when
  $|1/p-1/2|<(2\delta+1)/4$. In general dimension the Stein–Tomas theorem
  gives the conjecture for $\max(p,p')\geq2(d+1)/(d-1)$, and the
  Bochner–Riesz conjecture implies the restriction conjecture (Tao). At
  $\delta=0$ the ball multiplier fails for $p\ne2$ (68).
* **75. Bourgain–Demeter decoupling.** Partition the $\delta$-neighborhood of
  the paraboloid $\{(\xi,|\xi|^2):\xi\in[0,1]^{d-1}\}$ into boxes $\theta$
  of dimensions about $\delta^{1/2}\times\dots\times\delta^{1/2}\times\delta$,
  and let $f_\theta$ be the Fourier restriction of $f$ to $\theta$. If
  $\widehat f$ is supported in that neighborhood and
  $2\leq p\leq2(d+1)/(d-1)$, then for every $\varepsilon>0$
  $$\|f\|_{L^p(\mathbb R^d)}\leq C_\varepsilon\delta^{-\varepsilon}
    \Big(\sum_\theta\|f_\theta\|_{L^p(\mathbb R^d)}^2\Big)^{1/2}.$$
  The range is sharp. The analogous decoupling for the moment curve gives
  Vinogradov's mean value theorem (Bourgain–Demeter–Guth); decoupling also
  gives sharp Strichartz estimates on tori.

## Reference guide

Stein–Shakarchi, Katznelson, and Grafakos overlap on transforms, series,
summability, and the classical convergence questions. Grafakos, Stein–Weiss,
Duoandikoetxea, Stein's two major harmonic-analysis books, and Torchinsky
provide the real-variable and multiplier core. The weighted and endpoint
parts recur in Grafakos's advanced treatment, García-Cuerva–Rubio de Francia,
and Cruz-Uribe–Martell–Pérez. Muscalu–Schlag connects those methods to
oscillatory and multilinear analysis; Stein and Sogge give the principal
restriction and oscillatory-integral context. Demeter, Wolff's lectures, and
Mattila treat Kakeya sets, restriction, Bochner–Riesz, and decoupling. The
statements here select established common results, without attempting the
union of the specialized decoupling, additive-combinatorial, multiparameter,
and vector-valued theories.

Local source copies consulted include substantial text, not just contents:

* [Stein–Shakarchi, *Fourier Analysis*](References/SteinShakarchi2003PrincetonLecturesAnalysis1FourierAnalysisIntroduction-PrincetonUniversityPress.pdf).
* [Grafakos, *Classical Fourier Analysis*](References/Grafakos2014ClassicalFourierAnalysis3rdEd-SpringerGTM.pdf).
* [Grafakos, *Modern Fourier Analysis*](References/Grafakos2009ModernFourierAnalysis2ndEd-SpringerGTM.pdf).
* [Muscalu–Schlag, *Classical and Multilinear Harmonic Analysis*, I](References/MuscaluSchlag2013ClassicalMultilinearHarmonicAnalysisVol1-Cambridge.pdf).
* [Demeter, *Fourier Restriction, Decoupling, and Applications*](References/Demeter2019FourierRestrictionDecouplingApplications-CambridgeStudiesAM184.pdf).

The advanced Grafakos volume supplies a companion treatment of the weighted,
Hardy-space, and restriction material; the bibliography lists it together
with the classical volume, and separately lists the newer introductory
*Fundamentals of Fourier Analysis*.
