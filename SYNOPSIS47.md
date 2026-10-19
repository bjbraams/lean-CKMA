# Synopsis: Approximation theory

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-47);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring core material from Section 47 of
[CKMA-bib.md](CKMA-bib.md#ckma-47).
It treats best approximation, positive operators, direct and inverse
theorems, polynomial, rational, and Padé approximation, splines, kernels,
sparse expansions, widths, discrepancy, ridge functions, and tractability. Orthogonal-polynomial spectral theory is developed
in Section 48; the approximation questions here concern error, smoothness,
stability, and the size of approximation classes.

The high-dimensional probabilistic counterpart is in
[07A](CKMA-bib.md#ckma-07a), structured expansions and sampling in Section 29,
and transport-based optimization in [39C](CKMA-bib.md#ckma-39c). Error
estimates and approximation classes remain the organising questions here.

Write $\mathcal P_n$ for polynomials of degree at most $n$ and
$\mathcal T_n$ for trigonometric polynomials of frequencies $|k|\leq n$.
For a normed function space $X$, put
$E_n(f)_X=\inf_{p\in\mathcal P_n}\|f-p\|_X$; a superscript
$\mathrm{trig}$ indicates $\mathcal T_n$. Uniform-approximation statements
use real continuous functions on a compact interval unless specified otherwise.

## Best approximation and alternation

* **1. Finite-dimensional existence.** Every finite-dimensional
  subspace of a normed space admits a best approximant to each point.
  Compactness of bounded coefficient sets supplies existence.
* **2. Strict-convexity uniqueness.** In a strictly convex normed
  space, best approximants from convex sets are unique whenever they
  exist. In particular finite-dimensional $L^p$ approximation is unique
  for $1<p<\infty$.
* **3. Hilbert projection.** Best approximation from a closed Hilbert
  subspace is characterized by orthogonality of the residual, and
  satisfies the Pythagorean identity and contraction estimate.
* **4. Dual characterization.** For a closed linear subspace $V$,
  $p\in V$ is best for $f\notin V$ exactly when a norm-one
  functional annihilating $V$ takes value $\|f-p\|$ on $f-p$.
* **5. Haar-space uniqueness.** A real $m$-dimensional subspace
  of continuous functions on an interval in which every nonzero
  function has at most $m-1$ distinct zeros has unique uniform best approximants.
* **6. Chebyshev alternation theorem.** A polynomial $p\in\mathcal P_n$
  is the best uniform approximant to $f\notin\mathcal P_n$ exactly
  when $f-p$ takes alternating values $\pm\|f-p\|_\infty$ at
  $n+2$ increasing points. Haar spaces have the analogous $m+1$ point criterion.
* **7. Strong uniqueness.** For a fixed $f$ outside a Haar space,
  its best approximant $p_*$ satisfies
  $\|f-p\|_\infty\geq\|f-p_*\|_\infty+
  \gamma(f)\|p-p_*\|_\infty$, with $\gamma(f)>0$.
* **8. Chebyshev minimax polynomial.** Among monic degree-$n$
  polynomials on $[-1,1]$, $2^{1-n}T_n$ has the unique smallest
  uniform norm $2^{1-n}$, where $T_n(\cos\theta)=\cos n\theta$.
* **9. Polynomial interpolation.** Distinct nodes determine a unique
  polynomial interpolant. If $f\in C^{n+1}$, its error at $x$
  is $f^{(n+1)}(\xi)\prod_{j=0}^n(x-x_j)/(n+1)!$ for an
  intervening $\xi$.
* **10. Lebesgue inequality.** A bounded projection $L$ onto an
  approximation space satisfies $\|f-Lf\|\leq(1+\|L\|)\inf_p\|f-p\|$.
  For interpolation, $\|L\|=\sup_x\sum_j|\ell_j(x)|$.

## Density and positive approximation operators

* **11. Weierstrass theorem.** Algebraic polynomials are uniformly
  dense on a compact interval; trigonometric polynomials are uniformly
  dense among continuous periodic functions.
* **12. Stone–Weierstrass theorem.** A real subalgebra of $C(K)$
  containing constants and separating points is uniformly dense.
  For complex algebras add closure under complex conjugation.
* **13. Müntz–Szász theorem.** If $0<\lambda_1<\lambda_2<\cdots\to\infty$,
  the span of $1,x^{\lambda_1},x^{\lambda_2},\ldots$ is dense
  in $C[0,1]$ exactly when $\sum_j1/\lambda_j=\infty$.
* **14. Bernstein polynomial convergence.**
  $B_nf(x)=\sum_{k=0}^nf(k/n)\binom nkx^k(1-x)^{n-k}$
  converges uniformly to every $f\in C[0,1]$. These operators are
  positive, preserve affine functions, and are contractions.
* **15. Quantitative Bernstein estimate.**
  $\|B_nf-f\|_\infty\leq C\omega(f,n^{-1/2})$, where
  $\omega$ is the ordinary modulus of continuity. The variance
  $x(1-x)/n$ gives the local scale.
* **16. Voronovskaya asymptotics.** If $f\in C^2[0,1]$, then
  $n(B_nf-f)\to\frac12x(1-x)f''(x)$ uniformly.
* **17. Korovkin theorem.** Positive linear maps
  $L_n:C[0,1]\to C[0,1]$ converge strongly to the identity
  exactly when they converge uniformly on $1,x,x^2$.
* **18. Shape preservation.** Bernstein operators preserve
  monotonicity and convexity. Their first and second derivatives are
  Bernstein expansions of the corresponding scaled finite differences.

## Smoothness, direct estimates, and inverse estimates

For periodic $f\in L^p$, $1\leq p\leq\infty$, define
$\omega_r(f,t)_p=\sup_{|h|\leq t}\|\Delta_h^rf\|_p$.
At $p=\infty$ use continuous functions. The derivative $K$-functional is
$K_r(f,t^r)_p=\inf_g(\|f-g\|_p+t^r\|g^{(r)}\|_p)$.
For algebraic approximation put $\varphi(x)=\sqrt{1-x^2}$;
the **Ditzian–Totik modulus** uses centered differences with step
$h\varphi(x)$ where all evaluation points remain in $[-1,1]$.

* **19. Modulus–$K$ equivalence.** For periodic functions,
  $K_r(f,t^r)_p\asymp\omega_r(f,t)_p$.
  Thus derivative approximation and finite-difference smoothness describe
  the same scale without requiring $f$ itself to have derivatives.
* **20. Jackson's trigonometric theorem.**
  $E_n^{\mathrm{trig}}(f)_p\leq C_r\omega_r(f,1/n)_p$. For
  $f^{(r-1)}$ absolutely continuous, the sharp form is
  $E_n^{\mathrm{trig}}(f)_\infty\leq K_r(n+1)^{-r}\|f^{(r)}\|_\infty$
  with the Favard constants $K_r=\frac4\pi\sum_{j\geq0}(-1)^{j(r+1)}(2j+1)^{-r-1}$.
* **21. Inverse trigonometric estimate.**
  $\omega_r(f,1/n)_p\leq C_rn^{-r}
  \sum_{k=0}^n(k+1)^{r-1}E_k^{\mathrm{trig}}(f)_p$.
  Good approximation therefore forces smoothness.
* **22. Hölder–Zygmund characterization.** For $0<s<r$,
  $E_n^{\mathrm{trig}}(f)_p=O(n^{-s})$ exactly when
  $\omega_r(f,t)_p=O(t^s)$. At $s=r$ the displayed inverse
  estimate allows a logarithmic loss, so the endpoint requires care.
* **23. Bernstein derivative inequality.**
  $\|T^{(r)}\|_p\leq n^r\|T\|_p$ for $T\in\mathcal T_n$,
  $1\leq p\leq\infty$.
* **24. Markov inequality.** For $P\in\mathcal P_n$ on $[-1,1]$,
  $\|P'\|_\infty\leq n^2\|P\|_\infty$. The exponent and
  first-derivative constant are sharp.
* **25. Interior Bernstein inequality.**
  $\|\varphi P'\|_\infty\leq n\|P\|_\infty$.
  It explains the transition from interior scale $n^{-1}$ to
  endpoint scale $n^{-2}$.
* **26. Algebraic Jackson theorem.** For continuous functions on
  $[-1,1]$, $E_n(f)_\infty\leq C_r\omega_r(f,1/n)_\infty$,
  using differences confined to the interval and $n\geq r$.
* **27. Weighted sharp direct theorem.** For $1\leq p\leq\infty$,
  $E_n(f)_p\leq C_r\omega_\varphi^r(f,1/n)_p$, $n\geq r$.
  The variable step gives the correct endpoint behavior.
* **28. Weighted inverse theorem.**
  $\omega_\varphi^r(f,1/n)_p\leq C_rn^{-r}
  \sum_{k=0}^n(k+1)^{r-1}E_k(f)_p$.
* **29. Weighted $K$-functional.** For sufficiently small $t$,
  $\omega_\varphi^r(f,t)_p\asymp
  \inf_g(\|f-g\|_p+t^r\|\varphi^rg^{(r)}\|_p)$,
  with $g^{(r-1)}$ locally absolutely continuous.
* **30. Nikolskii inequality.** For $1\leq p\leq q\leq\infty$,
  $\|T\|_q\leq Cn^{1/p-1/q}\|T\|_p$ for trigonometric
  polynomials of degree $n$. For algebraic polynomials in unweighted
  interval norms the corresponding universal exponent is $2(1/p-1/q)$.

## Chebyshev, analytic, and rational approximation

The **Bernstein ellipse** $E_\rho$, $\rho>1$, is the image of
$|w|=\rho$ under $z=(w+w^{-1})/2$.

* **31. Chebyshev coefficient decay.** If $f$ is holomorphic on
  and inside $E_\rho$ and bounded there by $M$, its Chebyshev
  coefficients satisfy $|a_k|\leq2M\rho^{-k}$.
* **32. Geometric convergence.** The degree-$n$ Chebyshev truncation
  has error at most $2M\rho^{-n}/(\rho-1)$; interpolation at
  Chebyshev extrema has error at most $4M\rho^{-n}/(\rho-1)$.
* **33. Converse analyticity.** If $E_n(f)_\infty\leq C\rho^{-n}$,
  then $f$ extends holomorphically inside every $E_\sigma$,
  $1<\sigma<\rho$.
* **34. Finite smoothness and coefficients.** For an integer $\nu\geq1$, if $f^{(\nu-1)}$
  is absolutely continuous and $f^{(\nu)}$ has bounded variation,
  then $a_k=O(k^{-\nu-1})$, and summation gives uniform truncation
  error $O(n^{-\nu})$.
* **35. Chebyshev interpolation stability.** Its Lebesgue constants
  are $(2/\pi)\log n+O(1)$. Hence interpolation is near-best
  with a logarithmic factor.
* **36. Faber's theorem.** No triangular choice of polynomial
  interpolation nodes makes the interpolants converge uniformly for
  every continuous function. The associated Lebesgue constants are unbounded.
* **37. Bernstein–Walsh inequality.** For a nonpolar compact set
  $K$ regular for its exterior Dirichlet problem and with connected
  complement, with Green function $g_K(\cdot,\infty)$ of
  $\mathbb C\setminus K$ with pole at $\infty$,
  $|P(z)|\leq\|P\|_K e^{n g_K(z,\infty)}$ for
  $P\in\mathcal P_n$. **Walsh's maximal convergence theorem:**
  $\limsup_n E_n(f)_K^{1/n}\leq1/R$, $R>1$, exactly when $f$ extends
  holomorphically to the region $\{g_K(\cdot,\infty)<\log R\}$; for
  $K=[-1,1]$ these regions are the Bernstein ellipses.
  The inequality holds more generally for every nonpolar compact $K$ on
  the unbounded component of $\mathbb C\setminus K$; capacity and Green
  functions therefore control polynomial growth away from the approximation set.
* **38. Rational minimax approximation.** A continuous real function
  on an interval has a best rational approximant of type $(m,n)$
  among real rational functions without interval poles. Limits may
  lose degree through common-factor cancellation.
* **39. Rational alternation.** For a reduced approximant $p/q$,
  let $\delta=\min(m-\deg p,n-\deg q)$. For nonzero residual,
  best type-$(m,n)$ approximation is characterized by
  $m+n+2-\delta$ alternating extrema, with the usual zero-numerator
  convention. The defect accounts for lost degrees.
* **40. Newman's theorem.** Best type-$(n,n)$ rational approximation
  to $|x|$ on $[-1,1]$ has error between
  $c_1e^{-c_2\sqrt n}$ and $c_3e^{-c_4\sqrt n}$ for positive
  constants; Stahl's sharp asymptotic is $E_{n,n}(|x|)\sim8e^{-\pi\sqrt n}$.
  Polynomial approximation has exact order $n^{-1}$ instead.
* **72. Padé approximants.** For a power series $f(z)=\sum_kc_kz^k$ and
  $m,n\geq0$ there are polynomials $P,Q\not\equiv0$, $\deg P\leq m$,
  $\deg Q\leq n$, with $Qf-P=O(z^{m+n+1})$; the rational function
  $[m/n]_f=P/Q$ is unique (Frobenius), although it need not match $f$ to
  that order when the table is not normal. The $[m/0]$ entries are the
  Taylor sections, and continued-fraction convergents give staircase paths
  in the table.
* **73. De Montessus de Ballore theorem.** If $f$ is meromorphic in
  $|z|<R$ with exactly $n$ poles there, counted with multiplicity, and
  holomorphic at $0$, then $[m/n]_f\to f$ uniformly on compact subsets
  of the disk minus the poles as $m\to\infty$, with
  $\limsup_m\|f-[m/n]_f\|_K^{1/m}\leq\max_K|z|/R$, and the poles of
  $[m/n]_f$ converge to those of $f$. For diagonal sequences
  $[n/n]_f$ of a function meromorphic in $\mathbb C$, convergence holds
  in planar measure (Nuttall) and in logarithmic capacity (Pommerenke) on
  compact sets, but not
  uniformly in general, because of spurious poles.

## Splines and total positivity

An **order-$k$ spline** has polynomial pieces of degree at most $k-1$,
with the continuity prescribed by knot multiplicities. With simple interior
knots it is $C^{k-2}$. Let $N_{i,k}$ be the normalized B-splines for
a nondecreasing knot sequence $t_i$.

* **41. Spline dimension.** On an interval with $M$ simple interior
  knots, the order-$k$ spline space has dimension $M+k$.
  A knot of multiplicity $r$ reduces continuity there to $C^{k-r-1}$.
* **42. B-spline basis.** The $N_{i,k}$ form a basis, are nonnegative,
  have support $[t_i,t_{i+k}]$, and sum to one on the basic interval
  for the usual endpoint-completed knot sequence.
* **43. Cox–de Boor recurrence.**
  $N_{i,k}(x)=\frac{x-t_i}{t_{i+k-1}-t_i}N_{i,k-1}(x)
  +\frac{t_{i+k}-x}{t_{i+k}-t_{i+1}}N_{i+1,k-1}(x)$,
  with zero-denominator terms interpreted as zero.
* **44. Differentiation and locality.** B-spline differentiation
  gives a difference of two order-$(k-1)$ B-splines with factors
  $(k-1)/(t_{i+k-1}-t_i)$ and $(k-1)/(t_{i+k}-t_{i+1})$.
  Derivatives and local approximation can therefore be controlled by coefficient differences.
* **45. Schoenberg–Whitney theorem.** For increasing interior
  interpolation nodes, the square B-spline collocation matrix is
  nonsingular exactly when nodes and supports satisfy
  $t_i<x_i<t_{i+k}$, with the corresponding endpoint conventions.
* **46. Total positivity.** B-spline collocation matrices at ordered
  nodes are totally nonnegative. Admissible minors are positive under
  the strict support inequalities.
* **47. Variation diminution.** A B-spline expansion has no more
  strict sign changes than its coefficient sequence. This explains
  positivity and shape-preservation properties of spline constructions.
* **48. Spline Jackson estimates.** For any knot sequence on $[a,b]$
  with maximal spacing $h$, $1\leq j\leq k$, $1\leq p\leq\infty$, and
  $f\in W^{j,p}$, some order-$k$ spline $S$ satisfies
  $\|f-S\|_p\leq C_kh^j\|f^{(j)}\|_p$; no mesh-ratio bound is needed.
  For uniform knots, matching Bernstein-type inverse estimates identify
  the spline approximation spaces with Besov spaces of order below $k-1+1/p$.
* **49. Local quasi-interpolation.** Bounded local spline operators
  reproducing degree-$(k-1)$ polynomials achieve the corresponding
  smoothness error estimates without solving a global interpolation system.
* **50. Natural cubic variational principle.** The natural cubic
  interpolant uniquely minimizes $\int_a^b|u''|^2$ among $H^2$
  functions with the prescribed nodal values, when the distinct nodes
  include both endpoints. Its second derivative vanishes at those endpoints.
* **51. Smoothing-spline representer theorem.** For $\lambda>0$,
  minimizing a positive weighted sum of squared nodal errors plus
  $\lambda\int|u^{(m)}|^2$ gives a natural spline of degree
  $2m-1$ with knots among the data sites. At least $m$ distinct
  sites ensure uniqueness by controlling the polynomial nullspace.

## Kernel and scattered-data approximation

For a positive definite kernel $K$, its **native space** is the
reproducing-kernel Hilbert space generated by $K(\cdot,x)$.
The fill distance of nodes $X\subset\Omega$ is
$h_{X,\Omega}=\sup_{x\in\Omega}\min_{x_j\in X}|x-x_j|$.

* **52. Positive definite interpolation.** Strict positive definiteness
  makes the Gram matrix at distinct sites invertible and gives a
  unique interpolant $s_X=\sum c_jK(\cdot,x_j)$.
* **53. Minimum norm and projection.** The kernel interpolant is
  the orthogonal projection onto the kernel span and has the least
  native-space norm among all functions with those data.
* **54. Power-function error.**
  $|f(x)-s_X(x)|\leq P_X(x)\|f\|_K$, where
  $P_X(x)^2=K(x,x)-k_X(x)^*K_X^{-1}k_X(x)$.
  This is the exact norm of the residual evaluation functional.
* **55. Sobolev-native-space rates.** If the native norm is equivalent
  to $H^s(\Omega)$, $s>d/2$, on a bounded domain with the
  standard extension and interior-cone properties, then
  $\|f-s_X\|_\infty\leq Ch_{X,\Omega}^{s-d/2}\|f\|_{H^s}$
  for sufficiently small fill distance.
* **56. Bochner criterion.** A continuous translation-invariant kernel
  $K(x-y)$ is positive definite exactly when it is the Fourier
  transform of a finite positive measure. A spectral density positive
  on an open set gives strict positive definiteness at distinct sites.
* **57. Conditional positive definiteness.** A strictly conditionally positive
  definite kernel of order $m$, augmented by polynomials of degree
  less than $m$, gives a uniquely solvable interpolation system when
  the sites are polynomially unisolvent and the coefficient side
  constraints annihilate those polynomials.
* **58. General representer theorem.** Minimizing a function of
  finitely many bounded linear observations plus a strictly increasing
  function of the Hilbert norm yields a minimizer in the span of
  the observation representers. Orthogonal components only increase the penalty.

## Nonlinear approximation, widths, and dimension

For a dictionary $\mathcal D$, let $\sigma_m(f)$ be the least error
of linear combinations of at most $m$ dictionary elements. For bounded
$A\subset X$, the **Kolmogorov width** is
$d_m(A;X)=\inf_{\dim V\leq m}\sup_{f\in A}\inf_{v\in V}\|f-v\|$.
A normalized basis is **democratic** when sums over equal-size finite
index sets have comparable norms uniformly.

* **59. Orthogonal best-term approximation.** In an orthonormal
  basis, best $m$-term approximation retains the $m$ largest
  coefficient moduli; squared error is the sum of the omitted squared moduli.
* **60. Stechkin inequality.** For $0<\tau<2$, coefficients in
  $\ell^\tau$ give $\sigma_m(f)_2\leq
  Cm^{1/2-1/\tau}\|c\|_{\ell^\tau}$.
  Wavelet Besov norms turn this sequence estimate into spatial approximation rates.
* **61. Greedy-basis characterization.** A normalized Schauder basis
  has thresholding approximants $G_mf$ (keep the $m$ coefficients of
  largest modulus) satisfying $\|f-G_mf\|\leq C\sigma_m(f)$
  uniformly exactly when it is unconditional and democratic.
* **62. Orthogonal greedy rate.** For a unit-norm Hilbert dictionary,
  functions in its closed absolutely convex hull have orthogonal-greedy
  error at most $Cm^{-1/2}$. Weak choices with a fixed positive
  selection parameter retain this rate with a changed constant.
* **63. Wavelet nonlinear rates.** For sufficiently regular wavelets,
  $f\in B_{\tau,\tau}^s$ with $1/\tau=s/d+1/2$ has
  $\sigma_m(f)_{L^2}\leq Cm^{-s/d}\|f\|_{B_{\tau,\tau}^s}$.
  The critical Besov scale permits spatially inhomogeneous smoothness.
* **64. Hilbert ellipsoid widths.** If $T$ is compact between
  Hilbert spaces with singular values $s_1\geq s_2\geq\cdots$,
  then $d_m(TB)=s_{m+1}$. Best rank-$m$ linear approximation
  has the same worst-case error.
* **65. Widths of finite-dimensional balls.** The **Gelfand width** is
  $d^m(A;X)=\inf_{\operatorname{codim}L\leq m}\sup_{f\in A\cap L}\|f\|$
  over closed subspaces $L$. The Gelfand widths of the
  $\ell^1$ ball satisfy $d^m(B_1^N;\ell_2^N)\asymp
  \min\{1,((1+\log(N/m))/m)^{1/2}\}$ (Kashin; Garnaev–Gluskin), and by
  duality the same holds for the Kolmogorov widths $d_m(B_2^N;\ell_\infty^N)$.
  Discretization gives Kashin's orders of the Kolmogorov widths
  $d_m(W^r_p;L^q)$ of Sobolev classes for $p<q$, $q>2$: they are of
  smaller order than the corresponding linear widths.
* **66. Sobolev widths.** For the unit ball of $H^s(\mathbb T^d)$
  in $L^2$, $d_m\asymp m^{-s/d}$, $s>0$.
  Frequency counting makes the dependence on dimension explicit.
* **67. Mixed-smoothness widths.** For the periodic Hilbert space
  with Fourier weight $\prod_{j=1}^d(1+|k_j|^2)^s$,
  $d_m\asymp m^{-s}(\log m)^{s(d-1)}$ in $L^2$.
  Hyperbolic crosses give the corresponding optimal spectral spaces.
* **68. Hyperbolic-cross counting.**
  $\#\{k\in\mathbb Z^d:\prod_j\max(1,|k_j|)\leq N\}
  \asymp N(\log N)^{d-1}$ for fixed $d$ and large $N$.
* **69. Multivariate polynomial dimension.** Total-degree-$n$
  polynomial spaces in $d$ variables have dimension $\binom{n+d}{d}$;
  tensor degree bounds give $\prod_j(n_j+1)$.
* **70. Tensor analytic approximation.** Holomorphy in a product
  of Bernstein ellipses, with boundedness on their closures, gives
  product-geometric coefficient decay.
  Tensor truncation errors are bounded by a constant times
  $\sum_j\rho_j^{-n_j}$ with the other ellipse parameters fixed.
* **71. Approximation on spheres.** On $S^{d-1}$, spherical
  polynomials satisfy Jackson and inverse estimates with rotational
  moduli of smoothness. Their degree-$n$ dimension has order
  $n^{d-1}$, giving the manifold dimension in approximation rates.

## Discrepancy, ridge functions, and tractability

For a finite set $\{x_1,\ldots,x_N\}\subset[0,1)^s$ the **star
discrepancy** is $D_N^*=\sup_{t\in[0,1]^s}
|N^{-1}\#\{i:x_i\in[0,t)\}-t_1\cdots t_s|$. A **ridge function** on
$\mathbb R^d$ has the form $x\mapsto g(a\cdot x)$ with $a\neq0$.

* **74. Koksma–Hlawka inequality.** If $f$ has bounded variation
  $V_{\rm HK}(f)$ in the sense of Hardy and Krause on $[0,1]^s$, then
  $|N^{-1}\sum_{i=1}^Nf(x_i)-\int_{[0,1]^s}f|\leq V_{\rm HK}(f)D_N^*$.
  For $s=1$ this is Koksma's inequality with ordinary variation.
  A sequence is uniformly distributed exactly when $D_N^*\to0$.
* **75. Discrepancy orders.** Every $N$-point set in $[0,1)^s$,
  $s\geq2$, has $D_N^*\geq c_s(\log N)^{(s-1)/2}/N$ (Roth; for $s=2$
  Schmidt's sharp bound $c\log N/N$). Hammersley point sets and
  $(t,m,s)$-nets achieve $D_N^*\leq C_s(\log N)^{s-1}/N$, and
  Halton sequences and $(t,s)$-sequences achieve
  $D_N^*\leq C_s(\log N)^s/N$ for all initial segments.
  Quasi-Monte Carlo integration therefore converges at almost order
  $N^{-1}$ for fixed $s$, compared with $N^{-1/2}$ for Monte Carlo.
* **76. Density of ridge functions.** For a set $\Omega$ of directions,
  $\operatorname{span}\{g(a\cdot x):a\in\Omega,\ g\in C(\mathbb R)\}$
  is dense in $C(\mathbb R^d)$, uniformly on compact sets, exactly when
  no nonzero homogeneous polynomial vanishes on $\Omega$ (Vostrecov–Kreines,
  Lin–Pinkus). For continuous $\sigma:\mathbb R\to\mathbb R$,
  $\operatorname{span}\{\sigma(w\cdot x+b):w\in\mathbb R^d,\ b\in\mathbb R\}$
  is dense in $C(\mathbb R^d)$ in that topology exactly when $\sigma$
  is not a polynomial (Leshno–Lin–Pinkus–Schocken); this is the
  universal approximation theorem for one-hidden-layer neural networks.
* **77. Tractability.** For a sequence of $d$-variate problems let
  $n(\varepsilon,d)$ be the least number of information evaluations
  needed to reduce the worst-case error to $\varepsilon$ times the initial
  error. The problem is **polynomially tractable** if
  $n(\varepsilon,d)\leq Cd^q\varepsilon^{-p}$, **strongly** so if
  $q=0$, and suffers the **curse of dimensionality** if
  $n(\varepsilon,d)\geq(1+\gamma)^d$ for some fixed $\varepsilon,\gamma>0$
  and infinitely many $d$. For quasi-Monte Carlo integration in weighted
  Sobolev spaces with product weights $\gamma_j$, strong tractability holds
  exactly when $\sum_j\gamma_j<\infty$, and tractability exactly when
  $\limsup_d\sum_{j\leq d}\gamma_j/\log d<\infty$ (Sloan–Woźniakowski);
  with equal weights the problem is intractable.

## Reference guide

Cheney, Rivlin, Achieser, Timan, DeVore–Lorentz, and Lorentz share
the minimax, density, direct, and inverse theory. Ditzian–Totik and
Bustamante sharpen interval and endpoint estimates. Trefethen compares
analytic, Chebyshev, interpolation, and rational approximation; Saff–Totik
and Stahl–Totik explain the potential-theoretic geometry. Schumaker,
de Boor, Karlin, and Pinkus supply splines and total positivity.
Wendland and Iske connect interpolation with native spaces; Temlyakov,
DeVore, Pinkus, and the hyperbolic-cross references explain sparse
approximation and widths. The spherical texts give corresponding
constructions on curved domains. Baker–Graves-Morris supplies Padé
approximation; Drmota–Tichy and Dick–Pillichshammer discrepancy and
quasi-Monte Carlo integration; Pinkus ridge functions; and
Novak–Woźniakowski tractability. Runge and Mergelyan approximation in the
complex plane are in SYNOPSIS40.

Local full-text sources consulted:

* [Trefethen, *Approximation Theory and Approximation Practice*, author manuscript](References/Trefethen2013ApproximationTheoryApproximationPractice-AuthorManuscript.pdf).
* [Bustamante, *Algebraic Approximation*](References/Bustamante2012AlgebraicApproximationGuidePastCurrentSolutions-BirkhaeuserFrontiersMath.pdf).
* [Braess, *Nonlinear Approximation Theory*](References/Braess1986NonlinearApproximationTheory-SpringerSerCompMath07.pdf).
* [Schumaker, *Spline Functions: Basic Theory*](References/Shumaker2007SplineFunctionsBasicTheory-CambridgeMathLibrary.pdf).
* [Iske, *Approximation Theory and Algorithms for Data Analysis*](References/Iske2018ApproximationTheoryAlgorithmsDataAnalysis-SpringerTAM68.pdf).
* [Pinkus, *n-Widths in Approximation Theory*](References/Pinkus1985NWidthsApproximationTheory-SpringerErgebMath3.pdf).
* [Temlyakov, *Sparse Approximation with Bases*](References/Temlyakov2015SparseApproximationWithBases-BirkhaeuserACMBIRK.pdf).
* [Baker–Graves-Morris, *Padé Approximants*, second edition](References/BakerGravesMorris1996PadéApproximants2ndEd-CambridgeEMA59.pdf).
* [Drmota–Tichy, *Sequences, Discrepancies and Applications*](References/DrmotaTichy1997SequencesDiscrepanciesApplications-SpringerLNM1651.pdf).
* [Pinkus, *Ridge Functions*](References/Pinkus2015RidgeFunctions-Cambridge.TractsMath205.pdf).
* [Dai–Xu, *Approximation Theory and Harmonic Analysis on Spheres and Balls*](References/DaiXu2013ApproximationTheoryHarmonicAnalysisSpheresBalls-SpringerSMM.pdf).
