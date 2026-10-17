# Synopsis: Orthogonal polynomials, moment problems, and spectral recurrences

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects recurring material from Section 48 of
[CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md).
It develops the dictionary between polynomial orthogonality, three-term
recurrences, quadrature, positive moment functionals, and spectral measures,
followed by unit-circle theory and the principal asymptotic results.
Classical special-function identities are treated further in Section 49;
the integrable and Riemann–Hilbert continuations belong principally to Section 51.

For real-line orthogonality, $\mu$ is a positive Borel measure with infinite
support and finite moments of all orders. Write $p_n(x)=\kappa_nx^n+\cdots$,
$\kappa_n>0$, for orthonormal polynomials, and $P_n=p_n/\kappa_n$ for
monic ones. Normalize $\mu(\mathbb R)=1$ when discussing its Jacobi
matrix. Put $K_n(x,y)=\sum_{j=0}^np_j(x)\overline{p_j(y)}$.

## Orthogonality, recurrence, and zeros

* **1. Gram–Schmidt construction.** Positive definiteness of all
  moment matrices gives unique orthonormal polynomials with positive
  leading coefficient and unique monic orthogonal polynomials.
* **2. Extremal property.** $P_n$ uniquely minimizes the $L^2(\mu)$
  norm among monic degree-$n$ polynomials. Its norm is $1/\kappa_n$.
* **3. Three-term recurrence.**
  $xp_n=a_{n+1}p_{n+1}+b_np_n+a_np_{n-1}$, where
  $a_{n+1}>0$, $b_n\in\mathbb R$, $a_0=0$.
  In particular $a_{n+1}=\kappa_n/\kappa_{n+1}$.
* **4. Favard's theorem.** Conversely every such real recurrence
  with positive off-diagonal coefficients has a positive orthogonality
  measure with infinite support and all finite moments. The recurrence
  and total mass fix the moments, but need not fix the measure.
* **5. Hankel determinants.** If
  $D_n=\det[s_{j+k}]_{j,k=0}^{n-1}$, $D_0=1$, then
  $\|P_n\|^2=D_{n+1}/D_n$. Determinant formulas recover $P_n$
  and the recurrence coefficients from the moments.
* **6. Real and simple zeros.** The $n$ zeros of $p_n$ are
  simple and lie in the interior of the convex hull of $\operatorname{supp}\mu$.
* **7. Interlacing.** Zeros of $p_n$ and $p_{n+1}$ strictly
  interlace. Each open gap of the support contains at most one
  zero of $p_n$.
* **8. Christoffel–Darboux formula.**
  $K_n(x,y)=a_{n+1}[p_{n+1}(x)p_n(y)-p_n(x)p_{n+1}(y)]/(x-y)$
  for real distinct $x,y$; the diagonal value is its derivative limit.
* **9. Reproducing kernel.** $K_n$ reproduces polynomials of degree
  at most $n$ in $L^2(\mu)$ and is independent of the chosen
  orthonormal basis of that space.
* **10. Christoffel variational principle.**
  $\lambda_n(x)=1/K_n(x,x)=\min\{\int|Q|^2d\mu:
  \deg Q\leq n,\ Q(x)=1\}$.
* **11. Classical weights.** Jacobi weights
  $(1-x)^\alpha(1+x)^\beta$ on $(-1,1)$, $\alpha,\beta>-1$,
  Laguerre weights $x^\alpha e^{-x}$, $\alpha>-1$, and Hermite
  weight $e^{-x^2}$ produce positive orthogonal systems with complete
  polynomial spans in their $L^2$ spaces.
* **12. Rodrigues structure.** For the classical weights, differentiation
  of a weight times a power of the Pearson polynomial gives the
  orthogonal polynomial. Integration by parts proves orthogonality,
  provided the parameter restrictions make the endpoint terms vanish.
* **13. Bochner classification.** Positive real-line orthogonal
  systems whose degree-$n$ polynomials are eigenfunctions of one
  second-order differential operator with polynomial coefficients of
  degrees at most two and one are, under the nondegenerate classical
  hypotheses, Jacobi, Laguerre, or Hermite systems up to affine changes.

## Gaussian quadrature and Cauchy transforms

* **14. Gauss quadrature.** The zeros $x_1,\ldots,x_n$ of $p_n$
  support a unique quadrature rule exact on $\mathcal P_{2n-1}$.
  Its weights are positive and equal $1/K_{n-1}(x_j,x_j)$.
* **15. Maximal exactness.** No $n$-node rule with real nodes can
  integrate every polynomial of degree $2n$ for an infinite-support
  positive measure. The squared node polynomial gives the obstruction.
* **16. Gauss error formula.** For compact interval support and
  $f\in C^{2n}$, the error is
  $f^{(2n)}(\xi)\|P_n\|^2/(2n)!$ for an intervening $\xi$.
* **17. Radau and Lobatto rules.** Prescribing one endpoint leaves
  maximal degree $2n-2$ for $n$ nodes; prescribing both endpoints
  leaves $2n-3$. For a positive measure on a nondegenerate compact
  interval, the corresponding rules have positive weights.
* **18. Markov–Stieltjes inequalities.** For increasing Gauss nodes,
  $\sum_{j<k}\lambda_j\leq\mu(( -\infty,x_k))
  \leq\mu(( -\infty,x_k])\leq\sum_{j\leq k}\lambda_j$.
  These bounds compare cumulative mass with quadrature weights.
* **19. Markov convergence.** For compact support, the Gauss
  quadrature measures converge weakly to $\mu$. Their Cauchy
  transforms converge locally uniformly off the supporting interval.
* **20. Padé correspondence.** For
  $C(z)=\int(z-x)^{-1}d\mu(x)$, the $[n-1/n]$ Padé
  approximant at infinity is the Gauss Cauchy transform
  $\sum_j\lambda_j/(z-x_j)$. It matches the first $2n$ moments.
* **21. Christoffel modification.** If $a$ lies to the left of the
  support, the monic polynomials for $(x-a)d\mu$ are
  $[P_{n+1}(x)-P_{n+1}(a)P_n(x)/P_n(a)]/(x-a)$.
  This transforms recurrence coefficients by factorization of the Jacobi matrix.

## Jacobi operators and spectral measures

The half-line **Jacobi expression** on $\ell^2(\mathbb N_0)$ is
$(Ju)_n=a_{n+1}u_{n+1}+b_nu_n+a_nu_{n-1}$.
The minimal operator starts on finitely supported vectors.
For a self-adjoint realization set
$m(z)=\langle\delta_0,(J-z)^{-1}\delta_0\rangle$.

* **22. Bounded Jacobi correspondence.** Bounded real $b_n$ and
  bounded positive $a_n$ define a bounded self-adjoint operator;
  $\|J\|\leq\sup|b_n|+2\sup a_n$.
  Conversely boundedness bounds every matrix coefficient.
* **23. Spectral representation.** In the bounded case, $\delta_0$
  is cyclic and $\delta_n\mapsto p_n$ gives a unitary map onto
  $L^2(\mu)$ under which $J$ becomes multiplication by $x$.
  Its spectrum is $\operatorname{supp}\mu$.
* **24. Finite sections and zeros.** The characteristic polynomial
  of the upper-left $n\times n$ Jacobi block is $P_n$.
  Its spectral weights at $\delta_0$ are precisely the Gauss weights.
* **25. Weyl-function representation.**
  $m(z)=\int(x-z)^{-1}d\mu(x)$ has positive imaginary part in
  the upper half-plane. Stieltjes inversion recovers $\mu$ from
  its boundary imaginary parts, including its atoms.
* **26. Continued fraction.** If $m_1$ is the Weyl function of
  the once-stripped Jacobi operator, then
  $m(z)=[b_0-z-a_1^2m_1(z)]^{-1}$.
  Iteration gives the Jacobi continued fraction and finite-section approximants.
* **27. Spectral uniqueness.** A probability spectral measure with
  compact infinite support determines all Jacobi coefficients uniquely.
  Equivalently, the full Weyl function determines the half-line operator.
* **28. Limit-point/limit-circle alternative.** The unbounded minimal
  Jacobi operator has deficiency indices $(0,0)$ or $(1,1)$.
  The first case gives essential self-adjointness; the second requires
  a boundary condition at infinity.
* **29. Determinacy correspondence.** The Hamburger moment problem
  associated with the recurrence is determinate exactly when the
  minimal Jacobi operator is essentially self-adjoint.
* **30. Jacobi Carleman criterion.** $\sum_{n\geq1}a_n^{-1}=\infty$
  implies essential self-adjointness and determinacy.

## Moment existence, uniqueness, and positivity

For a sequence $s=(s_\alpha)$ define the **moment functional**
$L(x^\alpha)=s_\alpha$. A representing measure on closed $K$ satisfies
$L(p)=\int_Kp\,d\mu$. Moment matrices are indexed by monomials;
localizing matrices represent $L(gp\bar q)$.

* **31. Hamburger theorem.** A real sequence $(s_n)_{n\geq0}$
  is a moment sequence on $\mathbb R$ exactly when every Hankel
  matrix $[s_{j+k}]$ is positive semidefinite.
* **32. Stieltjes theorem.** It is a moment sequence on $[0,\infty)$
  exactly when both $[s_{j+k}]$ and $[s_{j+k+1}]$ are positive
  semidefinite in every finite size.
* **33. Hausdorff theorem.** It is a moment sequence on $[0,1]$
  exactly when $(-1)^k\Delta^ks_n\geq0$ for all $n,k\geq0$.
  The representing measure is then unique.
* **34. Compact-support determinacy.** Measures of compact support
  are determined by their moments. Bounds $s_{2n}\leq CR^{2n}$
  force every representing measure to be supported in $[-R,R]$.
* **35. Moment Carleman criteria.**
  $\sum_ns_{2n}^{-1/(2n)}=\infty$ gives Hamburger determinacy;
  $\sum_ns_n^{-1/(2n)}=\infty$ gives Stieltjes determinacy when
  a Stieltjes representing measure exists.
* **36. Krein indeterminacy criterion.** If $w\geq0$ on
  $\mathbb R$, $w(x)dx$ has all moments, and
  $\int\log w(x)/(1+x^2)dx>-\infty$, its Hamburger moment
  problem is indeterminate.
* **37. Explicit lognormal indeterminacy.** The distinct densities
  $e^{-(\log x)^2/2}(1+\varepsilon\sin(2\pi\log x))/(x\sqrt{2\pi})$,
  $x>0$, $|\varepsilon|\leq1$, all have moments $s_n=e^{n^2/2}$.
* **38. Polynomial density distinction.** Determinacy implies
  polynomial density in $L^2(\mu)$. In an indeterminate Hamburger
  problem some extremal representing measures also have dense
  polynomials, so density alone is not a determinacy criterion.
* **39. Nevanlinna parametrization.** In an indeterminate Hamburger
  problem, all Cauchy transforms are described by a fractional-linear
  transformation of a Pick-function parameter using four entire
  functions determined by the recurrence. Real constant parameters
  give the canonical self-adjoint-extension measures.
* **40. Haviland's theorem.** A linear functional on real
  multivariable polynomials has a representing measure on closed $K$
  exactly when it is nonnegative on every polynomial nonnegative on $K$.
* **41. Multivariate Carleman criterion.** Positivity on squares
  together with the Carleman divergence condition in each coordinate
  yields a unique representing measure on $\mathbb R^d$.
* **42. Schmüdgen Positivstellensatz.** If
  $K=\{g_1\geq0,\ldots,g_m\geq0\}$ is compact, every polynomial
  strictly positive on $K$ is $\sum_{\nu\in\{0,1\}^m}\sigma_\nu g^\nu$,
  with each $\sigma_\nu$ a sum of squares.
* **43. Putinar Positivstellensatz.** If the quadratic module
  $\{\sigma_0+\sum_j\sigma_jg_j\}$ is Archimedean, meaning it
  contains $N-\sum x_i^2$ for some $N$, every strictly positive
  polynomial on $K$ belongs to that module. A functional positive
  on the module has a representing measure on $K$.
* **44. Tchakaloff theorem.** A positive measure with the required
  finite moments has a positive atomic quadrature measure reproducing
  all polynomials of degree at most $r$, with at most
  $\dim\mathcal P_r(\mathbb R^d)$ atoms chosen in its support.
* **45. Flat moment theorem.** If a positive semidefinite truncated
  moment matrix $M_n$ satisfies
  $\operatorname{rank}M_n=\operatorname{rank}M_{n-1}=r$,
  the data have a unique representing measure, with exactly $r$ atoms.
  For constrained supports, positive localizing matrices enforce the
  corresponding support conditions in the flat-extension formulation.

## Orthogonal polynomials on the unit circle

Here $\mu$ is a probability on $\mathbb T$ with infinite support.
Write $\Phi_n$ for its monic orthogonal polynomials,
$\Phi_n^*(z)=z^n\overline{\Phi_n(1/\bar z)}$, and
$\alpha_n=-\overline{\Phi_{n+1}(0)}$.

* **46. Szegő recurrence.**
  $\Phi_{n+1}=z\Phi_n-\bar\alpha_n\Phi_n^*$ and
  $\Phi_{n+1}^*=\Phi_n^*-\alpha_nz\Phi_n$, with $|\alpha_n|<1$.
* **47. Norm product.**
  $\|\Phi_n\|^2=\prod_{j=0}^{n-1}(1-|\alpha_j|^2)$.
  All zeros of $\Phi_n$ lie strictly inside the disk.
* **48. Verblunsky theorem.** Infinite-support circle probabilities
  correspond bijectively to arbitrary sequences $\alpha_n\in\mathbb D$.
  Finite support corresponds to termination with a last coefficient on $\mathbb T$.
* **49. Carathéodory–Schur dictionary.**
  $F(z)=\int(\zeta+z)/(\zeta-z)d\mu(\zeta)$ has positive
  real part and $F(0)=1$; $s(z)=(F(z)-1)/(z(F(z)+1))$
  is Schur. The Schur algorithm successively extracts exactly the
  Verblunsky coefficients.
* **50. Unit-circle Christoffel–Darboux formula.** For orthonormal
  $\varphi_n$, $\sum_{j=0}^n\varphi_j(z)\overline{\varphi_j(w)}$
  equals
  $[\varphi_{n+1}^*(z)\overline{\varphi_{n+1}^*(w)}-
  \varphi_{n+1}(z)\overline{\varphi_{n+1}(w)}]/(1-z\bar w)$.
* **51. Paraorthogonal polynomials.**
  $z\Phi_{n-1}(z)-\bar\beta\Phi_{n-1}^*(z)$, $|\beta|=1$,
  has $n$ distinct zeros on the circle. They give a positive
  $n$-node quadrature rule exact on Laurent powers $|k|\leq n-1$.
* **52. CMV representation.** Multiplication by $z$ in the
  orthonormal Laurent-polynomial basis is a five-diagonal unitary
  CMV matrix, factored into alternating $2\times2$ unitary blocks
  determined by $\alpha_n$. Its spectral measure at the first basis
  vector is $\mu$. See [Simon's survey](https://arxiv.org/pdf/math/0502485), Section 5.
* **53. Szegő theorem.** For $d\mu=w\,dm+d\mu_s$,
  $\prod_{n\geq0}(1-|\alpha_n|^2)=\exp\int\log w\,dm$.
  Thus finite logarithmic integral is equivalent to $\sum|\alpha_n|^2<\infty$.
* **54. Szegő function.** If that integral is finite,
  $D(z)=\exp[\frac12\int(\zeta+z)/(\zeta-z)\log w\,dm]$
  is outer, $|D^*|^2=w$ almost everywhere, and
  $D(0)^2=\exp\int\log w\,dm$.
* **55. Toeplitz determinants.**
  $D_n(w)=\det[\widehat w(j-k)]_{j,k=0}^{n-1}$ equals the
  product of the first $n$ squared monic orthogonal norms.
  Thus norm asymptotics and determinant asymptotics are equivalent data.
* **56. Strong Szegő theorem.** For a positive smooth circle
  weight $w=e^L$,
  $D_n(w)e^{-n\widehat L(0)}\to
  \exp\sum_{k\geq1}k|\widehat L(k)|^2$.
  The Sobolev-$1/2$ condition on $L$ is the natural sharp finite-constant condition.
* **57. Rakhmanov's theorem.** If $w>0$ almost everywhere on
  the whole circle, then $\alpha_n\to0$, even with an additional
  singular part of $\mu$.

## Asymptotics and potential theory

For compact nonpolar real support $K$, call $\mu$ **regular** if
$\kappa_n^{1/n}\to\operatorname{cap}(K)^{-1}$.
Let $\omega_K$ be its logarithmic equilibrium measure and $g_K$
the exterior Green function with pole at infinity.

* **58. Extremal norm regularity.** Regularity is equivalently
  $\|P_n\|_{L^2(\mu)}^{1/n}\to\operatorname{cap}(K)$.
  It expresses asymptotic extremality of monic orthogonal polynomials.
* **59. Equilibrium zero distribution.** For regular $\mu$ on a
  compact subset of $\mathbb R$, the normalized zero-counting
  measures of $p_n$ converge weakly to $\omega_K$.
* **60. Exterior root asymptotics.** For regular $\mu$,
  $|p_n(z)|^{1/n}\to e^{g_K(z,\infty)}$ locally uniformly
  outside the convex hull of $K$.
* **61. Positivity implies interval regularity.** If $\mu$ is
  supported on $[-1,1]$ and its density is positive almost everywhere
  there, it is regular. Its zero measures tend to
  $dx/(\pi\sqrt{1-x^2})$.
* **62. Real-line Rakhmanov theorem.** For probability measures
  supported on $[-2,2]$ with density positive almost everywhere,
  $a_n\to1$ and $b_n\to0$.
* **63. Szegő exterior asymptotics.** For $d\mu=w(x)dx$ on
  $[-1,1]$, if the weight satisfies
  $\int_{-1}^1\log w(x)/\sqrt{1-x^2}\,dx>-\infty$,
  then $p_n(z)/(z+\sqrt{z^2-1})^n$ converges locally uniformly
  off $[-1,1]$ to a nonvanishing analytic factor determined by
  the Szegő function, with the branch asymptotic to $2z$.
* **64. Christoffel bulk asymptotics.** For a continuous positive
  density $w$ on $[-1,1]$,
  $n\lambda_{n-1}(x)\to\pi w(x)\sqrt{1-x^2}$ locally uniformly
  in the open interval.
* **65. Mehler–Heine limit.** For Jacobi parameters $\alpha,\beta>-1$,
  $n^{-\alpha}P_n^{(\alpha,\beta)}(\cos(z/n))\to
  (z/2)^{-\alpha}J_\alpha(z)$ locally uniformly in complex $z$,
  with the right side interpreted by its entire even series.
* **66. Riemann–Hilbert characterization.** For positive smooth
  rapidly decreasing $w$ on $\mathbb R$, the unique normalized
  $2\times2$ problem with jump
  $Y_+=Y_-\begin{pmatrix}1&w\\0&1\end{pmatrix}$ and
  $Y=(I+O(z^{-1}))\operatorname{diag}(z^n,z^{-n})$
  has $Y_{11}=P_n$; the other entries are adjacent polynomials
  and their Cauchy transforms. This gives the analytic route to strong asymptotics.

## Multivariate structure and modified measures

* **67. Multivariate orthogonal decomposition.** With positive
  polynomial inner product in $d$ variables, the polynomials of
  exact orthogonal degree $n$ have dimension $\binom{n+d-1}{d-1}$.
  Degree-at-most-$n$ spaces split orthogonally into these layers.
* **68. Matrix three-term relations.** Multiplication by each
  coordinate connects only the degree layers $n-1,n,n+1$.
  The matrix coefficients obey compatibility relations because coordinate
  multiplication operators commute.
* **69. Product measures.** Tensor products of one-variable
  orthogonal polynomials form a complete orthogonal system whenever
  the component polynomial systems are complete. Total-degree
  truncation selects the corresponding tensor multiindices.
* **70. Gaussian cubature obstruction.** A degree-$(2n-1)$
  cubature rule with the minimal $\dim\mathcal P_{n-1}$ nodes
  requires common zeros of all degree-$n$ orthogonal polynomials.
  In the positive definite setting these common zeros give Gaussian
  cubature when their number is exactly that minimum.
* **71. Finite-rank moment functionals.** A positive full moment
  matrix of finite rank $r$ has a unique $r$-atomic representing
  measure. Its kernel is the ideal of polynomials vanishing at those atoms.
* **72. Positivity versus sums of squares.** In several variables,
  nonnegative polynomials need not be sums of polynomial squares.
  Consequently positivity of multivariate moment matrices alone does
  not imply a representing measure; Haviland positivity or additional
  moment, growth, or support hypotheses are needed.

## Reference guide

Szegő, Chihara, Ismail, Freud, and Gautschi share the recurrence,
zero, kernel, and quadrature core. Akhiezer, Shohat–Tamarkin,
Krein–Nudel'man, and Schmüdgen develop existence and determinacy;
Schmüdgen, Marshall, and Lasserre supply the multivariate positivity
continuation. Simon and the unit-circle chapters of Ismail organize
OPUC and spectral recurrences. Stahl–Totik, Saff–Totik, Levin–Lubinsky,
and Deift supply the potential and asymptotic theories. Dunkl–Xu
explains the matrix and cubature structure in several variables.
Integrable deformations and detailed classifications of hypergeometric
families are treated in the adjacent synopses.

Local full-text sources consulted:

* [Ismail, *Classical and Quantum Orthogonal Polynomials in One Variable*](References/Ismail2005ClassicalQuantumOrthogonalPolynomialsOneVariable-CambridgeEMA98.pdf).
* [Gautschi, *Orthogonal Polynomials: Computation and Approximation*](References/Gautschi2004OrthogonalPolynomialsComputationApproximation-OxfordUP.pdf).
* [Schmüdgen, *The Moment Problem*](References/Schmuedgen2017MomentProblem-SpringerGTM277.pdf).
* [Stahl–Totik, *General Orthogonal Polynomials*](References/StahlTotik1992GeneralOrthogonalPolynomials-CambridgeEMA43.pdf).
* [Levin–Lubinsky, *Orthogonal Polynomials for Exponential Weights*](References/LevinLubinsky2001OrthogonalPolynomialsExponentialWeights-Springer.CMS.pdf).
* [Dunkl–Xu, *Orthogonal Polynomials of Several Variables*, second edition](References/DunklXu2014OrthogonalPolynomialsSeveralVariables2ndEd-CambridgeEMA155.pdf).

Simon's linked survey was used for the CMV representation alongside
the unit-circle textbook material. The local Chihara copy is image-based
and was not used as searchable full text.
