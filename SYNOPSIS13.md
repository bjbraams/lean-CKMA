# Synopsis: Matrix analysis, operator monotonicity, and noncommutative inequalities

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects recurring content from Section 13 of
[CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md). It begins with
spectral comparison and unitarily invariant norms, then develops matrix order,
operator functions and means, trace inequalities, and the entropy consequences
for positive maps. The final statements record the basic infinite-dimensional
trace-ideal extensions.

Matrices are complex unless specified otherwise, $A^*$ is the adjoint, and
$A\geq0$ means positive semidefinite; $A>0$ means positive definite.
The **Loewner order** is $A\leq B$ when $B-A\geq0$. Hermitian eigenvalues
$\lambda_1(A)\geq\cdots\geq\lambda_n(A)$ and singular values
$s_1(A)\geq\cdots\geq s_n(A)\geq0$ are in decreasing order.
The operator norm is $\|A\|=s_1(A)$; the Schatten norm is
$\|A\|_p=(\operatorname{tr}|A|^p)^{1/p}$, $|A|=(A^*A)^{1/2}$.

Products of positive matrices need not be Hermitian or positive, so their
order cannot be compared directly without an appropriate symmetric placement
of factors. Congruence $A\mapsto C^*AC$ preserves positivity; similarity
$A\mapsto C^{-1}AC$ preserves eigenvalues but generally does not preserve
Hermitian structure. Trace cyclicity permits cyclic permutations of factors,
rather than arbitrary permutations. These distinctions account for the
sandwiches, congruences, and trace expressions in the statements below.

## Spectral structure and variational comparison

* **1. Spectral theorem.** A normal matrix is unitarily diagonalizable.
  Hermitian matrices have real eigenvalues, and positivity is equivalent to
  nonnegative eigenvalues. Spectral projections give
  $A=\sum_\lambda\lambda P_\lambda$ and the associated functional calculus.
* **2. Singular value decomposition.** Every rectangular matrix has
  $A=U\Sigma V^*$ with unitary $U,V$ and nonnegative diagonal entries of
  $\Sigma$. These entries are the square roots of the eigenvalues of $A^*A$,
  with zeros included according to dimension.
* **3. Polar decomposition.** $A=U|A|$, where $U$ is the uniquely determined
  partial isometry with initial space $(\ker A)^\perp$. For square invertible
  $A$, $U$ is unitary and unique.
* **4. Schur triangularization.** Every square complex matrix is unitarily
  similar to an upper triangular matrix with its eigenvalues on the diagonal,
  in any prescribed order. Normality forces this triangular matrix to be diagonal.
* **5. Courant–Fischer principle.** For Hermitian $A$,
  $$\lambda_k(A)=\max_{\dim V=k}\min_{\substack{x\in V\\|x|=1}}x^*Ax
    =\min_{\dim V=n-k+1}\max_{\substack{x\in V\\|x|=1}}x^*Ax.$$
* **6. Ky Fan maximum principle.**
  $\sum_{i=1}^k\lambda_i(A)=\max_{P}\operatorname{tr}(PA)$, over rank-$k$
  orthogonal projections. In particular, Loewner order implies ordered
  eigenvalue inequalities.
* **7. Cauchy interlacing.** Eigenvalues of a Hermitian compression to a
  codimension-one subspace interlace those of the original matrix. For a
  rank-$k$ perturbation this yields the corresponding index-shift bounds.
* **8. Weyl inequalities.** For Hermitian $A,B$,
  $\lambda_{i+j-1}(A+B)\leq\lambda_i(A)+\lambda_j(B)$ when $i+j-1\leq n$.
  In particular $|\lambda_i(A)-\lambda_i(B)|\leq\|A-B\|$.
* **9. Spectral majorization.** Lidskii's inequality gives
  $\lambda(A+B)\prec\lambda(A)+\lambda(B)$. The Schur–Horn theorem says
  that the diagonals of Hermitian matrices with eigenvalue vector $\lambda$
  are exactly the vectors majorized by $\lambda$.
* **10. Hoffman–Wielandt inequality.** For normal $A,B$, some matching of
  their eigenvalues satisfies
  $\sum_i|\lambda_i(A)-\lambda_{\pi(i)}(B)|^2\leq\|A-B\|_2^2$.
  For Hermitian matrices the decreasing-order matching works.

## Singular values, norms, and determinant inequalities

A norm is **unitarily invariant** if $\|UAV\|_{\!u}=\|A\|_{\!u}$ for unitary
$U,V$. Such norms correspond to symmetric gauge norms of the singular-value
vector. **Weak majorization** $a\prec_w b$ means all decreasing partial sums
of $a$ are bounded by those of $b$, without equality of total sums.

* **11. Von Neumann trace inequality.**
  $|\operatorname{tr}(A^*B)|\leq\sum_i s_i(A)s_i(B)$.
* **12. Ky Fan dominance.** $s(A)\prec_w s(B)$ exactly when
  $\|A\|_{\!u}\leq\|B\|_{\!u}$ for every unitarily invariant norm.
* **13. Mirsky perturbation inequality.** For every unitarily invariant norm,
  $\|\operatorname{diag}(s(A)-s(B))\|_{\!u}\leq\|A-B\|_{\!u}$.
  Rectangular versions use the corresponding singular-value gauge.
* **14. Schatten Hölder inequality.** If $1/r=1/p+1/q$ and
  $p,q,r\in[1,\infty]$, then $\|AB\|_r\leq\|A\|_p\|B\|_q$.
  In particular $|\operatorname{tr}(A^*B)|\leq\|A\|_p\|B\|_{p'}$.
* **15. Schatten triangle and duality.** Schatten $p$ norms are norms for
  $p\geq1$, and their dual norms under the trace pairing are Schatten $p'$
  norms, including operator/trace norm duality.
* **16. Eckart–Young–Mirsky theorem.** Truncating the SVD after $k$ terms
  gives a best rank-at-most-$k$ approximation in every unitarily invariant
  norm. Its operator error is $s_{k+1}$, and its squared Frobenius error is
  $\sum_{j>k}s_j^2$.
* **17. Multiplicative singular-value bounds.**
  $s_{i+j-1}(AB)\leq s_i(A)s_j(B)$ for $i+j-1\leq n$; more generally
  $\prod_{i=1}^ks_i(AB)\leq\prod_{i=1}^ks_i(A)s_i(B)$.
* **18. Hadamard determinant inequality.** For $A\geq0$,
  $\det A\leq\prod_i a_{ii}$. For $A>0$, equality holds exactly when $A$
  is diagonal in the given basis.
* **19. Fischer inequality.** For a positive semidefinite block matrix
  $A=\begin{pmatrix}B&C\\C^*&D\end{pmatrix}$,
  $\det A\leq\det B\det D$. In the positive definite case, equality means $C=0$.
* **20. Minkowski determinant inequality.** For positive semidefinite
  $n\times n$ matrices,
  $\det(A+B)^{1/n}\geq\det A^{1/n}+\det B^{1/n}$.
  For positive definite matrices, equality means proportionality.

## Positive blocks, products, and factorization

* **21. Schur complement.** If $B>0$, then
  $\begin{pmatrix}B&C\\C^*&D\end{pmatrix}\geq0$ exactly when
  $D-C^*B^{-1}C\geq0$, and its determinant is
  $\det B\det(D-C^*B^{-1}C)$. Singular-block versions require a range condition
  and the Moore–Penrose inverse.
* **22. Positive block factorization.** For $A,B\geq0$, the block
  $\begin{pmatrix}A&C\\C^*&B\end{pmatrix}$ is positive exactly when
  $C=A^{1/2}KB^{1/2}$ for a contraction $K$ of the compatible dimensions.
* **23. Schur product theorem.** The entrywise product of positive
  semidefinite matrices is positive semidefinite. If both factors are positive
  definite, so is their entrywise product.
* **24. Tensor products.** Positivity is preserved by tensor products;
  eigenvalues and singular values of $A\otimes B$ are the pairwise products.
  Thus $\|A\otimes B\|_p=\|A\|_p\|B\|_p$ for Schatten norms.
* **25. Douglas factorization.** For matrices $A,B$ with common target,
  $AA^*\leq BB^*$ exactly when $A=BC$ for a contraction $C$.
  This is the norm-controlled version of range inclusion.

## Operator monotonicity and convexity

A real function on an interval is **operator monotone** if $A\leq B$ implies
$f(A)\leq f(B)$ in every matrix dimension. It is **operator convex** if
$f((1-t)A+tB)\leq(1-t)f(A)+tf(B)$ in every dimension. Scalar monotonicity or
convexity alone does not imply these stronger properties.

* **26. Functional calculus and differentiation.** For Hermitian $A$,
  $f(A)=\sum_\lambda f(\lambda)P_\lambda$. If $f\in C^1$ near its spectrum,
  the Fréchet derivative in an eigenbasis is
  $(Df(A)[H])_{ij}=f^{[1]}(\lambda_i,\lambda_j)H_{ij}$, where the divided
  difference on the diagonal is $f'$. Holomorphic functional calculus extends
  this to general matrices through a resolvent contour integral.
* **27. Loewner–Heinz inequality.** $0\leq A\leq B$ implies $A^r\leq B^r$
  for $0\leq r\leq1$; $r=0$ is interpreted by the constant function one.
  The assertion fails in general for $r>1$.
* **28. Inverse order.** For positive definite matrices,
  $A\leq B$ exactly when $B^{-1}\leq A^{-1}$.
* **29. Logarithm.** The matrix logarithm is operator monotone and operator
  concave on the positive cone. The map $A\mapsto A^{-1}$ is operator convex
  there, while $A\mapsto A^r$ is operator concave for $0<r<1$.
* **30. Loewner's theorem.** A function on an open real interval is operator
  monotone exactly when it is the real restriction of an analytic Pick
  function with nonnegative imaginary part on the upper half-plane, extending
  analytically across that interval. Real constants are included.
* **31. Integral representation on the positive half-line.** A nonnegative
  operator-monotone function has a unique representation
  $$f(t)=a+bt+\int_{(0,\infty)}\frac{t}{t+\lambda}\,\nu(d\lambda),$$
  where $a,b\geq0$ and $\int(1+\lambda)^{-1}\nu(d\lambda)<\infty$.
  Conversely every such representation is nonnegative and operator monotone.
* **32. Bendat–Sherman criterion.** For continuous $f:[0,\infty)\to\mathbb R$
  with $f(0)=0$, operator convexity is equivalent to operator monotonicity of
  $t\mapsto f(t)/t$ on $(0,\infty)$.
* **33. Choi–Davis–Jensen inequality.** For a unital positive linear map and
  operator-convex $f$, $f(\Phi(A))\leq\Phi(f(A))$ when the spectra lie in
  its interval of definition.
* **34. Hansen–Pedersen inequality.** If $C$ is a contraction, $f$ is operator
  convex on an interval containing zero, and $f(0)\leq0$, then
  $f(C^*AC)\leq C^*f(A)C$, subject to the spectral-domain condition.
* **35. Davis compression criterion.** Operator convexity is equivalent to
  $f(PAP|_{\operatorname{ran}P})\leq Pf(A)P|_{\operatorname{ran}P}$ for all
  finite-dimensional Hermitian $A$ and orthogonal compressions with the relevant
  spectra in the interval.
* **36. Positive concavity and monotonicity.** A nonnegative function on
  $(0,\infty)$ is operator concave exactly when it is operator monotone.
  Nonnegativity on the whole half-line is part of this equivalence.

## Matrix means and geometry of the positive cone

For $A,B>0$ define the weighted **geometric mean**
$A\#_tB=A^{1/2}(A^{-1/2}BA^{-1/2})^tA^{1/2}$, $0\leq t\leq1$.
A **Kubo–Ando mean** is a normalized binary operation on positive operators
that is monotone, continuous under decreasing limits, and satisfies the
transformer inequality
$C^*(A\,\sigma\,B)C\leq(C^*AC)\,\sigma\,(C^*BC)$.
For invertible congruences this becomes equality, and normalization is
$I\,\sigma\,I=I$.

* **37. Geometric mean identities.** $A\#_tB=B\#_{1-t}A$, and simultaneous
  invertible congruence commutes with the mean. Inversion gives
  $(A\#_tB)^{-1}=A^{-1}\#_tB^{-1}$.
* **38. Arithmetic–geometric–harmonic order.**
  $$((1-t)A^{-1}+tB^{-1})^{-1}
    \leq A\#_tB\leq(1-t)A+tB.$$
  For $0<t<1$, equality in either comparison forces $A=B$.
* **39. Kubo–Ando representation.** Normalized operator means correspond
  bijectively to nonnegative operator-monotone $f$ with $f(1)=1$, through
  $A\,\sigma\,B=A^{1/2}f(A^{-1/2}BA^{-1/2})A^{1/2}$, extended to singular
  inputs by decreasing limits.
* **40. Joint concavity and positive maps.** Operator means are jointly
  concave. For a completely positive map with positive definite output inputs,
  $\Phi(A\# B)\leq\Phi(A)\#\Phi(B)$; semidefinite versions follow by limits.
* **41. Affine-invariant distance.** The positive definite cone with metric
  $g_A(H,K)=\operatorname{tr}(A^{-1}HA^{-1}K)$ has distance
  $d(A,B)=\|\log(A^{-1/2}BA^{-1/2})\|_2$. Its unique geodesic from $A$ to
  $B$ is $A\#_tB$.
* **42. Nonpositive curvature.** This metric satisfies
  $$d(C,A\#_tB)^2\leq(1-t)d(C,A)^2+td(C,B)^2-t(1-t)d(A,B)^2.$$
  In particular, squared-distance barycenters are unique for finitely
  supported probability distributions on the positive cone.

## Trace inequalities

* **43. Klein inequality.** For differentiable convex scalar $f$ and Hermitian
  $A,B$ with spectra in its interval,
  $\operatorname{tr}[f(A)-f(B)-(A-B)f'(B)]\geq0$.
  For strictly convex $f$, equality forces $A=B$.
* **44. Golden–Thompson inequality.** For Hermitian $H,K$,
  $\operatorname{tr}e^{H+K}\leq\operatorname{tr}(e^He^K)$.
* **45. Lieb concavity theorem.** For fixed $K$ and $0\leq t\leq1$,
  $(A,B)\mapsto\operatorname{tr}(K^*A^tKB^{1-t})$ is jointly concave on
  positive matrices, with endpoint zeroth powers interpreted as the identity.
* **46. Araki–Lieb–Thirring inequality.** For $A,B\geq0$, $r\geq1$, $q>0$,
  $$\operatorname{tr}(B^{1/2}AB^{1/2})^{rq}
    \leq\operatorname{tr}(B^{r/2}A^rB^{r/2})^q.$$
  For $0<r<1$ the inequality reverses.
* **47. Trace convexity.** Scalar convexity of $f$ implies convexity of
  $A\mapsto\operatorname{tr}f(A)$ on the Hermitian spectral domain. This
  requires less than operator convexity; for concave $f$ the direction reverses.
* **48. Peierls–Bogoliubov inequality.**
  $\log\operatorname{tr}e^{H+K}\geq\log\operatorname{tr}e^H+
  \operatorname{tr}(Ke^H)/\operatorname{tr}e^H$ for Hermitian $H,K$.
* **49. Gibbs variational principle.** For Hermitian $H$,
  $$\log\operatorname{tr}e^H
    =\max_{\rho\geq0,\operatorname{tr}\rho=1}
       \{\operatorname{tr}(\rho H)-\operatorname{tr}(\rho\log\rho)\}.$$
  The unique maximizer is $e^H/\operatorname{tr}e^H$.
* **50. Positivity of relative entropy.** For density matrices,
  $D(\rho\|\sigma)=\operatorname{tr}\rho(\log\rho-\log\sigma)\geq0$,
  with equality exactly for $\rho=\sigma$. It is infinite if
  $\operatorname{supp}\rho\not\subseteq\operatorname{supp}\sigma$;
  $0\log0=0$ on the supported subspace.

## Completely positive maps and quantum entropy

A map $\Phi$ is **completely positive** if $I_k\otimes\Phi$ preserves
positivity for every $k$. A **quantum channel** is a completely positive
trace-preserving map. The von Neumann entropy is
$S(\rho)=-\operatorname{tr}\rho\log\rho$, in natural-logarithm units.
Partial traces define reduced density matrices such as $\rho_{AB}$ and $\rho_B$.

* **51. Kraus representation.** $\Phi$ is completely positive exactly when
  $\Phi(A)=\sum_jV_jAV_j^*$. Trace preservation is
  $\sum_jV_j^*V_j=I$; unitality is $\sum_jV_jV_j^*=I$ on the output space.
* **52. Choi criterion.** Complete positivity is equivalent to positivity of
  $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$. Trace preservation is
  $\operatorname{tr}_{\mathrm{out}}J(\Phi)=I_{\mathrm{in}}$.
* **53. Stinespring dilation.** A unital completely positive map between
  matrix algebras has the representation $\Phi(A)=V^*(A\otimes I)V$ for
  an isometry $V$ into a larger tensor-product space.
* **54. Kadison–Schwarz inequality.** For a unital 2-positive map,
  $\Phi(A)^*\Phi(A)\leq\Phi(A^*A)$. Complete positivity is sufficient;
  ordinary positivity alone only gives the corresponding Hermitian-square statement.
* **55. Majorization by unitary mixing.** For density matrices of the same
  size, $\lambda(\rho)\prec\lambda(\sigma)$ exactly when $\rho$ is a convex
  combination of unitary conjugates of $\sigma$.
* **56. Data processing.** Every quantum channel satisfies
  $D(\Phi(\rho)\|\Phi(\sigma))\leq D(\rho\|\sigma)$.
  Partial trace is an important special case.
* **57. Joint convexity of relative entropy.**
  $D(\sum_jp_j\rho_j\|\sum_jp_j\sigma_j)
  \leq\sum_jp_jD(\rho_j\|\sigma_j)$ for probability weights.
* **58. Strong subadditivity.** For a tripartite state,
  $S(\rho_{ABC})+S(\rho_B)\leq S(\rho_{AB})+S(\rho_{BC})$.
  This is the nonnegativity of conditional mutual information.
* **59. Subadditivity and Araki–Lieb.**
  $|S(\rho_A)-S(\rho_B)|\leq S(\rho_{AB})\leq S(\rho_A)+S(\rho_B)$.
  Equality in the upper bound holds exactly for a product state.
* **60. Quantum Pinsker inequality.**
  $D(\rho\|\sigma)\geq\frac12\|\rho-\sigma\|_1^2$.
  The constant corresponds to natural logarithms and the unhalved trace norm.

## Trace ideals and determinants

For compact operators on a separable Hilbert space, singular values are defined
as eigenvalues of $|T|$ with multiplicity. The **Schatten ideal** $\mathcal S_p$
consists of those with $\sum_js_j(T)^p<\infty$; $\mathcal S_1$ is trace class
and $\mathcal S_2$ is Hilbert–Schmidt. Hölder and the ideal inequalities extend
to these classes.

* **61. Lidskii trace theorem.** For trace-class $T$, the eigenvalues, counted
  with algebraic multiplicity, are absolutely summable and
  $\operatorname{tr}T=\sum_j\lambda_j(T)$, even without self-adjointness.
* **62. Fredholm determinant.** For trace-class $T$,
  $\det(I+zT)=\prod_j(1+z\lambda_j(T))$ is entire, with zeros prescribed by
  nonzero eigenvalues. It is continuous in trace norm and multiplicative on
  products of identity-plus-trace-class operators. Near zero,
  $\log\det(I+zT)=\sum_{k\geq1}(-1)^{k+1}z^k\operatorname{tr}(T^k)/k$.
* **63. Regularized determinant.** For Hilbert–Schmidt $T$,
  $\det_2(I+T)=\prod_j(1+\lambda_j(T))e^{-\lambda_j(T)}$ is well defined
  and continuous in Hilbert–Schmidt norm. For $S,T\in\mathcal S_2$,
  $$\det_2((I+S)(I+T))
    =\det_2(I+S)\det_2(I+T)e^{-\operatorname{tr}(ST)}.$$
  The correction records why ordinary determinant multiplicativity changes
  after regularization.

## Perturbation and further trace and entropy inequalities

The Frobenius notation $\|\cdot\|_2$ below agrees with the Schatten convention
fixed above. A **spectral subspace** is a sum of eigenspaces, and a spectral
gap relevant to perturbation separates a selected cluster from the unwanted
part of the spectrum. The binary entropy is
$h_2(t)=-t\log t-(1-t)\log(1-t)$, with its continuous endpoint values.

* **64. Sylvester equation.** The equation $AX-XB=C$ has a unique solution
  for every $C$ exactly when $A$ and $B$ have disjoint spectra. If $A,B$ are
  Hermitian with spectral distance at least $\delta>0$, then
  $\|X\|_2\leq\|C\|_2/\delta$. Spectral separation thus converts a residual
  into a controlled correction.
* **65. Davis–Kahan residual bound.** Let $P$ be a spectral projection of
  Hermitian $A$, let $X$ have orthonormal columns, and let $H$ be Hermitian
  of the corresponding column dimension. If the spectrum of $H$ is separated
  by $\delta>0$ from that of $A$ on $\operatorname{ran}(I-P)$, then
  $$\|(I-P)X\|_2\leq\delta^{-1}\|AX-XH\|_2.$$
  This Frobenius form measures the angle of an approximate invariant subspace
  through its residual and the relevant gap.
* **66. Weyl eigenvalue–singular-value majorization.** Order the eigenvalues
  of any square matrix by decreasing modulus. Then
  $\prod_{j=1}^k|\lambda_j(A)|\leq\prod_{j=1}^ks_j(A)$ for every $k$,
  with equality of the full products. Consequently
  $\sum_j|\lambda_j(A)|^p\leq\sum_js_j(A)^p$ for $p>0$.
* **67. Log-determinant concavity.** On positive definite matrices,
  $A\mapsto\log\det A$ is strictly concave, and
  $$D\log\det A[H]=\operatorname{tr}(A^{-1}H),\qquad
    D^2\log\det A[H,H]=-\operatorname{tr}(A^{-1}HA^{-1}H).$$
  Strictness holds in every nonzero Hermitian direction. The negative
  log-determinant is therefore a convex barrier for the positive cone.
* **68. Lieb exponential concavity.** For fixed Hermitian $H$, the function
  $A\mapsto\operatorname{tr}\exp(H+\log A)$ is concave on $A>0$.
  This form connects the trace inequalities with matrix moment-generating
  functions, where noncommuting exponentials cannot be factored as scalar ones.
* **69. Heinz norm inequality.** For $A,B\geq0$, $0\leq t\leq1$, and every
  unitarily invariant norm,
  $$\|A^tXB^{1-t}+A^{1-t}XB^t\|_{\!u}\leq\|AX+XB\|_{\!u}.$$
  At $t=1/2$ it bounds a symmetrically weighted product by the corresponding
  arithmetic expression; endpoint powers use the identity convention.
* **70. Wigner–Yanase–Dyson skew information.** For a density matrix and
  Hermitian $H$, $0<t<1$,
  $$I_t(\rho,H)=\operatorname{tr}(\rho H^2)
     -\operatorname{tr}(\rho^tH\rho^{1-t}H)\geq0.$$
  It is convex in $\rho$ and vanishes exactly when $\rho$ commutes with $H$.
  Convexity follows from Lieb's joint concavity and distinguishes a
  noncommutative part of the variance.
* **71. Entropy continuity.** In dimension $n\geq2$, with
  $T=\frac12\|\rho-\sigma\|_1$,
  $$|S(\rho)-S(\sigma)|\leq T\log(n-1)+h_2(T).$$
  This sharp Fannes–Audenaert bound gives uniform continuity in each fixed
  dimension and exhibits its dependence on dimension explicitly.
* **72. Matrix arithmetic–geometric norm inequality.** For square matrices
  $A,B$ and every unitarily invariant norm,
  $2\|A^*B\|_{\!u}\leq\|AA^*+BB^*\|_{\!u}$.
  Unlike a scalar inequality of numbers, this statement is a comparison of
  singular-value norms, not a Loewner-order assertion about $A^*B$.
* **73. Convex spectral functions.** A symmetric convex function
  $\phi:\mathbb R^n\to\mathbb R$ induces a convex unitarily invariant function
  $A\mapsto\phi(\lambda(A))$ on Hermitian matrices. This extends trace
  convexity beyond separable sums of scalar functions and is the basic
  bridge from ordinary convexity to spectral optimization.
* **74. Entropy of mixtures.** For density matrices and probability weights,
  $$\sum_jp_jS(\rho_j)\leq S(\sum_jp_j\rho_j)
       \leq-\sum_jp_j\log p_j+\sum_jp_jS(\rho_j).$$
  Moreover $0\leq S(\rho)\leq\log n$, with equality at the lower endpoint
  exactly for rank-one states and at the upper endpoint exactly for $I/n$.
  Mixing can add at most the classical entropy of the mixing variable.

## Reference guide

Bhatia, *Matrix Analysis*, Chapters I–V, supplies spectral comparison,
majorization, norms, and operator functions; its later chapters develop
perturbations and trace inequalities. Horn–Johnson gives an independent large
reference for these finite-dimensional results. Bhatia, *Positive Definite
Matrices*, develops means and the positive-cone geometry. Simon's *Loewner's
Theorem*, alongside Donoghue, supplies the analytic and integral-representation
view of operator monotonicity.

Hiai–Petz and Carlen connect operator convexity and trace inequalities with
relative entropy. Watrous provides a systematic finite-dimensional treatment
of completely positive maps and entropy inequalities; Bengtsson–Życzkowski
and Heinosaari–Ziman supply complementary convex and geometric accounts.
Simon, *Trace Ideals*, and Gohberg–Krein supply the trace-ideal and determinant
endpoint, which is developed further in the operator-theory sections.

Local source anchors:

- [Bhatia, *Matrix Analysis*](References/Bhatia1997MatrixAnalysis-SpringerGTM169.pdf).
- [Horn–Johnson, *Matrix Analysis*](References/HornJohnson1985MatrixAnalysis-Cambridge.pdf).
- [Horn–Johnson, *Topics in Matrix Analysis*](References/HornJohnson1991TopicsInMatrixAnalysis-Cambridge.pdf).
- [Simon, *Loewner's Theorem*](References/Simon2019LoewnersTheoremMonotoneMatrixFunctions-SpringerGL354.pdf).
- [Watrous, *The Theory of Quantum Information*](References/Watrous2018TheoryQuantumInformation-Cambridge.pdf).
