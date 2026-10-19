# Synopsis: Bounded operator theory, spectra, and functional models

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-21);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects the recurring graduate and beginning research core of
Section 21 of [CKMA-bib.md](CKMA-bib.md#ckma-21).
It develops joint, Weyl, and Browder spectra, Fredholm theory, compact
ideals, contractions, dilations, and functional models, the Toeplitz
extension, reproducing kernels, the first structural results on invariant
subspaces and linear dynamics, and operators in Krein and Pontryagin
spaces. General unbounded operators and operator algebras are treated in
Sections 22 and 23.

Unless indicated otherwise, $H$ is a nonzero complex Hilbert space,
$\mathcal B(H)$ denotes its bounded operators, and inner products are linear
in the first variable. The **spectrum** is
$\sigma(T)=\{z:zI-T\text{ is not invertible}\}$, the **resolvent** is
$R(z,T)=(zI-T)^{-1}$, and $r(T)=\max_{z\in\sigma(T)}|z|$.
A subspace is **invariant** if $TM\subset M$, and **reducing** if it is
invariant for both $T$ and $T^*$.

## Operator topologies, spectra, and factorization

The **strong operator topology** is pointwise norm convergence; the **weak
operator topology** is pointwise convergence of matrix coefficients.
An operator is **normal** if $T^*T=TT^*$, **hyponormal** if
$T^*T\geq TT^*$, and a **contraction** if $\|T\|\leq1$.
The adjoint and closed-range identities, polar decomposition, and the
bounded spectral theorem for normal operators are in SYNOPSIS15, items 46,
64, and 65.

* **3. Douglas factorization theorem.** For $A:K\to H$ and $B:L\to H$,
  $\operatorname{ran}A\subset\operatorname{ran}B$ exactly when
  $AA^*\leq cBB^*$ for some $c$, and exactly when $A=BC$ for some
  bounded $C:K\to L$. The least such $c$ is the square of the least
  possible norm of $C$.
* **4. Bounded convergence and multiplication.** A strongly or weakly
  convergent sequence of operators is uniformly norm bounded. Multiplication
  is jointly strongly continuous on norm-bounded sets, while adjoints are
  weakly continuous; adjoints need not preserve strong convergence.
* **5. Spectral radius and calculus.** The spectrum is nonempty compact,
  $r(T)=\lim_n\|T^n\|^{1/n}$, and the holomorphic functional calculus
  satisfies $\sigma(f(T))=f(\sigma(T))$.
* **7. Fuglede–Putnam theorem.** If $N$ and $M$ are normal and $NX=XM$
  for a bounded $X$, then $N^*X=XM^*$. In particular an operator commuting
  with a normal operator commutes with its adjoint and with all its Borel
  functions.
* **8. Approximate eigenvectors.** Every boundary point of the spectrum
  of a bounded operator on a complex Banach space is an approximate
  eigenvalue: some unit vectors $x_n$ satisfy $(T-zI)x_n\to0$.
  For normal operators this holds at every spectral point.
* **9. Numerical range.** $W(T)=\{\langle Tx,x\rangle:\|x\|=1\}$ is convex
  (Toeplitz–Hausdorff), $\sigma(T)\subset\overline{W(T)}$, and the numerical
  radius $w(T)$ satisfies $w(T)\leq\|T\|\leq2w(T)$. For normal $T$,
  $\overline{W(T)}$ is the convex hull of $\sigma(T)$ and $w(T)=\|T\|$.
* **10. Spectral decomposition.** Disjoint compact spectral components
  yield commuting Riesz projections
  $P=(2\pi i)^{-1}\int_\Gamma(zI-T)^{-1}\,dz$ and invariant direct
  sums on which the restrictions have the corresponding spectra.
* **67. Taylor joint spectrum.** For a commuting tuple
  $T=(T_1,\ldots,T_n)$ on a complex Banach space $X\neq0$, $\lambda\in\mathbb C^n$
  lies outside the **Taylor spectrum** $\sigma_T(T)$ when the Koszul complex
  of $T-\lambda=(T_1-\lambda_1,\ldots,T_n-\lambda_n)$ on $X$ is exact.
  Then $\sigma_T(T)$ is nonempty and compact, equals $\sigma(T_1)$ for
  $n=1$, and is contained in the joint spectrum of $T$ in any commutative
  Banach subalgebra of $\mathcal B(X)$ containing the $T_j$ (in particular
  in $\prod_j\sigma(T_j)$). It has the projection property
  $\pi(\sigma_T(T_1,\ldots,T_n))=\sigma_T(T_1,\ldots,T_{n-1})$, and there
  is a holomorphic functional calculus on neighbourhoods of $\sigma_T(T)$
  with the spectral mapping property $\sigma_T(f(T))=f(\sigma_T(T))$ for
  holomorphic $f:U\to\mathbb C^m$ (Taylor).

## Fredholm operators and essential spectra

A bounded map $T:X\to Y$ between Banach spaces is **Fredholm** if its
range is closed and both $\ker T$ and $Y/\operatorname{ran}T$ are finite
dimensional. Its **index** is
$\operatorname{ind}T=\dim\ker T-\dim(Y/\operatorname{ran}T)$.
The **Calkin algebra** is $\mathcal B(H)/\mathcal K(H)$, where
$\mathcal K(H)$ is the compact ideal; the **essential spectrum** here means
$\sigma_{\rm ess}(T)=\{z:T-zI\text{ is not Fredholm}\}$.
The Fredholm alternative for $I-K$ is SYNOPSIS15, item 53, and Weyl's
criterion for the essential spectrum of self-adjoint operators is
SYNOPSIS22, item 29.

* **11. Atkinson theorem.** $T$ is Fredholm exactly when it has a bounded
  inverse modulo compact operators. For endomorphisms this says that its
  image in the Calkin algebra is invertible. Finite codimension of the
  range forces the range to be closed.
* **12. Stability and local constancy.** Fredholm operators form an open
  subset of $\mathcal L(X,Y)$, and their index is locally constant.
  Compact perturbations preserve Fredholmness and the index.
* **13. Product and adjoint rules.** Products of Fredholm operators are
  Fredholm, with $\operatorname{ind}(ST)=\operatorname{ind}S+
  \operatorname{ind}T$. For the Hilbert-space or Banach-space adjoint,
  $\operatorname{ind}T^*=-\operatorname{ind}T$.
* **15. Analytic Fredholm theorem.** If $K(z)$ is a norm-holomorphic
  compact-operator family on a connected plane domain, then either
  $I-K(z)$ is nowhere invertible or its inverse is meromorphic, with
  discrete poles and finite-rank principal parts. One invertible parameter
  rules out the first alternative.
* **16. Essential spectral invariance.** Compact perturbations preserve
  $\sigma_{\rm ess}$. For bounded self-adjoint $T$, the complement of
  its essential spectrum in its spectrum consists exactly of isolated
  eigenvalues of finite multiplicity.
* **18. Weyl–von Neumann–Berg and Brown–Douglas–Fillmore.** On separable
  $H$, every normal operator is the sum of a diagonal normal operator and a
  compact operator of arbitrarily small norm (Hilbert–Schmidt for
  self-adjoint operators); two normal operators are unitarily equivalent
  modulo compacts exactly when their essential spectra agree. For
  essentially normal operators ($T^*T-TT^*$ compact), unitary equivalence
  modulo compacts holds exactly when the essential spectra agree and
  $\operatorname{ind}(T-\lambda)$ agrees off the essential spectrum (BDF).
* **68. Weyl and Browder spectra.** For a bounded operator $T$ on a
  complex Banach space, the **Weyl spectrum** $\sigma_w(T)$ is the set of
  $\lambda$ for which $T-\lambda I$ is not Fredholm of index zero, and the
  **Browder spectrum** $\sigma_b(T)$ the set for which $T-\lambda I$ is not
  Fredholm with finite ascent and descent. Then
  $\sigma_{\rm ess}(T)\subset\sigma_w(T)\subset\sigma_b(T)\subset\sigma(T)$,
  $\sigma_w(T)=\bigcap_{K\text{ compact}}\sigma(T+K)$ (Schechter), and
  $\sigma_b(T)=\sigma_w(T)\cup\operatorname{acc}\sigma(T)$, where
  $\operatorname{acc}$ denotes the set of accumulation points; the
  complement $\sigma(T)\setminus\sigma_b(T)$ consists of the isolated
  eigenvalues with finite-rank Riesz projections. Both $\sigma_w$ and
  $\sigma_b$ are invariant under compact perturbation (for $\sigma_b$, by
  commuting compact perturbation).
* **69. Weyl's theorem.** $T$ **satisfies Weyl's theorem** if
  $\sigma(T)\setminus\sigma_w(T)$ is exactly the set of isolated
  eigenvalues of finite multiplicity, and **Browder's theorem** if
  $\sigma_w(T)=\sigma_b(T)$. Weyl's theorem implies Browder's theorem.
  Self-adjoint operators satisfy Weyl's theorem (H. Weyl), as do normal and,
  more generally, hyponormal operators and Toeplitz operators (Coburn).
  If $T$ or $T^*$ has SVEP, Browder's theorem holds. A compact
  perturbation of an operator satisfying Weyl's theorem need not satisfy it.

## Compact operators, singular values, and trace ideals

For compact $T$, the **singular values** $s_n(T)$ are the eigenvalues of
$|T|$ in decreasing order, repeated by multiplicity and padded by zeros.
The **Schatten class** $S^p$ has $\sum_ns_n(T)^p<\infty$,
$1\leq p<\infty$. $S^2$ and $S^1$ are the Hilbert–Schmidt and trace
classes, respectively.

* **20. Calkin's theorem on ideals.** If $H$ is separable and infinite
  dimensional, every nonzero proper two-sided ideal of $\mathcal B(H)$
  contains the finite-rank operators and is contained in $\mathcal K(H)$;
  hence $\mathcal K(H)$ is its only nontrivial closed ideal. Such ideals
  correspond to symmetric sequence spaces of singular values.
* **22. Ideal inequalities.** $\|ATB\|_p\leq\|A\|\|T\|_p\|B\|$,
  and Schatten Hölder gives $\|ST\|_r\leq\|S\|_p\|T\|_q$ when
  $1/r=1/p+1/q$ and $p,q,r\geq1$. In particular, products of two
  Hilbert–Schmidt maps are trace class.
* **23. Trace and cyclicity.** For $T\in S^1$,
  $\operatorname{tr}T=\sum_j\langle Te_j,e_j\rangle$ is absolutely
  convergent and basis independent. If $A$ is bounded,
  $\operatorname{tr}(AT)=\operatorname{tr}(TA)$ and
  $|\operatorname{tr}T|\leq\|T\|_1$.
* **24. Lidskii theorem and determinant.** For trace-class $T$,
  $\operatorname{tr}T=\sum_j\lambda_j(T)$ with algebraic multiplicities.
  The Fredholm determinant $\det(I+T)=\prod_j(1+\lambda_j(T))$ is
  well defined, continuous in $\|\cdot\|_1$, multiplicative, and vanishes
  exactly when $I+T$ is not invertible. The eigenvalues are absolutely
  summable even without self-adjointness. The function
  $z\mapsto\det(I+zT)=\prod_j(1+z\lambda_j(T))$ is entire, and near zero
  $\log\det(I+zT)=\sum_{k\geq1}(-1)^{k+1}z^k\operatorname{tr}(T^k)/k$.
* **25. Weyl inequalities.** If $|\lambda_1|\geq|\lambda_2|\geq\cdots$ are
  the eigenvalues of a compact $T$ with algebraic multiplicity, then
  $\prod_{j\leq n}|\lambda_j|\leq\prod_{j\leq n}s_j(T)$ for every $n$.
  Consequently $\sum_j|\lambda_j|^p\leq\sum_js_j(T)^p$ for $p>0$.
  For an $n\times n$ matrix $T$ the full products are equal:
  $\prod_{j\leq n}|\lambda_j|=\prod_{j\leq n}s_j(T)=|\det T|$.
* **70. Volterra operator.** $Vf(x)=\int_0^xf(t)\,dt$ on $L^2[0,1]$ is
  compact and quasinilpotent, $\sigma(V)=\{0\}$ with no eigenvalues, and
  its singular values are $s_n=2/((2n-1)\pi)$, so $\|V\|=2/\pi$ and
  $V\in S^p$ exactly for $p>1$. Its real part $(V+V^*)/2$ has rank one.
  The closed invariant subspaces of $V$ are exactly
  $\{f:f=0\text{ a.e. on }[0,a]\}$, $0\leq a\leq1$, a chain
  (Brodskii, Donoghue); $V$ is the basic example of the triangular models
  of Gohberg–Krein.

## Isometries, contractions, and functional models

The unilateral shift on $H^2(E)$ is $Sf(z)=zf(z)$, where $H^2(E)$
consists of analytic $E$-valued functions with square-summable Taylor
coefficients. A contraction is **completely nonunitary** if it has no
nonzero reducing subspace on which it is unitary. Its defect operators and
spaces are $D_T=(I-T^*T)^{1/2}$ and
$\mathcal D_T=\overline{\operatorname{ran}D_T}$.

* **26. Wold decomposition.** Every isometry is the orthogonal sum of
  a unitary operator and a unilateral shift. The shift multiplicity is
  $\dim\ker V^*$; its shift part is
  $\bigoplus_{n\geq0}V^n\ker V^*$.
* **28. Beurling–Lax–Halmos theorem.** Closed invariant subspaces of
  $H^2(E)$ are ranges $\Theta H^2(F)$ of multiplication by operator-valued
  inner functions, for suitable Hilbert $F$; the multiplier is an isometry.
* **29. Isometric dilation theorem.** Every contraction $T$ is a compression
  of an isometry $V$ with $T^n=P_HV^n|_H$ for $n\geq0$. Requiring
  $K=\overline{\operatorname{span}}\{V^nH:n\geq0\}$ makes the dilation
  unique up to a unitary fixing $H$.
* **30. Unitary dilation theorem.** Every contraction has a unitary power
  dilation $U$ with $T^n=P_HU^n|_H$ for $n\geq0$, unique under
  $K=\overline{\operatorname{span}}\{U^nH:n\in\mathbb Z\}$.
* **31. von Neumann inequality.** If $T$ is a contraction and $p$ is a
  polynomial, $\|p(T)\|\leq\max_{|z|\leq1}|p(z)|$. This extends the
  polynomial calculus contractively to the disk algebra.
* **32. Ando theorem.** Every commuting pair of contractions has commuting
  unitary dilations for their nonnegative mixed powers. Consequently
  $\|p(T_1,T_2)\|\leq\sup_{\mathbb D^2}|p|$. For three commuting
  contractions both the dilation and the polynomial inequality fail
  (Parrott, Varopoulos).
* **33. Completely nonunitary decomposition.** A contraction splits
  uniquely into reducing unitary and completely nonunitary parts. The latter
  admits a contractive weak-star continuous $H^\infty(\mathbb D)$ calculus,
  extending polynomial evaluation.
* **34. Characteristic function.** The analytic contractive function
  $$\Theta_T(z)=\left[-T+zD_{T^*}(I-zT^*)^{-1}D_T\right]|_{\mathcal D_T}
      :\mathcal D_T\to\mathcal D_{T^*}$$
  is a complete unitary invariant for completely nonunitary contractions,
  up to constant unitary identifications of the two defect spaces.
* **35. Pure contraction model.** If $T^{*n}\to0$ strongly, then
  $\Theta_T$ is inner and $T$ is unitarily equivalent to the compression
  of the shift to
  $H^2(\mathcal D_{T^*})\ominus\Theta_TH^2(\mathcal D_T)$.
* **36. Scalar model operators.** For inner $\theta$,
  $K_\theta=H^2\ominus\theta H^2$ is backward-shift invariant and
  $S_\theta=P_{K_\theta}S|_{K_\theta}$ is a contraction. Moreover
  $\theta(S_\theta)=0$, and the kernel of its $H^\infty$ calculus is
  exactly $\theta H^\infty$ when $\theta$ is nonconstant.
* **37. Commutant lifting.** If $X$ commutes with a contraction $T$,
  it lifts to an operator $Y$ commuting with the minimal isometric dilation
  $V$, with $P_HY|_H=X$ and $\|Y\|=\|X\|$. Its scalar case is Sarason's
  theorem: every operator commuting with $S_\theta$ equals $\phi(S_\theta)$
  for some $\phi\in H^\infty$ with $\|\phi\|_\infty=\|\phi(S_\theta)\|$;
  this yields both Nevanlinna–Pick interpolation and Nehari's theorem.
* **38. Sz.-Nagy similarity criterion.** An invertible operator is similar
  to a unitary operator exactly when $\sup_{n\in\mathbb Z}\|T^n\|<\infty$.
  Power boundedness for nonnegative powers alone does not suffice, and a
  polynomially bounded operator need not be similar to a contraction
  (Pisier's solution of Halmos's problem).
* **71. Unitary realization of Schur functions.** An analytic
  $S:\mathbb D\to\mathcal B(U,Y)$ satisfies $\sup_z\|S(z)\|\leq1$ exactly
  when $S(z)=D+zC(I-zA)^{-1}B$ for a unitary colligation
  $\begin{pmatrix}A&B\\C&D\end{pmatrix}:H\oplus U\to H\oplus Y$. A closely
  connected such colligation ($H$ is spanned by the ranges of $A^nB$ and
  $A^{*n}C^*$) is unique up to unitary equivalence on $H$, and the
  characteristic function of item 34 is the realization of this kind for
  the colligation built from $T$ and its defect operators.
* **72. Class $C_0$ and Jordan models.** A completely nonunitary
  contraction is of **class $C_0$** if $u(T)=0$ for some nonzero
  $u\in H^\infty$; the annihilating functions are then the multiples of an
  inner **minimal function** $m_T$. If $T$ is of class $C_0$ on a separable
  space, it is quasisimilar (intertwined both ways by injective operators with
  dense range) to a unique **Jordan operator**
  $\bigoplus_{j\geq0}S_{\theta_j}$ with inner $\theta_j$,
  $\theta_{j+1}\mid\theta_j$, and $\theta_0=m_T$, where $S_\theta$ is
  the model operator of item 36 (Sz.-Nagy–Foiaş, Bercovici).

## Toeplitz and Hankel operators

Let $P:L^2(\mathbb T)\to H^2$ be the orthogonal projection, with normalized
arc measure. For $\phi\in L^\infty(\mathbb T)$ define
$T_\phi=P M_\phi|_{H^2}$ and $H_\phi=(I-P)M_\phi|_{H^2}$.
Thus $H_\phi:H^2\to H^2{}^\perp$.
The concrete Toeplitz and Hankel theory (Brown–Halmos, Coburn, the
Fredholm index, Nehari, Hartman, Kronecker, and Szegő) is in Section 42,
SYNOPSIS42, items 29–37, as the Section 21 bibliography intro indicates.

* **44. Toeplitz extension.** The C*-algebra generated by $S$ contains
  all compact operators, and its quotient by them is $C(\mathbb T)$,
  taking $S$ to the coordinate function. Semicommutators of continuous-symbol
  Toeplitz operators are compact.

## Hyponormality, subnormality, and invariant subspaces

$T$ is **subnormal** if it is the restriction of a normal operator to an
invariant subspace. For positive bounded weights $w_n$, the unilateral
weighted shift is $We_n=w_ne_{n+1}$ on $\ell^2(\mathbb N_0)$.

* **49. Subnormal implies hyponormal.** A subnormal operator is hyponormal,
  and every hyponormal operator satisfies $\|T\|=r(T)$. The converse
  from hyponormality to subnormality is false.
* **50. Weighted-shift hyponormality.** $W$ is hyponormal exactly when
  $w_0\leq w_1\leq\cdots$. This follows from the diagonal entries
  of $W^*W-WW^*$.
* **51. Berger measure criterion.** Set $\beta_0=1$ and
  $\beta_n=w_0^2\cdots w_{n-1}^2$. The weighted shift is subnormal
  exactly when $\beta_n=\int t^n\,d\mu(t)$ for a probability measure
  on $[0,\|W\|^2]$ (Berger; see Conway, *The Theory of Subnormal
  Operators*).
* **52. Lomonosov theorem and invariant subspaces.** On a complex Banach space
  of dimension greater than one, every nonscalar operator commuting with
  a nonzero compact operator has a nontrivial closed hyperinvariant
  subspace. Hyperinvariant means invariant under every operator commuting
  with the given operator. Compact operators on Banach spaces
  (Aronszajn–Smith) and subnormal operators (S. Brown) have nontrivial
  invariant subspaces; there are operators on Banach spaces such as $\ell^1$
  with none (Enflo, Read), while the separable Hilbert-space problem is open.

## Reproducing kernels and interpolation

An **RKHS** is a Hilbert space of functions whose point evaluations are
continuous. Its kernel satisfies $f(w)=\langle f,K_w\rangle$,
$K_w(z)=K(z,w)$. A kernel is **positive definite** if every finite
matrix $(K(z_i,z_j))$ is positive semidefinite. A **multiplier** is a
function $\phi$ for which multiplication is a bounded operator on the space.

* **53. Moore–Aronszajn theorem.** Every positive definite kernel
  determines a unique RKHS with that reproducing kernel. Finite linear
  combinations of its kernel functions are dense.
* **54. Kolmogorov factorization.** A positive definite kernel has a
  Hilbert-space realization $K(z,w)=\langle v_w,v_z\rangle$.
  A minimal realization, whose vectors span densely, is unique up to unitary
  equivalence.
* **55. Schur products of kernels.** Sums and pointwise products of
  positive definite kernels are positive definite. The product construction
  is realized by tensor products of the corresponding feature vectors.
* **56. Multiplier criterion.** $\|M_\phi\|\leq C$ exactly when
  $(C^2-\phi(z)\overline{\phi(w)})K(z,w)$ is a positive definite kernel.
  In this case $M_\phi^*K_w=\overline{\phi(w)}K_w$.
* **57. Kernel comparison and inclusion.** The inclusion
  $H(K_1)\hookrightarrow H(K_2)$ has norm at most $C$ exactly when
  $C^2K_2-K_1$ is positive definite.

## Local spectra and linear dynamics

The **local spectrum** $\sigma_T(x)$ is the complement of points having
an analytic local solution $f(z)$ of $(zI-T)f(z)=x$. $T$ has **SVEP**
if the only analytic local solution of $(zI-T)f(z)=0$ is zero.
On a separable Banach space, $T$ is **hypercyclic** if some orbit
$\{T^nx:n\geq0\}$ is dense.

* **60. SVEP and uniqueness.** Under SVEP the analytic local resolvent
  of each vector is unique wherever it exists. Its local spectrum is a
  compact subset of $\sigma(T)$ and is nonempty for $x\ne0$.
* **61. Normal local spectra.** For a normal operator with spectral
  measure $E$, $\sigma_T(x)$ is the support of
  $B\mapsto\langle E(B)x,x\rangle$. Normal operators have SVEP, and for
  closed $F\subset\mathbb C$ the local spectral subspace
  $\{x:\sigma_T(x)\subset F\}$ is the reducing subspace $E(F)H$.
* **62. Birkhoff transitivity theorem.** For a bounded operator on a
  separable infinite-dimensional Banach space, hypercyclicity is equivalent
  to topological transitivity: for any nonempty open $U,V$, some
  $n\geq0$ satisfies $T^nU\cap V\ne\varnothing$. Hypercyclic vectors
  then form a dense $G_\delta$ set.
* **63. Hypercyclicity criterion.** Suppose dense sets $X_0,Y_0$, integers
  $n_k\uparrow\infty$, and maps $S_k:Y_0\to X$ satisfy
  $T^{n_k}x\to0$ for $x\in X_0$, $S_ky\to0$, and
  $T^{n_k}S_ky\to y$ for $y\in Y_0$. Then $T$ is hypercyclic.
* **64. Adjoint obstruction.** The adjoint of a hypercyclic operator has
  no eigenvalues: a nonzero eigenfunctional would map a dense orbit to
  a geometric scalar sequence, which cannot be dense in the scalar field.
* **65. Rolewicz example.** For the backward shift $B$ on $\ell^p$,
  $1\leq p<\infty$, or on $c_0$, the operator $\lambda B$ is
  hypercyclic exactly when $|\lambda|>1$.
* **66. Spectral obstruction to hypercyclicity.** Every connected
  component of the spectrum of a hypercyclic operator meets the unit
  circle. In particular, compact operators on infinite-dimensional
  Banach spaces are not hypercyclic.

## Indefinite inner product spaces

A **Krein space** is a complex vector space $\mathcal K$ with a Hermitian
form $[\cdot,\cdot]$ admitting a **fundamental decomposition**
$\mathcal K=\mathcal K_+[\dotplus]\mathcal K_-$ into $[\cdot,\cdot]$-orthogonal
subspaces such that $(\mathcal K_\pm,\pm[\cdot,\cdot])$ are Hilbert spaces.
With $J=P_+-P_-$, $\langle x,y\rangle=[Jx,y]$ is a Hilbert inner product.
If $\kappa=\dim\mathcal K_+<\infty$, $\mathcal K$ is a **Pontryagin space**
$\Pi_\kappa$. A subspace is **nonnegative** if $[x,x]\geq0$ on it, and an
operator is **self-adjoint** if $[Ax,y]=[x,Ay]$.

* **73. Fundamental decompositions and maximal semidefinite subspaces.**
  All fundamental decompositions of a Krein space give equivalent Hilbert
  norms, so its topology is intrinsic, and $\dim\mathcal K_\pm$ do not
  depend on the decomposition. A subspace is maximal nonnegative exactly
  when it is the graph $\{x+Kx:x\in\mathcal K_+\}$ of a contraction
  $K:\mathcal K_+\to\mathcal K_-$ (its angular operator). In $\Pi_\kappa$
  every nonnegative subspace has dimension at most $\kappa$, with equality
  for the maximal ones.
* **74. Pontryagin's invariant subspace theorem.** Every bounded
  self-adjoint operator $A$ in $\Pi_\kappa$ has a $\kappa$-dimensional
  nonnegative invariant subspace (Pontryagin). Its nonreal spectrum consists of
  eigenvalues symmetric about $\mathbb R$, whose root subspaces in the upper
  half-plane have total dimension at most $\kappa$; a unitary operator in
  $\Pi_\kappa$ likewise has at most $\kappa$ eigenvalues, counted with
  algebraic multiplicity, outside the closed unit disc.

## Reference guide

Gohberg–Goldberg–Kaashoek develops the Fredholm, compact, and trace-ideal
structure. Sz.-Nagy–Foiaş–Bercovici–Kérchy supplies dilations, characteristic
functions, models, and commutant lifting. Nikolski's Toeplitz course gives
an independent concrete treatment of shifts, Toeplitz and Hankel operators,
and determinant asymptotics; these recur in Douglas, Rosenblum–Rovnyak,
and Böttcher–Silbermann. Conway and Douglas treat the Calkin algebra,
essential unitary equivalence, and the Brown–Douglas–Fillmore theorem.
Paulsen–Raghupathi supplies the kernel and
interpolation foundation. Müller treats the Taylor spectrum and spectral
systems (the local copy is the 2003 first edition), and Aiena the Weyl and
Browder spectra and Weyl-type theorems. Sz.-Nagy–Foiaş–Bercovici–Kérchy
also gives the class $C_0$ and Jordan models; Ball–Gohberg–Rodman and
Arov–Dym develop realizations of contractive analytic functions;
Gohberg–Krein treats the Volterra operator and triangular models; and
Bognár is the source for Krein and Pontryagin spaces. The local-spectrum
and dynamics sections select basic results shared by the specialist
references in the supplementary bibliography, rather than attempting their
full classification theories.

Local source copies consulted:

* [Gohberg–Goldberg–Kaashoek, Classes of Linear Operators I](References/GohbergGoldberegKaashoek1990ClassesLinearOperatorsVol1-SpringerOTAA49.pdf).
* [Sz.-Nagy–Foiaş–Bercovici–Kérchy, Harmonic Analysis of Operators on Hilbert Space](References/NagyFoiasBercoviciKérchy2010HarmonicAnalysisOperatorsHilbertSpace2ndEd-SpringerUTX.pdf).
* [Nikolski, Toeplitz Matrices and Operators](References/Nikolski2019ToeplitzMatricesOperators-CambridgeStudiesAM182.pdf).
* [Paulsen–Raghupathi, An Introduction to the Theory of Reproducing Kernel Hilbert Spaces](References/PaulsenRaghupathi2016IntroductionTheoryReproducingKernelHilbertSpaces-CambridgeStudiesAM152.pdf).
* [Bognár, Indefinite Inner Product Spaces](References/Bognár1974IndefiniteInnerProductSpaces-SpringerErgeb78.pdf).
* [Müller, Spectral Theory of Linear Operators and Spectral Systems in Banach Algebras](References/Müller2003SpectralTheoryLinearOperatorsSpectralSystemsBanachAlgebras-SpringerOTAA139.pdf).
* [Grosse-Erdmann–Peris Manguillot, Linear Chaos](References/GrosseErdmannPerisManguillot2011LinearChaos-Springer.UTX.pdf).
