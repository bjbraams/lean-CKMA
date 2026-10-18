# Synopsis: Bounded operator theory, spectra, and functional models

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects the recurring graduate and beginning research core of
Section 21 of [CKMA-bib.md](CKMA-bib.md).
It develops Fredholm theory, compact ideals, contractions and dilations,
Toeplitz and Hankel operators, reproducing kernels, and the first structural
results on invariant subspaces and linear dynamics. General unbounded
operators and operator algebras are treated in Sections 22 and 23.

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

* **1. Adjoint and closed range.** $\|T^*T\|=\|T\|^2$,
  $\overline{\operatorname{ran}T}=(\ker T^*)^\perp$, and
  $\operatorname{ran}T$ is closed exactly when $T$ is bounded below on
  $(\ker T)^\perp$. Closedness of the ranges of $T$ and $T^*$ is equivalent.
* **2. Polar decomposition.** Every $T$ has a unique decomposition
  $T=U|T|$, where $|T|=(T^*T)^{1/2}$ and $U$ is a partial isometry
  with initial space $(\ker T)^\perp$ and final space
  $\overline{\operatorname{ran}T}$.
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
* **6. Normal spectral theorem.** A normal $T$ has a projection-valued
  measure $E$ with $T=\int z\,dE(z)$, and bounded Borel functions define
  $f(T)=\int f\,dE$. In particular
  $\|R(z,T)\|=\operatorname{dist}(z,\sigma(T))^{-1}$ off the spectrum.
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

## Fredholm operators and essential spectra

A bounded map $T:X\to Y$ between Banach spaces is **Fredholm** if its
range is closed and both $\ker T$ and $Y/\operatorname{ran}T$ are finite
dimensional. Its **index** is
$\operatorname{ind}T=\dim\ker T-\dim(Y/\operatorname{ran}T)$.
The **Calkin algebra** is $\mathcal B(H)/\mathcal K(H)$, where
$\mathcal K(H)$ is the compact ideal; the **essential spectrum** here means
$\sigma_{\rm ess}(T)=\{z:T-zI\text{ is not Fredholm}\}$.

* **11. Atkinson theorem.** $T$ is Fredholm exactly when it has a bounded
  inverse modulo compact operators. For endomorphisms this says that its
  image in the Calkin algebra is invertible.
* **12. Stability and local constancy.** Fredholm operators form an open
  subset of $\mathcal L(X,Y)$, and their index is locally constant.
  Compact perturbations preserve Fredholmness and the index.
* **13. Product and adjoint rules.** Products of Fredholm operators are
  Fredholm, with $\operatorname{ind}(ST)=\operatorname{ind}S+
  \operatorname{ind}T$. For the Hilbert-space or Banach-space adjoint,
  $\operatorname{ind}T^*=-\operatorname{ind}T$.
* **14. Fredholm alternative.** For compact $K$, $I-K$ is Fredholm of
  index zero. It is invertible exactly when it is injective, and
  $(I-K)x=y$ is solvable exactly when $y\perp\ker(I-K^*)$ on Hilbert space.
* **15. Analytic Fredholm theorem.** If $K(z)$ is a norm-holomorphic
  compact-operator family on a connected plane domain, then either
  $I-K(z)$ is nowhere invertible or its inverse is meromorphic, with
  discrete poles and finite-rank principal parts.
* **16. Essential spectral invariance.** Compact perturbations preserve
  $\sigma_{\rm ess}$. For bounded self-adjoint $T$, the complement of
  its essential spectrum in its spectrum consists exactly of isolated
  eigenvalues of finite multiplicity.
* **17. Weyl criterion for essential spectrum.** For self-adjoint $T$,
  $\lambda\in\sigma_{\rm ess}(T)$ exactly when there are unit vectors
  $x_n\rightharpoonup0$ with $(T-\lambda I)x_n\to0$. Such a sequence
  can be chosen orthonormal.
* **18. Weyl–von Neumann–Berg and Brown–Douglas–Fillmore.** On separable
  $H$, every normal operator is the sum of a diagonal normal operator and a
  compact operator of arbitrarily small norm (Hilbert–Schmidt for
  self-adjoint operators); two normal operators are unitarily equivalent
  modulo compacts exactly when their essential spectra agree. For
  essentially normal operators ($T^*T-TT^*$ compact), unitary equivalence
  modulo compacts holds exactly when the essential spectra agree and
  $\operatorname{ind}(T-\lambda)$ agrees off the essential spectrum (BDF).

## Compact operators, singular values, and trace ideals

For compact $T$, the **singular values** $s_n(T)$ are the eigenvalues of
$|T|$ in decreasing order, repeated by multiplicity and padded by zeros.
The **Schatten class** $S^p$ has $\sum_ns_n(T)^p<\infty$,
$1\leq p<\infty$. $S^2$ and $S^1$ are the Hilbert–Schmidt and trace
classes, respectively.

* **19. Compact spectral theorem.** A compact normal operator is diagonal
  in an orthonormal basis. For general compact operators, every nonzero
  spectral point is an isolated eigenvalue of finite algebraic multiplicity;
  zero is the only possible spectral accumulation point.
* **20. Calkin's theorem on ideals.** If $H$ is separable and infinite
  dimensional, every nonzero proper two-sided ideal of $\mathcal B(H)$
  contains the finite-rank operators and is contained in $\mathcal K(H)$;
  hence $\mathcal K(H)$ is its only nontrivial closed ideal. Such ideals
  correspond to symmetric sequence spaces of singular values.
* **21. Singular value approximation.** With $s_1(T)\geq s_2(T)\geq\cdots$,
  $s_n(T)=\inf_{\operatorname{rank}F<n}\|T-F\|$. Singular value
  decompositions therefore give optimal finite-rank approximation in
  operator norm.
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
  exactly when $I+T$ is not invertible.
* **25. Weyl inequalities.** If $|\lambda_1|\geq|\lambda_2|\geq\cdots$ are
  the eigenvalues of a compact $T$ with algebraic multiplicity, then
  $\prod_{j\leq n}|\lambda_j|\leq\prod_{j\leq n}s_j(T)$ for every $n$.
  Consequently $\sum_j|\lambda_j|^p\leq\sum_js_j(T)^p$ for $p>0$.

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
* **27. Beurling theorem.** Every nonzero closed shift-invariant subspace
  of scalar $H^2$ is $\theta H^2$ for an inner function $\theta$, unique
  up to a unimodular constant. Inner means that its boundary values have
  modulus one almost everywhere.
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

## Toeplitz and Hankel operators

Let $P:L^2(\mathbb T)\to H^2$ be the orthogonal projection, with normalized
arc measure. For $\phi\in L^\infty(\mathbb T)$ define
$T_\phi=P M_\phi|_{H^2}$ and $H_\phi=(I-P)M_\phi|_{H^2}$.
Thus $H_\phi:H^2\to H^2{}^\perp$.

* **39. Brown–Halmos characterization.** $T\in\mathcal B(H^2)$ is
  Toeplitz exactly when $S^*TS=T$. Its symbol in $L^\infty$ is unique,
  $\|T_\phi\|=\|\phi\|_\infty$, and $T_\phi^*=T_{\overline\phi}$.
* **40. Product identity.**
  $T_\phi T_\psi-T_{\phi\psi}=-H_{\overline\phi}^*H_\psi$.
  In particular $T_\phi T_\psi=T_{\phi\psi}$ if $\psi$ is analytic
  or $\phi$ is coanalytic.
* **41. Coburn alternative.** For a nonzero scalar symbol $\phi$,
  at least one of $\ker T_\phi$ and $\ker T_\phi^*$ is zero.
  Hence a Fredholm scalar Toeplitz operator of index zero is invertible.
* **42. Continuous-symbol Fredholm theorem.** For $\phi\in C(\mathbb T)$,
  $T_\phi$ is Fredholm exactly when $\phi$ has no zeros, and then
  $\operatorname{ind}T_\phi=-\operatorname{wind}(\phi,0)$.
* **43. Essential spectrum of Toeplitz operators.** For continuous $\phi$,
  $\sigma_{\rm ess}(T_\phi)=\phi(\mathbb T)$. Its full spectrum consists
  of that curve together with points $\lambda$ where
  $\operatorname{wind}(\phi-\lambda,0)\ne0$.
* **44. Toeplitz extension.** The C*-algebra generated by $S$ contains
  all compact operators, and its quotient by them is $C(\mathbb T)$,
  taking $S$ to the coordinate function. Semicommutators of continuous-symbol
  Toeplitz operators are compact.
* **45. Nehari theorem.** The Hankel norm satisfies
  $\|H_\phi\|=\operatorname{dist}_{L^\infty}(\phi,H^\infty)$.
  Every bounded Hankel matrix has an $L^\infty$ symbol, so its boundedness
  is precisely a bounded-symbol extension problem.
* **46. Hartman theorem.** $H_\phi$ is compact exactly when
  $\phi\in H^\infty+C(\mathbb T)$.
* **47. Kronecker finite-rank theorem.** A Hankel matrix has finite rank
  exactly when the power series formed from its Hankel coefficients is
  rational. For a bounded Hankel operator this is equivalent to its
  negative Fourier part being the negative part of a rational symbol
  with no poles on $\mathbb T$.
* **48. Szegő limit theorems.** If $\phi>0$ is
  smooth on $\mathbb T$ and $T_n(\phi)$ is its $n\times n$ Toeplitz
  matrix, then
  $$\det T_n(\phi)\sim\exp\left(n\widehat{\log\phi}(0)
       +\sum_{k\geq1}k\widehat{\log\phi}(k)
                            \widehat{\log\phi}(-k)\right).$$
  The first Szegő theorem, $(\det T_n(\phi))^{1/n}\to
  \exp\int\log\phi$, holds for every nonnegative $\phi\in L^1$ (both sides
  zero if $\log\phi\notin L^1$).

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
  on $[0,\|W\|^2]$
  ([an explicit lecture-note formulation](https://www.math.snu.ac.kr/~wylee/Lecture%20notes%20in%20math/Lecture%20Notes%20on%20OperatorTheory.pdf), Theorem 4.1.4).
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
* **58. Nevanlinna–Pick interpolation.** For distinct $z_i\in\mathbb D$,
  there is analytic $f$ with $\|f\|_\infty\leq1$ and $f(z_i)=w_i$
  exactly when $((1-w_i\overline{w_j})/(1-z_i\overline{z_j}))$ is
  positive semidefinite.
* **59. de Branges–Rovnyak kernels.** If $b$ is analytic with
  $\|b\|_\infty\leq1$, then
  $K_b(z,w)=(1-b(z)\overline{b(w)})/(1-z\overline w)$ is positive
  definite. For inner $b=\theta$, its RKHS is isometrically $K_\theta$.

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

## Reference guide

Gohberg–Goldberg–Kaashoek develops the Fredholm, compact, and trace-ideal
structure. Sz.-Nagy–Foiaş–Bercovici–Kérchy supplies dilations, characteristic
functions, models, and commutant lifting. Nikolski's Toeplitz course gives
an independent concrete treatment of shifts, Toeplitz and Hankel operators,
and determinant asymptotics; these recur in Douglas, Rosenblum–Rovnyak,
and Böttcher–Silbermann. Conway and Douglas treat the Calkin algebra,
essential unitary equivalence, and the Brown–Douglas–Fillmore theorem.
Paulsen–Raghupathi supplies the kernel and
interpolation foundation. The local-spectrum and dynamics sections select
basic results shared by the specialist references in the supplementary
bibliography, rather than attempting their full classification theories.

Local source copies consulted:

* [Gohberg–Goldberg–Kaashoek, Classes of Linear Operators I](References/GohbergGoldberegKaashoek1990ClassesLinearOperatorsVol1-SpringerOTAA49.pdf).
* [Sz.-Nagy–Foiaş–Bercovici–Kérchy, Harmonic Analysis of Operators on Hilbert Space](References/NagyFoiasBercoviciKérchy2010HarmonicAnalysisOperatorsHilbertSpace2ndEd-SpringerUTX.pdf).
* [Nikolski, Toeplitz Matrices and Operators](References/Nikolski2019ToeplitzMatricesOperators-CambridgeStudiesAM182.pdf).
* [Paulsen–Raghupathi, An Introduction to the Theory of Reproducing Kernel Hilbert Spaces](References/PaulsenRaghupathi2016IntroductionTheoryReproducingKernelHilbertSpaces-CambridgeStudiesAM152.pdf).
* [Müller, Spectral Theory of Linear Operators and Spectral Systems in Banach Algebras](References/Müller2003SpectralTheoryLinearOperatorsSpectralSystemsBanachAlgebras-SpringerOTAA139.pdf).
* [Grosse-Erdmann–Peris Manguillot, Linear Chaos](References/GrosseErdmannPerisManguillot2011LinearChaos-Springer.UTX.pdf).
