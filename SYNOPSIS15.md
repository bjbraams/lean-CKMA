# Synopsis: Core Banach and Hilbert space theory

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-15);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects the recurring graduate core of Section 15 of
[CKMA-bib.md](CKMA-bib.md#ckma-15): completeness,
duality, weak compactness, Hilbert space geometry, and the first structure
theorems for linear operators. The more specialized geometry of Banach
spaces, locally convex theory, Banach algebras, and general spectral theory
have separate synopses. Some overlap supplies the foundations those subjects use.

Scalars are $\mathbb R$ or $\mathbb C$ unless a statement specifies otherwise.
A **Banach space** is a complete normed vector space; a **Hilbert space** is
complete for the norm induced by an inner product. Write $B_X$ for the closed
unit ball, $X^*$ for the continuous linear dual, and $\mathcal L(X,Y)$ for
bounded linear operators with the operator norm. An **isomorphism** is a bounded
linear bijection with bounded inverse; an **isometry** preserves the norm.
Unless stated otherwise, $X$ and $Y$ denote Banach spaces.
Hilbert inner products are linear in the first variable.

## Completeness, quotient spaces, and classical examples

A subspace is **complemented** if it is the range of a bounded projection.
For a closed subspace $M\subset X$, the quotient norm is
$\|x+M\|=\inf_{m\in M}\|x-m\|$. A set is **relatively compact** if its
closure is compact; in a complete metric space this is equivalent to total
boundedness.

* **1. Completion theorem.** Every normed space embeds isometrically as a
  dense subspace of a Banach space, uniquely up to the isometry fixing the
  original space. Bounded maps into Banach spaces extend uniquely to the completion.
* **2. Quotients and operator spaces.** If $X$ is Banach and $M\subset X$
  is closed, then $X/M$ is Banach; for normed $X$, $\mathcal L(X,Y)$ is
  Banach whenever $Y$ is. A bounded map
  vanishing on $M$ factors uniquely through $X/M$, with the same norm.
* **3. Finite-dimensional equivalence.** All norms on a finite-dimensional
  vector space are equivalent; every linear map from it to a normed space is
  continuous. Finite-dimensional subspaces of normed spaces are closed.
* **4. Riesz lemma and local compactness.** If $M$ is a proper closed subspace
  of $X$ and $0<\alpha<1$, some $x\in X$ has $\|x\|=1$ and
  $\operatorname{dist}(x,M)>\alpha$. Consequently $B_X$ is norm compact
  exactly when $X$ is finite dimensional.
* **5. Completeness of classical spaces.** The spaces $\ell^p$, $L^p(\mu)$
  for $1\leq p\leq\infty$, $c_0$, and $C_0(K)$ for locally compact
  Hausdorff $K$ are Banach. A normed space is complete exactly when every
  absolutely summable series in it converges in norm.
* **6. Duals of sequence and function spaces.** For $1<p<\infty$,
  $(\ell^p)^*=\ell^{p'}$; also $c_0^*=\ell^1$ and $(\ell^1)^*=\ell^\infty$.
  For $1<p<\infty$, $(L^p(\mu))^*=L^{p'}(\mu)$ isometrically under
  integration for every measure; $(L^1)^*=L^\infty$ holds for
  $\sigma$-finite $\mu$. The dual of $L^\infty$ is strictly larger than
  $L^1$ except in finite-dimensional cases; it consists of bounded finitely
  additive measures.
* **69. Arzelà–Ascoli theorem.** For compact Hausdorff $K$, a subset of
  $C(K)$ is relatively norm compact exactly when it is pointwise bounded
  and equicontinuous.
* **9. Complemented subspaces.** A closed subspace $M$ of a Banach space
  is complemented exactly when $X=M\oplus N$ for another closed subspace
  $N$. Every finite-dimensional or closed finite-codimensional subspace is
  complemented; arbitrary closed subspaces need not be.

## Hahn–Banach, separation, and duality

For $A\subset X$ let $A^\perp=\{f\in X^*:f|_A=0\}$, and for $B\subset X^*$
let $B_\perp=\{x\in X:f(x)=0\ (f\in B)\}$. The canonical
map $J:X\to X^{**}$ is $(Jx)(f)=f(x)$. A real function $p$ is
**sublinear** if it is subadditive and positively homogeneous.

* **10. Hahn–Banach extension.** A real linear functional on a subspace,
  dominated there by a sublinear function $p$, extends with the same
  domination to the full space. Over either scalar field, every bounded
  linear functional on a subspace extends without increasing its norm.
* **11. Norming functionals.** For every nonzero $x\in X$ there is
  $f\in X^*$ with $\|f\|=1$ and $f(x)=\|x\|$. Hence
  $\|x\|=\sup_{f\in B_{X^*}}|f(x)|$, and $J$ is an isometric embedding.
* **12. Separation of convex sets.** Disjoint convex sets, one of which is
  open, can be separated by a nonzero continuous real linear functional.
  A compact convex set and a disjoint closed convex set can be strictly
  separated; in particular so can a point and a closed convex set.
  In complex spaces use real parts of complex linear functionals.
* **13. Distance to a subspace.** For a closed linear subspace $M$,
  $$\operatorname{dist}(x,M)=
    \sup\{|f(x)|:f\in M^\perp,\ \|f\|\leq1\}.$$
  In particular, continuous functionals detect membership in $M$.
* **14. Duality of subspaces and quotients.** For closed $M\subset X$,
  $(X/M)^*$ identifies isometrically with $M^\perp$, while restriction
  induces the isometric identification $X^*/M^\perp\cong M^*$.
* **16. Goldstine theorem.** $J(B_X)$ is weak-star dense in $B_{X^{**}}$.
  Thus $J(X)$ is weak-star dense in $X^{**}$, though norm closed and proper
  when $X$ is nonreflexive.

## Baire category and the fundamental mapping principles

A family $\mathcal T\subset\mathcal L(X,Y)$ is **pointwise bounded** if
$\sup_{T\in\mathcal T}\|Tx\|<\infty$ for each $x\in X$.

* **17. Baire category theorem.** A complete metric space is not a countable
  union of closed sets with empty interior. Equivalently, a countable
  intersection of dense open sets is dense.
* **18. Uniform boundedness principle.** A pointwise bounded family of
  bounded linear maps from a Banach space to a normed space has uniformly
  bounded operator norms. Consequently weakly bounded subsets of a normed
  space are norm bounded.
* **19. Open mapping and bounded inverse.** A bounded surjective linear map
  between Banach spaces is open. In particular, a bounded linear bijection
  between Banach spaces has bounded inverse.
* **20. Closed graph theorem.** An everywhere-defined linear map between
  Banach spaces is bounded exactly when its graph is closed in the product
  norm. The requirement that its domain be the whole source matters.
* **21. Convergence on a dense subspace.** If $T_n\in\mathcal L(X,Y)$ are
  uniformly bounded, $Y$ is Banach, and $T_nx$ converges for each $x$ in a
  dense linear subspace, then it converges for every $x\in X$. The limit
  operator is bounded, with norm at most $\sup_n\|T_n\|$.
* **22. Closed range estimates.** For $T\in\mathcal L(X,Y)$ between Banach
  spaces, its range is closed exactly when
  $\operatorname{dist}(x,\ker T)\leq C\|Tx\|$ for some $C$ and all $x$.
  If $T$ is injective, this says that $T$ is bounded below.

## Weak topologies, compactness, and reflexivity

The **weak topology** $\sigma(X,X^*)$ is pointwise convergence against
$X^*$; the **weak-star topology** $\sigma(X^*,X)$ is pointwise convergence
on $X$. A Banach space is **reflexive** if $J$ is onto. Compactness below is
topological compactness, which must be distinguished from sequential
compactness until the relevant theorem is invoked.

* **23. Banach–Alaoglu theorem.** $B_{X^*}$ is weak-star compact. Every
  norm-bounded weak-star closed subset of $X^*$ is therefore weak-star compact.
* **24. Metrizability on dual balls.** If $X$ is separable, the weak-star
  topology of $B_{X^*}$ is metrizable. Thus every bounded sequence in $X^*$
  has a weak-star convergent subsequence. Separability of $X^*$ similarly
  makes the weak topology metrizable on $B_X$.
* **25. Weak lower semicontinuity.** The norm, and every norm lower
  semicontinuous convex function, is weakly lower semicontinuous. Norm-closed
  convex subsets are weakly closed.
* **26. Mazur theorem.** If $x_n\rightharpoonup x$, then $x$ lies in the
  norm closure of the convex hull of each tail of $(x_n)$. Suitable finite
  convex combinations of successive tails converge to $x$ in norm.
* **27. Reflexivity and weak compactness.** A Banach space is reflexive
  exactly when $B_X$ is weakly compact. Closed subspaces and quotients of
  reflexive spaces are reflexive, and $X$ is reflexive exactly when $X^*$ is.
* **28. Eberlein–Šmulian theorem.** A subset of a Banach space is relatively
  weakly compact exactly when every sequence in it has a weakly convergent
  subsequence with limit in the ambient space. In particular, bounded
  sequences in reflexive spaces have weakly convergent subsequences.
* **29. James compactness theorem.** A Banach space is reflexive exactly
  when every $f\in X^*$ attains its norm on $B_X$. More generally,
  a closed bounded convex set is weakly compact exactly when every
  continuous real linear functional attains its supremum there.
* **31. Krein–Šmulian theorem.** A convex subset $C\subset X^*$ is
  weak-star closed exactly when $C\cap rB_{X^*}$ is weak-star closed for
  every $r>0$.
* **32. Separability and duality.** If $X^*$ is separable, then $X$ is
  separable. For reflexive $X$, separability of $X$ and of $X^*$ are
  equivalent. The converse implication fails for general Banach spaces.
* **33. Uniform convexity and reflexivity.** If, in a Banach space $X$,
  for each $\varepsilon>0$
  there is $\delta>0$ such that unit-ball vectors with distance at least
  $\varepsilon$ have midpoint norm at most $1-\delta$, then $X$ is
  reflexive (Milman–Pettis). Clarkson's inequalities show that $L^p$ is
  uniformly convex, hence reflexive, for $1<p<\infty$.
* **34. Weak convergence and norms.** In a uniformly convex space,
  $x_n\rightharpoonup x$ and $\|x_n\|\to\|x\|$ imply $x_n\to x$
  in norm. In Hilbert space the same conclusion follows from the inner
  product identity for $\|x_n-x\|^2$.
* **35. Direct method in reflexive spaces.** A proper weakly lower
  semicontinuous coercive function on a nonempty weakly closed subset of a
  reflexive Banach space attains its infimum there.
  A strictly convex objective on a convex domain has at most one minimizer.

## Hilbert space geometry and variational problems

For $M\subset H$, let $M^\perp=\{x:\langle x,m\rangle=0\ (m\in M)\}$.
An **orthonormal basis** is a maximal orthonormal set, whose closed linear
span is $H$; its expansions are norm limits, not algebraic finite expansions.
A bounded operator $T$ on $H$ is **self-adjoint** if
$\langle Tx,y\rangle=\langle x,Ty\rangle$ for all $x,y$, and **positive** if
$\langle Tx,x\rangle\geq0$ for all $x$.

* **36. Cauchy–Schwarz and polarization.**
  $|\langle x,y\rangle|\leq\|x\|\|y\|$, with equality for nonzero
  vectors exactly when they are linearly dependent. The norm determines
  the inner product by polarization.
* **37. Jordan–von Neumann theorem.** A norm is induced by an inner
  product exactly when it satisfies
  $\|x+y\|^2+\|x-y\|^2=2\|x\|^2+2\|y\|^2$.
* **38. Projection onto closed convex sets.** Every nonempty closed convex
  $C\subset H$ has a unique nearest point $P_Cx$ to each $x$. It is
  characterized by $\operatorname{Re}\langle x-P_Cx,y-P_Cx\rangle\leq0$
  for $y\in C$, and $P_C$ is nonexpansive. Indeed it is firmly nonexpansive:
  $\|P_Cx-P_Cy\|^2\leq\operatorname{Re}\langle P_Cx-P_Cy,x-y\rangle$.
* **39. Orthogonal decomposition.** For a closed linear subspace $M$,
  $H=M\oplus M^\perp$. Its nearest-point map is a bounded self-adjoint
  projection; every bounded self-adjoint projection arises this way.
* **40. Riesz–Fréchet representation.** Every $f\in H^*$ has a unique
  representation $f(x)=\langle x,y\rangle$, with $\|f\|=\|y\|$.
  Thus $H$ is reflexive; the identification with its linear dual is
  conjugate linear over $\mathbb C$.
* **41. Bessel and Parseval.** For an orthonormal family $(e_i)$,
  $\sum_i|\langle x,e_i\rangle|^2\leq\|x\|^2$. If the family is a
  basis, equality holds and $x=\sum_i\langle x,e_i\rangle e_i$ in norm.
  Only countably many coefficients of a given vector are nonzero.
* **42. Classification of Hilbert spaces.** Every Hilbert space has an
  orthonormal basis and is isometrically isomorphic to $\ell^2(I)$ for its
  basis index set $I$. Two Hilbert spaces are unitarily isomorphic exactly
  when their orthonormal bases have the same cardinality.
* **70. Gram–Schmidt and separable Hilbert spaces.** Every finite or
  countable linearly independent sequence $(x_n)$ in $H$ yields, by
  Gram–Schmidt orthonormalization, an orthonormal sequence $(e_n)$ with the
  same linear spans $\operatorname{span}\{x_1,\dots,x_n\}$ for every $n$.
  Hence $H$ is separable exactly when it has a countable orthonormal basis,
  and every infinite-dimensional separable Hilbert space is unitarily
  isomorphic to $\ell^2$.
* **43. Lax–Milgram theorem.** If a bounded sesquilinear form $a$ on $H$
  is linear in its first variable and
  $\operatorname{Re}a(u,u)\geq\alpha\|u\|^2$ with $\alpha>0$, then for
  every bounded conjugate-linear functional $F$ there is a unique $u$ such
  that $a(u,v)=F(v)$ for all $v$, and $\|u\|\leq\alpha^{-1}\|F\|$.
* **44. Stampacchia variational inequality.** In a real Hilbert space, for
  a bounded coercive bilinear form $a$, a nonempty closed convex set $C$,
  and $f\in H^*$, there is a unique $u\in C$ satisfying
  $a(u,v-u)\geq f(v-u)$ for every $v\in C$.
* **45. Galerkin approximation and Céa lemma.** Under the Lax–Milgram
  assumptions, the solution $u_V$ in any closed subspace $V$ satisfies
  $\|u-u_V\|\leq(\|a\|/\alpha)\inf_{v\in V}\|u-v\|$.
  Dense nested approximation spaces therefore give norm convergence.

## Adjoints, compactness, and the Fredholm alternative

The **Banach adjoint** is $T^*f=f\circ T$. On Hilbert spaces it corresponds
to the operator determined by $\langle Tx,y\rangle=\langle x,T^*y\rangle$.
An operator is **compact** if it maps bounded sets to relatively compact
sets; **weakly compact** uses relative weak compactness instead.

* **46. Adjoint identities.** $\|T^*\|=\|T\|$, $(ST)^*=T^*S^*$, and on
  Hilbert spaces $\|T^*T\|=\|T\|^2$. Moreover
  $(\operatorname{ran}T)^\perp=\ker T^*$ and
  $\overline{\operatorname{ran}T}=(\ker T^*)_\perp$. On Hilbert spaces the
  range of $T$ is closed exactly when $T$ is bounded below on
  $(\ker T)^\perp$.
* **47. Closed range theorem.** For bounded maps between Banach spaces,
  $\operatorname{ran}T$ is norm closed exactly when $\operatorname{ran}T^*$
  is norm closed, and then $\operatorname{ran}T=(\ker T^*)_\perp$ and
  $\operatorname{ran}T^*=(\ker T)^\perp$. Also $T$ is surjective exactly
  when $T^*$ is bounded below.
* **48. Gantmacher theorem.** $T:X\to Y$ is weakly compact exactly when
  $T^{**}(X^{**})\subset J_Y(Y)$, and exactly when $T^*$ is weakly compact.
  Every bounded operator factoring through a reflexive space is weakly
  compact; conversely every weakly compact operator so factors
  (Davis–Figiel–Johnson–Pełczyński).
* **49. Compact operator ideal.** Compact operators form a norm-closed
  linear subspace and are preserved by composition with bounded operators.
  Every finite-rank operator is compact. The identity on an infinite-dimensional
  Banach space is not compact.
* **50. Schauder theorem.** An operator between Banach spaces is compact
  exactly when its adjoint is compact.
* **51. Compact operators and weak convergence.** If $T$ is compact and
  $x_n\rightharpoonup x$, then $Tx_n\to Tx$ in norm. On a reflexive
  source, the property that weakly convergent sequences have norm-convergent
  images characterizes compactness.
* **52. Finite-rank approximation in Hilbert space.** A compact operator
  between Hilbert spaces is a norm limit of finite-rank operators. On general
  Banach spaces this assertion requires approximation hypotheses and can fail.
* **53. Riesz–Fredholm alternative.** For compact $K:X\to X$, $I-K$ has
  closed range, finite-dimensional kernel and cokernel of equal dimension.
  It is injective exactly when it is surjective, and then has bounded inverse.
* **54. Solvability condition.** In result 53, $(I-K)x=y$ is solvable exactly
  when $f(y)=0$ for all $f\in\ker(I-K^*)$. Solutions, when they exist,
  form an affine translate of $\ker(I-K)$.
* **56. Compact spectral structure.** For compact $K$ on a complex Banach
  space, every nonzero spectral value is an isolated eigenvalue with finite
  algebraic multiplicity. There are only finitely many outside any disk
  about zero. In infinite dimension, zero belongs to the spectrum. A compact
  normal operator on a Hilbert space is diagonal in an orthonormal basis.
* **57. Compact self-adjoint spectral theorem.** A compact self-adjoint
  operator on $H$ has an orthonormal basis of eigenvectors, including a basis
  of its kernel. Its nonzero eigenvalues are real, of finite multiplicity,
  and tend to zero if infinite in number.
* **58. Courant–Fischer min–max principle.** Let the positive eigenvalues of a
  compact self-adjoint operator $T$ on an infinite-dimensional $H$ be listed
  with multiplicity as $\lambda_1\geq\lambda_2\geq\cdots$, padded with
  zeros if there are only finitely many. Then for every $k\geq1$
  $$\lambda_k=\sup_{\dim V=k}\ \min_{x\in V,\ \|x\|=1}\langle Tx,x\rangle
     =\min_{\dim W=k-1}\ \sup_{x\perp W,\ \|x\|=1}\langle Tx,x\rangle,$$
  the supremum being attained when $\lambda_k>0$.
  Consequences include Weyl's perturbation bound
  $|\lambda_k(S)-\lambda_k(T)|\leq\|S-T\|$ for these padded lists and
  eigenvalue interlacing.
* **59. Singular value decomposition.** A compact operator $T:H_1\to H_2$
  has an expansion $Tx=\sum_ns_n\langle x,e_n\rangle f_n$ with orthonormal
  systems, $s_1\geq s_2\geq\cdots>0$, and $s_n\to0$ if infinite; the
  $s_n^2$ are the nonzero eigenvalues of $T^*T$. Truncation gives best
  rank-at-most-$n$ approximation error $s_{n+1}$ in operator norm, with
  the singular-value list padded by zeros in the finite-rank case.
  Equivalently, $s_n(T)=\inf_{\operatorname{rank}F<n}\|T-F\|$.

## First spectral and fixed-point principles

The spectral statements in this section use complex spaces. For bounded
$T$ on a nonzero complex Banach space,
$\sigma(T)=\{\lambda:\lambda I-T\text{ is not invertible}\}$ and
$R(\lambda,T)=(\lambda I-T)^{-1}$ on its complement. A Hilbert-space
operator is **normal** if $TT^*=T^*T$; self-adjoint and positive operators
are defined before result 36. The Fredholm index is treated in Section 21
(Atkinson's theorem, SYNOPSIS21, item 11), the Banach and Schauder fixed-point
theorems in Section 35, and the mean ergodic theorem in Section 10.

* **60. Neumann series and resolvent.** If $\|S\|<1$, then
  $(I-S)^{-1}=\sum_{n\geq0}S^n$ in operator norm. Invertible operators
  form an open set; the resolvent is holomorphic and satisfies
  $R(\lambda,T)-R(\mu,T)=(\mu-\lambda)R(\lambda,T)R(\mu,T)$.
* **61. Spectrum and spectral radius.** $\sigma(T)$ is nonempty compact,
  contained in $\{|\lambda|\leq\|T\|\}$, and
  $r(T)=\lim_n\|T^n\|^{1/n}=\inf_n\|T^n\|^{1/n}$.
* **62. Polynomial spectral mapping.** For every complex polynomial $p$,
  $\sigma(p(T))=p(\sigma(T))$. The corresponding rational formula holds
  when all poles avoid $\sigma(T)$.
* **63. Self-adjoint spectral bounds.** A bounded self-adjoint operator has
  real spectrum and norm $\sup_{\lambda\in\sigma(T)}|\lambda|$.
  It is positive exactly when its spectrum lies in $[0,\infty)$.
* **64. Positive square root and polar decomposition.** Every bounded
  positive operator has a unique bounded positive square root. Every bounded
  $T:H_1\to H_2$ has a unique factorization $T=U(T^*T)^{1/2}$ where $U$
  is the partial isometry with initial space $\overline{\operatorname{ran}T^*}$
  and final space $\overline{\operatorname{ran}T}$.
* **65. Bounded normal spectral theorem.** For normal $T$ there is a unique
  projection-valued measure $E$ on $\sigma(T)$ with
  $T=\int z\,dE(z)$. Continuous functional calculus is an isometric
  unital star homomorphism from $C(\sigma(T))$ onto the C*-algebra generated
  by $T$ and the identity. Bounded Borel functions define
  $f(T)=\int f\,dE$, and $\|R(z,T)\|=\operatorname{dist}(z,\sigma(T))^{-1}$
  off the spectrum.

## Reference guide

Conway, Chapters I–VI, gives the Hilbert geometry, Banach principles, and
weak compactness spine, with Stone–Weierstrass (stated in Section 47) in V.8;
Chapters VII–IX supply
the initial spectral results and Chapter XI the Fredholm index.
Brezis, Chapters 1–6, independently develops separation, mapping principles,
reflexivity, variational problems, and compact operator theory. Einsiedler–Ward
connects these foundations with spectral and ergodic applications. These
overlaps, also central to Rudin, Lax, Yosida, and the newer courses listed in
the supplementary bibliography, determine the selection. James and
Krein–Šmulian belong to the broader structural graduate core rather than
every first course. Detailed unbounded spectral theory and semigroup
generation are left to Sections 22 and 24.

Local source copies consulted:

* [Conway, A Course in Functional Analysis](References/Conway1985CourseInFunctionalAnalysis-SpringerGTM96.pdf).
* [Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations](References/Brezis2011FunctionalAnalysisSobolevSpacesPartialDifferentialEquations-SpringerUTX.pdf).
* [Einsiedler–Ward, Functional Analysis, Spectral Theory, and Applications](References/EinsiedlerWard2017FunctionalAnalysisSpectralTheoryApplications-SpringerGTM276.pdf).
