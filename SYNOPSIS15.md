# Synopsis: Core Banach and Hilbert space theory

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects the recurring graduate core of Section 15 of
[CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md): completeness,
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
* **2. Quotients and operator spaces.** If $X,Y$ are Banach and $M\subset X$
  is closed, then $X/M$ and $\mathcal L(X,Y)$ are Banach. A bounded map
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
  Hausdorff $K$ are Banach. Uniform limits preserve continuity and vanishing
  at infinity; absolutely summable series in a Banach space converge in norm.
* **6. Duals of sequence and function spaces.** For $1<p<\infty$,
  $(\ell^p)^*=\ell^{p'}$; also $c_0^*=\ell^1$ and $(\ell^1)^*=\ell^\infty$.
  On a $\sigma$-finite measure space, $(L^p)^*=L^{p'}$ for $1\leq p<\infty$,
  isometrically under integration. The dual of $L^\infty$ need not be $L^1$.
* **7. Riesz representation for continuous functions.** The dual of $C_0(K)$
  is the space of finite regular real or complex Borel measures on $K$, with
  total variation norm, under $f\mapsto\int f\,d\mu$.
* **8. Complemented subspaces.** A closed subspace $M$ of a Banach space
  is complemented exactly when $X=M\oplus N$ for another closed subspace
  $N$. Every finite-dimensional or closed finite-codimensional subspace is
  complemented; arbitrary closed subspaces need not be.

## Hahn–Banach, separation, and duality

For $A\subset X$ let $A^\perp=\{f\in X^*:f|_A=0\}$. The canonical
map $J:X\to X^{**}$ is $(Jx)(f)=f(x)$. A real function $p$ is
**sublinear** if it is subadditive and positively homogeneous.

* **9. Hahn–Banach extension.** A real linear functional on a subspace,
  dominated there by a sublinear function $p$, extends with the same
  domination to the full space. Over either scalar field, every bounded
  linear functional on a subspace extends without increasing its norm.
* **10. Norming functionals.** For every nonzero $x\in X$ there is
  $f\in X^*$ with $\|f\|=1$ and $f(x)=\|x\|$. Hence
  $\|x\|=\sup_{f\in B_{X^*}}|f(x)|$, and $J$ is an isometric embedding.
* **11. Separation of convex sets.** Disjoint convex sets, one of which is
  open, can be separated by a nonzero continuous real linear functional.
  A point outside a closed convex set can be strictly separated from it.
  In complex spaces use real parts of complex linear functionals.
* **12. Distance to a subspace.** For a closed linear subspace $M$,
  $$\operatorname{dist}(x,M)=
    \sup\{|f(x)|:f\in M^\perp,\ \|f\|\leq1\}.$$
  In particular, continuous functionals detect membership in $M$.
* **13. Duality of subspaces and quotients.** For closed $M\subset X$,
  $(X/M)^*$ identifies isometrically with $M^\perp$, while restriction
  induces the isometric identification $X^*/M^\perp\cong M^*$.
* **14. Bipolar theorem.** If $A^\circ=\{f:|f(a)|\leq1\ (a\in A)\}$,
  then $A^{\circ\circ}$, viewed in $X$, is the weak closure of the
  absolutely convex hull of $A\cup\{0\}$. For convex sets, weak and norm
  closures coincide.
* **15. Goldstine theorem.** $J(B_X)$ is weak-star dense in $B_{X^{**}}$.
  This is a density statement about the entire ball, even when $X$ is
  nonreflexive and $J(X)$ is a proper norm-closed subspace of $X^{**}$.

## Baire category and the fundamental mapping principles

A family $\mathcal T\subset\mathcal L(X,Y)$ is **pointwise bounded** if
$\sup_{T\in\mathcal T}\|Tx\|<\infty$ for each $x\in X$.

* **16. Baire category theorem.** A complete metric space is not a countable
  union of closed sets with empty interior. Equivalently, a countable
  intersection of dense open sets is dense.
* **17. Uniform boundedness principle.** A pointwise bounded family of
  bounded linear maps from a Banach space to a normed space has uniformly
  bounded operator norms. Consequently weakly bounded subsets of a normed
  space are norm bounded.
* **18. Open mapping and bounded inverse.** A bounded surjective linear map
  between Banach spaces is open. In particular, a bounded linear bijection
  between Banach spaces has bounded inverse.
* **19. Closed graph theorem.** An everywhere-defined linear map between
  Banach spaces is bounded exactly when its graph is closed in the product
  norm. The requirement that its domain be the whole source matters.
* **20. Convergence on a dense subspace.** If $T_n\in\mathcal L(X,Y)$ are
  uniformly bounded, $Y$ is Banach, and $T_nx$ converges for each $x$ in a
  dense linear subspace, then it converges for every $x\in X$. The limit
  operator is bounded, with norm at most $\sup_n\|T_n\|$.
* **21. Closed range estimates.** For $T\in\mathcal L(X,Y)$ between Banach
  spaces, its range is closed exactly when
  $\operatorname{dist}(x,\ker T)\leq C\|Tx\|$ for some $C$ and all $x$.
  If $T$ is injective, this says that $T$ is bounded below.

## Weak topologies, compactness, and reflexivity

The **weak topology** $\sigma(X,X^*)$ is pointwise convergence against
$X^*$; the **weak-star topology** $\sigma(X^*,X)$ is pointwise convergence
on $X$. A Banach space is **reflexive** if $J$ is onto. Compactness below is
topological compactness, which must be distinguished from sequential
compactness until the relevant theorem is invoked.

* **22. Banach–Alaoglu theorem.** $B_{X^*}$ is weak-star compact. Every
  norm-bounded weak-star closed subset of $X^*$ is therefore weak-star compact.
* **23. Metrizability on dual balls.** If $X$ is separable, the weak-star
  topology of $B_{X^*}$ is metrizable. Thus every bounded sequence in $X^*$
  has a weak-star convergent subsequence. Separability of $X^*$ similarly
  makes the weak topology metrizable on $B_X$.
* **24. Weak lower semicontinuity.** The norm, and every norm lower
  semicontinuous convex function, is weakly lower semicontinuous. Norm-closed
  convex subsets are weakly closed.
* **25. Mazur theorem.** If $x_n\rightharpoonup x$, then $x$ lies in the
  norm closure of the convex hull of each tail of $(x_n)$. Suitable finite
  convex combinations of successive tails converge to $x$ in norm.
* **26. Reflexivity and weak compactness.** A Banach space is reflexive
  exactly when $B_X$ is weakly compact. Closed subspaces and quotients of
  reflexive spaces are reflexive, and $X$ is reflexive exactly when $X^*$ is.
* **27. Eberlein–Šmulian theorem.** A subset of a Banach space is relatively
  weakly compact exactly when every sequence in it has a weakly convergent
  subsequence with limit in the ambient space. In particular, bounded
  sequences in reflexive spaces have weakly convergent subsequences.
* **28. James compactness theorem.** A Banach space is reflexive exactly
  when every $f\in X^*$ attains its norm on $B_X$. More generally,
  a closed bounded convex set is weakly compact exactly when every
  continuous real linear functional attains its supremum there.
* **29. Krein–Milman theorem.** A nonempty compact convex subset of a
  Hausdorff locally convex space is the closed convex hull of its extreme
  points. It applies in particular to weak-star compact dual balls.
* **30. Krein–Šmulian theorem.** A convex subset $C\subset X^*$ is
  weak-star closed exactly when $C\cap rB_{X^*}$ is weak-star closed for
  every $r>0$.
* **31. Separability and duality.** If $X^*$ is separable, then $X$ is
  separable. For reflexive $X$, separability of $X$ and of $X^*$ are
  equivalent. The converse implication fails for general Banach spaces.
* **32. Uniform convexity and reflexivity.** If for each $\varepsilon>0$
  there is $\delta>0$ such that unit-ball vectors with distance at least
  $\varepsilon$ have midpoint norm at most $1-\delta$, then $X$ is
  reflexive (Milman–Pettis). In particular, $L^p$ is reflexive for $1<p<\infty$.
* **33. Weak convergence and norms.** In a uniformly convex space,
  $x_n\rightharpoonup x$ and $\|x_n\|\to\|x\|$ imply $x_n\to x$
  in norm. In Hilbert space the same conclusion follows from the inner
  product identity for $\|x_n-x\|^2$.
* **34. Direct method in reflexive spaces.** A proper weakly lower
  semicontinuous coercive function on a nonempty weakly closed subset of a
  reflexive Banach space attains its infimum, provided that infimum is finite.
  A strictly convex objective on a convex domain has at most one minimizer.

## Hilbert space geometry and variational problems

For $M\subset H$, let $M^\perp=\{x:\langle x,m\rangle=0\ (m\in M)\}$.
An **orthonormal basis** is a maximal orthonormal set, whose closed linear
span is $H$; its expansions are norm limits, not algebraic finite expansions.

* **35. Cauchy–Schwarz and polarization.**
  $|\langle x,y\rangle|\leq\|x\|\|y\|$, with equality for nonzero
  vectors exactly when they are linearly dependent. The norm determines
  the inner product by polarization.
* **36. Jordan–von Neumann theorem.** A norm is induced by an inner
  product exactly when it satisfies
  $\|x+y\|^2+\|x-y\|^2=2\|x\|^2+2\|y\|^2$.
* **37. Projection onto closed convex sets.** Every nonempty closed convex
  $C\subset H$ has a unique nearest point $P_Cx$ to each $x$. It is
  characterized by $\operatorname{Re}\langle x-P_Cx,y-P_Cx\rangle\leq0$
  for $y\in C$, and $P_C$ is nonexpansive.
* **38. Orthogonal decomposition.** For a closed linear subspace $M$,
  $H=M\oplus M^\perp$. Its nearest-point map is a bounded self-adjoint
  projection; every bounded self-adjoint projection arises this way.
* **39. Riesz–Fréchet representation.** Every $f\in H^*$ has a unique
  representation $f(x)=\langle x,y\rangle$, with $\|f\|=\|y\|$.
  Thus $H$ is reflexive; the identification with its linear dual is
  conjugate linear over $\mathbb C$.
* **40. Bessel and Parseval.** For an orthonormal family $(e_i)$,
  $\sum_i|\langle x,e_i\rangle|^2\leq\|x\|^2$. If the family is a
  basis, equality holds and $x=\sum_i\langle x,e_i\rangle e_i$ in norm.
  Only countably many coefficients of a given vector are nonzero.
* **41. Classification of Hilbert spaces.** Every Hilbert space has an
  orthonormal basis and is isometrically isomorphic to $\ell^2(I)$ for its
  basis index set $I$. Two Hilbert spaces are unitarily isomorphic exactly
  when their orthonormal bases have the same cardinality.
* **42. Lax–Milgram theorem.** If a bounded sesquilinear form $a$ on $H$
  is linear in its first variable and
  $\operatorname{Re}a(u,u)\geq\alpha\|u\|^2$ with $\alpha>0$, then for
  every bounded conjugate-linear functional $F$ there is a unique $u$ such
  that $a(u,v)=F(v)$ for all $v$, and $\|u\|\leq\alpha^{-1}\|F\|$.
* **43. Stampacchia variational inequality.** In a real Hilbert space, for
  a bounded coercive bilinear form $a$, a nonempty closed convex set $C$,
  and $f\in H^*$, there is a unique $u\in C$ satisfying
  $a(u,v-u)\geq f(v-u)$ for every $v\in C$.
* **44. Galerkin approximation and Céa lemma.** Under the Lax–Milgram
  assumptions, the solution $u_V$ in any closed subspace $V$ satisfies
  $\|u-u_V\|\leq(\|a\|/\alpha)\inf_{v\in V}\|u-v\|$.
  Dense nested approximation spaces therefore give norm convergence.

## Adjoints, compactness, and the Fredholm alternative

The **Banach adjoint** is $T^*f=f\circ T$. On Hilbert spaces it corresponds
to the operator determined by $\langle Tx,y\rangle=\langle x,T^*y\rangle$.
An operator is **compact** if it maps bounded sets to relatively compact
sets; **weakly compact** uses relative weak compactness instead.

* **45. Adjoint identities.** $\|T^*\|=\|T\|$, $(ST)^*=T^*S^*$, and on
  Hilbert spaces $\|T^*T\|=\|T\|^2$. Moreover
  $(\operatorname{ran}T)^\perp=\ker T^*$ and
  $\overline{\operatorname{ran}T}=(\ker T^*)_\perp$.
* **46. Closed range theorem.** For bounded maps between Banach spaces,
  $\operatorname{ran}T$ is norm closed exactly when $\operatorname{ran}T^*$
  is norm closed. In Hilbert spaces this yields
  $\operatorname{ran}T=(\ker T^*)^\perp$ and
  $\operatorname{ran}T^*=(\ker T)^\perp$ when the ranges are closed.
* **47. Gantmacher criterion.** $T:X\to Y$ is weakly compact exactly when
  $T^{**}(X^{**})\subset J_Y(Y)$. In particular, every bounded operator
  factoring through a reflexive space is weakly compact.
* **48. Compact operator ideal.** Compact operators form a norm-closed
  linear subspace and are preserved by composition with bounded operators.
  Every finite-rank operator is compact. The identity on an infinite-dimensional
  Banach space is not compact.
* **49. Schauder theorem.** An operator between Banach spaces is compact
  exactly when its adjoint is compact.
* **50. Compact operators and weak convergence.** If $T$ is compact and
  $x_n\rightharpoonup x$, then $Tx_n\to Tx$ in norm. On a reflexive
  source, the property that weakly convergent sequences have norm-convergent
  images characterizes compactness.
* **51. Finite-rank approximation in Hilbert space.** A compact operator
  between Hilbert spaces is a norm limit of finite-rank operators. On general
  Banach spaces this assertion requires approximation hypotheses and can fail.
* **52. Riesz–Fredholm alternative.** For compact $K:X\to X$, $I-K$ has
  closed range, finite-dimensional kernel and cokernel of equal dimension.
  It is injective exactly when it is surjective, and then has bounded inverse.
* **53. Solvability condition.** In result 52, $(I-K)x=y$ is solvable exactly
  when $f(y)=0$ for all $f\in\ker(I-K^*)$. Solutions, when they exist,
  form an affine translate of $\ker(I-K)$.
* **54. Compact spectral structure.** For compact $K$ on a complex Banach
  space, every nonzero spectral value is an isolated eigenvalue with finite
  algebraic multiplicity. There are only finitely many outside any disk
  about zero. In infinite dimension, zero belongs to the spectrum.
* **55. Compact self-adjoint spectral theorem.** A compact self-adjoint
  operator on $H$ has an orthonormal basis of eigenvectors, including a basis
  of its kernel. Its nonzero eigenvalues are real, of finite multiplicity,
  and tend to zero if infinite in number.
* **56. Singular value decomposition.** A compact operator $T:H_1\to H_2$
  has an expansion $Tx=\sum_ns_n\langle x,e_n\rangle f_n$ with orthonormal
  systems, $s_n>0$, and $s_n\to0$ if infinite. Truncation gives best
  rank-at-most-$n$ approximation error $s_{n+1}$ in operator norm, with
  the singular-value list padded by zeros in the finite-rank case.

## First spectral and fixed-point principles

The spectral statements in this section use complex spaces. For bounded
$T$ on a nonzero complex Banach space,
$\sigma(T)=\{\lambda:\lambda I-T\text{ is not invertible}\}$ and
$R(\lambda,T)=(\lambda I-T)^{-1}$ on its complement. An operator is
**self-adjoint** if $T=T^*$, **normal** if $TT^*=T^*T$, and **positive**
if $\langle Tx,x\rangle\geq0$ for all $x$.

* **57. Neumann series and resolvent.** If $\|S\|<1$, then
  $(I-S)^{-1}=\sum_{n\geq0}S^n$ in operator norm. Invertible operators
  form an open set; the resolvent is holomorphic and satisfies
  $R(\lambda,T)-R(\mu,T)=(\mu-\lambda)R(\lambda,T)R(\mu,T)$.
* **58. Spectrum and spectral radius.** $\sigma(T)$ is nonempty compact,
  contained in $\{|\lambda|\leq\|T\|\}$, and
  $r(T)=\lim_n\|T^n\|^{1/n}=\inf_n\|T^n\|^{1/n}$.
* **59. Polynomial spectral mapping.** For every complex polynomial $p$,
  $\sigma(p(T))=p(\sigma(T))$. The corresponding rational formula holds
  when all poles avoid $\sigma(T)$.
* **60. Self-adjoint spectral bounds.** A bounded self-adjoint operator has
  real spectrum and norm $\sup_{\lambda\in\sigma(T)}|\lambda|$.
  It is positive exactly when its spectrum lies in $[0,\infty)$.
* **61. Positive square root and polar decomposition.** Every bounded
  positive operator has a unique bounded positive square root. Every bounded
  $T:H_1\to H_2$ has a unique factorization $T=U(T^*T)^{1/2}$ where $U$
  is the partial isometry with initial space $\overline{\operatorname{ran}T^*}$
  and final space $\overline{\operatorname{ran}T}$.
* **62. Bounded normal spectral theorem.** For normal $T$ there is a unique
  projection-valued measure $E$ on $\sigma(T)$ with
  $T=\int z\,dE(z)$. Continuous functional calculus is an isometric
  unital star homomorphism from $C(\sigma(T))$ onto the C*-algebra generated
  by $T$ and the identity.
* **63. Banach contraction principle.** A contraction with Lipschitz
  constant $q<1$ on a nonempty complete metric space has a unique fixed
  point. Its iterates converge from every starting point, with
  $d(x_n,x_*)\leq q^nd(x_0,x_1)/(1-q)$.
* **64. Schauder fixed-point theorem.** If $C$ is a nonempty closed convex
  subset of a Banach space and $F:C\to C$ is continuous with relatively
  compact image, then $F$ has a fixed point.
* **65. Mean ergodic theorem on reflexive spaces.** If $T$ is power bounded
  on a reflexive Banach space, then $n^{-1}\sum_{k=0}^{n-1}T^kx$ converges
  in norm for every $x$. The resulting projection gives
  $X=\ker(I-T)\oplus\overline{\operatorname{ran}(I-T)}$.
* **66. Arzelà–Ascoli theorem.** For compact Hausdorff $K$, a subset of
  $C(K)$ is relatively norm compact exactly when it is pointwise bounded
  and equicontinuous. This supplies the basic compactness mechanism for
  many integral operators and fixed-point applications.

## Reference guide

Conway, Chapters I–VI, gives the Hilbert geometry, Banach principles, and
weak compactness spine; Chapters VII–IX supply the initial spectral results.
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
