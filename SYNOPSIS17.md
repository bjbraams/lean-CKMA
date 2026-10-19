# Synopsis: Banach space geometry, bases, and operator ideals

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-17);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects the recurring structural core of Section 17 of
[CKMA-bib.md](CKMA-bib.md#ckma-17). Its questions
concern the subspaces a Banach space must contain, the expansions it admits,
its finite-dimensional geometry, and the classes of operators controlled by
that geometry. The selection combines the basic-sequence tradition with
type and cotype, renorming, and summing operators. Scalar fields are real
or complex; statements involving convex bodies or differentiability use real
spaces unless specified.

Write $[x_n]$ for the closed linear span of a sequence. A **Schauder basis**
$(e_n)$ gives a unique norm-convergent expansion
$x=\sum_ne_n^*(x)e_n$ for every $x$; a **basic sequence** is a basis for
its own closed span. Two basic sequences are **equivalent** if the map
taking corresponding vectors to each other extends to an isomorphism of
their spans. Equivalent norms preserve the Banach space isomorphism class,
but can change its metric geometry considerably.

The **approximation property** means that the identity can be approximated
uniformly on each compact subset by finite-rank operators. The **bounded
approximation property** requires such operators with a common operator-norm
bound.

## Bases, block sequences, and duality

The partial-sum projections are $P_nx=\sum_{j\leq n}e_j^*(x)e_j$.
A **block sequence** has vectors supported on successive disjoint finite
intervals of a basis. A basis is **unconditional** if every expansion
converges under every permutation, and **shrinking** if $(e_n^*)$ is a
basis of $X^*$. It is **boundedly complete** if bounded partial sums
$\sum_{j\leq n}a_je_j$ always converge.

* **1. Basis projections and coordinates.** Coordinate functionals of a
  Schauder basis are continuous, $\sup_n\|P_n\|<\infty$, and
  $P_nx\to x$. Conversely a complete biorthogonal system with uniformly
  bounded partial-sum operators is a Schauder basis.
* **2. Basic sequence criterion.** A sequence of nonzero vectors is basic
  exactly when there is $C$ such that
  $\|\sum_{j\leq m}a_jx_j\|\leq C\|\sum_{j\leq n}a_jx_j\|$ for
  all $m\leq n$ and scalar coefficients. This is the uniform boundedness
  criterion for its initial-segment projections.
* **3. Equivalence criterion.** Basic sequences $(x_n)$ and $(y_n)$ are
  equivalent exactly when constants $0<c\leq C<\infty$ give
  $$c\Big\|\sum a_nx_n\Big\|\leq\Big\|\sum a_ny_n\Big\|
    \leq C\Big\|\sum a_nx_n\Big\|$$
  for every finitely supported scalar sequence.
* **4. Block basic sequences.** Every sequence of nonzero successive
  blocks of a Schauder basis is basic, with basis constant at most that of
  the original basis. Blocks of an unconditional basis are unconditional.
* **5. Small perturbations.** If $(x_n)$ is basic with coordinate
  functionals $x_n^*$ on $[x_n]$, and
  $\sum_n\|x_n^*\|\|x_n-y_n\|<1$, then $(y_n)$ is basic and equivalent
  to $(x_n)$. If $[x_n]$ is complemented by a projection $P$ and
  $\|P\|\sum_n\|x_n^*\|\|x_n-y_n\|<1$, then $[y_n]$ is also complemented.
* **6. Existence of basic sequences.** Every infinite-dimensional Banach
  space contains an infinite basic sequence (Mazur); the space itself need
  not have a basis (result 32).
* **7. Bessaga–Pełczyński selection principle.** A seminormalized weakly
  null sequence in a space with a Schauder basis has a subsequence equivalent
  to a block sequence of that basis. Here seminormalized means
  $0<\inf_n\|x_n\|\leq\sup_n\|x_n\|<\infty$. Embedding a separable
  space into $C[0,1]$ shows that in every Banach space a seminormalized
  weakly null sequence has a basic subsequence.
* **8. Unconditionality criterion.** A basis is unconditional exactly when
  its coordinate projections onto arbitrary finite sets are uniformly
  bounded. Equivalently, changing coefficient signs or scalar phases is
  uniformly bounded on finite sums. It can then be renormed to have
  unconditional constant one.
* **9. Shrinking basis criterion.** A basis is shrinking exactly when
  $\|f-P_n^*f\|\to0$ for every $f\in X^*$. Equivalently, every bounded
  block sequence of the basis is weakly null.
* **10. James basis theorem.** A Banach space with a Schauder basis is
  reflexive exactly when the basis is both shrinking and boundedly complete.
* **11. Duality of basis properties.** If a basis of $X$ is shrinking, its
  dual basis in $X^*$ is boundedly complete. If it is boundedly complete,
  $X$ identifies with the dual of $[e_n^*]\subset X^*$ via evaluation,
  with equivalent norms.
* **12. Unconditional reflexivity criterion.** A Banach space with an
  unconditional basis is reflexive exactly when it contains no subspace
  isomorphic to $c_0$ or $\ell^1$. For that basis, absence of $\ell^1$
  characterizes shrinking and absence of $c_0$ characterizes bounded completeness.
* **70. James quasi-reflexive space.** The James space $J$ consists of real
  sequences $x$ with $x(k)\to0$ and finite norm
  $$\|x\|_J=\sup\frac1{\sqrt2}\Big((x(p_m)-x(p_0))^2
    +\sum_{i=1}^m(x(p_i)-x(p_{i-1}))^2\Big)^{1/2},$$
  the supremum over $m$ and $p_0<p_1<\cdots<p_m$. The unit vectors form a
  shrinking basis that is not boundedly complete. $J$ has codimension one in
  $J^{**}$, yet $J$ is isometric to $J^{**}$ (James): a nonreflexive space
  isomorphic to its bidual. It contains no copy of $c_0$ or $\ell^1$, so by
  result 12 it has no unconditional basis; it does not even embed in a space
  with an unconditional basis, and it is not isomorphic to $J\oplus J$.
* **13. Basis and approximation property.** A Schauder basis gives bounded
  finite-rank approximations to the identity, converging uniformly on compact
  sets. Thus a space with a basis has the bounded approximation property.
* **14. Greedy basis characterization.** For a normalized basis, retaining
  the $m$ largest coefficients gives approximations within a uniform factor
  of the best $m$-term error exactly when the basis is unconditional and
  democratic. Democracy means that $\|\sum_{j\in A}e_j\|$ and
  $\|\sum_{j\in B}e_j\|$ are uniformly comparable whenever $|A|=|B|$.

## Weak sequences and unconditional series

A series $\sum x_n$ is **weakly unconditionally Cauchy** if
$\sum_n|f(x_n)|<\infty$ for every $f\in X^*$. A sequence is **weakly
Cauchy** if every scalar sequence $f(x_n)$ is Cauchy. These conditions do
not themselves assert convergence to a vector of $X$.

* **15. Unconditional convergence criteria.** A series is unconditionally
  norm convergent exactly when the net of sums over finite subsets of
  $\mathbb N$ converges; equivalently, its tails over all finite subsets
  tend uniformly to zero. Every rearrangement then has the same sum.
* **16. Weak unconditional boundedness.** A series is weakly unconditionally
  Cauchy exactly when its finite signed sums are uniformly bounded in norm.
  Over complex scalars one may equivalently use all coefficients of modulus
  at most one.
* **17. Orlicz–Pettis theorem.** If every subseries of $\sum x_n$ converges
  weakly to a vector of $X$, then the series converges unconditionally in
  norm. Scalar absolute summability alone does not supply the subseries limits.
* **18. Bessaga–Pełczyński $c_0$ criterion.** $X$ contains no copy of $c_0$
  exactly when every weakly unconditionally Cauchy series in $X$ is
  unconditionally norm convergent.
* **19. Dvoretzky–Rogers theorem.** Every infinite-dimensional Banach space
  contains an unconditionally convergent series $\sum x_n$ for which
  $\sum\|x_n\|=\infty$. Unconditional and absolute convergence of all
  series agree exactly in finite dimension.
* **20. Schur property of $\ell^1$.** Weakly convergent sequences in
  $\ell^1$ converge in norm. Consequently weakly compact subsets of
  $\ell^1$ are norm compact.
* **21. Rosenthal $\ell^1$ theorem.** Every bounded sequence in a Banach
  space has either a weakly Cauchy subsequence or a subsequence equivalent
  to the standard basis of $\ell^1$.
* **22. James distortion theorem.** If $X$ contains a subspace isomorphic
  to $c_0$ (respectively $\ell^1$), then for every $\varepsilon>0$ it
  contains a subspace $(1+\varepsilon)$-isomorphic to $c_0$ (respectively
  $\ell^1$). In contrast, $\ell^p$ for $1<p<\infty$ is arbitrarily
  distortable: for every $\lambda>1$ it admits an equivalent norm that is
  $\lambda$-distorted on every infinite-dimensional subspace
  (Odell–Schlumprecht).
* **23. Dunford–Pettis compactness in $L^1$.** On a finite measure space,
  a bounded subset of $L^1$ is relatively weakly compact exactly when it is
  uniformly integrable. The result separates weak compactness from norm
  compactness in this nonreflexive space.
* **24. Dunford–Pettis property of classical spaces.** For $X=L^1(\mu)$
  or $C(K)$, with $K$ compact Hausdorff, every weakly compact operator
  $T:X\to Y$ sends weakly null sequences to norm-null sequences.

## Classical subspaces, quotients, and complemented copies

* **25. Banach–Mazur universality.** Every separable Banach space embeds
  linearly isometrically into $C[0,1]$. Every separable Banach space is also
  isomorphic to a quotient of $\ell^1$.
* **71. Milutin theorem.** For every uncountable compact metric space $K$,
  $C(K)$ is isomorphic to $C[0,1]$. Thus, for instance, $C(\Delta)$ on the
  Cantor set, $C([0,1]^n)$, and $C[0,1]$ are mutually isomorphic, although
  not isometric.
* **26. Sobczyk theorem.** Every copy of $c_0$ in a separable Banach space
  is complemented. For an isometric copy there is a projection of norm at
  most two. The ambient separability assumption is essential.
* **27. Phillips noncomplementability theorem.** $c_0$ is not complemented
  in $\ell^\infty$, although it is a closed subspace. Thus closed subspaces
  of Banach spaces need not split.
* **28. Pitt theorem.** If $1\leq q<p<\infty$, every bounded linear
  operator $\ell^p\to\ell^q$ is compact. In particular, the spaces
  $\ell^p$, $1\leq p<\infty$, are pairwise nonisomorphic.
* **29. Pełczyński decomposition method.** If each of $X$ and $Y$ is
  isomorphic to a complemented subspace of the other, and
  $X\cong\ell^p(X)$ for some $1\leq p<\infty$ (or $X\cong c_0(X)$), then
  $X\cong Y$. Consequently $\ell^p$, $1\leq p<\infty$, and $c_0$ are
  prime: every infinite-dimensional complemented subspace is isomorphic to
  the whole space (Pełczyński). Every infinite-dimensional closed subspace of
  these spaces contains a further subspace isomorphic to the whole space and
  complemented in it. Up to equivalence, $c_0$, $\ell^1$, and $\ell^2$ are
  the only spaces with a unique normalized unconditional basis
  (Lindenstrauss–Pełczyński, Lindenstrauss–Zippin).
* **30. Haar basis.** The Haar system, with the constant function included,
  is a Schauder basis of $L^p[0,1]$ for $1\leq p<\infty$ and an
  unconditional basis for $1<p<\infty$ (Paley, Marcinkiewicz). The space
  $L^1[0,1]$ has no unconditional basis at all and does not embed in a space
  with one.
* **31. Subspaces of $L^p$.** For $1\leq p<\infty$ the Rademacher
  functions span a copy of $\ell^2$ in $L^p[0,1]$ (Khintchine), complemented
  when $1<p<\infty$. For $2<p<\infty$ every infinite-dimensional closed
  subspace of $L^p$ is either isomorphic to $\ell^2$ and complemented, or
  contains a copy of $\ell^p$ complemented in $L^p$ (Kadec–Pełczyński).
  For $1\leq p<\infty$, $p\neq2$, $L^p[0,1]$ and $\ell^p$ are not isomorphic.
* **32. Enflo approximation counterexample.** There exist separable Banach
  spaces without the approximation property, hence without a Schauder basis.
  Not every compact operator between Banach spaces is a norm limit of
  finite-rank operators.
* **33. Complemented-subspace characterization of Hilbert space.** A Banach
  space in which every closed subspace is complemented is isomorphic to a
  Hilbert space (Lindenstrauss–Tzafriri). Orthogonal projections give the
  converse for Hilbert spaces and their isomorphic copies.
* **34. Gowers–Maurey and Gowers dichotomy.** Tsirelson's space is a
  reflexive space with unconditional basis containing no copy of $c_0$ or
  any $\ell^p$. There exist hereditarily indecomposable spaces, in which no
  closed infinite-dimensional subspace is a topological direct sum of two
  infinite-dimensional closed subspaces; on a complex such space every
  operator is $\lambda I+S$ with $S$ strictly singular (no restriction of $S$
  to an infinite-dimensional subspace is an isomorphism), so it is isomorphic to
  no proper subspace (Gowers–Maurey). Every infinite-dimensional Banach space
  contains either a hereditarily indecomposable subspace or a subspace with an
  unconditional basis (Gowers). With Komorowski–Tomczak-Jaegermann, this shows
  that $\ell^2$ is the only space isomorphic to all its infinite-dimensional
  closed subspaces.

## Local geometry, random sums, and finite representability

Let $(r_j)$ be independent symmetric signs. $X$ has **type $p$**,
$1\leq p\leq2$, if
$(\mathbb E\|\sum r_jx_j\|^2)^{1/2}\leq T(\sum\|x_j\|^p)^{1/p}$;
it has **cotype $q$**, $2\leq q<\infty$, if
$(\sum\|x_j\|^q)^{1/q}\leq C(\mathbb E\|\sum r_jx_j\|^2)^{1/2}$.
The **Banach–Mazur distance** between finite-dimensional isomorphic spaces
is $d(X,Y)=\inf_T\|T\|\|T^{-1}\|$. $Y$ is **finitely representable**
in $X$ if each finite-dimensional subspace of $Y$ embeds into $X$ with
distortion at most $1+\varepsilon$, for every $\varepsilon>0$.

* **35. Kahane–Khintchine inequality.** For $0<p,q<\infty$, the moments
  $(\mathbb E\|\sum r_jx_j\|^p)^{1/p}$ and
  $(\mathbb E\|\sum r_jx_j\|^q)^{1/q}$ are equivalent with constants
  depending only on $p,q$, independently of the space and the finite sequence.
  The corresponding statement holds for Gaussian sums.
* **36. Type and cotype of $L^p$.** For $1\leq p<\infty$, $L^p$ has
  type $\min(p,2)$ and cotype $\max(p,2)$. These exponents are optimal
  for the infinite classical $\ell^p$ spaces and nonatomic $L^p$ spaces.
* **37. Stability of type and cotype.** Type and cotype pass to subspaces
  and are invariant under isomorphism; type also passes to quotients.
  Type $p>1$ of $X$ implies cotype $p'$ of $X^*$.
* **38. Kwapień theorem.** A Banach space is isomorphic to a Hilbert space
  exactly when it has both type two and cotype two.
* **73. Kwapień–Maurey factorization and Maurey extension.** If $X$ has
  type two and $Y$ has cotype two, every bounded $T:X\to Y$ factors through a
  Hilbert space. More strongly (Maurey), if $E\subseteq X$ is a closed
  subspace and $T:E\to Y$ is bounded, there are a Hilbert space $H$ and
  operators $S:X\to H$, $R:H\to Y$ with $RS|_E=T$ and
  $\|R\|\|S\|\leq T_2(X)C_2(Y)\|T\|$, the product of the type-two and
  cotype-two constants. In particular every subspace of a type-two space
  that is isomorphic to a Hilbert space is complemented.
* **74. Maurey–Nikishin factorization.** Let $X$ have type $r>1$, let
  $\mu$ be $\sigma$-finite, $1\leq p<q<r$, and let $T:X\to L^p(\mu)$ be
  bounded. Then there is a strictly positive probability density $h$ such
  that $x\mapsto h^{-1/p}Tx$ is bounded from $X$ into $L^q(h\,d\mu)$; thus
  $T$ factors through $L^q$ after a change of density. For $q=r<2$ the
  conclusion can fail.
* **39. Dvoretzky theorem.** Every infinite-dimensional Banach space
  contains, for every $n$ and $\varepsilon>0$, an $n$-dimensional subspace
  with Banach–Mazur distance at most $1+\varepsilon$ from $\ell_2^n$.
  Equivalently, $\ell^2$ is finitely representable in every such space.
  Quantitatively, an $n$-dimensional normed space contains
  $(1+\varepsilon)$-Euclidean subspaces of dimension $k\geq c(\varepsilon)\log n$
  (Milman's concentration proof), and $\ell_\infty^n$ shows that the order
  $\log n$ cannot be improved in general.
* **72. Kadets–Snobar theorem.** Every $n$-dimensional subspace $E$ of a
  Banach space $Y$ is the range of a projection $P$ on $Y$ with
  $\|P\|\leq\sqrt n$. The proof uses an isomorphism $S:E\to\ell_2^n$ with
  $\|S^{-1}\|=1$ and $\pi_2(S)\leq\sqrt n$, refining John's ellipsoid
  theorem (SYNOPSIS12, item 11), and extends $S$ to $Y$ with the same
  two-summing norm via Pietsch's theorem (results 54–55). The order
  $\sqrt n$ is optimal: the projection constants of $\ell_2^n$ grow like
  $\sqrt{2n/\pi}$.
* **41. Krivine theorem.** For every normalized basic sequence there is
  $p\in[1,\infty]$ such that, for each $n$ and $\varepsilon>0$, some
  normalized successive blocks are $(1+\varepsilon)$-equivalent to the
  unit vector basis of $\ell_p^n$. For $p=\infty$ this is block finite
  representability of $c_0$.
* **42. Local reflexivity.** Given finite-dimensional $E\subset X^{**}$,
  $F\subset X^*$, and $\varepsilon>0$, there is $T:E\to X$ with
  $(1-\varepsilon)\|u\|\leq\|Tu\|\leq(1+\varepsilon)\|u\|$,
  $f(Tu)=u(f)$ for $f\in F$, and $T(Jx)=x$ whenever $Jx\in E$.
* **43. Finite cotype criterion.** $X$ has finite cotype exactly when the
  spaces $\ell_\infty^n$ do not embed into $X$ with uniformly bounded
  distortions (Maurey–Pisier).
* **44. Nontrivial type criterion.** $X$ has type $p>1$ for some $p$
  exactly when the spaces $\ell_1^n$ do not embed with uniformly bounded
  distortions. This is also equivalent to $K$-convexity, the uniform
  boundedness of the Rademacher projections on $L^2$ with values in $X$.

## Convexity, smoothness, and Radon–Nikodým geometry

The **modulus of convexity** is
$\delta_X(\varepsilon)=\inf\{1-\|(x+y)/2\|:x,y\in B_X,
\|x-y\|\geq\varepsilon\}$. The **modulus of smoothness** is
$\rho_X(t)=\sup_{\|x\|=\|y\|=1}(\|x+ty\|+\|x-ty\|)/2-1$.
Uniform convexity means $\delta_X(\varepsilon)>0$ for $\varepsilon>0$;
uniform smoothness means $\rho_X(t)/t\to0$. A space is **superreflexive**
if every Banach space finitely representable in it is reflexive.

The **Radon–Nikodým property** means that every countably additive
$X$-valued measure of bounded variation, absolutely continuous with respect
to a finite positive measure, has a Bochner integrable density. Its
Lipschitz and martingale characterizations are SYNOPSIS18, items 12–13.

* **45. Convexity–smoothness duality.** $X$ is uniformly smooth exactly
  when $X^*$ is uniformly convex; $X$ is uniformly convex exactly when
  $X^*$ is uniformly smooth. Each of these properties implies reflexivity.
* **46. Superreflexive renorming theorem.** A Banach space is superreflexive
  exactly when it admits an equivalent uniformly convex norm, and exactly
  when it admits an equivalent uniformly smooth norm (Enflo, James). Such a
  norm can be chosen with moduli of power type (Pisier).
* **47. Smooth norm and supporting functional.** The norm is Gâteaux
  differentiable at $x\ne0$ exactly when there is a unique norm-one real
  functional attaining $\|x\|$ at $x$. This functional is the derivative.
* **48. Separable renorming.** Every separable Banach space admits an
  equivalent locally uniformly rotund norm. Here local uniform rotundity
  means that $\|x_n\|=\|x\|=1$ and $\|x_n+x\|\to2$ imply
  $\|x_n-x\|\to0$.
* **49. Dentability and the Radon–Nikodým property.** $X$ has the
  Radon–Nikodým property exactly when every nonempty bounded subset has
  slices of arbitrarily small diameter. A slice is the intersection with
  $\{x:f(x)>\sup f(A)-\alpha\}$ for some real $f\in X^*$ and $\alpha>0$.
* **50. Asplund characterization.** $X$ is Asplund, meaning that every
  separable subspace has separable dual, exactly when $X^*$ has the
  Radon–Nikodým property. Equivalently, every continuous convex function on
  an open convex subset is Fréchet differentiable on a dense $G_\delta$ set.

## Summing operators, tensor norms, and approximation

An operator $T:X\to Y$ is **absolutely $p$-summing**, $1\leq p<\infty$,
if the least constant $\pi_p(T)$ in
$$\Big(\sum_j\|Tx_j\|^p\Big)^{1/p}
 \leq\pi_p(T)\sup_{f\in B_{X^*}}
                  \Big(\sum_j|f(x_j)|^p\Big)^{1/p}$$
is finite. An **operator ideal** is stable under addition and composition
on either side by bounded maps. A **nuclear operator** has a representation
$Tx=\sum_j f_j(x)y_j$ with $\sum_j\|f_j\|\|y_j\|<\infty$.

* **52. Summing ideal property.** Absolutely $p$-summing maps form a Banach
  operator ideal, and $\pi_p(ATB)\leq\|A\|\pi_p(T)\|B\|$.
  Every finite-rank operator is $p$-summing.
* **53. Inclusion theorem.** If $1\leq p\leq q<\infty$, then every
  $p$-summing map is $q$-summing and $\pi_q(T)\leq\pi_p(T)$.
* **54. Pietsch domination theorem.** $T$ is $p$-summing exactly when
  some regular Borel probability measure $\mu$ on weak-star compact
  $B_{X^*}$ satisfies
  $$\|Tx\|\leq C\left(\int_{B_{X^*}}|f(x)|^p\,d\mu(f)\right)^{1/p}.$$
  The optimal domination constant equals $\pi_p(T)$.
* **55. Pietsch factorization.** Every $p$-summing operator factors through
  the closure in $L^p(\mu)$ of the evaluation functions $f\mapsto f(x)$,
  with the first map the canonical evaluation map and the second bounded.
* **56. Hilbert–Schmidt identification.** For operators between Hilbert
  spaces, being two-summing is equivalent to being Hilbert–Schmidt
  ($\sum_j\|Te_j\|^2<\infty$ for an orthonormal basis $(e_j)$), and
  $\pi_2(T)^2=\sum_j\|Te_j\|^2$ for any orthonormal basis.
* **57. Grothendieck inequality.** There is a scalar-field-dependent
  universal $K_G$ such that for every finite scalar matrix $(a_{ij})$ and
  unit vectors $u_i,v_j$ in a Hilbert space,
  $$\left|\sum_{i,j}a_{ij}\langle u_i,v_j\rangle\right|
    \leq K_G\sup_{|s_i|,|t_j|\leq1}
                 \left|\sum_{i,j}a_{ij}s_it_j\right|.$$
* **58. Grothendieck summing theorem.** Every bounded operator
  $\ell^1\to H$, with $H$ Hilbert, is one-summing, with a universal
  bound on its summing norm in terms of its operator norm.
* **59. Nuclear ideal properties.** Nuclear operators are compact and
  one-summing. Their nuclear norm is the infimum of
  $\sum_j\|f_j\|\|y_j\|$ over all nuclear representations, and satisfies
  the operator ideal inequality.
* **60. Projective tensor representation.** Nuclear operators $X\to Y$
  are the image of the canonical map
  $X^*\widehat\otimes_\pi Y\to\mathcal L(X,Y)$. The nuclear norm is
  the quotient norm of this map; the map need not be injective.
* **61. Approximation property criterion.** $X$ has the approximation
  property exactly when, for every Banach space $Y$, finite-rank maps
  $Y\to X$ are norm dense in the compact maps $Y\to X$.
* **62. Approximation and tensors.** If $Y$ has the approximation property,
  the canonical map $X^*\widehat\otimes_\pi Y\to\mathcal L(X,Y)$ is
  injective for every $X$. This restores uniqueness of the nuclear tensor
  associated with an operator.
* **63. Trace of nuclear operators.** On a space with the approximation
  property, a nuclear endomorphism has a well-defined trace
  $\operatorname{tr}T=\sum_j f_j(y_j)$, independent of the nuclear
  representation, with $|\operatorname{tr}T|\leq\|T\|_{\rm nuc}$.
* **64. Approximation numbers.** For $a_n(T)=\inf_{\operatorname{rank}R<n}
  \|T-R\|$, one has $a_n(ATB)\leq\|A\|a_n(T)\|B\|$ and
  $a_{m+n-1}(S+T)\leq a_m(S)+a_n(T)$. On Hilbert spaces the
  approximation numbers of a compact operator are its singular values.

## Metric structure and nonlinear equivalence

* **65. Mazur–Ulam theorem.** Every surjective isometry between real
  normed spaces is affine. After translating the image of zero to zero,
  it is a real linear isometry.
* **66. Mankiewicz extension theorem.** A bijective isometry between open
  connected subsets of real normed spaces extends uniquely to an affine
  isometry of the ambient spaces. In particular this holds for their open
  unit balls.
* **75. Lipschitz-free spaces.** For a metric space $M$ with base point
  $0$, let $\mathrm{Lip}_0(M)$ be the Banach space of real Lipschitz functions
  vanishing at $0$, normed by the Lipschitz constant. The **free space**
  $\mathcal F(M)$ is the closed span of the evaluations $\delta(x)$ in
  $\mathrm{Lip}_0(M)^*$. Then $\delta:M\to\mathcal F(M)$ is an isometric
  embedding, $\mathcal F(M)^*=\mathrm{Lip}_0(M)$ isometrically, and every
  Lipschitz map from $M$ into a Banach space vanishing at $0$ extends uniquely
  to a bounded linear map on $\mathcal F(M)$ with the same norm.
  If a separable Banach space $X$ embeds isometrically, not necessarily
  linearly, into a Banach space $Y$, then $Y$ contains a linear isometric
  copy of $X$ (Godefroy–Kalton).
* **67. Rademacher theorem with Banach target.** If $X$ has the
  Radon–Nikodým property, every Lipschitz map from an open subset of
  $\mathbb R^n$ into $X$ is Fréchet differentiable almost everywhere.
* **68. Ribe finite-dimensional invariance.** Uniformly homeomorphic
  Banach spaces are crudely finitely representable in each other:
  each finite-dimensional subspace of either space embeds
  into the other with distortion bounded independently of its dimension.
  Thus uniform metric equivalence retains substantial local linear geometry.
* **69. Bourgain embedding theorem.** Every $n$-point metric space embeds
  into $\ell^2$ with bi-Lipschitz distortion $O(\log n)$. Expander graphs show
  that this order is optimal (Linial–London–Rabinovich).

## Reference guide

Albiac–Kalton supplies the main route through bases, weak sequences,
classical spaces, type and cotype, finite-dimensional structure, and nonlinear
geometry. Diestel independently develops the sequence and series theorems;
Diestel–Jarchow–Tonge provides the systematic summing-operator and
factorization theory. Ryan clarifies tensor representations and approximation
properties; Albiac–Kalton, Chapters 3, 4, 7, 13, and 14, also cover the James
space, Milutin's theorem, Maurey's factorization theorems, the Kadets–Snobar
theorem, and Lipschitz-free spaces. These themes overlap with Lindenstrauss–Tzafriri, Wojtaszczyk,
Pisier, and the geometry handbooks; Albiac–Kalton, Chapters 9 and 11, treat
uniqueness of unconditional bases, Rosenthal's theorem, and Tsirelson's
space, while Ostrovskii covers metric embeddings such as Bourgain's theorem. The renorming and Radon–Nikodým
material also occurs throughout the specialized references listed in both
bibliographies. Individual exotic-space constructions are represented by their
structural consequences rather than their complete machinery.

Local source copies consulted:

* [Albiac–Kalton, Topics in Banach Space Theory](References/AlbiacKalton2016TopicsBanachSpaceTheory2ndEd-SpringerGTM.pdf).
* [Diestel, Sequences and Series in Banach Spaces](References/Diestel1984SequencesSeriesBanachSpaces-SpringerGTM92.pdf).
* [Diestel–Jarchow–Tonge, Absolutely Summing Operators](References/DiestelJarchowTonge1995AbsolutelySummingOperators-CambridgeStudiesAM43.pdf).
* [Ryan, Introduction to Tensor Products of Banach Spaces](References/Ryan2002IntroductionTensorProductsBanachSpaces-SpringerMonogMath.pdf).
