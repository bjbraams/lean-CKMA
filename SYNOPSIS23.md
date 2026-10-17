# Synopsis: Operator algebras, operator spaces, free probability, and noncommutative geometry

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects the recurring foundational and beginning research core of
Section 23 of [CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md).
The section contains several connected subjects, each with its own monographs.
Accordingly the selection combines the common operator-algebra foundation
with separate cores in matrix norm geometry, free probability, K-theory, and
spectral geometry. It does not identify the content of a single introductory
course with the content of this whole sub-area.

A **C*-algebra** is a complex Banach star algebra satisfying
$\|a^*a\|=\|a\|^2$. A **representation** is a star homomorphism into
$\mathcal B(H)$. A **von Neumann algebra** is a unital star subalgebra of
$\mathcal B(H)$ closed in the weak operator topology. Write $M'$ for the
commutant and $Z(M)=M\cap M'$ for the center. A **state** is a positive
linear functional of norm one; a **trace** also satisfies $\tau(ab)=\tau(ba)$.
Hilbert inner products are linear in the first variable.

## C*-algebras, positivity, and representations

* **1. Spectral permanence.** A C*-subalgebra has the same spectrum for
  each of its elements as the containing C*-algebra, using compatible
  unitizations. In particular a unital C*-subalgebra is inverse closed.
* **2. Continuous functional calculus.** A normal element $a$ generates
  a commutative unital C*-algebra isometrically star isomorphic to
  $C(\sigma(a))$, with the coordinate function corresponding to $a$.
* **3. Positivity criterion and roots.** The conditions $a=b^*b$,
  $a=a^*$ with $\sigma(a)\subset[0,\infty)$, and $a=c^2$ for positive
  $c$ are equivalent. The positive square root is unique.
* **4. Order and norm.** For self-adjoint $a$ in a unital C*-algebra,
  $\|a\|\leq r$ exactly when $-r1\leq a\leq r1$. The positive cone
  is closed, proper, and generates the self-adjoint part.
* **5. Contractivity and uniqueness of norm.** Star homomorphisms between
  C*-algebras are contractive; injective ones are isometric. Hence the
  C*-norm is uniquely determined by the algebraic star structure.
* **6. Ideals and quotients.** Closed two-sided ideals are self-adjoint;
  their quotients are C*-algebras. Every C*-algebra and every such ideal
  has an approximate identity of positive contractions.
* **7. Commutative representation.** Every commutative C*-algebra is
  $C_0(X)$ for its locally compact character space $X$, uniquely up to
  homeomorphism. Unital algebras correspond to compact spaces.
* **8. Positive functional estimates.** A positive functional satisfies
  $|\varphi(b^*a)|^2\leq\varphi(a^*a)\varphi(b^*b)$. On a unital
  algebra it is bounded with $\|\varphi\|=\varphi(1)$.
* **9. GNS construction.** Every state has a cyclic representation
  $(\pi_\varphi,H_\varphi,\Omega_\varphi)$ with
  $\varphi(a)=\langle\pi_\varphi(a)\Omega_\varphi,\Omega_\varphi\rangle$,
  unique up to a unitary preserving the cyclic vector.
* **10. Gelfand–Naimark theorem.** Every C*-algebra has a faithful
  isometric representation as a norm-closed star algebra of operators.
  The direct sum of its state GNS representations is faithful.
* **11. Pure states and irreducibility.** A state is an extreme point of
  the state space exactly when its GNS representation is irreducible.
  Irreducibility is equivalent to the commutant consisting of scalars.
* **12. States detect positive elements.** For $a\geq0$,
  $\|a\|=\sup_\varphi\varphi(a)$ over states. On a unital algebra,
  the state space is weak-star compact and is the weak-star closed convex
  hull of its pure states.

## Completely positive maps and dilations

A map $\Phi:A\to B$ is **completely positive** (CP) if
$\Phi_n:M_n(A)\to M_n(B)$, acting entrywise, is positive for every $n$.
An **operator system** is a unital self-adjoint subspace of a C*-algebra.

* **13. Norm of a CP map.** For CP $\Phi$ on a unital C*-algebra,
  $\|\Phi\|=\|\Phi(1)\|$, and the same norm bounds every amplification.
  In particular unital CP maps are completely contractive.
* **14. Kadison–Schwarz inequality.** A unital two-positive map satisfies
  $\Phi(a)^*\Phi(a)\leq\Phi(a^*a)$. Positivity alone gives the
  corresponding inequality for self-adjoint $a$.
* **15. Choi matrix criterion.** $\Phi:M_n\to M_m$ is CP exactly when
  its block matrix $C_\Phi=(\Phi(e_{ij}))_{i,j=1}^n$ is positive.
* **16. Kraus representation.** Every CP map $M_n\to M_m$ is
  $\Phi(a)=\sum_jV_j^*aV_j$ for finitely many $V_j:\mathbb C^m\to
  \mathbb C^n$. It is unital exactly when $\sum_jV_j^*V_j=I$.
* **17. Stinespring theorem.** A CP map $\Phi:A\to\mathcal B(H)$ on
  a unital C*-algebra is $\Phi(a)=V^*\pi(a)V$ for a representation
  $\pi$ on $K$. The realization is unique up to unitary equivalence when
  $K=\overline{\pi(A)VH}$; $V$ is isometric if $\Phi$ is unital.
* **18. Arveson extension theorem.** Every CP map from an operator
  system $S\subset A$ into $\mathcal B(H)$ extends to a CP map on $A$.
  Unitality is preserved.
* **19. Multiplicative domain.** For unital CP $\Phi$, the elements
  satisfying equality in both Schwarz inequalities for $a$ and $a^*$
  form a C*-subalgebra. For such $a$,
  $\Phi(ab)=\Phi(a)\Phi(b)$ and $\Phi(ba)=\Phi(b)\Phi(a)$.
* **20. Tomiyama projection theorem.** A norm-one projection of a
  C*-algebra onto a C*-subalgebra is a positive conditional expectation:
  $E(b_1ab_2)=b_1E(a)b_2$. It is completely positive.

## Von Neumann algebras and projection structure

A functional on a von Neumann algebra is **normal** if it is ultraweakly
continuous; for positive functionals this is equivalent to preserving
bounded increasing suprema. A projection $p$ is **finite** if it is not
equivalent to a proper subprojection, where $p\sim q$ means
$v^*v=p$, $vv^*=q$ for a partial isometry $v$ in the algebra.
A **factor** has center $\mathbb C1$.

* **21. Bicommutant theorem.** A unital star algebra has the same strong
  and weak operator closures, both equal to its bicommutant. Thus
  $M=M''$ characterizes von Neumann algebras.
* **22. Kaplansky density theorem.** If a C*-algebra acts nondegenerately,
  its unit ball is strongly dense in the unit ball of its bicommutant.
  The same holds for self-adjoint and positive unit balls.
* **23. Predual theorem.** Every von Neumann algebra has a unique Banach
  predual, consisting of its normal functionals. For $\mathcal B(H)$
  this is trace class, paired by $\operatorname{tr}(Ta)$.
* **24. Monotone completeness.** Every bounded increasing net of
  self-adjoint elements of $M$ has a supremum in $M$, and converges
  strongly to it. The projection lattice is complete.
* **25. Polar decomposition inside the algebra.** For $a\in M$, its
  polar partial isometry and all spectral projections of $|a|$ belong
  to $M$. Bounded Borel functional calculus therefore stays inside $M$.
* **26. Comparison of projections.** For projections $p,q\in M$ there
  is a central projection $z$ with $zp\precsim zq$ and
  $(1-z)q\precsim(1-z)p$. In a factor, any two projections are comparable.
* **27. Type decomposition.** A von Neumann algebra splits uniquely by
  central projections into types I, II, and III. Type I has abelian
  projections with central support one; type II is semifinite without
  nonzero abelian projections; type III has no nonzero finite projections.
* **28. Type I factors.** Every type I factor is isomorphic to
  $\mathcal B(K)$. The finite-dimensional factors are precisely the full
  matrix algebras.
* **29. Dimension in a finite factor.** A II$_1$ factor has a unique
  normalized normal trace $\tau$; projections satisfy
  $p\sim q$ exactly when $\tau(p)=\tau(q)$, and all values in $[0,1]$
  occur. This provides continuous dimension in place of integer rank.
* **30. Finite conditional expectation.** If $N\subset M$ are finite
  von Neumann algebras with a faithful normal tracial state $\tau$ on $M$,
  there is a unique $\tau$-preserving normal conditional expectation
  $E_N:M\to N$. On $L^2(M,\tau)$ it is the orthogonal projection onto
  $L^2(N,\tau)$.
* **31. Noncommutative Hölder inequality.** For a semifinite faithful
  normal trace, the spaces $L^p(M,\tau)$ of measurable affiliated
  operators satisfy $\|xy\|_r\leq\|x\|_p\|y\|_q$ when
  $1/r=1/p+1/q$ and $p,q,r\geq1$. Trace duality gives
  $L^p(M)^*=L^{p'}(M)$ for $1<p<\infty$.
* **32. Central decomposition.** A von Neumann algebra with separable
  predual decomposes as a direct integral of factors over its center,
  uniquely up to the appropriate measure-class equivalence.

## Modular theory, equilibrium, and subfactors

For a cyclic separating unit vector $\Omega$ of $M$, put
$\varphi(a)=\langle a\Omega,\Omega\rangle$ and close the antilinear
operator $S_0(a\Omega)=a^*\Omega$ and write $S=J\Delta^{1/2}$.
Here $J$ is the **modular conjugation** and $\Delta$ the **modular
operator**. A II$_1$ **subfactor** is a unital inclusion of II$_1$ factors.

* **33. Tomita theorem.** $JMJ=M'$ and
  $\Delta^{it}M\Delta^{-it}=M$. Thus
  $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$ is a one-parameter automorphism
  group intrinsic to the faithful normal vector state.
* **34. Modular KMS relation.** For $a,b\in M$, there is a bounded
  function analytic in $0<\operatorname{Im}z<1$, continuous on its
  closure, with boundary values
  $F(t)=\varphi(\sigma_t(a)b)$ and
  $F(t+i)=\varphi(b\sigma_t(a))$. This boundary convention fixes the
  sign of the modular dynamics.
* **35. Trace criterion.** A faithful normal state is tracial exactly
  when its modular automorphism group is trivial. In a finite-dimensional
  algebra with density matrix $\rho>0$, its modular group is
  $\sigma_t(a)=\rho^{it}a\rho^{-it}$.
* **36. Modular conditional expectations.** For a faithful normal state
  $\varphi$, a von Neumann subalgebra $N\subset M$ admits a
  $\varphi$-preserving normal conditional expectation exactly when it is
  invariant under $\sigma_t^\varphi$ for all $t$ (Takesaki).
* **37. Finite-dimensional Gibbs states.** For dynamics
  $\alpha_t(a)=e^{itH}ae^{-itH}$, the state with density
  $e^{-\beta H}/\operatorname{tr}(e^{-\beta H})$ satisfies the
  $\beta$-KMS relation with lower boundary
  $\varphi(a\alpha_t(b))$ and upper boundary
  $\varphi(\alpha_t(b)a)$ at height $\beta>0$.
* **38. Jones index theorem.** For an inclusion $N\subset M$ of II$_1$
  factors, $[M:N]=\dim_NL^2(M)$ lies in
  $\{4\cos^2(\pi/n):n=3,4,\ldots\}\cup[4,\infty]$.
  Each listed value is realized by a subfactor.

## Tensor products, nuclearity, and approximation

The **minimal tensor norm** on $A\odot B$ comes from faithful spatial
representations; the **maximal norm** is the supremum over pairs of
commuting representations. $A$ is **nuclear** if these norms agree for
every C*-algebra $B$, and **exact** if minimal tensoring by $A$ preserves
short exact sequences.

* **39. Minimal and maximal tensor products.** Both constructions give
  C*-completions, with $\|x\|_{\min}\leq\|x\|_{\max}$. The spatial
  norm is independent of the faithful representations used to define it.
* **40. Completely positive approximation theorem.** $A$ is nuclear
  exactly when its identity is a point-norm limit of compositions
  $A\to M_{n_i}\to A$ of completely positive contractions.
* **41. Nuclear examples and permanence.** Commutative and finite-dimensional
  C*-algebras are nuclear. Nuclearity passes to closed ideals, quotients,
  inductive limits, and minimal tensor products; every nuclear algebra is exact.
* **42. Exactness and subalgebras.** C*-subalgebras of exact algebras are
  exact. Nuclearity, by contrast, does not pass to arbitrary C*-subalgebras.
* **43. Amenability theorem.** A C*-algebra is nuclear exactly when it
  is amenable as a Banach algebra. This connects completely positive
  finite-dimensional approximation with the derivation definition of amenability.
* **44. Group C*-algebras and amenability.** A discrete group $G$ is
  amenable exactly when its reduced group C*-algebra $C_r^*(G)$ is
  nuclear. For amenable $G$, the canonical map $C^*(G)\to C_r^*(G)$
  is an isomorphism.

## K-theory, extensions, and crossed products

$K_0(A)$ is formed from stable Murray–von Neumann classes of matrix
projections by group completion; $K_1(A)$ uses stable homotopy classes
of matrix unitaries. Nonunital groups are defined through the unitization
and the kernel of the scalar map. The **suspension** is $SA=C_0(\mathbb R)\otimes A$.
An **AF algebra** is an inductive limit of finite-dimensional C*-algebras.

* **45. Homotopy invariance and stability.** Homotopic star homomorphisms
  induce the same K-theory maps, and $K_i(A\otimes\mathcal K)=K_i(A)$.
  Matrix amplification therefore does not change K-theory.
* **46. Basic K-groups.** $K_0(\mathbb C)=\mathbb Z$ and
  $K_1(\mathbb C)=0$, with the same groups for $\mathcal K$ and for
  each full matrix algebra. Also $K_0(C(\mathbb T))=K_1(C(\mathbb T))=\mathbb Z$.
* **47. Bott periodicity.** $K_i(S^2A)\cong K_i(A)$ naturally. Together
  with $K_i(SA)=K_{1-i}(A)$ this makes complex C*-algebra K-theory
  two-periodic.
* **48. Six-term exact sequence.** A short exact sequence
  $0\to I\to A\to B\to0$ yields the cyclic exact sequence
  $$K_0(I)\to K_0(A)\to K_0(B)\xrightarrow{\partial}
       K_1(I)\to K_1(A)\to K_1(B)\xrightarrow{\partial}K_0(I).$$
* **49. Index boundary map.** For the Calkin extension, the connecting
  map takes an invertible class represented by a Fredholm operator to its
  Fredholm index in $K_0(\mathcal K)=\mathbb Z$.
  In the Toeplitz extension this recovers minus winding number.
* **50. Continuity and AF classification.** K-theory commutes with
  C*-inductive limits. Separable unital AF algebras are classified by their
  ordered $K_0$ groups with distinguished order unit; their $K_1$ groups vanish.
* **51. Morita invariance.** Strongly Morita equivalent C*-algebras have
  isomorphic K-groups. For sigma-unital algebras, strong Morita equivalence
  is equivalent to isomorphism after stabilization by $\mathcal K$.
* **52. Crossed-product universal property.** For a discrete action
  $\alpha:G\to\operatorname{Aut}(A)$, representations of the full crossed
  product $A\rtimes_\alpha G$ correspond to covariant pairs
  $(\pi,U)$ satisfying $U_g\pi(a)U_g^*=\pi(\alpha_g(a))$.
* **53. Pimsner–Voiculescu exact sequence.** For an automorphism $\alpha$
  of $A$, K-theory of $A\rtimes_\alpha\mathbb Z$ fits into the cyclic
  exact sequence with maps
  $K_i(A)\xrightarrow{1-\alpha_*}K_i(A)\to
  K_i(A\rtimes_\alpha\mathbb Z)\to K_{1-i}(A)$.

## Operator spaces and completely bounded maps

An **operator space** is a closed linear subspace $E\subset\mathcal B(H)$
with its induced matrix norms. A linear map is **completely bounded** if
$\|T\|_{\rm cb}=\sup_n\|T_n\|<\infty$. A **complete isometry** preserves
all matrix norms, not merely the norm on $E$.

* **54. Ruan representation theorem.** Abstract matrix norms come from
  a concrete operator space exactly when
  $\|x\oplus y\|=\max(\|x\|,\|y\|)$ and
  $\|\alpha x\beta\|\leq\|\alpha\|\|x\|\|\beta\|$ for scalar
  matrices of compatible sizes.
* **55. Wittstock extension theorem.** A completely bounded map from
  an operator subspace $E\subset A$ into $\mathcal B(H)$ extends to
  all of $A$ without increasing its completely bounded norm.
* **56. Wittstock decomposition.** Every completely bounded map from a
  C*-algebra into $\mathcal B(H)$ is a linear combination of four CP maps.
  A self-adjoint such map is a difference of two CP maps.
* **57. Similarity theorem.** A unital homomorphism from a C*-algebra
  into $\mathcal B(H)$ is completely bounded exactly when it is similar
  to a star representation. Its cb norm is the infimum of the similarity
  condition numbers $\|S\|\|S^{-1}\|$.
* **58. Haagerup tensor product.** The matrix norms defined by
  $\|u\|_h=\inf_{u=v\odot w}\|v\|\|w\|$, where
  $(v\odot w)_{ij}=\sum_kv_{ik}\otimes w_{kj}$, give an associative
  operator-space tensor product. Concrete operator multiplication extends
  completely contractively from the Haagerup tensor product.

## Free probability and random matrix limits

A **noncommutative probability space** is a unital algebra with a unital
linear functional $\varphi$, positive in the star setting. Unital subalgebras
are **free** if $\varphi(a_1\cdots a_n)=0$ whenever successive factors
come from different subalgebras and each has zero expectation. A
**distribution** records all joint star moments. $NC(n)$ denotes the
noncrossing partitions of $\{1,\ldots,n\}$.

* **59. Free product construction.** A family of C*-probability spaces
  with faithful states has a reduced free product with state-preserving
  embeddings whose images are free. The prescribed marginal states and freeness determine all
  joint moments uniquely.
* **60. Free cumulants.** Unique multilinear functionals $\kappa_n$ are
  determined recursively by
  $$\varphi(a_1\cdots a_n)=\sum_{\pi\in NC(n)}\kappa_\pi(a_1,\ldots,a_n),$$
  where $\kappa_\pi$ is the product of cumulants over its blocks.
  Freeness is equivalent to vanishing of mixed cumulants.
* **61. Free central limit theorem.** For identically distributed free
  self-adjoint variables of mean zero and variance one, normalized sums
  converge in moments to the semicircle law
  $(2\pi)^{-1}\sqrt{4-x^2}\,1_{[-2,2]}dx$.
* **62. Semicircular Wick formula.** Moments of a centered semicircular
  family are sums over noncrossing pairings, with products of the specified
  covariances. Odd moments vanish; the variance-one scalar even moments
  are the Catalan numbers.
* **63. Free Poisson limit.** For $\lambda>0$, sums of $N$ free
  projections, each with expectation $\lambda/N$, converge in moments to the free Poisson law
  whose cumulants all equal $\lambda$. Its continuous support is
  $[(1-\sqrt\lambda)^2,(1+\sqrt\lambda)^2]$ and its atom at zero
  has mass $\max(1-\lambda,0)$.
* **64. R-transform linearization.** For a compactly supported law,
  $R(w)=\sum_{n\geq1}\kappa_nw^{n-1}$ near zero. Free additive
  convolution satisfies $R_{\mu\boxplus\nu}=R_\mu+R_\nu$.
* **65. Cauchy transform inversion.** With
  $G_\mu(z)=\int(z-x)^{-1}d\mu(x)$, one has
  $G_\mu^{-1}(w)=w^{-1}+R_\mu(w)$ near infinity and zero, respectively.
  Boundary values of $G_\mu$ recover $\mu$ by Stieltjes inversion.
* **66. S-transform multiplication.** For variables with nonzero mean,
  define $\psi_a(z)=\sum_{n\geq1}\varphi(a^n)z^n$ and
  $S_a(z)=(1+z)\psi_a^{-1}(z)/z$. If $a,b$ are free,
  $S_{ab}=S_aS_b$ as formal series, or analytically near zero when bounded.
* **67. Asymptotic freeness of Gaussian matrices.** Independent GUE
  matrices with variance normalization $1/N$ converge jointly in normalized
  trace moments, almost surely, to a free variance-one semicircular family.
* **68. Haar conjugation and asymptotic freeness.** Deterministic uniformly
  bounded self-adjoint matrix families with limiting moments become
  asymptotically free after independent Haar-unitary conjugation, in expected
  normalized trace moments. Their marginal limits are retained.
* **69. Free compression.** If a projection $p$ of trace $t>0$ is free
  from $a$, then in $pAp$ with normalized state $\varphi(\cdot)/t$,
  $\kappa_n(pap,\ldots,pap)=t^{n-1}\kappa_n(a,\ldots,a)$.

## Spectral triples and index pairings

A **spectral triple** $(\mathcal A,H,D)$ consists of a represented unital
star algebra preserving $D(D)$, a self-adjoint $D$ with compact resolvent,
and bounded commutators $[D,a]$ for $a\in\mathcal A$. An even triple has a grading
$\gamma$ commuting with $\mathcal A$ and anticommuting with $D$.
A **Fredholm module** uses a bounded self-adjoint $F$ with
$F^2-I$ and all $[F,a]$ compact, together with a grading in the even case.
For a positive compact operator with
$\sup_N\sum_{j\leq N}s_j/\log(1+N)<\infty$, a **Dixmier trace**
is obtained by a suitable generalized limit of these logarithmic means.
The operator is **Dixmier measurable** if the value is independent of that choice.

* **70. Bounded transform.** A spectral triple gives a Fredholm module
  by $F=D(1+D^2)^{-1/2}$. Compactness of its commutators follows from
  boundedness of $[D,a]$ and compact resolvent.
* **71. Even index pairing.** If $p\in M_n(\mathcal A)$ is a projection,
  compression of $F^+:H^+\to H^-$ gives a Fredholm map
  $pF^+p:p(H^+)^n\to p(H^-)^n$. Its index depends only on the
  $K_0$ class and the Fredholm module class.
* **72. Odd index pairing.** For an odd module represented with
  $F^2=I$, let $P=(I+F)/2$. A matrix unitary $u$ gives the Fredholm
  operator $PuP$ on $PH^n$, and its index defines the pairing with $K_1$.
* **73. Homotopy and compact perturbation invariance.** These index
  pairings are additive, invariant under stable unitary equivalence and
  norm-continuous operator homotopy, and unchanged by compact perturbations
  of $F$.
* **74. Classical Dirac example.** On a closed spin manifold of dimension
  $d$, $(C^\infty(M),L^2(M,S),D)$ is a spectral triple. One has
  $[D,f]=c(df)$ up to the chosen Clifford convention and
  $(1+D^2)^{-p/2}$ trace class for $p>d$.
* **75. Connes distance formula.** On a connected closed spin manifold,
  $$d(x,y)=\sup\{|f(x)-f(y)|:f\in C^\infty(M,\mathbb R),
                                      \ \|[D,f]\|\leq1\}.$$
  Thus the commutator norm recovers the geodesic metric.
* **76. Dixmier trace theorem.** A positive classical pseudodifferential
  operator $P$ of order $-d$ on a closed $d$-manifold, $d\geq1$, is
  Dixmier measurable and satisfies $\operatorname{Tr}_\omega P=d^{-1}\operatorname{Res}P$.
  Here $\operatorname{Res}P=(2\pi)^{-d}\int_{S^*M}
  \operatorname{tr}\sigma_{-d}(P)$ is the noncommutative residue.
* **77. Geometric index pairing.** On an even-dimensional closed spin
  manifold, pairing the Dirac class with a smooth vector bundle $E$ gives
  $\operatorname{ind}D_E^+=\int_M\widehat A(TM)\operatorname{ch}(E)$.
  This identifies the operator index with characteristic-class integration.

## Reference guide

Blackadar gives a unified structural account of C*- and von Neumann
algebras, representations, tensor products, modular theory, and the framework
for K-theory. These topics recur in Murphy, Kadison–Ringrose, Takesaki,
Bratteli–Robinson, and the classification references. Paulsen independently
develops matrix positivity, dilation, and completely bounded methods.
Nica–Speicher and Mingo–Speicher provide the common combinatorial and
random-matrix core of free probability. Gracia-Bondía–Várilly–Figueroa
develops spectral triples, Fredholm modules, trace ideals, and geometric index
pairings, alongside Connes and the later introductions in the bibliography.
Detailed classification theorems, quantum groups, and groupoid constructions
require additional separate treatments.

Local source copies consulted:

* [Blackadar, Operator Algebras](References/Blackadar2006OperatorAlgebras-SpringerEMS122.pdf).
* [Strung, An Introduction to C*-algebras and the Classification Program](References/Strung2021CStarAlgebrasClassificationProgram-Birkhauser.ACMCRM.pdf).
* [Paulsen, Completely Bounded Maps and Operator Algebras](References/Paulsen2003CompletelyBoundedMapsOperatorAlgebras-CambridgeStudiesAM78.pdf).
* [Nica–Speicher, Lectures on the Combinatorics of Free Probability](References/NicaSpeicher2006LecturesCombinatoricsFreeProbability-CambridgeUP.LMSLNS335.pdf).
* [Mingo–Speicher, Free Probability and Random Matrices](References/MingoSpeicher2017FreeProbabilityRandomMatrices-BookSpringerFieldsInst.pdf).
* [Gracia-Bondía–Várilly–Figueroa, Elements of Noncommutative Geometry](References/GraciaBondíaVárillyFigueroa2001ElementsNoncommutativeGeometry-BirkhäuserAdvTexts.pdf).
