# Synopsis: Operator algebras, operator spaces, free probability, and noncommutative geometry

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-23);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects the recurring foundational and beginning research core of
Section 23 of [CKMA-bib.md](CKMA-bib.md#ckma-23).
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
* **82. Kadison transitivity theorem.** Let $\pi$ be an irreducible
  representation of $A$ on $H$, $\xi_1,\ldots,\xi_n\in H$ linearly
  independent, and $T\in\mathcal B(H)$. There is $a\in A$ with
  $\pi(a)\xi_i=T\xi_i$ for all $i$ and $\|a\|\leq\|T\|$; if $T$ is
  self-adjoint, $a$ can be taken self-adjoint, and if $A$ is unital and $T$
  unitary, $a$ can be taken unitary. Hence topologically irreducible
  representations are algebraically irreducible, and their kernels are
  exactly the primitive ideals of $A$.

A C*-algebra is **CCR** (liminal) if $\pi(A)=\mathcal K(H_\pi)$ for every
irreducible representation $\pi$, **GCR** (postliminal) if
$\pi(A)\supset\mathcal K(H_\pi)$ for every such $\pi$, and **type I** if
$\pi(A)''$ is a type I factor (item 27) for every factor representation $\pi$.
$\widehat A$ denotes the unitary equivalence classes of irreducible
representations and $\mathop{\mathrm{Prim}}A$ their kernels, with the
hull–kernel topology.

* **83. Glimm's type I theorem.** For a separable C*-algebra the following
  are equivalent: $A$ is GCR; $A$ is type I; $A$ has a composition series
  with CCR subquotients; irreducible representations with the same kernel
  are unitarily equivalent, so $\widehat A\to\mathop{\mathrm{Prim}}A$ is a
  bijection; $\widehat A$ is a $T_0$ space; the Borel structure of
  $\widehat A$ is countably separated. If $A$ is not type I, it has factor
  representations of types II and III and uncountably many inequivalent
  irreducible representations with a common kernel (Glimm). Commutative
  algebras, $\mathcal K(H)$, and the Toeplitz algebra are type I; the
  CAR algebra and $C^*_r(\mathbb F_2)$ are not.

## Completely positive maps and dilations

A map $\Phi:A\to B$ is **completely positive** (CP) if
$\Phi_n:M_n(A)\to M_n(B)$, acting entrywise, is positive for every $n$.
An **operator system** is a unital self-adjoint subspace of a C*-algebra.
The Choi criterion and the Kraus representation for maps between matrix
algebras are in SYNOPSIS13, items 54 and 53.

* **13. Norm of a CP map.** For CP $\Phi$ on a unital C*-algebra,
  $\|\Phi\|=\|\Phi(1)\|$, and the same norm bounds every amplification.
  In particular unital CP maps are completely contractive.
* **14. Kadison–Schwarz inequality.** A unital two-positive map satisfies
  $\Phi(a)^*\Phi(a)\leq\Phi(a^*a)$. Positivity alone gives the
  corresponding inequality for self-adjoint $a$. Complete positivity
  suffices.
* **17. Stinespring theorem.** A CP map $\Phi:A\to\mathcal B(H)$ on
  a unital C*-algebra is $\Phi(a)=V^*\pi(a)V$ for a representation
  $\pi$ on $K$. The realization is unique up to unitary equivalence when
  $K=\overline{\pi(A)VH}$; $V$ is isometric if $\Phi$ is unital.
  Between matrix algebras a unital completely positive map has the form
  $\Phi(A)=V^*(A\otimes I)V$ with $V$ an isometry into a larger
  tensor-product space.
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
$v^*v=p$, $vv^*=q$ for a partial isometry $v$ in the algebra, and
$p\precsim q$ means $p\sim q'\leq q$ for some projection $q'$. A projection
$p$ is **abelian** if $pMp$ is commutative; its **central support** is the
smallest central projection $z$ with $zp=p$. $M$ is **semifinite** if every
nonzero central projection majorizes a nonzero finite projection. A positive
functional, weight or trace $\varphi$ is **faithful** if $\varphi(x^*x)=0$
implies $x=0$. $M\subset\mathcal B(H)$ is **injective** if there is a
norm-one projection of $\mathcal B(H)$ onto $M$, and **hyperfinite** if it is
the ultraweak closure of an increasing union of finite-dimensional
star subalgebras.
A **factor** has center $\mathbb C1$.

* **21. Bicommutant theorem.** A unital star algebra has the same strong
  and weak operator closures, both equal to its bicommutant. Thus
  $M=M''$ characterizes von Neumann algebras.
* **22. Kaplansky density theorem.** If a C*-algebra acts nondegenerately,
  its unit ball is strongly dense in the unit ball of its bicommutant.
  The same holds for self-adjoint and positive unit balls.
* **23. Predual theorem.** Every von Neumann algebra has a unique Banach
  predual, consisting of its normal functionals. For $\mathcal B(H)$
  this is trace class, paired by $\mathop{\mathrm{tr}}(Ta)$. Conversely a
  C*-algebra that is isometrically a dual Banach space is a von Neumann
  algebra (Sakai).
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
* **30. Group von Neumann algebras and hyperfiniteness.** For a discrete
  group $G$, $L(G)=\lambda(G)''$ is a factor exactly when every nontrivial
  conjugacy class of $G$ is infinite (ICC), and for $G\neq\{e\}$ it is
  then of type II$_1$ with
  trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$. There is a unique
  hyperfinite II$_1$ factor $R$ (Murray–von Neumann), and $L(\mathbb F_2)$ is
  not isomorphic to $R$ (property $\Gamma$, the existence of nontrivial
  central sequences, holds for $R$ but not for $L(\mathbb F_2)$). For von Neumann algebras with
  separable predual, injectivity is equivalent to hyperfiniteness (Connes);
  in particular $L(G)\cong R$ for every amenable ICC group $G$.
* **31. Finite conditional expectation.** If $N\subset M$ are finite
  von Neumann algebras with a faithful normal tracial state $\tau$ on $M$,
  there is a unique $\tau$-preserving normal conditional expectation
  $E_N:M\to N$. On $L^2(M,\tau)$ it is the orthogonal projection onto
  $L^2(N,\tau)$.
* **32. Noncommutative Hölder inequality.** For a semifinite faithful
  normal trace, the spaces $L^p(M,\tau)$ of measurable affiliated
  operators satisfy $\|xy\|_r\leq\|x\|_p\|y\|_q$ when
  $1/r=1/p+1/q$ and $p,q,r\geq1$. Trace duality gives
  $L^p(M)^*=L^{p'}(M)$ for $1<p<\infty$.
* **33. Central decomposition.** A von Neumann algebra with separable
  predual decomposes as a direct integral of factors over its center,
  uniquely up to the appropriate measure-class equivalence.
* **34. Derivations.** Every derivation of a C*-algebra into itself is
  bounded (Sakai), and every derivation of a von Neumann algebra into itself
  is inner (Kadison–Sakai). A derivation of a C*-algebra $A\subset\mathcal B(H)$
  is the restriction of an inner derivation of $A''$.

## Modular theory, equilibrium, and subfactors

For a cyclic separating unit vector $\Omega$ of $M$, put
$\varphi(a)=\langle a\Omega,\Omega\rangle$ and close the antilinear
operator $S_0(a\Omega)=a^*\Omega$ and write $S=J\Delta^{1/2}$.
Here $J$ is the **modular conjugation** and $\Delta$ the **modular
operator**. A II$_1$ **subfactor** is a unital inclusion of II$_1$ factors.

* **35. Tomita theorem.** $JMJ=M'$ and
  $\Delta^{it}M\Delta^{-it}=M$. Thus
  $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$ is a one-parameter automorphism
  group intrinsic to the faithful normal vector state.
* **36. Modular KMS relation.** For $a,b\in M$, there is a bounded
  function analytic in $0<\mathop{\mathrm{Im}}z<1$, continuous on its
  closure, with boundary values
  $F(t)=\varphi(\sigma_t(a)b)$ and
  $F(t+i)=\varphi(b\sigma_t(a))$. This boundary convention fixes the
  sign of the modular dynamics.
* **37. Trace criterion.** A faithful normal state is tracial exactly
  when its modular automorphism group is trivial. In a finite-dimensional
  algebra with density matrix $\rho>0$, its modular group is
  $\sigma_t(a)=\rho^{it}a\rho^{-it}$.
* **38. Modular conditional expectations.** For a faithful normal state
  $\varphi$, a von Neumann subalgebra $N\subset M$ admits a
  $\varphi$-preserving normal conditional expectation exactly when it is
  invariant under $\sigma_t^\varphi$ for all $t$ (Takesaki).
* **39. Connes cocycle and type III classification.** For faithful normal
  states (or weights) $\varphi,\psi$ there is a unitary cocycle
  $u_t=(D\psi:D\varphi)_t$ in $M$ with
  $\sigma_t^\psi=\mathop{\mathrm{Ad}}u_t\circ\sigma_t^\varphi$ and
  $u_{s+t}=u_s\sigma_s^\varphi(u_t)$. Hence the modular flow is intrinsic
  modulo inner automorphisms, and $M$ is semifinite exactly when
  $\sigma^\varphi$ is inner.
  Connes's invariant $S(M)=\bigcap_\varphi\sigma(\Delta_\varphi)$, over
  faithful normal states for $\sigma$-finite $M$ (faithful normal
  semifinite weights in general), divides
  type III factors into III$_0$ ($S=\{0,1\}$), III$_\lambda$
  ($S=\{0\}\cup\lambda^{\mathbb Z}$, $0<\lambda<1$), and III$_1$
  ($S=[0,\infty)$).
* **40. Finite-dimensional Gibbs states.** For dynamics
  $\alpha_t(a)=e^{itH}ae^{-itH}$, the state with density
  $e^{-\beta H}/\mathop{\mathrm{tr}}(e^{-\beta H})$ satisfies the
  $\beta$-KMS relation with lower boundary
  $\varphi(a\alpha_t(b))$ and upper boundary
  $\varphi(\alpha_t(b)a)$ at height $\beta>0$.
* **41. Jones index theorem.** For an inclusion $N\subset M$ of II$_1$
  factors, $[M:N]=\dim_NL^2(M)$ lies in
  $\{4\cos^2(\pi/n):n=3,4,\ldots\}\cup[4,\infty]$.
  Each listed value is realized by a subfactor.

## Tensor products, nuclearity, and approximation

The **minimal tensor norm** on $A\odot B$ comes from faithful spatial
representations; the **maximal norm** is the supremum over pairs of
commuting representations. $A$ is **nuclear** if these norms agree for
every C*-algebra $B$, and **exact** if minimal tensoring by $A$ preserves
short exact sequences.

* **42. Minimal and maximal tensor products.** Both constructions give
  C*-completions, with $\|x\|_{\min}\leq\|x\|_{\max}$. The spatial
  norm is independent of the faithful representations used to define it.
* **43. Completely positive approximation theorem.** $A$ is nuclear
  exactly when its identity is a point-norm limit of compositions
  $A\to M_{n_i}\to A$ of completely positive contractions.
* **44. Nuclear examples and permanence.** Commutative and finite-dimensional
  C*-algebras are nuclear. Nuclearity passes to closed ideals, quotients,
  inductive limits, and minimal tensor products; every nuclear algebra is exact.
* **45. Exactness and subalgebras.** C*-subalgebras of exact algebras are
  exact. Nuclearity, by contrast, does not pass to arbitrary C*-subalgebras.
* **46. Amenability theorem.** A C*-algebra is nuclear exactly when it
  is amenable as a Banach algebra (Connes, Haagerup).
* **47. Group C*-algebras and amenability.** A discrete group $G$ is
  amenable exactly when its reduced group C*-algebra $C_r^*(G)$ is
  nuclear. For amenable $G$, the canonical map $C^*(G)\to C_r^*(G)$
  is an isomorphism.

## K-theory, extensions, and crossed products

$K_0(A)$ is formed from stable Murray–von Neumann classes of matrix
projections by group completion; $K_1(A)$ uses stable homotopy classes
of matrix unitaries. Nonunital groups are defined through the unitization
and the kernel of the scalar map. The **suspension** is $SA=C_0(\mathbb R)\otimes A$.
An **AF algebra** is an inductive limit of finite-dimensional C*-algebras.

* **48. Homotopy invariance and stability.** Homotopic star homomorphisms
  induce the same K-theory maps, and $K_i(A\otimes\mathcal K)=K_i(A)$.
  Matrix amplification therefore does not change K-theory.
* **49. Basic K-groups.** $K_0(\mathbb C)=\mathbb Z$ and
  $K_1(\mathbb C)=0$, with the same groups for $\mathcal K$ and for
  each full matrix algebra. Also $K_0(C(\mathbb T))=K_1(C(\mathbb T))=\mathbb Z$.
* **50. Bott periodicity.** $K_i(S^2A)\cong K_i(A)$ naturally. Together
  with $K_i(SA)=K_{1-i}(A)$ this makes complex C*-algebra K-theory
  two-periodic.
* **51. Six-term exact sequence.** A short exact sequence
  $0\to I\to A\to B\to0$ yields the cyclic exact sequence
  $$K_0(I)\to K_0(A)\to K_0(B)\xrightarrow{\partial}
       K_1(I)\to K_1(A)\to K_1(B)\xrightarrow{\partial}K_0(I).$$
* **52. Index boundary map.** For the Calkin extension, the connecting
  map takes an invertible class represented by a Fredholm operator to its
  Fredholm index in $K_0(\mathcal K)=\mathbb Z$.
  In the Toeplitz extension this recovers minus winding number. (Convention:
  $\partial[u]=[1-v^*v]-[1-vv^*]$ for a partial-isometry lift $v$ of $u$;
  some texts use the opposite sign.)
* **53. Continuity and AF classification.** K-theory commutes with
  C*-inductive limits. Separable unital AF algebras are classified by their
  ordered $K_0$ groups with distinguished order unit; their $K_1$ groups vanish.
* **84. UHF algebras.** A **UHF algebra** is a unital inductive limit
  $\bigotimes_{k\geq1}M_{n_k}$ of full matrix algebras with unital
  connecting maps; its **supernatural number** $\prod_pp^{e_p}$,
  $e_p\in\{0,1,\ldots,\infty\}$, records the exponents of primes dividing
  $n_1n_2\cdots n_k$ as $k\to\infty$. UHF algebras are simple, nuclear,
  with a unique tracial state, and
  $K_0=\{a/b\in\mathbb Q:b\text{ divides the supernatural number}\}$ with
  $[1]=1$. Two UHF algebras are isomorphic exactly when their supernatural
  numbers agree (Glimm). The CAR algebra is $M_{2^\infty}$.
* **54. Cuntz algebras and classification.** The Cuntz algebra $\mathcal O_n$,
  generated by isometries $s_1,\ldots,s_n$ with $\sum_js_js_j^*=1$
  ($2\leq n<\infty$), is simple, nuclear, and purely infinite (every
  nonzero hereditary C*-subalgebra contains an infinite projection), with
  $K_0(\mathcal O_n)=\mathbb Z/(n-1)$, $[1]\mapsto1$, and $K_1=0$.
  Unital Kirchberg algebras (simple, separable, nuclear, purely infinite)
  satisfying the UCT (the universal coefficient theorem of
  Rosenberg–Schochet for $KK(A,\cdot)$; equivalently $A$ is $KK$-equivalent
  to a commutative C*-algebra) are classified by $(K_0,[1],K_1)$
  (Kirchberg–Phillips);
  $A\otimes\mathcal O_2\cong\mathcal O_2$ for every unital simple separable
  nuclear $A$. In the stably finite case, unital simple separable nuclear
  $\mathcal Z$-stable ($A\otimes\mathcal Z\cong A$ for the Jiang–Su algebra
  $\mathcal Z$) UCT algebras are classified by the Elliott invariant
  ($K$-theory, traces, and their pairing).
* **55. Morita invariance.** Strongly Morita equivalent C*-algebras (linked
  by an imprimitivity bimodule) have isomorphic K-groups. For
  $\sigma$-unital algebras (with a countable approximate unit), strong
  Morita equivalence
  is equivalent to isomorphism after stabilization by $\mathcal K$.
* **56. Crossed-product universal property.** For a discrete action
  $\alpha:G\to\mathop{\mathrm{Aut}}(A)$, representations of the full crossed
  product $A\rtimes_\alpha G$ correspond to covariant pairs
  $(\pi,U)$ satisfying $U_g\pi(a)U_g^*=\pi(\alpha_g(a))$.
* **57. Pimsner–Voiculescu exact sequence.** For an automorphism $\alpha$
  of $A$, K-theory of $A\rtimes_\alpha\mathbb Z$ fits into the cyclic
  exact sequence with maps
  $K_i(A)\xrightarrow{1-\alpha_*}K_i(A)\to
  K_i(A\rtimes_\alpha\mathbb Z)\to K_{1-i}(A)$.
* **85. Irrational rotation algebras.** For $\theta\in\mathbb R$, the
  rotation algebra $A_\theta$ is the universal C*-algebra generated by
  unitaries $u,v$ with $vu=e^{2\pi i\theta}uv$; it is
  $C(\mathbb T)\rtimes\mathbb Z$ for rotation by $2\pi\theta$. For
  irrational $\theta$ it is simple, nuclear, with a unique tracial state
  $\tau$. By item 57, $K_0(A_\theta)\cong K_1(A_\theta)\cong\mathbb Z^2$,
  and $\tau_*(K_0(A_\theta))=\mathbb Z+\theta\mathbb Z$
  (Pimsner–Voiculescu); every value in $(\mathbb Z+\theta\mathbb Z)\cap[0,1]$
  is the trace of a projection (Rieffel). Hence, for irrational
  $\theta,\theta'$, $A_\theta\cong A_{\theta'}$ exactly when
  $\theta'\equiv\pm\theta\pmod{\mathbb Z}$, and $A_\theta$ and
  $A_{\theta'}$ are strongly Morita equivalent exactly when $\theta,\theta'$
  lie in the same $GL_2(\mathbb Z)$-orbit (Rieffel).
* **86. Takai duality.** For an action $\alpha$ of a locally compact
  abelian group $G$ on $A$, the dual action of $\widehat G$ on
  $A\rtimes_\alpha G$ is given on $C_c(G,A)$ by
  $(\widehat\alpha_\gamma f)(s)=\overline{\gamma(s)}f(s)$, and
  $(A\rtimes_\alpha G)\rtimes_{\widehat\alpha}\widehat G\cong
  A\otimes\mathcal K(L^2(G))$ (Takai). Thus $A$ is recovered from
  the crossed product up to stable isomorphism.

For separable $A$ and $\sigma$-unital $B$, a **Kasparov $(A,B)$-module**
$(E,\phi,F)$ consists of a countably generated graded Hilbert $B$-module
$E$, a graded representation $\phi$ of $A$ by adjointable operators, and an
odd adjointable $F$ such that $\phi(a)(F^2-1)$, $\phi(a)(F-F^*)$, and
$[F,\phi(a)]$ are compact for all $a$. $KK(A,B)$ is the group of homotopy
classes of such modules.

* **87. Kasparov product.** $KK(A,B)$ is contravariant in $A$, covariant in
  $B$, homotopy invariant, stable under tensoring with $\mathcal K$, and
  split exact in each variable, with $KK(\mathbb C,B)=K_0(B)$ and
  $KK(A,\mathbb C)=K^0(A)$, the K-homology of $A$, built from the
  Fredholm modules of item 74. There is an associative bilinear product
  $KK(A,B)\times KK(B,C)\to KK(A,C)$ extending composition of star
  homomorphisms; for $A=\mathbb C$ it gives the action of $KK(B,C)$ on
  K-theory, and the even index pairing of item 75 is the product
  $K_0(A)\times K^0(A)\to KK(\mathbb C,\mathbb C)=\mathbb Z$.
  An invertible element of $KK(A,B)$ is a **$KK$-equivalence**.
* **88. Universal coefficient theorem.** A separable $A$ **satisfies the
  UCT** if for every $\sigma$-unital $B$ there is a natural exact sequence
  $$0\to\mathop{\mathrm{Ext}}\nolimits^1_{\mathbb Z}(K_*(A),K_{*+1}(B))\to KK_*(A,B)
     \to\mathop{\mathrm{Hom}}(K_*(A),K_*(B))\to0,$$
  split unnaturally. This holds exactly when $A$ is $KK$-equivalent to a
  commutative C*-algebra (Rosenberg–Schochet); the separable nuclear such
  algebras form the **bootstrap class**. Two algebras satisfying the UCT are
  $KK$-equivalent exactly when their K-groups are isomorphic. The bootstrap
  class contains the separable type I algebras and is closed under inductive
  limits, extensions, and crossed products by $\mathbb Z$ and $\mathbb R$;
  whether every separable nuclear C*-algebra satisfies the UCT is open.

## Operator spaces and completely bounded maps

An **operator space** is a closed linear subspace $E\subset\mathcal B(H)$
with its induced matrix norms. A linear map is **completely bounded** if
$\|T\|_{\rm cb}=\sup_n\|T_n\|<\infty$. A **complete isometry** preserves
all matrix norms, not merely the norm on $E$.

* **58. Ruan representation theorem.** Abstract matrix norms come from
  a concrete operator space exactly when
  $\|x\oplus y\|=\max(\|x\|,\|y\|)$ and
  $\|\alpha x\beta\|\leq\|\alpha\|\|x\|\|\beta\|$ for scalar
  matrices of compatible sizes.
* **59. Wittstock extension theorem.** A completely bounded map from
  an operator subspace $E\subset A$ into $\mathcal B(H)$ extends to
  all of $A$ without increasing its completely bounded norm.
* **60. Wittstock decomposition and factorization.** Every completely bounded map from a
  C*-algebra into $\mathcal B(H)$ is a linear combination of four CP maps.
  A self-adjoint such map is a difference of two CP maps. More precisely,
  $\Phi(a)=V^*\pi(a)W$ for a representation $\pi$ and bounded $V,W$ with
  $\|V\|\|W\|=\|\Phi\|_{\rm cb}$ (Haagerup–Paulsen–Wittstock).
* **61. Similarity theorem.** A unital homomorphism from a C*-algebra
  into $\mathcal B(H)$ is completely bounded exactly when it is similar
  to a star representation. Its cb norm is the infimum of the similarity
  condition numbers $\|S\|\|S^{-1}\|$.
* **62. Haagerup tensor product.** The matrix norms defined by
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

* **63. Free product construction.** A family of C*-probability spaces
  with faithful states has a reduced free product with state-preserving
  embeddings whose images are free. The prescribed marginal states and freeness determine all
  joint moments uniquely.
* **64. Free cumulants.** Unique multilinear functionals $\kappa_n$ are
  determined recursively by
  $$\varphi(a_1\cdots a_n)=\sum_{\pi\in NC(n)}\kappa_\pi(a_1,\ldots,a_n),$$
  where $\kappa_\pi$ is the product of cumulants over its blocks.
  Freeness is equivalent to vanishing of mixed cumulants.
* **65. Free central limit theorem.** For identically distributed free
  self-adjoint variables of mean zero and variance one, normalized sums
  converge in moments to the semicircle law
  $(2\pi)^{-1}\sqrt{4-x^2}\,1_{[-2,2]}dx$.
* **66. Semicircular Wick formula.** Moments of a centered semicircular
  family are sums over noncrossing pairings, with products of the specified
  covariances. Odd moments vanish; the variance-one scalar even moments
  are the Catalan numbers.
* **67. Free Poisson limit.** For $\lambda>0$, sums of $N$ free
  projections, each with expectation $\lambda/N$, converge in moments to the free Poisson law
  whose cumulants all equal $\lambda$. Its continuous support is
  $[(1-\sqrt\lambda)^2,(1+\sqrt\lambda)^2]$ and its atom at zero
  has mass $\max(1-\lambda,0)$. It is the limiting eigenvalue distribution
  of $N^{-1}XX^*$ for $N\times M$ matrices $X$ with i.i.d. standardized
  entries and $M/N\to\lambda$ (Marchenko–Pastur).
* **68. R-transform linearization.** For a compactly supported law,
  $R(w)=\sum_{n\geq1}\kappa_nw^{n-1}$ near zero. Free additive
  convolution satisfies $R_{\mu\boxplus\nu}=R_\mu+R_\nu$.
* **69. Cauchy transform inversion.** With
  $G_\mu(z)=\int(z-x)^{-1}d\mu(x)$, one has
  $G_\mu^{-1}(w)=w^{-1}+R_\mu(w)$ near infinity and zero, respectively.
  Boundary values of $G_\mu$ recover $\mu$ by Stieltjes inversion.
* **70. S-transform multiplication.** For variables with nonzero mean,
  define $\psi_a(z)=\sum_{n\geq1}\varphi(a^n)z^n$ and
  $S_a(z)=(1+z)\psi_a^{-1}(z)/z$. If $a,b$ are free,
  $S_{ab}=S_aS_b$ as formal series, or analytically near zero when bounded.
* **71. Asymptotic freeness of Gaussian matrices.** Independent GUE
  matrices with variance normalization $1/N$ converge jointly in normalized
  trace moments, almost surely, to a free variance-one semicircular family.
* **72. Haar conjugation and asymptotic freeness.** Deterministic uniformly
  bounded self-adjoint matrix families with limiting moments become
  asymptotically free after independent Haar-unitary conjugation, in expected
  normalized trace moments. Their marginal limits are retained.
* **73. Free compression.** If a projection $p$ of trace $t>0$ is free
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

* **74. Bounded transform.** A spectral triple gives a Fredholm module
  by $F=D(1+D^2)^{-1/2}$. Compactness of its commutators follows from
  boundedness of $[D,a]$ and compact resolvent.
* **75. Even index pairing.** If $p\in M_n(\mathcal A)$ is a projection,
  compression of $F^+:H^+\to H^-$ gives a Fredholm map
  $pF^+p:p(H^+)^n\to p(H^-)^n$. Its index depends only on the
  $K_0$ class and the Fredholm module class.
* **76. Odd index pairing.** For an odd module represented with
  $F^2=I$, let $P=(I+F)/2$. A matrix unitary $u$ gives the Fredholm
  operator $PuP$ on $PH^n$, and its index defines the pairing with $K_1$.
* **77. Homotopy and compact perturbation invariance.** These index
  pairings are additive, invariant under stable unitary equivalence and
  norm-continuous operator homotopy, and unchanged by compact perturbations
  of $F$.
* **78. Classical Dirac example.** On a closed spin manifold of dimension
  $d$, $(C^\infty(M),L^2(M,S),D)$ is a spectral triple. One has
  $[D,f]=c(df)$ up to the chosen Clifford convention and
  $(1+D^2)^{-p/2}$ trace class for $p>d$.
* **79. Connes distance formula.** On a connected closed spin manifold,
  $$d(x,y)=\sup\{|f(x)-f(y)|:f\in C^\infty(M,\mathbb R),
                                      \ \|[D,f]\|\leq1\}.$$
  Thus the commutator norm recovers the geodesic metric.
* **80. Dixmier trace theorem.** A positive classical pseudodifferential
  operator $P$ of order $-d$ on a closed $d$-manifold, $d\geq1$, is
  Dixmier measurable and satisfies $\mathop{\mathrm{Tr}}_\omega P=d^{-1}\mathop{\mathrm{Res}}P$.
  Here $\mathop{\mathrm{Res}}P=(2\pi)^{-d}\int_{S^*M}
  \mathop{\mathrm{tr}}\sigma_{-d}(P)$ is the noncommutative residue.
* **81. Geometric index pairing.** On an even-dimensional closed spin
  manifold, pairing the Dirac class with a smooth vector bundle $E$ gives
  $\mathop{\mathrm{ind}}D_E^+=\int_M\widehat A(TM)\mathop{\mathrm{ch}}(E)$
  (Atiyah–Singer).

## Reference guide

Blackadar gives a unified structural account of C*- and von Neumann
algebras, representations, tensor products, modular theory, and the framework
for K-theory. These topics recur in Murphy, Kadison–Ringrose, Takesaki,
Bratteli–Robinson, and the classification references; Takesaki is the
standard source for the Connes cocycle and the type III classification, and
Strung for Cuntz algebras and the classification of nuclear C*-algebras.
Brown–Ozawa is the standard source for tensor products, nuclearity,
exactness, and group C*-algebras, and Rørdam–Larsen–Laustsen for the
K-theory items; Blackadar's *K-Theory for Operator Algebras* develops
$KK$-theory and the UCT. Murphy, Davidson, and Dixmier treat transitivity,
type I algebras and Glimm's theorem, UHF algebras, and (Davidson) the
rotation algebras; Williams treats crossed products and Takai duality.
Pisier and Effros–Ruan are the standard sources for operator spaces.
Paulsen independently develops matrix positivity, dilation, and completely
bounded methods.
Nica–Speicher and Mingo–Speicher provide the common combinatorial and
random-matrix core of free probability. Gracia-Bondía–Várilly–Figueroa
develops spectral triples, Fredholm modules, trace ideals, and geometric index
pairings, alongside Connes and the later introductions in the bibliography.
Detailed classification theorems, quantum groups, and groupoid constructions
require additional separate treatments.

Local source copies consulted:

* [Blackadar, Operator Algebras](References/Blackadar2006OperatorAlgebras-SpringerEMS122.pdf).
* [Rørdam–Larsen–Laustsen, An Introduction to K-Theory for C*-Algebras](References/RordamLarsenLaustsen2000IntroductionKTheoryCStarAlgebras-Cambridge.LMSST49.pdf).
* [Strung, An Introduction to C*-algebras and the Classification Program](References/Strung2021CStarAlgebrasClassificationProgram-Birkhauser.ACMCRM.pdf).
* [Paulsen, Completely Bounded Maps and Operator Algebras](References/Paulsen2003CompletelyBoundedMapsOperatorAlgebras-CambridgeStudiesAM78.pdf).
* [Nica–Speicher, Lectures on the Combinatorics of Free Probability](References/NicaSpeicher2006LecturesCombinatoricsFreeProbability-CambridgeUP.LMSLNS335.pdf).
* [Mingo–Speicher, Free Probability and Random Matrices](References/MingoSpeicher2017FreeProbabilityRandomMatrices-BookSpringerFieldsInst.pdf).
* [Gracia-Bondía–Várilly–Figueroa, Elements of Noncommutative Geometry](References/GraciaBondíaVárillyFigueroa2001ElementsNoncommutativeGeometry-BirkhäuserAdvTexts.pdf).
