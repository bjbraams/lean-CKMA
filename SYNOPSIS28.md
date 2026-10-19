# Synopsis: Abstract harmonic analysis on groups

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-28);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects the common foundations and principal continuations of
Section 28 of [CKMA-bib.md](CKMA-bib.md#ckma-28).
Its central objects are locally compact groups, their convolution algebras,
unitary representations, and Fourier transforms. Compact and abelian groups
admit particularly complete theories; induction and the noncommutative
Plancherel theorem explain what replaces scalar Fourier analysis more generally.
The group $C^*$-algebras (18, 20) and the Fourier algebra (57, 61) are
also studied as Banach and operator algebras in Sections 20 and 23.

Groups are Hausdorff and locally compact. Statements using measurable fields
of representations assume second countability. Haar measure is left Haar
measure, and the modular function is normalized by
$$
\int_G f(xy)\,dx=\Delta_G(y)^{-1}\int_G f(x)\,dx.
$$
Representations are strongly continuous and unitary on complex Hilbert spaces
unless specified otherwise. Compact groups have Haar measure of mass one.

## Haar measure, convolution, and homogeneous spaces

* **1. Haar's theorem.** Every locally compact group $G$ admits a
  nonzero left-invariant regular Borel measure finite on compact sets,
  unique up to a positive scalar. Every nonempty open set has positive measure.
  Haar measure is outer regular on Borel sets and inner regular on open
  sets; it need not be inner regular on all Borel sets unless $G$ is
  $\sigma$-compact. Compact groups admit the normalization $\mu(G)=1$.
* **2. The modular homomorphism.** $\Delta_G:G\to(0,\infty)$ is
  a continuous homomorphism. Inversion carries left Haar measure to
  right Haar measure, with
  $\int f(x^{-1})dx=\int f(x)\Delta_G(x^{-1})dx$.
* **3. Unimodularity.** Abelian, compact, and discrete groups are
  unimodular: $\Delta_G=1$. Connected nilpotent and connected semisimple
  Lie groups are also unimodular. General solvable groups need not be.
* **4. Continuity of translations.** Left translations are strongly
  continuous isometries on $L^p(G)$ for $1\leq p<\infty$.
  Right translation $R_yf(x)=f(xy)$ has norm
  $\Delta_G(y)^{-1/p}$.
* **5. The group algebra.** With
  $$
  f*g(x)=\int_G f(y)g(y^{-1}x)dy,\qquad
  f^*(x)=\Delta_G(x^{-1})\overline{f(x^{-1})},
  $$
  $L^1(G)$ is a Banach $*$-algebra:
  $\|f*g\|_1\leq\|f\|_1\|g\|_1$ and
  $(f*g)^*=g^**f^*$.
* **6. Convolution on $L^p$.** If $f\in L^1(G)$ and $g\in L^p(G)$,
  then $\|f*g\|_p\leq\|f\|_1\|g\|_p$, including $p=\infty$.
  On a unimodular group the full Young inequality holds with
  $1+1/r=1/p+1/q$ and $1\leq p,q,r\leq\infty$.
* **7. Approximate identities.** There are nonnegative $e_U\in C_c(G)$
  of integral one supported in arbitrarily small identity neighborhoods.
  They can be chosen to give a bounded two-sided approximate identity
  for $L^1(G)$; $e_U*f\to f$ in $L^p$ for finite $p$.
* **8. Measure algebra.** Finite regular complex measures form a unital
  Banach $*$-algebra $M(G)$ under convolution, with identity $\delta_e$.
  The map $f\mapsto f(x)dx$ embeds $L^1(G)$ as a closed ideal.
* **9. Invariant quotient measure.** If $H$ is a closed subgroup,
  $G/H$ has a nonzero $G$-invariant Radon measure exactly when
  $\Delta_G|_H=\Delta_H$. Such a measure is unique up to scalar.
* **10. Weil's integration formula.** Under that modular condition,
  Haar and quotient measures can be normalized so that
  $\int_G f(x)dx=\int_{G/H}\int_Hf(xh)dh\,d(xH)$ for $f\in C_c(G)$.
  General closed subgroups admit a quasi-invariant quotient measure and
  an integration formula with a positive continuous rho-function.
* **11. Compact averaging.** For compact $H$, averaging
  $f\mapsto\int_H f(xh)dh$ is a bounded projection onto right
  $H$-invariant functions. In a unitary representation,
  $\int_H\pi(h)dh$ is the orthogonal projection onto $H$-fixed vectors.

## Unitary representations and positive definite functions

A representation is **irreducible** if it has no nontrivial closed invariant
subspace, and **cyclic** if the orbit of one vector has dense linear span.
A function $\phi$ is **positive definite** if
$\sum_{i,j}\overline{c_i}c_j\phi(x_i^{-1}x_j)\geq0$ for all finite choices.

* **12. Integrated representations.**
  $\pi(f)=\int_G f(x)\pi(x)dx$ is a nondegenerate contractive
  $*$-representation of $L^1(G)$. Conversely every nondegenerate
  $*$-representation of $L^1(G)$ arises uniquely this way.
* **13. Schur's lemma.** A unitary representation is irreducible exactly
  when its bounded commutant consists of scalar multiples of the identity.
  An intertwiner between irreducible representations is either zero or
  a scalar multiple of a unitary equivalence.
* **14. Orthogonal decomposition.** The orthogonal complement of a
  closed invariant subspace is invariant. Every representation is an
  orthogonal sum of cyclic representations; irreducible decompositions
  require additional hypotheses or direct integrals.
* **15. Coefficients of positive type.** Functions
  $\phi(x)=\langle\pi(x)v,v\rangle$ are continuous positive definite,
  and every positive definite function satisfies
  $\phi(x^{-1})=\overline{\phi(x)}$ and $|\phi(x)|\leq\phi(e)$.
  Products and nonnegative sums preserve positive definiteness.
* **16. Gelfand–Naimark–Segal construction.** Every continuous positive
  definite function is $\langle\pi(x)v,v\rangle$ for a cyclic unitary
  representation, unique up to a unitary carrying the cyclic vector to
  the cyclic vector.
* **17. Irreducibility and extreme points.** A normalized continuous
  positive definite function is extreme in the convex set of normalized
  positive definite functions exactly when its cyclic GNS representation
  is irreducible.
* **18. The group $C^*$-algebra.** Completion of $L^1(G)$ in the norm
  $\|f\|_{C^*(G)}=\sup_\pi\|\pi(f)\|$ gives a $C^*$-algebra whose
  nondegenerate representations correspond to unitary representations
  of $G$. Positive definite functions correspond to positive functionals.
* **19. Gelfand–Raikov theorem.** For every locally compact group, the
  irreducible unitary representations separate points: for $x\neq e$
  there is an irreducible $\pi$ with $\pi(x)\neq I$.
* **20. The regular representation.**
  $\lambda(x)f(y)=f(x^{-1}y)$ is unitary on $L^2(G)$.
  Its integrated representation is left convolution. The closure of
  $\lambda(L^1(G))$ is the reduced algebra $C_r^*(G)$, a quotient
  of $C^*(G)$.

## Locally compact abelian groups

For abelian $G$, the **dual group** $\widehat G$ consists of continuous
characters $\chi:G\to\mathbb T$, with the compact-open topology.
Set $\widehat f(\chi)=\int_Gf(x)\overline{\chi(x)}dx$.
Wiener's Tauberian theorem and Malliavin's failure of spectral synthesis
are stated in SYNOPSIS20, item 41.

* **21. Local compactness of the dual.** $\widehat G$ is a locally
  compact abelian group. The dual of a compact group is discrete and
  the dual of a discrete group is compact; the converse implications hold.
* **22. Basic dual pairs.**
  $\widehat{\mathbb R^d}\simeq\mathbb R^d$ through
  $x\mapsto e^{2\pi ix\cdot\xi}$, $\widehat{\mathbb Z^d}\simeq\mathbb T^d$,
  and $\widehat{\mathbb T^d}\simeq\mathbb Z^d$.
  Finite abelian groups are isomorphic, noncanonically, to their duals.
* **23. Character extension and separation.** Every continuous character
  on a closed subgroup of an LCA group extends to the whole group.
  Characters separate points of $G$.
* **24. Pontryagin duality.** The evaluation map
  $G\to\widehat{\widehat G}$, $x\mapsto(\chi\mapsto\chi(x))$,
  is a topological group isomorphism.
* **25. Annihilators and quotients.** For closed $H\subset G$, let
  $H^\perp=\{\chi:\chi|_H=1\}$. Then
  $\widehat{G/H}\simeq H^\perp$ and
  $\widehat H\simeq\widehat G/H^\perp$; the double annihilator is $H$.
* **26. Riemann–Lebesgue and uniqueness.**
  $\widehat f\in C_0(\widehat G)$ for $f\in L^1(G)$.
  The Fourier transform is injective on $L^1(G)$ and on finite measures.
  Finite measures have bounded continuous Fourier–Stieltjes transforms.
* **27. Fourier algebra identities.**
  $\widehat{f*g}=\widehat f\widehat g$ and
  $\widehat{f^*}=\overline{\widehat f}$.
  The characters of the commutative Banach algebra $L^1(G)$ are exactly
  evaluations $f\mapsto\widehat f(\chi)$.
* **28. Fourier inversion.** Haar measure on $\widehat G$ can be
  normalized uniquely so that, whenever $f\in L^1(G)$ and
  $\widehat f\in L^1(\widehat G)$,
  $f(x)=\int_{\widehat G}\widehat f(\chi)\chi(x)d\chi$ almost everywhere.
* **29. Plancherel theorem.** With this normalization, Fourier
  transformation extends to a unitary $L^2(G)\to L^2(\widehat G)$.
  For $1\leq p\leq2$, it also satisfies
  $\|\widehat f\|_{p'}\leq\|f\|_p$.
* **30. Bochner's theorem.** Continuous positive definite functions on
  $G$ are exactly $\phi(x)=\int_{\widehat G}\chi(x)d\mu(\chi)$
  for finite positive measures $\mu$, uniquely determined, with
  $\mu(\widehat G)=\phi(e)$.
* **31. Spectral theorem for abelian representations.** Every unitary
  representation of an LCA group has a unique projection-valued measure
  $E$ on $\widehat G$ such that
  $\pi(x)=\int\chi(x)dE(\chi)$ (Stone–Naimark–Ambrose–Godement).
  Integrated operators are $\pi(f)=\int\widehat f(\overline\chi)dE(\chi)$.
* **33. Generalized Poisson summation.** Let $\Lambda$ be a discrete
  cocompact subgroup and $v$ the measure of $G/\Lambda$.
  If $f\in C_c(G)$ and
  $\sum_{\chi\in\Lambda^\perp}|\widehat f(\chi)|<\infty$, then
  $$
  \sum_{\lambda\in\Lambda}f(x\lambda)
  =v^{-1}\sum_{\chi\in\Lambda^\perp}\widehat f(\chi)\chi(x).
  $$
  This follows by Fourier inversion of the continuous periodization.
* **34. Almost periodic functions.** The uniform closure of finite
  linear combinations of characters is $C(bG)$ pulled back along
  the canonical dense homomorphism $G\to bG$, the Bohr compactification.
  It carries the invariant mean obtained from Haar probability on $bG$.
* **64. Structure of LCA groups.** Every LCA group has an open subgroup
  isomorphic to $\mathbb R^n\times K$ with $K$ compact. A compactly generated
  LCA group is isomorphic to $\mathbb R^n\times\mathbb Z^m\times K$ with $K$
  compact, and a connected one to $\mathbb R^n\times K$ with $K$ compact
  and connected. Dually, if $\widehat G$ is compactly generated then
  $G\simeq\mathbb R^n\times\mathbb T^m\times D$ with $D$ discrete. This
  reduces many questions to $\mathbb R^n$, discrete, and compact groups
  (Hewitt–Ross).

## Compact and finite groups

Write $\widehat G$ for equivalence classes of irreducible unitary
representations, and $d_\pi=\dim H_\pi$. In this part define
$\widehat f(\pi)=\int_G f(x)\pi(x)^*dx$.

* **35. Finite dimensionality.** Every irreducible unitary
  representation of a compact group is finite dimensional.
  Every unitary representation is a Hilbert direct sum of irreducibles.
* **36. Schur orthogonality.** Matrix entries from inequivalent
  irreducibles are orthogonal, and in orthonormal coordinates
  $\int_G\pi_{ij}(x)\overline{\sigma_{kl}(x)}dx
  =\delta_{\pi\sigma}\delta_{ik}\delta_{jl}/d_\pi$.
* **37. Peter–Weyl density.** Finite linear combinations of matrix
  coefficients are uniformly dense in $C(G)$. The functions
  $\sqrt{d_\pi}\pi_{ij}$ form an orthonormal basis of $L^2(G)$.
* **38. Regular multiplicities.** In the left or right regular
  representation, each irreducible $\pi$ occurs with multiplicity
  $d_\pi$. Equivalently
  $L^2(G)\simeq\bigoplus_{\pi\in\widehat G}H_\pi\otimes H_\pi^*$
  with its left–right action.
* **39. Compact-group Plancherel formula.**
  $\|f\|_2^2=\sum_\pi d_\pi\|\widehat f(\pi)\|_{\mathrm{HS}}^2$.
  Fourier inversion is
  $f(x)=\sum_\pi d_\pi\operatorname{Tr}(\widehat f(\pi)\pi(x))$
  in $L^2$, with finite-set partial sums.
* **40. Noncommutative convolution formula.** With the adjoint
  convention above,
  $\widehat{f*g}(\pi)=\widehat g(\pi)\widehat f(\pi)$ and
  $\widehat{f^*}(\pi)=\widehat f(\pi)^*$.
  This order reversal disappears if one uses integrated representations
  $\pi(f)$ instead of $\widehat f(\pi)$.
* **41. Characters and class functions.** The irreducible characters
  $\chi_\pi=\operatorname{Tr}\pi$ form an orthonormal basis for
  the conjugation-invariant subspace of $L^2(G)$. For central $f$,
  $\widehat f(\pi)$ is scalar, so central convolution diagonalizes
  on irreducible components.
* **42. Character multiplicities.** In finite-dimensional compact-group
  representations, $\dim\operatorname{Hom}_G(\pi,V)
  =\int_G\chi_V\overline{\chi_\pi}$. Tensor-product multiplicities
  are obtained by taking inner products of products of characters.
* **43. Finite-group Fourier inversion.** For finite $G$ with normalized
  counting measure, the compact formulas are finite sums, valid pointwise
  for every function, and $\sum_\pi d_\pi^2=|G|$.
  The number of irreducibles is the number of conjugacy classes.
* **44. Compact-group separation.** Finite-dimensional unitary
  representations separate points. A compact group embeds into a product
  of unitary groups, and every compact Lie group has a faithful
  finite-dimensional unitary representation.
* **45. Spherical harmonic decomposition.** On $S^{d-1}$, $d\geq2$,
  restrictions of homogeneous harmonic polynomials of degree $\ell$
  give mutually orthogonal eigenspaces of $-\Delta_S$ with eigenvalues
  $\ell(\ell+d-2)$; their sum is dense in $L^2(S^{d-1})$.
  This realizes compact homogeneous-space harmonic analysis.
* **46. Weyl's formulas.** Let $G$ be compact connected Lie with maximal
  torus $T$, Weyl group $W$, positive roots $\alpha$, and half-sum $\rho$.
  Irreducible representations correspond to dominant integral highest
  weights $\lambda$; their characters on $T$ are
  $\chi_\lambda=\sum_{w\in W}\varepsilon(w)e^{w(\lambda+\rho)}/
  \sum_{w\in W}\varepsilon(w)e^{w\rho}$ (numerator and denominator are
  functions on a finite cover of $T$, on $T$ itself when $\rho$ is integral,
  for example for simply connected $G$; the quotient is a function on $T$), with
  $d_\lambda=\prod_{\alpha>0}\langle\lambda+\rho,\alpha\rangle/
  \langle\rho,\alpha\rangle$. For continuous class functions,
  $\int_Gf=|W|^{-1}\int_Tf(t)|\delta(t)|^2dt$, where
  $\delta=\sum_w\varepsilon(w)e^{w\rho}$ is the Weyl denominator.

## Induction and noncompact representation theory

For closed $H\subset G$, **unitary induction** constructs
$\operatorname{Ind}_H^G\sigma$ from measurable sections of the bundle
$G\times_H H_\sigma\to G/H$, with the quotient measure and its
Radon–Nikodym correction. For invariant quotient measure, sections can
be written $F(xh)=\sigma(h)^{-1}F(x)$ with square-integrable quotient norm.

* **47. Induction in stages.** For closed subgroups $H\subset K\subset G$,
  $\operatorname{Ind}_H^G\sigma\simeq
  \operatorname{Ind}_K^G(\operatorname{Ind}_H^K\sigma)$.
  Induction preserves unitary equivalence and orthogonal sums.
* **48. Frobenius reciprocity for compact groups.** If $G$ is compact
  and $H$ closed, the multiplicity of an irreducible $\pi$ in
  $\operatorname{Ind}_H^G\sigma$ equals the multiplicity pairing
  $\dim\operatorname{Hom}_H(\pi|_H,\sigma)$.
  In particular, its multiplicity in $L^2(G/H)$ is $\dim H_\pi^H$.
* **49. Mackey's imprimitivity theorem.** A unitary representation
  equipped with a projection-valued measure on $G/H$ satisfying
  $U(x)E(B)U(x)^*=E(xB)$ is unitarily equivalent to the canonical
  system attached to a representation induced from $H$.
* **50. Direct-integral decomposition.** A group is type I if every
  factor representation generates a von Neumann factor isomorphic to
  $B(K)$ for a Hilbert space $K$. For second-countable type-I
  groups, every separable unitary representation decomposes into a
  direct integral of irreducibles. The measure class and multiplicity
  function are unique up to the natural equivalence. Compact, abelian,
  connected nilpotent, and real reductive groups are type I; nonabelian
  free groups are not, and for these direct-integral decompositions are
  not unique (Glimm, Thoma).
* **51. Noncommutative Plancherel theorem.** If $G$ is second-countable,
  unimodular, and type I, there is a Plancherel measure $\mu$ on
  $\widehat G$ such that
  $$
  \|f\|_2^2=\int_{\widehat G}\|\pi(f)\|_{\mathrm{HS}}^2d\mu(\pi),
  \qquad f\in L^1\cap L^2.
  $$
  The transform extends unitarily onto the corresponding direct integral
  of Hilbert–Schmidt spaces. Nonunimodular groups require formal-dimension
  operators rather than this unmodified formula.
* **52. Mackey's little-group method.** Let $G=N\rtimes H$ with $N$
  abelian and the $H$-orbits in $\widehat N$ regularly embedded (the
  orbit space countably separated). For $\nu\in\widehat N$ let $H_\nu$
  be its stabilizer and $\rho$ an irreducible representation of $H_\nu$.
  Then $\operatorname{Ind}_{N\rtimes H_\nu}^G(\nu\rho)$, with
  $(\nu\rho)(nh)=\nu(n)\rho(h)$, is irreducible, every irreducible
  representation of $G$ arises so, and the parameters are the orbits and
  the classes of $\rho$. Examples: the $ax+b$ group and Euclidean motion
  groups.
* **53. Stone–von Neumann theorem.** For the real Heisenberg group,
  every irreducible unitary representation with a fixed nontrivial central
  character is equivalent to the Schrödinger representation with that
  character. The remaining irreducibles are characters of the abelian quotient.
* **65. Heisenberg Plancherel and Weyl transform.** Let
  $H^n=\mathbb C^n\times\mathbb R$ with
  $(z,t)(w,s)=(z+w,t+s+\frac12\operatorname{Im}(z\cdot\overline w))$, and
  let $\pi_\lambda$, $\lambda\neq0$, be the Schrödinger representation on
  $L^2(\mathbb R^n)$ with central character $e^{i\lambda t}$. For
  $f\in L^1\cap L^2(H^n)$ the operators
  $\widehat f(\lambda)=\int f(z,t)\pi_\lambda(z,t)\,dz\,dt$ are
  Hilbert–Schmidt and
  $$\|f\|_2^2=(2\pi)^{-n-1}\int_{\mathbb R\setminus\{0\}}
    \|\widehat f(\lambda)\|_{\mathrm{HS}}^2|\lambda|^n\,d\lambda;$$
  the map extends to a unitary onto the corresponding $L^2$ space of
  Hilbert–Schmidt-valued functions, and the one-dimensional characters
  carry no Plancherel measure. At $\lambda=1$ the Weyl transform
  $W(g)=\int_{\mathbb C^n}g(z)\pi_1(z,0)\,dz$ satisfies
  $\|W(g)\|_{\mathrm{HS}}^2=(2\pi)^n\|g\|_{L^2(\mathbb C^n)}^2$
  (normalization of Thangavelu).
* **54. Kirillov's orbit correspondence.** For a connected simply
  connected nilpotent Lie group, coadjoint orbits in $\mathfrak g^*$
  parametrize the irreducible unitary representations. A representative
  is induced from the character associated to a polarization of the
  orbit functional $\ell$. A polarization is a subordinate subalgebra
  $\mathfrak h$ with $\ell([\mathfrak h,\mathfrak h])=0$ and dimension
  $(\dim\mathfrak g+\dim\mathfrak g_\ell)/2$.
* **55. Smooth vectors.** In a unitary representation of a Lie group,
  vectors $v$ for which $x\mapsto\pi(x)v$ is smooth are dense.
  On this common invariant domain, differentiation gives a Lie algebra
  representation satisfying
  $[d\pi(X),d\pi(Y)]=d\pi([X,Y])$.
* **56. Compact Lie-group spectral decomposition.** A bi-invariant
  Riemannian metric gives a Laplacian acting by a scalar on every
  irreducible coefficient space. Its heat semigroup is convolution
  with a smooth central kernel, with spectral expansion obtained by
  multiplying each character term by its heat eigenvalue factor.

## Convolution algebras, amenability, and spherical analysis

The **Fourier–Stieltjes algebra** $B(G)$ consists of coefficients of unitary
representations, with its norm as $C^*(G)^*$. The **Fourier algebra**
$A(G)$ consists of coefficients of the left regular representation, with
its canonical coefficient norm. For LCA groups these identify respectively
with $M(\widehat G)$ and $L^1(\widehat G)$ under inverse Fourier transform.

* **57. Coefficient algebra properties.** $B(G)$ is a Banach algebra
  under pointwise multiplication, using tensor products of representations.
  $A(G)$ is a closed ideal in $B(G)$ and lies in $C_0(G)$. Every
  $u\in A(G)$ has the form $u=f*\check g$ with $f,g\in L^2(G)$ and
  $\|u\|_A=\min\|f\|_2\|g\|_2$; the Gelfand spectrum of $A(G)$ is $G$,
  and $A(G)^*$ is the group von Neumann algebra $VN(G)$ (Eymard).
* **58. Amenability and invariant means.** A locally compact group is
  amenable exactly when there is a positive normalized left-invariant
  mean on $L^\infty(G)$. Compact and abelian groups are amenable;
  amenability is preserved under extensions, quotients, and passage to
  closed subgroups. Groups containing a closed nonabelian free discrete
  subgroup, such as $SL_2(\mathbb R)$, are not amenable.
* **59. Følner's criterion for discrete groups.** A discrete group is
  amenable exactly when, for every finite $K\subset G$ and
  $\varepsilon>0$, there is a finite nonempty $F$ with
  $|kF\mathbin\triangle F|<\varepsilon|F|$ for all $k\in K$.
* **60. Amenability and regular representations.** For locally compact
  $G$, amenability is equivalent to the trivial representation being
  weakly contained in $\lambda$, and to the canonical map
  $C^*(G)\to C_r^*(G)$ being an isomorphism.
  Here $\pi$ is weakly contained in $\rho$ if
  $\|\pi(f)\|\leq\|\rho(f)\|$ for every $f\in L^1(G)$.
* **61. Leptin's theorem.** $G$ is amenable exactly when $A(G)$
  has a bounded approximate identity for pointwise multiplication.
* **66. Kazhdan's property (T).** $G$ has **property (T)** if there are a
  compact $Q\subset G$ and $\varepsilon>0$ such that every unitary
  representation with a unit vector $v$ satisfying
  $\sup_{x\in Q}\|\pi(x)v-v\|<\varepsilon$ has a nonzero invariant vector;
  equivalently, every representation weakly containing the trivial one
  contains it. Such $G$ is compactly generated and its abelianization
  $G/\overline{[G,G]}$ is compact; a group with (T) is amenable exactly when
  it is compact. Property (T) passes to quotients and to lattices and back.
  $SL_n(\mathbb R)$ and $SL_n(\mathbb Z)$, $n\geq3$, have (T) (Kazhdan),
  while $\mathbb Z$, $SL_2(\mathbb R)$, and nonabelian free groups do not.
  For $\sigma$-compact $G$, (T) is equivalent to every continuous affine
  isometric action on a real Hilbert space having a fixed point
  (Delorme–Guichardet).
* **62. Gelfand pairs.** For compact $K\subset G$, commutativity of
  the algebra of integrable $K$-bi-invariant functions is the defining
  Gelfand-pair property. If $G$ is compact, it is equivalent to
  $\dim H_\pi^K\leq1$ for every irreducible $\pi$. Gelfand's criterion:
  if a continuous involutive automorphism $\theta$ of $G$ satisfies $\theta(x)\in Kx^{-1}K$ for all $x$, then $(G,K)$ is a Gelfand
  pair; this covers Riemannian symmetric pairs such as $(SO(d),SO(d-1))$ and
  $(SL_2(\mathbb R),SO(2))$.
* **63. Spherical functions.** In a Gelfand pair, normalized bounded
  spherical functions satisfy
  $\int_K\phi(xky)dk=\phi(x)\phi(y)$.
  Integration against their inverse-variable values gives the characters
  of the commutative $K$-bi-invariant convolution algebra. For compact
  $G$, they are coefficients of irreducible representations on their
  one-dimensional $K$-fixed spaces. Godement's Plancherel theorem gives a
  unique positive measure $\mu$ on the positive definite spherical
  functions with $\int_G|f|^2=\int|\widehat f(\phi)|^2d\mu(\phi)$ for
  $K$-bi-invariant $f\in L^1\cap L^2$.

For the next entries $G$ is a connected noncompact semisimple Lie group with
finite center, $K$ a maximal compact subgroup, and $G=KAN$ an Iwasawa
decomposition with $\mathfrak a$ the Lie algebra of $A$, $W$ the restricted
Weyl group, and $\rho$ the half-sum of positive restricted roots counted with
multiplicity. Write $g=k\exp H(g)n$. Then $(G,K)$ is a Gelfand pair and $G/K$
is a Riemannian symmetric space of noncompact type.

* **67. Harish-Chandra's spherical functions.** The spherical functions of
  $(G,K)$ are exactly
  $\phi_\lambda(g)=\int_Ke^{(i\lambda-\rho)(H(gk))}dk$,
  $\lambda\in\mathfrak a^*_{\mathbb C}$, with $\phi_\lambda=\phi_\mu$ exactly
  when $\mu\in W\lambda$. The **spherical transform** of $K$-bi-invariant
  $f$ is $\widetilde f(\lambda)=\int_Gf(g)\phi_{-\lambda}(g)\,dg$. For
  $\lambda\in\mathfrak a^*$ regular, $\phi_\lambda(\exp tH)$ behaves as
  $\sum_{w\in W}c(w\lambda)e^{(iw\lambda-\rho)(tH)}$ when $t\to\infty$, $H$
  in the positive chamber; the **Harish-Chandra $c$-function** $c(\lambda)$
  is a product of Gamma-function quotients over the positive indivisible
  roots (Gindikin–Karpelevich).
* **68. Plancherel and Paley–Wiener theorems on $G/K$.** With suitable
  normalizations, for $K$-bi-invariant $f\in L^1\cap L^2(G)$,
  $$\int_G|f(g)|^2dg=\frac1{|W|}\int_{\mathfrak a^*}
    |\widetilde f(\lambda)|^2|c(\lambda)|^{-2}\,d\lambda,$$
  so the Plancherel measure of Godement's theorem (63) is carried by the
  real parameters (Harish-Chandra). The spherical transform maps the
  $K$-bi-invariant $C_c^\infty$ functions supported in
  $K\exp(\overline{B_R})K$, $B_R$ the ball of radius $R$ in $\mathfrak a$,
  bijectively onto the $W$-invariant entire functions on
  $\mathfrak a^*_{\mathbb C}$ of exponential type $R$
  (Helgason, Gangolli). Through the Helgason Fourier transform the same
  measure governs $L^2(G/K)$.

## Reference guide

Folland, Hewitt–Ross, Rudin, Loomis, and Reiter–Stegeman overlap on Haar
measure, group algebras, duality, positive definite functions, and compact
groups. Folland and Kaniuth–Taylor connect this foundation to induction,
imprimitivity, and direct integrals. Faraut, Helgason, and the Lie-group
texts explain spherical analysis and the transition from compact Fourier
series to noncompact representation theory. The orbit and Heisenberg
results recur in the nilpotent-group and phase-space references.
The amenability and coefficient-algebra statements belong to the overlap
with Reiter–Stegeman and Kaniuth–Lau. Detailed semisimple Plancherel
formulas, individual reductive duals, and the specialized theories of
rigidity and random walks require further dedicated inventories. Bekka–de la
Harpe–Valette is the reference for property (T); Helgason and
Gangolli–Varadarajan for spherical analysis on symmetric spaces; Thangavelu
and Folland (*Harmonic Analysis in Phase Space*) for the Heisenberg group.

Variants of Leptin's theorem for ideals of the Fourier algebra are studied
in Forrest–Kaniuth–Lau–Spronk, *Ideals with Bounded Approximate Identities
in Fourier Algebras* (J. Funct. Anal., 2003).

Local source copies consulted:

* [Folland, *A Course in Abstract Harmonic Analysis*](References/Folland2015CourseAbstractHarmonicAnalysis-CRCPress.pdf).
* [Hewitt–Ross, *Abstract Harmonic Analysis*, II](References/HewittRoss1970AbstractHarmonicAnalysis2StructureAnalysisCompactGroupsAnalysisLocallyCompactAbelianGroups-SpringerGL152.pdf).
* [Faraut, *Analysis on Lie Groups*](References/Faraut2008AnalysisLieGroups-CambridgeStudiesAM110.pdf).
* [Kaniuth–Taylor, *Induced Representations of Locally Compact Groups*](References/KaniuthTaylor2013InducedRepresentationsLocallyCompactGroups-Cambridge.TractsMath197.pdf).
* [Thangavelu, *Harmonic Analysis on the Heisenberg Group*](References/Thangavelu1998HarmonicAnalysisHeisenbergGroup-BirkhäuserProgMath159.pdf).
* [Deitmar–Echterhoff, *Principles of Harmonic Analysis*](References/DeitmarEchterhoff2014PrinciplesHarmonicAnalysis2ndEd-SpringerUTX.pdf).

The noncommutative transform conventions have been stated separately because
the references use both integrated and adjoint Fourier transforms.
