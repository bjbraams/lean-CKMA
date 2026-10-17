# Synopsis: Abstract harmonic analysis on groups

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects the common foundations and principal continuations of
Section 28 of [CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md).
Its central objects are locally compact groups, their convolution algebras,
unitary representations, and Fourier transforms. Compact and abelian groups
admit particularly complete theories; induction and the noncommutative
Plancherel theorem explain what replaces scalar Fourier analysis more generally.

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
* **19. The regular representation.**
  $\lambda(x)f(y)=f(x^{-1}y)$ is unitary on $L^2(G)$.
  Its integrated representation is left convolution. The closure of
  $\lambda(L^1(G))$ is the reduced algebra $C_r^*(G)$, a quotient
  of $C^*(G)$.

## Locally compact abelian groups

For abelian $G$, the **dual group** $\widehat G$ consists of continuous
characters $\chi:G\to\mathbb T$, with the compact-open topology.
Set $\widehat f(\chi)=\int_Gf(x)\overline{\chi(x)}dx$.

* **20. Local compactness of the dual.** $\widehat G$ is a locally
  compact abelian group. The dual of a compact group is discrete and
  the dual of a discrete group is compact; the converse implications hold.
* **21. Basic dual pairs.**
  $\widehat{\mathbb R^d}\simeq\mathbb R^d$ through
  $x\mapsto e^{2\pi ix\cdot\xi}$, $\widehat{\mathbb Z^d}\simeq\mathbb T^d$,
  and $\widehat{\mathbb T^d}\simeq\mathbb Z^d$.
  Finite abelian groups are isomorphic, noncanonically, to their duals.
* **22. Character extension and separation.** Every continuous character
  on a closed subgroup of an LCA group extends to the whole group.
  Characters separate points of $G$.
* **23. Pontryagin duality.** The evaluation map
  $G\to\widehat{\widehat G}$, $x\mapsto(\chi\mapsto\chi(x))$,
  is a topological group isomorphism.
* **24. Annihilators and quotients.** For closed $H\subset G$, let
  $H^\perp=\{\chi:\chi|_H=1\}$. Then
  $\widehat{G/H}\simeq H^\perp$ and
  $\widehat H\simeq\widehat G/H^\perp$; the double annihilator is $H$.
* **25. Riemann–Lebesgue and uniqueness.**
  $\widehat f\in C_0(\widehat G)$ for $f\in L^1(G)$.
  The Fourier transform is injective on $L^1(G)$ and on finite measures.
* **26. Fourier algebra identities.**
  $\widehat{f*g}=\widehat f\widehat g$ and
  $\widehat{f^*}=\overline{\widehat f}$.
  The characters of the commutative Banach algebra $L^1(G)$ are exactly
  evaluations $f\mapsto\widehat f(\chi)$.
* **27. Fourier inversion.** Haar measure on $\widehat G$ can be
  normalized uniquely so that, whenever $f\in L^1(G)$ and
  $\widehat f\in L^1(\widehat G)$,
  $f(x)=\int_{\widehat G}\widehat f(\chi)\chi(x)d\chi$ almost everywhere.
* **28. Plancherel theorem.** With this normalization, Fourier
  transformation extends to a unitary $L^2(G)\to L^2(\widehat G)$.
  For $1\leq p\leq2$, it also satisfies
  $\|\widehat f\|_{p'}\leq\|f\|_p$.
* **29. Bochner's theorem.** Continuous positive definite functions on
  $G$ are exactly $\phi(x)=\int_{\widehat G}\chi(x)d\mu(\chi)$
  for finite positive measures $\mu$, uniquely determined, with
  $\mu(\widehat G)=\phi(e)$.
* **30. Spectral theorem for abelian representations.** Every unitary
  representation of an LCA group has a unique projection-valued measure
  $E$ on $\widehat G$ such that
  $\pi(x)=\int\chi(x)dE(\chi)$. Integrated operators are obtained
  by the corresponding scalar functional calculus.
* **31. Wiener's Tauberian theorem.** Translates of $f\in L^1(G)$
  span a dense subspace of $L^1(G)$ exactly when $\widehat f$
  has no zeros. More generally a closed ideal is all of $L^1(G)$
  exactly when its common Fourier zero set is empty.
* **32. Generalized Poisson summation.** Let $\Lambda$ be a discrete
  cocompact subgroup and $v$ the measure of $G/\Lambda$.
  If $f\in C_c(G)$ and
  $\sum_{\chi\in\Lambda^\perp}|\widehat f(\chi)|<\infty$, then
  $$
  \sum_{\lambda\in\Lambda}f(x\lambda)
  =v^{-1}\sum_{\chi\in\Lambda^\perp}\widehat f(\chi)\chi(x).
  $$
  This follows by Fourier inversion of the continuous periodization.
* **33. Almost periodic functions.** The uniform closure of finite
  linear combinations of characters is $C(bG)$ pulled back along
  the canonical dense homomorphism $G\to bG$, the Bohr compactification.
  It carries the invariant mean obtained from Haar probability on $bG$.

## Compact and finite groups

Write $\widehat G$ for equivalence classes of irreducible unitary
representations, and $d_\pi=\dim H_\pi$. In this part define
$\widehat f(\pi)=\int_G f(x)\pi(x)^*dx$.

* **34. Finite dimensionality.** Every irreducible unitary
  representation of a compact group is finite dimensional.
  Every unitary representation is a Hilbert direct sum of irreducibles.
* **35. Schur orthogonality.** Matrix entries from inequivalent
  irreducibles are orthogonal, and in orthonormal coordinates
  $\int_G\pi_{ij}(x)\overline{\sigma_{kl}(x)}dx
  =\delta_{\pi\sigma}\delta_{ik}\delta_{jl}/d_\pi$.
* **36. Peter–Weyl density.** Finite linear combinations of matrix
  coefficients are uniformly dense in $C(G)$. The functions
  $\sqrt{d_\pi}\pi_{ij}$ form an orthonormal basis of $L^2(G)$.
* **37. Regular multiplicities.** In the left or right regular
  representation, each irreducible $\pi$ occurs with multiplicity
  $d_\pi$. Equivalently
  $L^2(G)\simeq\bigoplus_{\pi\in\widehat G}H_\pi\otimes H_\pi^*$
  with its left–right action.
* **38. Compact-group Plancherel formula.**
  $\|f\|_2^2=\sum_\pi d_\pi\|\widehat f(\pi)\|_{\mathrm{HS}}^2$.
  Fourier inversion is
  $f(x)=\sum_\pi d_\pi\operatorname{Tr}(\widehat f(\pi)\pi(x))$
  in $L^2$, with finite-set partial sums.
* **39. Noncommutative convolution formula.** With the adjoint
  convention above,
  $\widehat{f*g}(\pi)=\widehat g(\pi)\widehat f(\pi)$ and
  $\widehat{f^*}(\pi)=\widehat f(\pi)^*$.
  This order reversal disappears if one uses integrated representations
  $\pi(f)$ instead of $\widehat f(\pi)$.
* **40. Characters and class functions.** The irreducible characters
  $\chi_\pi=\operatorname{Tr}\pi$ form an orthonormal basis for
  the conjugation-invariant subspace of $L^2(G)$. For central $f$,
  $\widehat f(\pi)$ is scalar, so central convolution diagonalizes
  on irreducible components.
* **41. Character multiplicities.** In finite-dimensional compact-group
  representations, $\dim\operatorname{Hom}_G(\pi,V)
  =\int_G\chi_V\overline{\chi_\pi}$. Tensor-product multiplicities
  are obtained by taking inner products of products of characters.
* **42. Finite-group Fourier inversion.** For finite $G$ with normalized
  counting measure, the compact formulas are finite sums, valid pointwise
  for every function, and $\sum_\pi d_\pi^2=|G|$.
  The number of irreducibles is the number of conjugacy classes.
* **43. Compact-group separation.** Finite-dimensional unitary
  representations separate points. A compact group embeds into a product
  of unitary groups, and every compact Lie group has a faithful
  finite-dimensional unitary representation.
* **44. Spherical harmonic decomposition.** On $S^{d-1}$, $d\geq2$,
  restrictions of homogeneous harmonic polynomials of degree $\ell$
  give mutually orthogonal eigenspaces of $-\Delta_S$ with eigenvalues
  $\ell(\ell+d-2)$; their sum is dense in $L^2(S^{d-1})$.
  This realizes compact homogeneous-space harmonic analysis.

## Induction and noncompact representation theory

For closed $H\subset G$, **unitary induction** constructs
$\operatorname{Ind}_H^G\sigma$ from measurable sections of the bundle
$G\times_H H_\sigma\to G/H$, with the quotient measure and its
Radon–Nikodym correction. For invariant quotient measure, sections can
be written $F(xh)=\sigma(h)^{-1}F(x)$ with square-integrable quotient norm.

* **45. Induction in stages.** For closed subgroups $H\subset K\subset G$,
  $\operatorname{Ind}_H^G\sigma\simeq
  \operatorname{Ind}_K^G(\operatorname{Ind}_H^K\sigma)$.
  Induction preserves unitary equivalence and orthogonal sums.
* **46. Frobenius reciprocity for compact groups.** If $G$ is compact
  and $H$ closed, the multiplicity of an irreducible $\pi$ in
  $\operatorname{Ind}_H^G\sigma$ equals the multiplicity pairing
  $\dim\operatorname{Hom}_H(\pi|_H,\sigma)$.
  In particular, its multiplicity in $L^2(G/H)$ is $\dim H_\pi^H$.
* **47. Mackey's imprimitivity theorem.** A unitary representation
  equipped with a projection-valued measure on $G/H$ satisfying
  $U(x)E(B)U(x)^*=E(xB)$ is unitarily equivalent to the canonical
  system attached to a representation induced from $H$.
* **48. Direct-integral decomposition.** For second-countable type-I
  groups, every separable unitary representation decomposes into a
  direct integral of irreducibles. The measure class and multiplicity
  function are unique up to the natural equivalence.
  Type I means that every factor representation generates a type-I
  von Neumann algebra, an algebra isomorphic to $B(K)$ for a Hilbert space $K$.
* **49. Noncommutative Plancherel theorem.** If $G$ is second-countable,
  unimodular, and type I, there is a Plancherel measure $\mu$ on
  $\widehat G$ such that
  $$
  \|f\|_2^2=\int_{\widehat G}\|\pi(f)\|_{\mathrm{HS}}^2d\mu(\pi),
  \qquad f\in L^1\cap L^2.
  $$
  The transform extends unitarily onto the corresponding direct integral
  of Hilbert–Schmidt spaces. Nonunimodular groups require formal-dimension
  operators rather than this unmodified formula.
* **50. Stone–von Neumann theorem.** For the real Heisenberg group,
  every irreducible unitary representation with a fixed nontrivial central
  character is equivalent to the Schrödinger representation with that
  character. The remaining irreducibles are characters of the abelian quotient.
* **51. Kirillov's orbit correspondence.** For a connected simply
  connected nilpotent Lie group, coadjoint orbits in $\mathfrak g^*$
  parametrize the irreducible unitary representations. A representative
  is induced from the character associated to a polarization of the
  orbit functional $\ell$. A polarization is a subordinate subalgebra
  $\mathfrak h$ with $\ell([\mathfrak h,\mathfrak h])=0$ and dimension
  $(\dim\mathfrak g+\dim\mathfrak g_\ell)/2$.
* **52. Smooth vectors.** In a unitary representation of a Lie group,
  vectors $v$ for which $x\mapsto\pi(x)v$ is smooth are dense.
  On this common invariant domain, differentiation gives a Lie algebra
  representation satisfying
  $[d\pi(X),d\pi(Y)]=d\pi([X,Y])$.
* **53. Compact Lie-group spectral decomposition.** A bi-invariant
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

* **54. Coefficient algebra properties.** $B(G)$ is a Banach algebra
  under pointwise multiplication, using tensor products of representations.
  $A(G)$ is a closed ideal in $B(G)$ and lies in $C_0(G)$.
* **55. Amenability and invariant means.** A locally compact group is
  amenable exactly when there is a positive normalized left-invariant
  mean on $L^\infty(G)$. Compact and abelian groups are amenable;
  amenability is preserved under extensions and passage to closed subgroups.
* **56. Følner's criterion for discrete groups.** A discrete group is
  amenable exactly when, for every finite $K\subset G$ and
  $\varepsilon>0$, there is a finite nonempty $F$ with
  $|kF\mathbin\triangle F|<\varepsilon|F|$ for all $k\in K$.
* **57. Amenability and regular representations.** For locally compact
  $G$, amenability is equivalent to the trivial representation being
  weakly contained in $\lambda$, and to the canonical map
  $C^*(G)\to C_r^*(G)$ being an isomorphism.
  Here $\pi$ is weakly contained in $\rho$ if
  $\|\pi(f)\|\leq\|\rho(f)\|$ for every $f\in L^1(G)$.
* **58. Leptin's theorem.** $G$ is amenable exactly when $A(G)$
  has a bounded approximate identity for pointwise multiplication.
  See also the opening formulation in
  [Forrest–Kaniuth–Lau–Spronk](https://www.math.uwaterloo.ca/~nspronk/papers/forrestkls03.pdf).
* **59. Gelfand pairs.** For compact $K\subset G$, commutativity of
  the algebra of integrable $K$-bi-invariant functions is the defining
  Gelfand-pair property. If $G$ is compact, it is equivalent to
  $\dim H_\pi^K\leq1$ for every irreducible $\pi$.
* **60. Spherical functions.** In a Gelfand pair, normalized bounded
  spherical functions satisfy
  $\int_K\phi(xky)dk=\phi(x)\phi(y)$.
  Integration against their inverse-variable values gives the characters
  of the commutative $K$-bi-invariant convolution algebra. For compact
  $G$, they are coefficients of irreducible representations on their
  one-dimensional $K$-fixed spaces.

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
property (T) and random walks require further dedicated inventories.

Local source copies consulted:

* [Folland, *A Course in Abstract Harmonic Analysis*](References/Folland2015CourseAbstractHarmonicAnalysis-CRCPress.pdf).
* [Hewitt–Ross, *Abstract Harmonic Analysis*, II](References/HewittRoss1970AbstractHarmonicAnalysis2StructureAnalysisCompactGroupsAnalysisLocallyCompactAbelianGroups-SpringerGL152.pdf).
* [Faraut, *Analysis on Lie Groups*](References/Faraut2008AnalysisLieGroups-CambridgeStudiesAM110.pdf).
* [Kaniuth–Taylor, *Induced Representations of Locally Compact Groups*](References/KaniuthTaylor2013InducedRepresentationsLocallyCompactGroups-Cambridge.TractsMath197.pdf).
* [Deitmar–Echterhoff, *Principles of Harmonic Analysis*](References/DeitmarEchterhoff2014PrinciplesHarmonicAnalysis2ndEd-SpringerUTX.pdf).

The noncommutative transform conventions have been stated separately because
the references use both integrated and adjoint Fourier transforms.
