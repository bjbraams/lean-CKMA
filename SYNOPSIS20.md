# Synopsis: Banach algebras and commutative harmonic analysis of algebras

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects the recurring core of Section 20 of
[CKMA-bib.md](CKMA-bib.md). It develops
spectra, characters and Gelfand transforms, function algebras, ideal theory,
convolution algebras, and amenability. General operator algebra representation
theory belongs primarily to Section 23, and harmonic analysis on groups
to Section 28; the overlap here concerns the algebraic methods that organize
those subjects.

A **Banach algebra** is a complex Banach space with associative bilinear
multiplication satisfying $\|ab\|\leq\|a\|\|b\|$. Identities, when present,
are normalized to have norm one. For a nonunital algebra use the
**unitization** $A^\#=A\oplus\mathbb C1$, with the usual product and
sum norm. Spectra of nonunital elements are taken in this unitization.
Write $A^{-1}$ for the invertible group of a unital algebra and
$\sigma_A(a)=\{\lambda:\lambda1-a\notin A^{-1}\}$.
A **C*-algebra** has a conjugate-linear involution $a\mapsto a^*$ with
$(ab)^*=b^*a^*$ and $\|a^*a\|=\|a\|^2$.

## Invertibility, spectra, and holomorphic calculus

* **1. Neumann series.** If $\|a\|<1$, then
  $(1-a)^{-1}=\sum_{n\geq0}a^n$ in norm. Consequently $A^{-1}$ is open,
  inversion is continuous and holomorphic, and
  $\|(a+h)^{-1}-a^{-1}\|\to0$ as $h\to0$ for $a\in A^{-1}$.
* **2. Spectrum theorem.** In a nonzero unital complex Banach algebra,
  $\sigma_A(a)$ is nonempty compact and is contained in
  $\{\lambda:|\lambda|\leq\|a\|\}$. The map $a\mapsto\sigma(a)$ is upper
  semicontinuous (Newburgh), though not continuous in general.
* **3. Spectral radius formula.**
  $$r(a)=\max_{\lambda\in\sigma_A(a)}|\lambda|
       =\lim_{n\to\infty}\|a^n\|^{1/n}
       =\inf_{n\geq1}\|a^n\|^{1/n}.$$
  Thus $\sum a^n$ converges whenever $r(a)<1$, even if $\|a\|\geq1$.
* **4. Resolvent identity.** The resolvent $R(\lambda,a)=(\lambda1-a)^{-1}$
  is holomorphic off the spectrum and satisfies
  $R(\lambda,a)-R(\mu,a)=(\mu-\lambda)R(\lambda,a)R(\mu,a)$.
* **5. Polynomial and rational spectral mapping.**
  $\sigma(p(a))=p(\sigma(a))$ for every polynomial $p$; the same holds
  for rational functions with poles outside $\sigma(a)$.
* **6. Gelfand–Mazur theorem.** A complex normed division algebra (completeness
  is not needed) is $\mathbb C1$. Over the reals the normed division algebras
  are $\mathbb R$, $\mathbb C$, and $\mathbb H$ (Mazur).
* **7. Holomorphic functional calculus.** A function holomorphic on a
  neighborhood of $\sigma(a)$ defines
  $f(a)=(2\pi i)^{-1}\int_\Gamma f(z)(z1-a)^{-1}\,dz$.
  This is independent of admissible contours, is a unital algebra
  homomorphism in $f$, continuous for locally uniform convergence, and
  satisfies $\sigma(f(a))=f(\sigma(a))$ and $(g\circ f)(a)=g(f(a))$.
* **8. Riesz idempotents.** A decomposition of $\sigma(a)$ into disjoint
  relatively open-and-closed parts gives commuting idempotents by contour
  integration of the resolvent. They sum to one and split the element
  into the corresponding spectral parts.
* **9. Change of ambient algebra.** If $B$ is a closed unital subalgebra
  of $A$ with the same identity, then $\sigma_A(b)\subset\sigma_B(b)$
  and $\partial\sigma_B(b)\subset\partial\sigma_A(b)$, so $\sigma_B(b)$ is
  $\sigma_A(b)$ with some bounded components of its complement filled in.
  Hence the spectra agree if $\mathbb C\setminus\sigma_A(b)$ is connected;
  they always agree for C*-subalgebras of C*-algebras.
* **10. Radical criterion.** The Jacobson radical is a closed two-sided
  ideal, characterized by
  $a\in\operatorname{rad}A$ exactly when $1-ba$ is invertible for every
  $b\in A$ in the unitization. The quotient by the radical is semisimple.
  Radical elements are quasinilpotent; the converse holds for commutative
  algebras but fails in general (e.g. in matrix algebras).

## Characters and the Gelfand representation

A **character** is a nonzero multiplicative complex linear functional.
The **character space** $\Delta(A)$ has the weak-star topology, and
$\widehat a(\varphi)=\varphi(a)$ is the **Gelfand transform**.
An algebra is **semisimple** if its Jacobson radical is zero. The next
statements assume commutativity unless indicated otherwise.

* **11. Automatic continuity of characters.** Every character is continuous
  with $|\varphi(a)|\leq r(a)\leq\|a\|$. On a unital algebra it has
  norm one and takes the identity to one.
* **12. Maximal ideals and characters.** In a commutative unital Banach
  algebra, every maximal proper ideal is closed and is the kernel of a
  unique character. Its quotient is $\mathbb C$. In the nonunital case
  the analogous correspondence uses maximal modular ideals.
* **13. Gelfand representation theorem.** $\Delta(A)$ is locally compact
  Hausdorff, compact when $A$ is unital, and
  $a\mapsto\widehat a$ is a contractive homomorphism into
  $C_0(\Delta(A))$. For nonunital $A$, adjoining the zero functional
  gives a compact space.
* **14. Spectrum by characters.** For unital commutative $A$,
  $\sigma(a)=\widehat a(\Delta(A))$ and
  $r(a)=\|\widehat a\|_\infty$. In the nonunital convention used here,
  $\sigma(a)=\widehat a(\Delta(A))\cup\{0\}$.
* **15. Semisimplicity criterion.**
  $\operatorname{rad}A=\bigcap_{\varphi\in\Delta(A)}\ker\varphi
  =\{a:r(a)=0\}$. Hence $A$ is semisimple exactly when the Gelfand
  transform is injective, and exactly when the spectral radius is a norm.
* **16. Simultaneous invertibility test.** In a commutative unital algebra,
  $a_1,\ldots,a_n$ generate the unit ideal exactly when they have no
  common zero on $\Delta(A)$. Equivalently, some $b_j\in A$ satisfy
  $\sum_jb_ja_j=1$.
* **17. Several-variable functional calculus.** For $a_1,\ldots,a_n$ in
  a commutative unital $A$ and $f$ holomorphic near the joint spectrum
  $\{(\widehat a_1(\varphi),\ldots,\widehat a_n(\varphi)):\varphi\in\Delta(A)\}
  \subset\mathbb C^n$, there is $b\in A$ with
  $\widehat b=f(\widehat a_1,\ldots,\widehat a_n)$ (Shilov, Arens–Calderón).
  Consequences: the identity component of $A^{-1}$ is $\exp A$, and
  $A^{-1}/\exp A\cong H^1(\Delta(A),\mathbb Z)$ (Arens–Royden).
* **18. Automatic continuity into semisimple algebras.** Every algebra
  homomorphism from a Banach algebra into a commutative semisimple Banach
  algebra is continuous (Shilov). More generally, every semisimple Banach
  algebra, commutative or not, has a unique complete algebra norm up to
  equivalence (Johnson).
* **19. Gleason–Kahane–Żelazko theorem.** If a complex linear functional
  $F$ on a unital Banach algebra satisfies $F(1)=1$ and never vanishes
  on invertible elements, then it is multiplicative. Neither continuity
  nor commutativity need be assumed.
* **20. Commutative C*-algebra theorem.** If $A$ is a commutative
  C*-algebra, its Gelfand transform is an isometric star isomorphism
  $A\cong C_0(\Delta(A))$. For unital $A$ the target is $C(\Delta(A))$.
* **21. Uniform norm criterion.** A commutative Banach algebra satisfying
  $\|a^2\|=\|a\|^2$ for all $a$ has $\|a\|=r(a)$ and is represented
  isometrically as a closed function algebra on its character space.

## Uniform algebras, boundaries, and representing measures

A **uniform algebra** on compact Hausdorff $K$ is a closed subalgebra
$A\subset C(K)$ containing constants and separating points. It is
**natural** if every character is evaluation at a point of $K$.
A closed **boundary** $F\subset K$ satisfies
$\|f\|_K=\max_F|f|$ for all $f\in A$; the smallest such boundary
is the **Shilov boundary**.

* **22. Stone–Weierstrass theorem.** A conjugation-closed complex uniform
  algebra on $K$ is all of $C(K)$. The real version requires only constants
  and point separation.
* **23. Shilov boundary theorem.** Every uniform algebra has a smallest
  closed boundary. Restricting to that boundary is an isometric algebra
  embedding, though the character space can be larger than the boundary.
* **24. Representing measures.** Every character of a uniform algebra
  on $K$ has a representing probability measure $\mu$ on $K$:
  $\varphi(f)=\int_Kf\,d\mu$. Such a measure can be chosen supported
  on the Shilov boundary and need not be unique.
* **25. Peak points and boundaries.** If some $f\in A$ has $f(x)=1$
  and $|f(y)|<1$ for $y\ne x$, then $x$ belongs to every closed
  boundary and its only representing probability measure is $\delta_x$.
  For compact metrizable $K$, the closure of the peak points is the Shilov
  boundary (Bishop's theorem).
* **26. Shilov idempotent theorem.** For a commutative unital Banach
  algebra and a clopen subset $U\subset\Delta(A)$, there is an idempotent
  $e\in A$ with $\widehat e=1_U$. Thus disconnected character spaces
  force nontrivial algebraic decompositions.
* **27. Polynomial hull interpretation.** For compact $K\subset\mathbb C^n$,
  the character space of the uniform closure $P(K)$ of polynomials is its
  polynomial hull
  $\widehat K=\{z:|p(z)|\leq\sup_K|p|\text{ for every polynomial }p\}$.
* **28. Disk algebra model.** The disk algebra consists of continuous
  functions on $\overline{\mathbb D}$ holomorphic on $\mathbb D$.
  Its character space is $\overline{\mathbb D}$ and its Shilov boundary
  is $\mathbb T$; the representing measures of $z\in\mathbb D$ include the
  Poisson measure, and $P(\mathbb T)$ is the disk algebra restricted to
  $\mathbb T$.
* **29. Carleson corona theorem.** The open disk is dense in the character
  space of $H^\infty(\mathbb D)$. Equivalently, if
  $f_1,\ldots,f_n\in H^\infty$ satisfy $\sum_j|f_j|\geq\delta>0$ on
  $\mathbb D$, then $\sum_jg_jf_j=1$ for some $g_j\in H^\infty$, with
  bounds on $\|g_j\|_\infty$ depending only on $n$ and $\delta$.

## Regularity, ideals, and spectral synthesis

For commutative $A$, the **hull** of an ideal $I$ is
$h(I)=\{\varphi:\widehat a(\varphi)=0\ (a\in I)\}$; for
$F\subset\Delta(A)$ its **kernel** is
$k(F)=\{a:\widehat a|_F=0\}$. The algebra is **regular** if a point
can be separated from any closed set not containing it by a Gelfand
transform taking values one at the point and zero on the set. It is
**Tauberian** if elements with compactly supported Gelfand transform are dense.

* **30. Hull–kernel correspondence.** $I\subset k(h(I))$, and
  $k(h(I))/I$ is the radical of $A/I$ for closed ideals in a unital
  commutative algebra. Thus equality holds exactly when that quotient is
  semisimple.
* **31. Closed ideals of $C_0(K)$.** Every closed ideal is $k(F)$ for a
  unique closed subset $F\subset K$, and restriction identifies
  $C_0(K)/k(F)$ isometrically with $C_0(F)$.
* **32. Regularity and topology.** A commutative semisimple Banach algebra
  is regular exactly when its Gelfand topology agrees with the hull–kernel
  topology. Regularity provides functions localized in prescribed open
  neighborhoods of the character space.
* **33. Compact localization.** In a regular algebra, for compact
  $K\subset U\subset\Delta(A)$ with $U$ open, there is $a\in A$
  with $\widehat a=1$ on $K$ and compact support contained in $U$.
  The construction also yields finite subordinate partitions on compact sets.
* **34. Minimal and maximal ideals for a hull.** In a regular semisimple
  Tauberian algebra, let $j(F)$ be the closure of elements whose transforms
  have compact support disjoint from closed $F$. Every closed ideal with
  hull $F$ lies between $j(F)$ and $k(F)$. The set $F$ is a **set of
  synthesis** exactly when $j(F)=k(F)$.
* **35. Failure of synthesis detected by derivatives.** In
  $C^1[0,1]$ with its standard Banach algebra norm, the ideals
  $\{f:f(t_0)=0\}$ and $\{f:f(t_0)=f'(t_0)=0\}$, for
  $0<t_0<1$, are distinct closed ideals with the same hull.
  Pointwise zero sets therefore need not determine closed ideals.
* **36. Bounded point derivations.** A functional satisfying
  $D(ab)=\varphi(a)D(b)+\varphi(b)D(a)$ is a point derivation at
  $\varphi$. Interior differentiation gives nonzero bounded point
  derivations on the disk algebra; $C(K)$ has none.

## Convolution algebras and Fourier transforms

Let $G$ be a locally compact group with left Haar measure. The group algebra
$L^1(G)$ has convolution
$(f*g)(x)=\int f(y)g(y^{-1}x)\,dy$; $M(G)$ is the algebra of finite
regular measures with convolution and identity $\delta_e$. When $G$ is
abelian, its dual group $\widehat G$ consists of continuous unitary
characters, and $\widehat f(\gamma)=\int f(x)\overline{\gamma(x)}\,dx$.

* **37. Group algebra and approximate identities.** $L^1(G)$ is a Banach
  algebra and a closed ideal of $M(G)$. It has a two-sided approximate
  identity of norm one, constructed from nonnegative functions concentrated
  near the identity. It has an identity element exactly when $G$ is discrete.
* **38. Character space of an abelian group algebra.** For abelian $G$,
  $\Delta(L^1(G))\cong\widehat G$, and the Gelfand transform is the
  Fourier transform. $L^1(G)$ is semisimple and
  $\widehat{f*g}=\widehat f\,\widehat g$.
* **39. Riemann–Lebesgue and uniqueness.** $\widehat f\in C_0(\widehat G)$
  for $f\in L^1(G)$; the transform is injective. Finite measures have
  bounded continuous Fourier–Stieltjes transforms, also uniquely determining
  the measure.
* **40. Wiener lemma.** If $f\in C(\mathbb T)$ has an absolutely
  convergent Fourier series and no zeros on $\mathbb T$, then $1/f$ also
  has an absolutely convergent Fourier series. More generally a holomorphic
  function of $f$ near its range belongs to the same Wiener algebra (Lévy).
* **41. Wiener Tauberian theorem.** For abelian $G$ and $f\in L^1(G)$,
  the closed span of the translates of $f$ is all of $L^1(G)$ exactly
  when $\widehat f$ has no zero on $\widehat G$. Equivalently, the
  closed convolution ideal generated by $f$ is the entire algebra.
* **42. Regularity and Tauberianity.** For every locally compact abelian
  $G$, $L^1(G)$ is regular and Tauberian. In particular there are
  Fourier transforms supported in arbitrarily small neighborhoods of any
  dual point, and compactly supported transforms give a dense ideal.
* **43. Spectral synthesis in $L^1(G)$.** Points, closed subgroups, and
  more generally closed sets in the coset ring of $\widehat G$ are sets of
  synthesis (indeed Ditkin sets). If $G$ is noncompact, so that
  $\widehat G$ is nondiscrete, some closed subsets of $\widehat G$ fail
  synthesis (Malliavin); for $\mathbb R^n$, $n\geq3$, the unit sphere
  already fails (L. Schwartz).
* **44. Wendel multiplier theorem.** Every bounded operator on $L^1(G)$
  commuting with right translations is left convolution by a unique
  $\mu\in M(G)$, and its norm is $\|\mu\|$. In the abelian case this
  identifies the multiplier algebra of $L^1(G)$ with $M(G)$.
* **45. Wiener–Pitt phenomenon.** For nondiscrete abelian $G$ the
  Fourier–Stieltjes characters do not exhaust $\Delta(M(G))$, and
  $\sigma(\mu)$ can be strictly larger than the closure of
  $\widehat\mu(\widehat G)$. There
  are measures on $\mathbb T$ whose Fourier coefficients are bounded away
  from zero but which are not invertible in $M(\mathbb T)$.
* **46. Cohen idempotent theorem.** For abelian $G$, the transforms of
  idempotent measures in $M(G)$ are exactly indicators of sets in the coset
  ring of $\widehat G$, generated by cosets of its open subgroups. The
  hulls of closed ideals of $L^1(G)$ with bounded approximate identities
  are exactly the closed sets in the coset ring of $\widehat G$.

## Approximate identities, modules, and derivations

A **bounded approximate identity** is a bounded net $(e_\alpha)$ with
$e_\alpha a\to a$ and $ae_\alpha\to a$. A left Banach $A$-module $X$
is **essential** if $\overline{AX}=X$. A bounded **derivation** into a
bimodule satisfies $D(ab)=a\cdot D(b)+D(a)\cdot b$; it is **inner**
if $D(a)=a\cdot x-x\cdot a$ for some fixed $x$.

* **47. Cohen–Hewitt factorization.** Let $A$ have a bounded left
  approximate identity $(e_\alpha)$ and let $X$ be a left Banach module.
  Then $X$ is essential exactly when $e_\alpha x\to x$ for all $x$, and in
  that case each $x\in X$ has the form $x=ay$ with $a\in A$, and $y$
  can be taken in $\overline{Ax}$ with $\|y-x\|<\varepsilon$ for any given
  $\varepsilon>0$. In particular $A=A^2$ when $A$ has a bounded approximate identity.
* **48. Multipliers of continuous-function algebras.** The multiplier
  algebra of $C_0(K)$ is $C_b(K)$, isometrically, acting by pointwise
  multiplication; for noncompact $K$ it is larger than the unitization.
* **49. Singer–Wermer theorem.** The range of every continuous derivation
  from a commutative Banach algebra into itself lies in its radical.
  Continuity can be dropped (Thomas), and every derivation of a commutative
  semisimple Banach algebra into itself is zero (Johnson).

## Amenability and its harmonic-analytic characterizations

A Banach algebra $A$ is **amenable** if every bounded derivation into
every dual Banach bimodule is inner. A locally compact group is
**amenable** if $L^\infty(G)$ admits a positive normalized left-invariant
mean. These are different definitions connected by a theorem below.
The projective tensor product $A\widehat\otimes_\pi A$ carries the
outer bimodule actions, and $m(a\otimes b)=ab$.

* **50. Approximate diagonal characterization.** $A$ is amenable exactly
  when there is a bounded net $d_\alpha\in A\widehat\otimes_\pi A$ such that
  $a\cdot d_\alpha-d_\alpha\cdot a\to0$ and
  $m(d_\alpha)a\to a$ for every $a\in A$.
* **51. Approximate identity consequence.** Every amenable Banach algebra
  has a bounded two-sided approximate identity. Thus an algebra lacking
  such an identity cannot be amenable.
* **52. Permanence of amenability.** Continuous surjective homomorphic
  images of amenable Banach algebras are amenable. A closed ideal in an
  amenable algebra is amenable exactly when it has a bounded approximate
  identity. Projective tensor products of amenable algebras are amenable.
* **53. Basic examples.** Every $C_0(K)$ is amenable, as is every finite
  direct sum of full complex matrix algebras. A finite-dimensional complex
  Banach algebra is amenable exactly when it is semisimple.
* **54. Vanishing in symmetric modules.** If $A$ is commutative and
  amenable, every bounded derivation into a symmetric Banach bimodule is
  zero. In particular, there are no nonzero bounded point derivations.
* **55. Johnson group algebra theorem.** For every locally compact group
  $G$, the Banach algebra $L^1(G)$ is amenable exactly when $G$ is amenable.
  All abelian and compact groups are amenable; the discrete free group
  on two generators is not.
* **56. Reiter characterization.** $G$ is amenable exactly when there are
  nonnegative $f_\alpha\in L^1(G)$ of integral one with
  $\|L_sf_\alpha-f_\alpha\|_1\to0$ uniformly for $s$ in compact subsets
  of $G$, where $L_sf(t)=f(s^{-1}t)$.
* **57. Følner criterion for discrete groups.** A discrete group is
  amenable exactly when for every finite $S\subset G$ and $\varepsilon>0$
  some finite nonempty $F\subset G$ satisfies
  $|sF\mathbin\triangle F|<\varepsilon|F|$ for all $s\in S$.

The **Fourier algebra** $A(G)$ consists of sums of coefficient functions
of the left regular representation, with norm given by the infimum of the
sums of the products of their $L^2$ vector norms. It is a commutative
Banach algebra under pointwise multiplication. The **Fourier–Stieltjes
algebra** $B(G)$ uses coefficients of arbitrary unitary representations.

* **58. Abelian Fourier algebra identification.** If $G$ is abelian,
  Fourier transformation identifies $L^1(\widehat G)$ isometrically with
  $A(G)$, and $M(\widehat G)$ with $B(G)$; convolution corresponds to
  pointwise multiplication.
* **59. Leptin theorem.** $A(G)$ has a bounded approximate identity
  exactly when $G$ is amenable. This concerns a bounded approximate
  identity, rather than Banach algebra amenability of $A(G)$.
* **60. Weak amenability of group algebras.** For every locally compact
  $G$, each bounded derivation $L^1(G)\to L^1(G)^*$ is inner. Thus
  group algebras are weakly amenable even when the group is not amenable.

## Bidual multiplication and weak compactness

The two **Arens products** extend multiplication to $A^{**}$ by the two
orders of iterated weak-star limits of bounded approximating nets. They
agree on the canonical copy of $A$. The algebra is **Arens regular** if
these products agree everywhere.

* **61. Arens regularity criteria.** $A$ is Arens regular exactly when,
  for each $f\in A^*$, the operator $a\mapsto[b\mapsto f(ab)]$ from $A$
  to $A^*$ is weakly compact. Equivalently (Grothendieck's double-limit
  criterion), for all bounded sequences $(a_n),(b_m)$ and $f\in A^*$,
  $\lim_n\lim_m f(a_nb_m)=\lim_m\lim_n f(a_nb_m)$ whenever both iterated
  limits exist.
* **62. C*-algebra regularity.** Every C*-algebra is Arens regular; its
  bidual, with the Arens product, is a von Neumann algebra, the enveloping
  von Neumann algebra.
* **63. Group algebra contrast.** $L^1(G)$ is Arens regular exactly when
  the locally compact group $G$ is finite (Young). In particular,
  commutativity, semisimplicity, and amenability do not imply Arens
  regularity.

## Reference guide

Bonsall–Duncan supplies the spectral, radical, character, and automatic
continuity backbone. Kaniuth develops the commutative Gelfand theory,
holomorphic calculus (including the several-variable calculus and the
Arens–Royden theorem), boundaries, regularity, group algebras, multipliers,
and synthesis in a single course. These topics overlap extensively with
Rickart, Gelfand–Raikov–Shilov, Gamelin, Browder, Palmer, and Dales;
Gamelin is the standard source for uniform algebras and the corona theorem.
Runde gives the module, derivation, approximate-diagonal, and group
amenability theory, including the Fourier algebra connections. The bidual
viewpoint is developed further in the newer Dales–Ülger reference.
Specialist automatic continuity problems, stable ranks, and the detailed
classification of synthesis sets are beyond this common selection.

Local source copies consulted:

* [Bonsall–Duncan, Complete Normed Algebras](References/BonsallDuncan1973CompleteNormedAlgebras-SpringerErgeb80.pdf).
* [Kaniuth, A Course in Commutative Banach Algebras](References/Kaniuth2009CourseInCommutativeBanachAlgebras-SpringerGTM.pdf).
* [Runde, Amenable Banach Algebras: A Panorama](References/Runde2020AmenableBanachAlgebras-Springer.SMM.pdf).
