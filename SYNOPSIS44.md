# Synopsis: Riemann surfaces, quasiconformal mappings, and Teichmüller theory

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects recurring core material from Section 44 of
[CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md).
It joins the analytic theory of surfaces, divisors and periods, measurable
complex structures, and deformation spaces. The emphasis is on results
shared by several surface and quasiconformal references; the algebraic
geometry of higher-dimensional varieties and the full theory of Kleinian
three-manifolds are outside its scope.

A **Riemann surface** is a connected, second-countable Hausdorff
one-dimensional complex manifold. An **open surface** means a noncompact
surface without boundary. Unless otherwise stated, compact surfaces have
no boundary and genus $g$. Holomorphic $1$-forms are sections of the
canonical bundle $K_X$; quadratic differentials are sections of $K_X^2$.
The detailed Teichmüller statements below concern closed oriented surfaces
of genus $g\geq2$, with the torus case stated separately.

## Holomorphic maps, coverings, and uniformization

* **1. Local mapping theorem.** A nonconstant holomorphic map of
  surfaces has local coordinate form $z\mapsto z^e$, $e\geq1$.
  It is open; its critical points are isolated, and $e$ is its local degree.
* **2. Compact branched coverings.** A nonconstant holomorphic map
  between compact surfaces is surjective and proper, with a fixed
  finite degree $d$. Each fiber has total local degree $d$.
* **3. Riemann–Hurwitz formula.** For such a map $f:X\to Y$,
  $2g_X-2=d(2g_Y-2)+\sum_{x\in X}(e_x-1)$.
* **4. Compact maximum principle.** Holomorphic functions on a
  compact surface are constant. A nonzero meromorphic function has
  equally many zeros and poles, counting orders.
* **5. Global residue theorem.** A meromorphic $1$-form on a compact
  surface has total residue zero. The residue is independent of the
  local coordinate.
* **6. Covering complex structures.** A topological covering of a
  Riemann surface has a unique complex structure making the covering
  locally biholomorphic. Deck transformations are holomorphic, and
  the universal covering is again a Riemann surface.
* **7. Uniformization.** Every simply connected Riemann surface is
  biholomorphic to exactly one of $\widehat{\mathbb C}$,
  $\mathbb C$, and $\mathbb D$. General surfaces are quotients
  of these universal covers by freely acting deck groups.
* **8. Compact uniformization by genus.** Genus zero gives the
  sphere; genus one gives $\mathbb C/\Lambda$ for a lattice;
  genus at least two gives $\mathbb D/\Gamma$ for a torsion-free
  cocompact Fuchsian group. In the last case the conformal class has
  a unique metric of curvature $-1$.
* **9. Gauss–Bonnet.** For any smooth metric on a compact surface,
  $\int_XK\,dA=2\pi(2-2g)$.
  A curvature-$-1$ surface of genus $g\geq2$ has area $4\pi(g-1)$.
* **10. Schwarz–Pick on surfaces.** Holomorphic maps between
  hyperbolic surfaces contract their complete Poincaré metrics.
  Equality in the infinitesimal estimate at a point forces the map
  to be a holomorphic covering and a local isometry.

## Divisors, line bundles, and Riemann–Roch

A **divisor** is a finite integral sum $D=\sum n_pp$; its degree
is $\sum n_p$. A **principal divisor** is $(f)$ for a nonzero
meromorphic function. Set
$L(D)=\{f:(f)+D\geq0\}\cup\{0\}$ and $\ell(D)=\dim L(D)$.
The line bundle $\mathcal O(D)$ has these meromorphic functions as
its holomorphic sections.

* **11. Divisor–bundle correspondence.** Divisors modulo principal
  divisors classify holomorphic line bundles on a compact Riemann
  surface. Degree is invariant under linear equivalence and additive
  under tensor product.
* **12. Riemann–Roch theorem.**
  $\ell(D)-\ell(K_X-D)=\deg D+1-g$.
  Equivalently, $h^0(L)-h^1(L)=\deg L+1-g$ for a line bundle $L$.
* **13. Serre duality.** $H^1(X,L)$ is naturally dual to
  $H^0(X,K_X\otimes L^{-1})$, through integration or residue pairing.
* **14. Canonical degree and dimensions.**
  $\deg K_X=2g-2$, $h^0(K_X)=g$, and $h^1(\mathcal O_X)=g$.
  For $g\geq2$, $h^0(K_X^2)=3g-3$.
* **15. High-degree nonspeciality.** If $\deg D>2g-2$, then
  $\ell(D)=\deg D+1-g$. A line bundle of negative degree has
  no nonzero holomorphic sections.
* **16. Meromorphic functions exist.** For each $p\in X$,
  $\ell((g+1)p)\geq2$. Hence every compact surface has a
  nonconstant meromorphic function, of degree at most $g+1$.
* **17. Very ample divisors.** A line bundle of degree at least
  $2g+1$ separates points and tangent directions, and its complete
  linear system embeds $X$ into projective space.
* **18. Algebraicity of compact surfaces.** Every compact Riemann
  surface is the analytification of a nonsingular projective algebraic
  curve. Its meromorphic function field is a finite extension of
  $\mathbb C(f)$ for every nonconstant meromorphic $f$.
* **19. Genus-zero classification.** A genus-zero compact surface
  has a degree-one meromorphic function and is therefore biholomorphic
  to the sphere. This also follows from uniformization.
* **20. Principal-part obstruction for functions.** Prescribed finite
  principal parts $p_j$ at finitely many points of compact $X$
  come from a meromorphic function exactly when
  $\sum_j\operatorname{Res}(p_j\omega)=0$ for every holomorphic
  $1$-form $\omega$.
* **21. Principal parts of differentials.** Prescribed meromorphic
  differential principal parts on a compact surface are realizable
  exactly when their residues sum to zero. The ambiguity is a
  holomorphic differential.
* **22. Weierstrass gap theorem.** At a point of a genus-$g\geq1$
  surface, exactly $g$ positive integers fail to occur as the order
  of the sole pole of a meromorphic function. They lie in
  $\{1,\ldots,2g-1\}$. At generic points the gaps are $1,\ldots,g$.
* **23. Canonical mapping.** For $g\geq2$, the canonical system
  has no base points. It embeds a nonhyperelliptic surface; on a
  hyperelliptic surface it factors through the degree-two map to
  $\mathbb P^1$ and the degree-$(g-1)$ rational normal curve.
* **24. Hyperelliptic branch count.** A double cover of the sphere
  by a genus-$g$ surface has $2g+2$ branch points. Every genus-two
  compact surface is hyperelliptic.

## Harmonic forms, periods, and the Jacobian

In this subsection assume $g\geq1$.
Choose a symplectic homology basis $a_1,b_1,\ldots,a_g,b_g$.
Normalize holomorphic forms by $\int_{a_j}\omega_i=\delta_{ij}$
and set $\tau_{ij}=\int_{b_j}\omega_i$.

* **25. Hodge theorem on surfaces.** Every real de Rham cohomology
  class in degree one has a unique harmonic representative. These
  form a $2g$-dimensional real space, the real parts of holomorphic
  differentials and their conjugate partners.
* **26. Riemann bilinear relations.** For closed $1$-forms,
  $\int_X\alpha\wedge\beta=\sum_j(A_j(\alpha)B_j(\beta)
  -B_j(\alpha)A_j(\beta))$. Applied to holomorphic forms and their
  conjugates, this gives the normalization and positivity relations.
* **27. Period matrix.** The normalized matrix satisfies
  $\tau^T=\tau$ and $\Im\tau>0$.
  The torus $J(X)=\mathbb C^g/(\mathbb Z^g+\tau\mathbb Z^g)$
  carries a natural principal polarization.
* **28. Abel's theorem.** A degree-zero divisor $D=\sum n_pp$
  is principal exactly when
  $\sum n_p\int_{p_0}^p(\omega_1,\ldots,\omega_g)=0$ in $J(X)$.
* **29. Jacobi inversion.** The Abel map from the $g$th symmetric
  power $X^{(g)}$ onto $J(X)$ is surjective and generically
  one-to-one. Every degree-$g$ divisor class has an effective representative.
* **30. Abel–Jacobi embedding.** For $g\geq1$, the map
  $p\mapsto\int_{p_0}^p\omega$ embeds $X$ in $J(X)$.
  For $g=1$ it is an isomorphism onto the torus.
* **31. Riemann theta divisor.** The theta function
  $\theta(z,\tau)=\sum_{n\in\mathbb Z^g}
  e^{\pi i n^T\tau n+2\pi i n^Tz}$ defines a divisor on $J(X)$.
  Its zero set is a translate of the Abel image of effective
  degree-$(g-1)$ divisors (Riemann's vanishing theorem).
* **32. Torelli's theorem.** A compact Riemann surface is determined
  up to biholomorphism by its principally polarized Jacobian.
  The polarization is part of the required data.

## Open surfaces and global analytic construction

* **33. Behnke–Stein theorem.** Every open Riemann surface is Stein:
  holomorphic functions separate points, give local coordinates, and
  have compact holomorphic hulls of compact sets.
* **34. Open-surface Mittag–Leffler and Weierstrass theorems.**
  Arbitrary meromorphic principal parts on a discrete set are globally
  realizable on an open surface, and every divisor there is principal.
  Thus the compact-surface cohomological obstructions disappear.
* **35. Runge approximation.** For compact $K$ in an open surface
  $X$, holomorphic functions near $K$ are uniformly approximable by
  functions holomorphic on $X$ exactly when $X\setminus K$ has
  no relatively compact connected component.
* **36. Global $\bar\partial$ solvability.** Every smooth $(0,1)$-form
  on an open Riemann surface is $\bar\partial u$ for a smooth
  function $u$. More generally coherent analytic sheaves have vanishing
  higher cohomology there.

## Quasiconformal mappings and measurable complex structures

An orientation-preserving homeomorphism $f:\Omega\to\Omega'$ is
**$K$-quasiconformal** if $f\in W^{1,2}_{\mathrm{loc}}$ and
$|f_{\bar z}|\leq k|f_z|$ almost everywhere, where
$k=(K-1)/(K+1)<1$. Its **Beltrami coefficient** is
$\mu_f=f_{\bar z}/f_z$. A Beltrami differential transforms as
$\mu(z)d\bar z/dz$ under conformal coordinate changes.

* **37. Analytic and geometric equivalence.** The Sobolev definition
  agrees with absolute continuity on almost every coordinate line
  plus bounded distortion, and with the inequalities
  $K^{-1}\operatorname{Mod}_2\Gamma\leq
  \operatorname{Mod}_2(f\Gamma)\leq K\operatorname{Mod}_2\Gamma$
  for all curve families.
* **38. Weyl's lemma.** A $1$-quasiconformal map is conformal.
  Almost everywhere vanishing of $f_{\bar z}$ gives this conclusion
  for a Sobolev map; pointwise differentiability almost everywhere alone
  would not suffice.
* **39. Measurable Riemann mapping theorem.** Every measurable
  $\mu$ on the sphere with $\|\mu\|_\infty<1$ is integrated
  by a quasiconformal homeomorphism solving
  $f_{\bar z}=\mu f_z$. Fixing the images of three distinct
  points determines it uniquely.
* **40. Conformal ambiguity and Stoilow factorization.** Two
  homeomorphic solutions of the same Beltrami equation differ by
  conformal postcomposition. More generally a nonconstant planar
  quasiregular map factors locally, and globally on a plane domain
  after integrating its coefficient, as $h\circ\phi$ with $h$
  holomorphic and $\phi$ quasiconformal.
* **41. Composition and inversion.** Compositions have maximal
  dilatation at most the product of the dilatations; inverses have the
  same planar maximal dilatation. Pullback of Beltrami differentials
  obeys the derivative chain rule almost everywhere.
* **42. Area formula and null sets.** Planar quasiconformal maps
  and their inverses preserve area-null sets,
  $J_f=|f_z|^2-|f_{\bar z}|^2>0$ almost everywhere, and
  $|f(E)|=\int_EJ_f$ for measurable $E$.
* **43. Normal-family compactness.** Sphere $K$-quasiconformal maps
  fixing three distinct points form a compact family in the uniform
  spherical topology. Limits are $K$-quasiconformal homeomorphisms.
* **44. Parameter dependence.** The normalized sphere solution
  depends holomorphically on a holomorphic family of Beltrami
  coefficients uniformly bounded below one in $L^\infty$.
  This is pointwise holomorphic dependence of the normalized maps.
* **45. Mori distortion.** A normalized $K$-quasiconformal disk map
  fixing zero satisfies $|f(z)-f(w)|\leq C(K)|z-w|^{1/K}$.
  Local Hölder bounds and the inverse estimate hold on plane domains.
* **46. Quasisymmetric boundary maps.** A disk quasiconformal
  homeomorphism extends to a quasisymmetric circle homeomorphism.
  Conversely every orientation-preserving quasisymmetric circle map
  has a quasiconformal disk extension, with quantitative control.
* **47. Quasicircle characterization.** A Jordan curve is a
  quasiconformal image of the circle exactly when it is bounded turning:
  for any two points, the smaller-diameter joining subarc has diameter
  at most $C$ times their distance.
* **48. Reflection and welding.** A quasicircle admits a quasiconformal
  reflection fixing it pointwise. Every quasisymmetric circle
  homeomorphism is the welding of two conformal maps onto complementary
  Jordan domains bounded by a quasicircle, unique up to Möbius transformation.
* **49. Sharp higher integrability.** For planar $K>1$,
  $Df\in L^p_{\mathrm{loc}}$ for every $p<2K/(K-1)$ and
  $J_f\in L^q_{\mathrm{loc}}$ for every $q<K/(K-1)$.
  The endpoints cannot be included universally.
* **50. Astala area distortion.** If $f:\mathbb D\to\mathbb D$
  is $K$-quasiconformal and fixes zero, then
  $|f(E)|\leq C(K)|E|^{1/K}$ for measurable $E$.
  The exponent is sharp.
* **51. Dimension distortion.** If $\dim_HE=t$, a planar
  $K$-quasiconformal map satisfies
  $2t/[2K-(K-1)t]\leq\dim_Hf(E)\leq2Kt/[2+(K-1)t]$.
  Both bounds are sharp.
* **52. Finite distortion needs integrability hypotheses.** For
  $f\in W^{1,1}_{\mathrm{loc}}$, replacing bounded $K$ by a merely
  finite measurable $K(x)$ in $\|Df\|^n\leq K(x)J_f$,
  with $J_f\in L^1_{\mathrm{loc}}$,
  defines the finite-distortion setting. Without further integrability
  assumptions there are maps for which the classical openness,
  discreteness, or null-set conclusions fail.
* **53. Higher-dimensional quasiconformality.** For homeomorphisms
  in $\mathbb R^n$, the $W^{1,n}_{\mathrm{loc}}$ bounded-distortion
  definition is equivalent, with controlled constants, to bounded
  distortion of $n$-modulus. Such maps and their inverses have
  higher integrability $W^{1,n+\varepsilon}_{\mathrm{loc}}$ for
  some $\varepsilon=\varepsilon(n,K)>0$.
* **54. Quasiregular openness and discreteness.** A nonconstant
  continuous $W^{1,n}_{\mathrm{loc}}$ map with bounded distortion
  is open and discrete. In dimension two Stoilow factorization reduces
  its branch behavior to holomorphic branching; no such holomorphic
  factorization exists in higher dimensions.

## Teichmüller spaces and extremal maps

A point of $\mathcal T_g$ is a compact Riemann surface $X$ with
an orientation-preserving marking from a fixed topological surface,
modulo conformal maps compatible with the markings up to isotopy.
The **Teichmüller distance** is
$d_T(X,Y)=\frac12\inf_f\log K(f)$ over maps in the marked class.
Write $Q(X)=H^0(X,K_X^2)$ with $\|q\|_1=\int_X|q|$.

* **55. Extremal existence.** The infimum defining $d_T$ is attained
  in each marked homotopy class. If $X\ne Y$, the extremal map
  has coefficient $\mu=k\bar q/|q|$ for a nonzero $q\in Q(X)$,
  $0<k<1$.
* **56. Teichmüller uniqueness.** That extremal map is unique in
  its marked class. The initial quadratic differential is unique up
  to positive scalar; away from its zeros the map is affine in
  natural coordinates $w=\int\sqrt q$.
* **57. Complete geodesic metric.** $d_T$ is complete and any two
  points are joined by a unique Teichmüller geodesic. Stretching the
  horizontal and vertical directions of $q$ by $e^t$ and $e^{-t}$
  parametrizes it with unit speed.
* **58. Dimension and contractibility.** $\mathcal T_g$ is a complex
  manifold of dimension $3g-3$, homeomorphic to $\mathbb R^{6g-6}$.
  In particular it is contractible.
* **59. Infinitesimal deformation.** The tangent space is the quotient
  of bounded Beltrami differentials by those annihilating every
  $q\in Q(X)$ under $\int\mu q$.
  The holomorphic cotangent space is canonically $Q(X)$.
* **60. Teichmüller Finsler norm.** The infinitesimal norm is
  $\|[\mu]\|_T=\sup_{\|q\|_1\leq1}|\int\mu q|$,
  equivalently the least $L^\infty$ norm in the tangent class.
  Its path metric is $d_T$.
* **61. Bers embedding.** Fixing a base surface, simultaneous
  uniformization and a Schwarzian derivative embed $\mathcal T_g$
  biholomorphically as a bounded domain in the $3g-3$ dimensional
  space of quadratic differentials on the conjugate base surface.
* **62. Fenchel–Nielsen coordinates.** A fixed pants decomposition
  gives global real-analytic coordinates
  $(\ell_i,\tau_i)_{i=1}^{3g-3}\in(0,\infty)^{3g-3}\times\mathbb R^{3g-3}$,
  where lengths and real twists determine the marked hyperbolic surface.
* **63. Extremal-length distance formula.** For essential simple
  closed curves $\alpha$,
  $d_T(X,Y)=\frac12\log\sup_\alpha
  \operatorname{Ext}_Y(\alpha)/\operatorname{Ext}_X(\alpha)$.
  This connects quasiconformal distortion with the extremal metrics
  of Section 43.
* **64. Harmonic diffeomorphisms.** Between closed hyperbolic surfaces,
  every homotopy class of orientation-preserving homeomorphisms
  contains a unique harmonic map, and that map is a diffeomorphism.
* **65. Hopf parametrization.** The Hopf differential of a harmonic
  map is holomorphic. With the source hyperbolic surface fixed, the
  Hopf differentials of the marked harmonic diffeomorphisms parametrize
  $\mathcal T_g$ by the vector space $Q(X)$.
* **66. Torus Teichmüller space.** Marked complex tori are
  $\mathbb C/(\mathbb Z+\tau\mathbb Z)$, $\tau\in\mathbb H$.
  Their Teichmüller metric is half the curvature-$-1$ Poincaré metric,
  and changing the marking gives the $PSL(2,\mathbb Z)$ action.

## Moduli, mapping classes, and hyperbolic geometry

The **mapping class group** is
$\operatorname{Mod}_g=\pi_0(\operatorname{Homeo}^+(S_g))$;
the moduli space is $\mathcal M_g=\mathcal T_g/\operatorname{Mod}_g$.
For the hyperbolic metric $\rho^2|dz|^2$, the Weil–Petersson
cotangent pairing is $\langle q,p\rangle_{WP}
=\int q\bar p\,\rho^{-2}dx\,dy$.

* **67. Mapping-class action.** The mapping class group acts
  properly discontinuously by biholomorphisms and Teichmüller isometries.
  Stabilizers are finite conformal automorphism groups; the quotient
  is a complex orbifold of dimension $3g-3$, allowing its finite
  ineffective kernel in small genus.
* **68. Hurwitz automorphism bound.** For $g\geq2$,
  $|\operatorname{Aut}(X)|\leq84(g-1)$.
  The proof uses the ramified quotient and hyperbolic orbifold area.
* **69. Nielsen realization.** Every finite subgroup of
  $\operatorname{Mod}_g$ fixes a point of $\mathcal T_g$ and is
  realized by conformal automorphisms of a suitable surface.
* **70. Nielsen–Thurston classification.** Every mapping class is
  periodic, reducible, or pseudo-Anosov: an infinite-order irreducible
  class preserves a pair of transverse measured foliations, scaling
  one by $\lambda>1$ and the other by $\lambda^{-1}$.
* **71. Pseudo-Anosov translation.** A pseudo-Anosov class has an
  invariant Teichmüller geodesic and translation length $\log\lambda$,
  where $\lambda$ is its stretch factor.
* **72. Mumford compactness.** For each $\varepsilon>0$, the locus
  in $\mathcal M_g$ with hyperbolic systole at least $\varepsilon$
  is compact. Noncompactness of moduli is therefore detected by short geodesics.
* **73. Collar lemma.** A simple closed geodesic of length $\ell$
  has an embedded collar of half-width
  $\operatorname{arsinh}(1/\sinh(\ell/2))$.
  The standard collars of disjoint simple closed geodesics are disjoint.
* **74. Weil–Petersson geometry.** The dual of the displayed pairing
  gives a Kähler metric with negative sectional curvature. It is
  incomplete; pinching essential curves produces finite-distance
  degenerations. Mapping classes act by its isometries.
* **75. Simultaneous uniformization.** Given two marked genus-$g$
  surfaces with opposite orientations, a quasifuchsian group has two
  invariant simply connected components of discontinuity whose
  quotients realize them. The marked group is unique up to Möbius conjugacy.
* **76. Hyperbolic pants rigidity.** A hyperbolic pair of pants with
  geodesic boundary is determined up to isometry by its three boundary
  lengths. Gluing these pieces with twist parameters reconstructs
  the Fenchel–Nielsen coordinates and explains the analytic degeneration
  when a length tends to zero.

## Reference guide

Forster, Farkas–Kra, Miranda, Jost, Narasimhan, Gunning, Donaldson,
and Napier–Ramachandran share the compact-surface, divisor, period,
and uniformization core. The open-surface statements connect their
cohomological and analytic constructions. Ahlfors, Lehto–Virtanen,
Astala–Iwaniec–Martin, and the quasiconformal chapters of Branner–Fagella
supply the measurable-structure theory; Hencl–Koskela explains which
conclusions need stronger distortion assumptions. Imayoshi–Taniguchi,
Hubbard, Gardiner–Lakic, Jost, and the Teichmüller handbook organize
the deformation theory. Farb–Margalit supplies its topological companion,
and Buser, Marden, Kapovich, and Wolpert connect it with hyperbolic
and Weil–Petersson geometry. Three-dimensional uniformization is represented
only by the simultaneous-uniformization bridge.

Local full-text sources consulted:

* [Farkas–Kra, *Riemann Surfaces*](References/FarkasKra1992RiemannSurfaces-SpringerGTM71.pdf).
* [Jost, *Compact Riemann Surfaces*, third edition](References/Jost2006CompactRiemannSurfacesIntroductionContemporaryMathematics3rdEd-SpringerUTX.pdf).
* [Napier–Ramachandran, *An Introduction to Riemann Surfaces*](References/NapierRamachandran2012IntroductionRiemannSurfaces-BirkhaeuserCOR.pdf).
* [Branner–Fagella, *Quasiconformal Surgery in Holomorphic Dynamics*](References/BrannerFagella2014QuasiconformalSurgeryHolomorphicDynamics-Cambridge.StudAM141.pdf), principally its general quasiconformal chapters.
* [Hencl–Koskela, *Lectures on Mappings of Finite Distortion*](References/HenclKoskela2014MappingsFiniteDistortion-Springer.LNM2096.pdf).
* [Kapovich, *Hyperbolic Manifolds and Discrete Groups*](References/Kapovich2010HyperbolicManifoldsDiscreteGroups-BirkhaeuserMBC.pdf), principally its surface and Teichmüller chapters.
