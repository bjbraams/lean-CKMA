# Synopsis: Several complex variables, complex manifolds, pluripotential theory, and CR analysis

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects recurring core material from Section 45 of
[CKMA-bib.md](CKMA-bib.md).
It covers local analytic geometry, domains of holomorphy, Stein theory,
$\bar\partial$, positive currents and Monge–Ampère equations, complex
geometry, invariant metrics, and CR boundaries. Each of these has its own
graduate literature; the selection records their common working theorems
and principal connections rather than the contents of every specialist book.

Domains are connected open subsets of $\mathbb C^n$. A function is
**plurisubharmonic** (psh) if it is upper semicontinuous and its restriction
to every complex line is subharmonic or identically $-\infty$; exclude
the identically $-\infty$ function unless expressly allowed. For $C^2$
functions this means that the complex Hessian $(u_{j\bar k})$ is
positive semidefinite. Use
$d^c=\frac{i}{2\pi}(\bar\partial-\partial)$, so
$dd^c=\frac{i}{\pi}\partial\bar\partial$.

## Local holomorphic functions and analytic sets

* **1. Hartogs separate analyticity.** A function separately
  holomorphic in each coordinate on an open subset of $\mathbb C^n$
  is jointly holomorphic; no preliminary continuity hypothesis is needed.
* **2. Polydisk Cauchy formula.** Iterated one-variable Cauchy
  formulas give convergent multivariable Taylor series, derivative
  estimates, and normal convergence on smaller polydisks.
* **3. Identity and maximum principles.** A holomorphic function
  vanishing on a nonempty open set vanishes on the domain. A local
  maximum of its modulus forces constancy. A nonconstant scalar-valued
  holomorphic function is an open map.
* **4. Holomorphic rank theorem.** A holomorphic map of constant
  rank has local holomorphic coordinates in which it is a coordinate
  projection followed by inclusion. Invertible derivative gives a
  local biholomorphism; the implicit-function theorem is the corresponding
  local description of a regular zero set.
* **5. Hartogs extension.** If $n\geq2$, $K\Subset\Omega$, and
  $\Omega\setminus K$ is connected, every holomorphic function on
  $\Omega\setminus K$ extends uniquely to $\Omega$.
* **6. Riemann extension across analytic sets.** A holomorphic
  function off an analytic subset extends across it if locally bounded
  there. Across analytic subsets of complex codimension at least two,
  holomorphic functions extend without a boundedness assumption.
* **7. Weierstrass preparation.** If a germ $f(z',z_n)$ has order
  $d$ in $z_n$ at the origin, then $f=uP$, uniquely, where $u$
  is a holomorphic unit and $P$ is monic of degree $d$ in $z_n$
  with holomorphic coefficients vanishing at $z'=0$.
* **8. Weierstrass division.** For such a distinguished polynomial
  $P$, every holomorphic germ $g$ has a unique decomposition
  $g=qP+r$, where $r$ is polynomial in $z_n$ of degree less than $d$.
* **9. Local analytic algebra.** The convergent power-series ring
  $\mathbb C\{z_1,\ldots,z_n\}$ is Noetherian, regular local,
  and a unique factorization domain. Analytic germs therefore have
  finite local defining systems and finite irreducible decompositions.
* **10. Regular and singular loci.** A reduced analytic set has a
  dense regular locus. Its singular locus is analytic and has strictly
  smaller dimension on every positive-dimensional irreducible component.
* **11. Analytic Nullstellensatz.** For an ideal of convergent
  power-series germs, the germs vanishing on its zero germ form its
  radical. Reduced analytic germs correspond to radical ideals.
* **12. Remmert proper mapping theorem.** The image of an analytic
  set under a proper holomorphic map is analytic.
* **13. Normalization.** Every reduced complex analytic space has
  a normalization: a finite holomorphic map from a normal space,
  biholomorphic over its normal locus, uniquely determined by this property.

## Pseudoconvexity, Stein spaces, and approximation

A domain is **pseudoconvex** if it admits a continuous psh exhaustion.
For a $C^2$ defining function $\rho$ with domain $\rho<0$, its
**Levi form** is $\sum\rho_{j\bar k}v_j\bar v_k$ restricted to
$\sum\rho_jv_j=0$. Strict pseudoconvexity means positivity there.
A complex manifold is **Stein** if it is holomorphically convex and
global holomorphic functions separate points and furnish local coordinates.
The holomorphic hull of compact $K\subset X$ is
$\widehat K_X=\{x:|f(x)|\leq\sup_K|f|\text{ for all }f\in\mathcal O(X)\}$.

* **14. Levi criterion.** For a domain with $C^2$ boundary,
  pseudoconvexity is equivalent to nonnegativity of the boundary Levi form.
  Strict positivity yields local strictly psh defining functions.
* **15. Levi problem.** For domains in $\mathbb C^n$, the following
  are equivalent: pseudoconvexity, being a domain of holomorphy,
  holomorphic convexity, and being Stein.
* **16. Strictly psh exhaustions.** A complex manifold is Stein
  exactly when it admits a smooth strictly psh exhaustion.
  A compact positive-dimensional analytic subset cannot lie in a Stein manifold.
* **17. Reinhardt domains.** A Reinhardt domain is pseudoconvex
  exactly when its logarithmic image away from coordinate hyperplanes
  is convex and, for each hyperplane $\{z_j=0\}$ that it meets,
  replacing $z_j$ by $\lambda z_j$, $|\lambda|\leq1$, preserves
  membership in the domain. A complete Reinhardt domain is pseudoconvex
  exactly when it is logarithmically convex.
* **18. Power-series domains.** Domains of absolute convergence of
  multivariable power series are complete logarithmically convex
  Reinhardt domains. Conversely every such domain is a domain of
  convergence of a suitable power series.
* **19. Envelopes of holomorphy.** A domain in $\mathbb C^n$ has
  a universal simultaneous extension space for its holomorphic functions.
  The envelope is Stein as a Riemann domain, but need not be a
  single-sheeted domain in $\mathbb C^n$.
* **20. Oka–Weil approximation.** If $K$ is holomorphically convex
  in a Stein space, functions holomorphic near $K$ are uniformly
  approximable on $K$ by global holomorphic functions.
  For polynomially convex $K\subset\mathbb C^n$, polynomials suffice.
* **21. Oka coherence theorem.** The structure sheaf and ideal
  sheaves of analytic subsets are coherent. Kernels of morphisms
  between coherent analytic sheaves are coherent.
* **22. Cartan's theorem A.** A coherent analytic sheaf on a Stein
  space is generated at each stalk by its global sections.
* **23. Cartan's theorem B.** On a Stein space, coherent analytic
  sheaves satisfy $H^q(X,\mathcal F)=0$ for every $q\geq1$.
* **24. Additive Cousin problem.** Every additive holomorphic Cousin
  cocycle on a Stein space splits. In particular compatible meromorphic
  principal-part data have a global meromorphic realization.
* **25. Multiplicative Cousin obstruction.** On a Stein manifold,
  a divisor is principal exactly when its associated topological line
  bundle is trivial. The exponential sequence identifies the obstruction
  with its class in $H^2(X,\mathbb Z)$.
* **26. Extension from subvarieties.** Every holomorphic function on
  a closed analytic subspace of a Stein space extends holomorphically
  to the ambient space, by coherence and theorem B.
* **27. Oka–Grauert principle.** Holomorphic vector bundles on a
  Stein manifold are classified by their underlying topological complex
  bundles. Topological equivalence of holomorphic bundles implies
  holomorphic equivalence.
* **28. Stein embedding.** Every Stein manifold of complex dimension
  $n$ admits a proper holomorphic embedding into $\mathbb C^{2n+1}$.
  For $n\geq2$ the optimal dimension is $\lfloor3n/2\rfloor+1$
  (Eliashberg–Gromov, Schürmann); open Riemann surfaces embed properly in $\mathbb C^3$.
* **29. Oka mapping principle.** If $Y$ is an Oka manifold and $X$
  is Stein, continuous maps $X\to Y$ deform to holomorphic maps,
  with parametric approximation and interpolation in the Oka formulation.
  Complex Lie groups and complex homogeneous manifolds are examples of $Y$.

## The d-bar equation and the Neumann problem

The **Dolbeault complex** uses
$\bar\partial:A^{p,q}\to A^{p,q+1}$, $\bar\partial^2=0$.
On a Hermitian domain put
$\Box_q=\bar\partial\bar\partial^*+\bar\partial^*\bar\partial$
with its Hilbert-complex boundary conditions. Its inverse on the orthogonal
complement of its kernel is the **$\bar\partial$-Neumann operator** $N_q$.

* **30. Local Dolbeault lemma.** Every smooth $\bar\partial$-closed
  $(p,q)$-form with $q\geq1$ is locally $\bar\partial$ of a
  smooth $(p,q-1)$-form.
* **31. Bochner–Martinelli representation.** A $C^1$ function on
  the closure of a bounded $C^1$ domain equals its boundary
  Bochner–Martinelli integral minus the interior integral of its
  $\bar\partial$. For holomorphic functions only the boundary term remains.
* **32. Koppelman homotopy.** The corresponding form-valued
  kernels give local homotopy formulas
  $f=\bar\partial Tf+T\bar\partial f$ in positive antiholomorphic
  degree, with boundary terms on bounded domains.
* **33. Hörmander weighted estimate.** On a pseudoconvex domain,
  for $C^2$ strictly psh $\phi$ and $\bar\partial$-closed $(0,1)$-form
  $g$, there is $\bar\partial u=g$ with
  $\int|u|^2e^{-\phi}\leq\int\langle(\phi_{j\bar k})^{-1}g,g\rangle e^{-\phi}$
  whenever the right side is finite.
* **34. Morrey–Kohn–Hörmander identity.** The weighted sum
  $\|\bar\partial u\|_\phi^2+\|\bar\partial_\phi^*u\|_\phi^2$
  decomposes into derivative terms, complex-Hessian terms, and a
  boundary Levi term. Pseudoconvexity makes the latter nonnegative
  in positive antiholomorphic degree.
* **35. Basic $L^2$ solvability.** On a bounded pseudoconvex domain,
  the $\bar\partial$ operators have closed range in $L^2$.
  For $1\leq q\leq n$, $N_q$ is bounded and
  $\bar\partial\bar\partial^*N_qg=g$ for closed $g$.
* **36. Canonical solution.** The least-norm solution of
  $\bar\partial u=g$ is $u=\bar\partial^*N_qg$; it is
  orthogonal to the kernel of $\bar\partial$.
* **37. Hilbert-complex decomposition.** On a bounded pseudoconvex
  domain, a positive-degree $L^2$ form splits orthogonally into
  $\bar\partial\bar\partial^*N_qu+
  \bar\partial^*\bar\partial N_qu$.
  The general closed-range decomposition also includes harmonic forms.
* **38. Bergman projection formula.** On functions,
  $P=I-\bar\partial^*N_1\bar\partial$, initially on the
  $\bar\partial$ domain and then by its bounded extension.
* **39. Strictly pseudoconvex subellipticity.** On a smooth bounded
  strictly pseudoconvex domain, the Neumann quadratic form controls
  the $H^{1/2}$ norm in degrees $q\geq1$. Canonical solutions
  gain half a Sobolev derivative, with the corresponding global estimates.
* **40. Finite type and subellipticity.** At a smooth pseudoconvex
  boundary point in $\mathbb C^n$, finite D'Angelo type is equivalent
  to a local positive-order subelliptic estimate for $(0,1)$-forms (Catlin).
* **41. Global regularity and Condition R.** If the Bergman projection of
  a smooth bounded domain preserves $C^\infty(\overline\Omega)$
  (Condition R), biholomorphisms onto another such domain extend smoothly
  to the closures (Bell–Ligocka). Condition R and global regularity of $N_q$
  hold for smooth bounded convex domains and under compactness of $N_q$
  (Boas–Straube, Kohn–Nirenberg), but fail on suitable smooth bounded
  pseudoconvex worm domains (Barrett, Christ).
* **42. Ohsawa–Takegoshi extension.** On a bounded pseudoconvex
  domain $\Omega\subset\mathbb C^n$, a holomorphic function on
  $\Omega\cap\{z_n=0\}$ with finite weighted $L^2$ norm extends
  to $F\in\mathcal O(\Omega)$ with
  $\int_\Omega|F|^2e^{-\phi}\leq C\int_{\Omega\cap\{z_n=0\}}|f|^2e^{-\phi}$
  for psh $\phi$. If $|z_n|<r$ on $\Omega$ one may take $C=\pi r^2$,
  which is optimal (Błocki, Guan–Zhou).
* **43. Skoda division.** Let $g=(g_1,\ldots,g_m)$ be holomorphic
  on a pseudoconvex domain, $q=\min(n,m-1)$, and $\alpha>1$.
  If $f$ is holomorphic and $\int|f|^2|g|^{-2(\alpha q+1)}e^{-\psi}<\infty$, with
  $\psi$ psh, then $f=\sum g_jh_j$ holomorphically and
  $\int\sum|h_j|^2|g|^{-2\alpha q}e^{-\psi}$ is at most
  $\alpha/(\alpha-1)$ times that integral.
* **44. Multiplier-ideal coherence.** For psh $\phi$, the germs
  $f$ with $|f|^2e^{-2\phi}$ locally integrable form a coherent
  ideal sheaf $\mathcal I(\phi)$.
* **45. Nadel vanishing.** If a line bundle on a compact Kähler
  manifold has a singular Hermitian metric with curvature bounded
  below by a positive Kähler form, then
  $H^q(X,K_X\otimes L\otimes\mathcal I(h))=0$ for $q\geq1$.

## Positive currents and pluripotential theory

A **positive current** acts nonnegatively on strongly positive test forms.
For locally bounded psh functions, the Bedford–Taylor products
$dd^cu_1\wedge\cdots\wedge dd^cu_k$ are defined recursively by
distributional differentiation of $u_1dd^cu_2\wedge\cdots$.
For a Kähler form $\omega$, $u$ is **$\omega$-psh** if
$\omega+dd^cu\geq0$.

* **46. Stability of psh functions.** Finite maxima, convex increasing
  compositions, and decreasing limits preserve plurisubharmonicity,
  unless a limit is identically $-\infty$. Locally bounded-above
  suprema become psh after upper-semicontinuous regularization.
* **47. Local regularization.** Convolution on smaller coordinate
  domains approximates a psh function decreasingly by smooth psh
  functions. A locally integrable distribution has a psh representative
  exactly when its $dd^c$ is positive.
* **48. Poincaré–Lelong formula.** For nonzero holomorphic $f$,
  $dd^c\log|f|=[\operatorname{div}f]$ as currents.
  For a Hermitian holomorphic line bundle this becomes the divisor
  current minus its first-Chern curvature form.
* **49. Siu analyticity.** For a positive closed current, the sets
  where its Lelong number is at least a fixed positive constant are
  analytic. For a positive closed $(1,1)$-current, its divisorial
  part has a unique decomposition into integration currents plus a
  residual positive current with no divisorial generic Lelong numbers.
* **50. Bedford–Taylor products.** Products of $dd^c$ of locally
  bounded psh functions are positive, closed, symmetric, and local.
  In top degree they define positive Monge–Ampère measures.
* **51. Monotone continuity.** Decreasing locally bounded psh
  approximations yield weak convergence of their Bedford–Taylor products.
  This supplies the definition independently of smooth approximating sequences.
* **52. Comparison principle.** If bounded psh $u,v$ on a bounded
  domain satisfy $\liminf_{z\to\partial\Omega}(u-v)\geq0$, then
  $\int_{\{u<v\}}(dd^cv)^n\leq\int_{\{u<v\}}(dd^cu)^n$.
* **53. Maximality.** A locally bounded psh function is maximal
  under compactly supported psh competitors exactly when
  $(dd^cu)^n=0$.
* **54. Chern–Levine–Nirenberg estimate.** On nested relatively
  compact coordinate sets, masses of mixed $dd^c$ products are
  bounded by a constant times the product of the local supremum
  norms of bounded psh potentials, with a fixed background positive form.
* **55. Monge–Ampère Dirichlet problem.** On a bounded smoothly
  strictly pseudoconvex domain, continuous boundary data and continuous
  nonnegative volume density have a unique continuous psh solution
  of $(dd^cu)^n=f\,dV$ with those boundary values.
* **56. Capacity and $L^p$ densities.** The relative capacity
  $\sup_{-1\leq v\leq0}\int_E(dd^cv)^n$ controls exceptional
  sets and psh convergence. On a compact Kähler manifold, a
  nonnegative $L^p$ density, $p>1$, of the correct total mass
  has a unique bounded $\omega$-psh Monge–Ampère solution normalized
  by $\sup_Xu=0$ (Kołodziej).
* **57. Pluripolar sets.** A set $E\subset\mathbb C^n$ is
  **locally pluripolar** if near each point it lies in $\{u=-\infty\}$
  for a local psh $u\not\equiv-\infty$. Such sets are globally pluripolar:
  $E\subset\{u=-\infty\}$ for some psh $u$ on $\mathbb C^n$ (Josefson).
  In a bounded hyperconvex domain, $E$ is pluripolar exactly when its
  outer relative capacity vanishes, and negligible sets
  $\{\sup_\alpha u_\alpha<(\sup_\alpha u_\alpha)^*\}$ are pluripolar
  (Bedford–Taylor).
* **58. Calabi–Yau theorem.** On a compact Kähler manifold,
  each smooth positive volume form of mass $\int\omega^n$ is
  $(\omega+dd^cu)^n$ for a unique smooth $u$ modulo constants,
  with $\omega+dd^cu>0$. Thus a prescribed Ricci form in
  $2\pi c_1(X)$ is realized uniquely in a fixed Kähler class. If
  $c_1(X)<0$, there is a unique Kähler–Einstein metric with
  $\operatorname{Ric}=-\omega$ (Aubin, Yau); if $c_1(X)=0$, each Kähler
  class contains a unique Ricci-flat metric.

## Complex manifolds and Kähler geometry

* **59. Newlander–Nirenberg theorem.** A smooth almost complex
  structure comes from holomorphic coordinates exactly when its
  Nijenhuis tensor vanishes, equivalently its $(0,1)$ vector fields
  are involutive.
* **60. Dolbeault theorem.** For a holomorphic vector bundle $E$,
  $H^q(X,\Omega^p\otimes E)$ is the cohomology of its smooth
  $\bar\partial$ complex in bidegree $(p,q)$.
* **61. Hermitian Hodge theorem.** On a compact Hermitian manifold,
  every Dolbeault class has a unique $\bar\partial$-harmonic
  representative, and the cohomology groups are finite-dimensional.
* **62. Serre duality.** On a compact complex $n$-manifold,
  $H^q(X,E)$ is dual to $H^{n-q}(X,K_X\otimes E^*)$ by integration.
* **63. Kähler identities.** For a Kähler metric,
  $\Delta_d=2\Delta_\partial=2\Delta_{\bar\partial}$, with the
  associated commutator identities for wedge multiplication by
  $\omega$ and its adjoint.
* **64. Kähler Hodge decomposition.**
  $H^k(X,\mathbb C)=\bigoplus_{p+q=k}H^{p,q}(X)$ on compact
  Kähler manifolds, with $h^{p,q}=h^{q,p}$ and
  $h^{p,q}=h^{n-p,n-q}$.
* **65. The $\partial\bar\partial$ lemma.** A pure-type form on
  a compact Kähler manifold that is $d$-closed and $d$-exact is
  $\partial\bar\partial$-exact. Equivalent versions use
  $\partial$- or $\bar\partial$-exactness.
* **66. Hard Lefschetz theorem.** Wedge multiplication by
  $[\omega]^{n-k}$ is an isomorphism
  $H^k(X,\mathbb C)\to H^{2n-k}(X,\mathbb C)$ for $k\leq n$.
* **67. Kodaira–Nakano vanishing.** If $L$ is positive on compact
  Kähler $X$, then $H^q(X,\Omega^p\otimes L)=0$ for
  $p+q>n$. In particular $H^q(X,K_X\otimes L)=0$ for $q>0$.
* **68. Kodaira embedding theorem.** A compact complex manifold
  with a positive holomorphic line bundle is projective; sufficiently
  high tensor powers give embeddings. Equivalently, a compact Kähler
  manifold with an integral Kähler class is projective. The embedding is
  given by a base-point-free space of sections that separates points and
  tangent vectors.
* **69. Chow's theorem and GAGA.** Closed analytic subsets of
  $\mathbb P^N$ are algebraic. On a projective variety, analytic and
  algebraic coherent sheaves correspond, with the same cohomology (Serre);
  meromorphic functions on it are rational.

## Invariant metrics and bounded-domain rigidity

The **Carathéodory distance** is the supremum of disk distances under
holomorphic maps to $\mathbb D$; the **Kobayashi pseudodistance** is
the infimum of sums of disk distances along holomorphic disk chains.
A domain is **circular about zero** when it is invariant under
$z\mapsto e^{it}z$.

* **70. Holomorphic contraction.** Both pseudodistances contract
  under holomorphic maps, and $c_X\leq k_X$. Their infinitesimal
  versions have the same functorial property.
* **71. Ball Schwarz lemma.** Holomorphic ball maps fixing zero
  contract Euclidean norm. Ball automorphisms transfer this to the
  invariant distance, with
  $k_{\mathbb B^n}(0,z)=\operatorname{arctanh}\|z\|$ in the
  curvature-$-4$ disk normalization.
* **72. Lempert theorem.** On a bounded convex domain, Carathéodory
  and Kobayashi distances agree and are realized by complex geodesics
  through any two points. Such a geodesic has a holomorphic left inverse.
* **73. Brody criterion.** A compact complex manifold is Kobayashi
  hyperbolic exactly when every entire map $\mathbb C\to X$ is constant.
  Compactness is essential for this equivalence.
* **74. Bergman transformation.** The Bergman kernel transforms
  by the holomorphic Jacobian determinant under biholomorphisms.
  Where nondegenerate, $\partial\bar\partial\log K(z,z)$
  defines a biholomorphically invariant Hermitian metric. For the ball,
  $K(z,w)=n!\,\pi^{-n}(1-\langle z,w\rangle)^{-n-1}$.
* **75. Cartan uniqueness.** An automorphism of a bounded domain
  fixing a point with identity derivative is the identity. A
  biholomorphism between bounded circular domains containing zero that
  maps zero to zero is linear. Hence (Poincaré) for $n\geq2$ the ball and
  the polydisk are not biholomorphic, since their isotropy groups at zero,
  $U(n)$ and the torus extended by coordinate permutations, are not conjugate.

## CR geometry and boundary analysis

For a real hypersurface $M\subset\mathbb C^n$, its **CR bundle**
is $T^{0,1}M=\mathbb CTM\cap T^{0,1}\mathbb C^n$.
A smooth function is **CR** if every section of this bundle annihilates it.
The induced tangential complex is denoted $\bar\partial_b$.

* **76. Tangential integrability.** The bundle $T^{0,1}M$ is
  involutive and has zero intersection with its conjugate.
  This makes $\bar\partial_b^2=0$ on its intrinsic quotient complex;
  restrictions of holomorphic functions are CR.
* **77. Levi form as a commutator.** The transverse part of
  $[L,\bar L]$ for complex tangent fields recovers the boundary
  Levi form, up to the chosen normal and sign. Its rank and signature
  are CR invariants, with sign reversed by reversing the normal.
* **78. Hartogs–Bochner boundary extension.** For $n\geq2$, a
  smooth CR function on the connected smooth boundary of a bounded
  domain in $\mathbb C^n$ extends holomorphically into the domain,
  smoothly up to the boundary.
* **79. One-sided Lewy extension.** Near a strictly pseudoconvex
  hypersurface point in $\mathbb C^n$, $n\geq2$, smooth CR
  functions extend holomorphically to the pseudoconvex side locally.
* **80. Finite-type interpretation.** On a smooth pseudoconvex
  hypersurface in $\mathbb C^2$, finite order of contact with
  complex curves is equivalent to finite commutator type of complex
  tangential fields. It is the geometric source of positive subelliptic gain.
* **81. Fefferman boundary regularity.** A biholomorphism between
  bounded smoothly strictly pseudoconvex domains extends to a smooth
  diffeomorphism of their closures and induces a boundary CR equivalence.
* **82. Alexander rigidity.** For $n\geq2$, a proper holomorphic
  self-map of the unit ball in $\mathbb C^n$ is an automorphism.
  The disk's higher-degree proper Blaschke maps have no such analogue.

## Reference guide

Fritzsche–Grauert, Hörmander, Gunning–Rossi, Scheidemann, Shabat,
and the introductory notes share the local, pseudoconvex, and Stein core.
Range and Laurent-Thiébaut develop integral representations; Hörmander,
Ohsawa, Chen–Shaw, Folland–Kohn, Straube, and Haslinger connect them
with $L^2$ estimates and boundary regularity. Demailly, Klimek,
Guedj–Zeriahi, and the Monge–Ampère lecture volumes organize currents
and pluripotential theory. Wells and Huybrechts supply the complex-manifold
and Kähler framework; Forstnerič develops the Oka continuation. The CR
and invariant-metric references give the corresponding geometric theories.
Specialized stability questions and individual canonical-metric programmes
are not included as separate inventories.

Local full-text sources consulted:

* [Fritzsche–Grauert, *From Holomorphic Functions to Complex Manifolds*](References/FritzscheGrauert2002HolomorphicFunctionsComplexManifolds-SpringerGTM213.pdf).
* [Laurent-Thiébaut, *Holomorphic Function Theory in Several Variables*](References/LaurentThiebaut2011HolomorphicFunctionTheorySeveralVariables-SpringerUTX.pdf).
* [Ohsawa, *L² Approaches in Several Complex Variables*, second edition](References/Ohsawa2018L2ApproachesSeveralComplexVariables2ndEd-Springer.SMM.pdf).
* [Folland–Kohn, *The Neumann Problem for the Cauchy–Riemann Complex*](References/FollandKohn1973NeumannProblemCauchyRiemannComplex-PrincetonAnnalsMathStud75.pdf).
* [Haslinger, *The d-bar-Neumann Problem and Schrödinger Operators*, first edition](References/Haslinger2014DBarNeumannProblemSchrödingerOperators-DeGruyterExpMath59.pdf).
* [Guedj (ed.), *Complex Monge–Ampère Equations and Geodesics in the Space of Kähler Metrics*](References/GuedjEds2012ComplexMongeAmpereEquationsGeodesicsSpaceKahlerMetrics-Springer.LNM2038.pdf).
* [Huybrechts, *Complex Geometry*](References/Huybrechts2005ComplexGeometryIntroduction-SpringerUTX.pdf).
* [Wells, *Differential Analysis on Complex Manifolds*](References/WellsJr2008DifferentialAnalysisComplexManifolds3rdEd-SpringerGTM.pdf).
* [Forstnerič, *Stein Manifolds and Holomorphic Mappings*, second edition](References/Forstnerič2017SteinManifoldsHolomorphicMappingsHomotopyPrincipleComplexAnalysis2ndEd-SpringerErgebMath3.pdf).

The local Krantz course is largely image-based and was not used as
searchable full text; the accessible texts above supply the source comparison.
