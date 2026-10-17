# Synopsis: Complex dynamics

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects recurring material from Section 46 of
[CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md).
Its main subject is iteration of rational and polynomial maps, together
with the local, quasiconformal, ergodic, and potential-theoretic methods
that recur in the listed books. The final sections give foundational
extensions to transcendental and higher-dimensional holomorphic dynamics.
Arithmetic and non-Archimedean dynamics are separate substantial theories
and are not incorporated wholesale.

Unless specified otherwise, $f:\widehat{\mathbb C}\to\widehat{\mathbb C}$
is rational of degree $d\geq2$; $f^n$ denotes iteration. The **Fatou set**
$F(f)$ is the open set where $\{f^n\}$ is normal in the spherical metric;
the **Julia set** is its complement $J(f)$. The **postcritical set** is
$P(f)=\overline{\bigcup_{n\geq1}f^n(\operatorname{Crit}f)}$.
The multiplier of a period-$p$ point is $(f^p)'$ in a local coordinate.

## Julia sets and global iteration

* **1. Complete invariance.** Both Fatou and Julia sets are completely
  invariant: their forward images and full inverse images equal themselves.
* **2. Nontriviality and perfection.** $J(f)$ is nonempty, compact,
  infinite, and perfect. It has empty interior unless it is the whole sphere.
* **3. Exceptional points.** There are at most two points with finite
  backward orbit. The exceptional set is completely invariant and
  lies in the Fatou set.
* **4. Backward-orbit density.** The closure of the backward orbit
  of any nonexceptional point contains $J(f)$; if the point belongs
  to $J(f)$, that closure is exactly $J(f)$.
* **5. Blowing-up property.** If an open set meets $J(f)$, the
  union of its forward images covers the sphere apart from at most
  the exceptional points. This is the dynamical consequence of Montel's theorem.
* **6. Repelling cycles are dense.** Repelling periodic points lie
  in $J(f)$ and are dense there. Attracting periodic points lie in $F(f)$.
* **7. Iteration does not change Julia sets.** For every $k\geq1$,
  $F(f^k)=F(f)$ and $J(f^k)=J(f)$.
* **8. Periodic-point count.** The equation $f^n(z)=z$ has
  $d^n+1$ solutions counted with intersection multiplicity on the sphere.
  Multiple solutions occur exactly when the corresponding multiplier is one.
* **9. Holomorphic fixed-point formula.** If every fixed point is
  simple, then $\sum_{f(a)=a}(1-f'(a))^{-1}=1$, using local
  coordinates at infinity. General versions use residues when multiplier one occurs.
  The formula is also treated in [Milnor's introductory lectures](https://arxiv.org/pdf/math/9201272).

## Local normal forms and small divisors

* **10. Koenigs linearization.** A germ $f(z)=\lambda z+O(z^2)$
  with $0<|\lambda|\ne1$ is locally conjugate to $z\mapsto\lambda z$.
  The conjugating germ normalized to have derivative one is unique.
* **11. Böttcher's theorem.** A superattracting germ
  $f(z)=az^k+O(z^{k+1})$, $k\geq2$, is locally conjugate to
  $z\mapsto z^k$. The coordinate is unique up to a $(k-1)$st root of unity.
* **12. Leau–Fatou flower theorem.** For
  $f(z)=z+az^{k+1}+O(z^{k+2})$, $a\ne0$, there are $k$
  attracting and $k$ repelling petals. Their union with the fixed point
  contains a neighborhood of it, and their directions alternate.
* **13. Fatou coordinates.** On an attracting or repelling petal,
  a holomorphic coordinate conjugates iteration to translation
  $w\mapsto w+1$. Its leading asymptotic is $-1/(kaz^k)$.
* **14. Siegel's Diophantine theorem.** If $\lambda=e^{2\pi i\theta}$
  and $|\lambda^n-1|\geq Cn^{-\tau}$ for all $n\geq1$,
  every germ with multiplier $\lambda$ is holomorphically linearizable.
* **15. Brjuno–Yoccoz theorem.** For irrational $\theta$ with
  continued-fraction denominators $q_n$, convergence of
  $\sum_n\log q_{n+1}/q_n$ implies linearizability of every such
  germ. It is necessary for the quadratic germ
  $e^{2\pi i\theta}z+z^2$ to be linearizable.
* **16. Cremer behavior.** There exist irrational multipliers and
  holomorphic germs that are not linearizable. In a rational map,
  a non-linearizable irrationally indifferent periodic point belongs to the Julia set.

## Fatou components and hyperbolicity

* **17. Critical points in attracting basins.** Every cycle of
  immediate attracting basins contains a critical point. Thus a
  degree-$d$ rational map has at most $2d-2$ attracting cycles.
* **18. Critical points in parabolic basins.** Every cycle of
  immediate parabolic basins contains a critical point whose orbit
  converges to the parabolic cycle.
* **19. Periodic Fatou classification.** A periodic Fatou component
  is an attracting basin, a parabolic basin, a Siegel disk, or a
  Herman ring. On the last two, the first return map is conformally
  conjugate to an irrational rotation of a disk or annulus.
* **20. Sullivan's no-wandering-domains theorem.** Every Fatou
  component of a rational map is eventually periodic. Consequently
  the preceding list describes all components after finitely many iterates.
* **21. Fatou–Shishikura inequality.** The number of nonrepelling
  periodic point cycles of a rational map is at most $2d-2$.
  This includes irrationally indifferent cycles, not just attracting ones.
* **22. Polynomial Fatou domains.** A polynomial has no Herman
  rings. Its bounded Fatou components are simply connected, while
  the basin of infinity is governed by its external Green function.
* **23. Hyperbolicity criteria.** The following are equivalent:
  $P(f)\cap J(f)=\varnothing$; every critical orbit tends to an
  attracting cycle; and uniform expansion of some iterate on $J(f)$
  in a smooth conformal metric near that set.
* **24. Expanding geometry.** A hyperbolic rational map has uniform
  contraction of inverse branches near its Julia set, bounded distortion,
  and a finite Markov description. These supply its conformal-repeller structure.
* **25. Structural stability.** Hyperbolicity is open in parameter
  space. Nearby hyperbolic Julia dynamics are conjugate by a
  holomorphic motion, extending to a quasiconformal sphere motion.
* **26. Dimension of hyperbolic Julia sets.** A hyperbolic rational
  Julia set has Hausdorff dimension strictly below two and hence area zero.
* **27. Subhyperbolic local connectivity.** A polynomial with connected
  Julia set, no parabolic cycles, and every Julia critical point
  preperiodic has a locally connected Julia set if all remaining
  critical points tend to attracting cycles. Expansion uses an orbifold metric.

## Polynomial Green functions, rays, and equilibrium measures

For a polynomial $p$ of degree $d\geq2$, its **filled Julia set** is
$K(p)=\{z:(p^n(z))\text{ is bounded}\}$ and its escape-rate function is
$G_p(z)=\lim_{n\to\infty}d^{-n}\log^+|p^n(z)|$.
Use $dd^c=\frac{i}{\pi}\partial\bar\partial$.

* **28. Filled-set structure.** $K(p)$ is nonempty, compact, and
  full: its complement has no bounded component. Its boundary is
  $J(p)$, and its complement is exactly the basin of infinity.
* **29. Connectedness criterion.** $K(p)$, equivalently $J(p)$,
  is connected exactly when every finite critical point has bounded orbit.
* **30. Escape of all critical points.** If every finite critical
  point escapes to infinity, $J(p)$ is a Cantor expanding repeller.
  This sufficient condition is not used as a characterization of all Cantor Julia sets.
* **31. Escape-rate potential.** The limit defining $G_p$ exists
  locally uniformly, is continuous and subharmonic, vanishes exactly
  on $K(p)$, is harmonic outside it, and satisfies $G_p\circ p=dG_p$.
* **32. External Böttcher coordinate.** Near infinity,
  $\phi(p(z))=\phi(z)^d$ and $G_p=\log|\phi|$.
  If $K(p)$ is connected, $\phi$ extends conformally over its
  entire complement onto $\{|w|>1\}$.
* **33. Equilibrium measure.** $\mu_p=dd^cG_p$ is a probability
  measure supported on $J(p)$, equal to logarithmic equilibrium
  measure of $K(p)$ and harmonic measure from infinity.
  It satisfies $p_*\mu_p=\mu_p$ and $p^*\mu_p=d\mu_p$.
* **34. Preimage equidistribution.** For a rational map, there is
  an invariant probability measure $\mu_f$ on $J(f)$ such that
  $d^{-n}(f^n)^*\delta_a\rightharpoonup\mu_f$ for every
  nonexceptional $a$, counting inverse images with multiplicity.
* **35. Maximal entropy.** $h_{\rm top}(f)=\log d$ and $\mu_f$
  is the unique invariant probability measure of entropy $\log d$.
  It is mixing and has no atoms.
* **36. Periodic-point equidistribution.** The normalized counting
  measures on the fixed points of $f^n$, with multiplicity and total
  normalization $d^n+1$, converge weakly to $\mu_f$.
  Repelling periodic points give the same limiting measure.
* **37. External-ray dynamics.** When $K(p)$ is connected, curves
  $\phi^{-1}(re^{2\pi i\theta})$, $r>1$, are external rays.
  The map $p$ sends the ray of angle $\theta$ to that of angle $d\theta$.
* **38. Rational-ray landing.** Every periodic external ray of a
  connected polynomial Julia set lands at a repelling or parabolic
  periodic point. Every such periodic point is the landing point of
  at least one periodic ray. Preperiodic rays satisfy the corresponding iterated statement.
* **39. Local connectivity and semiconjugacy.** If $J(p)$ is
  connected and locally connected, the inverse external coordinate
  extends continuously to the circle, giving a surjective semiconjugacy
  from $\theta\mapsto d\theta$ onto $p|_{J(p)}$.

## Parameter spaces, deformation, and renormalization

For $p_c(z)=z^2+c$, the **Mandelbrot set** is
$\mathcal M=\{c:(p_c^n(0))\text{ is bounded}\}$.
A **polynomial-like map** is a proper holomorphic map $U\to V$ of
degree at least two, with $U\Subset V$ topological disks; its filled set
consists of points whose iterates remain in $U$.
A **holomorphic motion** is injective at each parameter, holomorphic
in the parameter at each moving point, and the identity at a base parameter.
**Julia stability** means local existence of an equivariant holomorphic
motion of the Julia set.

* **40. Mandelbrot connectedness.** $\mathcal M$ is compact and
  connected, and $c\in\mathcal M$ exactly when $J(p_c)$ is connected.
  An escape bound gives $\mathcal M\subset\{|c|\leq2\}$.
* **41. Parameter external map.** The function
  $\Phi(c)=\phi_c(c)$ conformally maps
  $\mathbb C\setminus\mathcal M$ onto $\{|w|>1\}$ with
  $\Phi(c)/c\to1$ at infinity. Parameter rays are its radial inverse images.
* **42. Hyperbolic components.** In the quadratic family, a
  hyperbolic component is simply connected and its attracting-cycle
  multiplier is a conformal coordinate onto $\mathbb D$.
  Its center is the unique parameter with superattracting cycle.
* **43. Holomorphic-motion extension.** A holomorphic motion of
  a subset of the sphere extends to its closure and, over a disk
  parameter space, to a motion of the whole sphere with quasiconformal slices.
* **44. Mañé–Sad–Sullivan stability.** Julia-stable parameters form
  an open dense set in the full space of rational maps of fixed degree.
  Stability is characterized by normality of the locally marked critical
  orbits and yields holomorphic motion of the Julia set.
* **45. Hybrid straightening.** Every polynomial-like map is
  quasiconformally conjugate near its filled set to a polynomial of
  the same degree, with the conjugacy conformal almost everywhere
  on the filled set. If that set is connected, the polynomial is
  unique up to affine conjugacy.
* **46. Renormalization.** A polynomial-like restriction of an
  iterate is a renormalization, and straightening assigns it an
  ordinary polynomial model. Degree, critical points, and connectedness
  of the small filled set control the applicability and uniqueness of the model.
* **47. Invariant-structure surgery.** A quasiregular sphere map
  preserving a measurable conformal structure with bounded distortion
  is conjugate to a rational map by integrating that structure.
  This is the basic straightening mechanism of quasiconformal surgery.
* **48. Thurston characterization.** A postcritically finite
  orientation-preserving branched sphere covering with hyperbolic
  orbifold is equivalent to a rational map exactly when every stable
  essential nonperipheral multicurve has Thurston matrix of spectral
  radius less than one. Matrix entries sum reciprocal covering degrees
  over isotopic inverse curves. The rational map is unique up to Möbius conjugacy.

## Conformal repellers and thermodynamic formalism

Let $f:X\to X$ be a topologically mixing expanding conformal repeller.
For a Hölder potential $\varphi$, write $P(\varphi)$ for pressure and
$\mathcal L_\varphi u(x)=\sum_{f(y)=x}e^{\varphi(y)}u(y)$.

* **49. Variational principle.**
  $P(\varphi)=\sup_\nu(h_\nu(f)+\int\varphi\,d\nu)$ over
  invariant probabilities. An attaining measure is an equilibrium state.
* **50. Ruelle–Perron–Frobenius theorem.** On Hölder functions,
  $\mathcal L_\varphi$ has a simple positive leading eigenvalue
  $e^{P(\varphi)}$, a positive eigenfunction, an eigenmeasure, and
  a spectral gap after normalization.
* **51. Gibbs states.** Hölder potentials have unique equilibrium
  states with the Gibbs cylinder estimates. They are mixing, with
  exponential correlation decay for Hölder observables.
* **52. Bowen dimension formula.** The Hausdorff dimension of
  $X$ is the unique zero $s$ of $P(-s\log|f'|)$.
  In particular this computes dimensions of hyperbolic rational Julia sets.
* **53. Dimension of an ergodic measure.** For an ergodic invariant
  probability on a conformal expanding repeller,
  $\dim_H\nu=h_\nu(f)/\int\log|f'|\,d\nu$.
  The measure is exact-dimensional.
* **54. Conformal iterated systems.** A finite conformal iterated
  function system satisfying the open set condition and bounded
  distortion has limit-set dimension equal to the zero of its
  geometric pressure. This extends the similarity equation
  $\sum r_i^s=1$.
* **55. Countable-system distinction.** For a finitely primitive
  conformal graph-directed system with the standard compactness,
  cone, contraction, and separation assumptions,
  $\dim_HJ=\inf\{t:P(t)<0\}=\sup_F\dim_HJ_F$ over finite
  subsystems. If pressure has a zero it equals the dimension; a
  zero need not exist for a countable alphabet.

## Transcendental entire dynamics

Here $f:\mathbb C\to\mathbb C$ is transcendental entire.
The **singular set** $S(f)$ is the closure of its finite critical and
finite asymptotic values. The **escaping set** is
$I(f)=\{z:f^n(z)\to\infty\}$.
Class $\mathcal B$ has bounded $S(f)$; class $\mathcal S$ has finite $S(f)$.

* **56. Singular values and covering maps.** Over a simply connected
  domain disjoint from $S(f)$, inverse branches continue without
  branching; $f:f^{-1}(\mathbb C\setminus S(f))\to
  \mathbb C\setminus S(f)$ is a covering map.
* **57. Transcendental Julia theory.** The Julia set is nonempty,
  perfect, and completely invariant, and repelling periodic points
  are dense in it. Normal-family arguments remain central despite
  the essential singularity at infinity.
* **58. Eremenko escaping theorem.** $I(f)$ is nonempty and
  $\partial I(f)=J(f)$. Its closure has no bounded connected component.
  This closure statement does not assert the corresponding property
  for components of $I(f)$ itself.
* **59. Class-$\mathcal B$ escape.** For a transcendental entire
  function with bounded singular set, every escaping point belongs
  to the Julia set. Thus this class has no escaping Fatou component.
* **60. Finite singular type.** Functions in class $\mathcal S$
  have no wandering Fatou components. Singular values replace critical
  values as the finite controlling set in deformation arguments.
* **61. Baker domains occur.** Transcendental entire maps can have
  invariant Fatou components on which iterates tend to infinity.
  For $f(z)=z+1+e^{-z}$, a sufficiently far right half-plane
  is invariant and its points escape, producing a Baker domain.

## Several-variable holomorphic dynamics

Let $F:\mathbb P^k\to\mathbb P^k$ be a holomorphic endomorphism
of algebraic degree $d\geq2$, and normalize the Fubini–Study form
$\omega$ by $\int\omega^k=1$.

* **62. Green current.** $d^{-n}(F^n)^*\omega$ converges to a
  positive closed $(1,1)$-current $T$ with continuous local potentials
  and $F^*T=dT$. Its construction uses a uniformly convergent
  potential series.
* **63. Equilibrium measure.** The product $\mu=T^k$ is a
  probability measure with $F_*\mu=\mu$, $F^*\mu=d^k\mu$.
  It does not charge pluripolar sets and is mixing.
* **64. Entropy on projective space.**
  $h_{\rm top}(F)=k\log d$, and $\mu$ is the unique invariant
  probability measure attaining that entropy.
* **65. Polynomial escape in several variables.** For a polynomial
  map of $\mathbb C^k$ extending holomorphically to $\mathbb P^k$,
  $d^{-n}\log^+\|F^n(z)\|$ converges locally uniformly to a
  continuous psh Green function $G$, with $G\circ F=dG$.
  Its zero set is the set of bounded forward orbits.
* **66. Generalized Hénon escape.** For
  $H(z,w)=(p(z)-aw,z)$, $a\ne0$, $\deg p=d\geq2$,
  the forward and backward escape limits $G^\pm$ are continuous
  psh functions, zero on the respective bounded-orbit sets, with
  $G^+\circ H=dG^+$ and $G^-\circ H^{-1}=dG^-$.
* **67. Hénon equilibrium measure.** The Green currents
  $T^\pm=dd^cG^\pm$ have wedge product an invariant probability
  measure supported on the intersection of the forward and backward
  Julia boundaries. Its measure entropy is $\log d$.
* **68. Holomorphic linearization without resonance.** In several
  variables, an attracting germ with invertible derivative whose
  eigenvalues have no multiplicative resonances is holomorphically
  conjugate to its linear part. With resonances, Poincaré–Dulac
  polynomial normal forms replace linearization.

## Reference guide

Milnor, Carleson–Gamelin, Beardon, Steinmetz, and the introductory
chapters of McMullen share the rational, local, Fatou, and polynomial
core. McMullen and Branner–Fagella develop deformation, straightening,
and renormalization; Hubbard supplies Thurston's characterization.
Przytycki–Urbański and Mauldin–Urbański give the expanding and
thermodynamic framework. The CIME lectures compare local germs,
transcendental dynamics, projective endomorphisms, and polynomial
automorphisms; Kotus–Urbański develops the meromorphic continuation.
Statements here retain the rational, entire, and higher-dimensional
hypotheses separately, especially for no-wandering and escape assertions.

Local full-text sources consulted:

* [McMullen, *Complex Dynamics and Renormalization*](References/McMullen1995ComplexDynamicsRenormalization-PrincetonAnnalsMathStud135.pdf).
* [Branner–Fagella, *Quasiconformal Surgery in Holomorphic Dynamics*](References/BrannerFagella2014QuasiconformalSurgeryHolomorphicDynamics-Cambridge.StudAM141.pdf).
* [Abate–Bedford–Brunella–Dinh–Schleicher–Sibony, *Holomorphic Dynamical Systems*](References/AbateBedfordBrunellaEtAl2010HolomorphicDynamicalSystems-Springer.LNM1998.pdf).
* [Mauldin–Urbański, *Graph Directed Markov Systems*](References/MauldinUrbanski2003GraphDirectedMarkovSystems-Cambridge.TractsMath148.pdf).
* [Kotus–Urbański, *Meromorphic Dynamics I*](References/KotusUrbanski2023MeromorphicDynamicsVol1-Cambridge.NMM46.pdf).

The linked Milnor text is his earlier introductory lecture version,
not the later edition named in the main bibliography.
