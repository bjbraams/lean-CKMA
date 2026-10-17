# Synopsis: Ergodic theory and measurable dynamics

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects the common graduate and beginning research content of
Section 10 of [CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md):
recurrence, ergodic averages, spectral structure, entropy, invariant measures,
and their connections with smooth dynamics and combinatorics. Joinings,
multiple averages, and infinite-measure results extend the introductory core
in directions recurring across the monographs.

A **probability-preserving system** $(X,\mathcal B,\mu,T)$ consists of a standard
probability space and a measurable transformation satisfying
$\mu(T^{-1}A)=\mu(A)$. Invertibility is assumed when negative iterates, unitary
spectral theory, or two-sided generators are used. Its **invariant
$\sigma$-field** is $\mathcal I=\{A:T^{-1}A=A\bmod\mu\}$.
The system is **ergodic** if $\mathcal I$ is trivial. A **factor** is a
probability-preserving quotient $\pi$ satisfying $\pi T=S\pi$ almost everywhere;
an **isomorphism** is an invertible such map modulo null sets.

The invariant measure is part of the system: one topological transformation
can support many mutually singular ergodic probabilities with different
entropies and recurrence statistics. A periodic orbit carries an invariant
atomic probability, while a mixing system need not have any periodic points
in a particular measurable model. Accordingly, statements about orbit counts
below have explicit topological or symbolic hypotheses; measurable isomorphism
preserves entropy and spectral structure, but it does not preserve arbitrary
features of a chosen topology.

## Recurrence, induction, and the ergodic theorems

For $A$ of positive measure, its **first return time** is
$\tau_A(x)=\inf\{n\geq1:T^nx\in A\}$ on $A$; the induced transformation is
$T_Ax=T^{\tau_A(x)}x$. Write
$A_Nf=N^{-1}\sum_{n=0}^{N-1}f\circ T^n$.

* **1. Poincaré recurrence.** Almost every point of a measurable set $A$
  returns to $A$ infinitely often. On a separable metric model, almost every
  point returns arbitrarily close to itself.
* **2. Kac's formula.** In an ergodic probability system, for $\mu(A)>0$,
  $$\int_A\tau_A\,d\mu=1.$$
  Thus the mean return time under $\mu_A=\mu(A)^{-1}\mu|_A$ is $1/\mu(A)$.
  The induced transformation preserves $\mu_A$ and is ergodic.
* **3. Characterizations of ergodicity.** Ergodicity is equivalent to every
  invariant measurable real function being constant almost everywhere, and to
  $$\frac1N\sum_{n<N}\mu(A\cap T^{-n}B)\longrightarrow\mu(A)\mu(B)$$
  for every measurable $A,B$.
* **4. Hopf maximal inequality.** For $f\in L^1$, let
  $E=\{x:\sup_{n\geq1}\sum_{j<n}f(T^jx)>0\}$. Then $\int_E f\,d\mu\geq0$.
  Applying this to $|f|-\lambda$ yields the weak maximal estimate
  $\mu\{\sup_NA_N|f|>\lambda\}\leq\|f\|_1/\lambda$.
* **5. Birkhoff pointwise theorem.** For $f\in L^1$,
  $A_Nf\to\mathbb E[f\mid\mathcal I]$ almost everywhere and in $L^1$.
  In an ergodic system the limit is $\int f\,d\mu$. For $f\in L^p$,
  $1\leq p<\infty$, convergence also holds in $L^p$.
* **6. Von Neumann mean ergodic theorem.** For a unitary operator $U$ on a
  Hilbert space, $N^{-1}\sum_{n<N}U^n$ converges strongly to orthogonal
  projection onto $\ker(I-U)$. Applied to $Uf=f\circ T$, it gives the
  $L^2$ ergodic theorem.
* **7. Kingman's subadditive theorem.** If integrable $f_n$ satisfy
  $f_{n+m}\leq f_n+f_m\circ T^n$ and
  $\inf_n n^{-1}\int f_n\,d\mu>-\infty$, then $f_n/n$ converges almost
  everywhere and in $L^1$ to an invariant integrable function. In the ergodic
  case the limit is $\inf_n n^{-1}\int f_n\,d\mu$.
* **8. Ergodic decomposition.** A probability-preserving standard system
  decomposes into ergodic invariant probabilities $\mu_\omega$ with
  $\mu=\int\mu_\omega\,d\eta(\omega)$. For integrable $f$, the component
  integrals realize $\mathbb E[f\mid\mathcal I]$. The decomposition is unique
  in its standard measure-theoretic sense.
* **9. Rokhlin tower lemma.** For an invertible aperiodic standard probability
  system, every height $n$ and $\varepsilon>0$ admit a measurable base $B$
  with $B,TB,\ldots,T^{n-1}B$ disjoint and union of measure greater than
  $1-\varepsilon$.
* **10. Natural extension.** Every probability-preserving transformation has
  an invertible extension whose past coordinates generate the extension and
  whose future projects to the original system. It is unique up to the
  corresponding isomorphism and preserves ergodicity and entropy.

## Koopman operators and spectral structure

The **Koopman operator** $Uf=f\circ T$ is an isometry on $L^p$ and, for
invertible $T$, unitary on $L^2$. The system is **weakly mixing** if the
Cesàro averages of $|\mu(A\cap T^{-n}B)-\mu(A)\mu(B)|$ tend to zero; it is
**strongly mixing** if the individual differences tend to zero.
**Discrete spectrum** means that eigenfunctions span $L^2$.

* **11. Spectral representation of correlations.** For $f\in L^2$ in an
  invertible system there is a unique finite positive measure $\sigma_f$ on
  the unit circle with
  $\langle U^nf,f\rangle=\int z^n\,d\sigma_f(z)$ for $n\in\mathbb Z$.
  Atoms describe eigenfunction components.
* **12. Weak mixing criteria.** Weak mixing is equivalent to ergodicity of
  $T\times T$, to the absence of nonconstant $L^2$ eigenfunctions, and to
  continuity of every spectral measure on the mean-zero subspace. These
  criteria refer to an invertible probability system in the spectral formulation.
* **13. Mixing and correlations.** Strong mixing is equivalent to
  $\langle U^nf,g\rangle\to\mu(f)\overline{\mu(g)}$ for all $f,g\in L^2$.
  Strong mixing implies weak mixing, which implies ergodicity; the converses
  fail in general.
* **14. Weak mixing and products.** The product of a weakly mixing system
  with any ergodic probability-preserving system is ergodic. In particular,
  every finite Cartesian power of a weakly mixing system is ergodic.
* **15. Wiener spectral criterion.** For a finite measure $\sigma$ on the
  circle,
  $$\lim_{N\to\infty}\frac1N\sum_{n<N}|\widehat\sigma(n)|^2
    =\sum_z|\sigma(\{z\})|^2.$$
  Applied to Koopman spectral measures, it identifies the continuous-spectrum
  part with Cesàro decay of correlations.
* **16. Halmos–von Neumann theorem.** An ergodic invertible standard system
  with discrete spectrum is measurably isomorphic to a rotation on a compact
  metrizable abelian group with Haar measure. Its eigenvalue group determines
  this rotation up to isomorphism.
* **17. Kronecker factor.** The closed span of eigenfunctions is the $L^2$
  space of a factor, the maximal factor with discrete spectrum. For ergodic
  systems it is a compact-group rotation and governs the structured part of
  two-term nonconventional averages.

## Entropy and measurable classification

For a finite or countable partition $\mathcal P$, define
$H_\mu(\mathcal P)=-\sum_{P\in\mathcal P}\mu(P)\log\mu(P)$, with
$0\log0=0$, and
$\mathcal P_0^{n-1}=\bigvee_{j=0}^{n-1}T^{-j}\mathcal P$.
The **entropy rate** is
$h_\mu(T,\mathcal P)=\lim_n n^{-1}H_\mu(\mathcal P_0^{n-1})$.
The **Kolmogorov–Sinai entropy** $h_\mu(T)$ is the supremum of these rates over
finite partitions. Natural logarithms are used.

* **18. Entropy chain rule.**
  $H(\mathcal P\vee\mathcal Q)=H(\mathcal Q)+H(\mathcal P\mid\mathcal Q)$.
  Conditioning reduces entropy, and
  $H(\mathcal P\vee\mathcal Q)\leq H(\mathcal P)+H(\mathcal Q)$, with equality
  for independent partitions of finite entropy.
* **19. Existence and functoriality of dynamical entropy.** Subadditivity gives
  the entropy-rate limit. Entropy is invariant under measurable isomorphism,
  does not increase on passing to a factor, and is additive for products of
  probability systems.
* **20. Kolmogorov–Sinai generator theorem.** If $H(\mathcal P)<\infty$ and
  $\bigvee_{n\in\mathbb Z}T^{-n}\mathcal P$ generates the measurable sets
  modulo null sets, then $h_\mu(T)=h_\mu(T,\mathcal P)$.
* **21. Shannon–McMillan–Breiman theorem.** For an ergodic system and a
  partition of finite entropy,
  $$-\frac1n\log\mu(\mathcal P_0^{n-1}(x))
    \longrightarrow h_\mu(T,\mathcal P)$$
  almost everywhere and in $L^1$. Typical length-$n$ names therefore have
  probability on the exponential scale $e^{-nh}$.
* **22. Bernoulli entropy.** The two-sided independent shift with alphabet
  probabilities $(p_i)$ has entropy $-\sum_i p_i\log p_i$, with infinity
  allowed. Nontrivial Bernoulli shifts are strongly mixing.
* **23. Markov entropy.** A stationary finite-state Markov shift with
  transition matrix $P$ and stationary vector $\pi$ has
  $h=-\sum_{i,j}\pi_iP_{ij}\log P_{ij}$. Irreducibility and aperiodicity give
  mixing of this shift.
* **24. Abramov induction formula.** For an ergodic invertible system and
  $\mu(A)>0$, the induced system satisfies
  $h_{\mu_A}(T_A)=h_\mu(T)/\mu(A)$.
* **25. Sinai factor theorem.** Every ergodic invertible system has a Bernoulli
  factor of any prescribed finite alphabet distribution whose entropy does
  not exceed the entropy of the system.
* **26. Ornstein isomorphism theorem.** Two two-sided Bernoulli shifts of the
  same entropy are measurably isomorphic, including the standard infinite-entropy
  case. Entropy is thus a complete invariant within this class, although it is
  not a complete invariant for arbitrary ergodic transformations.
* **27. Pinsker factor.** Every invertible probability system has a maximal
  zero-entropy factor, generated by its zero-entropy measurable partitions.
  For a Bernoulli shift with positive entropy this factor is trivial: every
  nontrivial factor has positive entropy.

## Topological dynamics and thermodynamic formalism

Here $T:X\to X$ is continuous on a compact metric space. Set
$d_n(x,y)=\max_{j<n}d(T^jx,T^jy)$; an $(n,\varepsilon)$-separated set has
pairwise $d_n$ distances greater than $\varepsilon$. Topological entropy is the
exponential growth rate of maximal separated sets as $n\to\infty$ followed by
$\varepsilon\downarrow0$. For continuous $\phi$, **pressure** weights each
point by $\exp(S_n\phi(x))$, where $S_n\phi=\sum_{j<n}\phi\circ T^j$.

* **28. Invariant probability existence.** The invariant probabilities form
  a nonempty compact convex set. Weak limits of empirical measures
  $N^{-1}\sum_{n<N}\delta_{T^nx}$ are invariant; its extreme points are exactly
  the ergodic probabilities.
* **29. Unique ergodicity and uniform averages.** There is a unique invariant
  probability $\mu$ exactly when $A_Nf\to\int f\,d\mu$ uniformly on $X$ for
  every continuous $f$. This conclusion is stronger than almost-everywhere
  convergence for a fixed invariant probability.
* **30. Weyl equidistribution.** A sequence $x_n$ in $\mathbb T^d$ is
  Haar-equidistributed exactly when
  $N^{-1}\sum_{n<N}e^{2\pi i\langle k,x_n\rangle}\to0$ for every
  nonzero $k\in\mathbb Z^d$. Rotation by $\alpha$ is uniquely ergodic exactly
  when $\langle k,\alpha\rangle\notin\mathbb Z$ for nonzero $k$.
* **31. Entropy of a shift of finite type.** For a primitive zero–one matrix
  $A$, the admissible shift space has topological entropy $\log\rho(A)$.
  Perron–Frobenius eigenvectors determine its unique measure of maximal entropy.
* **32. Variational principle for entropy.**
  $h_{\mathrm{top}}(T)=\sup_{\mu\in\mathcal M_T}h_\mu(T)$.
  The supremum need not be attained without further hypotheses.
* **33. Variational principle for pressure.**
  $$P(\phi)=\sup_{\mu\in\mathcal M_T}
     \left(h_\mu(T)+\int\phi\,d\mu\right).$$
  A maximizing measure is an **equilibrium state**. Taking $\phi=0$ recovers
  the entropy principle.
* **34. Ruelle–Perron–Frobenius theorem.** On a mixing one-sided finite-type
  shift and for Hölder $\phi$, the transfer operator
  $\mathcal L_\phi f(x)=\sum_{Ty=x}e^{\phi(y)}f(y)$ has a simple positive
  leading eigenvalue $e^{P(\phi)}$, a positive Hölder eigenfunction, and an
  eigenmeasure. The remaining spectrum on the Hölder space is separated from
  the leading eigenvalue; their normalized product is the unique equilibrium state.
* **35. Gibbs property and correlations.** In that setting the equilibrium
  measure obeys
  $$C^{-1}\leq\frac{\mu([x_0\ldots x_{n-1}])}
    {\exp(S_n\phi(x)-nP(\phi))}\leq C.$$
  Hölder observables have exponential decay of correlations. This is the
  basic connection between local weights and statistical independence at long times.
* **36. Periodic-orbit pressure.** For a mixing finite-type shift and Hölder
  potential,
  $$P(\phi)=\lim_n\frac1n\log\sum_{T^nx=x}e^{S_n\phi(x)}.$$
  In particular, periodic-point growth recovers topological entropy.

## Lyapunov exponents and smooth ergodic theory

A **linear cocycle** is $A^{(n)}(x)=A(T^{n-1}x)\cdots A(x)$.
Its Lyapunov exponents describe exponential growth of vectors and singular
values. For a diffeomorphism the principal example is $A(x)=DT_x$.
The multiplicity $m_i$ is the dimension of the exponent space.

* **37. Furstenberg–Kesten growth theorem.** For an ergodic base and a matrix
  cocycle with integrable $\log^+\|A\|$, Kingman's theorem gives an
  almost-everywhere constant limit of $n^{-1}\log\|A^{(n)}(x)\|$, possibly
  $-\infty$. Under integrable inverse norms it is finite.
* **38. Oseledets multiplicative ergodic theorem.** For an invertible ergodic
  base, $A(x)\in GL(d,\mathbb R)$, and integrable
  $\log^+\|A\|+\log^+\|A^{-1}\|$, there are exponents
  $\lambda_1>\cdots>\lambda_r$ and a measurable invariant splitting
  $\mathbb R^d=\bigoplus_iE_i(x)$ with
  $n^{-1}\log|A^{(n)}(x)v|\to\lambda_i$ for nonzero $v\in E_i(x)$.
* **39. Margulis–Ruelle inequality.** For a $C^1$ diffeomorphism of a compact
  manifold and an invariant probability,
  $$h_\mu(T)\leq\int\sum_{\lambda_i(x)>0}m_i(x)\lambda_i(x)\,d\mu(x).$$
* **40. Pesin entropy formula.** For a $C^{1+\alpha}$ diffeomorphism,
  $\alpha>0$, of a compact manifold, an invariant probability absolutely
  continuous with respect to Riemannian volume satisfies equality in result 39.
  The positive exponents give the entropy produced along unstable directions.
* **41. Hopf ergodicity theorem.** The geodesic flow of a compact connected
  negatively curved smooth Riemannian manifold is ergodic for normalized
  Liouville measure. Stable and unstable foliations connect geometric
  hyperbolicity with equality of forward and backward time averages.

## Joinings, recurrence, and nonconventional averages

A **joining** is an invariant probability on a product system with the given
marginals. Two systems are **disjoint** if their product measure is their only
joining. The terminology concerns stationary couplings, rather than
independence of random variables already placed on one probability space.

* **42. Compactness and extreme joinings.** For compact metric models, joinings
  form a nonempty compact convex set. If the prescribed marginals are ergodic,
  its extreme points are precisely the ergodic joinings.
* **43. Ergodic decomposition of joinings.** A joining of ergodic systems
  decomposes into ergodic joinings with the same marginals. This allows
  structural questions about couplings to be reduced to ergodic ones.
* **44. Spectral disjointness.** For invertible ergodic systems, mutually
  singular maximal spectral types on their mean-zero $L^2$ spaces imply
  disjointness. A joining would otherwise give a nonzero intertwining Markov
  operator between these spectral representations.
* **45. Weak mixing versus discrete spectrum.** Every weakly mixing system
  is disjoint from every ergodic discrete-spectrum system. Continuous and
  pure-point spectral components therefore cannot sustain a nontrivial joining.
* **46. Furstenberg multiple recurrence.** If $\mu(A)>0$ and $k\geq1$, then
  $$\liminf_{N\to\infty}\frac1N\sum_{n=1}^N
    \mu(A\cap T^{-n}A\cap\cdots\cap T^{-kn}A)>0.$$
* **47. Correspondence principle.** A subset $E\subseteq\mathbb Z$ of
  positive upper Banach density admits a probability-preserving shift model
  and a set $A$ with that density as its measure, such that finite intersection
  densities dominate the corresponding intersection measures in the model.
* **48. Szemerédi's theorem.** Every subset of the integers of positive upper
  Banach density contains arithmetic progressions of every finite length with
  positive common difference. The correspondence principle transfers multiple
  recurrence to this combinatorial assertion.
* **49. Multiple mean convergence.** For bounded measurable $f_1,\ldots,f_k$,
  $$\frac1N\sum_{n=1}^N\prod_{j=1}^kf_j(T^{jn}x)$$
  converges in $L^2$. This is the Host–Kra–Ziegler theorem for powers of one
  transformation, without an ergodicity requirement on the original system.
* **50. Nilpotent characteristic factors.** In an ergodic invertible system,
  the factor $\mathcal Z_{k-1}$ is characteristic for the averages in result 49:
  replacing each $f_j$ by its conditional expectation on this factor does not
  change their $L^2$ limit. These factors are inverse limits of
  $(k-1)$-step nilsystems; $\mathcal Z_1$ is the Kronecker factor.
* **51. Wiener–Wintner theorem.** For an ergodic system and $f\in L^1$, one
  full-measure set of $x$ works simultaneously for every real $\theta$ in the
  convergence of $N^{-1}\sum_{n<N}e^{2\pi in\theta}f(T^nx)$.
* **52. Bourgain double recurrence theorem.** For bounded $f,g$ in a
  probability-preserving system,
  $N^{-1}\sum_{n<N}f(T^nx)g(T^{2n}x)$ converges almost everywhere.
  Higher-order $L^2$ convergence does not by itself assert this pointwise conclusion.

## Infinite invariant measure

Here $\mu$ is $\sigma$-finite, possibly infinite, and $T$ is invertible and
measure-preserving. A set is **wandering** if its distinct translates are
disjoint modulo null sets. The system is **conservative** if no wandering set
has positive measure.

* **53. Hopf decomposition.** The space decomposes, uniquely modulo null sets,
  into invariant conservative and dissipative parts. The dissipative part is
  a countable union of translates of one wandering set. Conservativity is the
  appropriate recurrence condition when finite invariant mass is unavailable.
* **54. Hopf ratio theorem.** In a conservative ergodic system, for
  $f,g\in L^1$ with $g>0$ almost everywhere,
  $$\frac{\sum_{n<N}f(T^nx)}{\sum_{n<N}g(T^nx)}
    \longrightarrow\frac{\int f\,d\mu}{\int g\,d\mu}$$
  almost everywhere. The denominator integral is finite and strictly positive.
* **55. Vanishing ordinary averages.** If additionally $\mu(X)=\infty$,
  then $A_Nf\to0$ almost everywhere for every $f\in L^1$. Ratio averages,
  rather than division by $N$, recover nontrivial integral information.

## Operator principles and statistical consequences

An operator is **power bounded** when $\sup_n\|U^n\|<\infty$.
A **coboundary** is a function of the form $u-u\circ T$; its orbit sums telescope.
For a positive integrable roof $r$ over an invertible system, the
**suspension flow** moves vertically on $\{(x,s):0\leq s<r(x)\}$ and
identifies $(x,r(x))$ with $(Tx,0)$. Its invariant probability is the normalized
restriction of $\mu(dx)ds$.

* **56. Spectral splitting.** A unitary Koopman representation splits
  orthogonally into the closed span of eigenfunctions and the continuous-spectrum
  subspace. On the latter, Cesàro averages of squared correlations vanish.
  This is the Hilbert-space form of the compact/reversible and weakly mixing
  decomposition, developed more generally by Jacobs–de Leeuw–Glicksberg.
* **57. Hilbert-space van der Corput lemma.** Let $u_n$ be a bounded sequence
  in a Hilbert space. If
  $$\lim_{H\to\infty}\frac1H\sum_{h=1}^H
    \limsup_{N\to\infty}\left|\frac1N\sum_{n=1}^N
       \langle u_{n+h},u_n\rangle\right|=0,$$
  then $N^{-1}\sum_{n=1}^Nu_n\to0$ in norm. This reduces convergence of
  nonconventional averages to correlations of lower complexity.
* **58. Reflexive mean ergodic theorem.** For a power-bounded operator on a
  reflexive Banach space, Cesàro averages converge strongly to a bounded
  projection, and
  $E=\ker(I-U)\oplus\overline{\operatorname{ran}(I-U)}$.
  This gives a common operator theorem behind many $L^p$ mean-ergodic results.
* **59. Flow ergodic theorem.** For a jointly measurable probability-preserving
  flow and $f\in L^1$,
  $T^{-1}\int_0^Tf\circ\phi^t\,dt$ converges almost everywhere and in $L^1$
  to the conditional expectation on the flow-invariant $\sigma$-field.
  Ergodicity of a flow refers to invariance under every time, rather than
  ergodicity of each individual time map.
* **60. Entropy and ergodic decomposition.** Dynamical entropy is affine in
  the invariant measure and satisfies
  $h_\mu(T)=\int h_{\mu_\omega}(T)d\eta(\omega)$ under ergodic decomposition.
  This is stronger than the ordinary concavity of static partition entropy.
* **61. Abramov suspension formula.** For an ergodic base and integrable
  positive roof, the suspension flow satisfies
  $h(\phi^t)=|t|h_\mu(T)/\int r\,d\mu$.
  Changing the time spent between returns changes entropy per unit time by
  precisely the average roof length.
* **62. Livšic theorem for shifts.** On a mixing two-sided shift of finite
  type, a real Hölder function has zero sum on every periodic orbit exactly
  when it is a Hölder coboundary. Periodic-orbit identities are therefore
  sufficient, as well as necessary, for solving this cohomological equation.
* **63. Central limit theorem for Gibbs shifts.** For a Hölder potential on
  a mixing finite-type shift, a real centered Hölder observable satisfies
  $$N^{-1/2}\sum_{n<N}f\circ T^n\Rightarrow N(0,\sigma_f^2),\qquad
    \sigma_f^2=\int f^2d\mu+2\sum_{n\geq1}\int f(f\circ T^n)d\mu.$$
  The series converges absolutely. The variance vanishes exactly for Hölder
  coboundaries; otherwise it is positive. The spectral gap of the transfer
  operator provides both this limit law and the correlation estimates.

## Reference guide

Viana–Oliveira, *Foundations of Ergodic Theory*, Chapters 1–10, provides the
recurrence, averages, decomposition, spectral, and entropy core; Chapters 11–12
develop expanding maps and thermodynamic formalism. Walters, Petersen,
Cornfeld–Fomin–Sinai, and Einsiedler–Ward cover much of the same foundational
material. Eisner–Farkas–Haase–Nagel, Chapters 6–18 and 20–21, provides the
operator, joining, and multiple-average viewpoint.

Downarowicz, *Entropy in Dynamical Systems*, Parts I–II, gives an independent
entropy-centered treatment, including the classification and variational
theorems. Ruelle and Bowen develop the Gibbs and transfer-operator framework.
Viana's Lyapunov lectures, Barreira–Pesin, and Katok–Hasselblatt develop the
smooth endpoint; Krengel and Aaronson the infinite-measure one. Furstenberg
and Host–Kra are the principal structural references for multiple recurrence
and nilpotent factors. These later endpoints are shared monograph material,
rather than prerequisites for a first course.

Local source anchors:

- [Viana–Oliveira, *Foundations of Ergodic Theory*](References/VianaOliveira2016FoundationsErgodicTheory-Cambridge.StudAM151.pdf).
- [Eisner et al., *Operator Theoretic Aspects of Ergodic Theory*](References/EisnerFarkasHaaseNagel2015OperatorTheoreticAspectsErgodicTheory-SpringerGTM272.pdf).
- [Downarowicz, *Entropy in Dynamical Systems*](References/Downarowicz2011EntropyDynamicalSystems-Cambridge.NMM18.pdf).
- [Viana, *Lectures on Lyapunov Exponents*](References/Viana2014LecturesLyapunovExponents-Cambridge.StudAM145.pdf).
- [Barreira–Pesin, *Nonuniform Hyperbolicity*](References/BarreiraPesin2007NonuniformHyperbolicity-CambridgeEMA115.pdf).
- [Ruelle, *Thermodynamic Formalism*](References/Ruelle2004ThermodynamicFormalismMathematicalStructureEquilibriumStatisticalMechanics2ndEd-CambridgeMathLib.pdf).
