# Synopsis: Hardy, Bergman, and model spaces; operators on analytic function spaces

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-42);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring core material from Section 42 of
[CKMA-bib.md](CKMA-bib.md#ckma-42).
Boundary factorization, reproducing kernels, interpolation, and analytic
operators connect the spaces in its title. The distinctions between their
boundary measures, area measures, norms, and multiplier algebras are essential.

Real-variable Hardy spaces belong to Section 27, abstract bounded-operator
models and the general operator model theory to Section 21, several-variable
function and kernel theory to [45A](CKMA-bib.md#ckma-45a), and conformal
boundary geometry to Section 43.

Put $\mathbb T=\partial\mathbb D$, $dm=dt/(2\pi)$ on $\mathbb T$,
and $dA_0=dx\,dy/\pi$ on $\mathbb D$. For $0<p<\infty$,
$$
H^p=\left\{f\in\mathcal O(\mathbb D):
\|f\|_p^p=\sup_{r<1}\int_{\mathbb T}|f(r\zeta)|^pdm(\zeta)<\infty\right\};
$$
$H^\infty$ has the supremum norm. For $\alpha>-1$,
$A_\alpha^p=\mathcal O(\mathbb D)\cap L^p(dA_\alpha)$, where
$dA_\alpha=(\alpha+1)(1-|z|^2)^\alpha dA_0$.
Inner products are linear in the first variable.

## Hardy spaces, boundary values, and factorization

An **inner function** is a bounded holomorphic function with boundary
modulus one almost everywhere. An **outer function** is, up to a unimodular
constant,
$\exp\int_{\mathbb T}(\zeta+z)/(\zeta-z)\log h(\zeta)dm(\zeta)$,
where $h>0$ and $\log h\in L^1$; it lies in $H^p$, $0<p\leq\infty$,
exactly when $h\in L^p$.

* **1. Boundary realization.** Every $f\in H^p$, $0<p<\infty$,
  has nontangential limits $f^*$ almost everywhere,
  $\|f\|_p=\|f^*\|_{L^p}$, and $f(r\cdot)\to f^*$ in $L^p$.
  For $p=\infty$, boundary limits identify the supremum and essential-supremum norms.
* **2. Completeness and point evaluations.** $H^p$ is Banach for
  $p\geq1$ and complete as a quasi-Banach space for $0<p<1$.
  Moreover $|f(z)|\leq(1-|z|^2)^{-1/p}\|f\|_p$.
* **3. Integral means and maximal functions.** For holomorphic $f$ on
  $\mathbb D$ and $0<p\leq\infty$, the integral mean $M_p(r,f)$ is
  nondecreasing in $r$ and $\log M_p(r,f)$ is convex in $\log r$
  (Hardy). For $0<p<\infty$ and $f\in H^p$, the nontangential maximal
  function $\sup_{z\in\Gamma_\beta(\zeta)}|f(z)|$ over Stolz angles lies
  in $L^p(\mathbb T)$ with norm at most $C_{p,\beta}\|f\|_p$.
* **4. Polynomial density.** Polynomials are dense in $H^p$ for
  $0<p<\infty$. They are not norm dense in $H^\infty$;
  their uniform closure is the disk algebra $A(\mathbb D)$.
* **5. Blaschke zero condition.** The zeros of a nonzero $H^p$
  function satisfy $\sum_j(1-|a_j|)<\infty$.
  Conversely every such sequence, with multiplicity, is the zero set
  of a Blaschke product and hence of a bounded holomorphic function.
* **6. Division by a Blaschke product.** If $B$ is the Blaschke
  product of the zeros of $f\in H^p$, then $f/B\in H^p$
  and $\|f/B\|_p=\|f\|_p$.
* **7. Canonical factorization.** Every nonzero $f\in H^p$ has
  a factorization $f=BS_\mu O$, unique up to unimodular constants,
  where $B$ is Blaschke, $O$ is outer, and
  $S_\mu(z)=\exp[-\int(\zeta+z)/(\zeta-z)d\mu(\zeta)]$
  for a finite positive singular measure $\mu$.
* **8. Frostman's theorem.** If $\theta$ is inner, then
  $(\theta-a)/(1-\bar a\theta)$ is a Blaschke product for every
  $a\in\mathbb D$ outside a set of logarithmic capacity zero. Hence
  Blaschke products are uniformly dense in the inner functions.
* **9. Outer functions and cyclicity.** An $H^2$ function is cyclic
  for multiplication by $z$ exactly when it is outer. Equivalently,
  the closure of its polynomial multiples is $H^2$.
* **10. Boundary uniqueness.** A nonzero $H^p$ function has
  $\log|f^*|\in L^1$ and cannot have boundary values zero on a
  set of positive arclength. Its modulus determines its outer factor.
* **11. Riesz factorization.** Every $f\in H^1$ is a product
  $gh$ with $g,h\in H^2$ and
  $\|f\|_1=\|g\|_2\|h\|_2$.
  Inner–outer factorization gives corresponding factorizations among other $H^p$ spaces.
* **12. F. and M. Riesz theorem.** A finite complex measure on
  $\mathbb T$ whose negative Fourier coefficients vanish is
  absolutely continuous, with density in $H^1$.
* **13. Riesz projection and duality.** The analytic projection $P_+$
  is bounded on $L^p$, $1<p<\infty$; consequently $(H^p)^*$
  identifies with $H^{p'}$ under boundary pairing, with equivalent norms.
* **14. Hardy coefficient inequality.** If $f(z)=\sum a_nz^n\in H^1$,
  then $\sum_{n\geq0}|a_n|/(n+1)\leq C\|f\|_1$.
  For $H^2$, Parseval gives $\|f\|_2^2=\sum|a_n|^2$.
* **15. Szegő kernel.** $H^2$ is a reproducing-kernel Hilbert space
  with $k_w(z)=(1-\bar wz)^{-1}$ and
  $\|k_w\|^2=(1-|w|^2)^{-1}$.
* **84. Nevanlinna and Smirnov classes.** The Nevanlinna class $N$
  consists of holomorphic $f$ on $\mathbb D$ with
  $\sup_r\int\log^+|f(r\zeta)|\,dm<\infty$; these are exactly the
  quotients $g/h$ of bounded holomorphic functions with $h$ zero-free.
  Nonzero $f\in N$ factor as $BS_1O/S_2$ with $B$ Blaschke, $S_1,S_2$
  singular inner, and $O$ outer. The Smirnov class $N^+$ is the subclass
  with $S_2$ constant, equivalently the quotients with outer denominator.
  $H^p\subset N^+$ for all $p>0$, and the boundary map is injective on $N$.
* **16. Smirnov maximum principle.** If $f$ is a quotient of bounded
  holomorphic functions with outer denominator, and $f^*\in L^p$,
  then $f\in H^p$. In particular a bounded boundary modulus gives
  the same bound inside for such a quotient.
* **17. Beurling's invariant-subspace theorem.** Every nonzero closed
  subspace of $H^2$ invariant under multiplication by $z$ is
  $\theta H^2$ for an inner $\theta$, unique up to a unimodular constant.
* **18. Multipliers.** The multiplier algebra of $H^p$,
  $0<p\leq\infty$, is $H^\infty$, with multiplier norm
  $\|M_\phi\|=\|\phi\|_\infty$.
* **19. Rudin–Carleson interpolation.** If $E\subset\mathbb T$
  is compact with arclength zero, every continuous function on $E$
  extends to the disk algebra without increasing its supremum norm.
* **28. Szegő infimum theorem.** If $w\geq0$ is integrable, then
  $\inf_{p(0)=0}\int|1-p|^2w\,dm=\exp\int\log w\,dm$,
  where $p$ ranges over analytic polynomials and the right side is
  zero when the logarithmic integral is $-\infty$.

## Carleson measures, BMO, and interpolation

For an arc $I$ of normalized length $|I|$, let
$S(I)=\{r\zeta:\zeta\in I,\ 1-|I|<r<1\}$.
A finite positive measure is **Carleson** if $\mu(S(I))\leq C|I|$.
The analytic space **BMOA** consists of $H^1$ functions whose boundary
values have bounded mean oscillation; **VMOA** uses vanishing mean oscillation.

* **20. Carleson embedding theorem.** For every $0<p<\infty$,
  $\int_{\mathbb D}|f|^pd\mu\leq C\|f\|_{H^p}^p$ for all
  $f\in H^p$ exactly when $\mu$ is Carleson.
* **21. Compact embedding.** The preceding embedding is compact
  exactly when $\mu(S(I))/|I|\to0$ as $|I|\to0$.
* **22. BMOA and area measures.** A holomorphic $g$ belongs to
  BMOA exactly when $|g'(z)|^2(1-|z|^2)dA_0(z)$ is Carleson.
  VMOA corresponds to the vanishing Carleson condition.
* **23. Fefferman duality.** $(H^1)^*$ is BMOA, with equivalent
  norms, under the pairing
  $\lim_{r\uparrow1}\int f(r\zeta)\overline{g(r\zeta)}dm$.
  Moreover $(\mathrm{VMOA})^*$ identifies with $H^1$.
* **24. Carleson interpolation theorem.** A sequence of distinct
  $a_j\in\mathbb D$ interpolates every bounded scalar sequence
  by an $H^\infty$ function exactly when
  $\inf_j\prod_{k\ne j}|(a_j-a_k)/(1-\bar a_ka_j)|>0$.
* **25. Interpolation and kernels.** The same condition is equivalent
  to the normalized Szegő kernels at $a_j$ forming a Riesz sequence.
  It is also equivalent to pseudohyperbolic separation together with
  the Carleson property of $\sum_j(1-|a_j|^2)\delta_{a_j}$.
* **26. Nevanlinna–Pick theorem.** Given distinct $z_i\in\mathbb D$
  and prescribed $w_i$, a function $f$ with $\|f\|_\infty\leq1$
  and $f(z_i)=w_i$ exists exactly when
  $[(1-w_i\bar w_j)/(1-z_i\bar z_j)]$ is positive semidefinite.
* **27. Corona theorem.** If $f_1,\ldots,f_n\in H^\infty$ and
  $\sum|f_j(z)|\geq\delta>0$ throughout $\mathbb D$, there
  are $g_j\in H^\infty$ with $\sum f_jg_j=1$. If
  $\|f_j\|_\infty\leq1$, the bounds on $\|g_j\|_\infty$ depend only on
  $n$ and $\delta$; a bound on $\sum|g_j|$ independent of $n$ is also
  available (Rosenblum, Tolokonnikov, Uchiyama). Equivalently, $\mathbb D$ is dense in the maximal
  ideal space of $H^\infty$.

## Toeplitz and Hankel operators

For $\phi\in L^\infty(\mathbb T)$ define
$T_\phi f=P_+(\phi f)$ on $H^2$ and
$H_\phi f=(I-P_+)(\phi f)$ with values in
$H^2_-=L^2\ominus H^2$.

* **29. Toeplitz characterization.** A bounded operator $T$ on
  $H^2$ is a Toeplitz operator exactly when $S^*TS=T$,
  where $S=M_z$. Its $L^\infty$ symbol is unique and
  $\|T_\phi\|=\|\phi\|_\infty$.
  Moreover $T_\phi^*=T_{\bar\phi}$.
* **30. Toeplitz–Hankel product identity.**
  $T_\phi T_\psi-T_{\phi\psi}=-H_{\bar\phi}^*H_\psi$.
  This locates the failure of multiplicativity in the Hankel terms.
  In particular $T_\phi T_\psi=T_{\phi\psi}$ if $\psi$ is analytic or
  $\phi$ is coanalytic.
* **31. Coburn alternative.** For a nonzero $L^\infty$ symbol,
  at least one of $\ker T_\phi$ and $\ker T_\phi^*$ is zero.
  Hence a Fredholm Toeplitz operator with scalar symbol and index zero is
  invertible.
* **32. Toeplitz Fredholm index.** If $\phi\in C(\mathbb T)$,
  $T_\phi$ is Fredholm exactly when $\phi$ never vanishes;
  its index is $-\operatorname{wind}(\phi,0)$ and its essential
  spectrum is $\phi(\mathbb T)$.
* **33. Toeplitz spectra.** For continuous $\phi$, $\sigma(T_\phi)$
  is $\phi(\mathbb T)$ together with the points $\lambda$ about which
  $\phi$ has nonzero winding number. For real $\phi\in L^\infty$,
  $\sigma(T_\phi)=[\operatorname{ess\,inf}\phi,\operatorname{ess\,sup}\phi]$
  (Hartman–Wintner). For every $\phi\in L^\infty$, $\sigma(T_\phi)$
  contains the essential range of $\phi$ and is connected (Widom).
* **34. Szegő limit theorems.** Let $D_n(\phi)=\det[\widehat\phi(j-k)]_{j,k=0}^{n-1}$.
  If $\phi\geq0$ and $\log\phi\in L^1$, then
  $D_{n+1}(\phi)/D_n(\phi)\to G(\phi)=\exp\int\log\phi\,dm$.
  If $\phi=e^{\psi}$ with $\sum_k|k||\widehat\psi(k)|^2<\infty$, then
  $D_n(\phi)\sim G(\phi)^n\exp\sum_{k\geq1}k\widehat\psi(k)\widehat\psi(-k)$.
  The first Szegő theorem $D_n(\phi)^{1/n}\to\exp\int\log\phi\,dm$ holds
  for every nonnegative $\phi\in L^1$, both sides being zero if
  $\log\phi\notin L^1$.
* **35. Nehari's theorem.** Every bounded Hankel matrix has a bounded
  symbol, and $\|H_\phi\|=\operatorname{dist}_{L^\infty}(\phi,H^\infty)$.
* **36. Hartman's theorem.** $H_\phi$ is compact exactly when
  $\phi\in H^\infty+C(\mathbb T)$.
* **90. Douglas algebras.** $H^\infty+C(\mathbb T)$ is a closed
  subalgebra of $L^\infty$ (Sarason). Every uniformly closed algebra
  $\mathcal B$ with $H^\infty\subset\mathcal B\subset L^\infty$ is
  generated by $H^\infty$ and the conjugates $\bar\theta$ of the inner
  functions $\theta$ invertible in $\mathcal B$ (Chang–Marshall).
* **37. Kronecker's theorem.** For analytic $g\in H^2$,
  $H_{\bar g}$ has finite rank exactly when $g$ is rational
  with no poles in the closed disk. Constants give the zero operator.
  Equivalently, a Hankel matrix has finite rank exactly when the power
  series formed from its Hankel coefficients is rational.
* **38. Hilbert–Schmidt Hankel criterion.** If
  $g(z)=\sum a_nz^n$, then
  $\|H_{\bar g}\|_{S_2}^2=\sum_{n\geq1}n|a_n|^2$.
  Thus this Schatten condition is exactly finite Dirichlet energy.
* **39. Analytic symbols and BMOA.** $H_{\bar g}$ is bounded
  precisely for $g\in\mathrm{BMOA}$ and compact precisely for
  $g\in\mathrm{VMOA}$, with constants irrelevant to the operator.

## Model spaces and compressed shifts

For a nonconstant inner function $\theta$, put
$K_\theta=H^2\ominus\theta H^2$ and
$S_\theta=P_{K_\theta}M_z|_{K_\theta}$.
These are the **model space** and its **compressed shift**.

* **40. Backward-shift invariant subspaces.** Every proper nonzero
  closed $S^*$-invariant subspace of $H^2$ is $K_\theta$.
  Its orthogonal complement is supplied by Beurling's theorem.
* **41. Model kernels.** The reproducing kernel is
  $k_w^\theta(z)=(1-\overline{\theta(w)}\theta(z))/(1-\bar wz)$.
  In particular $\|k_w^\theta\|^2=(1-|\theta(w)|^2)/(1-|w|^2)$.
* **42. Product decomposition.**
  $K_{\theta_1\theta_2}=K_{\theta_1}\oplus\theta_1K_{\theta_2}$
  orthogonally. A finite Blaschke product of degree $n$ has an
  $n$-dimensional model space of rational functions.
* **43. Malmquist–Walsh bases.** Successive normalized kernels,
  multiplied by the preceding Blaschke factors, form an orthonormal
  basis of $K_B$ for a finite or infinite Blaschke product $B$.
  Repeated zeros are allowed.
* **44. Model conjugation.** The boundary formula
  $C_\theta f=\theta\bar\zeta\,\bar f$ defines an isometric
  antilinear involution of $K_\theta$, and
  $S_\theta=C_\theta S_\theta^*C_\theta$.
* **45. Sarason's commutant theorem.** An operator on $K_\theta$
  commutes with $S_\theta$ exactly when it equals
  $\phi(S_\theta)=P_{K_\theta}M_\phi|_{K_\theta}$ for some
  $\phi\in H^\infty$, and $\phi$ can be chosen with
  $\|\phi\|_\infty=\|\phi(S_\theta)\|$. Taking $\theta$ a finite
  Blaschke product recovers Nevanlinna–Pick and Carathéodory–Fejér
  interpolation.
* **46. Angular derivatives and evaluation.** At $\zeta\in\mathbb T$,
  every function of $K_\theta$ has a finite nontangential value
  exactly when $\theta$ has a finite Carathéodory angular derivative
  there. Evaluation is then bounded and its kernel has norm squared
  $|\theta'(\zeta)|$.
* **47. Clark measures.** For $|\alpha|=1$, the positive harmonic
  function $\Re[(\alpha+\theta)/(\alpha-\theta)]$ is the Poisson
  integral of a singular measure $\sigma_\alpha$ carried by
  $\{\theta=\alpha\}$. At a finite-angular-derivative point with
  $\theta(\zeta)=\alpha$, its atom has mass $1/|\theta'(\zeta)|$.
* **48. Clark representation.** Boundary restriction extends to a
  unitary map $K_\theta\to L^2(\sigma_\alpha)$.
  For $\theta(0)=0$ it identifies the corresponding unitary rank-one
  perturbation of $S_\theta$ with multiplication by $\zeta$.
* **49. Interpolating model bases.** If $B$ has simple zeros $a_j$,
  its normalized kernels at those zeros form a Riesz basis of $K_B$
  exactly when the zero sequence satisfies Carleson's interpolation condition.

## Cauchy transforms and subnormal operators

For a finite complex measure $\mu$ on $\mathbb T$, its **Cauchy transform**
is $K\mu(z)=\int_{\mathbb T}(1-\bar\zeta z)^{-1}d\mu(\zeta)$, $z\in\mathbb D$.
For a positive compactly supported measure $\mu$ on $\mathbb C$ and
$1\leq t<\infty$, $P^t(\mu)$ is the closure of the polynomials in $L^t(\mu)$.
A point $w$ is a **bounded point evaluation** if $p\mapsto p(w)$ extends
continuously to $P^t(\mu)$; it is **analytic** if this holds uniformly
near $w$.

* **85. Cauchy transforms of measures.** $K\mu\in H^p$ for every
  $0<p<1$, with $\|K\mu\|_p\leq C_p\|\mu\|$, and its boundary function
  obeys Kolmogorov's weak-type $(1,1)$ bound. By the F. and M. Riesz
  theorem $K\mu=0$ exactly when $d\mu=\bar h\,dm$ with $h\in H^1$,
  $h(0)=0$; with the quotient norm, the space of Cauchy transforms is
  isometric to the dual of the disk algebra.
* **86. Aleksandrov disintegration.** For an inner $\theta$ with Clark
  measures $\sigma_\alpha$ (item 47) and $f\in C(\mathbb T)$,
  $\int_{\mathbb T}\bigl(\int f\,d\sigma_\alpha\bigr)dm(\alpha)=\int f\,dm$;
  this extends to $f\in L^1(m)$, the inner integral being defined for
  almost every $\alpha$. If $\theta(0)=0$, the inverse of the Clark
  unitary of item 48 is the normalized Cauchy transform
  $g\mapsto(1-\bar\alpha\theta)K(g\sigma_\alpha)$.
* **87. Poltoratski's theorem.** If $\mu$ is a positive finite singular
  measure on $\mathbb T$ and $f\in L^2(\mu)$, then
  $K(f\mu)/K\mu\to f$ nontangentially at $\mu$-almost every point.
* **88. Cyclic subnormal operators.** Multiplication by $z$ on
  $P^2(\mu)$ is subnormal, and every cyclic subnormal operator is unitarily
  equivalent to such an operator (Bram). Multiplication by $z$ on $H^2$
  and on $A_\alpha^2$ are examples; on the Dirichlet space it is not even
  hyponormal. The minimal normal extension $N$ of a subnormal $S$ is
  unique up to unitary equivalence, $\sigma(N)\subset\sigma(S)$, and
  $\sigma(S)$ is $\sigma(N)$ with some bounded components of
  $\mathbb C\setminus\sigma(N)$ filled in. Subnormal operators have
  nontrivial invariant subspaces (S. Brown; SYNOPSIS21, item 52).
* **89. Thomson's theorem and Putnam's inequality.** For $1\leq t<\infty$,
  $\operatorname{supp}\mu$ has a Borel partition $\Delta_0,\Delta_1,\ldots$
  with $P^t(\mu)=L^t(\mu|_{\Delta_0})\oplus\bigoplus_{i\geq1}P^t(\mu|_{\Delta_i})$,
  where for $i\geq1$ the analytic bounded point evaluations of
  $P^t(\mu|_{\Delta_i})$ form a simply connected region $U_i$ with
  $\Delta_i\subset\overline{U_i}$. In particular $P^t(\mu)\neq L^t(\mu)$
  exactly when bounded point evaluations exist. Every hyponormal, in
  particular every subnormal, operator satisfies Putnam's inequality
  $\|T^*T-TT^*\|\leq\pi^{-1}\operatorname{area}\sigma(T)$.

## Bergman and Bloch spaces

The **Bloch space** consists of holomorphic $g$ with
$\|g\|_{\mathcal B}=|g(0)|+\sup_z(1-|z|^2)|g'(z)|<\infty$;
the **little Bloch space** has the weighted derivative tending to zero
at the boundary.

* **50. Bergman evaluation estimates.** $A_\alpha^p$ is complete,
  polynomials are dense for $p<\infty$, and
  $|f(z)|\leq C(1-|z|^2)^{-(\alpha+2)/p}\|f\|_{A_\alpha^p}$.
* **51. Bergman kernel.** $A_\alpha^2$ has kernel
  $K_\alpha(z,w)=(1-z\bar w)^{-\alpha-2}$.
  For $\alpha=0$, the normalized monomials are $\sqrt{n+1}z^n$.
* **52. Bergman projection.**
  $P_\alpha f(z)=\int K_\alpha(z,w)f(w)dA_\alpha(w)$
  is the orthogonal projection on $L^2(dA_\alpha)$ and extends
  boundedly from $L^p(dA_\alpha)$ onto $A_\alpha^p$ for $1<p<\infty$.
* **53. Bergman duality.** For $1<p<\infty$,
  $(A_\alpha^p)^*=A_\alpha^{p'}$ with equivalent norms under area
  pairing. At the endpoint $(A_\alpha^1)^*$ is Bloch space under
  the radially regularized pairing, again with equivalent norms.
* **54. Kernel transformation.** For a biholomorphism
  $\phi:\Omega_1\to\Omega_2$ of plane domains, their unweighted
  Bergman kernels satisfy
  $K_{\Omega_1}(z,w)=\phi'(z)\overline{\phi'(w)}
  K_{\Omega_2}(\phi(z),\phi(w))$.
* **55. Bergman Carleson measures.** For $0<p<\infty$,
  $A_\alpha^p\hookrightarrow L^p(\mu)$ is bounded exactly when
  $\sup_I\mu(S(I))/|I|^{\alpha+2}<\infty$.
  It is compact exactly when this ratio tends to zero for shrinking arcs.
* **56. Positive Bergman Toeplitz operators.** For positive finite
  $\mu$, $T_\mu f(z)=\int K_\alpha(z,w)f(w)d\mu(w)$ is
  bounded on $A_\alpha^2$ exactly when $\mu$ is a Bergman
  Carleson measure; compactness corresponds to the vanishing condition.
* **57. Berezin testing.** For positive $\mu$, boundedness of
  $T_\mu$ is equivalent to boundedness of
  $\widetilde\mu(z)=\int|K_\alpha(w,z)|^2/K_\alpha(z,z)d\mu(w)$.
  Compactness is equivalent to $\widetilde\mu(z)\to0$ at the boundary.
* **58. Bergman Hankel criterion.** For analytic $g\in A^2$,
  $(I-P)(\bar g f)$ extends boundedly on $A^2$ exactly when
  $g$ is Bloch, and compactly exactly when $g$ is little Bloch.
* **59. Bergman multipliers.** The multipliers of $A_\alpha^p$,
  $0<p<\infty$, are exactly $H^\infty$, with multiplier norm
  equal to the supremum norm.
* **60. Bloch geometry.** Bloch functions are exactly the holomorphic
  functions Lipschitz from the disk's hyperbolic metric to Euclidean
  distance, with equivalent seminorms. Disk automorphisms preserve
  the derivative seminorm.
* **61. Invariant subspaces differ from Hardy spaces.** The Bergman
  shift has invariant subspaces not of the form $\theta A^2$ for
  an inner $\theta$. Nevertheless every nonzero closed invariant
  subspace $M$ is generated by its wandering subspace
  $M\ominus zM$ under repeated multiplication by $z$.

## Dirichlet and de Branges–Rovnyak spaces

Use the Dirichlet norm
$\|f\|_{\mathcal D}^2=\|f\|_{H^2}^2+\int|f'|^2dA_0
=\sum_{n\geq0}(n+1)|a_n|^2$.
For $b\in H^\infty$, $\|b\|_\infty\leq1$, the space
$\mathcal H(b)$ is the range of $(I-T_bT_b^*)^{1/2}$ with its
range norm: the norm of the least-norm preimage.

* **62. Dirichlet kernel.** Point evaluations on $\mathcal D$ have
  kernel $k_w(z)=\log(1/(1-z\bar w))/(z\bar w)$, with value
  one when $z\bar w=0$. The energy seminorm is invariant under
  disk automorphisms.
* **63. Douglas formula.** Dirichlet energy equals
  $\iint_{\mathbb T^2}|f^*(\zeta)-f^*(\eta)|^2/
  |\zeta-\eta|^2\,dm(\zeta)dm(\eta)$, interpreted by approximation
  when necessary. It identifies $\mathcal D$ with an analytic
  boundary Sobolev space of order $1/2$.
* **64. Capacitary boundary limits.** Every Dirichlet function has
  radial boundary limits outside a set of logarithmic capacity zero.
  Capacity refines arclength-null exceptional sets in this space.
* **65. Stegenga's embedding theorem.** A finite positive measure
  embeds $\mathcal D$ into $L^2(\mu)$ exactly when
  $\mu(\bigcup_jS(I_j))\leq C\operatorname{Cap}(\bigcup_j I_j)$
  for all finite families of disjoint boundary arcs. Here
  $\operatorname{Cap}$ is the boundary Sobolev capacity of order
  $1/2$, comparable to the reciprocal of the minimum probability
  energy for the kernel $\log(e/|\zeta-\eta|)$ on the set.
* **66. Dirichlet multipliers.** A holomorphic $\phi$ multiplies
  $\mathcal D$ boundedly exactly when $\phi\in H^\infty$ and
  $|\phi'|^2dA_0$ is a Dirichlet Carleson measure.
* **67. Complete Pick interpolation.** For the displayed Dirichlet
  norm, a contractive multiplier taking finite data $z_i\mapsto w_i$
  exists exactly when $[(1-w_i\bar w_j)k_{z_j}(z_i)]\geq0$.
  The analogous matrix-valued interpolation criterion also holds.
* **68. Dirichlet multiplication and norm dependence.**
  $\mathcal D\cap H^\infty$ is an algebra, but strictly contains
  the multiplier algebra. Exact contractive Pick statements depend on
  the chosen Hilbert norm, not only on its equivalence class.
* **69. de Branges–Rovnyak kernel.** $\mathcal H(b)$ is a Hilbert
  space contractively included in $H^2$ with kernel
  $(1-\overline{b(w)}b(z))/(1-\bar wz)$.
  For inner $b=\theta$, it is isometrically $K_\theta$.
  The kernel is positive definite for every analytic $b$ with
  $\|b\|_\infty\leq1$.
* **70. Nonextreme symbols.** For a nonconstant Schur function $b$,
  nonextremality in the unit ball of $H^\infty$ is equivalent to
  $\log(1-|b^*|^2)\in L^1$. In this case there is a unique
  outer $a$, $a(0)>0$, with $|a|^2+|b|^2=1$ almost everywhere.
* **71. Nonextreme norm formula.** For that pair $(b,a)$,
  $f\in\mathcal H(b)$ exactly when there is $f^+\in H^2$
  with $T_{\bar b}f=T_{\bar a}f^+$; this $f^+$ is unique and
  $\|f\|_{\mathcal H(b)}^2=\|f\|_2^2+\|f^+\|_2^2$.
* **72. Polynomial density in $\mathcal H(b)$.** For nonconstant
  Schur $b$, polynomials belong to and are dense in $\mathcal H(b)$
  exactly when $b$ is nonextreme. Extreme symbols require a different
  approximation theory.

## Composition operators

For a holomorphic self-map $\phi$ of the disk, let $C_\phi f=f\circ\phi$.

* **73. Littlewood subordination.** If $\phi(0)=0$, $C_\phi$
  is a contraction on $H^p$ for every $0<p<\infty$.
  Every disk self-map induces a bounded operator on $H^p$;
  on $H^2$, $\|C_\phi\|\leq[(1+|\phi(0)|)/(1-|\phi(0)|)]^{1/2}$.
* **74. Pullback-measure criteria.** On $H^2$, where every $C_\phi$ is
  bounded (item 73) and the boundary pullback measure
  $m\circ(\phi^*)^{-1}$ on the closed disk is always Carleson, $C_\phi$
  is compact exactly when that measure is vanishing Carleson, with the
  natural extension of Carleson boxes. The Carleson criterion for
  boundedness is substantive on spaces such as $\mathcal D$.
  For $A_\alpha^2$, use instead $A_\alpha\circ\phi^{-1}$ and
  the Bergman box exponent $\alpha+2$.
* **75. Shapiro compactness criterion.** Define
  $N_\phi(w)=\sum_{\phi(z)=w}\log(1/|z|)$ with multiplicity,
  away from $\phi(0)$. Then $C_\phi$ is compact on $H^2$
  exactly when $N_\phi(w)/\log(1/|w|)\to0$ as $|w|\to1$.
* **76. Angular-derivative obstruction.** Compactness on $H^2$
  implies $(1-|z|^2)/(1-|\phi(z)|^2)\to0$ as $|z|\to1$.
  Thus a finite angular derivative at a boundary contact point precludes
  compactness. Absence of such derivatives alone is not sufficient in general.
* **77. Hardy isometries.** An inner self-map with $\phi(0)=0$
  induces an isometry on $H^2$. Conversely, an isometric composition
  operator on $H^2$ has precisely these properties.

## Fock spaces and planar sampling

For $\alpha>0$, the **Fock space** $\mathcal F_\alpha^2$ consists
of entire functions square-integrable for
$d\lambda_\alpha=(\alpha/\pi)e^{-\alpha|z|^2}dx\,dy$.
For a separated sequence $\Lambda\subset\mathbb C$, define
$D^\pm(\Lambda)=\lim_{R\to\infty}\{\inf,\sup\}_{z\in\mathbb C}
\#(\Lambda\cap B(z,R))/(\pi R^2)$, respectively using lower
and upper limits if necessary.

* **78. Fock kernel and basis.** The kernel is $e^{\alpha z\bar w}$,
  the normalized monomials are $\alpha^{n/2}z^n/\sqrt{n!}$,
  and $|f(z)|\leq e^{\alpha|z|^2/2}\|f\|$.
* **79. Gaussian translations.**
  $U_af(z)=e^{\alpha z\bar a-\alpha|a|^2/2}f(z-a)$ is unitary
  on $\mathcal F_\alpha^2$. These translations replace disk
  automorphisms in local estimates and kernel testing.
* **80. Fock Carleson measures.** The inequality
  $\int|f|^2e^{-\alpha|z|^2}d\mu\leq C\|f\|^2$ holds
  exactly when $\sup_z\mu(B(z,r))<\infty$ for one fixed $r>0$.
  Compactness corresponds to $\mu(B(z,r))\to0$ as $|z|\to\infty$.
* **81. Fock interpolation density.** A separated $\Lambda$
  interpolates arbitrary square-summable normalized values
  $f(\lambda)e^{-\alpha|\lambda|^2/2}$ exactly when
  $D^+(\Lambda)<\alpha/\pi$.
* **82. Fock sampling density.** A separated $\Lambda$ gives a
  sampling norm equivalent to $\|f\|^2$ exactly when
  $D^-(\Lambda)>\alpha/\pi$. The strict inequalities distinguish
  sampling and interpolation; in particular a lattice of critical density
  $\alpha/\pi$ is neither sampling nor interpolating.
* **83. Kernel interpretation.** Fock sampling is equivalent to the
  normalized kernels forming a frame; interpolation is equivalent to
  their forming a Riesz sequence. Thus density theorems become
  analytic versions of frame and basis criteria.

## Reference guide

Garnett, Duren, Koosis, Hoffman, and Nikolski share the Hardy factorization,
boundary, interpolation, and invariant-subspace core. Nikolski, Peller,
Böttcher–Silbermann, and the model-space books connect it with Toeplitz,
Hankel, and compressed-shift operators. Cima–Matheson–Ross treat Cauchy
transforms and Clark measures, and Conway's *The Theory of Subnormal
Operators* the function theory of subnormal operators. Fricain–Mashreghi provides a
large overlapping development before treating $\mathcal H(b)$ itself.
Hedenmalm–Korenblum–Zhu, Duren–Schuster, and Zhu develop the Bergman
counterparts; the Dirichlet references explain why capacity and multiplier
norms change the picture. Cowen–MacCluer and Shapiro supply composition
operator criteria, while Zhu's Fock-space book connects planar density
with the same reproducing-kernel methods. The several-variable extensions
are reserved for Section 45.

Local full-text sources consulted:

* [Garnett, *Bounded Analytic Functions*](References/Garnett2007BoundedAnalyticFunctionsRev1stEd-SpringerGTM.pdf).
* [Koosis, *Introduction to $H_p$ Spaces*](References/Koosis1999IntroductionHpSpaces2ndEd-CambridgeTractsMath115.pdf).
* [Nikolski, *Hardy Spaces*](References/Nikolski2019HardySpaces-Cambridge.pdf).
* [Fricain–Mashreghi, *The Theory of $\mathcal H(b)$ Spaces I*](References/FricainMashreghi2016TheoryHbSpacesVol1-Cambridge.NMM20.pdf) and [Volume II](References/FricainMashreghi2016TheoryHbSpacesVol2-Cambridge.NMM21.pdf).
* [Zhu, *Spaces of Holomorphic Functions in the Unit Ball*](References/Zhu2005SpacesHolomorphicFunctionsUnitBall-SpringerGTM226.pdf), specialized here to the disk.
* [Zhu, *Analysis on Fock Spaces*](References/Zhu2012AnalysisOnFockSpaces-SpringerGTM263.pdf).
* [El-Fallah–Kellay–Mashreghi–Ransford, *A Primer on the Dirichlet Space*](References/ElFallahKellayMashreghiRansford2014PrimerDirichletSpace-Cambridge.TractsMath203.pdf).
* [Paulsen–Raghupathi, *An Introduction to the Theory of Reproducing Kernel Hilbert Spaces*](References/PaulsenRaghupathi2016IntroductionTheoryReproducingKernelHilbertSpaces-CambridgeStudiesAM152.pdf).
* [Krantz, *Geometric Analysis of the Bergman Kernel and Metric*](References/Krantz2013GeometricAnalysisBergmanKernalMetric-SpringerGTM.pdf).
