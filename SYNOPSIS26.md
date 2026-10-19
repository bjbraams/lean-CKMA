# Synopsis: Sobolev spaces, smoothness scales, and interpolation

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-26);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects the recurring core of Section 26 of
[CKMA-bib.md](CKMA-bib.md#ckma-26). It treats
weak derivatives, extension and traces, compactness and capacity, fractional
smoothness, dyadic scales, interpolation, and the principal generalized
integrability spaces. Inequalities also appearing in Sections 11 and 14 are
retained as statements about spaces and mappings. Domain regularity and
endpoint restrictions are part of each assertion.

For open $\Omega\subset\mathbb R^d$, $W^{m,p}(\Omega)$ consists of
$L^p$ functions with distributional derivatives through integer order $m$
in $L^p$. The norm sums those derivative norms; $H^m=W^{m,2}$.
$W_0^{m,p}$ is the closure of $C_c^\infty(\Omega)$.
Unless specified otherwise $1\leq p<\infty$; statements using duality,
Bessel potentials, or singular-integral characterizations usually assume
$1<p<\infty$ explicitly. Spaces are inhomogeneous unless marked otherwise.

## Weak derivatives and approximation

* **1. Completeness and reflexivity.** $W^{m,p}$ is Banach, separable
  for $p<\infty$, and reflexive for $1<p<\infty$. With its standard
  quadratic norm, $H^m$ is Hilbert.
* **2. Uniqueness and distributional closedness.** Weak derivatives are
  unique almost everywhere. If $u_n\to u$ in $L^p$ and each
  $\partial^\alpha u_n\to v_\alpha$ in $L^p$, then
  $\partial^\alpha u=v_\alpha$; the derivative maps are closed.
* **3. Meyers–Serrin density.** For every open $\Omega$ and finite $p$,
  $C^\infty(\Omega)\cap W^{m,p}(\Omega)$ is dense in $W^{m,p}$.
  Smoothness up to the boundary and compact support require additional
  geometric or boundary conditions.
* **4. Mollification.** Interior mollifications converge in $W^{m,p}$
  on relatively compact subdomains, and derivatives commute with convolution.
  On all of $\mathbb R^d$, cutoffs followed by mollification approximate
  every $W^{m,p}$ function by compactly supported smooth functions.
* **6. One-dimensional characterization.** On a bounded interval,
  $W^{1,p}$ functions have absolutely continuous representatives and
  $u(t)=u(a)+\int_a^tu'(s)ds$. Conversely an absolutely continuous
  function with derivative in $L^p$ belongs to $W^{1,p}$.
* **7. Chain rule.** If $F\in C^1(\mathbb R)$ has bounded derivative
  and $F(0)=0$, then $F(u)\in W^{1,p}$ and
  $\nabla F(u)=F'(u)\nabla u$. On finite-measure domains the condition
  $F(0)=0$ may be dropped. Lipschitz $F$ has the corresponding
  almost-everywhere chain rule.
* **8. Truncation and level sets.** Positive parts, absolute values, and
  bounded truncations preserve $W^{1,p}$; for example
  $\nabla u^+=1_{\{u>0\}}\nabla u$. The weak gradient vanishes
  almost everywhere on every fixed level set $\{u=c\}$.
* **9. Product rule.** Bounded $W^{1,p}$ functions form an algebra,
  with $\nabla(uv)=u\nabla v+v\nabla u$. More general product rules
  follow when the displayed terms have the required integrability.
* **10. Bi-Lipschitz change of variables.** A bi-Lipschitz map between
  domains induces bounded isomorphisms of $W^{1,p}$ spaces by composition,
  with the almost-everywhere derivative chain rule. Higher orders require
  corresponding higher regularity of the map and its inverse.
* **11. Difference quotients and Lipschitz functions.** For
  $1<p\leq\infty$, $u\in L^p(\mathbb R^d)$ lies in $W^{1,p}$ exactly
  when $\|u(\cdot+h)-u\|_p\leq C|h|$ for all $h$, and then
  $C=\|\nabla u\|_p$ is admissible. In
  particular $W^{1,\infty}_{\rm loc}$ consists of the locally Lipschitz
  functions, which are differentiable almost everywhere (Rademacher).
  For $p=1$ the difference condition characterizes $BV$ instead, the
  $L^1$ functions whose distributional gradient is a finite Radon measure
  (Section 37).
* **12. Dual representation.** For $1<p<\infty$, every functional on
  $W_0^{m,p}(\Omega)$ is
  $u\mapsto\sum_{|\alpha|\leq m}\int f_\alpha\partial^\alpha u$
  for some $f_\alpha\in L^{p'}$. Its distributional form is a sum
  of derivatives of $L^{p'}$ functions, defining $W^{-m,p'}$.
* **13. Extension theorem.** On a bounded Lipschitz domain there is a
  bounded linear extension $W^{m,p}(\Omega)\to W^{m,p}(\mathbb R^d)$
  for each nonnegative integer $m$, including $p=1,\infty$.
  Consequently restrictions of globally smooth functions are dense for finite $p$.

## Embeddings, norm inequalities, and compactness

* **14. Sobolev embedding.** For $1\leq p<d$,
  $W^{1,p}(\mathbb R^d)\hookrightarrow L^{p^*}$,
  $p^*=dp/(d-p)$, with $\|u\|_{p^*}\leq C\|\nabla u\|_p$.
  Bounded Lipschitz domains have the corresponding inhomogeneous estimate.
* **15. Higher-order Sobolev embedding.** If $mp<d$,
  $W^{m,p}(\mathbb R^d)\hookrightarrow L^{dp/(d-mp)}$.
  More generally $W^{m,p}\hookrightarrow W^{k,q}$ when
  $1/q=1/p-(m-k)/d>0$ in the usual finite-exponent range.
* **16. Critical embedding.** On bounded Lipschitz domains,
  $W^{1,d}\hookrightarrow L^q$ for every finite $q$.
  For $d\geq2$ it does not embed into $L^\infty$; the endpoint
  exponential integrability is Trudinger's Orlicz embedding (81), with
  the sharp Moser constant in SYNOPSIS14, item 8.
* **17. Morrey embedding.** If $p>d$, then
  $W^{1,p}(\Omega)\hookrightarrow C^{0,1-d/p}(\overline\Omega)$
  on bounded Lipschitz domains. Higher-order versions apply after
  differentiating when the remaining Sobolev order exceeds $d/p$.
  For compactly supported functions on $\mathbb R^d$ the Hölder seminorm
  is bounded by $C\|\nabla u\|_p$.
* **18. Rellich–Kondrachov compactness.** On bounded Lipschitz domains,
  $W^{1,p}\hookrightarrow L^q$ is compact for $q<p^*$ when $p<d$,
  and for every finite $q$ when $p=d$. For $p>d$ it is compact into
  $C^{0,\beta}$ for $0\leq\beta<1-d/p$.
* **19. Poincaré inequalities.** On bounded connected Lipschitz domains,
  $\|u-u_\Omega\|_p\leq C\|\nabla u\|_p$.
  On $W_0^{1,p}$, $\|u\|_p\leq C\|\nabla u\|_p$ for every bounded
  open $\Omega$. Connectedness is essential for the mean-value form. For
  $u\in W_0^{1,p}(\Omega)$ the bound $\|u\|_p\leq C\|\nabla u\|_p$ holds
  on any open set of finite measure, indeed on any open set bounded in one
  direction, with no regularity or connectedness.
* **20. Lorentz refinement.** For $1<p<d$,
  $\|u\|_{L^{p^*,p}(\mathbb R^d)}\leq C\|\nabla u\|_p$, with the
  Lorentz spaces $L^{p,q}$ of 60.
  At $p=1$, $W^{1,1}$ embeds into $L^{d/(d-1),1}$ for $d>1$.
* **21. Gagliardo–Nirenberg inequality.** For $1\leq p<d$,
  $1\leq r\leq q\leq p^*$ and
  $1/q=\theta(1/p-1/d)+(1-\theta)/r$,
  $\|u\|_q\leq C\|\nabla u\|_p^\theta\|u\|_r^{1-\theta}$
  for smooth compactly supported $u$, and by density wherever the norms are finite.
  Higher-derivative versions extend this interpolation between smoothness
  and integrability under the corresponding scaling restrictions.
* **22. Sobolev algebra theorem.** For integer $m$ and $mp>d$,
  $W^{m,p}(\mathbb R^d)$ is a Banach algebra under pointwise
  multiplication, up to an equivalent norm; the same holds on bounded
  extension domains.
* **23. Fréchet–Kolmogorov criterion.** A bounded subset of
  $L^p(\mathbb R^d)$, $p<\infty$, is relatively compact exactly when
  translations tend uniformly to zero in norm and its $L^p$ mass is
  uniformly small outside large balls.
* **75. Ehrling–Lions lemma and Aubin–Lions compactness.** Let $X,Y,Z$ be
  Banach spaces with $X$ compactly embedded in $Y$ and $Y$ continuously
  embedded in $Z$. For every $\varepsilon>0$ there is $C_\varepsilon$ with
  $\|u\|_Y\leq\varepsilon\|u\|_X+C_\varepsilon\|u\|_Z$ for $u\in X$;
  for example $\|u\|_{W^{1,p}}\leq\varepsilon\|u\|_{W^{2,p}}+
  C_\varepsilon\|u\|_p$ on bounded Lipschitz domains. For $1\leq q<\infty$,
  a set of functions bounded in $L^q(0,T;X)$ whose time derivatives are
  bounded in $L^1(0,T;Z)$ is relatively compact in $L^q(0,T;Y)$
  (Aubin–Lions; Simon).

## Traces and zero boundary values

* **24. First-order trace theorem.** For bounded Lipschitz $\Omega$ and
  $1<p<\infty$, restriction extends to a bounded surjection
  $W^{1,p}(\Omega)\to B^{1-1/p}_{p,p}(\partial\Omega)$ with a bounded
  linear right inverse. For $p=2$ the range is $H^{1/2}$. For $p=1$ the
  trace maps $W^{1,1}(\Omega)$ onto $L^1(\partial\Omega)$ (Gagliardo), but
  no bounded linear right inverse exists (Peetre).
* **25. Higher traces on smooth boundaries.** On bounded smooth domains,
  the normal traces $\partial_n^ju$, $0\leq j<m$, map $W^{m,p}$
  boundedly to $B^{m-j-1/p}_{p,p}(\partial\Omega)$ for $1<p<\infty$.
  The joint normal-jet map has a bounded right inverse.
* **26. Kernel of the trace.** For bounded Lipschitz domains,
  $W_0^{1,p}=\ker\gamma$ for $1\leq p<\infty$. On smooth domains,
  $W_0^{m,p}$ is characterized by vanishing of all normal traces
  of orders $0,\ldots,m-1$.
* **27. Zero extension.** If $u\in W_0^{m,p}(\Omega)$, extension by
  zero belongs to $W^{m,p}(\mathbb R^d)$ and commutes with weak
  derivatives. For first order on bounded Lipschitz domains, the converse
  holds for $1\leq p<\infty$.
* **28. Green formula with traces.** On bounded Lipschitz domains,
  $\int_\Omega(u\partial_jv+v\partial_ju)=
  \int_{\partial\Omega}\gamma u\,\gamma v\,n_j$
  for $u\in W^{1,p}$, $v\in W^{1,p'}$, $1<p<\infty$.
* **29. Trace Sobolev exponent.** For bounded Lipschitz $\Omega$ and $1<p<d$,
  $W^{1,p}(\Omega)\hookrightarrow L^{p(d-1)/(d-p)}(\partial\Omega)$.
  The trace embedding is compact at smaller finite exponents.
  On the half-space the homogeneous form
  $\|u(\cdot,0)\|_{L^{p(d-1)/(d-p)}(\mathbb R^{d-1})}\leq
  C\|\nabla u\|_{L^p(\mathbb R^d_+)}$ holds for smooth functions
  compactly supported up to the boundary.
* **30. Hardy inequality.** For bounded Lipschitz $\Omega$ and
  $1<p<\infty$, $\|u/\operatorname{dist}(\cdot,\partial\Omega)\|_p
  \leq C\|\nabla u\|_p$ for $u\in W_0^{1,p}(\Omega)$. On a half-space
  or a convex domain the sharp constant is $p/(p-1)$.
* **76. Negative-order spaces and zero boundary values.** For open
  $\Omega$ and $s\geq0$, $H^s_0(\Omega)$ is the closure of
  $C_c^\infty(\Omega)$ in $H^s(\Omega)$ (restrictions of $H^{s,2}$
  functions) and $H^{-s}(\Omega)$ is its dual; with $L^2$ as pivot,
  $H^s_0\hookrightarrow L^2\hookrightarrow H^{-s}$ densely, and for integer
  $s$ this agrees with 12. On bounded Lipschitz domains
  $C_c^\infty(\Omega)$ is dense in $H^s(\Omega)$ exactly when
  $s\leq1/2$, so then $H^s_0=H^s$, and for $0\leq s<1/2$ extension by zero
  is bounded $H^s(\Omega)\to H^s(\mathbb R^d)$. On smooth domains, for
  $s>1/2$ with $s-1/2$ not an integer, $H^s_0(\Omega)$ consists of the
  $u\in H^s$ with $\partial_n^ju=0$ on $\partial\Omega$ for
  $0\leq j<s-1/2$ (Lions–Magenes).
* **77. Lions–Magenes space and interpolation of $H^s_0$.** On a bounded
  smooth domain, $[L^2(\Omega),H_0^1(\Omega)]_\theta=
  (L^2(\Omega),H_0^1(\Omega))_{\theta,2}$ equals $H^\theta(\Omega)$ for
  $0<\theta<1/2$ and $H^\theta_0(\Omega)$ for $1/2<\theta<1$. At
  $\theta=1/2$ it is
  $H^{1/2}_{00}(\Omega)=\{u\in H^{1/2}(\Omega):\rho^{-1/2}u\in L^2(\Omega)\}$,
  $\rho=\operatorname{dist}(\cdot,\partial\Omega)$, normed by
  $(\|u\|_{H^{1/2}}^2+\|\rho^{-1/2}u\|_2^2)^{1/2}$. Equivalently it consists
  of the $u$ whose extension by zero lies in $H^{1/2}(\mathbb R^d)$. It is
  dense in $H^{1/2}(\Omega)=H^{1/2}_0(\Omega)$ with a strictly stronger
  norm. For a smooth relatively open piece $\Gamma_0$ of $\partial\Omega$,
  $H^{1/2}_{00}(\Gamma_0)$ is the space of traces on $\Gamma_0$ of $H^1$
  functions vanishing on $\partial\Omega\setminus\overline{\Gamma_0}$, the
  data space of mixed boundary problems.

## Capacity and fine representatives

For $1<p<\infty$, **Sobolev capacity** $C_{1,p}(E)$ is the outer
capacity generated by the infimum of $\|v\|_{W^{1,p}(\mathbb R^d)}^p$
over smooth functions at least one near a compact set. A property holds
**quasi-everywhere** if its exceptional set has zero capacity.

* **31. Quasicontinuity.** Every $W^{1,p}(\mathbb R^d)$ function has
  a representative continuous outside an open set of arbitrarily small
  $C_{1,p}$ capacity. This representative is unique quasi-everywhere.
  With $C_{1,1}$ defined in the same way, this holds also for $p=1$.
* **32. Capacitary convergence.** From convergence in $W^{1,p}$ one
  can extract a subsequence of quasicontinuous representatives converging
  pointwise quasi-everywhere.
* **33. Havin–Bagby zero boundary criterion.** For any open
  $\Omega$, $u\in W_0^{1,p}(\Omega)$ exactly when it is the restriction
  of a global $W^{1,p}$ function whose quasicontinuous representative
  vanishes quasi-everywhere on $\mathbb R^d\setminus\Omega$.
* **35. Lusin approximation.** On a bounded Lipschitz domain, a Sobolev
  function with finite $p$ can be approximated in $W^{1,p}$ by Lipschitz
  functions agreeing with it outside sets whose measure tends to zero.

## Fractional Sobolev spaces and nonlocal energies

For $0<s<1$ and finite $p$, define
$$[u]_{W^{s,p}(\Omega)}^p=
  \iint_{\Omega\times\Omega}\frac{|u(x)-u(y)|^p}{|x-y|^{d+sp}}dxdy,$$
with norm $\|u\|_p+[u]_{W^{s,p}}$. The Bessel potential space
$H^{s,p}(\mathbb R^d)$ is defined by
$\|(I-\Delta)^{s/2}u\|_p<\infty$ through tempered distributions.

* **36. Completeness and density.** $W^{s,p}$ is Banach and is reflexive
  for $1<p<\infty$. Smooth compactly supported functions are dense
  in $W^{s,p}(\mathbb R^d)$ for finite $p$.
* **37. Fractional Hilbert identity.** $W^{s,2}(\mathbb R^d)=H^{s,2}$
  with equivalent norms; the Gagliardo energy equals a positive constant
  times $\int|\xi|^{2s}|\widehat u(\xi)|^2d\xi$.
* **38. Fractional Laplacian formula.** For Schwartz $u$ and $0<s<1$,
  $(-\Delta)^su(x)=c_{d,s}\operatorname{p.v.}\int
  (u(x)-u(y))/|x-y|^{d+2s}\,dy$, with the positive normalization
  giving Fourier symbol $|\xi|^{2s}$. Its quadratic energy is
  $c_{d,s}[u]_{W^{s,2}}^2/2$.
* **39. Fractional Sobolev embedding.** If $sp<d$,
  $W^{s,p}(\mathbb R^d)\hookrightarrow L^{dp/(d-sp)}$;
  if $sp>d$, it embeds into $C^{0,s-d/p}$.
  Bounded Lipschitz domains have the corresponding extension and embedding results.
* **40. Fractional compactness.** On bounded Lipschitz domains,
  $W^{s,p}\hookrightarrow L^q$ is compact for $q<dp/(d-sp)$
  when $sp<d$, and for every finite $q$ when $sp\geq d$.
* **41. Nonlocal Poincaré inequality.** For bounded connected Lipschitz
  $\Omega$, $\|u-u_\Omega\|_p\leq C[u]_{W^{s,p}(\Omega)}$.
  For globally defined functions vanishing outside a fixed bounded domain,
  the full-space Gagliardo seminorm controls the $L^p$ norm.
* **42. Bourgain–Brezis–Mironescu limit.** For $u\in W^{1,p}(\mathbb R^d)$,
  $$\lim_{s\uparrow1}(1-s)[u]_{W^{s,p}}^p
     =\frac1p\left(\int_{S^{d-1}}|\omega_1|^pd\omega\right)
                       \int|\nabla u|^p.$$
  Conversely, for $1<p<\infty$, $u\in L^p$ with finite
  $\liminf_{s\uparrow1}(1-s)[u]_{W^{s,p}}^p$ belongs to $W^{1,p}$; for
  $p=1$ the same condition characterizes $BV$ (Dávila).

## Besov and Triebel–Lizorkin scales

Choose a smooth inhomogeneous dyadic partition $(\varphi_j)_{j\geq0}$
in frequency and set $\Delta_ju=\mathcal F^{-1}(\varphi_j\widehat u)$.
The **Besov norm** is
$\|u\|_{B^s_{p,q}}=\|(2^{js}\|\Delta_ju\|_p)_j\|_{\ell^q}$;
the **Triebel–Lizorkin norm** is
$\|u\|_{F^s_{p,q}}=\|(\sum_j|2^{js}\Delta_ju|^q)^{1/q}\|_p$.
Use the supremum for $q=\infty$. Below Besov parameters are at least one,
and Triebel–Lizorkin assertions use $1<p<\infty$, unless otherwise stated.

* **43. Dyadic norm independence.** Different admissible dyadic partitions
  give equivalent norms and the same spaces. For real $s$, the indicated
  Banach ranges are complete spaces of tempered distributions.
* **45. Difference characterization.** For $0<s<1$ and finite $p$,
  $W^{s,p}=B^s_{p,p}$. More generally differences of integer order
  $m>s>0$, integrated against $|h|^{-sq-d}dh$, characterize
  $B^s_{p,q}$, with the usual supremum for $q=\infty$.
* **46. Bessel and Sobolev identifications.**
  $H^{s,p}=F^s_{p,2}$ for real $s$ and $1<p<\infty$;
  for nonnegative integer $m$, $W^{m,p}=H^{m,p}$.
  For $p\ne2$, fractional Gagliardo and Bessel spaces need not coincide.
* **47. Hölder–Zygmund identification.** For positive noninteger $s$,
  $B^s_{\infty,\infty}$ is the bounded Hölder space $C^s$.
  At positive integers it is the Zygmund class, which is larger than
  the corresponding bounded classical differentiability class.
* **48. Lifting isomorphism.** $(I-\Delta)^{t/2}$ maps
  $B^s_{p,q}$ isomorphically onto $B^{s-t}_{p,q}$ and
  $F^s_{p,q}$ onto $F^{s-t}_{p,q}$ in the indicated ranges.
* **49. Fine-index embeddings.** If $q_0\leq q_1$, then
  $B^s_{p,q_0}\hookrightarrow B^s_{p,q_1}$ and
  $F^s_{p,q_0}\hookrightarrow F^s_{p,q_1}$. Also
  $B^s_{p,\min(p,q)}\hookrightarrow F^s_{p,q}
  \hookrightarrow B^s_{p,\max(p,q)}$.
* **50. Sobolev-index embedding.** If $p_0\leq p_1$ and
  $s_0-d/p_0=s_1-d/p_1$, then
  $B^{s_0}_{p_0,q}\hookrightarrow B^{s_1}_{p_1,q}$.
  In particular $s>d/p$ gives continuous bounded representatives.
* **51. Besov trace.** For $1<p,q<\infty$ and $s>1/p$, restriction
  to a hyperplane is a bounded surjection
  $B^s_{p,q}(\mathbb R^d)\to B^{s-1/p}_{p,q}(\mathbb R^{d-1})$
  with a bounded right inverse. For $F^s_{p,q}$ the trace range is
  $B^{s-1/p}_{p,p}$.
* **52. Besov algebra theorem.** $B^s_{p,q}\cap L^\infty$ satisfies
  a product estimate controlled by the two $L^\infty$ norms and Besov
  norms when $s>0$. Hence $B^s_{p,q}$ is an algebra for $s>d/p$,
  and at $s=d/p>0$ when $q=1$.
* **78. Endpoint Triebel–Lizorkin identifications.** With the
  quasi-Banach range $0<p<\infty$ allowed, $F^0_{p,2}=h^p$, Goldberg's
  local Hardy space, with equivalent quasinorms; thus $F^0_{p,2}=L^p$ for
  $1<p<\infty$ (Littlewood–Paley), while $F^0_{1,2}=h^1$ is strictly smaller
  than $L^1$. With $F^s_{\infty,q}$ defined by the Carleson-type
  modification of the norm (Frazier–Jawerth), $F^0_{\infty,2}=\mathrm{bmo}$,
  the dual of $h^1$. The homogeneous versions give $H^p$ and BMO
  (Section 27).

## Real and complex interpolation

A **Banach couple** $(X_0,X_1)$ embeds both spaces into one Hausdorff
vector space. Define
$K(t,x)=\inf_{x=x_0+x_1}(\|x_0\|_{X_0}+t\|x_1\|_{X_1})$.
The **real interpolation space** $(X_0,X_1)_{\theta,q}$ has norm
$\|t^{-\theta}K(t,x)\|_{L^q(\mathbb R_+,dt/t)}$.
The **complex interpolation space** $[X_0,X_1]_\theta$ consists of
values at $\theta$ of bounded analytic strip functions with boundary
values in $X_0$ and $X_1$, with the infimum boundary norm.

* **53. Real interpolation theorem.** An operator bounded
  $X_i\to Y_i$ with norms $M_i$ acts boundedly between the real
  interpolation spaces with bound at most $M_0^{1-\theta}M_1^\theta$.
* **54. Complex interpolation theorem.** The same operator bound holds
  between complex interpolation spaces, by the three-lines theorem.
* **55. K–J equivalence.** Real interpolation can equivalently be
  described by representations $x=\int_0^\infty u(t)dt/t$,
  $u(t)\in X_0\cap X_1$, controlling
  $t^{-\theta}\max(\|u(t)\|_{X_0},t\|u(t)\|_{X_1})$ in $L^q(dt/t)$.
* **56. Reiteration theorem.** For $0<\theta_0<\theta_1<1$,
  $0<\eta<1$, and admissible $q,q_0,q_1$,
  $$((X_0,X_1)_{\theta_0,q_0},(X_0,X_1)_{\theta_1,q_1})_{\eta,q}
       =(X_0,X_1)_{(1-\eta)\theta_0+\eta\theta_1,q}$$
  with equivalent norms.
* **57. Real interpolation duality.** If $X_0\cap X_1$ is dense in
  both endpoints and $1\leq q<\infty$, then
  $((X_0,X_1)_{\theta,q})^*=(X_0^*,X_1^*)_{\theta,q'}$
  with equivalent norms under the natural pairing.
* **58. Riesz–Thorin theorem.** Bounds $T:L^{p_i}\to L^{q_i}$
  interpolate with reciprocal exponents affine in $\theta$ and norm
  at most $M_0^{1-\theta}M_1^\theta$, including the standard infinite
  endpoint exponents. This constant requires complex scalars; for real
  scalars and $p_i>q_i$ it can fail, and $2M_0^{1-\theta}M_1^\theta$ holds.
  Precisely: for complex $L^p$ spaces on $\sigma$-finite measure spaces and
  a linear operator $T$ on $L^{p_0}+L^{p_1}$ with
  $\|Tf\|_{q_j}\leq M_j\|f\|_{p_j}$, $j=0,1$, exponents in $[1,\infty]$,
  $0<\theta<1$, $p_\theta^{-1}=(1-\theta)p_0^{-1}+\theta p_1^{-1}$ and
  $q_\theta^{-1}=(1-\theta)q_0^{-1}+\theta q_1^{-1}$, one has
  $\|Tf\|_{q_\theta}\leq M_0^{1-\theta}M_1^\theta\|f\|_{p_\theta}$.
* **59. Marcinkiewicz interpolation.** A sublinear operator of weak
  types $(p_0,p_0)$ and $(p_1,p_1)$, $1\leq p_0<p_1\leq\infty$,
  is strongly bounded on $L^p$ for $p_0<p<p_1$; weak type $(\infty,\infty)$
  means boundedness on $L^\infty$. Constants depend only on the exponents
  and endpoint bounds. In particular weak type $(1,1)$ together with
  boundedness on $L^\infty$ gives strong type $(p,p)$ for every $1<p<\infty$.
* **60. Lorentz interpolation.** For $1\leq p_0<p_1\leq\infty$,
  $(L^{p_0},L^{p_1})_{\theta,q}=L^{p,q}$,
  $1/p=(1-\theta)/p_0+\theta/p_1$. Here
  $\|f\|_{p,q}$ is equivalent to
  $\|t^{1/p}f^*(t)\|_{L^q(dt/t)}$, with $f^*$ the decreasing rearrangement.
* **61. Complex $L^p$ interpolation.**
  $[L^{p_0},L^{p_1}]_\theta=L^p$ with reciprocal exponents as above
  on a $\sigma$-finite measure space, for $1\leq p_0,p_1\leq\infty$.
* **62. Bessel potential interpolation.** For $1<p<\infty$,
  $[H^{s_0,p},H^{s_1,p}]_\theta=H^{(1-\theta)s_0+\theta s_1,p}$.
  Extension and restriction transfer the usual smooth-domain versions.
* **63. Sobolev real interpolation.** For integers $0\leq m_0<m_1$,
  $1<p<\infty$, and $s=(1-\theta)m_0+\theta m_1$,
  $(W^{m_0,p},W^{m_1,p})_{\theta,q}=B^s_{p,q}$ on $\mathbb R^d$.
  This remains a Besov statement when $s$ is an integer.
* **64. Besov reiteration in smoothness.** For $s_0<s_1$,
  $(B^{s_0}_{p,q_0},B^{s_1}_{p,q_1})_{\theta,q}
  =B^{(1-\theta)s_0+\theta s_1}_{p,q}$ with equivalent norms.
* **65. Real interpolation of compactness.** If $T:X_0\to Y_0$ is
  compact and $T:X_1\to Y_1$ bounded, it is compact between the
  corresponding real interpolation spaces for $0<\theta<1$,
  $1\leq q<\infty$. Lions and Peetre proved this when the two source
  spaces or the two target spaces coincide; the general case is Cwikel's.
* **79. Stein's interpolation of analytic families.** Let $T_z$,
  $0\leq\operatorname{Re}z\leq1$, be linear maps from simple functions on a
  $\sigma$-finite space to measurable functions on another, such that for
  simple $f,g$ the function $z\mapsto\int(T_zf)g$ is continuous on the
  closed strip, holomorphic inside, and of admissible growth
  $\log|\int(T_zf)g|\leq Ce^{a|\operatorname{Im}z|}$ with $a<\pi$.
  If $\|T_{it}f\|_{q_0}\leq M_0(t)\|f\|_{p_0}$ and
  $\|T_{1+it}f\|_{q_1}\leq M_1(t)\|f\|_{p_1}$ with
  $\log M_j(t)\leq Ce^{b|t|}$, $b<\pi$, then
  $\|T_\theta f\|_{q_\theta}\leq M_\theta\|f\|_{p_\theta}$ for
  $0<\theta<1$, exponents as in 58, with $M_\theta$ depending only on
  $\theta$ and $M_0,M_1$ (Stein). It handles fractional integrals and
  Bochner–Riesz and restriction endpoints.
* **80. Complex reiteration and duality.** If $X_0\cap X_1$ is dense in
  $X_0$ and $X_1$, then for $0\leq\theta_0,\theta_1\leq1$ and $0<\eta<1$,
  $[[X_0,X_1]_{\theta_0},[X_0,X_1]_{\theta_1}]_\eta
  =[X_0,X_1]_{(1-\eta)\theta_0+\eta\theta_1}$ with equivalent norms; if in
  addition $X_0$ or $X_1$ is reflexive, $[X_0,X_1]_\theta^*
  =[X_0^*,X_1^*]_\theta$ with equal norms (Calderón). For
  $\theta_0\neq\theta_1$, real interpolation between complex
  interpolation spaces gives
  $([X_0,X_1]_{\theta_0},[X_0,X_1]_{\theta_1})_{\eta,q}
  =(X_0,X_1)_{(1-\eta)\theta_0+\eta\theta_1,q}$.

## Orlicz and variable-exponent spaces

A **Young function** is a convex increasing function on $[0,\infty)$
with $\Phi(0)=0$ and $\Phi(t)\to\infty$. An **N-function** is positive
for $t>0$ and additionally
satisfies $\Phi(t)/t\to0$ at zero and $\Phi(t)/t\to\infty$ at infinity.
For a Young function $\Phi$, the **Luxemburg norm** is
$\|f\|_\Phi=\inf\{\lambda>0:\int\Phi(|f|/\lambda)\leq1\}$.
Its complementary function is $\Psi(s)=\sup_{t\geq0}(st-\Phi(t))$.
For measurable $1\leq p(x)<\infty$, **variable Lebesgue space** $L^{p(\cdot)}$ uses
the modular $\rho(f)=\int|f(x)|^{p(x)}dx$ and its Luxemburg norm.
Write $p_-=\operatorname{ess\,inf}p$, $p_+=\operatorname{ess\,sup}p$.

* **66. Orlicz completeness and Hölder inequality.** $L^\Phi$ is Banach,
  and $\int|fg|\leq2\|f\|_\Phi\|g\|_\Psi$.
  Its Köthe associate is $L^\Psi$ with the equivalent Orlicz dual norm.
* **67. Growth conditions and reflexivity.** If complementary N-functions
  $\Phi,\Psi$ both satisfy the global doubling condition
  $\Phi(2t)\leq C\Phi(t)$ and its counterpart for $\Psi$, then their
  Orlicz spaces are reflexive and the usual integral duality gives their
  full Banach duals. Without such growth conditions singular functionals
  may occur.
* **68. Variable-exponent duality.** If $1<p_-\leq p_+<\infty$,
  $L^{p(\cdot)}$ is separable and reflexive, with dual
  $L^{p'(\cdot)}$ under integration, up to equivalent norms.
  The variable Hölder bound holds with constant at most two.
* **69. Norm–modular comparison.** For $p_+<\infty$,
  $$\min(\|f\|^{p_-},\|f\|^{p_+})\leq\rho(f)
       \leq\max(\|f\|^{p_-},\|f\|^{p_+}),$$
  with the variable Lebesgue norm. Thus convergence in norm and
  convergence of the difference modular to zero are equivalent.
* **70. Variable maximal theorem.** If $1<p_-\leq p_+<\infty$ and
  $p$ is globally log-Hölder continuous, the Hardy–Littlewood maximal
  operator is bounded on $L^{p(\cdot)}(\mathbb R^d)$. The condition
  controls $|p(x)-p(y)|$ by $C/\log(e+1/|x-y|)$ locally and
  $|p(x)-p_\infty|$ by $C/\log(e+|x|)$ at infinity.
* **71. Variable Sobolev embedding.** On a bounded Lipschitz domain,
  for log-Hölder $p$ with $1<p_-\leq p_+<d$,
  $W^{1,p(\cdot)}\hookrightarrow L^{p^*(\cdot)}$,
  where $p^*(x)=dp(x)/(d-p(x))$. Uniformly subcritical continuous
  target exponents give compact embeddings.
* **72. Variable smooth density.** Under these log-Hölder assumptions,
  smooth functions are dense in $W^{1,p(\cdot)}$ on a Lipschitz
  domain, and compactly supported smooth functions generate its
  zero-boundary space. Arbitrary measurable exponents need not admit
  the same density and approximation properties.
* **81. Trudinger's Orlicz embedding.** For bounded $\Omega\subset\mathbb R^d$,
  $d\geq2$, $W_0^{1,d}(\Omega)$ embeds continuously into the Orlicz space
  $L^\Phi(\Omega)$ with $\Phi(t)=\exp(t^{d/(d-1)})-1$, and on bounded
  Lipschitz domains so does $W^{1,d}(\Omega)$. Among Orlicz spaces this
  target is optimal (Trudinger). Moser's sharp exponential constant is in
  SYNOPSIS14, item 8.

## Morrey and Campanato descriptions

The **Morrey norm** on $\mathbb R^d$ is
$\sup_{B(x,r)}r^{-\lambda/p}(\int_{B(x,r)}|f|^p)^{1/p}$,
$0\leq\lambda\leq d$; the **Morrey space** $\mathcal M^p_\lambda$ consists of
the $f$ for which it is finite, so $\mathcal M^p_0=L^p$ and
$\mathcal M^p_d=L^\infty$. A **Campanato seminorm** measures oscillation:
$\sup_{B(x,r)}r^{-\alpha}(\fint_{B(x,r)}|f-f_B|^p)^{1/p}$.
These spaces describe local size and oscillation separately from ordinary
global integrability.

* **73. Campanato–Hölder equivalence.** For $0<\alpha<1$ and finite
  $p\geq1$, finiteness of the Campanato seminorm is equivalent, modulo
  constants and almost-everywhere representatives, to $\alpha$-Hölder
  continuity. The seminorms are equivalent.
* **74. BMO endpoint.** At $\alpha=0$, the Campanato seminorms for all
  finite $p\geq1$ are equivalent to the BMO seminorm, by the
  John–Nirenberg exponential-integrability theorem.
* **82. Morrey's Dirichlet growth theorem.** Let $u\in W^{1,1}(\Omega)$
  and $0<\alpha\leq1$. If $\int_{B_r}|\nabla u|\leq Kr^{d-1+\alpha}$ for
  every ball $B_r\subset\Omega$, then $u\in C^{0,\alpha}(\Omega)$ and
  $\operatorname{osc}_{B_r}u\leq C(d,\alpha)Kr^\alpha$ for such balls. By
  Hölder's inequality the hypothesis follows from
  $\int_{B_r}|\nabla u|^p\leq K^pr^{d-p+\alpha p}$, that is, from
  $\nabla u\in\mathcal M^p_{d-p+\alpha p}$; this is the route from
  Caccioppoli-type decay estimates to Hölder regularity.
* **83. Adams' Riesz potential theorem.** For $0<\alpha<d$,
  $0\leq\lambda<d$, and $1<p<(d-\lambda)/\alpha$, the Riesz potential
  $I_\alpha f(x)=\int f(y)|x-y|^{\alpha-d}dy$ maps
  $\mathcal M^p_\lambda$ boundedly into $\mathcal M^q_\lambda$ with
  $1/q=1/p-\alpha/(d-\lambda)$ (Adams). For $\lambda=0$ this is the
  Hardy–Littlewood–Sobolev theorem. It improves the integrability gain of
  the earlier Spanne–Peetre estimate.

## Reference guide

Leoni provides weak derivatives, approximation, embeddings, traces,
interpolation, and Besov spaces in one development. Brezis and Tartar
independently cover the Sobolev and interpolation foundation; Maz'ya
supplies the capacity and fine-property viewpoint. Lunardi gives the
abstract interpolation and trace methods. Triebel and Sawano develop the
dyadic scales, lifting, differences, and sharp parameter distinctions.
Adams (*Morrey Spaces*) and Sawano–Di Fazio–Hakim develop the Morrey
scale and the action of potentials on it.
Cruz-Uribe–Fiorenza supplies variable Lebesgue methods, alongside the
variable Sobolev and generalized Orlicz references in the bibliographies.
Quasi-Banach ranges, highly irregular extension domains, and full multiplier
classification lie beyond the Banach-range core selected here.

Local source copies consulted:

* [Leoni, A First Course in Sobolev Spaces](References/Leoni2017FirstCourseSobolevSpaces2ndEd-AMS.GSM181.pdf).
* [Tartar, An Introduction to Sobolev Spaces and Interpolation Spaces](References/Tartar2007IntroductionSobolevSpacesInterpolationSpaces-SpringerLectureNotesUMI03.pdf).
* [Lunardi, Interpolation Theory](References/Lunardi2018InterpolationTheory-SpringerLNSNS16.pdf).
* [Triebel, Theory of Function Spaces](References/Triebel1983TheoryFunctionSpaces1-BirkhäuserMBC.pdf).
* [Maz'ya, Sobolev Spaces](References/Mazya2011SobolevSpacesApplicationsEllipticPDE-SpringerGL342.pdf).
* [Adams, Morrey Spaces](References/Adams2015MorreySpaces-Birkhauser.LNANHA.pdf).
* [Cruz-Uribe–Fiorenza, Variable Lebesgue Spaces](References/CruzUribeFiorenza2013VariableLebesgueSpaces-Birkhauser.ANHA.pdf).
