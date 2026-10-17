# Synopsis: Sobolev spaces, smoothness scales, and interpolation

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects the recurring core of Section 26 of
[CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md). It treats
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
* **5. Absolute continuity on lines.** $u\in W^{1,p}$ exactly when it
  has representatives absolutely continuous on almost every coordinate
  line in interior boxes, with line derivatives and $u$ in $L^p$.
  These line derivatives are the weak partial derivatives.
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
* **11. Dual representation.** For $1<p<\infty$, every functional on
  $W_0^{m,p}(\Omega)$ is
  $u\mapsto\sum_{|\alpha|\leq m}\int f_\alpha\partial^\alpha u$
  for some $f_\alpha\in L^{p'}$. Its distributional form is a sum
  of derivatives of $L^{p'}$ functions, defining $W^{-m,p'}$.
* **12. Extension theorem.** On a bounded Lipschitz domain there is a
  bounded linear extension $W^{m,p}(\Omega)\to W^{m,p}(\mathbb R^d)$
  for each nonnegative integer $m$, including $p=1,\infty$.
  Consequently restrictions of globally smooth functions are dense for finite $p$.

## Embeddings, norm inequalities, and compactness

* **13. Sobolev embedding.** For $1\leq p<d$,
  $W^{1,p}(\mathbb R^d)\hookrightarrow L^{p^*}$,
  $p^*=dp/(d-p)$, with $\|u\|_{p^*}\leq C\|\nabla u\|_p$.
  Bounded Lipschitz domains have the corresponding inhomogeneous estimate.
* **14. Higher-order Sobolev embedding.** If $mp<d$,
  $W^{m,p}(\mathbb R^d)\hookrightarrow L^{dp/(d-mp)}$.
  More generally $W^{m,p}\hookrightarrow W^{k,q}$ when
  $1/q=1/p-(m-k)/d>0$ in the usual finite-exponent range.
* **15. Critical embedding.** On bounded Lipschitz domains,
  $W^{1,d}\hookrightarrow L^q$ for every finite $q$.
  For $d\geq2$ it does not embed into $L^\infty$; the endpoint
  exponential integrability is given by Moser–Trudinger.
* **16. Morrey embedding.** If $p>d$, then
  $W^{1,p}(\Omega)\hookrightarrow C^{0,1-d/p}(\overline\Omega)$
  on bounded Lipschitz domains. Higher-order versions apply after
  differentiating when the remaining Sobolev order exceeds $d/p$.
* **17. Rellich–Kondrachov compactness.** On bounded Lipschitz domains,
  $W^{1,p}\hookrightarrow L^q$ is compact for $q<p^*$ when $p<d$,
  and for every finite $q$ when $p=d$. For $p>d$ it is compact into
  $C^{0,\beta}$ for $0\leq\beta<1-d/p$.
* **18. Poincaré inequalities.** On bounded connected Lipschitz domains,
  $\|u-u_\Omega\|_p\leq C\|\nabla u\|_p$.
  On $W_0^{1,p}$, $\|u\|_p\leq C\|\nabla u\|_p$.
  Thus the gradient norm controls the full norm after fixing constants
  or zero boundary values.
* **19. Lorentz refinement.** For $1<p<d$,
  $\|u\|_{L^{p^*,p}(\mathbb R^d)}\leq C\|\nabla u\|_p$.
  At $p=1$, $W^{1,1}$ embeds into $L^{d/(d-1),1}$ for $d>1$.
* **20. Gagliardo–Nirenberg inequality.** For $1\leq p<d$,
  $1\leq r\leq q\leq p^*$ and
  $1/q=\theta(1/p-1/d)+(1-\theta)/r$,
  $\|u\|_q\leq C\|\nabla u\|_p^\theta\|u\|_r^{1-\theta}$
  for smooth compactly supported $u$, and by density wherever the norms are finite.
* **21. Sobolev algebra theorem.** For integer $m$ and $mp>d$,
  $W^{m,p}(\mathbb R^d)$ is a Banach algebra under pointwise
  multiplication, up to an equivalent norm; the same holds on bounded
  extension domains.
* **22. Fréchet–Kolmogorov criterion.** A bounded subset of
  $L^p(\mathbb R^d)$, $p<\infty$, is relatively compact exactly when
  translations tend uniformly to zero in norm and its $L^p$ mass is
  uniformly small outside large balls.

## Traces and zero boundary values

* **23. First-order trace theorem.** For bounded Lipschitz $\Omega$ and
  $1<p<\infty$, restriction extends to a bounded surjection
  $W^{1,p}(\Omega)\to B^{1-1/p}_{p,p}(\partial\Omega)$ with a bounded
  linear right inverse. For $p=2$ the range is $H^{1/2}$.
* **24. Higher traces on smooth boundaries.** On bounded smooth domains,
  the normal traces $\partial_n^ju$, $0\leq j<m$, map $W^{m,p}$
  boundedly to $B^{m-j-1/p}_{p,p}(\partial\Omega)$ for $1<p<\infty$.
  The joint normal-jet map has a bounded right inverse.
* **25. Kernel of the trace.** For bounded Lipschitz domains,
  $W_0^{1,p}=\ker\gamma$ for $1<p<\infty$. On smooth domains,
  $W_0^{m,p}$ is characterized by vanishing of all normal traces
  of orders $0,\ldots,m-1$.
* **26. Zero extension.** If $u\in W_0^{m,p}(\Omega)$, extension by
  zero belongs to $W^{m,p}(\mathbb R^d)$ and commutes with weak
  derivatives. For first order on Lipschitz domains, the converse holds
  for $1<p<\infty$.
* **27. Green formula with traces.** On bounded Lipschitz domains,
  $\int_\Omega(u\partial_jv+v\partial_ju)=
  \int_{\partial\Omega}\gamma u\,\gamma v\,n_j$
  for $u\in W^{1,p}$, $v\in W^{1,p'}$, $1<p<\infty$.
* **28. Trace Sobolev exponent.** For $1<p<d$,
  $W^{1,p}(\Omega)\hookrightarrow L^{p(d-1)/(d-p)}(\partial\Omega)$.
  The trace embedding is compact at smaller finite exponents.

## Capacity and fine representatives

For $1<p<\infty$, **Sobolev capacity** $C_{1,p}(E)$ is the outer
capacity generated by the infimum of $\|v\|_{W^{1,p}(\mathbb R^d)}^p$
over smooth functions at least one near a compact set. A property holds
**quasi-everywhere** if its exceptional set has zero capacity.

* **29. Quasicontinuity.** Every $W^{1,p}(\mathbb R^d)$ function has
  a representative continuous outside an open set of arbitrarily small
  $C_{1,p}$ capacity. This representative is unique quasi-everywhere.
* **30. Capacitary convergence.** From convergence in $W^{1,p}$ one
  can extract a subsequence of quasicontinuous representatives converging
  pointwise quasi-everywhere. Capacity therefore controls exceptional sets
  more finely than Lebesgue measure.
* **31. Arbitrary-domain zero boundary criterion.** For any open
  $\Omega$, $u\in W_0^{1,p}(\Omega)$ exactly when it is the restriction
  of a global $W^{1,p}$ function whose quasicontinuous representative
  vanishes quasi-everywhere on $\mathbb R^d\setminus\Omega$.
* **32. Approximate differentiability.** $W^{1,1}_{\rm loc}$ functions
  are approximately differentiable almost everywhere, and their approximate
  gradients agree with weak gradients. Ordinary pointwise differentiability
  in all directions is a stronger assertion.
* **33. Lusin approximation.** On a bounded Lipschitz domain, a Sobolev
  function with finite $p$ can be approximated in $W^{1,p}$ by Lipschitz
  functions agreeing with it outside sets whose measure tends to zero.
  This connects weak derivatives with classical Lipschitz differentiation.

## Fractional Sobolev spaces and nonlocal energies

For $0<s<1$ and finite $p$, define
$$[u]_{W^{s,p}(\Omega)}^p=
  \iint_{\Omega\times\Omega}\frac{|u(x)-u(y)|^p}{|x-y|^{d+sp}}dxdy,$$
with norm $\|u\|_p+[u]_{W^{s,p}}$. The Bessel potential space
$H^{s,p}(\mathbb R^d)$ is defined by
$\|(I-\Delta)^{s/2}u\|_p<\infty$ through tempered distributions.

* **34. Completeness and density.** $W^{s,p}$ is Banach and is reflexive
  for $1<p<\infty$. Smooth compactly supported functions are dense
  in $W^{s,p}(\mathbb R^d)$ for finite $p$.
* **35. Fractional Hilbert identity.** $W^{s,2}(\mathbb R^d)=H^{s,2}$
  with equivalent norms; the Gagliardo energy equals a positive constant
  times $\int|\xi|^{2s}|\widehat u(\xi)|^2d\xi$.
* **36. Fractional Laplacian formula.** For Schwartz $u$ and $0<s<1$,
  $(-\Delta)^su(x)=c_{d,s}\operatorname{p.v.}\int
  (u(x)-u(y))/|x-y|^{d+2s}\,dy$, with the positive normalization
  giving Fourier symbol $|\xi|^{2s}$. Its quadratic energy is
  $c_{d,s}[u]_{W^{s,2}}^2/2$.
* **37. Fractional Sobolev embedding.** If $sp<d$,
  $W^{s,p}(\mathbb R^d)\hookrightarrow L^{dp/(d-sp)}$;
  if $sp>d$, it embeds into $C^{0,s-d/p}$.
  Bounded Lipschitz domains have the corresponding extension and embedding results.
* **38. Fractional compactness.** On bounded Lipschitz domains,
  $W^{s,p}\hookrightarrow L^q$ is compact for $q<dp/(d-sp)$
  when $sp<d$, and for every finite $q$ when $sp\geq d$.
* **39. Nonlocal Poincaré inequality.** For bounded connected Lipschitz
  $\Omega$, $\|u-u_\Omega\|_p\leq C[u]_{W^{s,p}(\Omega)}$.
  For globally defined functions vanishing outside a fixed bounded domain,
  the full-space Gagliardo seminorm controls the $L^p$ norm.
* **40. Bourgain–Brezis–Mironescu limit.** For $u\in W^{1,p}(\mathbb R^d)$,
  $$\lim_{s\uparrow1}(1-s)[u]_{W^{s,p}}^p
     =\frac1p\left(\int_{S^{d-1}}|\omega_1|^pd\omega\right)
                       \int|\nabla u|^p.$$
  This identifies the normalized nonlocal energy with the local gradient energy.

## Besov and Triebel–Lizorkin scales

Choose a smooth inhomogeneous dyadic partition $(\varphi_j)_{j\geq0}$
in frequency and set $\Delta_ju=\mathcal F^{-1}(\varphi_j\widehat u)$.
The **Besov norm** is
$\|u\|_{B^s_{p,q}}=\|(2^{js}\|\Delta_ju\|_p)_j\|_{\ell^q}$;
the **Triebel–Lizorkin norm** is
$\|u\|_{F^s_{p,q}}=\|(\sum_j|2^{js}\Delta_ju|^q)^{1/q}\|_p$.
Use the supremum for $q=\infty$. Below Besov parameters are at least one,
and Triebel–Lizorkin assertions use $1<p<\infty$, unless otherwise stated.

* **41. Dyadic norm independence.** Different admissible dyadic partitions
  give equivalent norms and the same spaces. For real $s$, the indicated
  Banach ranges are complete spaces of tempered distributions.
* **42. Bernstein inequality.** If the Fourier support is in a ball of
  radius $C2^j$, then for $1\leq p\leq r\leq\infty$,
  $\|\partial^\alpha u\|_r\leq C_\alpha
  2^{j(|\alpha|+d(1/p-1/r))}\|u\|_p$.
* **43. Difference characterization.** For $0<s<1$ and finite $p$,
  $W^{s,p}=B^s_{p,p}$. More generally differences of integer order
  $m>s>0$, integrated against $|h|^{-sq-d}dh$, characterize
  $B^s_{p,q}$, with the usual supremum for $q=\infty$.
* **44. Bessel and Sobolev identifications.**
  $H^{s,p}=F^s_{p,2}$ for real $s$ and $1<p<\infty$;
  for nonnegative integer $m$, $W^{m,p}=H^{m,p}$.
  For $p\ne2$, fractional Gagliardo and Bessel spaces need not coincide.
* **45. Hölder–Zygmund identification.** For positive noninteger $s$,
  $B^s_{\infty,\infty}$ is the bounded Hölder space $C^s$.
  At positive integers it is the Zygmund class, which is larger than
  the corresponding bounded classical differentiability class.
* **46. Lifting isomorphism.** $(I-\Delta)^{t/2}$ maps
  $B^s_{p,q}$ isomorphically onto $B^{s-t}_{p,q}$ and
  $F^s_{p,q}$ onto $F^{s-t}_{p,q}$ in the indicated ranges.
* **47. Fine-index embeddings.** If $q_0\leq q_1$, then
  $B^s_{p,q_0}\hookrightarrow B^s_{p,q_1}$ and
  $F^s_{p,q_0}\hookrightarrow F^s_{p,q_1}$. Also
  $B^s_{p,\min(p,q)}\hookrightarrow F^s_{p,q}
  \hookrightarrow B^s_{p,\max(p,q)}$.
* **48. Sobolev-index embedding.** If $p_0\leq p_1$ and
  $s_0-d/p_0=s_1-d/p_1$, then
  $B^{s_0}_{p_0,q}\hookrightarrow B^{s_1}_{p_1,q}$.
  In particular $s>d/p$ gives continuous bounded representatives.
* **49. Besov trace.** For $1<p,q<\infty$ and $s>1/p$, restriction
  to a hyperplane is a bounded surjection
  $B^s_{p,q}(\mathbb R^d)\to B^{s-1/p}_{p,q}(\mathbb R^{d-1})$
  with a bounded right inverse. For $F^s_{p,q}$ the trace range is
  $B^{s-1/p}_{p,p}$.
* **50. Besov algebra theorem.** $B^s_{p,q}\cap L^\infty$ satisfies
  a product estimate controlled by the two $L^\infty$ norms and Besov
  norms when $s>0$. Hence $B^s_{p,q}$ is an algebra for $s>d/p$,
  and at $s=d/p>0$ when $q=1$.

## Real and complex interpolation

A **Banach couple** $(X_0,X_1)$ embeds both spaces into one Hausdorff
vector space. Define
$K(t,x)=\inf_{x=x_0+x_1}(\|x_0\|_{X_0}+t\|x_1\|_{X_1})$.
The **real interpolation space** $(X_0,X_1)_{\theta,q}$ has norm
$\|t^{-\theta}K(t,x)\|_{L^q(\mathbb R_+,dt/t)}$.
The **complex interpolation space** $[X_0,X_1]_\theta$ consists of
values at $\theta$ of bounded analytic strip functions with boundary
values in $X_0$ and $X_1$, with the infimum boundary norm.

* **51. Real interpolation theorem.** An operator bounded
  $X_i\to Y_i$ with norms $M_i$ acts boundedly between the real
  interpolation spaces with bound at most $M_0^{1-\theta}M_1^\theta$.
* **52. Complex interpolation theorem.** The same operator bound holds
  between complex interpolation spaces, by the three-lines theorem.
* **53. K–J equivalence.** Real interpolation can equivalently be
  described by representations $x=\int_0^\infty u(t)dt/t$,
  $u(t)\in X_0\cap X_1$, controlling
  $t^{-\theta}\max(\|u(t)\|_{X_0},t\|u(t)\|_{X_1})$ in $L^q(dt/t)$.
* **54. Reiteration theorem.** For $0<\theta_0<\theta_1<1$,
  $0<\eta<1$, and admissible $q,q_0,q_1$,
  $$((X_0,X_1)_{\theta_0,q_0},(X_0,X_1)_{\theta_1,q_1})_{\eta,q}
       =(X_0,X_1)_{(1-\eta)\theta_0+\eta\theta_1,q}$$
  with equivalent norms.
* **55. Real interpolation duality.** If $X_0\cap X_1$ is dense in
  both endpoints and $1\leq q<\infty$, then
  $((X_0,X_1)_{\theta,q})^*=(X_0^*,X_1^*)_{\theta,q'}$
  with equivalent norms under the natural pairing.
* **56. Riesz–Thorin theorem.** Bounds $T:L^{p_i}\to L^{q_i}$
  interpolate with reciprocal exponents affine in $\theta$ and norm
  at most $M_0^{1-\theta}M_1^\theta$, including the standard infinite
  endpoint exponents.
* **57. Marcinkiewicz interpolation.** A sublinear operator of weak
  types $(p_0,p_0)$ and $(p_1,p_1)$, $1\leq p_0<p_1<\infty$,
  is strongly bounded on $L^p$ for $p_0<p<p_1$.
* **58. Lorentz interpolation.** For $1\leq p_0<p_1\leq\infty$,
  $(L^{p_0},L^{p_1})_{\theta,q}=L^{p,q}$,
  $1/p=(1-\theta)/p_0+\theta/p_1$. Here
  $\|f\|_{p,q}$ is equivalent to
  $\|t^{1/p}f^*(t)\|_{L^q(dt/t)}$, with $f^*$ the decreasing rearrangement.
* **59. Complex $L^p$ interpolation.**
  $[L^{p_0},L^{p_1}]_\theta=L^p$ with reciprocal exponents as above
  on a $\sigma$-finite measure space, for $1\leq p_0,p_1\leq\infty$.
* **60. Bessel potential interpolation.** For $1<p<\infty$,
  $[H^{s_0,p},H^{s_1,p}]_\theta=H^{(1-\theta)s_0+\theta s_1,p}$.
  Extension and restriction transfer the usual smooth-domain versions.
* **61. Sobolev real interpolation.** For integers $0\leq m_0<m_1$,
  $1<p<\infty$, and $s=(1-\theta)m_0+\theta m_1$,
  $(W^{m_0,p},W^{m_1,p})_{\theta,q}=B^s_{p,q}$ on $\mathbb R^d$.
  This remains a Besov statement when $s$ is an integer.
* **62. Besov reiteration in smoothness.** For $s_0<s_1$,
  $(B^{s_0}_{p,q_0},B^{s_1}_{p,q_1})_{\theta,q}
  =B^{(1-\theta)s_0+\theta s_1}_{p,q}$ with equivalent norms.
* **63. Real interpolation of compactness.** If $T:X_0\to Y_0$ is
  compact and $T:X_1\to Y_1$ bounded, it is compact between the
  corresponding real interpolation spaces for $0<\theta<1$,
  $1\leq q<\infty$. This is the Lions–Peetre compactness theorem.

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

* **64. Orlicz completeness and Hölder inequality.** $L^\Phi$ is Banach,
  and $\int|fg|\leq2\|f\|_\Phi\|g\|_\Psi$.
  Its Köthe associate is $L^\Psi$ with the equivalent Orlicz dual norm.
* **65. Growth conditions and reflexivity.** If complementary N-functions
  $\Phi,\Psi$ both satisfy the global doubling condition
  $\Phi(2t)\leq C\Phi(t)$ and its counterpart for $\Psi$, then their
  Orlicz spaces are reflexive and the usual integral duality gives their
  full Banach duals. Without such growth conditions singular functionals
  may occur.
* **66. Variable-exponent duality.** If $1<p_-\leq p_+<\infty$,
  $L^{p(\cdot)}$ is separable and reflexive, with dual
  $L^{p'(\cdot)}$ under integration, up to equivalent norms.
  The variable Hölder bound holds with constant at most two.
* **67. Norm–modular comparison.** For $p_+<\infty$,
  $$\min(\|f\|^{p_-},\|f\|^{p_+})\leq\rho(f)
       \leq\max(\|f\|^{p_-},\|f\|^{p_+}),$$
  with the variable Lebesgue norm. Thus convergence in norm and
  convergence of the difference modular to zero are equivalent.
* **68. Variable maximal theorem.** If $1<p_-\leq p_+<\infty$ and
  $p$ is globally log-Hölder continuous, the Hardy–Littlewood maximal
  operator is bounded on $L^{p(\cdot)}(\mathbb R^d)$. The condition
  controls $|p(x)-p(y)|$ by $C/\log(e+1/|x-y|)$ locally and
  $|p(x)-p_\infty|$ by $C/\log(e+|x|)$ at infinity.
* **69. Variable Sobolev embedding.** On a bounded Lipschitz domain,
  for log-Hölder $p$ with $1<p_-\leq p_+<d$,
  $W^{1,p(\cdot)}\hookrightarrow L^{p^*(\cdot)}$,
  where $p^*(x)=dp(x)/(d-p(x))$. Uniformly subcritical continuous
  target exponents give compact embeddings.
* **70. Variable smooth density.** Under these log-Hölder assumptions,
  smooth functions are dense in $W^{1,p(\cdot)}$ on a Lipschitz
  domain, and compactly supported smooth functions generate its
  zero-boundary space. Arbitrary measurable exponents need not admit
  the same density and approximation properties.

## Morrey and Campanato descriptions

The **Morrey norm** on $\mathbb R^d$ is
$\sup_{B(x,r)}r^{-\lambda/p}(\int_{B(x,r)}|f|^p)^{1/p}$,
$0\leq\lambda\leq d$. A **Campanato seminorm** measures oscillation:
$\sup_{B(x,r)}r^{-\alpha}(\fint_{B(x,r)}|f-f_B|^p)^{1/p}$.
These spaces describe local size and oscillation separately from ordinary
global integrability.

* **71. Campanato–Hölder equivalence.** For $0<\alpha<1$ and finite
  $p\geq1$, finiteness of the Campanato seminorm is equivalent, modulo
  constants and almost-everywhere representatives, to $\alpha$-Hölder
  continuity. The seminorms are equivalent.
* **72. BMO endpoint.** At $\alpha=0$, the Campanato seminorms for all
  finite $p\geq1$ are equivalent to the BMO seminorm, by the
  John–Nirenberg exponential-integrability theorem. The endpoint describes
  controlled mean oscillation rather than bounded pointwise oscillation.

## Reference guide

Leoni provides weak derivatives, approximation, embeddings, traces,
interpolation, and Besov spaces in one development. Brezis and Tartar
independently cover the Sobolev and interpolation foundation; Maz'ya
supplies the capacity and fine-property viewpoint. Lunardi gives the
abstract interpolation and trace methods. Triebel and Sawano develop the
dyadic scales, lifting, differences, and sharp parameter distinctions.
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
* [Cruz-Uribe–Fiorenza, Variable Lebesgue Spaces](References/CruzUribeFiorenza2013VariableLebesgueSpaces-Birkhauser.ANHA.pdf).
