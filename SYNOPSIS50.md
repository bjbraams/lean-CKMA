# Synopsis: Asymptotic analysis, resurgence, and perturbation

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-50);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring core material from Section 50 of
[CKMA-bib.md](CKMA-bib.md#ckma-50).
It covers asymptotic scales, integral and coefficient methods, linear
differential equations and turning points, Gevrey expansions and summation,
resurgence, averaging, and singular and eigenvalue perturbation. Formal identities, asymptotic
expansions with remainders, and actual summed solutions are distinguished
throughout. Special-function normalizations are in Section 49, and
Riemann–Hilbert asymptotics are developed further in Section 51.

Microlocal and semiclassical operator methods remain in Section 30; nonlinear
dispersive evolution is identified as [34B](CKMA-bib.md#ckma-34b), and
integrable Riemann–Hilbert methods remain in Section 51. Spectral
asymptotics beyond the Bohr–Sommerfeld rule (entry 39), such as Weyl laws,
are in Sections 30 and 53.

For an asymptotic scale $\phi_{n+1}=o(\phi_n)$, write
$f\sim\sum a_n\phi_n$ if
$f-\sum_{n=0}^{N-1}a_n\phi_n=o(\phi_{N-1})$ for every $N$.
For power series near zero use the equivalent conventional remainder
$f-\sum_{n<N}a_nz^n=O(z^N)$ when all orders are available.
Sectorial estimates are uniform on closed proper subsectors; estimates
with an additional parameter explicitly require uniform hypotheses.

## Expansions, realization, and nonuniqueness

* **1. Uniqueness of coefficients.** An expansion in a fixed
  asymptotic scale has unique coefficients, obtained successively
  by subtracting the preceding terms and taking scaled limits.
* **2. Algebra of power expansions.** Sums and products of
  power-asymptotic expansions are computed formally, with each fixed
  truncation justified by its remainder. Division is valid when the
  denominator has a nonzero leading coefficient.
* **3. Differentiation in sectors.** A holomorphic power-asymptotic
  expansion may be differentiated termwise on smaller sectors.
  This follows from Cauchy estimates; real-variable asymptotics alone
  do not generally permit differentiation.
* **4. Integration of expansions.** Uniform expansions can be
  integrated on fixed finite paths with integrated remainder bounds.
  For indefinite asymptotic integration, an exponent $-1$ produces
  a logarithm, and an independent integration constant must be retained.
* **5. Borel's smooth realization theorem.** Every prescribed
  sequence of derivatives at a point is the jet of a smooth function.
* **6. Borel–Ritt theorem.** Every formal power series is the
  asymptotic expansion of a holomorphic function on any sector of
  finite opening (on the Riemann surface of the logarithm when the
  opening is at least $2\pi$).
* **7. Flat-function ambiguity.** On a sector where $\Re(1/z)>0$,
  $e^{-1/z}$ has the zero power-asymptotic expansion. Ordinary
  asymptotic data therefore do not determine a sectorial function uniquely.
* **8. Composition and inversion.** Compatible power expansions
  compose when the inner argument approaches the required expansion
  point. A nonzero linear term gives a formal inverse; an actual
  local analytic inverse inherits that inverse asymptotic expansion.

## Laplace, oscillatory, and uniform integral methods

The large parameter $\lambda$ tends to $+\infty$. Amplitudes are
smooth and integrable as required; cutoff versions separate a critical
point from all other contributions.

* **9. Watson's lemma.** If $a(t)\sim\sum_{n\geq0}a_nt^{n+\alpha-1}$
  at $0+$, $\Re\alpha>0$, and the tail has an exponential bound,
  then $\int_0^\infty e^{-\lambda t}a(t)dt
  \sim\sum a_n\Gamma(n+\alpha)\lambda^{-n-\alpha}$.
  A finite local remainder gives the corresponding integral remainder.
* **10. Nonstationary Laplace endpoint.** If a real phase has
  its unique minimum at $a$, $\phi'(a)>0$, and other regions
  are separated in phase, then
  $\int_a^b e^{-\lambda\phi(t)}A(t)dt
  \sim e^{-\lambda\phi(a)}A(a)/(\lambda\phi'(a))$ when $A(a)\ne0$.
* **11. Interior Laplace minimum.** A nondegenerate interior minimum
  $t_0$ contributes
  $e^{-\lambda\phi(t_0)}A(t_0)\sqrt{2\pi/(\lambda\phi''(t_0))}$.
  Taylor expansion after a Morse change of variable gives all higher terms.
* **12. Multidimensional Laplace method.** A unique nondegenerate
  interior minimum with positive Hessian $H$ contributes
  $e^{-\lambda\phi(x_0)}(2\pi/\lambda)^{m/2}A(x_0)/\sqrt{\det H}$
  in $m$ real dimensions, with a full expansion under smoothness
  and localization hypotheses.
* **13. Nonstationary phase.** If $A\in C_c^\infty$ and
  $\nabla\phi\ne0$ on its support, then
  $\int e^{i\lambda\phi}A=O_N(\lambda^{-N})$ for every $N$.
  On a compact interval $[a,b]$ with $\phi'\ne0$ and smooth $A$,
  integration by parts gives instead the endpoint expansion
  $\int_a^be^{i\lambda\phi}A\,dt=\bigl[e^{i\lambda\phi}A/(i\lambda\phi')\bigr]_a^b
  +O(\lambda^{-2})$, continued to all orders by repetition.
* **14. Stationary phase.** A nondegenerate critical point with
  real Hessian $H$ contributes
  $e^{i\lambda\phi(x_0)+i\pi\operatorname{sgn}H/4}
  (2\pi/\lambda)^{m/2}A(x_0)/\sqrt{|\det H|}$,
  with subsequent powers of $\lambda^{-1}$ and controlled remainder.
  For a unique nondegenerate critical point on the support of the amplitude,
  the remainder after the leading term is $O(\lambda^{-m/2-1})$. The van der
  Corput bound for degenerate phases is SYNOPSIS27, item 63.
* **15. Degenerate endpoint scale.** For $m>0$, $\Re\alpha>0$,
  $\int_0^\infty e^{-\lambda t^m}t^{\alpha-1}dt
  =\Gamma(\alpha/m)\lambda^{-\alpha/m}/m$.
  Local expansions reduce finite-order endpoint degeneracies to this model.
* **16. Steepest descent.** An analytic contour may be deformed
  through accessible saddles when no singularity is crossed and the
  closing contributions vanish. A simple saddle gives its Gaussian
  expansion; the contour orientation determines the square-root phase.
* **17. Saddle–endpoint transition.** A simple saddle approaching
  an endpoint has a uniform expansion in complementary error functions
  and Gaussian terms, provided the transformed amplitude remains
  analytic uniformly. Separate saddle and endpoint expansions cease
  to be uniform at their collision.
* **18. Coalescing saddles.** Two analytic simple saddles coalescing
  to a cubic critical point admit a cubic normal form and a uniform
  expansion in Airy functions and their derivatives. The transition
  scale is $\lambda^{-2/3}$ in the unfolding parameter.
* **19. Higher canonical integrals.** Three saddles coalescing
  generically lead to the quartic Pearcey phase
  $t^4/4+at^2/2+bt$. Its uniform scaling is
  $t=O(\lambda^{-1/4})$, $a=O(\lambda^{-1/2})$,
  $b=O(\lambda^{-3/4})$, with smooth amplitude corrections.
* **74. Newton polyhedra and oscillation index.** For a real-analytic
  phase $\phi$ on $\mathbb R^n$ with a critical point at $0$ and smooth
  amplitude of small support,
  $\int e^{i\lambda\phi}a\,dx\sim e^{i\lambda\phi(0)}\sum_\alpha\sum_{k=0}^{n-1}
  c_{\alpha,k}\lambda^\alpha(\log\lambda)^k$, with $\alpha$ in finitely
  many arithmetic progressions of negative rationals (Malgrange). If
  $\phi-\phi(0)$ is nondegenerate with respect to its Newton polyhedron at
  $0$ and the Newton distance $d$ (where the diagonal meets the polyhedron)
  exceeds one, the oscillation index is $-1/d$: the integral is
  $O(\lambda^{-1/d}(\log\lambda)^{n-1})$, and no faster rate holds for
  all amplitudes (Varchenko; Arnold–Gusein-Zade–Varchenko).
* **20. Darboux principle.** A remainder with $k$ continuous
  angular derivatives on the convergence circle has Taylor coefficients
  $o(n^{-k})$ after scaling the circle to radius one. Subtracting explicitly
  known singular parts on the convergence circle therefore determines
  leading coefficient asymptotics from those singularities.
* **21. Algebraic singularity transfer.** If $f$ is analytic in
  a dented disk about its unique dominant singularity $\rho$ and
  $f(z)\sim C(1-z/\rho)^{-\alpha}$ there, with
  $\alpha\notin\{0,-1,-2,\ldots\}$ and a compatible smaller
  remainder, then $[z^n]f\sim C\rho^{-n}n^{\alpha-1}/\Gamma(\alpha)$.
* **22. Multiple dominant singularities.** With finitely many
  separated singularities and the corresponding dented-domain
  continuation, their coefficient contributions add. Equal-modulus
  singularities can create oscillations or cancellation, so a single
  positive equivalent need not exist.
* **73. Saddle-point bound and Hayman admissibility.** If $f$ has
  nonnegative Taylor coefficients and radius $R$, then
  $[z^n]f\leq f(r)/r^n$ for $0<r<R$, best at $a(r)=n$, where
  $a(r)=rf'(r)/f(r)$. Let $b(r)=ra'(r)$. If $f$ is Hayman admissible
  ($b(r)\to\infty$ as $r\uparrow R$; for some $0<\delta(r)<\pi$,
  $f(re^{i\theta})\sim f(r)e^{i\theta a(r)-\theta^2b(r)/2}$ uniformly in
  $|\theta|\leq\delta(r)$, and $f(re^{i\theta})=o(f(r)/\sqrt{b(r)})$
  uniformly in $\delta(r)\leq|\theta|\leq\pi$), then
  $[z^n]f\sim f(r_n)r_n^{-n}/\sqrt{2\pi b(r_n)}$ with $a(r_n)=n$.
  For $f=e^z$ this is Stirling's formula for $1/n!$.

## Summation, Mellin transforms, and regular variation

* **23. Euler–Maclaurin formula.** For integers $m<n$ and smooth $f$,
  $$
  \sum_{k=m}^nf(k)=\int_m^nf(x)dx+\frac{f(m)+f(n)}2
  +\sum_{r=1}^p\frac{B_{2r}}{(2r)!}
  [f^{(2r-1)}(n)-f^{(2r-1)}(m)]+R_p.
  $$
  Here $R_p=-(2p)!^{-1}\int_m^n\widetilde B_{2p}(x)f^{(2p)}(x)dx$.
* **24. Euler–Maclaurin error bound.**
  $|R_p|\leq2\zeta(2p)(2\pi)^{-2p}\int_m^n|f^{(2p)}(x)|dx$.
  Endpoint derivative decay permits summation to an infinite endpoint.
* **26. Mellin contour displacement.** If a Mellin transform has
  meromorphic continuation and sufficient vertical decay, moving its
  inversion contour left yields small-$x$ expansions from the poles
  crossed, with remainder bounded by the new contour integral.
  Moving right yields large-$x$ expansions with the opposite residue orientation.
* **27. Mellin poles and logarithms.** A pole term
  $c(s-s_0)^{-r}$ contributes
  $c\,x^{-s_0}(-\log x)^{r-1}/(r-1)!$ when crossed in a leftward
  displacement. Higher pole orders encode logarithmic terms.
* **28. Mellin convolution method.** For
  $h(x)=\int_0^\infty f(t)g(x/t)dt/t$, the Mellin transform
  is $\mathcal Mh=\mathcal Mf\,\mathcal Mg$ in the common
  absolute-convergence strip. Pole multiplication then gives convolution asymptotics.
* **29. Karamata Tauberian theorem.** For a nondecreasing $U$
  with finite Laplace–Stieltjes transform at every positive argument,
  $\int e^{-st}dU(t)\sim s^{-\rho}L(1/s)$ as $s\downarrow0$
  exactly when $U(x)\sim x^\rho L(x)/\Gamma(1+\rho)$,
  where $\rho\geq0$ and $L$ is slowly varying.

## Differential equations, irregular singularities, and WKB

* **30. Frobenius theorem.** A regular singular linear equation
  has convergent local solutions built from powers, convergent
  power series, and finitely many logarithms. Indicial roots and
  resonances determine the exponents and logarithmic terms.
* **31. Levelt–Turrittin formal structure.** After finite ramification,
  a meromorphic linear system has a formal fundamental solution
  decomposed into factors $\widehat H(t)e^{Q(t^{-1})}t^L$,
  blockwise, with polynomial exponential parts, constant exponent
  matrices, and invertible formal power-series factors.
* **32. Sectorial realization.** For
  $z^{r+1}Y'=A(z)Y$, $r\geq1$, analytic $A$ with distinct
  eigenvalues at zero, on every sector of opening at most $\pi/r$
  and small radius there is an actual fundamental solution
  asymptotic to a given formal one (classical existence theorem).
  On sectors of opening greater than $\pi/r$ such a solution is
  unique when it exists; Stokes matrices compare these solutions on
  overlapping sectors of opening slightly greater than $\pi/r$.
* **33. Stokes matrices.** Sectorial fundamental solutions with
  the same formal normalization differ on overlaps by constant
  matrices. Their nontrivial entries describe exponentially small
  discrepancies invisible to the common power expansion.
* **34. Monodromy factorization.** Analytic monodromy around an
  irregular singularity is the ordered product of Stokes factors
  and formal monodromy, with the order fixed by the chosen sectors
  and continuation convention.
* **35. Liouville–Green approximation.** On a compact real interval
  where $Q\in C^2$ is positive and bounded away from zero,
  $\varepsilon^2y''=Qy$ has independent solutions
  $Q^{-1/4}\exp[\pm\varepsilon^{-1}\int\sqrt Q]\,(1+O(\varepsilon))$
  uniformly as $\varepsilon\downarrow0$.
* **36. WKB recursion.** With $y=\exp(\varepsilon^{-1}\int S)$,
  $S^2+\varepsilon S'=Q$. For $S\sim\sum\varepsilon^nS_n$,
  $S_0=\pm\sqrt Q$ and
  $S_n=-(S_{n-1}'+\sum_{j=1}^{n-1}S_jS_{n-j})/(2S_0)$.
* **37. Simple turning points.** If analytic $Q$ has a simple
  zero at $a$, the change
  $\frac23\zeta^{3/2}=\int_a^x\sqrt Q$
  transforms the leading equation to Airy form. Uniform solutions
  have leading factors $(\zeta/Q)^{1/4}\operatorname{Ai}
  (\varepsilon^{-2/3}\zeta)$ and the corresponding $\operatorname{Bi}$ term.
* **38. Turning-point connection.** For $Q<0$ to the left and
  $Q>0$ to the right of a simple turning point, a decaying term
  $CQ^{-1/4}e^{-\int_a^x\sqrt Q/\varepsilon}$ connects to
  $2C|Q|^{-1/4}\sin(\int_x^a\sqrt{-Q}/\varepsilon+\pi/4)$
  at leading order. Error is measured additively against the envelope near zeros.
* **39. Bohr–Sommerfeld rule.** For $-\varepsilon^2y''+V(x)y=Ey$
  with smooth confining single-well $V$, and eigenvalues $E_n$ in a
  fixed energy window where $V=E$ has exactly two simple turning points,
  $\int_{a(E_n)}^{b(E_n)}\sqrt{E_n-V(x)}dx
  =\pi\varepsilon(n+1/2)+O(\varepsilon^2)$.
* **40. Gevrey growth from rank one.** If $A$ is invertible and
  $b$ is analytic near $(0,0)$, the formal solution with $y(0)=0$
  of $z^2y'=Ay+zb(z,y)$ is unique and Gevrey of order one.
  Convergence is not implied by formal solvability.
* **41. Recessive-solution error bound.** For
  $W''=(\lambda^2+\chi(t))W$, $\lambda>0$,
  $\chi\in L^1[a,\infty)$, there is a unique solution with
  $e^{\lambda t}W(t)\to1$. Its Volterra equation gives
  $|e^{\lambda t}W(t)-1|\leq
  \exp[(2\lambda)^{-1}\int_t^\infty|\chi(s)|ds]-1$.

## Gevrey series, Borel summation, and resurgence

A **Gevrey-$s$ expansion** obeys
$|f(z)-\sum_{n<N}a_nz^n|\leq CA^N\Gamma(1+sN)|z|^N$.
For $s=1$ use the formal Borel transform and directional Laplace integral
$$
\mathcal B\widehat f(\xi)=\sum_{n\geq1}\frac{a_n\xi^{n-1}}{(n-1)!},
\qquad \mathcal S_\theta\widehat f(z)=a_0+
\int_0^{e^{i\theta}\infty}e^{-\xi/z}\mathcal B\widehat f(\xi)d\xi.
$$
One-summability requires analytic continuation of the Borel germ to a
sector about that ray with at most exponential growth there.

* **42. Optimal truncation.** A Gevrey-one remainder bound, truncated
  near $N\asymp1/(A|z|)$, yields error $O(e^{-c/|z|})$ for
  a positive $c$. Fixed-order algebraic estimates can thus conceal
  an exponentially small attainable error.
* **43. Watson uniqueness.** A holomorphic function with zero
  Gevrey-$s$ expansion on a sector of opening greater than $\pi s$
  is zero. Smaller sectors admit nontrivial exponentially flat functions.
* **44. Borel convergence.** A formal Gevrey-one series has a
  convergent Borel germ; conversely convergence of that germ gives
  factorial coefficient bounds. Continuation and growth are additional
  requirements for summability.
* **45. Borel–Laplace theorem.** Under the stated continuation and
  exponential-growth conditions, rotation of the admissible Laplace
  ray gives a holomorphic sum for small $z$ in a sector centered
  at $\theta$ of opening greater than $\pi$. It has the original
  Gevrey-one expansion on proper subsectors.
* **46. Product and convolution.** For series with zero constant
  terms, $\mathcal B(\widehat f\widehat g)=
  \mathcal B\widehat f*\mathcal B\widehat g$.
  Directionally summable series form an algebra and summation preserves products.
* **47. Differential compatibility.** Directional summation commutes
  with differentiation and multiplication by the independent variable
  on the corresponding domains. A summable formal differential-equation
  solution therefore sums to an actual solution when the analytic operations are admissible.
* **48. Nonlinear closure.** One-summable series in a common
  direction are stable under convergent analytic substitutions,
  reciprocals with nonzero constant term, and implicit solutions
  with nonzero relevant derivative. Summation respects these operations.
* **49. Euler example.** The divergent series
  $\sum_{n\geq0}(-1)^nn!z^{n+1}$ has Borel transform
  $1/(1+\xi)$ and positive-direction sum
  $\int_0^\infty e^{-\xi/z}/(1+\xi)d\xi$.
  This solves $z^2f'+f=z$ and has the stated factorial expansion.
* **50. Lateral jump formula.** When lateral Laplace contours
  differ by a positively oriented loop about a simple Borel pole
  $A$ with residue $c$, their sums differ by $2\pi ic\,e^{-A/z}$,
  assuming the remaining contour deformation is justified.
* **72. Smoothing of the Stokes phenomenon.** Let the Borel transform
  have a nearest simple pole at $A$ (entry 55), so the singulant is
  $F=A/z$ and $\arg z=\arg A$ is the Stokes line. Let $f$ be the lateral
  sum from the side where $\sigma=\Im F/\sqrt{2\Re F}$ is negative,
  continued across the line, and $\Delta=f-\mathcal S_{+}\widehat f$ its
  exponentially small difference from the lateral sum on the other side
  (entry 50). Truncating near the least term, $N=|F|+O(1)$, gives
  $f(z)-\sum_{n<N}a_nz^n=\Delta\cdot\frac12[1+\operatorname{erf}\sigma]
  (1+O(|z|^{1/2}))$ near the line. The subdominant exponential is
  switched on smoothly across an angular width $O(|z|^{1/2})$ (Berry);
  re-expanding the remainder in terminant functions gives exponentially
  improved and hyperasymptotic expansions (Dingle, Olver, Paris).
* **51. Ramis–Sibuya theorem.** Bounded holomorphic functions on
  a finite good sectorial covering of a punctured disk, whose
  overlap differences are $O(e^{-c/|z|^k})$, have one common
  Gevrey-$(1/k)$ expansion. Uniform subsector bounds are required.
* **52. Multisummability of linear systems.** Formal fundamental
  solutions of meromorphic linear ODEs, after ramification and removal
  of their exponential and logarithmic factors, have multisummable
  power-series factors. Their finitely many summation levels are
  determined by the positive slopes of the Newton polygon.
* **53. Resurgent convolution.** If a closed discrete singular set
  $\Omega$ contains zero and is stable under addition, Borel germs
  continuable along paths avoiding $\Omega$ are stable under
  convolution. The addition condition controls the possible new singularities.
* **54. Resurgent analytic operations.** The corresponding resurgent
  formal series are stable under products, analytic substitutions,
  and inverses with nonzero constant term. In the simple-singularity
  setting, local polar and logarithmic singular parts determine the
  lateral Stokes differences through Laplace continuation.
* **55. Singularities determine late terms.** If the Borel transform
  has a nearest simple pole $c/(\xi-A)$ and the remainder extends
  to a larger disk, then
  $a_n\sim-c(n-1)!A^{-n}$.
  Several nearest singularities contribute a sum, potentially with cancellation.
* **56. Exact WKB summation.** For a polynomial Schrödinger
  potential with simple zeros and a saddle-free Stokes graph, the
  normalized WKB series are Borel summable in the chosen direction
  at regular points of each Stokes region. Their sums solve the
  equation and obey the simple-turning-point connection formulas.
  The hypotheses are spelled out in Iwaki–Nakanishi, *Exact WKB analysis and cluster algebras* (arXiv:1401.7094), Section 2.

## Regular and singular perturbation of differential equations

Consider smooth slow–fast systems
$\dot x=f(x,y,\varepsilon)$,
$\varepsilon\dot y=g(x,y,\varepsilon)$.
Their **critical manifold** is $g(x,y,0)=0$; normal attraction means
the fast normal eigenvalues have real parts uniformly below zero.

* **57. Regular parameter dependence.** For an ODE with analytic
  vector field and analytic initial data in $\varepsilon$, solutions
  depend analytically on $\varepsilon$ on a fixed finite interval
  on which they remain in a common compact regularity domain.
  Differentiating the equation constructs a justified perturbation expansion.
* **58. Tikhonov theorem.** If the critical branch $y=h(x)$ is
  uniformly asymptotically stable for the frozen fast equation,
  the initial fast datum lies in its attraction basin, and the
  reduced solution stays in the regular branch, then $x_\varepsilon$
  converges uniformly to the reduced slow solution $x_0(t)$ on fixed
  intervals, and $y_\varepsilon(t)\to h(x_0(t))$ away from the initial time.
* **59. Initial-layer estimate.** With $C^2$ data, a uniform
  Hurwitz gap, matching slow initial data, and fast initial values in a fixed small attraction
  neighborhood, one has $x_\varepsilon-x_0=O(\varepsilon)$ and
  $|y_\varepsilon(t)-h(x_0(t))|
  \leq C\varepsilon+Ce^{-ct/\varepsilon}$ on a fixed regular interval.
* **60. Fenichel persistence.** A compact normally hyperbolic
  critical manifold persists for small $\varepsilon$ as a locally
  invariant slow manifold, $O(\varepsilon)$ close, with the
  differentiability allowed by the vector field and spectral gap.
* **61. Stable fibers and tracking.** Its stable and unstable
  manifolds and fiber foliations persist. In normally attracting
  directions, nearby trajectories approach the slow manifold
  exponentially in fast time and track a slow trajectory along stable fibers.
* **62. Elementary boundary layer.** For
  $\varepsilon u''+u'=f$ on $[0,1]$, $u(0)=\alpha$, $u(1)=\beta$,
  the reduced solution is $u_0(x)=\beta-\int_x^1f(t)dt$.
  For $f\in C^1$, $u_0(x)+(\alpha-u_0(0))e^{-x/\varepsilon}$
  approximates $u$ uniformly with error $O(\varepsilon)$.
* **69. Matching principle and composite expansion.** Let an outer
  expansion $u^o\sim\sum\varepsilon^nu^o_n(x)$ hold away from a layer at
  $x=0$, and an inner expansion $u^i\sim\sum\varepsilon^nU_n(X)$ in the
  stretched variable $X=x/\delta(\varepsilon)$, $\delta\to0$. Van Dyke's
  matching principle requires the $m$-term inner expansion of the
  $n$-term outer expansion to equal the $n$-term outer expansion of the
  $m$-term inner expansion, both written in one variable; Kaplun's
  intermediate matching requires agreement in $x=\eta\xi$ with
  $\delta\ll\eta\ll1$. The composite $u^c=u^o+u^i-(u^o)^i$, with
  $(u^o)^i$ the common part, is then uniformly valid to the matched
  order. In entry 62, $U_0(\infty)=u_0(0)$ gives exactly the stated
  approximant. The construction is formal; it is justified by an
  estimate such as entry 63.
* **70. Location of boundary layers.** Let $a,b,f\in C^\infty[0,1]$ and
  $a>0$. For all sufficiently small $\varepsilon>0$,
  $\varepsilon u''+a(x)u'+b(x)u=f$, $u(0)=\alpha$, $u(1)=\beta$, has a
  unique solution, and
  $u(x)=u_0(x)+(\alpha-u_0(0))e^{-a(0)x/\varepsilon}+O(\varepsilon)$
  uniformly, where $au_0'+bu_0=f$, $u_0(1)=\beta$; higher-order matched
  expansions hold to all orders. If $a<0$ the layer is at $x=1$; zeros of
  $a$ produce turning points with interior or corner layers (O'Malley).
* **63. Residual control by comparison.** For
  $L_\varepsilon=-\varepsilon d^2/dx^2+a(x)d/dx+c(x)$,
  $c\geq c_0>0$, the maximum principle gives
  $\|u-v\|_\infty\leq
  \max_{\partial I}|u-v|+c_0^{-1}\|L_\varepsilon(u-v)\|_\infty$.
  A matched construction becomes a uniform approximation once its
  boundary and residual errors are controlled.
* **65. Second-order zero-mean averaging.** For $\dot x=\varepsilon f(t,x)$
  with $T$-periodic $t$ dependence, first-order averaging compares
  solutions with those of $\dot y=\varepsilon\bar f(y)$,
  $\bar f=T^{-1}\int_0^Tf(t,\cdot)dt$, on times $O(\varepsilon^{-1})$
  (SYNOPSIS31, items 49–50). If $\bar f=0$, let
  $u(t,x)$ be the periodic zero-mean antiderivative of $f$ in $t$.
  The near-identity change $x=y+\varepsilon u(t,y)$ removes the
  order-$\varepsilon$ term, and the solution of
  $\dot y=\varepsilon^2\,\overline{D_xf\,u}(y)$ approximates $x$
  with error $O(\varepsilon)$ on times $O(\varepsilon^{-2})$, given
  uniformly bounded derivatives through order three and solutions
  remaining in a common compact domain.
* **67. Poincaré–Lindstedt method.** For
  $\ddot x+x+\varepsilon g(x,\dot x)=0$, the naive expansion in
  $\varepsilon$ has secular terms such as $t\sin t$ and is valid only
  for $t=O(1)$. Expanding the frequency as well, $\tau=\omega t$ with
  $\omega=1+\varepsilon\omega_1+\cdots$, and removing resonant terms
  at each order yields uniformly valid periodic expansions; for the
  Duffing equation $g=x^3$ the periodic orbit of amplitude $a$ has
  $\omega=1+\tfrac38\varepsilon a^2+O(\varepsilon^2)$. Two-timing
  reproduces the first-order averaged amplitude–phase equations.
* **71. Method of multiple scales.** For
  $\ddot x+x+\varepsilon h(x,\dot x)=0$ with smooth $h$, set $\tau=\varepsilon t$
  and $x=A(\tau)\cos(t+\varphi(\tau))+\varepsilon x_1(t,\tau)+\cdots$.
  Removing secular terms from $x_1$ gives
  $A'=\frac1{2\pi}\int_0^{2\pi}h(A\cos\theta,-A\sin\theta)\sin\theta\,d\theta$
  and
  $A\varphi'=\frac1{2\pi}\int_0^{2\pi}h(A\cos\theta,-A\sin\theta)\cos\theta\,d\theta$.
  These are the first-order averaged equations in amplitude–phase variables,
  so the leading term is $O(\varepsilon)$ accurate on $t=O(\varepsilon^{-1})$
  while $A$ stays in a compact subset of $(0,\infty)$. For Van der Pol,
  $h=-(1-x^2)\dot x$, one gets $A'=\frac A2(1-\frac{A^2}4)$, a limit cycle
  of amplitude $2$.
* **68. Rayleigh–Schrödinger perturbation.** Let $A$ be self-adjoint,
  $B$ bounded and symmetric, and $\lambda_0$ an isolated simple eigenvalue
  of $A$ with unit eigenvector $\phi_0$ and reduced resolvent $S$.
  Then $A+\varepsilon B$ has a unique eigenvalue near $\lambda_0$
  for small $|\varepsilon|$, analytic in $\varepsilon$, with
  $\lambda(\varepsilon)=\lambda_0+\varepsilon\langle B\phi_0,\phi_0\rangle
  -\varepsilon^2\langle SB\phi_0,B\phi_0\rangle+O(\varepsilon^3)$;
  for discrete spectrum
  $-\langle SB\phi_0,B\phi_0\rangle=\sum_{k\ne0}
  |\langle B\phi_0,\phi_k\rangle|^2/(\lambda_0-\lambda_k)$.
  Analytic families and degenerate eigenvalues are treated in Section 22.

## Reference guide

Olver, Wong, de Bruijn, Bleistein–Handelsman, Erdélyi, and Copson
share the expansion and integral core. Paris–Kaminski and Paris develop
Mellin–Barnes and exponentially improved methods; Flajolet–Sedgewick
connects the same complex-analytic mechanisms with coefficients.
Wasow, Fedoryuk, Olver, White, and Miller develop differential-equation
asymptotics and turning points. Costin, Balser, Mitschi–Sauzin,
Loday-Richaud, and Delabaere supply summability and resurgence;
Sabbah gives their Stokes-structure formulation. Kawai–Takei and
Honda–Kawai–Takei develop exact WKB. The singular-perturbation
texts and Sanders–Verhulst–Murdock give the reduction and averaging
theorems needed to justify long-time or layered approximations.

Local full-text sources consulted:

* [Olver, *Asymptotics and Special Functions*](References/Olver1997AsymptoticsSpecialFunctions-AKPeters.pdf).
* [Wong, *Asymptotic Approximations of Integrals*](References/Wong2001AsymptoticApproximationIntegrals-SIAM.Classics.pdf).
* [Paris–Kaminski, *Asymptotics and Mellin–Barnes Integrals*](References/ParisKaminski2001AsymptoticsMellinBarnesIntegrals-CambridgeEMA85.pdf).
* [White, *Asymptotic Analysis of Differential Equations*](References/White2010AsymptoticAnalysisDifferentialEquationsRevEd-ImperialCollegePress.pdf).
* [Loday-Richaud, *Divergent Series, Summability and Resurgence II*](References/LodayRichaud2016DivergentSeriesSummabilityResurgenceII-Springer.LNM2154.pdf).
* [Delabaere, *Divergent Series, Summability and Resurgence III*](References/Delabaere2016DivergentSeriesSummabilityResurgenceIII-Springer.LNM2155.pdf).
* [Sabbah, *Introduction to Stokes Structures*](References/Sabbah2013StokesStructures-Springer.LNM2060.pdf).
* [Shchepakina–Sobolev–Mortell, *Singular Perturbations*](References/ShchepakinaSobolevMortell2014SingularPerturbationsIntroductionSystemOrderReductionMethodsApplications-SpringerLNM2114.pdf).
* [Sanders–Verhulst–Murdock, *Averaging Methods in Nonlinear Dynamical Systems*](References/SandersVerhulstMurdock2007AveragingMethodsNonlinearDynamicalSystems2ndEd-SpringerAMS59.pdf).
* [Flajolet–Sedgewick, *Analytic Combinatorics*](References/FlajoletSedgewick2009AnalyticCombinatorics-Cambridge.pdf).

The linked exact-WKB paper was used to check the saddle-free summability
formulation; its cluster-algebra continuation is outside this selection.
