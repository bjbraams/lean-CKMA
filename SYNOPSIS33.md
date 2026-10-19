# Synopsis: Elliptic and parabolic equations — regularity, free boundaries, and viscosity solutions

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-33);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring material from Section 33 of
[CKMA-bib.md](CKMA-bib.md#ckma-33).
It develops the regularity theory beyond the basic linear framework of
Section 32: rough coefficients, quasilinear, fully nonlinear and degenerate
equations, viscosity solutions including first-order Hamilton–Jacobi
equations, nonlinear diffusion, and free boundaries. Scalar
equations and systems are distinguished, as are interior and boundary estimates.

Hamilton–Jacobi and viscosity methods connect with stochastic control in
[08C](CKMA-bib.md#ckma-08c) and optimization in Section 12; Monge–Ampère
equations connect with transport in [39C](CKMA-bib.md#ckma-39c). The
hyperbolic and dispersive branches are identified separately in
[34A](CKMA-bib.md#ckma-34a)–[34B](CKMA-bib.md#ckma-34b).

Write $\Delta=\sum_i\partial_i^2$. Uniform ellipticity of a matrix means
$\lambda|\xi|^2\leq a^{ij}(x)\xi_i\xi_j$ and $|A(x)|\leq\Lambda$,
with $0<\lambda\leq\Lambda<\infty$. Repeated indices are summed.
Unless stated otherwise, estimates are local on concentric interior balls;
constants depend on dimension, ellipticity, the indicated coefficient norms,
and the separation of the two balls. Hölder exponents lie in $(0,1)$.

## Weak solutions and rough-coefficient elliptic regularity

Variational $H_0^1$ existence for divergence-form equations and the linear
parabolic energy theory are stated in Section 32 (SYNOPSIS32, items 24
and 44).

* **2. Weak comparison.** If $-\operatorname{div}(A\nabla u)
  \leq-\operatorname{div}(A\nabla v)$ weakly and $(u-v)^+\in H_0^1$,
  then $u\leq v$ almost everywhere. A nonnegative zeroth-order term
  preserves the conclusion.
* **3. Caccioppoli estimate.** If $\operatorname{div}(A\nabla u)=0$,
  then $\int_{B_r}|\nabla u|^2\leq Cr^{-2}\int_{B_{2r}}|u-c|^2$
  for every constant $c$ and $B_{2r}\Subset\Omega$.
  Cutoff-energy arguments give variants with forcing and lower-order terms.
* **4. Local boundedness.** For weak solutions of the same equation,
  $\|u\|_{L^\infty(B_r)}\leq
  C(r^{-n}\int_{B_{2r}}|u|^2)^{1/2}$. Subsolutions satisfy the
  corresponding estimate for their positive parts.
* **5. Weak Harnack inequality.** For nonnegative weak supersolutions
  of $-\operatorname{div}(A\nabla u)\geq0$, there is $q>0$ with
  $(\fint_{B_r}u^q)^{1/q}\leq C\operatorname*{ess\,inf}_{B_r}u$,
  assuming the equation on a sufficiently larger concentric ball.
* **6. De Giorgi–Nash–Moser Harnack inequality.** A nonnegative weak
  solution satisfies $\operatorname*{ess\,sup}_{B_r}u
  \leq C\operatorname*{ess\,inf}_{B_r}u$ if $B_{2r}\Subset\Omega$.
  Only bounded measurability of the scalar equation's coefficients is needed.
* **7. Hölder continuity.** Weak solutions have a locally Hölder
  representative, with exponent and estimates depending only on $n$
  and ellipticity. In particular bounded measurable coefficients do
  not prevent scalar solutions from being continuous.
* **8. Hilbert's nineteenth problem.** If $F$ is smooth and uniformly
  convex with $\lambda I\leq D^2F\leq\Lambda I$, scalar local minimizers
  of $\int F(\nabla u)$ in $H^1$ are $C^\infty$, and analytic when $F$ is
  analytic (De Giorgi, Nash). Difference quotients put $\partial_ku$ in
  $H^1$, De Giorgi–Nash–Moser applied to the differentiated equation gives
  $u\in C^{1,\alpha}$, and Schauder theory bootstraps.
* **9. Higher integrability of the gradient.** There is $\varepsilon>0$
  depending only on dimension and ellipticity such that homogeneous
  weak solutions have $\nabla u\in L^{2+\varepsilon}_{\mathrm{loc}}$,
  with reverse Hölder bounds. The inhomogeneous estimate applies to
  $-\operatorname{div}(A\nabla u)=\operatorname{div}f$ for
  $f\in L^{2+\varepsilon}$ in the corresponding local range.
* **10. Scalar regularity does not extend to general systems.** In
  dimensions at least three, uniformly elliptic systems with bounded
  measurable coefficients can have discontinuous, even unbounded, weak
  solutions (De Giorgi); in dimension two weak solutions are Hölder
  continuous (Morrey). The scalar
  maximum-principle and Harnack mechanisms are unavailable in general.
* **11. Partial regularity of minimizers.** For smooth uniformly convex
  integrands $f(Du)$ with quadratic growth and bounded positive Hessian,
  vector-valued energy minimizers are $C^{1,\alpha}$ on an open set
  of full measure (Giaquinta–Giusti, Evans). Singular minimizers exist
  in high dimensions even for smooth uniformly convex integrands
  (Nečas, Šverák–Yan).

## Classical estimates and nondivergence equations

* **12. Weak maximum principle.** If
  $Lu=a^{ij}u_{ij}+b^iu_i+cu$, $c\leq0$, and $Lu\geq0$,
  then $\sup_\Omega u\leq\sup_{\partial\Omega}u^+$ on bounded domains,
  under boundedness and ellipticity assumptions and classical boundary continuity.
* **13. Strong maximum and Hopf principles.** A nonconstant solution
  under the preceding maximum-principle hypotheses cannot attain a
  nonnegative interior maximum. At a boundary maximum admitting an
  interior tangent ball, its outward normal derivative is strictly positive
  when that derivative exists and the coefficients satisfy the standard bounds.
* **14. Alexandrov–Bakelman–Pucci estimate.** For $u\in W^{2,n}(\Omega)
  \cap C(\overline\Omega)$, $\Omega$ bounded, and uniformly elliptic $A$,
  $\sup_\Omega u\leq\sup_{\partial\Omega}u^+
  +C\operatorname{diam}(\Omega)\|(a^{ij}u_{ij})^-\|_{L^n(\Omega)}$.
* **15. Krylov–Safonov theorem.** Nonnegative strong solutions of
  $a^{ij}(x)u_{ij}=0$ with measurable uniformly elliptic coefficients
  satisfy interior Harnack inequalities. General solutions have interior
  Hölder estimates with universal positive exponent.
* **16. Interior Schauder estimate.** If $a^{ij},b^i,c,f\in C^{0,\alpha}$
  and $Lu=f$, then on $\Omega'\Subset\Omega$,
  $\|u\|_{C^{2,\alpha}(\Omega')}\leq
  C(\|u\|_{C^0(\Omega)}+\|f\|_{C^{0,\alpha}(\Omega)})$.
  Smooth enough boundary and $C^{2,\alpha}$ Dirichlet data give the
  corresponding global estimate up to the boundary.
* **17. Boundary Schauder theory.** On a bounded $C^{2,\alpha}$ domain,
  the preceding coefficient assumptions and $C^{2,\alpha}$ Dirichlet
  data give a global estimate of the same order. With $c\leq0$,
  the Dirichlet problem is uniquely solvable in $C^{2,\alpha}$.
* **18. Interior $W^{2,p}$ estimates.** For $1<p<\infty$, continuous
  uniformly elliptic leading coefficients and bounded lower-order
  coefficients give local $W^{2,p}$ estimates for strong solutions,
  controlled by $\|Lu\|_p$ and $\|u\|_p$ on a larger set.
  A coefficient modulus of continuity enters the estimate.
* **19. Divergence-form Schauder estimate.** If $A,f\in C^{0,\alpha}$
  and $-\operatorname{div}(A\nabla u)=\operatorname{div}f$, weak
  solutions are locally $C^{1,\alpha}$, with bounds from the data
  and a local norm of $u$.
* **20. Method of continuity.** A uniformly bounded inverse estimate
  along a continuous family of bounded linear operators between fixed
  Banach spaces makes the set of invertible parameters both open and
  closed, provided it is nonempty. Elliptic a priori estimates therefore
  transfer solvability from a model operator to the target operator.
* **21. Symmetry and Liouville theorems.** If $f$ is locally Lipschitz and
  $u\in C^2(\overline B)$ is a positive solution of $\Delta u+f(u)=0$ in a
  ball with $u=0$ on the boundary, then $u$ is radially symmetric and
  strictly decreasing in $|x|$ (moving planes; Gidas–Ni–Nirenberg for
  $f\in C^1$, Berestycki–Nirenberg for locally Lipschitz $f$). For
  $n\geq3$, nonnegative solutions of $-\Delta u=u^q$ on $\mathbb R^n$
  vanish when $1<q<(n+2)/(n-2)$ (Gidas–Spruck), and for
  $q=(n+2)/(n-2)$ they are $0$ or the functions
  $c_n(\varepsilon/(\varepsilon^2+|x-x_0|^2))^{(n-2)/2}$,
  $c_n=(n(n-2))^{(n-2)/4}$
  (Caffarelli–Gidas–Spruck).

## Quasilinear equations

Consider $Qu=a^{ij}(x,u,Du)u_{ij}+b(x,u,Du)$, elliptic in
$\overline\Omega\times\mathbb R\times\mathbb R^n$, on a bounded domain.

* **73. Leray–Schauder reduction to a priori estimates.** Let
  $\partial\Omega\in C^{2,\alpha}$, $\varphi\in C^{2,\alpha}(\overline\Omega)$,
  and $a^{ij},b\in C^\alpha$. If for some $\beta>0$ every $C^{2,\alpha}$
  solution of $a^{ij}(x,u,Du)u_{ij}+\sigma b(x,u,Du)=0$, $u=\sigma\varphi$
  on $\partial\Omega$, $0\leq\sigma\leq1$, satisfies
  $\|u\|_{C^{1,\beta}(\overline\Omega)}\leq M$ with $M$ independent of
  $u$ and $\sigma$, then $Qu=0$, $u=\varphi$ on $\partial\Omega$, has a
  $C^{2,\alpha}$ solution. The proof applies the Leray–Schauder fixed-point
  theorem to the map that freezes the coefficients and solves the linear
  Schauder problem.
* **74. Hölder gradient estimates.** For $a^{ij}\in C^1$, $b\in C^0$,
  $\partial\Omega\in C^2$ and $C^2$ boundary values, solutions of $Qu=0$
  satisfy a global $C^{1,\gamma}$ estimate with $\gamma>0$ and the bound
  depending only on $n$, the data, and $\sup|u|+\sup|Du|$
  (Ladyzhenskaya–Ural'tseva). Hence solvability of the Dirichlet problem
  reduces to a priori bounds, in order, for $\sup|u|$, for $|Du|$ on
  $\partial\Omega$ (barriers), and for $|Du|$ in $\Omega$.
* **75. Minimal surface Dirichlet problem.** For a bounded $C^2$ domain,
  $\operatorname{div}(Du/\sqrt{1+|Du|^2})=0$, $u=\varphi$ on
  $\partial\Omega$, is solvable for every $\varphi\in C^0(\partial\Omega)$
  exactly when $\partial\Omega$ has nonnegative mean curvature
  (Jenkins–Serrin). For constant prescribed mean curvature $H$ the
  condition is that the boundary mean curvature be at least
  $n|H|/(n-1)$ (Serrin).
* **76. Minimal-surface gradient estimate.** A $C^2$ solution of the
  minimal surface equation satisfies
  $|Du(y)|\leq C_1\exp(C_2\sup_\Omega(u-u(y))/d)$,
  $d=\operatorname{dist}(y,\partial\Omega)$, with $C_1,C_2$ depending
  only on $n$ (Bombieri–De Giorgi–Miranda; Trudinger). The exponential
  form cannot be improved; it makes solutions compact under uniform bounds.

## Viscosity and fully nonlinear equations

For a continuous **proper degenerate elliptic** operator $G(x,r,p,X)$,
$G$ is nondecreasing in $r$ and nonincreasing in the symmetric matrix $X$.
An upper semicontinuous $u$ is a **viscosity subsolution** of $G=0$ if
$G(x,u,D\phi,D^2\phi)\leq0$ whenever $\phi\in C^2$ touches $u$ from
above. Supersolutions use lower semicontinuity, touching from below, and
the reverse inequality; a continuous solution is both.

* **22. Consistency.** For $C^2$ functions the viscosity and classical
  inequalities agree. For linear uniformly elliptic equations with
  smooth coefficients, continuous distributional and viscosity solutions agree.
* **23. Comparison and uniqueness.** For continuous viscosity sub- and
  supersolutions of $\gamma u+G_0(Du,D^2u)=f(x)$, $\gamma>0$,
  continuous $f$, and continuous degenerate elliptic $G_0$, ordered
  boundary values imply ordered solutions on a bounded domain.
* **24. Perron's construction.** If comparison holds and compatible
  continuous sub- and supersolutions provide boundary barriers, the
  supremum of intervening subsolutions, with semicontinuous envelopes,
  gives the unique continuous Dirichlet solution.
* **25. Stability.** Locally uniform limits of viscosity solutions are
  solutions when their operators converge locally uniformly. Upper and
  lower half-relaxed limits give the corresponding one-sided statements.
* **26. Suprema of subsolutions.** The upper semicontinuous envelope
  of a locally bounded supremum of subsolutions is a subsolution for
  a fixed continuous proper operator.

These foundational forms follow the
[Crandall–Ishii–Lions *User's Guide*](https://arxiv.org/pdf/math/9207212),
with coefficient-dependent comparison requiring its additional structural hypotheses.

For $F(D^2u)=f$, use the increasing convention
$\lambda\operatorname{tr}N\leq F(M+N)-F(M)\leq\Lambda\operatorname{tr}N$
for $N\geq0$. This corresponds to the proper operator $G=f-F$.
The **Pucci extremal operators** are
$\mathcal M^+(M)=\Lambda\sum_{\mu_i>0}\mu_i+\lambda\sum_{\mu_i<0}\mu_i$
and $\mathcal M^-$ with $\lambda,\Lambda$ interchanged.

* **27. Extremal inequalities.** Uniform ellipticity is equivalent to
  $\mathcal M^-(M-N)\leq F(M)-F(N)\leq\mathcal M^+(M-N)$.
  These inequalities place differences of solutions in universal elliptic classes.
* **28. Fully nonlinear Hölder estimates.** Viscosity solutions of the
  two Pucci inequalities with bounded forcing have interior $C^{0,\alpha}$
  estimates. Nonnegative solutions satisfy the corresponding Harnack inequality.
* **29. $C^{1,\alpha}$ regularity.** For translation-invariant uniformly
  elliptic $F$ with $F(0)=0$, bounded viscosity solutions of
  $F(D^2u)=0$ are locally $C^{1,\alpha}$ for a universal $\alpha>0$.
* **30. Evans–Krylov theorem.** If $F$ is uniformly elliptic and convex
  or concave, solutions of $F(D^2u)=f$ with Hölder $f$ have interior
  $C^{2,\beta}$ estimates for some $\beta>0$ controlled by the
  ellipticity and data regularity. Without convexity this fails: in
  dimension two solutions of $F(D^2u)=0$ are $C^{2,\alpha}$ (Nirenberg),
  but in dimensions $n\geq5$ there are viscosity solutions that are not
  $C^{1,1}$ (Nadirashvili–Vlăduţ for $n=5$;
  earlier constructions needed higher dimensions; see also
  Nadirashvili–Tkachev–Vlăduţ).
* **31. Fully nonlinear $W^{2,p}$ regularity.** For convex or concave
  translation-invariant uniformly elliptic $F$, $p>n$, and continuous
  $f\in L^p$, bounded viscosity solutions have local $W^{2,p}$
  estimates in terms of $\|u\|_\infty+\|f\|_p$.

## First-order Hamilton–Jacobi equations

For first-order equations the viscosity definitions above apply with $G$
independent of $X$. Assume $H(x,p)$ is continuous, uniformly continuous on
$\mathbb R^n\times B_R$ for each $R$, and satisfies
$|H(x,p)-H(y,p)|\leq\omega(|x-y|(1+|p|))$ for a modulus $\omega$.

* **77. First-order comparison.** For $\lambda>0$, a bounded uniformly
  continuous viscosity subsolution $u$ and supersolution $v$ of
  $\lambda w+H(x,Dw)=0$ on $\mathbb R^n$ satisfy $u\leq v$
  (Crandall–Lions, Crandall–Evans–Lions). On a bounded open set the same
  holds for $u,v\in C(\overline\Omega)$ with $u\leq v$ on $\partial\Omega$.
  When $H(\cdot,0)$ is bounded, Perron's method then gives a unique
  bounded uniformly continuous solution (Ishii).
* **78. The Cauchy problem.** For $g\in BUC(\mathbb R^n)$,
  $u_t+H(x,Du)=0$, $u(0)=g$, has a unique viscosity solution in
  $BUC(\mathbb R^n\times[0,T])$, and
  $\sup_x|u-v|(t)\leq\sup|g-h|$ for the solutions with data $g,h$.
  If $H$ is Lipschitz in $p$ with constant $L$, data agreeing on
  $B(x_0,R)$ give solutions agreeing on $B(x_0,R-Lt)$. For convex
  superlinear $H=H(p)$ and Lipschitz $g$ the solution is the Hopf–Lax
  formula (SYNOPSIS34, item 14).
* **79. Value functions of optimal control.** Let $A$ be compact,
  $b(x,a)$ bounded continuous and Lipschitz in $x$ uniformly in $a$, and
  $L(x,a)$ bounded continuous and uniformly continuous in $x$ uniformly
  in $a$. For $\lambda>0$ the discounted value function
  $V(x)=\inf_{a(\cdot)}\int_0^\infty e^{-\lambda t}L(y(t),a(t))dt$,
  $\dot y=b(y,a)$, $y(0)=x$, is bounded and uniformly continuous and is
  the unique such viscosity solution of the Hamilton–Jacobi–Bellman
  equation $\lambda V+\sup_a\{-b(x,a)\cdot DV-L(x,a)\}=0$
  (Bardi–Capuzzo-Dolcetta). The finite-horizon analogue is SYNOPSIS36,
  item 65.
* **80. Semiconcavity and a.e. solutions.** Lipschitz functions satisfying
  a first-order equation almost everywhere are not unique: for the eikonal
  problem $|Du|=1$ in a bounded $\Omega$, $u=0$ on $\partial\Omega$, the
  viscosity solution is $\operatorname{dist}(x,\partial\Omega)$, while
  $-\operatorname{dist}$ and many sawtooth functions are a.e. solutions.
  For smooth convex $H(p)$ and Lipschitz $g$, there is at most one
  Lipschitz a.e. solution of $u_t+H(Du)=0$, $u(0)=g$, with the
  one-sided bound $u(x+z,t)-2u(x,t)+u(x-z,t)\leq C(1+1/t)|z|^2$
  (Kruzhkov; Evans). If $D^2H\geq\theta I>0$, the Hopf–Lax solution
  satisfies this bound with $C(1+1/t)$ replaced by $1/(\theta t)$, even
  for nonsemiconcave $g$; semiconcave viscosity solutions are
  differentiable off a countably $(n-1)$-rectifiable set
  (Cannarsa–Sinestrari).

## Degenerate elliptic and Monge–Ampère equations

The **$p$-Laplacian** is
$\Delta_pu=\operatorname{div}(|\nabla u|^{p-2}\nabla u)$, $1<p<\infty$.
A function is $p$-harmonic when this vanishes weakly.

* **32. $p$-energy minimization.** On a bounded Lipschitz domain,
  $\int|\nabla u|^p/p-\langle f,u\rangle$ has a unique minimizer
  in each prescribed $W^{1,p}$ trace class for
  $f\in W^{-1,p'}$. Its Euler equation is $-\Delta_pu=f$.
* **33. Nonlinear comparison.** Weak $p$-subsolutions and
  $p$-supersolutions with ordered traces are ordered in the domain,
  by strict monotonicity of $\xi\mapsto|\xi|^{p-2}\xi$.
* **34. $p$-harmonic regularity.** Weak $p$-harmonic functions are
  locally $C^{1,\alpha}$ for some $\alpha=\alpha(n,p)>0$.
  Nonnegative ones satisfy scale-invariant Harnack estimates.
* **35. The infinity-harmonic limit.** For Lipschitz boundary data on
  a bounded domain, absolutely minimizing Lipschitz extensions are
  characterized by the viscosity equation
  $\Delta_\infty u=\langle D^2u\nabla u,\nabla u\rangle=0$.
  The extension is unique, and uniform limits of the corresponding
  $p$-harmonic extensions as $p\to\infty$ give it.

For convex $u$, its **Alexandrov Monge–Ampère measure** is
$\operatorname{MA}_u(E)=|\partial u(E)|$, the Lebesgue measure of the
subgradient image. For $C^2$ convex $u$, it equals $\det D^2u\,dx$.

* **36. Alexandrov stability and comparison.** Locally uniform convergence
  of convex functions gives weak convergence of their Monge–Ampère
  measures. Ordered boundary data and the reverse ordering of these
  measures imply the corresponding ordering of the convex functions.
* **37. Alexandrov Dirichlet problem.** On a bounded strictly convex
  domain, continuous boundary data and a finite nonnegative interior
  measure determine a unique continuous convex Alexandrov solution.
* **38. Interior Monge–Ampère regularity.** Strictly convex Alexandrov
  solutions with $0<\lambda\leq f\leq\Lambda$ are locally
  $C^{1,\alpha}$; Hölder $f$ gives local $C^{2,\alpha}$ regularity.
  Section geometry and strict convexity enter the estimates. Strict
  convexity is automatic in dimension two but not for $n\geq3$, where
  Pogorelov's solutions of $\det D^2u=1$ contain line segments and are
  not $C^{1,1}$.
* **39. Smooth Monge–Ampère Dirichlet theory.** Smooth uniformly convex
  domains, smooth boundary data, and smooth strictly positive density
  give a smooth strictly convex solution up to the boundary.

## Parabolic regularity and nonlinear diffusion

Parabolic cylinders use time scale $r^2$. The Hölder space
$C^{\alpha,\alpha/2}$ measures space with exponent $\alpha$ and time with
exponent $\alpha/2$; $W^{2,1}_p$ controls two spatial derivatives and one
time derivative in $L^p$.

* **41. Parabolic strong maximum principle.** A nonnegative solution
  of a uniformly parabolic scalar equation cannot vanish at an interior
  point unless it vanishes throughout the connected region reachable
  backward in time, under the maximum-principle sign condition.
* **42. Parabolic Harnack inequality.** Positive solutions with bounded
  measurable divergence coefficients satisfy
  $\sup_{Q^-}u\leq C\inf_{Q^+}u$ for separated earlier and later
  subcylinders inside a larger cylinder. The time separation is essential.
* **43. Parabolic De Giorgi–Nash regularity.** Energy solutions of
  scalar homogeneous uniformly parabolic divergence equations are
  locally Hölder continuous in the parabolic metric, with universal exponent.
* **44. Parabolic Schauder theory.** Coefficients and forcing in
  $C^{\alpha,\alpha/2}$ give interior
  $C^{2+\alpha,1+\alpha/2}$ estimates. Boundary versions require the
  matching spatial boundary smoothness and initial–boundary compatibility.
* **45. Parabolic $L^p$ estimates.** Smooth uniformly parabolic
  coefficients give local $W^{2,1}_p$ estimates for $1<p<\infty$.
  These yield strong solvability with the corresponding initial and
  lateral traces under compatibility conditions.
* **46. Gaussian fundamental-solution bounds.** For
  $u_t=\operatorname{div}(A(t,x)\nabla u)$ on all of $\mathbb R^n$,
  bounded measurable uniformly elliptic $A$ gives a positive kernel
  bounded above and below by constant multiples of
  $(t-s)^{-n/2}\exp(-c|x-y|^2/(t-s))$, with different positive constants.
* **47. Semilinear local existence and continuation.** For
  $u_t-\Delta u=f(u)$ with locally Lipschitz $f$, bounded continuous
  initial data have a unique local bounded mild solution. A finite
  maximal time requires $\|u(t)\|_\infty\to\infty$.
* **48. Sub- and supersolution trapping.** Ordered parabolic sub- and
  supersolutions trap the semilinear solution as long as it exists.
  A global bounded supersolution therefore prevents blowup.
* **49. Fujita exponent.** For $u_t-\Delta u=u^q$ on $\mathbb R^n$,
  $q>1$, every nontrivial nonnegative bounded compactly supported
  initial datum gives finite-time blowup if $q\leq1+2/n$.
  For $q>1+2/n$, sufficiently small nonnegative data in
  $L^1\cap L^\infty$ yield global solutions.
* **50. Reaction–diffusion energy.** For zero Dirichlet data and
  $F'=f$, smooth solutions satisfy
  $\frac d{dt}\int(\tfrac12|\nabla u|^2-F(u))=-\int|u_t|^2$.
  This is a Lyapunov functional for semilinear gradient diffusion.
* **51. Degenerate parabolic Hölder continuity.** Locally bounded
  weak solutions of $u_t-\Delta_pu=0$, $p\geq2$, are locally
  Hölder continuous. Their natural cylinders have time length
  $\omega^{2-p}r^p$ at spatial scale $r$ and oscillation scale $\omega$.
* **52. Intrinsic Harnack inequality.** For nonnegative solutions of
  the parabolic $p$-Laplacian with $p>2$, the value at an interior
  point controls a later spatial infimum at waiting time comparable
  to $u(x_0,t_0)^{2-p}r^p$, provided the enlarged intrinsic cylinder
  lies in the domain.
* **53. Porous-medium contraction and propagation.** For
  $u_t=\Delta(u^m)$, $m>1$, nonnegative $L^1$ data generate an
  $L^1$ contraction evolution preserving mass. Bounded compactly
  supported data remain compactly supported for finite times.
* **54. Barenblatt solutions.** The porous-medium equation has
  mass-parametrized solutions
  $$
  u(t,x)=t^{-a}\bigl(C-k|x|^2t^{-2b}\bigr)_+^{1/(m-1)},\quad
  b=\frac1{n(m-1)+2},\quad a=nb,\quad k=\frac{b(m-1)}{2m}.
  $$
  Their support radius is proportional to $t^b$.

## The classical obstacle problem

For a smooth obstacle $\psi$ and compatible trace $g\geq\psi$, minimize
$\int_\Omega(\tfrac12|\nabla u|^2-fu)$ over
$K=\{u\in H^1:u|_{\partial\Omega}=g,\ u\geq\psi\}$.
The **contact set** is $\{u=\psi\}$ and the **free boundary** is its
boundary inside $\Omega$. The normalized local model is
$u\geq0$, $\Delta u=1_{\{u>0\}}$.

* **55. Variational inequality.** The minimizer exists uniquely and
  satisfies $\int\nabla u\cdot\nabla(v-u)\geq\int f(v-u)$
  for every $v\in K$. This is equivalent to minimization.
* **56. Complementarity.** Distributionally $-\Delta u-f\geq0$;
  on $\{u>\psi\}$, $-\Delta u=f$. For smooth solutions this
  is the complementarity system
  $(u-\psi)(-\Delta u-f)=0$, $u\geq\psi$.
* **57. Optimal solution regularity.** For smooth forcing and a
  $C^{1,1}$ obstacle, the solution is locally $C^{1,1}$.
  Second derivatives can jump across the free boundary, so higher
  global regularity is not generally available.
* **58. Quadratic growth and nondegeneracy.** At a free-boundary point
  of the normalized model,
  $cr^2\leq\sup_{B_r}u\leq Cr^2$ for all sufficiently small $r$.
* **59. Blowup compactness.** The rescalings
  $u_{x_0,r}(x)=u(x_0+rx)/r^2$ have subsequences converging locally
  in $C^{1,\alpha}$ to nonzero global solutions of the obstacle problem.
  Weiss's monotonicity formula makes every blowup homogeneous of degree two.
* **60. Classification of quadratic blowups.** Blowups of the normalized
  classical obstacle problem are either
  $\tfrac12(x\cdot\nu)_+^2$, $|\nu|=1$, or
  $\tfrac12x\cdot Ax$ with $A\geq0$, $\operatorname{tr}A=1$.
  These distinguish regular and singular points.
* **61. Regular free boundary.** Near a point with half-space blowup,
  the free boundary is $C^{1,\alpha}$, and is smooth for the smooth
  classical model. Regular points form a relatively open subset.
* **62. Singular strata.** The quadratic blowup at a singular point
  is unique. Points where its matrix has kernel dimension $k$ lie
  locally in countably many $k$-dimensional $C^1$ submanifolds,
  for $0\leq k\leq n-1$.

## One-phase free boundaries and nonlocal regularity

For $Q>0$ constant, the **one-phase energy** is
$J(u)=\int(|\nabla u|^2+Q^2 1_{\{u>0\}})$, minimized among
nonnegative functions with fixed trace. Its free boundary is
$\partial\{u>0\}$ inside the domain.

* **63. One-phase existence and harmonicity.** The energy has minimizers
  for nonnegative admissible $H^1$ traces on bounded Lipschitz domains.
  Every minimizer is harmonic in its positivity set.
* **64. Lipschitz regularity and nondegeneracy.** Local minimizers are
  locally Lipschitz and satisfy $\sup_{B_r(x_0)}u\geq cr$ at
  free-boundary points. Both phases have positive density there.
* **65. Perimeter and measure bounds.** The positivity set has locally
  finite perimeter; its free boundary has locally finite
  $\mathcal H^{n-1}$ measure with two-sided bounds comparable to $r^{n-1}$
  in balls centered on it.
* **66. One-phase blowups.** Rescaling by $u(x_0+rx)/r$ gives
  subsequential global minimizing blowups. Weiss's adjusted-energy
  monotonicity makes these blowups one-homogeneous.
* **67. Improvement of flatness.** Sufficiently flat minimizing free
  boundaries become flatter at smaller scales. Near a half-space blowup
  the free boundary is $C^{1,\alpha}$; in the constant-coefficient model
  it is smooth, with $|\nabla u|=Q$ on its regular part.
* **68. Size of the one-phase singular set.** The regular part is
  relatively open and has full $\mathcal H^{n-1}$ measure.
  The singular set has Hausdorff dimension at most $n-5$; in
  dimensions at most four it is empty. A singular minimizing cone exists
  in dimension seven (De Silva–Jerison), so the sharp critical dimension
  lies in $\{5,6,7\}$.

For $0<s<1$, the **fractional Laplacian** has Fourier multiplier
$|\xi|^{2s}$ under the $e^{-ix\cdot\xi}$ convention, equivalently
$(-\Delta)^su=c_{n,s}\operatorname{pv}\int(u(x)-u(y))|x-y|^{-n-2s}dy$.

* **69. Nonlocal Dirichlet existence and comparison.** The fractional
  Dirichlet energy gives unique weak solutions with prescribed exterior
  values and forcing in the energy dual. Nonnegative forcing and
  exterior values give a nonnegative solution by comparison.
* **70. Fractional interior Schauder estimate.** If $u$ is globally
  bounded and $(-\Delta)^su=f$ with $f\in C^\alpha$ in a ball,
  then $u\in C^{2s+\alpha}$ on smaller balls when $2s+\alpha$
  is not an integer. The estimate includes $\|u\|_{L^\infty(\mathbb R^n)}$.
* **71. Fractional boundary behavior.** On a bounded smooth domain,
  solutions with bounded forcing and zero exterior value satisfy
  $|u(x)|\leq C\operatorname{dist}(x,\partial\Omega)^s$.
  The quotient by this power extends Hölder continuously to the boundary.
* **72. Boundary Harnack principles.** Two positive harmonic functions
  in a Lipschitz domain vanishing on a boundary portion have comparable,
  indeed Hölder continuous, quotient up to that portion (Dahlberg,
  Kemper, Caffarelli–Fabes–Mortola–Salsa); the same holds for
  divergence-form equations with bounded measurable coefficients. For
  positive fractional-harmonic functions vanishing on the exterior portion
  of a smooth boundary, quotients are likewise comparable and Hölder
  continuous near that boundary.

## Reference guide

Gilbarg–Trudinger, Han–Lin, and the Ladyzhenskaya–Ural'tseva books
provide the elliptic estimates; Lieberman, Friedman, and Krylov provide
their parabolic counterparts. Caffarelli–Cabré and the viscosity references
supply the fully nonlinear core; Gilbarg–Trudinger and
Ladyzhenskaya–Ural'tseva the quasilinear Dirichlet problem; and
Bardi–Capuzzo-Dolcetta, Barles, Cannarsa–Sinestrari, and Tran the
first-order Hamilton–Jacobi and control theory. The obstacle and
one-phase results recur in Caffarelli–Salsa, Petrosyan–Shahgholian–Uraltseva, Fernández-Real–Ros-Oton,
and Velichkov, with different emphasis. The nonlinear-potential and
Monge–Ampère monographs develop the degenerate equations separately.
Mean-field systems, detailed singular-set refinements, and specialized
subelliptic calculi are beyond this common selection.

Local source copies consulted:

* [Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*](References/GilbargTrudinger2001EllipticPartialDifferentialEquationsSecondOrder-SpringerClassicsGL224.pdf).
* [DiBenedetto, *Partial Differential Equations*](References/DiBenedetto2010PartialDifferentialEquations2ndEd-BirkhaeuserCOR.pdf).
* [Quittner–Souplet, *Superlinear Parabolic Problems*](References/QuittnerSouplet2019SuperlinearParabolicProblemsBlowUpGlobalExistenceSteadyStates2ndEd-BirkhäuserAdvTexts.pdf).
* [DiBenedetto–Gianazza–Vespri, *Harnack's Inequality for Degenerate and Singular Parabolic Equations*](References/DiBenedettoGianazzaVespri2012HarnackInequalityDegenerateSingularParabolicEquations-Springer.SMM.pdf).
* [Velichkov, *Regularity of the One-phase Free Boundaries*](References/Velichkov2023RegularityOnePhaseFreeBoundaries-Springer.LNUMI28.pdf).
* [Fernández-Real–Ros-Oton, *Integro-Differential Elliptic Equations*](References/FernandezRealRosOton2024IntegroDifferentialEllipticEquations-Birkhauser.PM350.pdf).

The Monge–Ampère comparison and regularity statements were also checked
against the authors' exposition
[De Philippis–Figalli, *The Monge–Ampère equation and its link to optimal transportation*](https://people.math.ethz.ch/~afigalli/lecture-notes-pdf/The-Monge-Ampere-equation-and-its-link-to-optimal-transportation.pdf).
