# Synopsis: Integral equations and classical operator methods

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-25);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects the recurring core of Section 25 of
[CKMA-bib.md](CKMA-bib.md#ckma-25): Fredholm
and Volterra equations, singular kernels, layer potentials, boundary
integral reductions, approximation, and regularization. Operator-theoretic
results are retained in the concrete forms used for kernels and boundary
value problems. Multidimensional singular integral operators and their
symbol calculus belong to Sections 27 and 30. Boundary signs are fixed explicitly, since different
references normalize fundamental solutions and double layers differently.

The [inverse-problems route](CKMA-MSC2020.md#inverse-problems) connects these
integral and regularization methods with Section 22, Carleman and microlocal
methods in Sections 30 and 33, and geometric inverse problems in Section 53.

A **Fredholm equation of the second kind** is $(I-\lambda K)u=f$;
an equation of the **first kind** is $Ku=f$. A **Volterra equation**
has integration over the past, for example
$u(t)-\int_0^tk(t,s)u(s)ds=f(t)$. Kernels may be functions or
singular integral kernels; a singular kernel requires a specified limiting
interpretation, not merely a formal integral sign.

## Kernel operators and elementary solution methods

* **1. Continuous kernels.** For compact $D\subset\mathbb R^d$
  and $k\in C(D\times D)$, $Ku(x)=\int_Dk(x,y)u(y)dy$
  is compact on $C(D)$ and on $L^2(D)$. Equicontinuity or approximation
  by finite sums of separated functions proves compactness.
* **2. Schur test.** If $\sup_x\int|k(x,y)|dy\leq a$ and
  $\sup_y\int|k(x,y)|dx\leq b$, then
  $\|K\|_{L^2\to L^2}\leq\sqrt{ab}$. The two separate bounds give
  the corresponding $L^\infty$ and $L^1$ estimates.
* **3. Hilbert–Schmidt kernels.** If $k\in L^2(D\times D)$, its
  integral operator is Hilbert–Schmidt, hence compact, and
  $\|K\|_{S^2}=\|k\|_{L^2}$. Its adjoint has kernel
  $\overline{k(y,x)}$.
* **4. Weakly singular compactness.** If $D$ is bounded, $k$ is continuous
  off the diagonal of $\overline D\times\overline D$, and
  $|k(x,y)|\leq C|x-y|^{-\alpha}$ with $0<\alpha<d$, then $K$ is
  compact on $C(\overline D)$ and $L^2(D)$. Truncating a small diagonal
  neighborhood gives operator-norm approximation by compact kernels.
* **5. Separable kernels.** For $k(x,y)=\sum_{j=1}^na_j(x)b_j(y)$,
  the second-kind equation reduces to the finite linear system
  $c_i-\lambda\sum_j(\int b_i a_j)c_j=\int b_if$, with
  $u=f+\lambda\sum_ja_jc_j$.
* **6. Neumann series.** If $|\lambda|\|K\|<1$, then
  $u=\sum_{n\geq0}\lambda^nK^nf$ is the unique solution. The
  condition $|\lambda|r(K)<1$ also suffices for norm convergence.
* **7. Resolvent kernels.** When the Neumann kernel series converges,
  $R_\lambda(x,y)=\sum_{n\geq1}\lambda^{n-1}k_n(x,y)$ gives
  $u=f+\lambda R_\lambda f$. Iterated kernels satisfy
  $k_{n+1}(x,y)=\int k(x,z)k_n(z,y)dz$.
* **8. Mercer theorem.** A continuous positive definite Hermitian kernel
  on compact $D$ with finite measure of full support has
  $k(x,y)=\sum_n\lambda_ne_n(x)\overline{e_n(y)}$, absolutely and
  uniformly, using its nonzero $L^2$ eigenvalues and continuous eigenfunctions.
  The operator is positive trace class and
  $\sum_n\lambda_n=\int_Dk(x,x)dx$.

## Fredholm theory and spectral expansions

The Fredholm alternative for compact operators and its adjoint solvability
condition are stated in SYNOPSIS15, items 53–54, and the analytic Fredholm
theorem in SYNOPSIS21, item 15.

* **11. Exceptional parameters.** For compact $K$ on a Banach space, the
  noninvertible parameters $\lambda\ne0$ of $I-\lambda K$ are reciprocals
  of nonzero eigenvalues of $K$. They are isolated,
  of finite algebraic multiplicity, with no finite accumulation point.
* **13. Fredholm determinant.** For continuous $k$ on $[a,b]^2$,
  $$d(\lambda)=\sum_{n\geq0}\frac{(-\lambda)^n}{n!}\int_{[a,b]^n}
    \det[k(x_i,x_j)]_{i,j=1}^n\,dx$$
  converges for all $\lambda$ by Hadamard's inequality and is entire. Its
  zeros are exactly the exceptional parameters, and off them the resolvent
  kernel is a ratio $D(x,y;\lambda)/d(\lambda)$ of entire functions given by
  analogous minor series. For trace-class $K$ the determinant
  $\det(I-\lambda K)=\prod_j(1-\lambda\mu_j)$, eigenvalues counted with
  algebraic multiplicity, extends this construction.
* **14. Symmetric-kernel solution.** For compact self-adjoint $K$,
  expansion in an orthonormal eigenbasis reduces the equation to
  $(1-\lambda\mu_j)u_j=f_j$. At an exceptional parameter, the
  matching components of $f$ must vanish; the other components determine
  the solution modulo the eigenspace.
* **15. Stability of second-kind equations.** If $I-K$ is invertible
  and $\|K-K_n\|\to0$, then $I-K_n$ is eventually invertible,
  their inverses converge in norm, and the solutions converge for
  convergent right sides.
* **16. Compact first-kind obstruction.** A compact injective operator
  on an infinite-dimensional Hilbert space cannot have a bounded inverse
  on its range; equivalently, its range is not closed. This is the basic
  source of instability of first-kind equations.

## Volterra equations and fractional integration

For $\alpha>0$, the **Riemann–Liouville integral** is
$I^\alpha f(t)=\Gamma(\alpha)^{-1}\int_0^t(t-s)^{\alpha-1}f(s)ds$.

* **17. Volterra iterates.** For a continuous triangular kernel bounded
  by $M$ on $0\leq s\leq t\leq T$, its operator satisfies
  $\|K^n\|_{C\to C}\leq(MT)^n/n!$. Hence $r(K)=0$.
* **18. Volterra solvability.** Under these hypotheses, $I-\lambda K$
  is invertible for every complex $\lambda$, and successive substitution
  converges uniformly. The solution depends continuously on the data on
  every bounded time interval.
* **20. ODE–Volterra equivalence.** The initial-value problem
  $u'=A(t)u+g(t)$, $u(0)=u_0$, is equivalent to its integrated
  Volterra equation. Continuous coefficients give the unique classical
  solution and a fundamental matrix with nonvanishing determinant.
* **21. Paley–Wiener theorem for convolution equations.** For
  $k\in L^1(\mathbb R_+)$, the resolvent $r=k+k*r$ of
  $u=f+k*u$ on $\mathbb R_+$ lies in $L^1(\mathbb R_+)$ exactly when
  $\hat k(z)=\int_0^\infty e^{-zt}k(t)dt\neq1$ for
  $\operatorname{Re}z\geq0$. Then $u=f+r*f$, and the solution map is
  bounded on $L^p(\mathbb R_+)$ for $1\leq p\leq\infty$.
* **22. Fractional semigroup law.** $I^\alpha I^\beta=I^{\alpha+\beta}$
  on $L^1(0,T)$ for positive $\alpha,\beta$. Fubini and the beta
  integral give the identity.
* **23. Abel inversion.** For $0<\alpha<1$, $I^\alpha u=f$ is
  inverted by $u=(d/dt)I^{1-\alpha}f$ whenever
  $I^{1-\alpha}f$ is absolutely continuous and vanishes at zero.
  These conditions characterize the range on $L^1(0,T)$.
* **24. Weakly singular Volterra equations.** For $\alpha>0$,
  $u-\lambda I^\alpha u=f$ has a unique continuous solution for
  continuous $f$, obtained by iterating the fractional integrals.
  For $f=1$ it is $E_\alpha(\lambda t^\alpha)$, where
  $E_\alpha(z)=\sum_{n\geq0}z^n/\Gamma(1+\alpha n)$.

## Cauchy singular integrals and factorization

Let $\Gamma$ be a smooth positively oriented simple closed plane curve.
Set $C\phi(z)=(2\pi i)^{-1}\int_\Gamma\phi(\zeta)/(\zeta-z)d\zeta$
off the curve and
$S\phi=(\pi i)^{-1}\operatorname{p.v.}\int_\Gamma
\phi(\zeta)/(\zeta-\cdot)d\zeta$ on it. Interior and exterior traces
are denoted by $C_+$ and $C_-$ in this subsection only.

* **25. Plemelj–Sokhotski formulas.** For Hölder densities,
  $C_+\phi=\frac12(I+S)\phi$ and
  $C_-\phi=\frac12(S-I)\phi$. Thus the jump is $\phi$ and the
  average is the principal-value integral.
* **26. Singular integral projections.** $S$ extends boundedly to
  $L^p(\Gamma)$ for $1<p<\infty$ and $S^2=I$.
  The operators $P_\pm=(I\pm S)/2$ are complementary bounded
  projections onto the interior and normalized exterior Hardy boundary spaces.
* **27. Singular integral Fredholm criterion.** For smooth scalar
  $a,b$ on $\Gamma$, $aI+bS$ is Fredholm on $L^p$, $1<p<\infty$,
  exactly when $a+b$ and $a-b$ never vanish. Its index is
  $-\operatorname{wind}((a+b)/(a-b),0)$.
* **28. Riemann–Hilbert problem.** Let $G$ be Hölder continuous and
  nowhere zero on $\Gamma$, $g$ Hölder, and $\kappa=\operatorname{wind}(G,0)$.
  Seek $\Phi$ holomorphic off $\Gamma$, vanishing at infinity, with
  Hölder boundary values satisfying $\Phi_+=G\Phi_-+g$. If
  $\kappa\geq0$ it is solvable for every $g$, with a $\kappa$-dimensional
  family of solutions; if $\kappa<0$ it is solvable exactly when $g$
  satisfies $-\kappa$ linear conditions, and then uniquely. With $0$
  inside $\Gamma$ and $\gamma=C(\log(t^{-\kappa}G))$, the canonical
  function $X=e^\gamma$ inside and $X=z^{-\kappa}e^\gamma$ outside
  satisfies $X_+=GX_-$ and reduces the problem to a Plemelj jump
  problem (Gakhov, Muskhelishvili).
* **29. Scalar Wiener–Hopf factorization.** A nowhere-zero function in
  the Wiener algebra of $\mathbb T$ factors as
  $a=a_-z^\kappa a_+$, where $a_+$ and its inverse have nonnegative
  Fourier frequencies, $a_-$ and its inverse have nonpositive frequencies,
  and $\kappa=\operatorname{wind}(a,0)$.
* **30. Toeplitz and Wiener–Hopf operators.** The associated Toeplitz operator is
  Fredholm of index $-\kappa$ and is invertible exactly when $\kappa=0$.
  In that case factorization gives the inverse through the triangular
  analytic and coanalytic factors. The continuous analogue: for
  $k\in L^1(\mathbb R)$, the Wiener–Hopf operator
  $u\mapsto u-\int_0^\infty k(\cdot-s)u(s)ds$ on $L^2(\mathbb R_+)$ is
  Fredholm exactly when $W(\xi)=1-\int e^{i\xi t}k(t)dt$ never vanishes,
  with index $-\operatorname{wind}(W,0)$ over $-\infty\leq\xi\leq\infty$
  (Krein).

## Laplace layer potentials and boundary operators

Here $\Omega\subset\mathbb R^3$ is bounded with connected smooth
boundary $\Gamma$, outward normal $n$, and
$\Phi(x,y)=1/(4\pi|x-y|)$, so $-\Delta\Phi=\delta$.
Define $S\mu(x)=\int_\Gamma\Phi(x,y)\mu(y)dS_y$ and
$D\eta(x)=\int_\Gamma\partial_{n_y}\Phi(x,y)\eta(y)dS_y$.
Now superscripts $-$ and $+$ mean interior and exterior traces,
respectively, and both normal derivatives use the same outward $n$.
Let $V=\gamma S$, $K$ be the averaged trace of $D$, $K'$ the averaged
normal derivative of $S$, and $W=-\partial_nD$.
In this and the next subsection $S$, $K$, and $\Phi$ have these meanings,
not those of the Cauchy operator, the generic kernel operator, or the
Riemann–Hilbert unknown of 28.

* **31. Green representation.** A smooth harmonic function in $\Omega$
  satisfies $u=S(\partial_nu)-D(\gamma u)$. The same representation
  extends to weak solutions with their Sobolev traces.
* **32. Double-layer jump.**
  $\gamma^-D=-\frac12I+K$ and $\gamma^+D=\frac12I+K$.
  The single layer has equal traces from both sides.
* **33. Normal derivative jump.**
  $\partial_n^-S=\frac12I+K'$ and
  $\partial_n^+S=-\frac12I+K'$. The normal derivative of $D$
  is continuous across the boundary and equals $-W$.
* **34. Sobolev mapping properties.**
  $V:H^{-1/2}(\Gamma)\to H^{1/2}(\Gamma)$,
  $K:H^{1/2}\to H^{1/2}$,
  $K':H^{-1/2}\to H^{-1/2}$, and
  $W:H^{1/2}\to H^{-1/2}$ are bounded. These energy-space mappings
  and jump formulas also hold on bounded Lipschitz boundaries.
* **35. Single-layer coercivity in three dimensions.** $V$ is symmetric
  and $\langle V\mu,\mu\rangle\geq c\|\mu\|_{H^{-1/2}}^2$.
  Consequently $V$ is an isomorphism between the indicated Sobolev spaces.
  The two-dimensional logarithmic case requires a capacity normalization
  or stabilization (61).
* **36. Hypersingular coercivity.** $W$ is symmetric nonnegative,
  has kernel the constants, and is coercive on $H^{1/2}(\Gamma)$
  modulo constants. Compatibility with constants is the corresponding
  solvability condition in $H^{-1/2}$.
* **37. Calderón projector.** The matrix
  $$\mathcal C^-=
     \begin{pmatrix}\frac12I-K&V\\W&\frac12I+K'\end{pmatrix}$$
  is a bounded projection onto interior harmonic Cauchy data. In
  particular $KV=VK'$, $WK=K'W$, and $K^2+VW=\frac14I$.
* **38. Interior Dirichlet equation.** Representing $u=D\eta$ reduces
  the Dirichlet problem to $(-\frac12I+K)\eta=g$. On the smooth
  connected boundary this is invertible, giving the unique harmonic
  function with the prescribed boundary values.
* **39. Interior Neumann equation.** Representing $u=S\mu$ gives
  $(\frac12I+K')\mu=h$. It is solvable exactly when
  $\langle h,1\rangle=0$; the density has a one-dimensional ambiguity
  and the potential is unique modulo constants.
* **40. Symmetrization.** $VK'=KV$ makes $K'$ self-adjoint in the
  single-layer energy inner product. For smooth $\Gamma$ it is compact
  on the energy space and has real spectrum in $[-1/2,1/2]$.
  Compactness need not persist for Lipschitz boundaries.
* **41. Lipschitz domains (Verchota).** If $\Omega$ is a bounded Lipschitz
  domain with connected boundary, Rellich identities show that
  $-\frac12I+K$ is invertible on $L^2(\Gamma)$ and $\frac12I+K'$ is
  invertible on the mean-zero subspace $L^2_0(\Gamma)$, although $K$ need
  not be compact. Hence the $L^2$ Dirichlet and Neumann problems are
  uniquely solvable (modulo constants for Neumann) with nontangential
  maximal function estimates.
* **61. Two-dimensional single layer.** In $\mathbb R^2$ take
  $\Phi(x,y)=-(2\pi)^{-1}\log|x-y|$ and a closed Lipschitz curve $\Gamma$.
  There is a unique equilibrium density $\mu_e\in H^{-1/2}(\Gamma)$ with
  $\langle\mu_e,1\rangle=1$ and $V\mu_e$ constant; that constant is
  $-(2\pi)^{-1}\log\operatorname{cap}(\Gamma)$, where
  $\operatorname{cap}(\Gamma)$ is the logarithmic capacity. $V$ is coercive on
  densities of mean zero, it is an isomorphism
  $H^{-1/2}(\Gamma)\to H^{1/2}(\Gamma)$ exactly when
  $\operatorname{cap}(\Gamma)\neq1$, and it is positive definite when
  $\operatorname{cap}(\Gamma)<1$, for instance when the diameter of
  $\Gamma$ is below $1$. Rescaling the curve therefore restores
  the three-dimensional theory of 35.

## Helmholtz scattering and boundary integral equations

Use $\Phi_k(x,y)=e^{ik|x-y|}/(4\pi|x-y|)$, $k>0$, and its layer
operators with the same signs. An exterior solution is **outgoing** if
it satisfies the Sommerfeld radiation condition
$\partial_ru-iku=o(r^{-1})$ and $u=O(r^{-1})$ in three dimensions.

* **42. Rellich uniqueness.** An outgoing Helmholtz solution with zero
  far-field pattern vanishes in the unbounded exterior component.
  Green's identity then gives uniqueness of the exterior Dirichlet problem.
* **43. Helmholtz jump relations.** Helmholtz layers have the same
  $\pm\frac12I$ jumps as Laplace layers. Their lower-order kernel
  differences are compact between the corresponding boundary energy spaces
  on smooth boundaries.
* **44. Combined-field invertibility.** For the exterior Dirichlet problem
  and real $\eta\ne0$, $u=(D_k-i\eta S_k)\mu$ leads to
  $(\frac12I+K_k-i\eta V_k)\mu=g$. This boundary operator is
  invertible for every real $k>0$ on a smooth connected boundary.
  The combination removes the interior eigenfrequency obstruction of
  the separate layer formulations (Brakhage–Werner).
* **45. Far-field representation.** Outgoing layer potentials have
  $u(x)=e^{ik|x|}u_\infty(\widehat x)/|x|+O(|x|^{-2})$.
  The far field is obtained by replacing $\Phi_k$ with
  $(4\pi)^{-1}e^{-ik\widehat x\cdot y}$, and differentiating this
  expression in $n_y$ for a double layer.
* **46. Analytic dependence.** Boundary integral operators depend
  analytically on complex $k$ away from the dimensional branching
  issues; in three dimensions the kernels are entire in $k$.
  Analytic Fredholm theory therefore gives meromorphic inverses wherever
  the family is Fredholm and invertible at one parameter.

## Electromagnetic and inverse obstacle scattering

Here $D\subset\mathbb R^3$ is a bounded $C^2$ domain with connected
exterior, $\nu$ is its outward normal, $k>0$, and $\Phi_k$ is as above.
The time-harmonic Maxwell equations are $\operatorname{curl}E-ikH=0$,
$\operatorname{curl}H+ikE=0$. An exterior solution is **radiating** if it
satisfies the Silver–Müller condition $H\times x-|x|E\to0$ as
$|x|\to\infty$, uniformly in $x/|x|$. For a sound-soft obstacle let
$u_\infty(\cdot,d)$ be the far-field pattern for incidence $e^{ikx\cdot d}$;
the **far-field operator** is
$(Fg)(\widehat x)=\int_{S^2}u_\infty(\widehat x,d)g(d)\,ds(d)$ on
$L^2(S^2)$.

* **62. Stratton–Chu formula.** A radiating solution $E,H$, continuously
  differentiable outside $\overline D$ and continuous up to $\partial D$,
  satisfies for $x\notin\overline D$
  $$E(x)=\operatorname{curl}\int_{\partial D}\nu\times E\,\Phi_k(x,\cdot)\,ds
    -\frac1{ik}\operatorname{curl}\operatorname{curl}
    \int_{\partial D}\nu\times H\,\Phi_k(x,\cdot)\,ds,$$
  and symmetrically for $H$. The Silver–Müller condition is equivalent to
  the Sommerfeld condition for the Cartesian components, and radiating
  fields have electric far-field patterns as in 45.
* **63. Perfect conductor problem.** For a Hölder continuous tangential
  field $c$ on $\partial D$ with Hölder continuous surface divergence, there
  is exactly one radiating solution with $\nu\times E=c$ on $\partial D$,
  depending continuously on $c$, for every $k>0$. A pure magnetic-dipole
  (vector single-layer) ansatz gives a second-kind equation that fails to
  be uniquely solvable at the interior resonances of $D$; a combined
  magnetic and electric dipole ansatz, with a compact smoothing operator in
  the electric part, is uniquely solvable for all $k>0$. This is the
  Maxwell analogue of 44 (Colton–Kress); Nédélec develops the variational
  setting with tangential trace spaces of order $-1/2$.
* **64. Uniqueness for inverse obstacle scattering.** Two sound-soft
  obstacles whose far-field patterns coincide for infinitely many distinct
  incident directions at one fixed $k$ are equal (Schiffer). Far-field
  patterns for all incident directions at one fixed $k$ determine the
  obstacle together with its boundary condition, sound-soft, sound-hard,
  or impedance (Kirsch–Kress). For a perfect conductor or an impedance
  obstacle the electric far fields for all incident directions and
  polarizations at one fixed $k$ likewise determine the scatterer.
* **65. Factorization method.** Let $D$ be sound-soft and let $k^2$ not be
  a Dirichlet eigenvalue of $-\Delta$ in $D$. Then $F$ is compact and normal,
  and with $\Phi_\infty(\widehat x,z)=(4\pi)^{-1}e^{-ik\widehat x\cdot z}$,
  a point $z\in\mathbb R^3$ lies in $D$ exactly when
  $(F^*F)^{1/4}g=\Phi_\infty(\cdot,z)$ is solvable in $L^2(S^2)$. With an
  eigensystem $(\lambda_n,\psi_n)$ of $F$ this is the Picard condition
  $\sum_n|\langle\Phi_\infty(\cdot,z),\psi_n\rangle|^2/|\lambda_n|<\infty$
  (Kirsch; compare 52). The linear sampling method uses approximate
  solutions of $Fg=\Phi_\infty(\cdot,z)$, whose Herglotz wave functions stay
  bounded in $H^1(D)$ for $z\in D$ and blow up for $z\notin D$ (Colton–Kirsch).

## Galerkin, quadrature, and operator approximation

* **47. Collectively compact approximation theorem.** Suppose $K_nx\to Kx$
  for every $x$, and $\bigcup_nK_n(B_X)$ is relatively compact.
  If $I-K$ is invertible, then $I-K_n$ is eventually invertible with
  uniformly bounded inverses, and their solutions converge for convergent data.
* **48. Projection approximation.** If uniformly bounded finite-rank
  projections $P_n\to I$ strongly and $K$ is compact, then
  $\|(I-P_n)K\|\to0$. Thus projected second-kind equations are stable
  and convergent whenever the limiting equation is invertible.
* **49. Nyström convergence.** For a continuous kernel on a compact
  domain and quadrature rules converging for every continuous function,
  the Nyström operators are collectively compact and pointwise convergent.
  If $I-K$ is invertible on $C$, the quadrature solutions exist for large
  $n$ and $\|u_n-u\|_\infty\leq C\|(K_n-K)u\|_\infty$, so they inherit
  the quadrature error on the exact solution.
* **51. Inf–sup stability.** For Banach spaces $X,Y$, let the variational
  form $a:X\times Y\to\mathbb C$ have bound $M$, and let finite-dimensional trial and test spaces $X_n,Y_n$ have
  equal dimension and
  $\inf_{\|v\|_X=1,v\in X_n}\sup_{\|w\|_Y=1,w\in Y_n}|a(v,w)|
  \geq\beta>0$. If $u$ solves the full equation, its discrete solution
  is unique and satisfies
  $\|u-u_n\|_X\leq(1+M/\beta)\inf_{v\in X_n}\|u-v\|_X$.

## Ill-posed equations and regularization

Let $K:X\to Y$ be compact between Hilbert spaces, with nonzero singular
system $Ke_j=s_jf_j$, $K^*f_j=s_je_j$. The **minimum-norm solution**
of $Ku=f$ is the solution orthogonal to $\ker K$. Noisy data satisfy
$\|f^\delta-f\|\leq\delta$.

* **52. Picard criterion.** $Ku=f$ is solvable exactly when
  $f\perp\ker K^*$ and
  $\sum_j|\langle f,f_j\rangle|^2/s_j^2<\infty$.
  The minimum-norm solution is
  $u^\dagger=\sum_js_j^{-1}\langle f,f_j\rangle e_j$.
* **53. Pseudoinverse.** The Moore–Penrose inverse maps
  $f\in\operatorname{ran}K\oplus\ker K^*$ to the minimum-norm
  least-squares solution. It is bounded exactly when $\operatorname{ran}K$
  is closed.
* **54. Tikhonov minimization.** For $\alpha>0$,
  $\|Ku-f^\delta\|^2+\alpha\|u\|^2$ has the unique minimizer
  $u_\alpha^\delta=(K^*K+\alpha I)^{-1}K^*f^\delta$.
* **55. Tikhonov stability and convergence.**
  $\|u_\alpha^\delta-u_\alpha\|\leq\delta/(2\sqrt\alpha)$.
  For exact solvable data $u_\alpha\to u^\dagger$ as $\alpha\downarrow0$;
  for noisy data, $\alpha\to0$ and $\delta/\sqrt\alpha\to0$ give
  convergence to $u^\dagger$.
* **56. Source-condition rates.** If
  $u^\dagger=(K^*K)^\nu w$, $0<\nu\leq1$, then
  $\|u_\alpha-u^\dagger\|\leq C_\nu\alpha^\nu\|w\|$.
  Balancing bias and noise gives error
  $O(\delta^{2\nu/(2\nu+1)})$ with
  $\alpha\asymp\delta^{2/(2\nu+1)}$ for a bounded source norm.
* **57. Truncated singular values.** Retaining only $s_j\geq a$ gives
  $u_a^\delta=\sum_{s_j\geq a}s_j^{-1}\langle f^\delta,f_j\rangle e_j$,
  with noise error at most $\delta/a$. If $a\downarrow0$ and
  $\delta/a\to0$, it converges to $u^\dagger$ for solvable data.
* **58. Discrepancy principle.** For fixed $\tau>1$, choosing the
  Tikhonov parameter by $\|Ku_\alpha^\delta-f^\delta\|=\tau\delta$
  yields convergence for solvable data as $\delta\to0$, taking
  $u^\delta=0$ when $\|f^\delta\|\leq\tau\delta$. It uses the noise level and
  residual rather than an unknown source norm, and gives the optimal rate
  $O(\delta^{2\nu/(2\nu+1)})$ for source conditions with $\nu\leq1/2$ only.
* **59. Landweber iteration.** If $0<\omega<2/\|K\|^2$, the iteration
  $u_{n+1}=u_n+\omega K^*(f-Ku_n)$, starting at zero, converges to
  the minimum-norm solution for exact solvable data. With noisy data,
  stopping with $n\to\infty$ and $\delta\sqrt n\to0$ regularizes it.
* **60. Conditional stability.** On a compact admissible set $M\subset X$
  where continuous $K$ is injective, its inverse $K(M)\to M$ is
  uniformly continuous. A priori compactness therefore restores stability,
  though it need not provide a Lipschitz or power-law modulus.

## Reference guide

Kress supplies the common operator, potential-theory, singular-integral,
approximation, and regularization spine. Zemyan independently develops
separable kernels, resolvent kernels, Fredholm and Volterra methods, and Abel
equations. Hsiao–Wendland develops the boundary operators, Sobolev mappings,
coercivity, and Calderón projectors; these overlap with McLean, Kenig,
and the modern layer-potential monographs. Colton–Kress
supplies the scattering applications, including the Maxwell equations and
inverse obstacle scattering; Nédélec treats acoustic and electromagnetic
boundary integral equations variationally. Gakhov and Muskhelishvili treat the
Riemann–Hilbert problem; Gohberg–Krupnik and Gohberg–Goldberg–Kaashoek give
the operator-theoretic Wiener–Hopf and Toeplitz theory; Kenig and Medková
treat Lipschitz boundaries. Numerical entries concern analytic
stability and convergence, not implementation recipes; retarded potentials
and advanced nonsmooth-domain theories require their separate function spaces.

Local source copies consulted:

* [Kress, Linear Integral Equations](References/Kress2014LinearIntegralEquations3rdEd-SpringerAMS82.pdf).
* [Zemyan, The Classical Theory of Integral Equations](References/Zemyan2012ClassicalTheoryIntegralEquationsConciseTreatment-Birkhäuser.pdf).
* [Hsiao–Wendland, Boundary Integral Equations](References/HsiaoWendland2008BoundaryIntegralEquations-SpringerAMS164.pdf).
* [Colton–Kress, Inverse Acoustic and Electromagnetic Scattering Theory](References/ColtonKress2013InverseAcousticElectromagneticScattering3rdEd-SpringerAMS93.pdf).
* [Gohberg–Goldberg–Kaashoek, Classes of Linear Operators I](References/GohbergGoldberegKaashoek1990ClassesLinearOperatorsVol1-SpringerOTAA49.pdf).
