# Synopsis: Malliavin calculus, rough paths, and stochastic partial differential equations

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-09);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis follows Section 09's three interacting subdivisions: Malliavin
calculus and infinite-dimensional analysis ([09A](CKMA-bib.md#ckma-09a)),
rough paths and singular-equation methods ([09B](CKMA-bib.md#ckma-09b)), and
stochastic partial differential equations ([09C](CKMA-bib.md#ckma-09c)).
Reconstruction and renormalized model equations are grouped with rough and
singular methods; Hilbert-space, variational, and random-field SPDE are
grouped together. The selection retains their recurring textbook core and
representative singular results rather than an inventory of all equations or
renormalization schemes.

Hilbert spaces are real and separable. On a Gaussian probability space,
$W:H\to L^2(\Omega)$ is **isonormal** if it is linear, centered Gaussian, and
$\mathbb E[W(h)W(k)]=\langle h,k\rangle_H$. Random variables in the Gaussian
parts are measurable with respect to $W$. On Wiener space,
$H=L^2([0,T];\mathbb R^d)$ and $W(h)=\int h\,dB$. Its associated
Cameron–Martin paths are $t\mapsto\int_0^th(s)ds$.

Lettered headings match the bibliography. Numbered results retain their
existing identifiers, including after moves between topical groups, so the
labels remain usable from the gap inventory; they need not run in increasing
order within the file.

**Space-time white noise** on $\mathbb R_+\times\mathbb R^d$ (or
$\mathbb R_+\times\mathbb T^d$) is the centered Gaussian random distribution with
covariance $\mathbb E[\xi(\phi)\xi(\psi)]=\int\phi\psi$.

<a id="synopsis-09a"></a>

## 09A. Malliavin Calculus and Infinite-Dimensional Analysis

Wiener chaos, differentiation, integration by parts, density criteria,
Gaussian approximation, Gaussian measures on Banach spaces, and analysis on
Poisson space follow 09A. The common isonormal and Cameron–Martin
conventions are fixed above.

### Wiener chaos and differential calculus on Gaussian space

A **smooth cylindrical functional** is
$F=f(W(h_1),\ldots,W(h_n))$, with smooth $f$ and sufficient moment bounds.
Its **Malliavin derivative** is
$DF=\sum_i\partial_if(W(h_1),\ldots,W(h_n))h_i$.
The **Wiener chaos** of order $q$ is the closed span of degree-$q$ Hermite
polynomials of Gaussian coordinates, orthogonalized against lower degrees.
Write $I_q(f)$ for the multiple Wiener integral of a symmetric tensor
$f\in H^{\odot q}$, with $I_0(c)=c$.

* **1. Wiener chaos decomposition.** Every $F\in L^2(\Omega)$ has a unique
  expansion $F=\sum_{q\geq0}I_q(f_q)$, convergent in $L^2$, and
  $\mathbb EF^2=\sum_{q\geq0}q!\|f_q\|^2$.

* **2. Multiple-integral isometry.**
  $\mathbb E[I_p(f)I_q(g)]=1_{\{p=q\}}q!\langle f,g\rangle$.
  Thus $f\mapsto I_q(f)/\sqrt{q!}$ is an isometry of $H^{\odot q}$ onto the
  $q$th chaos. On Wiener space, $I_q(f)=q!\int_{0<t_1<\cdots<t_q<T}
  f(t_1,\ldots,t_q)\,dB_{t_1}\cdots dB_{t_q}$ is an iterated Itô integral.

* **3. Product formula.** For symmetric tensors,
  $$I_p(f)I_q(g)=\sum_{r=0}^{p\wedge q}
    r!\binom pr\binom qr I_{p+q-2r}(f\widetilde\otimes_r g),$$
  where $\otimes_r$ contracts $r$ pairs of tensor variables and the tilde
  symmetrizes the remaining ones.

* **4. Closability and Sobolev spaces.** The cylindrical derivative is closable
  from $L^p(\Omega)$ to $L^p(\Omega;H)$ for $1\leq p<\infty$. Its iterates define
  the Banach spaces $\mathbb D^{k,p}$ with norm
  $\|F\|_{k,p}^p=\mathbb E|F|^p+\sum_{j=1}^k\mathbb E\|D^jF\|^p$.

* **5. Chain and product rules.** For $F\in\mathbb D^{1,p}$ and a $C^1$
  function with bounded derivative,
  $D\phi(F)=\phi'(F)DF$. Vector versions hold componentwise. Products obey
  $D(FG)=FDG+GDF$ when the factors and products have the indicated Sobolev
  integrability; a Lipschitz outer function has the corresponding weak chain rule.

* **6. Chaos description of differentiation.** A chaos expansion belongs to
  $\mathbb D^{1,2}$ exactly when $\sum_{q\geq1}q\,q!\|f_q\|^2<\infty$;
  then $D_tI_q(f)=qI_{q-1}(f(\cdot,t))$ in the Wiener realization.
  For $F\in\mathbb D^{q,2}$ the kernels are given by Stroock's formula
  $f_q=\frac1{q!}\mathbb E[D^qF]$.

* **7. Gaussian integration by parts.** For deterministic $h\in H$,
  $\mathbb E\langle DF,h\rangle=\mathbb E[FW(h)]$. More generally the
  **divergence** $\delta$, the $L^2$ adjoint of $D$, is characterized by
  $\mathbb E[F\delta(u)]=\mathbb E\langle DF,u\rangle$ on its adjoint domain.

* **8. Divergence product rule and isometry.** Under the requisite Sobolev
  integrability, $\delta(Fu)=F\delta(u)-\langle DF,u\rangle$.
  For $u\in\mathbb D^{1,2}(L^2[0,T])$,
  $$\mathbb E\delta(u)^2=\mathbb E\|u\|_H^2+
    \mathbb E\int_0^T\!\int_0^TD_su_tD_tu_s\,ds\,dt.$$

* **9. Adapted and anticipating integration.** Every square-integrable
  predictable $u$ belongs to the divergence domain and
  $\delta(u)=\int_0^Tu_t\,dB_t$. For nonadapted integrands the divergence,
  also called the Skorohod integral, retains the adjoint characterization;
  the extra term in result 8 records anticipation.

### Ornstein–Uhlenbeck analysis, densities, and normal approximation

The **Ornstein–Uhlenbeck generator** is $LI_q(f)=-qI_q(f)$; on its domain
$L=-\delta D$. The pseudo-inverse is
$L^{-1}F=-\sum_{q\geq1}q^{-1}I_q(f_q)$, annihilating constants.
For $F=(F_1,\ldots,F_m)$, its **Malliavin covariance matrix** is
$\gamma_F=(\langle DF_i,DF_j\rangle_H)_{i,j}$.

* **11. Mehler formula.** The chaos semigroup $P_tI_q=e^{-qt}I_q$ is
  $$P_tF(W)=\mathbb E'[F(e^{-t}W+\sqrt{1-e^{-2t}}W')],$$
  where $W'$ is an independent copy. It is a symmetric Markov contraction
  semigroup and $DP_tF=e^{-t}P_tDF$.

* **12. Meyer inequalities.** For $1<p<\infty$, the norms
  $\|DF\|_{L^p(H)}$ and $\|(-L)^{1/2}F\|_p$ are equivalent, with constants
  depending only on $p$. Higher-order versions identify Gaussian Sobolev norms
  with the corresponding powers of $I-L$.

* **13. Gaussian Poincaré and hypercontractivity.**
  $\mathop{\mathrm{Var}}F\leq\mathbb E\|DF\|_H^2$, and
  $\|P_tF\|_q\leq\|F\|_p$ when $1<p\leq q$ and
  $q-1\leq e^{2t}(p-1)$. In particular, a fixed Wiener chaos has equivalent
  $L^p$ norms for all finite $p>1$.

* **14. Clark–Ocone representation.** In the augmented Brownian filtration,
  for $F\in\mathbb D^{1,2}$,
  $$F=\mathbb EF+\int_0^T\mathbb E[D_tF\mid\mathcal F_t]\,dB_t.$$

* **15. Absolute continuity criterion.** If each $F_i\in\mathbb D^{1,2}$
  and $\det\gamma_F>0$ almost surely, the law of $F$ is absolutely continuous
  with respect to Lebesgue measure (Bouleau–Hirsch criterion). In one
  dimension this says that $\|DF\|_H>0$ almost surely suffices.

* **16. Smooth-density criterion and integration by parts.** If
  $F_i\in\mathbb D^\infty=\bigcap_{k,p>1}\mathbb D^{k,p}$ and
  $\mathbb E(\det\gamma_F)^{-p}<\infty$ for every $p>1$, then $F$ has a
  smooth density. For sufficiently regular $G$,
  $$\mathbb E[\partial_i\phi(F)G]
    =\mathbb E\!\left[\phi(F)\delta\left(
      G\sum_j(\gamma_F^{-1})_{ij}DF_j\right)\right],$$
  and iteration yields higher density derivatives.

* **17. Differentiating an SDE.** For an SDE with smooth bounded coefficients
  and bounded derivatives, $X_t\in\mathbb D^\infty$. Its derivative satisfies
  $D_sX_t=0$ for $s>t$ and, for $s\leq t$,
  $$D_sX_t=\sigma(X_s)+\int_s^tDb(X_r)D_sX_r\,dr+
    \sum_j\int_s^tD\sigma_j(X_r)D_sX_r\,dB_r^j.$$

* **18. Hörmander's density theorem.** Let
  $dX=V_0(X)dt+\sum_{j=1}^dV_j(X)\circ dB^j$, $X_0=x_0\in\mathbb R^m$,
  with smooth vector fields having bounded derivatives of all orders. Assume
  that $V_1,\ldots,V_d$ together with the iterated brackets
  $[V_i,V_j]$, $[V_i,[V_j,V_k]],\ldots$ ($0\leq i,j,k\leq d$) span
  $\mathbb R^m$ at $x_0$. Then $X_t$ has a smooth density for every $t>0$.
  The drift $V_0$ alone is not a spanning direction; it enters only through brackets.

* **19. Fourth moment theorem.** For fixed $q\geq2$ and
  $F_n=I_q(f_n)$ with $\mathbb EF_n^2\to1$, convergence
  $F_n\Rightarrow N(0,1)$ is equivalent to $\mathbb EF_n^4\to3$.
  It is also equivalent to the vanishing of all nontrivial contraction norms
  $\|f_n\otimes_r f_n\|$, $1\leq r<q$.

* **20. Malliavin–Stein bound.** If $F\in\mathbb D^{1,2}$ is centered with
  variance one, then
  $$d_{\mathrm{TV}}(F,N(0,1))
    \leq2\mathbb E|1-\langle DF,-DL^{-1}F\rangle_H|.$$
  Here total variation is the supremum of probability differences over Borel sets.

### Gaussian measures on Banach spaces

A Borel probability $\gamma$ on a separable Banach space $E$ is **centered
Gaussian** if every $\ell\in E^*$ has a centered, possibly degenerate, normal
law under $\gamma$. Its **Cameron–Martin space** is
$H_\gamma=\{h\in E:|h|_{H_\gamma}<\infty\}$, where
$|h|_{H_\gamma}=\sup\{\ell(h):\ell\in E^*,\ \int\ell^2d\gamma\leq1\}$. For
$h\in H_\gamma$, $\hat h$ is the element of the closure $E^*_\gamma$ of $E^*$
in $L^2(\gamma)$ with $\int\hat h\,\ell\,d\gamma=\ell(h)$ for all $\ell\in E^*$.
A Gaussian measure on a Hilbert space $K$ with mean $m$ and trace-class
covariance $Q$ is written $N(m,Q)$.

* **61. Fernique's theorem.** For a centered Gaussian measure $\gamma$ on a
  separable Banach space there is $\alpha>0$ with
  $\int\exp(\alpha\|x\|^2)\,\gamma(dx)<\infty$; in particular the norm has
  moments of every order. Sharply, with
  $\sigma^2=\sup_{\|\ell\|\leq1}\int\ell^2d\gamma$, the integral is finite for
  every $\alpha<1/(2\sigma^2)$ and infinite for every $\alpha>1/(2\sigma^2)$.
  The same integrability holds for every $\gamma$-almost surely finite
  measurable seminorm.

* **62. Structure of the Cameron–Martin space.** $H_\gamma$ is a separable
  Hilbert space, compactly embedded in $E$, and $h\mapsto\hat h$ is a unitary
  map of $H_\gamma$ onto $E^*_\gamma$. The support of $\gamma$ is the closure
  of $H_\gamma$ in $E$. If $H_\gamma$ is infinite-dimensional, then
  $\gamma(H_\gamma)=0$. Every $\gamma$-measurable linear subspace has measure
  $0$ or $1$ (zero–one law).

* **63. Cameron–Martin theorem for Gaussian measures.** For $h\in E$, the
  translate $\gamma_h=\gamma(\cdot-h)$ is equivalent to $\gamma$ exactly when
  $h\in H_\gamma$, and then
  $d\gamma_h/d\gamma=\exp(\hat h-\frac12|h|_{H_\gamma}^2)$; otherwise
  $\gamma_h\perp\gamma$. On classical Wiener space, $H_\gamma$ consists of the
  Cameron–Martin paths and $\hat h=W(\dot h)$; that case is SYNOPSIS08,
  item 30.

* **64. Abstract Wiener spaces (Gross).** Let $H$ be a separable Hilbert
  space and $\|\cdot\|$ a measurable norm on $H$: for every $\varepsilon>0$
  there is a finite-rank orthogonal projection $P_0$ such that the standard
  Gaussian cylinder measure gives $\{\|Px\|>\varepsilon\}$ probability less than
  $\varepsilon$ for every finite-rank orthogonal projection $P\perp P_0$. Then
  the standard cylinder measure extends to a centered Gaussian measure on
  the completion $B$ of $H$ in this norm, with Cameron–Martin space $H$.
  Conversely, every centered Gaussian measure $\gamma$ on a separable Banach
  space arises in this way from $H_\gamma$ and the closure of $H_\gamma$. When
  $H$ is infinite-dimensional its own norm is not measurable.

* **65. Feldman–Hájek theorem.** Two Gaussian measures on a separable Banach
  space are either equivalent or mutually singular. On a separable Hilbert
  space $K$, $N(m_1,Q_1)$ and $N(m_2,Q_2)$ are equivalent exactly when
  $Q_1^{1/2}(K)=Q_2^{1/2}(K)=K_0$, $m_1-m_2\in K_0$, and
  $(Q_1^{-1/2}Q_2^{1/2})(Q_1^{-1/2}Q_2^{1/2})^*-I$ is Hilbert–Schmidt on
  $\overline{K_0}$. In particular, if $\dim K_0=\infty$, then $N(0,c^2Q)$ and
  $N(0,Q)$ are mutually singular for $c^2\neq1$.

### Analysis on Poisson space

Let $\eta$ be a Poisson random measure on a measurable space $X$ with
$\sigma$-finite intensity $\lambda$ (SYNOPSIS06, item 53), and let $F=f(\eta)$
be a measurable functional. The **difference operator** is
$D_xF=f(\eta+\delta_x)-f(\eta)$, with iterates $D^n_{x_1,\ldots,x_n}F$. It
obeys $D_x(FG)=FD_xG+GD_xF+D_xFD_xG$. Multiple integrals $I_n$ are taken
with respect to the compensated measure $\eta-\lambda$.

* **66. Poisson chaos and Poincaré inequality.** Every $F\in L^2(P_\eta)$ has
  an orthogonal expansion $F=\sum_{n\geq0}I_n(f_n)$, convergent in $L^2$,
  with symmetric $f_n\in L^2(\lambda^n)$ given by
  $f_n(x_1,\ldots,x_n)=\frac1{n!}\mathbb E\,D^n_{x_1,\ldots,x_n}F$ and
  $\mathbb EF^2=\sum_nn!\|f_n\|^2$ (Fock-space representation). Moreover
  $\mathop{\mathrm{Var}}F\leq\mathbb E\int(D_xF)^2\lambda(dx)$.

* **67. Mecke equation and Poisson integration by parts.** A point process
  $\eta$ is Poisson with intensity $\lambda$ exactly when
  $\mathbb E\int h(x,\eta)\,\eta(dx)=\mathbb E\int h(x,\eta+\delta_x)\,\lambda(dx)$
  for all measurable $h\geq0$ (Mecke). Consequently, for $u\in L^2(\lambda)$
  and $F\in L^2$ with $DF\in L^2(P\otimes\lambda)$,
  $\mathop{\mathrm{Cov}}(I_1(u),F)=\mathbb E\int u(x)D_xF\,\lambda(dx)$; more
  generally
  $\mathop{\mathrm{Cov}}(F,G)=\mathbb E\int\!\int_0^1D_xF\,P_tD_xG\,dt\,\lambda(dx)$,
  where $P_t$ is the Poisson Ornstein–Uhlenbeck (thinning-and-superposition)
  semigroup. These identities underlie Malliavin–Stein bounds on Poisson space.

<a id="synopsis-09b"></a>

## 09B. Rough Paths and Singular-Equation Methods

Rough integration, rough differential equations, and singular-equation methods
follow 09B. Reconstruction, renormalization, and representative singular SPDE
are kept with the methods used to define and solve them; general Hilbert-space
and random-field SPDE follow in 09C.

### Young integration and the algebra of rough paths

For a continuous path $X$, write $X_{s,t}=X_t-X_s$.
For $1/3<\alpha\leq1/2$, an **$\alpha$-Hölder rough path** is a pair
$\mathbf X=(X,\mathbb X)$ with
$|X_{s,t}|\lesssim|t-s|^\alpha$, $|\mathbb X_{s,t}|\lesssim|t-s|^{2\alpha}$,
and **Chen's relation**
$\mathbb X_{s,t}=\mathbb X_{s,u}+\mathbb X_{u,t}+X_{s,u}\otimes X_{u,t}$.
It is **weakly geometric** when
$\mathop{\mathrm{Sym}}\mathbb X_{s,t}=\frac12X_{s,t}^{\otimes2}$.
Geometric rough paths are limits of iterated-integral lifts of smooth paths
in the corresponding rough-path topology.

* **21. Young's integration theorem.** If $X$ is $\alpha$-Hölder and $Y$ is
  $\beta$-Hölder with $\alpha+\beta>1$, Riemann sums define $\int Y\,dX$ and
  $$\left|\int_s^tY\,dX-Y_sX_{s,t}\right|
    \leq C\|Y\|_\beta\|X\|_\alpha|t-s|^{\alpha+\beta}.$$
  The analogous criterion is $1/p+1/q>1$ for finite variation exponents.

* **22. Sewing lemma.** If a continuous two-parameter increment $A_{s,t}$,
  zero on the diagonal, has defect
  $|A_{s,t}-A_{s,u}-A_{u,t}|\leq C|t-s|^\gamma$, $\gamma>1$, then there is
  a unique additive increment $I_{s,t}$ with
  $|I_{s,t}-A_{s,t}|\leq C_\gamma C|t-s|^\gamma$. Partition sums of $A$
  converge to $I$.

* **23. Smooth lifts and Chen's identity.** For a smooth or bounded-variation
  path, $\mathbb X_{s,t}=\int_s^tX_{s,r}\otimes dX_r$ satisfies Chen's relation
  and the symmetric identity. Higher iterated integrals multiply by tensor
  concatenation when adjacent intervals are joined.

* **24. Lyons extension theorem.** A multiplicative functional of finite
  $p$-variation, specified through tensor degree $\lfloor p\rfloor$, has a
  unique multiplicative extension to all tensor degrees with finite
  $p$-variation, and the degree-$n$ terms obey bounds of order
  $\omega(s,t)^{n/p}/(n/p)!$ for a control $\omega$. For a geometric rough
  path the extension is its **signature**; for bounded-variation paths the
  signature determines the path up to tree-like equivalence (Hambly–Lyons).

### Controlled integration and rough differential equations

A path $Y$ is **controlled by $X$** if
$Y_{s,t}=Y'_sX_{s,t}+R^Y_{s,t}$, with $Y'$ $\alpha$-Hölder and $R^Y$
$2\alpha$-Hölder. An **RDE** $dY=V(Y)\,d\mathbf X$ is an equation in this
controlled-path space, rather than an equation based only on the first-level path.

* **25. Controlled rough integration.** For a controlled pair $(Y,Y')$, sewing
  $Y_sX_{s,t}+Y'_s\mathbb X_{s,t}$ defines the integral, with error of order
  $|t-s|^{3\alpha}$. The integral is again controlled, with derivative $Y$.

* **26. Stability of integration.** The rough integral is locally Lipschitz
  jointly in the rough path and the controlled integrand, using their Hölder
  norms and initial values. Thus convergence of enhanced drivers, not merely
  uniform convergence of paths, controls convergence of integrals.

* **27. Composition of controlled paths.** If $Y$ is controlled and $f\in C_b^2$,
  then $f(Y)$ is controlled with derivative $Df(Y)Y'$. On bounded sets, the
  corresponding composition map is locally Lipschitz under one additional
  bounded derivative.

* **28. RDE existence and uniqueness.** For $V\in C_b^3$ and
  $1/3<\alpha\leq1/2$, every initial value and $\alpha$-Hölder rough path
  determine a unique global RDE solution on a finite interval. For general
  finite $p$-variation, $\mathop{\mathrm{Lip}}^\gamma$ vector fields with
  $\gamma>p$ give the corresponding theorem.

* **29. Universal limit theorem.** The RDE solution map is locally Lipschitz
  in initial data and enhanced driver under the preceding regularity conditions.
  Solutions of smooth controlled ODEs therefore converge whenever their lifted
  drivers converge in rough-path topology.

* **30. Geometric chain rule.** For a geometric driver and smooth $f$,
  $df(Y)=Df(Y)V(Y)\,d\mathbf X$, with the ordinary chain rule. The symmetric
  second-level identity is exactly what makes this rule hold.

* **31. Brownian lifts and Itô correction.** By the Kolmogorov criterion for
  rough paths, the iterated Itô integrals
  $\mathbb B^{\mathrm{Ito}}_{s,t}=\int_s^tB_{s,r}\otimes dB_r$ define almost
  surely an $\alpha$-Hölder rough path for every $\alpha<1/2$, and
  $\mathbb B^{\mathrm{Strat}}_{s,t}=\mathbb B^{\mathrm{Ito}}_{s,t}
  +\frac12(t-s)I$ is the geometric Stratonovich lift. Rough integrals and RDE
  solutions driven by these lifts coincide almost surely with the
  corresponding Itô and Stratonovich integrals and SDE solutions.

* **32. Wong–Zakai theorem.** Piecewise linear Brownian approximations converge,
  along deterministic partitions with mesh tending to zero, in probability
  after lifting to the Stratonovich Brownian rough path in any Hölder topology
  with exponent in $(1/3,1/2)$. For $C_b^3$ vector fields the corresponding ODE
  solutions converge to the Stratonovich SDE solution.

* **33. Support theorem.** For smooth bounded vector fields with bounded
  derivatives, the support of a diffusion law in continuous-path topology is
  the closure of solutions of its Stratonovich controlled ODE with
  Cameron–Martin controls and the same initial value.

* **34. Enhanced Schilder theorem.** Brownian rough paths scaled at levels one
  and two by $\sqrt\varepsilon$ and $\varepsilon$ satisfy a large deviation
  principle in $\alpha$-Hölder rough-path topology, $1/3<\alpha<1/2$, with
  rate $\frac12\int_0^T|\dot h|^2dt$ on Cameron–Martin lifts and infinity
  elsewhere. The RDE large deviation principle follows by contraction.

* **35. Gaussian rough paths.** Fractional Brownian motion with independent
  components and Hurst parameter $H>1/4$ has a canonical geometric lift obtained
  from smooth approximations. It has finite $p$-variation for every $p>1/H$;
  when $H\leq1/3$, levels beyond the second are required.

### Distributional products and the entrance to singular SPDE

Write $\mathcal C^\alpha=B_{\infty,\infty}^\alpha$ for Hölder–Besov spaces,
using parabolic scaling when time is present. A **regularity structure** consists
of a graded space of local expansion symbols and a group transporting such
expansions between base points. A **model** $(\Pi_x,\Gamma_{xy})$ realizes the
symbols as distributions and satisfies compatibility
$\Pi_x\Gamma_{xy}=\Pi_y$ with the prescribed scaling bounds. A
**modelled distribution** of regularity $\gamma$ has local coefficients whose
transported differences in homogeneity $\beta$ are $O(|x-y|^{\gamma-\beta})$.

* **54. Product criterion.** If $\alpha<0<\beta$ and $\alpha+\beta>0$,
  multiplication extends continuously
  $\mathcal C^\alpha\times\mathcal C^\beta\to\mathcal C^\alpha$.
  Bony's decomposition separates low–high, high–low, and resonant interactions;
  the resonant term has regularity $\alpha+\beta$. Without positive total
  regularity, general distributions do not have a canonical product.

* **55. Parabolic Schauder gain.** Convolution with a localized heat kernel
  raises parabolic Hölder–Besov regularity by two, away from integer endpoint
  formulations, with the corresponding local estimates. This balances the
  loss of regularity in the nonlinear terms of a mild equation.

* **56. Regularity of white noise.** In $d$ spatial dimensions, space-time
  white noise belongs locally almost surely to parabolic $\mathcal C^\alpha$
  for every $\alpha<-(d+2)/2$. Its heat convolution consequently has
  regularity below $(2-d)/2$, explaining why nonlinear products require
  additional structure in the singular cases.

* **57. Reconstruction theorem.** For a model and a modelled distribution
  $f$ of regularity $\gamma>0$, there is a unique distribution $\mathcal Rf$
  satisfying
  $$|\langle\mathcal Rf-\Pi_xf(x),\phi_x^\lambda\rangle|
    \lesssim\lambda^\gamma$$
  locally, uniformly over normalized smooth test functions at scale $\lambda$.
  Test regularity exceeds the negative of the lowest homogeneity.
  Reconstruction is locally continuous jointly in the model and coefficients.

* **58. Renormalized two-dimensional cubic equation.** On the two-dimensional
  torus, smooth initial data and mollified space-time white noise yield solutions
  of
  $$\partial_tu_\varepsilon=(\Delta-1)u_\varepsilon
     -u_\varepsilon^3+3C_\varepsilon u_\varepsilon+\xi_\varepsilon,$$
  where $C_\varepsilon$ is the variance of the stationary mollified linear
  convolution. With this Wick normalization the solutions converge in
  probability on finite horizons in $C([0,T];\mathcal C^{-\kappa})$,
  $\kappa>0$, to a mollifier-independent solution. The divergent linear
  counterterm is part of the equation's definition.

* **59. Cole–Hopf solution of KPZ.** On the one-dimensional torus with smooth
  strictly positive initial data, the positive solution of
  $dZ=\Delta Z\,dt+Z\,dW$ defines $h=\log Z$.
  For spatially mollified noise, Itô's formula gives
  $$dh_\varepsilon=
    (\Delta h_\varepsilon+|\partial_xh_\varepsilon|^2
       -\tfrac12\|\rho_\varepsilon\|_2^2)dt+dW_\varepsilon.$$
  The logarithms converge to the Cole–Hopf KPZ solution. The subtraction and
  its coefficient are fixed by the stated heat and noise normalizations.
  Regularity structures construct a solution theory for KPZ directly, and
  their renormalized solutions coincide with the Cole–Hopf solution.

* **60. Subcritical well-posedness.** For locally subcritical semilinear
  parabolic equations driven by space-time noise, solutions of the mollified
  equations with finitely many suitably chosen counterterms converge in
  probability, up to a random explosion time, to a limit independent of the
  mollifier; the renormalized models converge, and the abstract fixed point
  is solved in modelled distributions. For $\Phi^4_3$ on the
  three-dimensional torus the counterterm is $C_\varepsilon u_\varepsilon$
  with $C_\varepsilon$ diverging like $\varepsilon^{-1}$ plus a logarithmic
  correction; subcriticality of $\Phi^4_d$ requires $d<4$.

<a id="synopsis-09c"></a>

## 09C. Stochastic Partial Differential Equations

Hilbert-space stochastic integration, mild and variational evolution,
invariant measures, and random-field equations follow 09C. Singular equations
and their reconstruction and renormalization methods are in 09B; the
white-noise convention is shared across the subdivisions.

### Hilbert-space stochastic integration and evolution equations

Let $U,H$ be Hilbert spaces. A **cylindrical Wiener process** on $U$ is the
formal series $W_t=\sum_k\beta_k(t)e_k$; its coordinates exist even when the
series does not converge in $U$. The Hilbert–Schmidt operators from $U$ to $H$
form $L_2(U,H)$. For an evolution semigroup $S(t)$ with generator $A$, a
**mild solution** of $dX=(AX+F(X))dt+B(X)dW$ satisfies the variation-of-constants
formula in result 40.

* **36. Trace-class Wiener processes.** A positive self-adjoint covariance
  operator $Q$ on $U$, with eigenpairs $(q_k,e_k)$, defines a $U$-valued
  Wiener process exactly when $\mathop{\mathrm{tr}}Q<\infty$. Then
  $W_t^Q=\sum_k\sqrt{q_k}\beta_k(t)e_k$ in $L^2(\Omega;U)$, and
  $\mathbb E\|W_t^Q\|^2=t\mathop{\mathrm{tr}}Q$. A cylindrical Wiener process
  takes values in any larger Hilbert space $U_1\supset U$ with Hilbert–Schmidt
  embedding.

* **37. Hilbert-space Itô isometry.** Predictable $G$ with
  $\mathbb E\int_0^T\|G_s\|_{L_2(U,H)}^2ds<\infty$ has an $H$-valued
  martingale integral and
  $$\mathbb E\left\|\int_0^TG_s\,dW_s\right\|^2
    =\mathbb E\int_0^T\|G_s\|_{L_2(U,H)}^2ds.$$

* **38. Hilbert-space Itô formula.** For
  $dX=b\,dt+G\,dW$ with integrable $H$-valued drift and square-integrable
  Hilbert–Schmidt diffusion, $\phi\in C_b^2(H)$ satisfies
  $$d\phi(X)=D\phi(X)b\,dt+D\phi(X)G\,dW+
    \tfrac12\mathop{\mathrm{tr}}(G^*D^2\phi(X)G)dt.$$
  Localization allows the usual locally bounded variants.

* **39. Stochastic convolution criterion.** For deterministic $B$,
  $Z_t=\int_0^tS(t-s)B\,dW_s$ exists in $L^2(\Omega;H)$ exactly when
  $\int_0^t\|S(s)B\|_{L_2(U,H)}^2ds<\infty$. It is centered Gaussian with
  covariance $Q_t=\int_0^tS(s)BB^*S(s)^*ds$.

* **40. Lipschitz mild equations.** If $S$ is a strongly continuous contraction semigroup
  and $F:H\to H$, $B:H\to L_2(U,H)$ are globally Lipschitz, square-integrable
  initial data give a unique adapted continuous mild solution
  $$X_t=S(t)X_0+\int_0^tS(t-s)F(X_s)ds+
                     \int_0^tS(t-s)B(X_s)dW_s.$$
  It has finite $\mathbb E\sup_{t\leq T}\|X_t\|^2$ and continuous dependence
  on its initial data. For a general $C_0$-semigroup the same holds with
  initial data in $L^p$, $p>2$, using the factorization method for path
  continuity of stochastic convolutions.

* **41. Mild and weak formulations.** Under the preceding integrability,
  mild solutions are equivalent to solutions of
  $$\langle X_t,h\rangle=\langle X_0,h\rangle+
    \int_0^t(\langle X_s,A^*h\rangle+\langle F(X_s),h\rangle)ds+
    \int_0^t\langle B(X_s)^*h,dW_s\rangle,$$
  for $h\in D(A^*)$. Here “weak” refers to the spatial test formulation,
  not to a change of probability space.

* **68. Equations with Lévy noise.** Let $\pi$ be a Poisson random measure
  on $\mathbb R_+\times Z$ with intensity $dt\otimes\nu$ and compensated
  measure $\hat\pi$. For predictable $G$ with
  $\mathbb E\int_0^T\!\int_Z\|G(s,z)\|_H^2\nu(dz)ds<\infty$, the integral
  $\int_0^t\!\int_ZG\,d\hat\pi$ is a square-integrable $H$-valued martingale
  with second moment $\mathbb E\int_0^t\!\int_Z\|G\|_H^2\nu(dz)ds$. If $F$ is
  Lipschitz and $\int_Z\|G(x,z)-G(y,z)\|^2\nu(dz)\leq C\|x-y\|^2$ with linear
  growth, square-integrable initial data give a unique mild solution of
  $X_t=S(t)X_0+\int_0^tS(t-s)F(X_s)ds+\int_0^t\!\int_ZS(t-s)G(X_{s-},z)\,\hat\pi(ds,dz)$;
  for a contraction semigroup it has a càdlàg version (Peszat–Zabczyk).

### Variational solutions and invariant measures

A **Gelfand triple** $V\hookrightarrow H\cong H^*\hookrightarrow V^*$ has
$V$ separable and reflexive, densely and continuously embedded in $H$. For
$dX=A(X)dt+B(X)dW$, a variational solution lies in
$L^\alpha(\Omega\times[0,T];V)$ and satisfies the equation in $V^*$ with an
$H$-continuous version.
Hemicontinuity of $A$ means continuity of
$r\mapsto\langle A(u+rv),w\rangle$ for fixed $u,v,w\in V$.

* **42. Variational Itô identity.** With drift in $L^{\alpha'}(V^*)$ and
  diffusion in $L^2(L_2(U,H))$, the variational equation satisfies
  $$\|X_t\|_H^2=\|X_0\|_H^2+
    \int_0^t\bigl(2\langle A(X_s),X_s\rangle+\|B(X_s)\|_{L_2}^2\bigr)ds
    +2\int_0^t\langle X_s,B(X_s)dW_s\rangle_H.$$

* **43. Monotone variational existence theorem.** Suppose $A:V\to V^*$ is
  hemicontinuous, $B:V\to L_2(U,H)$ is measurable, and for some $\alpha>1$,
  $$2\langle A(u)-A(v),u-v\rangle+\|B(u)-B(v)\|_{L_2}^2
      \leq C\|u-v\|_H^2,$$
  $$2\langle A(v),v\rangle+\|B(v)\|_{L_2}^2
      \leq C(1+\|v\|_H^2)-c\|v\|_V^\alpha,$$
  and $\|A(v)\|_{V^*}^{\alpha'}\leq C(1+\|v\|_V^\alpha)$.
  Here $c>0$ and $\alpha'=\alpha/(\alpha-1)$. These assumptions yield a unique
  variational solution for square-integrable initial data, with the associated
  energy bounds.

* **44. Stability and the Markov property.** The monotonicity estimate gives
  $\mathbb E\|X_t^x-X_t^y\|_H^2\leq e^{Ct}\|x-y\|_H^2$. For deterministic
  time-homogeneous coefficients this yields a Feller Markov transition
  semigroup on bounded continuous functions.

* **45. Invariant Gaussian laws.** For the linear equation with exponentially
  stable $S$, if
  $Q_\infty=\int_0^\infty S(s)BB^*S(s)^*ds$ is trace class, then
  $N(0,Q_\infty)$ is the unique invariant probability, and transition laws
  converge weakly to it. Its covariance solves the Lyapunov equation
  $AQ_\infty+Q_\infty A^*+BB^*=0$ in weak form.

* **46. Krylov–Bogoliubov existence.** For a Feller Markov semigroup on a
  Polish space, tightness of
  $T^{-1}\int_0^T\mathcal L(X_t^x)dt$ as $T\to\infty$ gives an invariant
  probability as a weak subsequential limit. Compact embeddings and coercive
  energy bounds provide a standard route to this tightness.

* **47. Doob–Khasminskii uniqueness.** If a Markov transition semigroup on a
  Polish space is strong Feller (it maps bounded measurable functions to
  continuous ones) and irreducible (every transition probability charges every
  open set) at some time $t_0>0$, then it has at most one invariant
  probability, and that measure is equivalent to every transition probability
  $P_t(x,\cdot)$ with $t\ge2t_0$. For nondegenerate additive noise both properties follow from
  Bismut–Elworthy–Li formulas and control arguments.

### Random-field SPDE and spatial regularity

The **Walsh integral** integrates predictable functions against the associated
orthogonal martingale measure. For the heat operator $\Delta$, write
$p_t(x)=(4\pi t)^{-d/2}e^{-|x|^2/(4t)}$.

* **48. Walsh isometry.** For square-integrable predictable $g$,
  $$\mathbb E\left|\int_0^T\int g(s,x)W(ds,dx)\right|^2
    =\mathbb E\int_0^T\int|g(s,x)|^2dx\,ds.$$
  This constructs stochastic convolutions pointwise in the spatial variable.

* **49. White-noise heat equation.** The stochastic heat convolution at a
  point has variance $\int_0^t\|p_s\|_2^2ds$, finite exactly when $d<2$.
  Thus spatially white forcing gives a function-valued heat convolution in
  dimension one, but distribution-valued solutions in higher dimensions.

* **50. Semilinear random-field existence.** In one space dimension, bounded
  measurable initial data and globally Lipschitz drift and noise coefficients
  give a unique predictable mild random-field solution of
  $\partial_tu=\Delta u+b(u)+\sigma(u)\xi$, with bounded moments uniformly
  over space and compact positive-time intervals.

* **51. Dalang's condition.** For temporally white Gaussian noise whose
  spatial covariance is a nonnegative tempered measure with spectral measure
  $\mu$, the heat stochastic convolution exists at a point exactly when
  $$\int_{\mathbb R^d}\frac{\mu(d\zeta)}{1+|\zeta|^2}<\infty.$$
  This condition also gives the standard Lipschitz semilinear random-field
  existence theory for bounded initial data.

* **52. Heat-equation Hölder exponents.** For the one-dimensional linear
  white-noise heat equation with smooth initial data, a version is locally
  Hölder of every time exponent below $1/4$ and every space exponent below
  $1/2$. The same upper regularity conclusions hold for globally Lipschitz
  semilinear equations with suitable bounded initial data away from time zero.

* **53. Comparison.** For one-dimensional stochastic heat equations driven
  by the same white noise and the same Lipschitz $\sigma$, ordered initial
  data and ordered Lipschitz drifts yield ordered continuous solutions almost
  surely. If moreover $\sigma(0)=0$ and the drift $b$ satisfies $b(0)=0$,
  nonnegative initial data that are not identically zero give solutions that
  are strictly positive at all positive times (Mueller's positivity theorem).

## Reference guide

### Correspondence with the subdivisions

- **[09A](#synopsis-09a)**: The Malliavin and Gaussian-analysis references
  supply chaos, differentiation, densities, and normal approximation.
- **[09B](#synopsis-09b)**: The rough-path and regularity-structure references
  supply controlled integration, reconstruction, and the singular-equation
  examples.
- **[09C](#synopsis-09c)**: The Hilbert-space, variational, semigroup, and
  random-field SPDE references supply the general evolution and regularity
  results.

### Source comparisons and local copies

Nualart, *The Malliavin Calculus and Related Topics*, Chapters 1–2, and
Nualart–Nualart, *Introduction to Malliavin Calculus*, Chapters 3–8, provide
overlapping treatments of chaos, differential operators, densities, and normal
approximation. Da Prato, Bogachev, Malliavin, Hu, and Nourdin–Peccati give
complementary Gaussian, geometric, and approximation viewpoints.
Kuo, *Gaussian Measures in Banach Spaces*, and Bogachev, *Gaussian Measures*
(listed in Section 4), supply abstract Wiener spaces, Fernique's theorem, the
Cameron–Martin space, and the Feldman–Hájek dichotomy; Da Prato–Zabczyk give
the Hilbert-space form of the last. The Poisson-space results follow
Last–Penrose, *Lectures on the Poisson Process* (listed in Section 6), with
Osswald, Bally–Caramellino–Cont, and Bouleau–Denis developing jump-process
Malliavin calculus further.

Friz–Hairer, *A Course on Rough Paths*, Chapters 2–5 and 8–11, supplies
controlled integration, RDEs, Brownian and Gaussian lifts; Lyons–Caruana–Lévy
and Friz–Victoir develop the extension and universal-limit theory in greater
generality. Friz–Hairer, Chapters 13–16, treats reconstruction and singular
equations, with KPZ as the worked example. The two-dimensional cubic example and Cole–Hopf equation are useful
common models across singular-SPDE and random-interface treatments; they do
not represent the full scope of regularity structures or paracontrolled calculus.

Prévôt–Röckner, Chapters 2 and 4, and Liu–Röckner develop Hilbert-space
integration and variational solutions. Lototsky–Rozovsky provides a broad
independent SPDE course. Peszat–Zabczyk treats equations driven by Lévy
noise. Da Prato–Zabczyk is the principal semigroup
reference, and their *Ergodicity for Infinite Dimensional Systems* treats
strong Feller, irreducibility, and uniqueness of invariant measures, while Walsh and the Dalang–Khoshnevisan–Mueller–Nualart–Xiao minicourse
develop the random-field viewpoint and its dimension-dependent existence criteria.

Local source anchors:

- [Nualart, *The Malliavin Calculus and Related Topics*](References/Nualart2006MalliavinCalculusRelatedTopics2ndEd-SpringerPIA.pdf).
- [Nualart–Nualart, *Introduction to Malliavin Calculus*](References/NualartNualart2018IntroductionMalliavinCalculus-CambridgeIMSTextbooks.pdf).
- [Friz–Hairer, *A Course on Rough Paths*](References/FrizHairer2020CourseRoughPathsIntroductionRegularityStructures2ndEd-Springer.UTX.pdf).
- [Prévôt–Röckner, *A Concise Course on SPDE*](References/PrévôtRöckner2007ConciseCourseStochasticPartialDifferentialEquations-SpringerLNM1905.pdf).
- [Liu–Röckner, *Stochastic Partial Differential Equations*](References/LiuRöckner2015StochasticPartialDifferentialEquationsIntroduction-SpringerUTX.pdf).
- [The Dalang et al. minicourse](References/DalangKhoshnevisanMuellerEtAl2009MinicourseStochasticPartialDifferentialEquations-Springer.LNM1962.pdf).
- [Kuo, *Gaussian Measures in Banach Spaces*](References/Kuo1975GaussianMeasuresBanachSpaces-Springer.LNM473.pdf).
- [Bogachev, *Gaussian Measures*](References/Bogachev1998Gaussian%20Measures-AMS.MathSurvMonog.pdf).
- [Last–Penrose, *Lectures on the Poisson Process*](References/LastPenrose2018LecturesPoissonProcess-Cambridge.IMSTextbooks7.pdf).
- [Lototsky–Rozovsky, *Stochastic Partial Differential Equations*](References/LototskyRozovsky2017StochasticPartialDifferentialEquations-SpringerUTX.pdf).
