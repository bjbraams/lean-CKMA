# Synopsis: Malliavin calculus, rough paths, and stochastic partial differential equations

Part of the [mathematical synopsis series](SYNOPSIS.md).

Section 09 of [CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md)
joins three interacting theories: differentiation of random functionals,
integration against irregular signals, and evolution equations with noise.
The selection below follows their recurring textbook core. The final part
records a small number of foundational results on singular SPDE; it does not
attempt to inventory all equations or renormalization schemes in the research
literature.

Hilbert spaces are real and separable. On a Gaussian probability space,
$W:H\to L^2(\Omega)$ is **isonormal** if it is linear, centered Gaussian, and
$\mathbb E[W(h)W(k)]=\langle h,k\rangle_H$. Random variables in the Gaussian
parts are measurable with respect to $W$. On Wiener space,
$H=L^2([0,T];\mathbb R^d)$ and $W(h)=\int h\,dB$. Its associated
Cameron–Martin paths are $t\mapsto\int_0^th(s)ds$.

## Wiener chaos and differential calculus on Gaussian space

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
  This identifies the symmetric tensor powers with the homogeneous chaoses.
* **3. Product formula.** For symmetric tensors,
  $$I_p(f)I_q(g)=\sum_{r=0}^{p\wedge q}
    r!\binom pr\binom qr I_{p+q-2r}(f\widetilde\otimes_r g),$$
  where $\otimes_r$ contracts $r$ pairs of tensor variables and the tilde
  symmetrizes the remaining ones.
* **4. Closability and Sobolev spaces.** The cylindrical derivative is closable
  from $L^p(\Omega)$ to $L^p(\Omega;H)$ for $1<p<\infty$. Its iterates define
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

## Ornstein–Uhlenbeck analysis, densities, and normal approximation

The **Ornstein–Uhlenbeck generator** is $LI_q(f)=-qI_q(f)$; on its domain
$L=-\delta D$. The pseudo-inverse is
$L^{-1}F=-\sum_{q\geq1}q^{-1}I_q(f_q)$, annihilating constants.
For $F=(F_1,\ldots,F_m)$, its **Malliavin covariance matrix** is
$\gamma_F=(\langle DF_i,DF_j\rangle_H)_{i,j}$.

* **10. Mehler formula.** The chaos semigroup $P_tI_q=e^{-qt}I_q$ is
  $$P_tF(W)=\mathbb E'[F(e^{-t}W+\sqrt{1-e^{-2t}}W')],$$
  where $W'$ is an independent copy. It is a symmetric Markov contraction
  semigroup and $DP_tF=e^{-t}P_tDF$.
* **11. Meyer inequalities.** For $1<p<\infty$, the norms
  $\|DF\|_{L^p(H)}$ and $\|(-L)^{1/2}F\|_p$ are equivalent, with constants
  depending only on $p$. Higher-order versions identify Gaussian Sobolev norms
  with the corresponding powers of $I-L$.
* **12. Gaussian Poincaré and hypercontractivity.**
  $\operatorname{Var}F\leq\mathbb E\|DF\|_H^2$, and
  $\|P_tF\|_q\leq\|F\|_p$ when $1<p\leq q$ and
  $q-1\leq e^{2t}(p-1)$. In particular, a fixed Wiener chaos has equivalent
  $L^p$ norms for all finite $p>1$.
* **13. Clark–Ocone representation.** In the augmented Brownian filtration,
  for $F\in\mathbb D^{1,2}$,
  $$F=\mathbb EF+\int_0^T\mathbb E[D_tF\mid\mathcal F_t]\,dB_t.$$
  Thus differentiating the terminal functional identifies its martingale
  representation integrand.
* **14. Absolute continuity criterion.** If each $F_i\in\mathbb D^{1,2}$
  and $\det\gamma_F>0$ almost surely, the law of $F$ is absolutely continuous
  with respect to Lebesgue measure. In one dimension, $\|DF\|_H>0$ almost
  surely suffices (Bouleau–Hirsch criterion).
* **15. Smooth-density criterion and integration by parts.** If
  $F_i\in\mathbb D^\infty=\bigcap_{k,p>1}\mathbb D^{k,p}$ and
  $\mathbb E(\det\gamma_F)^{-p}<\infty$ for every $p>1$, then $F$ has a
  smooth density. For sufficiently regular $G$,
  $$\mathbb E[\partial_i\phi(F)G]
    =\mathbb E\!\left[\phi(F)\delta\left(
      G\sum_j(\gamma_F^{-1})_{ij}DF_j\right)\right],$$
  and iteration yields higher density derivatives.
* **16. Differentiating an SDE.** For an SDE with smooth bounded coefficients
  and bounded derivatives, $X_t\in\mathbb D^\infty$. Its derivative satisfies
  $D_sX_t=0$ for $s>t$ and, for $s\leq t$,
  $$D_sX_t=\sigma(X_s)+\int_s^tDb(X_r)D_sX_r\,dr+
    \sum_j\int_s^tD\sigma_j(X_r)D_sX_r\,dB_r^j.$$
* **17. Hörmander's density theorem.** For a Stratonovich SDE with
  $C_b^\infty$ vector fields, assume the diffusion fields and their iterated
  brackets with the diffusion and drift fields span the tangent space at every
  point. Then the law at each positive time, from a fixed starting point, has
  a smooth density. The drift field alone is not included as a spanning direction.
* **18. Fourth moment theorem.** For fixed $q\geq2$ and
  $F_n=I_q(f_n)$ with $\mathbb EF_n^2\to1$, convergence
  $F_n\Rightarrow N(0,1)$ is equivalent to $\mathbb EF_n^4\to3$.
  It is also equivalent to the vanishing of all nontrivial contraction norms
  $\|f_n\otimes_r f_n\|$, $1\leq r<q$.
* **19. Malliavin–Stein bound.** If $F\in\mathbb D^{1,2}$ is centered with
  variance one, then
  $$d_{\mathrm{TV}}(F,N(0,1))
    \leq2\mathbb E|1-\langle DF,-DL^{-1}F\rangle_H|.$$
  Here total variation is the supremum of probability differences over Borel sets.

## Young integration and the algebra of rough paths

For a continuous path $X$, write $X_{s,t}=X_t-X_s$.
For $1/3<\alpha\leq1/2$, an **$\alpha$-Hölder rough path** is a pair
$\mathbf X=(X,\mathbb X)$ with
$|X_{s,t}|\lesssim|t-s|^\alpha$, $|\mathbb X_{s,t}|\lesssim|t-s|^{2\alpha}$,
and **Chen's relation**
$\mathbb X_{s,t}=\mathbb X_{s,u}+\mathbb X_{u,t}+X_{s,u}\otimes X_{u,t}$.
It is **weakly geometric** when
$\operatorname{Sym}\mathbb X_{s,t}=\frac12X_{s,t}^{\otimes2}$.
Geometric rough paths are limits of iterated-integral lifts of smooth paths
in the corresponding rough-path topology.

* **20. Young's integration theorem.** If $X$ is $\alpha$-Hölder and $Y$ is
  $\beta$-Hölder with $\alpha+\beta>1$, Riemann sums define $\int Y\,dX$ and
  $$\left|\int_s^tY\,dX-Y_sX_{s,t}\right|
    \leq C\|Y\|_\beta\|X\|_\alpha|t-s|^{\alpha+\beta}.$$
  The analogous criterion is $1/p+1/q>1$ for finite variation exponents.
* **21. Sewing lemma.** If a continuous two-parameter increment $A_{s,t}$,
  zero on the diagonal, has defect
  $|A_{s,t}-A_{s,u}-A_{u,t}|\leq C|t-s|^\gamma$, $\gamma>1$, then there is
  a unique additive increment $I_{s,t}$ with
  $|I_{s,t}-A_{s,t}|\leq C_\gamma C|t-s|^\gamma$. Partition sums of $A$
  converge to $I$.
* **22. Smooth lifts and Chen's identity.** For a smooth or bounded-variation
  path, $\mathbb X_{s,t}=\int_s^tX_{s,r}\otimes dX_r$ satisfies Chen's relation
  and the symmetric identity. Higher iterated integrals multiply by tensor
  concatenation when adjacent intervals are joined.
* **23. Lyons extension theorem.** A multiplicative geometric rough path of
  finite $p$-variation, specified through degree $\lfloor p\rfloor$, has a
  unique extension to all tensor degrees with the corresponding factorial
  decay bounds. The extended collection is its **signature**.

## Controlled integration and rough differential equations

A path $Y$ is **controlled by $X$** if
$Y_{s,t}=Y'_sX_{s,t}+R^Y_{s,t}$, with $Y'$ $\alpha$-Hölder and $R^Y$
$2\alpha$-Hölder. An **RDE** $dY=V(Y)\,d\mathbf X$ is an equation in this
controlled-path space, rather than an equation based only on the first-level path.

* **24. Controlled rough integration.** For a controlled pair $(Y,Y')$, sewing
  $Y_sX_{s,t}+Y'_s\mathbb X_{s,t}$ defines the integral, with error of order
  $|t-s|^{3\alpha}$. The integral is again controlled, with derivative $Y$.
* **25. Stability of integration.** The rough integral is locally Lipschitz
  jointly in the rough path and the controlled integrand, using their Hölder
  norms and initial values. Thus convergence of enhanced drivers, not merely
  uniform convergence of paths, controls convergence of integrals.
* **26. Composition of controlled paths.** If $Y$ is controlled and $f\in C_b^2$,
  then $f(Y)$ is controlled with derivative $Df(Y)Y'$. On bounded sets, the
  corresponding composition map is locally Lipschitz under one additional
  bounded derivative.
* **27. RDE existence and uniqueness.** For $V\in C_b^3$ and
  $1/3<\alpha\leq1/2$, every initial value and $\alpha$-Hölder rough path
  determine a unique global RDE solution on a finite interval. For general
  finite $p$-variation, $\operatorname{Lip}^\gamma$ vector fields with
  $\gamma>p$ give the corresponding theorem.
* **28. Universal limit theorem.** The RDE solution map is locally Lipschitz
  in initial data and enhanced driver under the preceding regularity conditions.
  Solutions of smooth controlled ODEs therefore converge whenever their lifted
  drivers converge in rough-path topology.
* **29. Geometric chain rule.** For a geometric driver and smooth $f$,
  $df(Y)=Df(Y)V(Y)\,d\mathbf X$, with the ordinary chain rule. The symmetric
  second-level identity is exactly what makes this rule hold.
* **30. Brownian lifts and Itô correction.** Brownian motion has both Itô and
  Stratonovich lifts of every Hölder order below $1/2$, with
  $\mathbb B^{\mathrm{Strat}}_{s,t}=\mathbb B^{\mathrm{Ito}}_{s,t}
  +\frac12(t-s)I$. The Stratonovich lift is geometric; the Itô lift gives
  Itô integration and its quadratic-variation correction.
* **31. Wong–Zakai theorem.** Piecewise linear Brownian approximations converge,
  along deterministic partitions with mesh tending to zero, in probability
  after lifting to the Stratonovich Brownian rough path in any Hölder topology
  with exponent in $(1/3,1/2)$. For $C_b^3$ vector fields the corresponding ODE
  solutions converge to the Stratonovich SDE solution.
* **32. Support theorem.** For smooth bounded vector fields with bounded
  derivatives, the support of a diffusion law in continuous-path topology is
  the closure of solutions of its Stratonovich controlled ODE with
  Cameron–Martin controls and the same initial value.
* **33. Enhanced Schilder theorem.** Brownian rough paths scaled at levels one
  and two by $\sqrt\varepsilon$ and $\varepsilon$ satisfy a large deviation
  principle in $\alpha$-Hölder rough-path topology, $1/3<\alpha<1/2$, with
  rate $\frac12\int_0^T|\dot h|^2dt$ on Cameron–Martin lifts and infinity
  elsewhere. The RDE large deviation principle follows by contraction.
* **34. Gaussian rough paths.** Fractional Brownian motion with independent
  components and Hurst parameter $H>1/4$ has a canonical geometric lift obtained
  from smooth approximations. It has finite $p$-variation for every $p>1/H$;
  when $H\leq1/3$, levels beyond the second are required.

## Hilbert-space stochastic integration and evolution equations

Let $U,H$ be Hilbert spaces. A **cylindrical Wiener process** on $U$ is the
formal series $W_t=\sum_k\beta_k(t)e_k$; its coordinates exist even when the
series does not converge in $U$. The Hilbert–Schmidt operators from $U$ to $H$
form $L_2(U,H)$. For an evolution semigroup $S(t)$ with generator $A$, a
**mild solution** of $dX=(AX+F(X))dt+B(X)dW$ satisfies the variation-of-constants
formula in result 39.

* **35. Trace-class Wiener processes.** A positive covariance operator $Q$
  defines an $H$-valued Gaussian Wiener process exactly when $\operatorname{tr}Q$
  is finite. Then $W_t^Q=\sum_k\sqrt{q_k}\beta_k(t)e_k$ in
  $L^2(\Omega;H)$, and $\mathbb E\|W_t^Q\|^2=t\operatorname{tr}Q$.
* **36. Hilbert-space Itô isometry.** Predictable $G$ with
  $\mathbb E\int_0^T\|G_s\|_{L_2(U,H)}^2ds<\infty$ has an $H$-valued
  martingale integral and
  $$\mathbb E\left\|\int_0^TG_s\,dW_s\right\|^2
    =\mathbb E\int_0^T\|G_s\|_{L_2(U,H)}^2ds.$$
* **37. Hilbert-space Itô formula.** For
  $dX=b\,dt+G\,dW$ with integrable $H$-valued drift and square-integrable
  Hilbert–Schmidt diffusion, $\phi\in C_b^2(H)$ satisfies
  $$d\phi(X)=D\phi(X)b\,dt+D\phi(X)G\,dW+
    \tfrac12\operatorname{tr}(G^*D^2\phi(X)G)dt.$$
  Localization allows the usual locally bounded variants.
* **38. Stochastic convolution criterion.** For deterministic $B$,
  $Z_t=\int_0^tS(t-s)B\,dW_s$ exists in $L^2(\Omega;H)$ exactly when
  $\int_0^t\|S(s)B\|_{L_2(U,H)}^2ds<\infty$. It is centered Gaussian with
  covariance $Q_t=\int_0^tS(s)BB^*S(s)^*ds$.
* **39. Lipschitz mild equations.** If $S$ is a strongly continuous contraction semigroup
  and $F:H\to H$, $B:H\to L_2(U,H)$ are globally Lipschitz, square-integrable
  initial data give a unique adapted continuous mild solution
  $$X_t=S(t)X_0+\int_0^tS(t-s)F(X_s)ds+
                     \int_0^tS(t-s)B(X_s)dW_s.$$
  It has finite $\mathbb E\sup_{t\leq T}\|X_t\|^2$ and continuous dependence
  on its initial data.
* **40. Mild and weak formulations.** Under the preceding integrability,
  mild solutions are equivalent to solutions of
  $$\langle X_t,h\rangle=\langle X_0,h\rangle+
    \int_0^t(\langle X_s,A^*h\rangle+\langle F(X_s),h\rangle)ds+
    \int_0^t\langle B(X_s)^*h,dW_s\rangle,$$
  for $h\in D(A^*)$. Here “weak” refers to the spatial test formulation,
  not to a change of probability space.

## Variational solutions and invariant measures

A **Gelfand triple** $V\hookrightarrow H\cong H^*\hookrightarrow V^*$ has
$V$ separable and reflexive, densely and continuously embedded in $H$. For
$dX=A(X)dt+B(X)dW$, a variational solution lies in
$L^\alpha(\Omega\times[0,T];V)$ and satisfies the equation in $V^*$ with an
$H$-continuous version.
Hemicontinuity of $A$ means continuity of
$r\mapsto\langle A(u+rv),w\rangle$ for fixed $u,v,w\in V$.

* **41. Variational Itô identity.** With drift in $L^{\alpha'}(V^*)$ and
  diffusion in $L^2(L_2(U,H))$, the variational equation satisfies
  $$\|X_t\|_H^2=\|X_0\|_H^2+
    \int_0^t\bigl(2\langle A(X_s),X_s\rangle+\|B(X_s)\|_{L_2}^2\bigr)ds
    +2\int_0^t\langle X_s,B(X_s)dW_s\rangle_H.$$
* **42. Monotone variational existence theorem.** Suppose $A:V\to V^*$ is
  hemicontinuous, $B:V\to L_2(U,H)$ is measurable, and for some $\alpha>1$,
  $$2\langle A(u)-A(v),u-v\rangle+\|B(u)-B(v)\|_{L_2}^2
      \leq C\|u-v\|_H^2,$$
  $$2\langle A(v),v\rangle+\|B(v)\|_{L_2}^2
      \leq C(1+\|v\|_H^2)-c\|v\|_V^\alpha,$$
  and $\|A(v)\|_{V^*}^{\alpha'}\leq C(1+\|v\|_V^\alpha)$.
  Here $c>0$ and $\alpha'=\alpha/(\alpha-1)$. These assumptions yield a unique
  variational solution for square-integrable initial data, with the associated
  energy bounds.
* **43. Stability and the Markov property.** The monotonicity estimate gives
  $\mathbb E\|X_t^x-X_t^y\|_H^2\leq e^{Ct}\|x-y\|_H^2$. For deterministic
  time-homogeneous coefficients this yields a Feller Markov transition
  semigroup on bounded continuous functions.
* **44. Invariant Gaussian laws.** For the linear equation with exponentially
  stable $S$, if
  $Q_\infty=\int_0^\infty S(s)BB^*S(s)^*ds$ is trace class, then
  $N(0,Q_\infty)$ is the unique invariant probability, and transition laws
  converge weakly to it. Its covariance solves the Lyapunov equation
  $AQ_\infty+Q_\infty A^*+BB^*=0$ in weak form.
* **45. Krylov–Bogoliubov existence.** For a Feller Markov semigroup on a
  Polish space, tightness of
  $T^{-1}\int_0^T\mathcal L(X_t^x)dt$ as $T\to\infty$ gives an invariant
  probability as a weak subsequential limit. Compact embeddings and coercive
  energy bounds provide a standard route to this tightness.

## Random-field SPDE and spatial regularity

**Space-time white noise** is the centered Gaussian random distribution with
covariance $\mathbb E[\xi(\phi)\xi(\psi)]=\int\phi\psi$.
The **Walsh integral** integrates predictable functions against the associated
orthogonal martingale measure. For the heat operator $\Delta$, write
$p_t(x)=(4\pi t)^{-d/2}e^{-|x|^2/(4t)}$.

* **46. Walsh isometry.** For square-integrable predictable $g$,
  $$\mathbb E\left|\int_0^T\int g(s,x)W(ds,dx)\right|^2
    =\mathbb E\int_0^T\int|g(s,x)|^2dx\,ds.$$
  This constructs stochastic convolutions pointwise in the spatial variable.
* **47. White-noise heat equation.** The stochastic heat convolution at a
  point has variance $\int_0^t\|p_s\|_2^2ds$, finite exactly when $d<2$.
  Thus spatially white forcing gives a function-valued heat convolution in
  dimension one, but distribution-valued solutions in higher dimensions.
* **48. Semilinear random-field existence.** In one space dimension, bounded
  measurable initial data and globally Lipschitz drift and noise coefficients
  give a unique predictable mild random-field solution of
  $\partial_tu=\Delta u+b(u)+\sigma(u)\xi$, with bounded moments uniformly
  over space and compact positive-time intervals.
* **49. Dalang's condition.** For temporally white Gaussian noise whose
  spatial covariance is a nonnegative tempered measure with spectral measure
  $\mu$, the heat stochastic convolution exists at a point exactly when
  $$\int_{\mathbb R^d}\frac{\mu(d\zeta)}{1+|\zeta|^2}<\infty.$$
  This condition also gives the standard Lipschitz semilinear random-field
  existence theory for bounded initial data.
* **50. Heat-equation Hölder exponents.** For the one-dimensional linear
  white-noise heat equation with smooth initial data, a version is locally
  Hölder of every time exponent below $1/4$ and every space exponent below
  $1/2$. The same upper regularity conclusions hold for globally Lipschitz
  semilinear equations with suitable bounded initial data away from time zero.
* **51. Comparison.** For one-dimensional stochastic heat equations driven
  by the same white noise and the same Lipschitz $\sigma$, ordered initial
  data and ordered Lipschitz drifts yield ordered continuous solutions almost
  surely. Strict positivity for the multiplicative heat equation follows by
  its stronger positivity theorem when the initial function is strictly positive.

## Distributional products and the entrance to singular SPDE

Write $\mathcal C^\alpha=B_{\infty,\infty}^\alpha$ for Hölder–Besov spaces,
using parabolic scaling when time is present. A **regularity structure** consists
of a graded space of local expansion symbols and a group transporting such
expansions between base points. A **model** $(\Pi_x,\Gamma_{xy})$ realizes the
symbols as distributions and satisfies compatibility
$\Pi_x\Gamma_{xy}=\Pi_y$ with the prescribed scaling bounds. A
**modelled distribution** of regularity $\gamma$ has local coefficients whose
transported differences in homogeneity $\beta$ are $O(|x-y|^{\gamma-\beta})$.

* **52. Product criterion.** If $\alpha<0<\beta$ and $\alpha+\beta>0$,
  multiplication extends continuously
  $\mathcal C^\alpha\times\mathcal C^\beta\to\mathcal C^\alpha$.
  Bony's decomposition separates low–high, high–low, and resonant interactions;
  the resonant term has regularity $\alpha+\beta$. Without positive total
  regularity, general distributions do not have a canonical product.
* **53. Parabolic Schauder gain.** Convolution with a localized heat kernel
  raises parabolic Hölder–Besov regularity by two, away from integer endpoint
  formulations, with the corresponding local estimates. This balances the
  loss of regularity in the nonlinear terms of a mild equation.
* **54. Regularity of white noise.** In $d$ spatial dimensions, space-time
  white noise belongs locally almost surely to parabolic $\mathcal C^\alpha$
  for every $\alpha<-(d+2)/2$. Its heat convolution consequently has
  regularity below $(2-d)/2$, explaining why nonlinear products require
  additional structure in the singular cases.
* **55. Reconstruction theorem.** For a model and a modelled distribution
  $f$ of regularity $\gamma>0$, there is a unique distribution $\mathcal Rf$
  satisfying
  $$|\langle\mathcal Rf-\Pi_xf(x),\phi_x^\lambda\rangle|
    \lesssim\lambda^\gamma$$
  locally, uniformly over normalized smooth test functions at scale $\lambda$.
  Test regularity exceeds the negative of the lowest homogeneity.
  Reconstruction is locally continuous jointly in the model and coefficients.
* **56. Renormalized two-dimensional cubic equation.** On the two-dimensional
  torus, smooth initial data and mollified space-time white noise yield solutions
  of
  $$\partial_tu_\varepsilon=(\Delta-1)u_\varepsilon
     -u_\varepsilon^3+3C_\varepsilon u_\varepsilon+\xi_\varepsilon,$$
  where $C_\varepsilon$ is the variance of the stationary mollified linear
  convolution. With this Wick normalization the solutions converge in
  probability on finite horizons in $C([0,T];\mathcal C^{-\kappa})$,
  $\kappa>0$, to a mollifier-independent solution. The divergent linear
  counterterm is part of the equation's definition.
* **57. Cole–Hopf solution of KPZ.** On the one-dimensional torus with smooth
  strictly positive initial data, the positive solution of
  $dZ=\Delta Z\,dt+Z\,dW$ defines $h=\log Z$.
  For spatially mollified noise, Itô's formula gives
  $$dh_\varepsilon=
    (\Delta h_\varepsilon+|\partial_xh_\varepsilon|^2
       -\tfrac12\|\rho_\varepsilon\|_2^2)dt+dW_\varepsilon.$$
  The logarithms converge to the Cole–Hopf KPZ solution. The subtraction and
  its coefficient are fixed by the stated heat and noise normalizations.

## Reference guide

Nualart, *The Malliavin Calculus and Related Topics*, Chapters 1–2, and
Nualart–Nualart, *Introduction to Malliavin Calculus*, Chapters 3–8, provide
overlapping treatments of chaos, differential operators, densities, and normal
approximation. Da Prato, Bogachev, Malliavin, Hu, and Nourdin–Peccati give
complementary Gaussian, geometric, and approximation viewpoints.

Friz–Hairer, *A Course on Rough Paths*, Chapters 2–5 and 8–11, supplies
controlled integration, RDEs, Brownian and Gaussian lifts; Lyons–Caruana–Lévy
and Friz–Victoir develop the extension and universal-limit theory in greater
generality. Friz–Hairer, Chapters 13–16, treats reconstruction and singular
equations. The two-dimensional cubic example and Cole–Hopf equation are useful
common models across singular-SPDE and random-interface treatments; they do
not represent the full scope of regularity structures or paracontrolled calculus.

Prévôt–Röckner, Chapters 2 and 4, and Liu–Röckner develop Hilbert-space
integration and variational solutions. Lototsky–Rozovsky provides a broad
independent SPDE course. Da Prato–Zabczyk is the principal semigroup reference,
while Walsh and the Dalang–Khoshnevisan–Mueller–Nualart–Xiao minicourse
develop the random-field viewpoint and its dimension-dependent existence criteria.

Local source anchors:

- [Nualart, *The Malliavin Calculus and Related Topics*](References/Nualart2006MalliavinCalculusRelatedTopics2ndEd-SpringerPIA.pdf).
- [Nualart–Nualart, *Introduction to Malliavin Calculus*](References/NualartNualart2018IntroductionMalliavinCalculus-CambridgeIMSTextbooks.pdf).
- [Friz–Hairer, *A Course on Rough Paths*](References/FrizHairer2020CourseRoughPathsIntroductionRegularityStructures2ndEd-Springer.UTX.pdf).
- [Prévôt–Röckner, *A Concise Course on SPDE*](References/PrévôtRöckner2007ConciseCourseStochasticPartialDifferentialEquations-SpringerLNM1905.pdf).
- [Liu–Röckner, *Stochastic Partial Differential Equations*](References/LiuRöckner2015StochasticPartialDifferentialEquationsIntroduction-SpringerUTX.pdf).
- [The Dalang et al. minicourse](References/DalangKhoshnevisanMuellerEtAl2009MinicourseStochasticPartialDifferentialEquations-Springer.LNM1962.pdf).
- [Lototsky–Rozovsky, *Stochastic Partial Differential Equations*](References/LototskyRozovsky2017StochasticPartialDifferentialEquations-SpringerUTX.pdf).
