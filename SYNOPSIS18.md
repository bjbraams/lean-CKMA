# Synopsis: Vector-valued analysis and analysis in Banach spaces

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-18);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects the working core of Section 18 of
[CKMA-bib.md](CKMA-bib.md#ckma-18). It connects
integration and martingales with Banach space geometry, Fourier multipliers,
randomized operator bounds, and evolution equations. Hytönen–van Neerven–
Veraar–Weis supplies the unifying treatment; the vector-measure, martingale,
Laplace-transform, and maximal-regularity references provide overlapping
foundations and applications. The target is a real or complex Banach space
$X$; Fourier multiplier and holomorphic calculus statements use complex
spaces or their complexifications.

The vector-valued toolkit here supports stochastic calculus in
[08A](CKMA-bib.md#ckma-08a), stochastic evolution in
[09C](CKMA-bib.md#ckma-09c), and maximal regularity in Section 24; Section 17
emphasises Banach-space structure itself.

For a complete measure space $(S,\Sigma,\mu)$, a function $f:S\to X$ is
**strongly measurable** if it is an almost-everywhere limit of measurable
simple functions, and **weakly measurable** if $x^*f$ is measurable for every
$x^*\in X^*$. The Bochner space $L^p(S;X)$ uses the norm
$(\int\|f\|^p)^{1/p}$, with the usual essential-supremum modification.
Probability filtrations are increasing unless stated otherwise.

## Bochner integration, duality, and differentiation

* **1. Pettis measurability theorem.** Strong measurability is equivalent
  to weak measurability together with being essentially separably valued:
  outside a null set, the range lies in a separable closed subspace of $X$.
* **2. Bochner integrability criterion.** A strongly measurable function
  is Bochner integrable exactly when $\int\|f\|\,d\mu<\infty$. Its integral
  satisfies $\|\int f\|\leq\int\|f\|$, and bounded linear operators commute
  with integration.
* **67. Pettis and Dunford integrals.** If $f:S\to X$ is weakly measurable
  and $x^*f\in L^1(\mu)$ for every $x^*\in X^*$, then for each
  $A\in\Sigma$ there is a unique $x_A^{**}\in X^{**}$ with
  $x_A^{**}(x^*)=\int_Ax^*f\,d\mu$ (the Dunford integral, by the closed
  graph theorem). The function is **Pettis integrable** if every $x_A^{**}$
  lies in $X$; then $A\mapsto\int_Af$ is a countably additive
  $\mu$-continuous vector measure (Pettis). Bochner integrable functions are
  Pettis integrable with the same integral. For finite $\mu$, every Dunford
  integrable function is Pettis integrable if $X$ is reflexive, and every
  strongly measurable one is if $X$ contains no copy of $c_0$. The map
  $t\mapsto e_t$ from $[0,1]$ to $\ell^2([0,1])$ is Pettis integrable with
  all integrals zero but is not strongly measurable.
* **3. Completeness and dominated convergence.** $L^p(S;X)$ is Banach for
  $1\leq p\leq\infty$. If $f_n\to f$ almost everywhere and
  $\|f_n\|\leq g\in L^p$, $p<\infty$, then $f_n\to f$ in $L^p(S;X)$.
  Integrable simple functions are dense when $p<\infty$.
* **4. Bochner Fubini theorem.** For $\sigma$-finite measure spaces,
  $L^p(S;L^p(T;X))\cong L^p(S\times T;X)$ isometrically for
  $1\leq p<\infty$. Integrable functions admit iterated Bochner integrals,
  and both orders equal the product integral.
* **5. Vector-valued Hölder duality.** Integration gives an isometric
  embedding $L^{p'}(S;X^*)\hookrightarrow L^p(S;X)^*$ for $1\leq p<\infty$
  on a $\sigma$-finite space. It is onto if $X^*$ has the Radon–Nikodým
  property; conversely, surjectivity on $[0,1]$ characterizes that property.
* **6. Conditional expectation.** Every $f\in L^p(\Omega;X)$ has an
  $X$-valued conditional expectation onto a sub-$\sigma$-algebra, contractive
  for $1\leq p\leq\infty$. It is characterized by its integrals on
  measurable sets and commutes with bounded linear maps. No Radon–Nikodým
  assumption on $X$ is required for this construction.
* **7. Lebesgue differentiation.** For $f\in L^1_{\rm loc}(\mathbb R^d;X)$,
  almost every $x$ is a norm Lebesgue point:
  $\lim_{r\downarrow0}\fint_{B(x,r)}\|f(y)-f(x)\|\,dy=0$.
  Consequently mollifiers converge locally in $L^p$ for $p<\infty$.
* **8. Fundamental theorem for Bochner integrals.** If $f\in L^1(0,T;X)$,
  $F(t)=\int_0^t f(s)\,ds$ is absolutely continuous and norm differentiable
  almost everywhere with derivative $f$. Every $W^{1,p}(0,T;X)$ function
  has such a representative after adding its initial value.
* **9. Vector-valued Young inequality.** For scalar $k\in L^1(\mathbb R^d)$,
  $\|k*f\|_{L^p(X)}\leq\|k\|_1\|f\|_{L^p(X)}$, including $p=1,\infty$.
  More generally the usual Young exponent relation holds with the norm of
  the vector-valued factor inside the scalar estimate.

## Vector measures and the Radon–Nikodým property

A countably additive $X$-valued measure $\nu$ has **bounded variation** if
$|\nu|(S)=\sup\sum_j\|\nu(A_j)\|<\infty$, over finite measurable
partitions. $X$ has the **Radon–Nikodým property** (RNP) if every such
measure absolutely continuous with respect to a finite positive measure
has a Bochner integrable density.

* **68. Bartle–Dunford–Schwartz theorem.** Let $F:\Sigma\to X$ be
  countably additive on a $\sigma$-algebra, with semivariation
  $\|F\|(A)=\sup_{\|x^*\|\leq1}|x^*F|(A)$. Then $F$ has bounded, relatively
  weakly compact range, and there is a finite positive **control measure**
  $\lambda$ on $\Sigma$ with $\|F\|(A)\to0$ as $\lambda(A)\to0$; one may
  take $\lambda=|x^*F|$ for a suitable $x^*\in X^*$ (Rybakov). Weak
  countable additivity already implies countable additivity (Orlicz–Pettis),
  and $F$ need not have bounded variation.
* **69. Lyapunov convexity theorem.** The range
  $\{\nu(A):A\in\Sigma\}$ of a nonatomic countably additive measure
  $\nu:\Sigma\to\mathbb R^n$ is compact and convex. In infinite dimensions
  this can fail: $A\mapsto\mathbf 1_A\in L^2[0,1]$ is nonatomic, with closed
  range that is neither compact nor convex. If $X$ has RNP and $F$ is
  countably additive, nonatomic, and of bounded variation, the closure of its
  range is compact and convex (Uhl). Lyapunov's theorem underlies bang–bang
  principles in control theory.
* **10. Vector Radon–Nikodým theorem.** In an RNP space, $\nu\ll\mu$
  of bounded variation has a unique density $f\in L^1(\mu;X)$, with
  $\nu(A)=\int_A f\,d\mu$ and $|\nu|(A)=\int_A\|f\|\,d\mu$.
* **11. Stability and examples of RNP.** Closed subspaces of RNP spaces
  have RNP. Reflexive spaces and separable dual spaces have RNP; $c_0$,
  $L^1[0,1]$, and $C[0,1]$ do not. RNP is separably determined but not
  inherited by quotients, since every separable space is a quotient of $\ell^1$.
* **12. Lipschitz characterization.** $X$ has RNP exactly when every
  Lipschitz curve $[0,1]\to X$ is differentiable almost everywhere.
  In this case such curves are integrals of their essentially bounded derivatives.
* **13. Martingale characterization of RNP.** $X$ has RNP exactly when
  every uniformly integrable $X$-valued martingale converges in $L^1$ and
  almost surely in norm. It is enough to test the dyadic filtration on
  $[0,1]$.
* **14. Bounded $L^p$ martingales.** If $X$ has RNP and $1<p<\infty$,
  every $L^p$-bounded martingale converges almost surely and in $L^p$ to
  a terminal variable $M_\infty$, with $M_n=\mathbb E(M_\infty\mid\mathcal F_n)$.
* **70. Representable operators on $L^1$.** For finite $\mu$, a bounded
  $T:L^1(\mu)\to X$ is **representable** if $Tf=\int fg\,d\mu$ for some
  $g\in L^\infty(\mu;X)$, and then $\|T\|=\|g\|_\infty$. Weakly compact
  operators from $L^1(\mu)$ are representable (Dunford–Pettis–Phillips), and
  $X$ has RNP exactly when every bounded operator $L^1[0,1]\to X$ is
  representable. Representable operators are exactly those factoring through
  $\ell^1$ (Lewis–Stegall).

## Random sums, martingale inequalities, and UMD spaces

An $X$-valued **martingale difference sequence** $(d_n)$ satisfies
$d_n\in L^1(\mathcal F_n;X)$ and
$\mathbb E(d_n\mid\mathcal F_{n-1})=0$. The space is **UMD** if, for
some $1<p<\infty$, there is $\beta$ such that every finite such sequence
and every deterministic choice of signs obey
$$\left\|\sum_n\varepsilon_nd_n\right\|_{L^p(X)}
 \leq\beta\left\|\sum_nd_n\right\|_{L^p(X)}.$$
The abbreviation stands for unconditional martingale differences.

* **15. Doob maximal inequality.** For an $X$-valued martingale and
  $1<p<\infty$,
  $\|\max_{n\leq N}\|M_n\|\|_p\leq p'\|M_N\|_{L^p(X)}$.
  This follows from the scalar submartingale $\|M_n\|$ and holds in every $X$.
* **16. Kahane contraction principle.** For independent signs $(r_j)$,
  real scalars $|a_j|\leq1$, and $p\geq1$,
  $\|\sum r_ja_jx_j\|_{L^p(X)}\leq\|\sum r_jx_j\|_{L^p(X)}$.
  Complex coefficients satisfy the analogous estimate with an absolute constant.
* **18. UMD extrapolation.** If the defining martingale transform estimate
  holds for one exponent $p\in(1,\infty)$, it holds for every such exponent.
  It also holds for predictable scalar multipliers with absolute value at
  most one, with constants depending on $p$ and $X$.
* **19. UMD stability.** Closed subspaces, quotients, and duals of UMD
  spaces are UMD. For $1<q<\infty$, $L^q(S;X)$ is UMD exactly when $X$ is.
  Burkholder's geometric characterization: $X$ is UMD exactly when it is
  $\zeta$-convex, i.e. some biconvex $\zeta:X\times X\to\mathbb R$ has
  $\zeta(0,0)>0$ and $\zeta(x,y)\leq\|x+y\|$ whenever $\|x\|=\|y\|=1$.
* **20. Standard examples.** Hilbert spaces, scalar $L^q$ spaces, and
  Schatten classes $S^q$ are UMD for $1<q<\infty$. Infinite-dimensional
  $L^1$, $L^\infty$, and $c_0$ are not UMD.
* **71. Burkholder's sharp constant.** For a Hilbert space $X$, including
  the scalar field, and $1<p<\infty$, the optimal UMD constant is
  $\beta_p=p^*-1$, $p^*=\max(p,p/(p-1))$. The same bound holds for
  transforms by predictable real multipliers with values in $[-1,1]$. The
  proof constructs an explicit special function, the model for later
  Bellman-function arguments.
* **21. Geometric consequences.** UMD spaces are superreflexive, have
  nontrivial Rademacher type and finite cotype, and have RNP. Reflexivity
  or superreflexivity alone does not imply UMD.
* **22. Randomized martingale equivalence.** In a UMD space,
  $\|\sum d_n\|_{L^p(\Omega;X)}$ is equivalent to
  $(\mathbb E_r\|\sum r_nd_n\|_{L^p(\Omega;X)}^p)^{1/p}$,
  uniformly over finite difference sequences.
* **23. Vector-valued Stein inequality.** In a UMD space, conditional
  expectations associated with one filtration form an R-bounded family
  on $L^p(\Omega;X)$ for $1<p<\infty$. The randomized inequality applies
  to arbitrary input functions, without requiring them to be adapted.
* **24. Martingale type and smooth renorming.** For $1<p\leq2$, the
  estimate $\mathbb E\|\sum d_j\|^p\leq C^p\sum\mathbb E\|d_j\|^p$
  holds exactly when $X$ admits an equivalent norm with modulus of
  smoothness at most $Ct^p$ (with possibly another $C$).
* **25. Martingale cotype and convex renorming.** For $2\leq q<\infty$,
  $\sum\mathbb E\|d_j\|^q\leq C^q\mathbb E\|\sum d_j\|^q$ holds
  exactly when $X$ has an equivalent norm with modulus of convexity at
  least $c\varepsilon^q$.

## R-bounded and Gaussian-bounded operator families

A family $\mathcal T\subset\mathcal L(X,Y)$ is **R-bounded** if
$$\left(\mathbb E\left\|\sum_jr_jT_jx_j\right\|^2\right)^{1/2}
 \leq C\left(\mathbb E\left\|\sum_jr_jx_j\right\|^2\right)^{1/2}$$
for all finite choices $T_j\in\mathcal T$ and $x_j\in X$. Replacing
signs by independent standard real Gaussians defines **$\gamma$-boundedness**.
These are bounds on whole families acting on random sums, rather than just
on each operator separately.

* **26. Independence of random-sum exponent.** Replacing the second
  moments in the definition by any fixed positive moment yields equivalent
  R-bounds or $\gamma$-bounds, by moment equivalence (SYNOPSIS17, item 35).
* **27. Stability of R-bounds.** R-bounded families are uniformly bounded.
  Finite unions, sums, compositions, and strong-operator closures preserve
  R-boundedness with the corresponding bounds. Closed absolutely convex
  hulls preserve it up to a scalar-field constant.
* **28. Hilbert space reduction.** For maps between Hilbert spaces,
  R-boundedness, $\gamma$-boundedness, and uniform boundedness coincide,
  with their second-moment bounds equal. Uniform boundedness alone is
  insufficient on general Banach spaces.
* **29. R-bounds and Gaussian bounds.** Every R-bounded family is
  $\gamma$-bounded. If the source has finite cotype, the converse holds
  with a constant depending on that space.
* **30. Integrating an R-bounded family.** If $T(s)$ has R-bounded range,
  the operators $\int a(s)T(s)\,d\mu(s)$ with $\|a\|_1\leq1$ form an
  R-bounded family, whenever the integrals exist strongly on each vector.
* **31. Differentiable families.** If $T:[a,b]\to\mathcal L(X,Y)$ is
  continuously differentiable and
  $\|T(a)\|+\int_a^b\|T'(t)\|\,dt<\infty$, its range is R-bounded,
  with bound controlled by this quantity.

## Fourier analysis and randomized Littlewood–Paley theory

Use $\widehat f(\xi)=\int e^{-ix\cdot\xi}f(x)\,dx$ on Bochner
integrable functions. For a symbol $m(\xi)\in\mathcal L(X,Y)$, a
**Fourier multiplier** is the extension of
$T_mf=\mathcal F^{-1}(m\widehat f)$ to the indicated $L^p$ spaces.

* **32. Hilbert-valued Plancherel theorem.** If $X$ is Hilbert, Fourier
  transformation extends to $L^2(\mathbb R^d;X)$ with
  $\|\widehat f\|_2=(2\pi)^{d/2}\|f\|_2$. A comparable $L^2$ estimate
  for Fourier transformation characterizes spaces isomorphic to Hilbert space.
* **72. Fourier type.** $X$ has **Fourier type** $p\in[1,2]$ if Fourier
  transformation is bounded from $L^p(\mathbb R^d;X)$ to
  $L^{p'}(\mathbb R^d;X)$. Every space has Fourier type one; Fourier type $p$
  implies type $p$ and cotype $p'$; $L^q$ has Fourier type $\min(q,q')$ for
  $1\leq q<\infty$; and Fourier type two characterizes spaces isomorphic to
  Hilbert space (Kwapień, result 32). A space has some Fourier type $p>1$
  exactly when it has nontrivial type (Bourgain).
* **33. Hilbert transform characterization.** $X$ is UMD exactly when
  $Hf(x)=\operatorname{p.v.}\,\pi^{-1}\int f(x-y)/y\,dy$ is bounded on
  $L^p(\mathbb R;X)$ for one, hence every, $1<p<\infty$.
* **34. Riesz transforms.** In a UMD space the multipliers
  $-i\xi_j/|\xi|$ are bounded on $L^p(\mathbb R^d;X)$ for
  $1<p<\infty$. Conversely boundedness of a classical Riesz transform
  on such a space characterizes UMD.
* **35. Vector-valued Calderón–Zygmund theorem.** Let $T$ be bounded from
  $L^{p_0}(\mathbb R^d;X)$ to $L^{p_0}(\mathbb R^d;Y)$ for some
  $1<p_0<\infty$, with an $\mathcal L(X,Y)$-valued kernel representing it off
  the support of compactly supported $f$ and satisfying Hörmander's condition
  $\int_{|x-y|>2|y-y'|}\|K(x,y)-K(x,y')\|\,dx\leq C$. Then $T$ is of weak
  type $(1,1)$ and bounded on $L^p$ for $1<p\leq p_0$; the dual condition
  gives $p_0<p<\infty$ (Benedek–Calderón–Panzone). No geometric property of
  $X$ enters beyond the initial $L^{p_0}$ bound.
* **36. Necessary R-bounded range.** If a strongly continuous
  operator-valued symbol defines a bounded $L^p(\mathbb R^d;X)\to
  L^p(\mathbb R^d;Y)$ multiplier, its range is R-bounded. For merely
  measurable symbols $m$, the set of values $m(\xi)$ at Lebesgue points $\xi$
  of $m$ is R-bounded (Clément–Prüss).
* **37. Operator-valued Mihlin theorem on the line.** If $X,Y$ are UMD,
  $m\in C^1(\mathbb R\setminus\{0\};\mathcal L(X,Y))$, and
  $\{m(\xi),\xi m'(\xi):\xi\ne0\}$ is R-bounded, then $T_m$ is bounded
  from $L^p(\mathbb R;X)$ to $L^p(\mathbb R;Y)$ for $1<p<\infty$.
* **38. A multidimensional Mihlin formulation.** For UMD $X,Y$, it is
  sufficient that a symbol have continuous derivatives through order $d$
  away from zero and that
  $\{|\xi|^{|\alpha|}\partial^\alpha m(\xi):\xi\ne0,\
  \alpha\in\{0,1\}^d\}$ be R-bounded. Then it is an $L^p$ multiplier
  for every $1<p<\infty$.
* **39. Randomized Littlewood–Paley equivalence.** For a smooth dyadic
  annular partition $(\Delta_j)$ and UMD $X$,
  $$\|f\|_{L^p(X)}\asymp
    \left(\mathbb E_r\left\|\sum_jr_j\Delta_jf\right\|_{L^p(X)}^p\right)^{1/p},
       \qquad1<p<\infty.$$
  The inhomogeneous version includes one low-frequency block.
* **40. Sobolev and Bessel potential agreement.** If $X$ is UMD,
  $1<p<\infty$, and $k$ is a nonnegative integer, then
  $W^{k,p}(\mathbb R^d;X)=H^{k,p}(\mathbb R^d;X)$ with equivalent norms,
  where $\|f\|_{H^{s,p}}=\|(I-\Delta)^{s/2}f\|_{L^p(X)}$.
* **41. Interpolation of Bochner spaces.** For $1\leq p_0,p_1<\infty$,
  $0<\theta<1$, and $1/p=(1-\theta)/p_0+\theta/p_1$,
  on a $\sigma$-finite measure space,
  $[L^{p_0}(S;X_0),L^{p_1}(S;X_1)]_\theta
  =L^p(S;[X_0,X_1]_\theta)$ for compatible complex Banach couples,
  with the usual natural norm identification.
* **42. Bessel potential interpolation.** For UMD $X$,
  $[H^{s_0,p}(X),H^{s_1,p}(X)]_\theta=H^{(1-\theta)s_0+\theta s_1,p}(X)$
  with equivalent norms, for real $s_0,s_1$ and $1<p<\infty$.

## Gaussian radonifying operators and stochastic integration

For real Hilbert $H$, the space $\gamma(H,X)$ is the completion of
finite-rank maps in the norm
$\|T\|_\gamma^2=\mathbb E\|\sum_j\gamma_jTh_j\|^2$, with $(h_j)$
orthonormal on their finite-dimensional support. These are the
**$\gamma$-radonifying operators**. Complex spaces may be regarded as real
for this construction. A cylindrical Brownian motion $W_H$ has independent
scalar Brownian coordinates along an orthonormal basis of $H$.

For a function $\phi:S\to X$, its radonifying function norm means the
norm of the integral operator $R_\phi g=\int_Sg(s)\phi(s)\,d\mu(s)$
from $L^2(S)$ to $X$, initially interpreted by scalar duality when needed.
For operator-valued $\Phi$, similarly
$R_\Phi g=\int_0^T\Phi(t)g(t)\,dt$ on $L^2(0,T;H)$.

* **43. Basis independence and Gaussian realization.** The radonifying
  norm is independent of the orthonormal basis. For separable $H$, a bounded
  $T:H\to X$ is radonifying exactly when $\sum_j\gamma_jTh_j$ converges
  in $L^2(\Omega;X)$; the sum realizes a Radon Gaussian variable with
  covariance $TT^*$.
* **44. Radonifying ideal property.** If $T\in\gamma(H,X)$,
  $A\in\mathcal L(X,Y)$, and $B\in\mathcal L(K,H)$, then
  $ATB\in\gamma(K,Y)$ and
  $\|ATB\|_\gamma\leq\|A\|\|T\|_\gamma\|B\|$.
* **45. Hilbert–Schmidt case.** For Hilbert targets,
  $\gamma(H,X)$ equals the Hilbert–Schmidt class, isometrically. Thus
  the general radonifying norm extends the square-summability norm used
  in Hilbert-valued stochastic integration.
* **46. Square functions in $L^q$.** For $1\leq q<\infty$ and an
  orthonormal basis $(h_j)$,
  $$\|T\|_{\gamma(H,L^q(S))}\asymp_q
       \left\|\left(\sum_j|Th_j|^2\right)^{1/2}\right\|_{L^q(S)}.$$
  Finiteness of this square-function norm characterizes the radonifying maps.
* **47. Gamma Fubini theorem.** For $1\leq p<\infty$,
  $\gamma(H,L^p(S;X))\cong L^p(S;\gamma(H,X))$ with equivalent norms,
  under the natural identification on finite-rank tensors.
* **48. Type, cotype, and time integration.** Type two of $X$ gives the
  continuous embedding $L^2(S;X)\hookrightarrow\gamma(L^2(S),X)$ via
  integral operators; cotype two gives the reverse embedding. Both
  embeddings together characterize the Hilbert space isomorphism class.
* **49. Gamma multiplier theorem.** If $M(s)\in\mathcal L(X,Y)$ is
  strongly measurable on each vector and has $\gamma$-bounded range, then
  pointwise multiplication by $M$ extends boundedly between the associated
  radonifying function spaces when $Y$ contains no copy of $c_0$.
* **50. Deterministic stochastic integrability.** A deterministic
  operator-valued function $\Phi$ is integrable against $W_H$ exactly when
  its integral operator $R_\Phi:L^2(0,T;H)\to X$ is radonifying, assuming
  the scalar integrals defining $R_\Phi$ exist. Its Gaussian integral obeys
  $\mathbb E\|\int_0^T\Phi\,dW_H\|^2=\|R_\Phi\|_\gamma^2$.
* **51. UMD Itô isomorphism.** For adapted elementary $\Phi$ in a UMD
  space and $1<p<\infty$,
  $$\mathbb E\sup_{t\leq T}\left\|\int_0^t\Phi\,dW_H\right\|^p
       \asymp_{p,X}\mathbb E\|R_\Phi\|_{\gamma(L^2(0,T;H),X)}^p.$$
  Completion gives the stochastic integral for limits in this norm
  ([van Neerven–Veraar–Weis, Theorem 5.5](https://arxiv.org/abs/1304.7575)).
* **52. Martingale type-two integration bound.** If $X$ has martingale
  type two, adapted elementary processes satisfy
  $\mathbb E\|\int_0^T\Phi\,dW_H\|^2
  \leq C_X\mathbb E\int_0^T\|\Phi(t)\|_{\gamma(H,X)}^2dt$.
  This supplies a sufficient stochastic integrability criterion.

## Laplace transforms, functional calculus, and maximal regularity

For an exponentially bounded function, its **Laplace transform** is
$\mathcal Lf(\lambda)=\int_0^\infty e^{-\lambda t}f(t)\,dt$ on a right
half-plane. A densely defined closed operator $A$ is **sectorial** of
angle $\omega<\pi$ if its spectrum lies in $\overline{\Sigma_\omega}$,
$\Sigma_\theta=\{z\ne0:|\arg z|<\theta\}$, and
$\lambda(\lambda-A)^{-1}$ is uniformly bounded outside every larger sector.
Replacing these bounds by R-bounds defines **R-sectoriality**.

* **53. Vector-valued holomorphy.** A function $f:U\to X$ on open
  $U\subset\mathbb C$ is norm holomorphic exactly when $x^*\circ f$ is
  holomorphic for every $x^*\in X^*$ (Dunford); for locally bounded $f$ a
  norming subspace of $X^*$ suffices. Cauchy's integral formula, power series
  expansions, Liouville's theorem, and Vitali-type convergence theorems then
  hold as in the scalar case.
* **54. Laplace uniqueness and holomorphy.** Bochner Laplace transforms
  are holomorphic on their half-plane of absolute convergence. Equal
  transforms imply equality almost everywhere of the original locally
  integrable functions; bounded linear maps commute with transformation.
* **55. Laplace convolution theorem.** Under exponential integrability,
  $\mathcal L(k*f)(\lambda)=\mathcal Lk(\lambda)\mathcal Lf(\lambda)$,
  including operator-valued $k$ acting on $X$-valued $f$, with the displayed
  order of multiplication.
* **56. Widder–Arendt theorem.** For $r\in C^\infty((0,\infty);X)$ and
  $M\geq0$, the bounds
  $\|\lambda^{n+1}r^{(n)}(\lambda)/n!\|\leq M$ for all $\lambda>0$,
  $n\geq0$, hold exactly when $r(\lambda)=\lambda\int_0^\infty
  e^{-\lambda t}F(t)\,dt$ for some $F$ with $F(0)=0$ and Lipschitz
  constant at most $M$. If $X$ has RNP, $r$ is then the Laplace transform of
  a function bounded by $M$. This gives a Laplace-transform proof of the
  Hille–Yosida theorem and the theory of integrated semigroups.
* **58. Sectorial holomorphic calculus.** For holomorphic $f$ on a sector
  larger than that of $A$, with suitable decay at zero and infinity,
  $$f(A)=\frac1{2\pi i}\int_\Gamma f(z)(z-A)^{-1}\,dz.$$
  The construction is an algebra homomorphism and extends by regularization
  where defined. A bounded $H^\infty$ calculus means
  $\|f(A)\|\leq C\|f\|_\infty$ on such a sector.
* **59. Bounded calculus and R-sectoriality.** On a UMD space, a sectorial
  operator with bounded $H^\infty$ calculus is R-sectorial on every strictly
  larger sector. In particular, a calculus angle below $\pi/2$ yields an
  R-sectorial angle below $\pi/2$.
* **60. Dore–Venni theorem.** Let $X$ be UMD and let $A,B$ be
  resolvent-commuting sectorial operators, one of them invertible, with bounded
  imaginary powers $\|A^{is}\|\leq Ke^{\theta_A|s|}$,
  $\|B^{is}\|\leq Ke^{\theta_B|s|}$, and $\theta_A+\theta_B<\pi$. Then
  $A+B$ on $D(A)\cap D(B)$ is closed and invertible. With $B=d/dt$ on
  $L^p(0,T;X)$, $D(B)=\{u\in W^{1,p}(0,T;X):u(0)=0\}$, this gives maximal
  regularity for $A$ of power angle below $\pi/2$.

For the next statements assume $A$ is invertible and sectorial with angle
below $\pi/2$, so $e^{-tA}$ is bounded analytic and exponentially stable.
**Maximal $L^p$ regularity** means that for every $f\in L^p(0,\infty;X)$,
$u'+Au=f$, $u(0)=0$, has a solution in
$W^{1,p}(0,\infty;X)\cap L^p(0,\infty;D(A))$ with
$\|u'\|_p+\|Au\|_p\leq C\|f\|_p$.

The characterizations of maximal regularity (de Simon, Weis, the
$H^\infty$-calculus criterion, and the initial trace space) are SYNOPSIS24,
items 30–33.

* **65. Bounded perturbations.** If $A$ has maximal regularity and
  $B\in\mathcal L(X)$, then $A+B$ has maximal regularity on finite
  intervals. A sufficiently large positive shift gives the corresponding
  exponentially stable half-line formulation.
* **66. Vector-valued heat regularity.** If $X$ is UMD and $1<p,q<\infty$,
  the zero-initial-value equation $u_t-\Delta u+u=f$ on $\mathbb R^d$
  satisfies
  $\|u_t\|_{L^p_tL^q_x(X)}+\|u\|_{L^p_tW^{2,q}_x(X)}
  \leq C\|f\|_{L^p_tL^q_x(X)}$ on the half-line.

## Reference guide

Hytönen–van Neerven–Veraar–Weis, Volume I, develops Bochner spaces, RNP,
martingales, UMD, and vector-valued Fourier analysis. Volume II supplies
random-sum geometry, R-bounds, radonifying operators, and functional calculus.
Pisier's martingale monograph independently develops the geometric and
renorming connections. Arendt–Batty–Hieber–Neubrander gives the Laplace
transform and Cauchy-problem route, including vector-valued holomorphy and
the Widder–Arendt theorem; Diestel–Uhl and the stochastic evolution
literature supply the vector-measure and integration background, including
the Pettis integral, the Bartle–Dunford–Schwartz and Lyapunov theorems, and
representable operators. Osękowski develops Burkholder's sharp martingale
inequalities.

The maximal-regularity characterization and perturbation statements can also
be checked in [Kunstmann–Weis's lecture notes](https://www.karlin.mff.cuni.cz/~barta/ToDownload/Kunstmann-Weis2004.pdf),
especially the introductory characterization and operator-sum sections.
The stochastic integration statements are also treated in
[van Neerven–Veraar–Weis's survey](https://arxiv.org/abs/1304.7575).
These are accessible author texts corresponding to the references named in
the bibliography. More general noninvertible, weighted, nonautonomous, and
stochastic maximal-regularity variants require additional hypotheses and are
not subsumed by the formulations above.

Local source copies consulted:

* [Hytönen–van Neerven–Veraar–Weis, Analysis in Banach Spaces I](References/HytönenVanNeervenVeraarWeis2016AnalysisInBanachSpacesVol1MartingalesLittlewoodPaleyTheory-SpringerEMG.pdf).
* [Hytönen–van Neerven–Veraar–Weis, Analysis in Banach Spaces II](References/HytönenVanNeervenVeraarWeis2017AnalysisInBanachSpacesVol2ProbabilisticMethodsOperatorTheory-SpringerEMG.pdf).
* [Pisier, Martingales in Banach Spaces](References/Pisier2016MartingalesBanachSpaces-Cambridge.StudAM155.pdf).
* [Arendt–Batty–Hieber–Neubrander, Vector-Valued Laplace Transforms and Cauchy Problems](References/ArendtBattyHieberNeubrander2011VectorValuedLaplaceTransformsCauchyProblems-Birkhauser.MMA96.pdf).
