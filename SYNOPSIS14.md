# Synopsis: Functional, isoperimetric, and geometric inequalities

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-14);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects the recurring graduate and beginning research core of
Section 14 of [CKMA-bib.md](CKMA-bib.md#ckma-14).
Its subject is the interaction of norm inequalities, perimeter and capacity,
spectral gaps, heat propagation, curvature, and transport. Classical statements
also appearing in Section 11 are retained where they anchor a different set
of connections. Euclidean results are separated from probability and
Riemannian formulations so that their constants and normalizations remain visible.

The inequality viewpoint here complements metric geometry in
[39A](CKMA-bib.md#ckma-39a), diffusion and curvature estimates in
[39B](CKMA-bib.md#ckma-39b), and transport and displacement convexity in
[39C](CKMA-bib.md#ckma-39c); function-space construction remains in Section
26. Concentration consequences are developed in Section 7, perimeter and
geometric measure theory in Section 37, Riemannian comparison geometry
(Bonnet–Myers, Bishop–Gromov, Li–Yau) in Section 52, heat-kernel equivalences
in Section 39, and semiclassical eigenvalue bounds (Lieb–Thirring) in
Sections 22 and 53. The convex-geometric inequalities of mixed volumes and
sections complement the convex analysis of Section 12.

Write $\omega_n=|B_1(0)|$, $p^*=np/(n-p)$ for $p<n$, and
$\mathcal E(f,f)=\int\Gamma(f)\,d\mu$ for a Dirichlet energy, where the
carré du champ $\Gamma$ is defined before result 33 ($\Gamma(f)=|\nabla f|^2$
for the Euclidean or Riemannian Laplacian). The perimeter $P(E)$ of a measurable
set is the total variation of the distributional gradient of $\mathbf 1_E$. A probability
measure satisfies **Poincaré with constant $C_P$** if
$\mathop{\mathrm{Var}}_\mu f\leq C_P\mathcal E(f,f)$, and **logarithmic Sobolev
with constant $C_{LS}$** if
$\mathop{\mathrm{Ent}}_\mu(f^2)\leq2C_{LS}\mathcal E(f,f)$.
Here $\mathop{\mathrm{Ent}}_\mu h=\int h\log(h/\int h\,d\mu)d\mu$.
The heat generator throughout is $\Delta$, rather than $\frac12\Delta$.

An inequality is **sharp** when its constant cannot be improved; this does
not imply that an admissible nonzero function attains equality. A **stability
inequality** controls distance from the family of extremizers by the deficit
in the sharp inequality. A **defective** functional inequality has an extra
lower-order term, often needed on finite-volume spaces where constants have
zero gradient. Scaling, boundary conditions, and normalization of total mass
must therefore be fixed before comparing constants from different formulations.

## Sobolev, interpolation, and singular-weight inequalities

The space $W^{1,p}(\Omega)$ consists of functions with themselves and their
weak first derivatives in $L^p$; $W_0^{1,p}$ is the closure of compactly
supported smooth functions. The homogeneous energy space on $\mathbb R^n$
is the completion in the gradient norm where the Sobolev inequality makes
this a function space. Constants below are finite and positive unless indicated.
The basic Gagliardo–Nirenberg, Poincaré, Morrey, and trace embeddings are
stated in Section 26; this section records sharp constants and extremals.

* **1. Endpoint Sobolev and isoperimetry.** For compactly supported smooth
  functions in dimension $n\geq2$,
  $$\|u\|_{n/(n-1)}\leq\frac1{n\omega_n^{1/n}}\|\nabla u\|_1.$$
  The extension to $BV$ is equivalent by coarea to
  $P(E)\geq n\omega_n^{1/n}|E|^{(n-1)/n}$. Equality at positive finite volume
  holds exactly for balls, up to null sets (De Giorgi).
* **2. Sobolev inequality.** For $1<p<n$,
  $\|u\|_{p^*}\leq S_{n,p}\|\nabla u\|_p$ on $C_c^\infty(\mathbb R^n)$
  and its homogeneous completion. The exponent is forced by scaling.
* **3. Sharp Sobolev inequality (Aubin, Talenti).** For $n\geq3$, the best
  constant $S_n=S_{n,2}$ is attained in the homogeneous space by
  $U(x)=(1+|x|^2)^{-(n-2)/2}$. Thus
  $S_n=\|U\|_{2^*}/\|\nabla U\|_2$; all nonzero real extremizers are its
  scalar multiples, translations, and dilations. For general $1<p<n$ the
  extremal profile is $(1+|x|^{p/(p-1)})^{-(n-p)/p}$.
* **6. Payne–Weinberger diameter bound.** On a bounded convex domain of
  diameter $D$, mean-zero $u\in H^1$ satisfies
  $\int|\nabla u|^2\geq\pi^2D^{-2}\int|u|^2$. The constant is sharp
  across convex domains.
* **8. Moser–Trudinger inequality.** If $n\geq2$, $|\Omega|<\infty$, and
  $u\in W_0^{1,n}(\Omega)$ with $\|\nabla u\|_n\leq1$, then
  $$\int_\Omega\exp(\alpha_n|u|^{n/(n-1)})dx\leq C_n|\Omega|,
    \qquad\alpha_n=n|S^{n-1}|^{1/(n-1)}.$$
  Increasing $\alpha_n$ makes the uniform bound false.
* **9. Hardy inequality.** For $1<p<n$,
  $\int|\nabla u|^p\geq((n-p)/p)^p\int|u|^p/|x|^p$ on
  $C_c^\infty(\mathbb R^n)$. The scale-invariant constant is optimal; it is
  not attained in the homogeneous Sobolev space.
* **10. Rellich inequality.** For $n\geq5$ and
  $u\in C_c^\infty(\mathbb R^n\setminus\{0\})$,
  $$\int|\Delta u|^2dx\geq\left(\frac{n(n-4)}4\right)^2
    \int\frac{|u|^2}{|x|^4}dx.$$
  The constant is optimal.
* **11. Boundary Hardy inequality.** For a proper convex open set,
  $\int_\Omega|\nabla u|^2\geq\frac14\int_\Omega
  |u|^2/\mathop{\mathrm{dist}}(x,\partial\Omega)^2$ for $u\in C_c^\infty(\Omega)$.
  The coefficient $1/4$ is the best constant for every such $\Omega$; for
  nonconvex domains the best constant may be smaller.
* **12. Caffarelli–Kohn–Nirenberg inequality.** For $n\geq3$,
  $a<(n-2)/2$, $a\leq b\leq a+1$, and $p=2n/(n-2+2(b-a))$,
  $$\Big(\int|x|^{-bp}|u|^p\,dx\Big)^{2/p}\leq C\int|x|^{-2a}|\nabla u|^2dx$$
  on $C_c^\infty(\mathbb R^n)$. The cases $a=b=0$ and $b=a+1$ are the Sobolev
  and weighted Hardy inequalities; the exponent is again forced by scaling.
* **13. Hardy–Littlewood–Sobolev inequality.** If $0<\lambda<n$ and
  $1/p+1/q+\lambda/n=2$ with $p,q>1$, then
  $\iint |f(x)g(y)|/|x-y|^\lambda\,dxdy\leq C\|f\|_p\|g\|_q$.
  For $p=q=2n/(2n-\lambda)$ the sharp constant is attained exactly by
  translates, dilates, and multiples of $(1+|x|^2)^{-(2n-\lambda)/2}$ (Lieb).
* **14. Fractional Sobolev inequality.** For $0<s<n/2$,
  $\|u\|_{2n/(n-2s)}\leq C\|(-\Delta)^{s/2}u\|_2$ on the homogeneous
  fractional Sobolev space. It is the dual Riesz-potential form of result 13.

## Capacity, perimeter, and spectral optimization

For compact $K\subset\Omega$, the relative **$p$-capacity** is
$\mathop{\mathrm{cap}}_p(K,\Omega)=\inf\int_\Omega|\nabla v|^p$, over
$v\in C_c^\infty(\Omega)$ at least one near $K$.
Perimeter is the total variation of the distributional gradient of an indicator;
it is meaningful for nonsmooth sets. The first Dirichlet eigenvalue is the
infimum of $\int|\nabla u|^2/\int u^2$ over nonzero $H_0^1(\Omega)$.

* **16. Maz'ya capacitary criterion.** For a positive Radon measure $\nu$,
  $1<p\leq q<\infty$, the inequality
  $\|u\|_{L^q(\nu)}\leq C\|\nabla u\|_{L^p(\Omega)}$ on $C_c^\infty(\Omega)$
  holds exactly when
  $$\nu(K)^{p/q}\leq C'\mathop{\mathrm{cap}}\nolimits_p(K,\Omega)$$
  for every compact $K\subset\Omega$. The optimal constants are comparable
  after the appropriate $p$th power, with factors depending on the exponents.
* **17. Strong capacitary inequality.** For $1<p<\infty$ and smooth compactly
  supported $u$,
  $$\int_0^\infty\mathop{\mathrm{cap}}\nolimits_p(\{|u|\geq t\},\Omega)\,d(t^p)
    \leq C_p\int_\Omega|\nabla u|^pdx.$$
  This is stronger than estimating each individual superlevel capacity.
* **18. Isocapacitary inequality.** For $1<p<n$, among compact sets of fixed
  positive volume in $\mathbb R^n$, the ball minimizes homogeneous $p$-capacity.
  The comparison has the scale $|K|^{(n-p)/n}$.
* **19. Pólya–Szegő inequality.** If $u\geq0$ on $\mathbb R^n$ vanishes at
  infinity in the sense $|\{u>t\}|<\infty$ for $t>0$, and
  $u\in W^{1,p}_{\mathrm{loc}}$ with $\nabla u\in L^p$, $1\leq p<\infty$, then
  its symmetric decreasing rearrangement satisfies
  $\|\nabla u^*\|_p\leq\|\nabla u\|_p$, while all $L^q$ norms are preserved.
  This reduces the sharp Sobolev, Moser–Trudinger, and Faber–Krahn problems
  to radial functions. For $1<p<\infty$, equality forces $u$ to be a
  translate of $u^*$ provided
  $|\{\nabla u^*=0,\ 0<u^*<\mathop{\mathrm{ess\,sup}}u\}|=0$ (Brothers–Ziemer).
* **20. Cheeger's inequality.** For the Dirichlet Cheeger constant
  $h(\Omega)=\inf_{E\Subset\Omega}P(E)/|E|$, with positive-volume finite-perimeter
  competitors, $\lambda_1(\Omega)\geq h(\Omega)^2/4$.
  On a closed manifold the analogous constant uses
  $P(E)/\min(|E|,|M\setminus E|)$ and bounds the first nonzero eigenvalue.
* **21. Faber–Krahn inequality.** A ball minimizes the first Dirichlet
  eigenvalue among open sets of fixed finite volume, uniquely up to sets of
  zero capacity. The second eigenvalue is minimized by the disjoint union of
  two equal balls (Krahn–Szegő).
* **22. Szegő–Weinberger inequality.** A ball maximizes the first nonzero
  Neumann eigenvalue among bounded connected Lipschitz domains of fixed
  volume. Thus Dirichlet and Neumann shape inequalities have opposite directions.
* **23. Saint-Venant inequality.** The torsional rigidity
  $\mathcal T(\Omega)=\int_\Omega u$, where $-\Delta u=1$ and
  $u\in H_0^1(\Omega)$, is maximized by the ball at fixed volume.
* **24. Quantitative isoperimetry.** For $n\geq2$ and finite positive-volume
  finite-perimeter $E$,
  $$\frac{P(E)}{n\omega_n^{1/n}|E|^{(n-1)/n}}-1
    \geq c_n\mathcal A(E)^2,$$
  where $\mathcal A(E)=\inf_{|B|=|E|}|E\triangle B|/|E|$ over balls
  (Fusco–Maggi–Pratelli). The quadratic asymmetry scale is sharp.
* **25. Relative isoperimetry.** For $n\geq2$, on a ball $B_r$,
  $\min(|E\cap B_r|,|B_r\setminus E|)^{(n-1)/n}
  \leq C_nP(E,B_r)$. Lipschitz-domain versions have constants depending
  on the domain and yield local $BV$ Poincaré inequalities.

## Geometric inequalities for Gaussian, curved, and convex models

* **26. Gaussian isoperimetry.** Standard Gaussian perimeter satisfies
  $P_\gamma(E)\geq\varphi(\Phi^{-1}(\gamma(E)))$.
  Halfspaces attain equality; here $\varphi$ and $\Phi$ are the standard
  normal density and distribution function (Borell, Sudakov–Tsirelson).
  Equivalently $\gamma(E_r)\geq\Phi(\Phi^{-1}(\gamma(E))+r)$ for the
  $r$-neighbourhood, which gives dimension-free Gaussian concentration.
* **27. Lévy–Gromov comparison.** On a closed connected $n$-manifold,
  $n\geq2$, with $\mathop{\mathrm{Ric}}\geq(n-1)g$, the isoperimetric profile
  for normalized volume is at least that of the unit round $n$-sphere with
  normalized volume. Both volume and perimeter are divided by total volume.
* **28. Brunn–Minkowski inequality.**
  $|A+B|^{1/n}\geq|A|^{1/n}+|B|^{1/n}$ for nonempty compact Euclidean sets.
  Convex bodies of positive volume have equality exactly when homothetic.
* **29. Prékopa–Leindler inequality.** Let $f,g,h\geq0$ be measurable on
  $\mathbb R^n$ and $0<t<1$. If
  $h((1-t)x+ty)\geq f(x)^{1-t}g(y)^t$ for all $x,y\in\mathbb R^n$, then
  $\int h\geq(\int f)^{1-t}(\int g)^t$.
  This is a functional strengthening of Brunn–Minkowski.
* **30. Brascamp–Lieb variance inequality.** If
  $d\mu=Z^{-1}e^{-V}dx$ with $V\in C^2$ and positive definite Hessian, then
  $$\mathop{\mathrm{Var}}\nolimits_\mu f\leq
    \int\langle(D^2V)^{-1}\nabla f,\nabla f\rangle\,d\mu.$$
  An infinite right side is permitted; uniform convexity yields Poincaré.
* **31. Geometric Brascamp–Lieb inequality.** If $B_iB_i^*=I$ and
  $\sum_i c_iB_i^*B_i=I$, $c_i>0$, then
  $\int\prod_i f_i(B_ix)^{c_i}dx\leq\prod_i(\int f_i)^{c_i}$.
  Compatible Gaussian functions show the constant is one.
* **32. Loomis–Whitney inequality.** For Borel $E\subseteq\mathbb R^n$,
  $n\geq2$, $|E|^{n-1}\leq\prod_i|\pi_iE|$, with $\pi_i$ the coordinate
  hyperplane projections. This is a geometric Brascamp–Lieb instance.

## Mixed volumes and convex-body inequalities

Let $\mathcal K^n$ be the nonempty compact convex subsets of $\mathbb R^n$, with
the Hausdorff metric
$\delta(K,L)=\min\{\varepsilon\geq0:K\subseteq L+\varepsilon B,\ L\subseteq K+\varepsilon B\}$,
where $B$ is the closed unit ball; a **convex body** is an element of
$\mathcal K^n$ with nonempty interior. The support function
$h_K(u)=\max_{x\in K}\langle x,u\rangle$ satisfies $h_{K+L}=h_K+h_L$. For
$0\in\mathop{\mathrm{int}}K$ the **polar body** is
$K^\circ=\{y:\langle x,y\rangle\leq1\ (x\in K)\}$. A **star body** is a compact
set, star-shaped about $0$, whose radial function
$\rho_K(u)=\max\{t\geq0:tu\in K\}$ is positive and continuous on $S^{n-1}$;
its gauge is $\|x\|_K=|x|/\rho_K(x/|x|)$.

* **74. Blaschke selection theorem.** Every sequence in $\mathcal K^n$
  contained in a fixed ball has a subsequence converging in the Hausdorff
  metric to an element of $\mathcal K^n$. Volume is continuous on
  $\mathcal K^n$, so continuous functionals attain their extrema on bounded
  Hausdorff-closed families; this is the compactness behind extremal bodies.
* **75. Minkowski's mixed-volume theorem.** For $K_1,\dots,K_m\in\mathcal K^n$
  and $\lambda_i\geq0$,
  $$|\lambda_1K_1+\cdots+\lambda_mK_m|=\sum_{i_1,\dots,i_n=1}^m
    \lambda_{i_1}\cdots\lambda_{i_n}V(K_{i_1},\dots,K_{i_n}),$$
  where the **mixed volumes** $V$ are uniquely determined by requiring symmetry
  in their arguments. They are nonnegative, Minkowski additive and positively
  homogeneous in each argument, translation invariant, monotone under
  inclusion, continuous, and $V(K,\dots,K)=|K|$; $V(K_1,\dots,K_n)>0$ exactly
  when there are segments $S_i\subseteq K_i$ with linearly independent
  directions. Write $V(K[j],L[n-j])$ for $K$ repeated $j$ times. For a
  convex body $K$, $V(K[n-1],L)=\frac1n\int_{S^{n-1}}h_L\,dS_K$, where the
  **surface area measure** $S_K(\omega)$ is the $(n-1)$-dimensional Hausdorff
  measure of the boundary points of $K$ having an outer unit normal in $\omega$.
* **76. Steiner formula and Hadwiger's theorem.** For $K\in\mathcal K^n$ and
  $t\geq0$, with $\omega_0=1$,
  $$|K+tB|=\sum_{j=0}^n\omega_{n-j}V_j(K)t^{n-j},\qquad
    V_j(K)=\binom nj\frac{V(K[j],B[n-j])}{\omega_{n-j}}.$$
  The **intrinsic volumes** $V_j$ do not depend on the ambient dimension:
  $V_n$ is volume, $2V_{n-1}$ is surface area of a convex body, $V_1$ is a
  multiple of mean width, and $V_0=1$. Every Hausdorff-continuous,
  rigid-motion-invariant valuation on $\mathcal K^n$ (that is,
  $\phi(K\cup L)+\phi(K\cap L)=\phi(K)+\phi(L)$ whenever $K\cup L$ is convex)
  is a linear combination of $V_0,\dots,V_n$ (Hadwiger).
* **77. Cauchy–Kubota formulas.** For $K\in\mathcal K^n$ and $1\leq j\leq n-1$,
  $$V_j(K)=\binom nj\frac{\omega_n}{\omega_j\omega_{n-j}}
    \int_{G(n,j)}V_j(K|E)\,d\nu_j(E),$$
  where $K|E$ is the orthogonal projection and $\nu_j$ the rotation-invariant
  probability on the Grassmannian. For $j=n-1$ this is Cauchy's surface area
  formula $S(K)=\omega_{n-1}^{-1}\int_{S^{n-1}}|K|u^\perp|\,du$ for a convex
  body $K$, with $du$ the surface measure on the sphere.
* **78. Minkowski's first inequality.** For convex bodies $K,L$,
  $V(K[n-1],L)^n\geq|K|^{n-1}|L|$, with equality exactly when $K$ and $L$ are
  homothetic. For convex bodies it is equivalent to the Brunn–Minkowski
  inequality (result 28); $L=B$ gives the isoperimetric inequality, since
  $S(K)=nV(K[n-1],B)$.
* **79. Alexandrov–Fenchel inequality.** For $K_1,\dots,K_n\in\mathcal K^n$,
  $$V(K_1,K_2,K_3,\dots,K_n)^2\geq
    V(K_1,K_1,K_3,\dots,K_n)\,V(K_2,K_2,K_3,\dots,K_n).$$
  Consequently $j\mapsto V(K[j],L[n-j])$ is log-concave, Minkowski's quadratic
  inequality $V(K[n-1],L)^2\geq|K|\,V(K[n-2],L[2])$ holds, and
  $V(K_1,\dots,K_n)^n\geq|K_1|\cdots|K_n|$. With $L=B$ this yields the
  isoperimetric-type inequalities between intrinsic volumes. The equality
  cases are characterized only in special classes.
* **80. Minkowski existence and uniqueness theorem.** A finite Borel measure
  $\mu$ on $S^{n-1}$ is the surface area measure of a convex body exactly when
  it is not concentrated on a great subsphere and $\int u\,d\mu(u)=0$. The
  body is unique up to translation, by the equality case in result 78. For
  $d\mu=f\,du$ with smooth positive $f$, the problem is the Monge–Ampère
  equation $\det(\nabla^2h+hI)=f$ for the support function on the sphere.
* **81. Blaschke–Santaló inequality.** For an origin-symmetric convex body
  $K$, $|K|\,|K^\circ|\leq\omega_n^2$, with equality exactly for ellipsoids.
  Every convex body has a unique interior point $s$ minimizing
  $|(K-x)^\circ|$, and the same bound holds for $K-s$. In the reverse
  direction $|K|\,|K^\circ|\geq c^n\omega_n^2$ for origin-symmetric $K$ with
  an absolute $c>0$ (Bourgain–Milman). Mahler's conjecture that the cube is
  extremal, with value $4^n/n!$, is proved only for $n\leq3$.
* **82. Rogers–Shephard inequality.** For a convex body $K$,
  $2^n|K|\leq|K-K|\leq\binom{2n}n|K|$. Equality holds on the left exactly for
  centrally symmetric $K$, by result 28, and on the right exactly for
  simplices. The ratio $|K-K|/|K|$ is thus an affine-invariant measure of
  asymmetry.
* **83. Intersection bodies and the Busemann–Petty problem.** The
  intersection body $IL$ of an origin-symmetric star body $L$ has radial
  function $\rho_{IL}(u)=|L\cap u^\perp|_{n-1}$; the class of intersection
  bodies is the closure of these in the radial metric. If $L$ is convex, so
  is $IL$ (Busemann). If $K$ is an intersection body, $L$ an origin-symmetric
  star body, and $|K\cap u^\perp|\leq|L\cap u^\perp|$ for all $u\in S^{n-1}$,
  then $|K|\leq|L|$ (Lutwak). For origin-symmetric convex bodies, smaller
  central hyperplane sections force smaller volume exactly when $n\leq4$
  (Busemann–Petty problem; Gardner, Koldobsky, Zhang). With the Fourier
  transform $\widehat f(\xi)=\int e^{-ix\cdot\xi}f(x)\,dx$ on distributions,
  $|K\cap\xi^\perp|=\frac1{\pi(n-1)}(\|x\|_K^{-n+1})^\wedge(\xi)$ for unit
  $\xi$, and an origin-symmetric star body $K$ is an intersection body exactly
  when $\|x\|_K^{-1}$ is a positive definite distribution (Koldobsky).

## Functional inequalities and symmetric Markov semigroups

Let $(P_t)$ be a conservative symmetric Markov semigroup with generator $L$
and invariant measure $\mu$. A **Dirichlet form** is its closed energy
$\mathcal E(f,f)=-\langle f,Lf\rangle$. In diffusion settings
$\Gamma(f,g)=\frac12(L(fg)-fLg-gLf)$ and $\Gamma(f)=\Gamma(f,f)$.
Identities are first read on a smooth core and extended by closure;
probability is assumed when variance or normalized entropy is used.

* **33. Variance identity.**
  $\frac{d}{dt}\mathop{\mathrm{Var}}_\mu(P_tf)=-2\mathcal E(P_tf,P_tf)$.
  For an ergodic semigroup,
  $\mathop{\mathrm{Var}}_\mu f=2\int_0^\infty\mathcal E(P_tf,P_tf)dt$.
* **34. Spectral gap and decay.** Poincaré with constant $C_P$ is equivalent
  to $\|P_tf-\mu(f)\|_2\leq e^{-t/C_P}\|f-\mu(f)\|_2$.
  The bottom of the nonzero spectrum of $-L$ is at least $1/C_P$.
* **35. Entropy dissipation.** For a diffusion semigroup and a positive
  probability density $h$,
  $$\frac{d}{dt}\mathop{\mathrm{Ent}}\nolimits_\mu(P_th)
    =-I_\mu(P_th),\qquad
    I_\mu(h)=\int\frac{\Gamma(h)}h\,d\mu.$$
  For a general symmetric Markov semigroup the dissipation is
  $\mathcal E(P_th,\log P_th)$ instead.
  Logarithmic Sobolev with constant $C_{LS}$ gives entropy decay
  $\mathop{\mathrm{Ent}}_\mu(P_th)\leq e^{-2t/C_{LS}}\mathop{\mathrm{Ent}}_\mu(h)$.
* **36. Gross hypercontractivity theorem.** Logarithmic Sobolev with constant
  $C_{LS}$ is equivalent, for diffusion semigroups, to
  $\|P_tf\|_{q(t)}\leq\|f\|_p$, where
  $q(t)-1=(p-1)e^{2t/C_{LS}}$, $p>1$. The Ornstein–Uhlenbeck semigroup is
  the model case, with $C_{LS}=1$.
* **37. Tensorization.** Poincaré and logarithmic Sobolev inequalities
  tensorize over product measures, with constant the largest coordinate constant
  for the sum energy. This is their principal source of dimension independence.
* **38. Holley–Stroock perturbation.** Reweighting by $d\nu=e^\psi d\mu/Z$
  with bounded oscillation $\sup\psi-\inf\psi$ multiplies a Poincaré or
  logarithmic Sobolev constant by at most $e^{\mathop{\mathrm{osc}}\psi}$.
* **40. Nash inequality.** On $\mathbb R^n$,
  $\|f\|_2^{2+4/n}\leq C_n\|\nabla f\|_2^2\|f\|_1^{4/n}$.
  This interpolates mass, energy, and square-integrability.
* **43. Weak Poincaré and polynomial decay.** If bounded functions satisfy
  $\mathop{\mathrm{Var}}_\mu f\leq Cs^{-\alpha}\mathcal E(f,f)
  +s\mathop{\mathrm{Osc}}(f)^2$ for every $s>0$, $\alpha>0$, then
  $\mathop{\mathrm{Var}}_\mu(P_tf)\leq C'(1+t)^{-1/\alpha}
  \mathop{\mathrm{Osc}}(f)^2$. Optimizing the defect replaces a spectral gap
  by slower convergence to equilibrium.
* **44. Rothaus tightening.**
  $\mathop{\mathrm{Ent}}(f^2)\leq\mathop{\mathrm{Ent}}((f-\mu f)^2)
  +2\mathop{\mathrm{Var}}(f)$. Thus a defective bound
  $\mathop{\mathrm{Ent}}(f^2)\leq a\mathcal E(f,f)+b\|f\|_2^2$, $a,b\geq0$, combined
  with Poincaré, gives
  $\mathop{\mathrm{Ent}}(f^2)\leq[a+(b+2)C_P]\mathcal E(f,f)$.
* **65. Linearization of logarithmic Sobolev.** A probability logarithmic
  Sobolev inequality with constant $C_{LS}$ implies Poincaré with
  $C_P\leq C_{LS}$. Substituting $1+\varepsilon f$ and expanding to second
  order identifies the variance as the quadratic part of entropy. The converse
  fails in general, so exponential $L^2$ decay alone need not give hypercontractivity.
* **66. Variational formula for entropy.** For probabilities on a Polish space
  and the relative entropy $H$ defined before result 55,
  $$H(\nu\mid\mu)=\sup_g\left\{\int g\,d\nu-
      \log\int e^g d\mu\right\},$$
  where bounded measurable $g$ suffice, and bounded continuous $g$ also suffice.
  This formula links exponential integrability to transport and concentration;
  it remains valid when the entropy is infinite.

## Curvature–dimension calculus and Riemannian comparison

On a complete connected Riemannian manifold with smooth weight,
$L=\Delta-\nabla V\cdot\nabla$ is symmetric for $e^{-V}d\mathrm{vol}$.
Assume conservativity when using its semigroup. Set
$\Gamma_2(f)=\frac12L\Gamma(f)-\Gamma(f,Lf)$.
The **curvature–dimension condition** $CD(\kappa,N)$ is
$\Gamma_2(f)\geq\kappa\Gamma(f)+(Lf)^2/N$; the last term is zero for
$N=\infty$. Global probability inequalities below use normalized invariant mass.

* **45. Bochner identity.**
  $$\Gamma_2(f)=\|\nabla^2f\|^2+
    (\mathop{\mathrm{Ric}}+\nabla^2V)(\nabla f,\nabla f).$$
  Thus a lower bound on weighted Ricci curvature is $CD(\kappa,\infty)$;
  the unweighted $n$-dimensional Laplacian has the additional dimension term.
* **46. Gradient estimate.** $CD(\kappa,\infty)$ is equivalent, in the
  smooth diffusion framework, to
  $\Gamma(P_tf)\leq e^{-2\kappa t}P_t\Gamma(f)$. For a symmetric
  conservative diffusion generator this uses the usual diffusion calculus and
  closure hypotheses; the implication from the gradient bound back to
  $CD(\kappa,\infty)$ follows by differentiating at $t=0$ on a core.
* **47. Curvature implies Poincaré.** For $\kappa>0$,
  $CD(\kappa,\infty)$ gives $C_P\leq1/\kappa$. Standard Gaussian measure
  has $\kappa=1$ and attains this constant on affine functions.
* **48. Bakry–Émery logarithmic Sobolev inequality.** Under the same positive
  curvature assumption, $C_{LS}\leq1/\kappa$. For $V(x)=|x|^2/2$ this is
  the sharp Gaussian logarithmic Sobolev inequality. Explicitly: if
  $d\mu=e^{-V}dx$ on $\mathbb R^n$ with $V$ smooth and
  $\nabla^2V\geq\kappa I$, $\kappa>0$, then $\mu$ satisfies the logarithmic
  Sobolev inequality, hence the Poincaré inequality, with constant $1/\kappa$.
* **49. Lichnerowicz bound.** Under $CD(\kappa,N)$, $\kappa>0$, $N>1$,
  the spectral gap is at least $\kappa N/(N-1)$ in the corresponding
  ergodic probability setting. In particular, a closed $n$-manifold with
  $\mathop{\mathrm{Ric}}\geq(n-1)Kg$, $K>0$, has $\lambda_1\geq nK$; equality
  holds only for the round sphere (Obata).
* **67. Cheng eigenvalue comparison.** On a complete $n$-manifold with
  nonnegative Ricci curvature, the first Dirichlet eigenvalue of a geodesic
  ball of radius $r$ is at most that of the Euclidean radius-$r$ ball:
  $\lambda_1(B(x,r))\leq j_{n/2-1,1}^2/r^2$, where $j_{\nu,1}$ is the
  first positive zero of $J_\nu$. The eigenvalue is understood variationally
  even when the geodesic sphere is not smooth.
* **68. Buser's converse to Cheeger.** For a closed connected $n$-manifold,
  $n\geq2$, with $\mathop{\mathrm{Ric}}\geq-(n-1)k^2g$, $k\geq0$,
  $\lambda_1\leq C_n(kh+h^2)$ for the closed-manifold Cheeger constant.
  Together with Cheeger's lower bound, this compares spectral and isoperimetric
  gaps under a curvature lower bound.

## Transport, entropy, and sharp model inequalities

The **Wasserstein distance** $W_p$ is the infimum of
$(\int d(x,y)^p\,d\pi)^{1/p}$ over couplings. Relative entropy is
$H(\nu\mid\mu)=\int\log(d\nu/d\mu)d\nu$ when absolutely continuous,
and infinity otherwise. In Euclidean space,
$I(\nu\mid\mu)=\int|\nabla\log(d\nu/d\mu)|^2d\nu$.
For a probability with density $p$ on $\mathbb R^n$, relative entropy compares
it with a specified reference measure; the Euclidean integral
$\int p\log p\,dx$ instead uses Lebesgue reference, which has infinite mass.
The two expressions have different transformation laws under dilations.

* **55. Gaussian Talagrand inequality.**
  $W_2(\nu,\gamma_n)^2\leq2H(\nu\mid\gamma_n)$ for every probability
  $\nu$, with extended values allowed (Talagrand). Such transport
  inequalities tensorize and imply Gaussian concentration (Marton's argument).
* **56. HWI inequality.** For $\mu=Z^{-1}e^{-V}dx$ with
  $D^2V\geq\kappa I$ and finite second moment, and sufficiently regular probabilities with finite
  second moment and Fisher information,
  $$H(\nu\mid\mu)\leq W_2(\nu,\mu)\sqrt{I(\nu\mid\mu)}
      -\frac\kappa2W_2(\nu,\mu)^2.$$
* **57. Otto–Villani implication.** Logarithmic Sobolev with constant
  $C_{LS}$ for a smooth probability on a complete Riemannian manifold implies
  $W_2(\nu,\mu)^2\leq2C_{LS}H(\nu\mid\mu)$.
* **58. Bobkov–Götze equivalence.** On a Polish metric space with finite
  first moment, $W_1(\nu,\mu)^2\leq2C H(\nu\mid\mu)$ is equivalent to
  $\int e^{\lambda(f-\mu f)}d\mu\leq e^{C\lambda^2/2}$ for every
  1-Lipschitz $f$ and real $\lambda$.
* **59. Wasserstein contraction.** For the conservative Langevin diffusion
  generated by $\Delta-\nabla V\cdot\nabla$ with $D^2V\geq\kappa I$,
  $W_2(P_t^*\nu,P_t^*\eta)\leq e^{-\kappa t}W_2(\nu,\eta)$.
* **60. Displacement convexity.** Under that Hessian bound, relative entropy
  is $\kappa$-convex along Euclidean $W_2$ geodesics:
  $$H(\nu_t\mid\mu)\leq(1-t)H(\nu_0\mid\mu)+tH(\nu_1\mid\mu)
     -\frac\kappa2t(1-t)W_2(\nu_0,\nu_1)^2.$$
  Finite-entropy, finite-second-moment endpoints give the standard formulation.
* **61. Gaussian Beckner inequalities.** For $1\leq p<2$,
  $$\|f\|_{L^2(\gamma_n)}^2-\|f\|_{L^p(\gamma_n)}^2
    \leq(2-p)\int|\nabla f|^2d\gamma_n.$$
  Dividing by $2-p$ and letting $p\uparrow2$ gives the Gaussian logarithmic
  Sobolev inequality;
  the $p=1$ bound is a variance-type endpoint.
* **62. Sharp sphere Sobolev inequality.** On the unit $n$-sphere, $n\geq3$,
  with normalized volume,
  $$\|f\|_{2n/(n-2)}^2\leq\|f\|_2^2+
        \frac4{n(n-2)}\|\nabla f\|_2^2.$$
  The coefficient is sharp; conformal factors give its extremizers.
* **63. Aubin's local-to-global sharp bound.** On a closed connected $n$-manifold,
  $n\geq3$, for every $\varepsilon>0$ there is $C_\varepsilon$ with
  $$\|u\|_{2^*}^2\leq(S_n^2+\varepsilon)\|\nabla u\|_2^2
      +C_\varepsilon\|u\|_2^2.$$
  The leading constant cannot be smaller than the Euclidean one. For the
  conformal Laplacian, minimization of the corresponding Sobolev quotient is
  the Yamabe problem; every smooth closed conformal class in dimension at
  least three has a smooth positive minimizer and hence a constant-scalar-curvature
  representative (Yamabe, Trudinger, Aubin, Schoen). Loss of compactness at
  the critical exponent is the central difficulty.
* **64. Sharp Euclidean logarithmic Sobolev inequality.** If $\|f\|_2=1$,
  $f\in H^1(\mathbb R^n)$, then
  $$\int f^2\log f^2dx\leq\frac n2\log\left(
      \frac2{\pi e n}\int|\nabla f|^2dx\right).$$
  The positive part is controlled by the inequality; a negative-infinite
  integral is allowed. Gaussian functions attain equality. This scale-invariant
  Lebesgue formulation differs from the normalized Gaussian-measure inequality.

## Further equivalences, stability, and spectral consequences

In the spectral statements below Dirichlet eigenvalues are ordered increasingly.

* **69. Isoperimetry and endpoint Sobolev.** On a Riemannian manifold, a
  bound $P(E)\geq c|E|^{1-1/d}$, $d>1$, for all precompact finite-perimeter
  sets is equivalent to
  $\|u\|_{d/(d-1)}\leq c^{-1}\int|\nabla u|$ for compactly supported
  functions. Coarea and the integral triangle inequality give one direction;
  smooth approximation of indicators gives the other. Thus perimeter profiles
  can determine Sobolev exponents without an ambient Euclidean structure.
* **70. Bianchi–Egnell stability.** For $n\geq3$ and the sharp constant $S_n$,
  $$\|\nabla u\|_2^2-S_n^{-2}\|u\|_{2^*}^2
    \geq c_n\inf_{v\in\mathcal M}\|\nabla(u-v)\|_2^2,$$
  where $\mathcal M$ is the family of scalar multiples, translations, and
  dilations of the Sobolev optimizer, including zero.
* **71. Ashbaugh–Benguria ratio inequality.** For a bounded Euclidean
  domain in dimension $n\geq2$,
  $\lambda_2(\Omega)/\lambda_1(\Omega)
  \leq\lambda_2(B)/\lambda_1(B)$, the Payne–Pólya–Weinberger conjecture.
  Balls maximize this scale-invariant Dirichlet eigenvalue ratio.
* **72. Berezin–Li–Yau eigenvalue sum.** For bounded open
  $\Omega\subseteq\mathbb R^n$ and $k\geq1$,
  $$\sum_{j=1}^k\lambda_j(\Omega)\geq
    \frac n{n+2}(2\pi)^2(\omega_n|\Omega|)^{-2/n}k^{1+2/n}.$$
  The leading coefficient agrees with the integrated Weyl asymptotic, and no
  boundary regularity is needed.

## Reference guide

Maz'ya, *Sobolev Spaces*, especially the chapters on boundary-vanishing
functions, capacities, and embeddings, supplies the Euclidean and capacitary
spine. Aubin and Hebey develop sharp constants and the manifold endpoint;
Ghoussoub–Moradifam develops Hardy, Rellich, and Caffarelli–Kohn–Nirenberg
inequalities, and Baernstein and Lieb–Loss give the rearrangement
(Pólya–Szegő, Riesz) route to sharp constants. Chavel,
Burago–Zalgaller, Maggi, and Henrot connect perimeter, comparison geometry,
and spectral optimization. The quantitative isoperimetric statement is the
standard stability theorem surveyed in the Maggi/Fusco strand of the bibliography.

Bakry–Gentil–Ledoux, Chapters 4–6, develops Poincaré, logarithmic Sobolev,
Sobolev, and curvature–dimension inequalities; Chapters 7–9 gives the weak,
capacitary, isoperimetric, and transport connections. Saloff-Coste and
Grigor'yan develop the heat-kernel side, including the equivalence of
doubling plus Poincaré with parabolic Harnack and Gaussian bounds. Villani and Ledoux give independent
transport and concentration treatments; Gaussian sharp results also belong to
Bogachev's Gaussian-measure framework.

Burago–Zalgaller and Schneider's *Convex Bodies* (listed in Section 12)
develop mixed volumes, the Steiner and Kubota formulas, the Minkowski problem,
the Alexandrov–Fenchel, Blaschke–Santaló, and Rogers–Shephard inequalities;
Koldobsky and Gardner's *Geometric Tomography* (listed in Section 37) treat
intersection bodies and the Busemann–Petty problem, and Toth treats measures of
symmetry such as the Rogers–Shephard ratio.

The final spectral bounds recur in Henrot and the shape-optimization
literature; curvature comparisons in Chavel and the heat-kernel references.
Sobolev stability belongs to the quantitative-inequality strand, and the
negative-eigenvalue bounds are treated in Lieb–Seiringer and
Frank–Laptev–Weidl, cross-referenced from the spectral-theory sections.

Local source anchors:

- [Maz'ya, *Sobolev Spaces*](References/Mazya2011SobolevSpacesApplicationsEllipticPDE-SpringerGL342.pdf).
- [Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion Operators*](References/BakryGentilLedoux2014AnalysisGeometryMarkovDiffusionOperators-SpringerGL348.pdf).
- [Villani, *Optimal Transport: Old and New*](References/Villani2009OptimalTransportOldNew-SpringerGL338.pdf).
- [Burago–Zalgaller, *Geometric Inequalities*](References/BuragoZagaller1988GeometricInequalities-SpringerGL285.pdf).
- [Schneider, *Convex Bodies: The Brunn–Minkowski Theory*](References/Schneider1993ConvexBodiesBrunnMinkowskiTheory-CambridgeEMA44.pdf) and [Gardner, *Geometric Tomography*](References/Gardner2006GeometricTomography2ndEd-CambridgeEMA58.pdf), supplementary local sources for mixed volumes and sections.
- [Pólya–Szegő, *Isoperimetric Inequalities in Mathematical Physics*](References/PolyaSzegö1951rep2016IsoperimetricInequalitiesMathematicalPhysics-PrincetonAnnalsMathStud27.pdf).
- [Chavel, *Riemannian Geometry*](References/Chavel2006RiemannianGeometryModernIntroduction2ndEd-CambridgeStudiesAM98.pdf), a supplementary local source for the comparison geometry.
- [Frank–Laptev–Weidl, *Schrödinger Operators: Eigenvalues and Lieb–Thirring Inequalities*](References/FrankLaptevWeidl2023SchrodingerOperatorsEigenvaluesLiebThirringInequalities-Cambridge.StudAM200.pdf), for the negative-eigenvalue bounds.
