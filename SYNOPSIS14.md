# Synopsis: Functional, isoperimetric, and geometric inequalities

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects the recurring graduate and beginning research core of
Section 14 of [CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md).
Its subject is the interaction of norm inequalities, perimeter and capacity,
spectral gaps, heat propagation, curvature, and transport. Classical statements
also appearing in Section 11 are retained where they anchor a different set
of connections. Euclidean results are separated from probability and
Riemannian formulations so that their constants and normalizations remain visible.

Write $\omega_n=|B_1(0)|$, $p^*=np/(n-p)$ for $p<n$, and
$\mathcal E(f,f)=\int\Gamma(f)\,d\mu$ for a Dirichlet energy. A probability
measure satisfies **Poincaré with constant $C_P$** if
$\operatorname{Var}_\mu f\leq C_P\mathcal E(f,f)$, and **logarithmic Sobolev
with constant $C_{LS}$** if
$\operatorname{Ent}_\mu(f^2)\leq2C_{LS}\mathcal E(f,f)$.
Here $\operatorname{Ent}_\mu h=\int h\log(h/\int h\,d\mu)d\mu$.
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

* **1. Endpoint Sobolev and isoperimetry.** For compactly supported smooth
  functions in dimension $n\geq2$,
  $$\|u\|_{n/(n-1)}\leq\frac1{n\omega_n^{1/n}}\|\nabla u\|_1.$$
  The extension to $BV$ is equivalent by coarea to
  $P(E)\geq n\omega_n^{1/n}|E|^{(n-1)/n}$.
* **2. Sobolev inequality.** For $1<p<n$,
  $\|u\|_{p^*}\leq S_{n,p}\|\nabla u\|_p$ on $C_c^\infty(\mathbb R^n)$
  and its homogeneous completion. The exponent is forced by scaling.
* **3. Sharp quadratic Sobolev inequality.** For $n\geq3$, the best constant
  $S_n=S_{n,2}$ is attained in the homogeneous space by
  $U(x)=(1+|x|^2)^{-(n-2)/2}$. Thus
  $S_n=\|U\|_{2^*}/\|\nabla U\|_2$; all nonzero real extremizers are its
  scalar multiples, translations, and dilations (Aubin–Talenti theorem).
* **4. Gagliardo–Nirenberg interpolation.** For $1\leq p<n$,
  $1\leq r\leq q\leq p^*$, and
  $1/q=\theta(1/p-1/n)+(1-\theta)/r$,
  $$\|u\|_q\leq C\|\nabla u\|_p^\theta\|u\|_r^{1-\theta}.$$
  Higher-derivative versions extend this interpolation between smoothness and
  integrability under their corresponding scaling restrictions.
* **5. Poincaré inequality on domains.** On a bounded connected Lipschitz
  domain, $\|u-u_\Omega\|_p\leq C\|\nabla u\|_p$ for $1\leq p<\infty$.
  Zero boundary values give $\|u\|_p\leq C\|\nabla u\|_p$ without subtracting
  the mean. Connectedness is essential for the mean-subtracted assertion.
* **6. Payne–Weinberger diameter bound.** On a bounded convex domain of
  diameter $D$, mean-zero $u\in H^1$ satisfies
  $\int|\nabla u|^2\geq\pi^2D^{-2}\int|u|^2$. The constant is sharp
  across convex domains.
* **7. Morrey inequality.** For $p>n$, $u\in W^{1,p}$ on a bounded Lipschitz
  domain has a representative Hölder continuous with exponent $1-n/p$ and
  controlled Hölder norm. For compactly supported functions on $\mathbb R^n$,
  the Hölder seminorm is bounded by $C\|\nabla u\|_p$.
* **8. Moser–Trudinger inequality.** If $n\geq2$, $|\Omega|<\infty$, and
  $u\in W_0^{1,n}(\Omega)$ with $\|\nabla u\|_n\leq1$, then
  $$\int_\Omega\exp(\alpha_n|u|^{n/(n-1)})dx\leq C_n|\Omega|,
    \qquad\alpha_n=n|S^{n-1}|^{1/(n-1)}.$$
  Increasing $\alpha_n$ makes the uniform bound false.
* **9. Hardy inequality.** For $1<p<n$,
  $\int|\nabla u|^p\geq((n-p)/p)^p\int|u|^p/|x|^p$ on
  $C_c^\infty(\mathbb R^n)$. The scale-invariant constant is optimal.
* **10. Rellich inequality.** For $n\geq5$ and
  $u\in C_c^\infty(\mathbb R^n\setminus\{0\})$,
  $$\int|\Delta u|^2dx\geq\left(\frac{n(n-4)}4\right)^2
    \int\frac{|u|^2}{|x|^4}dx.$$
  The constant is optimal.
* **11. Boundary Hardy inequality.** For a proper convex open set,
  $\int_\Omega|\nabla u|^2\geq\frac14\int_\Omega
  |u|^2/\operatorname{dist}(x,\partial\Omega)^2$ for $u\in C_c^\infty(\Omega)$.
  The coefficient $1/4$ is sharp in the standard smooth-boundary cases.
* **12. Hardy–Littlewood–Sobolev inequality.** If $0<\lambda<n$ and
  $1/p+1/q+\lambda/n=2$ with $p,q>1$, then
  $\iint |f(x)g(y)|/|x-y|^\lambda\,dxdy\leq C\|f\|_p\|g\|_q$.
* **13. Fractional Sobolev inequality.** For $0<s<n/2$,
  $\|u\|_{2n/(n-2s)}\leq C\|(-\Delta)^{s/2}u\|_2$ on the homogeneous
  fractional Sobolev space. This is a Riesz-potential form of result 12.
* **14. Sobolev trace inequality.** For $1<p<n$ on the half-space,
  $$\|u(\cdot,0)\|_{L^{p(n-1)/(n-p)}(\mathbb R^{n-1})}
    \leq C\|\nabla u\|_{L^p(\mathbb R_+^n)}$$
  for smooth functions compactly supported up to the boundary.

## Capacity, perimeter, and spectral optimization

For compact $K\subset\Omega$, the relative **$p$-capacity** is
$\operatorname{cap}_p(K,\Omega)=\inf\int_\Omega|\nabla v|^p$, over
$v\in C_c^\infty(\Omega)$ at least one near $K$.
Perimeter is the total variation of the distributional gradient of an indicator;
it is meaningful for nonsmooth sets. The first Dirichlet eigenvalue is the
infimum of $\int|\nabla u|^2/\int u^2$ over nonzero $H_0^1(\Omega)$.

* **15. Maz'ya capacitary criterion.** For a positive Radon measure $\nu$,
  $1<p\leq q<\infty$, the inequality
  $\|u\|_{L^q(\nu)}\leq C\|\nabla u\|_{L^p(\Omega)}$ on $C_c^\infty(\Omega)$
  holds exactly when
  $$\nu(K)^{p/q}\leq C'\operatorname{cap}_p(K,\Omega)$$
  for every compact $K\subset\Omega$. The optimal constants are comparable
  after the appropriate $p$th power, with factors depending on the exponents.
* **16. Strong capacitary inequality.** For $1<p<\infty$ and smooth compactly
  supported $u$,
  $$\int_0^\infty\operatorname{cap}_p(\{|u|\geq t\},\Omega)\,d(t^p)
    \leq C_p\int_\Omega|\nabla u|^pdx.$$
  This is stronger than estimating each individual superlevel capacity.
* **17. Isocapacitary inequality.** For $1<p<n$, among compact sets of fixed
  positive volume in $\mathbb R^n$, the ball minimizes homogeneous $p$-capacity.
  The comparison has the scale $|K|^{(n-p)/n}$.
* **18. Cheeger's inequality.** For the Dirichlet Cheeger constant
  $h(\Omega)=\inf_{E\Subset\Omega}P(E)/|E|$, with positive-volume finite-perimeter
  competitors, $\lambda_1(\Omega)\geq h(\Omega)^2/4$.
  On a closed manifold the analogous constant uses
  $P(E)/\min(|E|,|M\setminus E|)$ and bounds the first nonzero eigenvalue.
* **19. Faber–Krahn inequality.** A ball minimizes the first Dirichlet
  eigenvalue among open sets of fixed finite volume.
* **20. Szegő–Weinberger inequality.** A ball maximizes the first nonzero
  Neumann eigenvalue among bounded connected Lipschitz domains of fixed
  volume. Thus Dirichlet and Neumann shape inequalities have opposite directions.
* **21. Saint-Venant inequality.** The torsional rigidity
  $\mathcal T(\Omega)=\int_\Omega u$, where $-\Delta u=1$ and
  $u\in H_0^1(\Omega)$, is maximized by the ball at fixed volume.
* **22. Quantitative isoperimetry.** For $n\geq2$ and finite positive-volume
  finite-perimeter $E$,
  $$\frac{P(E)}{n\omega_n^{1/n}|E|^{(n-1)/n}}-1
    \geq c_n\mathcal A(E)^2,$$
  where $\mathcal A(E)=\inf_{|B|=|E|}|E\triangle B|/|E|$ over balls.
  The quadratic asymmetry scale is sharp.
* **23. Relative isoperimetry.** For $n\geq2$, on a ball $B_r$,
  $\min(|E\cap B_r|,|B_r\setminus E|)^{(n-1)/n}
  \leq C_nP(E,B_r)$. Lipschitz-domain versions have constants depending
  on the domain and yield local $BV$ Poincaré inequalities.

## Geometric inequalities for Gaussian, curved, and convex models

* **24. Gaussian isoperimetry.** Standard Gaussian perimeter satisfies
  $P_\gamma(E)\geq\varphi(\Phi^{-1}(\gamma(E)))$.
  Halfspaces attain equality; here $\varphi$ and $\Phi$ are the standard
  normal density and distribution function.
* **25. Lévy–Gromov comparison.** On a closed connected $n$-manifold,
  $n\geq2$, with $\operatorname{Ric}\geq(n-1)g$, the isoperimetric profile
  for normalized volume is at least that of the unit round $n$-sphere with
  normalized volume. Both volume and perimeter are divided by total volume.
* **26. Brunn–Minkowski inequality.**
  $|A+B|^{1/n}\geq|A|^{1/n}+|B|^{1/n}$ for nonempty compact Euclidean sets.
  Convex bodies of positive volume have equality exactly when homothetic.
* **27. Prékopa–Leindler inequality.** If
  $h((1-t)x+ty)\geq f(x)^{1-t}g(y)^t$, $0<t<1$, then
  $\int h\geq(\int f)^{1-t}(\int g)^t$ for nonnegative integrable functions.
  This is a functional strengthening of Brunn–Minkowski.
* **28. Brascamp–Lieb variance inequality.** If
  $d\mu=Z^{-1}e^{-V}dx$ with $V\in C^2$ and positive definite Hessian, then
  $$\operatorname{Var}_\mu f\leq
    \int\langle(D^2V)^{-1}\nabla f,\nabla f\rangle\,d\mu.$$
  An infinite right side is permitted; uniform convexity yields Poincaré.
* **29. Geometric Brascamp–Lieb inequality.** If $B_iB_i^*=I$ and
  $\sum_i c_iB_i^*B_i=I$, $c_i>0$, then
  $\int\prod_i f_i(B_ix)^{c_i}dx\leq\prod_i(\int f_i)^{c_i}$.
  Compatible Gaussian functions show the constant is one.
* **30. Loomis–Whitney inequality.** For Borel $E\subseteq\mathbb R^n$,
  $n\geq2$, $|E|^{n-1}\leq\prod_i|\pi_iE|$, with $\pi_i$ the coordinate
  hyperplane projections. This is a geometric Brascamp–Lieb instance.

## Functional inequalities and symmetric Markov semigroups

Let $(P_t)$ be a conservative symmetric Markov semigroup with generator $L$
and invariant measure $\mu$. A **Dirichlet form** is its closed energy
$\mathcal E(f,f)=-\langle f,Lf\rangle$. In diffusion settings
$\Gamma(f,g)=\frac12(L(fg)-fLg-gLf)$ and $\Gamma(f)=\Gamma(f,f)$.
Identities are first read on a smooth core and extended by closure;
probability is assumed when variance or normalized entropy is used.

* **31. Variance identity.**
  $\frac{d}{dt}\operatorname{Var}_\mu(P_tf)=-2\mathcal E(P_tf,P_tf)$.
  For an ergodic semigroup,
  $\operatorname{Var}_\mu f=2\int_0^\infty\mathcal E(P_tf,P_tf)dt$.
* **32. Spectral gap and decay.** Poincaré with constant $C_P$ is equivalent
  to $\|P_tf-\mu(f)\|_2\leq e^{-t/C_P}\|f-\mu(f)\|_2$.
  The bottom of the nonzero spectrum of $-L$ is at least $1/C_P$.
* **33. Entropy dissipation.** For a positive probability density $h$,
  $$\frac{d}{dt}\operatorname{Ent}_\mu(P_th)
    =-I_\mu(P_th),\qquad
    I_\mu(h)=\int\frac{\Gamma(h)}h\,d\mu.$$
  Logarithmic Sobolev with constant $C_{LS}$ gives entropy decay
  $\operatorname{Ent}_\mu(P_th)\leq e^{-2t/C_{LS}}\operatorname{Ent}_\mu(h)$.
* **34. Gross hypercontractivity theorem.** Logarithmic Sobolev with constant
  $C_{LS}$ is equivalent, for diffusion semigroups, to
  $\|P_tf\|_{q(t)}\leq\|f\|_p$, where
  $q(t)-1=(p-1)e^{2t/C_{LS}}$, $p>1$.
* **35. Tensorization.** Poincaré and logarithmic Sobolev inequalities
  tensorize over product measures, with constant the largest coordinate constant
  for the sum energy. This is their principal source of dimension independence.
* **36. Holley–Stroock perturbation.** Reweighting by $d\nu=e^\psi d\mu/Z$
  with bounded oscillation $\sup\psi-\inf\psi$ multiplies a Poincaré or
  logarithmic Sobolev constant by at most $e^{\operatorname{osc}\psi}$.
* **37. Herbst concentration.** Logarithmic Sobolev with constant $C_{LS}$
  implies, for $\Gamma(f)\leq L_f^2$,
  $$\int e^{\lambda(f-\mu f)}d\mu\leq
       e^{C_{LS}L_f^2\lambda^2/2}.$$
  Consequently $\mu\{|f-\mu f|\geq t\}\leq2e^{-t^2/(2C_{LS}L_f^2)}$.
* **38. Nash inequality.** On $\mathbb R^n$,
  $\|f\|_2^{2+4/n}\leq C_n\|\nabla f\|_2^2\|f\|_1^{4/n}$.
  This interpolates mass, energy, and square-integrability.
* **39. Nash and heat-kernel bounds.** For symmetric Markov semigroups,
  a global Nash inequality of dimension $d>0$ is equivalent, up to constants,
  to $\|P_t\|_{1\to\infty}\leq Ct^{-d/2}$ for all $t>0$.
  These global forms cannot hold for a conservative probability semigroup
  without an additional large-time term.
* **40. Sobolev–Nash equivalence.** For $d>2$, the global Dirichlet-form
  Sobolev bound $\|f\|_{2d/(d-2)}^2\leq C\mathcal E(f,f)$ is equivalent
  to the dimension-$d$ Nash and ultracontractive bounds in this symmetric
  Markov setting. Constants may change between the formulations.
* **41. Weak Poincaré and polynomial decay.** If bounded functions satisfy
  $\operatorname{Var}_\mu f\leq Cs^{-\alpha}\mathcal E(f,f)
  +s\operatorname{Osc}(f)^2$ for every $s>0$, $\alpha>0$, then
  $\operatorname{Var}_\mu(P_tf)\leq C'(1+t)^{-1/\alpha}
  \operatorname{Osc}(f)^2$. Optimizing the defect replaces a spectral gap
  by slower convergence to equilibrium.
* **42. Rothaus tightening.**
  $\operatorname{Ent}(f^2)\leq\operatorname{Ent}((f-\mu f)^2)
  +2\operatorname{Var}(f)$. Thus a defective bound
  $\operatorname{Ent}(f^2)\leq a\mathcal E(f,f)+b\|f\|_2^2$, $a,b\geq0$, combined
  with Poincaré, gives
  $\operatorname{Ent}(f^2)\leq[a+(b+2)C_P]\mathcal E(f,f)$.

## Curvature–dimension calculus and Riemannian comparison

On a complete connected Riemannian manifold with smooth weight,
$L=\Delta-\nabla V\cdot\nabla$ is symmetric for $e^{-V}d\mathrm{vol}$.
Assume conservativity when using its semigroup. Set
$\Gamma_2(f)=\frac12L\Gamma(f)-\Gamma(f,Lf)$.
The **curvature–dimension condition** $CD(\kappa,N)$ is
$\Gamma_2(f)\geq\kappa\Gamma(f)+(Lf)^2/N$; the last term is zero for
$N=\infty$. Global probability inequalities below use normalized invariant mass.

* **43. Bochner identity.**
  $$\Gamma_2(f)=\|\nabla^2f\|^2+
    (\operatorname{Ric}+\nabla^2V)(\nabla f,\nabla f).$$
  Thus a lower bound on weighted Ricci curvature is $CD(\kappa,\infty)$;
  the unweighted $n$-dimensional Laplacian has the additional dimension term.
* **44. Gradient estimate.** $CD(\kappa,\infty)$ is equivalent, in the
  smooth diffusion framework, to
  $\Gamma(P_tf)\leq e^{-2\kappa t}P_t\Gamma(f)$.
* **45. Curvature implies Poincaré.** For $\kappa>0$,
  $CD(\kappa,\infty)$ gives $C_P\leq1/\kappa$. Standard Gaussian measure
  has $\kappa=1$ and attains this constant on affine functions.
* **46. Bakry–Émery logarithmic Sobolev inequality.** Under the same positive
  curvature assumption, $C_{LS}\leq1/\kappa$. For $V(x)=|x|^2/2$ this is
  the sharp Gaussian logarithmic Sobolev inequality.
* **47. Lichnerowicz bound.** Under $CD(\kappa,N)$, $\kappa>0$, $N>1$,
  the spectral gap is at least $\kappa N/(N-1)$ in the corresponding
  ergodic probability setting. In particular, a closed $n$-manifold with
  $\operatorname{Ric}\geq(n-1)Kg$ has $\lambda_1\geq nK$.
* **48. Li–Yau inequality.** On a complete $n$-manifold with nonnegative Ricci
  curvature, every positive heat solution satisfies
  $|\nabla\log u|^2-\partial_t\log u\leq n/(2t)$.
* **49. Parabolic Harnack consequence.** In the same setting, for $0<s<t$,
  $$u(s,x)\leq u(t,y)(t/s)^{n/2}
       \exp\left(\frac{d(x,y)^2}{4(t-s)}\right).$$
  The coefficients correspond to the generator $\Delta$.
* **50. Bishop–Gromov comparison.** On a complete manifold with
  $\operatorname{Ric}\geq0$, the ratio $\mathrm{vol}(B(x,r))/r^n$ is
  nonincreasing. In particular volume is doubling with factor at most $2^n$.
* **51. Bonnet–Myers bound.** For a complete $n$-manifold, $n\geq2$,
  $\operatorname{Ric}\geq(n-1)Kg$, $K>0$, implies compactness and
  $\operatorname{diam}M\leq\pi/\sqrt K$.

## Transport, entropy, and sharp model inequalities

The **Wasserstein distance** $W_p$ is the infimum of
$(\int d(x,y)^p\,d\pi)^{1/p}$ over couplings. Relative entropy is
$H(\nu\mid\mu)=\int\log(d\nu/d\mu)d\nu$ when absolutely continuous,
and infinity otherwise. In Euclidean space,
$I(\nu\mid\mu)=\int|\nabla\log(d\nu/d\mu)|^2d\nu$.

* **52. Gaussian Talagrand inequality.**
  $W_2(\nu,\gamma_n)^2\leq2H(\nu\mid\gamma_n)$ for every probability
  $\nu$, with extended values allowed.
* **53. HWI inequality.** For $\mu=Z^{-1}e^{-V}dx$ with
  $D^2V\geq\kappa I$ and finite second moment, and sufficiently regular probabilities with finite
  second moment and Fisher information,
  $$H(\nu\mid\mu)\leq W_2(\nu,\mu)\sqrt{I(\nu\mid\mu)}
      -\frac\kappa2W_2(\nu,\mu)^2.$$
* **54. Otto–Villani implication.** Logarithmic Sobolev with constant
  $C_{LS}$ for a smooth probability on a complete Riemannian manifold implies
  $W_2(\nu,\mu)^2\leq2C_{LS}H(\nu\mid\mu)$.
* **55. Bobkov–Götze equivalence.** On a Polish metric space with finite
  first moment, $W_1(\nu,\mu)^2\leq2C H(\nu\mid\mu)$ is equivalent to
  $\int e^{\lambda(f-\mu f)}d\mu\leq e^{C\lambda^2/2}$ for every
  1-Lipschitz $f$ and real $\lambda$.
* **56. Wasserstein contraction.** For the conservative Langevin diffusion
  generated by $\Delta-\nabla V\cdot\nabla$ with $D^2V\geq\kappa I$,
  $W_2(P_t^*\nu,P_t^*\eta)\leq e^{-\kappa t}W_2(\nu,\eta)$.
* **57. Displacement convexity.** Under that Hessian bound, relative entropy
  is $\kappa$-convex along Euclidean $W_2$ geodesics:
  $$H(\nu_t\mid\mu)\leq(1-t)H(\nu_0\mid\mu)+tH(\nu_1\mid\mu)
     -\frac\kappa2t(1-t)W_2(\nu_0,\nu_1)^2.$$
  Finite-entropy, finite-second-moment endpoints give the standard formulation.
* **58. Gaussian Beckner inequalities.** For $1\leq p<2$,
  $$\|f\|_{L^2(\gamma_n)}^2-\|f\|_{L^p(\gamma_n)}^2
    \leq(2-p)\int|\nabla f|^2d\gamma_n.$$
  The limit as $p\uparrow2$ is the Gaussian logarithmic Sobolev inequality;
  the $p=1$ bound is a variance-type endpoint.
* **59. Sharp sphere Sobolev inequality.** On the unit $n$-sphere, $n\geq3$,
  with normalized volume,
  $$\|f\|_{2n/(n-2)}^2\leq\|f\|_2^2+
        \frac4{n(n-2)}\|\nabla f\|_2^2.$$
  The coefficient is sharp; conformal factors give its extremizers.
* **60. Aubin's local-to-global sharp bound.** On a closed connected $n$-manifold,
  $n\geq3$, for every $\varepsilon>0$ there is $C_\varepsilon$ with
  $$\|u\|_{2^*}^2\leq(S_n^2+\varepsilon)\|\nabla u\|_2^2
      +C_\varepsilon\|u\|_2^2.$$
  The leading constant cannot be smaller than the Euclidean one. For the
  conformal Laplacian, minimization of the corresponding Sobolev quotient is
  the Yamabe problem; every smooth closed conformal class in dimension at
  least three has a smooth positive minimizer and hence a constant-scalar-curvature
  representative. Compactness at the critical exponent is the central difficulty.

## Further equivalences, stability, and spectral consequences

For a probability with density $p$ on $\mathbb R^n$, relative entropy compares
it with a specified reference measure; the Euclidean integral
$\int p\log p\,dx$ instead uses Lebesgue reference, which has infinite mass.
The two expressions have different transformation laws under dilations.
In the spectral statements below Dirichlet eigenvalues are ordered increasingly,
and the potential in $-\Delta-V$ is nonnegative.

* **61. Sharp Euclidean logarithmic Sobolev inequality.** If $\|f\|_2=1$,
  $f\in H^1(\mathbb R^n)$, then
  $$\int f^2\log f^2dx\leq\frac n2\log\left(
      \frac2{\pi e n}\int|\nabla f|^2dx\right).$$
  The positive part is controlled by the inequality; a negative-infinite
  integral is allowed. Gaussian functions attain equality. This scale-invariant
  Lebesgue formulation differs from the normalized Gaussian-measure inequality.
* **62. Linearization of logarithmic Sobolev.** A probability logarithmic
  Sobolev inequality with constant $C_{LS}$ implies Poincaré with
  $C_P\leq C_{LS}$. Substituting $1+\varepsilon f$ and expanding to second
  order identifies the variance as the quadratic part of entropy. The converse
  fails in general, so exponential $L^2$ decay alone need not give hypercontractivity.
* **63. Variational formula for entropy.** For probabilities on a Polish space,
  $$H(\nu\mid\mu)=\sup_g\left\{\int g\,d\nu-
      \log\int e^g d\mu\right\},$$
  where bounded measurable $g$ suffice, and bounded continuous $g$ also suffice.
  This formula links exponential integrability to transport and concentration;
  it remains valid when the entropy is infinite.
* **64. Cheng eigenvalue comparison.** On a complete $n$-manifold with
  nonnegative Ricci curvature, the first Dirichlet eigenvalue of a geodesic
  ball of radius $r$ is at most that of the Euclidean radius-$r$ ball:
  $\lambda_1(B(x,r))\leq j_{n/2-1,1}^2/r^2$, where $j_{\nu,1}$ is the
  first positive zero of $J_\nu$. The eigenvalue is understood variationally
  even when the geodesic sphere is not smooth.
* **65. Buser's converse to Cheeger.** For a closed connected $n$-manifold,
  $n\geq2$, with $\operatorname{Ric}\geq-(n-1)k^2g$, $k\geq0$,
  $\lambda_1\leq C_n(kh+h^2)$ for the closed-manifold Cheeger constant.
  Together with Cheeger's lower bound, this compares spectral and isoperimetric
  gaps under a curvature lower bound.
* **66. Isoperimetry and endpoint Sobolev.** On a Riemannian manifold, a
  bound $P(E)\geq c|E|^{1-1/d}$, $d>1$, for all precompact finite-perimeter
  sets is equivalent to
  $\|u\|_{d/(d-1)}\leq c^{-1}\int|\nabla u|$ for compactly supported
  functions. Coarea and the integral triangle inequality give one direction;
  smooth approximation of indicators gives the other. Thus perimeter profiles
  can determine Sobolev exponents without an ambient Euclidean structure.
* **67. Bianchi–Egnell stability.** For $n\geq3$ and the sharp constant $S_n$,
  $$\|\nabla u\|_2^2-S_n^{-2}\|u\|_{2^*}^2
    \geq c_n\inf_{v\in\mathcal M}\|\nabla(u-v)\|_2^2,$$
  where $\mathcal M$ is the family of scalar multiples, translations, and
  dilations of the Sobolev optimizer, including zero. The deficit therefore
  controls distance from the full family generated by the scaling, translation,
  and scalar-multiplication symmetries of the inequality.
* **68. Payne–Pólya–Weinberger ratio inequality.** For a bounded Euclidean
  domain in dimension $n\geq2$,
  $\lambda_2(\Omega)/\lambda_1(\Omega)
  \leq\lambda_2(B)/\lambda_1(B)$.
  Balls maximize this scale-invariant Dirichlet eigenvalue ratio. This is a
  different optimization problem from fixing volume and minimizing $\lambda_1$.
* **69. Berezin–Li–Yau eigenvalue sum.** For bounded open
  $\Omega\subseteq\mathbb R^n$ and $k\geq1$,
  $$\sum_{j=1}^k\lambda_j(\Omega)\geq
    \frac n{n+2}(2\pi)^2(\omega_n|\Omega|)^{-2/n}k^{1+2/n}.$$
  The leading coefficient agrees with the integrated Weyl asymptotic. The
  inequality is valid without a smooth-boundary assumption.
* **70. Lieb–Thirring inequalities.** For negative eigenvalues $E_j$ of
  $-\Delta-V$,
  $$\sum_j|E_j|^\gamma\leq L_{\gamma,n}
      \int_{\mathbb R^n}V(x)^{\gamma+n/2}dx.$$
  Finite constants exist for $\gamma\geq1/2$ in dimension one, $\gamma>0$
  in dimension two, and $\gamma\geq0$ in dimensions at least three.
  At $\gamma=0$ the left side counts negative eigenvalues, giving the
  Cwikel–Lieb–Rozenblum inequality. The potential is assumed to belong to the
  displayed Lebesgue class; infinite right sides give no quantitative content.

## Reference guide

Maz'ya, *Sobolev Spaces*, especially the chapters on boundary-vanishing
functions, capacities, and embeddings, supplies the Euclidean and capacitary
spine. Aubin and Hebey develop sharp constants and the manifold endpoint;
Ghoussoub–Moradifam develops Hardy and Rellich inequalities. Chavel,
Burago–Zalgaller, Maggi, and Henrot connect perimeter, comparison geometry,
and spectral optimization. The quantitative isoperimetric statement is the
standard stability theorem surveyed in the Maggi/Fusco strand of the bibliography.

Bakry–Gentil–Ledoux, Chapters 4–6, develops Poincaré, logarithmic Sobolev,
Sobolev, and curvature–dimension inequalities; Chapters 7–9 gives the weak,
capacitary, isoperimetric, and transport connections. Saloff-Coste and
Grigor'yan develop the heat-kernel side. Villani and Ledoux give independent
transport and concentration treatments; Gaussian sharp results also belong to
Bogachev's Gaussian-measure framework.

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
- [Pólya–Szegő, *Isoperimetric Inequalities in Mathematical Physics*](References/PolyaSzegö1951rep2016IsoperimetricInequalitiesMathematicalPhysics-PrincetonAnnalsMathStud27.pdf).
- [Chavel, *Riemannian Geometry*](References/Chavel2006RiemannianGeometryModernIntroduction2ndEd-CambridgeStudiesAM98.pdf), a supplementary local source for the comparison geometry.
- [Frank–Laptev–Weidl, *Schrödinger Operators: Eigenvalues and Lieb–Thirring Inequalities*](References/FrankLaptevWeidl2023SchrodingerOperatorsEigenvaluesLiebThirringInequalities-Cambridge.StudAM200.pdf), for the negative-eigenvalue bounds.
