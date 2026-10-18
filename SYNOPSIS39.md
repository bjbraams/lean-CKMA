# Synopsis: Metric measure spaces, Dirichlet forms, heat kernels, optimal transport, and fractals

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects recurring core material from Section 39 of
[CKMA-bib.md](CKMA-bib.md).
Its common theme is analysis specified by distances, measures, energies, and
transport, including spaces without smooth coordinates. Metric Sobolev theory,
diffusion, and transport have overlapping but distinct hypotheses; none of
these structures is implicit in the words “metric measure space.”

Unless specified otherwise, $(X,d,m)$ is complete and separable, $m$ is a
Radon measure of full support, and $0<m(B(x,r))<\infty$. Write
$V(x,r)=m(B(x,r))$. A measure is **doubling** if
$V(x,2r)\leq C_DV(x,r)$. A space is **Ahlfors $Q$-regular** if
$V(x,r)\asymp r^Q$ for $0<r<\operatorname{diam}X$.
All comparison constants are uniform on the scales under consideration.

## Upper gradients and metric Sobolev spaces

A Borel function $g\geq0$ is an **upper gradient** of $u$ if
$|u(\gamma(b))-u(\gamma(a))|\leq\int_\gamma g\,ds$ for every
rectifiable curve. The **$p$-modulus** of a curve family is
$$
\operatorname{Mod}_p\Gamma=\inf\left\{\int\rho^p\,dm:
\rho\geq0,\ \int_\gamma\rho\,ds\geq1\quad(\gamma\in\Gamma)\right\}.
$$
A **$p$-weak upper gradient** may fail on a family of zero $p$-modulus.
The **Newtonian space** $N^{1,p}(X)$ has norm
$\|u\|_{N^{1,p}}^p=\|u\|_p^p+\inf_g\|g\|_p^p$, with the
usual identification of zero-norm differences. A **$(1,p)$-Poincaré
inequality** means
$$
\fint_B|u-u_B|\,dm\leq Cr_B\left(\fint_{\lambda B}g^p\,dm\right)^{1/p}.
$$

* **1. Doubling geometry.** A doubling measure of full support makes
  $X$ metrically doubling: balls admit covers by uniformly finitely many
  half-radius balls. Completeness then makes closed bounded sets compact.
* **2. Maximal estimates and differentiation.** On a doubling space
  the centered maximal operator is weak type $(1,1)$ and bounded on
  $L^p$, $1<p\leq\infty$. Locally integrable functions have
  $m$-almost every point as a Lebesgue point.
* **3. Modulus convergence.** If $g_j\to g$ in $L^p$, a subsequence
  satisfies $\int_\gamma|g_j-g|\,ds\to0$ outside a curve family of
  zero $p$-modulus. This is the basic closure principle for weak upper gradients.
* **4. Minimal upper gradients.** For $1\leq p<\infty$, every Newtonian
  function has a minimal $p$-weak upper gradient $g_u\in L^p$,
  unique almost everywhere and bounded above almost everywhere by every
  other $L^p$ weak upper gradient.
* **5. Completeness and calculus.** $N^{1,p}$ is complete. Minimal
  gradients are local, obey a product inequality for bounded functions,
  and satisfy $g_{\phi\circ u}\leq\operatorname{Lip}(\phi)g_u$.
  For $C^1$ Lipschitz $\phi$, the sharper chain rule holds almost everywhere.
* **6. Euclidean identification.** On Euclidean open sets with
  Lebesgue measure, $N^{1,p}=W^{1,p}$ as spaces of appropriate
  representatives, and $g_u=|\nabla u|$ almost everywhere.
* **7. Quasiconvexity.** A complete doubling space supporting a
  $(1,p)$-Poincaré inequality is quasiconvex: points can be joined by
  curves of length at most $Cd(x,y)$.
* **8. Lipschitz density.** Under these same assumptions, Lipschitz
  functions in $N^{1,p}$ are dense there for $1\leq p<\infty$.
* **9. Sobolev capacity and quasi-continuity.** The capacity obtained
  by minimizing $\|u\|_{N^{1,p}}^p$ over $u\geq1$ on a set
  gives Newtonian functions quasi-continuous representatives on complete
  doubling Poincaré spaces. Their precise representatives are unique
  outside sets of zero capacity.
* **10. Sobolev–Poincaré improvement.** On an Ahlfors $Q$-regular
  Poincaré space, $1\leq p<Q$ gives the local inequality
  $\bigl(\fint_B|u-u_B|^{p^*}\bigr)^{1/p^*}
  \leq Cr_B(\fint_{\lambda B}g_u^p)^{1/p}$,
  where $p^*=Qp/(Q-p)$, with a fixed enlargement of the ball.
* **11. Morrey estimate.** If $p>Q$ in this setting, Newtonian
  functions have locally Hölder representatives of exponent $1-Q/p$;
  their oscillation is controlled by the local $L^p$ upper-gradient norm.
* **12. Keith–Zhong self-improvement.** If a complete doubling space
  supports a $(1,p)$-Poincaré inequality with $p>1$, it supports
  a $(1,p-\varepsilon)$-Poincaré inequality for some $\varepsilon>0$.
* **13. Cheeger differentiation.** A complete doubling Poincaré space
  admits countably many measurable charts of uniformly bounded finite
  dimension in which every real Lipschitz function has an almost
  everywhere unique measurable differential.
* **14. Hajłasz characterization.** On a complete doubling Poincaré
  space and for $p>1$, $N^{1,p}$ agrees, with equivalent norms,
  with the space of $L^p$ functions admitting $g\in L^p$ such that
  $|u(x)-u(y)|\leq d(x,y)(g(x)+g(y))$ outside a null set.

## Embeddings, quasisymmetry, and Gromov–Hausdorff convergence

A homeomorphism $f$ is **$\eta$-quasisymmetric** if
$d(x,a)\leq t\,d(x,b)$ implies $d(fx,fa)\leq\eta(t)\,d(fx,fb)$ for an
increasing homeomorphism $\eta$ of $[0,\infty)$. A space is
**$Q$-Loewner** if $\operatorname{Mod}_Q$ of the curves joining disjoint
continua $E,F$ is bounded below by a positive function of
$\operatorname{dist}(E,F)/\min(\operatorname{diam}E,\operatorname{diam}F)$.
The **Gromov–Hausdorff distance** $d_{GH}(X,Y)$ is the infimum of
Hausdorff distances between isometric copies of $X,Y$ in a common metric space.

* **15. Assouad embedding.** If $(X,d)$ is metrically doubling and
  $0<\varepsilon<1$, then the snowflake $(X,d^\varepsilon)$ admits a
  bi-Lipschitz embedding into some $\mathbb R^N$, with $N$ and the
  distortion depending only on $\varepsilon$ and the doubling constant.
  The case $\varepsilon=1$ fails, for example for the Heisenberg group.
* **16. Loewner spaces and quasisymmetry.** A proper geodesic Ahlfors
  $Q$-regular space with $Q>1$ is $Q$-Loewner if and only if it supports a
  $(1,Q)$-Poincaré inequality (Heinonen–Koskela), quantitatively.
  Quasiconformal homeomorphisms, defined by bounded infinitesimal
  distortion, between $Q$-regular Loewner spaces are locally quasisymmetric.
* **17. Gromov precompactness.** A family of compact metric spaces is
  precompact for $d_{GH}$ if and only if diameters are uniformly bounded
  and, for each $\varepsilon>0$, the number of $\varepsilon$-balls needed
  to cover each space is uniformly bounded. The limit space of such a
  sequence is compact; uniformly doubling spaces of bounded diameter, and
  closed Riemannian $n$-manifolds with $\operatorname{Ric}\geq-(n-1)k$
  and $\operatorname{diam}\leq D$ (by Bishop–Gromov), form precompact families.

## Dirichlet forms and symmetric processes

A **Dirichlet form** $(\mathcal E,\mathcal F)$ is a densely defined
closed nonnegative symmetric form on $L^2(m)$ with the Markov property:
normal contractions decrease energy. It is **regular** on a locally compact
separable space if $\mathcal F\cap C_c(X)$ is dense in both $\mathcal F$
for $\mathcal E_1=\mathcal E+\|\cdot\|_2^2$ and $C_0(X)$ uniformly.
It is **strongly local** if $\mathcal E(u,v)=0$ whenever $u$ is constant
near the compact support of $v$.

* **18. Form–operator correspondence.** A closed nonnegative form
  determines a unique nonnegative self-adjoint operator $A$ with
  $\mathcal F=D(A^{1/2})$ and
  $\mathcal E(u,v)=\langle A^{1/2}u,A^{1/2}v\rangle$.
  Its semigroup is $P_t=e^{-tA}$.
* **19. Beurling–Deny criterion.** The Markov property of the form
  is equivalent to $P_t$ being positivity preserving and
  $0\leq P_tf\leq1$ whenever $0\leq f\leq1$.
  Thus Dirichlet forms and symmetric sub-Markov semigroups correspond.
* **20. Extension and resolvents.** Such semigroups extend consistently
  as contractions to every $L^p$, $1\leq p\leq\infty$, and are
  strongly continuous for $p<\infty$. Their resolvents satisfy
  $(\alpha+A)^{-1}f=\int_0^\infty e^{-\alpha t}P_tf\,dt$.
* **21. Capacitary representatives.** A regular form has an associated
  $1$-capacity. Every $u\in\mathcal F$ has a quasi-continuous
  version, unique quasi-everywhere; energy-norm convergence admits a
  subsequence converging quasi-everywhere.
* **22. Process representation.** Every regular Dirichlet form has
  an associated symmetric Hunt process, unique up to the appropriate
  capacity-zero exceptional sets. Its transition semigroup represents
  $P_t$ using quasi-continuous versions.
* **23. Beurling–Deny decomposition.** A regular symmetric form
  decomposes uniquely into a strongly local energy, a symmetric jump
  energy off the diagonal, and a nonnegative killing measure.
  Strong locality excludes both jump and killing parts.
* **24. Energy measures.** Strongly local regular forms have
  carré-du-champ measures characterized, for bounded form functions,
  by $\int\phi\,d\Gamma(u)=\mathcal E(u,u\phi)
  -\frac12\mathcal E(u^2,\phi)$. They obey Leibniz and chain rules.
* **25. Diffusion and locality.** The process of a strongly local
  regular form has continuous sample paths up to its lifetime.
  Conservativeness, $P_t1=1$, is an additional property excluding explosion.
  On a complete Riemannian manifold it follows from Grigor'yan's volume test
  $\int^\infty r\,dr/\log V(x_0,r)=\infty$.
* **26. Recurrence criterion.** A Dirichlet form is recurrent precisely
  when there are $u_j\in\mathcal F$ with $0\leq u_j\leq1$, $u_j\to1$
  almost everywhere, and $\mathcal E(u_j)\to0$; it is transient precisely
  when the extended Dirichlet space is a Hilbert space under $\mathcal E$.
  An irreducible form is either recurrent or transient.

## Heat kernels, inequalities, and curvature

When $P_t$ has a density write
$P_tf(x)=\int p_t(x,y)f(y)\,dm(y)$. In the diffusion estimates below,
the **intrinsic distance** is the distance obtained from form functions
with $d\Gamma(u)\leq dm$. Compatibility of that distance with the topology
and completeness are explicit assumptions, not automatic consequences of regularity.

* **27. Kernel identities.** Symmetric heat kernels satisfy
  $p_t(x,y)=p_t(y,x)$, the Chapman–Kolmogorov identity, and
  $\int p_t(x,y)dm(y)\leq1$. Under conservativeness the last integral is one.
* **28. Davies–Gaffney estimate.** A strongly local form with its
  intrinsic distance satisfies
  $|\langle P_tf,g\rangle|\leq e^{-d(E,F)^2/(4t)}\|f\|_2\|g\|_2$
  for functions supported in sets $E,F$.
* **29. Nash equivalence.** The inequality
  $\|u\|_2^{2+4/D}\leq C\mathcal E(u)\|u\|_1^{4/D}$
  is equivalent, up to constants, to
  $\|P_t\|_{1\to\infty}\leq Ct^{-D/2}$ for all $t>0$.
* **30. Sobolev and ultracontractivity.** For $D>2$,
  $\|u\|_{2D/(D-2)}^2\leq C\mathcal E(u)$ implies the preceding
  heat bound; the heat bound also implies this Sobolev inequality.
  Finite-volume local versions include lower-order terms.
* **31. Gaussian estimates from geometry.** For a complete geodesic
  strongly local regular Dirichlet space with compatible intrinsic metric,
  volume doubling and a scale-invariant $L^2$-Poincaré inequality imply
  two-sided bounds
  $$
  \frac{c}{V(x,\sqrt t)}e^{-C d(x,y)^2/t}
  \leq p_t(x,y)\leq
  \frac{C}{V(x,\sqrt t)}e^{-c d(x,y)^2/t}.
  $$
  Kernel versions are understood outside exceptional sets, or everywhere
  when a continuous kernel is available.
* **32. Parabolic Harnack equivalence.** In this diffusion setting
  (Grigor'yan, Saloff-Coste, Sturm), the following are equivalent:
  volume doubling plus Poincaré; the scale-invariant parabolic Harnack
  inequality; and the two-sided Gaussian bounds of the preceding entry.
  Parabolic Harnack bounds positive caloric functions on an earlier interior
  subcylinder above by a constant times their infimum on a later one.
* **33. Hölder regularity.** Parabolic Harnack yields local Hölder
  continuity of caloric functions and the heat kernel. Its elliptic
  counterpart gives Harnack and Hölder estimates for harmonic functions.
* **34. Li–Yau estimate.** On a complete $n$-manifold with
  $\operatorname{Ric}\geq0$, positive heat solutions satisfy
  $|\nabla\log u|^2-\partial_t\log u\leq n/(2t)$.
  Integration gives the corresponding space-time Harnack inequality.
* **35. Varadhan asymptotics.** For the heat kernel of $\Delta$
  on a complete connected Riemannian manifold,
  $\lim_{t\downarrow0}-4t\log p_t(x,y)=d(x,y)^2$.
* **36. Bakry–Émery gradient bound.** For a symmetric conservative
  diffusion generator $L=-A$, the condition
  $\Gamma_2(f)\geq K\Gamma(f)$ implies
  $\Gamma(P_tf)\leq e^{-2Kt}P_t\Gamma(f)$, assuming the usual
  diffusion calculus and closure hypotheses. The converse follows by
  differentiating at $t=0$ on a core.
* **37. Curvature and functional inequalities.** If the diffusion is
  ergodic, $m$ is an invariant probability measure, and
  $\Gamma_2\geq K\Gamma$ with $K>0$,
  then $\operatorname{Var}_m(f)\leq K^{-1}\mathcal E(f)$ and
  $\operatorname{Ent}_m(f^2)\leq2K^{-1}\mathcal E(f)$.
* **38. Gross's hypercontractivity theorem.** For a symmetric Markov
  semigroup with invariant probability $m$, the logarithmic Sobolev
  inequality $\operatorname{Ent}_m(f^2)\leq2C\mathcal E(f)$ is equivalent to
  $\|P_tf\|_{q(t)}\leq\|f\|_p$ for all $1<p<\infty$, $t>0$, with
  $q(t)-1=(p-1)e^{2t/C}$. The Ornstein–Uhlenbeck semigroup is the model, with $C=1$.

## Optimal transportation and Wasserstein geometry

For probability measures $\mu,\nu$, a **coupling** is a probability
measure $\pi$ on $X\times X$ with these marginals; write $\Pi(\mu,\nu)$.
The Kantorovich cost is $\inf_{\pi\in\Pi}\int c\,d\pi$.
For $1\leq p<\infty$, $\mathcal P_p(X)$ consists of probabilities
with finite $p$th moment and
$W_p(\mu,\nu)^p=\inf_\pi\int d(x,y)^p\,d\pi$.
The Monge problem restricts to couplings $(\mathrm{id},T)_\#\mu$.

* **39. Existence of optimal plans.** A nonnegative lower semicontinuous
  cost on Polish spaces attains its minimum over couplings. The same
  holds for costs bounded below by a sum of integrable marginal functions.
* **40. Kantorovich duality.** For lower semicontinuous nonnegative
  costs, the primal value equals
  $\sup_{\phi(x)+\psi(y)\leq c(x,y)}(\int\phi\,d\mu+\int\psi\,d\nu)$
  in the standard integrable dual class. For compact spaces and continuous
  costs, optimal continuous potentials exist.
* **41. Cyclical monotonicity.** For a lower semicontinuous real-valued cost
  bounded below with finite optimal value, a coupling is optimal if and
  only if it is concentrated on a $c$-cyclically monotone set:
  $\sum c(x_i,y_i)\leq\sum c(x_i,y_{i+1})$ for every finite cycle.
  For quadratic cost on $\mathbb R^n$, Rockafellar's theorem places such
  sets in the subdifferential of a convex function.
* **42. Wasserstein completeness.** If $X$ is complete and separable,
  then $(\mathcal P_p(X),W_p)$ is complete and separable. Gluing
  couplings proves the triangle inequality.
* **43. Wasserstein convergence.** $W_p(\mu_j,\mu)\to0$ precisely
  when $\mu_j\rightharpoonup\mu$ and their $p$th moments about
  one base point converge. Equivalently, weak convergence is accompanied
  by uniform integrability of those moments.
* **44. Kantorovich–Rubinstein formula.**
  $W_1(\mu,\nu)=\sup_{\operatorname{Lip}(f)\leq1}\int f\,d(\mu-\nu)$
  for $\mu,\nu\in\mathcal P_1(X)$.
* **45. One-dimensional transport.** On $\mathbb R$ the quantile
  coupling is optimal for $|x-y|^p$ and
  $W_p^p=\int_0^1|F_\mu^{-1}(s)-F_\nu^{-1}(s)|^pds$.
  If $\mu$ has no atoms, it is induced by the monotone rearrangement.
* **46. Brenier's theorem.** For $\mu,\nu\in\mathcal P_2(\mathbb R^n)$
  with $\mu$ absolutely continuous, the quadratic optimal plan is unique
  and induced by $T=\nabla\phi$, with $\phi$ convex and $T$
  unique $\mu$-almost everywhere.
* **47. Monge–Ampère relation.** If Brenier's potential is $C^2$
  and the optimal map is a diffeomorphism between regions with densities
  $f,g$, then $g(\nabla\phi)\det D^2\phi=f$.
  Without such regularity, convex potentials give the corresponding
  measure-theoretic transport formulation.
* **48. Displacement interpolation.** An optimal Euclidean quadratic
  plan gives a constant-speed $W_2$ geodesic by pushing it forward under
  $(x,y)\mapsto(1-t)x+ty$. In a geodesic Polish space, optimal
  dynamical plans give the analogous construction along geodesics.
* **49. Benamou–Brenier formula.** On $\mathbb R^n$,
  $$
  W_2(\mu_0,\mu_1)^2=\inf\int_0^1\int|v_t|^2\,d\mu_t\,dt,
  \qquad \partial_t\mu_t+\nabla\cdot(v_t\mu_t)=0,
  $$
  over distributional solutions with the prescribed endpoints.
* **50. Absolutely continuous curves.** A $W_2$-absolutely continuous
  curve admits a velocity field solving the continuity equation with
  $\|v_t\|_{L^2(\mu_t)}=|\dot\mu_t|$ almost everywhere when chosen
  of minimal norm. Conversely an integrable $L^2$ velocity controls
  the metric derivative by its norm.
* **51. Displacement convexity.** On $\mathbb R^n$, for convex
  $U$ with $U(0)=0$, $\mu\mapsto\int U(\rho)dx$ is displacement convex if
  $s\mapsto s^nU(s^{-n})$ is convex and nonincreasing, with the
  usual lower semicontinuous extension to singular measures.
  Entropy and powers $U(r)=r^q/(q-1)$, $q>1$, are examples.
* **52. Potential and interaction energies.** If $D^2V\geq\lambda I$,
  $\int V\,d\mu$ is $\lambda$-convex along $W_2$ geodesics.
  Convex even interaction kernels give displacement-convex interaction
  energies $\frac12\iint W(x-y)d\mu(x)d\mu(y)$.
* **53. Ricci curvature and entropy.** On a complete weighted manifold
  $m=e^{-V}\mathrm{vol}$, $\operatorname{Ric}+D^2V\geq K$
  is equivalent to $K$-displacement convexity of relative entropy.
  This motivates the synthetic condition $CD(K,\infty)$.
* **54. Transport–entropy inequalities.** If a probability measure $m$ on
  a Riemannian manifold satisfies $\operatorname{Ent}_m(f^2)\leq
  (2/K)\int|\nabla f|^2dm$, then
  $W_2(\mu,m)^2\leq(2/K)\operatorname{Ent}(\mu\,|\,m)$ (Otto–Villani);
  this in turn implies the Poincaré inequality with constant $1/K$.
  For the standard Gaussian, $K=1$ (Talagrand's inequality).
* **55. Curvature–dimension conditions.** The Lott–Sturm–Villani
  condition $CD(K,N)$ asks for convexity, with $(K,N)$-distorted
  coefficients, of Rényi entropies along $W_2$ geodesics. It is stable
  under measured Gromov–Hausdorff convergence. For $1<N<\infty$ it implies
  Bishop–Gromov volume comparison with the model space, Brunn–Minkowski
  inequalities, and, for $K>0$, $\operatorname{diam}X\leq\pi\sqrt{(N-1)/K}$.
  On a weighted $n$-manifold with $N>n$ it is equivalent to
  $\operatorname{Ric}+D^2V-\frac{\nabla V\otimes\nabla V}{N-n}\geq K$.

## Metric gradient flows and synthetic diffusion

For a lower semicontinuous energy $F$, its **descending slope** is
$|\partial F|(x)=\limsup_{y\to x}(F(x)-F(y))_+/d(x,y)$.
The implicit step minimizes $F(y)+d(y,x)^2/(2\tau)$.
An **$EVI_\lambda$ flow** obeys, for every admissible comparison point $v$,
$$
\frac12\frac d{dt}d(u_t,v)^2+\frac\lambda2d(u_t,v)^2+F(u_t)\leq F(v).
$$

* **56. Metric derivatives.** Every absolutely continuous curve in a
  metric space has a metric derivative almost everywhere, and its length
  is the integral of that derivative. This derivative is the least
  almost everywhere upper bound in the absolute-continuity estimate.
* **57. Minimizing movements.** A proper lower semicontinuous energy
  on a complete metric space, bounded below and with compact sublevels,
  admits subsequential limits of implicit steps on finite time intervals
  from finite-energy initial points. Identifying the
  limit with a curve of maximal slope requires slope lower semicontinuity
  and an upper-gradient property; compactness alone does not supply it.
* **58. Convex flows in Hadamard spaces.** A proper lower semicontinuous
  convex energy on a complete $CAT(0)$ space generates a unique
  $EVI_0$ flow on the closure of its effective domain. Resolvents
  and the flow are nonexpansive, and iterated resolvents converge to it.
* **59. EVI uniqueness and contraction.** Two $EVI_\lambda$ flows
  satisfy $d(u_t,v_t)\leq e^{-\lambda t}d(u_0,v_0)$.
  They are unique and, when defined for all initial data, form a semigroup.
* **60. Energy dissipation.** For an EVI flow,
  $F(u_s)-F(u_t)=\frac12\int_s^t(|\dot u_r|^2+
  |\partial F|^2(u_r))dr$, and speed equals descending slope almost
  everywhere. For positive convexity, distance to a minimizer decays exponentially.
* **61. Wasserstein minimizing movements.** A proper lower semicontinuous
  energy on $\mathcal P_2(\mathbb R^n)$, $\lambda$-convex along
  generalized geodesics, generates an $EVI_\lambda$ flow if its
  penalized minimization problems attain their infima for all sufficiently
  small steps. The transport implicit scheme converges to this flow.
* **62. Heat and Fokker–Planck equations.** The $W_2$ gradient flow
  of $\int\rho\log\rho\,dx+\int V\rho\,dx$ solves
  $\partial_t\rho=\Delta\rho+\nabla\cdot(\rho\nabla V)$.
  For $V=0$ this identifies heat flow with steepest entropy descent.
* **63. Porous-medium flow.** The $W_2$ flow of
  $\frac1{q-1}\int\rho^qdx$, $q>1$, is the weak solution of
  $\partial_t\rho=\Delta\rho^q$, for initial probability densities
  with finite energy and second moment.
* **64. Cheeger energy and Hilbertianity.** Relaxation of
  $\frac12\int(\operatorname{lip}f)^2dm$ gives a convex lower
  semicontinuous energy and an $L^2$ gradient-flow semigroup. That
  semigroup is linear exactly when the relaxed energy is quadratic.
* **65. Riemannian synthetic curvature.** On an $RCD(K,\infty)$ probability space,
  namely a $CD(K,\infty)$ space with quadratic Cheeger energy,
  $L^2$ heat flow agrees with the $EVI_K$ entropy flow in $W_2$.
  It contracts $W_2$ by $e^{-Kt}$ for finite-second-moment initial measures.
  See also [Ambrosio–Gigli–Savaré's foundational treatment](https://arxiv.org/abs/1109.0222)
  for the equivalence with linear heat flow, initially with finite reference measure.

## Networks, resistance, and fractal diffusion

A weighted graph has symmetric conductances $b(x,y)\geq0$,
$b(x,x)=0$, $\sum_yb(x,y)<\infty$, vertex masses $m(x)>0$,
and possibly killing $c(x)\geq0$. Its energy and formal Laplacian are
$$
\mathcal E(u)=\frac12\sum_{x,y}b(x,y)|u(x)-u(y)|^2+
\sum_xc(x)|u(x)|^2,\qquad
Au(x)=\frac{\sum_yb(x,y)(u(x)-u(y))+c(x)u(x)}{m(x)}.
$$
A **resistance form** is a Markov energy on pointwise functions, Hilbert
modulo constants, separating points, with finite effective resistances.
The **walk dimension** $d_w$ describes time scale $r^{d_w}$; the
volume dimension $d_f$ describes $V(x,r)\asymp r^{d_f}$.

* **66. Graph realizations.** Closing finitely supported functions in
  the energy norm gives the regular Dirichlet realization; taking all
  finite-energy $\ell^2$ functions gives the Neumann realization.
  Their generators act by the displayed formal Laplacian on their domains.
  Equality of the realizations needs an additional uniqueness condition.
* **67. Electrical Dirichlet principle.** On a finite connected network,
  minimizing energy with boundary voltages gives the unique harmonic
  extension. Its boundary flux gives the conductance matrix; eliminating
  interior vertices preserves boundary effective resistances.
* **68. Effective resistance metric.** For a resistance form,
  $R(x,y)=\sup_{\mathcal E(u)>0}|u(x)-u(y)|^2/\mathcal E(u)$
  is a metric and $|u(x)-u(y)|^2\leq R(x,y)\mathcal E(u)$.
  Thus finite-energy functions are continuous in the resistance topology.
* **69. Thomson principle.** Effective resistance between two vertices
  is the minimum dissipation of unit flows between them. On an infinite
  locally finite connected network, transience is equivalent to a unit
  flow to infinity of finite energy.
* **70. Graph recurrence.** A connected network without killing is
  recurrent exactly when finitely supported functions $0\leq u_j\leq1$
  tend pointwise to one with $\mathcal E(u_j)\to0$. Equivalently,
  the effective resistance from a vertex to infinity is infinite.
* **71. Graph Harnack characterization.** For graphs with uniformly
  controlled transition probabilities, volume doubling and the
  scale-$r^2$ Poincaré inequality are equivalent to Gaussian estimates
  and parabolic Harnack. In discrete time the lower estimate uses
  $p_n+p_{n+1}$ to accommodate periodicity.
* **72. Resistance-form realization.** A regular resistance form on
  a locally compact resistance space, together with a full-support
  Radon measure, gives a regular Dirichlet form by closure on $L^2$.
  A local resistance form yields a diffusion.
* **73. Self-similar attractors.** A finite family of strict contractions
  has a unique nonempty compact invariant set, the fixed point of the
  union map on compact sets with the Hausdorff metric. Positive weights
  summing to one similarly determine a unique invariant probability measure.
* **74. Similarity dimension.** For Euclidean similarities with ratios
  $r_i$ satisfying the open set condition, the attractor has Hausdorff
  and box dimensions $s$ determined by $\sum_i r_i^s=1$,
  and $0<\mathcal H^s(K)<\infty$.
* **75. Gasket energy renormalization.** On the standard Sierpiński
  gasket, the graph energies renormalized by $(5/3)^j$ increase to
  a local resistance form. Harmonic extension minimizes energy and
  satisfies a finite system of self-similar extension rules.
* **76. Gasket anomalous scaling.** For the natural gasket measure,
  $d_f=\log3/\log2$ and $d_w=\log5/\log2$.
  Diffusion has time scale $r^{d_w}$ rather than $r^2$.
* **77. Sub-Gaussian kernels.** Conservative gasket diffusion satisfies, at small
  times and in its Euclidean metric, with $\Phi=(d(x,y)^{d_w}/t)^{1/(d_w-1)}$,
  $$
  c_1t^{-d_f/d_w}e^{-c_2\Phi}\leq p_t(x,y)
  \leq c_3t^{-d_f/d_w}e^{-c_4\Phi}.
  $$
  All four constants are strictly positive and independent of $t,x,y$.
* **78. Spectral dimension.** On a compact gasket with standard
  Dirichlet or Neumann conditions, the eigenvalue counting function
  obeys $N(\lambda)\asymp\lambda^{d_f/d_w}$ at high energy.
  The spectral dimension is $d_s=2d_f/d_w=2\log3/\log5$;
  a constant-coefficient Weyl asymptotic need not hold.
* **79. Cutoff inequalities for anomalous diffusion.** On controlled
  weighted graphs, volume doubling, a scale-$r^{d_w}$ Poincaré
  inequality, and the matching cutoff Sobolev inequality are equivalent
  to sub-Gaussian heat bounds and parabolic Harnack at that scale.
  Poincaré and doubling alone do not characterize $d_w>2$ diffusion.
* **80. Stability under rough isometries.** For controlled weighted
  graphs with comparable measures, the preceding Gaussian and
  sub-Gaussian Harnack properties are preserved by rough isometries.
  Their constants change with the comparison data.

## Reference guide

Heinonen and Heinonen–Koskela–Shanmugalingam–Tyson give the overlapping
upper-gradient, modulus, Poincaré, and differentiation theory; Heinonen
also treats Assouad embedding, Loewner spaces, and quasisymmetry, while
Burago–Burago–Ivanov, Ambrosio–Tilli, and Gromov develop Gromov–Hausdorff
convergence. Fukushima–
Oshima–Takeda and Chen–Fukushima are the general process references;
Keller–Lenz–Wojciechowski makes the form, semigroup, and recurrence
correspondences concrete on graphs. Grigor'yan, Saloff-Coste, Davies,
Bakry–Gentil–Ledoux, Barlow, and Kumagai connect inequalities and heat kernels.
Villani, Santambrogio, and Ambrosio–Gigli–Savaré organize transport and
gradient flows; the newer nonsmooth-geometry lectures explain the
Hilbertian synthetic-curvature continuation. Kigami, Barlow, Kumagai,
and Falconer supply the recurring fractal models. Specialized computational
transport, metastability, and fractal-zeta theories are not imported wholesale.

Local full-text sources consulted:

* [Heinonen, *Lectures on Analysis on Metric Spaces*](References/Heinonen2001AnalysisMetricSpaces-Springer.UTX.pdf).
* [Heinonen–Koskela–Shanmugalingam–Tyson, *Sobolev Spaces on Metric Measure Spaces*](References/HeinonenKoskelaShanmugalingamTyson2015SobolevSpacesMetricMeasureSpacesUpperGradients-CambridgeNewMathMonog27.pdf).
* [Keller–Lenz–Wojciechowski, *Graphs and Discrete Dirichlet Spaces*](References/KellerLenzWojciechowski2021GraphsDiscreteDirichletSpaces-Springer.GL358.pdf).
* [Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion Operators*](References/BakryGentilLedoux2014AnalysisGeometryMarkovDiffusionOperators-SpringerGL348.pdf).
* [Villani, *Optimal Transport: Old and New*](References/Villani2009OptimalTransportOldNew-SpringerGL338.pdf).
* [Ambrosio–Gigli–Savaré, *Gradient Flows*, second edition](References/AmbrosioGigliSavare2008GradientFlows2ndEd-SpringerLMETH.pdf).
* [Kumagai, *Random Walks on Disordered Media and their Scaling Limits*](References/Kumagai2014RandomWalksDisorderedMediaScalingLimits-Springer.LNM2101.pdf).
* [Kigami, *Geometry and Analysis of Metric Spaces via Weighted Partitions*](References/Kigami2020GeometryAnalysisMetricSpacesViaWeightedPartitions-Springer.LNM2265.pdf).
