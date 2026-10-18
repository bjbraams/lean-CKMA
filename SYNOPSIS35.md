# Synopsis: Nonlinear functional analysis, monotone operators, and fixed points

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects recurring content from Section 35 of
[CKMA-bib.md](CKMA-bib.md).
Its main themes are nonlinear equations in Banach spaces, topological and
metric fixed points, degree, monotonicity, nonlinear evolution, and bifurcation.
Convex duality is developed separately in Section 12 and critical-point
variational methods in Section 36; they reappear here when they solve
operator equations or inclusions.

Spaces are real unless stated otherwise. $X^*$ is the continuous dual of
a Banach space $X$, and $H$ is a Hilbert space identified with its dual.
A set-valued operator is identified with its graph; $y\in Ax$ is written
$(x,y)\in A$. Compact nonlinear maps are continuous maps taking bounded
sets into relatively compact sets, unless compactness of the entire image
is explicitly specified.

## Nonlinear calculus and reduction of equations

The **Fréchet derivative** $DF(x)$ is the bounded linear map satisfying
$F(x+h)=F(x)+DF(x)h+o(\|h\|)$. A Gâteaux derivative tests directional
limits and need not by itself give Fréchet differentiability.

* **1. Chain rule.** Fréchet differentiable maps between Banach spaces
  satisfy $D(G\circ F)(x)=DG(F(x))DF(x)$. Continuous derivatives
  give the corresponding $C^r$ composition rules.
* **2. Mean-value estimate.** On a convex set where $\|DF\|\leq L$,
  a $C^1$ map satisfies $\|F(x)-F(y)\|\leq L\|x-y\|$.
  The integral of $DF(y+t(x-y))(x-y)$ gives the exact difference.
* **3. Inverse function theorem.** If $F$ is $C^1$ and $DF(x_0)$
  is an isomorphism, $F$ has a $C^1$ inverse between neighborhoods
  of $x_0$ and $F(x_0)$. Higher differentiability is inherited.
* **4. Implicit function theorem.** If $F(x_0,y_0)=0$ and
  $D_yF(x_0,y_0)$ is an isomorphism, nearby zeros are uniquely
  $y=\phi(x)$, with
  $D\phi=-(D_yF)^{-1}D_xF$ and the same $C^r$ regularity as $F$.
* **5. Submersion theorem.** A surjective derivative with complemented
  kernel makes a regular level set a local Banach submanifold modeled
  on that kernel. The complement hypothesis is automatic for Hilbert spaces.
* **6. Lyapunov–Schmidt reduction.** If $DF(x_0)$ is Fredholm, split
  the domain into kernel and a complement, and the codomain into range
  and a finite-dimensional complement. The implicit function theorem
  solves the range equation, leaving a finite-dimensional reduced zero equation.
* **7. Proper global inversion.** A proper $C^1$ map between Banach
  spaces whose derivative is an isomorphism everywhere is a global
  $C^1$ diffeomorphism. Properness supplies global continuation of the
  local inverses; the target Banach space is simply connected.
* **8. Sard–Smale theorem.** If $F:M\to N$ is a $C^r$ Fredholm map
  between separable Banach manifolds and $r>\max(\operatorname{ind}F,0)$,
  its regular values form a residual subset of $N$. Generic solution sets
  $F^{-1}(y)$ are therefore $C^r$ manifolds of dimension $\operatorname{ind}F$.
* **9. Newton–Kantorovich convergence.** Let $DF(x_0)$ be invertible,
  $\|DF(x_0)^{-1}F(x_0)\|\leq\eta$, and
  $\|DF(x_0)^{-1}(DF(x)-DF(y))\|\leq L\|x-y\|$ on a suitable
  ball. If $L\eta\leq1/2$ and that ball contains the majorant radius
  $(1-\sqrt{1-2L\eta})/L$, Newton iterates stay in the closed ball of
  that radius about $x_0$ and converge to a zero, which is unique in a
  larger ball. Near a zero with invertible derivative and Lipschitz
  derivative, convergence is quadratic.
* **10. Nemytskii continuity.** For finite $p,q\geq1$, a Carathéodory
  function $f(x,s)$ with $|f(x,s)|\leq a(x)+C|s|^{p/q}$,
  $a\in L^q$, defines a continuous superposition map $L^p\to L^q$.
  Conversely, if $u\mapsto f(\cdot,u)$ maps $L^p$ into $L^q$ (on a
  $\sigma$-finite measure space), then it is continuous and bounded and
  such a growth bound holds (Krasnosel'skii).

## Topological and metric fixed-point theorems

* **11. Banach contraction theorem.** A strict contraction of a complete
  metric space has a unique fixed point, and every Picard orbit
  converges geometrically to it with the usual a posteriori error bound.
* **12. Brouwer fixed-point theorem.** A continuous self-map of a
  nonempty compact convex subset of $\mathbb R^n$ has a fixed point.
  Equivalently (acute-angle lemma), a continuous $F:\mathbb R^n\to\mathbb R^n$
  with $F(x)\cdot x\geq0$ on $|x|=R$ has a zero in $|x|\leq R$; this is the
  step that solves Galerkin approximations.
* **13. Schauder fixed-point theorem.** If $C$ is nonempty closed
  convex in a Banach space and $T:C\to C$ is continuous with
  relatively compact image, then $T$ has a fixed point.
  In particular this applies to compact maps on bounded $C$.
* **14. Schauder–Tychonoff theorem.** Every continuous self-map of a
  nonempty compact convex subset of a Hausdorff locally convex space
  has a fixed point.
* **15. Kakutani–Fan–Glicksberg theorem.** An upper semicontinuous
  set-valued self-map of a nonempty compact convex subset of a locally
  convex Hausdorff space has a fixed point if all values are nonempty,
  closed, and convex.
* **16. Schaefer's theorem.** If $T:X\to X$ is compact and
  $\{x:x=tTx,\ 0\leq t\leq1\}$ is bounded, then $T$ has a
  fixed point. An a priori bound on the homotopy replaces invariance
  of a prescribed ball.
* **17. Leray–Schauder alternative.** Let $U$ be a bounded open set
  containing zero and $T:\overline U\to X$ compact. Either $T$
  has a fixed point in $\overline U$, or $x=tTx$ for some
  $x\in\partial U$ and $t\in(0,1)$.
* **18. Krasnosel'skii sum theorem.** On a nonempty closed bounded
  convex set $C$, let $A$ be compact and $B$ a strict contraction.
  If $Ax+By\in C$ for every $x,y\in C$, then $A+B$ has a fixed point.
* **19. Darbo's theorem.** A continuous self-map of a nonempty closed
  bounded convex set has a fixed point if
  $\alpha(TB)\leq k\alpha(B)$ for every bounded subset $B$ and
  some $k<1$, where $\alpha$ is the Kuratowski measure of noncompactness.
  This is the infimum of diameters permitting a finite cover of the set.
* **20. Monotone iteration in ordered spaces.** Let the Banach space
  $X$ be ordered by a closed normal cone, $v\leq w$, and let
  $T:[v,w]\to X$ be increasing and compact with $v\leq Tv$ and
  $Tw\leq w$. Then $T^nv$ increases to the minimal and $T^nw$ decreases
  to the maximal fixed point of $T$ in $[v,w]$ (Amann). This underlies
  the method of sub- and supersolutions.
* **21. Browder–Göhde–Kirk theorem.** A nonexpansive self-map of a
  nonempty closed bounded convex subset of a uniformly convex Banach
  space has a fixed point. Compactness of the map is unnecessary.
* **22. Nadler's contraction theorem.** A set-valued map on a complete
  metric space, with nonempty closed bounded values and Hausdorff
  distance $d_H(Tx,Ty)\leq k d(x,y)$, $k<1$, has a fixed point
  $x\in Tx$.

## Degree, continuation, and topological obstructions

For bounded open $\Omega\subset\mathbb R^n$, continuous
$F:\overline\Omega\to\mathbb R^n$, and $y\notin F(\partial\Omega)$,
the **Brouwer degree** is the integer $\deg(F,\Omega,y)$.

* **23. Degree axioms.** Degree is normalized by
  $\deg(I,\Omega,y)=1$ for $y\in\Omega$, is additive over
  disjoint open subsets containing the relevant inverse image, and
  is invariant under homotopies avoiding $y$ on the boundary.
* **24. Existence and excision.** Nonzero degree implies a solution
  $F(x)=y$ in $\Omega$. Removing a closed region containing no
  such solution leaves the degree unchanged.
* **25. Regular-value formula.** For $C^1$ maps with regular value $y$,
  $\deg(F,\Omega,y)=\sum_{F(x)=y}\operatorname{sgn}\det DF(x)$.
  Each isolated nondegenerate zero has local degree $\pm1$.
* **26. Borsuk's odd mapping theorem.** An odd continuous map on the
  closure of a bounded symmetric neighborhood of zero, with no
  boundary zero, has odd degree and therefore an interior zero.
* **27. Borsuk–Ulam theorem.** Every continuous map
  $S^n\to\mathbb R^n$ takes the same value at some antipodal pair.
  Equivalently an odd map $S^n\to\mathbb R^n$ has a zero.
* **28. Leray–Schauder degree.** For compact $K:\overline\Omega\to X$,
  $x\ne Kx$ on $\partial\Omega$, finite-dimensional approximation
  defines $\deg(I-K,\Omega,0)$. It has normalization, additivity,
  homotopy invariance, and the nonzero-degree existence property.
* **29. Linear compact-perturbation degree.** If $K$ is real linear
  compact and $I-K$ invertible, its degree on a ball about zero is
  $(-1)^m$, where $m$ is the total algebraic multiplicity of real
  eigenvalues of $K$ greater than one.
* **30. Continuation of zeros.** If a compact homotopy has no boundary
  fixed point on a bounded open set and its initial degree is nonzero,
  every parameter has a fixed point there. The connected-component
  continuation principle strengthens this to a connected set crossing
  the parameter interval under the corresponding compactness hypotheses.
* **31. Cone compression–expansion.** Let $P$ be a cone in $X$,
  $\Omega_1,\Omega_2$ bounded open with $0\in\Omega_1$,
  $\overline\Omega_1\subset\Omega_2$, and
  $T:P\cap(\overline\Omega_2\setminus\Omega_1)\to P$ compact. If
  $\|Tx\|\leq\|x\|$ on $P\cap\partial\Omega_1$ and $\|Tx\|\geq\|x\|$
  on $P\cap\partial\Omega_2$, or the reverse, then $T$ has a fixed
  point in $P\cap(\overline\Omega_2\setminus\Omega_1)$
  (Krasnosel'skii). The proof uses the fixed-point index on the retract $P$,
  and it yields positive solutions distinct from zero.

## Monotone operators and variational inequalities

An operator $A:X\rightrightarrows X^*$ is **monotone** if
$\langle a-b,x-y\rangle\geq0$ for all graph pairs $(x,a),(y,b)$.
It is **maximal monotone** if no strictly larger monotone graph contains it.
A single-valued map is **hemicontinuous** if its restrictions to line
segments are weakly continuous in the dual pairing.

* **32. Minty's range theorem.** On $H$, a monotone graph $A$ is
  maximal monotone exactly when $\operatorname{Ran}(I+\lambda A)=H$
  for one, equivalently every, $\lambda>0$.
* **33. Firm resolvents.** For maximal monotone $A$,
  $J_{\lambda A}=(I+\lambda A)^{-1}$ is everywhere defined,
  single-valued, and firmly nonexpansive:
  $\|Jx-Jy\|^2\leq\langle Jx-Jy,x-y\rangle$.
* **34. Resolvent correspondence.** Every everywhere defined firmly
  nonexpansive map $J:H\to H$ is the resolvent of a unique maximal
  monotone graph, $A=J^{-1}-I$.
* **35. Yosida approximation.**
  $A_\lambda=\lambda^{-1}(I-J_{\lambda A})$ is single-valued,
  monotone, and $1/\lambda$-Lipschitz, with
  $A_\lambda x\in A(J_{\lambda A}x)$.
  For $x\in D(A)$ it converges to the minimal-norm element of $Ax$
  as $\lambda\downarrow0$.
* **36. Graph closedness.** Maximal monotone Hilbert-space graphs are
  closed for strong convergence in one variable and weak convergence
  in the other. Their values are closed convex sets, and
  $\overline{D(A)}$ is convex.
* **37. Local boundedness.** A maximal monotone operator is locally
  bounded on the interior of its domain. Boundary behavior may be
  multivalued or unbounded.
* **38. Subdifferential maximality.** For proper lower semicontinuous
  convex $\phi:H\to(-\infty,\infty]$, its convex subdifferential
  $\partial\phi$ is maximal monotone. Its resolvent minimizes
  $\phi(y)+\|y-x\|^2/(2\lambda)$ uniquely.
* **39. Maximal monotone sums.** If $A,B$ are maximal monotone on $H$
  and $D(A)\cap\operatorname{int}D(B)\ne\varnothing$, then
  $A+B$ is maximal monotone. In particular, addition of a continuous
  everywhere-defined monotone operator preserves maximality.
* **40. Browder–Minty surjectivity.** On a reflexive Banach space,
  an everywhere-defined hemicontinuous monotone map $A:X\to X^*$ with
  $\langle Ax,x\rangle/\|x\|\to\infty$ is onto $X^*$.
  Strict monotonicity makes its inverse single-valued.
* **41. Strong monotonicity.** If $A:H\to H$ is hemicontinuous and
  $\langle Ax-Ay,x-y\rangle\geq m\|x-y\|^2$, $m>0$,
  then it is bijective and $A^{-1}$ is $1/m$-Lipschitz.
* **42. Minty identification argument.** If $x_n\rightharpoonup x$,
  $Ax_n\rightharpoonup a$ in $X^*$, and
  $\limsup\langle Ax_n,x_n\rangle\leq\langle a,x\rangle$,
  a maximal monotone graph satisfies $a\in Ax$.
  This identifies weak limits of nonlinear approximations.
* **43. Pseudomonotone surjectivity.** An everywhere-defined bounded
  coercive pseudomonotone map $A:X\to X^*$ on a reflexive Banach
  space is onto. Pseudomonotonicity means that
  $x_n\rightharpoonup x$, $\limsup\langle Ax_n,x_n-x\rangle\leq0$
  imply $\langle Ax,x-y\rangle\leq
  \liminf\langle Ax_n,x_n-y\rangle$ for every $y$.
* **44. Minty variational inequality.** On a closed convex set $C$,
  a hemicontinuous monotone $A$ satisfies
  $\langle Au-f,v-u\rangle\geq0$ for all $v\in C$ exactly when
  $\langle Av-f,v-u\rangle\geq0$ for all $v\in C$.
* **45. Existence for variational inequalities.** On a reflexive space,
  a nonempty closed bounded convex $C$ and a bounded hemicontinuous
  monotone $A$ admit a solution of that inequality. Unbounded $C$
  is allowed under coercivity relative to one point of $C$.
* **46. Normal-cone formulation.** For closed convex $C\subset H$,
  $N_C(u)=\{z:\langle z,v-u\rangle\leq0\ \forall v\in C\}$
  is maximal monotone and $J_{\lambda N_C}=P_C$.
  The variational inequality is $0\in Au-f+N_C(u)$.
* **47. Nonlinear elliptic application.** The map
  $u\mapsto-\operatorname{div}(|\nabla u|^{p-2}\nabla u)$ from
  $W_0^{1,p}$ to $W^{-1,p'}$, $1<p<\infty$, is bounded,
  hemicontinuous, coercive, and strictly monotone. Hence every datum
  in the dual has a unique weak solution.

## Accretive evolution and nonlinear contraction semigroups

A graph $A\subset X\times X$ is **accretive** if
$\|x-y\|\leq\|x-y+\lambda(a-b)\|$ for every $\lambda>0$ and
every pair of graph points. It is **$m$-accretive** if also
$\operatorname{Ran}(I+\lambda A)=X$ for every $\lambda>0$.
On Hilbert spaces this is maximal monotonicity.

* **48. Crandall–Liggett generation.** An $m$-accretive graph generates
  a strongly continuous contraction semigroup on $\overline{D(A)}$ by
  $S(t)x=\lim_{n\to\infty}(I+(t/n)A)^{-n}x$,
  uniformly for $t$ in compact intervals. It gives the mild solution
  of $u'+Au\ni0$.
* **49. Strong Hilbert-space solutions.** If $A$ is maximal monotone
  on $H$ and $u_0\in D(A)$, the generated trajectory is locally
  Lipschitz in time and satisfies $u'(t)+Au(t)\ni0$ almost everywhere.
  Its speed is bounded by the norm of the minimal section $A^0u_0$.
* **50. Stability with forcing.** Solutions of $u'+Au\ni f$ satisfy
  $\|u(t)-v(t)\|\leq\|u_0-v_0\|+
  \int_0^t\|f-g\|ds$. Integrable forcing is treated by the
  corresponding limits of implicit time discretizations.
* **51. Subgradient evolution inequality.** For $A=\partial\phi$,
  the gradient flow satisfies
  $\tfrac12\frac d{dt}\|u-v\|^2+\phi(u)\leq\phi(v)$
  for every fixed $v\in D(\phi)$, almost everywhere in time.
* **52. Energy dissipation.** Along a Hilbert-space subgradient flow,
  $\phi(u(t))+\int_s^t\|u'(r)\|^2dr=\phi(u(s))$ for $0<s<t$.
  The flow is regularizing (Brezis): for $u_0\in\overline{D(\phi)}$,
  $u(t)\in D(\partial\phi)$ for every $t>0$, $t\mapsto\phi(u(t))$ is
  nonincreasing, and $\phi(u(t))\leq\phi(v)+\|u_0-v\|^2/(2t)$ for
  every $v\in D(\phi)$; if $u_0\in D(\phi)$ then $u'\in L^2(0,T;H)$.
* **53. Strongly monotone decay.** If $A$ is $m$-strongly monotone,
  its trajectories satisfy
  $\|S(t)x-S(t)y\|\leq e^{-mt}\|x-y\|$.
  If $A$ has a zero, all trajectories converge exponentially to that
  unique equilibrium.

## Nonexpansive iteration and operator splitting

* **54. Demiclosedness principle.** If $T$ is nonexpansive on a closed
  convex subset of $H$, $x_n\rightharpoonup x$, and
  $x_n-Tx_n\to0$ strongly, then $Tx=x$.
* **55. Krasnosel'skii–Mann iteration.** For nonexpansive $T$ with a
  fixed point, $x_{n+1}=(1-\alpha_n)x_n+\alpha_nTx_n$ converges
  weakly to a fixed point in $H$ if $0<\alpha_n<1$ and
  $\sum_n\alpha_n(1-\alpha_n)=\infty$.
* **56. Proximal-point convergence.** If $A$ is maximal monotone and
  $A^{-1}(0)\ne\varnothing$, then
  $x_{n+1}=J_{\lambda_nA}x_n$, $\inf_n\lambda_n>0$,
  converges weakly to a zero of $A$.
* **57. Forward–backward splitting.** Let $A$ be maximal monotone and
  $B$ be $\beta$-cocoercive, meaning
  $\langle Bx-By,x-y\rangle\geq\beta\|Bx-By\|^2$.
  If $(A+B)^{-1}(0)\ne\varnothing$ and $0<\gamma<2\beta$,
  $x_{n+1}=J_{\gamma A}(x_n-\gamma Bx_n)$ converges weakly
  to a zero of $A+B$.
* **58. Douglas–Rachford splitting.** For maximal monotone $A,B$,
  the map $T=I-J_{\gamma A}+J_{\gamma B}(2J_{\gamma A}-I)$
  is firmly nonexpansive. If $A+B$ has a zero, its iterates converge
  weakly to a fixed point and the shadow $J_{\gamma A}x_n$
  converges weakly to a zero of $A+B$.

## Local and global bifurcation

* **59. No bifurcation at an invertible linearization.** If
  $F(\lambda,0)=0$ and $D_uF(\lambda_0,0)$ is an isomorphism,
  the implicit function theorem excludes nearby nontrivial zeros.
  Loss of invertibility is necessary for local bifurcation.
* **60. Crandall–Rabinowitz simple-eigenvalue theorem.** Suppose $F$
  is $C^2$, $F(\lambda,0)=0$, and $L=D_uF(\lambda_0,0)$ is
  Fredholm of index zero with kernel $\mathbb R\phi$.
  If $D_\lambda D_uF(\lambda_0,0)\phi\notin\operatorname{Ran}L$,
  all nearby nontrivial zeros form a smooth curve
  $(\lambda(s),s\phi+o(s))$ through $(\lambda_0,0)$.
* **61. Odd-multiplicity global alternative.** For
  $u=\lambda Ku+N(\lambda,u)$ with $K$ linear compact, $N$
  compact on bounded sets, and $N(\lambda,u)=o(\|u\|)$ locally
  uniformly in $\lambda$, an odd-algebraic-multiplicity characteristic
  value $\lambda_0$ lies on a connected continuum in the closure of
  nontrivial solutions. The continuum is unbounded or meets another
  trivial characteristic point $(\lambda_1,0)$, $\lambda_1\ne\lambda_0$.
* **62. Degree change forces bifurcation.** If the local Leray–Schauder
  degree of a trivial branch changes between nearby parameter values,
  that interval contains a bifurcation point. This detects branches
  without differentiability of a parametrization of the solution set.
* **63. Bifurcation for potential operators.** Let $F$ be a $C^2$
  gradient operator near $0$ in $H$, $F(0)=0$, and let $\lambda_0$
  be an isolated eigenvalue of finite multiplicity of the self-adjoint
  operator $DF(0)$. Then $(\lambda_0,0)$ is a bifurcation point of
  $F(x)=\lambda x$, whatever the multiplicity: for every small
  $\varepsilon>0$ there are at least two solutions with $\|x\|=\varepsilon$
  and $\lambda\to\lambda_0$ (Böhme, Marino). Without the gradient
  structure this fails: $F(x_1,x_2)=(-x_2^3,x_1^3)$ has no nontrivial solutions.
* **64. Hopf bifurcation.** Let $\dot x=F(\lambda,x)$ on $\mathbb R^n$,
  $F$ of class $C^3$ with $F(\lambda,0)=0$. Suppose $D_xF(\lambda_0,0)$
  has a simple pair of eigenvalues $\pm i\omega_0$, $\omega_0>0$, no
  other eigenvalues in $i\omega_0\mathbb Z$, and the continuation
  $\mu(\lambda)$ of $i\omega_0$ crosses transversally,
  $\operatorname{Re}\mu'(\lambda_0)\neq0$. Then a one-parameter family
  of nonconstant periodic orbits with periods near $2\pi/\omega_0$ and
  amplitudes tending to zero emanates from $(\lambda_0,0)$, and near
  $(\lambda_0,0)$ it contains all small periodic orbits with such periods.
  The theorem extends to parabolic evolution equations (Crandall–Rabinowitz).

## Reference guide

Deimling, Zeidler, Nirenberg, and Berger overlap on nonlinear calculus,
compactness, and degree. Granas–Dugundji and Goebel–Kirk supply the
topological and metric fixed-point viewpoints. Showalter, Brezis, Barbu,
Bauschke–Combettes, and Simons give the monotone and accretive core,
with different emphasis on PDE, evolution, and optimization. Chow–Hale,
Kielhöfer, and Buffoni–Toland develop the bifurcation theory, including
Hopf and variational bifurcation. The selection
retains standard usable hypotheses rather than cataloguing every generalized
degree, condensing map, or monotonicity qualification.

Local source copies consulted:

* [Granas–Dugundji, *Fixed Point Theory*](References/GranasDugundji2003FixedPointTheory-SpringerMonogMath.pdf).
* [Zeidler, *Applied Functional Analysis: Main Principles and Their Applications*](References/Zeidler1995AppliedFunctionalAnalysisMainPrinciplesApplications-SpringerAMS109.pdf).
* [Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*](References/Brezis2011FunctionalAnalysisSobolevSpacesPartialDifferentialEquations-SpringerUTX.pdf).
* [Barbu, *Nonlinear Differential Equations of Monotone Types in Banach Spaces*](References/Barbu2010NonlinearDifferentialEquationsMonotoneTypesBanachSpaces-Springer.SMM.pdf).
* [Bauschke–Combettes, *Convex Analysis and Monotone Operator Theory in Hilbert Spaces*](References/BauschkeCombettes2017ConvexAnalysisMonotoneOperatorTheoryHilbertSpace2ndEd-SpringerCMSBM.pdf).
* [Kielhöfer, *Bifurcation Theory*](References/Kielhofer2012BifurcationTheory2ndEd-Springer.AMS156.pdf).
