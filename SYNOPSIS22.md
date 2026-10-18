# Synopsis: Unbounded operators, spectral theory, and mathematical physics

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects the recurring core of Section 22 of
[CKMA-bib.md](CKMA-bib.md): domains and
self-adjointness, spectral measures, quadratic forms, perturbations,
Schrödinger operators, one-dimensional spectral theory, and scattering.
Specialist many-body, random, semiclassical, and inverse theories extend
this core; their full hypotheses and techniques are not compressed into
the elementary statements below.

Throughout, $H$ is a complex Hilbert space with inner product linear in
the first variable. An **unbounded operator** includes its linear domain
$D(A)\subset H$. It is **closed** if its graph is closed, **closable** if
its graph closure is a graph, **symmetric** if
$\langle Au,v\rangle=\langle u,Av\rangle$ on $D(A)$, and
**self-adjoint** if $A=A^*$ including equality of domains. A **core** is
a subspace dense in $D(A)$ for the graph norm $\|u\|+\|Au\|$.

## Adjoints, extensions, and unitary dynamics

* **1. Adjoint and closure.** Every densely defined $A$ has a closed
  adjoint. It is closable exactly when $D(A^*)$ is dense, and then
  $\overline A=A^{**}$. Every densely defined symmetric operator is closable.
* **2. Graph norm criterion.** $A$ is closed exactly when $D(A)$ is
  complete in its graph norm. A bounded perturbation of a closed operator
  is closed on the same domain.
* **3. Nonreal resolvent estimate.** For symmetric $A$ and nonreal $z$,
  $\|(A-z)u\|\geq|\operatorname{Im}z|\|u\|$. If $A$ is self-adjoint,
  $z$ is in its resolvent and $\|(A-z)^{-1}\|\leq|\operatorname{Im}z|^{-1}$.
* **4. Self-adjointness by range.** A densely defined symmetric operator
  is self-adjoint exactly when $\operatorname{ran}(A+i)=
  \operatorname{ran}(A-i)=H$. It is essentially self-adjoint exactly when
  both these ranges are dense.
* **5. von Neumann extension theorem.** A closed densely defined symmetric
  $A$ has self-adjoint extensions exactly when its deficiency indices
  $n_\pm=\dim\ker(A^*\mp i)$ agree. Its self-adjoint extensions are
  parametrized by unitaries between the two deficiency spaces.
* **6. Cayley correspondence.** For self-adjoint $A$,
  $U=(A-i)(A+i)^{-1}$ is unitary and has no eigenvector with eigenvalue
  one. Conversely every such unitary determines a unique self-adjoint
  operator by the inverse Cayley transform.
* **7. Stone theorem.** Every strongly continuous unitary group is
  $U(t)=e^{-itA}$ for a unique self-adjoint $A$. Its differentiability
  domain is $D(A)$, and $U'(0)u=-iAu$ there.
* **8. Analytic vector criterion.** A symmetric operator with a dense
  invariant domain of analytic vectors is essentially self-adjoint
  (Nelson). An analytic vector satisfies
  $\sum_n t^n\|A^nu\|/n!<\infty$ for some $t>0$.

## Spectral measures and functional calculus

A **projection-valued measure** $E$ is countably additive in the strong
operator topology, with orthogonal projections as values and $E(\mathbb R)=I$.
Set $\mu_u(B)=\langle E(B)u,u\rangle$. The scalar spectral measures
decompose into atomic, absolutely continuous, and singular continuous parts.

* **9. Unbounded spectral theorem.** Every self-adjoint operator has a
  unique representation
  $$A=\int_\mathbb R\lambda\,dE(\lambda),\qquad
    D(A)=\left\{u:\int\lambda^2\,d\mu_u(\lambda)<\infty\right\}.$$
  The support of $E$ is $\sigma(A)\subset\mathbb R$.
* **10. Measurable functional calculus.** For a Borel function $f$,
  $f(A)$ has domain $\{u:\int|f|^2\,d\mu_u<\infty\}$ and
  $\|f(A)u\|^2=\int|f|^2\,d\mu_u$. Real-valued $f$ gives a
  self-adjoint operator; algebraic identities are interpreted on their
  appropriate domains.
* **11. Multiplication representation.** A self-adjoint operator on a
  separable Hilbert space is an orthogonal sum of multiplication operators
  by the real coordinate on scalar $L^2$ spaces. Spectral multiplicity
  records how many cyclic components occur.
* **12. Spectral type decomposition.**
  $H=H_{\rm pp}\oplus H_{\rm ac}\oplus H_{\rm sc}$ reduces $A$.
  The first space is the closed span of eigenvectors; the other two are
  characterized by absolute continuity and singular continuity of $\mu_u$.
* **13. Spectral projection at an eigenvalue.**
  $E(\{\lambda\})H=\ker(A-\lambda)$. Spectral projections commute
  with bounded Borel functions of $A$ and preserve $D(A)$.
* **14. Resolvent norm.** For self-adjoint $A$,
  $\|(A-z)^{-1}\|=\operatorname{dist}(z,\sigma(A))^{-1}$ off its
  spectrum. Spectral distance therefore controls the resolvent exactly.
* **15. Stone inversion formula.** If $\mu_u(\{a,b\})=0$, then
  $$\mu_u((a,b))=\lim_{\varepsilon\downarrow0}\frac1\pi
    \int_a^b\operatorname{Im}\langle(A-\lambda-i\varepsilon)^{-1}u,u\rangle
       \,d\lambda.$$
  At atoms the symmetric limiting formula assigns half of each endpoint mass.
* **16. Strong resolvent convergence.** If self-adjoint $A_n,A$ satisfy
  $(A_n-z)^{-1}\to(A-z)^{-1}$ strongly for one nonreal $z$, this holds
  for every nonreal $z$. Then $f(A_n)\to f(A)$ strongly for every
  bounded continuous $f$.
* **17. Norm resolvent convergence.** Norm convergence of one nonreal
  resolvent gives norm convergence of $f(A_n)$ to $f(A)$ for $f\in C_0(\mathbb R)$.
  Isolated finite spectral clusters persist, with convergent spectral
  projections and stable total multiplicity.
* **18. Convergence of unitary dynamics.** Strong resolvent convergence
  implies $e^{-itA_n}u\to e^{-itA}u$ uniformly for $t$ in compact
  intervals, for each $u\in H$.

## Closed quadratic forms and self-adjoint realizations

A densely defined symmetric form $q$ is **lower semibounded** if
$q[u]\geq-c\|u\|^2$. It is **closed** if its domain $Q(q)$ is complete
for $(q[u]+(c+1)\|u\|^2)^{1/2}$, and **closable** if it has a closed
extension obtained by completing its graph in this form norm.

* **19. First representation theorem.** Every densely defined closed
  lower-semibounded form determines a unique self-adjoint lower-semibounded
  $A$ with $D(A)\subset Q(q)$ and $q(u,v)=\langle Au,v\rangle$
  for $u\in D(A)$, $v\in Q(q)$.
* **20. Second representation theorem.** If $A\geq0$ corresponds to $q$,
  then $Q(q)=D(A^{1/2})$ and
  $q(u,v)=\langle A^{1/2}u,A^{1/2}v\rangle$. The operator domain
  is generally smaller than the form domain.
* **21. Friedrichs extension.** Every densely defined lower-semibounded
  symmetric operator has a canonical self-adjoint extension obtained by
  closing its quadratic form. Its form domain is the completion of the
  original domain in the form norm.
* **22. KLMN theorem.** If $q\geq0$ is closed and a symmetric form $b$
  on $Q(q)$ satisfies $|b[u]|\leq a q[u]+c\|u\|^2$ with $a<1$,
  then $q+b$ is closed and lower semibounded on the same form domain.
* **23. Monotone convergence of forms.** An increasing sequence of
  nonnegative closed forms has a closed supremum form on the vectors
  where the supremum is finite. If that domain is dense, the associated
  operators converge in the strong resolvent sense.
* **24. Dirichlet and Neumann Laplacians.** On a bounded Lipschitz domain,
  the energy $\int_\Omega|\nabla u|^2$ on $H_0^1(\Omega)$ and
  $H^1(\Omega)$ defines the nonnegative Dirichlet and Neumann Laplacians,
  respectively. Their boundary conditions arise from the form domains.
* **25. Compact resolvent criterion.** A lower-semibounded operator has
  compact resolvent exactly when its form domain embeds compactly in $H$.
  Then its eigenvectors form an orthonormal basis and eigenvalues tend to
  $+\infty$, with multiplicity, in infinite dimension.

## Variational principles and essential spectrum

The **discrete spectrum** consists of isolated eigenvalues of finite
multiplicity; the **essential spectrum** is the rest of the spectrum.
For self-adjoint operators this agrees with the Fredholm definition.

* **26. Rayleigh principle.** For lower-semibounded $A$,
  $\inf\sigma(A)=\inf_{u\in Q(q),\|u\|=1}q[u]$. Attainment gives
  an eigenvector at the spectral bottom.
* **27. Min–max principle.** The numbers
  $$\lambda_n=\inf_{\substack{L\subset Q(q)\\\dim L=n}}
                 \sup_{0\ne u\in L}\frac{q[u]}{\|u\|^2}$$
  enumerate the eigenvalues below $\inf\sigma_{\rm ess}(A)$, with
  multiplicity, and equal that threshold once there are fewer than $n$
  such eigenvalues. The threshold is $+\infty$ for compact resolvent.
* **28. Form comparison and bracketing.** Enlarging a form domain or
  decreasing a form lowers all min–max values. Hence Dirichlet eigenvalues
  decrease as the domain grows, and if a bounded domain $\Omega$ is split by
  interior interfaces into finitely many Lipschitz pieces $\Omega_k$, then
  in the min–max ordering
  $\bigoplus_k(-\Delta^N_{\Omega_k})\leq-\Delta^N_\Omega\leq
  -\Delta^D_\Omega\leq\bigoplus_k(-\Delta^D_{\Omega_k})$
  (Dirichlet–Neumann bracketing, the route to the Weyl law).
* **29. Weyl criterion.** $\lambda\in\sigma(A)$ exactly when unit
  $u_n\in D(A)$ satisfy $(A-\lambda)u_n\to0$. It belongs to the
  essential spectrum exactly when such vectors can be chosen weakly null,
  or orthonormal.
* **30. Weyl stability theorem.** If two self-adjoint operators have
  compact resolvent difference at a common nonreal point, their essential
  spectra coincide. Relative compactness of a symmetric perturbation is
  a standard sufficient condition.
* **31. Weyl law on bounded domains.** For a bounded smooth domain in
  $\mathbb R^d$, both Dirichlet and Neumann counting functions satisfy
  $N(\Lambda)\sim(2\pi)^{-d}\omega_d|\Omega|\Lambda^{d/2}$.

## Perturbation theory

$B$ is **$A$-bounded** if $D(A)\subset D(B)$ and
$\|Bu\|\leq a\|Au\|+b\|u\|$. It is **$A$-compact** if it is compact
from the graph-norm domain to $H$. A holomorphic family of **type (A)**
has a common domain and holomorphic $A(z)u$ there; a **type (B)** family
is obtained from closed sectorial forms with common domain and holomorphic
form values.

* **32. Kato–Rellich theorem.** If $A$ is self-adjoint and $B$ symmetric
  with $A$-bound less than one, $A+B$ is self-adjoint on $D(A)$ and
  essentially self-adjoint on every core of $A$.
* **33. Resolvent perturbation identity.** On the common resolvent set,
  $(A+B-z)^{-1}-(A-z)^{-1}=-(A+B-z)^{-1}B(A-z)^{-1}$,
  whenever the compositions are defined, in particular for bounded $B$.
  A small norm of $B(A-z)^{-1}$ also gives a convergent inverse series.
* **34. Analytic isolated eigenvalues.** For a holomorphic type (A) or
  type (B) family, an isolated spectral cluster of finite multiplicity has
  a locally holomorphic Riesz projection. A simple isolated eigenvalue
  and its eigenvector can be chosen holomorphically locally.
* **35. Rellich theorem.** For a real-analytic self-adjoint family of
  type (A), isolated finite-multiplicity eigenvalues admit locally
  real-analytic eigenvalue branches and orthonormal eigenvector branches,
  including through crossings.
* **36. Feynman–Hellmann formula.** For a differentiable normalized
  simple eigenpair $A(t)u(t)=\lambda(t)u(t)$ with common operator
  domain, $\lambda'(t)=\langle A'(t)u(t),u(t)\rangle$.
* **37. Schur complement reduction.** For a block operator with bounded
  off-diagonal entries, if $D-z$ is invertible, invertibility of
  $\begin{pmatrix}A-z&B\\C&D-z\end{pmatrix}$ is equivalent to that of
  $A-z-B(D-z)^{-1}C$ on $D(A)$. This is the basic Feshbach reduction.
* **38. Birman–Schwinger principle.** If $H_0\geq0$, $V\geq0$, and
  $K_E=V^{1/2}(H_0+E)^{-1}V^{1/2}$ is a well-defined compact operator,
  then $-E<0$ is an eigenvalue of the form sum $H_0-V$ exactly when
  $1$ is an eigenvalue of $K_E$, with the same multiplicity.
  Moreover the number of eigenvalues of $H_0-V$ below $-E$ equals the
  number of eigenvalues of $K_E$ greater than $1$.
* **39. Trotter product formula.** If $A$ and $B$ are self-adjoint and
  $A+B$ is essentially self-adjoint on $D(A)\cap D(B)$, then
  $e^{it\overline{(A+B)}}=\operatorname{s-lim}_{n\to\infty}
  (e^{itA/n}e^{itB/n})^n$. For $A,B$ bounded below the analogous
  formula holds for $e^{-t(A\dotplus B)}$ with the form sum (Kato); this is
  the operator basis of the Feynman–Kac formula.

## Schrödinger operators and eigenvalue estimates

Write $H_V=-\Delta+V$ on $L^2(\mathbb R^d)$, with form realization when
needed, and $V_- =\max(-V,0)$. The form statements assume $V_+$ is
locally integrable and the negative part satisfies the stated relative
form bounds, so the form domain is dense and the operator is well defined.

* **40. Free Laplacian.** $-\Delta$ is self-adjoint on $H^2(\mathbb R^d)$,
  essentially self-adjoint on $C_c^\infty$, and unitarily equivalent by
  Fourier transformation to multiplication by $|\xi|^2$. Its spectrum
  is purely absolutely continuous and equals $[0,\infty)$.
* **41. Bounded potentials.** For real bounded $V$, $H_V$ is self-adjoint
  on $H^2$ and essentially self-adjoint on $C_c^\infty$.
* **42. Kato's theorem and the hydrogen atom.** On $\mathbb R^3$, every real
  $V\in L^2+L^\infty$ is $-\Delta$-bounded with relative bound zero, so
  $-\Delta+V$ is self-adjoint on $H^2$ and essentially self-adjoint on
  $C_c^\infty$; the same holds for atomic and molecular many-body
  Hamiltonians. For $-\Delta-c/|x|$, $c>0$, the negative spectrum consists of
  the eigenvalues $-c^2/(4n^2)$ with multiplicity $n^2$, $n\geq1$, and
  $\sigma_{\rm ess}=[0,\infty)$.
* **43. Decaying potentials and essential spectrum.** If $V$ is real,
  bounded, and tends to zero at infinity, multiplication by $V$ is
  relatively compact with respect to $-\Delta$ and
  $\sigma_{\rm ess}(H_V)=[0,\infty)$. Negative eigenvalues are discrete
  and can accumulate only at zero.
* **44. HVZ theorem.** For an $N$-body Hamiltonian with the centre of mass
  removed and pair potentials relatively compact with respect to the
  Laplacian on $\mathbb R^3$ (e.g. in $L^2+L^\infty_\varepsilon$), the
  essential spectrum is $[\Sigma,\infty)$, where $\Sigma$ is the minimum of
  the bottoms of the spectra of the cluster Hamiltonians over decompositions
  into at least two clusters (Hunziker, van Winter, Zhislin).
* **45. Confining potentials.** If $V$ is locally bounded, bounded below,
  and tends to $+\infty$ at infinity, $H_V$ has compact resolvent. For the
  harmonic oscillator $-\Delta+|x|^2$ on $\mathbb R^d$ the eigenvalues are
  $2|\alpha|+d$, $\alpha\in\mathbb N_0^d$, with Hermite eigenfunctions.
* **46. Cwikel–Lieb–Rozenblum bound.** For $d\geq3$ and
  $V_-\in L^{d/2}$,
  $N(H_V<0)\leq C_d\int V_-^{d/2}$, with multiplicities.
* **47. Lieb–Thirring inequality.** Negative eigenvalues satisfy
  $\sum_j|\lambda_j|^\gamma\leq L_{\gamma,d}\int V_-^{\gamma+d/2}$
  for $\gamma\geq1/2$ in dimension one, $\gamma>0$ in dimension two,
  and $\gamma\geq0$ in dimensions at least three. At $\gamma=0$
  the left side counts negative eigenvalues.
* **48. Positivity and the ground state.** For real bounded $V$ on
  $\mathbb R^d$, $e^{-tH_V}$ is positivity improving for $t>0$.
  If the bottom of the spectrum is an eigenvalue, it is simple and
  has a strictly positive eigenfunction.
* **49. Agmon decay, a basic case.** For real bounded $V$, an
  $L^2$ eigenfunction of energy $E<\liminf_{|x|\to\infty}V(x)$
  satisfies $e^{a|x|}u\in L^2$ whenever
  $0<a^2<\liminf V-E$. Weighted energy estimates give analogous
  decay in the Agmon metric for more general potentials.

## Sturm–Liouville operators and quantum graphs

For the one-dimensional expression $\tau u=-u''+Vu$ with real
$V\in L^1_{\rm loc}(a,b)$, the maximal domain consists of $u,u'$
locally absolutely continuous with $u,\tau u\in L^2$. A singular
endpoint is **limit circle** if all solutions for nonreal spectral
parameter are square integrable near it, and **limit point** otherwise.

* **50. Green identity.** On a regular finite interval,
  $\langle\tau u,v\rangle-\langle u,\tau v\rangle
  =[u\overline{v'}-u'\overline v]_a^b$. Self-adjoint boundary
  conditions are precisely maximal subspaces on which this boundary
  form vanishes.
* **51. Separated boundary conditions.** Real separated Dirichlet,
  Neumann, or Robin conditions at regular endpoints give self-adjoint
  operators with compact resolvent, simple eigenvalues, and complete
  orthonormal eigenfunctions.
* **52. Weyl alternative.** At each endpoint the limit-point/limit-circle
  classification is independent of the nonreal parameter. A limit-circle
  endpoint requires one self-adjoint boundary condition; a limit-point
  endpoint requires none. The minimal operator is essentially self-adjoint
  exactly when both endpoints are limit point.
* **53. Sturm oscillation theorem.** The $n$th eigenfunction for regular
  separated boundary conditions has exactly $n-1$ zeros in $(a,b)$,
  counting eigenvalues increasingly from $n=1$.
* **54. Interlacing.** Changing one separated endpoint condition from
  Dirichlet to Neumann gives interlacing eigenvalues. More generally the
  spectra for two distinct separated conditions at one endpoint interlace
  while the other condition is fixed.
* **55. Weyl–Titchmarsh function.** On a half-line with a regular left
  endpoint and limit-point infinity, the square-integrable solution
  normalized by $u(z,a)=1$ has $m(z)=u'(z,a)$ holomorphic in the upper
  half-plane with $\operatorname{Im}m(z)>0$. Its Herglotz measure
  determines the scalar spectral representation, and $m$ determines $V$
  (Borg–Marchenko uniqueness).
* **56. Kirchhoff quantum graphs.** On a finite compact metric graph,
  the edgewise $-u''$ with continuity at vertices and sum of outward
  derivatives zero is self-adjoint and nonnegative, with compact resolvent.
  Its form is $\sum_e\int_e|u'|^2$ on continuous edgewise $H^1$ functions.
* **57. Graph Weyl law.** For a compact metric graph of total edge length
  $L$, the eigenvalue counting function is
  $N(\Lambda)\sim L\sqrt\Lambda/\pi$. Finite changes among
  self-adjoint vertex conditions do not change this leading term.

## Scattering, spectral dynamics, and stability

For self-adjoint $A,A_0$, the **wave operators** are
$W_\pm=\operatorname{s-lim}_{t\to\pm\infty}e^{itA}e^{-itA_0}P_{\rm ac}(A_0)$,
when they exist. They are **complete** if their ranges equal $H_{\rm ac}(A)$.

* **58. Intertwining and isometry.** Existing wave operators are
  isometries on $H_{\rm ac}(A_0)$ and intertwine the spectral calculi:
  $f(A)W_\pm=W_\pm f(A_0)$ for bounded Borel $f$. Their ranges lie
  in $H_{\rm ac}(A)$.
* **59. Cook criterion.** If $A=A_0+V$ with bounded self-adjoint $V$,
  and $\int_0^\infty\|Ve^{-itA_0}u\|\,dt<\infty$ on a dense
  subset of $H_{\rm ac}(A_0)$, then $W_+$ exists. The analogous
  negative-time condition gives $W_-$.
* **60. Short-range Schrödinger scattering.** If $V$ is real with
  $|V(x)|\leq C(1+|x|)^{-1-\varepsilon}$, $\varepsilon>0$, then for
  $H_V=-\Delta+V$ on $\mathbb R^d$ the weighted resolvents
  $\langle x\rangle^{-s}(H_V-\lambda\mp i0)^{-1}\langle x\rangle^{-s}$,
  $s>1/2$, exist locally uniformly on $(0,\infty)$, where there are no
  embedded eigenvalues (Kato), by the limiting absorption principle. Consequently
  $\sigma_{\rm sc}(H_V)=\varnothing$, and $W_\pm(H_V,-\Delta)$ exist and
  are complete (Agmon–Kato–Kuroda; Enss for a time-dependent proof). Mourre's
  commutator estimate gives the abstract form of this method.
* **61. Kato–Rosenblum and Birman–Kuroda theorems.** A trace-class self-adjoint perturbation
  preserves the absolutely continuous part up to unitary equivalence:
  if $A-A_0$ is bounded trace class, both wave operators exist and are
  complete. More generally it suffices that
  $(A-z)^{-1}-(A_0-z)^{-1}$ be trace class for one nonreal $z$
  (Birman–Kuroda). Singular spectral parts need not be preserved.
* **62. Scattering operator.** If both wave operators are complete,
  $S=W_+^*W_-$ is unitary on $H_{\rm ac}(A_0)$ and commutes with
  its spectral projections. In a spectral representation it decomposes
  into scattering matrices acting on multiplicity fibers.
* **63. RAGE theorem.** A vector $u$ belongs to the continuous spectral
  subspace exactly when for every compact $C$,
  $T^{-1}\int_0^T\|Ce^{-itA}u\|^2dt\to0$. A vector belongs to the
  pure point subspace exactly when its unitary orbit is relatively compact
  ([Teschl, Chapter 5](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf)).
* **64. Absolutely continuous local decay.** If $u\in H_{\rm ac}(A)$,
  then $Ce^{-itA}u\to0$ in norm for every compact $C$ as
  $|t|\to\infty$. Scalar matrix coefficients tend to zero by the
  Riemann–Lebesgue lemma, and compactness upgrades weak decay to norm decay.

## Nonnormal spectra and pseudospectra

For a closed operator with nonempty resolvent, its **$\varepsilon$-pseudospectrum**
is $\sigma_\varepsilon(A)=\sigma(A)\cup
\{z\in\rho(A):\|(A-z)^{-1}\|>\varepsilon^{-1}\}$.

* **65. Perturbation characterization.** On Hilbert space,
  $\sigma_\varepsilon(A)=\bigcup_{\|B\|<\varepsilon}\sigma(A+B)$,
  with bounded perturbations on $D(A)$. For normal $A$, it is precisely
  the open $\varepsilon$-neighborhood of the spectrum.
* **66. Bauer–Fike bound.** If a finite-dimensional matrix is diagonalized
  as $A=VDV^{-1}$, every eigenvalue of $A+B$ lies within
  $\|V\|\|V^{-1}\|\|B\|$ of $\sigma(A)$. Poor conditioning permits
  much greater spectral movement than for normal matrices.
* **67. Numerical range bound.** For bounded $A$, its spectrum lies in
  the closure of $W(A)=\{\langle Au,u\rangle:\|u\|=1\}$, and
  $\|(A-z)^{-1}\|\leq\operatorname{dist}(z,W(A))^{-1}$ outside
  that closure.
* **68. Resolvent and transient growth.** If $A$ generates a semigroup
  with $\|e^{tA}\|\leq M e^{\omega t}$, then
  $\|(z-A)^{-1}\|\leq M/(\operatorname{Re}z-\omega)$ for
  $\operatorname{Re}z>\omega$. Large resolvent norms therefore force
  large possible growth constants even when the spectrum is stable.
  Conversely, for an $N\times N$ matrix with Kreiss constant
  $\mathcal K=\sup_{\operatorname{Re}z>0}\operatorname{Re}z\,\|(z-A)^{-1}\|$,
  one has $\mathcal K\leq\sup_{t\geq0}\|e^{tA}\|\leq eN\mathcal K$
  (Kreiss matrix theorem).

## Reference guide

Kato supplies the closed-operator, form, extension, and perturbation theory.
Borthwick's general spectral course independently treats the spectral theorem,
variational arguments, differential operators, Schrödinger operators, and
graphs. Hall gives the self-adjointness and unitary-dynamics foundation from
the mathematical quantum-mechanics viewpoint. These themes recur throughout
Reed–Simon, Schmüdgen, Weidmann, Davies, Teschl, and Hislop–Sigal.
Frank–Laptev–Weidl develops the eigenvalue estimates. Reed–Simon III–IV,
Cycon–Froese–Kirsch–Simon, and Hislop–Sigal treat the HVZ theorem, limiting
absorption, and short-range scattering; the scattering and
nonnormal sections select foundational results shared by the relevant
monographs rather than a comprehensive scattering or resonance theory.

Teschl's [author-hosted online edition](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf),
Chapter 5, was also consulted for the spectral-dynamics formulations.

Local source copies consulted:

* [Kato, Perturbation Theory for Linear Operators](References/Kato1995PerturbationTheoryLinearOperators-SpringerClassicsMath132.pdf).
* [Borthwick, Spectral Theory: Basic Concepts and Applications](References/Borthwick2020SpectralTheory-Springer.GTM284.pdf).
* [Hall, Quantum Theory for Mathematicians](References/Hall2013QuantumTheoryMathematicians-SpringerGTM.pdf).
* [Frank–Laptev–Weidl, Schrödinger Operators: Eigenvalues and Lieb–Thirring Inequalities](References/FrankLaptevWeidl2023SchrodingerOperatorsEigenvaluesLiebThirringInequalities-Cambridge.StudAM200.pdf).
* [Davies, Linear Operators and Their Spectra](References/Davies2007LinearOperatorsSpectra-CambridgeStudiesAM106.pdf).
