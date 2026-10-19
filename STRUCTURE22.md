# Structure 22: Unbounded operators, spectral theory, and mathematical physics

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS22.md); [bibliographical scope](CKMA-bib.md#ckma-22); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.InnerProductSpace.LinearPMap`, `Mathlib.Topology.Algebra.Module.LinearPMap`, `Mathlib.Analysis.InnerProductSpace.LaxMilgram`, `Mathlib.Analysis.InnerProductSpace.Laplacian`, `Mathlib.Analysis.Distribution.FourierMultiplier`.

**Namespaces.** `LinearPMap`, `ContinuousLinearMap`, `Submodule`, `InnerProductSpace`, `Laplacian`, `SchwartzMap`, `TemperedDistribution`, and `IsCoercive`.

## Adjoints, extensions, and unitary dynamics

[Mathematical scope](SYNOPSIS22.md#adjoints-extensions-and-unitary-dynamics).

### Mathlib

**Partially defined operators.**

A partially defined linear map carries a domain. It is closed when its graph is closed, and closable when the closure of the graph is still a graph. A closable map has a closure, the smallest closed extension, whose graph is the closure of the graph; a subspace is a core when the closure of the restriction is the closure of the map (`LinearPMap.HasCore`), and the original domain is a core of the closure. For injective maps, closedness and closability pass to the inverse, and the closure of the inverse is the inverse of the closure (`Topology/Algebra/Module/LinearPMap.lean`).

On inner product spaces, \(T\) is a formal adjoint of \(S\) when \(\langle Tx, y\rangle = \langle x, Sy\rangle\) for \(x\) in the domain of \(T\) and \(y\) in the domain of \(S\). The adjoint \(T^\dagger\) is defined for every partially defined map. Its domain consists of those vectors \(y\) for which \(z\mapsto\langle y, Tz\rangle\) is continuous on the domain of \(T\). If the domain of \(T\) is dense and the source is a Hilbert space, the adjoint is the Riesz representative of that functional: it is a formal adjoint, it contains every formal adjoint, and its graph is closed. If the domain is not dense, the adjoint is defined to be the zero map on its domain. A self-adjoint partially defined operator is closed (`Analysis/InnerProductSpace/LinearPMap.lean`).

The bounded adjoint and this adjoint agree when the bounded operator is viewed as a partially defined operator with dense domain.

### TauCeti

**Adjoints and self-adjointness.** The double adjoint of a closed subspace of \(E\times F\) is itself, and the adjoint of a closed densely defined operator is densely defined (`Submodule.adjoint_adjoint`, `LinearPMap.dense_adjoint_domain`, [double adjoints](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/LinearPMap/SubmoduleAdjoint.lean)). A real form of the basic self-adjointness criterion is proved over any `RCLike` field: for symmetric \(B\) and \(\mu\neq0\), the “pair shift” \((x,y)\mapsto(\mu x-By,\,Bx+\mu y)\), which is \(\mu+iB\) on the complexification written in real coordinates, is surjective exactly when \(B\) is self-adjoint (`LinearPMap.IsFormalAdjoint.isSelfAdjoint_iff_surjective_pairShift`, [pair shift](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/LinearPMap/PairShift.lean)). Adding a bounded self-adjoint operator preserves self-adjointness, and so does unitary conjugation ([constructions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/LinearPMap/Constructions.lean)).

Stone's theorem is proved: a self-adjoint partially defined operator on a complex Hilbert space gives a unique strongly continuous unitary group whose complex generator is \(iA\); conversely the unitary-group generator is skew-self-adjoint ([unbounded Stone theorem](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Semigroups/Group/Stone/Unbounded.lean), [unitary generators](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Semigroups/Group/Stone/Basic.lean)). The general closed-generator, resolvent, and generation results are described in Section 24.

For unbounded operators TauCeti also supplies the resolvent calculus that Mathlib's Banach-algebra resolvent cannot express. A bounded resolvent of a partially defined operator at \(\lambda\) is defined, with the resolvent set and the resolvent; the resolvent set is open and the resolvent is analytic in operator norm, by the Neumann series ([resolvent set](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean), [analyticity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Operator/Resolvent/Analytic.lean)). For a self-adjoint operator every nonreal \(c\) is in the resolvent set: \(c-A\) is bijective with bounded inverse, by the identity \(\|(c-A)x\|^2=(\operatorname{Im}c)^2\|x\|^2+\|(\operatorname{Re}c-A)x\|^2\) and the absence of nonreal eigenvalues ([self-adjoint shifts](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjoint.lean)). More precisely, a shift \(z-A\) bounded below by \(c\lVert x\rVert\) gives a resolvent point with \(\lVert R(z)\rVert\le c^{-1}\), so \(\lVert R(z)\rVert\le|\operatorname{Im}z|^{-1}\), the spectrum is real, and \(R(z)^\ast=R(\bar z)\); conversely, if \(\sigma(A)\) avoids \((c-s,c+s)\) then \(\lVert R(c)\rVert\le s^{-1}\) ([resolvent bounds](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/LinearPMap/Resolvent.lean), [spectral gaps](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralGap.lean)). The Cayley transform \((A-i)(A+i)^{-1}\) of a symmetric operator with \(-i\) in the resolvent set is an isometry, and for self-adjoint \(A\) it is unitary (`IsSelfAdjoint.cayley_mem_unitary`), so the continuous functional calculus of the unitary applies ([Cayley transform](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/LinearPMap/Cayley.lean)). A subspace whose orthogonal projection preserves the domain and which is invariant together with its complement reduces \(A\), and the reduced part inherits density of the domain, closedness, symmetry and self-adjointness ([reducing subspaces](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/LinearPMap/Reducing.lean)). The Cayley transform determines the operator: the graph of \(A\) is \(\{(x-Ux,\,i(x+Ux))\}\), so \(1\) is not an eigenvalue of \(U\) (`LinearPMap.mem_graph_iff_exists_cayley`, `LinearPMap.cayley_apply_eq_self_iff`, [Cayley transform, algebraic part](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Operator/LinearPMap/Cayley.lean)). The converse, that every unitary without eigenvalue \(1\) is the Cayley transform of a self-adjoint operator, is not stated.

**Synopsis entries.** Covered: 22.3, 22.7 (TauCeti). Partly covered: 22.1 (closed adjoint in Mathlib, dense adjoint domain for closed densely defined operators in TauCeti; \(\overline A=A^{\ast\ast}\) and closability of symmetric operators are not stated), 22.4 (the real pair-shift form of the range criterion for self-adjointness, TauCeti; essential self-adjointness is absent), 22.6 (unitarity of the Cayley transform, absence of the eigenvalue \(1\), and recovery of \(A\), TauCeti; the inverse Cayley transform of an arbitrary such unitary is absent). Not covered: 22.2, 22.5, 22.69, 22.70, 22.8.

## Spectral measures and functional calculus

[Mathematical scope](SYNOPSIS22.md#spectral-measures-and-functional-calculus).

### TauCeti

For a strongly continuous unitary representation of a locally compact abelian group, each diagonal matrix coefficient is the Fourier–Stieltjes transform of a finite measure on the dual group, the cyclic form of the SNAG theorem ([cyclic SNAG theorem](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Pontryagin/StronglyContinuous.lean); see Section 20). With the scalar spectral measures of bounded normal operators (Section 21) and the Cayley transform, these are the ingredients of the unbounded spectral theorem, which itself is not formalized.

For a nonnegative measurable multiplier \(m\), multiplication by \(-m\) on \(L^p(\mu)\), \(1\le p<\infty\), with its exact maximal domain, generates \(e^{-tm}\), and its resolvent is multiplication by \((\lambda+m)^{-1}\) ([multiplication generators](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Semigroups/Multiplication/MeasureLp/Generator.lean)); this is supporting material for the multiplication representation, not that representation itself.

For a self-adjoint operator, \(\lVert R(z)\rVert\le|\operatorname{Im}z|^{-1}\) for nonreal \(z\), and if \(\sigma(A)\) avoids \((c-s,c+s)\) then \(\lVert R(c)\rVert\le s^{-1}\) (see the previous heading); this is the upper bound in result 14 at real points.

**Synopsis entries.** Partly covered: 22.14 (upper bound \(\lVert R(c)\rVert\le\operatorname{dist}(c,\sigma(A))^{-1}\) at real \(c\) and \(\lVert R(z)\rVert\le|\operatorname{Im}z|^{-1}\), TauCeti; equality is absent). Not covered: 22.9–22.13, 22.15–22.18.

## Closed quadratic forms and self-adjoint realizations

[Mathematical scope](SYNOPSIS22.md#closed-quadratic-forms-and-self-adjoint-realizations).

### Mathlib

**Lax–Milgram.**

Let \(V\) be a real Hilbert space, and let \(B\) be a bounded bilinear form \(V\times V\to\mathbb{R}\). The form is coercive when some constant \(C>0\) satisfies \(C\lVert u\rVert^2\le B(u,u)\) for every \(u\). After the Riesz identification \(V^*\cong V\), the operator \(B^\sharp\) defined by \(\langle B^\sharp v,w\rangle=B(v,w)\) is a continuous linear automorphism of \(V\). Thus, for every continuous linear functional \(\ell\in V^*\), there is a unique \(u\in V\) satisfying \(B(u,w)=\ell(w)\) for every \(w\), and the solution depends continuously and linearly on \(\ell\) (`Analysis/InnerProductSpace/LaxMilgram.lean`, `Analysis/Normed/Operator/NormedSpace.lean`).

### TauCeti

The weak Dirichlet problem for a divergence-form operator on \(H^1_0(\Omega)\), its compact solution operator on bounded domains, and the orthonormal basis of eigenfunctions for symmetric coercive forms with compact embedding are recorded under the next heading; they are the variational, not the operator-theoretic, form of results 24 and 25. Lions' representation theorem, a Lax–Milgram variant with test space only mapped into the Hilbert space and no uniqueness, is also proved ([Lions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Lions.lean)).

**Synopsis entries.** Partly covered: 22.24 (Dirichlet energy on \(H^1_0\) in weak form, through a solution operator; the Neumann case and the self-adjoint operator are absent), 22.25 (compact solution operator and eigenbasis for coercive symmetric forms with compact embedding; the converse and the operator formulation are absent). Not covered: 22.19–22.23.

## Variational principles and essential spectrum

[Mathematical scope](SYNOPSIS22.md#variational-principles-and-essential-spectrum).

### TauCeti

The Dirichlet eigenvalue problem for a divergence-form elliptic operator \(-\partial_j(a^{ij}\partial_i u)+b^i\partial_iu+cu\) on an open set \(\Omega\subseteq\mathbb{R}^n\) is developed in weak form through the solution operator \(S:L^2(\Omega)\to L^2(\Omega)\), with no boundary regularity. Under coercivity the eigenvalues are positive and bounded below by the coercivity constant; on a bounded domain \(S\) is compact by Rellich–Kondrachov; and when the energy form is symmetric, \(L^2(\Omega)\) has an orthonormal basis of Dirichlet eigenfunctions, with finite-dimensional eigenspaces ([Dirichlet spectrum](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Spectrum/Basic.lean); the abstract form for coercive variational problems is [variational spectrum](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Variational/Spectrum.lean)). This is the spectral theorem for the Dirichlet Laplacian and its divergence-form relatives on bounded domains, proved through the compact inverse; the operator is not realized as a self-adjoint `LinearPMap`, and the Rayleigh principle (the first eigenvalue is the minimum of the Rayleigh quotient, `IsCoercive.isLeast_rayleighQuotient`) is stated for the abstract variational problem ([Rayleigh](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Variational/Rayleigh.lean)). On a bounded interval \((a,b)\) the Dirichlet eigenvalues of \(-d^2/dx^2\) are exactly \((k\pi/(b-a))^2\), \(k\ge1\), with sine eigenfunctions ([interval spectrum](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Spectrum/Interval.lean)). In finite dimension the Courant–Fischer min–max characterization of the eigenvalues of a symmetric operator and Weyl's perturbation inequality are proved ([Courant–Fischer](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/CourantFischer.lean)). Lions' representation theorem, a Lax–Milgram variant with test space only mapped into the Hilbert space and no uniqueness, is also proved ([Lions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Lions.lean)).

**Synopsis entries.** Partly covered: 22.26 (least eigenvalue of a coercive variational problem with compact embedding as the minimum of the Rayleigh quotient), 22.27 (finite-dimensional Courant–Fischer). Not covered: 22.28–22.31.

## Perturbation theory

[Mathematical scope](SYNOPSIS22.md#perturbation-theory).

### TauCeti

Relative boundedness \(\lVert Vx\rVert\le a\lVert x\rVert+b\lVert Ax\rVert\) on \(D(A)\subseteq D(V)\) is set up with its calculus (`LinearPMap.IsRelativelyBounded`) ([relative bounds](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Operator/LinearPMap/RelativeBound.lean)). The Kato–Rellich theorem is proved over any `RCLike` field: if \(A\) is self-adjoint, \(V\) symmetric and \(A\)-bounded with \(b<1\), then \(A+V\) is self-adjoint on \(D(A)\) (`IsSelfAdjoint.add_of_isRelativelyBounded`) ([Kato–Rellich](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/LinearPMap/KatoRellich.lean)). A resolvent point \(\lambda\) of \(A\) survives a bounded perturbation \(B\) with \(\lVert B\rVert\lVert R(\lambda,A)\rVert<1\), with \(R(\lambda,A+B)=R(\lambda,A)(I-BR(\lambda,A))^{-1}\) ([resolvent perturbation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Operator/Resolvent/Perturbation.lean)).

**Synopsis entries.** Partly covered: 22.32 (self-adjointness of \(A+V\) on \(D(A)\); essential self-adjointness on cores is not stated), 22.33 (bounded perturbations small against the resolvent, with the closed form \(R(\lambda,A+B)=R(\lambda,A)(I-BR(\lambda,A))^{-1}\); the difference identity for unbounded \(B\) is absent). Not covered: 22.34–22.39.

## Schrödinger operators and eigenvalue estimates

[Mathematical scope](SYNOPSIS22.md#schrödinger-operators-and-eigenvalue-estimates).

### Mathlib

**The Laplacian.**

For a function from a finite-dimensional real inner product space into a real normed space, the Laplacian is the second derivative contracted against the canonical covariant tensor of the domain. It equals the sum of the second directional derivatives along any orthonormal basis. On \(\mathbb{R}\) it is the ordinary second derivative. A constant function has Laplacian zero. Functions that agree on a neighborhood have Laplacians that agree at the point. On twice continuously differentiable functions the Laplacian is \(\mathbb{R}\)-linear: it preserves addition, subtraction, negation, and scalar multiplication, and it commutes with postcomposition by a continuous linear map (`Analysis/InnerProductSpace/Laplacian.lean`).

On Schwartz functions and on tempered distributions the Laplacian is the Fourier multiplier with symbol \(-4\pi^2\lVert\xi\rVert^2\) in Mathlib's normalization (`Analysis/Distribution/FourierMultiplier.lean`, `SchwartzMap.laplacian_eq_fourierMultiplierCLM`, `TemperedDistribution.laplacian_eq_fourierMultiplierCLM`).

This is a differential operator on smooth functions and distributions.

### TauCeti

The normalized Hermite functions form a Hilbert basis of \(L^2(\mathbb R)\) and satisfy the pointwise harmonic-oscillator equation \(-\psi_n''+x^2\psi_n=(2n+1)\psi_n\) ([basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Function/HilbertBasis.lean), [eigen-equation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Oscillator.lean)). On the real Schwartz space, the creation and annihilation operators satisfy \([a,a^\dagger]=I\), with \(a\psi_n=\sqrt n\,\psi_{n-1}\), \(a^\dagger\psi_n=\sqrt{n+1}\,\psi_{n+1}\) and \(H\psi_n=(n+\tfrac12)\psi_n\) for \(H=a^\dagger a+\tfrac12\) ([ladder operators](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Operator.lean)).

**Synopsis entries.** Partly covered: 22.45 (one-dimensional harmonic oscillator: Hermite functions form an eigenbasis for the pointwise equation, TauCeti; compact resolvent for confining potentials and the self-adjoint realization are absent). Not covered: 22.40–22.44, 22.46–22.49.

## Periodic, random, and Dirac operators

[Mathematical scope](SYNOPSIS22.md#periodic-random-and-dirac-operators).

**Synopsis entries.** Not covered: 22.71–22.76.

## Sturm–Liouville operators and quantum graphs

[Mathematical scope](SYNOPSIS22.md#sturmliouville-operators-and-quantum-graphs).

The explicit Dirichlet spectrum of \(-d^2/dx^2\) on a bounded interval, recorded under “Variational principles and essential spectrum”, is the only related material.

**Synopsis entries.** Not covered: 22.50, 22.52, 22.54–22.57.

## Scattering, spectral dynamics, and stability

[Mathematical scope](SYNOPSIS22.md#scattering-spectral-dynamics-and-stability).

**Synopsis entries.** Not covered: 22.58–22.64.

## Nonnormal spectra and pseudospectra

[Mathematical scope](SYNOPSIS22.md#nonnormal-spectra-and-pseudospectra).

### TauCeti

For a complex strongly continuous semigroup with growth bound \((\omega,M)\), \(\lVert R(\lambda,A)\rVert\le M/(\operatorname{Re}\lambda-\omega)\) on the half-plane \(\operatorname{Re}\lambda>\omega\), with the corresponding power bounds (`TauCeti.Semigroups.StronglyContinuousSemigroup.norm_resolvent_complexGenerator_le`, [complex resolvent bounds](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Semigroups/Resolvent/Complex.lean); Section 24).

**Synopsis entries.** Partly covered: 22.68 (the resolvent bound from a growth bound; the Kreiss matrix theorem is absent). Not covered: 22.65–22.67.
