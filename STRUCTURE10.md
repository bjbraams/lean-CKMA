# Structure 10: Ergodic theory and measurable dynamics

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS10.md); [bibliographical scope](CKMA-bib.md#ckma-10); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; the closing line of each section states which synopsis entries are covered.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Dynamics.Ergodic`, `Mathlib.Dynamics.BirkhoffSum`, `Mathlib.Analysis.InnerProductSpace.MeanErgodic`, `Mathlib.MeasureTheory.Function.LpSpace.Basic`, `Mathlib.MeasureTheory.Group.FoelnerFilter`, `Mathlib.MeasureTheory.Function.Intersectivity`, `Mathlib.Dynamics.TopologicalEntropy`, `Mathlib.Dynamics.Minimal`, `Mathlib.Dynamics.Transitive`, `Mathlib.Dynamics.Circle.RotationNumber`, `Mathlib.Dynamics.SymbolicDynamics`, `Mathlib.Dynamics.OmegaLimit`, `Mathlib.Dynamics.PeriodicPts`, `Mathlib.Dynamics.Flow`, `Mathlib.Dynamics.FixedPoints`, `Mathlib.Analysis.Subadditive`, `Mathlib.Combinatorics.HalesJewett`, `Mathlib.Combinatorics.Additive.Corner.Roth`.

**Namespaces.** `MeasureTheory`, with nested `MeasurePreserving`, `Conservative`, `MeasurableEquiv`, and `Lp`. The predicates `PreErgodic`, `QuasiErgodic`, and `Ergodic` are namespaces of their own, as are `ErgodicSMul` and `AddCircle`. Endomorphisms of a group are `MonoidHom`. Følner sequences are `IsFoelner`. Topological entropy is `Dynamics`. Flows are `Flow`, and the translation number of a degree-one lift is `CircleDeg1Lift`. Symbolic dynamics is `SymbolicDynamics`, with nested `FullShift` and `Pattern`. Fixed points and periodic points are `Function`. Minimality and topological transitivity are the classes `MulAction.IsMinimal`, `AddAction.IsMinimal`, `MulAction.IsTopologicallyTransitive`, and `AddAction.IsTopologicallyTransitive`. Birkhoff sums and averages, and the ω-limit of a general action, are declared at the root; ω-limits of a flow return to `Flow`. Fekete's lemma is `Subadditive`, and the van der Waerden and Roth theorems are in `Combinatorics` and at the root. TauCeti declarations are mostly under `TauCeti.Probability` and `TauCeti.MeasureTheory`; the Bernoulli-shift theorems are in `MeasureTheory.Measure`, the diagonal spectral measure in `ContinuousLinearMap`, and the action form of the extreme-point theorems in `ErgodicSMul`.

## Recurrence, induction, and the ergodic theorems

[Mathematical scope](SYNOPSIS10.md#recurrence-induction-and-the-ergodic-theorems).

### Mathlib

**Measure-preserving maps and recurrence.**

A map is measure-preserving when it is measurable and pushes the source measure onto the target measure. Preimages of null sets are null, and a null-measurable set has the same measure as its preimage. Composition and iteration preserve the property, as do addition and scaling of measures (`Dynamics/Ergodic/MeasurePreserving.lean`). A map is quasi-measure-preserving, or nonsingular, when it is measurable and the preimage of a null set is null.

If \(f\) preserves \(\mu\) and \(\mu(X)<n\,\mu(s)\) for a null-measurable \(s\), then some point of \(s\) returns to \(s\) at a positive time strictly less than \(n\). In particular, a self-map preserving a finite measure is conservative (`MeasurePreserving.conservative`): a nonsingular self-map is conservative when every measurable set of positive measure contains a point that returns at some positive time (`Dynamics/Ergodic/Conservative.lean`). From conservativity one gets the stronger statements. For infinitely many times \(m\), the intersection of \(s\) with its preimage under \(f^{m}\) has positive measure. Poincaré recurrence: for a null-measurable \(s\), almost every point of \(s\) returns to \(s\) infinitely often, and almost every point whose orbit meets \(s\) at least once meets it infinitely often (`Conservative.ae_mem_imp_frequently_image_mem`, `Conservative.ae_forall_image_mem_imp_frequently_image_mem`). The topological form, on a second-countable space whose open sets are measurable, says that almost every point visits each of its neighbourhoods infinitely often (`Conservative.ae_frequently_mem_of_mem_nhds`). An iterate of a conservative map is conservative, and the identity is conservative.

**Ergodicity and invariant functions.**

A self-map is pre-ergodic when every measurable strictly invariant set is almost empty or almost the whole space. On a probability space this is a zero–one law. It is ergodic when it is measure-preserving and pre-ergodic, and quasi-ergodic when it is nonsingular and pre-ergodic. For a quasi-ergodic map, almost invariance of a null-measurable set is enough. For an ergodic map and a set of finite measure, an almost inclusion of the set in its preimage, or of the preimage in the set, or of the image in the set, forces the set to be almost empty or almost full; on a finite measure space the finite-measure hypothesis is free (`Dynamics/Ergodic/Ergodic.lean`). Ergodicity passes to iterates in the pre-ergodic direction (ergodicity of an iterate implies pre-ergodicity of the map), is preserved by measure-preserving semiconjugacy, and is invariant under conjugation by a measure-preserving measurable equivalence. The inverse of an ergodic measurable equivalence is ergodic.

An a.e. strongly measurable function from the space into a nonempty metrizable space, almost invariant under a quasi-ergodic map, is almost everywhere constant. The same holds for a null-measurable function into a countably separated measurable space, and, under strict invariance and strict measurability, for a pre-ergodic map (`Dynamics/Ergodic/Function.lean`; for instance `QuasiErgodic.ae_eq_const_of_ae_eq_comp₀`, `PreErgodic.ae_eq_const_of_ae_eq_comp`). This is the forward direction of the function characterization of ergodicity; the converse follows from indicator functions but is not stated as an equivalence, and the Cesàro correlation criterion is not proved.

If \(\mu\) is a finite invariant measure and \(\nu\) is a σ-finite invariant measure, then both the singular part of \(\mu\) with respect to \(\nu\) and the absolutely continuous part are invariant. If both measures are finite, the Radon–Nikodym derivative \(d\mu/d\nu\) is almost everywhere invariant under the map (`Dynamics/Ergodic/RadonNikodym.lean`).

**Birkhoff sums and the mean ergodic theorem.**

The Birkhoff sum of an observable \(g\) along \(f\) is \(\sum_{k=0}^{n-1} g(f^{k}x)\), and the Birkhoff average is that sum divided by \(n\) (`birkhoffSum`, `birkhoffAverage`). If \(g\circ f=g\) and \(n\neq 0\), the average equals \(g\). The average is almost invariant:
\[
A_n(fx)-A_n(x)=n^{-1}\bigl(g(f^{n}x)-g(x)\bigr).
\]
If the orbit of \(g\) is bounded in a normed space, the difference of the averages along the orbits of \(fx\) and of \(x\) tends to zero. At a fixed point the averages tend to \(g(x)\), because they equal \(g(x)\) for every positive time. If \(f\) is \(1\)-Lipschitz and \(g\) is uniformly continuous, the averages are uniformly equicontinuous, and the set of points at which they converge to a prescribed continuous limit is closed (`Dynamics/BirkhoffSum/Basic.lean`, `Dynamics/BirkhoffSum/Average.lean`, `Dynamics/BirkhoffSum/NormedSpace.lean`). Quasi-measure-preserving maps preserve almost-everywhere equality of sums and of averages (`Dynamics/BirkhoffSum/QuasiMeasurePreserving.lean`). No pointwise convergence theorem for a measure-preserving transformation is proved.

The von Neumann theorem is proved for a contraction (`Analysis/InnerProductSpace/MeanErgodic.lean`). On a real or complex Hilbert space, if \(f\) is continuous and linear with \(\|f\|\le 1\), the averages \(n^{-1}\sum_{k=0}^{n-1}f^{k}(x)\) converge to the orthogonal projection of \(x\) onto the fixed subspace of \(f\) (`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`). This contains the unitary case. The normed-space criterion behind it is recorded under [Operator principles and statistical consequences](#operator-principles-and-statistical-consequences). The composition operator of a measure-preserving map on \(L^p\) is a linear isometry for \(1\le p\) (`Lp.compMeasurePreservingₗᵢ`, `MeasureTheory/Function/LpSpace/Basic.lean`); Mathlib does not combine it with the mean ergodic theorem.

### TauCeti

For a measure-preserving transformation, TauCeti specializes the Hilbert-space mean ergodic theorem to the Koopman operator on vector-valued \(L^2\): the averages converge in \(L^2\) to the orthogonal projection onto the fixed subspace ([mean ergodic theorem](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Ergodic/MeanErgodic.lean), `birkhoffAverage_tendsto_metProjection`). It then identifies that projection with conditional expectation on the invariant σ-algebra. The representative-level conditional-expectation statement assumes integrability and σ-finiteness of the trimmed measure, automatic in the finite-measure setting ([identification](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Ergodic/CondExpProjection.lean)). In the probabilists' form, for a measure-preserving \(T\), σ-finiteness of the measure on the invariant σ-algebra \(\mathcal I\), and a real integrable \(f\in L^2\), the pointwise Birkhoff averages converge in \(L^2\) to \(\mathbb E[f\mid\mathcal I]\), and on a finite measure space the mean absolute deviation \(\int|A_nf-\mathbb E[f\mid\mathcal I]|\,d\mu\) tends to zero for \(f\in L^2\) (`tendsto_eLpNorm_birkhoffAverage_sub_condExp`, `tendsto_integral_abs_birkhoffAverage_sub_condExp`). The supporting files show that an almost invariant real function has a strictly invariant measurable representative, so that the fixed space of the Koopman operator on \(L^p\) is the subspace of functions measurable for the invariant σ-algebra ([invariant representatives](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Ergodic/InvariantSigma.lean), `fixedSpace_eq_lpMeas_invariants`; [fixed space](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Ergodic/FixedSpace.lean)), and that the Birkhoff averages of the composition operator on \(L^p\) are represented by the pointwise averages ([Birkhoff averages on \(L^p\)](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Ergodic/BirkhoffLp.lean)). The convergence assertion is in the \(L^2\) norm for square-integrable observables; neither almost-everywhere convergence nor \(L^1\) convergence for integrable observables is proved.

For a probability measure \(\mu\) on an arbitrary measurable space, the one-sided shift on \(\alpha^{\mathbb N}\) is ergodic for the product law \(\mu^{\otimes\mathbb N}\), and more generally for any shift-invariant path law with independent coordinates; the proof shows that shift-invariant events are tail events and applies Kolmogorov's zero–one law ([Bernoulli shifts](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Ergodic/BernoulliShift.lean), `ergodic_shift_infinitePi_const`, `ergodic_shift_of_iIndepFun`). TauCeti also proves that a stationary process on a countable state space is recurrent, by Poincaré recurrence for the shift ([recurrent processes](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Recurrent/Basic.lean), `recurrent_of_measurePreserving_shift`; Section 8).

For a measurable action of a group \(G\), an almost invariant function of an ergodic action is almost everywhere constant (`ErgodicSMul.ae_eq_const_of_forall_ae_eq_comp_smul₀`), and for a countable group the almost invariant and the strictly invariant events agree up to null sets ([extreme invariant measures](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Group/ErgodicExtreme.lean); [countable actions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Group/CountableAction.lean)). This is the group-action analogue of Mathlib's single-map theorem.

The only decomposition into ergodic components is de Finetti's: for a standard Borel state space, the barycenter map \(\pi\mapsto\int P^{\otimes\mathbb N}\,d\pi(P)\) is an affine bijection from probability measures on the laws onto exchangeable path laws, carrying point masses exactly to the extreme exchangeable laws, which are the i.i.d. laws and the ergodic laws for the action of finitely supported permutations ([de Finetti correspondence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/DeFinetti/Correspondence.lean), `deFinettiEquiv`, `deFinettiBarycenter_mem_extremePoints_iff`; [ergodicity of exchangeable laws](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Exchangeability/PathSpace/Exchangeable/Ergodic.lean)). For a finite measure on path space, the conditional law of the initial coordinate given the shift-invariant σ-algebra is constructed as a random probability measure ([invariant conditional law](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Process/PathLaw/InvariantConditionalLaw.lean)); this is not a decomposition into ergodic measures.

**Synopsis entries.** Covered: 10.1, 10.6 (Mathlib; TauCeti for the Koopman application). Partly covered: 10.3 (invariant functions of an ergodic map or action are almost everywhere constant; the correlation criterion is absent), 10.5 (TauCeti: \(L^2\) convergence to \(\mathbb E[f\mid\mathcal I]\) for \(f\in L^2\); \(L^p\) mean convergence follows by density and the contraction bounds; almost-everywhere convergence is absent), 10.8 (TauCeti: ergodic decomposition of exchangeable laws only). Not covered: 10.2, 10.4, 10.60, 10.7, 10.9, 10.10.

## Koopman operators and spectral structure

[Mathematical scope](SYNOPSIS10.md#koopman-operators-and-spectral-structure).

### TauCeti

Herglotz's theorem is proved: a function \(\varphi:\mathbb Z\to\mathbb C\) is positive definite if and only if \(\varphi(n)=\int z^n\,d\mu(z)\) for a finite positive measure \(\mu\) on the unit circle ([Herglotz](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Bochner/Herglotz.lean), `TauCeti.exists_isFiniteMeasure_integral_zpow_eq`, `TauCeti.isPositiveDefiniteSub_iff_exists_isFiniteMeasure_integral_zpow_eq`). Independently, for a normal bounded operator \(a\) on a complex Hilbert space and a vector \(\xi\), the diagonal spectral measure \(\mu_\xi\) on the spectrum is the unique finite measure with \(\langle\xi,f(a)\xi\rangle=\int f\,d\mu_\xi\) for continuous \(f\) ([diagonal measure](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean), `ContinuousLinearMap.diagMeasure`, `ContinuousLinearMap.eq_diagMeasure_iff`). Either result yields the spectral measure of a vector under a unitary operator, but neither is applied to Koopman operators. As supporting structure, the Koopman operator \(g\mapsto g\circ T\) of a measure-preserving map is bundled as a positive, unital, multiplicative linear operator on almost-everywhere classes of measurable real functions ([Koopman operator](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Ergodic/KoopmanMarkov.lean), `koopmanMarkov`). Mixing notions, eigenfunctions, and spectral types of a system are not defined in either library.

**Synopsis entries.** Partly covered: 10.11 (TauCeti: Herglotz's theorem and diagonal spectral measures of normal operators, not specialized to Koopman operators). Not covered: 10.12–10.17.

## Entropy and measurable classification

[Mathematical scope](SYNOPSIS10.md#entropy-and-measurable-classification).

Neither library defines the entropy of a partition or the Kolmogorov–Sinai entropy of a measure-preserving transformation. As supporting material, Mathlib has Fekete's lemma for subadditive sequences (`Subadditive.tendsto_lim`, `Analysis/Subadditive.lean`), which is the limit step in the existence of the entropy rate, and the function \(x\mapsto -x\log x\) (`Real.negMulLog`, `Analysis/SpecialFunctions/Log/NegMulLog.lean`). Ergodicity of Bernoulli shifts (TauCeti) is recorded in the first section.

**Synopsis entries.** Not covered: 10.18, 10.19, 10.61, 10.20–10.25, 10.62, 10.26–10.28.

## Topological dynamics and thermodynamic formalism

[Mathematical scope](SYNOPSIS10.md#topological-dynamics-and-thermodynamic-formalism).

### Mathlib

**Invariant probabilities.**

Krylov–Bogolyubov: a continuous self-map of a nonempty compact Hausdorff space with its Borel σ-algebra preserves some regular Borel probability measure (`MeasureTheory.exists_measurePreserving_probabilityMeasure`). The proof defines the empirical measure along an orbit as the Birkhoff average of Dirac masses (`empiricalMeasure`) and shows that a cluster point of the empirical measures is invariant. A variant produces an invariant probability measure supported on a given compact forward-invariant set \(K\), for a measurable map continuous on \(K\) of a possibly noncompact space (`exists_measurePreserving_probabilityMeasure_of_compact_forwardInvariant`; `Dynamics/Ergodic/EmpiricalMeasure.lean`).

A finite measure is ergodic if and only if it is an extreme point of the invariant measures of the same total mass. In particular, a probability measure is ergodic if and only if it is an extreme point of the invariant probabilities (`Ergodic.iff_mem_extremePoints`). If a finite invariant measure is absolutely continuous with respect to a finite ergodic measure, it is a scalar multiple of that measure; if both are probabilities, they agree (`Dynamics/Ergodic/Extreme.lean`). Compactness of the set of invariant probabilities in the weak topology is not stated, and unique ergodicity is not defined.

**Topological dynamics.**

An action of a monoid is minimal when every orbit is dense. A nonempty closed invariant set is then empty or the whole space, and a compact set can be covered by finitely many translates of any nonempty open set (`Dynamics/Minimal.lean`). A minimal set, as a subset, is not defined, and uniform recurrence is absent. The action is topologically transitive when every pair of nonempty open sets has some translate of the first meeting the second, equivalently when the saturation of every nonempty open set is dense. Minimality implies topological transitivity (`Dynamics/Transitive.lean`).

A flow of an additive topological monoid on a space is a continuous monoid action. Invariant and forward-invariant sets, orbits, restriction to an invariant set, time reversal for a group, and semiconjugacy of flows are defined (`Dynamics/Flow.lean`). The ω-limit of a set along a filter is the intersection of the closures of the forward images. It is closed. On a compact space, the ω-limit of a nonempty set along a nontrivial filter is nonempty. For a flow, if translation along the monoid preserves the filter, the ω-limit is invariant (`Dynamics/OmegaLimit.lean`).

A point is periodic of period \(n\) when its \(n\)th iterate returns to it; the definition allows \(n=0\). The minimal period divides every period, the map is bijective on its periodic points, and the fixed-point set of a continuous self-map of a Hausdorff space is closed. If the iterates of \(x\) converge to \(y\) and the map is continuous at \(y\), then \(y\) is fixed (`Dynamics/PeriodicPts/Defs.lean`, `Dynamics/FixedPoints/Topology.lean`).

**Topological entropy.**

Topological entropy is the Bowen–Dinaburg entropy of a uniformly continuous setting, stated for an arbitrary subset of a uniform space and taking values in the extended reals. For an entourage \(U\), two orbit segments of length \(n\) are distinguished when some iterate leaves \(U\). If \(N(T,F,U,n)\) is the least cardinality of a dynamical cover of \(F\), the entourage entropy is
\[
h(T,F,U)=\limsup_{n\to\infty}\frac{1}{n}\log N(T,F,U,n),
\]
and the entropy \(h(T,F)\) is the supremum of these quantities over entourages (`coverEntropy`). A parallel definition uses a liminf, and the basic lemmas on dynamical entourages are in `Dynamics/TopologicalEntropy/DynamicalEntourage.lean`. The two agree when \(F\) is invariant (`coverEntropyInf_eq_coverEntropy`). The empty set has entropy \(-\infty\); a nonempty set has entropy at least \(0\). Each fixed entourage has finite entropy on a compact invariant set, which does not by itself make \(h(T,F)\) finite. The same supremum is obtained from dynamical nets, the separated-set form. Entropy is monotone in the set, the entropy of a finite union is the maximum, a uniformly continuous semiconjugacy does not raise entropy, and the entropy of the restriction of the map to an invariant set equals the entropy of that set (`Dynamics/TopologicalEntropy/CoverEntropy.lean`, `Dynamics/TopologicalEntropy/NetEntropy.lean`, `Dynamics/TopologicalEntropy/Semiconj.lean`, `Dynamics/TopologicalEntropy/Subset.lean`). The comparison with dynamical balls in a metric space is listed there as future work. No entropy of a specific system (shift, toral automorphism) is computed, and there is no pressure or variational principle.

**Circle dynamics.**

On the additive circle of circumference \(T>0\), with Haar measure, \(y\mapsto n\cdot y\) is ergodic whenever \(n\in\mathbb{Z}\) satisfies \(|n|>1\), and so is \(y\mapsto n\cdot y+x\) for any fixed \(x\) (`AddCircle.ergodic_zsmul`, `AddCircle.ergodic_zsmul_add`). The argument is a Lebesgue density argument: a null-measurable set that is almost invariant under a family of rotations whose additive orders tend to infinity is almost empty or almost full (`Dynamics/Ergodic/AddCircle.lean`). Rotation by a fixed \(a\) is ergodic if and only if \(a\) has infinite additive order. Equivalently, the integer multiples of \(a\) are dense. For a real representative, those multiples are dense if and only if the ratio of the representative to the circumference is irrational (`Dynamics/Ergodic/AddCircleAdd.lean`). This is ergodicity for Haar measure, not unique ergodicity or equidistribution. A continuous surjective endomorphism of a compact second-countable group is ergodic for Haar measure when the preimages of the identity under its iterates are dense (`MonoidHom.ergodic_of_dense_iUnion_preimage_one`, `Dynamics/Ergodic/Action/OfMinimal.lean`); the eigenvalue criterion for toral automorphisms is not derived from it.

A degree-one lift is a monotone map \(f:\mathbb{R}\to\mathbb{R}\) with \(f(x+1)=f(x)+1\). Its translation number exists and is independent of the base point:
\[
\tau(f)=\lim_{n\to\infty}\frac{f^{n}(x)-x}{n}.
\]
It is monotone in \(f\), additive on commuting maps, changes sign under inversion, and is unchanged by semiconjugacy in this class. For continuous \(f\), \(\tau(f)=m/n\) in lowest terms if and only if \(f^{n}(x)=x+m\) for some \(x\) (`CircleDeg1Lift.translationNumber_eq_rat_iff`), and two bijective lifts with the same translation number are semiconjugate by a degree-one lift (`CircleDeg1Lift.semiconj_of_bijective_of_translationNumber_eq`). The same semiconjugacy holds for two group actions by such lifts whenever corresponding elements have equal translation numbers (`Dynamics/Circle/RotationNumber/TranslationNumber.lean`). The rotation number of a circle homeomorphism, as a class in \(\mathbb R/\mathbb Z\), is not constructed.

**Symbolic dynamics.**

On a left-cancellative monoid, configurations are maps from the monoid to an alphabet, with the product topology and the left shift. Cylinders are clopen when the alphabet is discrete, and closed when it is \(T_1\). A subshift is a closed shift-invariant set of configurations (`SymbolicDynamics.FullShift.Subshift`, `MulSubshift`). A pattern is a configuration that takes a default value off a finite support. Forbidding a family of patterns defines a subshift when the alphabet is discrete (`MulSubshift.ofForbidden`), and the language of a set of configurations on a finite shape is defined, with finiteness of the patterns of a given support over a finite alphabet (`Dynamics/SymbolicDynamics/Basic.lean`). A finite forbidden family is allowed by this construction. The module comment names a subshift of finite type, but no separate declaration for it exists, and the entropy of a subshift is not defined. Irreducible and primitive nonnegative matrices are defined, with the path characterization of positive entries of powers (`Matrix.IsIrreducible`, `Matrix.IsPrimitive`, `LinearAlgebra/Matrix/Irreducible/Defs.lean`); the Perron–Frobenius theorem itself is not proved.

**Van der Waerden's theorem.**

For a finitely coloured commutative additive monoid \(M\) and a finite set \(S\subseteq M\), some homothetic copy \(\{a\cdot s+b:s\in S\}\) with \(a>0\) is monochromatic (`Combinatorics.exists_mono_homothetic_copy`, `Combinatorics/HalesJewett.lean`). With \(M=\mathbb Z\) and \(S=\{0,\ldots,k-1\}\) this gives, for each \(k\), a monochromatic arithmetic progression of length \(k\); the proof is combinatorial, via the Hales–Jewett theorem, not by topological multiple recurrence.

### TauCeti

For a measurable action of a countable group, an invariant finite measure is ergodic if and only if it is an extreme point of the invariant measures of the same mass (`ErgodicSMul.iff_mem_extremePoints_measure_univ_eq`, `ErgodicSMul.iff_mem_extremePoints`); the invariant measures of given mass form a convex set. In integral form, on a countably generated space an ergodic probability written as a mixture of invariant probabilities has almost every component equal to it (`ErgodicSMul.ae_eq_of_comp_eq`; [extreme invariant measures](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Group/ErgodicExtreme.lean)).

**Synopsis entries.** Partly covered: 10.29 (existence by Krylov–Bogolyubov via empirical measures and the extreme-point characterization of ergodic measures; compactness of the set of invariant probabilities is not stated), 10.65 (only van der Waerden's theorem, by a combinatorial proof; minimal sets, uniform recurrence, and the Furstenberg–Weiss theorem are absent), 10.32 (the circle case: multiplication by \(n\), \(|n|>1\), is ergodic; mixing, the higher-dimensional criterion, and entropy are absent). Not covered: 10.30, 10.31, 10.33–10.39, 10.63.

## Uniformly hyperbolic systems

[Mathematical scope](SYNOPSIS10.md#uniformly-hyperbolic-systems).

**Synopsis entries.** Not covered: 10.66, 10.67.

## Lyapunov exponents and smooth ergodic theory

[Mathematical scope](SYNOPSIS10.md#lyapunov-exponents-and-smooth-ergodic-theory).

**Synopsis entries.** Not covered: 10.40–10.44.

## Joinings, recurrence, and nonconventional averages

[Mathematical scope](SYNOPSIS10.md#joinings-recurrence-and-nonconventional-averages).

### Mathlib

Roth's theorem, the length-three case of Szemerédi's theorem, is proved in finitary form: for \(\varepsilon>0\) and \(n\) large enough depending on \(\varepsilon\), every \(A\subseteq\{0,\ldots,n-1\}\) with \(|A|\ge\varepsilon n\) contains a nontrivial three-term arithmetic progression, and the Roth number of \(\{0,\ldots,n-1\}\) is \(o(n)\) (`roth_3ap_theorem_nat`, `rothNumberNat_isLittleO_id`, `Combinatorics/Additive/Corner/Roth.lean`). The proof goes through the corners theorem and the triangle removal lemma, not through ergodic theory. As supporting material, Bergelson's intersectivity lemma is proved: in a finite measure space, a sequence of measurable sets of measure at least \(r>0\) has an infinite subsequence all of whose finite intersections have positive measure (`bergelson`, `MeasureTheory/Function/Intersectivity.lean`). Joinings and multiple recurrence are not formalized.

**Synopsis entries.** Partly covered: 10.48 (the case \(k=1\) is not stated, but follows from TauCeti's \(L^2\) mean ergodic theorem; \(k\geq2\) is absent), 10.50 (Mathlib: progressions of length three only, in finitary form, by a combinatorial proof). Not covered: 10.45–10.47, 10.49, 10.51–10.54.

## Infinite invariant measure

[Mathematical scope](SYNOPSIS10.md#infinite-invariant-measure).

The nearest supporting material is Mathlib's notion of a conservative nonsingular map and its recurrence theorems, recorded in the first section; it is stated for arbitrary measures, but wandering sets, the Hopf decomposition, and ratio averages are absent.

**Synopsis entries.** Not covered: 10.55–10.57.

## Actions of amenable groups and orbit equivalence

[Mathematical scope](SYNOPSIS10.md#actions-of-amenable-groups-and-orbit-equivalence).

### Mathlib

**Følner filters (supporting).**

Let a group act on a measure space. A family of sets \(F_i\), indexed along a filter, is Følner when the sets are eventually measurable and of finite positive measure, and for every group element \(g\)
\[
\frac{\mu\bigl((g\cdot F_i)\triangle F_i\bigr)}{\mu(F_i)}\to 0.
\]
The constant family equal to the whole space is Følner when the measure is finite and nonzero. There is a maximal Følner filter on the measurable sets of finite positive measure, characterised by the same ratio tending to zero, and a family is Følner if and only if it tends to that filter. Along an ultrafilter, the densities \(\mu(s\cap F_i)/\mu(F_i)\) converge. If the underlying measure is invariant, this mean is invariant under the action, the whole space has mean one, and the mean is additive for a measurable set disjoint from another set. Consequently, a nontrivial Følner filter produces a finitely additive \(G\)-invariant probability, with values in the extended nonnegative reals: total mass one, invariant under the action, and additive when one of the two sets is measurable and the sets are disjoint (`IsFoelner.amenable`, `MeasureTheory/Group/FoelnerFilter.lean`). The file uses the name amenable for this existence statement and says explicitly that amenability itself has not been defined. Averages along Følner sets and ergodic theorems for group actions are not proved.

**Ergodic group actions (supporting).**

An action of a group on a measure space is ergodic when the measure is invariant and every null-measurable set that is almost invariant under every group element is almost empty or almost full (`ErgodicSMul`). For the iteration action of a measurable self-map, this agrees with ergodicity of the map (`Dynamics/Ergodic/Action/Basic.lean`). The left action of a group on itself is ergodic for any s-finite left-invariant measure, and the right action is ergodic for any s-finite right-invariant measure, assuming multiplication and inversion are measurable (`Dynamics/Ergodic/Action/Regular.lean`).

If a monoid acts continuously and ergodically on an \(\mathrm{R}_1\) space, and \(\mu\) is a finite inner-regular measure, then an element whose natural powers are dense in the monoid acts ergodically. The same holds for integer powers in a group. Thus if \(N\) acts continuously and ergodically and \(M\) acts minimally on \(N\), the induced action of \(M\) is ergodic. On a second-countable topological group, left multiplication by \(g\) is ergodic for a finite, nonzero, inner-regular, left-invariant measure if and only if the integer powers of \(g\) are dense (`ergodic_mul_left_iff_denseRange_zpow`). One direction needs only that the measure of every nonempty open set is positive (`Dynamics/Ergodic/Action/OfMinimal.lean`).

**Synopsis entries.** Not covered: 10.68–10.71.

## Operator principles and statistical consequences

[Mathematical scope](SYNOPSIS10.md#operator-principles-and-statistical-consequences).

### Mathlib

Let \(f\) be a linear self-map of a normed space over \(\mathbb{R}\) or \(\mathbb{C}\), Lipschitz with constant \(1\), and let \(g\) be a continuous linear projection onto the fixed subspace of \(f\), equal to the identity on that subspace. If the kernel of \(g\) is contained in the closure of the range of \(f-\mathrm{id}\), then for every vector \(x\) the averages \(n^{-1}\sum_{k=0}^{n-1}f^{k}(x)\) converge in norm to \(g(x)\) (`LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure`, `Analysis/InnerProductSpace/MeanErgodic.lean`). This is the convergence half of the mean ergodic theorem under an assumed splitting \(E=\ker(I-f)\oplus\overline{\mathop{\mathrm{ran}}(I-f)}\); the existence of the splitting for power-bounded operators on reflexive spaces is not proved.

**Synopsis entries.** Partly covered: 10.59 (Mathlib: convergence for contractions given the fixed-space splitting; the reflexive-space theorem is absent). Not covered: 10.58, 10.64.
