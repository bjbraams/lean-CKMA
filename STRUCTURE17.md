# Structure 17: Banach space geometry, bases, and operator ideals

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS17.md); [bibliographical scope](CKMA-bib.md#ckma-17); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.Normed.Module.Bases`, `Mathlib.Analysis.InnerProductSpace.l2Space`, `Mathlib.Topology.Algebra.InfiniteSum`, `Mathlib.Analysis.Normed.Module.Complemented`, `Mathlib.Analysis.Normed.Module.MStructure`, `Mathlib.Analysis.Convex.Uniform`, `Mathlib.Analysis.InnerProductSpace.Convex`, `Mathlib.Analysis.Calculus.FDeriv.Norm`, `Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm`, `Mathlib.Analysis.Normed.Affine.MazurUlam`, `Mathlib.Analysis.Calculus.Rademacher`.

**Namespaces.** Bases are `GeneralSchauderBasis`, `SchauderBasis`, `UnconditionalSchauderBasis`, and `RankOneDecomposition`; TauCeti's approximation properties are `HasApproximationProperty`, `HasBoundedApproximationPropertyWith`, and `HasMetricApproximationProperty`. Uniform convexity is `UniformConvexSpace`. Approximation numbers are `ContinuousLinearMap.singularValue` (TauCeti), and operator-ideal families live in `TauCeti.OperatorIdealFamily`.

## Bases, block sequences, and duality

[Mathematical scope](SYNOPSIS17.md#bases-block-sequences-and-duality).

### Mathlib

**Bases.** A generalized Schauder basis (`GeneralSchauderBasis`) consists of vectors and continuous coordinate functionals, biorthogonal, with every vector equal to the sum of its expansion along a summation filter. Classical Schauder bases (`SchauderBasis`, indexed by \(\mathbb{N}\) with convergence of partial sums) and unconditional bases (`UnconditionalSchauderBasis`, with convergence of the net of finite partial sums) are the two instances. The partial-sum projections converge pointwise to the identity (`tendsto_proj`) and have the expected ranges and composition law. On a Banach space they are uniformly bounded (`SchauderBasis.exists_norm_proj_le`), and for an unconditional basis the projections onto all finite sets are uniformly bounded (`UnconditionalSchauderBasis.exists_norm_proj_le`); the suprema are recorded as basis constants (`enormProjBound`, `nnnormProjBound`). Nested finite-rank projections converging pointwise to the identity, with rank-one successive differences, produce a classical Schauder basis (`RankOneDecomposition.basis`). A Hilbert basis is an unconditional Schauder basis, and a Hilbert basis indexed by \(\mathbb{N}\) is a classical one (`HilbertBasis.toUnconditionalSchauderBasis`, `HilbertBasis.toSchauderBasis`) (`Analysis/Normed/Module/Bases.lean`, `Analysis/InnerProductSpace/l2Space.lean`).

### TauCeti

**Bases.** Building on Mathlib's `GeneralSchauderBasis`, TauCeti proves that every strictly increasing subsequence of a Schauder basis is a basis of its closed span, with basis constant at most the original one (`SchauderBasis.subsequence`, [subsequences](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Bases/Subsequence.lean)); that bounded linear equivalences transport bases ([transport](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Bases/Map.lean)); that the norm \(\sup_n\|P_nx\|\) is an equivalent norm in which the basis is monotone ([monotone renorming](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Bases/Monotone.lean)); and the small-perturbation principle for a basis of the whole space: if \(\delta=\sum_i\|e_i^*\|\,\|e_i-f_i\|<1\) in a Banach space with basis \((e_i)\), a linear isomorphism with norm at most \(1+\delta\) and inverse norm at most \((1-\delta)^{-1}\) sends \(e_i\) to \(f_i\), so \((f_i)\) is an equivalent basis (`smallPerturbationEquiv`, `perturb`, [perturbation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Bases/Perturbation.lean)). The unit vectors form an unconditional basis of \(\ell^p(\iota)\), \(1\le p<\infty\), and of \(c_0(\iota)\), with contractive finite projections ([\(\ell^p\) basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Lp/Basis.lean), [\(c_0\) basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Topology/ContinuousMap/ZeroAtInfty/Basis.lean)).

**Duality and reflexivity.** In a Banach space, the coordinate functionals of a Schauder basis form a basis of their closed span in the dual; a basis is shrinking exactly when \(\|f-P_n^*f\|\to0\) for every \(f\in X^*\) (`isShrinking_iff_tendsto_comp_proj`), and then the coordinate functionals form a basis of the whole dual (`IsShrinking.dualBasis`, [dual basic sequence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Bases/Dual/Basic.lean)). A basis is shrinking if and only if its dual basic sequence is boundedly complete; the implication from shrinking to bounded completeness assumes a proper scalar field, which covers \(\mathbb{R}\) and \(\mathbb{C}\) (`isShrinking_iff_isBoundedlyComplete_dualBasis`, [bounded completeness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Bases/Dual/BoundedlyComplete.lean)). **James's basis theorem** holds over \(\mathbb{R}\) and \(\mathbb{C}\): a Banach space with a Schauder basis is reflexive if and only if the basis is shrinking and boundedly complete (`SchauderBasis.surjective_inclusionInDoubleDual_iff`, [reflexivity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Bases/Reflexive.lean)).

**Bases and approximation.** A Banach space with a Schauder basis, or with an unconditional basis, has the bounded approximation property with the basis constant as bound, and the metric approximation property when the relevant projections are contractions (`SchauderBasis.hasBoundedApproximationProperty`, [bases](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Bases/Approximation.lean)).

**Synopsis entries.** Covered: 17.10, 17.13 (TauCeti). Partly covered: 17.1 (the forward direction in Mathlib; the converse only in the form of nested finite-rank projections with rank-one differences converging pointwise), 17.4 (TauCeti: subsequences of a basis only, not general block sequences), 17.5 (TauCeti: perturbation of a basis of the whole Banach space; the complemented-subspace clause is absent), 17.8 (Mathlib: an unconditional basis has uniformly bounded finite coordinate projections; the converse and the renorming are absent), 17.9 (TauCeti: the dual-projection criterion; the block-sequence criterion is absent), 17.11 (TauCeti: the shrinking half, as an equivalence; the identification of \(X\) with the dual of \([e_n^*]\) is absent). Not covered: 17.2, 17.3, 17.6, 17.7, 17.12, 17.70, 17.14.

## Weak sequences and unconditional series

[Mathematical scope](SYNOPSIS17.md#weak-sequences-and-unconditional-series).

### Mathlib

**Unconditional summation.** Mathlib's basic notion of convergence of a series, `HasSum`, is convergence of the net of sums over finite subsets. In a complete space summability is equivalent to the Cauchy criterion that sums over finite sets disjoint from a sufficiently large finite set are small (`summable_iff_cauchySeq_finset`, `summable_iff_vanishing`, and `summable_iff_vanishing_norm` for normed groups), and the sum is invariant under every permutation of the index set (`Equiv.hasSum_iff`); a summable sequence has convergent partial sums (`HasSum.tendsto_sum_nat`) (`Topology/Algebra/InfiniteSum/Group.lean`, `Topology/Algebra/InfiniteSum/Basic.lean`, `Topology/Algebra/InfiniteSum/NatInt.lean`, `Analysis/Normed/Group/InfiniteSum.lean`). The converse statement, that convergence of every rearrangement of the partial sums implies `HasSum`, was not found.

### TauCeti

**Supporting material.** Weakly bounded sets are norm bounded, and weakly convergent sequences are bounded ([weak boundedness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/WeakSpace/Bounded.lean)). Weakly compact operators are defined, with Gantmacher's theorem ([weakly compact operators](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Operator/WeaklyCompact.lean)); the Dunford–Pettis property is not formalized.

**Synopsis entries.** Partly covered: 17.15 (Mathlib takes convergence of the net of finite partial sums as the definition and proves the Cauchy criterion and permutation invariance; the equivalence with convergence of all rearrangements is absent). Not covered: 17.16–17.24.

## Classical subspaces, quotients, and complemented copies

[Mathematical scope](SYNOPSIS17.md#classical-subspaces-quotients-and-complemented-copies).

### Mathlib

**Supporting material: complemented subspaces and L-projections.** A closed subspace of a Banach space is complemented when it is the range of a continuous linear projection (`Submodule.ClosedComplemented`). In a Banach space, algebraic complements that are both closed are topological complements, by the open mapping theorem (`Analysis/Normed/Module/Complemented.lean`); finite-dimensional subspaces of a locally convex space over \(\mathbb{R}\) or \(\mathbb{C}\) are complemented (`Submodule.ClosedComplemented.of_finiteDimensional`, `Analysis/LocallyConvex/HahnBanach.lean`), and so are closed subspaces of finite codimension (`Submodule.ClosedComplemented.of_finiteDimensional_quotient`, `Topology/Algebra/Module/FiniteDimension.lean`).

An L-projection on a normed space is a projection \(P\) with \(\|x\|=\|Px\|+\|(1-P)x\|\), and an M-projection one with \(\|x\|=\max(\|Px\|,\|(1-P)x\|)\). The L-projections commute and form a Boolean algebra (`IsLprojection`, `Analysis/Normed/Module/MStructure.lean`).

**Supporting material: universality.** Every separable metric space embeds isometrically, but not linearly, into \(\ell^\infty(\mathbb{N})\) (`kuratowskiEmbedding`, `Topology/MetricSpace/Kuratowski.lean`). This is not the Banach–Mazur theorem.

**Synopsis entries.** Not covered: 17.25, 17.71, 17.26–17.34.

## Local geometry, random sums, and finite representability

[Mathematical scope](SYNOPSIS17.md#local-geometry-random-sums-and-finite-representability).

**Synopsis entries.** Not covered: 17.35–17.38, 17.73, 17.74, 17.39, 17.72, 17.41–17.44.

## Convexity, smoothness, and Radon–Nikodým geometry

[Mathematical scope](SYNOPSIS17.md#convexity-smoothness-and-radonnikodým-geometry).

### Mathlib

**Uniform convexity.** A real seminormed group is uniformly convex (`UniformConvexSpace`) when, for every \(\varepsilon > 0\), some \(\delta > 0\) forces \(\|x+y\| \le 2-\delta\) whenever \(x\) and \(y\) are unit vectors at least \(\varepsilon\) apart. Uniformly convex spaces are strictly convex, and a real inner product space is uniformly convex (`InnerProductSpace.toUniformConvexSpace`). The file lists the Milman–Pettis theorem and Hanner's inequalities as future work. The development belongs with Section 12 (`Analysis/Convex/Uniform.lean`, `Analysis/InnerProductSpace/Convex.lean`). No modulus of smoothness or uniform smoothness is defined.

**Differentiability of the norm.** If the norm of a real normed space is Fréchet differentiable at \(x\), its derivative \(f\) satisfies \(f(x)=\|x\|\) and, on a nontrivial space, \(\|f\|=1\) (`DifferentiableAt.fderiv_norm_self`, `norm_fderiv_norm`, `Analysis/Calculus/FDeriv/Norm.lean`).

### TauCeti

**Milman–Pettis.** Every uniformly convex real Banach space is reflexive (`TauCeti.surjective_inclusionInDoubleDual_of_uniformConvexSpace`), and subspaces of uniformly convex spaces are uniformly convex ([Milman–Pettis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Uniform.lean)). For \(1<p<\infty\) and a strictly convex real normed space \(E\), \(L^p(\mu;E)\) is strictly convex (`MeasureTheory.Lp.strictConvexSpace`, [strict convexity of \(L^p\)](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/Lp/StrictConvex.lean)); uniform convexity of \(L^p\) is not formalized.

**Synopsis entries.** Partly covered: 17.45 (TauCeti: uniform convexity implies reflexivity; uniform smoothness and the duality are absent), 17.47 (Mathlib: a Fréchet derivative of the norm at \(x\) is a norm-one functional attaining \(\|x\|\); the Gâteaux characterization by uniqueness of the supporting functional is absent). Not covered: 17.46, 17.48–17.50.

## Summing operators, tensor norms, and approximation

[Mathematical scope](SYNOPSIS17.md#summing-operators-tensor-norms-and-approximation).

### Mathlib

**Supporting material: projective tensor seminorm.** The algebraic tensor product of a finite family of normed spaces carries a projective seminorm, with the isometric universal property for continuous multilinear maps (`PiTensorProduct.liftIsometry`) and the bound \(\|\bigotimes_i f_i\|\le\prod_i\|f_i\|\) for tensor products of operators (`PiTensorProduct.opNorm_mapL`) (`Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean`). There is no completed projective tensor product and no injective tensor norm; Section 16 gives the scope and limitations.

### TauCeti

**Approximation properties.** The approximation property, the bounded approximation property with constant \(C\), and the metric approximation property are defined by finite-rank operators approximating the identity uniformly on compact sets; a uniformly bounded net of finite-rank operators converging pointwise to the identity gives the BAP, and finite-dimensional spaces have the MAP ([definitions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/ApproximationProperty/Basic.lean)). The properties pass to bounded retracts and are invariant under isomorphism, with MAP preserved by isometries and contractive projections ([transport](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/ApproximationProperty/Transport.lean)). The spaces \(\ell^p(\iota)\), \(1\le p<\infty\), and \(c_0(\iota)\) have the MAP ([sequence spaces](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/ApproximationProperty/SequenceSpace.lean)). Spaces with a basis are recorded under the first heading.

**Approximation numbers and operator ideals.** For \(T\colon E\to F\) between seminormed spaces over any nontrivially normed field, the approximation numbers \(a_n(T)=\inf\{\|T-R\|:\mathop{\mathrm{rank}}R\le n\}\) (zero-based indexing, so they correspond to the synopsis's \(a_{n+1}\)) satisfy \(a_{m+n}(S+T)\le a_m(S)+a_n(T)\), \(a_{m+n}(ST)\le a_m(S)a_n(T)\), and \(a_n(ATB)\le\|A\|a_n(T)\|B\|\) (`ContinuousLinearMap.singularValue`, [approximation numbers](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean)). Over a complete field \(a_n(T)=0\) exactly when \(\mathop{\mathrm{rank}}T\le n\); \(a_n(T)\to0\) implies compactness for a complete target over a locally compact field, and conversely compact operators into inner product spaces satisfy \(a_n(T)\to0\), so they are norm limits of finite-rank operators ([compactness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Compact.lean)). Between real or complex Hilbert spaces \(a_n(T^*)=a_n(T)\) ([adjoints](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Adjoint.lean)). On finite-dimensional inner product spaces the approximation numbers are the singular values (Eckart–Young, [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/EckartYoung.lean)), and for diagonal operators on \(\ell^p\) with decreasing coefficient magnitudes they are those magnitudes ([diagonal operators](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Diagonal.lean)). A symmetric gauge on sequences (a symmetric norming function) induces an operator-ideal family on Hilbert spaces with the triangle and two-sided ideal inequalities; the normed ideal of finite gauge is packaged as a normed space ([families](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/Family.lean), [symmetric gauges](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/Family/SymmetricGauge.lean), [carriers](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/Carrier.lean)). The Ky Fan families are complete ([Ky Fan families](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/Family/KyFan.lean)). The nuclear gauge \(\sum_na_n(T)\), whose finite locus on Hilbert spaces is the trace class, is subadditive, adjoint invariant, and lower semicontinuous, satisfies the ideal inequality, and finite gauge forces compactness over a locally compact field with complete target ([nuclear gauge](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/Nuclear/Basic.lean)). For an operator from a Hilbert space to an inner product space, the Hilbert–Schmidt energy \(\sum_i\|Te_i\|^2\) equals \(\sum_na_n(T)^2\) ([Hilbert–Schmidt](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/HilbertSchmidt.lean)). Schatten \(p\)-seminorms, \(1\le p\le\infty\), are constructed for maps between finite-dimensional inner product spaces ([Schatten seminorms](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/Schatten.lean)); no \(\ell^p\) gauge instance on infinite sequences is given. These are \(s\)-number ideals on Hilbert spaces; nuclear operators between Banach spaces as sums \(\sum f_j\otimes y_j\), \(p\)-summing operators, and Pietsch factorization are not formalized.

**Compact and Fredholm operators.** For a compact operator \(K\) on a Banach space, \(I-K\) has finite-dimensional kernel, closed range, and finite-dimensional cokernel ([Riesz theory](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Operator/Compact/RieszTheory.lean)). Compact perturbations preserve the Fredholm index ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fredholm/CompactPerturbation.lean)). Compact and Fredholm operators belong to Sections 15 and 21.

**Synopsis entries.** Partly covered: 17.59 (TauCeti: the Hilbert-space trace-class analogue through the nuclear gauge \(\sum_na_n(T)\), with ideal inequality and compactness; nuclear representations, the nuclear norm on Banach spaces and one-summing are absent), 17.61 (TauCeti: for an inner product space \(X\), compact operators into \(X\) are norm limits of finite-rank operators; the characterization of the approximation property is absent), 17.64 (TauCeti: the index and ideal inequalities in full generality; the singular-value identification only on finite-dimensional spaces and for diagonal operators). Not covered: 17.52–17.58, 17.60, 17.62, 17.63.

## Metric structure and nonlinear equivalence

[Mathematical scope](SYNOPSIS17.md#metric-structure-and-nonlinear-equivalence).

### Mathlib

**Mazur–Ulam theorem.** A surjective isometry between real normed spaces is affine (`IsometryEquiv.toRealAffineIsometryEquiv`), and one fixing zero is a real linear isometry (`IsometryEquiv.toRealLinearIsometryEquivOfMapZero`) (`Analysis/Normed/Affine/MazurUlam.lean`).

**Rademacher's theorem, finite-dimensional target.** A Lipschitz map between finite-dimensional real normed spaces is differentiable almost everywhere with respect to an additive Haar measure (`LipschitzWith.ae_differentiableAt`, `Analysis/Calculus/Rademacher.lean`). TauCeti localizes this to locally Lipschitz maps ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Rademacher.lean)). Banach-space targets with the Radon–Nikodým property are not treated.

**Synopsis entries.** Covered: 17.65 (Mathlib). Partly covered: 17.67 (Mathlib: finite-dimensional targets only). Not covered: 17.66, 17.75, 17.68, 17.69.
