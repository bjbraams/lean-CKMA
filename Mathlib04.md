# 4. Real analysis, measure, and integration

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Some roots below are directory prefixes; the individual `.lean` files cited are the importable modules. The roots for this section are `Mathlib.MeasureTheory.MeasurableSpace`, `Mathlib.MeasureTheory.OuterMeasure`, `Mathlib.MeasureTheory.PiSystem`, `Mathlib.MeasureTheory.Measure`, `Mathlib.MeasureTheory.Integral`, `Mathlib.MeasureTheory.Function`, `Mathlib.MeasureTheory.Covering`, `Mathlib.MeasureTheory.VectorMeasure`, `Mathlib.MeasureTheory.Constructions`, and `Mathlib.MeasureTheory.Group`.

**Namespaces.** `MeasureTheory`, with nested `Measure`, `OuterMeasure`, `VectorMeasure`, `SignedMeasure`, `ComplexMeasure`, `Lp`, `SimpleFunc`, `FiniteMeasure`, and `ProbabilityMeasure`. Covering and differentiation lemmas are also declared in `Vitali`, `VitaliFamily`, and `Besicovitch`. The interval integral is `intervalIntegral`. The Riesz–Markov–Kakutani constructions are `RealRMK` and `NNRealRMK`. Standard Borel spaces are `StandardBorelSpace`.

This note records the graduate measure-and-integration core of Section 4, in the sense of Folland, Rudin, Royden, Tao, Stein–Shakarchi, Halmos, and Cohn: measurable spaces, construction of measures, the Lebesgue integral and its convergence theorems, product measures, signed and complex measures, \(L^p\), Haar measure, differentiation of measures, and weak convergence. Probability limit theorems are left to Section 6, and the fine structure of real functions to Section 5.

## Measurable spaces

A measurable space is a set with a σ-algebra: a family of subsets containing the empty set and closed under complements and countable unions. A map is measurable when the preimage of every measurable set is measurable. On a fixed set the σ-algebras form a complete lattice under inclusion, and every family of sets generates a least σ-algebra containing it. A map \(f\) induces a Galois connection between the σ-algebras on its domain and those on its codomain (`MeasureTheory/MeasurableSpace/Defs.lean`, `MeasureTheory/MeasurableSpace/Basic.lean`).

Dynkin’s π–λ theorem is proved as an induction principle. A π-system, in the form used here, is a family closed under binary intersections whenever the intersection is nonempty. A Dynkin system contains the empty set and is closed under complements and under countable unions of pairwise disjoint sets. A predicate that holds on a π-system, and is preserved by complements and disjoint countable unions, holds on the generated σ-algebra. Generating a π-system and then a σ-algebra produces the same σ-algebra as generating directly (`MeasureTheory/PiSystem.lean`).

## Outer measures and measures

An outer measure assigns to every subset an extended nonnegative real, sends the empty set to zero, and is monotone and countably subadditive (`MeasureTheory/OuterMeasure/Defs.lean`). From any set function that sends the empty set to zero one obtains a greatest outer measure lying below it, by taking infima of sums over countable covers (`MeasureTheory/OuterMeasure/OfFunction.lean`).

A set is Carathéodory measurable for an outer measure \(m\) when \(m(t) = m(t \cap s) + m(t \setminus s)\) for every test set \(t\). These sets form a σ-algebra (`MeasureTheory/OuterMeasure/Caratheodory.lean`). If a prescribed σ-algebra sits inside the Carathéodory σ-algebra, the outer measure restricts to a measure on it (`MeasureTheory/Measure/OuterMeasure.lean`).

A measure on a measurable space takes values in the extended nonnegative reals, vanishes on the empty set, and is countably additive on pairwise disjoint measurable sets. In the formalization a measure is an outer measure that is countably additive on measurable sets and coincides with the canonical extension of its restriction. The symbol \(\mu(s)\) therefore makes sense for an arbitrary set: it is the outer-measure value. Countable additivity is asserted for measurable sets, and countable subadditivity holds for all sets. Measures form a complete lattice and are closed under multiplication by extended nonnegative scalars (`MeasureTheory/Measure/MeasureSpaceDef.lean`).

A set is null measurable when it agrees almost everywhere with a measurable set. Equivalently, it differs from a measurable set by a null set. Null measurable sets form a σ-algebra. The completion of \(\mu\) is the same set function, read on that larger σ-algebra, and it is a complete measure: every subset of a null set is measurable (`MeasureTheory/Measure/NullMeasurable.lean`).

\(\mu\) is absolutely continuous with respect to \(\nu\), written \(\mu \ll \nu\), when every \(\nu\)-null set is \(\mu\)-null. This is equivalent to inclusion of the almost-everywhere filters (`MeasureTheory/Measure/AbsolutelyContinuous.lean`). The two measures are mutually singular when some measurable set carries all the \(\nu\)-mass and none of the \(\mu\)-mass (`MeasureTheory/Measure/MutuallySingular.lean`).

A measure is s-finite when it is a countable sum of finite measures, and σ-finite when the space is a countable union of sets of finite measure (`MeasureTheory/Measure/Typeclasses/SFinite.lean`).

The first Borel–Cantelli lemma is proved: if \(\sum_i \mu(s_i)\) is finite, then almost every point lies in only finitely many of the sets \(s_i\) (`MeasureTheory/OuterMeasure/BorelCantelli.lean`). The second lemma, for independent events, belongs to the probability library.

## Contents and regularity

A content on compact sets takes values in the extended nonnegative reals and is additive on disjoint sets in its domain, subadditive, and monotone. Its inner content on an open set is the supremum of the content of compact subsets. The associated outer measure of a set is the infimum of the inner content of open sets containing it. Restriction to the Borel sets yields a Borel measure. The construction is given for \(R_1\) spaces. The measure is outer regular by design, and it is regular when the space is locally compact (`MeasureTheory/Measure/Content.lean`).

Several regularity predicates are distinguished, because they diverge outside σ-compact spaces (`MeasureTheory/Measure/Regular.lean`).

- Outer regular: every measurable set is approximated from above by open sets.
- Weakly regular: outer regular, and every open set is approximated from inside by closed sets. A finite measure on a pseudometrizable Borel space is weakly regular, and so is a locally finite measure on a second-countable pseudometrizable Borel space.
- Regular: finite on compact sets, outer regular, and every open set is approximated from inside by compact sets.
- Inner regular: every measurable set is approximated from inside by compact sets. A companion predicate asks this only for measurable sets of finite measure.

A finite inner-regular measure is tight. A set of measures is tight when, for every \(\varepsilon > 0\), one compact set captures all but at most \(\varepsilon\) of the mass of every measure in the set. These definitions are in `MeasureTheory/Measure/Tight.lean`. The converse implication from relative compactness requires topological hypotheses; for probability measures on a complete second-countable metric space it is proved in `MeasureTheory/Measure/Prokhorov.lean`.

## Lebesgue measure, Stieltjes measure, products, and Hausdorff measure

Lebesgue measure on \(\mathbb{R}\) is the additive Haar measure of the line, and it coincides with the Stieltjes measure of the identity function. The product measure on \(\mathbb{R}^n\) is translation invariant. A linear endomorphism of \(\mathbb{R}^n\) multiplies Lebesgue measure by the absolute value of its determinant. The same scaling holds for any additive Haar measure on a finite-dimensional real vector space (`MeasureTheory/Measure/Lebesgue/Basic.lean`, `MeasureTheory/Measure/Lebesgue/EqHaar.lean`).

A Stieltjes function on a conditionally complete dense linear order is monotone and right-continuous. It induces a Borel measure giving mass \(f(b) - f(a)\) to the half-open interval \((a, b]\). Any monotone function determines a Stieltjes function by passage to the right limit. On an order with a least element, a Stieltjes measure gives that point mass zero, so a Dirac mass there is not a Stieltjes measure (`MeasureTheory/Measure/Stieltjes.lean`).

If \(\mu\) and \(\nu\) are s-finite, their product is the s-finite measure on the product space determined by
\[
(\mu \otimes \nu)(s) = \int \nu\{y : (x, y) \in s\}\, d\mu(x)
\]
for measurable \(s\), and \((\mu \otimes \nu)(A \times B) = \mu(A)\,\nu(B)\) for measurable rectangles (`MeasureTheory/Measure/Prod.lean`).

Hausdorff measure of dimension \(d\) is obtained from the metric outer measures that charge a set by at most the \(d\)-th power of its diameter, once the diameter is smaller than a scale \(\delta\), and then by taking the supremum over \(\delta\). Carathéodory’s criterion makes this a Borel measure. If \(d < d'\), then either the \(d\)-dimensional measure of a set is infinite or the \(d'\)-dimensional measure is zero. Hausdorff dimension is defined from that dichotomy. The same construction accepts a general gauge of the diameter, or a general set function, in place of the power of the diameter (`MeasureTheory/Measure/Hausdorff.lean`).

## Haar measure

On a locally compact Hausdorff group there exists a left Haar measure. The construction follows the compact-set covering argument. For a compact set \(K\) and a neighborhood \(U\) of the identity, \((K : U)\) is the least number of left translates of \(U\) needed to cover \(K\). Fixing a compact set \(K_0\) with nonempty interior, one considers the functions \(K\mapsto(K:U)/(K_0:U)\). Tychonoff’s theorem supplies a cluster point as \(U\) shrinks to the identity. The construction chooses such a cluster point; it does not assert convergence of the whole family of ratios. The resulting content extends to a regular left-invariant measure, normalized so that \(K_0\) has measure one. On compact sets, \(h(K)\) lies between the measure of the interior of \(K\) and the measure of \(K\) (`MeasureTheory/Measure/Haar/Basic.lean`).

Uniqueness holds up to a scalar, with the scalar depending on the two measures. Two left-invariant measures that are finite on compact sets integrate continuous compactly supported functions equally up to that scalar, and they agree up to the scalar on sets with compact closure and on open sets. Inner-regular left-invariant measures coincide up to a scalar, and so do regular ones. On a second-countable group, two Haar measures coincide up to a scalar. On a compact group, left-invariant measures coincide up to a scalar. Two Haar probability measures are equal (`MeasureTheory/Measure/Haar/Unique.lean`).

If \(\mu\) is an inner-regular left Haar measure, right translation by \(g^{-1}\) produces another left Haar measure, hence a scalar \(\Delta(g)\) with \(\mu(A g^{-1}) = \Delta(g)\,\mu(A)\). This modular character is a homomorphism to the positive reals and does not depend on the choice of \(\mu\). Continuity of \(\Delta\) is recorded as still to be proved (`MeasureTheory/Group/ModularCharacter.lean`).

## Signed, complex, and vector measures

A vector measure with values in a topological additive monoid is countably additive on measurable sets, in the sense of convergent sums, and sends the empty set and every nonmeasurable set to zero. A signed measure is a real-valued vector measure, and a complex measure is a complex-valued one (`MeasureTheory/VectorMeasure/Defs.lean`). Every complex measure is \(s + it\) for signed measures \(s\) and \(t\), and complex measures are equivalent to pairs of signed measures (`MeasureTheory/Measure/Complex.lean`).

The Hahn decomposition theorem splits a signed measure into complementary measurable sets, one positive and one negative for the measure (`MeasureTheory/VectorMeasure/Decomposition/Hahn.lean`). An unsigned form compares two finite positive measures: some measurable set is such that the second measure dominates the first on its subsets, and the first dominates the second on subsets of the complement (`MeasureTheory/Measure/Decomposition/Hahn.lean`).

The Jordan decomposition writes a signed measure uniquely as the difference of two mutually singular finite positive measures (`MeasureTheory/VectorMeasure/Decomposition/Jordan.lean`).

The Lebesgue decomposition theorem, for σ-finite positive measures \(\mu\) and \(\nu\), writes \(\mu\) as the sum of a measure singular to \(\nu\) and a measure with a measurable density with respect to \(\nu\). The singular part and the density are unique in that representation (`MeasureTheory/Measure/Decomposition/Lebesgue.lean`). The same decomposition holds for a signed measure against a σ-finite positive measure, by applying the positive result to the Jordan parts (`MeasureTheory/VectorMeasure/Decomposition/Lebesgue.lean`).

The Radon–Nikodym theorem is the absolutely continuous case. When a Lebesgue decomposition exists, \(\mu \ll \nu\) if and only if \(\mu\) is \(\nu\) weighted by the Radon–Nikodym derivative. For σ-finite measures the decomposition exists, so the theorem applies. Integrating the derivative over a measurable set recovers the measure of that set. There is a signed-measure form (`MeasureTheory/Measure/Decomposition/RadonNikodym.lean`).

## The integral

A simple function has finite range and measurable fibers. Every Borel measurable function with values in the extended nonnegative reals is the pointwise supremum of an increasing sequence of simple functions. To prove a statement for every such measurable function, it is enough to check it on multiples of indicators and to know that it passes to sums and to suprema of increasing sequences (`MeasureTheory/Function/SimpleFunc.lean`). If the target of a measurable function is a separable subset of a metric space, simple functions with values in that subset approximate it pointwise (`MeasureTheory/Function/SimpleFuncDense.lean`).

The lower Lebesgue integral takes values in the extended nonnegative reals. It is defined for functions into those reals, and the integral over a set is the integral against the restricted measure (`MeasureTheory/Integral/Lebesgue/Basic.lean`).

The monotone convergence theorem identifies the integral of the pointwise supremum of an increasing sequence of measurable extended-nonnegative functions with the supremum of the integrals. The same holds for an almost-everywhere measurable sequence, and for a supremum indexed by a countable directed set (`MeasureTheory/Integral/Lebesgue/Add.lean`).

Fatou’s lemma, for an almost-everywhere measurable family of extended-nonnegative functions indexed along a countably generated filter, says that the integral of the liminf is at most the liminf of the integrals (`MeasureTheory/Integral/Lebesgue/Add.lean`).

The dominated convergence theorem for the lower integral: if measurable extended-nonnegative functions converge almost everywhere, and are dominated by a single function of finite integral, then the integrals converge to the integral of the limit. The almost-everywhere measurable variant is included, as is a version along a countably generated filter (`MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean`).

Markov’s inequality, also called Chebyshev’s first inequality, states that for \(\varepsilon > 0\) and a nonnegative function,
\[
\mu\{x : \varepsilon \le f(x)\} \le \frac{1}{\varepsilon} \int f\, d\mu
\]
(`MeasureTheory/Integral/Lebesgue/Markov.lean`).

Tonelli’s theorem: for a measurable function on a product of s-finite measure spaces, with values in the extended nonnegative reals,
\[
\int f\, d(\mu \otimes \nu) = \iint f(x, y)\, d\nu(y)\, d\mu(x),
\]
and the two orders of integration agree (`MeasureTheory/Measure/Prod.lean`).

The Bochner integral extends integration to functions with values in a Banach space. It is obtained by passing through the space of integrable equivalence classes, and a function that is not integrable is assigned integral zero. On integrable functions the integral is linear, depends only on the almost-everywhere class, and satisfies
\[
\Bigl\|\int f\, d\mu\Bigr\| \le \int \|f\|\, d\mu
\]
(`MeasureTheory/Integral/Bochner/Basic.lean`). A function is strongly measurable when it is an everywhere pointwise limit of simple functions, and finitely strongly measurable when those simple functions may be taken with support of finite measure. If the target is second countable, strong measurability agrees with measurability. If the measure is σ-finite, strong measurability agrees with finite strong measurability (`MeasureTheory/Function/StronglyMeasurable/Basic.lean`).

Dominated convergence for the Bochner integral: if almost-everywhere strongly measurable functions with values in a real normed space converge almost everywhere and are dominated in norm by one integrable real function, then the integrals converge to the integral of the limit. The result extends to countably generated filters, and to series whose norms are dominated by a summable family of integrable functions (`MeasureTheory/Integral/DominatedConvergence.lean`).

Fubini’s theorem: if \(f\) is integrable on a product of s-finite spaces and takes values in a second-countable Banach space, then for almost every \(x\) the slice \(y \mapsto f(x, y)\) is integrable, \(x \mapsto \int \|f(x, y)\|\, d\nu(y)\) is integrable, and the integral equals the iterated integral in either order. For a continuous compactly supported integrand there is a Fubini theorem that does not require σ-finiteness of the measures (`MeasureTheory/Integral/Prod.lean`).

The layer-cake representation writes the integral of a nonnegative measurable function as the integral of its tail measures,
\[
\int f\, d\mu = \int_0^\infty \mu\{f \ge t\}\, dt,
\]
with a companion formula using strict inequality. More generally, if \(G\) vanishes at the origin and is absolutely continuous and increasing on the nonnegative reals, with derivative \(g\), then \(\int G \circ f\) equals the integral of the tail measures against \(g\) (`MeasureTheory/Integral/Layercake.lean`).

Hölder’s inequality for the lower integral of extended-nonnegative functions, with conjugate exponents \(p\) and \(q\), bounds the integral of a product by the product of the \(L^p\) and \(L^q\) integrals. A weighted form covers a finite family of functions whose exponents sum to one. Minkowski’s inequality gives the triangle inequality in \(L^p\) for \(p \ge 1\) (`MeasureTheory/Integral/MeanInequalities.lean`).

The Riesz–Markov–Kakutani theorem is proved for a locally compact Hausdorff space. A positive real-linear functional on the continuous real functions of compact support is integration against a regular Borel measure, unique among regular Borel measures. The corresponding statement for additive functionals with values in the nonnegative reals is reduced to the real-linear case (`MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`, `MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean`). The argument is the one in Rudin’s *Real and Complex Analysis*, built from a content on compact sets.

Vitali–Carathéodory approximation, in a strict form that assumes the measure is σ-finite and regular: an integrable real function lies strictly below an extended-real-valued lower-semicontinuous function, and strictly above an extended-real-valued upper-semicontinuous function, finite almost everywhere, whose integrals are arbitrarily close to its own (`MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean`).

## \(L^p\) spaces

Two strongly measurable functions are identified when they agree almost everywhere. The resulting space of classes carries the pointwise linear structure and the almost-everywhere partial order of the target (`MeasureTheory/Function/AEEqFun.lean`).

For an extended exponent \(p\), the space \(L^p\) consists of those classes whose \(L^p\) seminorm is finite. At a finite positive exponent the seminorm is the \(p\)-th root of the integral of the \(p\)-th power of the norm. At the exponent \(\infty\) it is the essential supremum of the norm (`MeasureTheory/Function/LpSpace/Basic.lean`, `MeasureTheory/Function/EssSup.lean`). For \(1 \le p \le \infty\), and for a Banach space of values, \(L^p\) is a Banach space (`MeasureTheory/Function/LpSpace/Complete.lean`).

For \(p < \infty\), simple functions are dense in \(L^p\). A predicate on \(L^p\), or on the integrable functions, may be proved by checking it on simple functions and passing to the limit (`MeasureTheory/Function/SimpleFuncDenseLp.lean`).

Continuous functions are dense in the same range of exponents. On a normal space, with a weakly regular measure, bounded continuous functions are dense in \(L^p\) for \(p < \infty\). On a locally compact space, with a regular measure, continuous functions of compact support are dense (`MeasureTheory/Function/ContinuousMapDense.lean`).

A continuous bilinear map of Banach spaces induces a bilinear map on a Hölder triple of \(L^p\) spaces. When the exponents are conjugate, integration against that bilinear map defines a continuous pairing of \(L^p\) with \(L^q\). Taking the bilinear map to be the evaluation of the bidual embedding, one obtains a map from \(L^p\) of the dual into the dual of \(L^q\) (`MeasureTheory/Function/Holder.lean`).

## Modes of convergence

Egorov’s theorem: on a finite measure space, a sequence of measurable functions that converges almost everywhere converges uniformly off a set of arbitrarily small measure (`MeasureTheory/Function/Egorov.lean`).

Convergence in measure means that for every \(\varepsilon > 0\), the measure of the set where two functions differ by at least \(\varepsilon\) tends to zero. Almost-everywhere convergence on a finite measure space implies convergence in measure. A sequence that converges in measure has a subsequence that converges almost everywhere. For \(0<p\le\infty\), convergence in \(L^p\) implies convergence in measure (`MeasureTheory/Function/ConvergenceInMeasure.lean`).

A family is uniformly integrable when the \(L^p\) norm of its restriction to a set of small measure is uniformly small. In the probabilistic form one also asks for a uniform bound on the \(L^p\) norms. Vitali’s convergence theorem, for a finite measure and an exponent \(1 \le p < \infty\): convergence in \(L^p\) is equivalent to uniform integrability together with convergence in measure. Almost-everywhere convergence and uniform integrability already give \(L^p\) convergence under the same hypotheses (`MeasureTheory/Function/UniformIntegrable.lean`).

## Change of variables and differentiation of measures

Let \(\mu\) be an additive Haar measure on a finite-dimensional real vector space, and let \(f\) be injective and differentiable on a measurable set \(s\). Then \(f(s)\) is measurable and
\[
\mu(f(s)) = \int_s \lvert \det Df(x) \rvert\, d\mu(x).
\]
The derivative is almost everywhere measurable. The same Jacobian factor implements the change of variables in the lower integral and in the Bochner integral. A null set is sent to a null set. If the derivative is nowhere invertible on \(s\), then \(f(s)\) has measure zero. One-dimensional statements, for monotone and antitone maps, use the ordinary derivative in place of the determinant (`MeasureTheory/Function/Jacobian.lean`, `MeasureTheory/Function/JacobianOneDim.lean`).

The topological Vitali covering theorem extracts, from a family of balls of bounded radii, a disjoint subfamily such that every ball of the original family is contained in the five-times enlargement of some selected ball. The measurable form, for a fine family of closed sets that occupy a definite fraction of a ball of comparable size, extracts a disjoint subfamily covering almost every point of the set at which the family is fine (`MeasureTheory/Covering/Vitali.lean`).

The Besicovitch covering theorem applies in a metric space that admits no satellite configuration of \(N+1\) balls, a condition satisfied by finite-dimensional real vector spaces. From any family of balls of bounded radii one can extract \(N\) disjoint subfamilies whose union covers every center. The measurable form covers almost every point by disjoint admissible balls, and small balls form a Vitali family (`MeasureTheory/Covering/Besicovitch.lean`).

Differentiation of measures along a Vitali family, on a second-countable metric space: for almost every point, as the sets of the family shrink to the point, the ratio of two measures tends to the Radon–Nikodym derivative. Almost every point of a measurable set is a density point along the family, and the average oscillation of an integrable function tends to zero (`MeasureTheory/Covering/Differentiation.lean`). For a locally finite, uniformly locally doubling measure on a σ-compact metric space, the same density statement holds along sequences of closed balls containing the point, without requiring the centers to be fixed (`MeasureTheory/Covering/DensityTheorem.lean`).

On the line, if a Banach-valued function is locally integrable, then for almost every \(x\) the indefinite integral \(\int_c^x f\) is differentiable at \(x\) with derivative \(f(x)\). The same holds almost everywhere on a compact interval when \(f\) is integrable on that interval (`MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`).

## Weak convergence

Finite measures, and probability measures, carry the topology of weak convergence: the coarsest topology making integration of every bounded continuous nonnegative function continuous. A net of finite measures converges weakly if and only if the integrals of all such functions converge, and likewise for probability measures and bounded continuous random variables (`MeasureTheory/Measure/FiniteMeasure.lean`, `MeasureTheory/Measure/ProbabilityMeasure.lean`).

The portmanteau implications are proved separately (`MeasureTheory/Measure/Portmanteau.lean`). Write (T) for weak convergence, (C) for the limsup inequality on closed sets, (O) for the liminf inequality on open sets, and (B) for convergence on Borel sets whose boundary is null.

- (C) and (O) are equivalent.
- (O) implies (B).
- (B) implies (C).
- (T) implies (C) when closed sets can be approximated pointwise from above by decreasing sequences of bounded continuous functions. Metrizable and pseudo-metrizable spaces satisfy that approximation property.
- For a sequence of Borel probability measures, (O) implies (T), and (C) implies (T).
- If the measures are tight, the closed-set inequality may be weakened to a compact-set inequality and still yields weak convergence.
- If a sequence of probability measures converges on every member of a π-system, and the π-system contains arbitrarily small neighborhoods of every point, then the sequence converges weakly.

The space of probability measures on a compact Hausdorff space is compact. The proof uses ultrafilters and the Riesz–Markov–Kakutani theorem, and it does not assume second-countability or metrizability. On a Hausdorff Borel space, the full set of probability measures satisfying \(\mu(K_n^c)\le u_n\) for every \(n\), where the \(K_n\) are compact and \(u_n\to0\), is compact if the space is normal or the \(K_n\) are increasing. An arbitrary subset of this set need not itself be compact. A tight set of probability measures has compact closure. In a complete second-countable metric space the converse holds: a set of probability measures with compact closure is tight. The finite-measure versions also require a uniform bound on total masses (`MeasureTheory/Measure/Prokhorov.lean`).

The set of all measures on a measurable space, probabilities included, is itself a measurable space, and the assignment is a monad on measurable spaces (`MeasureTheory/Measure/GiryMonad.lean`).

## Polish spaces and analytic sets

A standard Borel space is a measurable space isomorphic to the Borel σ-algebra of some Polish topology. A set is analytic when it is a continuous image of a Polish space; equivalently, it is empty or a continuous image of the Baire space \(\mathbb{N}^{\mathbb{N}}\). Continuous images of analytic sets are analytic, and in a Polish space every Borel set is analytic (`MeasureTheory/Constructions/Polish/Basic.lean`).

Lusin’s separation theorem: two disjoint analytic sets are contained in complementary Borel sets. The Lusin–Souslin theorem: a continuous injective image of a Borel subset of a Polish space is Borel, and a continuous injection from a Polish space is a measurable embedding for the Borel σ-algebras. A measurable injection from a standard Borel space into a countably separated measurable space is a measurable embedding as well.

The Lévy–Prokhorov metric is also constructed. On a separable metric Borel space its topology on probability measures agrees with weak convergence (`MeasureTheory/Measure/LevyProkhorovMetric.lean`, `LevyProkhorov.eq_convergenceInDistribution`).

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti adds a useful part of real-variable integration theory: the centred Hardy–Littlewood maximal function, its weak \((1,1)\) estimate, and its strong \((p,p)\) estimate for \(1<p<\infty\), for additive Haar measure on a finite-dimensional real normed space. The source proves measurability as well as the estimates ([maximal function](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/Integral/MaximalFunction.lean)). It also proves diagonal Marcinkiewicz interpolation between two finite weak-type exponents; the off-diagonal interpolation theorem is not included ([interpolation](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/Integral/Marcinkiewicz/General.lean)).

For \(1\le p<\infty\), normalized smooth convolution averages converge in \(L^p\), including for Banach-valued functions ([approximate identities](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/Function/Lp/ApproximateIdentity.lean)). A Fréchet–Kolmogorov compactness theorem proves sufficiency of boundedness, uniform translation continuity, and uniform tightness, for finite-dimensional target spaces; this file does not establish the converse characterization ([compactness](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/Function/Lp/FrechetKolmogorov.lean)).

## Topics of Section 4 not found in either inspected library

- Approximation of a finite-measure measurable function by a continuous function, off a set of small measure. The theorems of Lusin that are proved here are the separation theorem for analytic sets and the Lusin–Souslin theorem.
- A complex-linear Riesz–Markov–Kakutani theorem. The real-linear and nonnegative theorems are proved.
- The identification of the dual of \(L^p\) with \(L^q\). The integral pairing of \(L^p\) with \(L^q\), and the induced map into the dual, are constructed.
- Density of simple functions in \(L^\infty\). The file that proves density for \(p < \infty\) leaves the finite-dimensional \(L^\infty\) case as a remaining statement.
- The classical Vitali–Carathéodory theorem with a weak inequality and without σ-finiteness. The proved statement is the strict approximation, and it assumes a σ-finite regular measure.
- Continuity of the modular character of a locally compact group. The character itself is defined.
- The Diestel–Uhl theory of Banach-valued vector measures: a Radon–Nikodym theorem for general Banach targets, relative weak compactness of ranges, and Lyapunov’s convexity theorem. Signed and complex measures, and vector measures with values in a topological additive monoid, are present.
- Capacities, measure algebras, the lifting theorem, and Maharam’s theorem.
- Differentiable measures on infinite-dimensional spaces.

Gaussian measures, conditional expectation, and the limit theorems of probability are developed in the probability library and will be recorded with Section 6. Denjoy–Young–Saks and the Zahorski theory belong to Section 5; the Lebesgue differentiation theorem is included above because the Section 4 texts treat it with the integral.
