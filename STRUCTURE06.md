# Structure 06: Probability: measure-theoretic foundations and limit theory

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS06.md); [bibliographical scope](CKMA-bib.md#ckma-06); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; the **Synopsis entries** line at the end of each section states which numbered results are covered.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Probability`, `Mathlib.InformationTheory.KullbackLeibler`, `Mathlib.MeasureTheory.Function.ConditionalExpectation`, `Mathlib.MeasureTheory.Function.ConvergenceInMeasure`, `Mathlib.MeasureTheory.Function.ConvergenceInDistribution`, `Mathlib.MeasureTheory.Function.UniformIntegrable`, `Mathlib.MeasureTheory.Measure.CharacteristicFunction`, `Mathlib.MeasureTheory.Measure.LevyConvergence`, `Mathlib.MeasureTheory.Measure.Portmanteau`, `Mathlib.MeasureTheory.Measure.Prokhorov`, `Mathlib.MeasureTheory.Constructions.Projective`, `Mathlib.Combinatorics.SetFamily.FourFunctions`.

**Namespaces.** `ProbabilityTheory`, with nested `Kernel`. Conditional expectation, martingales, characteristic functions, and convergence in measure and in distribution are declared in `MeasureTheory`. Discrete distributions are `PMF`. TauCeti declarations are mostly in `TauCeti` and `TauCeti.Probability`, with extensions of `MeasureTheory` and `ProbabilityTheory`.

<a id="structure-06a"></a>

## 06A. Probability Foundations and Limit Theory

Independence, conditioning, construction of laws, scalar limit theorems, discrete-time martingales, and Gaussian and exchangeable laws are grouped here. Continuous-time processes are recorded in [Section 08](STRUCTURE08.md).

### Independence, construction, and zero–one laws

[Mathematical scope](SYNOPSIS06.md#independence-construction-and-zeroone-laws).

#### Mathlib

**Probability spaces, laws, and elementary conditioning.**

A probability measure is a measure of total mass one. The library writes \(\mathbb{P}\) for the canonical measure of a probability space, \(\mathbb{E}[X]\) for its integral, and \(\partial P/\partial Q\) for a Radon–Nikodym derivative (`Probability/Notation.lean`).

A random variable \(X\) has law \(\mu\) under \(P\) when \(X\) is almost everywhere measurable and the pushforward \(P\circ X^{-1}\) equals \(\mu\). Random variables on possibly different spaces are identically distributed when their laws coincide. On a countable index set, a family of i.i.d. coordinates has the product law (`Probability/HasLaw.lean`, `Probability/IdentDistrib.lean`, `Probability/IdentDistribIndep.lean`). There are lemmas producing a family of random variables with prescribed laws and mutual independence (`Probability/HasLawExists.lean`).

On a finite nonempty set the counting measure conditioned to the set is the uniform probability, and the probability of an event is the ratio of cardinalities (`Probability/UniformOn.lean`). A probability mass function is a function to the extended nonnegative reals summing to one. It determines a probability measure for which every set is measurable, and conversely a probability measure on a countable space with measurable singletons determines a mass function (`Probability/ProbabilityMassFunction/Basic.lean`).

The cumulative distribution function of a probability measure on \(\mathbb{R}\) is the monotone right-continuous function \(F(x)=\mu((-\infty,x])\), with limits \(0\) and \(1\) at \(-\infty\) and \(+\infty\). Two probability measures on the line are equal if and only if their distribution functions agree (`Probability/CDF.lean`).

A random variable has a density \(f\) with respect to a reference measure \(\mu\) when its law is absolutely continuous with respect to \(\mu\) and \(f\) is a Radon–Nikodym derivative: \(\mathbb{P}(X\in S)=\int_S f\,d\mu\) (`Probability/Density.lean`).

`Probability/Distributions/` constructs Bernoulli, binomial, geometric, and Poisson laws on discrete spaces; Beta, Cauchy, exponential, Gamma, and Pareto laws on the line; and the uniform law.

**Independence.**

A family of set systems is independent when the measure of a finite intersection, with one set from each of finitely many distinct systems, equals the product of the measures. A family of σ-algebras is independent when their collections of measurable sets are. An event is independent of others when the σ-algebra it generates is. Random variables are independent when the σ-algebras they generate are (`Probability/Independence/Basic.lean`). Two random variables are independent if and only if the law of the pair is the product of the laws (`indepFun_iff_map_prod_eq_prod_map_map`).

For independent random variables the expectation of a product of integrable functions of them is the product of the expectations (`IndepFun.integral_fun_comp_mul_comp`), and on a finite measure independence is equivalent to this factorization for bounded measurable test functions (`indepFun_iff_integral_comp_mul`, `Probability/Independence/Integration.lean`). On Borel spaces in which closed sets can be approximated from outside by bounded continuous functions, independence is equivalent to factorization of expectations of products of bounded continuous functions (`Probability/Independence/BoundedContinuousFunction.lean`). In second-countable real Hilbert spaces with their Borel σ-algebras, two random variables, or a finite family, are independent if and only if the joint characteristic function is the product of the marginal characteristic functions. In second-countable real Banach spaces with their Borel σ-algebras the same factorization is proved for the characteristic function formed with continuous linear functionals (`Probability/Independence/CharacteristicFunction.lean`).

An infinite family of probability measures has a unique product probability measure on the product space, characterized by its values on finite-dimensional cylinders (`Probability/ProductMeasure.lean`). Independent sequences, and indeed arbitrary families, with prescribed marginal laws are therefore constructed, and independence of arbitrary families is developed against that product (`Probability/Independence/InfinitePi.lean`). Projective families of finite-dimensional laws are defined, and a projective limit, when it exists, is unique among finite measures (`MeasureTheory/Constructions/Projective.lean`). The additive content that such a family induces on cylinder sets is constructed as the first step toward Kolmogorov's extension theorem (`MeasureTheory/Constructions/ProjectiveFamilyContent.lean`, `MeasureTheory/Constructions/ClosedCompactCylinders.lean`); the existence half for a general projective family is not stated in Mathlib.

Kolmogorov’s zero–one law: if \((s_i)\) is an independent sequence of sub-σ-algebras, every set in the tail σ-algebra has probability \(0\) or \(1\) (`measure_zero_or_one_of_measurableSet_limsup_atTop`, `Probability/Independence/ZeroOne.lean`).

The first Borel–Cantelli lemma is the measure-theoretic statement from [Section 04](STRUCTURE04.md): a summable sequence of measures charges almost every point only finitely often (`measure_limsup_atTop_eq_zero`). The second lemma is probabilistic: if the events are mutually independent and the sum of their probabilities diverges, the limsup has probability one (`measure_limsup_eq_one`, `Probability/BorelCantelli.lean`). The pairwise-independent version and the ratio form are not stated.

#### TauCeti

Kolmogorov's extension theorem is proved for countable index sets: a projective family of probability laws on finite products, in which every coordinate after the first is standard Borel, has a projective limit. The proof disintegrates the family into transition kernels and applies Mathlib's Ionescu–Tulcea theorem ([sequences](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Measure/ProjectiveLimit/Nat.lean), [countable index sets](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Measure/ProjectiveLimit/Countable.lean), `TauCeti.Measure.exists_isProjectiveLimit_of_countable`). The Hewitt–Savage zero–one law is proved: for an i.i.d. sequence, every event invariant under finite permutations has probability \(0\) or \(1\) ([Hewitt–Savage](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Exchangeability/PathSpace/HewittSavage.lean), `TauCeti.Probability.hewittSavage_trivial_of_iIndep`). A finite measure on \([0,\infty)\) is determined by its Laplace transform, already by its values at the positive integers ([Laplace determinacy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Moments/LaplaceDeterminacy.lean)).

**Synopsis entries.** Covered: 06.2, 06.3, 06.5 (Mathlib), 06.6 (TauCeti). Partly covered: 06.1 (existence for countable index sets in TauCeti; uniqueness and product measures for arbitrary index sets in Mathlib; existence for an arbitrary index set is not stated, but follows by reducing the projective-family content to countably many coordinates), 06.4 (mutually independent events; the pairwise version and the ratio limit are absent).

### Conditional expectation and conditional distributions

[Mathematical scope](SYNOPSIS06.md#conditional-expectation-and-conditional-distributions).

#### Mathlib

**Elementary conditioning.** The conditional probability of a finite measure given a set \(s\) of positive measure is the restriction to \(s\), scaled to a probability. Conditioning twice is conditioning on the intersection, and Bayes’ formula \(\mu(t\mid s)=\mu(s\mid t)\,\mu(t)/\mu(s)\) holds (`Probability/ConditionalProbability.lean`).

**Conditional independence.** Conditional independence of σ-algebras given a third σ-algebra is factorization of the conditional probabilities. On a standard Borel space this is expressed through the conditional-expectation kernel (`Probability/Independence/Conditional.lean`).

**Kernels and disintegration.** A kernel from \(\alpha\) to \(\beta\) is a measurable map from \(\alpha\) into the space of measures on \(\beta\). It is Markov when every value is a probability measure, finite when the total masses are uniformly bounded, and s-finite when it is a countable sum of finite kernels (`Probability/Kernel/Defs.lean`). Deterministic kernels include Dirac masses along a measurable map (`Probability/Kernel/Basic.lean`). Kernels compose, and a measure may be composed with a kernel. The category of measurable spaces and s-finite kernels is developed separately (`Probability/Kernel/Composition`, `Probability/Kernel/Category/SFinKer.lean`).

The Ionescu–Tulcea theorem extends a consistent sequence of finite compositions of kernels to a kernel that, given a trajectory up to time \(a\), returns the law of the entire future trajectory (`Probability/Kernel/IonescuTulcea/Traj.lean`).

A kernel disintegrates a measure \(\rho\) on a product \(\beta\times\Omega\) when \(\rho\) is the composition of its first marginal with that kernel. If \(\Omega\) is standard Borel, such a conditional kernel exists, for a finite measure; the corresponding finite-kernel construction assumes the required countability or countable-generation hypotheses on the parameter and first-factor spaces, and it is unique almost everywhere (`Probability/Kernel/Disintegration/Basic.lean`, `Probability/Kernel/Disintegration/StandardBorel.lean`, `Probability/Kernel/Disintegration/Unique.lean`). The construction on the line passes through a conditional distribution function (`Probability/Kernel/Disintegration/CondCDF.lean`). For random elements \(X,Y\) with \(X\) in a standard Borel space, the conditional distribution `condDistrib` represents conditional expectations: \(\mathbb{E}[f(X,Y)\mid Y]=\int f(x,Y)\,\kappa(Y,dx)\) almost surely (`condExp_prod_ae_eq_integral_condDistrib`, `Probability/Kernel/CondDistrib.lean`). A random variable has conditional distribution \(\kappa\) given another when the law of the pair is the composition of the law of the conditioning variable with \(\kappa\) (`Probability/HasCondDistrib.lean`).

**Conditional expectation.** The conditional expectation of an integrable Banach-valued function \(f\), relative to a sub-σ-algebra \(m\) for which the restricted measure is σ-finite, is an \(m\)-strongly measurable integrable function \(\mu[f\mid m]\) such that
\[
\int_s \mu[f\mid m]\,d\mu = \int_s f\,d\mu
\]
for every \(m\)-measurable \(s\). It is unique in \(L^1\). The construction projects in \(L^2\) onto the \(m\)-measurable functions (`condExpL2`, `MeasureTheory/Function/ConditionalExpectation/CondexpL2.lean`) and extends by the same procedure as the Bochner integral. The tower property holds: conditioning first to a larger σ-algebra and then to a smaller one is the same as conditioning directly to the smaller one (`MeasureTheory/Function/ConditionalExpectation/Basic.lean`).

If \(f\) is almost everywhere \(m\)-strongly measurable, \(g\) is integrable, and \(B(f,g)\) is integrable for a continuous bilinear map \(B\), then almost surely \(\mu[B(f,g)\mid m]=B(f,\mu[g\mid m])\). Scalar multiplication and the product of real functions are the special cases (`MeasureTheory/Function/ConditionalExpectation/PullOut.lean`).

Conditional Jensen: for a convex lower-semicontinuous \(\varphi\) on a closed convex set containing the values of an integrable \(f\), with \(\varphi\circ f\) integrable, \(\varphi(\mu[f\mid m])\le\mu[\varphi\circ f\mid m]\) almost everywhere (`ConvexOn.map_condExp_le`, `MeasureTheory/Function/ConditionalExpectation/CondJensen.lean`). Conditional expectation is a contraction on \(L^p\) for \(1\le p\le\infty\) (`eLpNorm_condExp_le_eLpNorm`, `MeasureTheory/Function/ConditionalExpectation/Real.lean`).

If \(f\) is measurable for one of two independent σ-algebras, its conditional expectation on the other is the constant \(\mathbb{E}[f]\) (`condExp_indep_eq`, `Probability/ConditionalExpectation.lean`). On a standard Borel space the conditional expectation is integration against a kernel: \(\mu[f\mid m](\omega)=\int f\,d\kappa_\omega\) almost everywhere (`Probability/Kernel/Condexp.lean`).

**Synopsis entries.** Covered: 06.7–06.10 (Mathlib). Partly covered: 06.11 (the case of a function of the independent variable alone; the formula for \(h(X,Y)\) is not stated).

### Convergence of random variables and probability laws

[Mathematical scope](SYNOPSIS06.md#convergence-of-random-variables-and-probability-laws).

#### Mathlib

**Convergence in probability.** On a finite measure, almost-everywhere convergence implies convergence in measure (`tendstoInMeasure_of_tendsto_ae`), and so does convergence in \(L^p\) for every \(p\ne0\), including \(0<p<1\) (`tendstoInMeasure_of_tendsto_eLpNorm`). Convergence in measure gives an almost-everywhere convergent subsequence, and on a finite measure convergence in measure is equivalent to every subsequence having a further almost-everywhere convergent subsequence (`TendstoInMeasure.exists_seq_tendsto_ae`, `exists_seq_tendstoInMeasure_atTop_iff`, `MeasureTheory/Function/ConvergenceInMeasure.lean`). Vitali's theorem: for \(1\le p<\infty\) on a finite measure, convergence in \(L^p\) is equivalent to convergence in measure together with uniform integrability (`tendstoInMeasure_iff_tendsto_Lp_finite`, `MeasureTheory/Function/UniformIntegrable.lean`).

**Convergence in distribution.** Random variables converge in distribution when their laws converge in the topology of weak convergence of probability measures. A continuous image preserves convergence in distribution (`TendstoInDistribution.continuous_comp`). Almost-sure convergence and convergence in probability imply convergence in distribution (`tendstoInDistribution_of_ae_tendsto`, `TendstoInMeasure.tendstoInDistribution`). If \(X_n\) converges in distribution and \(Y_n-X_n\) converges to zero in probability, then \(Y_n\) has the same limit (`tendstoInDistribution_of_tendstoInMeasure_sub`). Slutsky’s theorem: if \(X_n\) converges in distribution to \(Z\) and \(Y_n\) converges in probability to a constant \(c\), then \((X_n,Y_n)\) converges in distribution to \((Z,c)\), and \(g(X_n,Y_n)\) converges to \(g(Z,c)\) for continuous \(g\), in particular for sums (`TendstoInDistribution.prodMk_of_tendstoInMeasure_const`, `TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`, `TendstoInDistribution.add_of_tendstoInMeasure_const`, `MeasureTheory/Function/ConvergenceInDistribution.lean`). Convergence in distribution to a constant is not shown to imply convergence in probability.

The portmanteau theorem and Prokhorov’s theorem are the characterizations of this topology proved in [Section 04](STRUCTURE04.md): closed-set and open-set inequalities and convergence on continuity sets, each equivalent to weak convergence (`MeasureTheory/Measure/Portmanteau.lean`). A tight set of probability measures has compact closure, and in a complete second-countable metric space a set with compact closure is tight (`isCompact_closure_of_isTightMeasureSet`, `isTightMeasureSet_of_isCompact_closure`, `MeasureTheory/Measure/Prokhorov.lean`).

#### TauCeti

Inverse transform sampling: the quantile function of a real probability law pushes the uniform law on \((0,1)\) forward to that law ([quantiles](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Quantile.lean), `map_quantile_volume_Ioo`). This is the construction behind the one-dimensional Skorokhod representation, which is not stated. Pinsker's inequality \(d_{\mathrm{TV}}(\mu,\nu)^2\le\tfrac12\mathrm{KL}(\mu\|\nu)\) is proved ([Pinsker](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/InformationTheory/KullbackLeibler/Pinsker.lean)); couplings appear in the optimal-transport files of Section 04, but the maximal coupling is not stated.

**Synopsis entries.** Covered: 06.14, 06.16, 06.17 (Mathlib). Partly covered: 06.12 (all implications except convergence in distribution to a constant implying convergence in probability), 06.13 (the uniform-integrability criterion; the \(L^{1+\delta}\) sufficient condition is not stated), 06.15 (continuous maps only). Not covered: 06.18–06.20.

### Independent sums, random series, and laws of large numbers

[Mathematical scope](SYNOPSIS06.md#independent-sums-random-series-and-laws-of-large-numbers).

#### Mathlib

**Moments.** The \(p\)-th moment of a real random variable is the expectation of its \(p\)-th power, and the central moment subtracts the mean first. The moment-generating function is \(t\mapsto\mathbb{E}[e^{tX}]\), and the cumulant-generating function is its logarithm. For independent random variables the moment-generating function of a sum is the product, and the cumulant-generating function adds (`Probability/Moments/Basic.lean`). On a finite measure, the Chernoff bound says that if \(t\geq 0\) and \(e^{tX}\) is integrable, then
\[
\mu\{X\geq\varepsilon\}\leq\exp(-t\varepsilon+\mathop{\mathrm{cgf}}(t)),
\]
with a matching lower-tail bound for \(t\leq 0\). The variance of a finite sum is the double sum of covariances, so variances add for pairwise independent square-integrable summands, and Chebyshev's inequality \(\mathbb{P}(|X-\mathbb{E}X|\ge c)\le\mathop{\mathrm{Var}}X/c^2\) holds (`variance_sum`, `meas_ge_le_variance_div_sq`, `Probability/Moments/Variance.lean`). Together these give the weak law under \(n^{-2}\sum_{j\le n}\mathop{\mathrm{Var}}X_j\to0\) in one step.

**Laws of large numbers.** The strong law, in Etemadi’s form: if the random variables are pairwise independent, identically distributed, and integrable, then the sample averages converge almost surely to the common expectation (`strong_law_ae`). If they lie in \(L^p\) for \(1\le p<\infty\), the averages converge in \(L^p\) (`strong_law_Lp`). For Banach-valued variables the theorem follows by approximation with simple functions (`Probability/StrongLaw.lean`). Since almost-sure convergence implies convergence in probability on a probability space, the i.i.d. weak law follows. The converse for \(\mathbb{E}|X_1|=\infty\) and Kolmogorov's variance criterion are not stated.

#### TauCeti

The weak law of large numbers in Chebyshev's form for the average of \(n\) independent copies of a square-integrable statistic, with deviation probability at most \(\mathop{\mathrm{Var}}f/(nt^2)\) ([product moments](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Moments/Pi.lean), `TauCeti.meas_ge_le_variance_div_card_mul_sq_pi`), and the strong law on the canonical product space ([strong law](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/StrongLaw.lean), `TauCeti.Probability.strong_law_ae_infinitePi`).

**Synopsis entries.** Covered: 06.24 (Mathlib; the i.i.d. case from the strong law, the variance case from Chebyshev's inequality and additivity of variance). Partly covered: 06.25 (Etemadi's strong law and its \(L^p\) form; the converse and the variance criterion are absent), 06.23 (sufficiency is not stated, but follows from Mathlib's martingale convergence theorem, the variance of independent sums, and Borel–Cantelli; necessity is absent). Not covered: 06.21, 06.22, 06.26–06.28.

### Characteristic functions and classical distributional limits

[Mathematical scope](SYNOPSIS06.md#characteristic-functions-and-classical-distributional-limits).

#### Mathlib

The complex moment-generating function \(z\mapsto\mathbb{E}[e^{zX}]\) is holomorphic on the vertical strip over the interior of the real interval where the moment-generating function exists, and on the imaginary axis it is the characteristic function (`Probability/Moments/ComplexMGF.lean`). Where the real moment-generating function is finite on a neighborhood of a point, it is analytic (`Probability/Moments/MGFAnalytic.lean`).

The characteristic function of a finite measure on an inner product space is
\[
\varphi_\mu(t)=\int \exp(i\langle x,t\rangle)\,d\mu(x).
\]
On a normed space the dual characteristic function uses a continuous linear functional in place of the inner product. On a complete second-countable inner product space, finite measures with the same characteristic function are equal (`Measure.ext_of_charFun`). On a second-countable real Banach space with its Borel σ-algebra, finite measures with the same dual characteristic function are equal. The characteristic function of a convolution is the product (`charFun_conv`, `MeasureTheory/Measure/CharacteristicFunction/Basic.lean`), and that of a sum of independent random variables is the product of theirs (`IndepFun.charFun_map_add_eq_mul`, `iIndepFun.charFun_map_sum_eq_prod`, `Probability/Independence/CharacteristicFunction.lean`). The inversion formula for an integrable characteristic function is not stated for measures. If a finite measure on \(\mathbb{R}\) has a moment of order \(n\), the Taylor expansion of its characteristic function at the origin to order \(n\) has coefficients \((it)^k\int x^k\,d\mu/k!\) (`MeasureTheory/Measure/CharacteristicFunction/TaylorExpansion.lean`).

Lévy’s continuity theorem, on a finite-dimensional inner product space: a sequence of probability measures converges weakly to a given probability measure if and only if its characteristic functions converge pointwise to the characteristic function of that measure (`ProbabilityMeasure.tendsto_iff_tendsto_charFun`). If the characteristic functions converge pointwise to a limit that is continuous at the origin, the sequence of measures is tight (`isTightMeasureSet_of_tendsto_charFun`, `MeasureTheory/Measure/LevyConvergence.lean`); that the limit is then a characteristic function is not stated.

The Cramér–Wold theorem: for random variables with values in a finite-dimensional real inner product space, convergence in distribution is equivalent to convergence in distribution of every scalar projection (`tendstoInDistribution_iff_tendstoInDistribution_inner`, `Probability/CramerWold.lean`).

The central limit theorem in dimension one: if the variables are i.i.d. and square-integrable, with mean \(\mu\) and variance \(v\), then
\[
n^{-1/2}\sum_{k<n}(X_k-\mu)
\]
converges in distribution to the centered Gaussian of variance \(v\) (`tendstoInDistribution_inv_sqrt_mul_sum_sub`, `Probability/CentralLimitTheorem.lean`). The vector form is not stated.

Poisson limit of binomial probabilities: if \(np_n\to r\), then for each \(k\) the binomial probability \(\binom nk p_n^k(1-p_n)^{n-k}\) tends to \(e^{-r}r^k/k!\) (`tendsto_choose_mul_pow_of_tendsto_mul_atTop`, `Probability/Distributions/Poisson/PoissonLimitThm.lean`). This is the case of equal success probabilities in each row.

#### TauCeti

Bochner's theorem characterizes continuous positive-definite functions on finite-dimensional real inner-product spaces as Fourier transforms of unique finite positive measures ([Bochner](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Bochner/BochnerTheorem.lean)). A finite measure on the real line with finite exponential moments near the origin is determined by its moments ([moment determinacy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Moments/Determinacy.lean)), and a finite measure on a compact subset of \(\mathbb{R}^n\) by its mixed moments ([compact determinacy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Moments/CompactDeterminacy.lean)). The convergence half of the method of moments is not stated. The finite-dimensional standard-distribution library also includes implemented error, incomplete gamma, and incomplete beta functions, described in Section 49.

**Synopsis entries.** Covered: 06.31 (Mathlib). Partly covered: 06.29 (uniqueness and multiplicativity; inversion absent), 06.30 (the equivalence for a given limit law, and tightness; the limit is not shown to be a characteristic function), 06.32 (determinacy only, in TauCeti), 06.33 (dimension one), 06.38 (equal success probabilities in each row). Not covered: 06.34–06.37, 06.39.

### Discrete-time martingales

[Mathematical scope](SYNOPSIS06.md#discrete-time-martingales).

#### Mathlib

The filtration, adaptedness, stopping-time, and hitting-time vocabulary is recorded in [Section 08](STRUCTURE08.md). An integrable adapted process with values in a Banach space is a martingale when \(\mu[f_j\mid\mathcal{F}_i]=f_i\) almost surely whenever \(i\leq j\). It is a submartingale when \(f_i\leq\mu[f_j\mid\mathcal{F}_i]\), and a supermartingale when the inequality is reversed. The sequence of conditional expectations of a single integrable random variable, along a filtration, is a martingale (`Probability/Martingale/Basic.lean`).

Doob’s decomposition: a discrete-time integrable adapted process is the sum of a martingale and a predictable process starting at zero; the decomposition is unique almost everywhere, and for a submartingale the predictable part is almost surely increasing (`martingale_martingalePart`, `martingalePart_add_ae_eq`, `Submartingale.monotone_predictablePart`, `Probability/Martingale/Centering.lean`).

For a discrete real submartingale, if \(U_N(a,b)\) is the number of upcrossings of the interval \((a,b)\) before time \(N\), then
\[
(b-a)\,\mathbb{E}[U_N(a,b)]\leq\mathbb{E}[(f_N-a)^+]
\]
(`Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part`, `Probability/Martingale/Upcrossing.lean`). The sharper bound with \(\mathbb{E}(f_0-a)^+\) subtracted is not stated.

Almost-everywhere convergence: an \(L^1\)-bounded discrete submartingale converges almost everywhere to an integrable random variable measurable for \(\mathcal{F}_\infty=\bigvee_n\mathcal{F}_n\) (`Submartingale.ae_tendsto_limitProcess`). For a submartingale \(\sup_n\mathbb{E}X_n^+<\infty\) is equivalent to \(L^1\)-boundedness, and a nonnegative supermartingale is \(L^1\)-bounded, so these cases follow at once. The limit of an \(L^p\)-bounded submartingale lies in \(L^p\). A uniformly integrable submartingale converges almost everywhere and in \(L^1\) to an \(\mathcal{F}_\infty\)-measurable integrable limit. A uniformly integrable martingale is the sequence of conditional expectations of its limit, and conversely the conditional expectations of one integrable function along a filtration are uniformly integrable (`Integrable.uniformIntegrable_condExp_filtration`, `Probability/Process/Filtration.lean`). Lévy's upward theorem: if \(g\) is integrable, then \(\mathbb{E}[g\mid\mathcal{F}_n]\) converges to \(\mathbb{E}[g\mid\mathcal{F}_\infty]\) almost everywhere and in \(L^1\) (`tendsto_ae_condExp`, `tendsto_eLpNorm_condExp`, `Probability/Martingale/Convergence.lean`). The limit is named through a general limit process of a process along a filtration (`Probability/Process/LimitProcess.lean`). Convergence in \(L^p\) of \(L^p\)-bounded martingales, \(p>1\), is not stated.

Optional sampling, for a discrete martingale: the value at a stopping time \(\tau\) bounded by \(n\) is the conditional expectation of \(f_n\) on the σ-algebra of \(\tau\). If \(\sigma\leq\tau\) and \(\tau\) is bounded, the value at \(\sigma\) is the conditional expectation of the value at \(\tau\). If \(\tau\) is a bounded stopping time and \(\sigma\) is any stopping time, the value at \(\min(\tau,\sigma)\) is the conditional expectation of the value at \(\tau\) on the σ-algebra of \(\sigma\) (`Probability/Martingale/OptionalSampling.lean`). Optional stopping, or the fair-game theorem: an integrable adapted process is a submartingale if and only if \(\mathbb{E}[f_\tau]\leq\mathbb{E}[f_\pi]\) whenever \(\tau\leq\pi\) are bounded stopping times. The process stopped at a stopping time remains a submartingale (`Probability/Martingale/OptionalStopping.lean`). Optional sampling at unbounded stopping times for uniformly integrable martingales, and Wald's identity, are not stated.

Doob’s maximal inequality: for a nonnegative submartingale and \(\varepsilon\geq 0\), if \(f^*_n=\max_{k\leq n}f_k\), then
\[
\varepsilon\,\mu\{f^*_n\geq\varepsilon\}\leq\int_{\{f^*_n\geq\varepsilon\}} f_n\,d\mu
\]
(`maximal_ineq`, `Probability/Martingale/OptionalStopping.lean`). Doob's \(L^p\) inequality is not stated.

Lévy’s generalization of Borel–Cantelli: if \(s_n\in\mathcal{F}_n\), the limsup of the sets \(s_n\) agrees almost everywhere with the set where \(\sum_n\mathbb{P}(s_{n+1}\mid\mathcal{F}_n)\) diverges (`Probability/Martingale/BorelCantelli.lean`).

#### TauCeti

Lévy's downward theorem: conditional expectations of an integrable real random variable along a decreasing sequence of σ-algebras converge almost everywhere and in \(L^1\), and in \(L^p\) for \(f\in L^p\), \(p<\infty\), to the conditional expectation on their intersection, on a finite measure space. The proof goes through a uniform upcrossing bound for reverse martingales ([reverse-martingale convergence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Martingale/Convergence.lean), `MeasureTheory.tendsto_ae_condExp_iInf`, `MeasureTheory.tendsto_eLpNorm_condExp_iInf`).

**Synopsis entries.** Covered: 06.40, 06.42, 06.45 (Mathlib), 06.46 (TauCeti). Partly covered: 06.41 (without the initial term), 06.43 (the weak-type inequality; Doob's \(L^p\) inequality is absent), 06.44 (the \(L^1\) theory; \(L^p\) convergence is absent), 06.47 (bounded stopping times; unbounded times and Wald's identity are absent).

### Gaussian laws, infinite divisibility, and exchangeability

[Mathematical scope](SYNOPSIS06.md#gaussian-laws-infinite-divisibility-and-exchangeability).

#### Mathlib

Covariance of real random variables, and covariance as a bilinear form on a Hilbert space or through the dual of a Banach space, are defined (`Probability/Moments/Covariance.lean`, `Probability/Moments/CovarianceBilin.lean`, `Probability/Moments/CovarianceBilinDual.lean`).

A measure on a Banach space is Gaussian when its image under every continuous linear functional is a real Gaussian measure. Equivalently, the dual characteristic function has the form \(\exp(i\,L(m)-\tfrac12 f(L,L))\) for a mean vector \(m\) and a positive semidefinite covariance form \(f\), and both are unique (`Probability/Distributions/Gaussian/Basic.lean`, `Probability/Distributions/Gaussian/CharFun.lean`). Fernique’s theorem: for a Gaussian measure on a second-countable normed space there is a constant \(C>0\) such that \(\exp(C\|x\|^2)\) is integrable. On a second-countable Banach space every moment is finite (`Probability/Distributions/Gaussian/Fernique.lean`).

On the line, the Gaussian of mean \(\mu\) and variance \(v>0\) has density \((2\pi v)^{-1/2}\exp(-(x-\mu)^2/(2v))\), and variance zero is a Dirac mass. Translates and dilates of a Gaussian are Gaussian (`Probability/Distributions/Gaussian/Real.lean`). The standard Gaussian on a finite-dimensional Euclidean space is the law of independent standard coordinates in an orthonormal basis. A multivariate Gaussian on a Euclidean space is determined by a mean vector and a positive semidefinite covariance matrix (`Probability/Distributions/Gaussian/Multivariate.lean`).

A random variable has a Gaussian law when its law is a Gaussian measure. If \((X,Y)\) is jointly Gaussian with zero covariance, \(X\) and \(Y\) are independent; the same holds for a jointly Gaussian family with vanishing cross-covariances, in Banach and Hilbert spaces and for real families; and independent Gaussian variables are jointly Gaussian (`HasGaussianLaw.indepFun_of_covariance_eq_zero`, `HasGaussianLaw.iIndepFun_of_covariance_eq_zero`, `Probability/Distributions/Gaussian/HasGaussianLaw/Independence.lean`).

#### TauCeti

For a jointly Gaussian vector with positive-semidefinite covariance whose observed block is positive definite, the regular conditional distribution of one block given the other is Gaussian with affine mean and Schur-complement covariance ([Gaussian conditioning](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Distributions/Gaussian/Conditional.lean), `TauCeti.Probability.condDistrib_multivariateGaussian`).

The Cauchy law has characteristic function \(e^{ix_0t-\gamma|t|}\), and the average of independent Cauchy variables with common parameters has the same law ([Cauchy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Distributions/Cauchy/Basic.lean), `TauCeti.Probability.charFun_cauchyMeasure`, `ProbabilityTheory.iIndepFun.hasLaw_average_cauchyMeasure`). This is the symmetric stable law with \(\alpha=1\); the case \(\alpha=2\) is the Gaussian.

There is a substantial exchangeability development. The de Finetti–Ryll-Nardzewski theorem identifies exchangeable, or more generally contractable, sequences with conditionally independent identically distributed sequences, for nonempty standard Borel state spaces. It is proved in conditional and mixture forms ([theorem](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/DeFinetti/Theorem.lean), `deFinetti`, `exchangeable_iff_mixedIID`). For Polish state spaces, empirical measures converge almost surely weakly to a directing measure ([empirical form](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/DeFinetti/EmpiricalMeasure.lean)). For separately exchangeable standard-Borel-valued arrays, TauCeti proves the Aldous–Hoover representation by a measurable function of independent global, row, column, and cell uniform variables ([array representation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Exchangeability/Arrays/AldousHoover/Separate/Representation.lean)). The jointly exchangeable form is also proved: a jointly exchangeable array law is the law of \(F(U,U_i,U_j,U_{\{i,j\}})\) with independent uniform global, vertex, and unordered-pair variables, and conversely ([joint representation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Exchangeability/Arrays/AldousHoover/Joint/Representation.lean)).

Among multivariate distributions, TauCeti defines the Dirichlet law by normalizing independent positive-shape Gamma variables and proves its simplex support ([Dirichlet](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Distributions/Dirichlet/Basic.lean)). It constructs Wishart laws as Gram sums of finitely many independent Gaussian vectors, including singular positive-semidefinite covariance cases, and proves congruence and convolution identities ([Wishart](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Distributions/Wishart/Basic.lean)). The univariate library is also larger than Mathlib's: chi-squared, Student \(t\), Fisher \(F\), Laplace, log-normal, Weibull, inverse-gamma, negative-binomial, hypergeometric, and multinomial laws, with densities, distribution functions, moments, and the classical relations between them, such as Student \(t\) as a Gaussian–chi-squared ratio ([distributions](https://github.com/TauCetiProject/TauCeti/tree/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Distributions)). This is catalogue content rather than limit theory. The Bernstein-function Lévy–Khintchine theorem in Section 49 is a further representation result, with narrower scope than general infinite divisibility on the real line.

**Synopsis entries.** Covered: 06.48 (Mathlib), 06.49, 06.55 (TauCeti). Partly covered: 06.52 (\(\alpha=1\) and \(\alpha=2\) only). Not covered: 06.50, 06.51.

### Functional limits and empirical distributions

[Mathematical scope](SYNOPSIS06.md#functional-limits-and-empirical-distributions).

Tightness and weak convergence of probability measures on metric spaces (above) and TauCeti's empirical measures of sequences ([empirical measures](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Process/EmpiricalMeasure.lean)) are the nearest supporting material.

**Synopsis entries.** Not covered: 06.57–06.59.

<a id="structure-06b"></a>

## 06B. Large Deviations

Exponential tilting, cumulant-generating functions, and relative entropy provide the material relevant to this subdivision. Their exact statements are recorded below.

### Large-deviation principles

[Mathematical scope](SYNOPSIS06.md#large-deviation-principles).

#### Mathlib

Exponential tilting is related to the generating functions: under the tilted measure \(e^{tX}\mu/\mathbb{E}[e^{tX}]\), the mean and variance of \(X\) are the first and second derivatives of the cumulant-generating function at \(t\) (`Probability/Moments/Tilted.lean`). The Kullback–Leibler divergence of finite measures is defined with values in the extended nonnegative reals; it is nonnegative (Gibbs' inequality) and vanishes only for equal measures, satisfies the chain rule for compositions of a measure with a Markov kernel, and decreases under measurable maps, restriction to sub-σ-algebras, and Markov kernels (data processing) (`InformationTheory/KullbackLeibler/Basic.lean`, `InformationTheory/KullbackLeibler/ChainRule.lean`, `InformationTheory/KullbackLeibler/DataProcessing.lean`). The conditional variance relative to a sub-σ-algebra is defined (`Probability/CondVar.lean`).

#### TauCeti

The Donsker–Varadhan variational formula is proved: for finite measures, \(\mathrm{KL}(\mu\|\nu)=\sup_f\bigl(\int f\,d\mu-\int(e^f-1)\,d\nu\bigr)\) over bounded measurable \(f\), with bounded continuous \(f\) sufficing on a pseudometrizable Borel space, and for probability measures \(\mathrm{KL}(\mu\|\nu)=\sup_f\bigl(\int f\,d\mu-\log\int e^f\,d\nu\bigr)\); consequently the divergence is jointly lower semicontinuous for weak convergence ([Donsker–Varadhan](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/InformationTheory/KullbackLeibler/Variational.lean)). This is the lower semicontinuity of Sanov's rate function, but no large-deviation principle is stated.

**Synopsis entries.** Not covered: 06.60–06.64, 06.67, 06.68.

<a id="structure-06c"></a>

## 06C. Random Measures, Random Fields, and Stochastic Geometry

Reusable foundations for random measures include the Poisson count law, product measures, kernels, and projective constructions in 06A, together with the measure constructions in [Section 04](STRUCTURE04.md). The scalar Poisson law specifies counts; it is a different object from a Poisson random measure.

### Poisson random measures

[Mathematical scope](SYNOPSIS06.md#poisson-random-measures).

Neither library defines Poisson random measures or point processes; the scalar Poisson law (`Probability/Distributions/Poisson/Basic.lean`) is the nearest material.

**Synopsis entries.** Not covered: 06.53, 06.54, 06.69–06.71.

### Gaussian random fields

[Mathematical scope](SYNOPSIS06.md#gaussian-random-fields).

**Synopsis entries.** Not covered: 06.72.

<a id="structure-06d"></a>

## 06D. Discrete Probability and Probabilistic Statistical Mechanics

Product probability spaces, independence, zero–one laws, and exchangeable sequences in 06A provide reusable foundations for discrete probability models. The process and martingale constructions in [Section 08](STRUCTURE08.md) supply further probabilistic tools.

### Branching processes

[Mathematical scope](SYNOPSIS06.md#branching-processes).

**Synopsis entries.** Not covered: 06.65, 06.66.

### Random walks, correlation inequalities, and percolation

[Mathematical scope](SYNOPSIS06.md#random-walks-correlation-inequalities-and-percolation).

#### Mathlib

The four functions theorem of Ahlswede and Daykin is proved on finite distributive lattices, and with it the Fortuin–Kasteleyn–Ginibre inequality: if \(\mu\ge0\) satisfies \(\mu(a)\mu(b)\le\mu(a\wedge b)\mu(a\vee b)\) and \(f,g\ge0\) are monotone, then \(\bigl(\sum\mu f\bigr)\bigl(\sum\mu g\bigr)\le\bigl(\sum\mu\bigr)\bigl(\sum\mu fg\bigr)\) (`four_functions_theorem`, `fkg`, `Combinatorics/SetFamily/FourFunctions.lean`). Nonnegativity is removed by adding constants. A product Bernoulli measure on the subsets of a finite set satisfies the lattice condition with equality, which gives Harris's inequality for \(\mathbb{P}_p\); the uniform case is the Harris–Kleitman inequality for upper sets (`IsUpperSet.le_card_inter_finset`, `Combinatorics/SetFamily/HarrisKleitman.lean`).

**Synopsis entries.** Covered: 06.74 (Mathlib). Not covered: 06.73, 06.75–06.77.

### Gibbs measures and phase transitions

[Mathematical scope](SYNOPSIS06.md#gibbs-measures-and-phase-transitions).

**Synopsis entries.** Not covered: 06.78–06.80.
