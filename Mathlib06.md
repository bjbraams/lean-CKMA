# 6. Probability: measure-theoretic foundations and limit theory

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Some roots below are directory prefixes; the individual `.lean` files cited are the importable modules. The roots for this section are `Mathlib.Probability`, `Mathlib.MeasureTheory.Function.ConditionalExpectation`, `Mathlib.MeasureTheory.Function.ConvergenceInDistribution`, `Mathlib.MeasureTheory.Measure.CharacteristicFunction`, `Mathlib.MeasureTheory.Measure.LevyConvergence`, `Mathlib.MeasureTheory.Measure.Portmanteau`, and `Mathlib.MeasureTheory.Measure.Prokhorov`.

**Namespaces.** `ProbabilityTheory`, with nested `Kernel`. Conditional expectation, characteristic functions, and convergence in distribution are declared in `MeasureTheory`. Discrete distributions are `PMF`.

This note records the measure-theoretic foundations of probability and the limit theorems that accompany them: independence, conditioning, kernels, characteristic functions, and the strong law and the central limit theorem. Martingales, processes, and Brownian motion are Section 8. Sub-Gaussian tails and metric entropy are Section 7. The topology of weak convergence was written out in `Mathlib04.md` and is only recalled here.

## Probability spaces, laws, and elementary conditioning

A probability measure is a measure of total mass one. The library writes \(\mathbb{P}\) for the canonical measure of a probability space, \(\mathbb{E}[X]\) for its integral, and \(\partial P/\partial Q\) for a Radon–Nikodym derivative (`Probability/Notation.lean`).

A random variable \(X\) has law \(\mu\) under \(P\) when \(X\) is almost everywhere measurable and the pushforward \(P\circ X^{-1}\) equals \(\mu\). Random variables on possibly different spaces are identically distributed when their laws coincide. On a countable index set, a family of i.i.d. coordinates has the product law (`Probability/HasLaw.lean`, `Probability/IdentDistrib.lean`, `Probability/IdentDistribIndep.lean`). There are lemmas producing a family of random variables with prescribed laws and mutual independence (`Probability/HasLawExists.lean`).

On a finite nonempty set the counting measure conditioned to the set is the uniform probability, and the probability of an event is the ratio of cardinalities (`Probability/UniformOn.lean`). A probability mass function is a function to the extended nonnegative reals summing to one. It determines a probability measure for which every set is measurable, and conversely a probability measure on a countable space with measurable singletons determines a mass function (`Probability/ProbabilityMassFunction/Basic.lean`).

The conditional probability of a finite measure given a set \(s\) of positive measure is the restriction to \(s\), scaled to a probability. Conditioning twice is conditioning on the intersection, and Bayes’ formula \(\mu(t\mid s)=\mu(s\mid t)\,\mu(t)/\mu(s)\) holds (`Probability/ConditionalProbability.lean`).

The cumulative distribution function of a probability measure on \(\mathbb{R}\) is the monotone right-continuous function \(F(x)=\mu((-\infty,x])\), with limits \(0\) and \(1\) at \(-\infty\) and \(+\infty\). Two probability measures on the line are equal if and only if their distribution functions agree (`Probability/CDF.lean`).

A random variable has a density \(f\) with respect to a reference measure \(\mu\) when its law is absolutely continuous with respect to \(\mu\) and \(f\) is a Radon–Nikodym derivative: \(\mathbb{P}(X\in S)=\int_S f\,d\mu\) (`Probability/Density.lean`).

## Independence

A family of set systems is independent when the measure of a finite intersection, with one set from each of finitely many distinct systems, equals the product of the measures. A family of σ-algebras is independent when their collections of measurable sets are. An event is independent of others when the σ-algebra it generates is. Random variables are independent when the σ-algebras they generate are (`Probability/Independence/Basic.lean`).

For independent random variables with values in the extended nonnegative reals, the expectation of a product is the product of the expectations (`Probability/Independence/Integration.lean`). On Borel spaces in which closed sets can be approximated from outside by bounded continuous functions, independence is equivalent to factorization of expectations of products of bounded continuous functions (`Probability/Independence/BoundedContinuousFunction.lean`). In second-countable real Hilbert spaces with their Borel σ-algebras, two random variables, or a finite family, are independent if and only if the joint characteristic function is the product of the marginal characteristic functions. In second-countable real Banach spaces with their Borel σ-algebras the same factorization is proved for the characteristic function formed with continuous linear functionals (`Probability/Independence/CharacteristicFunction.lean`).

An infinite family of probability measures has a unique product probability measure on the product space, characterized by its values on finite-dimensional cylinders (`Probability/ProductMeasure.lean`). Independence of arbitrary, not necessarily countable, families is developed against that product (`Probability/Independence/InfinitePi.lean`).

Kolmogorov’s zero–one law: if \((s_i)\) is an independent sequence of sub-σ-algebras, every set in the tail σ-algebra has probability \(0\) or \(1\) (`Probability/Independence/ZeroOne.lean`).

The first Borel–Cantelli lemma is the measure-theoretic statement from `Mathlib04.md`: a summable sequence of measures charges almost every point only finitely often. The second lemma is probabilistic: if the events are independent and the sum of their probabilities diverges, the limsup has probability one (`Probability/BorelCantelli.lean`).

Conditional independence of σ-algebras given a third σ-algebra is factorization of the conditional probabilities. On a standard Borel space this is expressed through the conditional-expectation kernel (`Probability/Independence/Conditional.lean`).

## Kernels, disintegration, and conditional expectation

A kernel from \(\alpha\) to \(\beta\) is a measurable map from \(\alpha\) into the space of measures on \(\beta\). It is Markov when every value is a probability measure, finite when the total masses are uniformly bounded, and s-finite when it is a countable sum of finite kernels (`Probability/Kernel/Defs.lean`). Deterministic kernels include Dirac masses along a measurable map (`Probability/Kernel/Basic.lean`). Kernels compose, and a measure may be composed with a kernel. The category of measurable spaces and s-finite kernels is developed separately (`Probability/Kernel/Composition`, `Probability/Kernel/Category/SFinKer.lean`).

The Ionescu–Tulcea theorem extends a consistent sequence of finite compositions of kernels to a kernel that, given a trajectory up to time \(a\), returns the law of the entire future trajectory (`Probability/Kernel/IonescuTulcea/Traj.lean`).

A kernel disintegrates a measure \(\rho\) on a product \(\beta\times\Omega\) when \(\rho\) is the composition of its first marginal with that kernel. If \(\Omega\) is standard Borel, such a conditional kernel exists, for a finite measure; the corresponding finite-kernel construction assumes the required countability or countable-generation hypotheses on the parameter and first-factor spaces, and it is unique almost everywhere (`Probability/Kernel/Disintegration/Basic.lean`, `Probability/Kernel/Disintegration/StandardBorel.lean`, `Probability/Kernel/Disintegration/Unique.lean`). The construction on the line passes through a conditional distribution function (`Probability/Kernel/Disintegration/CondCDF.lean`).

The conditional expectation of an integrable Banach-valued function \(f\), relative to a sub-σ-algebra \(m\) for which the restricted measure is σ-finite, is an \(m\)-strongly measurable integrable function \(\mu[f\mid m]\) such that
\[
\int_s \mu[f\mid m]\,d\mu = \int_s f\,d\mu
\]
for every \(m\)-measurable \(s\). It is unique in \(L^1\). The construction projects in \(L^2\) onto the \(m\)-measurable functions and extends by the same procedure as the Bochner integral. The tower property holds: conditioning first to a larger σ-algebra and then to a smaller one is the same as conditioning directly to the smaller one (`MeasureTheory/Function/ConditionalExpectation/Basic.lean`).

If \(f\) is almost everywhere \(m\)-strongly measurable, \(g\) is integrable, and \(B(f,g)\) is integrable for a continuous bilinear map \(B\), then almost surely \(\mu[B(f,g)\mid m]=B(f,\mu[g\mid m])\). Scalar multiplication and the product of real functions are the special cases (`MeasureTheory/Function/ConditionalExpectation/PullOut.lean`). If \(f\) is measurable for one of two independent σ-algebras, its conditional expectation on the other is the constant \(\mathbb{E}[f]\) (`Probability/ConditionalExpectation.lean`).

On a standard Borel space the conditional expectation is integration against a kernel: \(\mu[f\mid m](\omega)=\int f\,d\kappa_\omega\) almost everywhere (`Probability/Kernel/Condexp.lean`). A random variable has conditional distribution \(\kappa\) given another when the law of the pair is the composition of the law of the conditioning variable with \(\kappa\) (`Probability/HasCondDistrib.lean`).

## Moments, characteristic functions, and Gaussian measures

The \(p\)-th moment of a real random variable is the expectation of its \(p\)-th power, and the central moment subtracts the mean first. The moment-generating function is \(t\mapsto\mathbb{E}[e^{tX}]\), and the cumulant-generating function is its logarithm. For independent random variables the moment-generating function of a sum is the product, and the cumulant-generating function adds (`Probability/Moments/Basic.lean`). On a finite measure, the Chernoff bound says that if \(t\geq 0\) and \(e^{tX}\) is integrable, then
\[
\mu\{X\geq\varepsilon\}\leq\exp(-t\varepsilon+\operatorname{cgf}(t)),
\]
with a matching lower-tail bound for \(t\leq 0\).

The complex moment-generating function \(z\mapsto\mathbb{E}[e^{zX}]\) is holomorphic on the vertical strip over the interior of the real interval where the moment-generating function exists, and on the imaginary axis it is the characteristic function (`Probability/Moments/ComplexMGF.lean`). Where the real moment-generating function is finite on a neighborhood of a point, it is analytic (`Probability/Moments/MGFAnalytic.lean`).

Covariance of real random variables, and covariance as a bilinear form on a Hilbert space or through the dual of a Banach space, are defined (`Probability/Moments/Covariance.lean`, `Probability/Moments/CovarianceBilin.lean`, `Probability/Moments/CovarianceBilinDual.lean`).

The characteristic function of a finite measure on an inner product space is
\[
\varphi_\mu(t)=\int \exp(i\langle x,t\rangle)\,d\mu(x).
\]
On a normed space the dual characteristic function uses a continuous linear functional in place of the inner product. On a complete second-countable inner product space, finite measures with the same characteristic function are equal. On a second-countable real Banach space with its Borel σ-algebra, finite measures with the same dual characteristic function are equal (`MeasureTheory/Measure/CharacteristicFunction/Basic.lean`).

Lévy’s continuity theorem, on a finite-dimensional inner product space: a sequence of probability measures converges weakly to a given probability measure if and only if its characteristic functions converge pointwise to the characteristic function of that measure. If the characteristic functions converge pointwise to a limit that is continuous at the origin, the sequence of measures is tight (`MeasureTheory/Measure/LevyConvergence.lean`).

A measure on a Banach space is Gaussian when its image under every continuous linear functional is a real Gaussian measure. Equivalently, the dual characteristic function has the form \(\exp(i\,L(m)-\tfrac12 f(L,L))\) for a mean vector \(m\) and a positive semidefinite covariance form \(f\), and both are unique (`Probability/Distributions/Gaussian/Basic.lean`, `Probability/Distributions/Gaussian/CharFun.lean`). Fernique’s theorem: for a Gaussian measure on a second-countable normed space there is a constant \(C>0\) such that \(\exp(C\|x\|^2)\) is integrable. On a second-countable Banach space every moment is finite (`Probability/Distributions/Gaussian/Fernique.lean`).

On the line, the Gaussian of mean \(\mu\) and variance \(v>0\) has density \((2\pi v)^{-1/2}\exp(-(x-\mu)^2/(2v))\), and variance zero is a Dirac mass. Translates and dilates of a Gaussian are Gaussian (`Probability/Distributions/Gaussian/Real.lean`). The standard Gaussian on a finite-dimensional Euclidean space is the law of independent standard coordinates in an orthonormal basis. A multivariate Gaussian on a Euclidean space is determined by a mean vector and a positive semidefinite covariance matrix (`Probability/Distributions/Gaussian/Multivariate.lean`).

The same directory constructs Bernoulli, binomial, geometric, and Poisson laws on discrete spaces; Beta, Cauchy, exponential, Gamma, and Pareto laws on the line; and the uniform law. Binomial probabilities converge to the Poisson probabilities when \(n p_n\) tends to a finite limit (`Probability/Distributions`).

## Convergence in distribution and limit theorems

Random variables converge in distribution when their laws converge in the topology of weak convergence of probability measures. A continuous image preserves convergence in distribution. Convergence in probability implies convergence in distribution. Slutsky’s theorem: if \(X_n\) converges in distribution to \(Z\) and \(Y_n\) converges in probability to a constant \(c\), then \((X_n,Y_n)\) converges in distribution to \((Z,c)\) (`MeasureTheory/Function/ConvergenceInDistribution.lean`).

The portmanteau theorem and Prokhorov’s theorem are the characterizations of this topology proved in `Mathlib04.md`: closed-set and open-set inequalities, convergence on continuity sets, and the equivalence of tightness and relative compactness for probability measures on a complete second-countable metric space (`MeasureTheory/Measure/Portmanteau.lean`, `MeasureTheory/Measure/Prokhorov.lean`).

The Cramér–Wold theorem: for random variables with values in a finite-dimensional real inner product space, convergence in distribution is equivalent to convergence in distribution of every scalar projection (`Probability/CramerWold.lean`).

The strong law, in Etemadi’s form: if the random variables are pairwise independent, identically distributed, and integrable, then the sample averages converge almost surely to the common expectation. If they lie in \(L^p\) for \(1\le p<\infty\), the averages converge in \(L^p\). For Banach-valued variables the theorem follows by approximation with simple functions (`Probability/StrongLaw.lean`).

The central limit theorem in dimension one: if the variables are i.i.d. and square-integrable, with mean \(\mu\) and variance \(v\), then
\[
n^{-1/2}\sum_{k<n}(X_k-\mu)
\]
converges in distribution to the centered Gaussian of variance \(v\) (`Probability/CentralLimitTheorem.lean`).

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

There is a substantial exchangeability development. The de Finetti–Ryll-Nardzewski theorem identifies exchangeable, or more generally contractable, sequences with conditionally independent identically distributed sequences, for nonempty standard Borel state spaces. It is proved in conditional and mixture forms ([theorem](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Probability/DeFinetti/Theorem.lean)). For Polish state spaces, empirical measures converge almost surely weakly to a directing measure ([empirical form](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Probability/DeFinetti/EmpiricalMeasure.lean)). For separately exchangeable standard-Borel-valued arrays, TauCeti proves the Aldous–Hoover representation by a measurable function of independent global, row, column, and cell uniform variables ([array representation](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Probability/Exchangeability/Arrays/AldousHoover/SeparateRepresentation.lean)).

Further additions include Bochner's characterization of continuous positive-definite functions on finite-dimensional real inner-product spaces as Fourier transforms of unique finite positive measures ([Bochner](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Bochner/BochnerTheorem.lean)), and determinacy of finite measures on the real line from moments under an exponential-moment hypothesis ([moment determinacy](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Probability/Moments/Determinacy.lean)). The finite-dimensional standard-distribution library also includes implemented error, incomplete gamma, and incomplete beta functions, described in Section 49. These results do not supply a functional central limit theorem or a general large-deviation principle.

Among multivariate distributions, TauCeti defines the Dirichlet law by normalizing independent positive-shape Gamma variables and proves its simplex support ([Dirichlet](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Probability/Distributions/Dirichlet/Basic.lean)). It constructs Wishart laws as Gram sums of finitely many independent Gaussian vectors, including singular positive-semidefinite covariance cases, and proves congruence and convolution identities ([Wishart](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Probability/Distributions/Wishart/Basic.lean)). The Bernstein-function Lévy–Khintchine theorem in Section 49 is a further representation result, with narrower scope than general infinite divisibility on the real line.

## Topics of Section 6 not found in either inspected library

- The law of the iterated logarithm.
- A local central limit theorem, and a multidimensional central limit theorem stated apart from Cramér–Wold.
- Stable laws and infinitely divisible distributions.
- Large-deviation principles. The Chernoff bound from the cumulant-generating function is the inequality recorded above; Sanov’s theorem and Varadhan’s lemma were not found.
- Empirical processes and functional limit theorems in the sense of Billingsley’s *Convergence of Probability Measures*. Tightness and weak convergence of probability measures on metric spaces are present.
