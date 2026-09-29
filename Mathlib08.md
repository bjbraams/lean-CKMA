# 8. Stochastic processes, martingales, and stochastic calculus

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Some roots below are directory prefixes; the individual `.lean` files cited are the importable modules. The roots for this section are `Mathlib.Probability.Process`, `Mathlib.Probability.Martingale`, `Mathlib.Probability.BrownianMotion`, and `Mathlib.MeasureTheory.Function.ConditionalExpectation`.

**Namespaces.** `MeasureTheory`, with nested `Filtration`, `Martingale`, `Submartingale`, `Supermartingale`, and `IsStoppingTime`. Brownian motion is `ProbabilityTheory`, with nested `BrownianReal` and the predicates `IsPreBrownianReal` and `IsBrownianReal`. Conditional expectation remains `MeasureTheory.condExp`, as in `Mathlib06.md`.

This note records discrete-time martingales, the language of filtrations and stopping times, and the measure-theoretic description of real Brownian motion. Stochastic integration was not found.

## Processes, filtrations, and stopping times

A filtration is a monotone family of sub-σ-algebras. Filtrations form a complete lattice. The natural filtration of a process is the smallest filtration to which the process is adapted. The right-continuation of a filtration enlarges each σ-algebra by the information immediately after the present time, and a filtration is right-continuous when it equals its right-continuation. A filtration is σ-finite when each of its σ-algebras makes the restricted measure σ-finite (`Probability/Process/Filtration.lean`).

A process is adapted when the value at time \(i\) is measurable for the σ-algebra at time \(i\), and progressively measurable when its restriction up to time \(i\) is measurable on the product of the past with the sample space. Strong measurability gives the corresponding strong notions. A continuous strongly adapted process is strongly progressive (`Probability/Process/Adapted.lean`).

The predictable σ-algebra is generated from the filtration in the usual way. A predictable process is measurable for that σ-algebra, and every predictable process is progressively measurable and adapted. In discrete time, predictability of \(u\) is measurability of \(u_{n+1}\) for \(\mathcal{F}_n\), together with measurability of \(u_0\) for \(\mathcal{F}_0\) (`Probability/Process/Predictable.lean`).

A stopping time takes values in the time index extended by a point at infinity, and \(\{\tau\leq i\}\) lies in \(\mathcal{F}_i\). It generates a σ-algebra. The stopped process of a progressively measurable process is progressively measurable, and stopping preserves membership in \(L^p\) along discrete time (`Probability/Process/Stopping.lean`).

The first time a process enters a set, between two deterministic times or after a deterministic time, is a hitting time. In discrete time, the hitting time of a strongly adapted process is a stopping time (`Probability/Process/HittingTime.lean`).

A property of processes holds locally, relative to a filtration, when some sequence of stopping times increases almost surely to infinity and each stopped process satisfies the property. A property is stable when it passes to stopped processes; the localization of a stable property is stable (`Probability/Process/LocalProperty.lean`).

The law of a process is the pushforward of the probability measure under the map that sends a sample to the whole path, equipped with the product (cylinder) σ-algebra. Two processes have the same law if and only if all their finite-dimensional distributions agree. A modification, meaning a process equal at each fixed time almost surely, has the same finite-dimensional distributions and the same law (`Probability/Process/FiniteDimensionalLaws.lean`).

## Martingales

An integrable adapted process with values in a Banach space is a martingale when \(\mu[f_j\mid\mathcal{F}_i]=f_i\) almost surely whenever \(i\leq j\). It is a submartingale when \(f_i\leq\mu[f_j\mid\mathcal{F}_i]\), and a supermartingale when the inequality is reversed. The sequence of conditional expectations of a single integrable random variable, along a filtration, is a martingale (`Probability/Martingale/Basic.lean`).

Doob’s decomposition: a discrete-time integrable adapted process is the sum of a martingale and a predictable process (`Probability/Martingale/Centering.lean`).

For a discrete real submartingale, if \(U_N(a,b)\) is the number of upcrossings of the interval \((a,b)\) before time \(N\), then
\[
(b-a)\,\mathbb{E}[U_N(a,b)]\leq\mathbb{E}[(f_N-a)^+].
\]
(`Probability/Martingale/Upcrossing.lean`).

Almost-everywhere convergence: an \(L^1\)-bounded discrete submartingale converges almost everywhere to an integrable random variable measurable for \(\mathcal{F}_\infty=\bigvee_n\mathcal{F}_n\). The limit of an \(L^p\)-bounded submartingale lies in \(L^p\). A uniformly integrable submartingale converges almost everywhere and in \(L^1\) to an \(\mathcal{F}_\infty\)-measurable integrable limit. A uniformly integrable martingale is the sequence of conditional expectations of its limit. If \(g\) is integrable and \(\mathcal{F}_\infty\)-measurable, then \(\mathbb{E}[g\mid\mathcal{F}_n]\) converges to \(g\) almost everywhere and in \(L^1\) (`Probability/Martingale/Convergence.lean`).

Optional sampling, for a discrete martingale: the value at a stopping time \(\tau\) bounded by \(n\) is the conditional expectation of \(f_n\) on the σ-algebra of \(\tau\). If \(\sigma\leq\tau\) and \(\tau\) is bounded, the value at \(\sigma\) is the conditional expectation of the value at \(\tau\). If \(\tau\) is a bounded stopping time and \(\sigma\) is any stopping time, the value at \(\min(\tau,\sigma)\) is the conditional expectation of the value at \(\tau\) on the σ-algebra of \(\sigma\) (`Probability/Martingale/OptionalSampling.lean`).

Optional stopping, or the fair-game theorem: an integrable adapted process is a submartingale if and only if \(\mathbb{E}[f_\tau]\leq\mathbb{E}[f_\pi]\) whenever \(\tau\leq\pi\) are bounded stopping times. The process stopped at a stopping time remains a submartingale. Doob’s maximal inequality: for a nonnegative submartingale and \(\varepsilon\geq 0\), if \(f^*_n=\max_{k\leq n}f_k\), then
\[
\varepsilon\,\mu\{f^*_n\geq\varepsilon\}\leq\int_{\{f^*_n\geq\varepsilon\}} f_n\,d\mu
\]
(`Probability/Martingale/OptionalStopping.lean`).

Lévy’s generalization of Borel–Cantelli: if \(s_n\in\mathcal{F}_n\), the limsup of the sets \(s_n\) agrees almost everywhere with the set where \(\sum_n\mathbb{P}(s_{n+1}\mid\mathcal{F}_n)\) diverges. The one-sided bound used in the proof identifies, for a submartingale with bounded increments, the set of convergence with the set of boundedness (`Probability/Martingale/BorelCantelli.lean`).

Azuma–Hoeffding concentration for adapted sums with conditional sub-Gaussian increments is also proved in `Probability/Moments/SubGaussian.lean`. The parameters add, giving an exponential upper-tail bound for the sum; Section 7 states the hypotheses and the bound.

## Kolmogorov’s condition and Brownian motion

A process satisfies Kolmogorov’s condition with exponents \(p,q\) and constant \(M\) when pairs of values are measurable and
\[
\int \operatorname{edist}(X_s,X_t)^p\,dP \leq M\,\operatorname{edist}(s,t)^q.
\]
The file defines this condition, and the condition of being a modification of such a process, and identifies it as the hypothesis of the Kolmogorov–Chentsov continuity theorem. The continuity theorem itself is not claimed (`Probability/Process/Kolmogorov.lean`).

A real process indexed by nonnegative reals is pre-Brownian when its finite-dimensional distributions are the centered Gaussian measures with covariance \(\min(s,t)\). It is Brownian when it is pre-Brownian and its paths are almost surely continuous. A centered Gaussian process with that covariance is pre-Brownian. The shifted process \(t\mapsto B_{t+t_0}-B_{t_0}\) is pre-Brownian and independent of the past up to \(t_0\) (`Probability/BrownianMotion/Basic.lean`).

Those finite-dimensional distributions form a projective family: the centered Gaussian on maps from a finite set \(I\subset\mathbb{R}_{\geq 0}\) to \(\mathbb{R}\), with covariance \(\min(s,t)\). The file records that a projective family is the input of Kolmogorov’s extension theorem, and that the extension theorem is not in the library (`Probability/BrownianMotion/GaussianProjectiveFamily.lean`).

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti proves Kolmogorov extension for a **countable** index set and standard Borel coordinate spaces: a projectively consistent family of finite-dimensional probability laws has a probability law on the countable product ([countable projective limits](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/Measure/ProjectiveLimit/Countable.lean)). This does not by itself construct a process indexed by every real time.

Lévy's downward theorem is also present: conditional expectations of an integrable real random variable along a decreasing sequence of σ-algebras converge almost everywhere and in \(L^1\) to conditional expectation on their intersection, on a finite measure space ([reverse-martingale convergence](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Probability/Martingale/Convergence.lean)). The de Finetti and separately exchangeable array representations of Section 6 give further process laws. None of these is an Itô integral or a continuous-time stochastic-calculus development.

## Topics of Section 8 not found in either inspected library

- Kolmogorov extension for arbitrary, possibly uncountable index sets. TauCeti proves the countable-index standard Borel case.
- The Kolmogorov–Chentsov theorem. The moment condition is defined.
- Continuous-time martingale theory beyond the definitions that apply to a general time index: the convergence, sampling, and maximal theorems above are discrete.
- The stochastic integral, quadratic variation, Itô’s formula, Girsanov’s theorem, and stochastic differential equations.
- Semimartingales. A localizing sequence and the notion of a local property are defined.
