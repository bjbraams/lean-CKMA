# Structure 08: Stochastic processes, martingales, and stochastic calculus

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS08.md); [bibliographical scope](CKMA-bib.md#ckma-08); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; the **Synopsis entries** line at the end of each section states which numbered results are covered.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Probability.Process`, `Mathlib.Probability.Martingale`, `Mathlib.Probability.BrownianMotion`, `Mathlib.Probability.Independence.Process`, `Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess`, `Mathlib.Probability.Kernel.Invariance`, `Mathlib.Probability.Kernel.Irreducible`, `Mathlib.MeasureTheory.Function.ConditionalExpectation`.

**Namespaces.** `MeasureTheory`, with nested `Filtration`, `Martingale`, `Submartingale`, `Supermartingale`, and `IsStoppingTime`. Brownian motion is `ProbabilityTheory`, with nested `BrownianReal` and the predicates `IsPreBrownianReal` and `IsBrownianReal`. Kernels are `ProbabilityTheory.Kernel`. Conditional expectation remains `MeasureTheory.condExp`, as in [Section 06](STRUCTURE06.md). TauCeti process declarations are in `TauCeti.Probability`.

<a id="structure-08a"></a>

## 08A. General Theory, Martingales, and Stochastic Calculus

Process measurability, stopping times, the finite-dimensional-law predicates for Brownian motion, and martingales indexed by a general time set belong here. The discrete-time martingale theorems (Doob decomposition, upcrossings, convergence, optional sampling, maximal inequality, Lévy's upward and downward theorems) are recorded in [Section 06](STRUCTURE06.md#discrete-time-martingales).

### Brownian motion and its sample paths

[Mathematical scope](SYNOPSIS08.md#brownian-motion-and-its-sample-paths).

#### Mathlib

**Process laws.** The law of a process is the pushforward of the probability measure under the map that sends a sample to the whole path, equipped with the product (cylinder) σ-algebra. Two processes have the same law if and only if all their finite-dimensional distributions agree. A modification, meaning a process equal at each fixed time almost surely, has the same finite-dimensional distributions and the same law (`Probability/Process/FiniteDimensionalLaws.lean`). Two processes are indistinguishable when, almost surely, they agree at every time simultaneously; this predicate has its own notation and API (`Probability/Process/Indistinguishable.lean`). A Gaussian process is a process whose finite-dimensional distributions are Gaussian (`IsGaussianProcess`, `Probability/Distributions/Gaussian/IsGaussianProcess/Def.lean`). A process has independent increments when the increments along every finite increasing sequence of times are independent, equivalently along every monotone sequence; a process with independent increments, Gaussian marginals, and almost surely zero initial value is a Gaussian process (`Probability/Independence/Process/HasIndepIncrements/Basic.lean`, `Probability/Independence/Process/HasIndepIncrements/IsGaussianProcess.lean`). Independence of a process from a random variable, or of two processes, follows from independence of their finite-dimensional marginals (`Probability/Independence/Process/Basic.lean`).

**Kolmogorov’s condition.** A process satisfies Kolmogorov’s condition with exponents \(p,q\) and constant \(M\) when pairs of values are measurable and
\[
\int \mathop{\mathrm{edist}}(X_s,X_t)^p\,dP \leq M\,\mathop{\mathrm{edist}}(s,t)^q.
\]
The file defines this condition (`IsKolmogorovProcess`), and the condition of being a modification of such a process (`IsAEKolmogorovProcess`), and identifies it as the hypothesis of the Kolmogorov–Chentsov continuity theorem. The continuity theorem itself is not stated (`Probability/Process/Kolmogorov.lean`). The covering-exponent and pair-reduction lemmas recorded in [Section 07](STRUCTURE07.md#metric-entropy-gaussian-comparison-and-chaining) were introduced for its proof.

**Brownian motion.** A real process indexed by nonnegative reals is pre-Brownian when its finite-dimensional distributions are the centered Gaussian measures with covariance \(\min(s,t)\). It is Brownian when it is pre-Brownian and its paths are almost surely continuous. A centered Gaussian process with that covariance is pre-Brownian (`IsGaussianProcess.isPreBrownianReal_of_covariance`). A process with independent increments and \(B_t\) of law \(N(0,t)\) for every \(t\) is pre-Brownian, and a pre-Brownian process has independent increments. The shifted process \(t\mapsto B_{t+t_0}-B_{t_0}\) is pre-Brownian and independent of the past up to \(t_0\) (the simple Markov property at a fixed time, `IsPreBrownianReal.indepFun_shift`). The class is invariant under \(B\mapsto-B\), under Brownian scaling \(t\mapsto c^{-1/2}B_{ct}\), \(c>0\), and, for pre-Brownian motion, under time inversion \(t\mapsto tB_{1/t}\) (`IsPreBrownianReal.neg`, `IsPreBrownianReal.smul`, `IsPreBrownianReal.inv`); negation, scaling, and shift also preserve Brownian motion (`Probability/BrownianMotion/Basic.lean`).

Those finite-dimensional distributions form a projective family: the centered Gaussian on maps from a finite set \(I\subset\mathbb{R}_{\geq 0}\) to \(\mathbb{R}\), with covariance \(\min(s,t)\) (`isProjectiveMeasureFamily_projectiveFamily`, `Probability/BrownianMotion/GaussianProjectiveFamily.lean`). Since the law of a process on the product σ-algebra is determined by its finite-dimensional distributions, all pre-Brownian motions have the same law there.

No process satisfying either predicate is constructed. Existence of Brownian motion would need the extension theorem for the uncountable index set and the Kolmogorov–Chentsov theorem, neither of which is proved, so the statements above are conditional on being given a Brownian motion.

#### TauCeti

TauCeti proves Kolmogorov extension for a **countable** index set and standard Borel coordinate spaces: a projectively consistent family of finite-dimensional probability laws has a probability law on the countable product ([countable projective limits](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Measure/ProjectiveLimit/Countable.lean), `TauCeti.Measure.exists_isProjectiveLimit_of_countable`). This gives Brownian motion at dyadic times, but does not by itself construct a process indexed by every real time.

**Synopsis entries.** Partly covered: 08.1 (uniqueness of the law on the product σ-algebra in dimension one; existence and the law on continuous path space are absent), 08.2 (scaling, negation, and time inversion in dimension one; orthogonal and conformal invariance are absent). Not covered: 08.63, 08.3–08.8.

### Continuous-time martingales and quadratic variation

[Mathematical scope](SYNOPSIS08.md#continuous-time-martingales-and-quadratic-variation).

#### Mathlib

**Processes, filtrations, and stopping times.** A filtration is a monotone family of sub-σ-algebras. Filtrations form a complete lattice. The natural filtration of a process is the smallest filtration to which the process is adapted. The right-continuation of a filtration enlarges each σ-algebra by the information immediately after the present time, and a filtration is right-continuous when it equals its right-continuation. A filtration is σ-finite when each of its σ-algebras makes the restricted measure σ-finite (`Probability/Process/Filtration.lean`).

A process is adapted when the value at time \(i\) is measurable for the σ-algebra at time \(i\), and progressively measurable when its restriction up to time \(i\) is measurable on the product of the past with the sample space. Strong measurability gives the corresponding strong notions. A continuous strongly adapted process is strongly progressive (`Probability/Process/Adapted.lean`).

The predictable σ-algebra is generated from the filtration in the usual way. A predictable process is measurable for that σ-algebra, and every predictable process is progressively measurable and adapted. In discrete time, predictability of \(u\) is measurability of \(u_{n+1}\) for \(\mathcal{F}_n\), together with measurability of \(u_0\) for \(\mathcal{F}_0\) (`Probability/Process/Predictable.lean`).

A stopping time takes values in the time index extended by a point at infinity, and \(\{\tau\leq i\}\) lies in \(\mathcal{F}_i\). It generates a σ-algebra. The stopped process of a progressively measurable process is progressively measurable, and stopping preserves membership in \(L^p\) along discrete time (`Probability/Process/Stopping.lean`).

The first time a process enters a set, between two deterministic times or after a deterministic time, is a hitting time. In discrete time, the hitting time of a strongly adapted process is a stopping time (`Probability/Process/HittingTime.lean`).

A property of processes holds locally, relative to a filtration, when some sequence of stopping times increases almost surely to infinity and each stopped process satisfies the property. A property is stable when it passes to stopped processes; the localization of a stable property is stable (`Probability/Process/LocalProperty.lean`). Local martingales and semimartingales are not defined.

**Martingales on a general time index.** An integrable adapted process with values in a Banach space is a martingale when \(\mu[f_j\mid\mathcal{F}_i]=f_i\) almost surely whenever \(i\leq j\), for any preordered time index, and similarly for sub- and supermartingales (`Probability/Martingale/Basic.lean`). Optional sampling holds for a martingale indexed by a linearly ordered time set with the order topology, in particular by \(\mathbb{R}_{\ge0}\), when the stopping times \(\sigma\le\tau\) are bounded and have countable range: the value at \(\sigma\) is the conditional expectation of the value at \(\tau\) (`stoppedValue_ae_eq_condExp_of_le_of_countable_range`, `Probability/Martingale/OptionalSampling.lean`). The convergence, maximal, and decomposition theorems are discrete-time ([Section 06](STRUCTURE06.md#discrete-time-martingales)). Azuma–Hoeffding concentration for adapted sums with conditionally sub-Gaussian increments is recorded in [Section 07](STRUCTURE07.md#product-spaces-entropy-and-geometric-concentration).

**Synopsis entries.** Partly covered: 08.10 (bounded stopping times with countable range; the càdlàg approximation and the uniformly integrable case are absent). Not covered: 08.9, 08.11–08.16.

### Stochastic integration and Itô's formula

[Mathematical scope](SYNOPSIS08.md#stochastic-integration-and-itôs-formula).

Neither library defines a stochastic integral. The predictable σ-algebra and the local-property framework above are the nearest supporting material.

**Synopsis entries.** Not covered: 08.17–08.26.

### Stochastic exponentials and change of measure

[Mathematical scope](SYNOPSIS08.md#stochastic-exponentials-and-change-of-measure).

**Synopsis entries.** Not covered: 08.27–08.30.

### Stochastic differential equations and approximation

[Mathematical scope](SYNOPSIS08.md#stochastic-differential-equations-and-approximation).

**Synopsis entries.** Not covered: 08.31–08.33, 08.39, 08.40, 08.57.

### Local time, occupation, and reflection

[Mathematical scope](SYNOPSIS08.md#local-time-occupation-and-reflection).

**Synopsis entries.** Not covered: 08.41–08.44, 08.64–08.67.

### Poisson integration and Lévy processes

[Mathematical scope](SYNOPSIS08.md#poisson-integration-and-lévy-processes).

The scalar Poisson law of [Section 06](STRUCTURE06.md) and the TauCeti Lévy–Khintchine representation of Bernstein functions (Section 49), which concerns Laplace exponents only, are the nearest supporting material.

**Synopsis entries.** Not covered: 08.53–08.56.

### Jump exponentials and Lévy-path variation

[Mathematical scope](SYNOPSIS08.md#jump-exponentials-and-lévy-path-variation).

**Synopsis entries.** Not covered: 08.60, 08.61.

<a id="structure-08b"></a>

## 08B. Markov Processes, Potential Theory, and Spatial Models

Transition kernels, invariant measures, discrete-time Markov chain laws, and exchangeability descriptions of mixtures of Markov chains supply the coverage in this subdivision.

### Markov semigroups, martingale problems, and chains

[Mathematical scope](SYNOPSIS08.md#markov-semigroups-martingale-problems-and-chains).

#### Mathlib

**Markov kernels as Markov chains.** The kernel library of [Section 06](STRUCTURE06.md) supplies the transition-kernel side of discrete-time Markov chains; composition of kernels is the Chapman–Kolmogorov operation. A measure is invariant for a kernel \(\kappa\) when \(\mu\) composed with \(\kappa\) is \(\mu\), and a kernel reversible for \(\pi\) (detailed balance) leaves \(\pi\) invariant (`Kernel.IsReversible.invariant`, `Probability/Kernel/Invariance.lean`). A kernel is \(\varphi\)-irreducible when every set of positive \(\varphi\)-measure is reached with positive probability, in some number of steps, from every state (`Probability/Kernel/Irreducible.lean`). The Ionescu–Tulcea theorem gives the law of the trajectory of a discrete-time chain (`Probability/Kernel/IonescuTulcea/Traj.lean`). Harris recurrence, drift conditions, convergence to equilibrium, and mixing-time bounds are not stated.

#### TauCeti

TauCeti packages the path law of a time-homogeneous Markov chain with given initial law and transition kernel, with its Markov property and the product formula for cylinder probabilities ([Markov chains](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Process/MarkovChain.lean), `TauCeti.Probability.markovChainLaw`). It proves that a stationary process on a countable state space is recurrent, by Poincaré recurrence for the shift ([recurrence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Recurrent/Basic.lean), `TauCeti.Probability.recurrent_of_measurePreserving_shift`). For a Markov chain on a countable state space started at a recurrent state, the successive excursions from that state are independent and identically distributed, and the path law is the image of their infinite product under concatenation ([excursions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Process/Excursion/MarkovChain.lean), `TauCeti.Probability.markovChainLaw_eq_map_pathOfExcursions`). The Diaconis–Freedman theorem is proved: a recurrent process on a countable state space is Markov exchangeable if and only if it is a mixture of Markov chains ([Diaconis–Freedman](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Exchangeability/Recurrence/InitialState.lean), `TauCeti.Probability.markovExchangeable_iff_mixedMarkovChain`). The de Finetti and separately exchangeable array representations of Section 06 give further process laws.

Strongly continuous semigroups on Banach spaces, with the Hille–Yosida and Lumer–Phillips generation theorems, are developed analytically ([semigroups](https://github.com/TauCetiProject/TauCeti/tree/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Semigroups)); they are not connected to transition kernels or Feller processes.

**Synopsis entries.** Partly covered: 08.45 (Chapman–Kolmogorov as kernel composition and the construction of discrete-time chains; continuous-time construction is absent). Not covered: 08.46–08.52, 08.68–08.70.

### Diffusion generators and analytic equations

[Mathematical scope](SYNOPSIS08.md#diffusion-generators-and-analytic-equations).

**Synopsis entries.** Not covered: 08.34–08.38.

### Interacting particle systems

[Mathematical scope](SYNOPSIS08.md#interacting-particle-systems).

**Synopsis entries.** Not covered: 08.71, 08.72.

### Harmonic transforms and invariant diffusion laws

[Mathematical scope](SYNOPSIS08.md#harmonic-transforms-and-invariant-diffusion-laws).

**Synopsis entries.** Not covered: 08.58, 08.59, 08.62.

<a id="structure-08c"></a>

## 08C. Stochastic Control, Optimal Stopping, Backward Equations, and Mean-Field Games

The reusable probabilistic ingredients for stochastic control are conditional expectation and transition kernels in [Section 06](STRUCTURE06.md), stopping times and optional sampling in 08A and Section 06, and the Markov-kernel constructions in 08B. These are supporting structures for formulating control problems.

### Optimal stopping

[Mathematical scope](SYNOPSIS08.md#optimal-stopping).

**Synopsis entries.** Not covered: 08.73, 08.74.

### Controlled diffusions and dynamic programming

[Mathematical scope](SYNOPSIS08.md#controlled-diffusions-and-dynamic-programming).

**Synopsis entries.** Not covered: 08.75, 08.76.

### Backward stochastic differential equations

[Mathematical scope](SYNOPSIS08.md#backward-stochastic-differential-equations).

**Synopsis entries.** Not covered: 08.77–08.79.

### Mean-field games

[Mathematical scope](SYNOPSIS08.md#mean-field-games).

**Synopsis entries.** Not covered: 08.80, 08.81.
