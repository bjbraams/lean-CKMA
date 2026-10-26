# Short derivations for entries of GAPS.md

[GAPS.md](GAPS.md) selects principal theorem statements of core mathematical
analysis that are not proved in Mathlib or TauCeti. Neither library states the
**59 statements** below. Each follows from results that the libraries do prove,
by a comparatively short argument: a combination of existing theorems, a
specialization, a finite calculation, or a construction packaged in a new
definition. They stay in `GAPS.md` because they belong to the core knowledge
of analysis. This file gives, for each of them, an outline of the argument and
the library results it uses.

The library revisions are those recorded in `GAPS.md`:

- Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca`
- TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`

Both are dated 18 October 2026. Paths are relative to the root of the
respective repository.

## How to read the entries

Entries follow the order and section headings of `GAPS.md`. Each entry has
the following parts.

- **Statement:** the entry as it appears in `GAPS.md`, including its
  account of what the libraries already contain.
- **Scope:** present only when the short argument covers just part of the
  statement (23.9 and 42.52). The rest of that statement remains a
  substantial gap.
- **Argument:** an outline of the proof from library results.
- **Library results:** the declarations and files used.

Every declaration and file named here was located in the sources at the
revisions above. Admissions, acquisition targets and roadmap text were not
used. No Lean code implementing these arguments has been written or
compiled, and no axiom audit has been performed. "Short" describes the
mathematics. Some arguments still need definitions, transport between
formulations, or measurability code, and none of this is an estimate of the
effort needed to formalize them. An entry of `GAPS.md` that is absent here is
not thereby certified to lack a short proof.

## Index

- **05.** 05.7 Baire classification of derivatives; 05.30 Approximate continuity.
- **06.** 06.1 Kolmogorov extension theorem; 06.62 Varadhan's integral lemma.
- **07.** 07.4 Bernstein's inequality; 07.6 Equivalent sub-Gaussian descriptions; 07.33 Symmetrization; 07.47 Johnson–Lindenstrauss lemma.
- **08.** 08.7 Quadratic variation.
- **11.** 11.22 Hardy–Littlewood–Pólya characterization; 11.24 Karamata's inequality; 11.37 Hilbert's integral inequality; 11.38 Carleman's inequality.
- **12.** 12.32 Everywhere-defined proximal mapping.
- **13.** 13.7 Cauchy interlacing; 13.8 Weyl inequalities; 13.10 Hoffman–Wielandt inequality; 13.13 Von Neumann trace inequality; 13.18 Eckart–Young–Mirsky theorem.
- **14.** 14.40 Nash inequality.
- **16.** 16.13 Bipolar theorem for dual pairs.
- **20.** 20.40 Wiener lemma.
- **21.** 21.11 Atkinson theorem; 21.16 Discrete spectrum of self-adjoint operators.
- **22.** 22.32 Kato–Rellich theorem: cores.
- **23.** 23.9 GNS cyclic vector and uniqueness; 23.10 Gelfand–Naimark theorem.
- **25.** 25.3 Hilbert–Schmidt kernels; 25.18 Volterra solvability; 25.23 Abel inversion; 25.47 Collectively compact approximation theorem.
- **26.** 26.16 Failure of the critical $L^\infty$ embedding; 26.37 Fractional Hilbert identity; 26.53 Real interpolation theorem; 26.54 Complex interpolation theorem.
- **27.** 27.4 Hausdorff–Young inequality; 27.13 Heisenberg uncertainty.
- **28.** 28.2 The modular homomorphism.
- **29.** 29.2 Frame operator criterion; 29.3 Canonical dual reconstruction; 29.58 Shannon sampling theorem.
- **31.** 31.24 Lyapunov's direct theorem; 31.26 LaSalle invariance principle.
- **36.** 36.1 Euler–Lagrange equation.
- **39.** 39.73 Self-similar attractors.
- **40.** 40.25 Laurent expansion.
- **42.** 42.51 Bergman kernel; 42.52 Bergman projection.
- **45.** 45.2 Polydisk Taylor expansion and estimates.
- **46.** 46.10 Koenigs linearization; 46.11 Böttcher's theorem.
- **47.** 47.17 Korovkin theorem.
- **48.** 48.6 Real and simple zeros; 48.14 Gauss quadrature; 48.34 Hausdorff theorem.
- **49.** 49.6 Gamma multiplication beyond duplication; 49.13 Gauss equation; 49.30 Bessel generating function.
- **50.** 50.23 Euler–Maclaurin formula.

---

## 05. Differentiation and the fine structure of real functions

### 05.7. Baire classification of derivatives

**Statement.** If $f$ is differentiable on an
open interval, $f'$ is of Baire class one, as follows by taking continuous
difference quotients locally.

**Argument.** Put $h_n(x)=\min(1/n,\mathop{\mathrm{dist}}(x,\mathbb R\setminus
I)/2)$. It is continuous and positive on $I$, and $x+h_n(x)\in I$. The
quotients $g_n(x)=(f(x+h_n(x))-f(x))/h_n(x)$ are continuous because $f$ is.
For fixed $x$, $h_n(x)=1/n$ for large $n$, so $g_n(x)\to f'(x)$ by the
difference-quotient characterization of the derivative. Neither library
defines Baire class one; the conclusion can be stated as the existence of
such a sequence.

**Library results.** `hasDerivAt_iff_tendsto_slope_zero` in
`Mathlib/Analysis/Calculus/Deriv/Slope.lean`; `HasDerivAt.continuousAt` and
continuity of `Metric.infDist`.

### 05.30. Approximate continuity

**Statement.** Every finite measurable function is
approximately continuous almost everywhere: for almost every $x$ and every
$\varepsilon>0$, the set $\{y:|f(y)-f(x)|>\varepsilon\}$ has density zero at $x$.

**Argument.** Put $g=\arctan\circ f$, which is bounded and measurable, hence
locally integrable. Almost every $x$ is a Lebesgue point of $g$:
$|B(x,r)|^{-1}\int_{B(x,r)}|g(y)-g(x)|\,dy\to0$. Fix such an $x$ and
$\varepsilon>0$. Continuity of $\tan$ at $g(x)\in(-\pi/2,\pi/2)$ gives
$\delta>0$ such that $|g(y)-g(x)|\le\delta$ implies
$|f(y)-f(x)|\le\varepsilon$. Markov's inequality on $B(x,r)$ then bounds the
relative measure of $\{|f(y)-f(x)|>\varepsilon\}$ by $\delta^{-1}$ times that
average, which tends to zero.

**Library results.** `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub` in
`Mathlib/MeasureTheory/Covering/DensityTheorem.lean`, for closed balls of a
doubling measure such as Lebesgue measure;
`VitaliFamily.ae_tendsto_average_norm_sub` in
`Mathlib/MeasureTheory/Covering/Differentiation.lean`; Markov's inequality
`MeasureTheory.mul_meas_ge_le_integral_of_nonneg`; `Real.continuousOn_tan_Ioo`
and `Real.tan_arctan` in `Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean`.

## 06. Probability, measure-theoretic foundations, and limit theory

### 06.1. Kolmogorov extension theorem

**Statement.** A consistent family of finite-dimensional
probability distributions, indexed by the finite subsets of an arbitrary
(possibly uncountable) index set, with standard Borel coordinate spaces
determines a unique law on the product $\sigma$-algebra. TauCeti proves
existence for countable index sets, uniqueness is available in general, and
Mathlib constructs arbitrary products of probability measures; missing is
existence for an uncountable index set, for instance by reduction to countably
many coordinates.

**Argument.** Uniqueness holds in general. For existence, put the projective
family content on measurable cylinders. By the argument Mathlib uses for
product measures, $\sigma$-additivity reduces to the following claim. If
$A_n$ are decreasing cylinders whose contents stay above $\varepsilon>0$,
then $\bigcap_nA_n\ne\varnothing$. Each $A_n$ depends on a finite set
$J_n$, so all of them depend on the countable set $J=\bigcup_nJ_n$. The
family restricted to finite subsets of $J$ is projective. TauCeti's
countable theorem gives a probability measure $\mu_J$ on $\prod_{i\in J}X_i$
with $\mu_J(B_n)=$ content$(A_n)\ge\varepsilon$, where $A_n$ is the
preimage of $B_n$. Continuity from above gives
$\mu_J(\bigcap_nB_n)\ge\varepsilon$, so some $y$ lies in every $B_n$. Each
$X_i$ carries a probability measure and is therefore nonempty, so $y$
extends arbitrarily outside $J$ to a point of $\bigcap_nA_n$. The content is
then $\sigma$-subadditive and extends to a measure, which is a projective
limit.

**Library results.** `TauCeti.Measure.exists_isProjectiveLimit_of_countable` in
`TauCeti/MeasureTheory/Measure/ProjectiveLimit/Countable.lean`;
`MeasureTheory.IsProjectiveLimit.unique` in
`Mathlib/MeasureTheory/Constructions/Projective.lean`;
`projectiveFamilyContent` in
`Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean`. The
model reduction is `piContent_tendsto_zero` and `isSigmaSubadditive_piContent`
in `Mathlib/Probability/ProductMeasure.lean`, using
`addContent_iUnion_eq_sum_of_tendsto_zero` and
`isSigmaSubadditive_of_addContent_iUnion_eq_tsum`
(`Mathlib/MeasureTheory/Measure/AddContent.lean`). `AddContent.measure` is in
`Mathlib/MeasureTheory/OuterMeasure/OfAddContent.lean`.

### 06.62. Varadhan's integral lemma

**Statement.** If $X_n$ satisfies a large deviation
principle with good rate $I$, then for bounded continuous $f$,
$$\lim_n n^{-1}\log\mathbb E e^{nf(X_n)}=\sup_x(f(x)-I(x)).$$

**Argument.** Only the two large-deviation bounds of the hypothesis are used;
neither Cramér's nor Sanov's theorem is needed. Boundedness of $f$ is
essential, since unbounded versions require an additional tail condition.

Put $Z_n=\mathbb E e^{nf(X_n)}$. For any $x$ with $I(x)<\infty$ and
$\delta>0$, the open set $U=\{y:f(y)>f(x)-\delta\}$ gives
$$
\liminf_n n^{-1}\log Z_n
 \ge f(x)-\delta-\inf_U I\ge f(x)-\delta-I(x).
$$
For the upper bound, partition the bounded range of $f$ into finitely many
intervals $[a_j,a_j+\delta]$. Bound the contribution of each interval by
$e^{n(a_j+\delta)}\mathbb P(f(X_n)\ge a_j)$ and apply the LDP upper bound to
the closed set $\{f\ge a_j\}$. The logarithmic growth of a finite sum is at
most the maximum of its summands' growth rates: the factor given by the
number of intervals contributes $\log m/n\to0$. Each rate is at most
$\delta+\sup_x(f(x)-I(x))$. Take the supremum in the lower bound and then
let $\delta\downarrow0$. Empty bins contribute zero; probabilities zero
are handled with extended logarithms. Goodness of $I$, although assumed
in the statement, is not needed in this bounded version.

**Library results.** Mathlib's integral monotonicity and finite additivity
in `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`, and the real
logarithm/exponential laws in
`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`. The LDP bounds are
hypotheses supplied by the statement, not library existence results.

## 07. Concentration, high-dimensional probability, and empirical processes

### 07.4. Bernstein's inequality

**Statement.** For independent centered $X_i$ with
$|X_i|\leq b$ and $v=\sum_i\mathbb EX_i^2$,
$$\mathbb P\left(\left|\sum_iX_i\right|\geq t\right)
  \leq2\exp\left(-\frac{t^2}{2(v+bt/3)}\right).$$

**Argument.** A short estimate of the exponential series feeds Mathlib's Chernoff
bound. The argument does not give the matrix Bernstein inequality 07.44.

For $b>0$, $0\le\lambda<3/b$, centering removes the linear term and
$|X|^k\le b^{k-2}X^2$ for $k\ge2$. Since
$k!\ge2\cdot3^{k-2}$,
$$
\mathbb E e^{\lambda X}
 \le 1+\frac{\lambda^2\mathbb EX^2}{2(1-\lambda b/3)}
 \le \exp\!\left(\frac{\lambda^2\mathbb EX^2}
                         {2(1-\lambda b/3)}\right).
$$
Boundedness justifies termwise integration by absolute domination.
Independence multiplies the MGFs. Chernoff with
$\lambda=t/(v+bt/3)$ gives the upper tail for $v>0,t>0$;
apply the same estimate to $-\sum_iX_i$ and add the two bounds.
If $v=0$, each centered summand is zero almost everywhere; $b=0$ is
likewise trivial. At $t=0$ the usual bound is trivial, with the degenerate
$0/0$ expression interpreted separately.

**Library results.** `ProbabilityTheory.iIndepFun.mgf_sum₀` and
`ProbabilityTheory.measure_ge_le_exp_mul_mgf` in
`Mathlib/Probability/Moments/Basic.lean`;
`NormedSpace.expSeries_div_hasSum_exp` in
`Mathlib/Analysis/Normed/Algebra/Exponential.lean`; geometric series in
`Mathlib/Analysis/SpecificLimits/Normed.lean`. The factorial comparison is
an induction, not an additional concentration theorem.

### 07.6. Equivalent sub-Gaussian descriptions

**Statement.** Up to universal changes of
constants, $\|X\|_{\psi_2}\leq K$ is equivalent to
$\mathbb P(|X|>t)\leq2e^{-ct^2/K^2}$ and to
$(\mathbb E|X|^p)^{1/p}\leq CK\sqrt p$ for $p\geq1$. For centered $X$ it
is also equivalent to a Gaussian moment-generating-function bound. Mathlib
proves that the moment-generating-function bound implies the Gaussian tail
bound; missing are the $\psi_2$ norm and the remaining implications among the
tail, moment-growth, $\psi_2$ and (for centered $X$) moment-generating-function
conditions.

**Argument.** The equivalences follow from tail integration, Markov's inequality and
an independent copy. The $\psi_2$ gauge is a definition, not additional
probability theory. All constants are universal; no sharp constant is
claimed.

If $\mathbb E e^{X^2/s^2}\le2$, Markov gives the Gaussian tail.
Conversely a tail $\mathbb P(|X|>t)\le2e^{-ct^2/K^2}$, integrated against
$d(e^{t^2/s^2})$, gives $\mathbb E e^{X^2/s^2}\le2$ for a sufficiently large
universal multiple $s$ of $K$. The pointwise estimate
$$
t^p\le s^p\left(\frac{p}{2e}\right)^{p/2} e^{t^2/s^2}
$$
then gives the moment bound for every real $p\ge1$. In the other direction,
Markov with $p$ proportional to $t^2/K^2$ gives the Gaussian tail; small
$t$ is absorbed into the constants. Infima in the gauge are handled by
first choosing any admissible $s$ above the infimum and then taking a limit.

For the centered MGF implication, let $X'$ be an independent copy and
$Y=X-X'$. Jensen gives
$\mathbb E e^{\lambda X}\le\mathbb E e^{\lambda Y}$.
The variable $Y$ is symmetric and has a $\psi_2$ bound with parameter
$s\le CK$, by the triangle inequality for moments and the implications
just proved. Consequently
$\mathbb E Y^{2k}\le2s^{2k}k!$. Expanding the MGF, odd moments vanish and
$(2k)!\ge(k!)^2$, so
$$
\mathbb E e^{\lambda Y}
 \le 1+2\sum_{k\ge1}\frac{(s^2\lambda^2)^k}{k!}
 =2e^{s^2\lambda^2}-1\le e^{2s^2\lambda^2}.
$$
Exponential integrability follows already from
$|\lambda Y|\le Y^2/s^2+\lambda^2s^2/4$, so this expansion is justified.
The MGF-to-tail implication is already in Mathlib. Without centering, the
MGF formulation must instead be applied to $X-\mathbb EX$.

**Library results.**
`MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul` in
`Mathlib/MeasureTheory/Integral/Layercake.lean`;
`ProbabilityTheory.exists_iid` in `Mathlib/Probability/HasLawExists.lean`;
integral Jensen in `Mathlib/Analysis/Convex/Integral.lean`;
`Mathlib/Probability/Moments/SubGaussian.lean`, the exponential series,
and the $L^p$ triangle inequality.

### 07.33. Symmetrization

**Statement.** For independent Rademacher signs $\varepsilon_i$,
independent of the data,
$$\mathbb E\sup_{f\in\mathcal F}|(P_n-P)f|
  \leq2\mathbb E\sup_{f\in\mathcal F}
    \left|\frac1n\sum_i\varepsilon_i f(X_i)\right|.$$

**Argument.** An independent copy of the sample exists
(`ProbabilityTheory.exists_iid`). Then
$(P_n-P)f=\mathbb E'[(P_n-P_n')f\mid X]$, so taking the supremum and using
$|\mathbb E'Z|\le\mathbb E'|Z|$ with Fubini gives
$\mathbb E\sup|(P_n-P)f|\le\mathbb E\sup|(P_n-P_n')f|$. Centred pairs are
symmetric, hence equal in law to Rademacher-signed pairs (`bernoulliMeasure`
at $\pm1$ with `iIndepFun`). The triangle inequality produces the factor $2$.
The statement assumes that the supremum is measurable.

**Library results.** `ProbabilityTheory.exists_iid` and `exists_hasLaw_indepFun`
in `Mathlib/Probability/HasLawExists.lean`; `bernoulliMeasure` in
`Mathlib/Probability/Distributions/Bernoulli.lean`; `iIndepFun` in
`Mathlib/Probability/Independence/Basic.lean`; conditional expectation and
Fubini in `Mathlib/MeasureTheory/Function/ConditionalExpectation/`.

### 07.47. Johnson–Lindenstrauss lemma

**Statement.** For $N$ points in Euclidean space and
$0<\varepsilon<1$, a linear map into dimension
$m\leq C\varepsilon^{-2}\log(2N)$ preserves all pairwise squared distances
within factors $1-\varepsilon$ and $1+\varepsilon$.

**Argument.** Draw an iid Gaussian matrix (`exists_iid` with
`gaussianReal 0 1`). Linear images of Gaussians remain Gaussian
(`IsGaussian.map`). For a unit vector $v$, $\|Gv\|^2$ is chi-squared, with
MGF $(1-2t)^{-m/2}$ (`TauCeti.Probability.mgf_id_chiSquaredMeasure`).
Chernoff (`measure_ge_le_exp_mul_mgf`) with the usual
$t=\varepsilon/(2(1+\varepsilon))$ gives sub-exponential tails of order
$e^{-c m\varepsilon^2}$. A union bound over at most $N^2$ pairs, with
$m\le C\varepsilon^{-2}\log(2N)$, yields a map of positive probability, hence
an existent linear map, that preserves all pairwise squared distances.

**Library results.** `exists_iid` as above; `gaussianReal` in
`Mathlib/Probability/Distributions/Gaussian/Real.lean`; `IsGaussian.map`;
TauCeti `TauCeti/Probability/Distributions/Gaussian/ChiSquared.lean`
(`hasLaw_sum_sq_gaussian`, `mgf_mul_sq_gaussianReal`,
`mgf_sum_mul_sq_pi_gaussianReal`);
`TauCeti/Probability/Distributions/ChiSquared.lean`
(`mgf_id_chiSquaredMeasure`); Chernoff in
`Mathlib/Probability/Moments/Basic.lean`.

## 08. Stochastic processes, martingales, and stochastic calculus

### 08.7. Quadratic variation

**Statement.** Along deterministic partitions with mesh tending
to zero, sums of squared Brownian increments converge in probability to elapsed
time, uniformly on compact time intervals. Along dyadic partitions convergence
holds almost surely. Thus $[B^i,B^j]_t=\delta_{ij}t$.

**Argument.** The computation uses only pre-Brownian increment laws, which
Mathlib already has (`IsPreBrownianReal.hasIndepIncrements`, `hasLaw_sub`).
Continuous paths (08.1) are not used. Along a deterministic partition of
$[0,T]$, the increments $\Delta B_i\sim N(0,\Delta t_i)$ are independent, so
$\mathbb E\sum(\Delta B_i)^2=T$. TauCeti's fourth-moment formula
`centralMoment_id_two_mul_gaussianReal` gives $\mathrm{Var}(X^2)=2\sigma^4$
for centred Gaussians, and `IndepFun.variance_sum` yields
$\mathrm{Var}(Q_\pi)=\sum 2(\Delta t_i)^2\le 2\,\mathrm{mesh}\,T\to0$.
Chebyshev (`meas_ge_le_variance_div_sq`) gives convergence in probability at
time $T$. For uniformity on $[0,T]$, $Q_t$ is constant between partition
times, so $\sup_{t\le T}|Q_t-t|$ is controlled by the discrete maximum of the
martingale $M_k=\sum_{i\le k}((\Delta B_i)^2-\Delta t_i)$ plus the mesh;
$M^2$ is a nonnegative submartingale, and Doob's weak-type bound
`maximal_ineq` sends $\mathbb P(\sup|M|\ge\varepsilon)$ to $0$. Along dyadics
the variances are summable, so Borel–Cantelli
(`measure_limsup_atTop_eq_zero`) gives almost-sure convergence. Independent
coordinates (`exists_iid`) give $[B^i,B^j]_t=\delta_{ij}t$.

**Library results.** `IsPreBrownianReal`, `HasIndepIncrements`, `hasLaw_sub` in
`Mathlib/Probability/BrownianMotion/Basic.lean` and
`Mathlib/Probability/Independence/Process/HasIndepIncrements/`;
`TauCeti.Probability.centralMoment_id_two_mul_gaussianReal` in
`TauCeti/Probability/Distributions/Gaussian/Moments.lean`;
`IndepFun.variance_sum`, `meas_ge_le_variance_div_sq` in
`Mathlib/Probability/Moments/Variance.lean`; `maximal_ineq` in
`Mathlib/Probability/Martingale/OptionalStopping.lean`;
`ProbabilityTheory.measure_limsup_atTop_eq_zero` in
`Mathlib/Probability/BorelCantelli.lean`.

## 11. Classical inequalities, means, majorization, and rearrangement

### 11.22. Hardy–Littlewood–Pólya characterization

**Statement.** $x\prec y$ exactly when
$x=Dy$ for a doubly stochastic matrix $D$. TauCeti proves that every $Dy$ lies
in the convex hull of the permutations of $y$, and Birkhoff's theorem gives
the converse; missing is the equivalence with the partial-sum inequalities,
above all the construction of $D$ from $x\prec y$.

**Argument.** Finite-dimensional separation, rearrangement and summation by parts
give both directions.

Write $x^\downarrow,y^\downarrow$ for decreasing rearrangements, and put
$C=\mathop{\mathrm{conv}}\{\sigma y\}$. This is a compact convex set.
If $x\prec y$, then for every real vector $c$, rearrangement and Abel
summation give
$$
c\cdot x\le c^\downarrow\cdot x^\downarrow
 \le c^\downarrow\cdot y^\downarrow
 =\max_\sigma c\cdot(\sigma y).
$$
For the middle inequality, with
$S_k=\sum_{i\le k}(y_i^\downarrow-x_i^\downarrow)$, the difference is
$\sum_{k<n}(c_k^\downarrow-c_{k+1}^\downarrow)S_k\ge0$; the total-sum
term vanishes. Strict separation of $x$ from $C$ would contradict this
inequality, hence $x\in C$. A finite convex expression
$x=\sum_\sigma t_\sigma\sigma y$ supplies
$D=\sum_\sigma t_\sigma P_\sigma$.

Conversely, TauCeti places $Dy$ in $C$. The sum of the $k$ largest
coordinates is $\max_{|J|=k}\sum_{j\in J}z_j$, a convex function invariant
under permutations. Its value on a convex combination of permutations of
$y$ is at most its value on $y$, and the total sum is preserved.
The zero-coordinate case is immediate; repeated entries cause no problem.

**Library results.** `iInter_halfSpaces_eq` and
`geometric_hahn_banach_closed_point` in
`Mathlib/Analysis/LocallyConvex/Separation.lean`;
`Set.Finite.isCompact_convexHull` in
`Mathlib/Analysis/Convex/Topology.lean`;
`Monovary.sum_mul_comp_perm_le_sum_mul` in
`Mathlib/Algebra/Order/Rearrangement.lean`;
`Finset.sum_range_by_parts` in `Mathlib/Algebra/BigOperators/Module.lean`;
`mem_convexHull_iff_exists_fintype` in
`Mathlib/Analysis/Convex/Combination.lean`; and
`Matrix.mulVec_mem_convexHull_range_comp_perm` in TauCeti's
`TauCeti/Analysis/Convex/PermutationOrbit.lean`.

### 11.24. Karamata's inequality

**Statement.** If $x\prec y$ and $\phi$ is convex on an
interval containing their entries, then $\sum_i\phi(x_i)\leq\sum_i\phi(y_i)$.
For strictly convex $\phi$, equality requires $x$ and $y$ to be permutations.
TauCeti proves the inequality when $x=Dy$ with $D$ doubly stochastic; missing
are the partial-sum hypothesis (which reduces to 11.22) and the equality case.

**Argument.** A direct argument avoids 11.22. After sorting
decreasingly, convex functions on $\mathbb R$ are right-differentiable on the
interior (`differentiableWithinAt_Ioi_of_mem_interior`,
`rightDeriv_le_slope`, `monotoneOn_rightDeriv`). The supporting-line
inequality $\phi(y_i)\ge\phi(x_i)+s_i(y_i-x_i)$ and Abel summation
(`sum_range_by_parts'`, or Abel's inequality in
`Mathlib/Algebra/Order/Chebyshev.lean`) give $\sum\phi(x_i)\le\sum\phi(y_i)$,
because the prefix sums of $y-x$ are nonnegative and the slopes $s_i$ are
decreasing. For strictly convex $\phi$, `rightDeriv_lt_slope` forces equality
only when the sorted tuples agree, i.e. when $x$ and $y$ are permutations.
TauCeti's doubly-stochastic form
(`ConvexOn.sum_map_mulVec_le_of_mem_doublyStochastic`) is a different route,
not a prerequisite.

**Library results.** Right derivatives of convex functions in
`Mathlib/Analysis/Convex/Deriv.lean`; `sum_range_by_parts'` in
`Mathlib/Algebra/BigOperators/Module.lean`; Abel/Chebyshev in
`Mathlib/Algebra/Order/Chebyshev.lean`. TauCeti
`TauCeti/Analysis/Convex/DoublyStochasticMatrix.lean` is related but unused
in this argument.

### 11.37. Hilbert's integral inequality

**Statement.** For $1<p<\infty$, $p'=p/(p-1)$, and nonnegative $f\in L^p(0,\infty)$,
$g\in L^{p'}(0,\infty)$,
$$\int_0^\infty\!\int_0^\infty\frac{f(x)g(y)}{x+y}dxdy
  \leq\frac{\pi}{\sin(\pi/p)}\|f\|_p\|g\|_{p'}.$$
The same optimal constant holds in the discrete sum with denominator $m+n$,
$m,n\geq1$.

**Argument.** Hölder's inequality, a one-variable substitution and the beta integral
give both inequalities with the optimal constant.

For nonnegative $f,g$, put $y=tx$. Tonelli and Hölder yield
$$
\iint\frac{f(x)g(y)}{x+y}\,dx\,dy
 =\int_0^\infty\frac{1}{1+t}\int_0^\infty f(x)g(tx)\,dx\,dt
 \le\|f\|_p\|g\|_{p'}\int_0^\infty\frac{t^{-1/p'}}{1+t}\,dt.
$$
The last integral is $B(1/p,1/p')=\pi/\sin(\pi/p)$ by Euler reflection.
Testing $f(x)=x^{-1/p}1_{[1,R]}$ and
$g(x)=x^{-1/p'}1_{[1,R]}$ proves sharpness: divide by $\log R$ and use
dominated convergence in the displayed $t$ integral. For fixed $t$ the
logarithmic length of the overlapping intervals, divided by $\log R$,
tends to one and is bounded by one.

For sequences, take $f=a_m$ on $[m-1,m)$ and $g=b_n$ on $[n-1,n)$.
Since $x+y\le m+n$ there, the integral dominates the discrete sum and the
norms are preserved. The discrete constant cannot be smaller: approximate
continuous compactly supported test functions away from zero by a mesh
of spacing $h$, with $a_m=h^{1/p}f(hm)$ and
$b_n=h^{1/p'}g(hn)$. The sum becomes a Riemann sum with factor $h^2$ for
the continuous bilinear form, and both norms converge. Finite truncation
and monotone convergence handle infinite nonnegative sequences.

**Library results.** Hölder in
`Mathlib/MeasureTheory/Integral/MeanInequalities.lean`; Tonelli/Fubini in
`Mathlib/MeasureTheory/Integral/Prod.lean`;
`TauCeti.integral_rpow_mul_one_add_rpow` in
`TauCeti/Analysis/SpecialFunctions/Beta.lean`;
`Complex.Gamma_mul_Gamma_one_sub` in
`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`; dominated convergence
and ordinary change of variables. No Hardy inequality is needed.

### 11.38. Carleman's inequality

**Statement.** For a nonnegative summable sequence,
$\sum_{n\geq1}(a_1\cdots a_n)^{1/n}\leq e\sum_{n\geq1}a_n$.
The constant $e$ is optimal.

**Argument.** Weighted AM–GM, a telescoping sum and Stirling's formula suffice.

AM–GM applied to $a_1,2a_2,\ldots,na_n$ gives
$$
(a_1\cdots a_n)^{1/n}
 \le\frac{1}{n(n!)^{1/n}}\sum_{k=1}^n ka_k
 \le\frac{e}{n(n+1)}\sum_{k=1}^n ka_k.
$$
For the last step, telescope
$\log(n!)=n\log(n+1)-\sum_{k=1}^n k\log(1+1/k)$ and use
$\log(1+1/k)\le1/k$. Interchanging the nonnegative sums and using
$\sum_{n\ge k}1/(n(n+1))=1/k$ proves the bound, as well as summability.
For sharpness use $a_k=1/k$ for $k\le N$ and zero otherwise.
Stirling gives $n(n!)^{-1/n}\to e$, so comparison with the divergent
harmonic sums shows that the ratio of the two sides' sums tends to $e$.
All inequalities also hold when some $a_k$ vanish.

**Library results.** `Real.geom_mean_le_arith_mean_weighted` in
`Mathlib/Analysis/MeanInequalities.lean`;
`Real.log_le_sub_one_of_pos` in
`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`;
`Stirling.factorial_isEquivalent_stirling` in
`Mathlib/Analysis/SpecialFunctions/Stirling.lean`; nonnegative sum
interchange and the elementary telescoping identity.

## 12. Convexity, convex analysis, optimization, and variational analysis

### 12.32. Everywhere-defined proximal mapping

**Statement.** For proper lower
semicontinuous convex $f$ on a Hilbert space and $\gamma>0$, prove that
$$\mathop{\mathrm{prox}}\nolimits_{\gamma f}(x)=
  \mathop{\mathrm{argmin}}\limits_y\left(f(y)+\frac{\|x-y\|^2}{2\gamma}\right)$$
exists for every $x$, and identify it with $J_{\gamma\partial f}x$.
TauCeti has Moreau–Yosida minimizers under compactness hypotheses.
Uniqueness and firm nonexpansiveness on the resolvent graph follow directly
from its subdifferential monotonicity inequality; the selected gap is
unrestricted Hilbert-space existence and the minimizer–resolvent bridge. Once
these exist, Moreau decomposition follows from the existing conjugate-subgradient
reciprocity; the cone case already follows from Hilbert projection.

**Argument.** TauCeti gives a continuous affine minorant
$f\ge\langle a,\cdot\rangle+b$, so
$\varphi(y)=f(y)+\|x-y\|^2/2\gamma$ is coercive. Every sublevel set of
$\varphi$ is convex and closed, hence weakly closed by Mazur's theorem, and
a nonempty one is bounded. It is therefore weakly compact, because a Hilbert
space is reflexive, and $\varphi$ attains its minimum on it. Strict
convexity of the quadratic term gives uniqueness.

Now compare $\varphi(p)$ with $\varphi(p+t(y-p))$ for $0<t\le1$. Convexity
of $f$, division by $t$ and the limit $t\downarrow0$ give
$f(y)\ge f(p)+\langle(x-p)/\gamma,y-p\rangle$. Hence
$(x-p)/\gamma\in\partial f(p)$, which says that $p=J_{\gamma\partial f}x$.
Conversely, this subgradient inequality and
$\|x-y\|^2\ge\|x-p\|^2-2\langle x-p,y-p\rangle$ show that $p$ minimizes.
Firm nonexpansiveness follows by adding the two subgradient inequalities at
$p=\mathop{\mathrm{prox}}(x)$ and $p'=\mathop{\mathrm{prox}}(x')$:
$\|p-p'\|^2\le\langle x-x',p-p'\rangle$.

**Library results.** `TauCeti.exists_affine_le_of_lt` in
`TauCeti/Analysis/Convex/FenchelMoreau.lean`;
`isCompact_toWeakSpace_of_isClosed_of_convex_of_isBounded` in
`TauCeti/Analysis/Normed/Module/Dual/Reflexive/WeakCompact.lean`;
`Convex.toWeakSpace_closure` in
`Mathlib/Analysis/LocallyConvex/WeakSpace.lean`; subdifferentials and their
monotonicity in `TauCeti/Analysis/Convex/Subdifferential.lean`. With the
conjugate reciprocity `mem_subdifferential_fenchelConjugate_iff` in the same
file, this also gives Moreau's decomposition 12.34.

## 13. Matrix analysis, operator monotonicity, and noncommutative inequalities

### 13.7. Cauchy interlacing

**Statement.** Eigenvalues of a Hermitian compression to a
codimension-one subspace interlace those of the original matrix. For a
rank-$k$ perturbation this yields the corresponding index-shift bounds.

**Argument.** Let $B=PAP|_W$ with $\dim W=n-1$. The span of the top $k$
eigenvectors of $B$ is a $k$-dimensional subspace of $W$ on which the
Rayleigh quotient of $A$ is at least $\lambda_k(B)$, so
$\lambda_k(A)\ge\lambda_k(B)$. For the other inequality, intersect $W$ with
the span of the top $k+1$ eigenvectors of $A$. The intersection has
dimension at least $k$, so the variational principle for $B$ gives
$\lambda_k(B)\ge\lambda_{k+1}(A)$. For a perturbation of rank $k$,
intersect the relevant spectral subspaces with the kernel of the
perturbation, which has codimension at most $k$.

**Library results.** `exists_submodule_forall_unit_eigenvalue_le_re_inner` and
`exists_unit_vector_re_inner_le_eigenvalue` in
`TauCeti/Analysis/InnerProductSpace/CourantFischer.lean`;
`Submodule.finrank_sup_add_finrank_inf_eq` in
`Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`.

### 13.8. Weyl inequalities

**Statement.** For Hermitian $A,B$,
$\lambda_{i+j-1}(A+B)\leq\lambda_i(A)+\lambda_j(B)$ when $i+j-1\leq n$.
TauCeti proves the special case $|\lambda_i(A)-\lambda_i(B)|\leq\|A-B\|$;
missing is the inequality with shifted indices.

**Argument.** Take the spans $U$ of the eigenvectors of $A$ with indices at
least $i$, $V$ of those of $B$ with indices at least $j$, and $W$ of the top
$i+j-1$ eigenvectors of $A+B$. Their dimensions sum to $2n+1$, so the three
spaces share a unit vector $x$. Then
$$
\lambda_{i+j-1}(A+B)\le\langle(A+B)x,x\rangle
=\langle Ax,x\rangle+\langle Bx,x\rangle\le\lambda_i(A)+\lambda_j(B).
$$

**Library results.** As for 13.7.

### 13.10. Hoffman–Wielandt inequality

**Statement.** For normal $A,B$, some matching of
their eigenvalues satisfies
$\sum_i|\lambda_i(A)-\lambda_{\pi(i)}(B)|^2\leq\|A-B\|_2^2$.
TauCeti proves the Hermitian case with the decreasing-order matching;
missing is the case of normal matrices with complex eigenvalues.

**Argument.** Write $A=\sum_i\alpha_iu_iu_i^*$ and
$B=\sum_k\beta_kv_kv_k^*$ in orthonormal eigenbases, and put
$W_{ik}=|\langle u_i,v_k\rangle|^2$. Expanding the Frobenius norm gives
$$
\|A-B\|_2^2=\sum_i|\alpha_i|^2+\sum_k|\beta_k|^2
-2\mathop{\mathrm{Re}}\sum_{i,k}\alpha_i\overline{\beta_k}W_{ik}.
$$
This is an affine, hence concave, function of $W$. The matrix $W$ is doubly
stochastic, so by Birkhoff's theorem it lies in the convex hull of the
permutation matrices. A concave function on that hull takes a value at most
its value at $W$ at some vertex $P_\pi$. At $P_\pi$ the expression equals
$\sum_i|\alpha_i-\beta_{\pi(i)}|^2$.

**Library results.** `exists_orthonormalBasis_apply_eq_smul_of_isStarNormal` in
`TauCeti/Analysis/InnerProductSpace/NormalOperator.lean`;
`schurWeight` and `schurWeight_mem_doublyStochastic` in
`TauCeti/Analysis/InnerProductSpace/SchurHorn.lean`;
`doublyStochastic_eq_convexHull_permMatrix` in
`Mathlib/Analysis/Convex/Birkhoff.lean`;
`ConcaveOn.exists_le_of_mem_convexHull` in
`Mathlib/Analysis/Convex/Jensen.lean`.

### 13.13. Von Neumann trace inequality

**Statement.** $|\mathop{\mathrm{tr}}(A^*B)|\leq\sum_i s_i(A)s_i(B)$.
TauCeti proves the Hermitian form
$\mathop{\mathrm{Re}}\mathop{\mathrm{tr}}(AB)\leq\sum_i\lambda_i(A)\lambda_i(B)$ and the
bound $|\mathop{\mathrm{tr}}(AU)|\leq\sum_is_i(A)$ for unitary $U$; missing is the
singular-value form for arbitrary square matrices.

**Argument.** Take a singular-value decomposition
$B=\sum_ks_k(B)\,y_kx_k^*$. Then
$\mathop{\mathrm{tr}}(A^*B)=\sum_ks_k(B)\langle y_k,Ax_k\rangle$. The phases of
the coefficients can be absorbed into the orthonormal family $(y_k)$. Ky Fan's
bound then gives $\sum_{k\le m}|\langle y_k,Ax_k\rangle|\le\sum_{k\le
m}s_k(A)$ for every $m$. Since $s_k(B)$ is decreasing, summation by parts
turns these prefix bounds into the stated inequality.

**Library results.** `exists_linearIsometryEquiv_eq_comp_toLin_diagonal_comp` in
`TauCeti/Analysis/InnerProductSpace/SingularValues.lean`;
`norm_sum_inner_le_kyFanSum` in
`TauCeti/Analysis/InnerProductSpace/KyFan.lean`; Abel summation in
`Mathlib/Algebra/BigOperators/Module.lean`.

### 13.18. Eckart–Young–Mirsky theorem

**Statement.** Truncating the SVD after $k$ terms
gives a best rank-at-most-$k$ approximation in every unitarily invariant
norm. Its operator error is $s_{k+1}$, and its squared Frobenius error is
$\sum_{j>k}s_j^2$. TauCeti proves the operator-norm case; missing is the
statement for general unitarily invariant norms.

**Argument.** Let $A_k$ be the truncation, so that
$s_j(A-A_k)=s_{j+k}(A)$. If $\mathop{\mathrm{rank}}B\le k$ then $s_{k+1}(B)=0$,
and the mixed-index inequality applied to $A=(A-B)+B$ gives
$s_{j+k}(A)\le s_j(A-B)$ for every $j$. Hence every Ky Fan sum of $A-A_k$ is
at most the corresponding sum of $A-B$, and Fan dominance gives
$\|A-A_k\|\le\|A-B\|$ in every unitarily invariant norm. The two error
formulas are read off the singular values $s_{j+k}(A)$ of $A-A_k$.

**Library results.** `ContinuousLinearMap.singularValue_add_index_le` in
`TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean`;
`singularValue_eq_linearMap_singularValues` in
`TauCeti/Analysis/OperatorIdeal/ApproximationNumber/EckartYoung.lean`;
`UnitarilyInvariantSeminorm.map_le_of_kyFanSum_le` in
`TauCeti/Analysis/InnerProductSpace/FanDominance.lean`;
`exists_linearIsometryEquiv_eq_comp_toLin_diagonal_comp` in
`TauCeti/Analysis/InnerProductSpace/SingularValues.lean`.

## 14. Functional, isoperimetric, and geometric inequalities

### 14.40. Nash inequality

**Statement.** On $\mathbb R^n$,
$\|f\|_2^{2+4/n}\leq C_n\|\nabla f\|_2^2\|f\|_1^{4/n}$.
This interpolates mass, energy, and square-integrability.

**Argument.** With the library normalization,
$\|\widehat f\|_\infty\le\|f\|_1$ and
$\|\nabla f\|_2^2=4\pi^2\int|\xi|^2|\widehat f|^2$. Split Plancherel's
integral at $|\xi|=R$:
$$
\|f\|_2^2\le|B_R|\,\|f\|_1^2+(2\pi R)^{-2}\|\nabla f\|_2^2 .
$$
Choosing $R^{n+2}$ proportional to $\|\nabla f\|_2^2/\|f\|_1^2$ and raising
to the power $(n+2)/n$ gives the inequality with a non-sharp $C_n$. The
cases $f=0$ and $\nabla f=0$ are immediate. Smooth approximation extends it
from Schwartz functions to $L^1\cap H^1$.

**Library results.** `MeasureTheory.Lp.inner_fourier_eq` and
`fourierTransformₗᵢ` in `Mathlib/Analysis/Fourier/LpSpace.lean`;
`norm_fourier_le_integral_norm` in
`Mathlib/Analysis/Fourier/FourierTransform.lean`; `fourier_fderiv` in
`Mathlib/Analysis/Fourier/FourierTransformDeriv.lean`; `volume_ball` in
`Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`.

## 16. Locally convex spaces, duality, and distributions

### 16.13. Bipolar theorem for dual pairs

**Statement.** $A^{\circ\circ}$ is the
$\sigma(E,F)$-closed absolutely convex hull of $A\cup\{0\}$. In particular,
absolutely convex weakly closed sets are recovered exactly from their polars.
TauCeti proves this for a locally convex space paired with its dual; missing
is the statement for an arbitrary dual pair.

**Argument.** Give $E$ the weak topology $\sigma(E,F)$ (`WeakBilin`). It is
locally convex, and Mathlib identifies its continuous dual with $F$ through
the pairing. Under this identification the polar of $A$ in the dual and its
polar in $F$ correspond, and so do the bipolars. TauCeti's bipolar theorem for
a locally convex space and its dual then gives the statement. The second
sentence of the entry follows by `AbsConvex.bipolar_eq_closure`. The work is
transport of polars along the dual identification.

**Library results.** `StrongDual.bipolar_eq_closedAbsConvexHull` and
`AbsConvex.bipolar_eq_closure` in
`TauCeti/Analysis/LocallyConvex/Bipolar.lean`;
`WeakBilin.locallyConvexSpace` and `LinearMap.dualEmbedding_surjective` in
`Mathlib/Analysis/LocallyConvex/WeakDual.lean`; polars in
`Mathlib/Analysis/LocallyConvex/Polar.lean`.

## 20. Banach algebras

### 20.40. Wiener lemma

**Statement.** If $f\in C(\mathbb T)$ has an absolutely
convergent Fourier series and no zeros on $\mathbb T$, then $1/f$ also
has an absolutely convergent Fourier series. The extension to holomorphic
functions of $f$ near its range depends on the holomorphic calculus of
20.7 and is not part of this entry.

**Argument.** Make $\ell^1(\mathbb Z)$ a commutative unital Banach algebra
under convolution. Young's bound $\|a*b\|_1\le\|a\|_1\|b\|_1$ is a
rearrangement of absolutely summable double series. A character $\chi$ is
determined by $z=\chi(\delta_1)$. Characters have norm at most one, and
$\delta_1$ and $\delta_{-1}$ both have norm one, so $|z|=1$. Density of
finitely supported sequences then gives $\chi(a)=\sum_na_nz^n$. If the
coefficient sequence $a$ of $f$ were not a unit, Mathlib's character
theorem would give a character vanishing at $a$, that is, a zero of $f$. So
$a$ is invertible in $\ell^1$, and the Fourier series of $a^{-1}$ is $1/f$.

**Library results.** `WeakDual.CharacterSpace.exists_apply_eq_zero` in
`Mathlib/Analysis/CStarAlgebra/GelfandDuality.lean`. It is stated for
complete normed commutative complex algebras, before any C*-hypothesis.
`lp` and `lp.hasSum_single` are in `Mathlib/Analysis/Normed/Lp/lpSpace.lean`.
The convolution product on $\ell^1(\mathbb Z)$ is setup code, not a new
theorem.

## 21. Bounded operator theory, spectra, and functional models

### 21.11. Atkinson theorem

**Statement.** $T$ is Fredholm exactly when it has a bounded
inverse modulo compact operators. Mathlib characterizes Fredholm operators
by inverses modulo finite-rank operators; missing is the converse with
compact remainders. Its restatement as invertibility of the image of $T$
in the Calkin algebra $\mathcal B(H)/\mathcal K(H)$ is quotient-algebra
packaging and is not part of this entry.

**Argument.** For the forward direction, Mathlib's quasi-inverse leaves
finite-rank remainders, which are compact. Conversely, $ST=I+K_1$ and
$TS=I+K_2$ are Fredholm by TauCeti's compact-perturbation theorem. Then
$\ker T\subseteq\ker(ST)$ is finite-dimensional, and
$\mathop{\mathrm{ran}}(TS)\subseteq\mathop{\mathrm{ran}}T$ has finite
codimension. TauCeti's finite kernel and cokernel criterion makes $T$
Fredholm; it supplies the closed range itself.

**Library results.** `isFredholm_iff_exists_isQuasiInverse` in
`Mathlib/Analysis/Normed/Operator/Fredholm/Basic.lean`;
`isFredholm_one_add` in
`TauCeti/Analysis/Fredholm/CompactPerturbation.lean`;
`isFredholm_iff_finite_ker_coker` and
`ContinuousLinearMap.isClosed_range_of_finite_coker` in
`TauCeti/Analysis/Fredholm/ClosedRange.lean`.

### 21.16. Discrete spectrum of self-adjoint operators

**Statement.** For bounded
self-adjoint $T$, the complement of its essential spectrum in its spectrum
consists exactly of isolated eigenvalues of finite multiplicity. Invariance
of $\sigma_{\rm ess}$ under compact perturbations is immediate from
TauCeti's compact-perturbation theorem for Fredholm operators.

**Argument.** If $\lambda\in\sigma(T)\setminus\sigma_{\mathrm{ess}}(T)$ in the
Fredholm sense, then $T-\lambda$ is Fredholm, so $\ker(T-\lambda)$ is
finite-dimensional. For self-adjoint operators TauCeti's closed-range adjoint
theorem gives $\mathop{\mathrm{ran}}(T-\lambda)=\ker(T-\lambda)^\perp$, hence
$\lambda$ is an eigenvalue of finite multiplicity, and $T-\lambda$ is
invertible on the orthogonal complement (`orthogonalKerEquivRange`,
`ContinuousLinearEquiv.ofBijective`). Since $\ker(T-\lambda)$ reduces $T$, for
$\mu\ne\lambda$ near $\lambda$ the operator $T-\mu$ is $(\lambda-\mu)I$ on the
kernel and a small perturbation of an invertible operator on its
complement. So $\lambda$ is isolated in $\sigma(T)$. Conversely, an isolated
eigenvalue of finite multiplicity has continuous indicator on $\sigma(T)$;
Mathlib's continuous functional calculus supplies the spectral projection,
and $T-\lambda$ is Fredholm.

**Library results.** TauCeti Fredholm theory in
`TauCeti/Analysis/Fredholm/Adjoint.lean`,
`TauCeti/Analysis/Fredholm/SelfAdjoint.lean`,
`TauCeti/Analysis/Fredholm/CompactPerturbation.lean`; Mathlib continuous
functional calculus in `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/`.

## 22. Unbounded operators, spectral theory, and mathematical physics

### 22.32. Kato–Rellich theorem: cores

**Statement.** If $A$ is self-adjoint and $B$
symmetric with $A$-bound less than one, then $A+B$, which is self-adjoint
on $D(A)$, is essentially self-adjoint on every core of $A$. TauCeti
proves self-adjointness on $D(A)$; missing is the core statement.

**Argument.** Put $T=(A+B)|_D$. Since $T\subseteq A+B$ and $A+B$ is
self-adjoint, hence closed, $T$ is closable and $\overline T\subseteq A+B$.
Conversely, let $x\in D(A)$. The core property gives $x_n\in D$ with
$x_n\to x$ and $Ax_n\to Ax$. The relative bound gives
$\|B(x_n-x)\|\le a\|A(x_n-x)\|+b\|x_n-x\|\to0$, so $Tx_n\to(A+B)x$. Hence
$\overline T=A+B$, which is self-adjoint.

**Library results.** `IsSelfAdjoint.add_of_isRelativelyBounded` in
`TauCeti/Analysis/InnerProductSpace/LinearPMap/KatoRellich.lean`;
`LinearPMap.HasCore`, `LinearPMap.IsClosable` and `LinearPMap.closure` in
`Mathlib/Topology/Algebra/Module/LinearPMap.lean`; self-adjoint partial maps
are closed by `IsSelfAdjoint.isClosed` in
`Mathlib/Analysis/InnerProductSpace/LinearPMap.lean`.

## 23. Operator algebras, operator spaces, free probability, and noncommutative geometry

### 23.9. GNS cyclic vector and uniqueness

**Statement.** Every state has a cyclic
representation $(\pi_\varphi,H_\varphi,\Omega_\varphi)$ with
$\varphi(a)=\langle\pi_\varphi(a)\Omega_\varphi,\Omega_\varphi\rangle$,
unique up to a unitary preserving the cyclic vector. Mathlib constructs
the GNS space and representation of a positive functional; for a unital
algebra the class of $1$ is a cyclic vector realizing $\varphi$ by a direct
computation from the construction. Missing are the cyclic vector for
nonunital algebras (through an approximate unit) and the uniqueness
statement.

**Scope.** Only uniqueness. The cyclic vector for nonunital algebras
remains a gap.

**Argument.** If two cyclic representations realize the same
state, $U\pi(a)\Omega=\pi'(a)\Omega'$ is a well-defined isometry because
$\|\pi(a)\Omega\|^2=\varphi(a^*a)$. It intertwines the representations, and by
cyclicity it extends to a unitary $H_\varphi\to H'$ carrying $\Omega$ to
$\Omega'$. This uses only `preGNS_inner_def`.

**Library results.** `preGNS_inner_def`, `gnsStarAlgHom` in
`Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean`.

### 23.10. Gelfand–Naimark theorem

**Statement.** Every C*-algebra has a faithful
isometric representation as a norm-closed star algebra of operators.
The direct sum of its state GNS representations is faithful.

**Argument.** For $a\ge0$, $\|a\|\in\sigma(a)$
(`norm_mem_spectrum_of_nonneg`). Evaluation at that point on $C^*(1,a)$ is a
state; Hahn–Banach (`exists_extension_norm_eq`) together with
`monotone_iff_opNorm_eq_map_one` extends it to a state of $A$ with
$\varphi(a)=\|a\|$. Mathlib already has the unital GNS representation. The
Hilbert sum of these representations over all states is faithful, and
injective star homomorphisms of C*-algebras are isometric
(`NonUnitalStarAlgHom.norm_map`). Nonunital algebras reduce by Mathlib
unitization.

**Library results.** `norm_mem_spectrum_of_nonneg` in
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean`;
`monotone_iff_opNorm_eq_map_one` in
`Mathlib/Analysis/CStarAlgebra/PositiveLinearFunctional.lean`;
`exists_extension_norm_eq` (Hahn–Banach); GNS as in 23.9;
`NonUnitalStarAlgHom.norm_map` in
`Mathlib/Analysis/CStarAlgebra/Hom.lean`; unitization in Mathlib.

## 25. Integral equations and classical operator methods

### 25.3. Hilbert–Schmidt kernels

**Statement.** TauCeti has the abstract Hilbert–Schmidt
norm and proves that operators of finite Hilbert–Schmidt norm are compact;
missing is the kernel side: if $k\in L^2(D\times D)$, its integral operator is
Hilbert–Schmidt with $\|K\|_{S^2}=\|k\|_{L^2}$, and its adjoint has kernel
$\overline{k(y,x)}$.

**Argument.** Cauchy–Schwarz, Parseval and Fubini give the kernel statement. Here
$D$ is a Lebesgue domain, so $L^2(D)$ is separable.

For $k\in L^2(D\times D)$, Cauchy–Schwarz in $y$, followed by Fubini, gives
$\|Kf\|_2\le\|k\|_2\|f\|_2$ and constructs the bounded map on equivalence
classes. Let $(e_j)$ be a countable Hilbert basis of $L^2(D)$. For almost
every $x$, the section $k(x,\cdot)$ is in $L^2$. Parseval for that section
and Tonelli give
$$
\sum_j\|Ke_j\|_2^2
 =\int_D\sum_j\left|\int_D k(x,y)e_j(y)\,dy\right|^2dx
 =\iint_{D\times D}|k(x,y)|^2\,dx\,dy.
$$
In the complex case apply Parseval to the conjugate section, or to the
conjugated basis; otherwise the coefficient convention would be wrong.
TauCeti identifies the left side with Hilbert–Schmidt energy and with the
squared $S^2$ norm. Finally Fubini in $\langle Kf,g\rangle$ identifies
the adjoint kernel as $\overline{k(y,x)}$. Absolute integrability here
follows by Cauchy–Schwarz on $D\times D$, since $f(y)\overline{g(x)}$ is
in $L^2(D\times D)$.

**Library results.** `HilbertBasis.tsum_inner_mul_inner` and
`HilbertBasis.hasSum_repr` in
`Mathlib/Analysis/InnerProductSpace/l2Space.lean`;
`MeasureTheory.integral_prod` and the section-integrability lemmas in
`Mathlib/MeasureTheory/Integral/Prod.lean`;
`ContinuousLinearMap.hilbertSchmidtEnergy_def` in
`TauCeti/Analysis/InnerProductSpace/HilbertSchmidt/Basic.lean`;
`ContinuousLinearMap.tsum_singularValue_sq_eq_hilbertSchmidtEnergy` in
`TauCeti/Analysis/OperatorIdeal/ApproximationNumber/HilbertSchmidt.lean`.

### 25.18. Volterra solvability

**Statement.** For $Ku(t)=\int_0^t k(t,s)u(s)\,ds$ on $C[0,T]$, with $k$ continuous on $0\leq s\leq t\leq T$, $I-\lambda K$
is invertible for every complex $\lambda$, and successive substitution
converges uniformly. The solution depends continuously on the data on
every bounded time interval.

**Argument.** For $Ku(t)=\int_0^t k(t,s)u(s)\,ds$ on $C[0,T]$ with $k$
continuous, induction on the iterated kernels gives
$|k_n(t,s)|\le M^n(t-s)^{n-1}/(n-1)!$ and $\|K^n\|\le(MT)^n/n!$. Gelfand's
formula yields spectral radius $0$, so $I-\lambda K$ is invertible for every
$\lambda$. The Neumann series is successive substitution; continuity in the
data is continuity of inversion.

**Library results.** `ContinuousMap.intervalIntegralOperator` in
`TauCeti/Analysis/Calculus/ContinuousMap.lean`;
Gelfand formula in `Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean`.

### 25.23. Abel inversion

**Statement.** For $0<\alpha<1$, $I^\alpha u=f$ is
inverted by $u=(d/dt)I^{1-\alpha}f$ whenever
$I^{1-\alpha}f$ is absolutely continuous and vanishes at zero.
These conditions characterize the range on $L^1(0,T)$.

**Argument.** The beta integral and the fundamental theorem of calculus for
absolutely continuous functions suffice.

For $\beta>0$ define
$$
I^\beta u(t)=\Gamma(\beta)^{-1}
                \int_0^t(t-s)^{\beta-1}u(s)\,ds.
$$
The kernel has $L^1(0,T)$ norm $T^\beta/\Gamma(\beta+1)$, so this is bounded
on $L^1$. Fubini on the triangle and the substitution
$s=r+(t-r)v$ evaluate the intervening kernel integral as
$(t-r)^{\beta+\gamma-1}B(\beta,\gamma)$, proving
$I^\beta I^\gamma=I^{\beta+\gamma}$ for positive orders. Absolute
integrability follows from the same nonnegative calculation with $|u|$.

Thus $f=I^\alpha u$ implies $I^{1-\alpha}f=I^1u$, which has an
absolutely continuous representative vanishing at zero and derivative $u$.
Conversely let $g=I^{1-\alpha}f$ have such a representative and put $u=g'$.
Then $I^1u=g$ by the fundamental theorem. The map $I^\beta$, $0<\beta<1$,
is injective: apply $I^{1-\beta}$ and then differentiate $I^1$.
Consequently
$I^{1-\alpha}(I^\alpha u)=g=I^{1-\alpha}f$ implies $I^\alpha u=f$.
All identities on $L^1$ are almost-everywhere identities; the value at zero
refers to the absolutely continuous representative, not an arbitrary
representative of an $L^1$ class.

**Library results.**
`TauCeti.integral_rpow_mul_one_sub_rpow` in
`TauCeti/Analysis/SpecialFunctions/Beta.lean` and the Gamma recurrence;
`Mathlib/MeasureTheory/Integral/Prod.lean`;
`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` in
`Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`;
the a.e. derivative of an indefinite integral in
`Mathlib/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`.
The scalar real theorem extends to complex functions by real and imaginary
parts. No Volterra resolvent theorem is needed.

### 25.47. Collectively compact approximation theorem

**Statement.** Suppose $K_nx\to Kx$
for every $x$, and $\bigcup_nK_n(B_X)$ is relatively compact.
If $I-K$ is invertible, then $I-K_n$ is eventually invertible with
uniformly bounded inverses, and their solutions converge for convergent data.

**Argument.** A compactness argument by contradiction, followed by the Fredholm
alternative for compact operators.

Write $L=\overline{\bigcup_nK_n(B_X)}$, which is compact.
Each $K_n$ is compact. Strong convergence also puts $K(B_X)$ inside $L$,
so $K$ is compact, and uniform boundedness gives $\sup_n\|K_n\|<\infty$.
If $I-K_n$ were not eventually bounded below by a common $c>0$, choose
$n_j\to\infty$, $\|x_j\|=1$ and $(I-K_{n_j})x_j\to0$.
After a subsequence, $K_{n_j}x_j\to y$, hence $x_j\to y$ and $\|y\|=1$.
The uniform norm bound and strong convergence at the fixed vector $y$
give $K_{n_j}x_j\to Ky$. Thus $y=Ky$, contrary to invertibility of $I-K$.
The Fredholm alternative makes the eventually injective $I-K_n$
surjective, with inverse norm at most $1/c$. For convergent data $f_n\to f$,
letting $x=(I-K)^{-1}f$ gives
$$
(I-K_n)^{-1}f_n-x
 =(I-K_n)^{-1}\bigl(f_n-f+(K_n-K)x\bigr)\longrightarrow0.
$$

**Library results.** `banach_steinhaus` in
`Mathlib/Analysis/Normed/Operator/BanachSteinhaus.lean`;
`IsCompactOperator.hasEigenvalue_or_mem_resolventSet` in
`Mathlib/Analysis/Normed/Operator/Compact/FredholmAlternative.lean`;
sequential compactness of compact metric sets. This does not require
operator-norm convergence of $K_n$.

## 26. Sobolev spaces, smoothness scales, and interpolation

### 26.16. Failure of the critical $L^\infty$ embedding

**Statement.** TauCeti proves
$W^{1,d}_0(\Omega)\hookrightarrow L^q$ for every finite $q$ on sets of finite
measure, together with Trudinger's exponential integrability; with the
Lipschitz extension operator this gives the embedding on bounded Lipschitz
domains. Missing is the sharpness statement: for $d\geq2$, $W^{1,d}$ does not
embed into $L^\infty$ (for example $\log\log(1/|x|)$ near the origin).

**Argument.** An explicit radial example. No sharp Moser–Trudinger theorem is
needed.

For $d\ge2$, choose a smooth cutoff equal to one near zero and supported
in a ball of radius less than one. Multiply it by
$u(x)=\log\log(e/|x|)$ away from zero and assign any value at zero.
Near zero the two required radial integrals are
$$
\int_0^a r^{d-1}\bigl(\log\log(e/r)\bigr)^d\,dr<\infty,
 \qquad
 \int_0^a\frac{dr}{r\log(e/r)^d}<\infty.
$$
The second is a power integral after $t=\log(e/r)$; the first has
exponential decay after the same substitution. The gradient off zero is
$-x/(|x|^2\log(e/|x|))$ before multiplication by the cutoff.
To justify the weak derivative, replace $u(r)$ by
$u(\max(r,\varepsilon))$. These cut-off functions are Lipschitz, and the
functions and their displayed gradients converge in $L^d$ by domination.
The existing weak-derivative limit theorem gives $u\in W^{1,d}$.
Every neighborhood of zero has a positive-measure superlevel set for
every height, so $u\notin L^\infty$. Translation and dilation place the
example in any nonempty domain containing a ball, including a bounded
Lipschitz domain. The condition $d>1$ is used exactly in the second integral.

**Library results.** `integrableOn_fun_norm_addHaar` in
`Mathlib/MeasureTheory/Constructions/HaarToSphere.lean` reduces radial
integrability to one dimension;
`LocallyLipschitzOn.hasWeakFDerivOn_fderiv` in
`TauCeti/Analysis/Sobolev/WeakDeriv/Lipschitz.lean`;
`TauCeti.hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub` in
`TauCeti/Analysis/Sobolev/WeakDeriv/Limit.lean`. On the bounded support,
$L^d$ convergence implies the $L^1$ convergence required by that last
theorem. Smooth cutoffs and the logarithm chain rule are already available.

### 26.37. Fractional Hilbert identity

**Statement.** $W^{s,2}(\mathbb R^d)=H^{s,2}$
with equivalent norms; the Gagliardo energy equals a positive constant
times $\int|\xi|^{2s}|\widehat u(\xi)|^2d\xi$.

**Argument.** Plancherel, Tonelli and a linear change of variables give both the
energy identity and the identification with the Bessel-potential space.

Use Mathlib's Fourier convention $e^{-2\pi i x\cdot\xi}$. Translation
and Plancherel give, for $u\in L^2$,
$$
\|u(\cdot+h)-u\|_2^2
 =\int |e^{2\pi i h\cdot\xi}-1|^2|\widehat u(\xi)|^2\,d\xi.
$$
Integrate against $|h|^{-d-2s}dh$, $0<s<1$, and apply Tonelli, allowing
infinite energies. Rotation and dilation in the inner integral give
$$
[u]_{W^{s,2}}^2=C_{d,s}\int |\xi|^{2s}|\widehat u(\xi)|^2\,d\xi,
 \quad
 C_{d,s}=\int\frac{|e^{2\pi i h_1}-1|^2}{|h|^{d+2s}}\,dh.
$$
Here $0<C_{d,s}<\infty$: near zero bound the numerator by
$4\pi^2|h|^2$, and at infinity by $4$. The radial powers are integrable
precisely for $0<s<1$; positivity holds on an open set. At $\xi=0$ the
inner integral is zero, so there is no division-by-zero exception.
Finally $(1+|\xi|^2)^s$ is comparable to $1+|\xi|^{2s}$, which identifies
the finite-energy space with $H^{s,2}$ with equivalent norms.

**Library results.** `MeasureTheory.Lp.norm_fourier_eq` in
`Mathlib/Analysis/Fourier/LpSpace.lean`;
`VectorFourier.fourierIntegral_comp_add_right` in
`Mathlib/Analysis/Fourier/FourierTransform.lean` (extend the translation
identity to $L^2$ by the existing Schwartz density);
Tonelli in `Mathlib/MeasureTheory/Integral/Prod.lean`;
radial integration in
`Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`;
`TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier` in
`Mathlib/Analysis/Distribution/Sobolev.lean`. This proves the identity
with its convention-dependent constant, not a normalization borrowed
from a different Fourier convention.

### 26.53. Real interpolation theorem

**Statement.** For abstract Banach couples, an operator bounded
$X_i\to Y_i$ with norms $M_i$ acts boundedly between the real
interpolation spaces with bound at most $M_0^{1-\theta}M_1^\theta$.

**Argument.** The bound follows directly from the definition of the
$K$-functional. Defining the interpolation spaces themselves is
infrastructure, not part of the bound.

Let $0<\theta<1$ and $1\le q\le\infty$. For positive endpoint bounds
$M_0,M_1$, every decomposition $x=x_0+x_1$ gives
$$
K_Y(t,Tx)\le M_0 K_X(tM_1/M_0,x).
$$
Multiply by $t^{-\theta}$ and put $s=tM_1/M_0$ in the $L^q(dt/t)$ norm.
The measure $dt/t$ is unchanged, and the factor is
$M_0^{1-\theta}M_1^\theta$. For $q=\infty$ the same substitution is just
a reindexing of a supremum. If an endpoint norm vanishes, use positive
bounds $M_i+\varepsilon$ and let $\varepsilon\downarrow0$.
Compatibility ensures that the two endpoint maps give a well-defined
linear map on the algebraic sum.

**Library results.** The $K$-functional and norm definitions, infimum monotonicity, the $L^q$ scaling laws, and
one-dimensional change of variables. No missing duality, representation,
or compactness theorem is used.

### 26.54. Complex interpolation theorem

**Statement.** The same operator bound holds
between complex interpolation spaces of abstract Banach couples, by the
three-lines theorem. TauCeti has only the $L^p$ case (Riesz–Thorin).

**Argument.** The bound is composition with $T$ and multiplication by an analytic
scalar weight in the defining space of strip functions.

For an admissible $F$ with $F(\theta)=x$ and positive endpoint bounds,
$$
G(z)=M_0^{z-1}M_1^{-z}\,TF(z)
$$
is admissible for the target couple, with boundary norm at most the
boundary norm of $F$. Positive real bases make the scalar weight bounded
on the closed strip, independent of the imaginary coordinate; any required
boundary decay is preserved. Evaluation at $\theta$ and the infimum over
$F$ give the desired $M_0^{1-\theta}M_1^\theta$ bound. Zero endpoint bounds
are handled by $M_i+\varepsilon$ as in 26.53.

The three-lines theorem supplies control of evaluation in the sum space
when setting up the interpolation norm. It is already available for
Banach-valued strip functions; no $L^p$-specific duality is required.

**Library results.**
`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'`
in `Mathlib/Analysis/Complex/Hadamard.lean`, including its boundedness and
`DiffContOnCl` hypotheses; complex powers with positive bases; composition
with continuous linear maps. Construction and completeness of all abstract
interpolation spaces are separate infrastructure tasks, not hidden
conclusions of this operator-bound entry.

## 27. Fourier analysis and real-variable harmonic analysis

### 27.4. Hausdorff–Young inequality

**Statement.** For $1\leq p\leq2$ and
$p'=p/(p-1)$, $\|\widehat f\|_{p'}\leq\|f\|_p$.
In general no corresponding bounded map $L^p\to L^{p'}$ exists for
$p>2$ on Euclidean space.

**Argument.** On simple functions the Fourier transform maps $L^1$ to
$L^\infty$ with norm at most one, and $L^2$ isometrically to $L^2$.
Riesz–Thorin with $p_0=1$, $q_0=\infty$, $p_1=q_1=2$ gives the bound for
$1<p<2$ on simple functions, and density extends it. For $p>2$, put
$f_t(x)=e^{-\pi(1+it)|x|^2}$. Then $\|f_t\|_p$ does not depend on $t$, while
$$
|\widehat f_t(\xi)|=(1+t^2)^{-d/4}e^{-\pi|\xi|^2/(1+t^2)},\qquad
\|\widehat f_t\|_{p'}=c_{p,d}(1+t^2)^{d(1/(2p')-1/4)}\to\infty .
$$

**Library results.** `TauCeti.eLpNorm_le_rpow_mul_rpow_mul_eLpNorm` and its
`_of_ne_top` variant in `TauCeti/MeasureTheory/Integral/RieszThorin.lean`;
`norm_fourier_le_integral_norm` and Plancherel as in 14.40;
`fourier_gaussian_innerProductSpace` in
`Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`.

### 27.13. Heisenberg uncertainty

**Statement.** For $\|f\|_2=1$ with finite
second moments, $\|x_jf\|_2\|\xi_j\widehat f\|_2\geq1/(4\pi)$.
Translations and modulations give the centered version, with Gaussian
equality cases.

**Argument.** For Schwartz $f$, integration by parts in $x_j$ gives
$\|f\|_2^2=-\int x_j\partial_j|f|^2=-2\mathop{\mathrm{Re}}\int x_jf\,
\overline{\partial_jf}$. Cauchy–Schwarz then gives
$\|f\|_2^2\le2\|x_jf\|_2\|\partial_jf\|_2$, and by Plancherel
$\|\partial_jf\|_2=2\pi\|\xi_j\widehat f\|_2$. Cutoff and mollification pass
to finite moments. Translation and modulation centre the moments, and the
Gaussian Fourier formula gives the equality cases.

**Library results.** `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` in
`Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`;
`fourier_fderiv` and Plancherel as in 14.40;
`fourier_gaussian_innerProductSpace` as in 27.4. The weak-derivative
identification is in `TauCeti/Analysis/Sobolev/BesselPotential/Basic.lean`.

## 28. Abstract harmonic analysis on groups

### 28.2. The modular homomorphism

**Statement.** $\Delta_G$ is continuous, and
inversion carries left Haar measure to right Haar measure, with
$\int f(x^{-1})dx=\int f(x)\Delta_G(x^{-1})dx$. Mathlib defines
`modularCharacter`, the reciprocal of $\Delta_G$, as a positive
homomorphism independent of the Haar measure; missing are its continuity
and the inversion formula.

**Argument.** Mathlib's character $D=\Delta_G^{-1}$ is
$D(g)=\int f(xg)\,d\mu/\int f\,d\mu$ for a fixed nonnegative nonzero
$f\in C_c(G)$. Its numerator is $\int f(y^{-1}g)\,d(\mathop{\mathrm{inv}}_*\mu)(y)$,
which is continuous in $g$ by the parameter-integral lemma. So $D$ and
$\Delta_G$ are continuous. The measure $\mathop{\mathrm{inv}}_*\mu$ is right
invariant, and so is $D\mu$. Haar uniqueness for the opposite group gives
$\mathop{\mathrm{inv}}_*\mu=c\,D\mu$. Inverting twice and using
$D(g^{-1})D(g)=1$ gives $c^2=1$, so $c=1$. Since $D(x)=\Delta_G(x^{-1})$,
this is the stated formula.

**Library results.** `modularCharacter`, `modularCharacterFun_eq_haarScalarFactor`
and `map_right_mul_eq_modularCharacterFun_smul` in
`Mathlib/MeasureTheory/Group/ModularCharacter.lean`;
`continuous_integral_apply_inv_mul`, `haarScalarFactor_eq_integral_div` and
`measure_isMulInvariant_eq_smul_of_isCompact_closure` in
`Mathlib/MeasureTheory/Measure/Haar/Unique.lean`.

## 29. Wavelets, frames, time–frequency analysis, and sampling

### 29.2. Frame operator criterion

**Statement.** A Bessel sequence is a frame exactly
when $S=C^*C$ is boundedly invertible; equivalently
$AI\leq S\leq BI$. It is also equivalent to synthesis being onto $H$.

**Argument.** The Bessel bound makes $C:H\to\ell^2$ bounded. Its adjoint is
$C^*c=\sum_kc_kf_k$, by continuity of $C^*$ and the coordinate expansion of
$c$. Since $\langle Sf,f\rangle=\|Cf\|^2$, the frame inequalities are
exactly $AI\le S\le BI$. The lower bound makes the self-adjoint $S$
injective with closed range, and its range is dense because
$\ker S^*=\ker S=0$; hence $S$ is invertible. Conversely, if $S$ is
invertible then $S\ge\|S^{-1}\|^{-1}I$ by the continuous functional
calculus. If $C^*$ is onto, the open mapping theorem gives $\delta>0$ with
$\delta B_H\subseteq C^*(B_{\ell^2})$, so
$\|Cf\|=\sup_{\|c\|\le1}|\langle C^*c,f\rangle|\ge\delta\|f\|$. If $S$ is
onto, so is $C^*$.

**Library results.** `lp.hasSum_single` in
`Mathlib/Analysis/Normed/Lp/lpSpace.lean`; adjoints and the continuous
functional calculus for bounded operators on Hilbert spaces;
`IsCoercive` and `range_eq_top` in
`Mathlib/Analysis/InnerProductSpace/LaxMilgram.lean` for real scalars; the
open mapping theorem in `Mathlib/Analysis/Normed/Operator/Banach.lean`.

### 29.3. Canonical dual reconstruction

**Statement.** The sequence
$\widetilde f_k=S^{-1}f_k$ is a frame, and
$f=\sum_k\langle f,\widetilde f_k\rangle f_k
=\sum_k\langle f,f_k\rangle\widetilde f_k$ unconditionally in $H$.
Its optimal bounds are the reciprocals of the original optimal bounds,
in reverse order.

**Argument.** Since $S^{-1}$ is self-adjoint, $f=SS^{-1}f=C^*CS^{-1}f$ gives
the first expansion, and $f=S^{-1}C^*Cf$ the second. Sums indexed by
arbitrary types in Mathlib are unconditional, and $C^*$ and $S^{-1}$
preserve them. The frame operator of $(\widetilde f_k)$ is
$S^{-1}SS^{-1}=S^{-1}$. The optimal bounds of a frame are the extreme points
of the spectrum of its frame operator, and $t\mapsto1/t$ reverses and
inverts them.

**Library results.** As for 29.2.

### 29.58. Shannon sampling theorem

**Statement.** For $f\in PW_B$,
$$
f(t)=\sum_{k\in\mathbb Z}f(k/(2B))\mathop{\mathrm{sinc}}(2Bt-k),
\qquad \|f\|_2^2=(2B)^{-1}\sum_k|f(k/(2B))|^2.
$$
The series converges in $L^2$ and uniformly on the real axis.

**Argument.** The Fourier-series Hilbert basis on the frequency interval,
transported by Plancherel. Assume $B>0$ and use the continuous
representative of the bandlimited $L^2$ function.

With Mathlib's frequency convention, $\widehat f$ is supported in $[-B,B]$.
An orthonormal basis of that interval is
$e_k(\xi)=(2B)^{-1/2}e^{-2\pi i k\xi/(2B)}$.
Its coefficients are $(2B)^{-1/2}f(k/(2B))$; inverse transforming a basis
vector gives $(2B)^{1/2}\mathop{\mathrm{sinc}}(2Bt-k)$, where the sinc in the statement
is normalized as $\sin(\pi t)/(\pi t)$. This is
`Real.sinc (Real.pi * t)` in Mathlib. Hilbert expansion and Parseval give
the sampling series and its exact norm identity.

For every Fourier-side remainder $r$, Cauchy–Schwarz on the fixed interval
gives $\|\mathcal F^{-1}r\|_\infty\le\sqrt{2B}\|r\|_2$. Thus the same
partial sums converge uniformly on the entire real line, as well as in
$L^2$. The inverse integral exists because an $L^2$ function supported
on that finite interval is in $L^1$. No general Paley–Wiener entire-function
characterization, nor Kadec or Landau theorem, is needed.

**Library results.** `fourierBasis`,
`hasSum_fourier_series_L2` and `hasSum_sq_fourierCoeffOn` in
`Mathlib/Analysis/Fourier/AddCircle.lean`;
`MeasureTheory.Lp.fourierTransformₗᵢ` in
`Mathlib/Analysis/Fourier/LpSpace.lean`;
`Mathlib/Analysis/Fourier/Inversion.lean`;
`Mathlib/Analysis/SpecialFunctions/Trigonometric/Sinc.lean`.
Passing between the circle and one interval is the existing `liftIoc`
machinery, not a new completeness theorem for exponentials.

## 31. Ordinary differential equations and dynamical systems

### 31.24. Lyapunov's direct theorem

**Statement.** A positive definite $C^1$ function
$V$ with $\dot V=\nabla V\cdot F\leq0$ near an equilibrium proves
stability. Strict negative definiteness of $\dot V$ proves asymptotic
stability. Proper global versions give global conclusions when solutions exist.

**Argument.** Local existence is Picard–Lindelöf, and the chain rule along
an integral curve gives $\frac{d}{dt}V(x(t))=\dot V(x(t))$. On the sphere
$|x|=\varepsilon$, compactness and $V>0$ give a positive minimum $m$. By
continuity of $V$ at the equilibrium, the sublevel set $\{V<m\}$ contains a
neighbourhood of it, and $\dot V\le0$ keeps trajectories starting there
inside the ball. They stay in a compact set and so exist for all forward
time. This is stability. If $\dot V<0$ away from the equilibrium, $V$
decreases along such a trajectory to a limit $c\ge0$. If $c>0$, the
trajectory stays in a compact annulus where $\dot V\le-\eta<0$, so $V$
would become negative in finite time. Hence $c=0$ and the trajectory
tends to the equilibrium. The proper global versions are the same argument
on compact sublevel sets. TauCeti's `TauCeti/Dynamics/Flow/Lyapunov.lean`
proves a different theorem: convergence on a compact space with a finite
rest set.

**Library results.** Picard–Lindelöf in `Mathlib/Analysis/ODE/PicardLindelof.lean`;
maximal integral curves in TauCeti; `HasFDerivAt.comp_hasDerivAt` in
`Mathlib/Analysis/Calculus/FDeriv/Comp.lean`.

### 31.26. LaSalle invariance principle

**Statement.** On a compact positively invariant
set where $\dot V\leq0$, every trajectory approaches the largest
invariant subset of $\{\dot V=0\}$. TauCeti proves the case of a
global flow on a compact space in which the points with $V$ constant
along their orbit form a finite set (each orbit then converges to one
of them); missing is the general statement, with an infinite invariant
set and a positively invariant compact subset of phase space.

**Argument.** For a trajectory in the compact set $K$, the omega-limit set
$\omega$ is nonempty, compact and invariant, and the trajectory eventually
enters each of its neighbourhoods. Since $V$ is monotone and bounded along
the trajectory, it converges to some $c$. By continuity $V=c$ on $\omega$.
Invariance makes $V$ constant along every orbit in $\omega$, so
$\dot V=0$ there. So $\omega$ is an invariant subset of $\{\dot V=0\}$,
hence of the largest one. TauCeti's Lyapunov convergence proof runs exactly
this argument before it uses finiteness of the rest set.

**Library results.** `nonempty_omegaLimit_of_isCompact_absorbing`,
`isInvariant_omegaLimit` and
`eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset`
in `Mathlib/Dynamics/OmegaLimit.lean`; the proof of
`Flow.exists_tendsto_atTop_of_antitone` in
`TauCeti/Dynamics/Flow/Lyapunov.lean`.

## 36. Calculus of variations, Γ-convergence, and homogenization

### 36.1. Euler–Lagrange equation

**Statement.** A sufficiently regular local minimizer
with admissible compactly supported variations satisfies
$f_u-\mathop{\mathrm{div}}f_{Du}=0$. For Sobolev minimizers this
holds weakly when derivative growth bounds justify differentiation
under the integral.

**Argument.** For compactly supported smooth $\varphi$, the growth bounds
dominate the difference quotients of $t\mapsto F(u+t\varphi)$. Hence this
function is differentiable at $0$ with derivative
$\int(f_u\varphi+f_{Du}\cdot\nabla\varphi)$. A local minimum forces this to
vanish, which is the weak equation. In the regular case, integrate by parts
against compactly supported $\varphi$. The fundamental lemma then gives
$f_u-\mathop{\mathrm{div}}f_{Du}=0$ almost everywhere, and continuity gives it
everywhere.

**Library results.** `hasFDerivAt_integral_of_dominated_of_fderiv_le` in
`Mathlib/Analysis/Calculus/ParametricIntegral.lean`;
`IsLocalMin.hasDerivAt_eq_zero` in
`Mathlib/Analysis/Calculus/LocalExtr/Basic.lean`;
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` as in 27.13;
`ae_eq_zero_of_integral_contDiff_smul_eq_zero` in
`Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`.

## 39. Metric measure spaces, Dirichlet forms, heat kernels, optimal transport, and fractals

### 39.73. Self-similar attractors

**Statement.** A finite family of strict contractions
of a complete metric space has a unique nonempty compact invariant set,
the fixed point of the union map on compact sets with the Hausdorff
metric. Positive weights summing to one similarly determine a unique
invariant probability measure.

**Argument.** On the complete space of nonempty compact sets with the Hausdorff
metric, $K\mapsto\bigcup_iS_i(K)$ is a contraction with the largest ratio.
Banach's theorem gives the attractor $K$. For measures, work in the
Wasserstein space $W_1$ over $K$, which is complete. There
$\mu\mapsto\sum_ip_i(S_i)_*\mu$ contracts by the pushforward Lipschitz bound
and the convexity of $W_1$ under mixtures, and Banach's theorem gives the
measure. For uniqueness among all invariant probabilities, note that
$d(S_ix,K)\le c\,d(x,K)$. Invariance then bounds the mass of
$\{d(\cdot,K)>\varepsilon\}$ by the mass of
$\{d(\cdot,K)>c^{-n}\varepsilon\}$ for every $n$, so it is zero. Every
invariant probability is therefore supported on $K$, where the fixed point is
unique.

**Library results.** `NonemptyCompacts` and its `CompleteSpace` instance in
`Mathlib/Topology/UniformSpace/Closeds.lean`; `ContractingWith` in
`Mathlib/Topology/MetricSpace/Contracting.lean`; `WassersteinComponent`
completeness in
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Complete.lean`;
`lipschitzWith_map` in
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Pushforward.lean`;
`wassersteinEDist_finset_sum_smul_rpow_le` in
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Mixture/Basic.lean`.

## 40. One complex variable — general theory

### 40.25. Laurent expansion

**Statement.** A holomorphic function on
$r<|z-a|<R$ has a unique Laurent series, normally convergent
on compact subannuli, with coefficients given by contour integrals
over any intervening circle.

**Argument.** Annulus Cauchy–Goursat is already in
`Mathlib/Analysis/Complex/CauchyIntegral.lean`. For $r<|w-a|<R$, Goursat
applied to the difference quotient $(f(z)-f(w))/(z-w)$ equates the two circle
integrals. The outer integral of $(z-w)^{-1}$ is $2\pi i$
(`circleIntegral.integral_sub_inv_of_mem_ball`); the inner integral vanishes
because $w$ lies outside that circle. This is the two-circle Cauchy formula.
The outer piece is the existing `cauchyPowerSeries`; the inner piece is the
geometric series for $1/(z-w)$ when $|z-a|<|w-a|$. Uniqueness of coefficients
is `circleIntegral.integral_sub_zpow_of_ne`.

**Library results.** `Mathlib/Analysis/Complex/CauchyIntegral.lean`;
`circleIntegral.integral_sub_inv_of_mem_ball`,
`circleIntegral.integral_sub_zpow_of_ne` in
`Mathlib/MeasureTheory/Integral/CircleIntegral.lean`; `cauchyPowerSeries`.

## 42. Hardy, Bergman, and model spaces; operators on analytic function spaces

### 42.51. Bergman kernel

**Statement.** $A_\alpha^2$ has kernel
$K_\alpha(z,w)=(1-z\bar w)^{-\alpha-2}$.
For $\alpha=0$, the normalized monomials are $\sqrt{n+1}z^n$.

**Argument.** Taylor expansion, Parseval on circles and the beta integral. The
calculation is specific to the disk with the stated radial weights.

Use the normalization of the statement,
$dA_\alpha=(\alpha+1)(1-|z|^2)^\alpha dx\,dy/\pi$, $\alpha>-1$.
Angular orthogonality and the substitution $t=r^2$ give
$$
\langle z^n,z^m\rangle=0\quad(n\ne m),\qquad
 c_n:=\|z^n\|_\alpha^2
 =\frac{\Gamma(\alpha+2)n!}{\Gamma(n+\alpha+2)}.
$$
If $f(z)=\sum a_nz^n$, Parseval on each circle of radius $r<1$ and
Tonelli in $r$ give
$\|f\|_\alpha^2=\sum_n c_n|a_n|^2$, allowing infinite values.
Conversely every sequence with this finite weighted square sum defines a
holomorphic function: Cauchy–Schwarz gives normal convergence on compact
subdisks because $\sum r^{2n}/c_n=(1-r^2)^{-\alpha-2}$.
This also proves completeness of the analytic subspace and the completeness
of the monomial system; those properties are not simply assumed.

The same Taylor formula for $(1-t)^{-\alpha-2}$ gives
$$
K_\alpha(z,w)=\sum_{n\ge0}\frac{z^n\overline w^{\,n}}{c_n}
             =(1-z\overline w)^{-\alpha-2}.
$$
Cauchy–Schwarz now proves bounded evaluation and the reproducing identity.
For $\alpha=0$, $c_n=1/(n+1)$, giving exactly $\sqrt{n+1}z^n$.
The Taylor coefficients of the complex power follow by differentiating
$(1-t)^{-\alpha-2}$ and using the Gamma recurrence; a missing named
binomial-series theorem is not needed.

**Library results.** `Complex.hasSum_taylorSeries_on_ball` in
`Mathlib/Analysis/Complex/TaylorSeries.lean`;
`hasSum_sq_fourierCoeff` in `Mathlib/Analysis/Fourier/AddCircle.lean`;
`Complex.integral_comp_polarCoord_symm` and
`Complex.lintegral_comp_polarCoord_symm` in
`Mathlib/Analysis/SpecialFunctions/PolarCoord.lean`;
`TauCeti.integral_rpow_mul_one_sub_rpow` in
`TauCeti/Analysis/SpecialFunctions/Beta.lean`;
the complex-power derivative in
`Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean`;
Tonelli and the Hilbert-space square-summable sequence model.

### 42.52. Bergman projection

**Statement.** $P_\alpha f(z)=\int K_\alpha(z,w)f(w)dA_\alpha(w)$
is the orthogonal projection on $L^2(dA_\alpha)$ and extends
boundedly from $L^p(dA_\alpha)$ onto $A_\alpha^p$ for $1<p<\infty$.

**Scope.** Only the $L^2$ projection clause. The bounds on $L^p$ for
$1<p<\infty$ need a separate weighted kernel estimate and remain a gap.

**Argument.** The orthogonal projection and its integral kernel follow from the
coefficient description in 42.51.

The preceding coefficient description makes $A_\alpha^2$ a closed subspace
of $L^2(dA_\alpha)$. Projecting onto its orthonormal monomials gives
$$
P_\alpha f(z)=\sum_n\frac{z^n}{c_n}
                   \int f(w)\overline w^{\,n}\,dA_\alpha(w)
              =\int K_\alpha(z,w)f(w)\,dA_\alpha(w).
$$
For fixed $z$, the kernel series converges in $L^2$ as a function of $w$,
so pairing with $f\in L^2$ justifies the interchange. This gives
$P_\alpha^2=P_\alpha=P_\alpha^*$ and norm one.

**Library results.** The derivation of 42.51;
`Submodule.orthogonalProjectionOnto` and `HilbertBasis.hasSum_repr` in
Mathlib's inner-product-space theory. No all-$p$ estimate is inferred from
the Hilbert projection theorem.

## 45. Several complex variables, complex manifolds, pluripotential theory, and CR analysis

### 45.2. Polydisk Taylor expansion and estimates

**Statement.** A function
holomorphic near a closed polydisk has a multivariable Taylor series
converging normally on the whole open polydisk, with Cauchy estimates
$|\partial^\alpha f(c)|\leq\alpha!\,R^{-\alpha}\sup_{T(c,R)}|f|$;
locally uniform limits of holomorphic functions of several variables
are holomorphic. TauCeti proves the polydisc Cauchy formula and local
analyticity of complex-differentiable functions on $\mathbb C^n$;
missing are convergence on the full polydisk, the estimates, and the
several-variable Weierstrass convergence theorem.

**Argument.** TauCeti already has the polydisc Cauchy formula for unequal
polyradii (`DifferentiableOn.torusIntegral_prod_sub_inv_smul`) and the
identification of holomorphy with analyticity on finite-dimensional spaces.
Expand $\prod_i(\zeta_i-w_i)^{-1}$ as a product of geometric series on the
whole open polydisk (`hasSum_geometric_of_norm_lt_one`) and integrate termwise
on the compact torus: that is the Taylor series with the Cauchy estimates.
Locally uniform limits: pass to the limit in the torus integral and reuse the
existing “Cauchy kernel $\Rightarrow$ analytic” argument.

**Library results.** `TauCeti/Analysis/Complex/CauchyIntegralPolydisc.lean`
(`DifferentiableOn.torusIntegral_prod_sub_inv_smul`);
`hasSum_geometric_of_norm_lt_one` in
`Mathlib/Analysis/SpecificLimits/Basic.lean`.

## 46. Complex dynamics

### 46.10. Koenigs linearization

**Statement.** A germ $f(z)=\lambda z+O(z^2)$
with $0<|\lambda|\ne1$ is locally conjugate to $z\mapsto\lambda z$.
The conjugating germ normalized to have derivative one is unique.

**Argument.** A geometrically convergent sequence of rescaled iterates and the
inverse function theorem. No classification of Fatou components is
involved.

First suppose $0<|\lambda|<1$. Choose
$|\lambda|<q<\sqrt{|\lambda|}$ and a sufficiently small disk where
$|f(z)|\le q|z|$ and $|f(z)-\lambda z|\le C|z|^2$.
For $\phi_n(z)=\lambda^{-n}f^{\circ n}(z)$,
$$
|\phi_{n+1}(z)-\phi_n(z)|
 \le\frac{C}{|\lambda|}
            \left(\frac{q^2}{|\lambda|}\right)^n|z|^2.
$$
This proves uniform convergence on a smaller disk to a holomorphic
$\phi=z+O(z^2)$, with $\phi\circ f=\lambda\phi$.
Its derivative one makes it a local coordinate. If $|\lambda|>1$, take the
local holomorphic inverse of $f$ and apply the attracting case to it.
For uniqueness, compare two normalized coordinates; their transition germ
$h=z+\sum_{m\ge2}b_mz^m$ commutes with multiplication by $\lambda$.
Thus $(\lambda^m-\lambda)b_m=0$, forcing every $b_m=0$ because
$|\lambda|\ne1$ and $\lambda\ne0$.

**Library results.**
`TendstoLocallyUniformlyOn.differentiableOn` and
`Complex.differentiableOn_tsum_of_summable_norm` in
`Mathlib/Analysis/Complex/LocallyUniformLimit.lean`;
`HasStrictDerivAt.localInverse` and `HasStrictDerivAt.to_localInverse` in
`Mathlib/Analysis/Calculus/InverseFunctionTheorem/Deriv.lean`;
Taylor expansion and geometric summability. Holomorphic maps supply the
strict derivative needed by the inverse theorem.

### 46.11. Böttcher's theorem

**Statement.** A superattracting germ
$f(z)=az^k+O(z^{k+1})$, $k\geq2$, is locally conjugate to
$z\mapsto z^k$. The coordinate is unique up to a $(k-1)$st root of unity.

**Argument.** A normally convergent series for a holomorphic logarithm.

Choose $c$ with $c^{k-1}=a$ and conjugate by $z\mapsto cz$ to reduce to
$f(z)=z^kg(z)$, $g(0)=1$. On a sufficiently small disk, $f$ maps the disk
into itself, $g$ has values near one, and $h=\log g$ is holomorphic and
bounded. Put
$$
S(z)=\sum_{j\ge0}k^{-j-1}h(f^{\circ j}(z)),\qquad
 \phi(z)=z\exp S(z).
$$
The geometric bound $k^{-j-1}\sup|h|$ gives normal convergence.
Reindexing gives $S(f(z))=kS(z)-h(z)$, hence
$\phi(f(z))=\phi(z)^k$. Also $S(0)=0$ and $\phi'(0)=1$, so $\phi$ is a
local holomorphic coordinate. For uniqueness with derivative one, a first
nonzero term $bz^m$, $m\ge2$, in the transition germ would give different
lowest terms in $h(z^k)$ and $h(z)^k$: degrees $km$ and $k+m-1$.
Thus no such term exists. Removing the derivative normalization leaves
exactly multiplication by a $(k-1)$st root of unity. The leading coefficient
$a$ must be nonzero, as is implicit in saying that the germ has order $k$.

**Library results.** `Complex.differentiableAt_log` in
`Mathlib/Analysis/SpecialFunctions/Complex/LogDeriv.lean` on the slit plane,
applied only near one;
`Complex.differentiableOn_tsum_of_summable_norm` in
`Mathlib/Analysis/Complex/LocallyUniformLimit.lean`;
the inverse function theorem as in 46.10; Taylor coefficient uniqueness;
existence of complex roots. TauCeti's local normal form
$f-f(z_0)=\varphi^m$ is not a conjugacy and is not used.

## 47. Approximation theory

### 47.17. Korovkin theorem

**Statement.** Positive linear maps
$L_n:C[0,1]\to C[0,1]$ converge strongly to the identity
exactly when they converge uniformly on $1,x,x^2$.

**Argument.** One pointwise quadratic bound and positivity.

For real continuous $f$, uniform continuity gives $\delta>0$ such that
$|f(y)-f(x)|<\varepsilon$ if $|x-y|<\delta$. With $M=\|f\|_\infty$,
$$
|f(y)-f(x)|\le\varepsilon+2M\delta^{-2}(y-x)^2
 \quad(0\le x,y\le1).
$$
Apply the positive functional $g\mapsto L_ng(x)$ for each fixed $x$ and
account for $L_n1\ne1$:
$$
|L_nf(x)-f(x)|
 \le\varepsilon L_n1(x)
 +2M\delta^{-2}\{L_n(t^2)(x)-2xL_n(t)(x)+x^2L_n1(x)\}
 +M|L_n1(x)-1|.
$$
The expression in braces tends uniformly to zero by the three hypotheses,
and $\|L_n1\|_\infty$ is bounded. Taking suprema, then
$n\to\infty$ and $\varepsilon\downarrow0$, proves convergence for every
$f$. The converse is immediate. Complex functions reduce to their real
and imaginary parts for the usual complex-linear positive maps.

**Library results.** Compact uniform continuity and the supremum norm
on `ContinuousMap`; positivity and linearity; finite sums and limits.
The nearby proof `bernsteinApproximation_uniform` in
`Mathlib/Analysis/SpecialFunctions/Bernstein.lean` explicitly carries out
the same near/far quadratic domination argument for Bernstein weights.
No general approximation theorem beyond this argument is required.

## 48. Orthogonal polynomials, moment problems, and spectral recurrences

### 48.6. Real and simple zeros

**Statement.** The $n$ zeros of $p_n$ are
simple and lie in the interior of the convex hull of $\mathop{\mathrm{supp}}\mu$.
Mathlib proves this for the Chebyshev weight $(1-x^2)^{-1/2}$
(`Polynomial.Chebyshev.roots_T_real`, `rootMultiplicity_T_real`); missing is
the statement for a general $\mu$.

**Argument.** A sign-change argument using polynomial factorization and
orthogonality. Take the section's positive measure of infinite support
with all required moments finite, and a nonzero degree-$n$ polynomial
$p_n$ orthogonal to all lower degrees.

Let $q$ be the product of $x-r$ over the distinct roots $r$ where $p_n$
changes sign in the interior of the convex hull of the support. If there
are fewer than $n$ such roots, then $\deg q<n$. The polynomial $p_nq$ has
a constant sign throughout that interval and on its endpoints, and is
not zero almost everywhere: a nonzero polynomial has finitely many roots,
whereas the measure has infinite support. Its integral is therefore
nonzero, contradicting $\int p_nq\,d\mu=0$. Consequently there are $n$
distinct interior sign-changing roots. Degree $n$ forces them all to be
simple and leaves no other roots. The argument works for unbounded
support; compactness of the support is not assumed.

**Library results.** Polynomial roots, multiplicities and degree
bounds; `Polynomial.signRight_mul` and the parity information in
`Mathlib/Analysis/Polynomial/SignRight.lean`;
`MeasureTheory.integral_eq_zero_iff_of_nonneg_ae` in
`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`;
`MeasureTheory.Measure.support_mem_ae` in
`Mathlib/MeasureTheory/Measure/Support.lean`.
The orthogonality assumption supplies the vanishing integral; no missing
Jacobi-operator spectral theorem is used.

### 48.14. Gauss quadrature

**Statement.** The zeros $x_1,\ldots,x_n$ of $p_n$
support a unique quadrature rule exact on $\mathcal P_{2n-1}$.
Its weights are positive and equal $1/K_{n-1}(x_j,x_j)$.
Mathlib proves the Chebyshev–Gauss case, with equal weights $\pi/n$
(`Polynomial.Chebyshev.integral_eq_sumZeroes`); missing are a general $\mu$,
uniqueness of the rule, and the Christoffel-number formula for the weights.

**Argument.** Given the zero argument of 48.6, polynomial division and Lagrange
interpolation give every clause.

For the $n$ zeros $x_j$ of $p_n$, let $\ell_j$ be the degree-$n-1$
Lagrange polynomials and set $w_j=\int\ell_j\,d\mu$.
Divide any $r$ of degree at most $2n-1$ as $r=p_nq+s$, with
$\deg q,\deg s<n$. Orthogonality kills the first term, and interpolation
of $s$ proves $\int r\,d\mu=\sum_jw_jr(x_j)$. Applying exactness to
$\ell_j^2$ gives $w_j=\int\ell_j^2\,d\mu>0$.
Applying any other exact rule at these nodes to $\ell_j$ proves uniqueness
of the weights.

For an orthonormal family $p_0,\ldots,p_{n-1}$ put
$K_{n-1}(x,y)=\sum_{r<n}p_r(x)\overline{p_r(y)}$.
Exactness applied to a product of $\ell_j$ with any polynomial of degree
less than $n$ gives
$\int s\ell_j\,d\mu=w_js(x_j)$ in the real convention. Thus
$\ell_j=w_jK_{n-1}(\cdot,x_j)$ by expansion in that finite orthonormal
basis. Evaluating at $x_j$ gives $w_j=1/K_{n-1}(x_j,x_j)$.
For nonnormalized orthogonal polynomials insert their squared norms in
the definition of $K$. If uniqueness allows the nodes to vary as well,
an $n$-node exact rule satisfies $\int p_nq=0$ for every $\deg q<n$;
Lagrange tests and positivity force $p_n$ to vanish at each node.

**Library results.** The preceding 48.6 derivation;
`Polynomial.Lagrange.basis`, `eval_basis_self`, `eval_basis_of_ne` and
`eq_interpolate` in `Mathlib/LinearAlgebra/Lagrange.lean`;
polynomial Euclidean division; finite-dimensional orthogonal expansion
and positive-integral criteria. Neither Christoffel–Darboux nor Favard's
theorem is a prerequisite.

### 48.34. Hausdorff theorem

**Statement.** It is a moment sequence on $[0,1]$
exactly when $(-1)^k\Delta^ks_n\geq0$ for all $n,k\geq0$.
Uniqueness of the representing measure follows from TauCeti's compact
moment determinacy; missing is the existence of a representing
measure for a completely monotone sequence.

**Argument.** Compactness of measures and finite Bernstein identities give the
existence direction. Extending the sequence to a continuous completely
monotone function is unnecessary.

Let $s$ be completely monotone in the difference sense. For $N\ge1$ put
$$
w_{N,k}=\binom Nk(-1)^{N-k}\Delta^{N-k}s_k\ge0,\qquad
 \mu_N=\sum_{k=0}^Nw_{N,k}\delta_{k/N}.
$$
Finite binomial expansion gives $\sum_kw_{N,k}=s_0$ and, for $j\le N$,
$$
\sum_k(k)_j w_{N,k}=(N)_j s_j,
$$
where $(k)_j=k(k-1)\cdots(k-j+1)$. One way to see the identity is to
define $L(x^j)=s_j$ on polynomials and apply $L$ to
$\sum_k(k)_j\binom Nk x^k(1-x)^{N-k}=(N)_jx^j$;
the latter follows by differentiating $(x+y)^N$ $j$ times in $x$ and
then setting $y=1-x$. These are finite polynomial identities.
Since $(k)_j/N^j-(k/N)^j=O_j(1/N)$ uniformly for $0\le k\le N$,
the ordinary $j$th moments of $\mu_N$ tend to $s_j$.

If $s_0>0$, normalize $\mu_N$ to probabilities on the compact interval.
Mathlib's compactness of probability measures gives a weakly convergent
subsequence, and the bounded continuous monomials pass to the limit.
Rescaling gives the required measure. If $s_0=0$, monotonicity and
nonnegativity force every $s_j=0$, represented by the zero measure.
Necessity is $(-1)^k\Delta^ks_n=\int x^n(1-x)^k\,d\mu\ge0$.
Uniqueness is TauCeti's compact moment determinacy.

**Library results.** The `CompactSpace (ProbabilityMeasure E)`
instance and `isCompact_setOfPred_finiteMeasure_eq_of_compactSpace` in
`Mathlib/MeasureTheory/Measure/Prokhorov.lean`; weak convergence tested by
bounded continuous functions in
`Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`;
Bernstein polynomials in `Mathlib/RingTheory/Polynomial/Bernstein.lean`
and polynomial differentiation. For uniqueness, the existing
`Measure.ext_of_forall_integral_monomial_eq` in
`TauCeti/Probability/Moments/CompactDeterminacy.lean` applies after the
one-coordinate identification. This does not prove the unbounded-support
Hamburger or Stieltjes existence theorems.

## 49. Special functions, integral transforms, and classical formulae

### 49.6. Gamma multiplication beyond duplication

**Statement.** For integers
$m\geq3$, prove
$\prod_{j=0}^{m-1}\Gamma(z+j/m)
=(2\pi)^{(m-1)/2}m^{1/2-mz}\Gamma(mz)$
away from poles, with the corresponding meromorphic identity.
The case $m=1$ is immediate and $m=2$ is Mathlib's duplication formula;
neither is part of the selected gap.

**Argument.** This is Mathlib's own duplication argument
(`doublingGamma_eq_Gamma`, Bohr–Mollerup) with a different constant. The
function
$$
f(x)=(2\pi)^{(1-m)/2}m^{x-1/2}\prod_{k=0}^{m-1}\Gamma\bigl((x+k)/m\bigr)
$$
is positive and log-convex on $(0,\infty)$ and satisfies $f(x+1)=xf(x)$. The
constant $f(1)=1$ is Euler reflection (`Gamma_mul_Gamma_one_sub`) together
with $\prod_{k=1}^{m-1}\sin(\pi k/m)=m/2^{m-1}$, from $X^m-1=\prod(X-\zeta)$
(`X_pow_sub_one_eq_prod`) evaluated at $1$ and
$|1-e^{2\pi ik/m}|=2\sin(\pi k/m)$. Meromorphic continuation is the same
$1/\Gamma$ argument already used for duplication. Stirling's formula is not
needed for the constant.

**Library results.** Bohr–Mollerup and duplication in
`Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean`;
`Gamma_mul_Gamma_one_sub` in
`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`;
`X_pow_sub_one_eq_prod` in
`Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean`.

### 49.13. Gauss equation

**Statement.** $F(a,b;c;z)$ is the solution normalized
by $F(0)=1$ of
$z(1-z)y''+[c-(a+b+1)z]y'-aby=0$.
Its singular points are regular singular at $0,1,\infty$.

**Argument.** Mathlib already defines ${}_2F_1$ as the scalar series with
radius $1$ and $F(0)=1$ (`ordinaryHypergeometric_zero`,
`ordinaryHypergeometricSeries_radius_eq_one`). Termwise differentiation is
`HasFPowerSeriesAt.deriv` / `hasDerivAt_tsum`. Substituting into
$z(1-z)y''+[c-(a+b+1)z]y'-aby$ is Pochhammer coefficient arithmetic
(`ascPochhammer_succ_eval`). Regular singular points at $0,1,\infty$ are the
indicial data of that ODE.

**Library results.** `Mathlib/Analysis/SpecialFunctions/OrdinaryHypergeometric.lean`
(`ordinaryHypergeometric_zero`, `ordinaryHypergeometricSeries_radius_eq_one`);
`HasFPowerSeriesAt.deriv`; `ascPochhammer_succ_eval`.

### 49.30. Bessel generating function

**Statement.** $e^{(z/2)(t-t^{-1})}=\sum_{n\in\mathbb Z}J_n(z)t^n$,
with normal convergence on compact subsets of $0<|t|<\infty$.

**Argument.** An absolutely convergent product of two exponential series.

For $t\ne0$, expand
$$
e^{zt/2}e^{-z/(2t)}
 =\sum_{r,s\ge0}\frac{(-1)^s(z/2)^{r+s}t^{r-s}}{r!s!}.
$$
For $n\ge0$, grouping the terms with $r-s=n$ gives
$$
\sum_{s\ge0}\frac{(-1)^s(z/2)^{n+2s}}{s!(n+s)!}=J_n(z),
$$
directly from Mathlib's regularized hypergeometric definition and
$\Gamma(n+s+1)=(n+s)!$. Negative diagonals give
$J_{-n}(z)=(-1)^nJ_n(z)$, already proved in Mathlib.
On $|z|\le R$ and $0<a\le|t|\le b$, the absolute double series is bounded
termwise by the product of the exponential series for $Rb/2$ and
$R/(2a)$. Thus regrouping is legitimate and gives normal convergence
on compact subannuli, including uniformity for $z$ in compact sets.

**Library results.** `Complex.besselJ_def`, `Complex.besselJ_neg_int`
in `Mathlib/Analysis/SpecialFunctions/Bessel.lean`;
`Complex.regularizedHGFunCoeff` and the zero-upper-parameter series in
`Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.lean`;
`NormedSpace.expSeries_div_hasSum_exp` in
`Mathlib/Analysis/Normed/Algebra/Exponential.lean`;
absolute-series product and regrouping in
`Mathlib/Topology/Algebra/InfiniteSum/Ring.lean` and the corresponding
normed-group sum theory. No general Laurent theorem is required here.

## 50. Asymptotic analysis, resurgence, and perturbation

### 50.23. Euler–Maclaurin formula

**Statement.** For integers $m<n$ and smooth $f$,
$$
\sum_{k=m}^nf(k)=\int_m^nf(x)dx+\frac{f(m)+f(n)}2
+\sum_{r=1}^p\frac{B_{2r}}{(2r)!}
[f^{(2r-1)}(n)-f^{(2r-1)}(m)]+R_p.
$$
Here $R_p=-(2p)!^{-1}\int_m^n\widetilde B_{2p}(x)f^{(2p)}(x)dx$.

**Argument.** Mathlib already has Bernoulli polynomials, $B_k'=kB_{k-1}$
(`hasDerivAt_bernoulliFun`), the antiderivative, endpoint values,
$\int_0^1 B_k$, and the periodization $\widetilde B_j(\{x\})$
(`periodizedBernoulli`). The formula is integration by parts on each
$[k,k+1]$ with $B_1(x)=x-1/2$, then summation. The jump of $B_1$ at integers
is `bernoulliFun_eval_one`.

**Library results.** `bernoulliFun`, `hasDerivAt_bernoulliFun`,
`periodizedBernoulli`, `bernoulliFun_eval_one` in
`Mathlib/NumberTheory/ZetaValues.lean`.
