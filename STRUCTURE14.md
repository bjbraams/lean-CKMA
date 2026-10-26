# Structure 14: Functional, isoperimetric, and geometric inequalities

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS14.md); [bibliographical scope](CKMA-bib.md#ckma-14); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.FunctionalSpaces.SobolevInequality`, `Mathlib.Algebra.Order.Rearrangement`, `Mathlib.Analysis.Convex.Body`, `Mathlib.Topology.MetricSpace.Closeds`, `Mathlib.Topology.Sets.VietorisTopology`, `Mathlib.InformationTheory.KullbackLeibler.Basic`.

**Namespaces.** The Sobolev inequality is in `MeasureTheory`. The rearrangement inequality is stated for `Monovary` and `Antivary`, as in Section 11. Convex bodies are `ConvexBody`, and the hyperspace of nonempty compact sets is `TopologicalSpace.NonemptyCompacts`. Relative entropy is `InformationTheory.klDiv`. The TauCeti results are in `TauCeti` and its subnamespaces (`TauCeti.W1p`, `TauCeti.PDE`, `TauCeti.Yamabe`), with `MeasureTheory.Measure.HasPrekopaLeindler` and the `ConvexBody` parallel-volume lemmas in the Mathlib namespaces.

## Sobolev, interpolation, and singular-weight inequalities

[Mathematical scope](SYNOPSIS14.md#sobolev-interpolation-and-singular-weight-inequalities).

### Mathlib

**The Gagliardo–Nirenberg–Sobolev inequality.**

The full development belongs to Section 26. The statements proved in `Analysis/FunctionalSpaces/SobolevInequality.lean` are as follows. On \(\iota\to\mathbb{R}\) with \(\iota\) finite of cardinality \(n\ge 2\), if \(p\) is the Hölder conjugate of \(n\) and \(u\) is a \(C^1\) compactly supported map into a real normed space, then
\[
\int^- \|u\|^p\le\Bigl(\int^- \|Du\|\Bigr)^p,
\]
with constant \(1\), using the coordinate sup norm on \(\iota\to\mathbb R\) and its induced operator norm on \(Du\). The integrals are lower integrals of extended norms. On a finite-dimensional real normed space of dimension \(n\ge 2\), with a Haar measure, the same comparison holds with a constant that depends only on the space, the measure, and \(p\); the constant comes from the comparison of Haar measure with Lebesgue measure on \(\mathbb{R}^n\) and from the operator norm of a chosen linear equivalence with \(\mathbb{R}^n\). Equivalently, the \(L^p\) norm of \(u\) is at most a constant times the \(L^1\) norm of its Fréchet derivative.

If the codomain is a real inner product space, \(1\le p<n\), and \(p'=np/(n-p)>0\) is the Sobolev conjugate defined by \((p')^{-1}=p^{-1}-n^{-1}\), then the \(L^{p'}\) norm of a \(C^1\) compactly supported \(u\) is at most a constant, depending on the measure and on \(p\), times the \(L^p\) norm of the derivative. If instead the codomain is finite-dimensional, the support of \(u\) lies in a bounded set \(s\), and \(1\le p<n\), then the \(L^p\) norm of \(u\) is at most a constant, depending on the codomain, the measure, \(s\), and \(p\), times the \(L^p\) norm of the derivative. This last statement is a Poincaré inequality for functions supported in a fixed bounded set.

The three statements are `MeasureTheory.lintegral_pow_le_pow_lintegral_fderiv` (the endpoint \(p=n/(n-1)\), any real normed codomain), `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner` and `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` (the Sobolev conjugate exponent, inner-product or finite-dimensional codomain), and `MeasureTheory.eLpNorm_le_eLpNorm_fderiv` (bounded support). The constants are not sharp and are not identified; in particular the isoperimetric constant \(n\omega_n^{1/n}\) of the endpoint inequality does not appear. The proof rests on the grid-lines lemma `MeasureTheory.lintegral_prod_lintegral_pow_le`, a Gagliardo-type product estimate for one function on a finite product of σ-finite measure spaces; the Loomis–Whitney inequality for sets is not stated.

### TauCeti

TauCeti extends the smooth-function Sobolev estimates to actual weak Sobolev spaces. For \(1\le p<n\), it proves \(W^{1,p}_0(\Omega)\hookrightarrow L^{np/(n-p)}(\Omega)\), with a gradient-norm bound (`TauCeti.W1p0.sobolevEmbeddingL`, [Sobolev embedding](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/Embedding.lean)). For \(n<p<\infty\), it constructs a continuous linear embedding of whole-space \(W^{1,p}(\mathbb R^n)\) into the global Hölder space of exponent \(1-n/p\) (`TauCeti.W1p.morreyEmbedding`, [Morrey embedding](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/W1p/HolderEmbedding.lean)). The zero-boundary condition in the first result and the whole-space domain in the second are part of the statements. Section 26 records the underlying spaces and compactness results.

A Poincaré inequality is proved on \(W^{1,p}_0(\Omega)\), \(1\le p\le\infty\), when \(\Omega\) lies in a slab of width \(b-a\): \(\|u\|_p\le(b-a)\|\nabla u\|_p\). The constant does not depend on the dimension, on \(p\), or on the shape of \(\Omega\); it rests on the same estimate for \(C^1\) functions supported in the slab ([slab](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/Poincare/Slab.lean)). A ball-containment version follows ([Poincaré](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/Poincare/W1p0.lean)). The inequality fails for \(W^{1,p}_0\) of the whole space, and this is proved as well (`TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv`, [whole space](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/Poincare/WholeSpace.lean)).

The Poincaré–Wirtinger inequality is proved on a bounded convex open set \(\Omega\) in a finite-dimensional real inner-product space, for \(1\le p<\infty\): for \(u\in W^{1,p}(\Omega)\) and a subset \(S\subseteq\Omega\) of positive measure,
\[
\Bigl\|u-\fint_S u\Bigr\|_{L^p(\Omega)}\le \frac{|B_1|\,(\mathop{\mathrm{diam}}\Omega)^{n+1}}{|S|}\,\|\nabla u\|_{L^p(\Omega)},
\]
with the constant \(2^{n+1}R\) on a ball of radius \(R\) averaged over the whole ball. The \(C^1\) version comes first, by the classical potential estimate ([C¹ version](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/Poincare/Wirtinger/Basic.lean), [Sobolev version](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/Poincare/Wirtinger/W1p.lean)). The constants are explicit, not sharp; in particular the Payne–Weinberger constant \(\pi^2/D^2\) is not obtained.

**Sobolev inequalities on sets of finite measure and Trudinger's inequality.** Let \(E\) be a real normed space of dimension \(n\ge1\) with an additive Haar measure, \(\omega=|B_1|\), and \(\Omega\) of finite measure. If \(1\le p\le q<\infty\) and \(\delta=1/p-1/q<1/n\), every \(u\in W^{1,p}_0(\Omega)\) satisfies \(\|u\|_q\le n^{-1}\omega^{-1/n}\bigl((1-\delta)/(1/n-\delta)\bigr)^{1-\delta}|\Omega|^{1/n-\delta}\|\nabla u\|_p\), in every dimension and without the restriction \(p<n\) ([finite measure](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/FiniteMeasure.lean)). The proof bounds \(|u|\) by the Riesz potential of \(|\nabla u|\) of order one and uses the estimate \(\|\int_\Omega|x-y|^{n(\kappa-1)}f(y)\,dy\|_{L^q(\Omega)}\le C\,|\Omega|^{\kappa-\delta}\|f\|_{L^p(\Omega)}\) for \(\delta<\kappa\le1\) (`TauCeti.eLpNorm_setLIntegral_enorm_sub_rpow_mul_le`, Gilbarg–Trudinger Lemma 7.12, [Riesz potential](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/RieszPotential.lean)); this is not the whole-space Hardy–Littlewood–Sobolev inequality. In the borderline case \(p=n\) the moment bounds grow like \(q^{1-1/n}\), and summing them gives **Trudinger's inequality**: for \(u\in W^{1,n}_0(\Omega)\) and for compactly supported \(C^1\) functions,
\[
\int_\Omega\exp\Bigl(\bigl(|u|/(c\,\|\nabla u\|_n)\bigr)^{n/(n-1)}\Bigr)\le e\,(n^n+5)\,|\Omega|,\qquad c=(2e)^{1-1/n}n^{-1}\omega^{-1/n}
\]
(`TauCeti.W1p.setLIntegral_exp_abs_value_div_rpow_le`, `TauCeti.setLIntegral_exp_norm_div_rpow_le`, [Trudinger](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/Trudinger.lean)). The exponent is explicit, not Moser's sharp \(\alpha_n\).

**Yamabe bubbles.** On a real inner product space of dimension \(n\), the bubbles \(U_{t,b}(x)=\bigl(2t/(t^2+|x-b|^2)\bigr)^{(n-2)/2}\), which are dilates, translates and multiples of the Aubin–Talenti profile \((1+|x|^2)^{-(n-2)/2}\), are defined (`TauCeti.Yamabe.bubble`), shown to be smooth and positive, and shown to solve the critical equation \(a_n(-\Delta U_{t,b})=n(n-1)U_{t,b}^{p_n-1}\) with \(a_n=4(n-1)/(n-2)\) and \(p_n=2n/(n-2)\), for \(n\ne2\) (`TauCeti.Yamabe.conformalCoefficient_mul_neg_laplacian_bubble`, [bubble](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Yamabe/Bubble.lean)). Their extremality for the Sobolev inequality and the value of \(S_n\) are not proved.

**Synopsis entries.** Covered: 14.2 (Mathlib for compactly supported \(C^1\) functions with a non-explicit constant; TauCeti on \(W^{1,p}_0(\Omega)\)). Partly covered: 14.1 (the endpoint inequality with a non-sharp constant, Mathlib; no isoperimetric form or equality case), 14.3 (the extremal profile is defined and solves the critical equation, TauCeti; no sharp constant or classification of extremizers), 14.6 (Poincaré–Wirtinger on bounded convex domains with an explicit non-sharp constant, TauCeti), 14.8 (Trudinger's inequality with a non-sharp explicit exponent, TauCeti; not Moser's \(\alpha_n\) or its optimality). Not covered: 14.9–14.14.

## Capacity, perimeter, and spectral optimization

[Mathematical scope](SYNOPSIS14.md#capacity-perimeter-and-spectral-optimization).

### Mathlib

**Discrete rearrangement.** The rearrangement inequality of Section 11 compares \(\sum_i f_i g_{\sigma i}\) with \(\sum_i f_i g_i\): the sum is maximized when \(f\) and \(g\) monovary and minimized when they antivary, for a permutation that moves only points of the set of summation (`Algebra/Order/Rearrangement.lean`). This is the finite-sum rearrangement inequality recorded in Section 11; it is not the symmetric decreasing rearrangement of functions on \(\mathbb R^n\).

### TauCeti

On the same bounded convex domains, De Giorgi's isoperimetric inequality for \(u\in W^{1,p}(\Omega)\), \(1\le p\le\infty\), and levels \(k<l\) reads \((l-k)\,|\{u\ge l\}|\,|\{u\le k\}|\le|B_1|(\mathop{\mathrm{diam}}\Omega)^{n+1}\int_{\{k<u<l\}}|\nabla u|\), with a ball version and a squared form for \(W^{1,2}\) (`TauCeti.W1p.sub_mul_measureReal_mul_measureReal_le_of_convex`, [De Giorgi](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/Poincare/Wirtinger/DeGiorgi.lean)). This is a functional relative isoperimetric inequality on convex domains; the perimeter form of the relative isoperimetric inequality is not stated.

De Giorgi's perimeter \(P(s;\Omega)\) is defined as the total variation of the indicator, is invariant under null modifications and complements, and is lower semicontinuous under local convergence in measure (`TauCeti.perimeter_le_liminf`, [perimeter](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/BoundedVariation/Perimeter.lean)). No inequality between perimeter and volume is proved for sets of finite perimeter in dimension \(n\ge2\).

**Schwarz rearrangement.** The Schwarz (symmetric decreasing) rearrangement of an arbitrary \(f\colon E\to[0,\infty]\) is defined from the distribution function; for an additive Haar measure it is measurable, radially nonincreasing, monotone, idempotent, independent of the a.e. representative, equimeasurable with \(f\), and preserves every \(L^p\) norm (`TauCeti.addHaar_setOf_lt_schwarzRearrangement`, `TauCeti.eLpNorm_schwarzRearrangement`, [Schwarz rearrangement](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/SchwarzRearrangement.lean)). No Pólya–Szegő gradient inequality is proved.

No capacity in the sense of the synopsis (relative \(p\)-capacity) is defined, and the Faber–Krahn, Szegő–Weinberger and Saint-Venant inequalities and Cheeger's inequality are not proved. The variational characterization of the first Dirichlet eigenvalue is recorded under [Further equivalences, stability, and spectral consequences](#further-equivalences-stability-and-spectral-consequences).

**Synopsis entries.** Partly covered: 14.19 (the symmetric decreasing rearrangement with equimeasurability and preservation of all \(L^q\) norms, TauCeti; no gradient inequality or equality case). Not covered: 14.16–14.18, 14.20–14.25.

## Geometric inequalities for Gaussian, curved, and convex models

[Mathematical scope](SYNOPSIS14.md#geometric-inequalities-for-gaussian-curved-and-convex-models).

### TauCeti

**Prékopa–Leindler and Brunn–Minkowski.** For a measure on a real module, `Measure.HasPrekopaLeindler θ` states that measurable \(f,g,h\colon E\to[0,\infty]\) with \(f(x)^{1-\theta}g(y)^\theta\le h((1-\theta)x+\theta y)\) for all \(x,y\) satisfy \((\int f)^{1-\theta}(\int g)^\theta\le\int h\). The property tensorizes over products and transfers along measure-preserving maps preserving affine combinations; Lebesgue measure on \(\mathbb R\), on \(\iota\to\mathbb R\), and on every finite-dimensional real inner product space has it for \(0\le\theta\le1\) (`TauCeti.hasPrekopaLeindler_volume`, [Prékopa–Leindler](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/PrekopaLeindler.lean)). Consequently, for nonempty null-measurable \(A,B\) in a positive-dimensional Euclidean space, \(|A|^{1/n}+|B|^{1/n}\le|A+B|^{1/n}\) with outer volume on the right, together with the multiplicative form \(|A|^{1-\theta}|B|^\theta\le|(1-\theta)A+\theta B|\) and real-valued versions (`TauCeti.volume_rpow_add_volume_rpow_le`, [Brunn–Minkowski](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Basic.lean); the one-dimensional case in [Real.lean](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Real.lean)). The equality case of Brunn–Minkowski (homothety of convex bodies) is not proved; the parallel-volume consequences for convex bodies are recorded under [Mixed volumes and convex-body inequalities](#mixed-volumes-and-convex-body-inequalities). The **isodiametric inequality** \(|s|\le\omega_n(\mathop{\mathrm{diam}}s/2)^n\) holds for every bounded set in a finite-dimensional real inner product space, with outer measure and no measurability hypothesis (`TauCeti.volume_le_volume_closedBall_diam_div_two`, [isodiametric](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Measure/Lebesgue/Isodiametric.lean)).

**Planar isoperimetry and Wirtinger's inequality.** For an absolutely continuous \(f\colon[a,b]\to V\) into a finite-dimensional real inner product space with \(f(a)=f(b)\) and \(f'\in L^2\), \(\int_a^b|f-\bar f|^2\le((b-a)/2\pi)^2\int_a^b|f'|^2\), with equality exactly for the mean plus a first harmonic (`TauCeti.integral_norm_sub_average_sq_le`, `TauCeti.integral_norm_sub_average_sq_eq_iff`, [Wirtinger](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Wirtinger.lean)). For an absolutely continuous closed plane curve with square-integrable derivative, \(4\pi|\mathop{\mathrm{signedArea}}\gamma|\le(b-a)\int_a^b|\gamma'|^2\), with equality exactly for constant curves and circles traversed once at constant speed; for a curve parametrized proportionally to arclength this is the isoperimetric inequality \(|\text{area}|\le L^2/4\pi\) (`TauCeti.four_pi_mul_abs_signedArea_le`, [area–energy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/AreaEnergy.lean)).

Gaussian isoperimetry, the Lévy–Gromov comparison, the Brascamp–Lieb inequalities and the Loomis–Whitney inequality are not formalized.

**Synopsis entries.** Covered: 14.29 (TauCeti). Partly covered: 14.28 (the inequality for nonempty measurable sets, with outer volume of the sum, TauCeti; not the equality case). Not covered: 14.26, 14.27, 14.30–14.32.

## Mixed volumes and convex-body inequalities

[Mathematical scope](SYNOPSIS14.md#mixed-volumes-and-convex-body-inequalities).

### Mathlib

`ConvexBody V` is the type of nonempty compact convex subsets of a real topological vector space, that is, of elements of \(\mathcal K^n\) in the synopsis notation (no interior condition is imposed). It is a module over \(\mathbb R_{\ge0}\) under Minkowski addition and dilation, and on a normed space it is a metric space for the Hausdorff distance (`ConvexBody.hausdorffDist_coe`, `Analysis/Convex/Body.lean`). Separately, the nonempty compact subsets of a metric space carry the Hausdorff metric (`TopologicalSpace.NonemptyCompacts`, `Topology/MetricSpace/Closeds.lean`), whose topology is the Vietoris topology, and the nonempty compact subsets of a fixed compact set form a compact set (`TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact`, `Topology/Sets/VietorisTopology.lean`). This gives the selection principle for nonempty compact subsets of a ball in \(\mathbb R^n\); the closedness of convexity under Hausdorff limits, and hence the Blaschke selection theorem for \(\mathcal K^n\) as stated, is not proved. Mixed volumes, support functions, surface area measures and intrinsic volumes are not defined.

### TauCeti

For `ConvexBody` elements \(K,L\) of a finite-dimensional real inner product space of positive dimension, \(t\mapsto|K+tL|^{1/n}\) is concave on \(t\ge0\) and bounded below by \(|K|^{1/n}+t|L|^{1/n}\) (`ConvexBody.concaveOn_volume_real_add_smul_rpow`). If its right derivative \(d\) at \(0\) exists, then \(d\ge|L|^{1/n}\), and \(d=|L|^{1/n}\) exactly when the profile is affine on \([0,\infty)\) (`ConvexBody.volume_real_rpow_le_of_hasDerivWithinAt`, `ConvexBody.hasDerivWithinAt_volume_real_add_smul_rpow_iff`, [parallel volume](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Parallel.lean)). Since \(d=|K|^{1/n-1}V(K[n-1],L)\) when \(|K|>0\), the bound \(d\ge|L|^{1/n}\) is Minkowski's first inequality, but only under the hypothesis that the derivative exists, and without mixed volumes or the homothety equality case.

**Synopsis entries.** Partly covered: 14.74 (the Hausdorff metric on nonempty compact convex sets and compactness of the nonempty compact subsets of a compact set, Mathlib; convexity of limits not proved), 14.78 (the derivative form of Minkowski's first inequality, assuming the right derivative of the parallel volume exists, TauCeti; no mixed volumes or equality case). Not covered: 14.75–14.77, 14.79–14.83.

## Functional inequalities and symmetric Markov semigroups

[Mathematical scope](SYNOPSIS14.md#functional-inequalities-and-symmetric-markov-semigroups).

### TauCeti

**Donsker–Varadhan variational formula.** For probability measures \(\mu,\nu\) on an arbitrary measurable space, Mathlib's relative entropy satisfies \(\mathop{\mathrm{klDiv}}(\mu,\nu)=\sup_f\bigl(\int f\,d\mu-\log\int e^f\,d\nu\bigr)\) over bounded measurable \(f\) (`TauCeti.klDiv_eq_iSup_integral_sub_log_integral_exp`), and on a pseudometrizable Borel space the supremum may be taken over bounded continuous \(f\) (`TauCeti.klDiv_eq_iSup_boundedContinuousFunction_integral_sub_log_integral_exp`). Both are equalities in \([0,\infty]\), so the case of infinite entropy is included. A version with the mass correction holds for finite measures, and relative entropy is jointly weakly lower semicontinuous ([variational formula](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/InformationTheory/KullbackLeibler/Variational.lean)).

Markov semigroups, Dirichlet forms in the sense of the synopsis, the carré du champ, and the Poincaré, logarithmic Sobolev, Nash and weak Poincaré inequalities are not formalized in either library.

**Synopsis entries.** Covered: 14.66 (TauCeti). Not covered: 14.33–14.38, 14.40, 14.43, 14.44, 14.65.

## Curvature–dimension calculus and Riemannian comparison

[Mathematical scope](SYNOPSIS14.md#curvaturedimension-calculus-and-riemannian-comparison).

### TauCeti

The synthetic condition \(CD(K,\infty)\) of Sturm and Lott–Villani is defined for metric-measure spaces as weak \(K\)-convexity of the Boltzmann entropy on \(P_2(X)\) (`TauCeti.MetricMeasureSpace.CurvatureDimensionInfinity`, [curvature–dimension](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/OptimalTransport/MetricMeasure/CurvatureDimension.lean)). This is the synthetic counterpart of the condition in the synopsis, not the Bakry–Émery \(\Gamma_2\) condition; no functional inequality is derived from it, and no smooth example (for instance a log-concave measure on \(\mathbb R^n\)) is shown to satisfy it.

**Synopsis entries.** Not covered: 14.45–14.49, 14.67, 14.68.

## Transport, entropy, and sharp model inequalities

[Mathematical scope](SYNOPSIS14.md#transport-entropy-and-sharp-model-inequalities).

### TauCeti

The supporting infrastructure is present, but none of the inequalities of this heading. TauCeti defines the Wasserstein space \(P_p(X)\) of laws with finite \(p\)-th moment with the distance \(W_p\) (`TauCeti.WassersteinSpace`, [Wasserstein space](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Space.lean)), the Boltzmann entropy \(\int\rho\log\rho\,dm\) relative to a possibly infinite reference measure together with its relation to `klDiv` ([internal energy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/InternalEnergy.lean)), and its lower semicontinuity on \(P_p(X)\) ([Boltzmann entropy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/BoltzmannEntropy.lean)). For an \(m\)-strongly convex potential \(V\) on a real Banach space, bounded below by \(-(A+B|x|^2)\), the potential energy \(\int V\,d\mu\) is \(m\)-convex along \(W_2\)-geodesics (`StrongConvexOn.geodesicallyConvex_potentialEnergy`, [potential energy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/PotentialEnergy.lean)); this is the potential part of displacement convexity of \(H(\cdot\mid e^{-V}dx)\), but displacement convexity of the Lebesgue entropy is not proved. Pinsker's inequality \(d_{TV}(\mu,\nu)^2\le\frac12\mathop{\mathrm{klDiv}}(\mu,\nu)\) is proved for probability measures on a measurable space (`TauCeti.totalVariation_sq_le_two_mul_klDiv`, [Pinsker](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/InformationTheory/KullbackLeibler/Pinsker.lean)); it is a transport–entropy inequality for the discrete metric, not the Bobkov–Götze equivalence.

**Synopsis entries.** Not covered: 14.55–14.64.

## Further equivalences, stability, and spectral consequences

[Mathematical scope](SYNOPSIS14.md#further-equivalences-stability-and-spectral-consequences).

### TauCeti

For a symmetric coercive divergence-form operator on a nonempty bounded open set, the first Dirichlet eigenvalue is the minimum of the Rayleigh quotient over \(H^1_0(\Omega)\), attained at an eigenfunction (`TauCeti.PDE.isLeast_rayleighQuotient_firstDirichletEigenvalue`, [Dirichlet spectrum](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Spectrum/Basic.lean)). It is the natural starting point for the eigenvalue inequalities of this heading, none of which is proved.

**Synopsis entries.** Not covered: 14.69–14.72.
