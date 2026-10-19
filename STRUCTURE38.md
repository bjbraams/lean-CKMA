# Structure 38: Potential theory and capacity

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS38.md); [bibliographical scope](CKMA-bib.md#ckma-38); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.InnerProductSpace.Harmonic.Basic`, `Mathlib.Analysis.Complex.Harmonic.MeanValue`, `Mathlib.Analysis.Complex.Harmonic.Liouville`, `Mathlib.Analysis.Complex.Harmonic.Analytic`, `Mathlib.Analysis.Complex.Poisson`, `Mathlib.Analysis.Complex.Harmonic.Poisson`, `Mathlib.Analysis.Complex.JensenFormula`, `Mathlib.Analysis.SpecialFunctions.Integrals.PosLog`, `Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace`.

**Namespaces.** Harmonic-function statements use `InnerProductSpace` (`InnerProductSpace.HarmonicOnNhd`); the Poisson kernel is defined at the root of its Mathlib file. No capacity or potential-theory namespace exists in Mathlib. TauCeti declarations are in `TauCeti` (for example `TauCeti.SubharmonicOn`, `TauCeti.WeaklyHarmonicOn`, `TauCeti.perronSolution`, `TauCeti.ballGreenKernel`) and are identified by name below.

## Harmonic, subharmonic, and superharmonic functions

[Mathematical scope](SYNOPSIS38.md#harmonic-subharmonic-and-superharmonic-functions).

### Mathlib

The Poisson integral on a disk in the complex plane is the formula of section 33: circle averages against the Poisson kernel recover holomorphic functions and real-valued harmonic functions inside the disk. It is not developed as potential theory. Harmonic functions on a finite-dimensional real inner product space are defined through the Laplacian (`InnerProductSpace.HarmonicOnNhd`, `Analysis/InnerProductSpace/Harmonic/Basic.lean`). In the plane, harmonic functions with values in a Banach space have the circle mean-value property (`InnerProductSpace.HarmonicOnNhd.circleAverage_eq`, `Analysis/Complex/Harmonic/MeanValue.lean`), a bounded harmonic function on \(\mathbb C\) is constant (`InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant` in `Analysis/Complex/Harmonic/Liouville.lean`), and a real harmonic function on a disc is the real part of a holomorphic function, hence real-analytic (`Analysis/Complex/Harmonic/Analytic.lean`).

### TauCeti

Nonnegative harmonic functions satisfy Harnack comparison on compact subsets of a connected open set in any finite dimension ([Harnack theorem](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Harnack/Basic.lean)). The mean-value property on Euclidean balls, weak and strong maximum principles for \(C^2\) subharmonic functions (functions with \(\Delta u\ge0\)), and Hopf's boundary-point lemma are also proved (Section 33; [mean value](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Harmonic/MeanValue/Basic.lean), [strong maximum principle](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Laplacian/StrongMaximumPrinciple.lean)). Conversely, a continuous function equal to its ball averages at every point for arbitrarily small radii is harmonic (`TauCeti.harmonicOnNhd_iff_continuousOn_setAverage_ball_eq`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Harmonic/MeanValue/Converse.lean)).

Weyl's lemma is proved: a locally integrable function whose distributional Laplacian vanishes on an open set agrees almost everywhere with a harmonic function, and a continuous function is harmonic exactly when it is weakly harmonic (`TauCeti.WeaklyHarmonicOn.exists_harmonicOnNhd_ae_eq`, `TauCeti.harmonicOnNhd_iff_weaklyHarmonicOn`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Harmonic/Weyl.lean)). Directional derivatives of harmonic functions are harmonic (`InnerProductSpace.HarmonicOnNhd.fderiv_apply`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Harmonic/Deriv.lean)), a harmonic function bounded by \(M\) on the balls of radius \(s\) about \(y\) and \(z\), with \(\|y-z\|\le s\), satisfies \(\|u(y)-u(z)\|\le2^n\,n\,M\|y-z\|/s\) in dimension \(n\), and \(L^2\) decay estimates on concentric balls hold (`InnerProductSpace.HarmonicOnNhd.norm_sub_le_of_norm_le`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Harmonic/Decay.lean)); locally uniform limits of harmonic functions are harmonic (`TauCeti.harmonicOnNhd_of_tendstoLocallyUniformlyOn`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Harmonic/Convergence.lean)). Harnack's convergence theorem: a monotone family of harmonic functions on a preconnected open set that is bounded above at one point converges locally uniformly to a harmonic function (`TauCeti.tendstoLocallyUniformlyOn_iSup_of_monotone`, `TauCeti.harmonicOnNhd_iSup_of_monotone`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Harnack/Convergence.lean)); the divergent alternative is not stated. In the plane the sharp Poisson-kernel Harnack constant and the strong maximum principle for harmonic functions are proved ([planar Harnack](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Harnack/Planar.lean), [strong principle](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Harnack/StrongPrinciple.lean)).

The Poisson integral of continuous data on a sphere is harmonic in the ball, continuous up to the boundary, and attains the data, on every ball in any finite dimension (`TauCeti.exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere`; [ball Poisson integral](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/PoissonIntegral/Ball.lean)); with the comparison principle this gives the unique continuous harmonic extension. The half-space Poisson integral of bounded continuous data solves the Dirichlet problem on a half-space ([half-space Poisson integral](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/PoissonIntegral/HalfSpace.lean)). The representation of positive harmonic functions by boundary measures is available only in the plane, through the Herglotz representation of holomorphic functions with nonnegative real part on the unit disc (`TauCeti.exists_isFiniteMeasure_eq_herglotzTransform_add`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Herglotz.lean)), combined with Mathlib's representation of a harmonic function on a disc as the real part of a holomorphic function (`Analysis/Complex/Harmonic/Analytic.lean`).

Continuous subharmonic functions are defined by the local sub-mean-value inequality, without differentiability (`TauCeti.SubharmonicOn`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Harmonic/Subharmonic.lean)). The class contains harmonic functions and is closed under maxima, nonnegative multiples and subtraction of harmonic functions, and the comparison principle holds on bounded open sets: a subharmonic \(u\) and a superharmonic \(w\), both continuous on \(\overline U\), with \(u\le w\) on \(\partial U\) satisfy \(u\le w\) on \(\overline U\).

TauCeti constructs the Euclidean Newtonian kernel and proves its fundamental-solution identity for \(-\Delta\) in dimension \(n\ge3\): for compactly supported \(C^2\) test functions, \(\int G_n\Delta\varphi=-\varphi(0)\), including translated poles ([distributional identity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/FundamentalSolution/Euclidean/DistributionalLaplacian.lean)). There is a separate logarithmic planar kernel ([planar kernel](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/FundamentalSolution/Planar/Basic.lean)). The Newtonian potential \(G_n\star f\) of a compactly supported \(C^2\) function solves \(-\Delta u=f\), is harmonic off the support of \(f\), decays like \(|x|^{2-n}\) for \(n\ge3\), and is the unique \(C^2\) solution vanishing at infinity; in the plane the logarithmic potential is the unique solution with \(u-G\int f\to0\) at infinity ([Newtonian potential](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/FundamentalSolution/Euclidean/Potential.lean), [planar potential](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/FundamentalSolution/Planar/Potential.lean)). Green kernels for balls and discs are constructed, symmetric in their two arguments (`TauCeti.ballGreenKernel_comm`), positive inside the ball outside dimension two, with boundary vanishing, the distributional identity \(-\Delta G(\cdot,y)=\delta_y\) in the ball ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/GreenFunction/DistributionalLaplacian.lean)), and the normal-derivative relation to the Poisson kernel ([Euclidean ball](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/GreenFunction/Ball.lean), [planar disk](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/GreenFunction/Disk.lean), [planar Poisson relation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/GreenFunction/Poisson.lean)). The half-space Green kernel is obtained by reflection ([half-space](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/GreenFunction/HalfSpace.lean)).

**Synopsis entries.** Covered: 38.1 (TauCeti). Partly covered: 38.2 (Dirichlet problem on balls by the Poisson integral in every dimension; the measure representation of positive harmonic functions only in the plane), 38.4 (Harnack inequality in every dimension; Liouville only for bounded harmonic functions on \(\mathbb C\)), 38.5 (convergent alternative only), 38.6 (first-order interior bound and harmonicity of derivatives in every dimension; analyticity only in the plane), 38.9 (continuous subharmonic functions by the sub-mean-value inequality; no upper semicontinuous class or distributional characterization), 38.11 (comparison of continuous subharmonic and superharmonic functions continuous up to the boundary of a bounded open set), 38.12 (Green kernels of balls, discs and half-spaces only), 38.13 (symmetry of the ball Green kernel only). Not covered: 38.3, 38.7, 38.8, 38.10, 38.14, 38.15.

## Newtonian capacity, equilibrium, and thinness

[Mathematical scope](SYNOPSIS38.md#newtonian-capacity-equilibrium-and-thinness).

No Newtonian capacity, finite-energy measure, equilibrium measure, polar set, or fine topology is defined in either library; the Newtonian kernel and potentials recorded in the previous topic are the nearest supporting material.

### TauCeti

A capacity of Choquet type for measures appears in the proof that analytic sets are universally measurable ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/MeasurableSpace/Analytic.lean)) (supporting material); it is not Newtonian capacity, and capacitability for Newtonian capacity is not derived.

**Synopsis entries.** Not covered: 38.16–38.27.

## The Dirichlet problem, harmonic measure, and ideal boundaries

[Mathematical scope](SYNOPSIS38.md#the-dirichlet-problem-harmonic-measure-and-ideal-boundaries).

### TauCeti

Perron's method is carried out on an arbitrary bounded open set \(\Omega\) ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Perron/Basic.lean)): for boundary data bounded on \(\partial\Omega\), the supremum of the Perron family (functions continuous on \(\overline\Omega\), subharmonic in \(\Omega\), below \(g\) on \(\partial\Omega\)) is harmonic in \(\Omega\), with no regularity of \(\partial\Omega\) or continuity of \(g\) (`TauCeti.harmonicOnNhd_perronSolution`). At a boundary point with a barrier where \(g\) is continuous along \(\partial\Omega\), the Perron solution attains \(g\) continuously; if every boundary point has a barrier, the Dirichlet problem is solvable for continuous data, and the exterior sphere condition supplies Newtonian (\(n\ne2\)) or logarithmic (\(n=2\)) barriers (`TauCeti.tendsto_perronSolution_of_isBarrier`, `TauCeti.exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier_of_exterior_sphere`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Perron/Barrier.lean)). The upper Perron solution is the symmetric construction. Agreement of the upper and lower Perron solutions for continuous data on an arbitrary bounded domain (Wiener resolutivity), the converse barrier characterization of regular points, harmonic measure on general domains, and capacitary regularity criteria are not proved.

**Synopsis entries.** Partly covered: 38.28 (the lower Perron solution is harmonic on every bounded open set; equality with the upper solution is not proved), 38.29 (a barrier implies regularity; the converse is not proved), 38.31 (barriers from an exterior sphere only). Not covered: 38.30, 38.32–38.38.

## Brownian interpretations

[Mathematical scope](SYNOPSIS38.md#brownian-interpretations).

**Synopsis entries.** Not covered: 38.40, 38.41.

## Riesz potentials and stable processes

[Mathematical scope](SYNOPSIS38.md#riesz-potentials-and-stable-processes).

### TauCeti

As supporting material, TauCeti proves the kernel bound and an \(L^p\)–\(L^q\) estimate for Riesz-type potentials \(\int|x-y|^{\alpha-n}f(y)\,dy\) over sets of finite measure (`TauCeti.setLIntegral_enorm_sub_rpow_le`, `TauCeti.eLpNorm_setLIntegral_enorm_sub_rpow_mul_le`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/RieszPotential.lean)). Riesz composition, Riesz energy, capacity, and stable processes are not present.

**Synopsis entries.** Not covered: 38.68–38.70.

## Sobolev capacity and nonlinear potential theory

[Mathematical scope](SYNOPSIS38.md#sobolev-capacity-and-nonlinear-potential-theory).

### Mathlib

**Supporting foundations.**

Bessel potential spaces provide Fourier-theoretic Sobolev spaces; their definitions and properties are recorded in [Section 26](STRUCTURE26.md). No capacity is defined from them.

**Synopsis entries.** Not covered: 38.43, 38.45–38.54.

## Logarithmic potentials and equilibrium in the plane

[Mathematical scope](SYNOPSIS38.md#logarithmic-potentials-and-equilibrium-in-the-plane).

### Mathlib

**Supporting foundations.**

One computation of logarithmic potential theory is present: the circle average of \(z\mapsto\log|z-a|\) over the unit circle equals \(\log^+|a|\), that is, the logarithmic potential of normalized arc length on the circle (`circleAverage_log_norm_sub_const_eq_posLog` in `Analysis/SpecialFunctions/Integrals/PosLog.lean`). Jensen's formula (`MeromorphicOn.circleAverage_log_norm`), which expresses the circle average of \(\log|f|\) for a meromorphic \(f\) through its zeros and poles, is proved (`Analysis/Complex/JensenFormula.lean`) and underlies the Nevanlinna theory recorded in Section 41. In the language of Ransford, these are statements about the logarithmic potentials of specific measures and about the Riesz measure of \(\log|f|\).
 No logarithmic capacity, equilibrium measure, or transfinite diameter is defined.

### TauCeti

The logarithmic kernel \(\log\|x-a\|\) is harmonic off \(a\) in a two-dimensional inner product space (`TauCeti.harmonicOnNhd_log_norm_sub_of_finrank_eq_two`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Harmonic/LogNorm.lean)), and the planar logarithmic potential and disc Green function are recorded in the first topic.

**Synopsis entries.** Partly covered: 38.55 (Jensen's formula for \(u=\log|f|\), \(f\) meromorphic; Mathlib). Not covered: 38.56–38.62.

## Analytic capacity and removability

[Mathematical scope](SYNOPSIS38.md#analytic-capacity-and-removability).

**Synopsis entries.** Not covered: 38.64–38.66.

## Harmonic approximation

[Mathematical scope](SYNOPSIS38.md#harmonic-approximation).

**Synopsis entries.** Not covered: 38.71, 38.72.

## Axiomatic potential theory

[Mathematical scope](SYNOPSIS38.md#axiomatic-potential-theory).

**Synopsis entries.** Not covered: 38.73, 38.74.
