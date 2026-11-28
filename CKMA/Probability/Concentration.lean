/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.Concentration.Basic
public import CKMA.Probability.Concentration.Bernstein
public import CKMA.Probability.Concentration.JohnsonLindenstrauss

/-!
# Sub-Gaussian gauges, Bernstein and dimension reduction (07.4, 07.6, 07.47)

`HasPsiTwoBound`, `HasGaussianTail` and `HasGaussianMoments` express the exponential,
tail and moment descriptions of a real sub-Gaussian random variable. The extended
nonnegative `psiTwoGauge` is infinite if no positive admissible scale exists.
The implication theorems compare these descriptions and Mathlib's sub-Gaussian MGF API.

The other main statements are Bernstein's inequality for independent centered variables
and the Johnson–Lindenstrauss finite-set embedding bound. Scale and probability
normalizations are explicit at the theorem interfaces.

## Main definitions

* `CKMA.HasPsiTwoBound`: exponential square integrability at scale `K` (in `Concentration.Basic`).
* `CKMA.psiTwoGauge`: the sub-Gaussian Luxemburg gauge (in `Concentration.Basic`).
* `CKMA.HasGaussianTail`: two-sided Gaussian tail decay (in `Concentration.Basic`).
* `CKMA.HasGaussianMoments`: square-root growth of `L^p` norms (in `Concentration.Basic`).

## Main results

* `CKMA.bernstein`: scalar Bernstein inequality for independent bounded centered summands
  (in `Concentration.Bernstein`).
* `CKMA.HasPsiTwoBound.hasGaussianTail`: exponential square control implies Gaussian tails.
* `CKMA.HasGaussianTail.hasPsiTwoBound`: Gaussian tails imply exponential square control.
* `CKMA.HasPsiTwoBound.hasGaussianMoments`: exponential square control implies moment growth.
* `CKMA.HasGaussianMoments.hasPsiTwoBound`: moment growth implies exponential square control.
* `CKMA.HasPsiTwoBound.hasSubgaussianMGF`: centered exponential square control implies
  sub-Gaussian MGF.
* `CKMA.johnson_lindenstrauss`: Johnson–Lindenstrauss finite-set dimension reduction
  (in `Concentration.JohnsonLindenstrauss`).

The implication theorems are in `Concentration.Basic`.
-/
