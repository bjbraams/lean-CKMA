/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.LargeDeviations.Basic
public import CKMA.Probability.LargeDeviations.Cramer
public import CKMA.Probability.LargeDeviations.Sanov
public import CKMA.Probability.LargeDeviations.Varadhan

/-!
# Large deviations

Entry module for large deviations at speed `n + 1`. Rate functions and large deviation
principles are TauCeti's `TauCeti.Probability.IsGoodRateFunction` and
`TauCeti.Probability.HasLDP`.

* `CKMA.Probability.LargeDeviations.Basic`: `logProbabilityRate`, the bounds
  `HasLargeDeviationBounds` and their relation to `HasLDP`.
* `CKMA.Probability.LargeDeviations.CramerLowerBound`: the Cramér lower bound for balls.
* `CKMA.Probability.LargeDeviations.Cramer`: Cramér's theorem (**06.60**).
* `CKMA.Probability.LargeDeviations.Sanov`: Sanov's theorem (**06.61**).
* `CKMA.Probability.LargeDeviations.Varadhan`: Varadhan's lemma for bounded continuous
  functions (**06.62**).
-/
