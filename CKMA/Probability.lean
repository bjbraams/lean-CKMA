/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.BrownianQuadraticVariation
public import CKMA.Probability.BrownianTheory
public import CKMA.Probability.Concentration
public import CKMA.Probability.GaussianLogSobolev
public import CKMA.Probability.HansonWright
public import CKMA.Probability.InfinitelyDivisible
public import CKMA.Probability.LargeDeviations
public import CKMA.Probability.LimitTheorems.IndependentSums
public import CKMA.Probability.LimitTheorems.LargeDeviations
public import CKMA.Probability.Moments.Hausdorff
public import CKMA.Probability.ProjectiveLimit
public import CKMA.Probability.Symmetrization

/-!
# Probability and stochastic processes

This entry module re-exports random-series and central-limit interfaces, concentration
and dimension reduction, large deviations, moment problems and projective limits.
Brownian motion is treated through continuous-path laws, modifications, stopping times
and quadratic variation. Empirical symmetrization uses an explicit independent sign space.

Extended nonnegative gauges and logarithms retain infinite values; probability and
integrability hypotheses are stated at the relevant theorem interfaces.
-/
