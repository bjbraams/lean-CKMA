/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.LimitTheorems.BerryEsseen
public import CKMA.Probability.LimitTheorems.IteratedLogarithm
public import CKMA.Probability.LimitTheorems.LindebergFeller
public import CKMA.Probability.LimitTheorems.ThreeSeries

/-!
# Limit theorems for sums of independent random variables (06.23, 06.27, 06.34, 06.36)

Index of the limit theorems for independent sums.

* `CKMA.Probability.LimitTheorems.ThreeSeries`: `CKMA.kolmogorov_threeSeries`, Kolmogorov's
  three-series theorem with ordered convergence of the series (**06.23**).
* `CKMA.Probability.LimitTheorems.IteratedLogarithm`: `CKMA.hartman_wintner`, the
  Hartman–Wintner law of the iterated logarithm (**06.27**).
* `CKMA.Probability.LimitTheorems.LindebergFeller`: `CKMA.lindeberg_feller` and
  `CKMA.lindeberg_feller_iff`, the Lindeberg–Feller theorem and its converse under Feller's
  condition (**06.34**).
* `CKMA.Probability.LimitTheorems.BerryEsseen`: `CKMA.berry_esseen`, the Berry–Esseen theorem
  in Kolmogorov distance (**06.36**).

Row second-moment sums in the Lindeberg–Feller theorem are uncentered; they are variances under
the centering hypothesis of the limit theorems.
-/
