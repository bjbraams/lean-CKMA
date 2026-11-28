/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Convex.Duality.Choquet
public import CKMA.Analysis.Convex.Duality.FenchelRockafellar
public import CKMA.Analysis.Convex.Duality.KKT
public import CKMA.Analysis.Convex.Duality.Subdifferential
public import CKMA.Analysis.Convex.Duality.Sum
public import CKMA.Analysis.Convex.Duality.SumIntrinsic

/-!
# Choquet measures, convex duality, and multiplier conditions

This entry module collects the duality files. Choquet representation uses probability measures
on a compact metrizable convex set, carried by its extreme points, and tests barycenters by
continuous affine scalar functions. Subdifferentials and Fenchel conjugates are TauCeti's, for
the continuous-dual pairing `(topDualPairing ℝ E).flip`. Extended-real properness and
finite-domain continuity hypotheses control the sum rule and Fenchel–Rockafellar dual
attainment; in finite dimensions, meeting relative interiors of the domains is an alternative
qualification for the sum rule. The finite-dimensional KKT interface separates feasibility from
nonnegative multipliers, stationarity, and complementary slackness; sufficiency holds in any
normed space. Sources: GAPS 12.9, 12.21, 12.39, and 12.40.

## Main results

* `CKMA.exists_choquetMeasure` (`Duality/Choquet`): Choquet representation on compact
  metrizable convex sets (**12.9**).
* `CKMA.subdifferential_add_eq` (`Duality/Sum`): the sum rule with a common finite-domain
  continuity point (**12.21**).
* `CKMA.subdifferential_add_eq_of_intrinsicInterior` (`Duality/SumIntrinsic`): the
  finite-dimensional sum rule under the relative-interior qualification (**12.21**).
* `CKMA.exists_fenchelDual_maximizer` (`Duality/FenchelRockafellar`): Fenchel–Rockafellar
  strong duality and dual attainment (**12.39**).
* `CKMA.exists_convexKKTMultipliers` (`Duality/KKT`): KKT multipliers under Slater's condition
  (**12.40**), and `CKMA.HasConvexKKTMultipliers.isMinOn`, sufficiency of the KKT conditions.
-/
