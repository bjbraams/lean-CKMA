/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.SpecialFunctions.Classical.GammaMultiplication
public import CKMA.Analysis.SpecialFunctions.Classical.Hypergeometric
public import CKMA.Analysis.SpecialFunctions.Classical.BesselGenerating

/-!
# Gamma multiplication, Gauss's equation and Bessel generating series

Gauss multiplication relates a finite product of shifted Gamma values to a single
Gamma value at the multiplied argument. The hypergeometric series solves Gauss's
equation and is the unique normalized analytic solution germ; the three singular
points are regular singular, as witnessed by analytic rational germs in local and
reciprocal coordinates. The bilateral integer-order Bessel generating series
converges normally away from its auxiliary variable's origin.

Gauss multiplication and Gauss's equation for the ordinary series are TauCeti's
`Complex.prod_Gamma_add_div` and `TauCeti.ordinaryHypergeometric_gaussEquation_of_norm_lt_one`;
the regularized equation holds for every denominator parameter.

## Main definitions

* `CKMA.gaussDifferentialExpression`: Gauss's hypergeometric differential expression.
* `CKMA.IsRegularSingularAt`: the regular-singular criterion for `y'' + P y' + Q y = 0` at a finite
  point.
* `CKMA.IsRegularSingularAtInfinity`: the regular-singular criterion at infinity after `z = 1 / w`.

## Main results

* `CKMA.gamma_multiplication`: Gauss's multiplication formula for every complex parameter
  (**49.6**).
* `CKMA.gauss_regularized_hypergeometric_ode`: the regularized function solves Gauss's equation in
  the unit disk for all parameters.
* `CKMA.gauss_hypergeometric_ode`: the ordinary hypergeometric series solves Gauss's equation in
  the unit disk (**49.13**).
* `CKMA.gauss_hypergeometric_unique`: uniqueness of the normalized analytic solution germ at `0`.
* `CKMA.gauss_isRegularSingularAt`: `0`, `1`, and `∞` are regular singular points of Gauss's
  equation.
* `CKMA.hasSum_bessel_generating`: the bilateral Bessel generating series identity (**49.30**).
* `CKMA.normallySummableOn_besselJ_mul_zpow`: normal convergence on compact subsets of
  `ℂ × (ℂ \ {0})`.

Sources: GAPS 49.6, 49.13 and 49.30. Special functions and branches reuse Mathlib and TauCeti.
-/
