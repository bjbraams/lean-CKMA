/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.CStarAlgebra.OperatorClosures.Bicommutant
public import CKMA.Analysis.CStarAlgebra.OperatorClosures.Kaplansky

/-!
# Operator commutants, bicommutants, and Kaplansky density

The commutant and the bicommutant theorem are in
`CKMA.Analysis.CStarAlgebra.OperatorClosures.Bicommutant`. Kaplansky density is in
`CKMA.Analysis.CStarAlgebra.OperatorClosures.Kaplansky`.
Inner products follow Mathlib's convention of linearity in the second variable.
Sources: GAPS 23.21 and 23.22.

The finite-vector strong density of a unital star algebra in its bicommutant is TauCeti's
`StarSubalgebra.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer`, and the
self-adjoint strong closure is
`StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint`. The Kaplansky
function, its difference identity, and the norm bound are `TauCeti.kaplanskyFun`,
`TauCeti.cfc_kaplanskyFun_sub_cfc_kaplanskyFun`, and `TauCeti.norm_cfc_kaplanskyFun_le`.
Nondegeneracy along an increasing approximate unit is
`NonUnitalStarAlgHom.isNondegenerate_iff_tendsto`.

## Main definitions

* `CKMA.boundedOperatorCommutant`: commutant of a set of bounded Hilbert-space operators.
* `CKMA.IsStrongOperatorApproximable`: strong-operator closure criterion on finite vector tuples.
* `CKMA.IsWeakOperatorApproximable`: weak-operator closure criterion on finite matrix coefficients.

## Main results

* `CKMA.bicommutant_closures`: von Neumann bicommutant theorem (**23.21**).
* `CKMA.kaplansky_density`, `CKMA.kaplansky_density_selfAdjoint`: Kaplansky density theorem
  (**23.22**).
-/
