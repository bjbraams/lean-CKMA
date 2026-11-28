/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.OrderedSpace.Representation.AL.Gluing.Sum
public import CKMA.Analysis.OrderedSpace.Representation.AM

/-!
# AM and AL Banach lattices and their representations

AM spaces have the maximum norm identity on the positive cone; an AM unit identifies the norm
unit ball with its order interval. AL spaces have additive norm on the positive cone, and the
KB property concerns convergence of increasing norm-bounded positive sequences. The predicates
are defined in `CKMA.Analysis.OrderedSpace.Representation.Basic`.

Kakutani representation identifies AM spaces with unit with continuous real functions on a
compact Hausdorff space and AL spaces with real L¹ spaces. The empty compact space represents
the zero space; no σ-finiteness restriction is imposed on the general AL representation.
Sources: GAPS 19.27 and 19.29.

## Main definitions

* `CKMA.IsAMSpace`: normed lattice with `‖x ⊔ y‖ = max ‖x‖ ‖y‖` on the positive cone.
* `CKMA.IsAMSpaceUnit`: positive unit whose order interval is the closed norm unit ball.
* `CKMA.IsALSpace`: normed lattice with `‖x + y‖ = ‖x‖ + ‖y‖` on the positive cone.
* `CKMA.IsKBSpace`: norm convergence of bounded monotone positive sequences.
* `CKMA.IsWeakUnit`: positive vector with zero disjoint complement.

## Main results

* `CKMA.IsAMSpaceUnit.isAMSpace`: an AM unit forces the AM norm identity.
* `CKMA.exists_amSpace_representation`: Kakutani representation of an AM space with unit as
  `C(K, ℝ)` (`Representation.AM.Norm`).
* `CKMA.exists_al_representation_of_weakUnit`: an AL space with a weak unit is an `L¹` space
  (`Representation.AL`).
* `CKMA.exists_alSpace_representation`: Kakutani representation of an AL space as `L¹(μ)`
  (`Representation.AL.Gluing.Sum`).
* `CKMA.IsALSpace.isKBSpace`: every complete AL space is a KB space (`Representation.AL`).
-/
