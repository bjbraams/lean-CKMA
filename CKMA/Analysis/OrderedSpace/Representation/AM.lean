/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.OrderedSpace.Representation.AM.Norm
public import CKMA.Analysis.OrderedSpace.Representation.AM.State

/-!
# Kakutani representation of an AM space with unit

An AM unit identifies the closed norm ball with an order interval. The weak-star state space
and its lattice-homomorphic extreme points are in
`CKMA.Analysis.OrderedSpace.Representation.AM.State`. Norm recovery and the representation as
`C(K, ℝ)` are in `CKMA.Analysis.OrderedSpace.Representation.AM.Norm`.
The zero space is represented by the empty compact carrier.
The argument follows Schaefer, *Banach Lattices and Positive Operators*, Proposition II.4.4 and
Theorem II.7.4.

## Main definitions

* `CKMA.amStateSet`: weak-star set of positive functionals normalized at the AM unit.
* `CKMA.amLatticeHomSet`: weak-star set of lattice-homomorphic functionals normalized at the
  AM unit.

## Main results

* `CKMA.isCompact_amStateSet`: the state set is weak-star compact.
* `CKMA.extremePoints_subset_amLatticeHomSet`: extreme points of `amStateSet e` are normalized
  lattice homomorphisms.
* `CKMA.isCompact_amLatticeHomSet`: the normalized lattice homomorphisms form a weak-star
  compact set.
* `CKMA.IsAMSpaceUnit.isAMSpace`: an AM unit forces the AM norm identity.
* `CKMA.exists_amSpace_representation`: Kakutani representation of an AM Banach lattice with
  unit.
-/
