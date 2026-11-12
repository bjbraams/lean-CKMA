/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Complex.Linearization
public import CKMA.Dynamics.Complex.Linearization.Boettcher
public import CKMA.Dynamics.Complex.Linearization.Koenigs
public import CKMA.Dynamics.Complex.PolynomialJulia
public import CKMA.Dynamics.Ergodic.Pointwise
public import CKMA.Dynamics.Ergodic.Pointwise.Birkhoff
public import CKMA.Dynamics.Ergodic.Pointwise.BirkhoffLimit
public import CKMA.Dynamics.Ergodic.Pointwise.BirkhoffShift
public import CKMA.Dynamics.Ergodic.Pointwise.Kingman
public import CKMA.Dynamics.Ergodic.Pointwise.KingmanAE
public import CKMA.Dynamics.Ergodic.Pointwise.KingmanClosure
public import CKMA.Dynamics.Ergodic.Pointwise.KingmanConv
public import CKMA.Dynamics.Ergodic.Pointwise.KingmanFull
public import CKMA.Dynamics.Ergodic.Pointwise.KingmanLimit
public import CKMA.Dynamics.Ergodic.Pointwise.KingmanOrbit
public import CKMA.Dynamics.Ergodic.Pointwise.Maximal
public import CKMA.Dynamics.Ergodic.Recurrence
public import CKMA.Dynamics.Ergodic.Recurrence.Multiple
public import CKMA.Dynamics.Flow
public import CKMA.Dynamics.IteratedFunctionSystem
public import CKMA.Dynamics.Lyapunov
public import CKMA.Dynamics.ODE.Planar
public import CKMA.Dynamics.ODE.Planar.Basic
public import CKMA.Dynamics.ODE.Planar.Bendixson
public import CKMA.Dynamics.ODE.Planar.Transversal
public import CKMA.Dynamics.Orbit

/-!
# Complex, ergodic and differential dynamics

This entry module re-exports bounded-orbit and flow interfaces, local complex conjugacies,
polynomial Julia sets, pointwise and subadditive ergodic theory, recurrence and self-similar
systems. Lyapunov and LaSalle criteria and the planar periodic-orbit theorem are formulated
for existing global flows, with their generator relation explicit.

Ergodic statements use probability-preserving transformations; the complex branch uses
Mathlib's polynomial, derivative and iteration conventions.
-/
