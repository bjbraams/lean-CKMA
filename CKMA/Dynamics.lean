/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Complex.EscapingSet
public import CKMA.Dynamics.Complex.Linearization
public import CKMA.Dynamics.Complex.Linearization.Boettcher
public import CKMA.Dynamics.Complex.Linearization.Koenigs
public import CKMA.Dynamics.Complex.Mandelbrot
public import CKMA.Dynamics.Complex.PolynomialJulia
public import CKMA.Dynamics.Ergodic.Pointwise
public import CKMA.Dynamics.Ergodic.Pointwise.Birkhoff
public import CKMA.Dynamics.Ergodic.Pointwise.BirkhoffLimit
public import CKMA.Dynamics.Ergodic.Pointwise.BirkhoffShift
public import CKMA.Dynamics.Ergodic.Pointwise.Kingman.Defs
public import CKMA.Dynamics.Ergodic.Pointwise.Kingman.Fekete
public import CKMA.Dynamics.Ergodic.Pointwise.Kingman.Liminf
public import CKMA.Dynamics.Ergodic.Pointwise.Kingman.LiminfMean
public import CKMA.Dynamics.Ergodic.Pointwise.Kingman.LinearBound
public import CKMA.Dynamics.Ergodic.Pointwise.Kingman.MeasurableProcess
public import CKMA.Dynamics.Ergodic.Pointwise.Kingman.Orbit
public import CKMA.Dynamics.Ergodic.Pointwise.Kingman.Truncation
public import CKMA.Dynamics.Ergodic.Pointwise.Maximal
public import CKMA.Dynamics.Ergodic.Recurrence
public import CKMA.Dynamics.Ergodic.Recurrence.Combinatorics
public import CKMA.Dynamics.Ergodic.Recurrence.Multiple
public import CKMA.Dynamics.Flow.Basic
public import CKMA.Dynamics.IteratedFunctionSystem
public import CKMA.Dynamics.Lyapunov
public import CKMA.Dynamics.ODE.Planar
public import CKMA.Dynamics.ODE.Planar.Basic
public import CKMA.Dynamics.ODE.Planar.Bendixson
public import CKMA.Dynamics.ODE.Planar.Transversal
public import CKMA.Dynamics.Orbit.Basic

/-!
# Complex, ergodic and differential dynamics

This entry module re-exports bounded-orbit and flow interfaces, local complex conjugacies,
polynomial Julia sets, the Mandelbrot set, escaping sets of entire functions, pointwise and
subadditive ergodic theory, recurrence and self-similar systems. Lyapunov and LaSalle criteria
and the planar periodic-orbit theorem are formulated for existing global flows, with their
generator relation explicit.

Ergodic statements use probability-preserving transformations; the complex branch uses
Mathlib's polynomial, derivative and iteration conventions.
-/
