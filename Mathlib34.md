# 34. Hyperbolic Equations, Conservation Laws, Dispersive PDE, Fluids, and Kinetic Theory

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. There is no import root for this subject. The divergence theorem on rectangular boxes, in `Mathlib.MeasureTheory.Integral.DivergenceTheorem` and `Mathlib.Analysis.BoxIntegral.DivergenceTheorem`, is the nearest integral identity, and it is recorded in section 32. It is not a conservation law.

**Namespaces.** None for this subject.

No wave equation, conservation law, shock, Burgers equation, Navier–Stokes or Euler equation, Boltzmann equation, kinetic equation, dispersive estimate, Strichartz estimate, or KdV equation is formalized in this checkout.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

No implemented theory of the wave equation, nonlinear conservation laws, dispersive equations, fluid equations, or kinetic equations was located. TauCeti does add general Banach-space semigroup generation and unique mild/classical solutions of an autonomous abstract Cauchy problem ([source](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Semigroups/CauchyProblem/Basic.lean); Section 24). The abstract theorem requires an identified generator; it does not, by itself, formalize any of the particular equations or propagation/dispersion estimates of this section.

## Topics of Section 34 not found in either inspected library

- Hyperbolic equations and finite propagation speed.
- Conservation laws, entropy solutions, shocks, and the Burgers equation.
- The Euler and Navier–Stokes equations.
- Dispersive equations, Strichartz estimates, and KdV.
- Kinetic theory, including the Boltzmann equation.
