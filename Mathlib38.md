# 38. Potential Theory and Capacity

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. There is no import root for this subject. The nearest constructions are the Poisson integral of section 33, in `Mathlib.Analysis.Complex.Poisson` and `Mathlib.Analysis.Complex.Harmonic.Poisson`, and the Bessel potential spaces of section 26, in `Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace`.

**Namespaces.** None for capacity or potential theory. The Poisson kernel is defined in the root namespace of its file, and the harmonic Poisson formula is `InnerProductSpace`.

The Poisson integral on a disk in the complex plane is the formula of section 33: circle averages against the Poisson kernel recover holomorphic functions and real-valued harmonic functions inside the disk. It is not developed as potential theory.

Bessel potential spaces are the Fourier-theoretic Sobolev spaces of section 26. No capacity is defined from them.

No capacity, Newtonian potential, equilibrium measure, fine topology, or thinness in the potential-theoretic sense was found.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti constructs the Euclidean Newtonian kernel and proves its fundamental-solution identity for \(-\Delta\) in dimension \(n\ge3\): for compactly supported \(C^2\) test functions, \(\int G_n\Delta\varphi=-\varphi(0)\), including translated poles ([distributional identity](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/FundamentalSolution/Euclidean/DistributionalLaplacian.lean)). There is a separate logarithmic planar kernel ([planar kernel](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/FundamentalSolution/Planar.lean)). Green kernels for balls/discs are constructed, with boundary vanishing and the normal-derivative relation to the Poisson kernel ([Euclidean ball](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/GreenFunction/Ball.lean), [planar disk](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/GreenFunction/Disk.lean), [planar Poisson relation](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/GreenFunction/Poisson.lean)).

Nonnegative harmonic functions satisfy Harnack comparison on compact subsets of a connected open set in any finite dimension ([Harnack theorem](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/Harnack/Basic.lean)). This fills some classical potential-theory coverage, but no capacity, fine-topology, equilibrium-measure, or general Riesz-potential mapping theory was located.

## Topics of Section 38 not found in either inspected library

- Capacities, including Bessel capacity and Sobolev capacity.
- A general Newtonian/Riesz potential-operator theory with mapping and regularity estimates. The Newtonian fundamental kernel and ball Green kernels are present in TauCeti.
- Equilibrium measures, and the fine topology and thin sets.
