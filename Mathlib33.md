# 33. Elliptic and Parabolic Equations: Regularity, Free Boundaries, and Viscosity Solutions

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The roots for this section are `Mathlib.Analysis.InnerProductSpace.Laplacian`, `Mathlib.Analysis.InnerProductSpace.Harmonic.Basic`, `Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions`, `Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl`, `Mathlib.Analysis.Complex.Harmonic.Analytic`, `Mathlib.Analysis.Complex.Harmonic.MeanValue`, `Mathlib.Analysis.Complex.Harmonic.Liouville`, `Mathlib.Analysis.Complex.Harmonic.Poisson`, `Mathlib.Analysis.Complex.Poisson`, and `Mathlib.Analysis.InnerProductSpace.LaxMilgram`.

**Namespaces.** The Laplacian, harmonicity, and the mean-value and Poisson theorems for harmonic functions are `InnerProductSpace`, with the predicates `HarmonicAt`, `HarmonicOnNhd`, and `HarmonicContOnCl`. The notation for the Laplacian is opened from `Laplacian`. The Lax–Milgram equivalence is `IsCoercive`.

What is proved is the Euclidean Laplacian, the elementary calculus of harmonic functions, and the mean-value, Liouville, and Poisson theorems on disks in the complex plane. Elliptic regularity is not present.

## The Laplacian and harmonic functions

On a finite-dimensional real inner product space \(E\), with values in a real normed space \(F\), the Laplacian of \(f:E\to F\) is the second derivative contracted against the canonical covariant tensor of \(E\). Equivalently, for any orthonormal basis \((e_i)\),
\[
\Delta f(x)=\sum_i D^2f(x)(e_i,e_i),
\]
and on \(\mathbb{R}\) this is the ordinary second derivative. The same contraction within a set of differentiability defines \(\Delta[s]\), and it agrees with \(\Delta\) when the set is everything. On functions of class \(C^2\), the Laplacian is real-linear (`Analysis/InnerProductSpace/Laplacian.lean`).

A function is harmonic at a point when it is of class \(C^2\) there and its Laplacian vanishes on a neighborhood of the point. It is harmonic on a neighborhood of a set when it is harmonic at every point of the set. Harmonicity is local, and it is preserved by addition, scalar multiplication, and post-composition with a continuous real-linear map. Constant functions are harmonic. The set of points of harmonicity is open (`Analysis/InnerProductSpace/Harmonic/Basic.lean`).

A function is said to be harmonic on a set and continuous on its closure when both of those hold. On a closed set the second clause follows from harmonicity on the set. The predicate is stable under addition, subtraction, real scalar multiplication, and continuous real-linear post-composition, and it passes to subsets (`Analysis/InnerProductSpace/Harmonic/HarmonicContOnCl.lean`).

On the complex plane, a map that is of class \(C^2\) over \(\mathbb{C}\) at a point is harmonic there over \(\mathbb{R}\). A map into a complete complex normed space that is complex-analytic at a point is harmonic there. The real part, the imaginary part, and the complex conjugate of a function \(\mathbb{C}\to\mathbb{C}\) are harmonic at a point of complex analyticity, and so is \(\log\|f\|\) at any point where an analytic \(f:\mathbb{C}\to\mathbb{C}\) does not vanish (`Analysis/InnerProductSpace/Harmonic/Constructions.lean`).

A real-valued function harmonic on a ball in \(\mathbb{C}\) is the real part of a holomorphic function on that ball, and a real-valued function harmonic on the whole plane is the real part of an entire function. A real-valued function harmonic at a point of \(\mathbb{C}\) is real-analytic there. The file records that real-analyticity on a general finite-dimensional inner product space, rather than only on \(\mathbb{C}\), is not proved (`Analysis/Complex/Harmonic/Analytic.lean`).

## Mean value, Liouville, and the Poisson integral

The mean-value property is a theorem about circle averages on disks in \(\mathbb{C}\), not about ball averages in a general Euclidean space. Let \(F\) be a complete real normed space. If \(f:\mathbb{C}\to F\) is harmonic on a neighborhood of the closed disk of radius \(|R|\) about \(c\), the circle average of \(f\) on the circle of radius \(R\) about \(c\) equals \(f(c)\). If instead \(f\) is harmonic on the open disk and continuous up to the closure, the same equality holds (`Analysis/Complex/Harmonic/MeanValue.lean`). Completeness of \(F\) is required because the circle average is a Bochner integral. The proof reduces to the real-valued case by continuous linear functionals.

Liouville’s theorem: a harmonic map \(f:\mathbb{C}\to E\) into a real normed space, defined and harmonic on the whole plane, with bounded image, is constant (`Analysis/Complex/Harmonic/Liouville.lean`).

The Poisson kernel of a disk of center \(c\), at an interior point \(w\) and a boundary point \(z\), is
\[
P_c(w,z)=\frac{\|z-c\|^2-\|w-c\|^2}{\|(z-c)-(w-c)\|^2}.
\]
On the circle it agrees with the real part of the Herglotz–Riesz kernel \((z-c+(w-c))/(z-c-(w-c))\) (`Analysis/Complex/Poisson.lean`). For a complex-differentiable map from a disk into a complete complex normed space, continuous up to the closure, the circle average of the Poisson kernel against the map recovers the value at any interior point. The same formula holds with the real part of the Herglotz–Riesz kernel in place of the Poisson kernel.

For real-valued harmonic functions the same identities are theorems, not only for holomorphic functions. If \(f:\mathbb{C}\to\mathbb{R}\) is harmonic on a neighborhood of the closed disk of radius \(R>0\) about \(c\), or harmonic on the open disk and continuous on its closure, and if \(w\) lies in the open disk, then the circle average of \(z\mapsto P_c(w,z)\,f(z)\) equals \(f(w)\), and likewise with the real part of the Herglotz–Riesz kernel (`Analysis/Complex/Harmonic/Poisson.lean`). The vector-valued harmonic case of the Poisson formula is marked as not yet proved. No Poisson integral over a Euclidean ball, a half-space, or the sphere in dimension greater than two was found.

## Lax–Milgram

The same statement as in section 32 is the only existence theorem near a linear elliptic variational problem. On a real Hilbert space, a continuous bilinear form \(B\) that is coercive, meaning \(C\|u\|^2\le B(u,u)\) for some \(C>0\) and every \(u\), induces a continuous linear automorphism \(v\mapsto B^\sharp v\) characterized by \(\langle B^\sharp v,w\rangle=B(v,w)\) (`Analysis/InnerProductSpace/LaxMilgram.lean`). Equivalently, for each continuous linear functional \(\ell\), the equation \(B(u,w)=\ell(w)\) for all \(w\) has a unique solution \(u\), depending continuously and linearly on \(\ell\). It is not a regularity theorem, and it is not specialized to any differential operator.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

Existence and uniqueness for coercive divergence-form weak Dirichlet problems, the compact solution operator on bounded domains, and the symmetric Dirichlet spectral theorem are implemented (Section 32; [Dirichlet existence](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/DirichletProblem.lean), [spectral theorem](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/Spectrum.lean)). Interior \(H^2\) regularity holds for a constant uniformly elliptic principal matrix with bounded measurable lower-order coefficients and \(L^2\) right-hand side ([regularity](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/Regularity/Interior.lean)). It should not be extended in this description to arbitrary measurable principal coefficients or to Schauder estimates.

The mean-value property over Euclidean balls is proved in arbitrary finite dimension ([mean value](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/InnerProductSpace/Harmonic/MeanValue.lean)). For nonnegative harmonic functions, TauCeti proves a local Harnack estimate and uniform comparison on compact subsets of a connected open domain ([Harnack](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/Harnack/Basic.lean)). It also proves Hopf's boundary-point lemma under the stated ball and differentiability hypotheses, and a strong maximum principle for the Laplacian ([Hopf lemma](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/InnerProductSpace/Laplacian/HopfLemma.lean), [strong maximum principle](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/InnerProductSpace/Laplacian/StrongMaximumPrinciple.lean)). These are harmonic/classical elliptic results; a De Giorgi–Nash–Moser theorem for measurable variable principal coefficients was not located.

For measurable uniformly elliptic principal coefficients, Caccioppoli interior energy inequalities are proved both for weak solutions and for positive-part truncations of weak subsolutions ([energy estimate](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/Caccioppoli/Basic.lean), [truncations](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/Caccioppoli/Truncation.lean)). Coercive divergence-form equations also have weak maximum and comparison principles, expressing nonpositive boundary data by membership of the positive part in \(H^1_0\), without a trace theorem ([weak maximum principle](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/MaximumPrinciple/Weak.lean)). These energy and order estimates do not complete De Giorgi iteration.

## Topics of Section 33 not found in either inspected library

- Schauder estimates and the De Giorgi–Nash–Moser theory for variable-coefficient equations. Harnack inequalities for harmonic functions are present in TauCeti.
- Viscosity solutions, free boundaries, parabolic equations, and the heat equation.
- Real-analyticity of harmonic functions in arbitrary finite dimension. Mean-value properties on Euclidean balls and spheres are proved in TauCeti.
- General elliptic boundary regularity and existence outside the coercive variational/Fredholm frameworks described above.
