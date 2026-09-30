# 50. Asymptotic Analysis, Resurgence, and Perturbation

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Some roots below are directory prefixes; the individual `.lean` files cited are the importable modules. The roots for this section are `Mathlib.Analysis.Asymptotics.Defs`, `Mathlib.Analysis.Asymptotics.AsymptoticEquivalent`, `Mathlib.Analysis.Asymptotics.Theta`, `Mathlib.Analysis.Asymptotics.ExpGrowth`, `Mathlib.Analysis.Asymptotics.SuperpolynomialDecay`, `Mathlib.Analysis.Asymptotics.SpecificAsymptotics`, and `Mathlib.Tactic.ComputeAsymptotics`.

**Namespaces.** `Asymptotics` for the Landau relations, with the notation \(f=O[l]g\), \(f=\Theta[l]g\), \(f=o[l]g\), and \(f\sim[l]g\). Exponential growth of a sequence is `ExpGrowth`. The multiseries used by the asymptotics procedure sit in `Tactic.ComputeAsymptotics`. There is no namespace for resurgence.

The library has Landau’s notation along an arbitrary filter, together with a tactic layer that reduces asymptotic goals to limits at infinity and manipulates real multiseries. It does not have a theory of divergent series.

## Little-o, big-O, and equivalence

The relations are indexed by a filter \(l\) on the common domain. They are not restricted to \(x\to\infty\). For normed codomains, \(f\) is big-O of \(g\) along \(l\) with constant \(c\), written as the relation `IsBigOWith`, when \(\|f(x)\|\leq c\,\|g(x)\|\) holds for all \(x\) in some set belonging to \(l\). Then \(f=O[l]g\) means that some real constant \(c\) works. One writes \(f=\Theta[l]g\) when each of \(f\) and \(g\) is big-O of the other along \(l\), and \(f=o[l]g\) when every positive constant works (`Analysis/Asymptotics/Defs.lean`).

Asymptotic equivalence \(f\sim[l]g\) means \((f-g)=o[l]g\) (`Analysis/Asymptotics/AsymptoticEquivalent.lean`). It is an equivalence relation. When the codomain is a normed field and \(g\) is eventually nonvanishing, equivalence is the same as \(f/g\to 1\) along \(l\). More generally, over a normed field, \(f\sim[l]g\) if and only if \(f=\varphi g\) eventually, for some \(\varphi\to 1\) along \(l\).

The same relations specialise to the usual filters: a neighbourhood of a point, a punctured neighbourhood, `atTop`, and the filter of cobounded sets. Concrete comparisons are collected separately. A function bounded in a punctured neighbourhood of \(a\) is little-o of \((x-a)^{-1}\) there. On a normed ring, \(x\mapsto x^p\) is little-o of \(x\mapsto x^q\) along the cobounded filter whenever \(p<q\), and the same comparison holds at \(+\infty\) in a normed ordered field (`Analysis/Asymptotics/SpecificAsymptotics.lean`).

Exponential growth of a sequence \(u:\mathbb{N}\to[0,\infty]\) is the extended-real \(\liminf\) or \(\limsup\) of \((\log u_n)/n\) (`Analysis/Asymptotics/ExpGrowth.lean`). Superpolynomial decay of \(f\) relative to a parameter \(k\), along a filter \(l\), means that \(k^n f\to 0\) along \(l\) for every natural number \(n\). This is equivalent to \(f\) being little-o, and also big-O, of every integer power of \(k\) (`Analysis/Asymptotics/SuperpolynomialDecay.lean`).

## Taylor remainders and Stirling asymptotics

The calculus library proves Taylor approximation in little-o form and Taylor’s theorem with Lagrange, Cauchy, and integral remainders. There are vector-valued remainder bounds as well (`Analysis/Calculus/Taylor.lean`). An integral remainder formula using iterated Fréchet derivatives also applies along segments in normed spaces (`Analysis/Calculus/TaylorIntegral.lean`). These are finite-order asymptotic expansions with controlled remainders.

A concrete large-parameter asymptotic theorem is Stirling’s formula \(n!\sim\sqrt{2\pi n}(n/e)^n\), together with a lower bound and a stepwise logarithmic error estimate (`Analysis/SpecialFunctions/Stirling.lean`; see Section 49). Thus the coverage includes proved asymptotic formulae as well as notation and tactic infrastructure. A general stationary-phase, steepest-descent, or Laplace-method theorem was not found.

## Summation, Abelian and Tauberian theorems

Abel's summation formula, the discrete integration by parts that converts asymptotics of partial sums into asymptotics of weighted sums, is proved in several forms (`NumberTheory/AbelSummation.lean`). Abel's limit theorem, the prototype Abelian theorem, is recorded in Section 40 (`Analysis/Complex/AbelLimit.lean`). No Euler–Maclaurin formula with remainder, and no general Tauberian theorem of Hardy–Littlewood or Karamata type, was found in Mathlib.

## The asymptotics procedure

`Mathlib.Tactic.ComputeAsymptotics` is a directory of support lemmas, not a resurgence theory. The lemmas reduce goals of the form “a limit along a one-sided or punctured neighbourhood”, and goals of big-O, little-o, and equivalence, to a limit along `atTop` (`Tactic/ComputeAsymptotics/Lemmas.lean`). The accompanying multiseries are lazy series of real monomials in a chosen basis of functions \(\mathbb{R}\to\mathbb{R}\), nested so that a series in \(b_1,\ldots,b_n\) is a series in \(b_1\) whose coefficients are series in the remaining basis. A coinductive predicate says that such a series approximates its attached function at \(+\infty\), after a trimming condition that isolates the leading monomial (`Tactic/ComputeAsymptotics/Multiseries/Defs.lean`). No syntax declaration of a tactic named `compute_asymptotics` appears in the library; the file describes the procedure those lemmas serve.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

There is concrete perturbation theory for operators. A bounded perturbation of a strongly continuous semigroup generator again generates a semigroup on the same domain, with growth bound \(M\exp((\omega+M\|B\|)t)\) when the original bound is \(M e^{\omega t}\) ([bounded perturbation theorem](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Semigroups/Generation/BoundedPerturbation.lean)). Fredholmness and index are stable under sufficiently small operator-norm perturbations and under compact perturbations ([small perturbations](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Fredholm/SmallPerturbation.lean), [compact perturbations](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Fredholm/CompactPerturbation.lean)).

These remove the blanket absence of operator perturbation theory.

On the Tauberian side, TauCeti proves the Wiener–Ikehara theorem: for nonnegative coefficients whose Dirichlet series minus \(\kappa/(s-1)\) extends continuously to \(\operatorname{Re}s\ge1\), the averages \(x^{-1}\sum_{n\le x}a_n\) tend to \(\kappa\) ([Wiener–Ikehara](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/NumberTheory/LSeries/WienerIkehara/SharpCutoff.lean); see Section 27). It also proves \(\operatorname{Li}(x)\sim x/\log x\) for the logarithmic integral (Section 49). No resurgence, Gevrey/Borel summation, WKB expansion, or singular-perturbation theory was located.

## Topics of Section 50 not found in either inspected library

- Resurgence, Borel summation, and Gevrey classes. The Borel \(\sigma\)-algebra is unrelated.
- The Laplace method, Watson's lemma, the method of steepest descent, and stationary phase as general theorems; the Euler–Maclaurin formula; Hardy–Littlewood and Karamata Tauberian theorems and regular variation.
- Transseries, and Poincaré asymptotics in the sense of a divergent series admitted by a holomorphic function in a sector.
- Singular perturbations and asymptotic perturbation expansions for differential equations, beyond the semigroup and Fredholm operator perturbation theorems described above.
