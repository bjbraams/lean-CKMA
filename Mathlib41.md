# 41. Classical Function Theory: Entire and Meromorphic Functions, Value Distribution

Checked against Mathlib commit `f039e1b8a616d45782a5c7fc5e7909249c36b8ea` (2026-10-18, Lean `v4.36.0-rc1`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The roots for this section are `Mathlib.Analysis.Complex.JensenFormula`, `Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic`, `Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic`, `Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Asymptotic`, `Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Truncated`, `Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction`, `Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem`, `Mathlib.Analysis.Complex.ValueDistribution.Cartan`, `Mathlib.Analysis.Complex.ValueDistribution.Proximity.IntegralPresentation`, `Mathlib.Analysis.Complex.ValueDistribution.SecondMainTheorem`, and `Mathlib.Analysis.Complex.CanonicalDecomposition`.

**Namespaces.** `ValueDistribution`, with nested `Cartan` for the kernel used in the integral form of the proximity function. The counting function of a locally finite divisor, before it is specialized to a meromorphic function, is `Function.locallyFinsuppWithin`. Jensen’s formula is `MeromorphicOn` and `AnalyticOnNhd`. The separation lemma sits in `Real` but is stated for a finite subset of any normed field. Canonical factors are `Complex`.

This note records Jensen’s formula and the part of Nevanlinna theory that is proved: the proximity function, the logarithmic counting function, the truncated counting function, the characteristic, Cartan’s formula, and the first main theorem in the form of invariance under inversion, under translation, and more generally under Möbius transformations. The second main theorem is not claimed.

## Jensen’s formula

Liouville’s theorem and the fundamental theorem of algebra are in Section 40. They are the elementary facts about entire functions in this checkout. Jensen’s formula is the bridge from the meromorphic calculus of that section to value distribution.

If \(f:\mathbb{C}\to\mathbb{C}\) is meromorphic on the closed disc of center \(c\) and radius \(|R|\), and \(R\neq 0\), the circle average of \(\log\|f\|\) equals the logarithm of the norm of the trailing coefficient of \(f\) at \(c\), plus a correction from the zeros and poles. With \(D\) the divisor of \(f\) on that closed disc,
\[
\operatorname{circleAverage}(\log\|f\|,c,R)
= \sum_u D(u)\log\bigl(R\,\|c-u\|^{-1}\bigr) + D(c)\log R + \log\|\text{trailing coefficient of }f\text{ at }c\|.
\]
The sum is finite. The term \(D(c)\log R\) compensates for the convention that \(\log(R\,\|c-u\|^{-1})\) is interpreted as zero when \(u=c\). If the order is infinite at even one point of the disc, \(f\) vanishes off a discrete set, the divisor is zero, and both sides are the value attached to the zero function (`Analysis/Complex/JensenFormula.lean`).

If \(f\) is analytic on the closed disc and \(f(c)\neq 0\), the order at the center vanishes, the trailing coefficient is \(f(c)\), and the formula reduces to the circle average of \(\log\|f\|\) equal to \(\log\|f(c)\|\) plus the sum of \(D(u)\log(R/\|c-u\|)\) over the zeros.

Jensen’s inequality bounds the number of zeros. If \(0<|r|<|R|\), \(f\) is analytic on the closed disc of radius \(|R|\), \(f(c)\neq 0\), and \(\|f\|\le M\) on the circle of radius \(|R|\) with \(M\ge 1\), then the sum of the divisor of \(f\) on the closed disc of radius \(|r|\) is at most \(\log(M/\|f(c)\|)/\log(|R|/|r|)\).

## The three Nevanlinna functions

The logarithmic counting function is defined first for an integer-valued function of locally finite support on a proper normed space, and then for a meromorphic function. For a divisor \(D\) and a radius \(r\), it is the sum of \(D(z)\log(r/\|z\|)\) over the closed disc of radius \(|r|\), with the value at the origin separated so that the formula stays consistent with Jensen’s formula. For a meromorphic \(f\) and a finite value \(a\), the counting function of \(f\) at \(a\) is this construction applied to the positive part of the divisor of \(f-a\), so it counts zeros of \(f-a\) with multiplicity. At the value infinity it is applied to the negative part of the divisor of \(f\), so it counts poles. It is even in the radius, nonnegative for radii at least one, and monotone. Subtracting a constant does not change the counting function at infinity. For a product, the counting function at zero or at infinity is at most the sum of the counting functions, up to the usual inequalities for several factors (`Analysis/Complex/ValueDistribution/LogCounting/Basic.lean`).

Asymptotically, a nonnegative locally finite divisor has finite support if and only if its counting function is \(O(\log r)\) as \(r\to\infty\). A meromorphic function on a nontrivially normed proper field has only removable singularities, in the sense that its normal-form representative is analytic on the whole field, if and only if the counting function of its poles is \(O(1)\). It has finitely many poles if and only if that counting function is \(O(\log r)\) (`Analysis/Complex/ValueDistribution/LogCounting/Asymptotic.lean`).

The truncated logarithmic counting function counts each zero of \(f-a\), or each pole when \(a=\infty\), once regardless of multiplicity; it is the counting function of the divisor truncated at one. It is bounded by the ordinary counting function and is nonnegative for radii at least one, it is monotone, and it depends on \(f\) only off a discrete set. The module comment records it as the quantity through which the second main theorem is classically stated (`Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean`).

The proximity function of a meromorphic \(f:\mathbb{C}\to E\), with \(E\) a complex normed space, measures how close \(f\) comes to a value on the circle of radius \(r\). At infinity it is the circle average of \(\log^+\|f\|\). At a finite value \(a\) it is the circle average of \(\log^+\|f-a\|^{-1}\). Large values mean a close approach. It depends on \(f\) only through its values off a discrete subset of the circle (`Analysis/Complex/ValueDistribution/Proximity/Basic.lean`). For scalar \(f\), the proximity to infinity is also an iterated circle average: the average over the unit circle, in the variable \(a\), of the circle average of \(\log\|f-a\|\) on \(|z|=R\) (`Analysis/Complex/ValueDistribution/Proximity/IntegralPresentation.lean`).

The characteristic function, also called the Nevanlinna height, is the sum of the proximity function and the logarithmic counting function, at any value in the codomain extended by a point at infinity. It is even in the radius and nonnegative for radii at least one. For a finite sum of meromorphic functions, the characteristic at infinity is at most the sum of the characteristics plus the logarithm of the number of terms, once the radius is at least one. The file notes that the characterization of rational functions by the growth of the characteristic is not yet proved (`Analysis/Complex/ValueDistribution/CharacteristicFunction.lean`).

## Cartan’s formula

For \(f:\mathbb{C}\to\mathbb{C}\) meromorphic on the plane and \(R\neq 0\), Cartan’s formula writes the characteristic at infinity as two circle averages over the unit circle:
\[
T(R,f,\infty)
= \operatorname{circleAverage}\bigl(a\mapsto N(R,f,a)\bigr)
+ \operatorname{circleAverage}\bigl(a\mapsto \log\|\text{trailing coefficient of }f-a\text{ at }0\|\bigr).
\]
Both integrands are circle-integrable. Away from radius zero, the second average is a constant, so the characteristic differs from the average of the counting function by a constant. As a consequence the characteristic at infinity is monotone on \((0,\infty)\). The file notes that this monotonicity is not obvious from the definition, because the proximity function need not be monotone (`Analysis/Complex/ValueDistribution/Cartan.lean`).

On a disc, the same circle of ideas produces a finite canonical decomposition. The canonical factor of radius \(R\) at a point \(w\) is \((R^2-\overline{w}\,z)/(R(z-w))\). It is meromorphic and, for \(R>0\) and \(|w|<R\), has a single pole at \(w\) and modulus one on the circle of radius \(R\). These factors replace the linear factors in a factorization of a meromorphic function on a disc. The file calls the resulting finite product a finite Blaschke product. It is a tool for the counting formula, not a theory of inner functions (`Analysis/Complex/CanonicalDecomposition.lean`).

## The first main theorem

The characteristic is defined to be the sum of proximity and counting, so the equality \(T=m+N\) is a definition. The theorem that is proved is the invariance of the characteristic at infinity, in a quantitative form (`Analysis/Complex/ValueDistribution/FirstMainTheorem.lean`).

If \(f:\mathbb{C}\to\mathbb{C}\) is meromorphic on the plane, then for every real radius \(R\)
\[
\bigl|T(R,f,\infty)-T(R,f^{-1},\infty)\bigr|
\le \max\bigl\{\bigl|\log\|f(0)\|\bigr|,\,\bigl|\log\|\text{trailing coefficient of }f\text{ at }0\|\bigr|\bigr\}.
\]
For \(R\neq 0\) the difference equals the logarithm of the norm of the trailing coefficient at the origin, and at \(R=0\) it equals \(\log\|f(0)\|\). In particular the difference is \(O(1)\) as \(R\to\infty\).

If \(f\) is meromorphic on the plane with values in a complex normed space, and \(a\) is a point of that space, then for every radius
\[
\bigl|T(R,f,\infty)-T(R,f-a,\infty)\bigr|\le \log^+\|a\|+\log 2.
\]
The counting functions at infinity agree, because subtracting a constant does not move the poles, and the inequality is an estimate of the proximity functions. The difference is again \(O(1)\) as \(R\to\infty\).

Thus the characteristic at infinity is invariant, up to a bounded function and with the bounds just stated, under \(f\mapsto f^{-1}\) and under \(f\mapsto f-c\). Combining these with invariance under scaling, postcomposition with any Möbius transformation \(w\mapsto(aw+b)/(cw+d)\), \(ad-bc\neq0\), changes \(T(R,f,\infty)\) by \(O(1)\) as \(R\to\infty\) (`isBigO_characteristic_sub_characteristic_moebius`).

## The second main theorem

The file says that it will, in the future, establish the second main theorem of value distribution theory, and that at present it collects material that will be used in the proof. The pinned module comment points to an external formalization at `https://github.com/kebekus/ProjectVD`; that external project is not part of this audit. The second main theorem is therefore not a theorem of this checkout (`Analysis/Complex/ValueDistribution/SecondMainTheorem.lean`).

What the file contains is a separation lemma on a normed field. For a finite set \(s\), there is a constant \(C\), depending only on \(s\), such that for every point \(w\)
\[
\sum_{a\in s}\log^+\|w-a\|^{-1}
\le \log^+\Bigl\|\sum_{a\in s}(w-a)^{-1}\Bigr\|+C.
\]
Closeness to some point of \(s\), measured by the sum of truncated logarithms, is detected by the single function \(\log^+\bigl\|\sum (w-a)^{-1}\bigr\|\).

## Growth and product expansions elsewhere

The growth tools of classical function theory are in Section 40: the Borel–Carathéodory inequality, the Phragmén–Lindelöf principle in sectors and strips, and Hadamard's three-lines theorem. Explicit infinite products and partial-fraction expansions are proved for particular functions: Euler's product for \(\sin\pi z\) and the Euler–Gauss limit formula for \(\Gamma\) (Section 49), and the partial-fraction expansion of \(\pi\cot\pi z\) (`cot_series_rep` in `Analysis/SpecialFunctions/Trigonometric/Cotangent.lean`). These are instances of the Weierstrass and Mittag-Leffler theorems, not the general theorems.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6ebb29f84b4d`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

Residues, canonical local meromorphic principal parts, and the contour argument principle add to the classical meromorphic-function theory ([local Laurent data](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Contour/MeromorphicLaurent.lean), [argument principle](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Contour/Argument/Principle.lean)). The monodromy theorem gives global branches from pathwise analytic continuation on simply connected domains ([source](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Complex/Conformal/GlobalBranch.lean)).

The Herglotz representation theorem characterizes holomorphic disc functions with nonnegative real part as transforms of finite positive circle measures, up to an imaginary constant ([representation](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Complex/Herglotz.lean)). Through the Cayley transform it gives the Pick (Nevanlinna) representation of holomorphic functions on the upper half-plane with nonnegative imaginary part, with the atom of the circle measure at \(1\) producing the linear term ([Pick functions](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Complex/Pick/Basic.lean), [Nevanlinna transport](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Complex/Pick/Nevanlinna.lean)); this concerns positive imaginary part, not Nevanlinna's value-distribution theory. The zero count of a holomorphic function on a disc, with multiplicity, is the quantity produced by the argument principle and compared by Rouché's and Hurwitz's theorems ([zero count](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Complex/ZeroCount.lean)). Locally bounded families of holomorphic functions are equicontinuous, the analytic core of Montel's theorem ([normal families](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Complex/Conformal/NormalFamilies.lean)); normality is not studied for meromorphic families or through the spherical derivative. No completion of the second main theorem, Hadamard factorization, or Picard's theorems was located.

## Topics of Section 41 not found in either inspected library

- The second main theorem, the defect relation, Nevanlinna's five-value theorem, and the lemma on the logarithmic derivative as a finished theorem. The separation lemma and the truncated counting function are the material collected toward a future proof, and a full formalization is cited outside this checkout.
- Hadamard factorization, canonical products, the genus of an entire function, and the growth order \(\limsup_{r\to\infty}\log\log M(r)/\log r\) and type. The order that is defined is the order of a zero or a pole.
- Functions of exponential type: Cartwright's theorem on zero distribution and the Paley–Wiener theorem in its complex-analytic form.
- Zalcman's rescaling lemma, Marty's criterion and the spherical derivative; normal families appear only as locally bounded holomorphic families (Montel).
- Wiman–Valiron theory: the maximum term, central index and the Wiman–Valiron approximation.
- Picard’s little and great theorems, and Bloch’s theorem. The Picard–Lindelöf theorem is an existence theorem for ordinary differential equations and is not this Picard theorem.
- The characterization of rational functions by the growth of the characteristic. The file records it as not yet proved. What is proved is that the pole-counting function is \(O(1)\) precisely for functions whose normal form is entire, and \(O(\log r)\) precisely when there are finitely many poles.
- A Nevanlinna theory of several complex variables. The references cited in the files discuss that theory, but every theorem above is one-variable, or is the formal counting function of a divisor on a normed field.
