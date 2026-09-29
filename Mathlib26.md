# 26. Sobolev Spaces, Smoothness Scales, and Interpolation

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The roots for this section are `Mathlib.Analysis.FunctionalSpaces.SobolevInequality`, `Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace`, `Mathlib.Analysis.Distribution.Sobolev`, `Mathlib.Analysis.Calculus.ContDiffHolder.Pointwise`, and `Mathlib.Analysis.Normed.Lp.SmoothApprox`.

**Namespaces.** The Gagliardo–Nirenberg–Sobolev inequality is `MeasureTheory`, with the inductive estimate in the nested namespace `GridLines`. Bessel potential spaces are `BesselPotentialSpace`, with notation \(H^{s,p}\), and the unbundled predicate is `TemperedDistribution.MemSobolev`. The pointwise Hölder condition is `ContDiffPointwiseHolderAt`. Density of smooth functions is `MeasureTheory.MemLp`.

This note records an inequality for compactly supported \(C^1\) functions, the Fourier-theoretic spaces \(H^{s,p}\), and a pointwise Hölder condition. It does not record the spaces \(W^{k,p}\).

## The Gagliardo–Nirenberg–Sobolev inequality

Let \(E\) be a finite-dimensional real normed space of dimension \(n\), equipped with a Haar measure, and let \(u\) be of class \(C^1\) in the sense `ContDiff ℝ 1`. The derivative below is the Fréchet derivative, measured in operator norm (`Analysis/FunctionalSpaces/SobolevInequality.lean`).

For the coordinate sup norm the inequality has constant \(1\). If the domain is \(\iota\to\mathbb{R}\) with \(n=\#\iota\geq 2\), if \(u\) has compact support, and if \(p=n/(n-1)\), then for a real normed codomain
\[
\int \|u\|^p \leq \Bigl(\int \|Du\|\Bigr)^p.
\]
The same bound, multiplied by a constant depending only on \(E\), the Haar measure, and \(p\), holds on a general \(E\) of dimension \(n\geq 2\). The constant is built from the comparison of the given Haar measure with Lebesgue measure on \(\mathbb{R}^n\) and from the operator norm of a chosen linear equivalence \(E\simeq\mathbb{R}^n\); it is not evaluated further.

The form with a general integrability exponent on the derivative is as follows. In the usual positive-exponent range, assume \(1\leq p<n\) and \(p'>0\) with
\[
\frac1{p'}=\frac1p-\frac1n,
\]
Thus \(p'=np/(n-p)\) and \(n\geq2\). If \(u\) has compact support, then \(\|u\|_{L^{p'}}\leq C\|Du\|_{L^p}\). When the codomain is a real inner product space, of any dimension, \(C\) depends only on \(E\), the measure, and \(p\). The source refers to this codomain as a Hilbert space; completeness is not an explicit hypothesis. When the codomain is a finite-dimensional real normed space, \(C\) may also depend on that codomain. The case \(p=1\), so that \(p'=n/(n-1)\), holds for an arbitrary real normed codomain.

If instead the support of \(u\) is contained in a bounded set \(s\), if \(1\leq p<n\), and if \(q\) satisfies \(p^{-1}-n^{-1}\leq q^{-1}\), then \(\|u\|_{L^q}\leq C\|Du\|_{L^p}\), where \(C\) depends on the codomain, the measure, \(s\), \(p\), and \(q\). In particular, with \(q=p\), a \(C^1\) function supported in a bounded set satisfies \(\|u\|_{L^p}\leq C\|Du\|_{L^p}\).

These statements are inequalities for \(C^1\) functions of compact support, or of support in a bounded set. They are not embeddings of a Sobolev space \(W^{1,p}\).

## Bessel potential spaces

On a finite-dimensional real inner product space \(E\), with its Lebesgue measure, and for a complete complex normed space \(F\), the Bessel potential of order \(s\in\mathbb{R}\) is the Fourier multiplier on tempered distributions with symbol \(x\mapsto(1+\|x\|^2)^{s/2}\). Because of the normalization of the Fourier transform, this is the operator \((1-(2\pi)^{-2}\Delta)^{s/2}\), not \((1-\Delta)^{s/2}\). Potentials add: the potential of order \(s'\) applied after the potential of order \(s\) is the potential of order \(s+s'\) (`Analysis/Distribution/Sobolev.lean`).

For \(1\leq p\leq\infty\), a tempered distribution \(u\) lies in the Sobolev class of order \(s\) and exponent \(p\) when that potential of \(u\) is represented by an \(L^p\) function. Every Schwartz function lies in every such class. The predicate is a complex vector space of distributions.

The file `Analysis/FunctionalSpaces/BesselPotentialSpace.lean` bundles the same data: an element of \(H^{s,p}(E,F)\) is a tempered distribution together with the \(L^p\) function produced by the Bessel potential. The underlying distribution determines the element. The map to the \(L^p\) function is a linear isometry onto \(L^p\), so \(H^{s,p}\) is a Banach space; the inverse sends an \(L^p\) function \(v\) to the potential of order \(-s\) applied to \(v\). For \(p=2\) and \(F\) a complex inner product space, the \(L^2\) inner product of the potentials makes \(H^s\) a Hilbert space. The unbundled predicate and the bundled space describe the same distributions.

For \(p=2\) there is a Fourier-side characterization: \(u\) lies in \(H^{s,2}\) if and only if \((1+\|\xi\|^2)^{s/2}\widehat u\) is represented by an \(L^2\) function. In that case the scale is monotone in the smoothness index, a bounded function of temperate growth preserves \(H^{s,2}\) under Fourier multiplication, a directional derivative maps \(H^{s,2}\) into \(H^{s-1,2}\), and the Laplacian maps \(H^{s,2}\) into \(H^{s-2,2}\). The derivative and monotonicity statements are not given for \(p\neq 2\).

If \(s>\dim E/2\) and \(u\in H^{s,2}\), the Fourier transform of \(u\) is represented by an \(L^1\) function. The source describes this integrability as the main calculation toward a Sobolev embedding. The embedding itself, into continuous or bounded functions, is not stated. Nothing in either file identifies \(H^{k,p}\) with a space \(W^{k,p}\) of weak derivatives.

## Pointwise Hölder regularity

For a natural number \(k\) and an exponent \(\alpha\in[0,1]\), a map of real normed spaces is of class \(C^{k+(\alpha)}\) at a point \(a\) when it is of class \(C^k\) at \(a\) and
\[
D^kf(x)-D^kf(a)=O(\|x-a\|^\alpha)\qquad\text{as }x\to a
\]
(`Analysis/Calculus/ContDiffHolder/Pointwise.lean`). The estimate fixes one point at \(a\). It is the pointwise, or weak, Hölder condition, not Hölder continuity of \(D^kf\) on a neighborhood of \(a\).

The class \(C^{k+(0)}\) is exactly \(C^k\). The class \(C^{0+(\alpha)}\) is continuity on a neighborhood of \(a\) together with \(f(x)-f(a)=O(\|x-a\|^\alpha)\). A map of class \(C^n\) at \(a\), with \(n>k\), is of class \(C^{k+(\alpha)}\) at \(a\) for every \(\alpha\). Lowering \(k\), or lowering \(\alpha\), preserves the condition. If \(f\) is \(C^k\) on a neighborhood of \(a\) and \(D^kf\) is Hölder continuous of exponent \(\alpha\) on that neighborhood, then \(f\) is \(C^{k+(\alpha)}\) at \(a\).

Composition of two maps of class \(C^{k+(\alpha)}\) is of class \(C^{k+(\alpha)}\) when \(k\neq 0\). If \(k=0\), composition still holds provided one of the two maps is differentiable at the relevant point. Continuous linear maps are of every class \(C^{k+(\alpha)}\), and so are products of two such maps. If \(l+m\leq k\), the \(m\)th derivative of a map of class \(C^{k+(\alpha)}\) is of class \(C^{l+(\alpha)}\). Applying a \(C^{k+(\alpha)}\) family of continuous linear maps to a \(C^{k+(\alpha)}\) map preserves the class. A Banach-algebra structure on a space of globally Hölder functions is not proved in this file.

The two-point condition, \(\operatorname{dist}(f x,f y)\leq C\operatorname{dist}(x,y)^\alpha\) on a set, is defined separately, with composition and a Hölder seminorm (`Topology/MetricSpace/Holder.lean`, `Topology/MetricSpace/HolderNorm.lean`). That is not a scale \(C^{k,\alpha}\).

## Approximation in \(L^p\)

On a finite-dimensional real normed space, for a measure finite on compact sets and for \(1\leq p<\infty\), every \(L^p\) function can be approximated in \(L^p\) by smooth compactly supported functions. Equivalently, the classes of such functions are dense in \(L^p\) (`Analysis/Normed/Lp/SmoothApprox.lean`).

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti defines real-valued \(W^{1,p}(\Omega)\) by weak derivatives as a closed space of \(L^p\) value-gradient pairs, and defines \(W^{k,p}(\Omega)\) using iterated weak derivatives. For \(p\ge1\) the resulting spaces are complete; the first-order \(p=2\) construction is Hilbert ([first order](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Sobolev/W1p/Basic.lean), [higher order](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Sobolev/Wkp/Basic.lean)). Domains are open subsets of finite-dimensional real inner-product spaces with additive Haar measure. The zero-boundary spaces are closures of compactly supported smooth functions. Extension by zero is an isometric operator for \(W^{1,p}_0\), with the expected weak gradient ([extension](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Sobolev/W1p/Extension.lean)).

The critical embedding \(W^{1,p}_0(\Omega)\hookrightarrow L^{np/(n-p)}(\Omega)\) is proved for \(1\le p<n\), and whole-space \(W^{1,p}\) embeds into the Hölder space of exponent \(1-n/p\) for \(n<p<\infty\) ([Sobolev embedding](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Sobolev/Embedding.lean), [Morrey embedding](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Sobolev/W1p/HolderEmbedding.lean)). Rellich–Kondrachov gives compactness of \(W^{1,p}_0(\Omega)\to L^p(\Omega)\) on bounded open domains, for \(1\le p<\infty\); no boundary regularity is required because these are zero-boundary spaces ([compactness](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Sobolev/RellichKondrachov.lean)).

Smooth convolution approximation is proved in \(L^p\), with the Sobolev library supplying mollification and weak-derivative compatibility ([approximate identities](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/Function/Lp/ApproximateIdentity.lean)). Diagonal Marcinkiewicz interpolation is also proved for sublinear operators between finite weak-type endpoints ([interpolation](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/Integral/Marcinkiewicz/General.lean)); it is distinct from an interpolation functor for Banach couples.

There are also complete spaces of bounded global \(C^{0,\alpha}\), \(C^{1,\alpha}\), and \(C^{2,\alpha}\) functions, with bounded derivatives as appropriate. The order-zero space is a Banach algebra for Banach-algebra-valued functions ([Hölder algebra](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Holder/Algebra.lean), [first order](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Holder/One.lean), [second order](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Holder/Two.lean)). These files do not define the full arbitrary-order Hölder–Zygmund scale.

For \(1\le p<\infty\), test functions are dense in whole-space \(W^{1,p}(\mathbb R^n)\), so \(W^{1,p}_0(\mathbb R^n)=W^{1,p}(\mathbb R^n)\) ([density](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Sobolev/W1p/Density.lean)). Poincaré estimates for zero-boundary spaces on slab-contained domains are recorded in Section 14.

## Topics of Section 26 not found in either inspected library

- Identification of the weak-derivative spaces \(W^{k,p}\) with the Bessel potential spaces \(H^{k,p}\).
- General embeddings on \(W^{1,p}(\Omega)\) for domains with boundary, and the borderline critical-exponent theory, beyond the zero-boundary and whole-space embeddings described above.
- Trace theorems and extension operators for general \(W^{1,p}(\Omega)\), for example on Lipschitz domains. Zero extension of \(W^{1,p}_0(\Omega)\) is proved in TauCeti.
- Real interpolation and complex interpolation of Banach spaces. Hadamard’s three-lines theorem is proved (`Analysis/Complex/Hadamard.lean`); it is not developed into an interpolation functor or into interpolation of Sobolev spaces.
- Besov spaces, Triebel–Lizorkin spaces, and Slobodeckij spaces.
- The full arbitrary-order Hölder–Zygmund scale. TauCeti constructs bounded global \(C^{0,\alpha}\), \(C^{1,\alpha}\), and \(C^{2,\alpha}\) Banach spaces, and the order-zero Banach-algebra structure.
