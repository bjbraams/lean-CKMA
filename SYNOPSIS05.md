# Synopsis: Differentiation and the fine structure of real functions

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects recurring material from Section 05 of
[CKMA-bib.md](CKMA-bib.md) and [CKMA-bib2.md](CKMA-bib2.md). Its center is the
relation between pointwise derivatives, measures, and integral reconstruction:
what differentiability forces, how it can fail, and which weaker notions survive
for Lipschitz, Sobolev, and bounded-variation functions. Classical smooth calculus
and nonabsolute integration provide the two ends of this spectrum.

Here $I$ is a real interval, $U\subseteq\mathbb R^n$ is open, $\mathcal L^n$ is
Lebesgue measure, and $\mathcal H^s$ is Hausdorff measure, normalized so that
$\mathcal H^k$ agrees with $k$-dimensional volume on $k$-planes. Almost-everywhere
statements refer to Lebesgue measure unless another measure is specified.

## Classical derivatives and smooth maps

The **Fréchet derivative** of $f:U\to\mathbb R^m$ at $x$ is the linear map
$Df(x)$ satisfying $f(x+h)=f(x)+Df(x)h+o(|h|)$. A map is $C^k$ if its derivatives
through order $k$ exist and are continuous. A point is **critical** for a map to
$\mathbb R^m$ when its derivative has rank less than $m$.

* **1. Mean value theorem and inequality.** For a continuous real function on
  $[a,b]$, differentiable on $(a,b)$, some $c$ satisfies
  $f(b)-f(a)=f'(c)(b-a)$. For vector-valued maps on a convex open set,
  $\sup_U\|Df\|\leq M$ implies $|f(x)-f(y)|\leq M|x-y|$.
* **2. Taylor's theorem.** For $f\in C^k(U)$,
  $$f(x+h)=\sum_{j=0}^k\frac{1}{j!}D^jf(x)[h^j]+o(|h|^k).$$
  If $f\in C^{k+1}$ near the segment, the remainder after order $k$ is
  $\frac1{k!}\int_0^1(1-t)^kD^{k+1}f(x+th)[h^{k+1}]\,dt$.
* **3. Inverse function theorem.** A $C^k$ map $f:U\to\mathbb R^n$, $k\geq1$,
  with invertible $Df(x_0)$ has a local $C^k$ inverse, whose derivative at $f(x)$
  is $Df(x)^{-1}$.
* **4. Implicit function theorem.** If $F(x,y)$ is $C^k$ near $(x_0,y_0)$,
  $F(x_0,y_0)=0$, and $D_yF(x_0,y_0)$ is invertible, its nearby zero set is
  uniquely a graph $y=g(x)$ with $g\in C^k$ and
  $Dg=-(D_yF)^{-1}D_xF$.
* **5. Sard's theorem.** If $f:U\to\mathbb R^m$ is $C^k$ with
  $k>\max(n-m,0)$, its critical values form a Lebesgue-null subset of
  $\mathbb R^m$. In particular, almost every value of a smooth map is regular.

## Derivatives as real functions: continuity, category, and Dini derivatives

The **upper and lower right Dini derivatives** are
$D^+f(x)=\limsup_{h\downarrow0}(f(x+h)-f(x))/h$ and $D_+f(x)$ with $\liminf$;
$D^-f,D_-f$ use $h\uparrow0$. Values in the extended real line are allowed.
A function is of **Baire class one** if it is a pointwise limit of continuous
functions. A **Darboux function** has the intermediate value property on intervals.

* **6. Darboux's theorem.** Every derivative has the intermediate value property,
  even when it is discontinuous. A derivative therefore cannot have a jump
  discontinuity.
* **7. Baire classification of derivatives.** If $f$ is differentiable on an
  open interval, $f'$ is of Baire class one, as follows by taking continuous
  difference quotients locally.
* **8. Continuity points of Baire-one functions.** On a real interval, the
  discontinuity set of a Baire-one function is a meagre $F_\sigma$ set. Thus an
  everywhere finite derivative is continuous on a dense $G_\delta$ set.
* **9. Dini criterion for monotonicity.** If $f$ is continuous on $[a,b]$ and
  $D_+f(x)\geq0$ at every $x\in[a,b)$, then $f$ is nondecreasing. In particular,
  $f'\geq0$ everywhere implies monotonicity. An almost-everywhere derivative
  inequality alone does not suffice for arbitrary continuous functions.
* **10. Denjoy–Young–Saks theorem.** For any finite real function on an interval,
  almost every interior point has exactly one of the following types:
  all four Dini derivatives are the same finite number;
  $D^+=D^-=+\infty$ and $D_+=D_-=-\infty$;
  $D^+=+\infty$, $D_-=-\infty$, and $D_+=D^-$ is finite;
  or $D^-=+\infty$, $D_+=-\infty$, and $D_-=D^+$ is finite.
* **11. Typical nondifferentiability.** In $C([a,b])$, $a<b$, with the uniform
  norm, the nowhere differentiable functions form a residual set (interior
  differentiability is meant). Continuous nowhere differentiable functions
  therefore exist in abundance in the sense of Baire category.

## Bounded variation and absolute continuity on the line

The **total variation** of $F:[a,b]\to\mathbb R$ is
$\operatorname{Var}(F)=\sup\sum_i|F(x_i)-F(x_{i-1})|$, over partitions.
The space $BV[a,b]$ consists of functions of finite variation. **Absolute
continuity** means that for every $\varepsilon>0$ some $\delta>0$ makes
$\sum_i|F(b_i)-F(a_i)|<\varepsilon$ whenever disjoint subintervals have total
length below $\delta$. The **Lusin property $(N)$** means that null sets have
null images.

* **12. Jordan's theorem.** A real function has bounded variation exactly when
  it is a difference of two bounded increasing functions. It has finite
  one-sided limits at every interior point and at most countably many
  discontinuities, all of jump type for the appropriate one-sided representative.
* **13. Lebesgue's theorem for monotone functions.** An increasing function is
  differentiable with finite derivative almost everywhere. Its derivative is
  nonnegative and integrable, and
  $\int_a^b F'\leq F(b)-F(a)$.
* **14. Differentiation of $BV$ functions.** A function of bounded variation has
  a finite derivative almost everywhere, with
  $\int_a^b|F'|\leq\operatorname{Var}(F)$. Its distributional derivative is a
  finite signed measure on $(a,b)$, after identification of functions equal
  almost everywhere.
* **15. Integral characterization of absolute continuity.** A function $F$ is
  absolutely continuous exactly when $F(x)=F(a)+\int_a^x g(t)\,dt$ for some
  $g\in L^1$. Then $F'=g$ almost everywhere and
  $\operatorname{Var}(F)=\int_a^b|F'|$.
* **16. Banach–Zarecki theorem.** A real function on a compact interval is
  absolutely continuous exactly when it is continuous, has bounded variation,
  and has property $(N)$.
* **17. Decomposition of variation.** For a right-continuous $BV$
  representative, the derivative measure splits uniquely into an absolutely
  continuous part $F'\,dx$, an atomic jump part, and a singular continuous part.
  For an increasing continuous function, the last part accounts precisely for
  the possible strict inequality in result 13.
* **18. Singular functions.** The Cantor distribution function is continuous,
  nondecreasing, nonconstant, and has derivative zero almost everywhere. Hence
  continuity, bounded variation, and almost-everywhere differentiability do not
  by themselves permit reconstruction by the Lebesgue integral of the derivative.
* **19. Helly selection.** A sequence on $[a,b]$ with uniformly bounded
  variations and uniformly bounded values at one point has a subsequence
  converging pointwise everywhere to a function of bounded variation. Variation
  is lower semicontinuous under this convergence.
* **20. Calculus for absolutely continuous functions.** Products of absolutely
  continuous functions on $[a,b]$ are absolutely continuous and satisfy the
  product rule almost everywhere and integration by parts. If $F$ is absolutely
  continuous and $\Phi$ is $C^1$ near its range, then
  $(\Phi\circ F)'=\Phi'(F)F'$ almost everywhere and $\Phi\circ F$ is absolutely
  continuous.

## Coverings, maximal functions, and differentiation bases

A **Vitali covering** of $E$ by balls supplies balls containing each point with
arbitrarily small radii. A **differentiation basis** assigns shrinking measurable
neighborhoods to each point and asks whether their averages recover a function.
The centered **Hardy–Littlewood maximal function** is
$$Mf(x)=\sup_{r>0}\frac1{|B(x,r)|}\int_{B(x,r)}|f(y)|\,dy.$$

* **21. The $5r$ covering lemma.** A family of balls with bounded radii in
  $\mathbb R^n$ has a countable disjoint subfamily whose fivefold enlargements
  cover the union of the original balls.
* **22. Vitali covering theorem.** If a family of closed balls is a Vitali
  covering of a measurable set $E$ of finite Lebesgue measure, a countable
  disjoint subfamily covers $E$ up to a null set.
* **23. Besicovitch covering theorem.** If a bounded set $E\subseteq\mathbb R^n$
  is supplied with arbitrarily small balls centered at each of its points,
  one can select a countable covering of $E$ with overlap bounded by a constant
  depending only on $n$. The stronger finite-family decomposition into disjoint
  subfamilies underlies differentiation for arbitrary Radon measures.
* **24. Whitney decomposition.** A nonempty proper open subset of $\mathbb R^n$
  is the union of a countable family of closed dyadic cubes with disjoint
  interiors, whose diameters are comparable to their distances from the
  complement. Slight enlargements can be chosen with bounded overlap.
* **25. Weak maximal inequality.** There is $C_n$ such that
  $$|\{Mf>\lambda\}|\leq\frac{C_n}{\lambda}\|f\|_1
    \qquad(\lambda>0).$$
* **26. Strong maximal inequality for balls.** For $1<p\leq\infty$,
  $\|Mf\|_p\leq C_{n,p}\|f\|_p$.
* **27. Lebesgue differentiation theorem.** For $f\in L^1_{\mathrm{loc}}$,
  $$\lim_{r\downarrow0}\frac1{|B(x,r)|}
    \int_{B(x,r)}|f(y)-f(x)|\,dy=0$$
  at almost every $x$. Cubes and families of bounded eccentricity give the same
  differentiation result.
* **28. Lebesgue density theorem.** Almost every point of a measurable set has
  density one in that set, and almost every point of its complement has density
  zero in the set.
* **29. Differentiation of measures.** If $\mu,\nu$ are positive Radon measures
  on $\mathbb R^n$ and $\nu=f\mu+\nu_s$, $\nu_s\perp\mu$, then
  $$\lim_{r\downarrow0}\frac{\nu(B(x,r))}{\mu(B(x,r))}=f(x)
    \quad\text{for }\mu\text{-almost every }x.$$
  For signed measures the same assertion holds locally by decomposition.
* **30. Approximate continuity.** Every finite measurable function is
  approximately continuous almost everywhere: for almost every $x$ and every
  $\varepsilon>0$, the set $\{y:|f(y)-f(x)|>\varepsilon\}$ has density zero at $x$.
* **31. Rectangular differentiation.** In dimension $n\geq2$, averages over all
  axis-parallel rectangles shrinking to $x$, with unrestricted eccentricity,
  differentiate $L(\log^+L)^{n-1}_{\mathrm{loc}}$. They do not differentiate
  all of $L^1_{\mathrm{loc}}$. The associated strong maximal operator satisfies
  the endpoint bound
  $$|\{M_{\!S}f>\lambda\}|\leq C_n\int
    \frac{|f|}{\lambda}
    \left(1+\log^+\frac{|f|}{\lambda}\right)^{n-1}dx.$$

## Lipschitz functions and approximate differentiation

A map is **$L$-Lipschitz** if $|f(x)-f(y)|\leq L|x-y|$.
A measurable $f:U\to\mathbb R^m$ is **approximately differentiable** at $x$ if
some linear $A$ satisfies
$\operatorname*{ap\,lim}_{y\to x}|f(y)-f(x)-A(y-x)|/|y-x|=0$; an approximate
limit excludes a set of density zero. A **weak derivative** $D_i f=g$ satisfies
$\int f\partial_i\phi=-\int g\phi$ for all $\phi\in C_c^\infty(U)$.
The **Sobolev space** $W^{1,p}(U)$ consists of $L^p$ functions whose first weak
derivatives are in $L^p$; its local version imposes this on relatively compact
open subsets. Classical differentiability specifies behavior along every
approach to a point. Approximate differentiability specifies it on a set of
density one. The latter is therefore meaningful for almost-everywhere
equivalence classes, and the approximate derivative is unique wherever the
point has full density in the domain.

* **32. McShane–Whitney extension.** Every real $L$-Lipschitz function on a
  nonempty subset $A$ of a metric space extends to the whole space with the same
  Lipschitz constant; extremal extensions are given by
  $\inf_{a\in A}(f(a)+Ld(x,a))$ and $\sup_{a\in A}(f(a)-Ld(x,a))$.
* **33. Kirszbraun's theorem.** An $L$-Lipschitz map from a subset of Euclidean
  space to another Euclidean space extends with the same constant. The theorem
  also holds for real Hilbert spaces.
* **34. Rademacher's theorem.** A locally Lipschitz map
  $f:U\to\mathbb R^m$ is Fréchet differentiable almost everywhere, and
  $\|Df(x)\|$ is bounded by its Lipschitz constant wherever the derivative exists.
* **35. Absolute continuity on lines.** A function in
  $W^{1,p}_{\mathrm{loc}}(U)$, $1\leq p\leq\infty$, has a representative
  absolutely continuous on almost every line segment parallel to a coordinate
  axis, locally in $U$. Its classical derivatives there are the weak partial
  derivatives. Conversely, this property together with local $L^p$
  integrability of the function and these derivatives characterizes
  $W^{1,p}_{\mathrm{loc}}$.
* **36. Lipschitz and $W^{1,\infty}$.** Locally Lipschitz functions belong to
  $W^{1,\infty}_{\mathrm{loc}}$. On a convex open set, a function with globally
  bounded weak gradient has a Lipschitz representative with Lipschitz constant
  at most $\|\nabla f\|_\infty$.
* **37. Approximate differentiation of Sobolev functions.** Every
  $f\in W^{1,1}_{\mathrm{loc}}(U)$ is approximately differentiable almost
  everywhere, and its approximate derivative equals its weak gradient.
* **38. Whitney's Lusin approximation theorem on the line.** A measurable
  function on a compact interval is approximately differentiable almost
  everywhere exactly when, for every $\varepsilon>0$, it agrees with a $C^1$
  function on a closed set whose complement has measure less than
  $\varepsilon$.
* **39. Lusin approximation of Sobolev functions.** If
  $f\in W^{1,1}_{\mathrm{loc}}(U)$ and $U$ has finite measure, then for every
  $\varepsilon>0$ there are a compact $K\subset U$ with $|U\setminus K|<\varepsilon$
  and $g\in C^1(\mathbb R^n)$ such that $g=f$ and $Dg=Df$ almost everywhere on
  $K$.
* **40. Area formula.** For Lipschitz $f:\mathbb R^n\to\mathbb R^m$, $n\leq m$,
  measurable $A$, and nonnegative measurable $g$,
  $$\int_A g(x)J_nf(x)\,dx
    =\int_{\mathbb R^m}\sum_{x\in A\cap f^{-1}(y)}g(x)\,d\mathcal H^n(y),$$
  where $J_nf=\sqrt{\det(Df^{\mathsf T}Df)}$ almost everywhere. For injective
  maps this is change of variables onto the image.
* **41. Coarea formula.** For Lipschitz $f:\mathbb R^n\to\mathbb R^m$, $n\geq m$,
  and nonnegative measurable $g$,
  $$\int g(x)J_mf(x)\,dx
    =\int_{\mathbb R^m}\int_{f^{-1}(y)}g(x)\,d\mathcal H^{n-m}(x)\,dy,$$
  where $J_mf=\sqrt{\det(DfDf^{\mathsf T})}$. For $m=1$, the Jacobian is
  $|\nabla f|$.

## Fine properties of $BV$ functions in several variables

A function $u\in L^1(U)$ is in **$BV(U)$** if its distributional gradient $Du$
is a finite vector measure. Its variation has the dual formula
$$|Du|(U)=\sup\left\{\int_Uu\,\operatorname{div}\phi\,dx:
  \phi\in C_c^1(U;\mathbb R^n),\ |\phi|\leq1\right\}.$$
A measurable set has **finite perimeter** in $U$ if its locally integrable
indicator has a distributional gradient of finite total variation there; its
perimeter is $P(E,U)=|D1_E|(U)$. No finite-volume assumption on $E$ is imposed.

* **42. Lower semicontinuity.** If $u_j\to u$ in $L^1_{\mathrm{loc}}(U)$, then
  $|Du|(U)\leq\liminf_j|Du_j|(U)$, with infinite variation allowed.
* **43. Smooth approximation.** Every $u\in BV(U)$ admits smooth
  $u_j\in C^\infty(U)\cap BV(U)$ with $u_j\to u$ in $L^1(U)$ and
  $\int_U|\nabla u_j|\,dx\to|Du|(U)$.
* **44. Compactness.** On a bounded Lipschitz domain, bounded subsets of
  $BV(U)$ are relatively compact in $L^1(U)$. Local versions hold on arbitrary
  open sets with uniform local bounds.
* **45. $BV$ coarea.** For real $u\in BV(U)$,
  $$|Du|(U)=\int_{-\infty}^{\infty}P(\{u>t\},U)\,dt.$$
  Thus almost all superlevel sets have finite perimeter.
* **46. Approximate differentiability in $BV$.** Every $BV$ function is
  approximately differentiable almost everywhere. Its approximate gradient is
  the density of the absolutely continuous part of $Du$ with respect to
  $\mathcal L^n$.
* **47. Slicing.** For $u\in BV(U)$, restrictions to almost every line parallel
  to a fixed coordinate axis are locally one-dimensional $BV$ functions.
  Integrating their variations over transverse coordinates gives the variation
  of the corresponding directional derivative measure.

## Nonabsolute integration and reconstruction of primitives

A **gauge** on $[a,b]$ is a positive function $\delta(x)$. A tagged partition
$\{([x_{i-1},x_i],\xi_i)\}$ is $\delta$-fine when each interval lies in
$(\xi_i-\delta(\xi_i),\xi_i+\delta(\xi_i))$. A function is
**Henstock–Kurzweil integrable** with integral $A$ if for every $\varepsilon>0$
there is a gauge making every fine tagged Riemann sum differ from $A$ by less
than $\varepsilon$.

A continuous function $F$ is **$ACG_*$** if $[a,b]$ is a countable union of
closed sets $E_j$ on each of which $F$ is absolutely continuous in the restricted
sense: for every $\varepsilon>0$, disjoint intervals with endpoints in $E_j$
and sufficiently small total length have sum of the oscillations of $F$ on
those intervals less than $\varepsilon$. Oscillation on $J$ means
$\sup_{x,y\in J}|F(x)-F(y)|$.

* **48. Existence of fine partitions.** Every positive gauge on a compact
  interval admits a fine tagged partition (Cousin's lemma). The gauge integral,
  when it exists, is therefore unique and is additive over adjacent intervals.
* **49. Extension of the Lebesgue integral.** Every Lebesgue-integrable function
  is Henstock–Kurzweil integrable with the same integral. A function and its
  absolute value are both gauge integrable exactly when it is Lebesgue integrable.
* **50. Integration of derivatives.** If $F$ is continuous on $[a,b]$ and has a
  finite derivative at every interior point, then $F'$ is Henstock–Kurzweil
  integrable and
  $$\int_a^bF'(x)\,dx=F(b)-F(a).$$
  Endpoint values of the integrand are immaterial.
* **51. Fundamental theorem for the gauge integral.** The indefinite
  Henstock–Kurzweil integral is continuous and has derivative equal to its
  integrand almost everywhere. Conversely, its primitives are precisely the
  generalized absolutely continuous functions in the restricted sense
  ($ACG_*$), with the additive constant fixed.
* **52. Equivalence of the classical nonabsolute integrals.** The
  Henstock–Kurzweil, Perron, and restricted Denjoy integrals on a compact
  interval have the same integrable functions and the same values. This
  equivalence does not identify them with the more permissive wide Denjoy integral.

## Extension, traces, and further fine properties

A **first-order jet** on a closed set $E$ is prescribed value and derivative
data $(f,p)$ with $p:E\to\mathbb R^n$. For $1\leq p<\infty$, the
**Sobolev $p$-capacity** of $E\subseteq\mathbb R^n$ is the infimum of
$\|v\|_{W^{1,p}(\mathbb R^n)}^p$ over Sobolev functions $v$ that are at least
one almost everywhere on some open neighborhood of $E$. Small capacity is a
stronger notion of exceptional size than small Lebesgue measure. Traces below
are defined by approach from inside the domain, not by arbitrary values assigned
on its boundary to an $L^1$ representative.

* **53. Whitney's $C^1$ extension theorem.** For compact $E\subseteq\mathbb R^n$,
  continuous data $f:E\to\mathbb R$, $p:E\to\mathbb R^n$ extend to
  $F\in C^1(\mathbb R^n)$ with $F|_E=f$, $\nabla F|_E=p$ if and only if
  $$f(y)-f(x)-p(x)\cdot(y-x)=o(|y-x|)$$
  uniformly for $x,y\in E$ as $|x-y|\to0$.
  The derivative data must satisfy continuity as assumed; the remainder
  condition alone is not a substitute for it.
* **54. Lipschitz control of exceptional sets.** An $L$-Lipschitz map satisfies
  $\mathcal H^s(f(E))\leq L^s\mathcal H^s(E)$ for $s>0$. In particular,
  Lipschitz maps $\mathbb R^n\to\mathbb R^n$ have property $(N)$. This
  measure control, together with almost-everywhere differentiability, is a
  principal reason area and change-of-variables formulas extend beyond $C^1$ maps.
* **55. Length and the indicatrix formula.** An absolutely continuous curve
  $\gamma:[a,b]\to\mathbb R^m$ is rectifiable and
  $$\operatorname{length}(\gamma)=\int_a^b|\gamma'(t)|dt.$$
  For real absolutely continuous $F$, this is also
  $\int_{\mathbb R}\#\{t\in[a,b]:F(t)=y\}\,dy$, with exceptional levels and
  endpoints interpreted almost everywhere. Thus total variation counts level
  crossings with multiplicity.
* **56. Sobolev inequality for variation.** If $n>1$ and
  $u\in BV(\mathbb R^n)$, then
  $\|u\|_{L^{n/(n-1)}}\leq C_n|Du|(\mathbb R^n)$. Taking $u=1_E$ yields
  the Euclidean isoperimetric inequality for finite-volume finite-perimeter
  sets. On a ball, subtracting the average gives the corresponding $BV$
  Poincaré inequality.
* **57. Trace and Gauss–Green for $BV$.** On a bounded Lipschitz domain,
  $u\in BV(U)$ has an interior trace $\operatorname{Tr}u\in
  L^1(\partial U,\mathcal H^{n-1})$. For $\phi$ continuously differentiable
  near $\overline U$,
  $$\int_Uu\,\operatorname{div}\phi\,dx+\int_U\phi\cdot dDu
    =\int_{\partial U}\operatorname{Tr}u\,\phi\cdot\nu\,d\mathcal H^{n-1},$$
  where $\nu$ is the outward unit normal defined almost everywhere on the boundary.
* **58. Quasicontinuity of Sobolev functions.** Every
  $u\in W^{1,p}(\mathbb R^n)$, $1\leq p<\infty$, has a representative such
  that for every $\varepsilon>0$ there is an open $G$ of $p$-capacity less than
  $\varepsilon$ for which $u|_{\mathbb R^n\setminus G}$ is continuous.
  The quasicontinuous representative is unique outside a set of capacity zero.

## Reference guide

Bruckner, *Differentiation of Real Functions*, especially Chapters I–V,
VIII, X–XI, and XIII, supplies the derivative, Dini, category, and primitive
viewpoint; Saks and Bruckner–Bruckner–Thomson supply parallel classical
accounts. De Guzmán, *Differentiation of Integrals in $\mathbb R^n$*, develops
the covering and differentiation-basis viewpoint, including the distinctive
behavior of rectangular bases. Thomson's books treat the same circle of ideas.

Evans–Gariepy, *Measure Theory and Fine Properties of Functions*, organizes
the Euclidean sequence of covering, differentiation, Lipschitz, area/coarea,
Sobolev, and $BV$ theory; Federer provides the larger geometric framework.
The local Evans–Gariepy PDF is incomplete: its available opening chapter was
consulted for measure differentiation and approximate continuity; its table of
contents supplies only orientation for the later chapters. The classical
one-dimensional overlap can also be read in Folland, Chapter 3, and
Stein–Shakarchi, Chapter 3, from Section 04. Smooth calculus is represented
in Section 05 by Makarov–Podkorytov and Krantz–Parks. The nonabsolute-integral
part records the common theory treated comparatively by Saks, Henstock, and
Gordon, rather than the specialized extensions of any single text.

Local source anchors:

- [Bruckner, *Differentiation of Real Functions*](References/Bruckner1978DifferentiationRealFunctions-Springer.LNM659.pdf).
- [De Guzmán, *Differentiation of Integrals in $\mathbb R^n$*](References/DeGuzman1975DifferentiationIntegralsRn-Springer.LNM481.pdf).
- [Evans–Gariepy, available incomplete copy](References/EvansGariepy2014MeasureTheoryFinePropertiesFunctions2ndEd-CRCPress.Incomplete.pdf).
- [Federer, *Geometric Measure Theory*](References/Federer1996GeometricMeasureTheory-SpringerClassicsMath.pdf).
- [Makarov–Podkorytov, *Smooth Functions and Maps*](References/MakarovPodkorytov2021SmoothFunctionsMaps-Springer.MoscowLectures07.pdf).
- [Krantz–Parks, *The Implicit Function Theorem*](References/KrantzParks2013ImplicitFunctionTheorem-Birkhauser.MBC.pdf).
