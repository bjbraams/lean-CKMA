# Synopsis: Differentiation and the fine structure of real functions

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-05);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring material from Section 05 of
[CKMA-bib.md](CKMA-bib.md#ckma-05). Its center is the
relation between pointwise derivatives, measures, and integral reconstruction:
what differentiability forces, how it can fail, and which weaker notions survive
for Lipschitz, Sobolev, and bounded-variation functions. Classical smooth calculus
and nonabsolute integration provide the two ends of this spectrum.

The metric and fractal counterparts are in [39A](CKMA-bib.md#ckma-39a);
Section 37 develops rectifiability, BV functions, and geometric integration,
while Section 26 emphasises weak derivatives and function-space mappings.

Here $I$ is a real interval, $U\subseteq\mathbb R^n$ is open, $\mathcal L^n$ is
Lebesgue measure, and $\mathcal H^s$ is Hausdorff measure, normalized so that
$\mathcal H^k$ agrees with $k$-dimensional volume on $k$-planes. Almost-everywhere
statements refer to Lebesgue measure unless another measure is specified.

## Classical derivatives and smooth maps

The **Fréchet derivative** of $f:U\to\mathbb R^m$ at $x$ is the linear map
$Df(x)$ satisfying $f(x+h)=f(x)+Df(x)h+o(|h|)$. A map is $C^k$ if its derivatives
through order $k$ exist and are continuous. A point is **critical** for a map to
$\mathbb R^m$ when its derivative has rank less than $m$. The mean value,
inverse function, and implicit function theorems are stated in Section 35
(SYNOPSIS35, items 2–4).

* **2. Taylor's theorem.** For $f\in C^k(U)$,
  $$f(x+h)=\sum_{j=0}^k\frac{1}{j!}D^jf(x)[h^j]+o(|h|^k).$$
  If $f\in C^{k+1}$ near the segment, the remainder after order $k$ is
  $\frac1{k!}\int_0^1(1-t)^kD^{k+1}f(x+th)[h^{k+1}]\,dt$.
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
* **63. Approximately continuous functions are derivatives.** Every bounded
  approximately continuous function on an interval is a derivative; its
  indefinite Lebesgue integral is differentiable everywhere with that derivative
  (Denjoy). Darboux and Baire class one together do not characterize derivatives:
  $\sin(1/x)$, extended by $a\in[-1,1]$ at $0$, has both properties for every
  $a$ but is a derivative only for $a=0$.
* **9. Dini criterion for monotonicity.** If $f$ is continuous on $[a,b]$ and
  $D^+f(x)\geq0$ at all but countably many $x\in[a,b)$, then $f$ is
  nondecreasing. In particular, $f'\geq0$ off a countable set implies
  monotonicity. An almost-everywhere derivative inequality does not suffice:
  the negative of the Cantor function is a counterexample.
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
$\mathop{\mathrm{Var}}(F)=\sup\sum_i|F(x_i)-F(x_{i-1})|$, over partitions.
The space $BV[a,b]$ consists of functions of finite variation. **Absolute
continuity** means that for every $\varepsilon>0$ some $\delta>0$ makes
$\sum_i|F(b_i)-F(a_i)|<\varepsilon$ whenever disjoint subintervals have total
length below $\delta$. The **Lusin property $(N)$** means that null sets have
null images.

* **12. Jordan's theorem.** A real function has bounded variation exactly when
  it is a difference of two bounded increasing functions. It has finite
  one-sided limits at every point and at most countably many discontinuities,
  each a jump or a removable discontinuity. For continuous $F$, the variation
  function $x\mapsto\mathop{\mathrm{Var}}(F|_{[a,x]})$ is continuous.
* **13. Lebesgue's theorem for monotone functions.** An increasing function is
  differentiable with finite derivative almost everywhere. Its derivative is
  nonnegative and integrable, and
  $\int_a^b F'\leq F(b)-F(a)$. If a series $\sum_kF_k$ of increasing functions
  converges on $[a,b]$, then it may be differentiated termwise almost everywhere
  (Fubini's differentiation theorem).
* **62. Rising sun lemma.** Let $G$ be continuous on $[a,b]$ and let $E$ be
  the set of $x\in(a,b)$ with $G(y)>G(x)$ for some $y\in(x,b]$. Then $E$ is
  open, and on each of its component intervals $(a_k,b_k)$ one has
  $G(a_k)=G(b_k)$, except that $G(a_k)\leq G(b_k)$ when $a_k=a$ (F. Riesz). It
  gives Riesz's proof of result 13 and the one-sided maximal inequality
  $|\{M^+f>\lambda\}|\leq\lambda^{-1}\int_{\{M^+f>\lambda\}}|f|$ for
  $M^+f(x)=\sup_{h>0}h^{-1}\int_x^{x+h}|f|$ and $f\in L^1(\mathbb R)$.
* **14. Differentiation of $BV$ functions.** A function of bounded variation has
  a finite derivative almost everywhere, with
  $\int_a^b|F'|\leq\mathop{\mathrm{Var}}(F)$. Its distributional derivative is a
  finite signed measure on $(a,b)$, after identification of functions equal
  almost everywhere.
* **15. Integral characterization of absolute continuity.** A function $F$ is
  absolutely continuous exactly when $F(x)=F(a)+\int_a^x g(t)\,dt$ for some
  $g\in L^1$. Then $F'=g$ almost everywhere and
  $\mathop{\mathrm{Var}}(F)=\int_a^b|F'|$.
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
* **58. Length and the Banach indicatrix.** An absolutely continuous curve
  $\gamma:[a,b]\to\mathbb R^m$ is rectifiable and
  $$\mathop{\mathrm{length}}(\gamma)=\int_a^b|\gamma'(t)|dt.$$
  For every continuous real $F$ on $[a,b]$, Banach's indicatrix theorem gives
  $$\mathop{\mathrm{Var}}(F)=\int_{\mathbb R}\#\{t\in[a,b]:F(t)=y\}\,dy,$$
  both sides possibly infinite: total variation counts level crossings with
  multiplicity.

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
  covering of an arbitrary set $E\subseteq\mathbb R^n$, a countable disjoint
  subfamily covers $E$ up to a Lebesgue null set.
* **23. Besicovitch covering theorem.** If a bounded set $E\subseteq\mathbb R^n$
  is supplied with a closed ball centered at each of its points, the radii
  being bounded, one can select a countable covering of $E$ with overlap bounded by a constant
  depending only on $n$. The stronger finite-family decomposition into disjoint
  subfamilies underlies differentiation for arbitrary Radon measures.
* **24. Whitney decomposition.** A nonempty proper open subset of $\mathbb R^n$
  is the union of a countable family of closed dyadic cubes with disjoint
  interiors, whose diameters are comparable to their distances from the
  complement. Slight enlargements can be chosen with bounded overlap.
* **25. Weak maximal inequality.** There is $C_n$ such that
  $$|\{Mf>\lambda\}|\leq\frac{C_n}{\lambda}\|f\|_1
    \qquad(\lambda>0).$$
  For the centred maximal function one may take $C_n=3^n$, by the finite
  Vitali selection of disjoint balls whose threefold enlargements cover.
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
* **65. Stein's maximal principle.** Let a compact group act transitively on a
  probability space $X$ preserving its measure, let $1\leq p\leq2$, and let
  $T_n$ be bounded linear operators on $L^p(X)$ commuting with the action. If
  $\sup_n|T_nf|<\infty$ almost everywhere for every $f\in L^p(X)$, then
  $f\mapsto\sup_n|T_nf|$ is of weak type $(p,p)$. Thus almost-everywhere
  convergence on $L^p$ forces a maximal inequality, and failure of the maximal
  inequality yields divergence for some $f\in L^p$.

## Lipschitz functions and approximate differentiation

A map is **$L$-Lipschitz** if $|f(x)-f(y)|\leq L|x-y|$.
A measurable $f:U\to\mathbb R^m$ is **approximately differentiable** at $x$ if
some linear $A$ satisfies
$\mathop{\mathrm{ap\,lim}}\limits_{y\to x}|f(y)-f(x)-A(y-x)|/|y-x|=0$; an approximate
limit excludes a set of density zero. A **weak derivative** $D_i f=g$ satisfies
$\int f\partial_i\phi=-\int g\phi$ for all $\phi\in C_c^\infty(U)$.
The **Sobolev space** $W^{1,p}(U)$ consists of $L^p$ functions whose first weak
derivatives are in $L^p$; its local version imposes this on relatively compact
open subsets. Approximate differentiability depends only on the
almost-everywhere equivalence class, and the approximate derivative is unique
where it exists.

* **32. McShane–Whitney extension.** Every real $L$-Lipschitz function on a
  nonempty subset $A$ of a metric space extends to the whole space with the same
  Lipschitz constant; extremal extensions are given by
  $\inf_{a\in A}(f(a)+Ld(x,a))$ and $\sup_{a\in A}(f(a)-Ld(x,a))$.
* **33. Kirszbraun's theorem.** An $L$-Lipschitz map from a subset of Euclidean
  space to another Euclidean space extends with the same constant. The theorem
  also holds for real Hilbert spaces. For $\mathbb R^m$-valued maps,
  componentwise McShane extension may multiply the Lipschitz constant by
  $\sqrt m$.
* **34. Rademacher's theorem.** A locally Lipschitz map
  $f:U\to\mathbb R^m$ is Fréchet differentiable almost everywhere, and
  $\|Df(x)\|$ is bounded by its Lipschitz constant wherever the derivative exists.
  A Lipschitz map agrees with a $C^1$ map outside a set of arbitrarily small
  measure.
* **64. Stepanov's theorem.** An arbitrary map $f:U\to\mathbb R^m$ is
  differentiable at almost every point of the set where
  $\limsup_{y\to x}|f(y)-f(x)|/|y-x|<\infty$.
* **35. Lipschitz maps in infinite dimensions.** If $X$ is a separable Banach
  space and $Y$ has the Radon–Nikodým property, every Lipschitz $f:X\to Y$ is
  Gâteaux differentiable outside an Aronszajn-null (in particular Haar-null)
  set (Aronszajn, Christensen, Mankiewicz). Fréchet differentiability is subtler:
  a real Lipschitz function on an Asplund space is Fréchet differentiable on a
  dense set (Preiss), and the size of its exceptional set is governed by porous
  and $\Gamma$-null sets rather than by Haar-null sets
  (Lindenstrauss–Preiss–Tišer).
* **36. Absolute continuity on lines.** A function in
  $W^{1,p}_{\mathrm{loc}}(U)$, $1\leq p\leq\infty$, has a representative
  absolutely continuous on almost every line segment parallel to a coordinate
  axis, locally in $U$. Its classical derivatives there are the weak partial
  derivatives. Conversely, this property together with local $L^p$
  integrability of the function and these derivatives characterizes
  $W^{1,p}_{\mathrm{loc}}$.
* **37. Lipschitz and $W^{1,\infty}$.** Locally Lipschitz functions belong to
  $W^{1,\infty}_{\mathrm{loc}}$. On a convex open set, a function with globally
  bounded weak gradient has a Lipschitz representative with Lipschitz constant
  at most $\|\nabla f\|_\infty$.
* **38. Convex functions and Aleksandrov's theorem.** A convex function on an
  open convex $U\subseteq\mathbb R^n$ is locally Lipschitz, hence differentiable
  almost everywhere, and its distributional Hessian is a matrix of signed Radon
  measures. It is twice differentiable almost everywhere in the Peano sense:
  for almost every $x$ there is a symmetric $A$ with
  $f(y)=f(x)+\nabla f(x)\cdot(y-x)+\tfrac12(y-x)\cdot A(y-x)+o(|y-x|^2)$, and
  $A$ is the density of the absolutely continuous part of $D^2f$. The a.e.
  Hessian is positive semidefinite.
* **39. Approximate differentiation of Sobolev functions.** Every
  $f\in W^{1,1}_{\mathrm{loc}}(U)$ is approximately differentiable almost
  everywhere, and its approximate derivative equals its weak gradient. For
  $p>n$, $W^{1,p}_{\mathrm{loc}}$ functions are classically differentiable
  almost everywhere; for $n\geq2$ and $p\leq n$ continuous representatives need
  not exist.
* **40. Whitney's Lusin approximation theorem on the line.** A measurable
  function on a compact interval is approximately differentiable almost
  everywhere exactly when, for every $\varepsilon>0$, it agrees with a $C^1$
  function on a closed set whose complement has measure less than
  $\varepsilon$.
* **41. Lusin approximation of Sobolev functions.** If
  $f\in W^{1,1}_{\mathrm{loc}}(U)$ and $U$ has finite measure, then for every
  $\varepsilon>0$ there are a compact $K\subset U$ with $|U\setminus K|<\varepsilon$
  and $g\in C^1(\mathbb R^n)$ such that $g=f$ and $Dg=Df$ almost everywhere on
  $K$.

## Fine properties of $BV$ functions in several variables

A function $u\in L^1(U)$ is in **$BV(U)$** if its distributional gradient $Du$
is a finite vector measure. Its variation has the dual formula
$$|Du|(U)=\sup\left\{\int_Uu\,\mathop{\mathrm{div}}\phi\,dx:
  \phi\in C_c^1(U;\mathbb R^n),\ |\phi|\leq1\right\}.$$
A measurable set has **finite perimeter** in $U$ if its locally integrable
indicator has a distributional gradient of finite total variation there; its
perimeter is $P(E,U)=|D1_E|(U)$. No finite-volume assumption on $E$ is imposed.
Section 37 states the theory of $BV$ functions and sets of finite perimeter:
the area and coarea formulas, compactness and approximation, De Giorgi's
structure theorem, slicing, the $BV$ Sobolev inequality, and traces
(SYNOPSIS37, items 13–14, 23–26, 30–32, 36).

* **49. Approximate differentiability and decomposition in $BV$.** Every $BV$
  function is approximately differentiable almost everywhere, and its
  approximate gradient $\nabla u$ is the density of the absolutely continuous
  part of $Du$. Moreover (Federer–Vol'pert)
  $$Du=\nabla u\,\mathcal L^n+(u^+-u^-)\nu_u\,\mathcal H^{n-1}\llcorner J_u
    +D^cu,$$
  where the approximate jump set $J_u$ is countably $(n-1)$-rectifiable with
  one-sided approximate limits $u^\pm$ and normal $\nu_u$, and the Cantor part
  $D^cu$ vanishes on Borel sets of $\sigma$-finite $\mathcal H^{n-1}$ measure.
  $|Du|$ vanishes on $\mathcal H^{n-1}$-null sets.

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

* **51. Existence of fine partitions.** Every positive gauge on a compact
  interval admits a fine tagged partition (Cousin's lemma). The gauge integral,
  when it exists, is therefore unique and is additive over adjacent intervals.
* **52. Extension of the Lebesgue integral.** Every Lebesgue-integrable function
  is Henstock–Kurzweil integrable with the same integral. A function and its
  absolute value are both gauge integrable exactly when it is Lebesgue integrable.
* **53. Integration of derivatives.** If $F$ is continuous on $[a,b]$ and has a
  finite derivative at all but countably many interior points, then $F'$
  (defined arbitrarily on the exceptional set) is Henstock–Kurzweil integrable and
  $$\int_a^bF'(x)\,dx=F(b)-F(a).$$
  Consequently, if $F$ is differentiable at every point of $[a,b]$ and
  $F'\in L^1$, then $F$ is absolutely continuous and the formula holds for the
  Lebesgue integral; without integrability of $F'$ (e.g.
  $x^2\sin(x^{-2})$) only the gauge integral reconstructs $F$.
* **54. Fundamental theorem for the gauge integral.** The indefinite
  Henstock–Kurzweil integral is continuous and has derivative equal to its
  integrand almost everywhere. Conversely, its primitives are precisely the
  generalized absolutely continuous functions in the restricted sense
  ($ACG_*$), with the additive constant fixed.
* **55. Equivalence of the classical nonabsolute integrals.** The
  Henstock–Kurzweil, Perron, and restricted Denjoy integrals on a compact
  interval have the same integrable functions and the same values. This
  equivalence does not identify them with the more permissive wide Denjoy integral.

## Extension, traces, and further fine properties

A **first-order jet** on a closed set $E$ is prescribed value and derivative
data $(f,p)$ with $p:E\to\mathbb R^n$. Traces of $BV$ functions are stated in
Section 37 (SYNOPSIS37, item 26), and Sobolev capacity and quasicontinuity in
Section 26 (SYNOPSIS26, item 31).

* **56. Whitney's $C^1$ extension theorem.** For compact $E\subseteq\mathbb R^n$,
  continuous data $f:E\to\mathbb R$, $p:E\to\mathbb R^n$ extend to
  $F\in C^1(\mathbb R^n)$ with $F|_E=f$, $\nabla F|_E=p$ if and only if
  $$f(y)-f(x)-p(x)\cdot(y-x)=o(|y-x|)$$
  uniformly for $x,y\in E$ as $|x-y|\to0$.

## Reference guide

Bruckner, *Differentiation of Real Functions*, especially Chapters I–V,
VIII, X–XI, and XIII, supplies the derivative, Dini, category, and primitive
viewpoint; Saks and Bruckner–Bruckner–Thomson supply parallel classical
accounts. De Guzmán, *Differentiation of Integrals in $\mathbb R^n$*, develops
the covering and differentiation-basis viewpoint, including the distinctive
behavior of rectangular bases. Thomson's books treat the same circle of ideas.

Evans–Gariepy, *Measure Theory and Fine Properties of Functions*, organizes
the Euclidean sequence of covering, differentiation, Lipschitz, area/coarea,
Sobolev, and $BV$ theory, including Aleksandrov's theorem (Section 6.4); the
several-variable $BV$ and area/coarea statements are now in Section 37.
Federer provides the
larger geometric framework, and Ambrosio–Fusco–Pallara the standard account of
the Federer–Vol'pert decomposition. Differentiability of Lipschitz maps on
Banach spaces is the subject of Lindenstrauss–Preiss–Tišer.
The local Evans–Gariepy PDF is incomplete: its available opening chapter was
consulted for measure differentiation and approximate continuity; its table of
contents supplies only orientation for the later chapters. The classical
one-dimensional overlap can also be read in Folland, Chapter 3, and
Stein–Shakarchi, Chapter 3, from Section 04. Smooth calculus is represented
in the bibliography by Makarov–Podkorytov, *Smooth Functions and Maps*, and
Krantz–Parks, *The Implicit Function Theorem*, both listed in Section 35, not
Section 05. The nonabsolute-integral
part records the common theory treated comparatively by Saks, Henstock, and
Gordon, rather than the specialized extensions of any single text.
Approximate continuity of derivatives (result 63) is in Bruckner, Chapters II
and III; the rising sun lemma in Stein–Shakarchi, Chapter 3; Stepanov's theorem
in Federer, 3.1.9, and Heinonen's *Lectures on Lipschitz Analysis*; and Stein's
maximal principle in Garsia, *Topics in Almost Everywhere Convergence*.

Local source anchors:

- [Bruckner, *Differentiation of Real Functions*](References/Bruckner1978DifferentiationRealFunctions-Springer.LNM659.pdf).
- [De Guzmán, *Differentiation of Integrals in $\mathbb R^n$*](References/DeGuzman1975DifferentiationIntegralsRn-Springer.LNM481.pdf).
- [Evans–Gariepy, available incomplete copy](References/EvansGariepy2014MeasureTheoryFinePropertiesFunctions2ndEd-CRCPress.Incomplete.pdf).
- [Federer, *Geometric Measure Theory*](References/Federer1996GeometricMeasureTheory-SpringerClassicsMath.pdf).
- [Makarov–Podkorytov, *Smooth Functions and Maps*](References/MakarovPodkorytov2021SmoothFunctionsMaps-Springer.MoscowLectures07.pdf).
- [Krantz–Parks, *The Implicit Function Theorem*](References/KrantzParks2013ImplicitFunctionTheorem-Birkhauser.MBC.pdf).
