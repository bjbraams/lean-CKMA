# Synopsis: Differentiation and the fine structure of real functions

Part of the [mathematical synopsis series](SYNOPSIS.md).

This synopsis selects recurring material from Section 05 of
[CKMA-bib.md](CKMA-bib.md). Its center is the
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
$\operatorname{Var}(F)=\sup\sum_i|F(x_i)-F(x_{i-1})|$, over partitions.
The space $BV[a,b]$ consists of functions of finite variation. **Absolute
continuity** means that for every $\varepsilon>0$ some $\delta>0$ makes
$\sum_i|F(b_i)-F(a_i)|<\varepsilon$ whenever disjoint subintervals have total
length below $\delta$. The **Lusin property $(N)$** means that null sets have
null images.

* **12. Jordan's theorem.** A real function has bounded variation exactly when
  it is a difference of two bounded increasing functions. It has finite
  one-sided limits at every point and at most countably many discontinuities,
  each a jump or a removable discontinuity. For continuous $F$, the variation
  function $x\mapsto\operatorname{Var}(F|_{[a,x]})$ is continuous.
* **13. Lebesgue's theorem for monotone functions.** An increasing function is
  differentiable with finite derivative almost everywhere. Its derivative is
  nonnegative and integrable, and
  $\int_a^b F'\leq F(b)-F(a)$. If a series $\sum_kF_k$ of increasing functions
  converges on $[a,b]$, then it may be differentiated termwise almost everywhere
  (Fubini's differentiation theorem).
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
open subsets. Approximate differentiability depends only on the
almost-everywhere equivalence class, and the approximate derivative is unique
where it exists.

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
* **35. Lipschitz maps in infinite dimensions.** If $X$ is a separable Banach
  space and $Y$ has the Radon–Nikodým property, every Lipschitz $f:X\to Y$ is
  Gâteaux differentiable outside an Aronszajn-null (in particular Haar-null)
  set (Aronszajn, Christensen, Mankiewicz). Fréchet differentiability is subtler:
  a real Lipschitz function on an Asplund space is Fréchet differentiable on a
  dense set (Preiss), but its exceptional set need not be Haar-null; porous and
  $\Gamma$-null sets govern this theory (Lindenstrauss–Preiss–Tišer).
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
  $A$ is the density of the absolutely continuous part of $D^2f$.
* **39. Approximate differentiation of Sobolev functions.** Every
  $f\in W^{1,1}_{\mathrm{loc}}(U)$ is approximately differentiable almost
  everywhere, and its approximate derivative equals its weak gradient.
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
* **42. Area formula.** For Lipschitz $f:\mathbb R^n\to\mathbb R^m$, $n\leq m$,
  measurable $A$, and nonnegative measurable $g$,
  $$\int_A g(x)J_nf(x)\,dx
    =\int_{\mathbb R^m}\sum_{x\in A\cap f^{-1}(y)}g(x)\,d\mathcal H^n(y),$$
  where $J_nf=\sqrt{\det(Df^{\mathsf T}Df)}$ almost everywhere. For injective
  maps this is change of variables onto the image.
* **43. Coarea formula.** For Lipschitz $f:\mathbb R^n\to\mathbb R^m$, $n\geq m$,
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

* **44. Lower semicontinuity.** If $u_j\to u$ in $L^1_{\mathrm{loc}}(U)$, then
  $|Du|(U)\leq\liminf_j|Du_j|(U)$, with infinite variation allowed.
* **45. Smooth approximation.** Every $u\in BV(U)$ admits smooth
  $u_j\in C^\infty(U)\cap BV(U)$ with $u_j\to u$ in $L^1(U)$ and
  $\int_U|\nabla u_j|\,dx\to|Du|(U)$.
* **46. Compactness.** On a bounded Lipschitz domain, bounded subsets of
  $BV(U)$ are relatively compact in $L^1(U)$. Local versions hold on arbitrary
  open sets with uniform local bounds.
* **47. $BV$ coarea.** For real $u\in BV(U)$,
  $$|Du|(U)=\int_{-\infty}^{\infty}P(\{u>t\},U)\,dt.$$
  Thus almost all superlevel sets have finite perimeter.
* **48. De Giorgi's structure theorem.** Let $E$ have locally finite perimeter
  in $\mathbb R^n$ and let $\partial^*E$ be its reduced boundary, the set of
  points $x$ of $\operatorname{supp}|D1_E|$ where
  $\nu_E(x)=-\lim_{r\downarrow0}D1_E(B(x,r))/|D1_E|(B(x,r))$ exists with
  $|\nu_E(x)|=1$. Then $\partial^*E$ is countably $(n-1)$-rectifiable,
  $|D1_E|=\mathcal H^{n-1}\llcorner\partial^*E$, and
  $$\int_E\operatorname{div}\phi\,dx=\int_{\partial^*E}\phi\cdot\nu_E
    \,d\mathcal H^{n-1}\qquad(\phi\in C^1_c(\mathbb R^n;\mathbb R^n)).$$
  The measure-theoretic boundary (points of density neither $0$ nor $1$) differs
  from $\partial^*E$ by an $\mathcal H^{n-1}$-null set (Federer).
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
* **50. Slicing.** For $u\in BV(U)$, restrictions to almost every line parallel
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
data $(f,p)$ with $p:E\to\mathbb R^n$. For $1\leq p<\infty$, the
**Sobolev $p$-capacity** of $E\subseteq\mathbb R^n$ is the infimum of
$\|v\|_{W^{1,p}(\mathbb R^n)}^p$ over Sobolev functions $v$ that are at least
one almost everywhere on some open neighborhood of $E$. Small capacity is a
stronger notion of exceptional size than small Lebesgue measure. Traces below
are defined by approach from inside the domain, not by arbitrary values assigned
on its boundary to an $L^1$ representative.

* **56. Whitney's $C^1$ extension theorem.** For compact $E\subseteq\mathbb R^n$,
  continuous data $f:E\to\mathbb R$, $p:E\to\mathbb R^n$ extend to
  $F\in C^1(\mathbb R^n)$ with $F|_E=f$, $\nabla F|_E=p$ if and only if
  $$f(y)-f(x)-p(x)\cdot(y-x)=o(|y-x|)$$
  uniformly for $x,y\in E$ as $|x-y|\to0$.
* **57. Lipschitz control of exceptional sets.** An $L$-Lipschitz map satisfies
  $\mathcal H^s(f(E))\leq L^s\mathcal H^s(E)$ for $s>0$. In particular,
  Lipschitz maps $\mathbb R^n\to\mathbb R^n$ have property $(N)$. This
  measure control, together with almost-everywhere differentiability, is a
  principal reason area and change-of-variables formulas extend beyond $C^1$ maps.
* **58. Length and the Banach indicatrix.** An absolutely continuous curve
  $\gamma:[a,b]\to\mathbb R^m$ is rectifiable and
  $$\operatorname{length}(\gamma)=\int_a^b|\gamma'(t)|dt.$$
  For every continuous real $F$ on $[a,b]$, Banach's indicatrix theorem gives
  $$\operatorname{Var}(F)=\int_{\mathbb R}\#\{t\in[a,b]:F(t)=y\}\,dy,$$
  both sides possibly infinite: total variation counts level crossings with
  multiplicity.
* **59. Sobolev inequality for variation.** If $n>1$ and
  $u\in BV(\mathbb R^n)$, then
  $\|u\|_{L^{n/(n-1)}}\leq C_n|Du|(\mathbb R^n)$. Taking $u=1_E$ yields
  the Euclidean isoperimetric inequality for finite-volume finite-perimeter
  sets. On a ball, subtracting the average gives the corresponding $BV$
  Poincaré inequality.
* **60. Trace and Gauss–Green for $BV$.** On a bounded Lipschitz domain,
  $u\in BV(U)$ has an interior trace $\operatorname{Tr}u\in
  L^1(\partial U,\mathcal H^{n-1})$. For $\phi$ continuously differentiable
  near $\overline U$,
  $$\int_Uu\,\operatorname{div}\phi\,dx+\int_U\phi\cdot dDu
    =\int_{\partial U}\operatorname{Tr}u\,\phi\cdot\nu\,d\mathcal H^{n-1},$$
  where $\nu$ is the outward unit normal defined almost everywhere on the boundary.
* **61. Quasicontinuity of Sobolev functions.** Every
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
Sobolev, and $BV$ theory, including the structure of sets of finite perimeter
(Section 5.7) and Aleksandrov's theorem (Section 6.4); Federer provides the
larger geometric framework, and Ambrosio–Fusco–Pallara the standard account of
the Federer–Vol'pert decomposition. Differentiability of Lipschitz maps on
Banach spaces is the subject of Lindenstrauss–Preiss–Tišer.
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
