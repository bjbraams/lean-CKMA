# Library review of GAPS.md, October 2026

## Second review: 19 October 2026

The current selection in [GAPS.md](GAPS.md) has **584 entries**, down from
616 at the start of this review. **32 entries were removed or consolidated**
and **13 retained entries were narrowed or clarified**. Synopsis identifiers
are preserved. Coverage links now point to `STRUCTURExx.md`.

This review used the local source trees of
[Mathlib](https://github.com/leanprover-community/mathlib4/tree/911003dd6dea5df215dff57f2717be762e11a6ca)
at `911003dd6dea5df215dff57f2717be762e11a6ca` and
[TauCeti](https://github.com/TauCetiProject/TauCeti/tree/5cdecf40e99d5a5ad0833afff31f5b007d68a149)
at `5cdecf40e99d5a5ad0833afff31f5b007d68a149`; both commits are dated
18 October 2026. Paths below are relative to the respective repository root.
All 616 selected assertions were revisited, with closer dependency checks for
compound statements and the borderline decisions from the first review.

The Mathlib changes since the first review concern valuations. TauCeti's changes
include weakly compact operators, finite-rank approximation, basis refinements,
conformal boundary-cluster results and manifold Sard theory. These do not supply
the major missing stochastic, microlocal, geometric-flow or global spectral
theories. In particular, its new completely continuous operators concern
approximation by finite-rank maps; this terminology does not establish the
Dunford–Pettis compactness theorem for subsets of $L^1$.

### Criterion and status of the evidence

The stricter criterion is substantial missing mathematics. Absence of a named
Lean declaration, an unbundled definition, or routine specialization and
composition does not justify selection. Conversely, existence cannot be inferred
from consequences stated conditionally on an existing solution. Generality,
scalar field, boundary regularity, summability and endpoint hypotheses matter.

The decisions below distinguish two reasons for removal:

* **Routine derivation:** the mathematical ingredients already exist, and the
  argument is given below. This is a source-based assessment of mathematical
  effort, not a claim that the resulting Lean adapter has been written or compiled.
* **Consolidation:** the remaining difficult step is already selected elsewhere;
  the additional assertion is a routine consequence of that step. This does not
  declare the prerequisite, or the dependent theorem, already formalized.

Existing source declarations were inspected, including their hypotheses and proof
bodies; admissions and roadmap text were excluded. No new Lean theorem was proved
in this documentation review. Some derived results will still require definition,
transport and measurability code. Such code alone does not make them principal
mathematical gaps under the requested criterion.

### Removed entries: routine derivations

* **13.7, Cauchy interlacing; 13.8, index-shifted Weyl inequalities.**
  TauCeti `Analysis/InnerProductSpace/CourantFischer.lean` supplies the
  variational theorem and the subspaces realizing its bounds, including
  `exists_submodule_forall_unit_eigenvalue_le_re_inner` and
  `exists_unit_vector_re_inner_le_eigenvalue`. For a compression, intersect
  a spectral subspace with the compressed space and use the elementary
  dimension bound. For Weyl, intersect the relevant spectral subspaces of
  $A$, $B$ and $A+B$; a unit vector in the intersection compares their
  Rayleigh quotients. Intersecting with the kernel of a rank-$k$ perturbation
  gives the rank-shift version. The existing theorem is stronger than just
  the previously cited same-index perturbation bound.

* **13.13, arbitrary-matrix von Neumann trace inequality.** TauCeti
  `Analysis/InnerProductSpace/SingularValues.lean` supplies the full finite
  singular-value decomposition, including
  `exists_linearIsometryEquiv_eq_comp_toLin_diagonal_comp`.
  `Analysis/InnerProductSpace/KyFan.lean`, `norm_sum_inner_le_kyFanSum`,
  bounds every initial sum of singular-vector matrix coefficients; phases
  can be absorbed into one orthonormal family to bound sums of their absolute
  values. Expand $B$ in its singular vectors, weight these prefix bounds by
  the decreasing singular values of $B$, and apply finite summation by parts.
  This gives $|\operatorname{tr}(A^*B)|\le\sum_i s_i(A)s_i(B)$.
  The normal-matrix Hoffman–Wielandt matching problem is a different theorem
  and remains in 13.10.

* **14.40, Nash inequality.** Mathlib
  `Analysis/Fourier/LpSpace.lean` gives Plancherel;
  `Analysis/Fourier/FourierTransform.lean` gives the $L^1$ Fourier bound,
  and `Analysis/Fourier/FourierTransformDeriv.lean` identifies derivatives.
  Split $\|\widehat f\|_2^2$ into $|\xi|\le R$ and its complement:
  $$\|f\|_2^2\le C_nR^n\|f\|_1^2+
    (2\pi R)^{-2}\|\nabla f\|_2^2.$$
  Optimizing $R>0$ gives the stated non-sharp inequality in every positive
  dimension; zero cases are immediate. Smooth approximation extends it to
  its natural $L^1\cap H^1$ domain. No sharp Nash constant was selected.

* **20.40, Wiener inverse lemma and its holomorphic extension.** Mathlib
  `Analysis/CStarAlgebra/GelfandDuality.lean` proves
  `WeakDual.CharacterSpace.exists_apply_eq_zero` and
  `WeakDual.CharacterSpace.mem_spectrum_iff_exists` for arbitrary commutative
  complex Banach algebras, before imposing the C*-identity. Use convolution
  on $\ell^1(\mathbb Z)$: Young's bound, summation and completeness supply
  its Banach-algebra structure. A character is determined by the unit shift;
  the shift and its inverse both have norm one, so its value has modulus
  one. Density of finitely supported sequences identifies that character
  with Fourier evaluation. The existing character theorem therefore makes
  a nowhere-zero Fourier series invertible in $\ell^1$. The inverse lemma
  needs algebra setup and this short identification, rather than a new
  spectral theorem. The stronger holomorphic-closure clause depends on the
  general holomorphic calculus already selected in 20.7 and is consolidated
  there; it is not asserted already formalized.

* **21.11, Atkinson theorem.** Mathlib
  `Analysis/Normed/Operator/Fredholm/Basic.lean` characterizes Fredholmness
  by a finite-rank quasi-inverse. TauCeti
  `Analysis/Fredholm/CompactPerturbation.lean` proves `isFredholm_one_add`
  for compact perturbations of the identity. If $ST-I$ and $TS-I$ are
  compact, both products are Fredholm. Then $\ker T\subseteq\ker(ST)$
  is finite-dimensional, while $\operatorname{ran}(TS)\subseteq
  \operatorname{ran}T$ makes the cokernel finite-dimensional. TauCeti's
  finite-kernel/cokernel criterion in `Analysis/Fredholm/ClosedRange.lean`
  finishes the proof; its compact-perturbation proof already uses precisely
  these inclusions. The forward implication uses the existing finite-rank
  quasi-inverse. Expressing the result in the quotient by the compact
  operator ideal adds quotient-algebra packaging, not a new spectral theorem.

* **25.54, Tikhonov minimizer.** Apply Mathlib
  `Analysis/InnerProductSpace/LaxMilgram.lean` to
  $B(u,v)=\operatorname{Re}\langle Ku,Kv\rangle+
  \alpha\operatorname{Re}\langle u,v\rangle$, $\alpha>0$.
  The resulting solution satisfies $(K^*K+\alpha I)u=K^*f^\delta$;
  expanding the quadratic functional proves unique minimality. For complex
  Hilbert spaces use realification; the normal equation recovers complex
  linearity. This does not supply convergence rates or other inverse-problem
  estimates.

* **27.4, Hausdorff–Young and failure above $2$.** TauCeti
  `MeasureTheory/Integral/RieszThorin.lean`, applied between the $L^1\to
  L^\infty$ Fourier bound and Mathlib's Plancherel isometry, gives the
  positive range, first on simple functions and then by density. The negative
  assertion also has a short existing route: Mathlib
  `Analysis/SpecialFunctions/Gaussian/FourierTransform.lean` proves the complex
  Gaussian formula for every parameter of positive real part. For
  $f_t(x)=e^{-\pi(1+it)|x|^2}$, $\|f_t\|_p$ is constant, while
  $\|\widehat f_t\|_{p'}$ grows as
  $(1+t^2)^{d(1/(2p')-1/4)}$ for $p>2$, in positive dimension.
  Thus the counterexample part was checked as well as interpolation.

* **27.13, Heisenberg uncertainty.** On Schwartz functions, integrate
  $\partial_j(x_j|f|^2)$, then apply Cauchy–Schwarz and the derivative
  Fourier identity from Mathlib `Analysis/Fourier/FourierTransformDeriv.lean`
  together with Plancherel. This gives the constant $1/(4\pi)$ for the
  library's Fourier normalization. Cutoff and mollification pass to finite
  position and frequency moments; TauCeti's weak-derivative/Bessel-potential
  identification in `Analysis/Sobolev/BesselPotential/Basic.lean` supplies
  the derivative interpretation. Translation and modulation center the
  moments. Mathlib's Gaussian Fourier formula supplies equality examples.
  No stronger uncertainty principle is inferred.

* **28.2, modular continuity and inversion.** Mathlib
  `MeasureTheory/Group/ModularCharacter.lean` already expresses its character
  $D(g)$ as $\int f(xg)\,d\mu/\int f\,d\mu$, for a fixed nonnegative
  nonzero compactly supported continuous $f$.
  `MeasureTheory/Measure/Haar/Unique.lean`,
  `continuous_integral_apply_inv_mul`, applied to the inverse-pushforward
  measure, gives continuity of the numerator; the denominator is positive.
  Thus the explicit source TODO about continuity is a missing declaration,
  not a principal mathematical gap. Inversion pushes $\mu$ to a right Haar
  measure, as is checked by the group identities. The positive continuous
  density $D$ also makes $D\mu$ a right Haar measure. Haar uniqueness,
  applied to the opposite group, gives $\operatorname{inv}_*\mu=cD\mu$.
  Applying inversion twice and using $D(g^{-1})D(g)=1$ gives $c^2=1$,
  hence $c=1$. The synopsis uses $\Delta_G=D^{-1}$, so its inversion density
  is $\Delta_G(x^{-1})=D(x)$. This reciprocal convention is now explicit
  in GAPS.md; substituting Mathlib's character without this conversion
  would give the wrong density. No general quotient integration is inferred.

* **29.2, frame operator criterion; 29.3, canonical dual reconstruction.**
  A Bessel bound constructs a bounded analysis map $C:H\to\ell^2$;
  synthesis is its adjoint and $S=C^*C$. The lower frame bound is precisely
  coercivity of $S$, so Lax–Milgram gives its inverse. Conversely, an inverse
  of $S$ bounds $C$ below. Surjectivity of $C^*$ gives the same bound by the
  open mapping theorem and the adjoint identity. Reconstruction follows by
  applying the synthesis map to Mathlib's unconditional coordinate expansion
  `lp.hasSum_single` in `Analysis/Normed/Lp/lpSpace.lean`. Apply this also
  to $S^{-1}$ for the canonical dual; the two reciprocal optimal bounds
  follow from the positive-operator inequalities. Mathlib's adjoints,
  coercive forms and open mapping theorem suffice for infinite sequences;
  TauCeti's finite `Analysis/InnerProductSpace/Frame.lean` was not mistaken
  for an infinite-frame theorem.

* **29.38, STFT orthogonality.** For Schwartz inputs, apply Mathlib's
  `MeasureTheory.Lp.inner_fourier_eq` in `Analysis/Fourier/LpSpace.lean`
  at each translation, then Fubini and translation invariance of Lebesgue
  measure. This gives the stated four-function identity and the bilinear
  $L^2$ norm bound. Schwartz density and that bound extend the identity to
  four arbitrary $L^2$ inputs. This does not construct Gabor frames or prove
  their density theorems.

* **31.26, LaSalle principle.** Mathlib `Dynamics/OmegaLimit.lean` supplies
  compactness, nonemptiness, invariance and eventual neighborhoods of an
  omega-limit set of a compactly trapped orbit. In TauCeti
  `Dynamics/Flow/Lyapunov.lean`, the proof of finite-rest-set convergence
  already shows that $V$ is constant on the omega-limit set and along its
  orbits before using finiteness. For a positively invariant compact subset,
  bounded monotonicity of $V$ gives the same argument: the omega-limit set is
  contained in the largest invariant subset of $\{\dot V=0\}$, and the
  trajectory approaches it. Finiteness is needed only to deduce convergence
  to a single point, not for LaSalle's conclusion.

* **32.2, smooth transport with a given complete characteristic flow.**
  Compose with the assumed smooth flow, apply the chain rule and the
  fundamental theorem of calculus, and compose with the inverse flow.
  These are Mathlib calculus results; constructing a rough flow or proving
  transport renormalization is not part of the stated result. The latter
  remains a gap in Section 34.

* **33.55, elementary obstacle variational inequality.** Mathlib
  `Analysis/InnerProductSpace/Convex.lean` gives projection onto a nonempty
  complete convex set and its variational characterization. TauCeti's
  $H^1_0$ space, zero-boundary Poincaré estimate and Lax–Milgram solution
  allow the Dirichlet energy to be used as the equivalent Hilbert norm;
  the obstacle constraint is closed and convex, by the closed order cone
  in $L^2$. Shift the affine boundary class and project the unconstrained
  solution onto this nonempty constraint set. Its projection inequality is
  exactly the displayed PDE inequality. This supplies no optimal regularity
  or free-boundary theorem; 33.57 and 33.61 remain.

* **34.23, free Schrödinger estimate.** TauCeti
  `Analysis/Fourier/L2Multiplier.lean` constructs bounded Fourier multipliers
  with composition and adjoint identities. The symbol $e^{-4\pi^2it|\xi|^2}$
  has modulus one, giving $L^2$ unitarity and preservation of each Fourier
  $H^s$ norm. Mathlib's complex Gaussian Fourier formula, regularized by
  $\varepsilon>0$ and passed to the limit on Schwartz functions, gives the
  kernel $(4\pi it)^{-d/2}e^{i|x|^2/(4t)}$. Its constant modulus gives
  the $L^1\to L^\infty$ bound, extended by density and compatibility with
  the $L^2$ multiplier. Strichartz and nonlinear evolution remain selected.

* **36.1, Euler–Lagrange first variation.** Mathlib
  `Analysis/Calculus/ParametricIntegral.lean` proves dominated
  differentiation under the integral, including
  `hasFDerivAt_integral_of_dominated_of_fderiv_le`.
  Differentiate along a compactly supported variation and use vanishing
  derivative at a local minimum. Weak integration by parts gives the weak
  equation; in the regular case the fundamental lemma is supplied by
  `Analysis/Distribution/AEEqOfIntegralContDiff.lean`,
  `ae_eq_zero_of_integral_contDiff_smul_eq_zero`.
  The original assertion already assumes derivative growth bounds sufficient
  to justify the differentiation; existence of minimizers is not inferred.

* **36.12, convex integral weak lower semicontinuity.** Norm convergence
  in $L^p$ gives an almost-everywhere convergent subsequence; continuity of
  a Carathéodory integrand and Fatou give norm lower semicontinuity of the
  nonnegative integral. Its sublevel sets are convex, so Mathlib
  `Analysis/LocallyConvex/WeakSpace.lean`, `Convex.toWeakSpace_closure`,
  makes them weakly closed as well. The weak derivative is continuous
  linear on the Sobolev space, and a continuous linear load preserves weak
  lower semicontinuity. Thus the convex case is routine; the quasiconvex,
  polyconvex and relaxation theorems remain substantial.

* **39.73, self-similar attractor and invariant probability.** Mathlib
  `Topology/UniformSpace/Closeds.lean` provides complete nonempty compact
  subsets with the Hausdorff uniform structure. For a nonempty finite
  contraction family on a complete metric space, the finite-union image map
  contracts that space, so Banach's fixed-point theorem gives the attractor.
  For measures, restrict the maps to this compact attractor. TauCeti's
  `MeasureTheory/OptimalTransport/Wasserstein/Complete.lean`,
  `Pushforward.lean` (`WassersteinSpace.lipschitzWith_map`) and
  `Mixture/Basic.lean` give a complete $W_1$ space and a contracting weighted
  pushforward map. Compact support ensures finite first moments. Uniqueness
  among all invariant probabilities, even without an assumed moment, follows
  by invariance and the estimate $d(S_i x,K)\le c\,d(x,K)$: the probability
  of $d(x,K)>\varepsilon$ is bounded by the tail at $c^{-n}\varepsilon$
  and hence is zero. Fractal dimensions and diffusion are not consequences.

* **43.34, conformal invariance of extremal length.** TauCeti
  `Analysis/Complex/Conformal/Area.lean` gives weighted conformal change of
  variables. Pull a measurable metric density through a conformal bijection:
  multiply it by $|F'|$. Curve lengths transform by the chain rule for
  absolutely continuous parametrizations, and area transforms by $|F'|^2$.
  The extremal-length quotient is unchanged. Apply the inverse map for the
  reverse inequality. This is a change-of-variables consequence, not a
  prime-end or extremal-metric existence theorem.

* **47.66, torus Sobolev widths.** Mathlib's multidimensional torus Fourier
  basis (`Analysis/Fourier/AddCircleMulti.lean`) identifies the embedding
  with the diagonal ellipsoid of weights $(1+|k|^2)^{-s/2}$.
  TauCeti `Analysis/OperatorIdeal/ApproximationNumber/Diagonal.lean`,
  `singularValue_diagonalCLM`, computes its approximation numbers, and
  `ApproximationNumber/MinMax.lean` gives the matching subspace lower bound.
  In a Hilbert target, projection onto each finite-dimensional approximating
  space identifies these numbers with the Kolmogorov widths of the image
  ball. Counting lattice points in cubes above and below a frequency ball
  gives $d_m\asymp m^{-s/d}$ for $s>0$, $d\ge1$. No general nonlinear
  width theory is asserted.

* **48.8, Christoffel–Darboux identity.** Multiply the assumed three-term
  recurrence at $x$ by $p_j(y)$, subtract its version at $y$ times $p_j(x)$,
  and sum over $j$. All intermediate terms telescope; the endpoint term is
  the displayed formula for $x\ne y$. Its diagonal value is the polynomial
  derivative limit. Only finite sums, polynomial algebra and differentiation
  are needed, all present in Mathlib. This does not prove Favard existence,
  general zero geometry or quadrature.

* **48.22, bounded Jacobi operators.** TauCeti
  `Analysis/Normed/Lp/Diagonal.lean`, `lp.diagonalCLM` and
  `norm_diagonalCLM`, gives bounded diagonal coefficient operators.
  Combine these with the norm-one unilateral shift on $\ell^2$:
  $J=S D_a+(S D_a)^*+D_b$ with the corresponding indexing.
  This proves bounded self-adjointness and the stated norm bound.
  Testing the matrix coefficients on unit coordinate vectors bounds the
  coefficients conversely. The unbounded self-adjoint realization and moment
  determinacy correspondence in 48.29 remain missing.

* **51.8, conditional small-norm bound.** Once bounded $C_-$ is assumed,
  $C_w h=C_-(hw)$ satisfies $\|C_w\|\le\|C_-\|\|w\|_\infty$.
  The existing Banach-algebra Neumann inverse solves
  $h=(I-C_w)^{-1}C_-w$, with $\mu=I+h$; this avoids treating the constant
  $I$ as an $L^2$ function on an unbounded contour. Cauchy–Schwarz gives
  the off-contour bound wherever the Cauchy kernel lies in $L^2$.
  The analytic boundary-value/reconstruction theorem is still selected
  in 51.6, and the contour singular-integral theory in 25.25.

* **51.22, formal KdV Lax identity.** Expand the commutator on a smooth
  test function by the Leibniz rule. All positive-order terms cancel and
  the remaining multiplication term is $6uu_x-u_{xxx}$.
  Differentiating the assumed compatible eigenfunction evolution proves
  constancy of its eigenparameter. These are finite calculus identities;
  they do not construct the KdV flow, its unbounded operator domains or its
  scattering evolution, all still substantial.

* **51.46, finite Toda Lax equations.** This is the finite open chain,
  as specified by 51.45–47 in the synopsis. Differentiate the displayed
  exponential coordinates and multiply the tridiagonal matrices.
  Isospectrality follows by solving the finite-dimensional linear equation
  $U'=BU$ and differentiating $U^{-1}JU$; TauCeti's linear ODE theory and
  Mathlib matrix calculus suffice. No infinite-lattice operator theorem,
  global Toda flow construction or inverse spectral theorem is inferred.

### Removed entries: consolidated dependencies

* **12.34, general Moreau decomposition.** The missing everywhere-defined
  Hilbert proximal maps remain in 12.32. Once they exist, TauCeti
  `Analysis/Convex/Subdifferential.lean`,
  `mem_subdifferential_fenchelConjugate_iff`, gives the decomposition directly
  from the resolvent inclusion. The closed-convex-cone case already follows
  from Mathlib's projection variational inequality by testing zero and twice
  the projected point. There is no second substantial gap after 12.32.

* **32.25, nonzero Dirichlet boundary data.** TauCeti already solves the
  weak problem with an $H^1$ lifting. What remains is exactly the fractional
  trace space and bounded right inverse selected in 26.24. Solving the
  zero-trace remainder is existing coercive variational PDE. This removal
  does not claim that the $H^{1/2}$ trace theorem is present.

* **38.33, harmonic measure.** On the bounded barrier-regular domains
  where TauCeti already solves the continuous Dirichlet problem, evaluation
  of the solution is a positive unital bounded linear functional on boundary
  continuous functions. Mathlib's Riesz–Markov theorem represents it by a
  probability measure. Harnack compares positive harmonic functions at two
  poles and hence their representing measures' null sets. For arbitrary
  bounded domains the genuinely missing prerequisite is the upper/lower
  Perron resolutivity in 38.28, where this consequence is now recorded.

* **51.14, conditional parametrix error estimate.** The original assertion
  assumes invertible outer/local models and small matching and remaining
  jumps. Taking their piecewise quotient is an algebraic change of unknown;
  the small-norm estimate and successive corrections are then Neumann
  inversion as in 51.8. The missing analytic boundary and reconstruction
  machinery belongs to 51.6 and 25.25. Building actual asymptotic local
  models is not supplied by this conditional assertion and is not declared
  already available.

### Narrowed or clarified retained entries

* **08.1:** retain Brownian construction and continuous modification.
  Mathlib `MeasureTheory/Constructions/BorelSpace/ContinuousMap.lean`,
  `ContinuousMap.borel_eq_iSup_comap_eval`, together with
  `Probability/Process/FiniteDimensionalLaws.lean`, gives uniqueness on
  continuous path space once those paths exist. Evaluation generates its
  Borel structure under the hypotheses satisfied by $[0,\infty)\to\mathbb R^d$.
* **10.5:** retain $L^1$ almost-everywhere Birkhoff convergence. TauCeti
  `Probability/Ergodic/CondExpProjection.lean`,
  `birkhoffAverage_tendsto_condExpL2` and
  `tendsto_eLpNorm_birkhoffAverage_sub_condExp`, identifies the $L^2$ limit.
  Bounded approximants and the contraction bounds extend norm convergence
  to every finite $p\ge1$: use the finite-measure inclusion for $p<2$,
  and $\|g\|_p^p\le\|g\|_\infty^{p-2}\|g\|_2^2$ for bounded
  differences when $p>2$. This gives no almost-everywhere convergence for
  the full sequence.
* **12.32:** retain general Hilbert proximal existence and the
  minimizer–resolvent identification. Subdifferential monotonicity in
  TauCeti `Analysis/Convex/Subdifferential.lean` gives uniqueness and firm
  nonexpansiveness on the graph directly. Compactness-based minimizer
  existence in `Analysis/GradientFlow/MoreauYosida/Existence.lean` was not
  treated as unrestricted existence. The dependent Moreau identity is
  consolidated here.
* **15.29:** retain the difficult sufficiency in James's compactness theorem;
  the necessary direction is weak continuity plus compact extreme values.
* **15.33:** exclude $p=2$, already Hilbert. TauCeti's Milman–Pettis theorem
  gives reflexivity once the remaining uniform convexity has been proved;
  strict convexity alone does not suffice.
* **18.5:** retain vector-valued duality surjectivity and the RNP equivalence.
  Mathlib `MeasureTheory/Function/Holder.lean` constructs the vector dual
  pairing and its bound. Simple-function norming tests give its isometry,
  using a countable norming family for the separable essential range of a
  strongly measurable dual-valued function. No vector Radon–Nikodým
  representation is obtained from Hölder alone.
* **26.26:** explicitly exclude TauCeti's all-$p$ half-space zero-extension
  criterion `W1p.mem_w1p0Submodule_normalHalfSpace_iff` in
  `Analysis/Sobolev/Trace/Kernel.lean`. Actual flat trace kernels are stated
  for $p=1,2$, and the global Lipschitz chart kernel is $p=2$ in
  `Analysis/Sobolev/LipschitzDomain/Trace/Kernel.lean`. General fractional
  traces and higher normal traces remain substantial.
* **38.28:** retain general resolutivity and consolidate harmonic-measure
  representation as its routine consequence, rather than counting 38.33.
* **39.61:** retain Wasserstein EVI generation and convergence of the full
  implicit scheme. Generic generalized minimizing movements in
  `Analysis/GradientFlow/MinimizingMovement.lean` and conditional EVI
  contraction and semigroup results do not prove this. Clarified the
  initial-state domain: start at finite energy, then extend to its closure;
  arbitrary points outside that closure are not covered.
* **42.1:** retain nontangential boundary values and analytic/boundary
  identification beyond the constructed boundary $H^2$ functions, together
  with the other exponents. TauCeti
  `Analysis/Fourier/Hardy/DiskFunction.lean`,
  `tendsto_eLpNorm_diskFunction_sub`, and Parseval already supply radial
  $L^2$ convergence and its norm identity.
* **49.6:** retain $m\ge3$ in Gamma multiplication. Mathlib
  `Analysis/SpecialFunctions/Gamma/BohrMollerup.lean` already proves
  duplication ($m=2$); $m=1$ is tautological. General multiplication is
  not supplied merely by repeating duplication for arbitrary $m$.
* **51.6:** retain the analytic contour boundary-value and reconstruction
  theorem; consolidate the conditional small-norm and parametrix estimates
  as consequences, without claiming the analytic setup has been formalized.
* **51.50:** retain analytic monodromy preservation and its qualified
  converse. Deriving the Schlesinger equations by differentiating the
  displayed rational connection and comparing coefficients is routine
  calculus and matrix algebra. Local analytic continuation, monodromy and
  normalization under moving poles require additional theory.

### Important gaps retained after checking the apparent shortcuts

* **11.22–24:** weak majorization in a convex set invariant under signs and
  permutations does not itself provide the equal-sum permutohedron
  characterization or all Karamata conclusions. TauCeti's majorization
  results were not substituted without their symmetry hypotheses.
* **13.10:** the Hermitian Hoffman–Wielandt theorem does not give the
  complex normal-matrix eigenvalue matching theorem.
* **15.28 and 17.23:** weakly compact operators and weak compactness of
  reflexive balls do not prove Eberlein–Šmulian or the $L^1$
  uniform-integrability compactness characterization.
* **24.13 and 32.50:** homogeneous semigroup theory and the scalar Fourier
  formulas do not by themselves establish the stated arbitrary-forcing
  Duhamel and energy-space wave solution theorems, including closed-domain
  and time-regularity identifications.
* **26.16:** positive critical Sobolev estimates do not give the stated
  unbounded Sobolev counterexample. A logarithmic cutoff still needs its
  weak derivative and singular integrability established. This was not
  removed merely because a textbook construction is familiar.
* **33.16–18:** the constant-coefficient and small-oscillation estimates
  are genuine coverage, but the full variable-coefficient local/boundary
  statements still require assembled localization, coefficient control and
  regularity arguments. TauCeti does supply a gradient interpolation
  inequality in `Analysis/Sobolev/Wkp/Interpolation.lean`; that useful
  ingredient was counted, rather than described as absent.
* **35.12:** abstract compactness and contraction principles do not yield
  Brouwer's fixed-point theorem without its topological argument.
* **39.61:** generalized-geodesic convexity definitions, uniqueness of a
  minimizing step and conditional EVI estimates do not construct an EVI
  solution. The retained generation step is essential.
* **40.25 and 45.2:** finite meromorphic principal parts do not give arbitrary
  annular Laurent expansions; local analyticity and the polydisc Cauchy
  formula do not by themselves supply the full stated polydisc expansion
  with its convergence and estimates.
* **43.51:** the new inverse boundary-cluster and local-frontier results
  improve specific approach regions. The general homeomorphism of Jordan
  domain closures still needs boundary-fibre connectedness or an equivalent
  argument; the available monotone-extension theorem assumes it.
  *Superseded on 2026-10-19:* TauCeti now proves the homeomorphism of
  Jordan domain closures
  (`exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier`), and
  43.51 has been removed; see the Section 43 record below.
* **52–53:** algebraic curvature/Clifford infrastructure, de Rham operations,
  compact spectral theory and manifold Sard do not supply the selected
  geometric estimates, geometric flows, manifold elliptic parametrices,
  heat asymptotics, Hodge decompositions or analytic index theorems.

### Validation

Checked the 50 section headings, stable synopsis identifiers, recomputed band
counts, nonempty selected-topic groups and local Markdown links. Compared all
root Markdown files with their contents at the start of this review: only
`GAPS.md` and this evidence file were edited. The Mathlib, SYNOPSIS and STRUCTURE
inventories were left untouched. Documentation checks and `git diff --check`
passed. There was no Lean-source edit or Lean build in this review.

## First review: 18 October 2026 (historical record)

The record below describes the earlier 645-to-616 revision and its earlier source
pins. Its KEEP and borderline decisions are historical; the second review above
supersedes them wherever it records a removal or narrowing. Its original counts
are preserved to make the sequence of revisions auditable.

This file records the evidence behind the October 2026 revision of [GAPS.md](GAPS.md).
Every numbered entry was checked against fresh source trees of
[Mathlib](https://github.com/leanprover-community/mathlib4) at commit
`f039e1b8a616d45782a5c7fc5e7909249c36b8ea` and
[TauCeti](https://github.com/TauCetiProject/TauCeti) at commit
`6ebb29f84b4d6e2019233da0718776a6e32e1526`, both dated 2026-10-18. The `Mathlibxx.md`
inventories and [TauCetiCoverage.md](TauCetiCoverage.md) describe the same revisions.
Paths below are relative to the root of the respective repository.

### Criteria

* **REMOVE:** a close equivalent exists. This means the same mathematical content at
  comparable generality, or a result from which the entry follows by a short routine
  argument.
* **NARROW:** a substantial part exists. The entry now states only the missing part
  and names what exists.
* **KEEP:** nothing close was found.

Only completed proofs count. Statements with `sorry` or `admit`, `proof_wanted`
targets, roadmap or TODO text, and definitions without the theorem were disregarded.
Every TauCeti declaration cited for a removal was confirmed to exist with no `sorry`
in its file.

### Summary

The number of entries fell from 645 to 616: 29 were removed and 50 narrowed. Most
removals come from TauCeti, which grew substantially between September and October 2026.

### Borderline decisions

These decisions could reasonably go the other way:

* **05.7 Baire class of derivatives, removed.** No Baire-class predicate exists; the
  theorem follows in a few lines from the difference-quotient characterization of
  the derivative.
* **05.30 Approximate continuity, removed.** No predicate exists; it follows from
  Mathlib's Lebesgue differentiation theorem in a few dozen lines.
* **16.13 Bipolar theorem for dual pairs, removed.** TauCeti proves it for a locally
  convex space and its dual; the general dual-pair form needs some transport code.
* **27.33 Calderón–Zygmund theorem, removed.** The case $2<p<\infty$ needs short glue
  through the adjoint kernel.
* **32.30 Interior $H^2$ regularity, removed.** TauCeti states membership in $H^2$; the
  local estimate follows from the whole-space bound applied with a cutoff.
* **33.6 Harnack inequality, removed.** TauCeti uses a larger ball than $B_{2r}$; a
  routine Harnack chain covers the difference.
* **36.44 Γ-convergence, removed.** Approximate minimizers are treated as routine glue.
* **13.13, 21.11 and 26.16, narrowed.** The missing parts are close to routine and
  could be removed. 13.18 and 22.32, first narrowed on the same grounds, were removed.
* **36.12, 35.12, 39.61, 39.73 and 27.4, kept.** These might be narrowed, but the
  existing ingredients are far from the statement.

### Decisions by section

#### Section 04: Real analysis, measure, and integration
Entries: 2 → 1 (removed 1, narrowed 1, kept 0).
- 04.20 Lusin's theorem: REMOVE. Evidence: TauCeti TauCeti/MeasureTheory/Function/Lusin.lean, `Measurable.exists_isClosed_measure_sdiff_lt_continuousOn` and `AEMeasurable.exists_isClosed_measure_sdiff_lt_continuousOn` (no sorry): for `[μ.WeaklyRegular]`, second-countable target, measurable `s` of finite measure, gives closed `F ⊆ s` with `μ (s \ F) < ε` and `ContinuousOn f F`; AEMeasurable covers measurability for the completion. A finite Radon (Regular) measure on an LCH (R1) space is WeaklyRegular (Mathlib Mathlib/MeasureTheory/Measure/Regular.lean, instance `Regular.weaklyRegular`), and `MeasurableSet.exists_isCompact_diff_lt` shrinks the closed set to a compact one: short glue.
- 04.39 Duality: NARROW. Evidence: Mathlib Mathlib/MeasureTheory/Function/Holder.lean, `ContinuousLinearMap.lpPairing`, `holderL` (pairing and bounded map Lp(Dual) → Dual(Lq)); TauCeti TauCeti/MeasureTheory/Function/Lp/Duality.lean, `MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le` (σ-finite, 1 ≤ q ≤ ∞: if |∫hg| ≤ C‖g‖_{q'} for simple g then ‖h‖_q ≤ C), giving isometry. Searched lpDual, toDual, StrongDual (Lp ...), surjective, "dual of L^p", Riesz representation: no surjectivity statement in either library. Narrowed to surjectivity.

#### Section 05: Differentiation and the fine structure of real functions
Entries: 5 → 3 (removed 2, narrowed 0, kept 3).
- 05.7 Baire classification of derivatives: REMOVE. Evidence: Mathlib Mathlib/Analysis/Calculus/Deriv/Slope.lean, `hasDerivAt_iff_tendsto_slope` / `hasDerivAt_iff_tendsto_slope_zero` (derivative is the limit of difference quotients); composing with $h_n(x)=\min(1/n,\operatorname{dist}(x,\partial I)/2)$ gives continuous functions converging pointwise to $f'$ on the open interval. Neither library defines "Baire class one" (searched Baire class, BaireOne, pointwise limit of continuous), but the content is this few-line glue. Borderline: the decision rests on the routine-glue criterion, not on a stated theorem.
- 05.10 Denjoy–Young–Saks theorem: KEEP. Searched Dini derivative, diniDeriv, Denjoy, Young–Saks in both libraries. Closest: TauCeti TauCeti/Analysis/GradientFlow/EVI/Basic.lean uses an upper right Dini derivative in the EVI definition only.
- 05.30 Approximate continuity: REMOVE. Evidence: Mathlib Mathlib/MeasureTheory/Covering/Differentiation.lean, `VitaliFamily.ae_tendsto_average_norm_sub` (Lebesgue points of locally integrable functions along a Vitali family, e.g. closed balls for Lebesgue measure via Besicovitch) and `ae_tendsto_measure_inter_div`. Apply it to the bounded measurable $g=\arctan\circ f$; Markov's inequality on balls shows $\{|g(y)-g(x)|>\delta\}$ has density zero at every Lebesgue point, and continuity of $\tan$ at $g(x)$ converts this into the statement for $f$. Short routine argument; no "approximately continuous" predicate in either library (searched approximate continuity, density zero, aplim). Borderline (a few dozen lines of glue).
- 05.31 Rectangular differentiation: KEEP. Searched strong maximal, Jessen, Marcinkiewicz–Zygmund, L log L, rectangle differentiation. Closest: TauCeti TauCeti/MeasureTheory/Integral/MaximalFunction.lean (centred Hardy–Littlewood maximal function over balls) and Calderón–Zygmund decomposition files; nothing for rectangles.
- 05.33 Kirszbraun's theorem: KEEP. Searched Kirszbraun, Lipschitz extension, extend. Closest: Mathlib Mathlib/Topology/MetricSpace/Lipschitz.lean, `LipschitzOnWith.extend_real`, `extend_pi` (McShane, real or sup-norm targets) and `LipschitzOnWith.extend_finite_dimension` (constant worsened); no same-constant Hilbert extension.

#### Section 06: Probability, measure-theoretic foundations, and limit theory
Entries: 10 → 10 (removed 0, narrowed 1, kept 9).
- 06.1 Kolmogorov extension theorem: NARROW. Evidence: TauCeti TauCeti/MeasureTheory/Measure/ProjectiveLimit/Countable.lean, `TauCeti.Measure.exists_isProjectiveLimit_of_countable` (countable index, standard Borel coordinates, probability projective family; no sorry) and ProjectiveLimit/Nat.lean `exists_isProjectiveLimit_nat`; Mathlib Mathlib/MeasureTheory/Constructions/Projective.lean `IsProjectiveLimit.unique` (uniqueness, any index) and Mathlib/Probability/ProductMeasure.lean (`Measure.infinitePi`, arbitrary products). Searched kolmogorovExtension, projectiveLimit, IsProjectiveLimit: no existence for uncountable index. Entry narrowed to the uncountable case.
- 06.23 Kolmogorov three-series theorem: KEEP. Searched three-series, two-series, random series, Kolmogorov inequality, Summable with iIndepFun. Closest: Mathlib Mathlib/Probability/StrongLaw.lean (strong law), Mathlib/Probability/Independence/ZeroOne.lean (zero–one law).
- 06.27 Hartman–Wintner iterated-logarithm law: KEEP. Searched iterated logarithm, Hartman, Wintner, log log in Probability trees. Nothing.
- 06.34 Lindeberg–Feller theorem: KEEP. Searched Lindeberg, Feller, Lyapunov, triangular array. Closest: Mathlib Mathlib/Probability/CentralLimitTheorem.lean, `tendstoInDistribution_inv_sqrt_mul_sum_sub` (i.i.d. case only).
- 06.36 Berry–Esseen bound: KEEP. Searched Berry, Esseen, Esseen smoothing. Nothing; only the qualitative i.i.d. CLT above.
- 06.51 Lévy–Khintchine formula: KEEP. Searched infinitely divisible, Khintchine/Khinchin, Lévy measure. Closest: TauCeti TauCeti/Analysis/CompletelyMonotone/Bernstein/LevyKhintchine/{Basic,Representation,Uniqueness}.lean (Lévy–Khintchine representation of Bernstein functions, i.e. Laplace exponents of subordinators on ℝ≥0), not characteristic functions of infinitely divisible real laws.
- 06.57 Donsker invariance principle: KEEP. Searched Donsker, invariance principle, functional central limit. Nothing; Mathlib has no existence of Brownian motion (only `IsBrownianReal` predicate, Mathlib/Probability/BrownianMotion/Basic.lean).
- 06.60 Cramér's theorem: KEEP. Searched large deviation, Cramér, rate function, Legendre transform. Closest: Mathlib Mathlib/Probability/Moments/Basic.lean `measure_ge_le_exp_mul_mgf` (Chernoff bound, the elementary upper-bound ingredient), Mathlib/Probability/Moments/Tilted.lean (exponential tilting).
- 06.61 Sanov's theorem: KEEP. Searched Sanov, large deviation, empirical measure. Closest: Kullback–Leibler divergence in Mathlib Mathlib/InformationTheory/KullbackLeibler and TauCeti TauCeti/InformationTheory/KullbackLeibler; TauCeti TauCeti/Probability/Process/EmpiricalMeasure.lean (definition of empirical measures).
- 06.62 Varadhan's integral lemma: KEEP. Searched Varadhan, Laplace principle, large deviation. Nothing.

#### Section 07: Concentration, high-dimensional probability, and empirical processes
Entries: 13 → 12 (removed 1, narrowed 0, kept 12).
- 07.4 Bernstein's inequality: KEEP. Searched Bernstein (probability/measure trees), Bennett, "t / 3". Closest: Mathlib Mathlib/Probability/Moments/SubGaussian.lean `measure_sum_ge_le_of_iIndepFun` (Hoeffding), Mathlib/Probability/Moments/Basic.lean `measure_ge_le_exp_mul_mgf` (Chernoff); Bernstein hits in TauCeti are Bernstein's theorem on completely monotone functions.
- 07.6 Equivalent sub-Gaussian descriptions: NARROW. Evidence: Mathlib Mathlib/Probability/Moments/SubGaussian.lean, `HasSubgaussianMGF.measure_ge_le` (MGF bound ⇒ Gaussian tail) and `HasSubgaussianMGF.memLp`; the module docstring lists the equivalences (i)–(v) as a TODO and no ψ₂/Orlicz norm is defined (searched Orlicz, psi_2, ψ₂, subgaussian in TauCeti: only McDiarmid uses). Narrowed to the ψ₂ norm and the remaining implications.
- 07.17 Gaussian logarithmic Sobolev inequality: KEEP. Searched log-Sobolev, logarithmic Sobolev, Gross, Herbst, entropy, Gaussian Poincaré. Closest: TauCeti TauCeti/Probability/Distributions/Gaussian/Hermite/Parseval.lean (Hermite expansion), no entropy inequality.
- 14.26 Gaussian isoperimetry (reviewed here; now in Section 14): KEEP. Searched Gaussian isoperimetry, Borell, Sudakov–Tsirelson, Ehrhard. Closest: TauCeti TauCeti/MeasureTheory/Integral/PrekopaLeindler.lean (Prékopa–Leindler) and Brunn–Minkowski; no Gaussian isoperimetric statement.
- 07.27 Dudley's entropy bound: KEEP. Searched Dudley, chaining, coveringNumber, metric entropy. Closest: Mathlib Mathlib/Topology/MetricSpace/CoveringNumbers.lean (covering/packing number definitions and comparisons), Mathlib/Topology/EMetricSpace/PairReduction.lean (`pair_reduction`, a chaining lemma), Mathlib/Probability/Process/Kolmogorov.lean (Kolmogorov condition definition); no entropy-integral bound.
- 07.32 Majorizing measure theorem: KEEP. Searched majorizing, Talagrand, gamma_2, generic chaining. Only the pair-reduction lemma above (citing Talagrand).
- 07.33 Symmetrization: KEEP. Searched symmetrization, Rademacher (only Rademacher's differentiation theorem), Rademacher complexity. Nothing.
- 07.37 Uniform deviations for VC classes: KEEP. Searched VC, Glivenko, Cantelli, uniform law, shatter. Closest: Mathlib Mathlib/Combinatorics/SetFamily/Shatter.lean (Sauer–Shelah, combinatorial), DualVC.lean; TauCeti TauCeti/Probability/Process/EmpiricalMeasure.lean (definition only).
- 07.43 Hanson–Wright inequality: KEEP. Searched Hanson, Wright, quadratic form concentration. Closest: TauCeti TauCeti/Probability/Distributions/Gaussian/QuadraticForm.lean (exact Gaussian quadratic-form laws).
- 07.44 Matrix Bernstein inequality: KEEP. Searched matrix Bernstein, matrix Chernoff, Tropp, Lieb concavity, Golden–Thompson. Closest: TauCeti TauCeti/Probability/Moments/MatrixConcentration.lean (entrywise Chebyshev union bound transferred to eigenvalues/operator norm with dimension factors; not exponential).
- 07.47 Johnson–Lindenstrauss lemma: KEEP. Searched Johnson–Lindenstrauss, random projection, dimension reduction. Nothing.
- 07.50 Wigner semicircle law: KEEP. Searched semicircle law, Wigner, empirical spectral. Only hyperbolic-geometry "semicircle" hits.
- 07.51 Marchenko–Pastur law: KEEP. Searched Marchenko, Pastur, empirical spectral. Closest: TauCeti TauCeti/Probability/Distributions/Wishart (finite-dimensional Wishart laws).

#### Section 08: Stochastic processes, martingales, and stochastic calculus
Entries: 15 → 15 (removed 0, narrowed 0, kept 15).
General search (both libraries, whole tree): brownian, Wiener measure, Kolmogorov–Chentsov, continuous modification, stochastic integral, Itô, quadratic variation, semimartingale, local martingale, Doob–Meyer, Burkholder, Davis–Gundy, martingale representation, Girsanov, Novikov, Feynman–Kac, stochastic differential, Yamada–Watanabe, local time, occupation, strong Markov, reflection principle, Lévy process, Poisson random measure. TauCeti has no Brownian-motion or stochastic-calculus file (only a mention in TauCeti/MeasureTheory/OptimalTransport/Entropic/Dynamic.lean). Mathlib relevant files: Mathlib/Probability/BrownianMotion/{Basic,GaussianProjectiveFamily}.lean, Mathlib/Probability/Process/{Kolmogorov,LocalProperty,Predictable,Indistinguishable,FiniteDimensionalLaws}.lean, Mathlib/Probability/Martingale/*.
- 08.1 Existence and uniqueness in law: KEEP. Closest: Mathlib `IsBrownianReal`/`IsPreBrownianReal` predicates, `projectiveFamily` (Brownian finite-dimensional laws, projective), `IsGaussianProcess.isPreBrownianReal_of_covariance`; `IsKolmogorovProcess` definition without the Kolmogorov–Chentsov theorem; `map_eq_iff_forall_finset_map_restrict_eq` (laws on the product space determined by finite-dimensional laws). No existence.
- 08.3 Strong Markov property: KEEP. Closest: Mathlib `IsPreBrownianReal.indepFun_shift` (simple Markov property at a deterministic time).
- 08.4 Reflection principle: KEEP. Nothing found.
- 08.7 Quadratic variation: KEEP. Nothing found (no quadratic variation of processes).
- 08.13 Doob–Meyer decomposition: KEEP. Closest: Mathlib Mathlib/Probability/Martingale/Centering.lean (discrete Doob decomposition `martingalePart`/`predictablePart`).
- 08.17 Itô isometry: KEEP. Nothing (no stochastic integral).
- 08.21 Itô's formula: KEEP. Nothing.
- 08.23 Burkholder–Davis–Gundy inequalities: KEEP. Closest: Mathlib `maximal_ineq` (Doob's maximal inequality, discrete time) in Mathlib/Probability/Martingale/OptionalStopping.lean.
- 08.26 Brownian martingale representation: KEEP. Nothing.
- 08.29 Girsanov's theorem: KEEP. Nothing (Mathlib/Probability/Moments/Tilted.lean has static exponential tilting only).
- 08.31 Existence and pathwise uniqueness for Lipschitz SDEs: KEEP. Nothing (ODE Picard–Lindelöf only).
- 08.33 Yamada–Watanabe principle: KEEP. Nothing.
- 08.36 Feynman–Kac formula: KEEP. Nothing.
- 08.42 Occupation density formula: KEEP. Nothing (occupation hits are unrelated algebra).
- 08.55 Lévy–Itô decomposition: KEEP. Nothing; TauCeti Bernstein-function Lévy–Khintchine files (TauCeti/Analysis/CompletelyMonotone/Bernstein/LevyKhintchine) concern Laplace exponents only.

#### Section 09: Malliavin calculus, rough paths, and stochastic partial differential equations
Entries: 14 → 14 (removed 0, narrowed 0, kept 14).
- 09.1 Wiener chaos decomposition: KEEP. Searched isonormal, Wiener chaos, multiple Wiener integral, Hermite, infinitePi+Gaussian. Closest: TauCeti TauCeti/Probability/Distributions/Gaussian/Hermite/Pi/Basis.lean (`gaussianHermitePiBasis`) and Pi/Parseval.lean (`hasSum_gaussianHermitePi_expansion`): Hermite Hilbert basis of L^2 of a Fintype-indexed product Gaussian only; no isonormal family, no infinite-dimensional chaos.
- 09.4 Closability and Sobolev spaces: KEEP. Searched Malliavin, cylindrical, D^{k,p}; nothing in either library.
- 09.11 Mehler formula: KEEP. Searched Mehler, Ornstein, OrnsteinUhlenbeck; nothing.
- 09.14 Clark–Ocone representation: KEEP. Searched Clark, Ocone, martingale representation, stochastic integral, Itô; Mathlib has only Predictable processes (Mathlib/Probability/Process/Predictable.lean) and Brownian predicates; no stochastic integral.
- 09.16 Smooth-density criterion: KEEP. Searched Malliavin covariance, smooth density, divergence; only unrelated TauCeti Sobolev density files.
- 09.18 Hörmander's density theorem: KEEP. Searched Hörmander/Hormander, hypoelliptic; hits are Calderón–Zygmund/Mihlin–Hörmander multipliers only.
- 09.21 Young's integration theorem: KEEP. Searched Young integral, Riemann–Stieltjes, p-variation, Hölder integral; nothing (Mathlib eVariationOn only).
- 09.22 Sewing lemma: KEEP. Searched sewing, Chen relation, rough path, two-parameter increment; nothing.
- 09.25 Controlled rough integration: KEEP. Same searches; nothing.
- 09.28 RDE existence and uniqueness: KEEP. Same searches; nothing.
- 09.40 Lipschitz mild equations: KEEP. Searched cylindrical Wiener, mild solution, Da Prato, stochastic convolution; closest TauCeti TauCeti/Analysis/Semigroups/CauchyProblem/Basic.lean (deterministic mild solutions of C0-semigroup Cauchy problems), no stochastic integral in Hilbert space.
- 09.51 Dalang's condition: KEEP. Searched Dalang, Walsh, white noise, SPDE; nothing.
- 09.57 Reconstruction theorem: KEEP. Searched regularity structure, reconstruction, Besov, paraproduct, model; only unrelated hits (TauCeti Littlewood–Paley bump functions).
- 09.58 Renormalized two-dimensional cubic equation: KEEP. Searched Phi4, Wick, renormaliz, SPDE; nothing.

#### Section 10: Ergodic theory and measurable dynamics
Entries: 11 → 11 (removed 0, narrowed 0, kept 11).
- 10.5 Birkhoff pointwise theorem: KEEP. Searched pointwise ergodic, maximal ergodic, Hopf, birkhoffAverage with ae/tendsto. Closest: Mathlib Mathlib/Analysis/InnerProductSpace/MeanErgodic.lean (`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`), TauCeti TauCeti/Probability/Ergodic/CondExpProjection.lean (L^2 limit = condexp on invariants), BirkhoffLp.lean; no a.e. or L^1 convergence.
- 10.7 Kingman's subadditive theorem: KEEP. Searched Kingman, subadditive ergodic; nothing.
- 10.8 Ergodic decomposition: KEEP. Searched ergodic decomposition; Mathlib Mathlib/Dynamics/Ergodic/Extreme.lean (`Ergodic.iff_mem_extremePoints`), TauCeti TauCeti/MeasureTheory/Group/ErgodicExtreme.lean (group actions), TauCeti/Probability/DeFinetti/Correspondence.lean (decomposition of exchangeable laws only), TauCeti/Probability/Process/PathLaw/InvariantConditionalLaw.lean (conditional law of one coordinate given shift invariants, not a decomposition into ergodic measures).
- 10.9 Rokhlin tower lemma: KEEP. Searched Rokhlin/Rohlin, aperiodic, tower; nothing.
- 10.20 Kolmogorov–Sinai generator theorem: KEEP. Searched Kolmogorov–Sinai, measure-theoretic/metric entropy, partition entropy; only finite KL/Shannon entropy in TauCeti InformationTheory.
- 10.22 Shannon–McMillan–Breiman: KEEP. Searched Shannon-McMillan, asymptotic equipartition; nothing.
- 10.27 Ornstein isomorphism theorem: KEEP. Searched Ornstein, Bernoulli shift; TauCeti TauCeti/Probability/Ergodic/BernoulliShift.lean proves only ergodicity of Bernoulli shifts.
- 10.35 Variational principle: KEEP. Mathlib Mathlib/Dynamics/TopologicalEntropy/{CoverEntropy,NetEntropy}.lean define topological entropy; no measure entropy, no variational principle.
- 10.37 Ruelle–Perron–Frobenius: KEEP. Searched Ruelle, transfer operator, Perron–Frobenius, equilibrium state, pressure; only Mathlib irreducible matrix definitions.
- 10.41 Oseledets theorem: KEEP. Searched Oseledets, Lyapunov exponent, multiplicative ergodic, cocycle; nothing.
- 10.48 Furstenberg multiple recurrence: KEEP. Searched Furstenberg, multiple recurrence, Szemerédi; Mathlib has combinatorial regularity/triangle removal/corners only (Mathlib/Combinatorics/...), no ergodic multiple recurrence.

#### Section 11: Classical inequalities, means, majorization, and rearrangement
Entries: 6 → 6 (removed 0, narrowed 2, kept 4).
- 11.9 Newton and Maclaurin inequalities: KEEP. Searched Newton inequality, Maclaurin, esymm inequalities; only algebraic Newton identities (Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean).
- 11.22 Hardy–Littlewood–Pólya characterization: NARROW. Evidence: TauCeti TauCeti/Analysis/Convex/PermutationOrbit.lean `Matrix.mulVec_mem_convexHull_range_comp_perm` (Dy in conv of permutations of y); Mathlib Mathlib/Analysis/Convex/Birkhoff.lean `doublyStochastic_eq_convexHull_permMatrix` (converse by glue; its module doc lists the majorization characterization as TODO); TauCeti TauCeti/Analysis/Convex/Majorization.lean `IsSymmetricConvex.mem_of_prefixSum_le` covers only weak majorization into permutation- and sign-invariant convex sets. Missing: x ≺ y (partial sums) ⇒ x = Dy.
- 11.24 Karamata's inequality: NARROW. Evidence: TauCeti TauCeti/Analysis/Convex/DoublyStochasticMatrix.lean `ConvexOn.sum_map_mulVec_le_of_mem_doublyStochastic` (sum φ(Dy) ≤ sum φ(y) for convex φ). Missing: hypothesis in partial-sum form (reduces to 11.22) and strict-convexity equality case.
- 11.32 Discrete Hardy inequality: KEEP. Searched Hardy inequality, Cesàro, Hardy operator, p/(p-1); hits are Hardy spaces/maximal functions only.
- 11.37 Hilbert's integral inequality: KEEP. Searched Hilbert inequality, Hilbert matrix, π/sin(π/p), 1/(x+y); nothing.
- 11.38 Carleman's inequality: KEEP. Searched Carleman; nothing.

#### Section 12: Convexity, convex analysis, and variational analysis
Entries: 10 → 8 (removed 2, narrowed 1, kept 7).
- 12.9 Choquet representation: KEEP. Searched Choquet, barycenter + extremePoints, boundary/maximal measure; Mathlib Krein–Milman (Mathlib/Analysis/Convex/KreinMilman.lean) and TauCeti face/extreme-point lemmas for measures (TauCeti/MeasureTheory/Measure/Face.lean) and de Finetti barycenters; no Choquet theorem.
- 05.38 Alexandrov's theorem (reviewed here; now in Section 05): REMOVE. Evidence: TauCeti TauCeti/Analysis/Convex/Alexandrov.lean `ConvexOn.ae_existsUnique_isPositive_isLittleO` (real convex u on a set Ω in a finite-dimensional inner product space with Haar measure: a.e. in Ω, u differentiable with unique positive A giving the second-order Taylor expansion); also `TauCeti.ae_existsUnique_isPositive_isLittleO` for EReal-valued f. Matches hypotheses and conclusion exactly.
- 12.18 Fenchel–Moreau theorem: REMOVE. Evidence: TauCeti TauCeti/Analysis/Convex/FenchelMoreau.lean `TauCeti.fenchelConjugate_flip_fenchelConjugate_eq` (E topological vector space, LocallyConvexSpace; f convex epigraph, lower semicontinuous, never ⊥; pairing representing the continuous dual ⇒ f** = f), plus `exists_affine_le_of_lt` (affine minorants); evaluation pairing with E →L ℝ gives the entry; no Hausdorff hypothesis needed.
- 12.21 Subdifferential sum rule: KEEP. TauCeti TauCeti/Analysis/Convex/Subdifferential.lean has only `mem_subdifferential_add_affine_iff` (adding an affine function); Mathlib has no subdifferential. Searched sum rule, subdifferential_add, Moreau–Rockafellar.
- 12.32 Proximal mapping: NARROW. Evidence: TauCeti TauCeti/Analysis/Convex/Alexandrov.lean `norm_sub_le_norm_add_sub_add_of_mem_subdifferential` ((I+∂f)^{-1} is 1-Lipschitz on its range, general real inner product space); TauCeti/Analysis/GradientFlow/MoreauYosida/Existence.lean `moreauYosidaResolvent_nonempty`, `moreauYosidaResolvent_nonempty_of_lowerSemicontinuous` (existence of minimizers in proper metric spaces or under an auxiliary compactness convergence). Missing: existence/uniqueness for every x in a general Hilbert space for convex lsc f, identification with J_{γ∂f}, firm nonexpansiveness.
- 12.34 Moreau decomposition: KEEP. Searched Moreau decomposition, prox, polar cone; nothing beyond the Moreau–Yosida infrastructure above.
- 12.39 Fenchel–Rockafellar duality: KEEP. Searched Fenchel–Rockafellar, strong duality; only optimal-transport (Kantorovich) dualities in TauCeti and a TODO in Mathlib/Analysis/Convex/Cone/Basic.lean.
- 12.40 Slater and KKT conditions: KEEP. Searched Slater, KKT, Karush, Lagrange multiplier; only smooth equality-constrained Lagrange multipliers (Mathlib/Analysis/Calculus/LagrangeMultipliers.lean).
- 12.45 Ekeland variational principle: KEEP. Searched Ekeland, Caristi, Bishop–Phelps, variational principle; Ekeland appears only as a bibliography item (Ekeland–Témam).
- 12.50 Clarke gradient representation: KEEP. Searched Clarke, generalized gradient; nothing (Mathlib has Rademacher's theorem only as an input).

#### Section 13: Matrix analysis, operator monotonicity, and noncommutative inequalities
Entries: 12 → 10 (removed 2, narrowed 3, kept 7).
- 13.5 Courant–Fischer principle: REMOVE. Evidence: TauCeti TauCeti/Analysis/InnerProductSpace/CourantFischer.lean `LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf_re_inner` (λ_k = sup over (k+1)-dim V of inf of Rayleigh quotient on unit vectors, symmetric operator on finite-dim RCLike space), with `exists_unit_vector_re_inner_le_eigenvalue` / `exists_submodule_forall_unit_eigenvalue_le_re_inner`; the min–max form follows by applying it to −T.
- 13.7 Cauchy interlacing: KEEP. Searched interlac, compression, Poincaré separation, rank-one perturbation; closest TauCeti Ky Fan trace inequality (TauCeti/Analysis/InnerProductSpace/KyFan.lean) and coordinate compressions of determinants (TauCeti/Analysis/Matrix/FiniteCompression.lean); no interlacing.
- 13.8 Weyl inequalities: NARROW. Evidence: TauCeti CourantFischer.lean `abs_eigenvalue_sub_eigenvalue_le_norm`, `abs_eigenvalues_sub_le_opNorm` (|λ_k(T)−λ_k(S)| ≤ ‖T−S‖), `eigenvalue_mono`. Missing: λ_{i+j−1}(A+B) ≤ λ_i(A)+λ_j(B).
- 13.10 Hoffman–Wielandt inequality: NARROW. Evidence: TauCeti TauCeti/Analysis/InnerProductSpace/HoffmanWielandt.lean `LinearMap.IsSymmetric.sum_sq_eigenvalues_sub_le_sum_sq_norm_apply` (symmetric operators, sorted matching). Missing: normal matrices.
- 13.13 Von Neumann trace inequality: NARROW. Evidence: TauCeti HoffmanWielandt.lean `LinearMap.IsSymmetric.re_trace_comp_le_sum_eigenvalues_mul_eigenvalues` (Re tr(TS) ≤ Σ λ_i μ_i, symmetric); KyFan.lean `LinearMap.norm_trace_comp_linearIsometryEquiv_le_kyFanSum` (|tr(AQ)| ≤ Σ σ_i(A), Q unitary). Missing: |tr(A*B)| ≤ Σ s_i(A)s_i(B) for arbitrary matrices (derivable via SVD + Abel summation + Ky Fan, but not stated).
- 13.18 Eckart–Young–Mirsky theorem: REMOVE (follows by a short argument from `singularValue_add_index_le` and `UnitarilyInvariantSeminorm.map_le_of_kyFanSum_le` together with the results below). Evidence: TauCeti TauCeti/Analysis/OperatorIdeal/ApproximationNumber/EckartYoung.lean `ContinuousLinearMap.singularValue_eq_linearMap_singularValues` (approximation number = singular value), Attainment.lean `exists_rank_le_nnnorm_sub_eq_singularValue`, Basic.lean `singularValue_add_index_le`, FanDominance.lean `UnitarilyInvariantSeminorm.map_le_of_kyFanSum_le`. Operator-norm case present; the all-unitarily-invariant-norm and Frobenius statements are not stated (would combine the mixed-index inequality with Fan dominance).
- 13.32 Loewner's theorem: KEEP. Searched operator monotone, Loewner, Pick; Mathlib proves monotonicity of rpow (0<p≤1) and log (Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Order.lean, ExpLog/Order.lean); TauCeti has Pick/Herglotz/Nevanlinna representations (TauCeti/Analysis/Complex/Pick/, TauCeti/Analysis/Complex/Herglotz.lean) but no link to matrix monotonicity.
- 13.35 Choi–Davis–Jensen inequality: KEEP. Searched operator convex, Jensen with cfc/positive maps, Hansen–Pedersen, Kadison; nothing.
- 13.46 Golden–Thompson inequality: KEEP. Searched Golden, Thompson, trace exp; nothing.
- 13.47 Lieb concavity theorem: KEEP. Searched Lieb, Ando, jointly concave; nothing relevant.
- 13.58 Data processing: KEEP. Mathlib Mathlib/InformationTheory/KullbackLeibler/DataProcessing.lean is classical KL only; Mathlib/Analysis/CStarAlgebra/CompletelyPositiveMap.lean defines CP maps; no quantum relative entropy.
- 13.60 Strong subadditivity: KEEP. Searched von Neumann entropy, strong subadditivity, partial trace; nothing.

#### Section 14: Functional, isoperimetric, and geometric inequalities
Entries: 10 → 9 (removed 1, narrowed 2, kept 7).
- 14.3 Sharp quadratic Sobolev inequality: KEEP. Searched talenti, aubin, sharp Sobolev, best/optimal constant, extremal, bubble. Closest: TauCeti TauCeti/Analysis/PDE/Yamabe/Bubble.lean defines the bubbles `bubble t b` and proves their PDE (`conformalCoefficient_mul_neg_laplacian_bubble`), but no sharp constant or extremizer statement; Mathlib Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean has GNS with non-sharp constant.
- 14.8 Moser–Trudinger inequality: NARROW. TauCeti TauCeti/Analysis/Sobolev/Trudinger.lean, `TauCeti.W1p.setLIntegral_exp_abs_value_div_rpow_le` and `TauCeti.setLIntegral_exp_norm_div_rpow_le` give $\int_\Omega\exp((|u|/(c\|Du\|_n))^{n/(n-1)})\le e(n^n+5)|\Omega|$ with explicit non-sharp $c$; Moser's sharp $\alpha_n$ and its optimality are missing.
- 14.9 Hardy inequality: KEEP. Searched Hardy's inequality, hardy_ineq, Hardy-type, Rellich, `‖x‖ ^` weights; only Hardy–Littlewood maximal function and Hardy spaces found.
- 14.13 Hardy–Littlewood–Sobolev inequality: KEEP. Searched Littlewood–Sobolev, fractional integration, Riesz potential. Closest: TauCeti TauCeti/MeasureTheory/Integral/RieszPotential.lean, `eLpNorm_setLIntegral_enorm_sub_rpow_mul_le` (Riesz potential $L^p\to L^q$ only on sets of finite measure, with $1/p-1/q<\kappa$; not the critical whole-space HLS).
- 14.21 Faber–Krahn inequality: KEEP. Searched Faber, Krahn, Pólya–Szegő, symmetrization. Closest: TauCeti TauCeti/MeasureTheory/Function/SchwarzRearrangement.lean (rearrangement, equimeasurability, Lp norms; no gradient inequality) and TauCeti/Analysis/PDE/Spectrum/Basic.lean (first Dirichlet eigenvalue as Rayleigh minimum).
- 14.24 Quantitative isoperimetry: KEEP. Searched isoperimetric, Fraenkel asymmetry, finite perimeter. Closest: TauCeti TauCeti/Analysis/BoundedVariation/Perimeter.lean (De Giorgi perimeter, `perimeter_le_liminf`); no isoperimetric inequality for perimeter; other "isoperimetric" hits are symplectic loop/Wirtinger results.
- 14.28 Brunn–Minkowski inequality: NARROW. TauCeti TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Basic.lean, `TauCeti.volume_rpow_add_volume_rpow_le` (nonempty null-measurable sets, outer volume of sum; covers compact sets); equality case for homothetic convex bodies missing (searched homothet; nothing relevant).
- 14.29 Prékopa–Leindler inequality: REMOVE. TauCeti TauCeti/MeasureTheory/Integral/PrekopaLeindler.lean, `TauCeti.hasPrekopaLeindler_volume` with `Measure.HasPrekopaLeindler` (measurable ℝ≥0∞-valued f,g,h with pointwise geometric-mean bound, 0≤θ≤1, finite-dimensional inner product space): same statement.
- 14.40 Nash inequality: KEEP. Searched Nash inequality (only author name hits). Closest: Mathlib GNS inequality, from which the case n≥3 would need an Lp interpolation argument; n=1,2 not covered.
- 14.48 Bakry–Émery logarithmic Sobolev inequality: KEEP. Searched Bakry, log-Sobolev, logarithmic Sobolev, Gamma_2, carré du champ, Gaussian Poincaré. Closest: TauCeti TauCeti/MeasureTheory/OptimalTransport/MetricMeasure/CurvatureDimension.lean (synthetic CD(K,∞) definition), TauCeti/MeasureTheory/Function/CheegerEnergy.lean; no log-Sobolev inequality.

#### Section 15: Core Banach and Hilbert space theory
Entries: 6 → 3 (removed 3, narrowed 1, kept 2).
- 15.16 Goldstine theorem: REMOVE. TauCeti TauCeti/Analysis/Normed/Module/Dual/Goldstine.lean, `closure_image_inclusionInDoubleDualWeak_closedBall_zero_one` (weak-star closure of $J(B_X)$ equals the closed unit ball of $X^{**}$), also `denseRange_inclusionInDoubleDualWeak`; normed spaces over RCLike scalars.
- 15.27 Reflexivity and weak compactness: REMOVE. TauCeti TauCeti/Analysis/Normed/Module/Dual/Reflexive/WeakCompact.lean, `surjective_inclusionInDoubleDual_iff_isCompact_toWeakSpace_closedBall` (reflexive iff weakly compact ball); Reflexive/Submodule.lean, `surjective_inclusionInDoubleDual` (closed subspaces) and `surjective_inclusionInDoubleDual_quotient`; Reflexive/Basic.lean, `surjective_inclusionInDoubleDual_strongDual_iff` (X reflexive iff X* reflexive). All parts covered.
- 15.28 Eberlein–Šmulian theorem: KEEP. Searched eberlein, smulian/šmulian, weakly sequentially, IsSeqCompact with toWeakSpace, StrictMono with WeakSpace, weakly convergent subsequence. Closest: Mathlib Mathlib/Analysis/Normed/Module/WeakDual.lean `WeakDual.isSeqCompact_closedBall` (weak-star, separable predual); TauCeti weak compactness via cluster points only.
- 15.29 James compactness theorem: KEEP. Searched james, norm attainment, Bishop–Phelps, attains supremum; no relevant result (TauCeti "James" hits are the James basis theorem and unrelated representation theory).
- 15.33 Uniform convexity and reflexivity: NARROW. TauCeti TauCeti/Analysis/Convex/Uniform.lean, `surjective_inclusionInDoubleDual_of_uniformConvexSpace` (Milman–Pettis, real complete uniformly convex spaces). No `UniformConvexSpace` instance for `Lp`/Clarkson inequalities in either library (only inner product spaces and submodules); rewritten to the uniform convexity and reflexivity of $L^p$.
- 15.47 Closed range theorem: REMOVE. TauCeti TauCeti/Analysis/Normed/Module/Dual/Adjoint.lean, `ContinuousLinearMap.isClosed_range_precomp_iff` (Banach spaces: range T closed iff range of Banach adjoint closed) and `range_precomp_eq_orthogonalBilin_ker`; Hilbert-space counterpart TauCeti TauCeti/Analysis/Fredholm/Adjoint.lean, `ContinuousLinearMap.isClosed_range_adjoint_iff`, `range_adjoint_eq_orthogonal_ker_of_isClosed_range`.

#### Section 16: Locally convex spaces, duality, and distributions
Entries: 9 → 8 (removed 1, narrowed 0, kept 8).
- 16.13 Bipolar theorem for dual pairs: REMOVE. TauCeti TauCeti/Analysis/LocallyConvex/Bipolar.lean, `StrongDual.bipolar_eq_closedAbsConvexHull` (bipolar = closed absolutely convex hull of $s\cup\{0\}$ for the pairing of a real/complex locally convex space with its dual) and `AbsConvex.bipolar_eq_closure`. The dual-pair version follows by applying it to `WeakBilin B` (Mathlib Mathlib/Analysis/LocallyConvex/WeakDual.lean: `WeakBilin.locallyConvexSpace`, `LinearMap.dualEmbedding_surjective` identifies the σ(E,F)-dual with F). Somewhat borderline: the glue (transporting polars along the dual identification) is routine but not entirely trivial.
- 16.15 Mackey–Arens theorem: KEEP. Searched mackey (only representation-theory hits), arens, compatible topology, polar topology. No Mackey topology in either library.
- 16.31 Nuclear tensor characterization: KEEP. Searched nuclear, projective/injective tensor topology. Closest: TauCeti TauCeti/Analysis/OperatorIdeal/Nuclear/Basic.lean (nuclear gauge of operators via approximation numbers); no nuclear locally convex spaces.
- 16.33 Nuclear Fréchet compactness: KEEP. Mathlib Mathlib/Analysis/LocallyConvex/Montel.lean defines `MontelSpace` (no instances for nuclear spaces); no nuclear spaces.
- 16.42 Distributions supported at a point: KEEP. Mathlib Mathlib/Analysis/Distribution/Support.lean has `dsupport`, `dsupport_delta`, support of derivatives; no converse structure theorem. Searched point support, supported at a point, dirac derivative.
- 16.43 Local structure theorem: KEEP. Searched finite order, derivative of continuous function, structure theorem; nothing in Mathlib/Analysis/Distribution or TauCeti/Analysis/Distribution.
- 16.51 Schwartz kernel theorem: KEEP. Only a docstring mention in Mathlib Mathlib/Analysis/Distribution/Distribution.lean (motivation remark); no theorem.
- 16.59 Paley–Wiener–Schwartz theorem: KEEP. Searched Paley, PaleyWiener, exponential type, entire with Fourier; only Littlewood–Paley and band-limited kernel estimates (TauCeti TauCeti/Analysis/Distribution/SchwartzSpace/BandLimited.lean).
- 16.63 Malgrange–Ehrenpreis theorem: KEEP. Searched malgrange, ehrenpreis, fundamental solution. Closest: TauCeti TauCeti/Analysis/PDE/FundamentalSolution/{Euclidean,Planar}/DistributionalLaplacian.lean (Laplacian only).

#### Section 17: Banach space geometry, bases, and operator ideals
Entries: 9 → 8 (removed 1, narrowed 0, kept 8).
- 17.10 James basis theorem: REMOVE. TauCeti TauCeti/Analysis/Normed/Module/Bases/Reflexive.lean, `surjective_inclusionInDoubleDual_iff` (for a Schauder basis b of a Banach space: reflexive iff b.IsShrinking ∧ b.IsBoundedlyComplete); no sorry.
- 17.21 Rosenthal ℓ¹ theorem: KEEP. Searched rosenthal, weakly Cauchy, equivalent to ℓ¹ basis; nothing.
- 17.23 Dunford–Pettis compactness in L¹: KEEP. Searched dunford, UnifIntegrable together with WeakSpace/weakly compact. Closest: TauCeti TauCeti/MeasureTheory/Measure/ProbabilityMeasure/UniformIntegrable.lean (uniform integrability along weakly convergent probability measures; different statement).
- 17.32 Enflo approximation counterexample: KEEP. TauCeti TauCeti/Analysis/Normed/Module/ApproximationProperty/Basic.lean defines AP/BAP/MAP and Bases/Approximation.lean proves BAP for spaces with a basis; no counterexample (searched enflo, counterexample, no approximation).
- 17.38 Kwapień theorem: KEEP. Searched kwapie, type 2, cotype, Rademacher (only Rademacher's differentiability theorem); no type/cotype.
- 17.39 Dvoretzky theorem: KEEP. Searched dvoretzky, Banach–Mazur distance, finitely representable; nothing.
- 17.46 Superreflexive renorming theorem: KEEP. Searched superreflexive, uniformly smooth, modulus of smoothness; only uniform convexity (Mathlib Analysis/Convex/Uniform.lean, TauCeti Milman–Pettis).
- 17.54 Pietsch domination theorem: KEEP. Searched pietsch, p-summing, absolutely summing; TauCeti operator-ideal files (TauCeti/Analysis/OperatorIdeal/) concern approximation numbers, Schatten/Ky Fan and nuclear gauges, not summing operators.
- 17.57 Grothendieck inequality: KEEP. Searched Grothendieck inequality/constant, K_G; only algebraic-geometry hits.

#### Section 18: Vector-valued analysis and analysis in Banach spaces
Entries: 8 → 8 (removed 0, narrowed 0, kept 8).
- 18.5 Vector-valued Hölder duality: KEEP. Searched Lp with StrongDual, dual of Bochner spaces, toDual; only scalar Hölder pairings (Mathlib Mathlib/MeasureTheory/Function/Holder.lean) and Hilbert/Gelfand-triple duality in TauCeti Sobolev evolution spaces; no $L^{p'}(X^*)\to L^p(X)^*$ isometry or RNP converse.
- 18.10 Vector Radon–Nikodým theorem: KEEP. Searched Radon–Nikodým property, RNP, reflexive with density. Mathlib Mathlib/MeasureTheory/VectorMeasure/ (Decomposition/RadonNikodym.lean for signed measures, BoundedVariation.lean for Stieltjes vector measures, `withDensityᵥ`); no Banach-valued density theorem.
- 18.13 Martingale characterization of RNP: KEEP. No RNP notion; Mathlib martingale convergence is real-valued. Searched martingale with Banach.
- 18.33 Hilbert transform characterization of UMD: KEEP. Searched UMD (no hits beyond substrings), Hilbert transform. Closest: TauCeti TauCeti/MeasureTheory/Integral/CalderonZygmund/StrongType.lean (Calderón–Zygmund for Hilbert-space-valued functions; Hilbert transform only mentioned).
- 18.37 Operator-valued Mihlin theorem on the line: KEEP. Searched R-bounded, Mihlin. Closest: TauCeti TauCeti/Analysis/Fourier/MihlinHormander.lean, `exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le` (scalar symbol, Hilbert-space-valued functions; no R-boundedness or UMD).
- 18.43 Basis independence and Gaussian realization: KEEP. Searched radonifying, gamma-radonifying, cylindrical, covariance operator. Closest: Mathlib Mathlib/Probability/Distributions/Gaussian/ (Gaussian measures on Banach spaces, Fernique) and Probability/Moments/CovarianceBilin.lean (covariance operator); no γ-radonifying norm.
- 18.51 UMD Itô isomorphism: KEEP. No UMD, cylindrical Brownian motion or Banach-valued stochastic integral found.
- 24.31 Weis characterization (reviewed here; now in Section 24): KEEP. Searched sectorial, R-sectorial, maximal regularity, analytic semigroup, Weis (only author citations); nothing relevant.

#### Section 19: Banach lattices, positive operators, and ordered structures
Entries: 8 → 8 (removed 0, narrowed 0, kept 8).
- 19.5 Band projections: KEEP. Searched both trees for band, disjoint complement, Dedekind complete, Riesz space, vector lattice, order projection. Closest: Mathlib `Mathlib/Algebra/Order/Group/Lattice.lean`, `Mathlib/Algebra/Order/Group/PosPart.lean` (lattice-ordered group identities only); no ideals or bands.
- 19.8 Freudenthal spectral theorem: KEEP. Searched Freudenthal, principal ideal, order unit, components; nothing.
- 19.15 Reflexivity criterion (KB spaces, Lozanovsky): KEEP. Searched KB space, order continuous norm, Lozanovsky, lattice copies of c_0/ell^1; nothing. Closest: Mathlib `Mathlib/Analysis/Normed/Order/Lattice.lean` (`NormedLatticeAddCommGroup`, solid norms).
- 19.20 Riesz–Kantorovich theorem: KEEP. Searched Riesz–Kantorovich, order bounded, regular operator, order dual; closest is Mathlib `Mathlib/Algebra/Order/Module/PositiveLinearMap.lean` (positive linear maps, no lattice structure on operators).
- 19.27 Kakutani representation of AM spaces with unit: KEEP. Searched Kakutani, AM-space, lattice isometry; only Riesz–Markov–Kakutani (`Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/*`), which is a different theorem; AM-space appears only in a docstring of `Mathlib/Algebra/Order/Group/Lattice.lean`.
- 19.29 Kakutani representation of AL spaces: KEEP. Same searches; nothing.
- 19.50 Krein–Rutman existence theorem: KEEP. Searched Krein–Rutman, Perron–Frobenius, positive operator spectral radius eigenvector, cone; closest is Mathlib `Mathlib/LinearAlgebra/Matrix/Irreducible/Defs.lean` (definitions of irreducible/primitive nonnegative matrices and path characterizations, no Perron–Frobenius eigenvalue theorem) and TauCeti `TauCeti/Probability/Ergodic/KoopmanMarkov.lean` (positive Koopman operator).
- 19.51 Strong positivity and a spectral gap: KEEP. Same searches (strongly positive, solid cone, ideal irreducible); nothing.

#### Section 20: Banach algebras and commutative harmonic analysis of algebras
Entries: 7 → 7 (removed 0, narrowed 0, kept 7).
- 20.7 Holomorphic functional calculus: KEEP. Searched holomorphic functional calculus, Riesz–Dunford, Riesz projection, contour/circle integrals of the resolvent, spectral mapping. Closest: Mathlib continuous functional calculus (`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/*`, C*-setting only) and `spectrum.map_polynomial_aeval` family (`Mathlib/FieldTheory/IsAlgClosed/Spectrum.lean`); TauCeti `TauCeti/Topology/Algebra/Module/LinearPMap/Resolvent/SpectralMapping.lean` (spectral mapping for resolvents only).
- 20.19 Gleason–Kahane–Żelazko theorem: KEEP. Searched Gleason, Kahane, Żelazko/Zelazko, functionals nonvanishing on units; nothing (TauCeti `TauCeti/Analysis/Normed/Algebra/AutomaticContinuity.lean` is unrelated automatic continuity of homomorphisms into finite-dimensional algebras).
- 20.23 Shilov boundary theorem: KEEP. Searched Shilov/Silov, uniform algebra, peak point, Choquet boundary, representing measure; nothing.
- 20.40 Wiener lemma: KEEP. Searched Wiener lemma/algebra, absolutely convergent Fourier series, summable `fourierCoeff`, ℓ¹ convolution algebras; Mathlib Gelfand theory (character space, `Mathlib/Analysis/Normed/Algebra/Spectrum.lean`) exists but ℓ¹(ℤ) is not set up as a Banach algebra, and no inverse-closedness result exists. TauCeti only has Wiener–Ikehara (`TauCeti/NumberTheory/LSeries/WienerIkehara/*`), a different theorem.
- 20.41 Wiener Tauberian theorem: KEEP. Same searches (Wiener Tauberian, translates dense in L¹, closed ideals of L¹(G)); nothing beyond Wiener–Ikehara.
- 20.47 Cohen–Hewitt factorization: KEEP. Searched Cohen, Hewitt, factorization, essential module, bounded approximate identity. Closest: Mathlib `Mathlib/Analysis/CStarAlgebra/ApproximateUnit.lean` (increasing approximate units in C*-algebras), TauCeti approximate identities in `TauCeti/MeasureTheory/Function/Lp/ApproximateIdentity.lean`, `TauCeti/RepresentationTheory/Compact/ApproximateIdentity.lean`; no factorization theorem.
- 20.55 Johnson group algebra theorem: KEEP. Searched amenable/amenability, derivation inner, invariant mean. Closest: Mathlib `Mathlib/MeasureTheory/Group/FoelnerFilter.lean` (`IsFoelner.amenable`: Følner filters give invariant finitely additive measures; docstring says amenability is not yet defined); no Banach-algebra amenability.

#### Section 21: Bounded operator theory, spectra, and functional models
Entries: 11 → 11 (removed 0, narrowed 5, kept 6).
- 15.65 Normal spectral theorem (reviewed here; now in Section 15): NARROW. Evidence: TauCeti `TauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean` (`ContinuousLinearMap.diagMeasure`, `integral_diagMeasure_eq_inner_cfc`, `eq_diagMeasure_iff`: scalar spectral measures of a normal operator); TauCeti `TauCeti/MeasureTheory/Function/BoundedBorel.lean` defines bounded Borel symbols only. The resolvent identity ‖R(z,T)‖ = dist(z,σ(T))⁻¹ follows from Mathlib's isometric CFC for normal elements (`IsStarNormal.instIsometricContinuousFunctionalCalculus`, `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic.lean`). Missing: projection-valued measure and Borel calculus; entry rewritten accordingly.
- 21.11 Atkinson theorem: NARROW. Evidence: Mathlib `Mathlib/Analysis/Normed/Operator/Fredholm/Basic.lean` (`ContinuousLinearMap.isFredholm_iff_exists_isQuasiInverse`, with `LinearMap.IsQuasiInverse` meaning inverse modulo finite-rank maps; `IsFredholm.of_isQuasiInverse`); TauCeti `TauCeti/Analysis/Fredholm/CompactPerturbation.lean` (`isFredholm_one_sub`, `IsFredholm.add_of_isCompactOperator`). No statement with compact remainders and no Calkin algebra (`compactOperator` in `Mathlib/Analysis/Normed/Operator/Compact/Basic.lean` is a submodule only).
- 21.15 Analytic Fredholm theorem: KEEP. Searched analytic Fredholm, meromorphic inverse of operator families, holomorphic compact families. Closest: TauCeti `TauCeti/Analysis/Normed/Operator/Resolvent/Analytic.lean` (analyticity of the resolvent on the resolvent set) and Riesz–Schauder theory `TauCeti/Analysis/Normed/Operator/Compact/RieszTheory.lean`.
- 21.16 Essential spectral invariance: NARROW. Evidence: invariance of σ_ess under compact perturbation follows at once from TauCeti `ContinuousLinearMap.IsFredholm.add_of_isCompactOperator` (`TauCeti/Analysis/Fredholm/CompactPerturbation.lean`) applied to T - z. Missing: σ(T) \ σ_ess(T) = isolated finite-multiplicity eigenvalues for self-adjoint T (searched essential spectrum, discrete spectrum, isolated eigenvalue; nothing). Entry renamed and restricted.
- 15.59 Singular value approximation (reviewed here; now in Section 15): NARROW. Evidence: TauCeti approximation numbers `ContinuousLinearMap.singularValue` (`TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean`, infimum over rank-≤n maps); Eckart–Young `singularValue_eq_linearMap_singularValues` in finite dimension (`.../EckartYoung.lean`, `.../Attainment.lean`); decreasing diagonal operators on ℓ^p (`.../Diagonal.lean`); `isCompactOperator_iff_tendsto_singularValue` (`.../Compact.lean`). Missing: identification with eigenvalues of |T| for general compact operators in infinite dimension (SVD).
- 21.22 Ideal inequalities: NARROW. Evidence: TauCeti `singularValue_comp_comp_le` (aₙ(ATB) ≤ ‖A‖aₙ(T)‖B‖), `TauCeti.SymmetricGauge.opGauge_comp_comp_le` (`TauCeti/Analysis/OperatorIdeal/Family/SymmetricGauge.lean`, covers Schatten gauges), `nuclearENorm_comp_comp_le` (`TauCeti/Analysis/OperatorIdeal/Nuclear/Basic.lean`). Missing: Schatten Hölder ‖ST‖_r ≤ ‖S‖_p‖T‖_q and HS·HS ⊂ trace class (only the weak index law `singularValue_comp_add_le_mul` exists; no Hölder in operator-ideal or finite-dimensional Schatten files).
- 21.23 Trace and cyclicity: KEEP. Searched trace class, trace functional on operators, `tr`, nuclear trace. Closest: TauCeti nuclear gauge `nuclearENorm` (finite exactly for trace class) and Hilbert–Schmidt energy `hilbertSchmidtEnergy_indep` (basis independence for Σ‖Tbᵢ‖²); no trace functional or cyclicity in infinite dimension (Mathlib `LinearMap.trace` is finite-dimensional).
- 21.26 Wold decomposition: KEEP. Searched Wold, unilateral shift, isometry decomposition; only Cramér–Wold (probability) and a docstring mention of the unilateral shift in TauCeti `TauCeti/RepresentationTheory/Continuous/InvariantComplement.lean`.
- 21.30 Unitary dilation theorem: KEEP. Searched dilation, Sz.-Nagy, power dilation, von Neumann inequality; nothing.
- 21.34 Characteristic function: KEEP. Searched characteristic function, completely nonunitary, defect operator, Foiaș; nothing (TauCeti `OpNormDefect.lean` is an unrelated norm-defect form).
- 21.37 Commutant lifting: KEEP. Searched commutant lifting, minimal isometric dilation; nothing.

#### Section 22: Unbounded operators, spectral theory, and mathematical physics
Entries: 13 → 13 (removed 0, narrowed 1, kept 12).
- 22.5 von Neumann extension theorem: KEEP. Searched deficiency index/space, self-adjoint extension, von Neumann. Closest: TauCeti Cayley transform `IsSelfAdjoint.cayley_mem_unitary` (`TauCeti/Analysis/InnerProductSpace/LinearPMap/Cayley.lean`) and surjectivity of nonreal shifts `IsSelfAdjoint.smul_sub_surjective` (`.../LinearPMap/SelfAdjoint.lean`); no extension classification.
- 22.9 Unbounded spectral theorem: KEEP. Searched spectral theorem, projection-valued measure, spectral measure. Closest: TauCeti Cayley transform (unitary, star-normal), scalar spectral measures of bounded normal operators (`.../BorelCalculus/DiagonalMeasure.lean`), cyclic SNAG theorem `ContRepresentation.exists_pontryaginMeasureTransform_eq_inner` (`TauCeti/Analysis/Fourier/Pontryagin/StronglyContinuous.lean`, scalar measures for unitary representations); no PVM representation with domain characterization.
- 22.19 First representation theorem: KEEP. Searched closed/closable form, semibounded form, representation theorem, form domain. Closest: TauCeti Lax–Milgram/Lions (`TauCeti/Analysis/InnerProductSpace/Lions.lean`), variational solution operator `IsCoercive.formSolutionOperator` (`.../Variational/Spectrum.lean`, bounded coercive forms on a Hilbert space V mapped into H); no self-adjoint operator associated with a closed form.
- 22.21 Friedrichs extension: KEEP. Searched Friedrichs, form closure; nothing.
- 22.22 KLMN theorem: KEEP. Searched KLMN, relatively form-bounded; only operator relative bounds `LinearPMap.IsRelativelyBounded` (`TauCeti/Analysis/Normed/Operator/LinearPMap/RelativeBound.lean`).
- 22.27 Min–max principle: KEEP. Searched min–max, Courant–Fischer, Rayleigh, essential spectrum. Closest: TauCeti finite-dimensional `LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf_re_inner` (`.../CourantFischer.lean`), first-eigenvalue `IsCoercive.isLeast_rayleighQuotient` (`.../Variational/Rayleigh.lean`), min–max bounds for approximation numbers (`.../OperatorIdeal/ApproximationNumber/MinMax.lean`); no unbounded min–max relative to inf σ_ess.
- 22.32 Kato–Rellich theorem: REMOVE (essential self-adjointness on every core of $A$ follows by a short argument from the self-adjointness of $A+B$ on $D(A)$ and the relative bound). Evidence: TauCeti `IsSelfAdjoint.add_of_isRelativelyBounded` (`TauCeti/Analysis/InnerProductSpace/LinearPMap/KatoRellich.lean`, no sorry): A self-adjoint, V symmetric, ‖Vx‖ ≤ a‖x‖ + b‖Ax‖ with b < 1 ⇒ A + V self-adjoint on D(A). Missing: essential self-adjointness on every core of A (Mathlib has `LinearPMap.HasCore` but no such result). Entry restricted to the core statement.
- 22.34 Analytic isolated eigenvalues: KEEP. Searched analytic perturbation, Riesz projection, holomorphic family, type (A)/(B); closest is TauCeti resolvent analyticity `LinearPMap.analyticOnNhd_resolvent` (`TauCeti/Analysis/Normed/Operator/Resolvent/Analytic.lean`), resolvent perturbation (`.../Resolvent/Perturbation.lean`); no Riesz projections or eigenvalue perturbation.
- 22.38 Birman–Schwinger principle: KEEP. Searched Birman, Schwinger, eigenvalue counting; only knot-theory citations of J. Birman.
- 22.40 Free Laplacian: KEEP. Searched Laplacian self-adjoint, essentially self-adjoint, Fourier multiplier; Mathlib `SchwartzMap.laplacian_eq_fourierMultiplierCLM` (`Mathlib/Analysis/Distribution/FourierMultiplier.lean`) and TauCeti unbounded multiplication generators (`TauCeti/Analysis/Semigroups/Multiplication/MeasureLp/Generator.lean`) are ingredients, but -Δ is not realized as a self-adjoint operator on L² and its spectrum is not computed.
- 22.52 Weyl alternative: KEEP. Searched limit point/limit circle, Weyl alternative, Sturm–Liouville; closest is TauCeti explicit Dirichlet spectrum of -d²/dx² on an interval (`TauCeti/Analysis/PDE/Spectrum/Interval.lean`), a regular problem only.
- 22.61 Kato–Rosenblum theorem: KEEP. Searched wave operator, scattering, Kato–Rosenblum, absolutely continuous spectrum; nothing.
- 22.63 RAGE theorem: KEEP. Searched RAGE, Ruelle, Amrein, Enss, continuous spectral subspace; nothing.

#### Section 23: Operator algebras, operator spaces, free probability, and noncommutative geometry
Entries: 17 → 17 (removed 0, narrowed 1, kept 16).
- 23.9 GNS construction: NARROW. Evidence: Mathlib `Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean` (`PositiveLinearMap.GNS`, `gnsNonUnitalStarAlgHom`, `gnsStarAlgHom`: GNS Hilbert space and representation for a positive functional); its TODO states that the unit cyclic vector with φ(a) = ⟨π(a)Ω,Ω⟩ is not yet constructed. No uniqueness up to unitary equivalence. TauCeti `TauCeti/Analysis/PositiveDefinite/Function/GNS.lean` is the group/positive-definite-function version. Entry restricted to the cyclic vector and uniqueness.
- 23.10 Gelfand–Naimark theorem: KEEP. Searched Gelfand–Naimark, faithful representation, universal representation, states separating points; only commutative duality (`Mathlib/Analysis/CStarAlgebra/GelfandDuality.lean`) and the GNS representation above.
- 23.17 Stinespring theorem: KEEP. Searched Stinespring, dilation of CP maps; Mathlib `Mathlib/Analysis/CStarAlgebra/CompletelyPositiveMap.lean` defines CP maps and shows star homomorphisms are CP, nothing more.
- 23.18 Arveson extension theorem: KEEP. Searched Arveson, operator system, CP extension; nothing.
- 23.21 Bicommutant theorem: KEEP. Searched double commutant/bicommutant, weak operator closure; Mathlib `Mathlib/Analysis/VonNeumannAlgebra/Basic.lean` defines `VonNeumannAlgebra` via double commutant and states the theorem as future work; only algebraic `Set.centralizer_centralizer` lemmas exist.
- 23.22 Kaplansky density theorem: KEEP. Searched Kaplansky; only Kaplansky's UFD criterion and topological-ring lemma.
- 23.23 Predual theorem: KEEP. Searched predual, Sakai, normal functional; `WStarAlgebra` in `Mathlib/Analysis/VonNeumannAlgebra/Basic.lean` assumes a predual, no theorem.
- 23.27 Type decomposition: KEEP. Searched type I/II/III, abelian/finite projections, Murray–von Neumann; nothing.
- 23.35 Tomita theorem: KEEP. Searched Tomita, Takesaki, modular operator/conjugation; nothing.
- 23.41 Jones index theorem: KEEP. Searched Jones index, subfactor, 4cos²(π/n); TauCeti Temperley–Lieb algebras and a Markov trace (`TauCeti/Algebra/TemperleyLieb/MarkovTrace.lean`) are algebraic knot-theory tools without index theory.
- 23.43 Completely positive approximation theorem: KEEP. Searched nuclear C*-algebra, tensor norms, CPAP; nothing.
- 23.50 Bott periodicity: KEEP. Searched K-theory, K_0/K_1 of C*-algebras, suspension; TauCeti `TauCeti/LinearAlgebra/CliffordAlgebra/BottPeriodicity.lean` is the algebraic Clifford-algebra periodicity, not C*-algebra K-theory.
- 23.51 Six-term exact sequence: KEEP. Same searches; six-term sequences in TauCeti concern group orders and module categories only.
- 23.58 Ruan representation theorem: KEEP. Searched operator space, completely bounded, Ruan, matrix norms; nothing.
- 23.65 Free central limit theorem: KEEP. Searched free probability, freeness, semicircle law, noncrossing partitions, free cumulants; nothing (semicircle hits are geometric arcs).
- 23.68 R-transform linearization: KEEP. Same searches plus R-transform; nothing.
- 23.71 Asymptotic freeness of Gaussian matrices: KEEP. Searched GUE, Wigner, random matrices, asymptotic freeness; TauCeti has only elementary random-matrix concentration (`TauCeti/Probability/Moments/MatrixConcentration.lean`).

#### Section 24: Semigroups, evolution equations, and functional calculus
Entries: 10 → 10 (removed 0, narrowed 0, kept 10).
- 24.13 Variation of constants: KEEP. Searched "variation of constants", "Duhamel", "mild solution", "inhomogeneous", "forcing" in both libraries. Closest: TauCeti TauCeti/Analysis/Semigroups/CauchyProblem/Basic.lean and Uniqueness.lean (IsMildSolution, IsClassicalSolution, IsMildSolution.unique, isMildSolution_realOperator) treat only the homogeneous problem u' = Au; no forcing term.
- 24.17 Trotter–Kato approximation: KEEP. Searched "Trotter", "Kato", "resolvent convergence", "strong resolvent". Closest: TauCeti Generation/HilleYosida/Limit.lean, Generation/LimitSemigroup.lean (yosidaLimitSemigroupOfTendsto, tendstoUniformlyOn_exp_yosidaApproximation_of_norm_resolvent_pow_le): convergence of Yosida approximants only, not the general resolvent-convergence equivalence.
- 24.18 Chernoff product formula: KEEP. Searched "Chernoff", "Lie product", "Trotter". Closest: TauCeti TauCeti/Geometry/Lie/Exponential/Trotter.lean (Lie–Trotter for finite-dimensional Lie groups); nothing for C0-semigroups.
- 24.20 Analytic generation theorem: KEEP. Searched "sectorial", "analytic semigroup", "holomorphic semigroup", "bounded analytic", "sector" in Semigroups/Analysis; no hits in semigroup context.
- 24.23 Balakrishnan formula: KEEP. Searched "Balakrishnan", "fractional power". Closest: Mathlib Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/IntegralRepresentation.lean (exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁): integral representation of x^p, 0<p<1, for positive elements of C*-algebras, up to an unspecified constant; not sectorial operators on Banach spaces.
- 24.30 de Simon maximal regularity: KEEP. Searched "maximal regularity", "de Simon", "R-bound", "R-sectorial", "H∞ calculus"; nothing.
- 24.35 Analytic spectral mapping: KEEP. Searched "spectral mapping" with semigroup context, "eventually norm continuous"; only Mathlib spectral mapping for polynomials/CFC in Banach algebras.
- 24.39 Gearhart–Prüss theorem: KEEP. Searched "Gearhart", "Prüss", "exponentially stable", "spectral bound"; nothing. TauCeti GrowthBound.lean has growth bounds only.
- 24.40 Arendt–Batty–Lyubich–Vũ theorem: KEEP. Searched "Arendt", "Batty", "Lyubich", "strongly stable"; nothing.
- 24.52 Crandall–Liggett generation: KEEP. Searched "accretive", "Crandall", "Liggett", "nonlinear semigroup", "nonlinear contraction"; nothing. TauCeti Dissipative/* is linear dissipativity only.

#### Section 25: Integral equations and classical operator methods
Entries: 9 → 9 (removed 0, narrowed 1, kept 8).
- 25.3 Hilbert–Schmidt kernels: NARROW. Evidence: TauCeti TauCeti/Analysis/InnerProductSpace/HilbertSchmidt/Basic.lean, Columns.lean, Isometry.lean (ContinuousLinearMap.hilbertSchmidtNorm, hilbertSchmidtEnergy, HilbertBasis.columnOperator; finite-energy operators are compact; adjoint and unitary invariance). No link between L^2(D×D) kernels and Hilbert–Schmidt operators; entry narrowed to the kernel identity ‖K‖_{S^2}=‖k‖_{L^2} and adjoint kernel.
- 25.8 Mercer theorem: KEEP. Searched "Mercer", "positive definite kernel", "RKHS". Closest: Mathlib Mathlib/Analysis/InnerProductSpace/Reproducing.lean (RKHS, Moore's theorem, RKHS.kernel_ofKernel); TauCeti TauCeti/Analysis/PositiveDefinite/* (positive-definite functions/kernels). No eigenfunction expansion or trace formula.
- 25.18 Volterra solvability: KEEP. Searched "Volterra", "successive substitution", "resolvent kernel", "Neumann series". Closest: TauCeti TauCeti/Analysis/Calculus/ContinuousMap.lean (ContinuousMap.intervalIntegralOperator: the primitive operator, kernel ≡ 1) and TauCeti TauCeti/Analysis/Normed/Operator/Resolvent/NeumannSeries.lean (abstract Neumann series); no quasinilpotence/invertibility for general continuous Volterra kernels.
- 25.23 Abel inversion: KEEP. Searched "Riemann–Liouville", "fractional integral", "Abel"; nothing relevant.
- 25.25 Plemelj–Sokhotski formulas: KEEP. Searched "Plemelj", "Sokhotski", "principal value", "Cauchy transform", "jump". Closest: TauCeti TauCeti/Analysis/Complex/CauchyKernel.lean (local integrability of 1/z in the plane); no boundary values of Cauchy integrals on curves.
- 25.34 Sobolev mapping properties (layer potentials): KEEP. Searched "layer potential", "single layer", "double layer", "boundary integral"; nothing. TauCeti has no H^{±1/2}(Γ) boundary spaces.
- 25.37 Calderón projector: KEEP. Same searches plus "Calderón projector"; nothing.
- 25.47 Collectively compact approximation theorem: KEEP. Searched "collectively compact", "Anselone", in Normed/Operator/Compact of both libraries; nothing.
- 25.54 Tikhonov minimization: KEEP (somewhat elementary). Searched "Tikhonov", "least squares", "normal equation", "pseudoinverse", "minimum norm". Nothing stated. Ingredients exist (Mathlib Mathlib/Analysis/InnerProductSpace/LaxMilgram.lean; TauCeti Analysis/InnerProductSpace/Variational/*), but the minimizer identification is not present; kept, though it is a completing-the-square exercise of moderate length.

#### Section 26: Sobolev spaces, smoothness scales, and interpolation
Entries: 10 → 10 (removed 0, narrowed 5, kept 5).
- 26.13 Extension theorem: NARROW. Evidence: TauCeti TauCeti/Analysis/Sobolev/LipschitzDomain/GlobalExtension.lean (W1p.exists_extensionL_of_isLipschitzDomainWith: bounded linear extension W^{1,p}(Ω)→W^{1,p}(ℝ×E), restriction left inverse, bounded Lipschitz Ω, 1≤p≤∞), with LipschitzDomain/Extension.lean, Trace/Epigraph/Extension.lean; density of global test functions W1p/Density.lean (W1p.denseRange_ofTestFunctionₗ_top) gives the density corollary by glue. Wkp/Extension.lean is only zero extension of W^{k,p}_0. Narrowed to m≥2.
- 26.16 Critical embedding: NARROW. Evidence: TauCeti TauCeti/Analysis/Sobolev/Trudinger.lean (W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient: W^{1,n}_0(Ω)→L^q all finite q on finite-measure Ω; W1p.setLIntegral_exp_abs_value_div_rpow_le: Trudinger's inequality); combined with the Lipschitz extension operator and cutoffs this gives the embedding on bounded Lipschitz domains. No counterexample to the L^∞ embedding found (searched "log log", "not_memLp_top", "counterexample"). Narrowed to the failure of W^{1,d}⊂L^∞, d≥2.
- 26.24 First-order trace theorem: NARROW. Evidence: TauCeti TauCeti/Analysis/Sobolev/LipschitzDomain/Trace/Basic.lean (W1p.lipschitzChartTrace: H^1 → L^2 local chart traces w.r.t. tangential Lebesgue measure), Trace/Extension.lean (W1p.halfSpaceTrace), Trace/HalfSpace.lean. No global boundary trace with surface measure, no Besov range, no right inverse, no p≠2. Narrowed accordingly.
- 26.26 Kernel of the trace: NARROW. Evidence: TauCeti Trace/Kernel.lean (W1p.restrictL_mem_w1p0Submodule_normalHalfSpace; ker of half-space trace = H^1_0 and W^{1,1}_0) and LipschitzDomain/Trace/Kernel.lean (W1p.exists_iInf_ker_lipschitzChartTrace_eq_of_isLipschitzDomainWith: on bounded Lipschitz Ω, H^1_0 = common kernel of finitely many local chart traces). Missing p≠2 on Lipschitz domains and higher-order normal traces.
- 26.31 Quasicontinuity: KEEP. Searched "capacity", "quasicontinu", "quasi-everywhere". Closest: TauCeti W1p/PreciseRepresentative.lean (W1p.ae_eq_preciseRepresentative, a.e. only); no Sobolev capacity.
- 26.37 Fractional Hilbert identity: KEEP. Searched "Gagliardo" (hits are Gagliardo–Nirenberg only), "Slobodeckij", "fractional Sobolev", "W^{s,p}". Mathlib Mathlib/Analysis/FunctionalSpaces/BesselPotentialSpace.lean defines H^{s,p} but no Gagliardo seminorm.
- 26.42 Bourgain–Brezis–Mironescu limit: KEEP. Searched "Bourgain", "Brezis", "Mironescu", "nonlocal"; nothing.
- 26.46 Bessel and Sobolev identifications: NARROW. Evidence: TauCeti TauCeti/Analysis/Sobolev/BesselPotential/Basic.lean (MeasureTheory.Lp.memSobolev_natCast_iff_exists_wkp_value_eq: H^{k,p}=W^{k,p}, integer k, 1<p<∞). No Triebel–Lizorkin spaces (searched "Triebel", "Besov", "square function"; only Littlewood–Paley cutoffs in TauCeti Analysis/Calculus/BumpFunction/LittlewoodPaley.lean). Narrowed to H^{s,p}=F^s_{p,2} and the p≠2 non-coincidence.
- 26.53 Real interpolation theorem: KEEP. Searched "K-functional", "real interpolation", "Banach couple", "compatible couple", "interpolation space"; nothing abstract. TauCeti Marcinkiewicz (MeasureTheory/Integral/Marcinkiewicz/*) is the L^p case only. Entry text now says "for abstract Banach couples".
- 26.54 Complex interpolation theorem: KEEP. Closest: TauCeti TauCeti/MeasureTheory/Integral/RieszThorin.lean (eLpNorm_le_rpow_mul_rpow_mul_eLpNorm: Riesz–Thorin on L^p) and Mathlib Mathlib/Analysis/Complex/Hadamard.lean (three lines); no abstract complex interpolation spaces. Entry text notes the Riesz–Thorin case.

#### Section 27: Fourier analysis and real-variable harmonic analysis
Entries: 13 → 9 (removed 4, narrowed 1, kept 8).
- 27.4 Hausdorff–Young inequality: KEEP. Not stated in either library (only mentioned in the RieszThorin module docstring). Ingredients: TauCeti TauCeti/MeasureTheory/Integral/RieszThorin.lean (eLpNorm_le_rpow_mul_rpow_mul_eLpNorm, on simple functions) and Mathlib Mathlib/Analysis/Fourier/LpSpace.lean (Lp.fourierTransformₗᵢ, identified with the integral only on Schwartz functions); assembling them needs the L^1∩L^2 identification and density, so not a few-line glue. Failure for p>2 also absent.
- 27.13 Heisenberg uncertainty: KEEP. Searched "Heisenberg", "uncertainty"; only Heisenberg group files.
- 27.17 Fejér summation: KEEP. Searched "Fejér", "Cesàro". Fejér means appear only inside TauCeti TauCeti/Analysis/Bochner/Herglotz.lean and Bochner/Fourier/Nonneg.lean (measures / positive-definite functions), not convergence of Fourier series.
- 27.22 Carleson–Hunt theorem: KEEP. Searched "Carleson", "Hunt"; nothing.
- 27.28 Calderón–Zygmund decomposition: REMOVE. Evidence: TauCeti TauCeti/MeasureTheory/Integral/CalderonZygmund/Decomposition.lean (calderonZygmundCubes, calderonZygmundGood_add_tsum_calderonZygmundBad, ae_enorm_calderonZygmundGood_le ‖g‖≤2^n t, lintegral_enorm_calderonZygmundGood_le, integral_calderonZygmundBad = 0, lintegral_enorm_calderonZygmundBad_le, mul_volume_biUnion_calderonZygmundCubes_le) — same statement on ℝ^n with dyadic cubes.
- 27.33 Calderón–Zygmund theorem: REMOVE. Evidence: TauCeti CalderonZygmund/StandardKernel.lean (ContinuousLinearMap.mul_volume_lt_enorm_le_of_norm_sub_le_mul_rpow: L^2-bounded with standard kernel ⇒ weak (1,1)), StrongType.lean (eLpNorm_le_of_hormander for 1<p<2; eLpNorm_le_of_setLIntegral_compl_closedBall_adjoint_le for 2<p<∞ via adjoint), WeakType.lean. Estimates are on L^2∩L^p, matching the section's dense-class convention; the adjoint's transposed kernel representation is short glue.
- 27.35 Hilbert transform: NARROW. Evidence: TauCeti TauCeti/Analysis/Fourier/MihlinHormander.lean (exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le) applies trivially to −i sgn ξ on ℝ, giving L^p bounds; H^2=−I is immediate from Mathlib/TauCeti L^2 multipliers (TauCeti Analysis/Fourier/L2Multiplier.lean). No principal-value Hilbert transform defined (searched "Hilbert transform"), so the p.v. formula, a.e. existence and weak (1,1) remain.
- 27.38 Mihlin multiplier theorem: REMOVE. Evidence: TauCeti TauCeti/Analysis/Fourier/MihlinHormander.lean (exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le, exists_fourierMultiplierCLM_eq_and_norm_le_of_norm_iteratedFDeriv_le): symbol smooth off 0 with ‖D^k m‖≤A‖ξ‖^{-k} for k≤N, 2N>n, bounded on L^p, 1<p<∞; same hypotheses and conclusion.
- 27.44 Weighted maximal theorem: KEEP. Searched "Muckenhoupt", "A_p weight", "weighted"; nothing. TauCeti MeasureTheory/Integral/MaximalFunction.lean is unweighted.
- 27.49 John–Nirenberg inequality: REMOVE. Evidence: TauCeti TauCeti/MeasureTheory/Integral/JohnNirenberg.lean (volume_lt_norm_sub_setAverage_le on dyadic cubes, volume_lt_norm_sub_setAverage_closedBall_le on all cubes: |{|f−f_Q|>s}| ≤ 2 exp(−c s/M)|Q|; setLIntegral_exp_mul_norm_sub_setAverage_le exponential integrability), from which equivalence of L^p-oscillation seminorms is a routine moment computation.
- 27.53 Hardy–BMO duality: KEEP. Searched "Hardy space", "atomic", "Fefferman", "H^1"; only BMO estimates (TauCeti CalderonZygmund/BoundedMeanOscillation.lean, L^∞→BMO).
- 27.56 Littlewood–Paley theorem: KEEP. Searched "Littlewood–Paley", "square function". Closest: TauCeti Analysis/Calculus/BumpFunction/LittlewoodPaley.lean and Analysis/Distribution/SchwartzSpace/LittlewoodPaley.lean (dyadic cutoffs and pieces of Mihlin symbols); no square-function equivalence.
- 27.66 Stein–Tomas restriction theorem: KEEP. Searched "Stein–Tomas", "restriction theorem", "Tomas", "Gaussian curvature" with Fourier; nothing.

#### Section 28: Abstract harmonic analysis on groups
Entries: 8 → 7 (removed 1, narrowed 2, kept 5).
- 28.2 The modular homomorphism: NARROW. Evidence: Mathlib Mathlib/MeasureTheory/Group/ModularCharacter.lean (modularCharacter : G →* ℝ≥0, modularCharacterFun_pos, modularCharacterFun_eq_haarScalarFactor); continuity is an explicit TODO and no inversion formula found (searched "modularCharacter" across both trees). Narrowed to continuity and ∫f(x⁻¹)dx = ∫f(x)Δ(x⁻¹)dx.
- 28.10 Weil's integration formula: NARROW. Evidence: Mathlib Mathlib/MeasureTheory/Measure/Haar/Quotient.lean (QuotientGroup.integral_eq_integral_automorphize, integral_mul_eq_integral_automorphize_mul: unfolding for a countable subgroup with a fundamental domain and right-invariant μ). Searched "Weil", "quasi-invariant", "rho-function", "Bruhat"; no general closed-subgroup quotient measure. Narrowed to the general case.
- 28.24 Pontryagin duality: KEEP. Searched "Pontryagin", "double dual", "bidual". Mathlib Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean is finite abelian only; TauCeti TauCeti/Analysis/Fourier/AddCircle.lean identifies the dual of the circle; TauCeti Analysis/Fourier/Pontryagin/* gives only continuity of evaluation and uniqueness of Fourier–Stieltjes transforms.
- 28.29 Plancherel theorem: KEEP. Searched "Plancherel", "inversion" in LCA contexts. Only Euclidean (Mathlib Analysis/Fourier/LpSpace.lean), circle and finite abelian versions; nothing for general LCA groups.
- 28.30 Bochner's theorem: REMOVE. Evidence: TauCeti TauCeti/Analysis/Bochner/LocallyCompactGroup.lean (IsPositiveDefiniteSub.exists_pontryaginMeasureTransform_eq_of_continuousAt; continuous_and_isPositiveDefiniteSub_iff_existsUnique_pontryaginMeasureTransform_eq): on any LCA group, continuous positive-definite functions are exactly Fourier–Stieltjes transforms of unique finite inner regular measures (arbitrary finite measures when the dual is Polish, e.g. G second countable); total mass φ(0) is immediate.
- 28.49 Mackey's imprimitivity theorem: KEEP. Searched "imprimitivity", "Mackey", "induced representation", "unitary induction"; only algebraic/number-theoretic induction.
- 28.53 Stone–von Neumann theorem: KEEP. Searched "Stone–von Neumann", "Schrödinger representation", "Weyl relation", "canonical commutation". Closest: TauCeti TauCeti/Analysis/SpecialFunctions/Hermite/Function/Operator.lean (CCR for Hermite ladder operators on Schwartz space) and Heisenberg group definitions; no uniqueness theorem.
- 28.58 Amenability and invariant means: KEEP. Searched "amenable", "invariant mean", "Følner". Closest: Mathlib Mathlib/MeasureTheory/Group/FoelnerFilter.lean (IsFoelner.amenable: a Følner filter gives an invariant finitely additive probability measure); no definition of amenable locally compact groups, characterization, or permanence properties.

#### Section 29: Wavelets, frames, time–frequency analysis, and sampling
Entries: 12 → 12 (removed 0, narrowed 0, kept 12).
- 29.2 Frame operator criterion: KEEP. Searched frame, Bessel sequence, Riesz basis, frame operator, synthesis in both libraries. Closest: TauCeti TauCeti/Analysis/InnerProductSpace/Frame.lean (finite families only: TauCeti.frameOperator, TauCeti.le_eigenvalues_gramOperator, TauCeti.mul_norm_sq_le_sum_norm_inner_sq_of_le_eigenvalues_gramOperator); no infinite frames or invertibility criterion.
- 29.3 Canonical dual reconstruction: KEEP. Same searches; no dual frame or S^{-1} reconstruction even for finite frames (only OrthonormalBasis.frameOperator_eq_id).
- 29.17 Wavelet construction from an MRA: KEEP. Searched wavelet, multiresolution, scaling filter, Haar system/function, Daubechies: nothing.
- 29.21 Compactly supported wavelets: KEEP. Same searches: nothing.
- 29.27 Unconditional L^p wavelet bases: KEEP. Searched wavelet, unconditional basis; TauCeti TauCeti/Analysis/Normed/Module/Bases/* has general Schauder bases (no wavelets, no L^p square functions for wavelets).
- 29.38 STFT orthogonality: KEEP. Searched short-time Fourier, STFT, Moyal, Wigner, ambiguity, modulation: nothing (only Plancherel available).
- 29.46 Gabor density obstruction: KEEP. Searched Gabor, time-frequency, density: nothing.
- 29.51 Balian–Low: KEEP. Searched Balian, uncertainty principle: nothing.
- 29.58 Shannon sampling: KEEP. Searched Shannon, sampling theorem, Whittaker, Kotelnikov, Paley–Wiener, bandlimited: only Mathlib Real.sinc (Mathlib/Analysis/SpecialFunctions/Trigonometric/Sinc.lean) and TauCeti SchwartzSpace/BandLimited.lean, which concerns Hörmander kernel estimates, not sampling.
- 29.61 Kadec 1/4: KEEP. Searched Kadec, Riesz basis of exponentials, perturbation; closest TauCeti Bases/Perturbation.lean (abstract small perturbation of Schauder bases, no exponentials or 1/4 constant).
- 29.62 Landau densities: KEEP. Searched Landau, Beurling density, uniformly separated: nothing.
- 29.68 Stable recovery from RIP: KEEP. Searched restricted isometry, compressed sensing, sparse recovery, basis pursuit: nothing.

#### Section 30: Distributions, pseudodifferential operators, microlocal and semiclassical analysis
Entries: 13 → 13 (removed 0, narrowed 0, kept 13).
- 30.15 Pullback theorem: KEEP. Searched wavefront, wave front, singular support, pullback of distributions: nothing.
- 30.17 Product theorem: KEEP. Same searches: nothing.
- 30.23 Composition formula: KEEP. Searched pseudodifferential, symbol class, quantization, Op(a): nothing; only constant-coefficient Fourier multipliers (Mathlib Analysis/Distribution/FourierMultiplier.lean).
- 30.27 Calderón–Vaillancourt: KEEP. Searched Calderón–Vaillancourt: nothing; closest TauCeti Fourier/L2Multiplier.lean and MihlinHormander.lean (x-independent symbols).
- 30.28 Sobolev mapping theorem: KEEP. Mathlib Analysis/Distribution/Sobolev.lean has Bessel-potential spaces with MemSobolev.fourierMultiplierCLM_of_bounded, MemSobolev.lineDerivOp, MemSobolev.laplacian (constant coefficients only); no x-dependent symbols.
- 30.31 Sharp Gårding: KEEP. Searched Gårding/Garding: only abstract Gårding inequalities for energy forms in TauCeti PDE (unrelated to symbols).
- 30.33 Parametrix theorem: KEEP. Searched parametrix, elliptic symbol: nothing.
- 30.39 Hörmander sums of squares: KEEP. Searched hypoelliptic, bracket generating, subelliptic: nothing.
- 30.40 Propagation of singularities: KEEP. Searched bicharacteristic, propagation of singularities, Hamilton field: nothing.
- 30.47 FIO composition: KEEP. Searched Fourier integral operator, canonical relation, oscillatory integral: nothing.
- 30.48 FIO L^2 boundedness: KEEP. Same: nothing.
- 30.50 Egorov's theorem: KEEP. "Egorov" only matches the measure-theoretic Egorov theorem (Mathlib MeasureTheory/Function/Egorov.lean).
- 30.57 Defect measures: KEEP. Searched defect measure, semiclassical, Wigner measure, Weyl quantization: nothing.

#### Section 31: Ordinary differential equations and dynamical systems
Entries: 10 → 10 (removed 0, narrowed 2, kept 8).
- 31.17 Floquet theorem: KEEP. Searched Floquet, monodromy, periodic coefficient, fundamental matrix in ODE dirs: nothing (TauCeti ODE/Linear.lean only has exp(tA) flows).
- 31.20 Sturm separation and comparison: KEEP. "Sturm" matches only Sturm sequences of polynomials and TauCeti PDE/Spectrum/Interval.lean (explicit Dirichlet spectrum of -d²/dx² on an interval); no zero interlacing or comparison.
- 31.24 Lyapunov's direct theorem: KEEP. Searched Lyapunov function/stable, asymptotically stable: TauCeti Dynamics/Flow/Lyapunov.lean has convergence and strict-max/min fixed-point results, no stability notions; GradientFlow.lean has monotonicity of f along gradient trajectories.
- 31.26 LaSalle invariance principle: NARROW. Evidence: TauCeti TauCeti/Dynamics/Flow/Lyapunov.lean, Flow.exists_tendsto_atTop_of_antitone (global flow on compact Hausdorff space, g antitone along orbits, orbit-constancy set contained in finite C ⇒ each orbit converges to a point of C), with TauCeti/Topology/OmegaLimit.lean (Flow.mapClusterPt_atTop_flow, invariance of ω-limits). Missing: general invariant set, positively invariant compact subsets.
- 31.27 Stable and unstable manifolds: NARROW. Evidence: TauCeti TauCeti/Analysis/ODE/LyapunovPerron/Local.lean (ContinuousLinearMap.setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image, contDiffAt_localStableGraphMap, hasFDerivAt_localStableGraphMap_zero and unstable analogues) and Smooth.lean (C¹ dependence) give C¹ local stable/unstable graphs tangent at 0 for y'=Ay+N(y) under exponential dichotomy hypotheses in a Banach space; ODE/ExponentialDichotomy.lean supplies the dichotomy only for symmetric operators; Calculus/Morse/GlobalChart.lean gives embedded C¹ stable/unstable manifolds for nondegenerate critical points of gradient flows. Missing: dichotomy for general hyperbolic matrices, C^r with r≥2.
- 31.28 Hartman–Grobman: KEEP. Searched Hartman, Grobman, topological conjugacy/linearization: only TauCeti Dynamics/Flow/Conjugacy.lean (transport of flows along homeomorphisms) and the Morse lemma; no linearization theorem.
- 31.29 Center manifolds: KEEP. Searched center/centre manifold: nothing.
- 31.38 Poincaré–Bendixson: KEEP. "Bendixson" only matches Cantor–Bendixson; nothing on planar flows.
- 31.47 Hopf bifurcation: KEEP. Searched bifurcation, Lyapunov coefficient: nothing.
- 31.64 KAM persistence: KEEP. Searched KAM, invariant tori, Diophantine frequency: nothing.

#### Section 32: Partial differential equations — general and linear theory
Entries: 14 → 10 (removed 4, narrowed 3, kept 7).
- 32.2 Linear transport: KEEP. Searched transport equation, characteristics, advection: nothing (flows of ODEs exist, no PDE statement).
- 32.5 Cauchy–Kowalevski: KEEP. Searched Kowalevski/Kovalevskaya variants: nothing.
- 30.43 Lewy's nonsolvability (reviewed here; now in Section 30): KEEP. Searched Lewy, local solvability: nothing.
- 32.18 Poisson formula: REMOVE. Evidence: TauCeti TauCeti/Analysis/PDE/PoissonIntegral/Ball.lean (TauCeti.integral_ballPoissonKernel, tendsto_ballPoissonIntegral, harmonicOnNhd_ballPoissonIntegral, exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere: harmonic extension of continuous data on every ball) and PoissonIntegral/HalfSpace.lean (halfSpacePoissonKernel = 2t/(nω_n|y−x|^n), mass one, Dirichlet problem for bounded data); uniqueness from the weak maximum principle (TauCeti PDE/MaximumPrinciple, Mathlib/TauCeti harmonic maximum principles).
- 32.19 Green's identities: KEEP. Searched Green's identity, divergence theorem: Mathlib BoxIntegral/DivergenceTheorem (boxes), TauCeti Sobolev/Trace/IntegrationByParts.lean (Gauss–Green on a half-space), Green/* (planar Green theorem), PDE/ClassicalSolution.lean (Green's first identity against H¹₀, no boundary term). No identity with boundary integral on general smooth domains.
- 32.22 Classical Dirichlet and Neumann solvability: NARROW. Evidence: TauCeti PDE/Perron/Barrier.lean, TauCeti.exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier_of_exterior_sphere (Dirichlet problem for continuous data on bounded domains with exterior sphere condition), plus Poisson integrals. Missing: smooth boundary ⇒ exterior sphere, boundary regularity, Neumann problem (no "Neumann problem" anywhere).
- 32.25 Nonzero boundary data: NARROW. Evidence: TauCeti PDE/DirichletProblem.lean, TauCeti.PDE.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq (u−g ∈ H¹₀ for g ∈ H¹(Ω), Lax–Milgram); Sobolev/LipschitzDomain/Trace/* (local chart traces, kernel = H¹₀). Missing: H^{1/2}(∂Ω) and trace surjectivity/lifting.
- 32.30 Interior H² regularity: REMOVE. Evidence: TauCeti TauCeti/Analysis/PDE/Regularity/Interior.lean, TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn (locally Lipschitz uniformly elliptic a, b,c ∈ L∞, f ∈ L², u ∈ H¹ weak solution ⇒ u ∈ H²(V) for V ⋐ Ω); the estimate comes from the whole-space theorem Regularity/Basic.lean UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzWith (bound by ‖f‖ and K‖∇u‖) applied to the cutoff, whose forcing is bounded by ‖f‖ and ‖u‖_{H¹}.
- 32.32 Boundary H² regularity: NARROW. Evidence: TauCeti PDE/Regularity/HalfSpace.lean, TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_halfSpace (constant A, H¹₀ solution on a half-space ⇒ H²); header states the normal step for variable coefficients is not proved. Missing: variable coefficients, C^{1,1} domains, higher regularity.
- 32.39 Gaussian heat kernel: REMOVE. Evidence: TauCeti TauCeti/Analysis/PDE/HeatKernel/Basic.lean, TauCeti.heatKernel, integral_heatKernel (mass one), hasDerivAt_heatKernel (∂_t K = ΔK), heatKernel_convolution_heatKernel (K_t*K_s=K_{t+s}); exact match.
- 32.44 Weak parabolic existence: REMOVE. Evidence: TauCeti TauCeti/Analysis/PDE/Parabolic/DirichletProblem.lean, exists_hasWeakLineDerivOn_gelfandDual_energyFormH1 (existence, u ∈ L²(H¹₀), u' ∈ L²(H⁻¹), continuous L² representative with u(t₀)=u₀) and eqOn_/ae_eq_of_hasWeakLineDerivOn_gelfandDual_energyFormH1 (uniqueness); jointly measurable bounded uniformly elliptic a(t,x), with drift and c ≥ −|γ| (more general than c ≥ 0), f ∈ L²(H⁻¹), u₀ ∈ L².
- 32.50 Wave Cauchy problem: KEEP. Searched wave equation, d'Alembert, Kirchhoff, u_tt: nothing (abstract Stone/unitary groups in TauCeti Semigroups not applied to the wave equation).
- 32.52 Finite propagation speed: KEEP. Searched finite propagation, domain of dependence, energy cone: nothing.
- 32.66 Complementing boundary conditions: KEEP. Searched Lopatinskii, Shapiro, complementing condition: nothing; only abstract Fredholm theory (Mathlib Analysis/Normed/Operator/Fredholm/*, TauCeti PDE/FredholmAlternative.lean for second-order Dirichlet).
Note: the original section had 14 entries (32.2, 5, 8, 18, 19, 22, 25, 30, 32, 39, 44, 50, 52, 66); the "Heat equations and parabolic energy methods" subheading was deleted.

#### Section 33: Elliptic and parabolic equations — regularity, free boundaries, and viscosity solutions
Entries: 17 → 16 (removed 1, narrowed 4, kept 12).
- 33.6 De Giorgi–Nash–Moser Harnack: REMOVE. Evidence: TauCeti TauCeti/Analysis/PDE/Regularity/Harnack.lean, TauCeti.PDE.exists_ae_ae_value_le_mul_value (nonnegative weak solution, measurable uniformly elliptic a, ess sup_{B_r} u ≤ C ess inf_{B_r} u when B(x₀,24√n r) ⊆ Ω, any n ≥ 1); the B_{2r} ⋐ Ω form follows by a routine Harnack chain/covering.
- 33.9 Higher integrability of the gradient: KEEP. Searched Gehring, Meyers, higher integrability, reverse Hölder for gradients: only TauCeti Regularity/ReverseHolder.lean (reverse Hölder for powers of supersolutions, Moser iteration) and a J-holomorphic higher-integrability lemma; nothing on ∇u ∈ L^{2+ε}.
- 33.14 ABP estimate: KEEP. Searched Alexandrov, Bakelman, Pucci, ABP: closest TauCeti PDE/MaximumPrinciple/NonDivergence.lean (classical weak maximum principle with sup bound via exponential barrier, C² solutions), not the L^n estimate.
- 33.15 Krylov–Safonov: KEEP. Searched Krylov, Safonov, nondivergence Harnack: nothing.
- 33.16 Interior Schauder estimate: NARROW. Evidence: TauCeti PDE/Regularity/Hessian/Schauder/Basic.lean, TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv (constant coefficients, C² solutions, interior C^{2,α}); Schauder/VariableCoefficient.lean (global a priori estimate for Hölder coefficients of small oscillation, no lower-order terms; header says localization and covering are separate). Missing: localized estimate for general Hölder a,b,c.
- 33.17 Boundary Schauder theory: KEEP. Searched Schauder + boundary/half-space, C^{2,α} Dirichlet solvability: nothing.
- 33.18 Interior W^{2,p} estimates: NARROW. Evidence: TauCeti PDE/Regularity/Hessian/VariableCoefficient.lean (TauCeti.PDE.exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq_of_abs_sub_le, small oscillation, whole space) and Hessian/Localization.lean (exists_lpNorm_smul_iteratedGradient_le_of_sum_mul_inner_eq_of_abs_sub_le, cutoff form with ‖∇u‖_p, ‖u‖_p). Missing: covering/interpolation absorption for continuous coefficients, lower-order coefficients.
- 33.23 Viscosity comparison and uniqueness: KEEP. "viscosity" only in TauCeti Analysis/Convex/MongeAmpere/Viscosity.lean (definition of viscosity sub/supersolutions for Monge–Ampère); no comparison principle for general degenerate elliptic G.
- 33.30 Evans–Krylov: KEEP. Searched Evans–Krylov, fully nonlinear, concave operator: nothing.
- 33.34 p-harmonic regularity: KEEP. Searched p-Laplacian, p-harmonic: nothing.
- 33.37 Alexandrov Dirichlet problem: NARROW. Evidence: TauCeti TauCeti/Analysis/Convex/MongeAmpere/Comparison.lean, TauCeti.le_of_mongeAmpereMeasure_le_of_le_frontier and eqOn_of_mongeAmpereMeasure_eq_of_eqOn_frontier (comparison and uniqueness on bounded open convex Ω for convex functions continuous on the closure); Convergence.lean (weak continuity). No existence theorem.
- 33.38 Interior Monge–Ampère regularity: KEEP. Searched Caffarelli, sections, strictly convex Alexandrov solution regularity: nothing beyond MongeAmpere/Decomposition.lean (a.e. Alexandrov Hessian determinant equals density).
- 33.46 Gaussian fundamental-solution bounds: KEEP. Searched Aronson, Nash, Gaussian bounds: only TauCeti PDE/HeatKernel/* (Laplacian heat kernel, constant coefficients).
- 33.53 Porous-medium contraction: KEEP. Searched porous, Barenblatt, degenerate diffusion: nothing.
- 33.55 Obstacle variational inequality: NARROW. Evidence: Mathlib Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean, exists_norm_eq_iInf_of_complete_convex and norm_eq_iInf_iff_real_inner_le_zero (projection onto a closed convex set and its variational-inequality characterization); TauCeti Lax–Milgram and Poincaré inequalities. Searched obstacle, variational inequality, Stampacchia (only Stampacchia's lemma/global bound): no obstacle-problem statement. Missing: instantiation for K ⊆ H¹.
- 33.57 Optimal C^{1,1} regularity: KEEP. Searched obstacle, free boundary, C^{1,1}: nothing.
- 33.61 Regular free boundary: KEEP. Searched free boundary, blowup, contact set: nothing.

#### Section 34: Hyperbolic equations, conservation laws, dispersive PDE, fluids, and kinetic theory
Entries: 21 → 21 (removed 0, narrowed 0, kept 21).
- 34.1 Smooth local well-posedness: KEEP. Searched "symmetrizable", "symmetric hyperbolic", "hyperbolic system", "Friedrichs", quasilinear; nothing in either library. Closest: TauCeti/Analysis/Semigroups (linear semigroup generation).
- 34.9 Kružkov existence and uniqueness: KEEP. Searched "Kružkov/Kruzkov", "entropy solution", "conservation law", "shock"; no hits.
- 34.14 Hopf–Lax formula: KEEP. Searched "Hopf–Lax", "Lax–Oleinik", "viscosity solution", "Hamilton–Jacobi", "inf-convolution". Closest: TauCeti/Analysis/GradientFlow/MoreauYosida/Derivative.lean (TauCeti.hasDerivAt_toReal_moreauYosida: time-step derivative of quadratic Moreau–Yosida, metric setting) and TauCeti/Analysis/Convex/Conjugate.lean; viscosity notion only for Monge–Ampère (TauCeti/Analysis/Convex/MongeAmpere/Viscosity.lean).
- 34.19 Glimm's small-BV theorem: KEEP. Searched "Glimm", "Riemann problem", "genuinely nonlinear"; none.
- 34.23 Schrödinger dispersive estimate: KEEP. Searched "Schrödinger/Schroedinger", "dispersive", "Fresnel", "oscillatory integral", "unitary group"; TauCeti hits are only entropic optimal transport (Schrödinger system). No free Schrödinger propagator.
- 34.24 Homogeneous Strichartz estimate: KEEP. "Strichartz", "TT*"; none.
- 34.31 Small-data critical scattering: KEEP. "scatter", "nonlinear Schrödinger"; none relevant.
- 34.32 Virial blowup criterion: KEEP. "virial", "blowup"; none.
- 34.38 Defocusing critical waves: KEEP. "wave equation", "d'Alembert"; none.
- 34.42 KdV global L^2 evolution: KEEP. "KdV", "Korteweg"; none.
- 34.45 Euler local well-posedness: KEEP. "Euler equations", "incompressible" (hits only 3-manifold topology), "vorticity"; none.
- 34.48 Beale–Kato–Majda: KEEP. "Beale", "vorticity"; none.
- 34.50 Yudovich uniqueness: KEEP. "Yudovich", "log-Lipschitz", "Osgood"; none.
- 34.54 Leray–Hopf existence: KEEP. "Navier", "Leray" (hits only algebraic topology); none. Closest: TauCeti/Analysis/PDE/Parabolic/Galerkin.lean, Existence.lean (linear parabolic Galerkin existence).
- 34.55 Two-dimensional viscous uniqueness: KEEP. Same searches; none.
- 34.57 Prodi–Serrin criterion: KEEP. "Serrin", "Prodi"; none.
- 34.60 Suitable weak-solution partial regularity: KEEP. "Caffarelli", "Kohn", "parabolic Hausdorff"; none.
- 34.67 Global classical Vlasov–Poisson: KEEP. "Vlasov" (only OT docstrings), "kinetic"; none.
- 34.70 Boltzmann's H theorem: KEEP. "Boltzmann" (only Boltzmann entropy on Wasserstein space: TauCeti/MeasureTheory/OptimalTransport/Wasserstein/BoltzmannEntropy.lean), "collision", "H-theorem"; no collision operator.
- 34.73 Renormalized Boltzmann existence: KEEP. "renormalized solution", "DiPerna"; none.
- 34.77 DiPerna–Lions transport renormalization: KEEP. "DiPerna", "renormaliz", "transport equation", "commutator estimate". Closest: TauCeti/MeasureTheory/OptimalTransport/ContinuityEquation/Basic.lean (TauCeti.IsContinuityEquation, distributional continuity equation for measures) and Endpoint.lean; no uniqueness/renormalization for Sobolev fields.

#### Section 35: Nonlinear functional analysis, monotone operators, and fixed points
Entries: 11 → 11 (removed 0, narrowed 0, kept 11).
- 35.9 Newton–Kantorovich convergence: KEEP. Searched "Newton", "Kantorovich" (OT only), "Newton iteration"; only polynomial/Henselian Newton (Mathlib/Dynamics/Newton.lean, Mathlib/RingTheory/Henselian.lean, TauCeti/RingTheory/AdicCompletion/Newton.lean). No Banach-space version.
- 35.12 Brouwer fixed-point theorem: KEEP. Searched "Brouwer" (only Jordan–Brouwer separation and Heyting/Brouwerian), "fixed point" with Convex/IsCompact, "no retraction", "Sperner", "hairy ball". Closest: TauCeti sphere homology (TauCeti/AlgebraicTopology/Cellular/RealProjective/Sphere.lean, AlgebraicTopology/Singular/JordanBrouwer.lean), from which Brouwer is not a few-line consequence.
- 35.13 Schauder fixed-point theorem: KEEP. "Schauder" hits are Schauder bases and Schauder estimates only.
- 35.15 Kakutani–Fan–Glicksberg: KEEP. "Kakutani" hits only Riesz–Markov–Kakutani; "Fan" only Ky Fan eigenvalue inequalities. Mathlib has upper/lower hemicontinuity (Mathlib/Topology/Semicontinuity/Hemicontinuity.lean) and Michael selection (Michael.lean, LowerHemicontinuous.exists_continuous_selection) but no set-valued fixed point.
- 35.21 Browder–Göhde–Kirk: KEEP. "nonexpansive", "Browder", "Göhde", "Kirk"; nonexpansive appears only in OT/convex Lipschitz lemmas. Mathlib/TauCeti have uniform convexity and Milman–Pettis (TauCeti/Analysis/Convex/Uniform.lean).
- 35.23 Degree axioms: KEEP. "topological degree", "Brouwer degree", "winding number" (only complex argument principle / Rouché in TauCeti/Analysis/Complex/Conformal); none.
- 35.28 Leray–Schauder degree: KEEP. "Leray–Schauder"; none.
- 35.32 Minty's range theorem: KEEP. "Minty", "maximal monotone", "monotone operator", "accretive", "resolvent". Closest: TauCeti/Analysis/Convex/Alexandrov.lean (monotonicity of convex subdifferential in R^n), Moreau–Yosida resolvents on metric spaces; no maximal monotone theory.
- 35.40 Browder–Minty surjectivity: KEEP. Same searches, "hemicontinuous" (Mathlib hits are set-valued hemicontinuity), "coercive"; closest TauCeti/Analysis/InnerProductSpace/Lions.lean (linear Lions representation theorem).
- 35.45 Existence for variational inequalities: KEEP. "variational inequality", "Stampacchia" (TauCeti/Analysis/SpecificLimits/Stampacchia.lean is the iteration lemma), "EVI" (metric gradient flows); none.
- 35.60 Crandall–Rabinowitz: KEEP. "Crandall", "Rabinowitz", "bifurcation"; none. Closest: TauCeti/Analysis/Fredholm/NormalForm.lean (Lyapunov–Schmidt normal form), which does not give the bifurcation curve without the genuine blow-up argument.

#### Section 36: Calculus of variations, Γ-convergence, and homogenization
Entries: 13 → 12 (removed 1, narrowed 0, kept 12).
- 36.1 Euler–Lagrange equation: KEEP. Searched "Euler–Lagrange" (only TauCeti/MeasureTheory/OptimalTransport/Wasserstein/EulerLagrange.lean, OT-specific), "first variation" (Riemannian geodesics), "Dirichlet principle"; no general integral functional.
- 36.12 Convex integral lower semicontinuity: KEEP. Searched "weakly lower semicontinuous", "Carathéodory integrand", WeakSpace lsc. Closest: Mathlib convex sets weakly closed (Mathlib/Analysis/LocallyConvex/WeakSpace.lean), TauCeti Mazur's lemma (TauCeti/Analysis/Normed/Module/Mazur.lean), OT/entropy lsc results; no Sobolev integral-functional statement.
- 36.17 Morrey's characterization: KEEP. "quasiconvex" (Mathlib QuasiconvexOn is the order-theoretic notion), "rank-one", "Morrey" (Sobolev embedding only); none.
- 36.20 Polyconvex existence: KEEP. "polyconvex", "minors"; none.
- 36.21 Quasiconvex relaxation: KEEP. "relaxation", "quasiconvex envelope"; none.
- 36.25 Young-measure compactness: KEEP. "Young measure"; none.
- 36.29 Div–curl lemma: KEEP. "div-curl", "compensated compactness", "Murat", "Tartar"; none.
- 36.31 Concentration–compactness vanishing lemma: KEEP. "concentration-compactness", "vanishing lemma", "Lions lemma"; none.
- 36.35 Mountain-pass theorem: KEEP. "mountain pass", "Palais–Smale", "deformation lemma", "Ekeland" (only references in TauCeti convex analysis), "minimax" (Sion only); none.
- 36.44 Fundamental theorem of Γ-convergence: REMOVE. Evidence: TauCeti, TauCeti/Topology/Semicontinuity/GammaConvergence.lean, TauCeti.TendstoGamma.tendsto_iInf and TauCeti.TendstoGamma.exists_isMinOn (equicoercive sequences on a first-countable space: infima converge, Γ-limit minimum attained), TauCeti.TendstoGamma.isMinOn_of_tendsto, TauCeti.TendstoGamma.lowerSemicontinuous; approximate minimizers follow from the liminf inequality plus tendsto_iInf in a few lines. No sorry in file.
- 36.50 Modica–Mortola: KEEP. "Modica", "Mortola", "Allen–Cahn", "double well"; none. TauCeti perimeter exists (TauCeti/Analysis/BoundedVariation/Perimeter.lean) as prerequisite.
- 36.54 Elliptic homogenization: KEEP. "homogeniz", "corrector", "periodic"; none. Closest: TauCeti elliptic energy forms and Dirichlet problem (TauCeti/Analysis/PDE/DirichletProblem.lean).
- 36.59 Two-scale compactness: KEEP. "two-scale", "Nguetseng"; none.

#### Section 37: Geometric measure theory, BV, rectifiability, and currents
Entries: 19 → 18 (removed 1, narrowed 1, kept 17).
- 37.4 Frostman's lemma: KEEP. Searched "Frostman", "Hausdorff content", "mass distribution"; none.
- 37.8 Projection dimension theorem: KEEP. "Marstrand", "Mattila", "projection theorem"; none.
- 37.13 Area formula: REMOVE. Evidence: TauCeti, TauCeti/MeasureTheory/Function/AreaFormula/Multiplicity.lean, LipschitzWith.lintegral_normDet_fderiv_mul_eq_lintegral_tsum (Lipschitz f between finite-dimensional inner product spaces, null-measurable s, measurable g ≥ 0: ∫_s J f · g = ∫ Σ_{fiber} g dμHE[dim U]) and lintegral_normDet_fderiv_eq_lintegral_encard; J f = normDet = sqrt(det(Df^T Df)), μHE normalized Hausdorff measure. No sorry in AreaFormula/.
- 37.14 Coarea formula: KEEP. "coarea", "co-area"; none.
- 37.18 Preiss's density theorem: KEEP. "Preiss", "density theorem", "rectifiable measure"; none. TauCeti/Geometry/MeasureTheory/Rectifiable.lean defines countably rectifiable sets only.
- 37.21 Besicovitch–Federer projection theorem: KEEP. "unrectifiable", "Besicovitch–Federer"; none.
- 37.24 BV compactness: NARROW. Evidence: TauCeti, TauCeti/Analysis/BoundedVariation/TotalVariation.lean, TauCeti.totalVariationOn_le_liminf (lsc of |Du|(Ω) under L^1_loc convergence); no compactness theorem for BV found ("compact" with totalVariationOn/BV). Entry now states only the compactness.
- 37.27 Jump-set structure: KEEP. "jump set", "approximate limit", "approximate continuity"; none.
- 37.30 Coarea for BV: KEEP. "coarea"; TauCeti has perimeter and total variation definitions only.
- 37.36 De Giorgi structure theorem: KEEP. "reduced boundary", "finite perimeter"; only TauCeti/Analysis/BoundedVariation/Perimeter.lean (definition, lsc, complements).
- 37.39 Gauss–Green theorem: KEEP. "Gauss–Green", "divergence theorem". Closest: Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean (boxes), TauCeti/MeasureTheory/Integral/DivergenceTheorem/{CompactSupport,HalfSpace}.lean, TauCeti/Analysis/Sobolev/Trace/IntegrationByParts.lean (half-space); none for reduced boundaries.
- 37.45 Interior regularity of minimizing boundaries: KEEP. "perimeter-minimizing", "minimal surface", "Simons"; none.
- 37.52 Federer–Fleming compactness: KEEP. "current", "Federer–Fleming", "flat norm", "comass"; no GMT currents.
- 37.54 Plateau existence: KEEP. "Plateau"; none.
- 37.57 Higher-codimension interior regularity: KEEP. "area-minimizing", "Almgren"; none.
- 37.59 Stationary monotonicity: KEEP. "varifold", "monotonicity formula", "stationary"; none.
- 37.62 Allard regularity: KEEP. "Allard", "tilt excess"; none.
- 37.66 Analyst's traveling-salesman theorem: KEEP. "traveling salesman", "Jones beta", "Ahlfors regular"; none. (TauCeti has curve length/arclength, TauCeti/Topology/MetricSpace/Arclength.)
- 37.67 Painlevé's problem: KEEP. "analytic capacity", "Painlevé", "removable" (only isolated removable singularities, Mathlib/Analysis/Complex/RemovableSingularity.lean); none.

#### Section 38: Potential theory and capacity
Entries: 13 → 13 (removed 0, narrowed 1, kept 12).
- 38.9 Distributional characterization: KEEP. Searched "subharmonic", "superharmonic", "Riesz measure", distributional Laplacian. Closest: TauCeti/Analysis/InnerProductSpace/Harmonic/Subharmonic.lean (TauCeti.SubharmonicOn: continuous functions with local sub-mean-value property, comparison principle); TauCeti/Analysis/PDE/GreenFunction/DistributionalLaplacian.lean (only for the ball Green kernel). No usc class or positive-measure characterization.
- 38.10 Riesz decomposition: KEEP. "Riesz decomposition", "Green potential"; TauCeti has Green kernels of ball/disk/half-space only (TauCeti/Analysis/PDE/GreenFunction/).
- 38.17 Equilibrium measure: KEEP. "capacity", "equilibrium measure", "capacitary"; only Choquet-type argument for analytic sets in TauCeti/MeasureTheory/MeasurableSpace/Analytic.lean (measure capacity, not Newtonian).
- 38.20 Choquet properties: KEEP. "Choquet", "capacitable"; none for Newtonian capacity.
- 38.28 Perron–Wiener solution: NARROW. Evidence: TauCeti, TauCeti/Analysis/PDE/Perron/Basic.lean, TauCeti.harmonicOnNhd_perronSolution (lower Perron solution, continuous subharmonic family, harmonic on any bounded open set with no boundary regularity); Perron/Barrier.lean (barriers, Dirichlet problem under exterior sphere). The upper solution is the symmetric case; missing is equality of upper and lower envelopes for continuous data (Wiener resolutivity). Entry rewritten to that.
- 38.30 Wiener's criterion: KEEP. "Wiener" (only Wiener–Hopf/Morse/Pick contexts), "thin"; only the exterior sphere barrier.
- 38.33 Harmonic measure: KEEP. "harmonic measure" (only reference citations in TauCeti/Analysis/Complex/Conformal); Poisson integrals on ball/half-space (TauCeti/Analysis/PDE/PoissonIntegral/) are the ball case only.
- 38.37 Martin representation: KEEP. "Martin boundary", "minimal harmonic"; none.
- 38.47 Nonlinear Wiener criterion: KEEP. "p-harmonic", "p-Laplacian", "p-capacity"; none.
- 38.49 Wolff potential estimates: KEEP. "Wolff" (only Denjoy–Wolff/length–area contexts); none.
- 38.57 Frostman's theorem: KEEP. "logarithmic energy", "logarithmic potential", "Frostman"; none.
- 38.60 Transfinite diameter: KEEP. "transfinite diameter", "Fekete", "Chebyshev constant"; none.
- 38.62 Weighted equilibrium: KEEP. "external field", "weighted equilibrium"; none.

#### Section 39: Metric measure spaces, Dirichlet forms, heat kernels, optimal transport, and fractals
Entries: 19 → 16 (removed 3, narrowed 1, kept 15).
- 39.4 Minimal upper gradients: KEEP. Searched upper gradient, Newtonian, p-modulus, Cheeger in both trees. Closest: TauCeti TauCeti/Analysis/GradientFlow/UpperGradient.lean (`TauCeti.IsStrongUpperGradient`, gradient-flow sense along AC curves) and TauCeti/MeasureTheory/Function/CheegerEnergy.lean (`TauCeti.cheegerEnergy`, relaxation definition); no curve modulus, no N^{1,p}, no minimal weak upper gradient.
- 39.13 Cheeger differentiation: KEEP. Searched Cheeger, Rademacher, doubling/Poincaré in metric settings; only Euclidean Rademacher (TauCeti AreaFormula) and the Cheeger energy definition.
- 39.18 Form–operator correspondence: KEEP. Searched Dirichlet form, closed form, Friedrichs, Kato representation, form domain; TauCeti has C0-semigroups (Analysis/Semigroups), unbounded self-adjoint operators (Analysis/InnerProductSpace/LinearPMap), PDE energy forms (Analysis/PDE/EnergyForm), but no closed-form → self-adjoint operator theorem.
- 39.19 Beurling–Deny criterion: KEEP. No Markov/sub-Markov semigroup or Dirichlet-form material found.
- 39.22 Process representation: KEEP. No Hunt process / Fukushima material.
- 39.23 Beurling–Deny decomposition: KEEP. Nothing found.
- 39.32 Parabolic Harnack equivalence: KEEP. Searched parabolic Harnack, caloric, heat kernel; only the Euclidean Gaussian heat kernel (TauCeti Analysis/PDE/HeatKernel/*) and elliptic Harnack.
- 39.40 Kantorovich duality: REMOVE. TauCeti TauCeti/MeasureTheory/OptimalTransport/Duality/LowerSemicontinuous.lean `TauCeti.isLUB_ofReal_kantorovichDualValue_integrable_of_lowerSemicontinuous` (strong duality, lsc ℝ≥0∞-valued costs, Polish spaces, integrable dual class); compact part: Duality/Attainment.lean `TauCeti.exists_isDualCertificate_of_continuous`/`isGreatest_kantorovichDualValue_integrable` (dual attained by c-conjugate potentials for bounded continuous costs) plus CTransform/Compact.lean `continuous_cTransform_coe` (c-transforms continuous on compact spaces), giving optimal continuous potentials by short glue; also Duality/Compact.lean `isLUB_kantorovichDualValue_continuous`.
- 39.46 Brenier's theorem: REMOVE. TauCeti TauCeti/MeasureTheory/OptimalTransport/Brenier.lean `TauCeti.exists_isKantorovichOptimalTransportMap_gradient` (μ ≪ Haar on finite-dim inner product space, finite quadratic cost; unique optimal plan = graph of ∇u, u convex lsc, map unique μ-a.e.) and `transportCost_norm_sub_sq_div_two_ne_top` (finite second moments ⇒ finite cost).
- 39.49 Benamou–Brenier formula: NARROW. TauCeti ContinuityEquation/PlanInterpolation.lean (Benamou–Brenier upper bound: displacement interpolation of an optimal plan solves the continuity equation with action ≤ / = W_p^p, `exists_isContinuityEquation_map_smul_fst_add_smul_snd...`) and Wasserstein/Superposition.lean (Lisini superposition for AC curves in P_p). The docstring states explicitly that the lower bound for arbitrary distributional solutions is not proved; entry narrowed to that lower bound.
- 39.51 Displacement convexity: KEEP. TauCeti has internal energy, Boltzmann and Rényi entropies (Wasserstein/InternalEnergy.lean, RenyiEntropy.lean) and geodesic convexity of potential/interaction energies, but no McCann convexity of internal energies.
- 39.53 Ricci curvature and entropy: KEEP. TauCeti MetricMeasure/CurvatureDimension.lean defines `CurvatureDimensionInfinity` and states von Renesse–Sturm only in prose; no equivalence with Ric + D²V ≥ K.
- 39.59 EVI uniqueness and contraction: REMOVE. TauCeti TauCeti/Analysis/GradientFlow/EVI/Basic.lean `TauCeti.IsEVISolution.dist_le` (d(u_t,v_t) ≤ e^{-λt} d(u_0,v_0), lsc energy), `IsEVISolution.eqOn` (uniqueness); EVI/Semigroup.lean `TauCeti.eviFlow_add`, `eviSemiflow` (semigroup law, continuous semiflow).
- 39.61 Wasserstein minimizing movements: KEEP. TauCeti has existence of the JKO step (Wasserstein/Resolvent.lean `WassersteinSpace.moreauYosidaResolvent_nonempty`), its uniqueness under generalized-geodesic convexity (GeneralizedGeodesic/Convex.lean), and existence of generalized minimizing movements (Analysis/GradientFlow/MinimizingMovement.lean); EVI/Semigroup.lean says existence of EVI solutions (AGS Thm 4.0.4) is not proved. No generation/convergence theorem.
- 39.65 Riemannian synthetic curvature: KEEP. Cheeger energy and CD(K,∞) are defined; no RCD, no heat flow identification or W_2 contraction.
- 39.72 Resistance-form realization: KEEP. Searched resistance form, effective resistance, Kigami; nothing.
- 39.73 Self-similar attractors: KEEP. Searched Hutchinson, iterated function system, attractor, self-similar; nothing. Ingredients only: Mathlib Topology/UniformSpace/Closeds.lean `NonemptyCompacts` completeness and Banach fixed point.
- 39.74 Similarity dimension: KEEP. Searched open set condition, Moran, similarity dimension; nothing.
- 39.77 Sub-Gaussian kernels: KEEP. Searched gasket, Sierpinski, walk dimension, sub-Gaussian (only probabilistic sub-Gaussian variables in Mathlib); nothing.

#### Section 40: One complex variable — graduate courses
Entries: 6 → 6 (removed 0, narrowed 0, kept 6).
- 40.25 Laurent expansion: KEEP. Searched Laurent, annulus in both trees. Closest: Mathlib Analysis/Complex/CauchyIntegral.lean (Cauchy formula/Goursat on annuli), TauCeti Analysis/Contour/MeromorphicLaurent.lean (finite principal part at a pole), TauCeti Analysis/Complex/Fuchsian/Cusp/Laurent.lean (Laurent q-expansion on punctured disc under a growth bound). No general annular Laurent series.
- 40.29 Great Picard theorem: KEEP. Searched Picard (only Picard–Lindelöf), essential singularity, Casorati; TauCeti ThricePuncturedSphere has only coordinates. Nothing.
- 40.60 Runge approximation: KEEP. Searched Runge, rational/polynomial approximation in Analysis/Complex; nothing.
- 40.62 Mergelyan's theorem: KEEP. Nothing found.
- 40.63 Mittag–Leffler theorem: KEEP. Only specific expansions: Mathlib Analysis/SpecialFunctions/Trigonometric/Cotangent.lean (cotangent), TauCeti TanhSeries.lean.
- 40.64 Weierstrass zero theorem: KEEP. Only finite divisors: Mathlib Analysis/Meromorphic/FactorizedRational.lean, Analysis/Complex/CanonicalDecomposition.lean; no infinite products with prescribed zeros.

#### Section 41: Classical function theory — entire and meromorphic functions, value distribution
Entries: 7 → 7 (removed 0, narrowed 0, kept 7).
- 41.10 Hadamard factorization: KEEP. Searched Hadamard (only three-lines and matrices), canonical product, elementary factor, order/genus of entire functions; nothing.
- 41.26 Cartwright zero distribution: KEEP. Searched Cartwright, exponential type, indicator, Paley–Wiener; nothing.
- 41.38 Logarithmic derivative lemma: KEEP. Mathlib Analysis/Complex/ValueDistribution/* has proximity, counting, characteristic, Cartan formula and first main theorem, but no logarithmic derivative lemma.
- 41.40 Second main theorem: KEEP. Mathlib Analysis/Complex/ValueDistribution/SecondMainTheorem.lean contains only the separation lemma `exists_sum_posLog_inv_norm_sub_le`; header says the theorem itself is future work. Truncated counting functions are defined (LogCounting/Truncated.lean).
- 41.48 Five-value theorem: KEEP. Nothing found.
- 41.52 Zalcman's rescaling lemma: KEEP. Searched Zalcman, spherical derivative, Marty; TauCeti has holomorphic Montel/normal families (Analysis/Complex/Conformal/NormalFamilies.lean) only.
- 41.59 Wiman–Valiron approximation: KEEP. Searched Wiman, Valiron, central index, maximum term; nothing.

#### Section 42: Hardy, Bergman, and model spaces; operators on analytic function spaces
Entries: 15 → 15 (removed 0, narrowed 1, kept 14).
- 42.1 Boundary realization: NARROW. TauCeti TauCeti/Analysis/Fourier/Hardy/Basic.lean (boundary H² as closed subspace of L²(circle), Hilbert basis) and Hardy/DiskFunction.lean `TauCeti.HardySpace.tendsto_eLpNorm_diskFunction_sub` (disc function of a boundary H² element has L² radial limit). No a.e. nontangential limits, no norm identity for the holomorphic H^p, no p ≠ 2; entry narrowed accordingly.
- 42.7 Canonical factorization: KEEP. Searched inner/outer function, Blaschke, singular inner; only finite canonical decomposition (Mathlib Analysis/Complex/CanonicalDecomposition.lean).
- 42.12 F. and M. Riesz theorem: KEEP. Searched F. and M. Riesz, analytic measure, Fourier–Stieltjes on the circle; nothing.
- 42.17 Beurling's invariant-subspace theorem: KEEP. Searched Beurling, shift-invariant, unilateral shift; "Beurling" only as Beurling transform in TauCeti Pompeiu.lean.
- 42.20 Carleson embedding theorem: KEEP. Searched Carleson; nothing.
- 42.24 Carleson interpolation theorem: KEEP. Nothing.
- 42.26 Nevanlinna–Pick theorem: KEEP. TauCeti Analysis/Complex/Pick/* and Herglotz.lean give Herglotz/Nevanlinna representations of Pick functions, not interpolation; Mathlib Reproducing.lean is abstract RKHS. No Pick interpolation theorem.
- 42.27 Corona theorem: KEEP. Nothing.
- 42.32 Toeplitz Fredholm index: KEEP. TauCeti Hardy/Toeplitz.lean and Hankel.lean (Toeplitz/Hankel operators, norm ≤ ‖a‖∞, adjoints, semicommutator `toeplitz_comp_sub_toeplitz`, `hankel_eq_zero_iff`); no Fredholmness or index theorem.
- 42.35 Nehari's theorem: KEEP. Only `TauCeti.norm_hankel_le`; no distance formula.
- 42.51 Bergman kernel: KEEP. Searched Bergman (only quiver/path algebra hits); nothing.
- 42.52 Bergman projection: KEEP. Nothing.
- 42.65 Stegenga's embedding theorem: KEEP. Searched Dirichlet space, Stegenga, capacity of arcs; nothing.
- 42.75 Shapiro compactness criterion: KEEP. Searched composition operator, Nevanlinna counting function on the disc; nothing.
- 42.82 Fock sampling density: KEEP. Searched Fock, Segal–Bargmann (only spin/Clifford Fock modules); nothing.

#### Section 43: Univalent functions, conformal mapping, and extremal methods
Entries: 9 → 9 (removed 0, narrowed 0, kept 9).
- 43.1 Grönwall area theorem: KEEP. TauCeti TauCeti/Analysis/Complex/Conformal/Area.lean is the area/change-of-variables formula for conformal maps; no statement for the class Σ or coefficient bound.
- 43.3 Koebe quarter theorem: KEEP. TauCeti Conformal/Koebe.lean is the Koebe square-root step of the Riemann mapping proof, not the quarter theorem; searched quarter, schlicht, Koebe function; nothing.
- 43.5 Distortion theorem: KEEP. Searched growth/distortion theorem; nothing (Schwarz–Pick derivative bounds only, Conformal/SchwarzPick/Derivative.lean).
- 43.8 de Branges's theorem: KEEP. Searched Bieberbach, de Branges, coefficient conjecture; nothing.
- 43.21 Loewner–Kufarev equation: KEEP. Searched Loewner (only Löwner order of operators), Kufarev, Loewner chain; nothing.
- 43.31 Nehari sufficient bound: KEEP. TauCeti Conformal/PreSchwarzian.lean (pre-Schwarzian composition and rigidity) and Univalence.lean (Noshiro–Warschawski) only; no Schwarzian univalence criterion.
- 43.34 Conformal invariance of extremal length: KEEP. Searched extremal length, curve modulus; closest TauCeti Conformal/LengthArea.lean and MeasureTheory/Integral/CircleLIntegral.lean (length–area inequality, Wolff's lemma), no extremal length.
- 43.49 Prime-end correspondence: KEEP. TauCeti Conformal/PrimeEnd/Crosscut/Basic.lean and Separation.lean define crosscuts and model separation only; no prime ends or compactification.
- 43.51 Jordan correspondence: KEEP (already narrowed in the coverage text). TauCeti Conformal/Caratheodory.lean `exists_continuousOn_closedBall_eqOn_iff_locallyConnectedSpace_frontier`, `exists_continuousOn_closedBall_bijOn_ball_of_isJordanCurve_frontier` (continuous extension); MonotoneExtension.lean `injOn_closedBall_of_isPreconnected_boundary_fiber` and BoundaryCorrespondence.lean `closureHomeomorph` (homeomorphism given connected boundary fibres / boundary injectivity). Caratheodory.lean states explicitly that injectivity for Jordan domains is not established.
- 2026-10-19: 43.51 REMOVED after the STRUCTURE43 revision. TauCeti Conformal/Jordan/Approach.lean `exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier` proves the homeomorphism of closures for Jordan domains; the remaining remark that local connectivity alone does not give injectivity is an example, not a substantial gap. Selection now 584.

#### Section 44: Riemann surfaces, quasiconformal mappings, and Teichmüller theory
Entries: 15 → 15 (removed 0, narrowed 4, kept 11).
- 44.3 Riemann–Hurwitz formula: NARROW. Evidence: TauCeti, TauCeti/FieldTheory/FunctionField/Different/Hurwitz.lean, `TauCeti.hurwitz_genus_formula`, `hurwitz_genus_formula_geometricDegree` (algebraic function fields, different divisor); TauCeti/Analysis/Complex/RiemannSurface/{Degree,Ramification,BranchValues,LocalNormalForm}.lean, `RiemannSurface.degree`, `ramificationDivisor`, `ramificationDegree_comp`, covering away from branch values (preparatory; docstrings say the Euler-characteristic step is not done). TauCeti/AlgebraicTopology/ThricePuncturedSphere/FilledCover/Ramification.lean `FilledCover.two_mul_genus_sub_two` uses a combinatorial genus of a permutation triple only. No genus of a compact Riemann surface found. Missing: analytic genus and the formula.
- 44.7 Uniformization: NARROW. Evidence: TauCeti, TauCeti/Analysis/Complex/Conformal/RiemannMapping/Existence.lean (Riemann mapping theorem for proper simply connected open subsets of ℂ). Searched "uniformization", "simply connected Riemann surface", "Koebe" in both libraries; no abstract-surface uniformization or deck-group quotient theorem.
- 44.12 Riemann–Roch theorem: NARROW. Evidence: TauCeti, TauCeti/FieldTheory/FunctionField/Differential/CanonicalDivisor.lean `TauCeti.exists_isRiemannRochDivisor` (Stichtenoth 1.5.15); TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/RiemannRoch/Basic.lean `SchemeWeilDivisor.eulerCharBelow_sheaf_eq_relativeDegree_add_one_sub_genus`; TauCeti/AlgebraicGeometry/LineBundle/SerreDuality.lean `finrank_cohomology_zero_sub_finrank_cohomology_zero_tensor_dual` (h^0(L)-h^0(ω⊗L^{-1}) = deg L+1-g on proper curves). TauCeti RiemannSurface/Meromorphic.lean defines meromorphic orders on Riemann surfaces but no L(D), genus, or Riemann existence/GAGA comparison (searched "Riemann existence", "GAGA"). Missing: analytic version on compact Riemann surfaces.
- 44.13 Serre duality: NARROW. Evidence: TauCeti, TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/SerreDuality.lean (H^1(O(D))^∨ ≃ H^0(O(K-D))), TauCeti/AlgebraicGeometry/LineBundle/SerreDuality.lean `nonempty_cohomologyOneDualEquivCohomologyZero_tensor_dual` (existence of an isomorphism for line bundles on proper curves). Missing: analytic duality on compact Riemann surfaces.
- 44.25 Riemann bilinear relations: KEEP. Searched "bilinear relation", "period matri", "Siegel upper"; closest: TauCeti/Geometry/Hodge/WeightOne/RiemannForm.lean (Riemann forms on lattices, linear algebra only). No periods of forms on surfaces.
- 44.27 Abel's theorem: KEEP. Closest: TauCeti/AlgebraicGeometry/WeilDivisor/AbelJacobi/*.lean, a formal divisor-class map x ↦ [x]-[x₀] into abstract Pic⁰, explicitly without the Jacobian variety or periods.
- 44.28 Jacobi inversion: KEEP. Same files; TauCeti's Riemann inequality gives effective representatives of algebraic divisor classes of degree ≥ g, but no analytic Abel map X^{(g)} → C^g/Λ.
- 44.38 Measurable Riemann mapping theorem: KEEP. Searched "quasiconformal", "Beltrami" (only Laplace–Beltrami hits in TauCeti Riemannian geometry); closest: TauCeti/Analysis/Complex/Pompeiu.lean (Cauchy transform inverts ∂̄ on compactly supported C¹ maps) and Sobolev W1p files.
- 44.49 Astala area distortion: KEEP. Nothing on quasiconformal maps found.
- 44.54 Extremal existence: KEEP. Searched "Teichmüller" (only Teichmüller lifts in p-adic files), "quadratic differential", "extremal length".
- 44.55 Teichmüller uniqueness: KEEP. As 44.54.
- 44.57 Dimension and contractibility: KEEP. As 44.54.
- 44.60 Bers embedding: KEEP. Searched "Bers", "Schwarzian"; TauCeti has a pre-Schwarzian file (Conformal/PreSchwarzian.lean) but no simultaneous uniformization or Teichmüller space.
- 44.63 Extremal-length distance formula: KEEP. No extremal length found in either library.
- 44.74 Mumford compactness: KEEP. Searched "Mumford" (abelian-variety rigidity only), "systole", "mapping class group" (braid groups only), "Weil–Petersson".

#### Section 45: Several complex variables, complex manifolds, pluripotential theory, and CR analysis
Entries: 20 → 20 (removed 0, narrowed 2, kept 18).
- 45.1 Hartogs separate analyticity: KEEP. Searched "Hartogs" (only algebraic Hartogs for normal schemes in TauCeti AlgebraicGeometry), "Osgood", "separately holomorphic/analytic"; closest: TauCeti/Analysis/Complex/CauchyIntegralPolydisc.lean (joint differentiability implies analyticity), which assumes joint complex differentiability.
- 45.2 Polydisk Cauchy formula: NARROW. Evidence: TauCeti, TauCeti/Analysis/Complex/CauchyIntegralPolydisc.lean, `DifferentiableOn.torusIntegral_prod_sub_inv_smul` (Cauchy formula on a polydisc), `DifferentiableOn.analyticOnNhd_of_finiteDimensional`, `TauCeti.analyticOnNhd_iff_differentiableOn_of_finiteDimensional`; no sorry. Mathlib's `TendstoLocallyUniformlyOn.differentiableOn` (Analysis/Complex/LocallyUniformLimit.lean) is one-variable only. Missing: full-polydisk convergence, Cauchy estimates, several-variable Weierstrass convergence.
- 45.5 Hartogs extension: KEEP. Same searches as 45.1; nothing.
- 45.7 Weierstrass preparation: KEEP. Closest: Mathlib, Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean (formal power series over an adically complete local ring); TauCeti, TauCeti/RingTheory/PowerSeries/Weierstrass/Preparation.lean (restricted series over complete ultrametric rings). Neither treats convergent complex germs.
- 45.8 Weierstrass division: KEEP. Same files (Mathlib `PowerSeries.IsWeierstrassDivisionAt`; TauCeti Weierstrass/Division.lean, nonarchimedean); no convergent complex version.
- 45.15 Levi problem: KEEP. Closest: TauCeti/Analysis/Complex/Pseudoconvex.lean, LeviForm.lean (pointwise strict plurisubharmonicity, Levi form calculus, Morse index bound). Searched "pseudoconvex domain", "domain of holomorphy", "holomorphically convex", "Stein"; nothing.
- 45.20 Oka–Weil approximation: KEEP. Searched "polynomially convex", "holomorphic hull", "Runge", "Oka"; nothing.
- 45.21 Oka coherence theorem: KEEP. Coherent-sheaf hits are algebraic (TauCeti AlgebraicGeometry/Cohomology); no analytic sheaves beyond TauCeti's holomorphic-germ sheaf on ℂ.
- 45.23 Cartan's theorem B: KEEP. Nothing for analytic spaces; TauCeti's affine vanishing is for quasi-coherent sheaves on schemes.
- 45.30 Local Dolbeault lemma: NARROW. Evidence: TauCeti, TauCeti/Analysis/Complex/Pompeiu.lean, `HasCompactSupport.two_pi_inv_smul_integral_sub_inv_smul_fderiv_apply_one_add_I_smul_apply_I` and `HasCompactSupport.fderiv_apply_one_add_I_smul_apply_I_two_pi_inv_smul_integral_sub_inv_smul` (Cauchy transform solves ∂̄u=f for compactly supported C¹ f in one variable; with a cutoff this gives the n=1 lemma). No Dolbeault complex or (p,q)-forms on ℂ^n found ("Dolbeault", "dbar").
- 45.33 Hörmander weighted estimate: KEEP. Searched "Hörmander" (hits are distribution theory, Pompeiu, LeviForm references), "weighted L2", "dbar"; nothing.
- 45.39 Strictly pseudoconvex subellipticity: KEEP. No ∂̄-Neumann operator found.
- 45.42 Ohsawa–Takegoshi extension: KEEP. Searched "Ohsawa"; nothing.
- 45.48 Poincaré–Lelong formula: KEEP. Searched "Poincaré–Lelong", "positive current", "current"; nothing in several variables.
- 45.50 Bedford–Taylor products: KEEP. Searched "Bedford", "plurisubharmonic" (only C² strict psh in TauCeti); nothing.
- 45.55 Monge–Ampère Dirichlet problem: KEEP. Closest: TauCeti/Analysis/Convex/MongeAmpere/*.lean (real Monge–Ampère measures of convex functions), not complex.
- 45.58 Calabi–Yau theorem: KEEP. Searched "Calabi" (Calabi–Yau algebras only), "Kähler"; nothing.
- 45.60 Dolbeault theorem: KEEP. Nothing on holomorphic vector bundles or Dolbeault cohomology.
- 45.67 Kodaira–Nakano vanishing: KEEP. Searched "Kodaira", "vanishing theorem"; nothing.
- 45.68 Kodaira embedding theorem: KEEP. Searched "Kodaira", "projective embedding", "ample"; only algebraic ampleness material, no analytic embedding theorem. Mathlib Geometry/Manifold/Complex.lean only proves constancy of holomorphic functions on compact complex manifolds.

#### Section 46: Complex dynamics
Entries: 16 → 16 (removed 0, narrowed 0, kept 16).
- 46.6 Repelling cycles are dense: KEEP. Searched "Julia set", "Fatou set", "repelling/attracting periodic", "periodic points dense", "Montel" (TauCeti Conformal/Montel/Basic.lean: locally bounded families only); no Julia/Fatou definitions in either library.
- 46.10 Koenigs linearization: KEEP. Searched "Koenigs", "Schröder equation", "linearization" (only TauCeti Morse-theoretic gradient linearization and Lie exponential); nothing holomorphic.
- 46.11 Böttcher's theorem: KEEP. Searched "Böttcher/Bottcher", "superattracting"; nothing.
- 46.12 Leau–Fatou flower theorem: KEEP. Searched "Leau", "flower", "petal"; only combinatorics hits.
- 46.19 Periodic Fatou classification: KEEP. Searched "Siegel disc/disk", "Herman ring", "Fatou component"; nothing. Closest: TauCeti Conformal/SchwarzPick/FixedPoint.lean and Rigidity.lean (disc self-maps).
- 46.20 Sullivan's no-wandering-domains theorem: KEEP. Searched "wandering domain", "quasiconformal"; nothing.
- 46.23 Hyperbolicity criteria: KEEP. Searched "postcritical", "hyperbolic rational"; nothing.
- 46.29 Connectedness criterion: KEEP. Searched "filled Julia", "escape rate"; nothing.
- 46.33 Equilibrium measure: KEEP. Searched "equilibrium measure", "logarithmic capacity", "harmonic measure" (only bibliography references in TauCeti); nothing.
- 46.35 Maximal entropy: KEEP. Mathlib Dynamics/TopologicalEntropy/*.lean defines cover/net entropy but computes no entropy of rational maps; no measure of maximal entropy.
- 46.40 Mandelbrot connectedness: KEEP. Searched "Mandelbrot"; nothing.
- 46.43 Holomorphic-motion extension: KEEP. Searched "holomorphic motion", "lambda lemma"; nothing.
- 46.45 Hybrid straightening: KEEP. Searched "polynomial-like", "straightening"; nothing.
- 46.48 Thurston characterization: KEEP. "Thurston" hits are 3-manifold geometrization and knot theory only.
- 46.52 Bowen dimension formula: KEEP. Searched "pressure", "transfer operator", "Ruelle"; Mathlib "Bowen" hits are entropy definitions only.
- 46.58 Eremenko escaping theorem: KEEP. Searched "escaping set", "Eremenko"; nothing.

#### Section 47: Approximation theory
Entries: 15 → 15 (removed 0, narrowed 1, kept 14).
- 47.6 Chebyshev alternation theorem: KEEP. Searched "equioscillation", "alternation theorem", "Haar space", "Chebyshev system", "best approximation" (TauCeti hit is operator approximation numbers); closest: Mathlib Analysis/SpecialFunctions/Trigonometric/Chebyshev/Extremal.lean (leading-coefficient extremality via Chebyshev nodes), not a best-approximation criterion.
- 47.13 Müntz–Szász theorem: KEEP. Searched "Müntz", "Szász"; nothing. Closest: Mathlib Stone–Weierstrass.
- 47.17 Korovkin theorem: KEEP. Searched "Korovkin"; nothing. Mathlib Analysis/SpecialFunctions/Bernstein.lean proves Bernstein-polynomial convergence directly, not Korovkin's criterion.
- 47.20 Jackson's trigonometric theorem: KEEP. Searched "Jackson", "modulus of smoothness/continuity", "K-functional", "trigonometric polynomial"; nothing quantitative.
- 47.21 Inverse trigonometric estimate: KEEP. Same searches; nothing.
- 47.23 Bernstein derivative inequality: KEEP. Searched "Bernstein inequality", "trigonometric polynomial" (only TauCeti Herglotz/Fejér material); nothing.
- 47.24 Markov inequality: NARROW. Evidence: Mathlib, Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Extremal.lean, `Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one` (for x ≥ 1, P^{(k)}(x) ≤ T_n^{(k)}(x) when |P| ≤ 1 on [-1,1]) with `derivative_T_eval_one` (T_n'(1)=n^2) in RingTheory/Polynomial/Chebyshev.lean: gives the endpoint case; interior points missing (rescaling gives only 2n^2).
- 47.32 Geometric convergence: KEEP. Searched "Bernstein ellipse", "Chebyshev truncation/interpolation"; closest: TauCeti Analysis/SpecialFunctions/Trigonometric/Chebyshev/HilbertBasis.lean and Parseval.lean (L^2 expansion, no rates).
- 47.35 Chebyshev interpolation stability: KEEP. Searched "Lebesgue constant"; nothing. Mathlib LinearAlgebra/Lagrange.lean has interpolation without stability bounds.
- 47.40 Newman's theorem: KEEP. Searched "Newman", "rational approximation" (Diophantine only); nothing.
- 47.42 B-spline basis: KEEP. Searched "B-spline", "spline"; nothing.
- 47.45 Schoenberg–Whitney theorem: KEEP. Searched "Schoenberg", "collocation"; nothing.
- 47.48 Spline Jackson estimates: KEEP. Nothing on splines.
- 47.51 Smoothing-spline representer theorem: KEEP. Nothing on splines or representer theorems for smoothing.
- 47.66 Sobolev widths: KEEP. Searched "Kolmogorov width", "n-width", "democratic", "greedy"; closest: TauCeti Analysis/OperatorIdeal/ApproximationNumber/*.lean (approximation numbers, Eckart–Young, min–max for compact operators), without Kolmogorov widths or the Sobolev-ball computation.

#### Section 48: Orthogonal polynomials, moment problems, and spectral recurrences
Entries: 16 → 16 (removed 0, narrowed 1, kept 15).
- 48.4 Favard's theorem: KEEP. Searched "Favard", "three-term recurrence", "Jacobi matrix/operator", "tridiagonal"; nothing for general measures (only Hermite ladder/recurrence identities in TauCeti).
- 48.6 Real and simple zeros: KEEP. Searched "orthogonal polynomial", "simple zeros/roots", "interlacing"; TauCeti SimpleRoots files concern continuity of roots, not orthogonality. Nothing for general μ.
- 48.8 Christoffel–Darboux formula: KEEP. Searched "Christoffel", "Darboux" (Mathlib Darboux theorem for derivatives only); nothing.
- 48.14 Gauss quadrature: KEEP. Searched "quadrature", "Gauss–Jacobi"; nothing.
- 48.22 Bounded Jacobi correspondence: KEEP. No Jacobi operators found.
- 48.29 Determinacy correspondence: KEEP. Searched "essentially self-adjoint", "Hamburger"; nothing. TauCeti Probability/Moments/Determinacy.lean is a sufficient condition only.
- 48.32 Hamburger theorem: KEEP. Searched "Hamburger", "moment sequence", "Hankel"; closest: TauCeti Analysis/Matrix/PosSemidef.lean `TauCeti.sub_nonneg_of_posSemidef_hankel` (a bounded PSD Hankel estimate) and Analysis/Bochner/Herglotz.lean `TauCeti.exists_isFiniteMeasure_integral_zpow_eq` (circle/trigonometric moment problem), neither the real-line existence theorem.
- 48.33 Stieltjes theorem: KEEP. TauCeti "Stieltjes moment" hit (Analysis/CompletelyMonotone/Stieltjes/Uniqueness.lean) concerns uniqueness for Stieltjes functions; no existence criterion via the two Hankel matrices.
- 48.34 Hausdorff theorem: NARROW. Evidence: TauCeti, TauCeti/Probability/Moments/CompactDeterminacy.lean `Measure.ext_of_forall_integral_monomial_eq_of_support` (measures on a compact set determined by moments) gives uniqueness; existence for completely monotone sequences not found. Closest existence result: TauCeti Analysis/CompletelyMonotone/Bernstein/HausdorffBernsteinWidder.lean `TauCeti.hausdorff_bernstein_widder` (continuous-variable Bernstein theorem; extending a sequence to a CM function is not routine).
- 48.36 Moment Carleman criteria: KEEP. Searched "Carleman"; closest: TauCeti Probability/Moments/Determinacy.lean (determinacy under a finite exponential moment, strictly weaker) and LaplaceDeterminacy.lean.
- 48.40 Nevanlinna parametrization: KEEP. TauCeti has Pick/Nevanlinna function representations (Analysis/Complex/Pick/*.lean, CompletelyMonotone/Stieltjes/Nevanlinna.lean), but no indeterminate moment problem or Nevanlinna matrix.
- 48.49 Verblunsky theorem: KEEP. Searched "Verblunsky", "Schur parameter", "Geronimus", "Szegő recursion"; nothing.
- 48.53 CMV representation: KEEP. Searched "CMV" (only unrelated tactic hits); nothing.
- 48.54 Szegő theorem: KEEP. Searched "Szegő/Szego", "Toeplitz determinant"; nothing.
- 48.57 Strong Szegő theorem: KEEP. Same; nothing.
- 48.60 Equilibrium zero distribution: KEEP. Searched "equilibrium measure", "logarithmic capacity", "zero-counting"; nothing.

#### Section 49: Special functions, integral transforms, and classical formulae
Entries: 12 → 12 (removed 0, narrowed 1, kept 11).
- 49.6 Multiplication formula: KEEP. Searched "multiplication", Gamma products, `prod.*Gamma` in both trees. Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean has only `Complex.Gamma_mul_Gamma_add_half` (duplication, m=2) and reflection; BohrMollerup.lean has the Bohr–Mollerup characterization and `Gamma_seq_tendsto_Gamma` (inputs for a proof, not the formula). TauCeti MultivariateGamma has unrelated finite products.
- 49.13 Gauss equation: KEEP. Mathlib/Analysis/SpecialFunctions/OrdinaryHypergeometric.lean and RegularizedHypergeometric.lean define ₂F₁ / regularized pFq and prove radius results only; no differential equation. TauCeti RegularizedHypergeometric.lean has only ₀F₁ contiguous relation and derivative of ₀F₁. Searched "hypergeometric.*(differential|equation)".
- 49.26 Second solution: KEEP. Mathlib/Analysis/SpecialFunctions/Bessel.lean lists "Bessel function of the second kind" as TODO; no besselY/Hankel functions in either tree (TauCeti has only Real.besselI).
- 49.30 Bessel generating function: KEEP. Listed as TODO in Mathlib Bessel.lean; no match in TauCeti.
- 49.32 Hankel transform: KEEP. Searched "Hankel transform", "hankelTransform", radial Fourier; nothing.
- 49.36 Airy representation: KEEP. No "Airy"/"airy" declarations in either tree.
- 49.40 Jacobi orthogonality: KEEP. No Jacobi/Gegenbauer polynomials; Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean has only Rodrigues formula, coefficients and symmetry (no orthogonality). TauCeti orthogonality results are for Hermite functions only.
- 49.42 Laguerre system: KEEP. No "laguerre" anywhere.
- 49.45 Spherical addition theorem: KEEP. Searched "spherical harmonic", "zonal", "harmonic polynomial", "addition theorem"; nothing.
- 49.50 Jacobi elliptic identities: KEEP. Searched "Jacobi elliptic", sn/cn, "complete elliptic", ellipticK; Mathlib has only Weierstrass ℘ (Elliptic/Weierstrass.lean) and Jacobi theta functions.
- 49.66 Bromwich inversion: NARROW. Mathlib/Analysis/MellinInversion.lean `mellinInv_mellin_eq` (Mellin-convergent f, transform integrable on the vertical line, f continuous at x) gives the Laplace/Bromwich formula at continuity points by substitution x=e^{-t}. Missing: principal-value limit and midpoint value for piecewise C¹ functions without absolute integrability of the transform. TauCeti Laplace material (CompletelyMonotone/...) concerns Bernstein representation and uniqueness, not complex inversion.
- 49.76 Mittag–Leffler entire functions: KEEP. "Mittag" only hits the cotangent partial-fraction expansion and Mittag-Leffler systems in category theory.

#### Section 50: Asymptotic analysis, resurgence, and perturbation
Entries: 14 → 14 (removed 0, narrowed 0, kept 14).
- 50.6 Borel–Ritt theorem: KEEP. Searched "Borel.?Ritt", "Ritt", "asymptotic expansion", "Borel's lemma" in both trees; no asymptotic-expansion notion or realization theorem (Mathlib Asymptotics/* has only O/o/~, SuperpolynomialDecay).
- 50.9 Watson's lemma: KEEP. "Watson" only in a bibliography reference; no Laplace-integral asymptotics.
- 50.11 Interior Laplace minimum: KEEP. Searched "Laplace method", Laplace asymptotics; closest content is the TauCeti Morse lemma (TauCeti/Analysis/Calculus/Morse/LocalNormalForm.lean) and Mathlib's Stirling formula, neither giving the Laplace asymptotic.
- 50.14 Stationary phase: KEEP. Searched "stationary phase", "van der Corput", "oscillatory integral"; only a Cauchy characteristic-function computation in TauCeti.
- 50.18 Coalescing saddles: KEEP. No Airy functions or cubic normal forms in either tree.
- 50.23 Euler–Maclaurin formula: KEEP. Searched "Euler.?Maclaurin", "Euler summation", "periodizedBernoulli"; Mathlib NumberTheory/ZetaValues.lean has `periodizedBernoulli`, `bernoulliFun_eq_integral` and Fourier coefficients, and NumberTheory/AbelSummation.lean has Abel summation (the first-order case only, not the formula with Bernoulli remainder).
- 50.29 Karamata Tauberian theorem: KEEP. Searched "Karamata", "slowly varying", "regularly varying", "Tauber"; only Wiener–Ikehara (TauCeti/NumberTheory/LSeries/WienerIkehara) and Karamata's majorization inequality (TauCeti SchurHorn), both distinct.
- 50.31 Levelt–Turrittin formal structure: KEEP. Searched "Turrittin", "Levelt", "irregular singular"; nothing.
- 50.35 Liouville–Green approximation: KEEP. Searched "WKB", "Liouville.?Green"; nothing.
- 50.37 Simple turning points: KEEP. Searched "turning point", "Airy"; nothing.
- 50.45 Borel–Laplace theorem: KEEP. Searched "Gevrey", "Borel sum", "Borel transform", "resurgen"; nothing.
- 50.51 Ramis–Sibuya theorem: KEEP. Searched "Ramis", "Sibuya", "Gevrey"; nothing.
- 50.58 Tikhonov theorem: KEEP. Searched "Tikhonov", "singular perturbation", "slow manifold"; only Tychonoff compactness hits.
- 50.60 Fenichel persistence: KEEP. Searched "Fenichel", "normally hyperbolic", "slow manifold"; closest is TauCeti Lyapunov–Perron stable/unstable manifolds of hyperbolic equilibria (TauCeti/Analysis/ODE/LyapunovPerron, Analysis/Calculus/Morse/LocalInvariantManifold.lean), not persistence of normally hyperbolic manifolds.

#### Section 51: Integrable systems and Riemann–Hilbert methods
Entries: 20 → 20 (removed 0, narrowed 0, kept 20).
- 51.4 Matrix partial indices: KEEP. Searched "Birkhoff factori", "partial ind", "Wiener.?Hopf", "Toeplitz"; closest is TauCeti Toeplitz/Hankel operators on Hardy space (TauCeti/Analysis/Fourier/Hardy/Toeplitz.lean, Hankel.lean), no matrix factorization.
- 51.6 Singular-integral formulation: KEEP. Searched "Riemann.?Hilbert", "Plemelj", "Sokhotski", "Cauchy transform"; only Mathlib MeasureTheory/Measure/ResolventTransform.lean (Cauchy–Stieltjes transform of a measure) and TauCeti Hilbert transform / Calderón–Zygmund theory on ℝⁿ, no contour Cauchy operators or RH problems.
- 51.8 Small-norm theorem: KEEP. Same searches; no contour Cauchy operators (Neumann series itself is generic).
- 51.14 Parametrix error theorem: KEEP. No Riemann–Hilbert or steepest-descent material.
- 51.16 Jost solutions: KEEP. Searched "Jost", "reflection coefficient", "scattering"; nothing relevant.
- 51.20 Marchenko reconstruction: KEEP. Searched "Marchenko", "Gelfand.?Levitan", "inverse scattering"; nothing.
- 51.22 KdV Lax pair: KEEP. Searched "KdV", "Korteweg", "Lax pair", "Lax equation"; nothing.
- 51.23 Linear evolution of scattering data: KEEP. As above.
- 51.25 Multisoliton determinant: KEEP. Searched "soliton"; nothing.
- 51.35 Liouville–Arnold theorem: KEEP. Searched "Liouville.?Arnold", "action.?angle", "first integral", "in involution", "symplectic manifold"; only linear symplectic algebra (TauCeti/LinearAlgebra/SymplecticGroup.lean, BilinearForm/SymplecticBasis.lean) and Mathlib Hofer.lean (unrelated metric lemma).
- 51.43 Theta-function solutions: KEEP. No KdV or Riemann theta functions in genus > 1.
- 51.46 Toda Lax equations: KEEP. Searched "Toda", "Jacobi matri", "isospectral"; nothing.
- 51.50 Schlesinger equations: KEEP. Searched "Schlesinger", "isomonodrom", "Fuchsian"; nothing.
- 51.53 Painlevé property: KEEP. "Painlev" hits only Painlevé removability in TauCeti conformal-mapping files.
- 51.54 Hastings–McLeod solution: KEEP. Searched "Hastings", "Airy"; nothing.
- 51.58 Fokas–Its–Kitaev characterization: KEEP. No RH problems; no orthogonal polynomials for general weights.
- 51.62 Bulk universality: KEEP. Searched "sine kernel", "universality", "equilibrium measure"; nothing relevant.
- 51.63 Soft-edge universality: KEEP. Searched "Airy kernel"; nothing.
- 51.65 Tracy–Widom formula: KEEP. Searched "Tracy", "Widom", "Fredholm determinant"; TauCeti Fredholm determinants are finite-dimensional/nonarchimedean (TauCeti/Analysis/Matrix/CharPowerSeries, Ultra.lean), no Airy-kernel determinant.
- 51.66 Longest increasing subsequences: KEEP. Searched "longest increasing", "increasing subsequence", "Erdős–Szekeres", "Ulam", "Vershik", "Hammersley", "Baik"; nothing relevant.

#### Section 52: Geometric analysis on manifolds
Entries: 34 → 34 (removed 0, narrowed 1, kept 33).
General search locations: Mathlib/Geometry/Manifold (Riemannian/Basic.lean, PathELength.lean, PoincareConjecture.lean with proof_wanted only); TauCeti/Geometry/Manifold/Riemannian (Geodesic/*, Isometry/*, Laplacian.lean, Conformal.lean, VolumeDensity/*, FirstVariation.lean, VariationField.lean), TauCeti/Geometry/Symplectic/*, TauCeti/Analysis/Calculus/Morse/*, TauCeti/Geometry/Manifold/Morse/*, TauCeti/Analysis/PDE/*, TauCeti/LowDimTopology/Geometrization.lean.
- 52.3 Jacobi fields and second variation: KEEP. Searched "Jacobi field", "second variation", "index form", "conjugate point"; TauCeti has only the first variation of energy (Riemannian/FirstVariation.lean `TauCeti.Manifold.hasDerivAt_energy`) and the curvature operator (Isometry/Curvature.lean).
- 52.5 Rauch comparison: KEEP. "Rauch", "comparison" in Riemannian dirs: only length/variation comparisons (EDistComparison, EVariationComparison), no curvature comparison.
- 52.7 Bonnet–Myers theorem: KEEP. "Myers"/"Bonnet" hit only author names; no Ricci lower-bound results.
- 52.8 Bishop–Gromov comparison: KEEP. "Bishop"/"Gromov" hits are Gromov product, Gromov compactness remarks; no volume comparison.
- 52.10 Cheeger–Gromoll splitting: KEEP. "splitting theorem", "Cheeger", "line": algebraic splitting theorems only.
- 52.11 Compactness with controlled geometry: KEEP. No Cheeger–Gromov convergence of Riemannian manifolds.
- 52.17 Bochner identity: KEEP. "Bochner" hits only the Bochner integral; "Weitzenböck" nothing. TauCeti Laplacian.lean has Hessian and Laplace–Beltrami but no Bochner formula.
- 52.19 Cheng–Yau gradient estimate: KEEP. "Cheng.?Yau", "gradient estimate"; TauCeti PDE/Harnack is Euclidean harmonic-function Harnack theory, not curvature-dependent manifold estimates.
- 52.21 Li–Yau differential estimate: KEEP. "Li.?Yau"; TauCeti PDE/HeatKernel is Euclidean.
- 14.49 Lichnerowicz–Obata theorem (reviewed here; now in Section 14): KEEP. "Lichnerowicz", "Obata", "first eigenvalue": only abstract Rayleigh-quotient results (TauCeti Analysis/InnerProductSpace/Variational).
- 52.31 Yamabe theorem: KEEP. TauCeti has only preliminaries: Euclidean Yamabe bubbles (Analysis/PDE/Yamabe/Bubble.lean), conformal change of gradient and volume (Riemannian/Conformal.lean, VolumeDensity/Conformal.lean).
- 52.37 Eells–Sampson existence: KEEP. "harmonic map", "tension field", "Eells"; nothing.
- 52.41 Two-dimensional weak regularity: KEEP. "Hélein", "weakly harmonic map"; nothing.
- 52.43 Bubble convergence on surfaces: KEEP. "bubbl" only in a TauCeti docstring about J-holomorphic mean-value inequality; no harmonic-map bubbling.
- 52.48 Stability operator: KEEP. "minimal hypersurface", "stability operator", "second fundamental form"; nothing.
- 52.52 Douglas–Radó Plateau theorem: KEEP. "Plateau", "Douglas", "Radó", "minimal surface"; nothing.
- 52.56 Bernstein theorem for graphs: KEEP. "Bernstein" hits concern Bernstein polynomials/functions only.
- 52.58 Short-time existence (MCF): KEEP. "mean curvature flow"; nothing.
- 52.61 Huisken monotonicity: KEEP. "Huisken"; nothing.
- 52.62 Convex hypersurface convergence: KEEP. Nothing.
- 52.66 Hamilton–DeTurck existence: KEEP. "Ricci flow", "DeTurck"; nothing.
- 52.71 Hamilton compactness: KEEP. Nothing.
- 52.73 Perelman W monotonicity: KEEP. "Perelman" only in the geometrization statement docstring.
- 52.74 No local collapsing: KEEP. Nothing.
- 52.75 Hamilton's three-dimensional convergence: KEEP. Nothing.
- 52.77 Three-dimensional geometrization: KEEP. TauCeti/LowDimTopology/Geometrization.lean defines `TauCeti.GeometrizationConjecture` as a Prop ("stated, not proved"); Mathlib PoincareConjecture.lean has proof_wanted only.
- 52.80 Symplectic nonsqueezing: KEEP. "nonsqueezing", "Gromov width"; TauCeti J-holomorphic energy estimates (Geometry/Symplectic/JHolomorphic/Energy/*) are ingredients only.
- 52.81 Morse homology: NARROW. TauCeti/Analysis/Calculus/Morse/Boundary/Basic.lean `TauCeti.morseBoundary` (mod-two boundary for Morse–Smale flows with compact sublevels on finite-dimensional inner-product spaces) and Boundary/Square.lean `TauCeti.morseBoundary_comp_morseBoundary_eq_zero_iff` (∂²=0 iff broken index-two trajectory sets are even); the files state that compactification/gluing, hence ∂²=0 itself, is not proved. Missing: ∂²=0, closed-manifold setting, isomorphism with singular homology.
- 52.82 Hamiltonian Floer continuation: KEEP. "Floer" appears only in references for DG local systems.
- 52.85 Uhlenbeck gauge theorem: KEEP. "Uhlenbeck", "Coulomb gauge", "Yang.?Mills"; nothing (gauge hits are quiver rescalings).
- 52.86 Gauge compactness: KEEP. Same.
- 52.87 Rashevskii–Chow theorem: KEEP. "Chow", "Rashevsk", "bracket.?generating", "sub.?Riemannian", "horizontal curve"; TauCeti Distribution.lean has involutive distributions and the Frobenius theorem only.
- 52.89 Ball–box theorem: KEEP. "ball.?box", "privileged coordinates"; nothing.
- 52.92 Positive mass theorem: KEEP. "positive mass", "ADM", "asymptotically flat"; nothing.

#### Section 53: Elliptic operators on manifolds, index theory, and spectral geometry
Entries: 38 → 38 (removed 0, narrowed 0, kept 38).
General search locations: TauCeti/Analysis/Fredholm/*, TauCeti/Analysis/PDE/* (Spectrum, FredholmAlternative, Ellipticity, HeatKernel), TauCeti/Analysis/InnerProductSpace/{Spectrum,Variational,CourantFischer}.lean, TauCeti/Geometry/Manifold/{DeRham,DifferentialForm,Riemannian/Laplacian.lean,Morse}, TauCeti/Topology/VectorBundle/EulerClass.lean, TauCeti/LinearAlgebra/CliffordAlgebra, TauCeti/RepresentationTheory/Spin, TauCeti/Geometry/Hodge (linear Hodge structures), Mathlib/LinearAlgebra/ExteriorPower/HodgeStar.lean.
- 53.5 Fredholm alternative: KEEP. "elliptic operator", "principal symbol", "pseudodifferential": only Euclidean bounded-domain results (TauCeti/Analysis/PDE/FredholmAlternative.lean, Dirichlet problem for divergence-form operators) and abstract Fredholm theory; no elliptic operators between bundles on closed manifolds.
- 53.9 Complete Dirac operators: KEEP. "Dirac operator", "essentially self-adjoint", "spinor bundle"; only algebraic Clifford/spinor modules.
- 53.12 Hodge theorem for elliptic complexes: KEEP. "Hodge theorem", "harmonic form", "Hodge Laplacian"; TauCeti DeRham has cohomology only; Mathlib HodgeStar.lean is linear algebra.
- 53.16 Hodge theory with boundary: KEEP. Same searches; nothing.
- 45.64 Kähler Hodge decomposition (reviewed here; now in Section 45): KEEP. "Kähler"; only Mathlib's oriented-angle `kahler` form; TauCeti Geometry/Hodge is abstract linear Hodge structures.
- 45.66 Hard Lefschetz theorem (reviewed here; now in Section 45): KEEP. "Lefschetz" hits only Lefschetz principle, Picard–Lefschetz reference, Poincaré–Lefschetz duality remark.
- 53.20 Witten deformation and Morse inequalities: KEEP. "Witten", "Morse inequalit"; TauCeti Geometry/Manifold/Morse/CriticalPoints.lean only counts critical points (docstring calls them the coefficients of the Morse polynomial); no inequalities.
- 53.21 Local heat expansion: KEEP. "heat kernel expansion", "Minakshisundaram", "heat trace"; TauCeti PDE/HeatKernel is the Euclidean Gaussian kernel.
- 53.24 Weyl law: KEEP. "Weyl law", "eigenvalue counting"; only Weyl's perturbation inequality (TauCeti CourantFischer.lean) and the explicit interval spectrum (PDE/Spectrum/Interval.lean).
- 53.28 Two-term boundary Weyl law: KEEP. As above.
- 53.30 Spectral zeta function: KEEP. "spectral zeta"; nothing.
- 53.32 Eta invariant: KEEP. "eta invariant"; nothing.
- 53.34 Cheeger–Müller theorem: KEEP. "analytic torsion", "Ray.?Singer", "Reidemeister torsion"; nothing.
- 53.38 Schrödinger–Lichnerowicz formula: KEEP. "Lichnerowicz", "spin structure"; nothing.
- 53.39 Positive-scalar-curvature obstruction: KEEP. Nothing.
- 53.41 McKean–Singer identity: KEEP. "McKean", "supertrace"; nothing.
- 53.42 Local index theorem: KEEP. "Getzler", "index theorem"; nothing.
- 53.43 Atiyah–Singer theorem: KEEP. "Atiyah" only Atiyah–Macdonald citations; no topological K-theory/Thom isomorphism (Bott periodicity hits are for Clifford algebras).
- 53.44 Spin index formula: KEEP. "A-hat genus", "Chern character"; nothing.
- 53.46 Chern–Gauss–Bonnet theorem: KEEP. "Gauss.?Bonnet", "Pfaffian", "Euler class"; only Gauss–Bonnet area formula for hyperbolic polygons (TauCeti Analysis/Complex/UpperHalfPlane/Polygon/.../GaussBonnet.lean) and the topological Euler class (Topology/VectorBundle/EulerClass.lean).
- 53.47 Hirzebruch signature theorem: KEEP. "signature theorem", "L-genus", "Pontryagin class"; nothing.
- 53.48 Hirzebruch–Riemann–Roch theorem: KEEP. "Riemann.?Roch" hits are function-field/Weil-divisor Riemann–Roch spaces in TauCeti algebraic geometry, not HRR for complex manifolds.
- 53.49 Families index theorem: KEEP. Nothing; TauCeti Fredholm/ContinuousFamily.lean is local constancy of the integer index, not an index class in K⁰(B).
- 53.54 Atiyah–Patodi–Singer formula: KEEP. Nothing.
- 53.55 Spectral flow as index: KEEP. "spectral flow"; nothing.
- 53.58 Atiyah's L² index theorem: KEEP. "von Neumann dimension", "L2 index"; nothing.
- 53.60 Bergman kernel asymptotics: KEEP. "Bergman" only diamond-lemma citations.
- 14.22 Szegő–Weinberger theorem (reviewed here; now in Section 14): KEEP. "Szegő", "Weinberger", "Faber.?Krahn"; nothing.
- 14.20 Cheeger spectral bound (reviewed here; now in Section 14): KEEP. "Cheeger constant"; TauCeti has only Cheeger energy local Lipschitz constant.
- 53.68 Steklov spectrum: KEEP. "Steklov" only journal citations; "Dirichlet.?to.?Neumann" nothing.
- 53.69 Courant nodal theorem: KEEP. "Courant", "nodal" (only Courant–Fischer min–max and Lagrange nodal polynomials).
- 53.71 Analytic nodal-volume bounds: KEEP. Nothing.
- 53.72 Sogge eigenfunction bounds: KEEP. "Sogge"; nothing.
- 53.76 Quantum ergodicity: KEEP. "quantum ergodic", "Shnirelman"; nothing.
- 53.77 Wave trace and lengths: KEEP. "wave trace", "Duistermaat", "Guillemin"; nothing.
- 53.78 Selberg trace formula: KEEP. "Selberg", "trace formula"; nothing.
- 53.79 Hyperbolic resonances: KEEP. "resonance", "convex.?cocompact"; nothing.
- 53.80 Spectral information and nonuniqueness: KEEP. "isospectral", "Milnor" (only Milnor join); nothing.

