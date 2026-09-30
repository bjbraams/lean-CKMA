# Coding Conventions and Mathematical Practices in Mathlib

This file summarizes style conventions and mathematical practices that are followed in Lean Mathlib
code. The summaries support specific instructions to LLM that may be put into an AGENTS.md file.
For coding conventions (Lean style conventions) it is possible to refer to detailed documents
addressed to Lean developers. Mathematical conventions are less well documented and for present
purposes they are often discovered by studying Mathlib code. In that case the objective here is to
provide more explicit precision.

The two main concerns are the **generality** of mathematical statements and the **duplication** of
statements and proofs. For each rule the document says whether it is (a) written down in official
Mathlib documentation, (b) enforced mechanically by a linter or an import check, or (c) implicit,
inferred from the code. Rules of kind (c) are marked *Observed* and cite the evidence. Evidence was
taken from the Mathlib checkout used in this project (commit `065356127b1d`, 2026-09-16); counts are
approximate and meant only to show that a pattern is systematic.

## Sources

Official community documentation, all under https://leanprover-community.github.io/contribute/:

- `index.html`: the entry point. It says that "mathlib intentionally has very high standards (on
  generality, integration with the remaining library and maintainability, including code style)".
- `values.html`, **Mathlib's values**. This is the only official page that states the generality
  principles explicitly (sections *General definitions*, *Weak hypotheses*, *Strong conclusions*,
  *Classical not constructive*, *Downstream projects*). See the section on mathematical statements
  below.
- `pr-review.html`, **Pull request review guide**. This is the main official source on duplication
  and placement (sections *Location*, *Do the results already exist?*, *Are new imports
  introduced?*, *Library integration*, *Is it general enough to support known future needs?*).
- `style.html` (library style), `naming.html` (naming), `doc.html` (documentation),
  `commit.html` (commit messages), `how-to-contribute.html`.

Documentation inside the Mathlib source tree:

- **Library notes.** Design decisions are recorded as `library_note «...»` declarations. They
  can be found with `grep -rn 'library_note «' Mathlib`. The ones most relevant here are «the
  algebraic hierarchy» (`Mathlib/Algebra/HierarchyDesign.lean`), «forgetful inheritance»
  (`Mathlib/Algebra/Group/Monoid.lean`), «continuity lemma statement» and «comp_of_eq lemmas»
  (`Mathlib/Topology/Continuous.lean`), «decidable arguments» (`Mathlib/Basic/Logic/Basic.lean`),
  «specialised high priority simp lemma» (`Mathlib/Data/NNRat/Defs.lean`) and «foundational
  algebra order theory» (`Mathlib/Data/Nat/Init.lean`).
- **Linters** in `Mathlib/Tactic/Linter/` and in Batteries (`Batteries/Tactic/Lint/`). Their
  docstrings are the authoritative statement of what is enforced mechanically.
- The `Wanted/` directory (statements with `proof_wanted`, no proof) and `Counterexamples/`
  (formalized counterexamples showing that hypotheses cannot be dropped).

Background: *The Lean mathematical library* (mathlib community, CPP 2020,
https://arxiv.org/abs/1910.09336), cited by the «the algebraic hierarchy» library note. On junk
values, which let Mathlib state many lemmas without hypotheses: K. Buzzard, *Division by zero in
type theory: a FAQ* (https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/).

## Lean style conventions

Instruction: Adhere to the broad Best Practices guidelines in this document:
https://lean4.dev/language/best-practices.
(Note: this page is a third-party summary of general Lean 4 idiom, not a Mathlib document. Where
it differs from the Mathlib pages below, the Mathlib pages take precedence.)

Instruction: Adhere to the naming conventions presented in this document:
https://leanprover-community.github.io/contribute/naming.html.
This document provides rules for file names and for names within files. It provides rules for `def`s,
`structure`s, `class`s, `theorem`s and `lemma`s. The rules cover capitalization, use of underscores,
representation of mathematical symbols as text, and the composition of verbs, nouns and adjectives or
adverbs into a name.
Rules for the naming of namespaces appear to be not so well developed. First, re-use an existing
Mathlib namespace whenever this is a reasonable choice.

Naming rules that bear on generality and on variants of a statement:

- Hypotheses appear in the name after `_of_`, in the order in which they occur: `A → B → C` is
  named `C_of_A_of_B` (naming guide).
- A lemma about a group with zero or a division ring, which would clash with the name of the group
  lemma, receives the suffix `₀`: `inv_eq_self` for groups, `inv_eq_self₀` for division rings
  (naming guide, *Groups vs groups with zero*).
- A statement about `fun x ↦ f x * g x`, rather than `f * g`, receives the prefix `fun_`, as in
  `Continuous.fun_mul` next to `Continuous.mul` (naming guide, *Unexpanded and expanded forms of
  functions*).
- Prop-valued classes that are nouns start with `Is` (`IsTopologicalRing`); `Has` is used when
  the predicate refers to data beyond its arguments (`HasCompactSupport`) (naming guide).
- A trailing prime marks a variant of an existing lemma. *Enforced*: the `docPrime` linter
  (`Mathlib/Tactic/Linter/DocPrime.lean`) warns on any primed declaration without a docstring. The
  docstring must explain how the variant differs from the unprimed lemma. *Observed*: the usual
  differences are an extra hypothesis (`sub_div` has none, `sub_div'` assumes `c ≠ 0`), a
  different syntactic form (`integral_neg` and `integral_neg'`), or a stronger or weaker hypothesis
  on an auxiliary function. A file with many primed lemmas explains the convention in its module
  docstring, as `Mathlib/Analysis/Calculus/MeanValue.lean` does.

Instruction: Adhere to the Library style guidelines presented in this document:
https://leanprover-community.github.io/contribute/style.html.
Note there Mathlib conventions for naming of code variables and for use of unicode. Note the
requirements and conventions for file headers, `module` structure, `import`s and module docstrings.
Note furthermore the layout and indentation rules for all code elements.
Try to follow the advice in the style guide about anonymous functions, conjunctions and disjunctions,
calculational proofs and use of @[simp]. Further points from that guide that affect the form of
statements:

- *Hypotheses left of colon*: arguments go before the colon rather than into `∀` or `→` when the
  proof would start by introducing them.
- *Normal forms*: one standard form of each notion is used in both statements and conclusions
  (for instance `s.Nonempty`). There is a deliberate asymmetry for bounds: hypotheses use the weak
  form (`x ≠ ⊥`), conclusions the strong form (`⊥ < x`). This is a local instance of "weak
  hypotheses, strong conclusions".
- *Transparency and API design*: definitions are semireducible by default. The need for `erw`, or
  for `rfl` after `simp` or `rw`, "is an indication that there is missing API". The remedy is to
  add lemmas, not to unfold definitions.
- *Deprecation*: public declarations are never simply deleted or renamed. The old name is kept as
  `@[deprecated (since := "YYYY-MM-DD")] alias old := new`, or as a deprecated declaration with a
  message, and may be removed after six months. *Enforced*: the Mathlib linter `deprecatedNoSince`
  (`Mathlib/Tactic/Linter/Lint.lean`) requires the `since` date. (About 4400 `@[deprecated`
  attributes in the checkout.)

Instruction: Follow the instructions and conventions in the document
https://leanprover-community.github.io/contribute/doc.html
This concerns documentation style. See there for conventions for the module header document, for
docstrings at each code element and for documentation of proof tactics. In particular:

- The module docstring has, in this order: a title; a summary; *Main definitions*; *Main
  statements*; *Notation*; *Implementation notes*, which is where design choices, typeclass
  choices and `simp` normal forms are explained; *References*; *Tags*.
- References go into `docs/references.bib` and are cited as `[Key]` in docstrings. Named theorems
  are set in bold, as in `**mean value theorem**`. Declarations can be linked to external databases
  with attributes such as `@[stacks 0123]` or `@[wikidata Q12345]`.
- *Observed*: when a statement exists in a discrete and a continuous version, the module docstring
  of each file names the other file. `Mathlib/MeasureTheory/Integral/MeanInequalities.lean` says
  "The versions for finite sums are in `Analysis.MeanInequalities`." Do the same when adding a
  parallel version.

## Mathematical statements

Mathlib expects theorems to be stated in maximum reasonable generality. More specialized versions of
any statement may be provided if they are of interest for applications.

### What the official documentation says

From *Mathlib's values* (`values.html`):

- *General definitions*: literature definitions are often tailored to a narrow scope. Mathlib
  prefers definitions that also work, for example, over the p-adic numbers for calculus, over any
  commutative ring in algebraic geometry, and for infinite-dimensional manifolds.
- *Weak hypotheses*: "When proving theorems in Mathlib we try hard to make assumptions as weak as
  possible." This benefits every later user of the theorem, since each use needs only the weaker
  assumptions.
- *Strong conclusions*: "we try to make theorem conclusions as strong as possible". For example, an
  existence result that can be upgraded to a set of positive measure is stated in that form.
- *Classical not constructive*: no effort is made to avoid excluded middle or to make definitions
  computable.

From the *Pull request review guide*: under *Is it general enough to support known future needs?*
the reviewer asks whether "there is a more general version of this result in the literature which
invokes pre-existing concepts in mathlib". If so, the PR should be generalized.

From the library note «the algebraic hierarchy»: a new typeclass is introduced only "when there is
'real mathematics' to be done with them, or when there is a meaningful gain in simplicity by
factoring out a common substructure". Generality therefore means using the existing classes, not
inventing new abstractions.

### What is enforced mechanically

- **No unused hypotheses.** The Batteries environment linter `unusedArguments`
  (`Batteries/Tactic/Lint/Misc.lean`) reports declarations with arguments that are not used.
  Exceptions must be marked `@[nolint unusedArguments]`, which happens about 160 times in the
  checkout, mostly for definitions whose extra argument is there to fix a type or an instance. For a
  theorem, an unused hypothesis almost always means the statement can be generalized by deleting
  it.
- **No unnecessary decidability assumptions.** The library note «decidable arguments»: if the
  statement does not need a `Decidable` instance, do not take one as an argument; use `classical`
  in the proof instead. The `unusedDecidableInType` linter
  (`Mathlib/Tactic/Linter/UnusedInstancesInType.lean`, currently off by default) detects violations.
- **Simp normal form.** The `simpNF` linter checks that the left-hand sides of `@[simp]` lemmas
  are in simp normal form. This indirectly forces statements into the normal forms described above.

### Implicit rules observed in the code

**G1. Generic scalar field.** *Observed.* Differential calculus is developed over an arbitrary
`[NontriviallyNormedField 𝕜]` (about 450 binders in the checkout). This covers ℝ, ℂ and the p-adic
fields at once. Statements that need a real structure but should hold for both ℝ and ℂ use
`[RCLike 𝕜]` (about 260 binders; the mean value inequalities in
`Analysis/Calculus/MeanValue.lean` are an example). Specialize to `ℝ` only when the order is used,
for example for Rolle's theorem or monotonicity. Do not write separate real and complex versions of
a statement that `RCLike` covers.

**G2. Definitions are made once, in general form. Special cases are abbreviations of the general
definition, not new definitions.** *Observed.* The one-variable derivative is defined through the
Fréchet derivative: `HasDerivAtFilter f f' L := HasFDerivAtFilter f (toSpanSingleton 𝕜 f') L`
(`Analysis/Calculus/Deriv/Basic.lean`). The interval integral `∫ x in a..b` is defined as a set
integral of the Bochner integral over `Ioc a b` (`MeasureTheory/Integral/IntervalIntegral/Basic.lean`).
The Bochner integral and the conditional expectation are both instances of one construction, the
extension `setToFun` of a dominated finitely-measure-additive set function
(`MeasureTheory/Integral/SetToL1.lean`). As a result, the dominated convergence theorems for both
are one-line applications of the `setToFun` versions.

**G3. Statements along a general filter.** *Observed.* Convergence statements are made along an
arbitrary filter, often a countably generated one. The sequence version is a separate lemma, which
either specializes the filter version or both come from a more general statement. Examples:
`tendsto_integral_filter_of_dominated_convergence` and `tendsto_integral_of_dominated_convergence`;
`HasFDerivAtFilter` underlying `HasFDerivAt`, `HasFDerivWithinAt` and `HasStrictFDerivAt`.

**G4. Localization variants form a fixed family.** *Observed.* A pointwise property comes in the
variants `…WithinAt`, `…At`, `…On` and global (for example `ContinuousWithinAt`, `ContinuousAt`,
`ContinuousOn`, `Continuous`; `HasFDerivWithinAt`, `HasFDerivAt`, …). The `WithinAt` form is the
most general, and the others are recovered from it with `univ` or a neighbourhood
(`hasFDerivWithinAt_univ`, `HasFDerivWithinAt.hasFDerivAt`). A new property of this kind is
expected to come with the whole family.

**G5. Junk values remove hypotheses.** *Observed; see Buzzard's FAQ above.* Operations are total:
`x / 0 = 0`; `deriv f x = 0` when `f` is not differentiable at `x`; the Bochner integral is `0` when
the function is not integrable, or when the target space is not complete (definition of `integral`
in `MeasureTheory/Integral/Bochner/Basic.lean`). Lemmas are therefore stated without hypotheses
whenever the junk value makes them true: `sub_div (a b c : K) : (a - b) / c = a / c - b / c`,
`integral_neg`, `integral_smul`. Only lemmas that genuinely need it take `c ≠ 0` or `Integrable f μ`
(`sub_div'`, `integral_add`). When adding a lemma, first check whether its hypotheses can be
dropped because of the junk-value convention.

**G6. Extended nonnegative values avoid integrability hypotheses.** *Observed.* Integral
inequalities are proved first for the lower Lebesgue integral of `ℝ≥0∞`-valued functions, where no
integrability or measurability-of-sum side conditions are needed. They are then transferred to real
or Bochner integrals. Examples: Tonelli before Fubini; Hölder and Minkowski in
`MeasureTheory/Integral/MeanInequalities.lean` (`ENNReal.lintegral_mul_le_Lp_mul_Lq` first).

**G7. Morphisms and substructures are handled by classes, not one type at a time.** *Official
(review guide, "Does it fit the design…") and observed.* Lemmas such as `map_add`, `map_mul` and
`map_zero` are stated once for every `FunLike` type with the relevant `…HomClass` instance. New
kinds of morphism should be bundled types with such instances, and new subobjects should use
`SetLike`. A lemma about ring homomorphisms written only for `RingHom` is too special if it holds
for any `RingHomClass`.

**G8. One proof for additive and multiplicative, and for order-dual, statements.** *Observed.*
Lemmas about monoids and groups are written multiplicatively and tagged `@[to_additive]`, which
generates the additive version automatically (about 16 300 occurrences). Order-theoretic lemmas
are increasingly tagged `@[to_dual]` (`Mathlib/Tactic/ToDual.lean`; about 5 600 occurrences), which
generates the dual statement for the reversed order. Writing the second version by hand is
duplication and is not accepted when the attribute applies.

**G9. The shape of "closure" lemmas.** *Library notes «continuity lemma statement» and «comp_of_eq
lemmas».* Closure properties are stated with arbitrary functions, as in
`Continuous.add (hf : Continuous f) (hg : Continuous g) : Continuous (f + g)`, rather than as
continuity of the operation `(+)`. The note says the same applies to `Measurable`,
`Differentiable`, `ContinuousOn`, and so on. Composition lemmas at a point take an explicit
equation, as in `ContinuousAt.comp_of_eq`, to help elaboration. Together with the `fun_` naming
rule this determines the expected statements of the basic API for any new regularity property.

**G10. Hypotheses as typeclass arguments.** *Observed.* Structural hypotheses that many lemmas
share are carried as instances rather than as explicit hypotheses: `[Nontrivial E]`,
`[CompleteSpace E]`, `[IsFiniteMeasure μ]`, `[SigmaFinite μ]`, `[Fact (1 ≤ p)]` for `Lp`. The
library note «fact non-instances» explains when `Fact` is used. Consistent with G5, `CompleteSpace`
is required only where a result actually needs it.

**G11. Necessity of hypotheses and missing theorems are recorded.** *Observed.* When a hypothesis
cannot be removed, a formal counterexample may be placed in `Counterexamples/`, for example
`NowhereDifferentiable.lean`, `SorgenfreyLine.lean`, `SeparableNotSecondCountable.lean`,
`Phillips.lean`. Statements whose proofs are wanted are placed in `Wanted/`, with `proof_wanted`
and no proof (34 in the checkout, including `Wanted/Analysis/`). *Enforced*: the
`directoryDependency` linter forbids importing `Wanted` from `Mathlib`, `Archive` or
`Counterexamples`.

## Mathematical proof

When a statement is included both in a general and in a more specific version and a proof of the
general version is available, then most often the proof of the specific version will just invoke the
more general statement.
A natural exception to that rule applies if the proof of the more general statement relies on the more
specific instance. In addition, sometimes Mathlib favours an explicit proof of a more specific case
in order to avoid the need to import much heavy machinery in a relatively lightweight module.

### What the official documentation says about duplication

The *Pull request review guide* says that mathlib aspires "for generality, and eschew[s] code
duplication". It warns that contributors often submit "a result that already exists, sometimes
verbatim, and other times in greater generality". The recommended check is to state the result in a
file with `import Mathlib` and try `exact?` or `apply?`. The same guide asks reviewers whether
declarations are in the appropriate files (use `#find_home`), whether new imports "import too
much", and whether a file should be split "to avoid import creep". When an existing result is too
special, the remedy is to generalize it, keeping the old name as a deprecated alias (see
*Deprecation* above), not to add a second theorem.

### What is enforced mechanically: the import hierarchy

The exception "to avoid heavy machinery in a lightweight module" is not a matter of taste. It is
enforced by three mechanisms, and these define where an elementary special case must be proved
directly.

1. **The `directoryDependency` linter** (`Mathlib/Tactic/Linter/DirectoryDependency.lean`,
   table `forbiddenImportDirs`, exceptions in `overrideAllowedImportDirs`). It forbids imports
   between top-level directories, and the check includes transitive imports. Pairs relevant to
   analysis include:
   - `Mathlib.Algebra` may not import `Mathlib.Analysis`. Since `Mathlib.MeasureTheory` builds on
     `Mathlib.Analysis`, algebra, including all of `Algebra/BigOperators`, cannot use measure
     theory or integrals.
   - `Mathlib.Data` may not import `Mathlib.Analysis`.
   - `Mathlib.Order` may not import `Mathlib.MeasureTheory` or `Mathlib.Probability`.
   - `Mathlib.LinearAlgebra` may not import `Mathlib.Topology`, `Mathlib.MeasureTheory` or
     `Mathlib.Probability`. There are listed exceptions such as `LinearAlgebra.Matrix` and
     `LinearAlgebra.QuadraticForm`, each justified by a comment.
   - Most directories may not import `Mathlib.Probability`, `Mathlib.Geometry.Manifold` or
     `Mathlib.AlgebraicGeometry`.
2. **`assert_not_exists`.** A file can declare that certain declarations must *not* be available at
   that point in the import graph. The build fails if a later change makes them available. About
   900 files use it. Analysis-relevant examples:
   - `Analysis/Convolution.lean`: `assert_not_exists ContDiffAt HasDerivAt`. Convolution must not
     depend on calculus.
   - `Analysis/SpecificLimits/Basic.lean`: `assert_not_exists Module.Basis NormedSpace`.
   - `Topology/Bornology/Absorbs.lean`: `assert_not_exists Real`.
   - `Analysis/Convex/Cone/Dual.lean`: `assert_not_exists InnerProductSpace`.
   - `Data/Nat/Init.lean`: `assert_not_exists Monoid`, in support of the library note
     «foundational algebra order theory».

   Before adding a proof to a file, read its `assert_not_exists` line. A proof that would need an
   excluded notion must go elsewhere, or must be done by more elementary means.
3. **The `minImports` and `upstreamableDecl` linters** (`Mathlib/Tactic/Linter/`). They report
   when a new declaration raises a file's minimal imports, and when a declaration could live in a
   file higher up in the hierarchy. Together with `#find_home`, they push each result to the lowest
   file where its hypotheses make sense. That file is also where the most general statement is
   expected to live.

### When duplication is accepted

*Observed and documented*: duplication is tolerated in the following situations, and normally only
in these.

- **Across a layering boundary.** A statement may be proved twice when the general proof lives in
  a directory that the special case may not import. Example: the finite-sum Cauchy–Schwarz
  inequality `Finset.sum_mul_sq_le_sq_mul_sq` (`Algebra/Order/BigOperators/Ring/Finset.lean`) is
  proved by algebra, for any strictly ordered commutative semiring. The inner-product-space
  inequality `norm_inner_le_norm` (`Analysis/InnerProductSpace/Basic.lean`) is proved separately.
  The elementary version is not a mere specialization: it is more general in another direction,
  since the scalars need not be real.
- **For simp performance or availability.** The library note «specialised high priority simp
  lemma» allows an early special lemma that a later, more general simp lemma subsumes. It is tagged
  `@[simp high]` if a large part of the library needs it without having the general lemma, or if
  the general lemma has expensive typeclass assumptions (about 140 `simp high` in the checkout).
- **Foundational developments of ℕ and ℤ.** Following the library note «foundational algebra order
  theory», the elementary facts about `ℕ` and `ℤ` are proved directly, without the algebraic
  typeclass hierarchy, because the hierarchy itself uses them. Other uses should go through the
  typeclasses.
- **Aliases are not duplicates.** `alias` (about 3 000 occurrences) creates a second name for the
  same proof. It is used for dot-notation access, for the directions of an `iff`, and for deprecated
  names. It is the accepted way to make a result findable under two names.

### Discrete and continuous versions

The earlier tentative rule "properties of finite sums must not be proven as counting-measure
specializations of properties of integrals" is confirmed, and it is enforced (see the import
hierarchy above): `Algebra/BigOperators` cannot import integration. The observed practice is as
follows.

- The finite-sum version is proved first, in `Algebra` or in a light `Analysis` file, by
  elementary means. The integral version is proved later, and its file imports the finite-sum file
  and cross-references it. Example: `Analysis/MeanInequalities.lean` (finite sums; imports
  `Algebra.BigOperators`, `Analysis.Convex.Jensen`) and
  `MeasureTheory/Integral/MeanInequalities.lean` (integrals; imports the former).
- Identities relating integrals and sums, such as integrals against counting measure or over a
  finite type, are proved in measure-theory files and point from integrals to sums, not the other
  way round.
- Infinite sums (`tsum`, `HasSum`) are defined topologically, for any topological additive monoid,
  independently of integration. The comparison with finite sums (`tsum_fintype`) is again a lemma
  that reduces the infinite case to the finite one.

### One variable and several variables

The earlier tentative rule that single-variable real analysis must not rely on multivariable real
analysis is **not correct as stated**. The code shows a more precise pattern.

- *Definitions are shared* (G2). The one-variable derivative is a special case of the Fréchet
  derivative over an arbitrary nontrivially normed field, so one-variable calculus depends on the
  definitions and basic API of multivariable calculus. The same holds for integrals.
- *Deep theorems are proved in one variable first and lifted by restricting to lines or segments.*
  In `Analysis/Calculus/MeanValue.lean` the "one-dimensional fencing inequalities" are proved
  first. The mean value inequality on a convex set in a normed space is deduced from them along
  segments. Rolle's theorem and the one-variable mean value theorem are proved directly on ℝ.
  Rademacher's theorem in finite dimension uses almost-everywhere differentiability of
  one-variable BV functions along lines.
- In complex analysis the direction is the same, and here the earlier rule is correct: statements
  for maps `E → F` between complex normed spaces are deduced from the one-variable case by
  restriction to complex lines. Liouville's theorem `Differentiable.apply_eq_apply_of_bounded`
  (`Analysis/Complex/Liouville.lean`) and the maximum modulus principle `norm_max_aux₁`–`₃` →
  `norm_eqOn_closedBall_of_isMaxOn` (`Analysis/Complex/AbsMax.lean`) are examples. The Cauchy
  integral formula and analyticity of complex-differentiable maps exist only for functions of one
  complex variable.

A more accurate instruction is therefore:

Instruction: Define a notion once, in the general setting (normed spaces over a general field,
filters, `WithinAt` forms). Obtain the one-variable notion as an abbreviation or specialization of
it. Prove the substantive one-variable theorem directly, using only one-variable tools. Deduce the
multivariable or Banach-space theorem from it by restriction to lines or segments, unless a
genuinely multivariable proof is shorter and needs no heavier imports.

### Further rules still to be investigated

- How Mathlib decides between a statement for `Finset.sum` and one for `∑ᶠ` (`finsum`) or `tsum`,
  when all three make sense.
- When a result about measures is stated for s-finite, σ-finite, or finite measures. The code seems
  to state results for s-finite measures when possible (product measures, Tonelli), but this has
  not been checked systematically.
- Placement conventions within `Mathlib/Analysis/` for results that fit several subdirectories.
  These are not covered by `directoryDependency`.
- Whether `to_dual` is now required for new order lemmas, or only encouraged. Its module
  docstring lists limitations, for example when combined with `to_additive`.
