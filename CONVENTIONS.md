# Coding Conventions and Mathematical Practices in Mathlib

This file summarizes style conventions and mathematical practices in Lean Mathlib. It supports
instructions for contributors and LLMs that may be put into an `AGENTS.md` file. Coding conventions
are documented in the community guides. Mathematical practices also require studying definitions,
theorem statements and proof dependencies in the source.

The two main concerns are the **generality** of mathematical statements and the **duplication** of
statements and proofs. The following labels distinguish the kinds of guidance:

- *Documented*: stated in official community documentation or a Mathlib library note.
- *Mechanical check*: a tool checks a specific condition; its activation context and limitations
  matter. Passing the check does not establish mathematical generality or good API design.
- *Observed*: a practice illustrated by source examples, without claiming a universal policy.
- *Project instruction*: guidance proposed here for adoption in a project's `AGENTS.md`.

Source observations and tool settings refer to the Mathlib checkout at commit
[`065356127b1d`](https://github.com/leanprover-community/mathlib4/tree/065356127b1dc0016f66b7283ce0ce2c4055aa55)
(2026-09-16). The community pages were reviewed on 2026-09-30 and can evolve independently of that
checkout. Source paths below are relative to the Mathlib repository unless prefixed by `Batteries/`;
paths beginning `Analysis/`, `Algebra/`, `Data/`, `MeasureTheory/` or `Topology/` abbreviate paths
under `Mathlib/`.
Examples establish the stated behavior at that revision; they do not establish a rule for every
part of the library.

## Sources

Official community documentation, all under https://leanprover-community.github.io/contribute/:

- [Contributing to Mathlib](https://leanprover-community.github.io/contribute/index.html):
  the entry point. It says that "mathlib intentionally has very high standards (on
  generality, integration with the remaining library and maintainability, including code style)".
- [Mathlib's values](https://leanprover-community.github.io/contribute/values.html). This page states the generality
  principles explicitly (sections *General definitions*, *Weak hypotheses*, *Strong conclusions*,
  *Classical not constructive*, *Downstream projects*). See the section on mathematical statements
  below.
- [Pull request review guide](https://leanprover-community.github.io/contribute/pr-review.html).
  This is the main official source on duplication
  and placement (sections *Location*, *Do the results already exist?*, *Are new imports
  introduced?*, *Library integration*, *Is it general enough to support known future needs?*).
- [Library style](https://leanprover-community.github.io/contribute/style.html),
  [naming](https://leanprover-community.github.io/contribute/naming.html),
  [documentation](https://leanprover-community.github.io/contribute/doc.html),
  [commit messages](https://leanprover-community.github.io/contribute/commit.html), and
  [how to contribute](https://leanprover-community.github.io/contribute/how-to-contribute.html).

Documentation inside the Mathlib source tree:

- **Library notes.** Design decisions are recorded as `library_note «...»` declarations. They
  can be found with `rg -n 'library_note «' Mathlib`. The ones most relevant here are «the
  algebraic hierarchy» (`Mathlib/Algebra/HierarchyDesign.lean`), «forgetful inheritance»
  (`Mathlib/Algebra/Group/Monoid.lean`), «continuity lemma statement» and «comp_of_eq lemmas»
  (`Mathlib/Topology/Continuous.lean`), «decidable arguments» (`Mathlib/Basic/Logic/Basic.lean`),
  «specialised high priority simp lemma» (`Mathlib/Data/NNRat/Defs.lean`) and «foundational
  algebra order theory» (`Mathlib/Data/Nat/Init.lean`).
- **Linters** in `Mathlib/Tactic/Linter/` and in Batteries (`Batteries/Tactic/Lint/`). Read their
  docstrings and implementations together with `Mathlib/Init.lean` and `lakefile.lean` to determine
  what they check and when they run. A registered option's default alone is not sufficient: a
  linter set can enable it.
- The `Wanted/` directory (statements with `proof_wanted`, no proof) and `Counterexamples/`
  (formalized counterexamples showing that hypotheses cannot be dropped).

Background: *The Lean mathematical library* (mathlib community, CPP 2020,
https://arxiv.org/abs/1910.09336), cited by the «the algebraic hierarchy» library note. On junk
values, which let Mathlib state many lemmas without hypotheses: K. Buzzard, *Division by zero in
type theory: a FAQ* (https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/).

## Lean style conventions

Project instruction: Use the broad Best Practices guidelines in this document as supplementary advice:
https://lean4.dev/language/best-practices.
(Note: this page is a third-party summary of general Lean 4 idiom, not a Mathlib document. Where
it differs from the Mathlib pages below, the Mathlib pages take precedence.)

Project instruction: Adhere to the naming conventions presented in this document:
https://leanprover-community.github.io/contribute/naming.html.
This document provides rules for file names and for names within files. It provides rules for `def`s,
`structure`s, `class`s, `theorem`s and `lemma`s. The rules cover capitalization, use of underscores,
representation of mathematical symbols as text, and the composition of verbs, nouns and adjectives or
adverbs into a name.

Project instruction: Reuse an existing Mathlib namespace when appropriate, and follow the placement
of neighboring declarations. Consider dot-notation access when choosing a namespace.

Naming rules that bear on generality and on variants of a statement:

- When hypotheses are included in a name, they appear after `_of_`, in their argument order:
  `A → B → C` can be named `C_of_A_of_B`. Routine hypotheses are often omitted (naming guide).
- A lemma about a group with zero or a division ring, which would clash with the name of the group
  lemma, receives the suffix `₀`: `inv_eq_self` for groups, `inv_eq_self₀` for division rings
  (naming guide, *Groups vs groups with zero*).
- When expanded and unexpanded function forms need distinguishing, use `fun_mul` for
  `fun x ↦ f x * g x` and `mul` for `f * g`, as in `Continuous.fun_mul` and `Continuous.mul`.
  The `fun_` prefix is not required if only the expanded form is provided (naming guide,
  *Unexpanded and expanded forms of functions*).
- Prop-valued classes that are nouns start with `Is` (`IsTopologicalRing`); adjective names need
  not. `Has` may be used when the predicate refers to data beyond its explicit arguments and this
  sounds natural (`HasCompactSupport`) (naming guide).
- *Observed*: a trailing prime often marks a variant. For example, `sub_div` states
  `(a - b) / c = a / c - b / c`, whereas `sub_div'` states
  `b - a / c = (b * c - a) / c` under `c ≠ 0` (`Mathlib/Algebra/Field/Basic.lean`). These are
  different identities, not the same identity with an extra hypothesis. Other variants differ in
  syntactic form or assumptions. `Mathlib/Analysis/Calculus/MeanValue.lean` explains its prime
  convention in its module docstring.
  *Project instruction*: explain the prime in a docstring, either by comparison with a related
  declaration or by explaining why a better name is unavailable. The optional `docPrime` check
  detects missing docstrings, not the adequacy of the explanation; see the activation table below.

Project instruction: Adhere to the Library style guidelines presented in this document:
https://leanprover-community.github.io/contribute/style.html.
Note there Mathlib conventions for naming of code variables and for use of unicode. Note the
requirements and conventions for file headers, `module` structure, `import`s and module docstrings.
Note furthermore the layout and indentation rules for all code elements.
Try to follow the advice in the style guide about anonymous functions, conjunctions and disjunctions,
calculational proofs and use of `@[simp]`. Further points from that guide that affect the form of
statements:

- *Hypotheses left of colon*: arguments go before the colon rather than into `∀` or `→` when the
  proof would start by introducing them.
- *Normal forms*: one standard form of each notion is used in both statements and conclusions
  (for instance `s.Nonempty`). There is a deliberate asymmetry for bounds: hypotheses use the
  form convenient to supply (`x ≠ ⊥`), conclusions the form convenient to use (`⊥ < x`). These
  conditions are equivalent in the relevant ordered setting; the distinction is API convenience.
- *Transparency and API design*: definitions are semireducible by default. The need for `erw`, or
  for `rfl` after `simp` or `rw`, "is an indication that there is missing API". The remedy is to
  consider suitable API lemmas. Unfolding a definition is still appropriate when developing its API.
- *Deprecation*: removed or renamed public theorems and definitions normally retain an old-name declaration as
  `@[deprecated (since := "YYYY-MM-DD")] alias old := new`, or as a deprecated declaration with a
  message, and may be removed after six months. The style guide gives exceptions, including named
  instances, certain automatically generated declarations, and simultaneous renamings that reuse a
  name. *Mechanical check*: the environment linter `deprecatedNoSince`
  (`Mathlib/Tactic/Linter/Lint.lean`) checks that a `since` date is present.

Project instruction: Follow the instructions and conventions in the document
https://leanprover-community.github.io/contribute/doc.html
This concerns documentation style. See there for conventions for the module header document, for
docstrings at each code element and for documentation of proof tactics. In particular:

- The module docstring begins with a title and summary. Subsequent sections, when present, follow
  this order: *Main definitions*; *Main statements*; *Notation*; *Implementation notes*;
  *References*; *Tags*. Main definitions and statements may instead be covered in the summary;
  omit Notation if the file introduces none. Implementation notes explain design choices,
  typeclass choices and `simp` normal forms.
- References go into `docs/references.bib` and are cited as `[Key]` in docstrings. Named theorems
  are set in bold, as in `**mean value theorem**`. Declarations can be linked to external databases
  with attributes such as `@[stacks 0123]` or `@[wikidata Q12345]`.
- *Observed*: `Mathlib/MeasureTheory/Integral/MeanInequalities.lean` cross-references
  `Analysis.MeanInequalities` for finite-sum versions. *Project instruction*: add useful
  cross-references when introducing parallel versions; a documentation reference does not require
  an import.

### Mechanical checks and their activation

The settings below refer to the cited checkout. Syntax linters run during elaboration when imported
and enabled. Environment linters inspect declarations through `#lint` or a configured lint driver;
they are not all part of an ordinary `lake build`. Mathlib configures the Batteries environment
lint driver in `lakefile.lean`. Downstream projects must check their own imports and configuration.

| Check | Activation and scope |
| --- | --- |
| `directoryDependency` | Enabled syntax linter; checks configured import restrictions and exceptions. |
| `unusedDecidableInType` | Its individual option defaults to false, but Mathlib enables it through `linter.mathlibStandardSet`; checks theorem statements. |
| `docPrime` | Disabled by default and excluded from Mathlib's standard set. When enabled, checks missing docstrings on names ending in a prime, with exemptions such as private declarations and listed exceptions. |
| `minImports`, `upstreamableDecl` | Disabled by default; optional diagnostics for dependency analysis and file splitting. |
| `unusedArguments`, `simpNF`, `deprecatedNoSince` | Environment linters; run through the relevant lint workflow or explicitly with `#lint`. |
| `assert_not_exists` | An explicit assertion in a file; fails during elaboration if a listed declaration is available. |

The activation evidence is in
[`Mathlib/Init.lean`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Init.lean)
and
[`lakefile.lean`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/lakefile.lean).
Neither successful compilation nor a clean lint run proves that hypotheses are minimal or that a
theorem is absent elsewhere in the library.

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
- *Classical not constructive*: avoiding excluded middle and making definitions computable are
  not general requirements. Some parts of Mathlib are constructive, but new material need not be.

From the *Pull request review guide*: under *Is it general enough to support known future needs?*
the reviewer asks whether "there is a more general version of this result in the literature which
invokes pre-existing concepts in mathlib". This is a reason to consider generalization, not an
unconditional requirement independent of the contribution's scope and library design.

From the library note «the algebraic hierarchy»: a new typeclass is introduced only "when there is
'real mathematics' to be done with them, or when there is a meaningful gain in simplicity by
factoring out a common substructure". Reuse existing abstractions where appropriate; introduce new
ones when substantive mathematics or a meaningful simplification justifies them.

### What mechanical checks establish

- **Unused arguments.** The Batteries environment linter `unusedArguments`
  (`Batteries/Tactic/Lint/Misc.lean`) looks for arguments absent from the declaration's value,
  result type and argument types. It has exemptions, including certain underscore-prefixed
  arguments and declarations containing `sorry`; `@[nolint unusedArguments]` can suppress the
  check for a declaration. A reported hypothesis is a candidate for removal. A hypothesis used by
  the current proof may still be mathematically unnecessary, which this check cannot discover.
- **No unnecessary decidability assumptions.** The library note «decidable arguments»: if the
  statement does not need a `Decidable` instance, do not take one as an argument; use `classical`
  in the proof instead. The `unusedDecidableInType` linter
  (`Mathlib/Tactic/Linter/UnusedInstancesInType.lean`) checks theorem statements for instances
  unused in the remainder of the type. Mathlib enables it through its standard linter set.
- **Simp normal form.** The `simpNF` linter checks that the left-hand sides of `@[simp]` lemmas
  are in simp normal form relative to the simp set. It helps detect ineffective simp lemmas;
  it does not enforce a normal form for every mathematical statement.

### Practices illustrated by the code

**G1. Generic scalar field.** *Observed.* Differential calculus is developed over an arbitrary
`[NontriviallyNormedField 𝕜]` in its normed-space API. This covers ℝ, ℂ and the p-adic
fields at once. Statements that need a real structure but should hold for both ℝ and ℂ use
`[RCLike 𝕜]`; the mean value inequalities in `Mathlib/Analysis/Calculus/MeanValue.lean` give
examples. Specializing to `ℝ` can be appropriate because of order, topology or other real-specific
structure. *Project instruction*: use the general scalar assumptions supported by the result and
its surrounding API. Prefer a shared `RCLike` theorem when it naturally covers both real and complex
applications; useful specialized wrappers may still be provided.

**G2. Special cases reuse general constructions.** *Observed.* The one-variable derivative is defined
through the Fréchet derivative: `HasDerivAtFilter f f' L := HasFDerivAtFilter f (toSpanSingleton 𝕜 f') L`
(`Mathlib/Analysis/Calculus/Deriv/Basic.lean`). This is a `def`, not a Lean `abbrev`.
The interval integral is the oriented difference
`(∫ x in Ioc a b, f x ∂μ) - ∫ x in Ioc b a, f x ∂μ`; when `a ≤ b` it reduces to the first
term. See
[`intervalIntegral`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean#L650-L660).
The Bochner integral and the `L¹`-valued conditional expectation also share the `setToFun`
construction (`Mathlib/MeasureTheory/Integral/SetToL1.lean`), allowing reuse of linearity and
convergence results. *Project instruction*: define special cases through general constructions and
reuse their API. Choose `def` or `abbrev` according to the intended transparency and interface.

**G3. Statements along a general filter.** *Observed.* Convergence statements use general filters
under the assumptions needed by the theorem, such as countable generation. A sequence version may
specialize the filter version, or both may follow from a more general statement. Examples:
`tendsto_integral_filter_of_dominated_convergence` and `tendsto_integral_of_dominated_convergence`;
`HasFDerivAtFilter` underlying `HasFDerivAt`, `HasFDerivWithinAt` and `HasStrictFDerivAt`.

**G4. Localization variants form useful families.** *Observed.* Many regularity properties have
variants `…WithinAt`, `…At`, `…On` and global (for example `ContinuousWithinAt`, `ContinuousAt`,
`ContinuousOn`, `Continuous`; `DifferentiableWithinAt`, `DifferentiableAt`,
`DifferentiableOn`, `Differentiable`). `WithinAt` handles set restrictions; the unrestricted
pointwise form is recovered with `univ`, or from a within-set statement when the set is a
neighborhood. `On` and global forms quantify over points. A filter formulation, when available,
can be more general still: `HasFDerivAtFilter` underlies ordinary, within-set and strict
differentiability. *Project instruction*: provide the variants and conversion lemmas appropriate to
the new property's uses; do not mechanically invent every suffix for every notion.

**G5. Junk values remove hypotheses.** *Observed; see Buzzard's FAQ above.* Operations are total:
in fields and division rings, `x / 0 = 0`; `deriv f x = 0` when `f` is not differentiable at `x`;
the Bochner integral is `0` when the function is not integrable, or when the target space is not
complete (definition of `integral`
in `MeasureTheory/Integral/Bochner/Basic.lean`). Lemmas are therefore stated without hypotheses
whenever the junk value makes them true: `sub_div (a b c : K) : (a - b) / c = a / c - b / c`,
`integral_neg`, `integral_smul`. Only lemmas that genuinely need it take `c ≠ 0` or `Integrable f μ`
(`sub_div'`, `integral_add`). *Project instruction*: when adding a lemma, check whether hypotheses can be
dropped because of the junk-value convention.

**G6. Extended nonnegative values avoid finiteness assumptions.** *Observed.* Many integral
inequalities are first proved for the lower Lebesgue integral of `ℝ≥0∞`-valued functions, allowing
infinite integrals, and then transferred to real or Bochner integrals. Examples include Tonelli
before Fubini, and Hölder and Minkowski in `Mathlib/MeasureTheory/Integral/MeanInequalities.lean`.
This does not remove all measurability or measure-class assumptions. For instance,
`lintegral_add_left'` requires `AEMeasurable f μ`; without that assumption the unconditional
`le_lintegral_add` supplies only an inequality. See
[`Lebesgue/Add.lean`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean#L273-L333).
*Project instruction*: retain the measurability and measure-class assumptions required by each
result, while checking whether finiteness can be avoided in an extended-valued formulation.

**G7. Shared morphism and substructure APIs.** *Documented
(review guide, "Does it fit the design…") and observed.* Lemmas such as `map_add`, `map_mul` and
`map_zero` are stated once for every `FunLike` type with the relevant `…HomClass` instance. New
kinds of morphism generally use bundled types and suitable morphism classes; subobjects generally
use `SetLike`. *Project instruction*: prefer a `RingHomClass` lemma over a `RingHom`-specific lemma
when the result uses only that shared interface. Follow the established design of the relevant
area; the review guide presents these as design guidance, not universal requirements.

**G8. One proof for additive and multiplicative, and for order-dual, statements.** *Observed.*
Many lemmas about monoids and groups use `@[to_additive]` to generate their additive versions.
Order-theoretic lemmas use `@[to_dual]` to generate statements for the reversed order; examples are
in `Mathlib/Tactic/ToDual.lean`, and the implementation and documentation are in
`Mathlib/Tactic/Translate/ToDual.lean`. *Project instruction*: prefer these attributes when they
produce the intended statements and API. Check their limitations and existing translations before
writing a second proof. Their availability does not establish a blanket prohibition on manual
variants.

**G9. The shape of "closure" lemmas.** *Documented: library notes «continuity lemma statement» and
«comp_of_eq lemmas».* Closure properties are stated with arbitrary functions, as in
`Continuous.add (hf : Continuous f) (hg : Continuous g) : Continuous (f + g)`, rather than as
continuity of the operation `(+)`. The note says the same applies to `Measurable`,
`Differentiable`, `ContinuousOn`, and so on. Composition lemmas at a point can have a `comp_of_eq`
variant with an explicit equation, as in `ContinuousAt.comp_of_eq`, to help elaboration alongside
the ordinary `comp` lemma. Together with the `fun_` naming rule, these are useful patterns when
designing an API for a new regularity property.

**G10. Hypotheses as typeclass arguments.** *Observed.* Structural hypotheses that many lemmas
share are carried as instances rather than as explicit hypotheses: `[Nontrivial E]`,
`[CompleteSpace E]`, `[IsFiniteMeasure μ]`, `[SigmaFinite μ]`, `[Fact (1 ≤ p)]` for `Lp`. The
library note «fact non-instances» warns against global `Fact` instances: typeclass search is not
a general proof-search mechanism. *Project instruction*: follow existing structural instance APIs,
and use explicit hypotheses for ordinary theorem assumptions unless there is a reason otherwise.
Consistent with G5, require `CompleteSpace` only where the result needs it.

**G11. Necessity of hypotheses and missing theorems are recorded.** *Observed.* When a hypothesis
cannot be removed, a formal counterexample may be placed in `Counterexamples/`, for example
`NowhereDifferentiable.lean`, `SorgenfreyLine.lean`, `SeparableNotSecondCountable.lean`,
`Phillips.lean`. Statements whose proofs are wanted are placed in `Wanted/`, with `proof_wanted`
and no proof (for example in `Wanted/Analysis/`). *Mechanical check*: the
`directoryDependency` linter forbids importing `Wanted` from `Mathlib`, `Archive` or
`Counterexamples`.

### Analysis-specific interfaces

The following project instructions are motivated by the existing calculus and measure-theory APIs.

- **Derivative relations and derivative values.** Prefer `HasDerivAt f f' x` or
  `HasFDerivAt f f' x` when asserting that a particular derivative exists. An equation
  `deriv f x = f'` alone need not establish differentiability because of the default value in G5.
  Derive value formulas with `HasDerivAt.deriv` or the corresponding Fréchet-derivative lemma;
  retain useful `deriv`/`fderiv` formulas for applications.
- **Uniqueness within sets.** Distinguish the existence of a derivative within a set from its
  unique value. For example, `HasDerivWithinAt.derivWithin` additionally requires
  `UniqueDiffWithinAt 𝕜 s x`. On a sufficiently small or degenerate set, derivative relations
  need not determine a unique derivative. Check uniqueness assumptions before rewriting a
  `derivWithin` or `fderivWithin` expression. These interfaces are in
  [`Deriv/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/Deriv/Basic.lean#L433-L441).
- **Pointwise and almost-everywhere statements.** Use `f =ᵐ[μ] g` or `∀ᵐ x ∂μ, P x` when the
  result only depends on behavior outside a null set. For example, `integral_congr_ae` accepts
  almost-everywhere equality. Keep pointwise assumptions where the conclusion concerns specified
  point values or continuity; an almost-everywhere statement alone does not supply them.
- **Measurability interfaces.** `AEMeasurable f μ` means that `f` agrees almost everywhere with
  a measurable function; it is weaker than `Measurable f`. For Bochner integration, distinguish
  `StronglyMeasurable` and `AEStronglyMeasurable` from these predicates. `Integrable f μ` includes
  almost-everywhere strong measurability as well as a finiteness condition. Use the weakest
  interface supported by the theorem, and check the topological assumptions before converting
  ordinary measurability to strong measurability. Sources:
  `Mathlib/MeasureTheory/Measure/AEMeasurable.lean`,
  `Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`, and
  `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`.

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
special, consider generalizing it under its existing name. If the name changes, apply the deprecation
guidance above; a deprecated alias is not automatically needed for a generalization. Specialized
wrappers may remain useful for elaboration, automation or discoverability.

### Searching before adding a result

Project instruction: before introducing a definition or proving a theorem, check for existing
constructions and results in the following order.

1. Search declaration names and mathematical terms with `rg`, including likely namespaces and
   more general concepts. Read nearby statements and module docstrings. Check equivalent forms,
   scalar-general versions, within-set variants and filter formulations.
2. State the intended result in a temporary scratch file with `import Mathlib`, and try `exact?`
   or `apply?` where the project's build workflow permits. Failure is not evidence of absence:
   search can miss equivalent formulations, required rewrites and useful intermediate lemmas.
3. Inspect a candidate theorem's full assumptions and conclusion, then determine whether a direct
   application, specialization or short wrapper supplies the desired API. If not, consider
   generalizing the existing result or placing a new result nearby.
4. Select imports and a destination compatible with the surrounding library. Read the file's
   header, library notes and `assert_not_exists` declarations. Use `#find_home` or optional import
   diagnostics as aids, and check mathematical discoverability as well as dependencies.
5. Replace exploratory broad imports with the imports appropriate to the final file, and run the
   project's build and applicable lint checks. Use the project's prescribed scratch-file and build
   procedures throughout.

### Import restrictions and placement diagnostics

Some import boundaries are mechanically checked; other placement decisions rely on review and
optional diagnostics. The mechanisms below constrain dependencies or help choose a destination.
They do not uniquely determine where every theorem must live or how it must be proved.

1. **The `directoryDependency` linter** (`Mathlib/Tactic/Linter/DirectoryDependency.lean`,
   tables `allowedImportDirs`, `forbiddenImportDirs`, and `overrideAllowedImportDirs`). It checks
   restrictions between module prefixes, including transitive imports. Pairs relevant to
   analysis include:
   - `Mathlib.Algebra` may not import `Mathlib.Analysis`. Thus `Algebra/BigOperators` cannot
     import Bochner integration, which depends on analysis. Do not infer a ban on every
     measure-theory file merely from its directory name; inspect its actual dependencies and the
     configured rules.
   - `Mathlib.Data` may not import `Mathlib.Analysis`.
   - `Mathlib.Order` may not import `Mathlib.MeasureTheory` or `Mathlib.Probability`.
   - `Mathlib.LinearAlgebra` may not import `Mathlib.Topology`, `Mathlib.MeasureTheory` or
     `Mathlib.Probability`. There are listed exceptions such as `LinearAlgebra.Matrix` and
     `LinearAlgebra.QuadraticForm`, each justified by a comment.
   - Most directories may not import `Mathlib.Probability`, `Mathlib.Geometry.Manifold` or
     `Mathlib.AlgebraicGeometry`.
2. **`assert_not_exists`.** A file can declare that certain declarations must *not* be available at
   that point in the import graph. The build fails if a later change makes them available.
   Analysis-relevant examples:
   - `Analysis/Convolution.lean`: `assert_not_exists ContDiffAt HasDerivAt`. This protects the
     file from dependencies exposing these calculus declarations.
   - `Analysis/SpecificLimits/Basic.lean`: `assert_not_exists Module.Basis NormedSpace`.
   - `Topology/Bornology/Absorbs.lean`: `assert_not_exists Real`.
   - `Analysis/Convex/Cone/Dual.lean`: `assert_not_exists InnerProductSpace`.
   - `Data/Nat/Init.lean`: `assert_not_exists Monoid`, in support of the library note
     «foundational algebra order theory».

   Before adding a proof to a file, read its `assert_not_exists` line. A proof that would need an
   excluded notion must go elsewhere, or must be done by more elementary means.
3. **Optional `minImports` and `upstreamableDecl` diagnostics** (`Mathlib/Tactic/Linter/`). They report
   when a new declaration raises a file's minimal imports, and when a declaration could live in a
   file higher up in the hierarchy. Both are disabled by default. Together with `#find_home`, they
   help identify possible placements and file splits. Dependencies of the actual proof, thematic
   organization and a useful API also matter; the weakest hypotheses alone do not determine a file.

### When duplication is accepted

*Observed and documented*: the following situations explain why related statements or separate
proofs can be useful. This is not an exhaustive list of permitted exceptions.

- **Across a layering boundary.** A statement may be proved twice when the general proof lives in
  a directory that the special case may not import. Example: the finite-sum Cauchy–Schwarz
  inequality `Finset.sum_mul_sq_le_sq_mul_sq` (`Algebra/Order/BigOperators/Ring/Finset.lean`) is
  proved algebraically under `[CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]`
  and `[ExistsAddOfLE R]`. The inner-product-space inequality `norm_inner_le_norm`
  (`Analysis/InnerProductSpace/Basic.lean`) is proved separately.
  The elementary version is not a mere specialization: it is more general in another direction,
  since the scalars need not be real.
- **For simp performance or availability.** The library note «specialised high priority simp
  lemma» allows an early special lemma that a later, more general simp lemma subsumes. It is tagged
  `@[simp high]` if a large part of the library needs it without having the general lemma, or if
  the general lemma has expensive typeclass assumptions.
- **Foundational developments of ℕ and ℤ.** Following the library note «foundational algebra order
  theory», the elementary facts about `ℕ` and `ℤ` are proved directly, without the algebraic
  typeclass hierarchy, because the hierarchy itself uses them. Other uses should go through the
  typeclasses.
- **Convenient statement variants.** Expanded function forms, reordered arguments and specialized
  assumptions can make a result usable by elaboration or automation. Such wrappers should normally
  reuse the underlying proof; mathematical equivalence does not make their API roles identical.
- **Aliases reuse existing results.** `alias` supplies another name for a declaration or extracts
  directions of an `iff`. It is used for dot-notation access and deprecated names. Use it when an
  additional name suffices; a wrapper lemma may be appropriate when the statement must change.

### Discrete and continuous versions

The import hierarchy prevents `Algebra/BigOperators` from importing Bochner integration, so finite-sum
results in that directory cannot be proved as counting-measure specializations of integral
results. The observed practice is as follows.

- In the mean-inequality development, finite-sum results are upstream of integral results, whose
  file imports and cross-references them. Example: `Analysis/MeanInequalities.lean` (finite sums;
  imports big-operator modules and `Analysis.Convex.Jensen`) and
  `MeasureTheory/Integral/MeanInequalities.lean` (integrals; imports the former).
- Identities relating integrals and sums, such as integrals against counting measure or over a
  finite type, live in measure-theory files. They allow conversion between the two expressions.
  A finite-sum result in a file that already imports integration may legitimately use integral
  results; the import restriction is not a blanket prohibition on this proof strategy.
- Infinite sums (`tsum`, `HasSum`) are defined topologically for additive commutative monoids,
  independently of integration. The comparison with finite sums (`tsum_fintype`) is again a lemma
  that reduces the infinite case to the finite one.

### One variable and several variables

The relationship between single-variable and multivariable analysis depends on the construction
and theorem. The following examples illustrate useful patterns without imposing a proof direction.

- *Definitions are shared* (G2). The one-variable derivative is a special case of the Fréchet
  derivative over an arbitrary nontrivially normed field, so one-variable calculus depends on the
  definitions and basic API of general differential calculus. Interval integrals similarly use
  general Bochner integration, whose domain is a measure space rather than a specified dimension.
- *Some substantive theorems are lifted from one variable by restricting to lines or segments.*
  In `Analysis/Calculus/MeanValue.lean` the "one-dimensional fencing inequalities" are proved
  first. The mean value inequality on a convex set in a normed space is deduced from them along
  segments. Rolle's theorem and the one-variable mean value theorem are proved directly on ℝ.
  Rademacher's theorem in finite dimension uses almost-everywhere differentiability of
  one-variable BV functions along lines.
- In complex analysis, some results for maps `E → F` between complex normed spaces follow by
  restriction to complex lines. Liouville's theorem `Differentiable.apply_eq_apply_of_bounded`
  (`Analysis/Complex/Liouville.lean`) and the maximum modulus principle `norm_max_aux₁`–`₃` →
  `norm_eqOn_closedBall_of_isMaxOn` (`Analysis/Complex/AbsMax.lean`) are examples. The Cauchy
  integral formula and the implications `DifferentiableOn.analyticAt` and
  `Differentiable.analyticAt` in `Mathlib/Analysis/Complex/CauchyIntegral.lean` concern maps
  `ℂ → E`, with completeness assumptions on the target where required. This describes those APIs
  in the cited checkout, rather than a mathematical limitation to one complex variable.

These observations suggest the following instruction:

Project instruction: reuse general definitions and available theorems, specializing them for
one-variable applications where appropriate. When developing a new theorem, consider restriction
to lines or segments if it reduces the argument to an available one-variable result. Also consider
a direct general proof. Choose according to the mathematics, the surrounding API, readability and
import constraints; there is no universal requirement to prove the one-variable case first.

### Further rules still to be investigated

- How Mathlib decides between a statement for `Finset.sum` and one for `∑ᶠ` (`finsum`) or `tsum`,
  when all three make sense.
- When a result about measures is stated for s-finite, σ-finite, or finite measures. The code seems
  to state results for s-finite measures when possible (product measures, Tonelli), but this has
  not been checked systematically.
- Placement conventions within `Mathlib/Analysis/` for results that fit several subdirectories.
  These are not covered by `directoryDependency`.
- Which combinations of `to_dual` and `to_additive` are supported for the intended new APIs.
  Check the translation documentation and relevant examples at the project's pinned revision.
