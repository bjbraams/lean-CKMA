# Lean structural assessment of CKMA

The library has 240 Lean modules and 3196 inventoried public declarations. Every module has a mathematical
doc header; every inventoried declaration and structure field has a registered formal docstring. All mathematical declarations live in the
`CKMA` namespace. Concrete public definitions are exposed to importing modules.

## Mathematical interfaces

- The Brownian law is a measure on continuous real paths with the Borel sigma-algebra.
  Pre-Brownian processes and their continuous modifications remain separate interfaces.
- Normal summability requires bounded compact norm images. Density zero records
  eventually finite ball masses. Inverse poles have positive order, nonzero analytic
  regularization and punctured invertibility; finite-order regularizability is a
  distinct weaker predicate.
- Caller-supplied redundant symmetry, properness, nonemptiness, continuity, scalar
  commutation and completeness hypotheses are absent from the reviewed interfaces.
  Accretive resolvent contraction is proved without completeness; generation retains it.
- Operator, Hermitian-matrix and trace APIs are uniform over real or complex scalars
  where appropriate. Metric stability and bounded forward orbits have independent
  ambient interfaces. Self-similar laws allow zero weights; representative-only
  Shannon statements allow arbitrary L² data before band restriction.
- Shared Hilbert carriers, flow generators and capacity cutoffs avoid parallel local
  infrastructure. Lagrange interpolation, positivity, essential suprema, commutants
  and compact Hausdorff carriers use the standard Mathlib objects. Proved bridges
  connect raw L² frames, weak topologies, test functions and the Laplacian to the
  corresponding library APIs. See [CREDITS.md](CREDITS.md) for exact provenance.

## Structure, names and documentation

Files follow their mathematical subjects; the planar flow theorem has no PDE-module
import. Entry modules assemble every implementation module exactly once as checked
by the index script. The largest file is `CKMA/Probability/Concentration.lean` at 477 lines;
there are no size-driven splits or source lines beyond 100 columns.

Definitions use Mathlib-style capitalization and theorem names retain their predicate
and operation spelling. The project has no misleading `CKMA.Set.Finite` or
`CKMA.Summable` extension namespace. Hardy and Fock membership predicates use a
consistent `Mem...` prefix. James's sufficiency result names compactness of the weak
image explicitly. Conventional historical theorem names remain where useful.

## Proof status and remaining mathematical work

The axiom audit covers 3196 public declarations. **200** depend on `sorryAx`
(191 direct admissions). The other 2996 declarations use only standard axioms,
including every lemma, definition, abbreviation and structure. The frame, approximate-continuity, proximal and Ekeland modules have no admissions. The main remaining task is
proof completion, with scopes in [FORMALIZATION.md](FORMALIZATION.md).

Broader APIs that are useful extensions, rather than prerequisites for the current
statements, include bundled closed form norms, fully bundled interpolation spaces, and
further locally uniform and operator-closure equivalences. Cohen–Hewitt is stated for a
bounded directed left approximate identity; the essential-module characterization and norm
control on the factor remain. Newton iteration is stated for real or complex scalars. The
current positive-data and explicitly specialized targets retain valid documented scope.
Substantial proofs may
justify splitting Choquet from optimization or the branches of integral equations;
present file sizes do not require it.

## Validation

- Full build: success, 9,561 jobs.
- Strict source checks: the public entry and all files changed by the current proof effort pass with `autoImplicit=false` and
  `relaxedAutoImplicit=false`.
- Catalogue/index checks: 603 entries, 242 started; 3196 declarations, source hashes
  and subject-entry membership verified.
- Fresh axiom audit: 200 declarations depend on `sorryAx` (191 direct admissions); 2996 use
  only standard axioms; no unexpected axioms or admitted non-theorem definitions.
- Compiled unused-argument and `defsWithUnderscore` checks: no findings. The
  unused-argument linter skips admissions, so mathematical redundancy is assessed
  separately from syntactic usage.
- Source and Markdown whitespace, local links, module headers and unchanged dependency
  pins are checked. No claim is made that the complete upstream Mathlib CI suite has
  been run, or that successful elaboration proves an admitted target.
