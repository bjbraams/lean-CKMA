# Project instructions — lean-CKMA

Before working, read and follow [the shared Lean instructions](../lean-codes/AGENTS.common.md),
then apply the project-specific rules below. Resolve that path relative to this file.
Local rules take precedence over the shared defaults. If the shared file is unavailable,
report that fact rather than proceeding without it.

## Build settings

- Lake root: the directory containing this `AGENTS.md`.
- Build output: `.lake/build-CKMA`; preserve the matching `buildDir` in `lakefile.toml`.
- Ordinary build command: `lake build > /tmp/ckma-build.log 2>&1`.

## Project

This is a project in the area of Core Knowledge of Mathematical Analysis at the level of
graduate students and beginning researchers.

One component of the project is to assemble a bibliography. The main working file is
`CKMA-bib.md`. This file is meant for the human reader. The file is divided into topical sections
numbered from 1 to 55.

PDF files for some of the references are in the directory ./References/. The directory
./ReferencesSuppl/ contains PDF files for some books in the general area of analysis tht are not
in the bibliography.

There may be additional files, for example `*.json`, for precise bibliographical data.

Files with names SYNOPSIS<dd>.md (where <dd> ranges from 04 to 53) are meant to describe the
mathematical content of the indicated section from the bibliography. Their numbered entries,
cited as <dd>.<k>, are stable identifiers; `SYNOPSIS.md` is the index.

Files with names STRUCTURE<dd>.md describe the coverage in Mathlib and TauCeti of the material in
the corresponding SYNOPSIS<dd>.md, with declarations, source locations and hypotheses. Each section
follows a synopsis heading and ends with a line classifying every numbered entry under it as
covered, partly covered, or not covered. `STRUCTURE.md` is the index and records the source
revisions. `MathlibCoverage.md` and `TauCetiCoverage.md` summarise the coverage section by section
for each library. `GAPS.md` selects and assesses the principal missing results, and
`GAPS_EASY.md` gives short derivations from library results for those entries of `GAPS.md` that
have one.

Following the bibliographical work and the development of the inventories the project continues
with the formalization of content of GAPS.md. The Lean codes for this formalization are developed
in the subdirectory CKMA. The Lean codes created there should all live in a CKMA namespace.
Within that namespace the naming should adhere to Mathlib standards. (I have in mind that at some
point this becomes a TauCeti project, and then the namespace CKMA will be replaced by namespace
TauCeti.) So one task is to go through all of GAPS.md and for the identified gaps, create code
according to Mathlib standards in the CKMA subdirectory. At first any such code may only be
admitted, but in time the `sorry`s should be removed.

You may be asked to edit, revise or expand any of the files in the project directory or to create
new files.
- Keep changes narrowly related to the request.
- Preserve unrelated user changes.
- Do not commit changes unless explicitly requested.

## File length

A Lean file of about 1000 lines is a candidate for splitting along a natural mathematical seam;
1500 lines is the hard limit, and a file longer than 1500 lines must be split.

## Imports between sections

For each section we have the most basic definitions and their minimal API (inasmuch as it is not
yet in Mathlib or somewhere else in TauCeti) in a file `CKMA/<Section>/Basic.lean`, which in turn
may reference files in a subdirectory `CKMA/<Section>/Basic/`.
As much as is possible files in one section of CKMA should import from other sections only such
`Basic` files. If it is necessary or it appears desirable to depart from this rule then please
note it explicitly in the conversation.

## Documentation consistency

- Describe the present mathematical content and coverage. Do not include
  development histories, review rounds, or accounts of additions, removals,
  renumbering, or changes in inventory counts. Retain source provenance
  and the library revisions needed to interpret coverage claims.
- Treat each numbered SYNOPSIS statement as the mathematical source for
  its restatements in GAPS.md and GAPS_EASY.md. Propagate corrections to
  hypotheses, conventions, and conclusions to every affected restatement
  and STRUCTURE assessment. A Scope or Argument paragraph must not silently
  add a missing hypothesis to a Statement paragraph.
- After changing statements or selections, recount synopsis entries,
  coverage classifications, selected gaps, easy entries, and Scope
  paragraphs. Update the indexes and library summaries, and check local
  Markdown links. New entries take the next free identifier.
