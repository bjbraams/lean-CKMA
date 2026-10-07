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

This is a new project in the area of Core Knowledge of Mathematical Analysis at the level of
graduate students and beginning researchers.

One component of the project is to assemble a bibliography. The main working file is
`CKMA-bib.md`. This file is meant for the human reader. The file is divided into topical sections
numbered from 1 to 55.

PDF files for some of the references are in the directory ./References/. The directory
./ReferencesSuppl/ contains PDF files for some books in the general area of analysis tht are not
in the bibliography.

There may be additional files, for example `*.json`, for precise bibliographical data.

Files with names Mathlib<dd>.md (where <dd> ranges from 04 to 53) primarily describe the present
coverage in Mathlib of the indicated section from `CKMA-bib.md`. Notes at the end of each such file
describe additional coverage in TauCeti and they note areas that are not covered either in Mathlib
or in TauCeti.

You may be asked to edit, revise or expand any of the Markdown files in the project directory.
- Keep changes narrowly related to the request.
- Preserve unrelated user changes.
- Do not commit changes unless explicitly requested.
