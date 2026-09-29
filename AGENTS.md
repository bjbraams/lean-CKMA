# Project instructions

## Build topology (do not change)

- Lake root is this directory. This directory is on NFS.
- .lake is a symlink to /export/scratch1/braams/lean-codes-lake on local disk.
- Never replace, delete, or retarget that symlink.
- Never run lake build from a subdirectory as if it were the package root.
- Never copy Mathlib or .lake onto NFS ($HOME).
- Do not “fix” the link because it points outside the repo. That is intentional.
- That lake directory is shared with the companion projects (lean-SCV, lean-codes, lean-AAR,
  lean-LCS). They share `.lake/packages` (all pin the same Mathlib), but this project writes
  its own build outputs to `.lake/build-CA` (`buildDir` in `lakefile.toml`), because Lake's
  build traces include the package name and modules with equal names (`ComplexAnalysis.*`,
  `ToMathlib.*`) would otherwise overwrite each other. Keep that `buildDir` setting; never
  write to or delete another project's build directory.
- Do not set `LEAN_PATH`, `LAKE_HOME`, or a custom cache dir unless asked.
- If `.lake` is missing or is no longer a symlink to the path above, stop and ask. Do not repair it.
- After every Lean edit: `lake build` from the Lake root.
- For ordinary builds, use lake build > /tmp/ac-build.log 2>&1; reuse this filename to preserve
  the existing command approval.
- Without LSP/MCP: treat `lake build` output as the only proof-state.
- Do not bump lean-toolchain or Mathlib unless asked.

## Project

This is a new project in the area of Core Knowledge of Mathematical Analysis at the level of
graduate students and beginning researchers.

The initial project effort is to assemble a bibliography. The main working file is
`CoreKnowledgeMathematicalAnalysis.md`. This file is meant for the human reader.

There may be additional files, for example `*.json`, for precise bibliographical data.

PDF files for some of the references are in the directory /export/scratch1/braams/Books/.
Files there have a name that shows the author or authors, year, a shortened title, and the
publisher. It may be possible to recognize a book just by the filename, but of course the
files are readable. There are about 6200 files there, so many more than the books for this
project.

You may be asked to edit, revise or expand any of the Markdown files in the project directory.
- Keep changes narrowly related to the request.
- Preserve unrelated user changes.
- Do not commit changes unless explicitly requested.
