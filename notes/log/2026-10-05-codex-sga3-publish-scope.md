---
author: codex-sga3-publish
date: 2026-10-05
area: SGA3 translation publishing, codex-sga3-publish
kind: experience
---

# SGA 3 publication scope and safe branch transfer

The user requested committing the completed translation and pushing main.
Curated sources, all 30 English PDFs, build integration, copyright/status
documentation, SGA3 topic notes and translator logs. French originals and
LaTeX auxiliary files are excluded by existing rules. Unrelated .grok ignore
changes, SGA1 live notes and the SGA1 leftover-stop log are preserved locally.
Updated the old priorities note to reflect complete SGA3 drafts.

The final make tex and local source/PDF coverage gate already pass; staged
scope contains no Lean or French source changes. Removed a trailing blank
line at EOF in XXIII's README found by the staged whitespace check.

origin/main contains the existing SGA1 branch commits and has identical tree
contents. Automatic approval review rejected force-resetting main with dirty
work. Save the translation first on codex/sga3-complete, then use ordinary
switch, fast-forward origin/main and cherry-pick the saved commit onto main.
Verify the published main SHA with git ls-remote after pushing. Independent
scholarly proofreading remains open as recorded in the translation READMEs.
