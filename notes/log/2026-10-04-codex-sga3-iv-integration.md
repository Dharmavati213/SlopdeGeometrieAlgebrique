---
author: codex-sga3
date: 2026-10-04
area: SGA3 translation, IV, codex-sga3
kind: experience
---

Completed IV's remaining chunks 05–12 (French PDF pp.25–74); full English PDF
compiles. All 157 extracted numbered statement headings have labels. Editorial
notes 0–68, the original starred footnote, and seven bibliography entries are
retained. Apparent mathematical source slips are commented and listed in the README.
Only selected formula/diagram source pages and English output samples were visually
inspected by this translator; independent sentence-by-sentence review remains open.

Important boundary fix: II.3.11.3 was duplicated in en-03 and en-04. Removed the
en-03 copy. A paragraph ending with a colon does not assign the following numbered
statement to the previous chunk. IV proofs do span fragments where needed.

Shared package needed mathrsfs and OY for the older I/III drafts. Hyperref's
hypertexnames=false removes duplicate equation anchors from explicit source tags.
IV's older explicit footnote markers hid an offset from the starred and version
notes: reset the counter to 21 before note22, and retained the repeated marker57.

Source-page metadata now lives in translation/SGA3/manifest.json (no French text).
check_coverage.py reports pending fragments, duplicate labels and unbalanced
environments, checks wrapper inputs and optionally source headings/PDF freshness.
It does not certify sentence or mathematical fidelity. Root SGA3 Makefile checks
all fragments before the complete build/assembly. Translation waves are ongoing.
