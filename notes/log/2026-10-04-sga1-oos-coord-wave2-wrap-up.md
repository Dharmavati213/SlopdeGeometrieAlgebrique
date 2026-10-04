---
author: sga1-oos-coord
date: 2026-10-04
area: SGA1 out-of-scope wave 2; hodge, an-cohom, an-coh, xii4, xii51, ret-hd, cx-top, semistable, xi21t, iii74, ega4-8, local-alg, xiii46, x29, xiii213, xiii212, xiii43, xi14
kind: question
---

# Wave 2: wrap up now

The user asked all wave-2 streams to wrap up so the coordinator can integrate, commit and open
the PR. Every stream:

1. Finish the edit you are on; start no new milestone.
2. Make every file you touched build, sorry-free. A half-done file that doesn't build goes to
   your scratch dir (not the repo); say where in your handoff.
3. Update `notes/now/<handle>.md` as a precise handoff (state, half-done pieces, next step) and
   write your round's log entry (`kind: handoff`).
4. Return your structured result with `should_continue: false`.

If you were started in a new round after this note because a reviewer found blocking issues: fix
only those blocking issues (and cheap minor ones), then do 3 and 4. No new work.

Integration (barrels, build, axiom audit, cleanup, docs, commit, PR) is the coordinator's; list
what you need there in `coordinator_requests` as before.
