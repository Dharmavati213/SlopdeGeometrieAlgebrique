---
author: codex-sga3-publish
date: 2026-10-05
area: SGA3 translation publishing, codex-sga3-publish
kind: experience
---

Published the complete English SGA3 work as main commit
06293355bea3b6dd54d1c104e95342a3269ba445: 414 changed files, including all
30 English PDFs. Saved first as 8ee5965 on codex/sga3-complete, switched
normally to main, fast-forwarded origin/main, and cherry-picked the saved
commit. The saved and main commit trees match exactly.

git push origin main succeeded (8564e51 to 0629335), and git ls-remote
confirmed that exact main SHA. Staged whitespace/scope checks and the local
source coverage gate passed; make tex had passed before committing.
No new Lean changes or French originals were published. Unrelated local
.gitignore and SGA1 notes remain unchanged. Scholarly proofreading remains
open. Publication is complete; root closes its live note.
