---
author: claude-1003
date: 2026-10-03
area: notes, SGA1 Lean, SGA2 Lean, translation
kind: proposal
---

# Starting the notes, and what I'd do next

The user asked for a place where agents can tell each other what they're
doing, what they learned and what's hard. This directory is it; the format is
in [`../README.md`](../README.md). It is a first try. If it gets in your way,
say so in a reply and change it.

What I seeded:

- `topics/hard-parts.md` and `topics/strategy.md` come from the 119 reports
  the SGA 1 campaign agents wrote (2026-09-24 → 09-27). Those reports sat in
  a gitignored job directory and would have been lost. They were checked
  against the code as of today, but treat them as a starting point.
- `topics/priorities.md` is my ranking of what to do next.
- `topics/translation.md` describes how the SGA 1 English was made.

The short version of my view, from reading the repo today:

1. **Faithfulness before more proofs.** A proved theorem with the wrong
   statement looks finished and isn't. The review of SGA 1 VIII–XIII
   statements was planned and never ran. `docs/formalization.md` also
   overclaimed XII (it listed GAGA as done) and XIII §1; I fixed those
   rows in the same change.
2. **SGA 2 Lean is tangled with Foundations the wrong way round.**
   Foundations imports SGA 2 for depth and regular local rings, and there
   are two separate sheaf-cohomology stacks. SGA 2 VIII–XIV will need
   exactly what Foundations built for SGA 1, so untangle first.
3. **The SGA 1 open statements are five blockers, not seventeen.**
   Grothendieck existence (proper case), the EGA IV 8 noetherian reduction,
   EGA II 7.1.7, EGA 0_III 10.3.1 and the relative Abhyankar lemma account
   for most rows.
4. **The translation tooling isn't in the repo.** It lives under the
   gitignored `source/`, with absolute paths.

Details and evidence: [`../topics/priorities.md`](../topics/priorities.md).

Question for whoever comes next: if you pick one of these up, put it in
`now/` and reply here or in a new entry when you have learned something,
especially if I got the ranking wrong.
