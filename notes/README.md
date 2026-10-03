# Notes

A place for the agents working on this repo (and the humans running them)
to talk to each other in writing. It covers what you're doing right now, what you
learned, what's hard, what you'd try next, and questions for whoever comes
after you.

`docs/` says *what* is done. `notes/` says *how* it went and *why*.

```
notes/
  now/      one file per agent: what I'm working on right now
  log/      dated entries, one per file, never edited after the fact
  topics/   curated knowledge, edited in place
```

## When you start

1. Read every file in `now/` to see who is working on what and which files
   they're touching. Stay off those files, or write to that agent first (see
   "Talking" below).
2. Read the last ten or so entries in `log/` and anything in your area:

   ```bash
   ls notes/log | tail -10
   grep -l '^area:.*IX' notes/log/*.md      # entries about Exposé IX
   ```

3. Read the topic files that touch your work, at least
   [`topics/hard-parts.md`](topics/hard-parts.md) before you start on
   something that looks open, and [`topics/strategy.md`](topics/strategy.md).
4. Check for questions nobody has answered (see below). If you know the
   answer, write it.

## While you work

Keep `now/<handle>.md` current. Create it when you start and update it when
your plan or your file set changes:

```markdown
---
author: <handle>
updated: 2026-10-03 14:20
---

Working on: SGA 1 IX.6.5, general locally noetherian case
Touching: lean/SGA/SGA1/ExposeIX/ExactSequence.lean, lean/SGA/Foundations/Limits/*.lean
Blocked on: nothing
Next: EGA IV 8 reduction for the non-noetherian case
```

Delete it when you stop. A `now/` file that hasn't been updated in two days
is stale; you may delete it, and say so in a log entry.

**Handle**: pick one when you start and use it in every file you write, e.g.
the work stream (`sga1-ix-ega4`), or tool and date (`codex-1003`). Humans use
their GitHub name.

## When you stop, or learn something worth keeping

Write a log entry: `log/YYYY-MM-DD-<handle>-<slug>.md`.

```markdown
---
author: sga1-ix-ega4
date: 2026-10-03
area: SGA1 IX, Foundations/Limits
kind: experience
---

# EGA IV 8 reduction for IX.6.5 is cheaper than it looked

What I did, what worked, what didn't and why, what's left and where,
what I'd do next. Name declarations and files.
```

`kind` is one of:

| kind | use it for |
| --- | --- |
| `experience` | what you did and what you learned: worked, failed, surprised you |
| `handoff` | stopping mid-task: exact state, what's half-done, the next step |
| `question` | something you want another agent (or the human) to answer |
| `reply` | an answer or a response to another entry (needs `re:`) |
| `proposal` | a strategy idea you want others to weigh in on |

Also update a topic file when what you learned is durable: a new hard part,
an obstacle that turned out easy, a mathlib API that saves a day, a trap. Edit
the relevant section in place and put your handle and the date on what you
add. If something there is now wrong, fix it or mark it resolved.

## Talking

Reply to an entry by writing a new one with `kind: reply` and `re:` set to
the file name you're answering:

```markdown
---
author: codex-1003
date: 2026-10-04
area: SGA1 IX
kind: reply
re: 2026-10-03-sga1-ix-ega4-ega4-reduction.md
---
```

Find the replies to an entry:

```bash
grep -l '^re: 2026-10-03-sga1-ix-ega4-ega4-reduction.md' notes/log/*.md
```

Find questions nobody has answered:

```bash
for q in $(grep -l '^kind: question' notes/log/*.md); do
  grep -q "^re: $(basename "$q")" notes/log/*.md || echo "$q"
done
```

To reach the agent that owns a `now/` file (for example to ask it to release a
file), write a `question` entry whose `area` names that agent's handle. Agents
check for their handle when they update their status:

```bash
grep -l '^area:.*<your-handle>' notes/log/*.md
```

## Rules

- **Never edit someone else's log entry.** Correct it with a `reply`. Log
  entries are a record. Topic files are the place to keep things current.
- **Be specific and honest.** Name the declaration, the file, the SGA number,
  the error. Say what failed and why. "It was hard" helps nobody. "The proper
  case needs the Grothendieck existence theorem, which mathlib lacks; the
  Stein factorization step is done in
  `lean/SGA/Foundations/Cohomology/SteinFactorization.lean`" does.
- **Short beats complete.** A ten-line entry that gets written beats a
  hundred-line one that doesn't.
- **Don't copy coverage tables.** What's proved and what's open lives in
  [`docs/formalization.md`](../docs/formalization.md) and
  [`docs/status.md`](../docs/status.md). Link to them.
- **Verify before you rely.** Notes are written by agents and go stale. Check
  a claim against the code before you build on it, and if it was wrong, say so
  in a reply or fix the topic file.
- **Notes travel with the branch.** Agents sharing a checkout see each
  other's notes immediately. Agents in separate worktrees or on separate
  branches see them once the branches are merged. Because every log entry is
  its own file, merges don't conflict.

Claiming a stretch of SGA for a pull request still happens through a GitHub
issue (see [`.github/CONTRIBUTING.md`](../.github/CONTRIBUTING.md)). `now/` is
the lighter, live version for agents in flight.
