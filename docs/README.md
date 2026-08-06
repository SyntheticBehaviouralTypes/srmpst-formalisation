# Change history

Completed and superseded plans, newest first. **Nothing here is a live
TODO** — `FUTURE_WORK.md` at the repository root is the only file to work
from. (There is no longer a root `TODO.md`; it was archived here on
2026-08-05 once its plan closed.)

Filenames carry the date the document was last worked on, and each one
repeats that date in its title, so a plan can be located from a reference
like "the 2026-08-04 plan" without opening anything.

| date | document | what it was | outcome |
|---|---|---|---|
| 2026-08-05 | [deciding `⊢a`](2026-08-05-DONE-deciding-algorithmic-judgment.md) | the checker for `⊢a`, and `⊢p` through it | **done** — `Check/Alg.agda`, hole-free, no postulates. Also the `⊢head` → `⊢a` migration of `Safety/*`. Its header box says which sections are superseded by `FUTURE_WORK.md`; the net sections claim the projection lemma is an `↔`, and **it is not**. |
| 2026-08-04 | [algorithmic normalisation](2026-08-04-DONE-algorithmic-normalisation.md) | introduce `⊢a` and `norm : ⊢p → ⊢a` | **done** — both live in `Definitions/Typing/{Algorithmic,Norm}.agda`. Its header box lists statements *proved false*; read that before reviving any idea from it. |
| 2026-07-25 | [uniform trace judgement](2026-07-25-unified-traces-plan.md) | one primitive multi-step judgement | **done** — `_-[_]->_` / `_-[¬_]->*_` in `Definitions/Behav.agda` |
| 2026-07-21 | [skip judgment redesign](2026-07-21-skip-redesign.md) | rework `⊢skip` | **done** — the judgment in `Definitions/Typing/Declarative.agda` |
| 2026-07-15 | [decidable checker design](2026-07-15-decidable-checker-design.md) | `Maybe` → `Dec` checker | **superseded twice** — the module it plans is deleted; the current checker is `Check/Alg.agda` |
| 2026-07-15 | [status](2026-07-15-status.md) | progress against the above | superseded with it |
| 2026-07-15 | [notes](2026-07-15-notes.md) | proof-structure overview | stale — predates the 2026-08 restructure |

## Reading order for someone new

1. `CLAUDE.md` — build commands, architecture, recurring gotchas.
2. `FUTURE_WORK.md` — the five open lines of work, and one dead end
   recorded so it is not repeated.
3. `2026-08-05-DONE-deciding-algorithmic-judgment.md` — its "Philosophy"
   and "Acceptance criterion" sections are still the best account of *why*
   `Check/Alg.agda` is shaped the way it is.
4. Anything else here, only when chasing why something is the way it is.
