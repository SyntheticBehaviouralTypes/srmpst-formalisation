# Change history

Completed and superseded plans, newest first. **Nothing here is a live
TODO** — `TODO.md` at the repository root is the only file to work from.

Filenames carry the date the document was last worked on, and each one
repeats that date in its title, so a plan can be located from a reference
like "the 2026-08-04 plan" without opening anything.

| date | document | what it was | outcome |
|---|---|---|---|
| 2026-08-04 | [algorithmic normalisation](2026-08-04-DONE-algorithmic-normalisation.md) | introduce `⊢a` and `norm : ⊢p → ⊢a` | **done** — both live in `Definitions/Typing/{Algorithmic,Norm}.agda`. Its header box lists statements *proved false*; read that before reviving any idea from it. |
| 2026-07-25 | [uniform trace judgement](2026-07-25-unified-traces-plan.md) | one primitive multi-step judgement | **done** — `_-[_]->_` / `_-[¬_]->*_` in `Definitions/Behav.agda` |
| 2026-07-21 | [skip judgment redesign](2026-07-21-skip-redesign.md) | rework `⊢skip` | **done** — the judgment in `Definitions/Typing/Declarative.agda` |
| 2026-07-15 | [decidable checker design](2026-07-15-decidable-checker-design.md) | `Maybe` → `Dec` checker | **superseded twice** — the module it plans is deleted; the current checker is `Check/Alg.agda` |
| 2026-07-15 | [status](2026-07-15-status.md) | progress against the above | superseded with it |
| 2026-07-15 | [notes](2026-07-15-notes.md) | proof-structure overview | stale — predates the 2026-08 restructure |

## Reading order for someone new

1. `CLAUDE.md` — build commands, architecture, recurring gotchas.
2. `TODO.md` — what is done, what is next, and the decisions behind both.
3. Anything here, only when chasing why something is the way it is.
