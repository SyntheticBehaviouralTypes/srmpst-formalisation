# CODING_STYLE.md

Hard rules for editing `*.agda` files in this repository, mined from how the
existing "locked" files (`Definitions/Behav.agda`, `Safety/*.agda`,
`Typing/Substitution.agda`) are actually written — not invented preferences.
Type-checking is necessary but not sufficient: an edit that compiles but
violates a rule below is not done. See `CLAUDE.md`'s "Recurring gotchas" for
the fuller incident history behind several of these; this file is the
checklist to apply on every edit, condensed to be actionable.

## 1. Editing discipline

- Never edit a file unless explicitly asked (`AGENTS.md`). This still holds
  when the ask is narrow — touch only what was asked.
- When asked to make site X "consistent with" an already-compiling template
  Y (e.g. an already-rewritten analogous function elsewhere), copy Y's
  binder names, argument order, and decomposition shape as closely as the
  two signatures allow. Deviate only for a specific, statable reason, and
  say what it is in a one-line comment — don't silently improvise new names.
- Before calling an edit done, diff it against its template site binder by
  binder, not just "does it type-check."

## 2. Binder hygiene

- Bind a name only if the clause body uses it, **or** a sibling clause of
  the same multi-clause function uses the same positional slot. Otherwise
  write `_`.
  - Standalone example (no siblings, so unused ⇒ `_`):
    `in/α gr px = _ ∷ [] , _ , tr/step gr tr/refl , here px` names neither
    the target state nor its own `∈T` witness.
  - Sibling-clause example (unused *here*, but keep the name because the
    next clause uses it): `Safety/Preservation.agda`'s
    `comm/ready-from-∈T-skip` and `Safety/Head.agda`'s `leaf-from-∈T` both
    name the decomposed state `H` in their `here`-clause even though that
    clause's body never mentions it, because the sibling `there`-clause
    does — keeping the same trace shape named identically across a case
    split is what a reader is tracking. `_` there would *break* the
    template, not follow it.
- When copying an existing multi-clause template (§1), copy its binder
  names as-is, including ones the specific clause you're writing doesn't
  use — don't "clean up" a name to `_` just because that one clause is
  silent about it.

## 3. Naming conventions

Use these; don't invent alternatives for concepts that already have a name
in the codebase.

| Name(s) | Meaning |
|---|---|
| `G`, `G′`, `G″`, `H`, `H′` | `Behav`/graph states. Primed = "the next/later one along a chain." |
| `gr`, `gr′`, `gr₀`, `gr₁`, … | A single-step transition witness (`_-<_>->_`). Subscripts distinguish two independently-arriving step witnesses live in the same clause. |
| `tr`, `tr′` | A multi-step trace (`_-[_]->_`). |
| `td` | A typing derivation (`_&_⊢p_∶_`). |
| `std`, `ktd` | A `⊢skip` derivation / its step continuation. |
| `mem` | An `Any`/`All` membership or exclusion witness over a trace's actions. |
| `na` | A `not-active-in` witness. |
| `P`, `Q` | Participants (`Part`). |
| `α`, `β`, `αs`, `βs` | Actions / lists of actions. |

Prefer the Unicode prime `′` (U+2032) for "the related next value of the
same thing." Only use a bare ASCII apostrophe where the codebase already
does, for an already-fixed reason (`Complete.agda`'s `{G' = …}` implicit,
called out in `CLAUDE.md`) — don't introduce new ASCII-apostrophe names.

## 4. Formatting

- 2-space indent per nesting level (module body, `where`, `with`
  continuations).
- One blank line between top-level definitions. No blank line inside a
  single multi-clause function unless separating logically distinct clause
  groups.
- Multi-line type signatures: leading `→` on the continuation line. Match
  the indent style of the declaration immediately above/around it in the
  same file rather than inventing a new layout.
- **Hard cap: 80 columns, no exceptions.** Some pre-existing files run
  longer (`Safety/Skip.agda` has a 147-column line) — that is legacy, not
  license; do not use it to justify a new long line. When a clause head
  doesn't fit, put the function name alone on its own line and each
  argument on its own indented line (see `Safety/Preservation.agda`'s
  `comm/ready-from-∈T-skip` for the pattern), rather than letting anything
  run past column 80. Check with
  `awk '{ print length }' file.agda | sort -rn | head` before calling an
  edit done.
- Only hand-align `=`/`→` across sibling clauses with padding spaces if the
  function already does it (e.g. `tr/trans`'s two clauses). Match the local
  convention — don't add alignment nobody asked for, and don't strip
  existing alignment.

## 5. Comments

- Default to none. Add one only to record a non-obvious *reason* — a design
  decision, a rejected alternative, an Agda-specific gotcha, a forward
  pointer to where something matters. Never restate what the code already
  says.
- Reference identifiers in backticks: `` `find-leaf/remember` ``,
  `` `P ∈T G` ``.
- If a helper's existence needs justifying, say which of §6's two
  conditions applies — don't just assert it's useful.

## 6. Abstraction discipline — no speculative helpers

- Established project rule (`unified-traces-plan.md` §2): do not add a
  "smart constructor" or helper purely to mirror a deleted name, or for
  hypothetical future reuse. Write the raw term inline where it is just as
  legible.
- Extract a helper only when it (a) composes ≥2 real proof steps, or (b) is
  actually called at several (roughly ≥5) sites in live (non-commented-out)
  code.
- Never introduce a new auxiliary judgment, transport lemma, or
  soundness/completeness layer to route around a hard case. Look for the
  small local fix first. If genuinely stuck, say so rather than adding an
  abstraction to paper over it.

## 7. Proof hygiene

- No `postulate`s and no silently-left `{!!}`. Every open hole must be
  tracked explicitly in the relevant `TODO.md`/plan document.
- Every `yes`/`no` in a `Dec` result is a real, direct proof term built from
  constructors/lemmas already in scope — never a deferred placeholder.
- When decomposing an existential (`Σ`/`∃`) to recurse, decompose the
  *given* argument in one step. Never reconstruct a multi-piece tuple from
  independently-matched sub-patterns of *different* arguments before
  recursing on it — the termination checker rejects this (see
  `unified-traces-plan.md` §9, `CLAUDE.md`'s gotchas). If two different
  arguments each contribute part of a recursive call's tuple, split into a
  `-aux` helper taking the pieces as separate curried arguments instead.

## 8. Imports

- Import the narrowest module that has what's needed
  (`Definitions.Typing`, not the full `Definitions` aggregator) inside
  `Safety/*.agda` and `Typing/Substitution.agda` — see `CLAUDE.md` for the
  cycle this avoids.
- Keep re-exports scoped to what's actually defined in the re-exporting
  file's own directory. Don't widen a re-export "for convenience" — this
  has previously broken unqualified-`open` ambiguity elsewhere.
- Pin vector implicits (`{Ξ}`, `{v}`, `{left}`, `{right}`, `{X}`, …)
  explicitly at call sites whenever the underlying operation is
  non-injective (`wt`, `Incl`, `mark`, `lookup`, `tabulate`) instead of
  leaving them for Agda to infer.

## 9. Before calling an edit done

- Recompile the single file in isolation (`agda path/to/File.agda`) while
  iterating — don't rely on `runall.sh` alone.
- Diff the change against whatever template site it was supposed to mirror,
  binder by binder.
- Confirm every hole you didn't fill is still exactly the hole that was
  there before — no new hole introduced silently.
