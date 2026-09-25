# CLEANUP

*Review written and applied 2026-09-25 on branch `set-typing`.* `[x]` = done,
`[~]` = done differently from the plan (reason given), `[ ]` = left for a
decision.

## 0. `CLAUDE.md` described a different branch

- [x] Rewritten for `set-typing`: branch line, `ROOTS`, directory layout,
      the `Typing/Alg*` and `Check/` sections, gotchas, and in-flight work.
- [x] `FUTURE_WORK.md` §B marked done, with a pointer to `PLAN.md`; its
      file table was updated.
- [x] `docs/README.md` rows for `Typing/{Algorithmic,Norm}.agda` and
      `Check/Alg.agda` were updated.
- [ ] `README.md` is still stale. It was already recorded as left alone on
      purpose.

## 1. Whole files / blocks

- [x] **`Check/Wait.agda`**: deleted. It was an orphan that nothing
      checked.
- [x] **`Typing/NoLoop.agda`**: deleted. `wait/∅` (D4) is now
      `proj₂ (findMain … (λ _ _ → ⊥) …)`, and `MainLeaf.agda`'s header was
      updated.
- [x] **`Check/Core.agda` `GraphChecker`**: the dead part was deleted
      (`messageGuarded?`, `MatchRecv`/`matchRecv?`,
      `ActionAt`/`findAction`/`findStep`, `RecvWitness`/`findRecv`).
      `InactiveAt`, `na?` and `bisim?~` stay, because tests use them.
- [x] **Expression checking is defined once.** `checkExpression` in
      `Check/Core.agda` is now Alg's direct recursion, and `Check/Alg.agda`
      has `exp? = checkExpression`. `_≟Sort_` moved to `Definitions/Expr.agda`,
      next to `Sort`, so the graph-free `Check.Core` can use it.

## 2. Duplicated lemmas

- [x] **Bit-vector weights**: new `Utils/Bits.agda` (`iter`, `wt`, `Incl`,
      `wt/mono`, `wt/strict`, `wt-bound`, `wt-full`, `wt/true`, …).
      `Reachability.agda` re-exports it, so existing imports still work.
      `Bisimulation.agda` dropped its copy (`bit`, `rowWeight`,
      `RowIncluded`, `bit/mono`, `rowWeight/mono`, `rowWeight/strict`,
      `rowWeight/true`).
- [x] **Bool/List lemmas in `Bisimulation.agda`** are now one-liners over
      stdlib (`T-∧`/`T-∨`, `all⁺/all⁻`, `any⁺/any⁻`, `find`). This was
      measured: 11.9 s / 0.78 GB against 10.3 s / 0.64 GB before.
- [~] **`≡true→T`/`T→≡true` → stdlib `T-≡`**: left as is. The swap would
      replace 4 lines with 4 lines. The two lemmas moved to `Utils/Bits.agda`.
- [x] **All-edges decider**: `all-edges?` is level-polymorphic and hoisted,
      and `all-out?` is built on it. One copy instead of two.
- [x] **`Vof`**: one copy, at the top level of `Typing/Alg.agda`.
- [x] **`stepbackAt?`**: deleted.
- [~] **Bool action equality**: `eqFin`/`eqSort`/`eqAction` and their
      soundness lemmas moved to `Graph/Action.agda`, and `_≟Actionᵇ_` is
      built from them. However, **`_≟Action_` stays structural.** Deriving
      it from `eqAction` made `Bisimulation.agda` take 110 s / 14 GB
      instead of 10 s / 0.6 GB, because `actionMatches` there is
      `⌊ _≟Action_ ⌋`. The `ChoiceCode`/`_≟Choice_` machinery stays
      with it. This is recorded as a gotcha in `CLAUDE.md`.

## 3. Dead definitions

- [x] `Typing/Properties.agda`: `~mainLeaf/weaken-visited`, `~MainLeaf`,
      and `mainLeaf/transport-leaf~/weaken-visited` with its comment.
- [x] `Typing/Declarative.agda`: the `MainLeaf` data type.
- [~] `Typing/Declarative.agda`: `_&_&_⊢skip_∶_` **kept**. The usage scan
      missed its infix uses in `Properties.agda`.
- [x] `Behav.agda`: `~R-L/id′`, and `step-is-prop/eq`, whose only user it
      was.
- [~] `Behav.agda`: `skip/∈T-back` **kept**, because `FUTURE_WORK.md` §A
      builds on it.
- [x] `Typing/Alg.agda`: `at/end-inv` and `⊢s′_∶_`, plus the `PLAN.md`
      line mentioning `⊢s′`.
- [~] `Typing/AlgEquiv.agda`: `wait/∅` **kept**. It is D4, a result, and is
      now derived from `findMain` (§1).
- [x] `Graph/Reachability.agda`: `reachVia?` and `Incl-≡`.
- [x] `Graph/Bisimulation.agda`: `refine/weight≤`, and `refine/mono`
      together with its private chain (`simulates/mono`,
      `edgeMatches/mono`, `all/mono`, `any/mono`).
- [x] `Graph/WellBehaved.agda`: `EdgeTarget`.
- [x] `Check/Alg.agda`: `alg-probe` and `alg-probe-in`. Its header and
      `PLAN.md` now name `Probing.probe`.

## 4. Tests

- [x] **`Tests/Perf01`–`07`** were merged into
      `Tests/Perf01_TinyRejections.agda`, one sub-module per shape, with the
      same seven forced rejections. The seven old files are deleted. The
      merged file checks in 5.5 s / 0.69 GB, against ~10 s per file before.
      Note that one-choice labels must be `here : Fin 1`: a bare `zero`
      leaves `nchoices` unsolved, and the first merge attempt took 560 s /
      8 GB before failing on unsolved metas.
- [x] **`Tests/CheckAlgSanity.agda`**: the `Reach₀?` section now tests
      `Env.unskip?` directly, and the header was updated.
- [ ] **`Tests/AnchorAttempts`, `Tests/PushRecAttempts`,
      `Tests/RecSkipCounterexample`**: not changed. Moving them to `Stale/`
      is your call. They are cheap (~10 s each).

## 5. Stale comments

- [x] `Typing/MainLeaf.agda`, `Typing/Properties.agda`,
      `Graph/Decision.agda` and `Check/Alg.agda`.
- [x] `Examples/{CounterExamples,NoSynGT,OAuth2,IndepW}.agda`.
- [x] `Definitions/Typing.agda`, `Typing/AlgNorm.agda`,
      `Typing/Substitution.agda`, `Graph/Algebra.agda`, `Check.agda`,
      `Check/Graph.agda`, `Tests/PushRecAttempts.agda` and
      `Tests/WaitNotSkip.agda`.
- [~] `Typing/AlgNorm.agda`'s header still describes the deleted
      `Norm.agda`, but it now says so explicitly ("now deleted"). It is kept
      as design history.

## Verification (2026-09-25)

Every root, test and example was checked with plain `agda`, and each exit
status and peak memory was recorded (`/usr/bin/time`), because an
OOM-killed run prints nothing.

- **Roots:** all pass. `Check.agda` took 103 s / 6.0 GB, against 114 s /
  7.0 GB at HEAD (measured in a worktree).
- **Tests and examples:** all pass, in 5–15 s each. `Examples/IndepW` took
  14.6 s / 2.6 GB.

## 6. Housekeeping

- [x] 17 orphaned `.agdai` files (deleted modules) were removed.
- [ ] `.claude/` is still untracked. Ignoring it or committing it is your
      call.
- [ ] Nothing is committed.
