# Status — `Maybe` → `Dec` conversion of `Definitions/TypeChecker.agda`

Tracks progress against the plan in `decidable.md`. The build is validated with
`./runall.sh` and is **green** as of this writing.

Goal: `check : ∀ Pr → Dec (Γ & Δ ⊢p P ◂ Pr ∶ s)` — a genuine decision procedure
for the declarative typing judgment over a finite-graph LTS, replacing the
current `Maybe`-returning checker.

---

## Done

### Phase 0 — mechanical `Dec` conversions (§1) ✅
- `inferExpression`, `messageGuarded?`, `findAction`, `findStep`, `findRecv`,
  `findIncoming` all return `Dec`.
- `⊢e-unique : Γ ⊢e E ∶ S → Γ ⊢e E ∶ S′ → S ≡ S′` added in `Definitions/Expr.agda`
  (also `s/unit≢s/bool`).

### Phase 1 — decidable graph infrastructure (§2) ✅
- `LTS/Reachability.agda`: reachability fixpoint (`reachVia`, `reachVia?`,
  `PathVia`, `wt`/`Incl` counting-termination), and `∈T?`.
- `t/end` now uses the exact `∈T?` instead of the `globallyInactive?`
  over-approximation.

### Phase 2 — semantic characterization of `⊢skip[ prod ]` (§3.1, §3.3, §3.4) ✅
- `SkipSem` module: `SemSkip`, `semSkip?`, and **Theorem B** (`build`/`theoremB`)
  turning a `SemSkip` witness into a `prod` skip tree (including cyclic
  `skip/cycle` closure).
- `checkClosure` rewired to `checkClosureSkip` (uses `semSkip?` + `theoremB`);
  removed the old `checkSkip`/`checkSkipStep`/`first`/`allMaybe`.

### Phase 3 — the bounded algorithmic judgment `Alg` (§4) ✅
- `LTS/Reachability.agda` gained `PathViaP` (predicate-filtered path) with
  bridges `pathViaP→pathVia` / `pathVia→pathViaP` and `pathViaP-map`.
- In `TypeChecker.agda`: standalone predicate-only `NLP` / `ReachLP` / `SemSkipP`;
  split the skip decision into a leaf-free `SkipDecide` module (`semSkip?`) vs the
  construction module `SkipSem` (`theoremB`).
- `Direct` / `direct?` / `direct-sound` — the syntax-directed layer with full
  refutations.
- The mutual block: `Alg : ℕ → Pred` (a recursive **function** on fuel, NOT a
  datatype — required for strict positivity; `Alg 0 = ⊥` gives an honest
  fuel-0 `no λ()`), `checkWithFuelD : ∀ k → Dec (Alg k …)`, `alg-sound`, and
  `alg-mono` (`k ≤ k′ → Alg k ⊆ Alg k′`) via `direct-mono`, `semSkipP-mono`,
  `reachLP-mono`.
- The old `Maybe` checker (`checkWithFuel`/`checkDirect`/`checkClosure`/`check`)
  still coexists as the public API; it gets rewired to `Alg` in §6.

### Completeness module architecture ✅
- `Definitions/TypeChecker/Complete.agda` (`module …Complete (N)` →
  `module GraphComplete (G)(wb)`) imports **both** `Definitions.TypeChecker`
  and `Safety.Skip` — no import cycle, since it lives outside the `Definitions`
  aggregator. Root `Complete.agda` wires it into `runall.sh`.

---

## PLAN REVISED (2026-07-14) — see `decidable.md` v2

The completeness capstone was restructured. **Dropped entirely** (do not
pursue): the `cost` measure as an induction metric, C2 (the stuck item), C3
(trace shortening), C4 / revisit normalization, round-tree canonicalization,
and the §6 budget arithmetic over declarative derivations. Replaced by:

1. **Saturation** `sat : Alg k ⊆ Alg (F Pr)` — pure `Alg`-side pigeonhole on
   the finite state set per level, using the existing `wt/Incl` machinery
   (v2 Phase S, new file `Definitions/TypeChecker/Saturate.agda`).
2. **Completeness up to `~`** — `complete : ⊢p ∶ s → Δ ~ᵛ Δ′ → s ~ s′ →
   Alg (F Pr) … s′` by *structural* induction (mirrors `td/bisim` case by
   case); the `~`-quantified IH makes Theorem A's leaf set
   `L t = ∃ ℓ. HasMainLeaf std ℓ × ℓ ~ t`, whose `~`-closure is `~trans` —
   this is what eliminates C2 (v2 Phase C).

Theorem A survives with the same abstract-`L` design, but the walk is now
**structural on the `PathViaP` path** (no length index, no fuel) — v2 Phase A.

### Carry-over status of Complete.agda pieces
- `spine` ✅, `HasMainLeaf` ✅, `skip-na` ✅ — reused as-is by v2 Phase A.
- `Anc` ✅ — to be extended to `AncL` (each entry also carries
  `HasMainLeaf D ℓ → L ℓ`).
- `maxWithMem(-lb)`, `traceLen`, `cost`/`costSkip`, `cost-unskip<`,
  `costSkip<skip`, `cost-main<skip`, `costSkip-child<` — **dead under v2**;
  ✅ deleted in Phase F step 4.

## Remaining work (v2 phases; do in this order)

- **Phase S** ✅ DONE (build green) — new file
  `Definitions/TypeChecker/Saturate.agda` (`module GraphSaturate (G)(wb)`),
  root `Saturate.agda` wired into `runall.sh`. Delivers
  `sat : ∀ Γ Δ P Pr s k → Alg k … s → Alg (F Pr) … s`. Contents: `F`/`J`,
  `pf-suc`, `J+size≡F`, `bound`, `branchFuel-lb`, `J-recv-bound`/`J-if₁`/`J-if₂`;
  `It`/`It?`/`it-mono-≤` (fuel-recursive function like `Alg`); pigeonhole
  `vec`/`stabOr` (via generic `findCex`+`¬→→×`)/`search` (fuel-with-invariant,
  `SkipSem.build` style)/`findStab`; `collapse`/`itCap`/`It→Alg`; mutual
  `sat`/`algk→It`/`directSat`/`satBr` (subterm-sat inlined per constructor,
  never through `direct-mono`). Gotcha hit: pin `wt-full {v = vec …}`.
- **Phase T** ✅ DONE (build green) — transport pack appended to
  `Complete.agda` (`GraphComplete`): `pathViaP-pull` (T1, pull `¬L`-path back
  along `~` via `~R→`/`~R→~`), `pathVia-push` (T2, push path forward via
  `~L→`/`~L→~`), `na-~` (T3), `semSkipP-bisim` (T4, composite — `SemSkipP`
  `~`-invariant for `~`-closed `L`), `hml-bisim` (T5, main leaf of a
  `SK.skip-td/bisim`-transported tree ↝ `~`-related original leaf; `skip/cycle`
  case absurd `()`), `dropSuc`+`weakenTo` (T6, prefix-weaken visited vector by
  iterating `SK.skip/weaken-visited {Ξ′ = []}`). Extra imports: `Data.Fin`/
  `import Data.Fin as F`, `_∸_`, `PathViaP`/`pathP/nil`/`pathP/cons`. Compiled
  first try — no gotchas hit.
- **Phase A** ✅ DONE (build green) — Theorem A in `Complete.agda`. `Anc`
  refactored to `AncL` (each entry also carries `∀{ℓ}→HasMainLeaf D ℓ→L ℓ`);
  `ancLookup` (positional). Added `hml-wv` (general-`Ξ′` `HasMainLeaf`
  pullback through `SK.skip/weaken-visited`) + `hml-weakenTo` (iterated) so the
  weakened ancestor's coverage transfers. `walk` is structural on the
  `PathViaP` argument: nil→(skip/main absurd via `¬Lt∘lc`, skip/step→`na`+
  `spine`); cons→`go (ktd gr_β) refl` where-helper (spine's eqn-kept trick):
  `(prod,child)` descends with subst-transported coverage, `(nonprod,
  skip/cycle X cyc-eq)` JUMPS = `ancLookup`+`weakenTo`+`SK.skip-td/bisim
  ~ᵛ-refl ~ᵛ-refl cyc-eq`, coverage recovered via `hml-bisim`+`hml-weakenTo`+
  `Lcl`. `theoremA` = `walk _ _ _ _ L Lcl std tt lc`. Compiled first try
  (Γ/Δ/P/Pr made explicit params of `walk` so the where-clause can name them;
  Ξ/r/t/u bound in the cons-clause pattern). Extra import: Vec `_++_`.
- **Phase C** ✅ DONE (build green) — completeness up to `~` in `Complete.agda`.
  Imports `F`/`sat`/`branchFuel-lb` from `GraphSaturate`, `All`, more
  `Nat.Properties`/`Data.Sum`. `F-suc`/`F-if₁`/`F-if₂`/`F-recv` subterm bounds;
  `intoF Pr` (one `sat` step, `Pr` EXPLICIT since `v`/`∅`/`rec` injected values
  don't mention the leaf predicate); `pred-fold` (fold a `-[¬P]->*` trace into
  `Alg` unskip steps, re-saturating each). Mutual `complete`/`completeLeaf`
  mirrors `td/bisim` case-by-case → `Alg (F Pr)`; `t/skip` instantiates
  `theoremA` with `L t = ∃ ℓ. HasMainLeaf std ℓ × ℓ~t` (`Lcl`=`~trans`,
  `lc`=`(_,hml,~refl)`), transports via `semSkipP-bisim`, maps leaves via
  `completeLeaf`; `t/unskip` via `SK.skip/bisim`+`pred-fold`. `complete₀ D =
  complete D ~ᵛ-refl ~refl`. Gotchas: bind `{Pr = PP}` per clause + pass to
  `intoF`; pin `{G = G}` on `listed⇒step`/`step⇒listed`; `∀ {ℓ} →` not `{ℓ}`.
- **Phase F steps 1–3** ✅ DONE (build green, strict) — the decision
  procedures in `Complete.agda`. In `GraphComplete`: `checkD`
  (`checkWithFuelD (F Pr)` + `alg-sound` yes-branch / `complete₀` no-branch),
  `checkClosedD`, and `checkSessionD` (finite conjunction over `Fin N` via a
  local `allDec`). At `Complete` level: `module WbIrr (G)(wb)(wb′)` with
  `typing-wb-irrelevant`/`skip-wb-irrelevant` (mutual, re-wraps each
  constructor — the judgments never inspect the `WellBehaved` witness) plus
  helpers `mode-conv`/`mg-conv` (`Mode`/`MessageGuarded` are `MPST`-parameterised
  so their copies differ per witness); then the bundled `checkProcessD`/
  `checkRootedProcessD`/`checkSessionWD`/`checkRootedSessionD` returning
  `Dec (CheckedProcess …)` / `Dec (CheckedSession …)` (destructure the record's
  existential witness, refute via `WbIrr.typing-wb-irrelevant`). Gotchas:
  import `Dec`; rename `check`→`checkD` (clashes with the Maybe `check`).
- **Phase F step 4** ✅ DONE (build green, strict) — final cleanup. Deleted
  from `TypeChecker.agda` the entire `Maybe` cluster: `CheckFunction`, `RecvAt`,
  `checkContinuation(s)`, `checkDirect`, `checkPredecessor(s)`, `fromT`,
  `checkClosureSkip`, `checkClosure`, `checkWithFuel`, the old `check`,
  `checkClosed`, the `Maybe` `checkSession` (+ local `allParticipants`), and the
  `Maybe` `checkProcess`/`checkRootedProcess`/`checkSession`/`checkRootedSession`
  wrappers. **Kept**: the whole `Dec`/`Alg` layer, the `Incoming`/`findIncoming`
  decision, `SkipSem`/`theoremB`, and the `ProcessTyping`/`CheckedProcess`/
  `SessionTyping`/`CheckedSession` records (consumed by the new `Dec` wrappers).
  Deleted from `Complete.agda` the dead §5 cost block: `maxWithMem(-lb)`,
  `traceLen`, `cost`/`costSkip`, `cost-unskip<`, `costSkip<skip`,
  `cost-main<skip`, `costSkip-child<`.

**The `Maybe`→`Dec` conversion is complete.** `Definitions/TypeChecker/Complete.agda`
now exposes `checkD`/`checkClosedD`/`checkSessionD` (in `GraphComplete`) and the
bundled `checkProcessD`/`checkRootedProcessD`/`checkSessionWD`/`checkRootedSessionD`
returning genuine `Dec`s.

---

## Recurring gotchas
- `wt`/`Incl`/`mark`/`lookup`/`tabulate` are **non-injective**, so vector
  implicits (`{Ξ}`, `{left}`, `{right}`, `{v}`, `{X}`) must be pinned at call
  sites or Agda leaves unsolved metas.
- `Alg` must be a fuel-recursive function, not a datatype (strict positivity).
- Cost termination is fragile: `cost (conts …)` is accepted only when `conts`
  stays the clause's pattern variable — use `where`-local helpers, never a
  separate mutual function.
- In `Complete.agda`: `open Typing.MPST wb hiding (_,_)`; import Vec's `_∷_`/`[]`;
  qualify `BTheory._-<_>->_ (graphTheory G)`; `skip/step`'s target implicit is
  `{G' = …}` (ASCII apostrophe).
- The with-abstraction pitfall when coercing a `ktd`-child's mode to `prod`
  (the `ktd gr ≡ (m,d)` equation gets dropped, and `with … in eq` fails when a
  context variable like `prf` depends on `ktd gr`): solved by a `where`-helper
  `go (ktd gr) refl` typed `(kg : ∃ Mode …) → ktd gr ≡ kg → goal`.
