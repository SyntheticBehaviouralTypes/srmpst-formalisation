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
  delete once Phase C compiles.

## Remaining work (v2 phases; do in this order)

- **Phase S** — `Saturate.agda`: `J Pr`, `J+size≡F`, `It`/`It?`/`It-mono`,
  `findStab` pigeonhole (build/fresh-style fuel-with-invariant), `It→Alg`,
  mutual `sat`/`algk→It`/`directSat`/`satBr`. Independent of everything else.
- **Phase T** — transport pack in `Complete.agda`: `pathViaP-pull`,
  `pathVia-push`, `na-~`, `semSkipP-bisim`, `hml-bisim`, `weakenTo`.
- **Phase A** — Theorem A: `AncL`/`ancLookup`, the walk (structural on path,
  `~`-jump via `weakenTo` + `skip-td/bisim` + `hml-bisim`), `theoremA`.
- **Phase C** — `complete`/`completeLeaf`/`pred-fold`/`complete₀`.
- **Phase F** — `check : Dec (⊢p)`, session `Dec`, `typing-wb-irrelevant`,
  delete `Maybe` cluster + dead cost block.

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
