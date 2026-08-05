# ARCHIVED — 2026-07-25 — uniform trace judgement

> Historical record. Completed; `_-[_]->_` and `_-[¬_]->*_` in
> `Definitions/Behav.agda` are its result.

Status: **implemented and verified** (`LTS.agda`/`Safety.agda` compile clean, including
under `--no-allow-unsolved-metas`; `Definitions.agda` fails only via the pre-existing,
unrelated `Definitions/TypeChecker/Restricted.agda` scope error documented in §0/§8 —
confirmed unchanged before and after). See §9 for two implementation details that
diverged from the plan as written below.

Not to be confused with `skip-redesign.md` (a separate, already-completed redesign of the
`⊢skip` productivity judgment) or `TODO.md` (untouched, out of scope for this plan —
tracks the separate, ongoing `Definitions/TypeChecker/*` port).

## 0. Scope and hard constraints

- Touches: `Definitions/Behav.agda`, `Safety/Skip.agda`, `Safety/Head.agda`,
  `Safety/Preservation.agda`, `Safety/Termination.agda`, `LTS/Reachability.agda`.
- Explicitly **not** touched: everything under `Definitions/TypeChecker/`
  (`Core.agda`, `Restricted.agda`, `Complete.agda`, `Completeness.agda`, the new
  in-progress `Check.agda`) and `Definitions/TypeChecker.agda` itself. Confirmed by
  direct grep that these files pattern-match `in/α`/`in/later`/`skip/refl`/`skip/step`
  as literal Agda constructors (e.g. `Restricted.agda:145-146`, `Check.agda:132-138`,
  `Completeness.agda:304-310`) and call `skip/advance`/`branch/before`/`skip/cat`/
  `skip/∈T-back` directly (`Completeness.agda:340-381`). **Per explicit instruction,
  these files are expected to stop compiling as a result of this change, and that is
  acceptable — no attempt is made here to keep them green.** Their reconciliation is
  separate, future, out-of-scope work.
- **Baseline check (verified by actually invoking `agda -i .`, not just reading
  `.agdai` presence): most of this is already broken today, independent of this
  plan.** `Definitions/TypeChecker/Restricted.agda` currently fails with a scope
  error (`Core.agda` no longer exports `SemSkipP`/`SkipDecide`/`SkipSem`, which
  `Restricted.agda` still expects), which cascades to `Complete.agda` (parse error —
  `⊢skip[ prod ]` no longer exists), `Completeness.agda`, `Network.agda`,
  `Definitions/TypeChecker.agda`, and therefore the root `Definitions.agda`
  aggregator, plus everything under `Examples/`/`Tests/`. Only
  `Definitions/TypeChecker/Core.agda` and the new `Check.agda` (5 open `{!!}` goals,
  otherwise complete) currently compile. So of the three root files `runall.sh`
  iterates, **`LTS.agda` and `Safety.agda` are the live, currently-green baseline;
  `Definitions.agda` is already red today for reasons unrelated to this plan** — its
  continued failure after this change is not a regression to worry about. See §6
  step 7.
- `Definitions/Types.agda` (`BTheory.in/α`/`BTheory.in/later` at lines 409-410, 630,
  762-774) is **not imported by anything** — not even by the root `Definitions.agda`
  aggregator — and is not touched by `runall.sh` (which only iterates root `*.agda`
  files: `Definitions.agda`, `LTS.agda`, `Safety.agda`). It's orphaned in-progress
  front-end work per `CLAUDE.md`, and is confirmed *already broken standalone today*
  for an unrelated reason (a duplicate `Choice` definition clashing with
  `Definitions/Actions.agda`) — one more reason this file is a non-issue for this
  plan. Treat as informational only, not a required phase; fix it later only if/when
  it's wired back into the build.

## 1. Motivation

`Definitions/Behav.agda` currently has three independently-defined, structurally
similar pieces of machinery for reasoning about multi-step behaviour:

- `_-[¬_]->*_` (`skip/refl`/`skip/step`): "reachable via a sequence of steps none of
  which involve `P`".
- `_∈T_` (`in/α`/`in/later`): "`P` participates somewhere reachable".
- Several proofs (`skip/advance`, `branch/before`, `no-new-branch/skip`, and — outside
  `Behav.agda` — `leaf-from-∈T`/`leaf-or-∈T`, `head/if/etd-from-∈T-skip`,
  `head/rec/guarded-from-∈T-skip`, `comm/ready-from-∈T-skip`) hand-roll ad hoc
  "walk one edge at a time, decreasing on the witness" arguments over these two
  relations independently, with near-identical shapes duplicated across files.

Goal: introduce one primitive labelled-trace judgement `G -[ trace ]-> G′` (`trace : List
Action`) and define `_∈T_`/`_-[¬_]->*_` **as** existentials over it, so both concepts are
provably instances of "there is a trace such that ... `P` (not) in the trace" rather than
independently-axiomatised inductive families.

## 2. New core definitions — `Definitions/Behav.agda`

Add, inside `BTheory`, right after the `_-<_>->_` field (before the current
`_not-active-in_`/`_-[¬_]->*_`/`_∈T_` block, which this replaces):

```agda
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All

infix 4 _-[_]->_

data _-[_]->_ : Behav → List Action → Behav → Set where
  tr/refl :
    ∀ {G} → G -[ [] ]-> G

  tr/step :
    ∀ {G G′ G″ α αs}
    → G -< α >-> G′
    → G′ -[ αs ]-> G″
    → G -[ α ∷ αs ]-> G″

tr/trans :
  ∀ {G G′ G″ αs βs}
  → G -[ αs ]-> G′ → G′ -[ βs ]-> G″ → G -[ αs ++ βs ]-> G″
tr/trans tr/refl tr′        = tr′
tr/trans (tr/step gr tr) tr′ = tr/step gr (tr/trans tr tr′)
```

Then redefine (this is the actual, literal redefinition — no facade):

```agda
_∈T_ : Part → Behav → Set
P ∈T G = ∃[ αs ] ∃[ G′ ] (G -[ αs ]-> G′) × Any (P ∈α_) αs

_∉T_ : Part → Behav → Set
P ∉T G = ¬ P ∈T G

ended : Behav → Set
ended G = ∀ P → ¬ P ∈T G

_-[¬_]->*_ : Behav → Part → Behav → Set
G -[¬ P ]->* G′ = ∃[ αs ] (G -[ αs ]-> G′) × All (P ∉α_) αs
```

`_not-active-in_` is untouched (doesn't mention either relation).

**On helper functions — no "smart constructors" as a policy.** The earlier draft of
this plan introduced `in/α`/`in/later`/`skip/refl`/`skip/step` purely to mirror the old
constructor names/types for compatibility. That reasoning no longer applies —
TypeChecker-compat is explicitly not a goal (§0) — so it's the wrong justification and
is dropped. Instead, judge each helper on its own merits: write the raw tuple directly
wherever it's just as legible, and only name a helper where it does real work or is
reused often enough that inlining it would be noise. Concretely, `skip/one`/`skip/cat`
clearly earn their keep (they compose two proof steps, not just repackage one):

```agda
skip/refl : ∀ {G P} → G -[¬ P ]->* G
skip/refl = [] , tr/refl , []

skip/step :
  ∀ {G G′ G″ P α}
  → G -< α >-> G′ → P ∉α α → G′ -[¬ P ]->* G″ → G -[¬ P ]->* G″
skip/step gr P∉α (αs , tr , allP) = _ ∷ αs , tr/step gr tr , P∉α ∷ allP

skip/one : ∀ {G G′ P α} → G -< α >-> G′ → P ∉α α → G -[¬ P ]->* G′
skip/one gr P∉α = skip/step gr P∉α skip/refl

skip/cat :
  ∀ {G G′ G″ P} → G -[¬ P ]->* G′ → G′ -[¬ P ]->* G″ → G -[¬ P ]->* G″
skip/cat (αs , tr , allP) (βs , tr′ , allP′) =
  αs ++ βs , tr/trans tr tr′ , All.++⁺ allP allP′

in/α : ∀ {P G G′ α} → G -< α >-> G′ → P ∈α α → P ∈T G
in/α gr px = _ ∷ [] , _ , tr/step gr tr/refl , here px

in/later : ∀ {P G G′ α} → G -< α >-> G′ → P ∈T G′ → P ∈T G
in/later gr (αs , G″ , tr , mem) = _ ∷ αs , G″ , tr/step gr tr , there mem

in/send : ∀ {G α G′} → G -< α >-> G′ → sender α ∈T G
in/send gr = in/α gr (∈S refl)

in/recv : ∀ {G α G′} → G -< α >-> G′ → receiver α ∈T G
in/recv gr = in/α gr (∈R refl)
```

`skip/refl`/`skip/step`/`in/α`/`in/later` are kept here too, but on their actual
merits: each is called at ≥5 sites in the surviving (non-`TypeChecker`) call sites
inventoried in §3/§8, and `in/send gr` reads better than an inlined 4-tuple at every
one of them. The distinction from the rejected "smart constructor" framing is real,
not cosmetic: these survive because they pull their weight as ordinary reusable
one-liners, not because their names happen to match a deleted constructor — if a
future site only needs one of these once, write the tuple inline there instead of
reaching for the helper. `skip/cat` needs
`Data.List.Relation.Unary.All.Properties`'s `++⁺` (list-append lemma for `All`) —
check it exists under that name in stdlib 2.2; a two-line manual induction on `allP`
is an easy fallback if not.

`_-[¬_]->*_` was previously `data _-[¬_]->*_ (G : Behav) (P : Part) : Behav → Set`
(curried), now a function `Behav → Part → Behav → Set` — same infix notation
`G -[¬ P ]->* G′` at every use site either way.

**The actual payoff of the trace representation — two generic transport lemmas.**
`_∈T_` and `_-[¬_]->*_` both pair a run (`_-[_]->_`, which threads through `Behav`
states) with a property of the trace's *labels alone* (`Any`/`All` over `List Action`
— neither ever mentions `Behav`). That decoupling is the whole point: bisimulation
transport for both relations reduces to transporting the run and reusing the
label-level witness completely unchanged, because `Any`/`All` don't care which states
the run passed through, only which actions it took. Concretely: **if `G ~ G′`, then
`G` and `G′` accept exactly the same traces** (up to relabelling the endpoint via
`~`) — one proof of that fact, not one per relation, is the actual uniform-trace
payoff. Two directions, mirroring the two existing single-step lemmas they generalize:

Forward (generalizes `~L`; `BTheory`-level, needs no `WellBehaved` axiom):
```agda
tr-transport :
  ∀ {G G′ H αs}
  → G ~ G′
  → G -[ αs ]-> H
  → ∃[ H′ ] (G′ -[ αs ]-> H′) × (H ~ H′)
tr-transport G~G′ tr/refl =
  _ , tr/refl , G~G′
tr-transport G~G′ (tr/step gr tr) =
  let _ , gr′ , G″~G‴ = ~L G~G′ gr
      _ , tr′ , H~H′  = tr-transport G″~G‴ tr
  in _ , tr/step gr′ tr′ , H~H′
```

Backward (generalizes the `WellBehaved` axiom `stepback/~`; lives in `WellBehaved`'s
derived-lemma section, alongside `skip/advance`, since it needs that axiom):
```agda
stepback/~* :
  ∀ {αs G₀ G₁ G₁′}
  → G₁ ~ G₁′
  → G₀ -[ αs ]-> G₁
  → ∃[ G₀′ ] (G₀ ~ G₀′) × (G₀′ -[ αs ]-> G₁′)
stepback/~* G₁~G₁′ tr/refl =
  _ , G₁~G₁′ , tr/refl
stepback/~* G₁~G₁′ (tr/step gr tr) =
  let _ , H~H′ , tr′   = stepback/~* G₁~G₁′ tr
      _ , G₀~G₀′ , gr′ = stepback/~ H~H′ gr
  in _ , G₀~G₀′ , tr/step gr′ tr′
```

Every bisimulation-transport lemma over `_∈T_`/`_-[¬_]->*_` elsewhere in the codebase
(`∈~`, `skip/bisim`, `skip/bisim-back`) is now a two-to-three line call into one of
these two plus reusing the membership/exclusion witness verbatim, instead of a bespoke
recursive walk re-deriving the same transport logic — see §4.

Overload note: `_&_⊢skip_∶_` in `Definitions/Typing.agda` independently declares its
own `skip/main`/`skip/step`/`skip/cycle` constructors, and Agda already disambiguates
the resulting `skip/step` name overload (BTheory's vs `⊢skip`'s) by expected type at
each use — this already happens today and needs no attention; it keeps working
identically since the `skip/step` helper above has the exact same type signature as
the constructor it replaces.

## 3. Sites that need real rewriting vs. sites that don't

Because construction (`in/α gr px`, `in/later gr rest`, `skip/refl`, `skip/step gr na
tr`) stays ordinary function application, **only sites that pattern-match directly on
a value of type `P ∈T G` or `G -[¬ P ]->* G′` in a clause head / `with` need surgery.**
Everything that merely calls `skip/advance`, `branch/before`, `skip/cat`,
`skip/∈T-back`, `∈~`, `in/send`, `in/recv`, etc. as an opaque function is unaffected,
because those functions' *type signatures* don't change, only their internal proof.
Verified by re-reading every file that mentions these identifiers (confirmed by grep
to be exhaustive, `Definitions/TypeChecker/*` excluded).

Among the sites needing surgery, two genuinely different shapes emerge, with very
different effort/risk:

- **Bisimulation transport** (`∈~`, `skip/bisim`, `skip/bisim-back`, and
  `skip/∈T-back`, which is trace-concatenation rather than transport but has the same
  "membership witness rides along unchanged" character): collapse to 2-3 line calls
  into `tr-transport`/`stepback/~*`/`tr/trans` (§2), *not* bespoke recursive walks.
  Low risk, low effort.
- **Genuine progress-making walks** (`skip/advance`, `no-new-branch/skip`,
  `leaf-from-∈T`, `head/if/etd-from-∈T-skip`, `head/rec/guarded-from-∈T-skip`,
  `comm/ready-from-∈T-skip`, `∈T→reach`): these consume the *head* of a trace/witness
  to make structural progress (diamond commutation, or ruling out `here` via `na`),
  not just relabel states along an existing run — no shortcut, still need direct
  `with`/tuple decomposition per §4's worked pattern.

| File | Trivial via transport lemmas | Needs genuine decomposition | Everything else in the file |
|---|---|---|---|
| `Definitions/Behav.agda` | `skip/∈T-back`, `∈~` | `skip/advance`, `no-new-branch/skip` | `branch/before` only calls the two decomposition-needing ones — no direct pattern match, unaffected |
| `Safety/Skip.agda` | `skip/bisim` | — | all `skip-td/bisim`/`skip-leaf/bisim`/etc. pattern-match `⊢skip`'s *own* constructors (a different, untouched datatype) and thread `inT`/`eq` through unchanged |
| `Safety/Head.agda` | `skip/bisim-back` | `leaf-from-∈T`, `cancel/unskip` (1st argument only), `head/if/etd-from-∈T-skip` | `leaf-or-∈T`, `td/head`, `mainLeaf/head`, `head/if/split`, `head/if/inv`, `t/if/inv` only construct or call opaquely |
| `Safety/Preservation.agda` | — | `comm/ready-from-∈T-skip` | `comm/ready-or-∈T`, `comm/ready`, `send/cont-skip`, `recv/cont-skip` pattern-match `⊢skip`/`⊢hskip` only, or construct `in/later` |
| `Safety/Termination.agda` | — | `head/rec/guarded-from-∈T-skip` | `head/rec/guarded-skip`, `rec/guarded` unaffected (⊢skip-level / opaque calls) |
| `LTS/Reachability.agda` | — | `∈T→reach` | `reach→∈T`/`∈T?` only construct (`in/later`, `activeToStep` — confirmed, §6 step 6) |
| `Definitions/Typing.agda` | — | — | `_∈T_`/`_-[¬_]->*_` appear only as field types (`skip/cycle`'s `inT`, `t/unskip`'s `tr`, `t/end`'s `done`); `hskip/typing`/`main-leaf-accessible` pattern-match `⊢skip`'s own constructors and thread the fields through unchanged |
| `Safety/Progress.agda` | — | — | everything constructs (`in/send`/`in/recv`/`in/later`) or uses `_∈T_`/`_∉T_` opaquely (`P ∉G (in/send gr)`, `subst (λ Q → Q ∈T _) ...`) |
| `Typing/Substitution.agda` | — | — | every `skip/*-expr`/`skip/*-proc` clause threads `inT`/`eq`/`tr` through unchanged, matching only `⊢skip`'s own constructors |

So the real work is **~12 functions across 6 files**, of which **4 are near-trivial**
(`skip/∈T-back`, `∈~`, `skip/bisim`, `skip/bisim-back`) and **~8 need the genuine
walk-decomposition treatment** — not a rewrite of every call site either way.

## 4. Rewrite patterns (worked examples)

### 4a. Bisimulation-transport sites — reuse §2's generic lemmas

Before (`Definitions/Behav.agda`, current — a bespoke recursive walk mixing state
transport and membership-witness transport at every step):
```agda
∈~ : ∀ {P G G′} → G ~ G′ → P ∈T G → P ∈T G′
∈~ G~G′ (in/α gr P∈α) =
  in/α (~L→ G~G′ gr) P∈α
∈~ G~G′ (in/later gr P∈G″) =
  in/later (~L→ G~G′ gr) (∈~ (~L→~ G~G′ gr) P∈G″)
```

After — transport the run via `tr-transport`, reuse `mem` verbatim (it's a fact about
`αs` alone, untouched by which states the run passes through):
```agda
∈~ : ∀ {P G G′} → G ~ G′ → P ∈T G → P ∈T G′
∈~ G~G′ (αs , H , tr , mem) =
  let H′ , tr′ , _ = tr-transport G~G′ tr
  in αs , H′ , tr′ , mem
```

`skip/bisim-back` (`Safety/Head.agda`) is the same shape, one `~sym` away (it
transports a trace *from* `G′` using `G ~ G′`, i.e. the mirror direction):
```agda
skip/bisim-back : ∀ {G G′ H′ P} → G ~ G′ → G′ -[¬ P ]->* H′ → ∃[ H ] (G -[¬ P ]->* H) × (H ~ H′)
skip/bisim-back G~G′ (αs , tr , allP) =
  let H , tr′ , H′~H = tr-transport (~sym G~G′) tr
  in H , (αs , tr′ , allP) , ~sym H′~H
```

`skip/bisim` (`Safety/Skip.agda`) needs the *backward* direction instead (it relates
the trace's target to `H`, and must produce a new source bisimilar to `G`), so it
calls `stepback/~*`:
```agda
skip/bisim : ∀ {G G′ H P} → G′ ~ H → G -[¬ P ]->* G′ → ∃[ H₀ ] (G ~ H₀) × (H₀ -[¬ P ]->* H)
skip/bisim G′~H (αs , tr , allP) =
  let H₀ , G~H₀ , tr′ = stepback/~* G′~H tr
  in H₀ , G~H₀ , (αs , tr′ , allP)
```

`skip/∈T-back` isn't a bisimulation transport at all — it's trace *concatenation* —
but has the same "membership witness doesn't care about states" character, so it
similarly collapses to `tr/trans` plus lifting `mem` across the list append (stdlib's
`Any.++⁺ʳ`, to confirm exact name — §7):
```agda
skip/∈T-back : ∀ {G G′ P Q} → G -[¬ P ]->* G′ → Q ∈T G′ → Q ∈T G
skip/∈T-back (αs , tr , _) (βs , H , tr′ , mem) =
  αs ++ βs , H , tr/trans tr tr′ , Any.++⁺ʳ αs mem
```

All four are now 2-3 lines with no recursion of their own — the recursion lives once,
in `tr-transport`/`stepback/~*`/`tr/trans`.

### 4b. Genuine-decomposition sites — direct `with`/tuple pattern matching

The remaining ~8 functions (`skip/advance`, `no-new-branch/skip`, `leaf-from-∈T`,
`head/if/etd-from-∈T-skip`, `head/rec/guarded-from-∈T-skip`,
`comm/ready-from-∈T-skip`, `∈T→reach`, plus `cancel/unskip`'s first argument) don't fit
this shortcut: each one *consumes* the head of a trace/membership witness to make
progress (diamond-commute an independent step, or rule out `here` via `na`/rule out an
edge via reachability), not just relabel states along an already-complete run. These
need a direct `with`/tuple decomposition of the Σ-type, structurally recursing on the
extracted trace/witness — the same idiom `Safety/Skip.agda`'s existing `lookup/insert`
already uses successfully today for an anonymous `∃[X] lu (...) X ~ G` argument (lines
24-45), so this is not a novel pattern for Agda's termination checker in this
codebase. E.g. `leaf-from-∈T`'s middle two clauses become:

```agda
leaf-from-∈T leaf-bisim (skip/step gr na ktd) (α ∷ αs , H , tr/step gr' tr , here px) =
  ⊥-elim (∉c→¬∈c (na gr') px)
leaf-from-∈T leaf-bisim std@(skip/step gr na ktd) (α ∷ αs , H , tr/step gr' tr , there mem) =
  leaf-from-∈T leaf-bisim
    (skip/unfold-cycle {Ξ = []} {Ξ′ = []} leaf-bisim std (ktd gr'))
    (αs , H , tr , mem)
```

`skip/advance` follows the same recipe (decompose its first argument's `(αs, tr,
allP)` instead of matching `skip/refl`/`skip/step`); the diamond/step-determinism
logic in the body is untouched, only the clause heads change shape. The
two-participant site (`comm/ready-from-∈T-skip`) and the other walk-and-fold sites
need the identical clause-head treatment on their `P ∈T G` argument; their bodies
(which call `skip/unfold-cycle`, `no-new-comm/step`, etc.) are otherwise untouched
since those callees' signatures don't change.

## 5. Optional follow-on cleanup (do only after §2-4 are green)

`leaf-or-∈T`+`leaf-from-∈T` (`Safety/Head.agda`) is already generic in `Leaf`. Once
rewritten, `head/if/etd-from-∈T-skip`/`head/if/etd-from-∈T` (`Safety/Head.agda`) and
`head/rec/guarded-from-∈T-skip`/`head/rec/guarded-from-∈T` (`Safety/Termination.agda`)
are, on inspection, literal specializations of it at `Leaf = ⊢head` followed by a
trivial case-specific inversion (`h/if`'s `etd` field / `h/rec`'s `MessageGuarded`
field) — their clause-by-clause structure is otherwise byte-for-byte identical to
`leaf-from-∈T`'s. Once all three are rewritten in the new trace-based shape, consider
collapsing them into one shared generic combinator (`leaf-from-skip` composed with a
per-case final extraction), removing the duplication. This is genuine "any other
argument that boils down to traces" cleanup, but is separable, lower-risk, optional
work — do it as a second pass, not bundled with §2-4. `comm/ready-from-∈T-skip`
(two-participant) is a related but structurally distinct case (carries Q's tree in
lockstep) — a stretch goal, not required.

## 6. Implementation order

1. `Definitions/Behav.agda`: add `_-[_]->_`/`tr/trans`, redefine `_∈T_`/
   `_-[¬_]->*_`/`ended`/`_∉T_`, add the helper functions from §2 (only where they
   genuinely earn their place, not as blanket compatibility shims), add
   `tr-transport` (`BTheory`-level) and `stepback/~*` (`WellBehaved`-level), rewrite
   `skip/∈T-back` and `∈~` via §4a, `skip/advance` and `no-new-branch/skip` via §4b.
   Typecheck this file in isolation (`agda Definitions/Behav.agda`) before moving on —
   everything downstream depends on it compiling first.
2. `Safety/Skip.agda`: rewrite `skip/bisim` via `stepback/~*` (§4a).
3. `Safety/Head.agda`: rewrite `skip/bisim-back` via `tr-transport` (§4a);
   `leaf-from-∈T`, `cancel/unskip`, `head/if/etd-from-∈T-skip` via §4b.
4. `Safety/Preservation.agda`: rewrite `comm/ready-from-∈T-skip`.
5. `Safety/Termination.agda`: rewrite `head/rec/guarded-from-∈T-skip`.
6. `LTS/Reachability.agda`: rewrite `∈T→reach` only. `activeToStep`/`reach→∈T`
   confirmed (by direct `agda -i .` check, not just grep) to only *construct*
   `in/α`/`in/later` via smart-constructor application — no rewrite needed there.
7. `./runall.sh` from repo root. Baseline (verified today, before any change):
   `LTS.agda` and `Safety.agda` compile clean; `Definitions.agda` already fails
   (pre-existing, unrelated — see §0). The bar to hit is therefore: **`LTS.agda` and
   `Safety.agda` still compile clean after this change.** `Definitions.agda` will
   continue to fail (now for an additional reason — `Definitions/TypeChecker.agda`
   breaking against the new `_∈T_`/`_-[¬_]->*_` shape, on top of its pre-existing
   `Restricted.agda` scope error) — that's expected per §0, not a new regression to
   chase.
8. (Optional, separate pass) §5's dedup cleanup.
9. (Separate, future, out of scope here) reconcile `Definitions/TypeChecker/*` with
   the new shape — tracked wherever the ongoing TypeChecker work already lives, not by
   this plan.

## 7. Open items to verify while implementing (not yet confirmed)

- Exact stdlib 2.2 names/availability of `All.++⁺` (list-append lemma for `All`, used
  by `skip/cat`) and `Any.++⁺ʳ` (list-append lemma for `Any`, used by `skip/∈T-back`);
  trivial manual fallbacks by induction if either name differs.
- After step 1 typechecks, re-derive `skip/advance`'s and `no-new-branch/skip`'s exact
  rewritten bodies against the real file (the shapes are mechanical per §4b, but write
  them against the live diamond/step-determinism lemmas rather than blind transcription).

## 8. Cross-check against an independent survey agent

A separate research pass (full `agda -i .` invocation, not just grep) confirmed the
file/function inventory in §3 and additionally found:

- Three distinct families share the token `skip/step` in this codebase: `Behav.agda`'s
  `_-[¬_]->*_` (in scope here), `Definitions/Typing.agda`'s `_&_⊢skip_∶_` process-typing
  judgement (untouched, different datatype, already handles the name overload today —
  see §2's overload note), and a third, 4-arg mode-annotated variant in
  `Definitions/TypeChecker/Complete.agda` (already non-compiling, irrelevant).
  `Safety/Head.agda`'s `cancel/unskip` is the one place that pattern-matches the first
  two *jointly* in the same clauses — confirmed already in §3's table.
- `Definitions/TypeChecker/Check.agda:132-138` (`find-leaf/remember`) is the one
  currently-*live* TypeChecker site with a direct `in/α`/`in/later` pattern match, so
  it's the concrete place that will visibly break, on top of the already-broken
  `Restricted.agda`/`Complete.agda`/`Completeness.agda`/`Network.agda`.
- No changes needed to §3's table as a result — it independently arrived at the same
  6-file, ~12-function list, modulo the `activeToStep` resolution folded into §6 step 6
  above.

## 9. Two things the written plan above got slightly wrong, found during implementation

- **`skip/step` name clash.** §2's overload note claimed Agda "already disambiguates"
  BTheory's `skip/step` against `Definitions/Typing.agda`'s `⊢skip`'s own `skip/step`
  "and needs no attention." Wrong: Agda supports overloading between two *data
  constructors* of that name, which is what made the old codebase's two `skip/step`s
  coexist — but once BTheory's `_-[¬_]->*_` stopped being a `data` type, its `skip/step`
  became an ordinary *function*, and a plain function can't share a name with a
  freshly-declared constructor in the same scope (`Definitions/Typing.agda` failed to
  scope-check: "Multiple definitions of skip/step"). Fixed by renaming the
  `BTheory`-level helper to `tr¬/step` (kept `skip/refl`, which never clashed — `⊢skip`
  has no constructor by that name). This has zero blast radius beyond
  `Definitions/Behav.agda` itself, since none of the planned rewrites in the other 5
  files ended up needing to *name* the BTheory-level constructor directly — they all
  decompose the Σ-type positionally instead.
- **Termination checker rejects recursion on a freshly re-packed tuple.** §4b's worked
  example recurses on `(αs, tr, allP)`-shaped tuples reconstructed from separately
  pattern-matched pieces. This works fine when the pieces come from decomposing a
  *single* prior argument in one step (`leaf-from-∈T`, `comm/ready-from-∈T-skip`,
  `head/if/etd-from-∈T-skip`, `head/rec/guarded-from-∈T-skip`, `∈T→reach` — all
  compiled as planned), but fails when three *independently, simultaneously* matched
  sub-patterns (a list cons, a `tr/step`, an `All` cons) get re-packed together in one
  call: `skip/advance`, `no-new-branch/skip`, and `cancel/unskip` all hit "Termination
  checking failed." Fixed by splitting each into a `-aux` helper that takes the run
  (`_-[_]->_`) as its own curried argument — never re-packed into a tuple at the
  recursive call — with the `All`-witness threaded alongside as a second curried
  argument; the public-facing function just unpacks its Σ-argument once and delegates.
  This is a stricter version of the `lookup/insert` precedent §4b cited: recursing on a
  *directly extracted* subterm is fine (as most of §4b's sites confirm), recursing on a
  freshly-reconstructed multi-piece tuple is not.
