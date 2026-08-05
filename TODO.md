# Deciding the algorithmic judgment `⊢a` — execution plan

## HOW TO RESUME (read this first)

This file is the handoff. If you have no context: read this section, then
"Philosophy", then "Acceptance criterion", then the numbered step you are on.
Everything below is written to be actionable cold.

**THIS PLAN IS DONE (2026-08-05).** All six steps are complete and
`./runall.sh --tests` is green on every root and every test, with no file
reporting holes and no `postulate` anywhere under `Check/`.

**The dead-code cull that followed is also done** — see "Cleanup" below.

**WHAT TO DO NEXT, in the owner's stated priority order:**

1. ~~Migrate `Safety/*` from `⊢head` to `⊢a`, then delete `⊢head`.~~
   **DONE 2026-08-05** — see the section below.
2. **Make type checking net-native.** THIS IS NOW THE TOP ITEM. State
   explosion, not well-behavedness compositionality, is the real problem —
   see "The actual problem with nets".

The plan this replaces is archived at
`docs/2026-08-04-DONE-algorithmic-normalisation.md` — read its header box
(not the body) for the list of statements that are **proved false** and must
not be resurrected.

**What is already done and must not be re-litigated:**

| file | state |
|---|---|
| `Definitions/Typing/Algorithmic.agda` | `⊢a`, `⊢blocked`, `alg/typing : ⊢a → ⊢p`. Hole-free. |
| `Definitions/Typing/Norm.agda` | `norm : ⊢p → trace → ⊢a`. Hole-free. |
| `Check/Core.agda` | the graph-level decision helpers. Compiles. |
| `Check/Alg.agda` | **the new checker.** Decides `⊢a` and, through it, `⊢p`. Hole-free, termination-checked, ~13 s. |
| `Check/Graph.agda` | `WBGraph`/`buildG`/`wb-of`/`typecheck`/`typecheckSession`, restored over `Check/Alg`. |
| `Check/Network.agda` | `WBNet`/`netWB`/`wb-net` **plus** the two API wrappers, restored. |
| `Check.agda` | aggregator; the drop-in replacement for the deleted `Definitions/TypeChecker.agda`. |
| `Tests/AlgCheck.agda` | forces the checker on real graphs; `Ex6` included (see below). |
| `Check/Decide.agda` | **DELETED.** Superseded in full and unreferenced. |

**Files allowed to be red:** none.

**How to verify state:** `agda --guardedness <the file you touched>`. Do NOT
run `./runall.sh` unless finishing a step or explicitly asked — it rechecks
every root and proves nothing about a one-file change.

### Why `Check/Alg.agda` is a new file and not more of `Check/Decide.agda`

`Check/Decide.agda` has open interaction metas, so Agda writes no interface
for it and every edit re-checks it from source (~90 s a round trip).
`Check/Alg.agda` is ~13 s. It carries its own copy of `size/proc`,
`remaining`/`mark`/`mark-decreases` and the `×-Lex` measure — which
`Check/Decide.agda`'s own "Refactor TODO" comment already says belong in a
module of their own. Nothing else of that file was needed: in particular
`step-predecessors` is NOT used, because the backward anchor search is a
`reach¬P?` query per candidate rather than a predecessor enumeration.

### The one design decision that is not in the plan below

The forward search is split by **regime**, on `∈T? P s`:

* `P ∈T s` (`treeA?`) — `skip/cycle` is available, so a literal revisit
  closes the tree and no refutation is ever needed at a revisit. The
  negative is built compositionally, with no table.
* `¬ P ∈T s` (`treeB?`) — the region is closed under successors and
  `skip/cycle` is unusable there, so the problem stops depending on `Ξ`.
  This is the *only* place a revisit has to be answered "no", and refuting
  it needs the whole exploration rather than the current path. That is what
  `Justified`/`FailedFrom`/`failed⇒¬tree` in `Check/Alg.agda` are: a
  post-fixed point of the failure operator, with deferred entries for the
  states still on the DFS stack, discharged by each frame as it unwinds.
  `failed⇒¬tree` then refutes by plain structural recursion on the tree.
  This is the old file's second postulate, discharged.

The measure is four components, `(size/proc Pr , regime , remaining v ,
phase)`. The phase exists purely for Agda's termination checker — see the
long comment at `Measure` in `Check/Alg.agda` before changing it.

---

## Philosophy

### What `Check/Decide.agda` does today, and why it is hard

`tcGraph` decides the **declarative** judgment `Γ & Δ ⊢p P ◂ Pr ∶ s` directly.
Two design commitments, both good, and both to be kept:

1. **No auxiliary shape-restricted relation.** Every `yes` *is* a
   `t/send`/`t/recv`/…/`t/skip` term, built on the spot. Soundness is the
   constructor discipline, not a theorem to prove afterwards.
2. **Completeness proved separately, before the decision function, never
   mentioning it.** A `Dec`-valued function's own "no" branch cannot refer to
   its own `Dec` value and rely on Agda unfolding it. So "no" branches
   contradict a small per-constructor tuple (`MatchOf`) or a raw `⊢skip`
   witness against already-`with`-bound local negatives.

The pain is **not** in either of those. It is that `⊢p` is not syntax-directed:
`t/skip` and `t/unskip` may be applied at *any* point, so a `no` must rule out
every state at which the derivation could have been anchored. That single fact
is the origin of essentially all the machinery in the file —
`Table`, `Covers`, `DirectCovered`, `mark`/`remaining`, `step-predecessors`,
the `rec-unskip` worklist, the lexicographic `_≺_` on
`(size/proc Pr , remaining marks)`, `leaf-permute`, `permute-tree`, and both
remaining postulates.

### Why deciding `⊢a` instead is the whole point

`⊢a` was built precisely to remove that. It has **one constructor per process
form**:

| process | `⊢a` form |
|---|---|
| `∅` | `a/end` |
| `ifp E then _ else _` | `a/if` |
| send / recv / `v` / `rec` | `a/skip` of a `⊢blocked`-leaf skip tree |

There is no floating `t/unskip`: the unskips survive only *inside* the leaves,
as `blocked/var`'s and `blocked/rec`'s traces. So the anchor is never in
question — it is whatever the leaf says it is.

**Consequence: the entire worklist/`Covers`/`Table` apparatus should
disappear**, and with it the four current holes and both postulates. That is
the payoff this plan is cashing in.

Deciding `⊢p` then comes for free, and should be the *last* step, not the
first:

```agda
tc? : Dec (Γ & Δ ⊢p P ◂ Pr ∶ s)
tc? = map′ alg/typing (λ ¬a p → ¬a (norm p skip/refl)) alg?
```

`alg/typing` is the soundness half (already proved) and `norm` is the
completeness half (already proved, hole-free). **Do not write a bespoke
completeness argument for `⊢p` again.**

### The one genuinely new decision problem

`blocked/rec` carries an **existential over the anchor**:

```agda
blocked/rec : W -[¬ P ]->* L → MessageGuarded Pr
            → Γ & (W ∷ Δ) ⊢a P ◂ Pr ∶ W
            → Γ & Δ ⊢blocked P ◂ rec Pr ∶ L
```

Deciding it means searching for a `W` that `¬P`-reaches `L` and at which the
body types. This is decidable because `State G` is finite, but it is a real
search and it is where the difficulty has moved to. Note it is *bounded and
local* — a finite set of candidate `W`, each with a decidable reachability
query — which is categorically easier than the old "rule out every anchor
everywhere" obligation. **Do not** try to avoid the search by picking a
canonical `W`: that is the anchor-moving idea, and it is refuted
(archived plan, §5e; `Stale/PushRecDerivations.agda.stale`, `Ex6`).

### The search space: FORWARD AND BACKWARD

Allowing a skip in front of a `rec` means the search cannot be forward-only.
`a/skip` walks `¬P`-**successors**; `blocked/rec`'s trace `W -[¬ P ]->* L`
points at a **predecessor** whose identity is *not given*. So for `rec` the
space to explore is the whole `¬P`-**connected component** of the current
state — every state joined to it by a `¬P` transition in *either* direction —
not the forward `¬P`-reachable set. `Check/Decide.agda` already has
`step-predecessors` for the backward direction; that helper survives even
though the worklist around it does not.

**`blocked/var` is NOT part of this, and must not be implemented as a search.**
Its source is `lu Δ X`, which is *known*, so it is one reachability query from
a fixed state followed by one bisimilarity test against the current one —
`reachVia?` then `bisim?~`, no exploration. (That is precisely why the rule is
oriented reach-then-`~` rather than `~`-then-reach: it puts the known state on
the left.) The genuinely unknown anchor occurs only in `blocked/rec`.

What a successful search can reconstruct, and at what cost:

| shape | direction | cost |
|---|---|---|
| `blocked/var` | backward, source **known** | one reachability query + one `~` test. No search. |
| skip tree (`a/skip`) | forward | **∀** successors typeable — exhaustive forward walk |
| `blocked/rec` | backward, source **unknown** | **∃** a past state typing the body — the only real search |
| both | forward then backward | **∀** future states, **∃** a past state for each |

The last row is not hypothetical: it is exactly `Ex6` in
`Stale/PushRecDerivations.agda.stale`, and it is why the forward walk and the
`rec` anchor search cannot be separated into independent passes. Together they
are **exhaustive and mutually recursive**, and the ∀/∃ alternation must be
reflected in the shape of the negatives — an `All`-shaped refutation for the
forward direction, an `Any`-shaped one for `rec`'s backward one. `var` needs
neither; its negative is just the two decisions failing.

### The well-founded measure

Primary candidate, lexicographic, largest component first:

```
(size/proc Pr , remaining visited)
```

exactly as `Check/Decide.agda` uses today (`_≺_`, `×-Lex`, `×-wellFounded`).
Why each component moves:

- `size/proc Pr` **strictly decreases** whenever the search goes under an
  action (`blocked/send`/`blocked/recv` continuations), into an `if` branch,
  or into a `rec` body. It never increases.
- `remaining visited` **strictly decreases** on every `skip/step` of the tree
  search, because the current state is marked before recursing. It is what
  makes the forward walk terminate, and it is why `skip/cycle` needs the
  visited set at all.
- The **backward** anchor enumeration needs no measure component: it is a
  plain structural fold over a finite `List (State G)`, and the body decision
  it launches sits at a strictly smaller `size/proc`.

Consequently the visited set may be **reset** whenever `size/proc` drops —
that is sound and is what lets each leaf's continuation start a fresh walk.
Check this before writing code: if a recursion is found that decreases
neither component, the measure is wrong, and the fix is more likely a third
component (candidate-list length) than a cleverer encoding.

---

## Steps

Steps 0–4 below are recorded as originally written; the tick boxes say what
actually happened. Read Steps 5 and 6 for what is left.

- [x] **Step 0 — inventory the helpers, write nothing.** Confirm what
      `Check/Core.agda`'s `GraphChecker` already gives:
      `messageGuarded?`, `findStep`, `findRecv`/`matchRecv?`/`RecvWitness`,
      `na?`, `bisim?~`; and from `Definitions/Graph/Reachability`:
      `reachVia?`, `∈T?`, `PathVia`. Write a short list at the top of the new
      module of what is missing. Expected gaps: a decision for
      `∃[ W ] W -[¬ P ]->* L` **enumerated** (not just `reachVia?` for a fixed
      pair), and the `⊢skip`-tree search itself.

- [x] **Step 1 — decide `⊢blocked` at a FIXED state, for each leaf form.**
      Four independent, local decisions. None needs a search over states except
      the last.
      - [x] `blocked/send` — `findStep` for `P ⟶ Q # i < S >`, `checkExpression`,
            then recurse into `⊢a` at the target.
            (`findStep` needed the sort read off the graph rather than given,
            hence `findSendStep`; the refutation uses
            `step-sort-deterministic` then `step-deterministic`.)
      - [x] `blocked/recv` — `matchRecv?`/`RecvWitness` for the branch family,
            then recurse per branch.
            (As an `All (RecvCont …) (edges G s)`, so `conts` is
            `All.lookup … ∘ step⇒listed` and its negative `All.tabulate`.)
      - [x] `blocked/var` — `reachVia?` from `lu Δ X`, then `bisim?~` against
            the current state. This is exactly why `blocked/var` is oriented
            reach-then-`~`: the *known* state is on the left, so it is one
            reachability fixed point followed by one bisimilarity test.
      - [x] `blocked/rec` — **the backward search.** Enumerate candidate
            anchors `W` (all of `State G`, or the `¬P`-connected component if
            that is cheaper to build), keep those with `W -[¬ P ]->* L`, and
            for each decide the body at `W` anchored `W`. This is an **∃**:
            yes on the first hit, and `no` must refute *all* candidates, so
            the enumeration is a structural fold over a finite list producing
            an `All`-shaped negative. `size/proc` drops entering the body, so
            this needs no measure component of its own.
            (Done as `FinP.any?` over all of `State G` with
            `reach¬P? P W s ×-dec alg? …`; the `All`-shaped negative is
            `any?`'s own. No worklist, no `step-predecessors`.)

- [x] **Step 2 — decide the `⊢skip` tree (the forward search).** Given `P`, a
      process `Pr` and a root `G`, decide
      `(Γ & Δ ⊢blocked_∶_) & [] ⊢skip P ◂ Pr ∶ G`. Shape of the search,
      mirroring the judgment:
      - at each state, first try `⊢blocked` (Step 1) → `skip/main`;
      - else require `na?` and recurse on **every** successor → `skip/step`.
        This is the **∀** half: `ktd` must be produced for all successors, so
        the recursion is over the adjacency list and the negative is
        per-successor (`Any` over the successors refutes the whole tree);
      - else, if the state is `~` to one already visited and `∈T?` holds →
        `skip/cycle`.

      Termination is the `remaining visited` component: mark the current
      state *before* recursing, so every `skip/step` strictly decreases it.
      Reuse `mark`/`remaining`/`_≺_` from `Check/Decide.agda` — that part of
      the old machinery IS worth keeping; it is `Covers`/`Table`/the worklist
      that dies.

      **This step is mutually recursive with Step 1's `blocked/rec`**, and
      that is the crux: a forward `skip/step` may land on a state whose only
      typing is a backward `blocked/rec`. Do not attempt to sequence them as
      two passes — see the ∀/∃ table above and `Ex6`.

      Two corrections to the sketch above, both forced:

      * the order is main, then **cycle**, then step — `skip/cycle` has to
        be tried before `skip/step`, otherwise a literal revisit has no
        answer and the measure cannot decrease;
      * the search is split by `∈T? P s` into `treeA?`/`treeB?`. See "The
        one design decision that is not in the plan" at the top of this
        file. Without the split, refuting a revisit needs the whole
        exploration, which is the old file's second postulate.

- [x] **Step 3 — decide `⊢a`.** Now syntax-directed on `Pr`:
      `∅ → a/end` via `∈T?`; `ifp → a/if` via `checkExpression` plus two
      recursive calls; everything else → `a/skip` of Step 2. Mutually
      recursive with Steps 1–2; find the measure before writing it (process
      size lexicographic with the visited-set measure is the obvious
      candidate, and is what the old file used).

      One correction: `a/skip` is available for **every** process form, `∅`
      and `ifp` included, since its `PPr` is generic. `⊢blocked` has no
      constructor for those two, so such a tree can only be closed by
      `skip/cycle` throughout — degenerate, but a legal derivation, so a
      `no` for `∅`/`ifp` has to rule it out as well as `a/end`/`a/if`.

- [x] **Step 4 — derive `Dec (⊢p)`.** One `map′`, as in "Philosophy" above.
      Nothing else. If this step needs more than a few lines, something in
      Steps 1–3 is wrong.
      (`Check/Alg.agda`'s `tc?`; it is two lines. `tcSession?` is
      `FinP.all?` over the participants.)

- [x] **Step 5 — delete the corpse.** Done: `Check/Decide.agda` deleted
      outright (on the owner's explicit instruction — it was untracked, so
      it is gone for good). Everything the plan listed — `Table`, `extend`,
      `Covers`, `Covers-from-closed`, `DirectCovered` + lemmas,
      `step-predecessors`, `rec-unskip`, `leaf-permute`, `permute-tree`,
      `rec-refute/unskip`, and **both postulates** — went with it, as did
      `find-leaf`, `end-refute-td` and the `if-refute/*`/`rec-refute/*`
      family: `⊢p`-refutation helpers that completeness-via-`norm` makes
      redundant. `runall.sh` lost the root and the "expected holes" special
      case.

- [x] **Step 6 — rewire.** Restore `Check/Network.agda`'s two commented-out
      API wrappers, and repair `Examples/` and `Tests/Perf*`, which import the
      long-deleted old checker.

      Done as: a new `Check/Graph.agda` (`WBGraph`/`buildG`/`wb-of`/
      `typecheck`/`typecheckSession`, same signatures as the deleted
      `Definitions/TypeChecker/Completeness.agda`), the two
      `Check/Network.agda` wrappers, and a new `Check.agda` aggregator that
      re-exports exactly what the deleted `Definitions/TypeChecker.agda` did
      — so every caller needed only its import line changed. All 17
      `Examples/*` + `Tests/Perf*` files compile.

      `Tests/Perf04_Size2Choice` and `Tests/Perf05_Size3ChoiceCheckA` cost
      an extra fix, and the *first* diagnosis of them here was WRONG — it
      claimed `wellBehaved?` had changed and the graphs were now unsound.
      It has not changed; neither has `Ref` (`loop`/`node`/`ended` is
      identical at HEAD). Those two files simply predate the `Ref` datatype
      — they still said `inj₁`/`inj₂`. Rewriting that to `loop`/`node`
      mechanically was not enough: under the old sum encoding there was no
      separate `ended`, so the translation left a spare edge-less *node*
      that is bisimilar to the `ended` state `compile` appends, and two
      distinct-but-bisimilar dead ends break `stepback/~` (the same death
      as the rejected graphs in `Tests/AnchorAttempts.agda`). Pointing the
      dead branches at `ended` and dropping the spare node fixes both.
      **Lesson: a dead end must be `ended`, never a node of its own.**

---

## Future (NOT part of this plan — do not start before Step 5 is green)

**Batch the `rec` anchor search: type against a SET of states.**

The naive Step 1 `blocked/rec` decides
`Γ & (W ∷ Δ) ⊢a P ◂ Pr ∶ W` once per candidate `W`, and each of those launches
its own forward walk over largely the same states. Instead compute, in one
pass over the `¬P`-connected component,

```
S(Pr, Δ) = { W ∈ component | Γ & (W ∷ Δ) ⊢a P ◂ Pr ∶ W }
```

as a bit-vector over `State G`. `blocked/rec` at leaf `L` then reduces to
"∃ W ∈ S with `W -[¬ P ]->* L`" — one reachability query against a
precomputed set.

**The real argument for it is the refutation, not the speed.** The `no`
branch needs an `All`-shaped negative over every candidate anchor. Built
candidate-by-candidate, that `All` has to be folded together from separately
obtained negatives — the pattern that has historically been the expensive
part. Computed as a set, the universal statement *is* the result, and the
per-state negatives are its complement.

Two caveats to settle before attempting it:

- **Δ-indexing.** The predicate depends on `Δ`, so the table is indexed by
  (subprocess, state, `Δ`) and `Δ` is a vector of states — `|states|^δ`
  environments. Fine at `δ = 1`; it degrades with recursion *nesting depth*,
  not process size. This is what decides viability.
- **Cycles do NOT force the typing to be iterated.** (An earlier draft of
  this note claimed they did; that was wrong.) `skip/cycle`'s self-dependence
  lives in the *skip tree*, not in the typing judgment, and it is closed
  afterwards from the `¬P` edges. For a fixed process `Pr`, in order:

  1. compute `B` = the states at which `Pr` is **directly blocked**
     (`blocked/send`/`recv`/`var`/`rec`). Each of those depends only on
     decisions at *strictly smaller* processes — continuations, `rec` bodies
     — so `B` is a clean bottom-up pass with no circularity at `Pr`;
  2. the `a/skip`-typeable set is then "states from which every `¬P`-path
     reaches `B` or revisits", a graph computation against a now-**fixed**
     `B`.

  Worked example: `G -[¬P]-> G'`, `G' -[P]-> G''`, `G' -[¬P]-> G`. Component
  `{G, G'}`; `B = {G'}` (only `G'` offers a `P` action); `G` follows because
  its only `¬P`-successor is in `B`. The `G → G' → G` loop is reconstructed
  from the `¬P` edges at the end — **nothing is re-typed**.

  What remains is only step 2's own shape: "all paths reach `B` or revisit"
  is a safety/AG-style property, so it is a *greatest* fixed point over the
  finite `¬P` graph (equivalently, a least fixed point of the failure set,
  propagated backwards from `¬P`-dead-ends outside `B`), plus `skip/cycle`'s
  `P ∈T` side condition on each closing revisit. Cheap and standard — but
  get the direction right, because a wrong choice here yields a wrong `no`.
  It cannot yield a bogus `yes`: every `yes` still hands back a real
  constructor.

Do the naive version first. It is the specification the batched version has
to agree with, and `Ex6` is the test that separates them.

---

## Cleanup (done 2026-08-05)

~2150 lines of dead code removed, each deletion verified by
`./runall.sh --tests` staying green. All of it existed to serve
`Check/Decide.agda`, which decided `⊢p` directly and therefore had to
*locate a specific leaf* inside a skip tree and preserve that leaf's
identity across every tree transformation. `Check/Alg.agda` never needs
that: completeness comes from `norm`, which does not track leaf identity.

| what | where | lines |
|---|---|---|
| the whole file | `Check/Decide.agda` | 1531 |
| `_≺ᵗ_`, `Accessibleᵗ`, `subderivation-well-founded`, `main-leaf-accessible` | `Definitions/Typing/Declarative.agda` (400 → 203) | 197 |
| the `~MainLeaf`-transport cluster (12 definitions) | `Definitions/Typing/Properties.agda` (794 → 365) | 429 |
| empty leftovers of the `git mv` | `LTS/`, `Typing/` | — |

`~MainLeaf` and `~mainLeaf/weaken-visited` **stay** — `Normalise.agda` and
`Norm.agda` still use them.

Method, for whoever repeats this: grep a candidate's name across
`--include="*.agda"`; if every hit is inside its own defining file, it is
dead. Delete it, recompile, and the next layer becomes visible. Do NOT
verify with `agda Definitions.agda` — that aggregator does not pull in
`Typing/Properties.agda` or `Typing/Normalise.agda`, so it will report
success on edits it never checked. Use `./runall.sh`.

---

## DONE: the `⊢head` → `⊢a` migration (2026-08-05)

**`⊢head` no longer exists.** `Safety/Preservation`, `Safety/Progress` and
`Safety/Termination` are stated and proved over `⊢a`; `⊢p` survives only at
the `⊢s` boundary. `./runall.sh --tests` green.

Deleted: `Definitions/Typing/Normalise.agda` (661 lines) in full, and the
`⊢head`/`⊢hskip`/`head/typing`/`hskip/typing` block in
`Definitions/Typing/Algorithmic.agda` (299 → 180 lines).

### The boundary

`alg/lookup` in `Safety/Preservation.agda` is the single `⊢s → ⊢a` door:

```agda
alg/lookup ts luP = norm (td/lookup ts luP) skip/refl
```

`alg/typing` appears only where `⊢s-update`/`⊢s-comm-update` must rebuild a
session derivation. Support lemmas are `⊢a`-stated; where their proof needs
`⊢p` the round trip is confined to `Definitions/Typing/`:

| lemma | where | proof |
|---|---|---|
| `a/rec/unfold` | `Substitution.agda` | round trip (1 line) |
| `alg/subst-expr` | `Substitution.agda` | round trip (1 line) |
| `a/if/inv` | `Norm.agda` | **native**, 4 lines |
| `a/rec/guarded` | `Norm.agda` | **native**, ~35 lines |

### Verdict on "does `⊢a` give cleaner proofs?" — mostly yes

Where it wins, and why:

* **`a/if/inv`: 4 lines vs `head/if/inv`'s ~90.** `⊢head`'s `h/skip` can
  sit over an `if` *and* its main leaf can be another `h/if`, so inversion
  needs two mutual walkers plus a `P ∈T` chase. `⊢blocked` has **no `if`
  form**, so there is nothing to chase.
* **`rec/guarded`: 1 line vs ~65.** `blocked/rec` carries
  `MessageGuarded Pr` as a field.
* **`comm/ready`: 3 non-mutual functions vs 5 in two mutual blocks.** All
  the `⊢head` structure existed to unwrap `h/skip` nested inside
  `skip/main`; `⊢a` has no such nesting.
* **`guarded/active`** had three near-identical `h/skip` clauses, one per
  `MessageGuarded` constructor; `a/skip` needs one.
* Conversions vanish: `blocked/send` stores an `⊢a`, so `send/cont` no
  longer calls `head/typing`; `norm` replaces `head/typing ∘ td/head`.
* Four cases disappear by coverage alone (`MessageGuarded` has no
  constructor for `∅`/`v`/`rec`; `⊢blocked` none for `ifp`).

Where it loses — both trace to the same root, that `a/skip` pins its leaves
to `⊢blocked`, which is exactly what makes `Check/Alg.agda`
syntax-directed:

* **Substitution.** `t/var`'s replacement is any `⊢p` (`td/bisim`, one
  line). `blocked/var` carries a ¬P-*trace* as well as a bisimilarity, so
  the replacement has to be moved along it. A native `alg/subst-proc` +
  `alg/advance` was built (~290 lines, terminating, no pragmas) and then
  **deleted**: `typing/subst-proc` has to stay for `t/rec/unfold`
  regardless, so it bought nothing over the one-line round trip.
* **`rec` unfolding.** `⊢p` keeps the trace (`t/unskip tr (t/rec/unfold td)`);
  `⊢a` must drive it into the leaves.

---

## Superseded: the `⊢head` → `⊢a` migration plan

### Decisions taken (owner, 2026-08-05) — read these before touching anything

1. **`⊢s` stays over `⊢p`.** The theorem statements do not change.
2. **The `⊢p → ⊢a → ⊢p` round trip is for the MAIN THEOREM ONLY.** From `⊢s`
   get `⊢p`, go *immediately* to `⊢a` via `norm _ skip/refl`, do everything
   there, and convert back with `alg/typing` only when a session derivation
   has to be rebuilt.
3. **No other use of `⊢p` is allowed anywhere in Safety** — including the
   proofs that are written over `⊢p` today. A support lemma Safety needs
   must be *re-proved* over `⊢a`, not reached through the round trip. (I got
   this wrong once: `inactive/done-blocked` used
   `alg/typing`→`t/rec/unfold`→`norm` internally. That is not allowed.)
4. **Afterwards delete `Definitions/Typing/Substitution.agda`** and any other
   property that is not genuinely about `⊢p` — or keep the statements as
   thin `⊢p → ⊢a → ⊢p` wrappers "for historic reasons" only, never as the
   primary proof.
5. **Secondary goal, and a real one: find out whether `⊢a` gives simpler,
   cleaner proofs.** If something comes out *worse* in `⊢a`, say so; do not
   hide it by keeping the `⊢p` version.

### Lemmas that must be ported to `⊢a` before Preservation/Termination move

| needed by | `⊢p` original | `⊢a` port |
|---|---|---|
| Preservation (comm) | `typing/subst-expr` | `alg/subst-expr` |
| `a/rec/unfold` | `typing/subst-proc` | `alg/subst-proc` |
| Progress, Preservation | `t/rec/unfold` | `a/rec/unfold` |
| Preservation, Termination | `t/if/inv` | `a/if/inv` |
| Termination | `rec/guarded` | `a/rec/guarded` |

`a/if/inv` should come out **shorter** than `head/if/inv`, not longer:
`head/if/inv` keeps `Ξ = []` via `skip/unfold-cycle` (`Leaf`-generic, still
in `Properties.agda`) so `skip/cycle` is absurd throughout and every leaf is
`skip/main` — and for `⊢a` that leaf is `⊢blocked … ifp …`, which has **no
constructor at all**, where `⊢head` still had to handle `h/if`.

### Status

**Goal (owner, 2026-08-05): Safety must be proved over the algorithmic
rules, not the declarative ones.** Then `⊢head` and everything serving it
gets deleted.

**`Safety/Progress.agda` is DONE** — fully on `⊢a`, no `⊢head` outside
comments, `Safety.agda` green. Its `inactive/done-blocked` still contains
the forbidden internal round trip and must be redone once `a/rec/unfold`
exists. `Termination` (19 refs) and `Preservation` (43 refs) not started.

**`Definitions/Typing/AlgSubst.agda` is NEW and green**, containing
`alg/weaken-proc`, `alg/weaken-expr`, `alg/subst-proc` (all with their
`⊢blocked`/`⊢skip` companions), `transport-alg`, and `Advanceable` /
`rec/advanceable`. Only process-level lemmas are borrowed from
`Substitution.agda` (`lookup/*`, `guarded/*`, `expr-weaken-lemma`) — none
mentions `⊢p`, so nothing here blocks deleting that file.

`blocked/var` is handled by passing the substituend *already able to
re-site itself* (`Advanceable`); for `rec` that is `skip/cat tr₀ tr`,
absorbing the trace into the anchor, and costs nothing.

**BLOCKED: `alg/advance` / `blockedAlg` type-check but fail termination**,
and `a/rec/unfold` needs them. Both are parked in a block comment with the
diagnosis in place. The obstacle:

- `alg/advance-aux → blockedAlg → alg/advance → alg/advance-aux`
  strictly decreases the **derivation** at every step;
- `alg/advance-aux → alg/advance-aux` (via `bskip/unfold-top`) rebuilds
  the tree, so only the **trace** decreases;
- a mixed cycle therefore decreases neither. `skip/advance` returns a
  fresh trace that *is* the same length, but nothing tells Agda so.

Fix: measure by the **process** — `=` on the unfold step, `<` through
`blockedAlg` — which needs a vector companion for `blocked/recv`'s
`lu Br j` so `Σ P ？[ S ]· Br → lu Br j` reads as structural. That is the
CLAUDE.md gotcha, applied here.

Note `push` (`Norm.agda`, "PUSH SKIP FORWARD") already IS the graft from a
skip tree of `⊢a` leaves to an `⊢a`, handling all six process forms
including `if` and `∅`. Do not rewrite it.

Early verdict on the secondary goal: `⊢a` is structurally cleaner. Under
`⊢head`, `h/skip` had to be re-handled once per sibling constructor
(`guarded/active` had three near-identical `h/skip` clauses); `a/skip`
needs one, because the process form is irrelevant to it. And four cases
disappear entirely, discharged by coverage: `MessageGuarded` has no
constructor for `∅`/`v`/`rec`, and `⊢blocked` none for `ifp`. Line count
went *up* (361 → 429) only because each function splits into an
`⊢a`/`⊢skip`/`⊢blocked` triple with three signatures.

`blocked/rec`'s per-leaf anchor — the thing I expected to hurt — cost
nothing: the anchor `W` never enters, because the argument unfolds the
recursion at the *leaf*.

What has to move — `⊢head` is used 46/51/38 times in
`Safety/Preservation.agda`, `Safety/Progress.agda`, `Safety/Termination.agda`
respectively:

| `⊢head` | `⊢a` replacement |
|---|---|
| `h/send` / `h/recv` | `blocked/send` / `blocked/recv`, *inside* a leaf |
| `h/rec` | `blocked/rec` (per-leaf anchor, not one common one) |
| `h/if` / `h/end` | `a/if` / `a/end` |
| `h/skip` + its `⊢hskip` companion walker | `a/skip`'s tree — same walk |
| — | `blocked/var`: IMPOSSIBLE in Safety, which is all `δ = 0`, so `v X` has `X : Fin 0`. Absurd pattern. |

So each Safety function splits differently: instead of one six-way case on
`⊢head`, a three-way case on `⊢a` (`a/skip`/`a/if`/`a/end`) with the
send/recv/rec analysis moving down into the `⊢blocked` leaf. The `⊢hskip`
companion walkers map onto the tree walk inside `a/skip` almost verbatim —
that part is a rename, not a re-proof.

Entry point: `td/head (M⊢G P) skip/refl` becomes `norm (M⊢G P) skip/refl`
(`Definitions/Typing/Norm.agda`, hole-free). Note `norm` is `Δ`-general
where `td/head` was `δ = 0` only, so it is strictly more applicable.

Once green, delete: `Definitions/Typing/Normalise.agda` (661 lines) in
full, and the `LEGACY` `⊢head` block in `Definitions/Typing/Algorithmic.agda`
(lines 177–299) together with `_⊢head_∶_`, `_&_⊢hskip_∶_`, `head/typing`
and `hskip/typing`.

---

## The actual problem with nets (owner, 2026-08-05)

Recorded correctly this time. Compositionality of *well-behavedness* is
NOT the issue. **State explosion is**, and specifically: type checking a
net runs on the net's flattened underlying graph.

`Check/Alg.agda`'s `AlgCheck` is parameterised by a concrete `(G : Graph)`
— it needs `State G`, `edges G s`, `size G` for the visited bit-vector,
`FinP.any?` over `State G` for the anchor search. It cannot consume an
abstract `BTheory`, and it certainly cannot consume `netTheory n`. So
`Check/Network.agda` has no choice but to be a flattening shim:

```agda
netWB  : ∀ {n} → WBNet n → WellBehaved (netTheory n)   -- structural, no product built
wb-net {n} w = net→pres n (netWB w)                     -- ← structure discarded here
typecheckNet w P Pr = AlgCheck.tc? (underlying (present n)) (wb-net w) …
```

`netTheory n` is genuinely net-native (`Behav = NState n`, `_-<_>->_ =
NStep n`). `netWB` builds a witness for it compositionally. And then its
only consumer immediately transports that witness onto the flattened
product and runs the checker there. `present n` is materialised on every
path regardless, so the product state space is always built.

The fix is a typing judgment (and decision procedure) that decomposes
along `∥` and `⨾` the way `WBNet` decomposes well-behavedness, so `tc?`
never sees `present n`:

- **`∥`** looks reachable: participants are disjoint (`disjoint?` already
  proves the side is unique), so typing `P` against `n₁ ∥ n₂` should be
  typing `P` against whichever side contains it.
- **`⨾`** is harder — it needs a process to split into the part typed
  against `n₁` and the part against `n₂`, and it hits the same wall as
  `stepback/~`, whose `WBNet` constructor already has to check
  `finiteStepback?` on the flattened composite. Decide whether `⨾` should
  be restricted to seams where that is structural before building anything.

---

## Also outstanding

- **`CLAUDE.md` is stale** (owner says: ignore the `.md` files, so this is
  recorded, not scheduled). It still calls `Check/Decide.agda` *the*
  decision procedure — that file is gone — and knows nothing about
  `Check/Alg.agda`, `Check/Graph.agda`, `Check.agda`.
- **Batching the `rec` anchor search** — the "Future" section below.
  Deliberately NOT started, and now lower priority than both items above.

---

## Acceptance criterion (what "done" means for this plan)

- `./runall.sh` clean on **all** roots, with **no** file reporting expected
  holes — i.e. the `Check/Decide.agda` special case in `runall.sh` can be
  deleted, and should be as part of Step 5.
  **MET** — `./runall.sh --tests` prints "All files processed
  successfully!"; the special case is gone.
- No `postulate` anywhere under `Check/`.
  **MET** — `Check/Alg.agda`, `Check/Graph.agda`, `Check/Core.agda`,
  `Check/Network.agda`, `Check.agda`. The only two were in
  `Check/Decide.agda`, now deleted.
- `Tests/AnchorAttempts.agda` still compiles (it is independent of this work
  but is the cheapest regression signal that the graph layer is untouched).
  **MET** — compiles, and is now in `TEST_ROOTS`.

## Loose ends left by the previous plan (verified 2026-08-04, not guesses)

- **`CLAUDE.md` is stale about this file.** It refers to `TODO.md`'s "Step 1"
  (directory restructure), "Step 7" (Examples/Perf repair) and "`h/skip`
  folded into the action and variable rules" — all of which belong to the
  archived plan, not this one. Its architecture section also still describes
  the pre-rename names. Worth a pass, but read the code before believing it.

- **`⊢head` is still alive and CANNOT simply be deleted.** The archived plan
  had a step to remove it; that step was never done. `grep` confirms
  `Definitions/Typing/Normalise.agda` is still imported by
  `Safety/Preservation.agda`, `Safety/Progress.agda`, `Safety/Termination.agda`
  and `Check/Decide.agda`. So retiring it is gated on the three `Safety`
  files being migrated to `⊢a`, which is *not* in scope here. If Step 5's
  deletions look like they should take `Normalise.agda` with them, they
  should not.

- **The `Ex6` regression is CONFIRMED (2026-08-04).** It is
  `Tests/AlgCheck.agda`, module `Ex6`, and the prediction held: under the
  new judgment `⊢a` *is* derivable at `G`, and the checker finds it
  unaided — `ex6-typed`/`ex6-typed/p` are forced (`T ⌊ … ⌋`), so the file
  compiling is the search actually running. It is also the regression test
  for the backward anchor search, since the anchor it has to find is `M`,
  which `G` does not reach.

- `Tests/AnchorAttempts.agda` is now in `TEST_ROOTS`, along with
  `Tests/AlgCheck.agda`.

- **The 28 GB test files are `wb`'s fault, and the fix is one keyword.**
  Profiled 2026-08-05. `wb = toWitness {a? = wellBehaved? G} tt` is a
  module-level *definition*, and Agda unfolds a definition at every use
  site (it shares argument thunks, not definition applications). So every
  type mentioning `Typing.MPST wb` that has to be normalised re-runs the
  whole `wellBehaved?` decision procedure. On `Tests/SkipBeforeVar.agda` —
  a TWO-state graph — warm interfaces:

  | file content | time | peak RSS |
  |---|---|---|
  | graph + `wb` only | 5 s | 0.58 GB |
  | + `A∉β`, `na` | 16 s | 1.0 GB |
  | + `ktd` | >544 s | >12 GB (heap cap) |
  | whole file, as committed | 259 s | **28 GB, OOM-killed** |
  | whole file, `wb` in an `abstract` block | 23 s | **1.0 GB** |
  | whole file, `wb` postulated (diagnostic only) | 5 s | 0.59 GB |

  Two other hypotheses were tested and **refuted**: the unsolved `nchoices`
  metavariable in `β` (pinning it left the full file at 26 GB) and
  `ktd`'s unpinned `step⇒listed` implicits (pinning them: 544 s → 525 s,
  i.e. nothing).

  **APPLIED** to both files; they are now in `TEST_ROOTS` and green.
  The fix is `opaque` around the witness — still a real proof, unlike a
  postulate:

  ```agda
  opaque
    wb : Typing.WellBehaved (graphTheory G)
    wb = toWitness {a? = wellBehaved? G} tt
  ```

  Everything the witness used to solve *by computation* must then be
  written down. All of it is mechanical, and all of it is the CLAUDE.md
  "pin your implicits" gotcha showing up where it was previously masked:

  - `nchoices` in a standalone action. `mkChoice zero s/unit` leaves it a
    metavariable (`zero : Fin (suc nchoices)` pins nothing), and a meta
    inside an action blocks `_≟Action_`, hence `bisim?`, hence everything.
    Write `mkChoice {nchoices = 0} zero s/unit`, or give the label a type
    that pins it (`lbl : Fin 1`, as `RecSkipCounterexample` already did).
  - `step⇒listed`'s `{s}`/`{α}`/`{t}` at every `with` site — an unsolved
    `{s = _}` leaves the scrutinee's edge list stuck, so `here` cannot even
    be case-split.
  - `skip/step`'s `{α}` and `{G' = …}` (ASCII apostrophe) and `skip/one`'s
    `{G′}`/`{α}` (Unicode prime — they differ!) wherever the step proof is
    a bare `tt`.
  - a clause that was previously undecidable becomes provably impossible:
    `no-edge-into-s`'s `ended` case is `here () / there ()` → a single `()`.

  One structural change was needed. `SkipBeforeVar`'s `K≁s` projected out
  of `_~_` with `~L→ K~s {α = β} {G′ = E} tt`, which has not type-checked
  since `Behav.agda` gave `~L→` its current signature — all four implicits
  come *before* the explicit `G~G′`, and the one named `G′` is the
  bisimilar state, not the step's target. The 28 GB blowup had masked the
  error; the file never got that far. It is now *decided* at the graph
  level (`complete (bisimulationCorrect G)`, then `Bisimilar G K s → ⊥`),
  which is shorter and needs no `unfolding` — `bisim?` never mentions `wb`.
  Note `GraphChecker.bisim?~` will NOT do here: that module is applied to
  `wb`, and a module application elaborated outside the opaque block stays
  blocked whatever `unfolding` a later block declares.

  Note the checker itself does not suffer from this: `Tests/AlgCheck.agda`
  forces six decisions over two graphs in 35 s / 1.0 GB, because `wb`
  reaches `AlgCheck` as a bound *module argument*.

## Rules carried over (violating these has cost days before)

- **Never leave a hard type error.** Holes are acceptable mid-step; a
  non-compiling file is not.
- **Never claim a step is done without a compiler run behind it**, and never
  write such a claim into this file.
- `wt`/`Incl`/`mark`/`lookup`/`tabulate` are non-injective — pin vector
  implicits (`{Ξ}`, `{visited}`, …) explicitly or Agda leaves unsolved metas.
- Anything recursing on a *looked-up* branch (`lookup Br j`) needs a
  vector-companion function so the termination checker sees structure.
- A value consulted many times must be passed as a **bound argument**, not
  re-derived at each use site — Agda shares argument thunks, not definition
  applications. Getting this wrong in `semSkip?` cost a factor of 10²–10³.
- Every file under `Safety/` and `Definitions/Typing/` imports the narrow
  `Definitions.Typing`, never the `Definitions` aggregator.
