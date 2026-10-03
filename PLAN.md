# PLAN.md — one process, many roles, by local views

*2026-10-03, `set-typing`. A step-by-step guide. Nothing is implemented except the
finite-graph prototype `Tests/Quotient.agda` (untracked).*

**Terms.** A *role* is `Part = Fin N`. A *process* implements a role set `Ps`; an
*assignment* `Ρ` partitions `Fin N` into processes. *Multi-role*: `|Ps| > 1`.

**Idea.** A multi-role process is typed by today's single-role judgment against its own
**local view** of the LTS: its roles merged, its internal steps hidden, its conflicts
resolved by a global order. Singletons are typed against the original. A view is a
`BTheory` on the same carrier (no graph is built). Only the theory changes, and only so
that views can be used without minimising them (Step 1).

**Example.** `P → Q . R → S` (the same LTS as `R → S . P → Q`) is the square
`0 -P→Q-> 1 -R→S-> 3`, `0 -R→S-> 2 -P→Q-> 3`. Under `{P,S}`/`{Q,R}`, merging alone gives
`{P,S}` a mixed choice at `0` (`PS→Q` vs `R→PS`). The order keeps `P→Q` at `0` in both
views: `{P,S}`: `PS→Q . R→PS`; `{Q,R}`: `P→QR . QR→S`.

---

## Step 1 — `WellBehaved` up to bisimilarity

A view keeps all of `B`'s states, so states can become bisimilar in it: an unstable state
with one hidden successor, or the two targets of a merged multicast (`NoSynGT` under
`{B,C}`). Three fields are stated up to identity and fail on these (an audit of every
state `≡` in `Behav`, `Typing/`, `Safety/`, `Proc` found no others; `Step G nothing G′ =
G ≡ G′` in `Preservation` is kept, since identity is always available). Step 1 is
independent of views and must leave everything green (`./runall.sh --clean --tests`).

### 1a. Weaken `step-deterministic`

```agda
step-deterministic : G -< α >-> G′ → G -< α >-> G″ → G′ ~ G″      -- was G′ ≡ G″
```

| use site | change |
|---|---|
| `Behav.agda` `branch/before` (`rewrite`) | return `Gⱼ -[¬ Q ]->* H × H ~ Gⱼ′`; forward-transport the run (`tr-transport`). Callers in `AlgNorm` that recurse on the result: carry the `~` into an `-aux` helper (a transport breaks structural recursion). |
| `AlgNorm.agda` `sendAt` (`rewrite`) | transport `td′` along the `~` (the set is `Closed`). |
| graph instance (`Graph/WellBehaved.agda`, nets) | prove the weak form from the strong one (`≡ → ~`). |

### 1a′. Weaken `step-diamond`

```agda
step-diamond : G -< α >-> G₁ → G -< α′ >-> G₂ → α ⋄ α′
             → ∃[ X ] ∃[ Y ] (G₁ -< α′ >-> X) × (G₂ -< α >-> Y) × X ~ Y   -- was one common G′
```

Views need it: if `α` leaves an internal step pending, the view's `α′` after `α` ends
after the hidden steps, while `α` after `α′` may end before them — bisimilar, not equal.

| use site | change |
|---|---|
| `Behav.agda` `skip/advance-aux` | still recurses on the original run (stays structural); returns `Gα -[¬ P ]->* Z × Z ~ G′α`, the tail moved forward by `tr-transport`. `skip/advance` likewise. |
| `skip/advance`'s consumers: `branch/before`, three uses in `AlgNorm` | absorb the `~` (the sets are `Closed`). |
| `Behav.agda` `no-new-branch/skip-aux` | none: it uses only the existence of the step. |
| graph instance, nets (`parWB`, `seqWB`, `NetworkPresent`) | prove the weak form from the strong one. |

### 1b. Delete `stepback/~`

Its only use is `skip/bisim` (`Properties.agda`): pull a `¬P` run back along a `~` on its
target. That has two clients, and both become `~`-closed by construction:

```agda
t/unskip : (tr : G -[¬ P ]->* G″) → G″ ~ G′ → (td : Γ & Δ ⊢p P ◂ Pr ∶ G) → … ∶ G′
Unskip P 𝒜 (ws , s) = ∃[ a ] (ws , a) ∈ 𝒜 × ∃[ s′ ] a -[¬ P ]->* s′ × s′ ~ s   -- Alg.agda
After  P 𝒜 s        = ∃[ a ] 𝒜 a × ∃[ s′ ] a -[¬ P ]->* s′ × s′ ~ s             -- AlgNorm.agda
```

- `td/bisim`'s `t/unskip` case and `after/~` become `~trans`; delete `skip/bisim`,
  `stepback/~*`.
- Consumers of a `t/unskip`/`Unskip` run (`Safety/`, `AlgEquiv`, `AlgDeclarative`,
  `Check/Alg.agda`): move what they need forward along the extra `~`
  (`~L→`/`~R→`/`tr-transport`/`td/bisim`). No consumer needs to go backwards — that is the
  thing to confirm while doing it.
- Delete the graph-side proofs: `stepbackAt′`, `finiteStepback?`, `stepback/sound`
  (`Decision.agda`), `stepbackG→N` (`NetworkPresent.agda`), `stepback/~` in `parWB`,
  `seqWB`, `wellBehaved`, `Tests/WaitNotSkip.agda`; drop `gs` from `WBNet`'s `⨾`
  (`Check/Network.agda`). This removes the one non-local check on nets.
- Update comments that cite stepback (`Examples/{OAuth2,IndepW,CounterExamples}`,
  `NetworkSeq.agda` header, `CLAUDE.md`'s "dead end must be `ended`" gotcha).

**Why deleting is sound.** `stepback/~` says no state is a bisimilar *duplicate* nothing
steps into. The judgment never needs that: it only needs derivations to transport along
`~`, which after the change is forward-only. **Risk.** If some consumer does need a
backward run, keep `stepback/~` for `B` and fall back to minimising views (D7).

### 1c. What weak determinism does and does not allow

- Allowed: one action to targets `b ~ c`, and diamonds closing up to `~`. Typing is
  invariant under `~` (`td/bisim`, `Closed`, `skip/cycle`'s `lu Ξ X ~ G`, `∈~`); the
  session's real state is fixed by the original, so nobody chooses between `b` and `c`.
- States shared between premises (`t/send`'s target, `conts`, `⊢s`'s common `G`,
  `Unskip`/`After` endpoints, `t/rec`'s `Δ`) are harmless for the same reason.
- Still excluded: targets that are not bisimilar.
- **User-facing consequence.** If a sender's two messages to different roles of one
  process have the same label and sort (`NoSynGT` under `{B,C}`), the process cannot tell
  which role each was for. Type-safe, but labels must differ if it matters.

## Step 2 — `Definitions/View.agda`

```agda
module View {N} (B : BTheory N) (Ps : PartSet) (p : Part) where   -- p ∈ Ps
  ⌊_⌋ : Action → Maybe Action
  -- P ⟶ Qs # c  ↦  ρ P ⟶ (ρ Qs ∖ ρ P) # c, ρ = Ps ↦ p; nothing if no receiver is left

  _-τ->_ : Behav → Behav → Set
  G -τ-> G′ = ∃[ α ] G -< α >-> G′ × ⌊ α ⌋ ≡ nothing

  Stable : Behav → Set
  Stable G = ∀ {G′} → ¬ G -τ-> G′

  Conflict : Action → Action → Set     -- both external for Ps, and Ps sends in one and
                                       -- receives in the other, or receives in both
                                       -- from different senders
  _≺_ : Comm → Comm → Set              -- fixed, decidable, strict, total (lexicographic)

  Kept : Behav → Action → Set
  Kept G α = ∀ {β G′} → G -< β >-> G′ → Conflict β α → ¬ comm β ≺ comm α

  _-<_>->ᵛ_ : Behav → Action → Behav → Set
  G -< β >->ᵛ G″ = ∃[ G₁ ] ∃[ α ] Star _-τ->_ G G₁ × Stable G₁
                 × G₁ -< α >-> G″ × Kept G₁ α × ⌊ α ⌋ ≡ just β

  view : BTheory N
  view = record { Behav = Behav ; _-<_>->_ = _-<_>->ᵛ_ }

  Exits : Set                          -- internal loops allowed, but each has an exit
  Exits = ∀ G → ∃[ G₁ ] Star _-τ->_ G G₁ × Stable G₁
```

Hiding is eager: a state with a pending internal step offers what its stable τ-successors
offer, so an internal choice (including one through a loop) is made by the process's next
external action. The session never performs internal steps, so loops are never executed.

## Step 3 — View lemmas

| lemma | statement | uses |
|---|---|---|
| `view/run` | `G -< β >->ᵛ G″ → ∃[ αs ] G -[ αs ]-> G″ × …` (hidden steps, then one step relabelled to `β`) | semantics, progress |
| `view/~` | `G ~ H` in `B` → `G ~ H` in `view` | preservation (global state vs typed state) |
| `view/commute` | an outsider step and a pending internal step commute (disjoint roles ⇒ `⋄` ⇒ `step-diamond`) | following outsiders while an internal choice is open |
| `conflict/⋄` | `Conflict β α` at one state ⇒ `α ⋄ β` | the order prunes only interleavings |

## Step 4 — Assignments and session semantics (`Proc.agda`)

- `Roles k = Vec PartSet k`, `Partition Ρ`, `owner : Part → Fin k`, `name : Fin k → Part`
  (`name j ∈ lookup Ρ j`).
- **Syntax unchanged.** In its view a process is `name j`; every other role is individual,
  so code names partners by role.
- `s/comm`: a send `Qs ! …` by `owner P` meets, for each process owning a role of `Qs`,
  one receive. Internal steps have no session step. A session run is a run of `B` with
  internal steps inserted.

## Step 5 — `⊢s`

```agda
⊢s M ∶ G = Partition Ρ × ∀ j → (if multi-role j
                                  then Γ & Δ ⊢p name j ◂ M[j] ∶ G   in MPST (wbᵛ j)
                                  else today's judgment            in MPST wb)
```

Hypotheses, as for `B` today: `WellBehaved B`, `Synchronous B`, and per multi-role `j`:
`WellBehaved (view j)`, `Synchronous (view j)`, `Exits j`. `balanced` for a view holds by
construction; `no-new-comm/step` must be checked.

## Step 6 — Preservation and termination

Per process, against its own theory, by today's proofs. Invariant: process `j`'s derivation
is at a state `~`-related, in `j`'s theory, to the global state. A global step `G -α-> G′`
moves `j` by: its own view step (`j` acts), an idle view step (outsider; `view/commute` if
`j` has a pending internal choice), or nothing (another process's internal step).

## Step 7 — Progress (open)

Processes are typed against different theories, so the proof must go through `B`. Sketch:
take the `≺`-least enabled external step of `B`; no view prunes it, so every process
involved keeps it. Open case: a process holding it behind a concurrent send it may order
freely. (A counterexample attempt failed: the receiver's view sees two concurrent sends
as one sender's choice of labels, so it accepts both orders.)

## Step 8 — Checker

On graphs everything is decidable: `⌊_⌋` is a function, `Stable`/`Kept` inspect one
state, the τ-closure is a walk with a visited set, `Exits` is "no empty closure". Build
each view as a graph, check `wellBehaved?`/`synchronous?`, run today's checker at
`name j`. Bring `Tests/Quotient.agda` in line: check `Exits`; drop the closure-set and
bisimilarity minimisation once Step 1 makes them unnecessary.

---

## Decisions

| # | decision | alternative |
|---|---|---|
| D1 | one view per multi-role process; singletons use `B` | one global quotient (everyone names processes) |
| D2 | view = layer on `BTheory` | build and minimise a graph (fine for the checker only) |
| D3 | conflicts (mixed, or different senders) resolved by a global `≺` | user priority in the same slot; textual order does not exist (same LTS) |
| D4 | eager hiding | lazy hiding (outsiders before/after hidden steps duplicate targets) |
| D5 | views must be well behaved and synchronous (hypotheses) | relativise `no-new-comm/step` to `Ρ` (changes the theory) |
| D6 | internal loops allowed; only exits count; `Exits` required | forbid loops (`Acc`); model them as local computation (needs local steps) |
| D7 | `WellBehaved` up to `~`: weak `step-deterministic` and `step-diamond`, no `stepback/~` (Step 1) | keep the exact forms; quotient/minimise views (a recomputation) |
| D8 | process syntax unchanged | acting-role annotations (unneeded: a process is one role in its view) |

## Evidence (`Tests/Quotient.agda`, ordered views)

Accepted: `RoundRobin`, `OAuth2`, `Rec2Buy`, `CounterExamples` (forward), `RecMW` — all
pairs; `NoSynGT`, `Multicast` — `{A,B}`, `{B,C}`; `LabelSorts` — `{A,B}`, `{B,C}`; the
square — both views; `P→Q#i . Q→R#i` — `{P,Q}`. Rejected, correctly: `LabelSorts` `{A,C}`
(one label, two sorts). `RecMW` `{W2,R}` needs the different-senders conflict.

## Open

- Progress (Step 7).
- Whether every consumer in 1b only transports forward.
- `≺` as a parameter of `⊢s` instead of fixed.
