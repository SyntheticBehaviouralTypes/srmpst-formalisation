# PLAN.md — one process, many roles, by local views

*Written 2026-10-02 on `set-typing`. Design only: nothing below is implemented in the
metatheory. `Tests/Quotient.agda` is a working prototype of the views on finite graphs
(§9), and the numbers in §9 come from it.*

**Terminology.** A **role** is a name in the global specification (`Part = Fin N`). A
**process** is code implementing a set of roles `Ps`. A session runs over a static
**assignment** of roles to processes whose sets partition `Fin N`. A process is
**multi-role** when `Ps` has more than one role, and a **singleton** otherwise.

## 0. The idea

A multi-role process is typed exactly as a single-role process is today, against its own
**local view** of the specification. The view is the original LTS seen by that process:

1. its roles **merge** into one; every other role stays individual;
2. steps among its own roles are **hidden**: the process makes such choices itself, at its
   next external action;
3. where it would face a **conflict** — a mixed choice, or receiving from two different
   senders — it keeps the step that comes first in a fixed global order.

Singleton processes are typed against the original LTS, unchanged. Only the roles of a
merger know about it: everybody else still sees individual roles.

The view is a **layer on `BTheory`** (§2): same carrier, a new step relation defined from
the old one. Nothing is recomputed; only the checker (§8) builds views concretely.

**What stays.** `BTheory`, `Synchronous`, actions, the process syntax, and the single-role
typing rules (`⊢p`, `⊢a`) are unchanged. `WellBehaved` is restated up to bisimilarity
(§5.1); that is the only change to the theory, and it is what lets a view be used without
minimising it. Graphs are still one instance.

## 1. Example

`P → Q . R → S . end` is the LTS (the same LTS as `R → S . P → Q . end`):

```
0 -[ P→Q ]-> 1     1 -[ R→S ]-> 3
0 -[ R→S ]-> 2     2 -[ P→Q ]-> 3
```

Under the assignment `{P,S}` / `{Q,R}`, merging alone gives, for `{P,S}`,

```
0 -[ PS→Q ]-> 1    0 -[ R→PS ]-> 2    1 -[ R→PS ]-> 3    2 -[ PS→Q ]-> 3
```

which is not well behaved: a mixed choice at `0`. The order (§2.3) keeps `P→Q` at `0` in
**both** views, so the views are

```
{P,S}:  0 -[ PS→Q ]-> 1 -[ R→PS ]-> 3        {Q,R}:  0 -[ P→QR ]-> 1 -[ QR→S ]-> 3
```

both well behaved and synchronous, and the two processes agree on the order.

## 2. Local views

```agda
module View {N} (B : BTheory N) (Ps : PartSet) (p : Part) where   -- p ∈ Ps names the process
  open BTheory B
```

### 2.1 Relabelling

`⌊_⌋ : Action → Maybe Action` collapses the roles of `Ps` onto `p` and keeps every other
role. A multicast `P ⟶ Qs # c` becomes `ρ P ⟶ (ρ Qs ∖ ρ P) # c`, where `ρ` sends `Ps` to
`p`; if no receiver is left, the step is **internal** and `⌊ α ⌋ ≡ nothing`. A multicast
from outside to several roles of `Ps` becomes one receive. A multicast from a role of `Ps`
to some of its own roles and some outside keeps only the outside receivers.

The view is a `BTheory N`, with the same `N`: in it the process is role `p`, and the other
roles of `Ps` never appear. So the typing judgment needs no re-indexing.

### 2.2 Hiding

```agda
  _-τ->_ : Behav → Behav → Set
  G -τ-> G′ = ∃[ α ] G -< α >-> G′ × ⌊ α ⌋ ≡ nothing

  Stable : Behav → Set
  Stable G = ∀ {G′} → ¬ G -τ-> G′
```

Hidden steps are **eager**: a state with an internal step pending offers what the stable
states it reaches by hidden steps offer. A state reaching several stable states is the
process's own **internal choice**, made by its next external action. An outsider can never
act at an unstable state of the view; it acts after the hidden steps (which the session
never performs; §4).

### 2.3 Order

```agda
  Kept : Behav → Action → Set
  Kept G α = ∀ {β G′} → G -< β >-> G′ → Conflict Ps β α → ¬ comm β ≺ comm α
```

- `Conflict Ps β α`: both steps are external for `Ps`, and either `Ps` sends in one and
  receives in the other (**mixed choice**), or `Ps` receives in both from **different
  senders**.
- `≺` is a fixed decidable strict total order on `Comm = Vec (Maybe Shape) N`, e.g.
  lexicographic. It is global: the same for every view.

### 2.4 The view

```agda
  _-<_>->ᵛ_ : Behav → Action → Behav → Set
  G -< β >->ᵛ G″ = ∃[ G₁ ] ∃[ α ] Star _-τ->_ G G₁ × Stable G₁
                 × G₁ -< α >-> G″ × Kept G₁ α × ⌊ α ⌋ ≡ just β

  view : BTheory N
  view = record { Behav = Behav ; _-<_>->_ = _-<_>->ᵛ_ }
```

`Stable` and `Kept` are negative; that is fine, since a step is a relation and not an
inductive type. Decidability is needed only on graphs (§8).

## 3. Conditions on a session

For an assignment `Ρ` and an original theory `B`:

1. `B` is well behaved and synchronous (today's hypotheses).
2. For every multi-role process `Ps` with name `p`:
   - `WellBehaved (View.view B Ps p)` and `Synchronous (View.view B Ps p)`;
   - **no internal loops**: `∀ G → Acc (flip _-τ->_) G`, i.e. there is no infinite run
     of steps internal to `Ps`.

Both view conditions are hypotheses, like well-behavedness of `B`: neither is free.
`balanced` holds by construction (a relabelled step is external, so it has a receiver
outside the process and a sender inside it); `no-new-comm/step` must be checked.

With no internal loops, every state reaches a stable state by hidden steps, so §2.2's
eager closure is total and no state of a view looks `ended` while the process is busy.

## 4. Typing and semantics

**Typing.** A multi-role process `Ps ◃ Pr` is typed by today's single-role judgment at
role `p` against its view: `Γ & Δ ⊢p p ◂ Pr ∶ G` in `MPST (wb-view Ps)`. A singleton
`⁅ P ⁆ ◃ Pr` is typed as today against `B`. A session is typed when every process is,
at the common initial state, and `Ρ` partitions the roles.

**Syntax.** Unchanged. In its view a process is `p`, and every other role is individual, so
its code names partners by **role**, exactly as a single-role process does. Its own other
roles never appear in its code.

**Semantics.** A session step is a multicast of the original LTS, resolved through the
assignment: a send `Qs ! …` by the process owning the sender meets, for each process that
owns a role of `Qs`, one receive. Hidden steps are never performed by the session. So a run
of the session is a run of the original LTS with each process's hidden steps inserted.

## 5. Metatheory

### 5.1 Well behaved up to bisimilarity

On the fly, a view keeps all of `B`'s states, including states that become bisimilar in the
view: an unstable state with one hidden successor behaves like that successor, and two
targets of one merged multicast may coincide (`Examples/NoSynGT.agda` under `{B,C}`). Two
fields of `WellBehaved` are stated up to identity, and fail on such duplicates:

| field | change | uses today |
|---|---|---|
| `step-deterministic` (`G′ ≡ G″`) | conclude `G′ ~ G″` | `Behav.agda` (`branch/before`) and `AlgNorm.agda` (`sendAt`), both by `rewrite`; becomes a `~` transport |
| `stepback/~` | **delete** | through `skip/bisim` only: `td/bisim`'s `t/unskip` case (`Properties.agda`) and `after/~` (`AlgNorm.agda`) |

To delete `stepback/~`, the two places that transport backwards take a `~` at the end of
their run: `t/unskip` takes `H -[¬ P ]->* G″` and `G″ ~ G`, and `After` likewise. Their
transport then composes `~`; every other transport is already forwards (`tr-transport`).
Graphs remain an instance (they satisfy the stronger statements).

### 5.2 Per-process results

Preservation and termination are stated per process against its own theory, and hold by
today's proofs once §5.1 is done. The one new lemma links a view to the original:

- `view/run`: a step of the view is a run of `B`: hidden steps of `Ps` followed by one
  external step whose relabelling is the view's action.

### 5.3 Why the order is consistent

- **Only interleavings are removed.** In a well-behaved `B`, two steps from one state where
  `Ps` sends in one and receives in the other (or receives in both, from different senders)
  are not related by `recv-overlap`, so they are `⋄` and `step-diamond` commutes them. A
  pruned step is still available after the kept one.
- **Every view prunes the same step.** `≺` is on role-level comms, and global.
- **A pruned step involves the process that pruned it.** So nobody can perform it without
  that process; processes that did not prune it wait for it, and it comes back after the
  kept step.

### 5.4 Progress — open

Processes are typed against different theories (each multi-role process its view, the
singletons `B`), so there is no common theory and today's progress proof does not apply as
it stands. It must go through the original: a stuck session gives, per process, a head that
its view enables, and `view/run` turns each into a run of `B`. The intended argument takes
the `≺`-least enabled external step of `B`: no view prunes it, so every process involved
keeps it. The case to close is a process holding that step behind a concurrent send it may
order freely. An attempted counterexample failed (the receiver's view sees the two sends as
one sender's choice of labels, so it must accept both orders), but that is evidence, not a
proof. **This stays open.**

## 6. Decisions

| # | decision | alternatives considered |
|---|---|---|
| D1 | One view per multi-role process; singletons use the original LTS. | One global quotient for all processes: makes everyone name processes, not roles, and is stronger than needed. |
| D2 | A view is a layer on `BTheory` (same carrier), not a new graph. | Compute a quotient graph and minimise it: what the prototype does; fine for a checker, not for the typing system. |
| D3 | Conflicts (mixed choice, receive from different senders) are resolved by a fixed global order `≺` on comms. | No order: rejects every concurrency between a process's sends and receives. An order chosen by the user (a priority on roles or comms) fits the same slot. The textual order of a specification is not available: `P → Q . R → S` and `R → S . P → Q` are one LTS. |
| D4 | Hidden steps are eager. | Lazy hiding (weak steps from any state): an outsider's action could then be matched before or after a hidden step, which duplicates targets. |
| D5 | Views must be well behaved **and** synchronous; both are hypotheses. | Relativise `no-new-comm/step` to the assignment: changes the theory instead of the view. |
| D6 | **No internal loops** (`Acc` for `_-τ->_`). | Allow loops with exits (the prototype does): the loop is then a local computation, which the process calculus does not model. Adding local steps to the calculus would allow it later. |
| D7 | `WellBehaved` up to `~`: weak `step-deterministic`, no `stepback/~`, `~` built into `t/unskip`/`After`. | A setoid carrier, or minimising views: heavier, and the latter is a recomputation. |
| D8 | Process syntax unchanged. | An acting-role annotation on sends/receives: unnecessary, since in its view a process is one role. |

## 7. Plan of work

1. **§5.1 alone**, on the existing development: weaken `step-deterministic`, delete
   `stepback/~`, add `~` to `t/unskip` and `After`, repair the four use sites and the graph
   instance. Everything must still check; this is independent of views.
2. `Definitions/View.agda`: `⌊_⌋`, `_-τ->_`, `Stable`, `Conflict`, `≺`, `Kept`, `view`,
   and `view/run`.
3. Session semantics over an assignment (`Proc.agda`), and `⊢s` with per-process theories.
4. Preservation and termination per process (§5.2).
5. Progress (§5.4).
6. Graph instance and checker (§8).

## 8. Checker

On a finite graph each piece is decidable: relabelling is a function on actions, `Stable`
and `Kept` inspect one state's edges, the hidden closure is a walk, and "no internal loops"
is acyclicity of internal edges. The checker may build each view as a graph (as the
prototype does), check `wellBehaved?` and `synchronous?` on it, and run today's checker at
role `p`. Making it compute on the fly is an optimisation, not a requirement.

## 9. Evidence: `Tests/Quotient.agda`

The prototype builds views as graphs — relabel, hide (eager), order, keep the reachable
part, minimise by bisimilarity — and forces `wellBehaved?`/`synchronous?` on each. Every
original passes. With ordering (`OV`: mixed choices only; `OV⁺`: both kinds of conflict,
tested where it matters — `RecMW` `{W2,R}` needs it, `LabelSorts` `{A,C}` stays rejected):

| protocol | views accepted | rejected |
|---|---|---|
| `Examples/RoundRobin` | all pairs | — |
| `Examples/OAuth2` | all pairs | — |
| `Examples/Rec2Buy` | `{B,S}`, `{A,S}`, `{A,B}`* | — |
| `Examples/NoSynGT` | `{A,B}`, `{B,C}` | — |
| `Examples/CounterExamples` (forward) | all pairs | — |
| `Tests/Multicast` | `{A,B}`, `{B,C}` | — |
| `Tests/LabelSorts` | `{A,B}`, `{B,C}` | `{A,C}`: one label, two sorts — correct |
| `Examples/RecMW` | all pairs | — |
| §1's square | `{P,S}`, `{Q,R}` | — |
| internal choice `P→Q#i . Q→R#i` | `{P,Q}` | — |

\* `Rec2Buy` under `{A,B}` turns the split/no negotiation into an internal loop. The
prototype accepts it by keeping only the loop's exits; under D6 it is rejected. The
prototype must be brought in line: an internal cycle should be `inadmissible`.

Where the prototype differs from this plan: it allows internal loops (above), and it
identifies states (by hidden-closure sets, then bisimilarity) where the plan relies on
§5.1 instead.

## 10. Open

- **Progress** across views (§5.4).
- `view/run` and whether §5.1 suffices for every use of `WellBehaved` in a view (to be
  confirmed once step 1 of §7 is done).
- Whether the order `≺` should be a parameter of `⊢s` (a user priority) rather than fixed.
- Local computation steps in the calculus, which would let D6 be lifted.
