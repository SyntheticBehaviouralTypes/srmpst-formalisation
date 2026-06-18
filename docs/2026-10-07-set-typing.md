# PLAN.md — one process, many roles, by local views

*Updated 2026-10-07, `set-typing`. Steps 1–3, Step 6 (projection, `follow`, `existence`,
`preservation/comm`), progress and termination for local typing, and the checker (Step 8)
are done and checked; `Tests/ViewsSession.agda` runs them end to end. **The global
order is dropped and hiding is lazy**: see "Current direction" right below (definitions,
lemmas, proofs, checker, order of work), which supersedes the order-based parts of Steps
2, 3, 6 and 7 (kept further down as the previous design). `Tests/Quotient.agda` is the
evidence for the current design ("Evidence").*

**Terms.** A *role* is `Part = Fin N`. A *process* implements a role set `Ps` (a *block*);
an *assignment* `Ρ` partitions `Fin N` into `K` blocks (`Assignment`, `Definitions/Proc.agda`).
*Multi-role*: `|Ps| > 1`.

**Idea.** Process code names the role that acts (`P ⇒ Qs ! …`, `R ⇐ P ？· …`), and a
process is typed at its role SET by today's judgment, generalised from one role to a set.
Each process is typed against its own **local view** of the LTS: its internal steps
hidden (any run of them before each of its own actions), nothing renamed, nothing
pruned; at a send or a receive the process acts on ONE role (`Focus`, a premise of the
typing rules), so no hypothesis beyond typing is needed for progress. Safety is stated against a **global view**, in
which the internal steps of every block taking part in a step are hidden. Local and global views are
related by **projection** (Step 6), not by transferring typings; a process's typing
never depends on how other roles are implemented.
A view is a `BTheory` on the same carrier and the same labels (no graph is built); only
the theory changes, and only so that views can be used without minimising them (Step 1).

**Example.** `P → Q . R → S` (the same LTS as `R → S . P → Q`) is the square
`0 -P→Q-> 1 -R→S-> 3`, `0 -R→S-> 2 -P→Q-> 3`. Under blocks `{P,S}`/`{Q,R}`, `{P,S}` has a
mixed choice at `0` (`P` sends, `S` receives): two roles able to act, so no code for
`{P,S}` types at `0` (`Focus`, §C). The order-based design below tried to resolve it instead; §A says why
that cannot work.

---

## Restructure (2026-10-07): views by default — DONE

**Outcome** (everything below checks: `Safety.agda`, `Check.agda`, every
`Examples/` and `Tests/` file):

- Judgments (`Typing/Declarative.agda`, `module Sessions B`):
  `⊢ᵛ[ Ps ] Pr ∶ G` (process `Pr` at role set `Ps`, typed against `Ps`'s
  view, with the view's `WellBehaved`) and `⊢s[ Ρ ] M ∶ G = ∀ j → ⊢ᵛ[ roles j ]
  M[j] ∶ G`.  No `ProcessTyping`/`SessionTyping`/`Progress` aliases.
- `Safety.agda` states, for every assignment: `preservation`,
  `preservation/τ`, `progress` (`done M ⊎ ∃ α M′. M [ α ]⇒ M′`),
  `progress/eventual`, `no-infinite-τ-reductions`, `replay`, `continue`, and
  `safety`: for any run `M =[ αs ]⇒* M′` (`Proc.agda`), the global view runs
  `G -[ αs ]->ᵍ G′`, `⊢s[ Ρ ] M′ ∶ G′`, and for every `n`, `M′` runs to a
  finished session or through `n` communications.  (Not "some run reaches
  `done`": false for non-terminating protocols.)  `singleton/⊢s`: per-role
  typings against `B` type the session at `singletons`.
- R1 went further than planned: views need NO synchrony at all.  `Balanced`
  of a view comes from `B` (`balanced/view`), and a view is checked by
  `wellBehaved?` only.  The relay view RecMW `{M,R}` now passes, but `{M,R}`
  is still rejected at typing (`Focus`: `M→W2` races `W1→R`).
- `Check/Graph.agda`: `typecheck WR Ps Pr : Dec (⊢ᵛ[ Ps ] Pr ∶ initial)` decides
  the view itself; `typecheckSession WR Ρ M : Dec (⊢s[ Ρ ] M ∶ initial)` is
  `all?` of it.  Same in `Check/Network.agda`.
- Examples: every partition of every protocol except IndepW (accepted ones
  with `M-safe = safety Ρ M-typed`; rejected ones as forced `false`).
  RecMW: 9 of 15 accepted.  Cost: IndepW (singletons only) 155 s / 2.3 GB, as
  each role's view graph of the flattened net runs `wellBehaved?`; a
  singleton could reuse `G`'s certificate (`singleton⇒`/`singleton⇐`)
  instead.
- R7: README and CLAUDE.md updated.  Sections below this one are the design
  record and keep the names of their time (`⊢ᴸ`, `Safety/Views/`, …).

Multi-role typing is THE theory; single-role typing is its singleton case. No parallel
single-role development is kept. Decided 2026-10-07: semantics per process, `⊢ᴾ` deleted,
view synchrony dropped where possible.

**R1. `Balanced` (`Behav.agda`); no synchrony hypothesis on views.** Split
`Synchronous`: `record Balanced B` holds `balanced` and what is derived from it
(`send-action`, `recv-sender`, `recv/foreign`, `send-det`); `Synchronous B` is
`Balanced B` plus `no-new-comm/step`. The `⊢p → ⊢a` half (`AlgNorm`, `Substitution`'s
`⊢a` faces, `Check/TypeCheck`) takes `Balanced`. New: `balanced/view : Balanced B →
Balanced (view Ps)` (a view step is a `B` step with the same label). `syncL` is dropped
from `Safety/Views/*`; a view is checked by `wellBehaved?` only. Grounds: the views'
`Synchronous` is used only through `send-action`/`recv-sender`/`send-det` (checked
2026-10-07); their `no-new-comm/step` never. Expected: relay blocks (RecMW `{M,R}`)
accepted.

**R2. Semantics per process (`Proc.agda`).** `Assignment` and `byOwner` move into
`Proc.agda` (`Definitions/Assignment.agda` deleted). `Session Ρ = Vec (Proc 0 0) K`;
`_[_]⇒_`, `_τ⇒_`, `_⇒∞`, `done`, `finished` are today's `Assignment.Over` ones. The
per-role semantics is deleted. Single-role sessions: the assignment `singletons =
byOwner id`.

**R3. Session typing (`Typing/Declarative.agda`, top level beside `MPST`).**

```agda
⊢s_∶_ : Session Ρ → Behav → Set
⊢s M ∶ G = ∀ j → Σ[ wb ∈ WellBehaved (view (roles j)) ]
                  MPST._&_⊢p_∶_ wb [] [] (roles j ◂ lu M j) G
```

Each process carries its own view's certificate, so nothing about views is a
hypothesis of the theorems. (Replaces `Typed.⊢ᴸ` with module parameters `wbL`/`syncL`.)

**R4. Safety over views by default.** `Safety/Views/{Preservation,Progress,Termination}`
move to `Safety/` (replacing the single-role proofs, which are deleted), stated over R3's
`⊢s` (inside, `wbL j = proj₁ (ts j)`); hypotheses `WellBehaved B`, `Synchronous B`.
Deleted: `Safety/Assignment.agda`, `Safety/Assignment/*`, `Typing/Assignment.agda` (`⊢ᴾ`).
Single-role results as the singleton case: a singleton view has exactly `B`'s steps (no
step is internal to one role, by `balanced`), so `Transfer` turns typing against `B` at
`⁅ P ⁆` into typing against `view ⁅ P ⁆` (`singleton/⊢s`, `Safety.agda`).

**R5. Checker, generalised in place (`Check/Graph.agda`).** `typecheck WR Ps Pr` decides
`wellBehaved?` of `Ps`'s view graph, then types `Pr` against it (`Check/View.agda`'s
transfer), returning `Σ wb, ⊢p`; `typecheckSession WR Ρ M : Dec (⊢s M ∶ initial …)` is
`all?` of `typecheck` per process. `WBGraph` keeps the certificates of `G` itself.
`typecheckNet`/`typecheckSessionNet` and `Check/Core`'s aliases follow.

**R6. Examples and tests, in place.** Every `Examples/*.agda` types its protocol under
EVERY partition of its roles (one `typecheckSession` per partition); a rejected partition
states the failing verdict. `IndepW` (7 roles: 877 partitions; a net) keeps its singleton
session. `Tests/` adapted.

**R7. Docs.** README, CLAUDE.md, this file ("Current direction" §H, Evidence).

Order R1 → R2 → R3/R4 → R5 → R6 → R7; each step checked with plain `agda` on its roots.
"Open" below is unchanged for now (R1 is expected to close the relay item).

---

## Current direction (2026-10-06): one role at a time, lazy views

Supersedes the order-based parts of Steps 2, 3, 6, 7 below. Everything about Step 1,
role annotations, Step 4, Step 5 (local typing) and `follow` stands. The two principles
the design follows:

- **(a) a sender may send FEWER labels.** A block's internal steps before one of its
  sends are the block's own choice; its derivation picks one send among those the view
  offers.
- **(b) a receiver may expect MORE labels.** A block's internal steps before one of its
  receives are nobody's choice to wait for; its derivation (`t/recv`'s `conts`) covers
  every receive through every prefix.

Hiding is LAZY for both: an own step of a block's view is any run of the block's
internal steps, then the step. An earlier version (sender-stable: a send only from a
state with no internal step pending) made `existence` unprovable as sketched (§E,
"Why not sender-stable") and is dropped (D17).

### A. Why the order goes

With roles named (D8), two conflicting steps enabled at one state never share a
participant (a shared role would be a receiver of one taking part in the other, and
`recv-overlap` would make them the same communication). So whenever pruning removes `α`
because a smaller conflicting `β` is enabled, `α` is still enabled after `β`
(commutation) and reappears right after a step sharing no participant with it: the view
violates `no-new-comm/step`. Measured on the merged-name prototype with names kept
(scratch variants of `Tests/Quotient.agda`, violations printed by Agda):

| view | all pruning | sends only |
|---|---|---|
| square `{P,S}` | `notSync` | ok (nothing pruned under `P ≺ R`) |
| square `{Q,R}` | `notSync` | `notSync` |
| 2a `{P,S}`, `P ≺ R` (and per state) | `notSync` | ok |
| 2a `{P,S}`, `R ≺ P` | `notSync` | `notSync` |
| RecMW `{W1,W2}`, `{M,R}`, `{M,W1}` | `notSync` | `notSync` |
| RecMW `{W2,R}` | `notSync` | ok |
| all others in the evidence table | ok | ok |

Each violation is "step taken, then the pruned step appears" (RecMW `{W1,W2}`: `M→W2` then
`W1→R`; square `{Q,R}`: `P→Q` then `R→S`). Send-only pruning is not enough either: in the
square with `P ≺ R`, `{P,S}` may then wait for `R→S` first and `{Q,R}` for `P→Q`:
deadlock. So an assignment passes `Synchronous` of its views only if pruning removes
nothing; the order is only a rejection device, and rejecting races directly (`NoRace`,
§C: `Focus` at every send and receive) gives the same verdicts while keeping
`no-new-comm/step` for the views.

Cost: the square under `{P,S}`/`{Q,R}`, 2a (`{P,S}`, which the old design accepted
under either order), RecMW `{W1,W2}`, `{M,R}`, `{M,W1}` and NoSynGT `{B,C}` are
rejected (`Tests/Quotient.agda`). Externally, a multi-role process acts on one
role at a time. (RecMW `{M,R}` is also a *relay*, rejected by `no-new-comm/step` of its
view for a different reason: `W2→R` then, through the hidden `R→M`, `M→W1`; see Open.)

### B. Definitions (`Definitions/View.agda`) — DONE

Parameters: `B : BTheory N`. No `_≺_`.

```agda
module Block (Ps : PartSet) where
  Internal : Action → Set
  Internal α = ∀ X → X ∈α α → X ∈ Ps                 -- the block talks to itself

  _-τ->_ : Behav → Behav → Set
  G -τ-> G′ = ∃[ γ ] G -< γ >-> G′ × Internal γ

-- THE LOCAL VIEW of block Ps (Ps is one block, everybody else a singleton)
module Local (Ps : PartSet) where          -- opened publicly
  Idle : Action → Set
  Idle α = Ps ∉αˢ α

  _-<_>->ᵛ_ : Behav → Action → Behav → Set
  G -< α >->ᵛ G″ =
      (Idle α × G -< α >-> G″)                                        -- D10
    ⊎ (¬ Internal Ps α × Ps ∈αˢ α
       × ∃[ G₁ ] Star (_-τ->_ Ps) G G₁ × G₁ -< α >-> G″)              -- lazy

  view : BTheory N

-- THE GLOBAL VIEW of an assignment (not opened: `open Global Ρ`)
module Global {K} (Ρ : Assignment K) where
  block : Part → PartSet
  block X = lu roles (owner X)

  -- Internal to the block of a participant of α (hence hidden before α).
  τ⟨_⟩ : Action → Behav → Behav → Set
  τ⟨ α ⟩ G G′ = ∃[ γ ] G -< γ >-> G′ × ∃[ X ] X ∈α α × Internal (block X) γ

  Hidden : Action → Set
  Hidden α = ∃[ X ] X ∈α α × Internal (block X) α

  _-<_>->ᵍ_ : Behav → Action → Behav → Set
  G -< α >->ᵍ G″ = ¬ Hidden α × ∃[ G₁ ] Star τ⟨ α ⟩ G G₁ × G₁ -< α >-> G″

  global : BTheory N
```

Remarks.
- Internal choice concurrent with an own action (the action available via `ε` and via
  a prefix `p`, with `p` one branch of a choice) can make the view non-deterministic up
  to `~`; then `wellBehaved?` rejects it.
- `Exits` is not needed: a block whose internal steps never lead to an external step
  has no own step in its view.
- Both views are `BTheory`s on `B`'s states and labels; nothing is renamed or built.

### C. Hypotheses

```agda
WellBehaved B,  Synchronous B                                   -- as today
WellBehaved (view Ps),  Synchronous (view Ps)   for every block  -- decided on the view
                                                                  -- graph (Step 8)
```

No other hypothesis: what `existence` (case iii) and progress need of a block is a
premise of its typing rules (D19), decided by the checker with the leaf:

```agda
-- Behav (per theory; used in the view): the process implementing P acts at role X
-- only, at G and wherever outsiders can move G to.
Focus P X G = ∀ {G′ β G″} → G -[¬ P ]->* G′ → G′ -< β >-> G″ → P ∈αˢ β → X ∈α β
t/send : Q ∈ P → Focus P Q G → G -<[ Q ↦ (! Qs) # i < S > ]>-> G′ → …
t/recv : R ∈ Q → Focus Q R G → G -<[ Q ∣ R ↦ (？ P) # i < T > ]>-> G′ → …
Dom P Q e, Offers Q P R I          -- a/send, a/recv: the leaves carry Focus
```

`Focus` is trivial for a singleton (`focus/⁅⁆`), closed under `~` and under outsiders'
runs (`t/unskip`). It rejects, at the state where the code faces it, every former
conflict (mixed; two sends by different own roles; two receives from different senders)
and the former gap (two receives from the same sender at different own roles, NoSynGT
`{B,C}`). A choice by ONE role (`P` sends to `Q` or to `R`; two labels to one partner)
stays allowed, as do internal choices and a multicast to two own roles (one step).
Earlier this was a view-level hypothesis `NoRace` (all states, all own steps), used by
progress only, so a typed session could be stuck; D19 moves it into typing.

### D. Lemmas (`Definitions/View/Lemmas.agda`) — DONE

Kept: `send/recv`, `sender/same`, `singleton/external`, `swap`, `push-aux`, `Mixed`,
`τs/~`, `split`. New:

```agda
local/idle : Ps ∉αˢ α → G -< α >-> G″ → G -< α >->ᵛ G″                    -- D10
local/~    : G ~ H → G ~ᵛ H                     -- bisimilar in B, bisimilar in the view

module _ (Ρ : Assignment K) where
  -- D4. A global step found after a step β involving no block of α's participants
  --     was available before β (`swap` along the hidden prefix, `no-new-comm/step`).
  pullback : G -< β >-> t → (∀ X → X ∈α α → block X ∉αˢ β)
           → t -< α >->ᵍ t′ → ∃[ G′ ] G -< α >->ᵍ G′

  module Projection (j : Fin K) where              -- Ps = lu roles j
    -- D3. Projection of a global step onto a block's local view.
    project/idle : Ps ∉αˢ α → G -< α >->ᵍ G′ → G -[¬ Ps ]->* G′
    project/own  : Ps ∈αˢ α → G -< α >->ᵍ G′
                 → ∃[ H ] ∃[ H′ ] G -[¬ Ps ]->* H × H -< α >->ᵛ H′ × H′ ~ G′
    -- D5. An own step of the local view is a global step.
    own/global   : Ps ∈αˢ α → G -< α >->ᵛ G″ → G -< α >->ᵍ G″
```

Not needed (planned earlier as D1, D2): `internal/inert`, `internal/keeps`. Deleted:
`stable/*`, `kept/*`, `conflict/*`, `comm/sender`, `SenderFirst`, the grouping lattice.

### E. Existence (`Safety/Views/Preservation.agda`, `module Exists`) — DONE

```agda
module Exists where
  module Comm (P∈ : P ∈ lu roles j)
              (recvs : ∀ k → Receives j Qs k → Rk k ∈ Qs × Rk k ∈ lu roles k
                                             × ⊢ᴸ_k  lu roles k ◂ Rk k ⇐ P ？· Br k ∶ G₀) where
    existence : Wait Ps (Dom P ((! Qs) # c)) ([] , G₀) → ∃[ G′ ] G₀ -< P ⟶ Qs # c >->ᵍ G′
  preservation/comm : ⊢ᴸ M ∶ G → M [ just α ]⇒ M′ → ∃[ G′ ] G -< α >->ᵍ G′ × ⊢ᴸ M′ ∶ G′
```

Recursion on the SENDER's tree only (`ready-or-∈T`, then `ready-from-∈T` on the `∈T`
run with `waitV/unfold-top`, as `comm/ready` today). The receivers' derivations stay at
`G₀`; the proof carries the run `Star Walk G₀ u` it has taken, where a `Walk` step is
internal to a receiving block or idle for the sender's and every receiving block. At a
`wv/step` (or `∈T` run step) `β`, idle for the sender's block, `kind β` decides:

- (i) `β` internal to a receiving block: recurse; `β` joins the hidden prefix (`extend`).
- (ii) `β` idle for every receiving block: recurse; `pullback` (D4) (`pull`).
- (iii) `β` involves a receiving block `k` externally: impossible (`busy`). The walk is
  `Mixed` for `k`; `split` gives `G₀ -[¬ k ]->* H`, `Star (_-τ->_ k) H H₁`, `H₁ ~ u`;
  so `β` is an own step of `k`'s view at `H`. `Per.receiver/busy`: `t/unskip` moves
  `k`'s derivation to `H`; `at/recv-inv` + `waitLeaf` give a receive `α′` from `P` in
  `k`'s view at `H`; the leaf's `Focus` puts `R_k` in `β`; `recv-overlap` of `k`'s view
  makes `comm α′ ≡ comm β`, so `P` takes part in `β`: contradiction.

Leaves: `own/global` (D5) and `send-action` of the sender's view.
`preservation/comm = existence ; follow`.

**Why not sender-stable.** With sends only from stable states, in (iii) `β` may be an
external send of `k` at a state where `k` has an internal step pending: not a step of
`k`'s view, so `k`'s derivation says nothing about it, and the result found after `β`
cannot be pulled back (`s -X→U-> t -X→R-> t₂ -P→R->`, `s -X→Y-> s_Y`, block `{R,X,Y}`:
a global step at `t`, none at `s`). No counterexample to `existence` was found; the
proof would need `Stable Ps G ⊎ ∃ internal step` and an induction over two trees.
Lazy sends remove the case; the alternative hypothesis `SendStable` (no external send
with an internal step pending) rejects NoSynGT `{A,B}` and makes the views coincide
with lazy ones elsewhere.

### F. Progress (`Safety/Views/Progress.agda`) — DONE

```agda
progress          : ⊢ᴸ M ∶ G → done M ⊎ Progress M
progress/eventual : ⊢ᴸ M ∶ G → ∃[ M′ ] ((M τ⇒ M′ × finished M′)
                                      ⊎ (∃[ M″ ] ∃[ α ] M τ⇒ M″ × M″ [ just α ]⇒ M′))
```

Every derivation stays at `G`. The proof keeps a run `Star Walk G u` of steps each
internal to some block. To consult block `k` at `u`, `split/` (a `split` that keeps a
label property, here "internal to some block") moves the other blocks' steps first;
`k`'s derivation follows them (`t/unskip`), and `k`'s own internal steps become the
prefix of a step of `k`'s view (`Blk.see`).

1. `Head.status`: a block's code at `G` is `∅` (done), `if`/`rec` (τ step), or a
   send/receive; then `waitActive` gives a trace of its view on which it acts, and
   `trace/active` walks it: steps internal to their sender's block extend the walk;
   the first other step is `Active` (its sender's block takes part externally).
2. `Head.sender` at the `Active` step's sender block `l`: `∅` contradicts the step;
   `if`/`rec` step; a receive is impossible (its offered step is `Foreign`, i.e. sent
   from outside `l`; the leaf's `Focus` puts the receiving role in the `Active` step;
   `recv-overlap` of `l`'s view and `sender/same` put that outside sender in `l`); a
   send gives its leaf step
   `P ⟶ Qs # i < S >` after `l`'s internal prefix, which extends the walk.
3. `receivers`: for each receiving block `k`, `Blk.recv-head`: `∅` contradicts, `if`/
   `rec` step, a send is impossible (`Focus`, `recv-overlap`, `sender/same`: `P` would
   be `k`'s), a receive is from `P` at a role of `Qs` with the leaf's arity
   (`Focus`, `recv-overlap`, `ev-inv`, `step-arity-det` of `k`'s view). Then `fire`:
   `s/comm`.

Hypotheses: `WellBehaved`/`Synchronous` of each local view — the ones typing uses. No
`Exits`, no order, nothing of the global view, no `NoRace`.

**Receives from own roles (D18).** Progress was false for the previous receive rule:
`B = P → {R, X}`, blocks `{P, R}` and `{X}`, codes `R ⇐ P ？· (∅ ∷ [])` and
`X ⇐ P ？· (∅ ∷ [])` both typed (the decision procedure accepted the first), and the
session is stuck. A receive of a process is now a step sent from OUTSIDE its role set:

```agda
Foreign Q α = ∃[ S ] S ∉ Q × Send α S                                   -- Actions
s -<[ Q ∣ R ↦ e ]>-> t = ∃[ α ] ev α R ≡ just e × s -< α >-> t × Foreign Q α  -- Behav
t/recv : R ∈ Q → G -<[ Q ∣ R ↦ (？ P) # i < T > ]>-> G′
       → (∀ {j U G″} → G -<[ Q ∣ R ↦ (？ P) # j < U > ]>-> G″ → …) → … ⊢p Q ◂ R ⇐ P ？· Br ∶ G
Offers Q P R I, Postᴿ Q R e                                              -- Alg (a/recv)
```

For one role it changes nothing (`recv/foreign`: a receive's sender is another role).
The checker decides `Foreign?`; the example above is now rejected, the others unchanged.

### G. Termination

Done (`Safety/Views/Termination.agda`); unaffected by the view change (internal
steps are not session steps).

### H. Checker (Step 8) — DONE

All compile; the tests force their verdicts by `refl`:

- `Definitions/Transfer.agda`: two theories on the same states with equivalent steps
  (`to`/`from`) agree on everything used: `~⇒`, `wb⇒`, `sync⇒`, and typing
  (`Typing.typing⇒`, by induction on `⊢p`/`⊢skip`). General: any theory whose steps
  match a view's can stand in for it.
- `Definitions/Graph/View.agda`: `viewGraph G Ps`, the local view of block `Ps` as a
  graph on the same states: outsiders' edges as they are, plus, for every state `u` in
  the `τ`-closure of `s` (reachability over `Gτ`, `Ps`'s internal edges), the edges
  `Ps` takes part in at `u` not internally. `view⇒`/`view⇐`: its steps are exactly
  `_-<_>->ᵛ_ Ps`.
- `Check/View.agda`: `ViewOK G Ps` (`wellBehaved?`, `synchronous?` of the view graph),
  `wbᵛ`/`syncᵛ` (the certificates moved to `view Ps`, definitionally the theory of
  `Safety/Views/`), `typecheckView G Ps ok Pr s : Dec (ViewTyping …)` (`tc?` on the view
  graph, moved both ways).
- `Definitions/Assignment.agda`: `byOwner`, the assignment of an owner map.
- `Tests/Views.agda`: RoundRobin `A→B→C→A`, block `{A,B}`: view well behaved and
  synchronous; `B ⇒ C ! … ∙ A ⇐ C ？· …` accepted; `A ⇒ B ! …` (an internal step as
  code) rejected. ~3.5s.
- `Tests/ViewsSession.agda`: end to end. The RoundRobin session under blocks `{A,B}`,
  `{C}` (codes above and `C ⇐ B ？· (C ⇒ A ! … ∙ ∅)`); `ts : ⊢ᴸ M ∶ s₀` from
  `typecheckView` per block, then `progress` and `progress/eventual` of
  `Safety.Views.Progress` applied. ~6 s / 0.75 GB. A first attempt, via `byOwner`, was
  killed for memory; this one differs in a hand-written `Assignment` with concrete
  `roles` vectors (so `lu roles j` is literally the block each certificate was decided
  at) and `opaque` global witnesses `wb`/`sync` (as `Tests/SkipBeforeVar.agda`). Which
  of the two mattered was not measured. `Check/View.agda` needed no change.
- `Tests/Quotient.agda`: rewritten on this checker ("Evidence"). ~60 s / 0.9 GB.

### I. Order of work

1. DONE. `View.agda`: definitions of §B.
2. DONE. `View/Lemmas.agda`: §D. `follow` re-proved with D3; `Safety/Views/Termination`
   adapted. Full build.
3. DONE. `existence` (§E), `preservation/comm`.
4. DONE. Progress (§F), `progress/eventual`; `no-infinite-τ` in `Safety/Views/Termination`.
5. DONE. Checker and prototype (§H): view graph, transfer, `typecheckView`, end-to-end
   session, `Tests/Quotient.agda` rewritten.
6. DONE. PLAN.md: D3, D9, D11 (and D4, D6, D16) retired; D19 final.

Optional later (Open): relay blocks need `no-new-comm/step` of the views stated on
block FOOTPRINTS (participants' blocks) instead of participants; `comm/ready` only ever
pulls back through steps idle for every involved block, so this weaker axiom suffices
and is derivable from `B`'s. ~30 lines in `Behav.agda`/`Preservation.agda`.

---

# Previous design (global order), kept for reference

Steps 2, 3 and 6–7 below describe the order-based pruning that "Current direction"
supersedes. Everything not about `_≺_`/`Kept`/conflicts still holds.

## Step 1 — `WellBehaved` up to bisimilarity — DONE

`step-deterministic` gives `G′ ~ G″`; `step-diamond` closes up to `~`
(`∃ X Y, … × X ~ Y`); `stepback/~` is deleted. `t/unskip` takes its run's end up to `~`
(`tr : G -[¬ P ]->* G″`, `eq : G″ ~ G′`), so `td/bisim` transports forward only, and
`Unskip`/`After` (and the checker's `Unskip?`/`Past?`, via a tabulated `Reached`) end up
to `~`. On graphs, `SameTarget` and `Commutes` (over the edge lists) ask the shared
bisimilarity matrix, so `wellBehaved?` stays a full `Dec`; `Tests/Quotient.agda` no longer
minimises views and every verdict is unchanged.

Networks: `parWB` lifts the weak forms with `~-pair`. `seqWB` needs `Moves n₁` (no live
state of `n₁` is stuck; otherwise a stuck state is `~` the end, and `seamTo` separates
them): `Moves` composes through `∥`/`⨾` and is decided on base graphs only
(`WBNet.base` has `{m : T ⌊ moves? G ⌋}`), and `⨾` no longer decides `finiteStepback?`.
No check sweeps a composite.

### 1c. What weak determinism does and does not allow

- Allowed: one action to targets `b ~ c`, and diamonds closing up to `~`. Typing is
  invariant under `~` (`td/bisim`, `Closed`, `skip/cycle`'s `lu Ξ X ~ G`, `∈~`).
- Still excluded: targets that are not bisimilar.

## Role annotations and role-set typing — DONE

- `Proc`: `_⇒_!_<_>∙_ : Part → PartSet → …` and `_⇐_？·_ : Part → Part → …`.
- `NProc`: `_◂_ : PartSet → Proc γ δ → NProc γ δ`. "Takes part" is `Ps ∈αˢ α`, "idle" is
  `Ps ∉αˢ α`; `not-active-in`, `∈T`, `-[¬_]->*`, `Wait`, `Front`, `Unskip`, … are over sets.
- `t/send`/`t/recv` (and `a/send`/`a/recv`) check their event at the annotated role and
  require it in the set (`Q∈ : Q ∈ P`, `R∈ : R ∈ Q`).
- Single-role sessions are the singleton case: `⊢s M ∶ G = ∀ P → … ⊢p ⁅ P ⁆ ◂ M[P] ∶ G`, and
  `s/comm` requires the annotations to match the session's indices. Single-role
  preservation, progress, termination and the checker (now at a `PartSet`) go through;
  every example and test is annotated and keeps its verdict.

## Step 2 — Views of groupings (`Definitions/View.agda`) — DONE

```agda
module Block (Ps : PartSet) where
  Internal α = ∀ X → X ∈α α → X ∈ Ps            -- every participant is a role of Ps
  G -τ-> G′  = ∃ α, G -< α >-> G′ × Internal α
  Stable G   = ∀ {G′} → ¬ G -τ-> G′
  Multi      = ∃ two distinct roles in Ps         -- only then does Ps hide or prune
  Sends, Recvs, SameSender, Clash, Conflict β α  -- as before (D11; NOT two receives
                                                 -- from one sender, PLAN 1c)
  Kept G α   = ∀ {G′ β G″} → G -[¬ Ps ]->* G′ → G′ -< β >-> G″ → Conflict β α
             → ¬ comm β ≺ comm α                 -- closed under outsider runs (D9)
  Exits      = ∀ G → ∃ G₁, Star _-τ->_ G G₁ × Stable G₁

record Grouping where block : Part → PartSet ; block/self ; block/same   -- a partition
_≤_ : refinement;  singletons;  local Ps;  assigned Ρ

-- the view of a grouping 𝒢
Hidden α      = ∃ X ∈α α, Internal (block X) α
G -τ⟨ α ⟩-> G′ = a step internal to the block of some participant of α
Ready G α     = ∀ X ∈α α → Stable (block X) G × (Multi (block X) → Kept (block X) G α)
G -< α >->ᵍ G″ = ¬ Hidden α × ∃ G₁, Star τ⟨α⟩ G G₁ × Ready G₁ α × G₁ -< α >-> G″
SenderFirst   = between different senders, `≺` depends only on the senders
```

- `singletons`: the original theory (`singletons/⇒`, `singletons/⇐`); D1 holds because a
  singleton block hides and prunes nothing.
- `local Ps`: `Ps`'s local view; an outsider's step is `B`'s step as it is (D10,
  `local/idle`).
- `assigned Ρ`: the global view. A communication hides the internal steps of EVERY block
  taking part, and needs each of them stable and (if multi-role) keeping it.
- Labels are never renamed, so `Unambiguous` is gone (trivially true). Its old target,
  NoSynGT's `{B,C}`, becomes a progress question (Open).

### 2a. Why `Kept` is closed under outsider runs (D9)

Pruning tells the process which way to resolve a race. The process resolves it in its
code, once, without seeing what outsiders have done. So the resolution it is given at a
state must agree with the one it is given at every state outsiders can move it to.

**Protocol.** `(P → Q) ∥ (R → T . R → S)`, five roles:

```
0 : P→Q ↦ 1,  R→T ↦ 2
1 : R→T ↦ 3
2 : P→Q ↦ 3,  R→S ↦ 4
3 : R→S ↦ 5
4 : P→Q ↦ 5
5 : end
```

**Block `{P,S}`.** `P→Q` is its send (at `P`), `R→S` its receive (at `S`), `R→T` is idle.
Mixed choice only at `2`.

**Per-state pruning, `R ≺ P`.** `P→Q` pruned at `2`, kept at `0`. At `0`, `P→Q ⋄ R→T`, so
the view's own `step-diamond` demands `P→Q` at `2`: not well behaved; rejected, rightly
(`Q ! v . R ? x` typed at `0` would be invalid after the unobservable `R→T`).
**Per-state pruning, `P ≺ R`.** `R→S` pruned at `2`: accepted. The verdict flips with the
senders' indices.

**With `Kept` closed under outsider runs.** `R ≺ P`: `P→Q` is pruned at `0` too (state `2`
is idle-reachable); the view is `0 -R→T-> 2 -R→S-> 4 -P→Q-> 5`; accepted with
`S ⇐ R ？· x . P ⇒ ⁅Q⁆ ! v`. `P ≺ R`: as before. Both orders accept; `≺` chooses the shape
of the program, not the verdict, as D3 intends.

### 2b. Why an outsider's step is not hidden (D10)

Hiding exists so that the process's own next action is chosen after its internal steps;
an outsider's step is nobody's choice in this process. Routing it through the closure
breaks preservation for outsiders (`Gα ≁ G₁α`) and rejects an internal choice next to an
outsider (two non-bisimilar `α`-targets), e.g. `P→S#0 . S→R#0 + P→S#1 . S→R#1 ∥ T→U`
under `{P,S}`. With D10: one `α`-step to `Gα`, whose closure keeps the choice open.

## Step 3 — View lemmas (`Definitions/View/Lemmas.agda`) — DONE

| lemma | statement |
|---|---|
| `send/recv`, `sender/same`, `comm/sender` | a step has one sender, heard by every receiver |
| `singleton/external`, `/stable`, `/multi` | a single role hides and prunes nothing |
| `conflict/comm`, `conflict/⋄` | conflicting steps are different communications; pruning removes an interleaving |
| `stable/idle`, `kept/idle` | stability and keeping survive outsiders' steps |
| `stable/~`, `kept/~`, `ready/~`, `view/~` | bisimilar in `B` ⇒ bisimilar in any view |
| `view/run` | a view step is hidden steps of `B`, then the step |
| `singletons/⇒`, `singletons/⇐`, `local/idle` | the lattice's ends |
| `kept/sender` | under `SenderFirst`, two receives from one outsider are kept or pruned together |
| `swap`, `push-aux`, `split` | steps of disjoint blocks commute up to `~`; a mixed run reorders to outsiders-first |
| `Projection.project/idle`, `project/own` | a step of a grouping where `Ps` is a block is, in `Ps`'s local view, outsiders' steps, then (if `Ps` takes part) one own local step, ending `~` |

## Step 4 — Assignments and session semantics (`Definitions/Assignment.agda`) — DONE

`Assignment K` (`roles`, `owner`, `owner/∈`, `∈/owner`); `Processes = Vec (Proc 0 0) K`.
The semantics is label-based, on processes alone: `s/comm` — role `P ∈ roles j` of
process `j` at `P ⇒ Qs ! i < E >∙ Pr`, every OTHER process `k` owning a role of `Qs`
(`Receives j Qs k`) at `Rk k ⇐ P ？· Br k` with `Rk k ∈ Qs ∩ roles k`; label
`P ⟶ Qs # i < sort/value V >`. Roles of `Qs` owned by `j` receive with the send.
`s/if/*`, `s/rec` as before.

## Step 5 — `⊢s` — DONE (two forms)

- **Local typing (the design).** `⊢ᴸ M ∶ G = ∀ j → … ⊢p roles j ◂ M[j] ∶ G` in
  `view (local (roles j))` (`Safety/Views/Preservation.agda`, `Typed`). Hypotheses per `j`:
  `WellBehaved`, `Synchronous` of the local view; `Exits` of the block; `SenderFirst` and
  well-foundedness of `≺` (needed by Step 6's existence half).
- **Global typing (a special case).** `⊢ᴾ M ∶ G` types every process against one theory
  (`Definitions/Typing/Assignment.agda`); with the global view
  (`Safety/Assignment.agda`) preservation and termination are PROVED
  (`Safety/Assignment/{Preservation,Termination}.agda`: today's proofs with each role
  replaced by its block). It is stricter than needed: a process committed to a send that
  a partner block delays (e.g. `Ps` sends `P→X` while `X`'s block must first take a
  smaller conflicting step, and `Ps` has another kept send) has no derivation against the
  global view, though the session is fine.
- **Not pursued: "local typing ⇒ global typing".** False without a consistency
  hypothesis (partner blocks' pruning), and recursion anchors (`t/var`, `skip/cycle`)
  close up to the local view's `~`, which does not imply the global view's.

## Step 6 — Preservation and termination against the global view

The global state moves along global-view steps; each process's local derivation follows
its projection. A session step corresponds to a global step `G -< α >->ᵍ G′`
(`assigned Ρ`), and:

- **follow — DONE** (`Safety/Views/Preservation.agda`, `Typed.follow`): the sender and
  each receiver take outsiders' steps (`t/unskip`, lifted by `local/idle`), then their own
  local step (`at/send-inv`/`at/recv-inv` with an empty walk), then `td/bisim` by
  `view/~`; everyone else takes outsiders' steps only. `preservation/τ` done.
- **existence — NEXT**: if the sender's code is at `P ⇒ Qs !` and every receiver's at
  `R ⇐ P ？·`, the global view has that step from `G`. Today's `comm/ready` drives all
  waiting trees in lockstep in ONE theory; here a receiver's internal step is an
  outsider's step to the sender but hidden from the receiver. Plan:
  1. follow the sender's tree to its own step: its internal steps, then the send, kept;
  2. there, follow each receiver's tree (`waitFollow`): an inactive receiver would have a
     smaller conflicting step reachable, which is contradictory (needs `≺`
     well-founded), so each is at a leaf;
  3. the receiver's leaf gives an internal-step path to a stable state where some receive
     from `P` is kept; by `kept/sender` the actual send is kept; it survives the
     receiver's internal steps (`recv-overlap`: they cannot involve its receivers);
  4. assemble the involved blocks' internal-step paths with `split`/`swap`.
  Hypotheses: `Exits` per block; `≺` well-founded.
- **termination — DONE** (`Safety/Views/Termination.agda`): no infinite internal runs,
  `done` runs to `finished`. `MessageGuarded` lives in `Proc.agda` and the τ-depth
  measure in `Safety/Depth.agda`, so the measure sums over processes typed against
  different local theories.
- *(Superseded: the existence plan above relies on pruning; see "Current direction",
  step 4.)*

## Step 7 — Progress (open; superseded by "Current direction", step 6)

Against the global view: at a state where every block is stable, take the `≺`-least
external step; no block taking part prunes it, so each involved process's code must be
at it (mixed choice and different-sender receives are conflicts; two sends by different
own roles too, D11). **Gap:** two receives by DIFFERENT own roles from the SAME sender
(NoSynGT's `{B,C}`) are not a conflict (the sender orders them), but annotated code
commits to one order, so a session can be stuck. Either reject such states (a new
`Unambiguous`) or let a receive name a set of roles ("receive from `S` at whichever of
`B`, `C`").

## Step 8 — Checker

On graphs everything is decidable. Build each local view and the global view as graphs
(idle edges copied, own edges from the closure, D10; global: every involved block's
hidden prefix), check `wellBehaved?`/`synchronous?` (up to `~`, no minimisation), `Exits`,
and run today's checker at `roles j` against the local view. Rewrite `Tests/Quotient.agda`
for the current design (no merging, no `Unambiguous`; the `{B,C}` question of Step 7).
Optional: a proof that the graph construction is `View.agda`'s view.

---

## Decisions

| # | decision | alternative |
|---|---|---|
| D1 | singletons hide and prune nothing (a singleton block's view is `B`) | prune singletons too |
| D2 | views are a layer on `BTheory` | build and minimise graphs (checker only) |
| D3 | *(retired by D16)* conflicts resolved by a global `≺`, required `SenderFirst` (and well-founded) | arbitrary `≺` (breaks `kept/sender`: a receive could be pruned while its sender's twin is kept) |
| D4 | *(retired by D17)* eager hiding | lazy hiding |
| D5 | views must be well behaved and synchronous (hypotheses) | relativise the axioms |
| D6 | internal loops allowed; `Exits` required *(`Exits` retired by D17)* | forbid loops |
| D7 | `WellBehaved` up to `~`; no `stepback/~`; `wellBehaved?` stays a `Dec` | exact forms + minimisation |
| D8 | code names the acting role; a process is typed at its role set | merge roles under one name (cannot tell which role sends; receivers name roles) |
| D9 | *(retired by D16)* `Kept` closed under outsider runs | per-state pruning |
| D10 | an outsider's step is `B`'s step | route through the closure |
| D11 | *(retired by D16; D19 rejects the same race at typing)* two sends by different own roles conflict | leave them free |
| D12 | views of groupings (a lattice): local = `{Ps}` + singletons, global = the assignment | one view per process only |
| D13 | processes typed against LOCAL views; safety against the GLOBAL view, related by projection | type against the global view (too strict); transfer local ⇒ global typing (false without extra hypotheses) |
| D14 | label-based session semantics | configuration semantics `(M , G)` (rejected) |
| D15 | `Moves` for `⨾` networks, decided on base graphs | decide `finiteStepback?` on composites |
| D16 | *(retired by D19)* reject races, by a view-level hypothesis `NoRace` per block; no order, no pruning; views stay synchronous. Retires D3, D9, D11. Superseded by D19 (same rejections, at typing) | keep the order (pruning always breaks `no-new-comm/step` in views once roles are named); drop `no-new-comm/step` for views (suspicious); prune sends only (deadlocks on the square) |
| D17 | **(current)** hiding is lazy: a block's own step is any run of its internal steps, then the step; the global step hides the internal steps of the blocks taking part. Retires D4 and `Exits` (D6) | sender-stable (sends only from stable states: `existence` unprovable as sketched, §E); `SendStable` hypothesis (rejects NoSynGT `{A,B}`); all-stable `Ready` (circular existence); typing against the global view (needs knowledge of the other processes) |
| D18 | **(current)** a receive of a process is a step sent from outside its role set (`Foreign`, `_-<[_∣_↦_]>->_`); an own role's multicast is the process's send, also at its own receivers | a syntactic premise `P ∉ Q` on the receive (same effect, but the condition belongs to the step, not to the code) |
| D19 | **(current, final)** `Focus`: at a send or receive, the acting role is the only role of the process that can act, at that state and wherever outsiders can move it; a premise of `t/send`/`t/recv` (in the leaves of `a/send`/`a/recv`), decided with the leaf. Progress then needs no hypothesis beyond typing. Retires D16 | `NoRace` as a hypothesis of progress (a typed session could be stuck) |

## Evidence (`Tests/Quotient.agda`, 2026-10-07)

Every original passes `wellBehaved?`/`synchronous?`. Views (`wellBehaved?`,
`synchronous?` of `viewGraph`):

- `ok`: `RoundRobin`, `OAuth2`, `Rec2Buy`, `NoSynGT`, `Forward`, `Multicast` — all three
  pairs; `RecMW` — every pair but `{M,R}`; `LabelSorts` — `{A,B}`, `{B,C}`; the square —
  both; `InternalChoice` `{P,Q}`; 2a and 2b `{P,S}`.
- `notWB`: `LabelSorts` `{A,C}` (one label, two sorts, once `A⟶C` is hidden).
- `notSync`: `RecMW` `{M,R}` (relay; Open).

Code (`typecheckView` at the initial state):

- accepted: `NoSynGT` `{A,B}`, `Forward` `{A,C}` (one label of a choice),
  `InternalChoice` `{P,Q}`, 2b `{P,S}`; RecMW `{M,W2}` and `{W1,R}` (controls, same
  shapes as the rejected RecMW codes).
- rejected by `Focus`, in BOTH orders: the square (`{P,S}`, `{Q,R}`), 2a `{P,S}`,
  RecMW `{M,W1}` (two sends by different own roles) and `{W1,W2}` (mixed), NoSynGT
  `{B,C}` (two receives from one sender).

So the views themselves pass wherever there is no relay; races are rejected at typing,
for every order the code could commit to.

## Open

- Relay blocks (receive on one role, forward internally, send from another): rejected by
  `no-new-comm/step` of the view; the footprint axiom of §I admits them.
- Races across views: a way to allow external races in multi-role processes that is
  consistent across views (pruning by a global order is not: it breaks
  `no-new-comm/step`).
- `README.md` (list of `WellBehaved` axioms) and `FUTURE_WORK.md` (`⨾` "still flattens")
  are stale.
