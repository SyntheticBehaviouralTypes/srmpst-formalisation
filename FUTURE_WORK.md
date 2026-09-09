# FUTURE WORK

*Written 2026-08-05. Four independent lines of work, plus one dead end
recorded so it is not repeated.*

| § | topic | independent of | state |
|---|---|---|---|
| [A](#a--the--projection-as-an-iff) | the `∥` projection as an iff | — | `→` **proved**, `←` false as stated |
| [B](#b--type-checking-over-sets-of-states) | checking over **sets** of states | A, C | designed; gated on the `Δ`-indexing question in B.5 |
| [C](#c--traversal-based-checking-over-nstate) | traversal over `NState`, no flat index | A, B | idea only |
| [D](#d--what-was-tried-and-reverted) | the `Presentation` refactor | — | **reverted, do not rebuild** |
| [E](#e--smaller-loose-ends) | smaller loose ends | — | recorded |

§A and §B are the two with real payoff and they compose: §A cuts *which*
state space you search, §B cuts *how many times* you search it.

---

## A — The `∥` projection as an iff

### A.1 The goal

`typecheckNet` currently flattens: it builds `underlying (present n)`, a
`Graph` with `nsize n` rows, and runs the graph checker on it.
`nsize (n₁ ∥ n₂) = suc (lsize n₂ + lsize n₁ * suc (lsize n₂))` — the
product. Everything about a net that is cheap (`WBNet` is compositional and
never sweeps the product) is thrown away at the checking step.

What we want instead: **a participant is typed against the sub-net it acts
in, and the rest falls out of diamond.** `P` takes no part in `n₂`, so
`n₂`'s interleavings are `¬P` steps that `⊢skip` already absorbs; there is
no reason to enumerate them.

### A.2 What is proved

`Definitions/Graph/NetworkProject.agda`, with `PFree P n₂` (decidable,
`pfree?` in `NetworkWB.agda`) meaning `P` occurs in no action of `n₂`:

```agda
project :
  ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (NState (n₁ ∥ n₂)) δ} {P Pr s}
  → PFree P n₂
  → Γ & Δ             ⊢a[ netTheory (n₁ ∥ n₂) ] P ◂ Pr ∶ s
  → Γ & (map projL Δ) ⊢a[ netTheory n₁ ]        P ◂ Pr ∶ projL s
```

Hole-free, structural, four mutual functions
(`projA`/`projSkip`/`stuckWalk`/`projBl`). Supporting machinery in the same
file: `projL`/`projR`, `mkPair-proj`, `pstep-invP` (inversion in projected
form), `skip-projL`, `inT-lift`, `inT-projL`, `stuck⇒∉T`.

Design notes worth keeping:

* Index by `projL s`, **not** by `mkPair a b`. The `mkPair` form pins the
  `n₂` component to a fixed `b`, and `blocked/rec`'s anchor is reached by a
  mixed trace and can sit at a different `n₂` state. With `projL` the `Δ`
  relation is just `map projL`.
* `PFree` earns its place in `blocked/send`/`blocked/recv`: the action
  mentions `P`, so `pstep-invP`'s `n₂` branch is *absurd* and the `n₁`
  branch IS the projected step.
* The one hard case is `skip/step`, which needs an `n₁`-step out of
  `projL s` when the product's step may be an `n₂` one. Split on
  `nedges n₁ (projL s)`; when empty, `n₁` is stuck *and stays stuck*
  (`n₂`-steps do not move it), so `stuckWalk` walks the tree down the
  `n₂`-only steps to the leaf it must end at.

### A.3 Why the converse is false

**This is the crux, and it is not a proof-engineering artifact: `∥`
genuinely adds divergence.**

#### Obstruction 1 — `Δ` is unconstrained (fixable; not an extra condition)

`blocked/var` at the product needs `lu Δ X -[¬P]->* H ~ s`; the projection
gives only the `n₁` half. Counterexample: `n₂ = b -γ-> b′` with `γ` P-free,
`Δ = [mkPair a b′]`, `s = mkPair a b`. The projection holds by `skip/refl`;
the product needs `b′` to reach `b`, and it does not.

Fix — an **index refinement**, not a side condition:

> invariant: for each `i`, `projR (lu Δ i)` reaches `projR s` in `n₂`.

It is maintained by construction, because `blocked/rec` may pick its anchor
as `mkPair W₁ (projR s)`: then `projL W = W₁`, `projR W = projR s`, and
`liftTr` turns the `n₁` anchor trace into the product one.

#### Obstruction 2 — `skip/cycle`'s productivity guard (needs a condition)

The product's `skip/step` must supply `ktd` for `n₂`-steps too. Those leave
`projL` unchanged, so the projected tree never shrinks and the branch can
close only by `skip/cycle` — which demands `P ∈T`.

Counterexample: `n₁ = a -δ-> c` with `c` terminal and `δ` P-free,
`Pr = v X`, `Δ₁ = [c]`; `n₂ = b -γ-> b`, a P-free self-loop. The projection
is `skip/step δ na ktd` closing at `c` by `blocked/var skip/refl ~refl`. At
`mkPair a b` the `γ` branch returns to `mkPair a b ∈ Ξ`, so only
`skip/cycle` can close it, and `P ∈T mkPair a b` is false — `P` occurs
nowhere. Nothing else applies: `mkPair c b ≁ mkPair a b`, since only the
latter has a `δ`.

So a P-free loop in `n₂` is *deliberately* rejected: under an unfair
scheduler `P`'s `v X` never reaches its anchor. The product typing failing
is **correct**; the component typing succeeding is also correct. They
disagree because `n₂` contributes infinite P-free behaviour that `n₁` alone
does not have.

**Do not attempt the obvious repair.** Threading `P ∈T` as a hypothesis
needs the forward lemma `G -[¬P]->* G′ → P ∈T G → P ∈T G′`, and *that is
false*: `G -β-> D` with `D` terminal, alongside `G -γ-> E -(P⟶R)-> F`,
gives `P ∈T G` but not `P ∈T D`. The codebase has only `skip/∈T-back` (the
converse) and `skip/advance` (which gets its independence from `P` being
*active*, which two P-free actions do not give).

### A.4 The extra condition — making it an iff

Two candidates. Both sufficient; neither machine-checked.

**(A-i) `P ∈T` along the spine — the structural one, and the better fit.**
If `P ∈T (projL s)` holds, the `n₂` branch closes: `Ξ` accumulates exactly
the visited product states, `NState n₂` is finite, so the walk revisits a
state already in `Ξ`, and `skip/cycle` applies with `~refl` and the `P ∈T`
witness (transported by `inT-lift`, since `n₂`-steps do not change
`projL`). The requirement is that it holds at *every* spine state, because
`P ∈T` is not preserved by `n₁`-steps.

Why this is the right shape: **the checker already makes exactly this
split.** `tree?` branches on `∈T? P s` into `treeA?` (regime `P ∈T`) and
`treeB?` (regime `¬ P ∈T`). So state the lift **relative to the regime** —
it should go through in regime A, which is precisely where `skip/cycle` is
available. Regime B is where the counterexample lives, and there the tree
is the `treeB?`/`FailedFrom` shape, a different argument.

The condition is also automatic for most processes: the leaf family is
determined by the process shape, so for `send`/`recv` every leaf is
`blocked/send`/`blocked/recv`, which gives a P-action, hence `P ∈T` at the
root by `in/later` along the spine. Only `v X` and `rec` leaves can fail it.

**(A-ii) `n₂` acyclic from `projR s` — crude, but easy.** Since `PFree`
makes *all* of `n₂`'s actions P-free, "no P-free divergence in `n₂`"
collapses exactly to "`n₂` has no reachable cycle". Decidable with the
existing reachability machinery. Under it the lift is provable and *easy*:
every `n₂` branch runs out of steps, so the measure is lexicographic
`(projected tree , n₂ remaining depth)` — no visited set, no `P ∈T`
threading. Combined with obstruction 1's `Δ` invariant, that is the whole
proof. Restrictive, though: recursive right-hand components are common.

**Recommendation:** do (A-ii) first — small, self-contained, and enough to
build and test `tcNet` end to end. Then attempt (A-i), which generalises.

### A.5 The checker, given the iff

```agda
tcNet (base G)   w P Pr s = -- delegate to Check/Alg.agda; `present (base G)` IS G
tcNet (n₁ ∥ n₂) w P Pr s with pfree? P n₂ | pfree? P n₁
... | yes f₂ | _      = map′ (lift f₂) (project f₂) (tcNet n₁ … (projL s))
... | _      | yes f₁ = map′ (lift f₁) (project f₁) (tcNet n₂ … (projR s))
... | no _   | no _   = -- P straddles: fall back to flattening
tcNet (n₁ ⨾ n₂) w P Pr s = -- a sum, so no explosion; seam handling only
```

`map′` needs both directions, which is why the `←` is the whole game. With
`project` alone the shortcut is **refutation-only**: a `no` from the
component refutes the product by contraposition, but its `yes` proves
nothing.

Two facts that already hold and should be used:

* **Compositional bisimilarity IS an iff, unconditionally available.**
  `~-pair` gives `⟸` and `~-projL`/`~-projR` give `⟹` under the
  receiver-`Disjoint` that `WBNet`'s `∥` constructor already demands. So
  `mkPair a b ~ mkPair a′ b′ ⟺ a ~ a′ × b ~ b′`, decided componentwise
  with no product. This is the escape from a fixpoint over product pairs,
  and it needs no new condition.
* **`PFree` is finer than participant-disjointness of the two nets.**
  `Disjoint` separates *receivers* only — a sender may appear on both
  sides — so per-participant `pfree?` takes the slow path only for the
  participants that genuinely straddle.

---

## B — Type checking over SETS of states

*Independent of §A and §C. This is the one that attacks the constant
factor rather than the state space, and it is probably the largest single
win available.*

### B.1 The observation

`alg? Γ Δ P Pr s` decides the judgment **at one state**. The process is
therefore re-traversed once per state, in three separate places:

* `tree?`/`treeAs?` walk forward through the `¬P` region and re-decide the
  *same* `Pr` at every state reached — `skip/step`'s `ktd` quantifies over
  all successors;
* `blocked/rec`'s anchor search runs `alg? Γ (W ∷ Δ) P Pr W` for **every**
  candidate `W` — that is |states| full traversals of the same body;
* `reachBisim?` runs a reachability query plus a `~` test for every
  candidate `H`, and `∈T? P s` re-runs `reachActive?` at every `s`.

So the work is `O(|Pr| × |states|)` traversals where it could be `O(|Pr|)`
passes over bit-vectors.

### B.2 The idea

Compute, by a **single structural recursion on `Pr`**, the *set* of states
at which it types:

```agda
alg* : (Γ …) (Δ …) (P : Part) (Pr : Proc γ δ) → StateSet
--  s ∈ alg* Γ Δ P Pr   ⟺   Γ & Δ ⊢a P ◂ Pr ∶ s
```

`StateSet = Vec Bool size` — **the representation already in the tree**, as
`Check/Alg.agda`'s `visited`/`stack`, with `wt`/`Incl`/`wt/strict` in
`Definitions/Graph/Reachability.agda` as the termination measure for any
fixpoint over it.

Each process form becomes a set transformer, and the decision procedure
falls out as membership plus a characterisation lemma. Sketch:

| form | transformer |
|---|---|
| `∅` | the complement of the `∈T` set for `P` |
| `ifp E then A else B` | `alg* A ∩ alg* B`, guarded by `⊢e` |
| `Q ! i < E >∙ Pr′` | **pre-image**: `{ s ∣ ∃ S s′. s -<P⟶Q#i<S>>-> s′ ∧ s′ ∈ alg* Pr′ }` |
| `Σ Q ？[ S ]· Br` | a `□`-style pre-image: some head edge exists, and *every* `j`-edge lands in `alg* (lookup Br j)` |
| `v X` | the `¬P`-reach set of `lu Δ X`, closed under `~` |
| `rec Pr′` | the anchor set `S(Pr′, Δ)` below, then one reachability query — but see the `Δ`-indexing caveat in B.5 |
| the `⊢skip` wrapper | the two-pass `B`-then-graph-computation of B.4, **not** a nested fixpoint |

The three expensive per-state queries become **precomputed tables, built
once**:

* the `∈T` set per participant — one backward fixpoint, replacing
  `∈T? P s` at every `s`;
* the all-pairs `¬P`-reachability **matrix** — replacing `reach¬P? P a H`
  per pair;
* the bisimilarity matrix — `approximation G` in `Bisimulation.agda`
  **already computes exactly this**, and `bisim? G x y` is already a lookup
  into it.

`Bisimulation.agda`'s `Matrix`/`refine`/`iterate`/`approximation` is the
template for all three: a size×size bit matrix refined to a fixpoint. So
this is not new machinery, it is the existing machinery applied to
reachability and participation as well as to `~`.

The specialisation of this to `blocked/rec` is what `docs/2026-08-05-DONE-deciding-algorithmic-judgment.md`'s "Future"
section calls **batching the anchor search**: compute, in one pass over the
`¬P`-connected component,

```
S(Pr, Δ) = { W ∈ component | Γ & (W ∷ Δ) ⊢a P ◂ Pr ∶ W }
```

as a bit-vector over `State G`, after which `blocked/rec` at leaf `L` is
just "∃ W ∈ S with `W -[¬P]->* L`" — one reachability query against a
precomputed set. B.3–B.6 below are that note, generalised from `rec` to the
whole judgment, and its two caveats survive the generalisation.

### B.3 The real argument is the REFUTATION, not the speed

The `no` branch needs an `All`-shaped negative over every candidate anchor.
Built candidate-by-candidate, that `All` has to be folded together from
separately obtained negatives — **the pattern that has historically been
the expensive part of this development**. Computed as a set, the universal
statement *is* the result, and the per-state negatives are its complement.

This is also why `Justified`/`FailedFrom`/`failed⇒¬tree` in `Check/Alg.agda`
should disappear: they exist purely to refute a revisit in the `¬ P ∈T`
regime, and set-based, a refutation is just "not in the fixpoint", computed
by the same pass. With them goes the four-component measure, including the
phase component that exists only to satisfy the termination checker.

### B.4 Cycles do NOT force the typing to be iterated

*(An earlier draft of the archived note claimed they did. That was wrong,
and it matters, because it is the difference between a nested fixpoint and
two independent passes.)*

`skip/cycle`'s self-dependence lives in the **skip tree**, not in the
typing judgment, and it is closed afterwards from the `¬P` edges. For a
fixed process `Pr`, in order:

1. compute `B` = the states at which `Pr` is **directly blocked**
   (`blocked/send`/`recv`/`var`/`rec`). Each of those depends only on
   decisions at *strictly smaller* processes — continuations, `rec` bodies
   — so `B` is a clean bottom-up pass with **no circularity at `Pr`**;
2. the `a/skip`-typeable set is then "states from which every `¬P`-path
   reaches `B` or revisits", a graph computation against a now-**fixed**
   `B`.

Worked example: `G -[¬P]-> G'`, `G' -[P]-> G''`, `G' -[¬P]-> G`. Component
`{G, G'}`; `B = {G'}` (only `G'` offers a `P` action); `G` follows because
its only `¬P`-successor is in `B`. The `G → G' → G` loop is reconstructed
from the `¬P` edges at the end — **nothing is re-typed**.

What remains is step 2's own shape. "All paths reach `B` or revisit" is a
safety/AG-style property, so it is a **greatest** fixed point over the
finite `¬P` graph — equivalently a least fixed point of the *failure* set,
propagated backwards from `¬P`-dead-ends outside `B` — plus `skip/cycle`'s
`P ∈T` side condition on each closing revisit. Cheap and standard, but
**get the direction right: a wrong choice here yields a wrong `no`.** It
cannot yield a bogus `yes` — every `yes` still hands back a real
constructor.

### B.5 The caveat that decides viability: Δ-indexing

The predicate depends on `Δ`, so the table is indexed by
(subprocess, state, `Δ`) — and `Δ` is a *vector of states*, i.e.
`|states|^δ` environments.

Fine at `δ = 1`. It degrades with recursion **nesting depth**, not with
process size. **Settle this before attempting the rest of §B**; it is what
decides whether the whole idea is viable, and no amount of cleverness in
B.2–B.4 rescues it if nesting is deep.

Worth checking first: how deep does `δ` actually get in `Examples/`? If the
answer is 1 or 2 throughout, the concern is theoretical and the work is
worth doing. There may also be a way to keep the table parametric in the
anchor rather than indexed by it — the dependence on a `Δ` entry enters
*only* through `blocked/var`, whose set is the `¬P`-reach set of `lu Δ X`
closed under `~`, so with the all-pairs reachability matrix a row lookup
might replace the indexing. That is a conjecture, not a result.

### B.6 What has to be proved, and the order to do it in

```agda
alg*-sound    : s ∈ alg* Γ Δ P Pr → Γ & Δ ⊢a P ◂ Pr ∶ s
alg*-complete : Γ & Δ ⊢a P ◂ Pr ∶ s → s ∈ alg* Γ Δ P Pr
```

then `alg? Γ Δ P Pr s = map′ alg*-sound alg*-complete (s ∈? alg* …)`. This
*replaces* the current per-state `Dec`; it does not sit alongside it.

**Do the naive version first.** The current `Check/Alg.agda` is the
specification the batched version has to agree with, and **`Ex6` is the
test that separates them** (`Tests/AlgCheck.agda`; the refuted
anchor-moving idea is in `Stale/PushRecDerivations.agda.stale`). Any
set-based rewrite that disagrees with the existing checker on `Ex6` is
wrong, not clever.

Remaining risks, honestly:

* B.5 is unresolved and is the gating item;
* the step-2 fixpoint has to be shown to terminate (`wt`/`Incl`/`wt/strict`
  are the right measure — the same argument `reachVia` already uses) **and**
  to characterise the tree exactly; the completeness direction is the real
  work, and the fixpoint direction is where a wrong `no` would come from;
* set-based checking still needs *a* state space to index over, so on a net
  it inherits whatever §A or §C decides about that. The win is orthogonal —
  fewer passes — and stacks with either.

---

## C — Traversal-based checking over `NState`

*Independent of §A and §B. Wanted only if the projection route (§A) is
abandoned; §D explains why the obvious version of this does not work.*

If a traversal-based checker is wanted *instead of* the projection, the
change is **not** an abstract `Presentation` (see §D). It is:

* visited sets as a **structural set over `NState n`** — `nEq?` already
  exists — rather than `Vec Bool (nsize n)`;
* reachability as a **worklist from a start state** following `nedges`,
  touching only reachable states, instead of a fixpoint iterated `size`
  times over all of them;
* `∈T?` and `reach¬P?` as forward searches from `s`, which is all they ever
  needed;
* the anchor search restricted to states that reach `s` — which
  `blocked/rec` requires anyway (`W -[¬P]->* L`), so the current
  enumeration does strictly more work than the rule permits.

Note the tension with §B: §B wants a dense bit-vector over a known index
set, §C wants a sparse set over reachable states only. They can be
reconciled (bit-vectors over the *reachable* subspace, discovered by a
worklist first) but that reconciliation is itself a design decision.

---

## D — What was tried and reverted

An attempt to make the checker net-native by *generalising it over a finite
presentation* rather than by using the projection. **It compiled end to
end, and it was still wrong.** Reverted 2026-08-05; the diagnosis is the
point.

The design: a `Presentation` record — `size : ℕ`, a bijection `ix`/`st` to
`Fin size`, and `out : Fin size → List (Action × Fin size)` as a
**function** instead of a tabulated `Vec` — with `Reachability.agda`'s
graph section, `GraphChecker` and `AlgCheck` all generalised over it, and a
`netPres` instance built from `nix`/`nst`/`nedges`.

**Why it defeats the purpose:** `Presentation.size` is `nsize n`, and the
algorithm is indexed by it.

* `reachVia ok s = iter size (expand ok) …`, and `expand` does a `tabulate`
  over all `size` states — O(size²) per reachability query, over the
  product;
* `reachActive?` (inside `∈T?`) is `FinP.any?` over all of `Fin size`;
* `reachBisim?` enumerates every state as a candidate `H`;
* `blocked/rec`'s anchor search enumerates every state as a candidate `W`;
* visited sets are `Vec Bool (nsize n)`, allocated per search.

So the product is still walked, repeatedly. Only the *storage* of the
adjacency table was removed, not the traversal. **The `Fin size` indexing
is the reification, in index form rather than table form.**

Measured on `Examples/IndepW.agda` (7 participants, `∥`), each after a full
rebuild of the dependency chain:

| `netPres.out` | time | peak RSS |
|---|---|---|
| lazy function | 3m04s | 1.08 GB |
| memoised table | 2m32s | 6.83 GB |

Memoising buys ~1.2× time for ~6× memory, and neither is a speedup over
flattening. (`present n` builds the same table the memoised form does, so
6.83 GB is the honest proxy for the flattened baseline — but that baseline
was never measured directly. Do that before quoting any comparison.)

What *was* worth having, and is cheap to recover if wanted: decoupling
`AlgCheck` from `Graph`; taking the `~` decision as a **parameter** rather
than importing `Bisimulation.agda`; `restrict` as a filtered `out` instead
of a second `Graph`; and the observation that `ReachableBy`/`Reachable` and
the `PathVia`↔`Reachable` bridges in `Reachability.agda` are dead code.

---

## E — Smaller loose ends

* **`WBNet`'s `⨾` still flattens.** It decides `finiteStepback?` on
  `underlying (present (n₁ ⨾ n₂))`. This is the one provably-global
  condition (see `NetworkSeq.agda`), it is independent of the checker, and
  it is not obviously removable.

### Decided 2026-08-06 — accepted as-is, do not re-raise as blockers

These were surfaced at handoff and the owner ruled on each. They are
recorded so a cold session does not "helpfully" fix them.

* **`NetworkProject.agda` is NOT in `runall.sh`'s `ROOTS`**, and nothing
  imports it, so `./runall.sh --tests` will not catch it rotting against a
  change in `Behav.agda` or `NetworkWB.agda`. **Accepted knowingly** — §A
  may be rethought from scratch when it is picked up, so pinning the file
  into the build now would be premature. If you do resume §A, re-check it
  first with
  `agda --guardedness Definitions/Graph/NetworkProject.agda`
  and expect it may need repair.
* **`CLAUDE.md` is untracked**, excluded via `.git/info/exclude`. Deliberate
  and expected; it is a local file, so its contents do not travel with a
  clone. Do not "fix" this by adding it.
* **The flattened baseline for `Examples/IndepW.agda` is unmeasured**, so
  §D's numbers have nothing to compare against. Deliberately deferred until
  someone actually starts optimising — at which point measure it *first*.
* **`README.md` is stale** — deliberately left alone for now.

---

## Where things live

| file | what |
|---|---|
| `Definitions/Graph/NetworkProject.agda` | `projL`/`projR`, the trace lemmas, **`project`**. `LiftStmt` is stated and is FALSE as written — §A.3. |
| `Definitions/Graph/NetworkWB.agda` | `PFree`/`pfree?`/`pfree⇒na`; `Disjoint`; `ParWB` with `~-pair`/`~-projL`/`~-projR`/`dis-⋄`. |
| `Definitions/Graph/Network.agda` | `nedges`, `mkPair`, `stepL`/`stepR`/`pstep-inv`, the `nix`/`nst` bijection, `present`. |
| `Definitions/Graph/Bisimulation.agda` | `Matrix`/`refine`/`iterate`/`approximation` — the template for §B's precomputed tables. |
| `Definitions/Graph/Reachability.agda` | `wt`/`Incl`/`wt/strict` — the termination measure for any `StateSet` fixpoint in §B. |
| `Check/Alg.agda` | the current per-state checker; §B replaces `alg?`, `Justified`/`FailedFrom` and the four-component measure. |
| `Check/Network.agda` | `WBNet`/`netWB`, and `typecheckNet` on the flattened path. |

`NetworkProject.agda` is checked with
`agda --guardedness Definitions/Graph/NetworkProject.agda`.
