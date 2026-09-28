# FUTURE WORK

*Rewritten 2026-09-28 for branch `set-typing`. The original (2026-08-05)
planned against the two-tier `⊢a`/`⊢blocked` judgment, which no longer
exists; git history has it.*

| § | topic | state |
|---|---|---|
| [A](#a--the--projection-as-an-iff) | the `∥` projection as an iff | `→` was proved over the **retired** `⊢a` (`Stale/`); needs porting. `←` is false as stated. |
| [B](#b--type-checking-over-sets-of-states) | checking over **sets** of states | **done** (`PLAN.md`) |
| [C](#c--traversal-based-checking-over-nstate) | traversal over `NState`, no flat index | idea only |
| [D](#d--what-was-tried-and-reverted) | the `Presentation` refactor | **reverted, do not rebuild** |
| [E](#e--smaller-loose-ends) | smaller loose ends | recorded |

**Where things stand.** The metatheory, the equivalence `⊢a ⟺ ⊢p` (for
every well-behaved theory) and the decision procedure are complete and
hole-free, and `PLAN.md` has no open items. What is left is net-specific:
nets are still type-checked by **flattening** (`typecheckNet` runs the graph
checker on `underlying (present n)`, whose size is the product). §A is the
route to not flattening; §C is the alternative if §A is abandoned.

**Baseline to beat** (the flattened path, measured 2026-09-26):
`Examples/IndepW` presents as **13 states**, and its 7-participant session
decision takes **2.2 s**. That is small, so §A is about scaling to larger
nets, not about the current examples.

---

## A — The `∥` projection as an iff

### A.1 The goal

A participant should be typed against the sub-net it acts in, and the rest
should fall out of diamond. If `P` takes no part in `n₂` (`PFree P n₂`,
decidable: `pfree?` in `NetworkWB.agda`), then `n₂`'s interleavings are
`¬P` steps, which `Wait`'s idle walk already absorbs. There is no reason to
enumerate them.

### A.2 What exists, and what porting means

`Stale/NetworkProject.agda.stale` (not type-checked; it last checked clean
on 2026-08-13) proves the `→` half over the **retired** judgment:

```agda
project :
  ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (NState (n₁ ∥ n₂)) δ} {P Pr s}
  → PFree P n₂
  → Γ & Δ             ⊢a[ netTheory (n₁ ∥ n₂) ] P ◂ Pr ∶ s
  → Γ & (map projL Δ) ⊢a[ netTheory n₁ ]        P ◂ Pr ∶ projL s
```

It is hole-free and structural, with four mutual functions
(`projA`/`projSkip`/`stuckWalk`/`projBl`) and supporting machinery
`projL`/`projR`, `mkPair-proj`, `pstep-invP`, `skip-projL`, `inT-lift`,
`inT-projL` and `stuck⇒∉T`.

**Porting it to the current `⊢a`** (`Definitions/Typing/Alg.agda`) means:

* **Sets, not states.** `⊢a` is indexed by a set of states `(anchors ,
  behaviour)`, so the statement becomes an image: `𝒮` over
  `netTheory (n₁ ∥ n₂)` maps to `{ (map projL ws , projL s) | (ws , s) ∈ 𝒮 }`
  over `netTheory n₁`.
* **Anchors live in the state now.** The old statement's `map projL Δ` is
  the same map applied to the anchor vector `ws`.
* **`Wait` replaces `⊢skip`.** The machinery that never touched skip trees
  (`projL`/`projR`, `pstep-invP`, `inT-*`) should carry over as is. The
  skip-tree parts (`projSkip`, `stuckWalk`, `skip-projL`) must be restated
  over `WaitV`. The stale file's header calls this "a port, not a rewrite".
  That is plausible, but it is unchecked.

**First step when resuming:** port the tree-independent lemmas, then
`stuckWalk` over `WaitV`, and only then the rule cases.

Design notes that survive the change of judgment:

* **Project anchors by `projL`, not by `mkPair a b`.** The `mkPair` form
  pins the `n₂` component, but a `rec`'s anchor is reached by a mixed trace
  and can sit at a different `n₂` state.
* **`PFree` earns its place at send and receive.** The action mentions `P`,
  so `pstep-invP`'s `n₂` branch is absurd, and the `n₁` branch is the
  projected step.
* **The hard case is the idle step** (`wv/step`, previously `skip/step`).
  It needs an `n₁`-step out of `projL s` when the product's step may be an
  `n₂` one. Split on `nedges n₁ (projL s)`. When that is empty, `n₁` is
  stuck and stays stuck (`n₂`-steps do not move it), so `stuckWalk` follows
  the `n₂`-only steps to the leaf the tree must end at.

### A.3 Why the converse is false

**`∥` genuinely adds divergence. This is not a proof-engineering
artifact.** Both obstructions below were found against the old judgment,
and both concern rules that have direct counterparts now.

#### Obstruction 1: anchors are unconstrained (fixable; not an extra condition)

`a/var` at the product needs `Unskip P (Var X)`: some state reaching `s`
by `¬P` steps whose anchor matches (`lu ws X ~ ·`). The projection only
supplies the `n₁` half.

Counterexample: `n₂ = b -γ-> b′` with `γ` P-free, anchors `[mkPair a b′]`,
and `s = mkPair a b`. The projection holds with the empty run. The product
needs `b′` to reach `b`, and it does not.

The fix is an **invariant on the index**, not a side condition:

> for each `i`, `projR (lu ws i)` reaches `projR s` in `n₂`.

`a/rec` maintains it by choosing its entry anchors as
`mkPair W₁ (projR s)`: then `projL W = W₁` and `projR W = projR s`, and
`liftTr` turns the `n₁` anchor trace into the product one.

#### Obstruction 2: the productivity guard (needs a condition)

At the product, `Wait`'s `wv/step` must cover `n₂`-steps too. Those leave
`projL` unchanged, so the projected tree never shrinks, and the branch can
close only by `wv/cycle`, which demands `P ∈T`.

Counterexample: `n₁ = a -δ-> c` with `c` terminal and `δ` P-free, and
`Pr = v X` anchored at `c`; `n₂ = b -γ-> b`, a P-free self-loop. The
projection types (one idle step to `c`, where the anchor matches). At
`mkPair a b`, the `γ` branch returns to a visited state, so only `wv/cycle`
can close it, and `P ∈T (mkPair a b)` is false because `P` occurs nowhere.
Nothing else applies either: `mkPair c b ≁ mkPair a b`, since only the
latter has a `δ`.

So a P-free loop in `n₂` is **deliberately** rejected. Under an unfair
scheduler, `P`'s `v X` never reaches its anchor. Both answers are correct:
the product typing fails, the component typing succeeds, and they disagree
because `n₂` contributes infinite P-free behaviour that `n₁` alone lacks.
(`Tests/WaitNotSkip.agda` is the same phenomenon without `∥`.)

**Do not attempt the obvious repair.** Threading `P ∈T` as a hypothesis
needs `G -[¬P]->* G′ → P ∈T G → P ∈T G′`, and *that is false*: take
`G -β-> D` with `D` terminal, alongside `G -γ-> E -(P⟶R)-> F`. Then
`P ∈T G` holds but `P ∈T D` does not. Only the converse, `skip/∈T-back`,
holds.

### A.4 The extra condition that makes it an iff

There are two candidates. Both are sufficient on paper; neither is
machine-checked.

**(A-i) `P ∈T` along the spine: structural, and the better fit.** If
`P ∈T (projL s)` holds, an `n₂` branch closes. `NState n₂` is finite, so
the walk revisits a state in the visited set, and `wv/cycle` applies with
`~refl` and the `P ∈T` witness, transported by `inT-lift` since `n₂`-steps
do not change `projL`. The condition must hold at *every* spine state,
because `P ∈T` is not preserved by `n₁`-steps.

This matches the rule: `wv/cycle` is available exactly where `P ∈T`. The
condition also comes for free for most processes. For a send or receive,
every leaf offers a `P`-action, which gives `P ∈T` back up the spine by
`in/later`. Only `v X` and `rec` leaves can fail it.

**(A-ii) `n₂` acyclic from `projR s`: crude, but easy.** Under `PFree`, all
of `n₂`'s actions are P-free, so "no P-free divergence in `n₂`" is exactly
"no reachable cycle in `n₂`". That is decidable with the existing
reachability machinery. Under it every `n₂` branch runs out of steps, so
the measure is lexicographic `(projected tree , n₂ remaining depth)`: no
visited set, and no `P ∈T` threading. Combined with obstruction 1's
invariant, that is the whole proof. It is restrictive, though, because
recursive right-hand components are common (IndepW's pipelines are loops).

**Recommendation:** port (A.2), then do (A-ii) to build and test `tcNet`
end to end, then attempt (A-i), which generalises it.

### A.5 The checker, given the iff

```agda
tcNet (base G)   w P Pr s = -- Check/TypeCheck's tc?; `present (base G)` IS G
tcNet (n₁ ∥ n₂) w P Pr s with pfree? P n₂ | pfree? P n₁
... | yes f₂ | _      = map′ (lift f₂) (project f₂) (tcNet n₁ … (projL s))
... | _      | yes f₁ = map′ (lift f₁) (project f₁) (tcNet n₂ … (projR s))
... | no _   | no _   = -- P straddles: fall back to flattening
tcNet (n₁ ⨾ n₂) w P Pr s = -- a sum, so no explosion; seam handling only
```

`map′` needs both directions, which is why the `←` is the whole game. With
`project` alone, the shortcut is refutation-only: a `no` from the component
refutes the product by contraposition, but a `yes` proves nothing.

Two facts that already hold and should be used:

* **Compositional bisimilarity is an unconditional iff.** `~-pair` gives
  `⟸`, and `~-projL`/`~-projR` give `⟹` under the receiver-`Disjoint`
  condition that `WBNet`'s `∥` already demands. So
  `mkPair a b ~ mkPair a′ b′ ⟺ a ~ a′ × b ~ b′` is decided componentwise,
  with no product.
* **`PFree` is finer than disjointness of participants.** `Disjoint`
  separates *receivers* only, and a sender may appear on both sides. So
  per-participant `pfree?` takes the slow path only for participants that
  genuinely straddle.

---

## B — Type checking over SETS of states

**Done on `set-typing` (September 2026).** `PLAN.md` is the record: the
rules, why each is shaped as it is, the checker, and its measured cost.
Here is how the original design's ideas landed:

* **"Decide the set at which `Pr` types, in one structural pass."** `⊢a` is
  now itself set-indexed (`Typing/Alg.agda`), and `Check/Alg.agda`'s
  `Probing.probe` returns the largest typed subset of the probed set, by
  structural recursion on the process.
* **"Precompute `∈T`, `¬P`-reachability and `~` as tables."** These are
  `Env` (per participant) and `Shared` (per graph). Rows are computed by
  `reachFix`, which forces each round and stops at the fixpoint.
* **"The refutation is the real argument."** Confirmed. `Justified`,
  `FailedFrom` and the four-component measure are gone, and a refutation is
  simply absence from the returned set.
* **"`Δ`-indexing may kill it" (the old B.5).** Resolved by putting the
  anchors *in* the state (`State δ = Vec Behav δ × Behav`) and checking
  `rec` entry with `Diag`, so nothing is indexed by environments.
* **"`⊢skip` as a second pass over a fixed blocked set" (the old B.4).**
  Superseded by `Wait`, a finite tree over a visited set, decided by a
  walk. `Wait ⟺ ⊢skip` is proved (`AlgEquiv.agda`).

Two cost ideas are recorded in `PLAN.md` as unneeded at current sizes: a
worklist/BFS reachability row, and deciding `Wait` once per leaf set rather
than once per root.

---

## C — Traversal-based checking over `NState`

*An alternative to §A: wanted only if the projection route is abandoned.
§D explains why the obvious version does not work.*

The checker indexes everything by `Fin size`: `Vec Bool size` sets, rows
over all states, and `FinP.any?` over all states for anchors and `∈T`. On a
net, `size` is the product. A traversal-based checker would instead use:

* visited sets as a **structural set over `NState n`** (`nEq?` exists),
  rather than `Vec Bool (nsize n)`;
* reachability as a **worklist from a start state** following `nedges`,
  touching only reachable states;
* `∈T` and `¬P`-reachability as forward searches from `s`;
* anchor candidates restricted to states that reach `s`, which `a/rec`
  requires anyway.

There is a tension with how §B landed. `Check/Alg.agda` is built on dense
bit-vectors over a known index set, while this wants sparse sets over
reachable states. They can be reconciled (bit-vectors over the reachable
subspace, discovered by a worklist first), but that reconciliation is
itself a design decision.

---

## D — What was tried and reverted

An attempt to make the checker net-native by *generalising it over a finite
presentation*, rather than by using the projection. **It compiled end to
end, and it was still wrong.** It was reverted on 2026-08-05; the diagnosis
is the point. (Names below are those of the checker at the time.)

The design was a `Presentation` record: `size : ℕ`, a bijection `ix`/`st`
to `Fin size`, and `out : Fin size → List (Action × Fin size)` as a
**function** instead of a tabulated `Vec`. `Reachability.agda`'s graph
section and the checker were generalised over it, and a `netPres` instance
was built from `nix`/`nst`/`nedges`.

**Why it defeats the purpose:** `Presentation.size` is `nsize n`, and the
algorithm is indexed by it. Reachability rows iterate `expand`, a
`tabulate` over all `size` states. `∈T` and the anchor search enumerate all
of `Fin size`, and visited sets are `Vec Bool (nsize n)`. So the product is
still walked, repeatedly: only the *storage* of the adjacency table was
removed, not the traversal. **The `Fin size` indexing is the reification,
in index form rather than table form.**

Measured on `Examples/IndepW.agda` with the checker of the time:

| `netPres.out` | time | peak RSS |
|---|---|---|
| lazy function | 3m04s | 1.08 GB |
| memoised table | 2m32s | 6.83 GB |

(For comparison, today's checker decides IndepW's session over the plain
flattened graph in 2.2 s. The checker changed, so this is not a comparison
of the two approaches.)

What was worth having, and is cheap to recover if wanted:

* decoupling the checker from `Graph`;
* taking the `~` decision as a **parameter** rather than importing
  `Bisimulation.agda`;
* `restrict` as a filtered `out` instead of a second `Graph`.

---

## E — Smaller loose ends

* **`WBNet`'s `⨾` still flattens.** It decides `finiteStepback?` on
  `underlying (present (n₁ ⨾ n₂))`. This is the one provably global
  condition (see `NetworkSeq.agda`). It is independent of the checker and
  not obviously removable.
* **`Stale/NetworkProject.agda.stale` is not type-checked**, so nothing
  catches it drifting further from the live definitions. That is accepted:
  §A starts with a port anyway (A.2).
* **`CLAUDE.md` is untracked**, excluded via `.git/info/exclude`. This is
  deliberate: it is a local file. Do not "fix" it by adding it.

Resolved since the 2026-08 version: the flattened IndepW baseline is
measured (see the top of this file), and `README.md` is current.

---

## Where things live

| file | what |
|---|---|
| `Stale/NetworkProject.agda.stale` | `projL`/`projR`, the trace lemmas, and **`project`** over the retired `⊢a`: §A's starting point. `LiftStmt` is stated there and is FALSE as written (§A.3). |
| `Definitions/Graph/NetworkWB.agda` | `PFree`/`pfree?`/`pfree⇒na`; `Disjoint`; `ParWB` with `~-pair`/`~-projL`/`~-projR`/`dis-⋄`. |
| `Definitions/Graph/Network.agda` | `nedges`, `mkPair`, `stepL`/`stepR`/`pstep-inv`, the `nix`/`nst` bijection, `present`. |
| `Definitions/Typing/Alg.agda` | the set-indexed `⊢a` that §A must be restated over: `WaitV`, `Unskip`, `Var`, `Diag`, `a/var`, `a/rec`. |
| `Definitions/Graph/Reachability.agda` | `reachVia` (the specification) and `reachFix`/`reachFix≡` (what to compute). |
| `Utils/Bits.agda` | `wt`/`Incl`/`wt/strict` (the fixpoint termination measure) and `iterateFix`/`iterateFix/iterate`. |
| `Check/Alg.agda` | the set-based checker. |
| `Check/Network.agda` | `WBNet`/`netWB`, and `typecheckNet` on the flattened path. |
