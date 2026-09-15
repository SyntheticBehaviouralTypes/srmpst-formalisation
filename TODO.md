# TODO — set-based, syntax-directed typing

```
┌──────────────────────────────────────────────────────────────────────────┐
│ LIVE PLAN.  Written 2026-08-14 on branch `set-typing`.                    │
│                                                                          │
│ This is NOT the archived plan.  Any comment in a `.agda` file or an       │
│ older doc that says "see TODO.md" refers to                               │
│ `docs/2026-08-05-DONE-deciding-algorithmic-judgment.md`, which is closed. │
│                                                                          │
│ `FUTURE_WORK.md` §B (checking over sets of states) is SUPERSEDED by this  │
│ file — this is that idea, done as a change of judgment rather than as an  │
│ optimisation of `Check/Alg.agda`.  §A is affected (see "Casualties").     │
│ §C and §D are untouched and still apply.                                  │
└──────────────────────────────────────────────────────────────────────────┘
```

## 1. The goal, in one paragraph

Replace `⊢a` / `⊢skip` / `⊢blocked` with a **single syntax-directed judgment
whose target is a SET of states** rather than one state:
`Γ & Δ ⊢ P ◂ Pr ∶ 𝒮`. There is exactly one rule per process form; `t/skip`,
`t/unskip`, the skip *tree*, and the separate leaf family all disappear, and
the walking-the-graph part of typing becomes two closure operators inside
`⊆`-premises. The shape of a derivation becomes the shape of `Pr`, so
derivation size is `O(|Pr|)` **independent of the graph** — that is the source
of the proof-simplicity win. Deciding the judgment becomes: compute the largest
`𝒮` bottom-up over `Pr`, then test membership.

*Amended 2026-09-11.* Two claims in this paragraph did not survive contact:
"the walking-the-graph part of typing becomes two closure operators" is FALSE
as stated — `Wait` needs a visited set, see §7 step 4b — and the performance
win is not one. Measured at step 6, the set-based checker is at **parity** with
the checker it replaces on this corpus; the `O(|Pr|)` claim is about derivation
size, and these graphs are small. The proof-simplicity win is real and is what
the exercise bought.

## 2. Decisions taken by the owner (do NOT re-litigate)

| # | decision | consequence |
|---|---|---|
| D1 | **`rec` anchors are SINGLETONS** (`s/rec₁`, below), not sets | `Δ : Vec Behav δ` stays a vector of *states*; nothing is indexed by environments; the rule is pointwise equivalent to `blocked/rec` |
| D2 | **Replacement**, not a second judgment | `⊢a`/`⊢skip`/`⊢blocked`/`Norm.agda` are deleted at the end; `Safety/` is restated |
| D3 | Rules live at the **abstract** level (`Definitions/Typing/`), over `Pred Behav` | keeps "prove once over `BTheory`, instantiate for graphs"; `Check/` gets the finite realisation only |
| D5 | **Remove the declared sort vector** `S` — FIRST, as its own green commit. **DONE**, see §7 step 1 | it was unused by `blocked/recv`; arity stays pinned by the branch vector's length. The constructor is now `Σ_？·_` |
| D6 | **Replace `Check/Alg.agda` in place** (no permanent side-by-side) | the `Tests/`+`Examples/` corpus is the only oracle; see §7 |
| — | **Do NOT add global sort/arity consistency** as a well-formedness condition | refuted by evidence: `Tests/LabelSorts.agda` and `Tests/LabelSortsForward.agda` are well behaved *and* typeable, and such a condition outlaws both |

D4 (`Loop P = ∅`, §5.1) and the `~`-closure question (§5.2) were **both closed on
2026-09-01** — D4 proved, `~`-closure decided as uniform. See those sections.

## 3. The rules

Sets are predicates `Behav → Set` abstractly, `Vec Bool (size G)` concretely.

### 3.1 The two operators — note they point in OPPOSITE directions

> **SUPERSEDED, 2026-09-11 — read §7 step 4b before implementing anything here.**
> The `Wait = ν W. Reach∀⁺ P 𝒮 (Guard P W)` below is **refuted**
> (`Tests/WaitNotSkip.agda`): a greatest fixpoint over `Pred Behav` admits
> infinite unfoldings that a finite `⊢skip` tree does not, which made
> `⊢ ⟺ ⊢set` unprovable. `Wait` is now a **μ indexed by a visited SET**
> (`WaitV`, `Definitions/Typing/Sets.agda`). `Reach₀`/`Reach~` below are
> unchanged and still accurate, and so is the `∈T`/`∉T` split in the last
> bullet — that is exactly how `Check/Wait.agda` is organised. The rest of this
> subsection is kept because it records WHY each premise is shaped as it is.

```
Wait P 𝒮   =  ν W. Reach∀⁺ P 𝒮 (Guard P W)             -- was ⊢skip; ∀-backward

  Reach∀  P 𝒳   = μ R. 𝒳 ∪ { s | P not-active-in s
                                ∧ (∃ α t. s -< α >-> t)       -- skip/step's witness
                                ∧ (∀ α t. s -< α >-> t → t ∈ R) }  -- skip/step's ktd

  Reach∀⁺ P 𝒮 𝒢 =      𝒮 ∪ { s | P not-active-in s            -- NO 𝒢-leaf at depth 0
                                ∧ (∃ α t. s -< α >-> t)
                                ∧ (∀ α t. s -< α >-> t
                                          → t ∈ Reach∀ P (𝒮 ∪ 𝒢)) }

  Guard   P W   = { s | P ∈T s ∧ s ∈ W }                      -- skip/cycle's guard

Reach₀ P 𝒜 = { s | ∃ a ∈ 𝒜. a -[¬ P ]->* s }                  -- was t/unskip; ∃-backward
Reach~ P 𝒜 = { s | ∃ a ∈ 𝒜. ∃ H. a -[¬ P ]->* H ∧ H ~ s }     -- = Reach₀ on ~-closed 𝒜
```

`Wait` reads: *along every path, within finitely many P-inactive steps you
either land in `𝒮`, or — **after at least one step** — reach a `P ∈T` state
from which the same holds again.*

**Four things that are load-bearing and easy to get wrong:**

* `Reach∀` is **universal** — the environment picks the branch. An existential
  backward closure here produces a checker that says `yes` when it must not.
* the `∃ α t` conjunct is `skip/step`'s own step witness: a P-inactive **dead
  end** is not skippable (it must be caught by `s/end` instead).
* **the ν must be PRODUCTIVE — a `Guard` leaf only STRICTLY below a step.**
  That is the whole point of `Reach∀⁺`, and it was got wrong once already.
  Writing `Wait P 𝒮 = ν W. Reach∀ P (𝒮 ∪ Guard P W)` with the obvious
  `Guard P W = { s | P ∈T s ∧ s ∈ W }` is **refuted**: `Wait P ∅` is then
  inhabited at every state where `P` is live, by `force w = r/leaf (inj₂ (pin , w))`,
  taking no step at all — which contradicts D4 (§5.1), now proved. `skip/cycle`
  cannot do this: `lu Ξ X ~ G` closes against a **strict** ancestor and every
  ancestor edge is a `skip/step`, so ≥1 step separates two cycle closures.
  Closing against a *distant* ancestor needs no extra machinery: `t ~ A` plus
  `Wait P 𝒮 A` gives `Wait P 𝒮 t` by `~`-closure (§5.2).
* the μ/ν split is **forced**, not stylistic: `P ∈T` is backward-closed
  (`in/later`, `Definitions/Behav.agda:93`), so `P ∉T` is forward-closed, so the
  `∉T` region is a sink where `Guard` is empty and `Wait` collapses to
  `Reach∀⁺ P 𝒮 ∅`, a plain lfp.
  Cycles exist only in the `∈T` region. **The two fixpoints are ordered, not
  nested** — compute the `∉T` lfp first, then the `∈T` gfp over it. This is what
  replaces `Justified`/`FailedFrom`/`failed⇒¬tree` and the four-component
  measure in `Check/Alg.agda`, phase component included.

### 3.2 The judgment

`Γ & Δ ⊢ P ◂ Pr ∶ 𝒮`, `Δ : Vec Behav δ` (D1). `𝒮` occurs only in
`⊆`-premises, so the judgment is downward closed and each `Pr` has a largest
`𝒮`; `∅` satisfies every rule.

```
       Γ ⊢e E ∶ S            Γ & Δ ⊢ P ◂ Pr ∶ 𝒯
       𝒮 ⊆ Wait P { s | ∃ s′. s -< P ⟶ Q # i < S > >-> s′ ∧ s′ ∈ 𝒯 }
s/send ───────────────────────────────────────────────────────────────────
                    Γ & Δ ⊢ P ◂ Q ! i < E >∙ Pr ∶ 𝒮


       ∀ j U.  (U ∷ Γ) & Δ ⊢ Q ◂ lu Br j ∶ 𝒯 j U
       𝒮 ⊆ Wait Q { s | (∃ j U t. s -< P ⟶ Q # j < U > >-> t)
                      ∧ (∀ j U t. s -< P ⟶ Q # j < U > >-> t → t ∈ 𝒯 j U) }
s/recv ───────────────────────────────────────────────────────────────────
                    Γ & Δ ⊢ Q ◂ Σ P ？· Br ∶ 𝒮


       Γ ⊢e E ∶ s/bool     Γ & Δ ⊢ P ◂ A ∶ 𝒮     Γ & Δ ⊢ P ◂ B ∶ 𝒮
s/if   ───────────────────────────────────────────────────────────────────
                 Γ & Δ ⊢ P ◂ ifp E then A else B ∶ 𝒮


       𝒮 ⊆ { s | ¬ P ∈T s }                𝒮 ⊆ Wait P (Reach~ P (lu Δ X))
s/end  ─────────────────────────    s/var  ───────────────────────────────
       Γ & Δ ⊢ P ◂ ∅ ∶ 𝒮                   Γ & Δ ⊢ P ◂ v X ∶ 𝒮


       MessageGuarded Pr
       ∀ W ∈ 𝒜.  Γ & (W ∷ Δ) ⊢ P ◂ Pr ∶ ⌈W⌉            -- ⌈W⌉ = the singleton
       𝒮 ⊆ Wait P (Reach₀ P 𝒜)
s/rec₁ ───────────────────────────────────────────────────────────────────
                    Γ & Δ ⊢ P ◂ rec Pr ∶ 𝒮
```

`⊢s M ∶ G` becomes `∀ P. G ∈ ⟦M [ P ]s⟧`.

Why each rule is shaped that way, in one line each:

* **send is `∃`, recv is `∀`+`∃`** — internal vs external choice. The process
  picks the send label, so that exact edge must exist; the sender picks the
  branch, so the process must cover every offered branch and *may cover more*.
  Verified: `recvConts?` returns a vacuous continuation for a non-matching
  action (`Check/Alg.agda:782`), and only `findRecv` (`:743`) demands one edge.
* **`S` in `s/send` is lifted out of the set** and inferred once — free, by
  `⊢e-unique` (`Definitions/Expr.agda:97`). "Every state uses the same sort" is
  a consequence, not a side condition.
* **`𝒯` in `s/recv` is indexed by `(j , U)`**, not by `j`. This is not
  pedantry — see §6, it has a machine-checked test.
* **`s/if`/`s/end` take no `Wait`** — `a/if`/`a/end` are top-level in `⊢a` and
  no `⊢blocked` constructor covers `ifp`/`∅`. **Modulo D4** (§5.1).

## 4. Current status

**Updated 2026-09-15.  ALL of §7 is done: `⊢a` IS DELETED.**  The development
now has exactly TWO systems — the declarative `⊢p` and the set-based `⊢`
— and nothing in between.  `agda --guardedness` exit 0 on every root from a
clean build, no holes, no `postulate`s, no `TERMINATING`:

| file | what |
|---|---|
| `Definitions/Typing/SetsNorm.agda` | `typing⇒set` — `⊢p → ⊢set` DIRECTLY (735 lines) |
| `Definitions/Typing/SetsDeclarative.agda` | `set⇒typing` — the converse |

Deleted: `Typing/Algorithmic.agda`, `Typing/Norm.agda` (830 lines),
`Typing/AlgProperties.agda`, `Typing/SetsAlg.agda`.  `Definitions/Graph/
NetworkProject.agda` moved to `Stale/` (§9 — write-off, not a port).
`ROOTS` updated; `Check/Sets.agda` now decides `⊢p` outright.

**THE ONE IDEA, recorded so it is not undone.**  `⊢p`'s `t/skip` is
SELF-REFERENTIAL — its leaf family is `⊢p` again.  So a fact dug out of one
past a `skip/cycle` may need unwrapping once more, and that unwrap is not a
subterm anything can see: BOTH an `Anc`/`findRun` chase (`MainLeaf.agda`'s
technique) and an unfold chase (`Norm.agda`'s) fail the termination checker
here, and no rearrangement of either fixes it.  Killing the self-reference is
precisely what `⊢a`'s two-layer `a/skip`/`⊢blocked` split was FOR — and
`WaitV` does it too, for nothing: its leaf family is a plain `Pred`.  So
**convert to `Wait` FIRST** (structural, `skip/cycle ↦ wv/cycle` one-for-one,
no chase at all), **then read the fact off with `waitFind`** — which is just
`findMain ∘ wait⇒skip`, both already proved.  Every leaf family in
`SetsNorm.agda` carries exactly the state-free facts its rule needs for that
reason: `SendE` the sort, `RecG` the guardedness, `IfE` the guard's typing.
`∅` is the one exception — `s/end`'s `done` must hold at EVERY state, not
just one, so `waitFind` is no use and it keeps an `a∅/notin`-style chase over
the (non-self-referential) `¬ P ∈T` family.

*The 2026-09-11 entry, for the record:* **Steps 1–5 of §7 were done: `⊢a ⟺ ⊢set` is PROVED.**
Six files, all `agda --guardedness` exit 0, no holes, no `postulate`s, no
`TERMINATING`:

| file | what |
|---|---|
| `Definitions/Typing/NoLoop.agda` | D4, `Loop P = ∅` |
| `Definitions/Typing/MainLeaf.agda` | `findMain` — every `⊢skip` tree has a main leaf, constructively |
| `Definitions/Typing/Sets.agda` | `WaitV`, `Reach₀`/`Reach~`, the seven rules |
| `Definitions/Typing/SetsEquiv.agda` | `skip⇒wait` / `wait⇒skip`, both directions |
| `Definitions/Typing/AlgProperties.agda` | `alg/bisim` / `alg/~` |
| `Definitions/Typing/SetsAlg.agda` | `set⇒alg` / `alg⇒set` — the equivalence |

**None is in `ROOTS`, so nothing re-checks them** — check them by hand until
they are wired in. Next is step 6 (move `Check/` onto the set form).

*The rest of this section is from 2026-08-14 and is retained for the parts that
have not moved:*

* Branch **`set-typing`**, forked from `simplified-theory` @ `15bf5bf`, which
  is the rollback point (last known-green commit).
* Working tree, uncommitted:
  * `Definitions/Graph/Reachability.agda` — dead code removed (`ReachableBy`,
    `Reachable`, `reachable/map`, `reachable/cat`, `pathVia→reachable`,
    `reachable→pathVia`, and the now-unused `⊤` import). `agda --guardedness`
    on it and on `Definitions/Graph.agda` (which re-exports it publicly): **exit 0**.
  * `Tests/LabelSorts.agda`, `Tests/LabelSortsForward.agda` — new, both **exit 0**,
    all decisions forced. See §6.
  * `FUTURE_WORK.md` — untracked, pre-existing.
* **Step 1 of §7 is done** (the sort vector); see there. Everything since is
  committed and `./runall.sh --tests` was green at that commit.
* **No rule has been written in Agda yet** — §7 step 3 is the first that does.
* `Definitions/Graph/NetworkProject.agda` typechecked clean on 2026-08-13
  (`agda --guardedness Definitions/Graph/NetworkProject.agda`, exit 0). It is
  not in `ROOTS`, so nothing re-checks it. See "Casualties".
* Still dead and NOT removed, confirmed by grep: the whole `PathViaP` family
  (`Definitions/Graph/Reachability.agda:304-345` in the pre-cleanup numbering)
  — `PathViaP`, `pathViaP-snoc`, `pathViaP-map`, `pathViaP→pathVia`,
  `pathVia→pathViaP`. Used nowhere, including inside its own file except by
  each other. ~45 lines, free to delete.

## 5. Open questions — BOTH NOW CLOSED (2026-09-01)

### 5.1 D4: is `Loop P = Wait P ∅` empty? — **ANSWERED: YES**

**Proved**, `Definitions/Typing/NoLoop.agda` (`loop/empty`, `Loop-empty`), which
typechecks clean. So §3.2's `s/if`/`s/end` do **not** need `∪ Loop P`. The
falsification attempt suggested below is unnecessary: no counterexample exists.

The proof recurses structurally on the `Any (P ∈α_) αs` witness, **not** on the
tree — the `skip/cycle` jump walks back *up*, so the tree is not decreasing. That
works only because `P ∈T` is an existential over a run and `tr-transport` keeps
the label list, hence the `Any` witness, literally unchanged.

Two things this does NOT settle. It is the `⊥`-leaf statement only, so it does
not discharge `Norm.agda:169`'s `MainLeaf` hypothesis, which needs a constructive
witness where the leafless argument yields only `¬¬∃`. And it says nothing yet
about `Wait P ∅` for the **corrected** `Reach∀⁺` (§3.1) — that is the next task.

*Historical, kept because it is what exposed the §3.1 bug:*

### 5.1′ (superseded) the original conjecture

`⟦if⟧`/`⟦∅⟧` as written in §3.2 are faithful to `⊢a` **only if** no skip tree
consists purely of `skip/step`/`skip/cycle` with no `skip/main` leaf. Otherwise
they need `∪ Loop P` and the rules get a wart.

*Conjecture (argued, NOT proved):* `Loop P = ∅`. Every node of such a tree is
P-inactive (`skip/step`'s `na`), so `skip/cycle`'s `P ∈T` premise has nowhere to
come from — the first P-action on the witnessing trace would sit at a covered,
hence P-inactive, state. The induction has to be transported across
`C ~ ancestor`, which is why it is not immediate.

**This is not only about the new rules.** `MainLeaf`
(`Definitions/Typing/Declarative.agda:173`) is exactly this statement, and
`Definitions/Typing/Norm.agda:169` takes it as a *hypothesis* — the current
development already leans on it and never proves it. Note
`Definitions/Typing/Properties.agda:98` (`~mainLeaf/weaken-visited (skip/cycle _ _) ()`):
`MainLeaf` has no constructor for `skip/cycle`, which is what makes the question
non-vacuous.

**Cheapest first move is falsification, not proof:** try to *build* a leafless
tree as a `Tests/` file. Either you get a counterexample — which settles D4 as
"carry `∪ Loop P`" and says something surprising about the current system — or
the attempt shows you the proof.

### 5.2 Should all sets be `~`-closed? — **DECIDED: YES (uniform closure)**

Owner's call, 2026-09-01. The load-bearing assumption was **verified, not
assumed**: `Reach∀`, `Wait` and `Reach₀` all preserve `~`-closure
(`reach∀/~`, `wait/~`, `reach₀/~` in `Definitions/Typing/Sets.agda`), and
`reach~→reach₀` proves `Reach₀ = Reach~` on `~`-closed sets. So the
`blocked/rec` / `blocked/var` asymmetry **collapses**: `s/var` and `s/rec` both
use `Reach₀`, and `Reach~` survives only as the bridge lemma.

Three readings taken where the plan was ambiguous, all cheap to revisit:

* `⌈W⌉` is the `~`-**closed** singleton `{s | W ~ s}`, not §3.2's raw singleton.
  A raw singleton is not `~`-closed, so it would contradict this very decision,
  and it is what lets both anchor rules use `Reach₀`.
* `Closed` is deliberately **not** a premise of any rule — it would break the
  downward closure of `𝒮` that §3.2's "each `Pr` has a largest `𝒮`" relies on.
  It is a hypothesis of the lemmas that need it instead.
* `⊢s′` is primed only to coexist with `Declarative`'s `⊢s`; it loses the prime
  at D2.

### 5.2′ OPEN: is `tclosed` a consequence rather than a premise?

**Raised by the owner 2026-09-11, not investigated.** `s/send` and `s/recv`
carry `tclosed` — the CONTINUATION set `𝒯` is `~`-closed — added because
`Safety/Preservation.agda`'s readiness argument re-roots both `Wait`s
(`waitV/unfold-top`) and re-rooting transports a leaf along `~`. The `⊢a` proof
got the same fact free from `blocked/bisim`; a `Pred` has no such theorem.

What is already known, so nobody re-derives it:

* The premise is **admissible**: it does not change what is typeable.
  `alg⇒set` always picks `𝒯 = Alg …`, closed by `alg/~`, so `⊢a ⟺ ⊢set`
  survives it. That is proved, and is why it was safe to add.
* It is **not** derivable for an arbitrary derivation. `𝒯` is existentially
  chosen and the judgment is downward closed, so a derivation may legitimately
  pick `𝒯 = { G }` for one typeable `G`, and a raw singleton is not `~`-closed.
  So "`tclosed` follows from `WellBehaved`" is false read literally.

**The form the owner's intuition probably takes, and the attack to try:**
every derivation should be *normalisable* to one whose sets are all `~`-closed,
by replacing each set with its `~`-closure — i.e.

```
set/close : Γ & Δ ⊢ PPr ∶ 𝒮 → Γ & Δ ⊢ PPr ∶ ⌈ 𝒮 ⌉closure
```

with all inner sets closed too. The induction looks like it goes through
BOTTOM-UP: at `s/send`, once the continuation's set has already been replaced by
its closure it *is* closed, so the leaf family is closed, so `wait/~` transports
`sub` from `s₀ ∈ 𝒮` to any `s ~ s₀` — which is exactly the missing step, and it
is where well-behavedness enters (`wait/~` rests on `na-bisim`/`~L→`/`~R→~`).
If that lemma exists, `tclosed` comes off the rules and is recovered as a lemma
applied once at `Preservation`'s entry.

Cost of leaving it as is: two premises on the rules that a reader will ask
about. Cost of the attack: one derivation transformer, ~60 lines, plus
re-proving the three places that pattern-match `s/send`/`s/recv`.

### 5.3 Recorded, deliberately deferred by D1

Set-valued `rec` anchors are *strictly more permissive* than `blocked/rec`: two
`v X` occurrences in different branches could close against different anchors.
Not built, not refuted. D1 sidesteps it. `s/rec₁` is the restriction of the set
rule, so this can be revisited later without redoing anything.

## 6. Evidence already in the tree — read before changing the recv rule

`Tests/LabelSorts.agda` (both decisions forced, exit 0) — one label carrying two
sorts at two leaves of a single receive's skip tree:

```
   s₀ --A⟶C#0<unit>--> s₁ --A⟶B#0<nat>-->  ended
   s₀ --A⟶C#1<unit>--> s₂ --A⟶B#0<bool>--> ended
```

Well behaved (`buildG … {p = tt}` elaborates). `step-sort-deterministic`
(`Definitions/Behav.agda:335`) compares two steps out of **one** state, so it
says nothing here; `step-arity-deterministic` (`:342`) likewise. The graph
survives `no-new-comm/step` (`:370`) because the skip step involves `A`, and
`no-new-branch/step` (`:360`) never fires because `s₀` offers no `A⟶B` comm.

* `M/good` — branch is `∅`: **accepted**.
* `M/bad` — branch is `ifp is-zero (var zero) …`: **rejected**, forced with
  `toWitnessFalse`. This is the control proving the `s/bool` leaf is genuinely
  visited.

`Tests/LabelSortsForward.agda` (exit 0) — the same shape extended so the protocol
varies in lockstep downstream; the branch `C ! here < var zero >∙ ∅` **uses** the
value and is accepted at both sorts, because `te/var` gives it `lookup Γ x`.

So: a body facing several sorts must typecheck under *all* of them, which admits
discarding *and* forwarding but not inspection. **Consequence: indexing `𝒯` by
`j` alone is wrong in both directions** — pick `s/nat` and you unsoundly accept
`M/bad`, pick `s/bool` and you incompletely reject `M/good`.

## 7. Next steps, in order

Each step ends green. The corpus is the oracle (§8).

1. ~~**[D5] Remove the declared sort vector**~~ — **DONE 2026-08-14**, commit
   `c70377d`. `Σ_？[_]·_` became `Σ_？·_` (`Definitions/Proc.agda:28`); 68 sites
   across `Definitions/`, `Check/`, `Safety/`, `Tests/`, `Examples/`.
   `./runall.sh --tests` exit 0 (incremental; everything downstream of
   `Proc.agda` rebuilt regardless). Two things learned, both worth knowing:
   `I` stayed inferable everywhere (the branch vector pins it, so no `{I = …}`
   had to be added), and the *dead* `{S : Vec Sort (suc I)}` binders had to be
   deleted alongside — leaving one in a signature where `S` no longer occurs
   turns it into an unsolvable metavariable at every use site.
   `Stale/` still uses the old syntax; it is not typechecked, so it was left.
2. ~~**Answer D4 (§5.1) and D5.2 (§5.2).**~~ — **DONE 2026-09-01.** D4 proved
   (`NoLoop.agda`); `~`-closure decided as option 1 and its assumption verified.
   See §5.1 and §5.2, both rewritten.
3. ~~**Write the abstract statements only**~~ — **DONE 2026-09-01**, in
   `Definitions/Typing/Sets.agda`: the operators, the seven rules, `⊢s′`. No
   `postulate`s, no holes, `agda --guardedness` exit 0. `Wait` is a coinductive
   `record` whose field is the inductive `Reach∀⁺`, so the fixpoints stay
   **sequenced, not nested** and the guardedness checker stays out of it.
   **This step also corrected §3.1** — see the `Reach∀⁺` bullet there.
   *Not in `ROOTS`; nothing re-checks it.*
3a. ~~**Prove `Wait P ∅ = ∅` for the corrected `Reach∀⁺`.**~~ — **DONE 2026-09-01**,
   `wait/∅` in `Sets.agda`. The corrected definition now agrees with D4, so
   `Reach∀⁺` is the *right* repair and not merely *a* repair.
   Simpler than `NoLoop.agda`: no ancestor context is needed, because a `Guard`
   leaf already packages the `Wait` it closes against. Recursion is again on the
   `Any (P ∈α_) αs` witness — `waitR/∅` hands it on unchanged at a guard leaf,
   but every cycle back through `waitR/∅` strictly decreases it, which Agda's
   termination checker accepts as-is.
4. **Prove the `Wait` characterisation** — both directions:
   `s ∈ Wait P 𝒮 ⟺ (Leaf = 𝒮) & [] ⊢skip P ◂ Pr ∶ s`. `⟸` is needed for
   "no bogus `no`", `⟹` for soundness.

   **`⟸` is DONE 2026-09-01** — `skip⇒wait` in `Definitions/Typing/SetsEquiv.agda`,
   exit 0, no holes. Two things it forced, both worth keeping:
   the bisimilarity is carried *into* the statement
   (`… ∶ G → G ~ s → Wait P 𝒮 s`) rather than applied afterwards, because a
   post-hoc `wait/~` puts the corecursive call in an ARGUMENT position where it
   is not guarded; and `Anc` stores each ancestor's `skip/step` **premises**, not
   its derivation, because `Reach∀⁺` admits no guard leaf at depth 0, so the node
   a cycle re-enters must be known to be a `skip/step`.

   **`⟹` is FALSE at the abstract level — MECHANIZED**, `Tests/WaitNotSkip.agda`,
   exit 0, no holes. A concrete `BTheory` with all **ten** `WellBehaved` axioms
   discharged (not nine — an earlier count here missed `recv-overlap⇒same-comm`),
   carrying `ce/wait : Wait P 𝒮 (g 0)` and
   `ce/no-skip : ¬ (Lf & [] ⊢skip P ◂ Pr ∶ g 0)`.

   The theory is an infinite chain `g i -< a i >-> g (suc i)`, `g i -< b i >-> e`,
   `e -< p >-> z`, with `a`/`b` free of `P` and `p` the only `P`-action.
   `𝒮` is "`P` is immediately active", which is `~`-closed (`𝒮/closed`) and is
   exactly the shape `s/send`'s leaf family takes — so this is not an artefact of
   an exotic `𝒮` nor of dropping §5.2. What separates the `g i` is the **arity**:
   at `g i` the branching is over `Fin (suc (suc i))`, so `a i ≠ a j`, so
   `g i ≁ g j`. Both steps out of `g i` share that arity and the comm `Q⟶R`,
   which is what keeps `step-arity-deterministic`, `recv-overlap⇒same-comm` and
   `step-diamond` satisfied. Bisimilarity on this theory is equality (`~⇒≡`),
   which is what makes `skip/cycle` unusable.

   This does NOT contradict `wait/∅` (step 3a): that argument needs the covered
   set to be step-closed, which fails here precisely because the `𝒮`-leaf at `e`
   is where `P ∈T (g i)` comes from.

   **Diagnosis — the ν is the problem, not the rules.** A `⊢skip` derivation is a
   FINITE tree whose leaves close against ANCESTORS; a greatest fixpoint over
   `Pred Behav` admits infinite unfoldings. The two coincide exactly when there
   are finitely many `~`-classes. So **no plain fixpoint over sets of states can
   be equivalent** — the property is genuinely one of the *(state, ancestor-set)*
   pair. Adding a finiteness axiom and proving `⟹` graph-only are both **ruled
   out by the owner**: the type systems must be equivalent, and `WellBehaved` must
   not change.

4b. ~~**Re-base `Wait` as a μ over (state, visited SET).**~~ — **DONE 2026-09-11.**
   `WaitV` in `Sets.agda`; `Reach∀`, `Reach∀⁺`, the coinductive record, `reach∀/~`
   and the mutual `wait/~` block are gone, replaced by `waitV/mono` and a
   three-case `wait/~`. **Both directions** of step 4 are now in `SetsEquiv.agda`
   (`skip⇒wait`, `wait⇒skip`), both plain structural recursions, no `Closed 𝒮`
   hypothesis, no theory-specific assumption. `wait/∅` (D4) is now a transport
   from `NoLoop.Loop-empty` rather than a second proof.
   `Tests/WaitNotSkip.agda` was flipped from counterexample to **regression
   test** (`ce/no-wait`): it is the only thing in the tree that would catch a
   "simplification" of `WaitV` back to a fixpoint over states alone.
   One lemma it forced: `waitV⇒skip` must be generalised over `V` with an
   inclusion `V ⊆ Vof Ξ`, because reconciling `Vof Ξ ∪ ⌈G⌉` with `Vof (G ∷ Ξ)`
   on the ARGUMENT of the recursive call loses structurality.
   *Superseded plan, kept for the record:* Keeps everything
   the owner requires — the seven typing rules of §3.2 are untouched, they still
   speak only of sets of states, and there is still no `skip` sub-judgment
   interleaved with typing. Only `Wait`'s internal definition changes, from a ν
   over states to an inductive family indexed by a visited *set*:

   ```
   data WaitV (P)(𝒮)(V : Pred) : Pred where
     wv/leaf  : 𝒮 s                                  → WaitV P 𝒮 V s
     wv/cycle : (∃ a. V a ∧ a ~ s) → P ∈T s          → WaitV P 𝒮 V s
     wv/step  : P-inactive s → (∃ step from s)
              → (∀ t. s -< _ >-> t → WaitV P 𝒮 (V ∪ ⌈s⌉) t)
                                                     → WaitV P 𝒮 V s
   Wait P 𝒮 = WaitV P 𝒮 ∅
   ```

   This is `⊢skip` with `Ξ` as a SET rather than a vector, so the equivalence
   becomes near-definitional and holds for every theory. The §1 win survives
   where it matters — the typing derivation is still one rule per process form and
   still `O(|Pr|)` — but §1's stronger claim that graph-walking collapses to "two
   closure operators" does NOT survive, and the `Justified`/`FailedFrom` idea
   returns in set form. **That trade needs the owner's sign-off before step 5.**
5. ~~**Prove `set ⟺ ⊢a`** for the whole judgment, using step 4.~~ — **DONE
   2026-09-11**, `Definitions/Typing/SetsAlg.agda`. Three new files, all
   `agda --guardedness` exit 0, no holes, no `postulate`s, no `TERMINATING`.

   * `set⇒alg : Γ & Δ ⊢ PPr ∶ 𝒮 → 𝒮 G → Γ & Δ ⊢a PPr ∶ G` (soundness).
     Every case is the same three moves: `sub`, then `wait⇒skip`, then
     `skip/map` rewriting the rule's own leaf family into `⊢blocked` ones.
     `skip/map` only needs the leaf translation at the tree's OWN process,
     because a `⊢skip` tree never changes the process it is about.
   * `alg⇒set : Γ & Δ ⊢a P ◂ Pr ∶ G → Γ & Δ ⊢ P ◂ Pr ∶ Alg Γ Δ (P ◂ Pr)`
     (completeness), where `Alg Γ Δ PPr = { G | Γ & Δ ⊢a PPr ∶ G }`. Stating it
     at the LARGEST set is what makes it provable — `s/send`'s `𝒯` must cover
     the continuation states of every leaf at once, which no singleton does —
     and `set/mono` (downward closure) recovers `⌈ G ⌉` and every smaller set.
     The recursion is on the **process**, not the derivation, since the
     derivation each case needs comes from `findMain` and is not a subterm;
     `algBr` is the mutual companion that makes `lu Br j` structural.

   Two things this step forced, both worth knowing:

   * **`s/recv`'s `conts` had to become CONDITIONAL** on `𝒯 j U` being
     inhabited: `∀ {j U t} → 𝒯 j U t → (U ∷ Γ) & Δ ⊢ Q ◂ lu Br j ∶ 𝒯 j U`.
     `blocked/recv` demands a continuation only for labels the behaviour
     actually offers, so the unconditional premise made the set rules strictly
     stronger than `⊢a` and completeness FALSE — a branch the graph never
     offers may be arbitrary, including carrying an ill-typed expression, which
     has no `Γ ⊢e E ∶ S` to give `s/send`, and `⊢a` still accepts it. Soundness
     is unaffected: `set⇒alg` reaches `conts` only from an actual edge, which
     supplies the witness. **Do not restore the unconditional form.**
   * **`findMain` (`Definitions/Typing/MainLeaf.agda`) closes §5.1's `¬¬∃`
     gap.** Every `⊢skip` tree has a `skip/main` leaf, constructively. It is
     `NoLoop.agda` generalised from the empty leaf family to an arbitrary one
     and from `⊥` to the leaf found; following the `P ∈T` run, as `NoLoop`
     does, is what avoids the double negation. `Norm.agda:169`'s `MainLeaf`
     hypothesis is NOT yet discharged from it — that `MainLeaf` is an inductive
     relation on a derivation, not a bare existential — but it is now one small
     step away.

   Also added: `Definitions/Typing/AlgProperties.agda`, bisimilarity transport
   for `⊢a`/`⊢blocked` (`alg/bisim`, `alg/~`), mirroring `Properties.agda`'s
   `td/bisim`. Needed at `s/rec`, whose premise sits at the `~`-closed anchor
   `⌈ W ⌉` (§5.2). Going through `alg/typing`/`td/bisim`/`norm` instead would
   have dragged in `Norm.agda`'s `MainLeaf` hypothesis for no gain.

   **None of these five files is in `ROOTS`, so nothing re-checks them.**
6. ~~**[Phase a] Move `Check/` onto the set form and delete `Check/Alg.agda`.**~~
   — **DONE 2026-09-11.** `Check/Alg.agda` (917 lines) is deleted and replaced
   by two files; `Check.agda`'s public surface is unchanged, so `Examples/`
   needed no edit at all and `Tests/` needed one import swap.

   * **`Check/Wait.agda`** — `wait?`, the graph-walking half. §3.1's `∈T?`
     split survives 4b and is the whole design: on `¬ P ∈T` no cycle can fire
     (forward closure of `¬ ∈T`), so `V` is irrelevant and that region is a
     plain lfp — the table `noCycle`, computed once; on `P ∈T` a revisit
     SUCCEEDS, so there is nothing to fail and `wt`/`Incl` is the entire
     termination argument. **`Justified`, `FailedFrom`, `failed⇒¬tree` and the
     four-component measure are gone, phase component included.**
     The visited set is read up to `~` (`Vof`) — that is what makes
     `Vof (mark V s)` and `Vof V ∪ ⌈ s ⌉` interchangeable in BOTH directions;
     with a raw index only the `yes` direction transfers, and it is the `no`
     direction that needs it.
   * **`Check/Sets.agda`** — the checker, one case per set rule, **structural
     on the process**: no `size/proc`, no `×-Lex`, no well-founded recursion in
     the walk at all. `lookup Br j` is made structural by the same `algBr`
     companion as `SetsAlg.agda`. Both directions of every case are
     `SetsAlg.agda`'s lemmas, not re-derivations — `yes` builds the derivation
     the way `set⇒alg` does, `no` returns the refuted `Wait`
     (`sendSub`/`recvSub`/`varSub`/`recSub`) or the failed premise
     (`inv/end`/`inv/if*`/`recGuard`/`inv/sendE`).

   `Check/Core.agda` was kept: its contents are decidability of the graph's own
   relations (expression checking, `findStep`/`findRecv`/`na?`/`bisim?~`/
   `messageGuarded?`), not algorithm.

   *Done:* `./runall.sh --tests` exit 0 — the whole corpus with decisions
   forced, **`Ex6` included**, plus both `toWitnessFalse` controls.

   **One performance trap, measured, worth not repeating.** `CLAUDE.md`'s
   "Agda shares argument thunks, not definition applications" applies to the
   `noCycle` table with full force: read as a module-level definition, every
   `lookup noCycle s` in the walk rebuilds the whole fixpoint.
   `Tests/Perf09_RevisitSpine`, deleting only that file's `.agdai`:

   | | time | peak RSS |
   |---|---|---|
   | old `Check/Alg.agda` (worktree at `fcac9e6`) | 9.60 s | 0.65 GB |
   | new, `noCycle` as a definition | 138.3 s | 1.5 GB |
   | new, `noCycle` as a bound argument | 9.78 s | 0.64 GB |

   So the set-based checker is at **parity** on this corpus, not faster — §1's
   asymptotic claim is about derivation SIZE, and these graphs are small. The
   table and its two correctness facts are passed into `wait?/acc` as
   arguments; **do not fold them back into the module.**
7. ~~**[Phase b] Migrate `Safety/`**, then delete `⊢a`, `⊢blocked`,
   `Norm.agda`, and the equivalence itself.~~ — **DONE 2026-09-15.**
   `⊢skip` STAYS: it is `Declarative.agda`'s, shared with `⊢p`'s own
   `t/skip`, and was never `⊢a`'s to delete.

   The seam turned out to be four sites, all the same shape — a `⊢p`-level
   operation with `⊢a` wrapped around it for no reason:

   * `Preservation.⊨/lookup` → `td⇒⊨` (was `norm` then `alg⇒⊨`).
   * `Preservation`'s uninvolved-participant case → **`t/unskip`**.  It was
     `⊨⇒typing (alg⇒⊨ (norm … tr))`: a `⊢p → ⊢a → ⊨ → ⊢p` round trip to
     absorb a trace that the declarative rule absorbs by itself.
   * `Substitution.⊨/rec/unfold` and `⊨/subst-expr` → `⊨⇒typing` out,
     `td⇒⊨` back, with `t/rec/unfold` / `typing/subst-expr` in the middle.
     `a/rec/unfold` and `alg/subst-expr` are gone; that file's own comment
     had already called these the two that would need a direct proof.

   Moved rather than re-proved, all `⊢a`-free already: `set/mono` and the
   `⊨` family (`_&_⊨_∷_`, `⊨/if-inv`, `⊨/rec-guarded`, `⊨/end-inv`) to
   `Sets.agda`; `skip/map` to `Properties.agda`.  `MainLeaf.agda` and
   `NoLoop.agda` STAY — `findMain` is generic in the leaf family and is now
   what `waitFind` is built from.
8. Update `FUTURE_WORK.md` (§B is superseded by this file; §A's investment is
   now in `Stale/NetworkProject.agda.stale`) and `CLAUDE.md`'s architecture
   section.  **STILL OPEN.**

Optional, independent, any time: delete the dead `PathViaP` family (§4).

## 8. Facts a cold session must know

* **Checking:** `agda --guardedness path/to/File.agda` from the repo root for a
  one-file change. `./runall.sh --tests` for the corpus (measured 2026-08-05 at
  303 s / 6.9 GB with `--clean`). Do not run `runall.sh` for a one-file edit.
* **CI does not cover this branch** — `.github/workflows/ci.yml` runs on `main`
  only. The corpus run is manual, and with D6 (in-place replacement) it is the
  only thing standing between you and a silently wrong checker.
* **Capture a green baseline before step 1**, for the same reason.
* **Every example goes in `Tests/`**, as a real file, with every decision forced
  (`toWitness` / `toWitnessFalse`) so that compiling the file *is* the search
  running. Pair a positive with a control that must be rejected. `TEST_ROOTS`
  globs `Tests/*.agda`, so a new file is covered automatically.
* **`Ex6`** (`Tests/AlgCheck.agda`) is the case that separates a batched checker
  from the specification — its anchor is `M`, which `G` does not reach. Any
  set-based rewrite that disagrees with the existing checker on `Ex6` is wrong,
  not clever. The refuted anchor-moving idea is in
  `Stale/PushRecDerivations.agda.stale`.
* `δ ≤ 1` throughout `Examples/` and `Tests/` — no process nests `rec` inside
  `rec` (grep, 2026-08-13). Relevant because it makes `FUTURE_WORK.md` §B.5's
  `Δ`-indexing worry moot; D1 removes it structurally anyway.
* All the gotchas in `CLAUDE.md` still apply, in particular: pin vector
  implicits; a recursion stops being structural through a `subst`; a value
  consulted many times must be a **bound argument** (Agda shares argument
  thunks, not definition applications); a hand-written dead end must be `ended`.
* *Unmeasured hypothesis, recorded so it is not mistaken for a finding:*
  `restrict P` (`Check/Alg.agda:132`) and `approximation G`
  (`Definitions/Graph/Bisimulation.agda:155`) are definition applications on the
  hot path and are therefore probably recomputed per call. Step 6 makes both
  bound-once tables by construction, so this should not be fixed separately —
  but if you want a number to compare against, measure before step 6, not after.

## 9. Casualties of D2 — **DECIDED 2026-09-15: written off, kept verbatim**

`NetworkProject.agda` is now `Stale/NetworkProject.agda.stale`, alongside
`PushRecDerivations.agda.stale`.  Nothing imported it, it was not in `ROOTS`,
and porting it is a separate exercise: the projection argument never mentions
the skip machinery that changed, so restating it over `_&_⊢_∷_` is a port,
not a rewrite, and can be done whenever §A is picked up again.  The text is
kept precisely so that stays true.

*The original note:*

**`Definitions/Graph/NetworkProject.agda` (497 lines) is stated over
`⊢a[ netTheory (n₁ ∥ n₂) ]`.** Deleting `⊢a` stops it compiling, and because it
is deliberately not in `ROOTS`, **nothing will tell you**. It is `FUTURE_WORK.md`
§A's entire proved investment (`project` plus `projL`/`projR`, `mkPair-proj`,
`pstep-invP`, `skip-projL`, `inT-lift`, `inT-projL`, `stuck⇒∉T`), and it
typechecks today. Either port it as part of step 7 or write it off knowingly and
restate §A against the new judgment later.

## 10. Do not do these

* Do not use an existential backward closure for the skip side (§3.1).
* **Do not re-base `Wait` on a fixpoint over states alone** — neither the ν of
  §3.1 nor any repair of it. Machine-refuted twice over: `Tests/WaitNotSkip.agda`
  (the ν accepts a state no `⊢skip` tree covers, which made `⊢ ⟺ ⊢set`
  unprovable) and, for the earlier `Guard` reading, `wait/∅`. Skippability is a
  property of the (state, ancestor-set) PAIR; the visited set in `WaitV` is not
  decoration. `Tests/WaitNotSkip.agda` is the regression test.
* Do not make `s/recv`'s `conts` unconditional again — completeness is false
  with it (§7 step 5).
* Do not index `𝒯` by `j` alone (§6).
* Do not add global sort/arity consistency as a well-formedness condition (§2).
* Do not re-introduce set-valued `rec` anchors without re-opening D1 (§5.3).
* Do not rebuild the `Presentation` refactor — built, measured, reverted;
  `FUTURE_WORK.md` §D says why.
* Do not resurrect `⊢head`/`⊢hskip`/`head/typing`, `Definitions/Types.agda`,
  `Definitions/TypeChecker*`, `Definitions/Typing/Normalise.agda`, or
  `Check/Decide.agda`.
* **Do not dig a fact out of a `⊢p` derivation directly** — convert to `Wait`
  first, then `waitFind`.  `t/skip`'s leaf family is `⊢p` itself, so a chase
  past a `skip/cycle` does not terminate-check, whichever of the two known
  chase techniques you reach for.  See §4.
