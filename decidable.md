# Plan: `Maybe` → `Dec` for `Definitions/TypeChecker.agda`

Goal: every checking function in `Definitions/TypeChecker.agda` returns
`Dec (⋯)` instead of `Maybe (⋯)`, i.e. the checker becomes a genuine decision
procedure for the declarative judgment `Γ & Δ ⊢p P ◂ Pr ∶ s` over a finite
graph LTS (and for `⊢s M ∶ s`). The outer fuel and its reducing metric
(`suc (size G) * processFuel Pr`, one unit per `checkWithFuel` layer) stay as
they are.

This is **not** a mechanical conversion. A `no` must refute *every* derivation
of a judgment that is **not syntax-directed**: `t/skip` and `t/unskip` apply at
every node, `skip/cycle` closes proofs up to bisimilarity `~`, and derivations
may be arbitrarily deep. The plan therefore has three parts: (i) new decidable
graph infrastructure, (ii) a *semantic characterization* of the `⊢skip[ prod ]`
judgment (this is the crux at `checkSkipStep`, line 430), and (iii) a
*bounded algorithmic judgment* with soundness and completeness theorems that
turn the fueled checker into a `Dec`.

---

## 0. The three obstacles (why `Maybe` is currently essential)

**(O1) Fuel exhaustion is inconclusive.**
`checkWithFuel 0 … = nothing` is fine for `Maybe`; for `Dec` the `0` case must
produce `¬ (Γ & Δ ⊢p …)`, which is simply false in general. Fix: the checker
must decide a *fuel-indexed algorithmic judgment* `Alg k`, exactly; then a
separate **completeness theorem** shows any declarative derivation fits inside
the budget `F Pr = suc (size G) * processFuel Pr`. Only the composite
`check = decide (Alg (F Pr))` + soundness + completeness is a `Dec` of the
declarative judgment. Fuel-0 then legitimately answers "no derivation *of the
bounded judgment*" — never "no derivation at all". (§4, §6)

**(O2) `checkSkipStep` (line 430) never synthesises `skip/cycle`.**
It demands a `prod` subtree for *every* outgoing edge, so any cycle in the
P-inactive region makes the whole search fail (the comment at lines 432–433
says exactly this). The visited vector `Ξ` is already threaded through
`checkSkip` precisely so loops can be closed by `skip/cycle`. But — and this
is the central logical finding of this plan — **"always close revisits with
`skip/cycle`" is incomplete** (counterexample in §3.2), because `skip/cycle`
is `nonprod` and `skip/step` demands that the *chosen* branch be `prod`.
The correct move is to characterize `⊢skip[ prod ]` semantically and decide
*that* (§3). The visited vector is then used in the *derivation-constructing*
direction, where literal (`≡`-based, via `~refl`) cycle closing suffices.

**(O3) `t/end` is checked by an over-approximation.**
`checkDirect … ∅ s` uses `globallyInactive?` (P absent from *every* state),
which is sufficient but not necessary for `¬ P ∈T s` (absence from the
*reachable cone of `s`*). A `no` from `globallyInactive?` refutes nothing.
Must be replaced by an exact `∈T? : ∀ P s → Dec (P ∈T s)` (§2.2).

Also note the general shape of the problem: at **every** process constructor
three rule heads are possible — the structural rule, `t/skip`, and `t/unskip`
— so every `no` is a triple refutation. This is what the algorithmic judgment
of §4 makes tractable.

---

## 1. Phase 0 — mechanical `Dec` conversions (no metatheory needed)

These are finite searches over lists/`Fin`; each `nothing` branch already
contains the refutation implicitly. New signatures:

| function | new type | refutation content |
|---|---|---|
| `inferExpression` | `∀ Γ E → Dec (TypedExpression Γ E)` | on `minus1`/`is-zero` failure: any typing of the whole forces (by inversion) a typing of `E` at `s/nat`, contradicting the sub-refutation **plus uniqueness** (below) |
| `messageGuarded?` | `∀ Pr → Dec (MessageGuarded Pr)` | `rec`, `v`, `∅`: `λ ()`; `ifp`: inversion `mg/if` |
| `findAction` | `∀ α xs → Dec (ActionAt α xs)` | standard `Any`-style search; `no` = `¬Any` |
| `findStep` | `∀ s α → Dec (∃[ t ] s -< α >-> t)` | `no` via `step⇒listed` composed with the `findAction` refutation |
| `findRecv` | `∀ P Q I xs → Dec (RecvWitness P Q I xs)` | same shape, driven by `matchRecv?` (already `Dec`) |
| `findIncoming` | `∀ P s xs → Dec (Incoming P s xs)` | same shape |
| `first` | drop, or `∀ xs → Dec (∃[ x ] x ∈ xs)` | list nonemptiness |
| `allMaybe` | `allDec : (∀ x → Dec (F x)) → ∀ xs → Dec (All F xs)` | i.e. a dependent `All.all?`; `no` = pointer to the failing element |
| `allParticipants` (in `checkSession`) | `(∀ i → Dec (A i)) → Dec (∀ i → A i)` | finite `∀` over `Fin n`; `no f = λ g → f (g i₀)` |

New helper lemma (trivial, by induction on the two derivations):

```
⊢e-unique : Γ ⊢e E ∶ S → Γ ⊢e E ∶ S′ → S ≡ S′
```

Needed wherever a rule mentions the *same* sort in two premises
(`t/send`: `gr` at sort `S` and `etd : Γ ⊢e E ∶ S`): the refutation
"no edge labelled with the inferred sort `S₀`" only refutes `t/send` because
any `etd` in any derivation must also be at `S₀`.

Also needed, from the `WellBehaved` bundle already in scope: `step-deterministic`
(a `t/send` derivation's continuation state is forced to be the `t` that
`findStep` found, so one recursive `no` at `t` refutes all of `t/send`), and
`step-is-prop` (two proofs of the same transition are equal — keeps `All`
lookups over `edges G s` coherent with quantification over transition proofs).

**Watch out (edge duplicates):** `edges G s` may contain duplicate entries.
`toWitness (fromWitness m)` need not be `m`, so *never* let a decision depend
on the *position* of an edge — make every per-edge decision a function of the
edge **value** `(α , t)`. Then `All.lookup` at whichever membership proof
`step⇒listed gr` produces is automatically consistent. (This matters again in
§3.4 for the `ktd` mode function.)

---

## 2. Phase 1 — decidable graph infrastructure (`LTS/`)

### 2.1 Reachability (`LTS/Reachability.agda` — implements the existing TODO)

Implement the least-fixed-point reachability the file's TODO already sketches,
generalized by a decidable *node* filter (needed for `NL` in §3) and returning
*bounded paths* (needed for the construction in §3.4):

```
-- one-step expansion of a Bool-vector of marked states, restricted to
-- nodes satisfying `ok`; iterate (size G) times ⇒ fixpoint
reachVia : (ok : State G → Bool) (start : State G) → Vec Bool (size G)

-- soundness / completeness w.r.t. the path relation
data PathVia (ok : …) : State G → State G → ℕ → Set   -- ok holds on all
                                                       -- states strictly
                                                       -- before the target
reachVia-sound    : lookup (reachVia ok s) t ≡ true → ∃[ n ] n ≤ size G × PathVia ok s t n
reachVia-complete : PathVia ok s t n → lookup (reachVia ok s) t ≡ true
reachVia?         : ∀ ok s t → Dec (∃[ n ] PathVia ok s t n)
```

Proof shape for completeness: paths may be assumed **simple** (cut the loop
between two visits of the same state — the standard pigeonhole shortening;
prove `PathVia ok s t n → ∃[ m ] m ≤ size G × PathVia ok s t m` first), then
induction on the ≤ `size G` iterations, using monotonicity of the expansion
step. This is a self-contained ~150–300 line development and unblocks
everything else.

Bridge to the abstract relations of `graphTheory G`:

```
path⇒skip : PathVia (λ _ → true …) -- with ¬P-labels
-- more precisely: a path all of whose edge labels satisfy P ∉α_
--   gives  s -[¬ P ]->* t   (by induction, using skip/step / skip/refl)
skip⇒path : s -[¬ P ]->* t → ∃ path        (inverse direction)
```

(For the label-filtered variant either add an edge filter to `PathVia` or
reuse `ReachableBy (P ∉α_)` and connect it to the Bool-vector fixpoint; the
existing `ReachableBy` is the right declarative side.)

### 2.2 Exact participation: `∈T?`

```
∈T? : ∀ (P : Part) (s : State G) → Dec (P ∈T s)
```

Characterization to prove and then decide by §2.1:

```
P ∈T s  ⇔  ∃[ t ] Reachable s t × ∃ (α ,u) ∈ edges G t. P ∈α α
```

(⇒ by induction on `_∈T_`: `in/α` gives the empty path, `in/later` prepends a
step. ⇐ by induction on the path: `in/later` at each step, `in/α` at the end.)
Then `Dec` by: decide the reachable set, then `Any (λ edge → P ∈α? …)` over
each reachable state's edge list.

`checkDirect … ∅ s` then becomes

```
checkDirect recur Γ Δ P ∅ s with ∈T? P s
... | no P∉T  = yes (t/end P∉T)
... | yes P∈T = no λ { (t/end done) → done P∈T ; … }   -- plus the t/skip /
                                                       -- t/unskip cases, §4
```

`GloballyInactive` / `inactive⇒notIn` can be deleted (or kept as a fast path
on the `yes` side only).

---

## 3. Phase 2 — the crux: deciding `Γ & Δ & [] ⊢skip[ prod ] P ◂ Pr ∶ s`

First, an important scoping fact that simplifies everything:
**`t/skip` fixes `Ξ = []`** (`(Γ & Δ ⊢p_∶_) & [] ⊢skip[ prod ] …`). The checker
only ever needs to *decide* the skip judgment at the empty visited vector.
Non-empty `Ξ` appears only *inside* proofs and inside the derivation
constructor of §3.4.

Throughout this section fix `Γ, Δ, P, Pr` and write `Leaf t` for the
declarative typing `Γ & Δ ⊢p P ◂ Pr ∶ t`.

### 3.1 Semantic characterization

For a set (decidable predicate) `L : State G → Set` define:

* `NL_L s` — the set of states `t` reachable from `s` by a path whose states
  (including `s` and `t`, excluding nothing else) all lie **outside `L`**.
  So `s ∈ L → NL_L s = ∅`.
* `Reach_L t` — some state of `L` is reachable from `t` (ordinary
  reachability; the path automatically stays in `NL_L` until its first `L`-hit).
* the **semantic skip predicate**

```
SemSkip L s  =  ∀ t → t ∈ NL_L s → (P not-active-in t) × Reach_L t
```

Intuition: a `prod` skip tree at `s` is a finite tree whose internal nodes are
exactly the non-`L` states reachable from `s` (children = *all* graph
successors, by `skip/step`'s `ktd`), whose leaves are `L`-states (`skip/main`)
or ancestor-bisimilar states (`skip/cycle`, `nonprod`), and in which every
internal node has at least one `prod` child (the `proj₁ (ktd gr) ≡ prod`
side-condition, with `gr` the chosen transition). Following chosen-`prod`
children strictly descends the finite tree, so **every internal node reaches an
`L`-leaf**; conversely `skip/cycle` closes the bookkeeping but adds no
semantic content because bisimilar states satisfy the same conditions.

Two easy lemmas to prove first:

```
-- (S1) the "spine lemma": prod derivations reach a main leaf
spine : Leaf & Ξ ⊢skip[ prod ] P ◂ Pr ∶ s →
        ∃ a path from s to some u with a skip/main leaf, i.e. Reach_{mains} s
  -- induction: skip/main ⇒ refl-path; skip/step ⇒ prepend gr, recurse on
  -- the chosen branch (prod by the side-condition); skip/cycle is nonprod.

-- (S2) monotonicity in L
semSkip-mono : L ⊆ L′ → SemSkip L s → SemSkip L′ s
  -- NL_{L′} ⊆ NL_L (avoiding a bigger set is harder) and Reach_L ⊆ Reach_{L′}.
```

### 3.2 Why the naive `Ξ`-search is incomplete (record this in a comment!)

Naive plan: in `checkSkipStep`, before recursing into successor `t`, test
`t ~ (some entry of s ∷ Ξ)` and close with `skip/cycle`; recurse only on fresh
states, so `Ξ` stays duplicate-free, depth ≤ `suc (size G)`, and fuel-0 is
unreachable by pigeonhole. **This is sound but incomplete.** Counterexample:

* States `s, a, ℓ`; edges `s → a`, `s → ℓ`, `a → s` (all labels ¬P);
  `Leaf` holds at `ℓ` only; `s ̸~ a` (different action sets).
* A `prod` derivation at `([], s)` exists:
  at `s` choose the branch to `ℓ` (`skip/main`, `prod`); the branch to `a`
  must also be handled: at `a` the only successor is `s`, and `skip/cycle`
  there is `nonprod` — **but the chosen branch of `a`'s `skip/step` must be
  `prod`**, so the derivation *re-expands* `s` (a second `skip/step` at `s`,
  with `Ξ = [a , s]`), where the `ℓ`-branch is `prod` and the `a`-branch now
  closes by `skip/cycle`.
* The naive search at `a` sees successor `s ∈ Ξ`, closes it `nonprod`, finds
  no `prod` child, and fails.

Moral: revisited states must sometimes be **re-expanded to manufacture the
`prod` witness**. Re-expansion makes canonical tree depth Θ(size G²) in the
worst case (chains of such gadgets), so the single `suc (size G)` inner fuel
of `checkSkip` cannot survive either. Hence: decide `SemSkip` (finite,
fuel-free, §3.3), and build the derivation separately with a lexicographic
double fuel (§3.4). The *outer* metric `suc (size G) * processFuel Pr` is
untouched; only `checkSkip`'s private inner fuel is replaced.

### 3.3 The decision procedure

Given `recur : ∀ t → Dec (Alg k ⋯ t)` (the fuel-decremented checker, §4):

```
L?    : ∀ t → Dec (L_alg t)            -- L_alg t = Alg k … Pr t; tabulate over states G
NL?   : Dec-set via reachVia (λ t → not ⌊ L? t ⌋) s     -- §2.1
semSkip? : Dec (SemSkip L_alg s)
  = for every t with NL-mark: inactiveAt? P t  ×  reachVia? (…) t →L_alg
```

All components are finite conjunctions/disjunctions over `states G` — **no
fuel, no recursion** beyond the calls to `recur`. This replaces
`checkSkipStep`+`checkSkip` in `checkClosure`.

### 3.4 Theorem B (sufficiency / the constructor): `SemSkip L s → Γ & Δ & [] ⊢skip[ prod ] P ◂ Pr ∶ s`

Here `L` must come with witnesses: `∀ t → L t → Leaf t` (the `yes`-derivations
from `recur`). Construction `build Ξ t`, maintaining invariants
(i) `t ∈ NL_L s ∪ L`, (ii) `Ξ` = the path of states from the root:

* `t ∈ L` → `skip/main (witness t)`. (`prod`)
* else `t ∈ NL_L s`, so `SemSkip` supplies `na : P not-active-in t` and a
  **bounded path** `t → … → ℓ ∈ L` (from `reachVia-sound`; length ≤ size G).
  Emit `skip/step gr na ktd refl` where:
  - `gr` := the transition along the path's first edge (`listed⇒step`);
  - `ktd gr′` is defined **by the value of `gr′`'s edge** (see §1's duplicate
    warning), via `step⇒listed`:
    * edge value = the spine edge → recurse `build (t ∷ Ξ) u*` **with the path
      tail as the new path** — even if `u* ∈ Ξ` (re-expansion, cf. §3.2);
      mode `prod`;
    * target `u ∈ t ∷ Ξ` *literally* (`≟Fin`) → `skip/cycle` at that index
      with `~refl` — **this is where the visited vector closes loops**; mode
      `nonprod`; (no `bisim?` needed here at all — literal equality suffices
      for completeness because ~-revisits are simply re-expanded)
    * otherwise → recurse `build (u ∷ … )` with a fresh `Reach_L u` path
      (u ∈ NL_L s by forward closure); mode `prod`.
  - the side condition `proj₁ (ktd gr) ≡ prod` holds *by computation*: the
    spine case is selected by decidable edge-value equality on `gr`'s own edge.

**Termination**: lexicographic on `(#states ∉ Ξ , length of remaining path)`.
Spine recursion keeps or shrinks component 1 and strictly shrinks 2; fresh-
state recursion strictly shrinks 1 (and resets 2 ≤ size G). Implement as two
nested fuels initialized to `suc (size G)` each, with arithmetic invariants
`fuel₁ + |distinct Ξ| > size G` etc., so both `0`-cases are discharged by
pigeonhole (`⊥-elim`), not by `nothing`.

### 3.5 Theorem A (necessity): `Γ & Δ & [] ⊢skip[ prod ] P ◂ Pr ∶ s → SemSkip L* s`

where `L*` is the **~-closure of the set of `skip/main`-leaf states of the
given derivation `D`** (each with its `Leaf` subderivation; the ~-closure
carries `td/bisim`-transported derivations). Stating A with this
derivation-relative leaf set (rather than "all declaratively typable states")
is essential: it is what makes the completeness glue in §6 go through with
*bounded* budgets.

Proof (the delicate one — all needed transport machinery **already exists** in
`Safety/Skip.agda`):

* Generalize over `Ξ` with the invariant
  `Anc Ξ = ∀ X → (prod derivation at the tail context drop (suc X) Ξ of lu Ξ X)`
  — every visited entry is an internal (`skip/step`, hence `prod`) node of the
  enclosing derivation, and its own subderivation lives over the shorter tail
  vector. At the top, `Anc [] = ⊤`.
* Fix `t ∈ NL_{L*} s` with a path of length `k`; prove
  `(inactive t × Reach_{L*} t)` **by induction on `k`**, walking the path down
  the derivation, *not* by induction on the derivation:
  - Nodes along the walk cannot be `skip/main` (their states are in `L*`,
    contradicting `t ∈ NL`), and are `prod` where required, so they are
    `skip/step`; step into the child matching the path edge.
  - Child is `prod` → its subderivation continues the walk (`Anc` extended by
    the current node's derivation).
  - Child is `skip/cycle` at `u₁ ~ lu Ξ′ X` → **jump**: take the ancestor
    derivation from `Anc`, `skip/weaken-visited*` it up to the current
    context, transport it along `~` with **`skip-leaf/bisim`**
    (leaf transport = `td/bisim`; its main-leaf states stay inside `L*`
    because `L*` is ~-closed), obtaining a `prod` derivation *at `u₁` itself*
    over the current `Ξ′` — the walk continues concretely with `k` already
    decreased. This is why induction on `k` terminates while induction on the
    derivation would not (the ancestor is *bigger*).
  - At `k = 0` (the node for `t`): `skip/step` gives `na` = inactivity, and
    the spine lemma (S1) gives `Reach_{L*} t` (its endpoint is a main-leaf
    state ⊆ `L*`).
* Auxiliary transports needed: inactivity along `~` (the `na ∘ ~R→` pattern
  already used in `skip-td/bisim`), and `Reach` along `~` against a ~-closed
  target set (replay the path with `~L→`/`~L→~`).

(`skip/unfold-cycle` from `Safety/Skip.agda` is closely related machinery and
may shortcut parts of this; but the `Anc`-invariant walk above is the
self-contained argument.)

Contrapositive of A (+ monotonicity S2 + the containment `L* ⊆ L_alg`
established during the completeness induction, §6) is exactly what the `no`
branch of `semSkip?` needs.

---

## 4. Phase 3 — the bounded algorithmic judgment `Alg`

Define an inductive family mirroring the current checker **exactly** (so the
current `just`-constructions become its soundness proof nearly line-for-line):

```
data Alg : ℕ → ∀ {γ δ} → Vec Sort γ → Vec (State G) δ
         → Part → Proc γ δ → State G → Set where
  -- no constructor at fuel 0
  alg/direct : Direct k … → Alg (suc k) …
  alg/pred   : ∀ r → ((α , s) ∈ edges G r) → P ∉α α → Alg k … Pr r
             → Alg (suc k) … Pr s                      -- one unskip STEP
  alg/skip   : SemSkip (Alg k … Pr) s → Alg (suc k) … Pr s
```

with `Direct k` the syntax-directed layer: one constructor per process
constructor, premises `Alg k` on **subterms** (send/recv/if/rec), plus the
side conditions exactly as in `checkDirect` but in their *exact* forms
(`∈T?` from §2.2 for `∅`; `T? (bisim? …)` with `BisimulationCorrect.sound` /
`.complete` for `v X`; `⊢e-unique`-backed expression checks; `matchRecv?`
et al.).

Then:

* `alg/mono : k ≤ k′ → Alg k … → Alg k′ …` (induction; needed by §6's
  arithmetic).
* **Decision**: `checkWithFuel : ∀ k → Dec (Alg k Γ Δ P Pr s)` — structurally
  the current function with every `Maybe` replaced by the Phase-0/1/2 `Dec`s;
  `checkPredecessors` stays the finite disjunction over `states G` it already
  is (its `no` is a finite conjunction of refutations); `checkClosure`'s skip
  arm is `semSkip?` (§3.3). **Fuel 0 answers `no (λ ())` — honestly**, since
  `Alg 0` has no constructors.
* **Soundness**: `alg-sound : Alg k … → Γ & Δ ⊢p P ◂ Pr ∶ s`.
  `alg/direct` = today's `checkDirect` constructions; `alg/pred` =
  `t/unskip (skip/one (listed⇒step …) P∉α)`; `alg/skip` = `t/skip ∘ build`
  (Theorem B, with leaf witnesses `alg-sound ∘ recur-yes`).

---

## 5. Interlude — the cost measure on declarative derivations

Completeness needs to recurse on something. Structural recursion fails
(normalization steps replace subderivations by *other* derivations), so define
`cost : Derivation → ℕ`:

* rule node = 1 + premises;
* `t/unskip tr td` = `length tr + 1 + cost td` (so trace-shortening is ≤);
* function-shaped premises (`t/recv`'s `conts`, `skip/step`'s `ktd`) are
  measured through the **edge list**: `sum/max over (α,t) ∈ edges G ·` of the
  premise at `listed⇒step` — well-defined because `step-is-prop` makes the
  premise independent of the transition proof.

Lemmas about `cost`:

```
(C1) subderivation (through a canonical edge) has strictly smaller cost
(C2) cost (td/bisim Δ~Δ′ G~G′ D) ≡ cost D        -- td/bisim is rule-for-rule;
     -- edge lists of bisimilar states have the same action/target multiset
     -- up to ~, measured through canonical picks; if ≡ is painful, ≤ suffices
(C3) trace shortening: t/unskip with a non-simple trace has a ≤-cost variant
     with a simple trace (cut graph loops; td unchanged)
(C4) revisit normalization (see §6): replacing a derivation by a nested
     derivation of the SAME judgment strictly decreases cost
```

---

## 6. Phase 4 — completeness

**Theorem.** `Γ & Δ ⊢p P ◂ Pr ∶ s → Alg (suc (size G) * processFuel Pr) Γ Δ P Pr s`.

Combined with §4 this yields the goal:

```
check : ∀ Γ Δ P Pr s → Dec (Γ & Δ ⊢p P ◂ Pr ∶ s)
check … with checkWithFuel (suc (size G) * processFuel Pr) …
... | yes a = yes (alg-sound a)
... | no ¬a = no (¬a ∘ complete)
```

Proof architecture — strong induction on `cost D`, with a budget invariant.

**6.1 The round tree.** Canonicalize the head of `D` (collapse `t/unskip`
chains with `skip/cat`, drop `skip/refl`, i.e. WLOG at most one `t/unskip`
above a structural rule or `t/skip`). Between two structural rules the
derivation is a tree of *rounds* at the same `(Γ, Δ, Pr)`:
an unskip **step** moves to a predecessor state (decompose the trace from the
`s` end, one `alg/pred` per step — this is why `checkPredecessors` is
single-step); a `t/skip` node **branches** into its `skip/main` leaves (each
leaf continues the round tree at its own state). Each round costs exactly one
fuel layer in `Alg`.

**6.2 Revisit normalization.** If the round tree below the current node ever
revisits the current node's *state*, some subderivation proves the **same
judgment** with strictly smaller cost (C1); recurse on it (strong induction —
this replaces derivation surgery entirely). Iterating: WLOG the round tree
from the current node never revisits the current state. Doing this at each
position as you descend, and observing that a normalized sub-round-tree is a
sub-tree of the original (so states excluded once stay excluded), gives:
**WLOG every root-to-leaf chain in the round tree has pairwise-distinct
states**, hence length ≤ size G.

**6.3 Budget arithmetic.** Show by the same induction, with `h` = number of
rounds already emitted on the current chain (`h ≤ size G`, states distinct,
current state fresh):

```
B Pr h = (suc (size G) ∸ h) + suc (size G) * (processFuel Pr ∸ 1)
```

is a sufficient budget: emitting a round needs `B Pr (suc h) ≤ B Pr h ∸ 1` ✓;
ending in a structural rule needs `1 + suc (size G) * processFuel(subterm)
≤ B Pr h`, which follows from `processFuel(subterm) < processFuel Pr`
(true for every premise: send/rec continuation, each recv branch via
`branchesFuel`, both `if` branches) and `h ≤ size G ∸ 1` ✓. At `h = 0` this is
exactly `suc (size G) * processFuel Pr`. Use `alg/mono` to round budgets up.

**6.4 The skip rounds.** For a `t/skip std` round, Theorem A gives
`SemSkip L* s` with `L*` = ~-closure of `std`'s main-leaf states, each
carrying a derivation of cost `< cost D` (C1, C2). By induction each such
state lands in `L_alg = Alg (k-1) … Pr ·` (they are exactly the round-tree
children, so §6.3 provides the `k-1` budget). Then `L* ⊆ L_alg` and
monotonicity (S2) turns `SemSkip L*` into the `SemSkip L_alg` demanded by
`alg/skip`. This containment argument is the reason Theorem A is stated
relative to the derivation's own leaves — with "all typable states" the
budget glue would be impossible at inner fuel levels.

---

## 7. Phase 5 — top level

* `checkClosed`, `check` — direct from §6's `check`.
* `checkSession : ∀ M s → Dec (⊢s M ∶ s)` — finite `∀` over participants
  (Phase 0's `allParticipants`).
* `checkProcess / checkSession (outer) / checkRooted*` — `Dec (CheckedProcess …)`
  / `Dec (CheckedSession …)`. Subtlety: the record stores *a* `wellBehaved`
  field, so the `no` case with `wellBehaved? G = yes wb` but no derivation
  must rule out derivations over a *different* `wb′`. The typing data type
  only ever uses `BTheory` fields, never `wb`, so prove once:

  ```
  typing-wb-irrelevant :
    (wb wb′ : WellBehaved (graphTheory G)) →
    Typing.MPST wb  ._&_⊢p_∶_ Γ Δ PPr s →
    Typing.MPST wb′ ._&_⊢p_∶_ Γ Δ PPr s
  ```

  by a (mutual, mechanical) induction — or refactor `Typing.MPST` to carve the
  judgment out of a `wb`-parameterized module (bigger diff; the lemma is
  cheaper).

---

## 8. Suggested order of implementation (each step compiles on its own)

1. **Phase 0** conversions + `⊢e-unique` (small, immediate value).
2. **`∈T?`** and the `t/end` fix (§2.2) — removes a genuine gap even in the
   `Maybe` checker.
3. **Reachability fixpoint** (§2.1) — the existing TODO; self-contained.
4. **`SemSkip` + Theorem B** (§3.3–3.4): replace `checkSkip`/`checkSkipStep`.
   At this point the *`Maybe`* checker already accepts cyclic skip regions —
   the original line-430 incompleteness is fixed before any `Dec` appears.
5. **`Alg` + decision + soundness** (§4) — mostly a re-typing of current code.
6. **`cost` + Theorem A + completeness** (§5, §3.5, §6) — the bulk of the new
   proof text; keep it in fresh modules, e.g.
   `Definitions/TypeChecker/{Algorithmic,Sound,Cost,SkipSemantics,Complete}.agda`.
7. **Phase 5** wrappers; delete the stale comments at lines 432–433 and
   477–478 of `TypeChecker.agda`.

## 9. Inventory

**Reused as-is:** `td/bisim`, `skip-td/bisim`, `skip-leaf/bisim`,
`skip/weaken-visited`, `lookup/weaken-visited`, (`skip/unfold-cycle`),
`skip/cat`, `skip/one`, `~L→/~R→/~L→~/~R→~`, `∈~`, `step-deterministic`,
`step-is-prop`, `bisimulationCorrect` (`sound`+`complete`), `wellBehaved?`,
`listed⇒step`/`step⇒listed`, `matchRecv?`, `inactiveAt?`, `≟Action`/`≟Edge`.

**New:** `⊢e-unique`; `∈T?`; `reachVia` + sound/complete + bounded simple
paths; `SemSkip`, `semSkip-mono` (S2), spine lemma (S1), Theorem A
(with the `Anc` invariant and ~-transport of inactivity/reachability),
Theorem B (lex-fuel constructor, literal-`Ξ` cycles, edge-value `ktd`);
`Alg` + `alg/mono` + `alg-sound`; `cost` + (C1)–(C4); the completeness
theorem (§6); `typing-wb-irrelevant`.

**Deliberately unchanged:** `processFuel`/`branchesFuel`, the outer fuel
`suc (size G) * processFuel Pr` and its once-per-layer decrement, the
declarative judgments, the `Safety/` metatheory.
