# Typing/Alg.agda: set-based rules

Hard requirement: `⊢a ⟺ ⊢p` for EVERY well-behaved theory, finite or infinite, independent
of the checker.

## States and sets (`Relation.Unary`: `Pred`, `_∈_`, `_⊆_`, `_∩_`, `Satisfiable`)

```agda
State δ  = Vec Behav δ × Behav          -- anchors of enclosing recs, current behaviour
States δ = Pred (State δ) 0ℓ

Post α 𝒮 (ws , t) = ∃[ s ] (ws , s) ∈ 𝒮 × s -< α >-> t
Dom  α   (_ , s)  = ∃[ t ] s -< α >-> t
Act  P   (_ , s)  = ∃[ α ] ∃[ t ] s -< α >-> t × P ∈α α
Offers P Q I x    = Σ[ j ∈ Fin (suc I) ] ∃[ U ] x ∈ Dom (P ⟶ Q # j < U >)
Ended P  (_ , s)  = ¬ P ∈T s

s ⇝[ P ] t        = P not-active-in s × ∃[ β ] s -< β >-> t
Reach P 𝒮 (ws , t) = ∃[ s ] (ws , s) ∈ 𝒮 × Star (_⇝[ P ]_) s t
Front P 𝒮         = Reach P 𝒮 ∩ Act P          -- where the idle walk stops

Wait   P L (ws , s) = WaitV P (λ t → (ws , t) ∈ L) ∅ s
Unskip P 𝒜 (ws , s) = ∃[ a ] (ws , a) ∈ 𝒜 × a -[¬ P ]->* s   -- t/unskip
Var X    (ws , s)   = lu ws X ~ s
Diag 𝒜 (W ∷ ws , s) = (ws , W) ∈ 𝒜 × W ~ s                   -- rec entry
```

## Rules

```agda
a/send : let α = P ⟶ Q # i < S > in
         Γ ⊢e E ∶ S
       → 𝒮 ⊆ Wait P (Dom α)
       → Γ ⊢a P ◂ Pr ∶ Post α (Front P 𝒮)
       → Γ ⊢a P ◂ Q ! i < E >∙ Pr ∶ 𝒮

a/recv : 𝒮 ⊆ Wait Q (Offers P Q I)
       → (∀ {j U} → let α = P ⟶ Q # j < U > in
          Satisfiable (Post α (Front Q 𝒮))
          → (U ∷ Γ) ⊢a Q ◂ lu Br j ∶ Post α (Front Q 𝒮))
       → Γ ⊢a Q ◂ Σ P ？· Br ∶ 𝒮

a/if   : Γ ⊢e E ∶ s/bool → Γ ⊢a P ◂ A ∶ 𝒮 → Γ ⊢a P ◂ B ∶ 𝒮 → Γ ⊢a P ◂ ifp E then A else B ∶ 𝒮
a/end  : 𝒮 ⊆ Ended P → Γ ⊢a P ◂ ∅ ∶ 𝒮
a/var  : 𝒮 ⊆ Wait P (Unskip P (Var X)) → Γ ⊢a P ◂ v X ∶ 𝒮
a/rec  : MessageGuarded Pr
       → Γ ⊢a P ◂ Pr ∶ Diag 𝒜
       → 𝒮 ⊆ Wait P (Unskip P 𝒜)
       → Γ ⊢a P ◂ rec Pr ∶ 𝒮
```

Pointwise form: `Γ ⊢at PPr ∶ x = Σ 𝒮. (Γ ⊢a PPr ∶ 𝒮) × x ∈ 𝒮`.

## Why

- **Frontier, not `¬P`-reachability.** `⊢skip` walks only through `P`-idle states and stops
  at the first state where `P` can act. Every `¬P`-reachable state is too strong
  (`R⟶Q ; P⟶Q#i`); walking past `P`-active states is too weak (`(P⟶R) ∥ (R′⟶Q ; P⟶Q#i)`).
- **`Wait`, not a reachability condition.** `Tests/WaitNotSkip.agda`'s infinite chain and a
  finite loop with the same exits agree on every "each idle-reachable state satisfies φ"
  condition; `⊢skip` rejects the first and accepts the second. Separating them needs
  well-foundedness modulo `~`, and building a tree from it needs the leaf/cycle choice
  recorded in the witness (`~` is not decidable). `Wait ⟺ ⊢skip` for every theory
  (`AlgEquiv.agda`).
- **Anchors in the state, no `Δ`.** `t/var` must return to the state where THAT `rec` was
  entered. A set-valued `Δ` only checks "somewhere in `𝒜`": `rec X. Q!a. X` over
  `W₁ ⇄ W₂` (`W₁ ≁ W₂`) would be accepted. With `Diag`, `(W₁ ∷ ws , W₁)` steps to
  `(W₁ ∷ ws , W₂)` and `a/var` checks `W₂` against `W₁` only.
- **`conts` conditional** on `Post` being inhabited: an unoffered branch may be ill-typed,
  and `⊢p` accepts it.
- **`Unskip`, not `Reach`,** for anchors: `t/unskip` follows `¬P`-labelled steps, which may
  leave `P`-active states.
- **`MessageGuarded`** is essential: without it `rec X. X` holds at any `𝒜`.

## Checker (not part of the equivalence)

`Check/Alg.agda`, built on `Definitions/*` only.

- `Probing.probe P E Γ Pr 𝒮 𝒮? : Probe Γ P Pr 𝒮`. `𝒮` is where typing is PROBED: `found`
  returns the largest `𝒯 ⊆ 𝒮` where `Pr` is typed (`typed`, `max`, non-empty); `none`
  says no derivation touches `𝒮`. Structural recursion on `Pr`:
  - send/recv: probe the continuation (each offered `(j , U)`) at `Post α (Front P 𝒮)`;
    keep states with `Wait` whose every continuation state was typed;
  - if: intersection; `∅`: `Ended`; `v X`: `Wait (Unskip (Var X))`;
  - rec: probe the body at `Diag (Past 𝒮)` (states an idle walk from `𝒮` reaches, run
    back along `¬P` steps); entry set = where every `~`-copy typed.
- `alg?` (typed at exactly `𝒮`): one probe + `𝒮 ⊆ 𝒯`; empty `𝒮` goes to `alg-empty?`
  (state-free facts only).
- `Wait` decided by a visited-set walk (`WaitDec`); an exact revisit with `P ∉T` is
  refuted by the loop. Result sets store the decided bit (`Ready`), since `Wait : Set₁`.
- `Check/TypeCheck.agda`: `tc?` = `alg?` at a singleton + the equivalence; `tcSession?`.

**Cost.** Sets are tabulated lazily (`memo`, `Tab`) and passed as ARGUMENTS so Agda
shares them; graph facts (idle/`¬P` reachability rows, bisimilarity, `∈T`, activity,
steps) are tabulated once per participant (`Env`), the bisimilarity matrix once per
graph (`Shared`: bisimilarity matrix, plain reachability rows). `∈T` is read off
the reachability rows (was: one full `reachVia` per target state). Action equality
is a bit (`eqAction`), because `_≟Action_` matches `yes refl` and so forces proofs
even for its tag. In each search the cheaper test goes first: reachability rows are
the expensive tables. Measured 2026-09-25: every test/example ≈ 10–12 s (≈ 9.7 s is
Agda loading); `Examples/IndepW` 26 s / 2.6 GB (was 86 s / 7.5 GB).

## TODO
- [x] `Definitions/Typing/Alg.agda` rewritten; inversions `at/send-inv`, `at/recv-inv`.
- [x] `AlgEquiv.agda`: `Wait` ⟺ `⊢skip`, unchanged content.
- [x] Equivalence for EVERY theory: `alg⇒typing`/`at⇒typing` (`AlgDeclarative.agda`),
      `typing⇒alg`/`td⇒at` (`AlgNorm.agda`, largest set `Typed`, `a/rec` at `Entry`).
- [x] `Substitution`, `Safety/{Preservation,Progress,Termination}`, `Check/Wait`,
      `Tests/WaitNotSkip` repaired.
- [x] `Check/Alg.agda`: `probe` (structural; returns the largest typed subset of the
      probed set) and `alg?` on top of it. Uses only `Definitions/*`.
- [x] `Check/TypeCheck.agda`: `tc?`/`tcSession?` via `alg?` at a singleton + the
      equivalence. `Check/Graph`, `Check/Network` use it. `./runall.sh` passes.
- [x] `Tests/AlgCheck`, `Tests/CheckAlgSanity` moved to the new API.
      `./runall.sh --tests` passes.
- [x] Tables: `memo`, `Env`, `Shared`, `After?` tabulates `Front`, leaf sets
      (`Dom`, `Offers`) tabulated, send/recv result sets scan edges, bit equality
      for actions, `∈T` from reachability rows, tabulated idle filter.
- [ ] Remaining cost (IndepW): `reachVia` rows, O(n³·deg) each (linear `Vec` lookups
      and an edge scan per state pair, n iterations). A worklist/BFS row with its own
      soundness/completeness would cut it to O(n + E).
- [ ] `Wait`: one walk per root; results not shared across roots.
- [x] `Check/Wait.agda` was unused by the checker: deleted 2026-09-25 (`CLEANUP.md`).
