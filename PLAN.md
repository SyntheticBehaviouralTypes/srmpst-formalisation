# Typing/Alg.agda: a/send rewrite

Primitives (standard Post/Pre reachability notation):

```agda
Post   : Action → Pred → Pred
Post α 𝒮 = λ t → ∃[ s ] 𝒮 s × s -< α >-> t

Post¬* : Part → Pred → Pred
Post¬* P 𝒮 = λ t → ∃[ s ] 𝒮 s × s -[¬ P ]->* t

Dom    : Action → Pred
Dom α = λ t → ∃[ u ] t -< α >-> u
```

New rule:

```agda
a/send : (etd : Γ ⊢e E ∶ S)
       → (rdy : Post¬* P 𝒮 ⊆ Dom (P⟶Q#i<S>))
       → (td  : Γ & Δ ⊢a P ◂ Pr ∶ Post (P⟶Q#i<S>) (Post¬* P 𝒮))
       → Γ & Δ ⊢a P ◂ Q ! i < E >∙ Pr ∶ 𝒮
```

Drops `𝒯`, `tclosed`, `sub`, `Wait` entirely for this rule. `Closed` becomes a lemma, not a field.

# Typing/Alg.agda: a/recv rewrite

Contravariant: process must handle at least what's offered (`BranchLabels ⊆ Enabled(s)`), checked pointwise per state in the closure (not aggregated over the whole set — needed for equivalence with `t/recv` in `Declarative.agda`).

```agda
Labels : Set₁
Labels = Action → Set

Enabled : Behav → Labels
Enabled s α = ∃[ t ] s -< α >-> t

Dom* : Labels → Pred          -- states where ALL of A is enabled
Dom* A s = A ⊆ Enabled s

BranchLabels : Labels          -- labels consumed by Br
BranchLabels α = ∃[ j ] α ≡ (P⟶Q#j<U j>)
```

```agda
a/recv : (rdy   : Post¬* Q 𝒮 ⊆ Dom* BranchLabels)
       → (conts : ∀ j → (U j ∷ Γ) & Δ ⊢a Q ◂ lu Br j ∶ Post (P⟶Q#j<U j>) (Post¬* Q 𝒮))
       → Γ & Δ ⊢a Q ◂ Σ P ？· Br ∶ 𝒮
```

**NOTE: double-check/adjust `BranchLabels` — `P`, `Q`, `U` are free in it, not OK as written.**

## TODO
- [ ] Fix `BranchLabels` (free `P`, `Q`, `U`).
- [ ] `a/var`, `a/rec`: revisit `Wait`/`Reach₀` with same Post/Post¬* style.
- [ ] Decide `Dom α = Post α ⊤` (drop as separate primitive) vs. keep standalone.
- [ ] Re-derive `alg⇒typing`/`typing⇒alg` equivalence against new rule shapes.
- [ ] `Check/Alg.agda`: `alg?` decides `Post¬*`/`Post`/`⊆`/`Dom` via `Bits` + `Reachability.agda` machinery (soundness/completeness vs. these declarative defs).
