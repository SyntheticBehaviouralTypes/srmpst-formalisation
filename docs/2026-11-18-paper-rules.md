# 2026-11-18 — Agda mirrors the ECOOP27 rules

Branch `paper-rules`, worktree `../srmpst-agda-paper-rules`, started from
`main` at `15fef27`.  Goal: the declarative rules in Agda read 
EXACTLY (or as close as reasonable) as the rules of the ECOOP27 paper 
  (`papers/ECOOP27/sections/roles.tex`). Introduce notations if neecessary.

## Decisions

| topic | paper | Agda |
|---|---|---|
| communication | point-to-point in §roles, multicast later | **multicast stays**; the paper's p2p rules are `Qs = ⁅ q ⁆`; `Foreign` is the later `p ∉ R` : agda should align with what is written in the paper *exactly* i.e. p \not\in R (or another symbol for \in if it clashes with something) | 
| bisimilarity | states of `𝓑/∼` (classes) | **states become `∼`-closed predicates** (classes); `Δ`, `Ξ` hold classes; class equality `≐` behind notation |
| labels | receive `{ℓ(x_ℓ).P_ℓ}_{ℓ∈𝓛}` | **labels are `ℕ`**; a receive carries `Vec (Maybe Proc) n`, `𝓛` is its domain, `ℓ ∈ 𝓛` is `Br ∋ ℓ ↦ P`; `step-arity-det` goes |
| sessions | `R ◁ P ∣ …` up to AC | **vector over an `Assignment` stays**, with paper-like notation |
| first-in | `r first-in (R, G)`, with `r ∈ R` | one record replacing `Q∈` + `Focus`, it should define EXACTLY `_first-in_` notation to be used in Agda |
| rule names | `⊢-Send`, …, `Skip-Step` | constructors `send`, `recv`, `skip`, `forward`, `if`, `end`, `rec`, `var`, `skip-main`, `skip-cycle`, `skip-step` |

## Phases

1. Labels (`Actions`, `Proc`, `Behav`, `Typing/*`, `Safety/*`, `Graph/*`,
   `Check/*`, `Utils/Branch`, `Proc/Syntax`, examples, tests).
2. Classes, and the declarative judgment over them.
3. `⊢p ⟺ ⊢a` (`AlgNorm`, `AlgDeclarative`) and `Safety` over classes.
4. Checker, examples, tests, README.

Each phase ends type-checked (`./runall.sh --tests`).  Memory: run every
check under a cap well below *available* memory (`AGDA_MEM_PERCENT`); the
2026-11-18 baseline (incremental, roots only) peaked at 609 MB.

## Status

- [x] worktree, baseline (`./runall.sh`, incremental: 25 s, 609 MB)
- [x] phase 1 (labels) — 2026-11-18: `./runall.sh --tests
  --CheckClosedProof` passes (362 s, 3.6 GB peak, cap 30%)
  - checked: `Utils/Family` (new: `_∋_↦_`, `∋-functional`, `_∋?_`),
    `Actions` (`Choice` = `ℕ` label + sort), `Proc` (send label `ℕ`,
    receive `Vec (Maybe Proc) n`, `s/comm` carries `Cont k` with
    `Br ∋ ℓ ↦ Cont k`), `Behav` (`step-arity-det` gone), `Typing/*`,
    `Transfer`, `Safety/Preservation`
  - also checked: `Safety/Progress` (`ReadyAt` carries the branch;
    `recv-head` reads it off the typing instead of arity; 1.1 GB peak),
    `Safety.agda`, `Graph/*` (choice code is `(label , sort)`; the arity
    condition is gone from `LocalConditions`), `Check/Alg` (receive case:
    `BrTable` of branch probes along the branch vector, per-edge `EvOK`),
    `Proc/Syntax` + `Utils/Branch` (`family`: ℕ-keyed branches, missing
    labels are `nothing`, no `every` proof)
  - examples and tests: label constants `Fin n` → `ℕ` (participants
    stay `Fin N`); `Tests/WaitNotSkip` tells its chain states apart by
    label (`continue i = suc i`) instead of arity
- [x] phase 2 — naming: classes are written `G` (or `B`) as in the paper,
  never a calligraphic letter; the class of `G` is `[ G ]`, as the paper's
  `[G]_∼ = {G′ | G′ ∼ G}`
  - `Definitions/Classes`: `Cls`, `[_]`, `_≐_`, the MLTS `B/∼` (`C`), and
    the lemmas moving steps, runs, `G -⟨ R ⟩->`, `R ∈ G` and `first-in`
    between a class and its representatives
  - `Definitions/Typing/Declarative`, module `MPST.Paper`: Fig. 4 as
    `Γ & Δ ⊢[ R ] P ∶ G` and `Γ & Δ & Ξ ⊢[ R ] P ∶ G`, with constructors
    `send`, `recv`, `skip`, `forward`, `if`, `end`, `rec`, `var`,
    `skip-main`, `skip-cycle`, `skip-step`; `_first-in_` (a pair since
    phase 6)
  - the generic leaf-indexed skip tree moved to `AlgEquiv` as `SkipT`
- [x] phase 3 — `Properties` (`td/≐`: invariance under `≐`), `AlgNorm`
  (`⊢ → ⊢a`), `AlgDeclarative` (`⊢a → ⊢`, every theory), `Substitution`,
  `Transfer`, `Safety`.  `Alg`'s `Offers` asks `P ∉ Q` (as the paper's
  multicast rule) instead of `Foreign`; `Balanced.recv-send` gives
  `Progress` the sender's send event
- [x] phase 4 — README (paper judgments, classes, `Utils/Family`, process
  syntax, Agda 2.8.0.2 + stdlib 2.4); `FUTURE_WORK.md` (a dated note that
  `⊢p`, `⊢skip`, `t/…`, `skip/…` are the former names)
- [x] phase 5 — closer to the paper (actions stay sets of events, for a
  future asynchronous semantics)
  - Fig. 2: session rules `P-Com`, `P-If1`, `P-If2`, `P-Rec`; labels
    `msg α` and `τ` (pattern synonyms over `Maybe Action`); `Assignment`
    is `roles` and `partition : ∀ r → ∃! _≡_ (λ k → r ∈ lu roles k)`, with
    `owner`, `owner/∈`, `∈/owner` derived
  - Fig. 3: views are the data type `V-Ext`/`V-Own`; internal steps
    `G -[⊆ R ]-> G′`; `G -[¬ R ]->* G′` is `Star` of `G -[¬ R ]-> G′`;
    `R ∈ G` is `∃ G′ . G -→* G′ × G′ -⟨ R ⟩->` (one definition of each
    since phase 6); `∼` is one coinductive record
    `_~_` (`Behav`) whose fields are the paper's two conditions, `sym`
    (symmetric) and `step` (closed under steps); being coinductive, it is
    the largest such relation
  - Fig. 4: one `∈`/`∉` (instances in `MPST.Paper`), contexts `Δ ▸ G`,
    `Ξ ▸ G`, `Γ ▸ t`
  - synchronous case: the paper's label `p ⇾ q # c` (`Actions`);
    `Balanced.send⇒step`, `step⇒send`, `recv⇒step`, `step⇒recv`, and on
    classes `MPST.Paper.Sync` (`send⇒label`, `label⇒send`, `recv⇒label`,
    `label⇒recv`)
- [x] phase 6 — one definition per notion
  - the paper's Fig. 3 notions are defined once, in `BTheory`, so they
    serve behaviours and classes (`C`) alike, and `MPST.Paper` re-exports
    `C`'s: `G -⟨ R ⟩-> G′`, `G -⟨ R ⟩->`, `G -→`, `G -→* G′`,
    `G -[¬ R ]-> G′`, `G -[¬ R ]->* G′` (`Star`), `R ∈T G`, and
    `r first-in (R , G) = r ∈ R × (∀ G -[¬ R ]->* G′ -< α >-> . R ∈ α → r ∈ α)`
  - removed, with their conversions: `Focus` (the algorithmic `Dom` and
    `Offers` ask `first-in`), the trace-based `∈T` and `-[¬ R ]->*`
    (`run⇒trace`, `trace⇒run`, `∈T⇒trace`, `trace⇒∈T`, `first-in⇒focus`,
    `focus⇒first-in`), `not-active-in` (now `¬ G -⟨ R ⟩->`), `Alg.Active`
    (now `s -⟨ P ⟩->`), `View.Idle` (now `Ps ∉αˢ α`), `Actions.Foreign`,
    and the unused trace lemmas `tr/trans`, `tr-transport`, `trᶜ⇒`, `tr⇒ᶜ`
  - `r ∉ α` and `R ∉ α` (`_∉α_`, `_∉αˢ_`) are literally `¬ r ∈ α`,
    `¬ R ∈ α`; `∉α→¬∈α`, `¬∈α→∉α`, `∉αˢ→¬∈αˢ`, `¬∈αˢ→∉αˢ` are gone.
    `≡nothing→∉α`/`∉α→≡nothing` read `r ∉ α` off the action; `∉αˢ-at` and
    `∀∉→∉αˢ` go one role at a time
  - labelled traces `G -[ αs ]-> G′` stay for the safety statements and
    the examples; `tr⇒run` turns an `R`-free trace into a run

## Where Agda still reads differently from the paper

Summary: Figs. 2–4 match the paper rule for rule and premise for premise.
What differs is (1) multicast, (2) actions as sets of events, (3) notation
forced by Agda (reserved symbols, de Bruijn indices, existing names), and
(4) two representation choices in Figs. 2–3.

**1. Multicast** (the paper's p2p rules are the case `Qs = ⁅ q ⁆`)

| paper | Agda |
|---|---|
| `p ⇒ q!ℓ(e).P` | `p ⇒ Qs ! ℓ < e >∙ P` |
| `G —p→q:ℓ(t)→ G′` (⊢-Send) | `G -[ p ⇒ Qs ∶ ℓ < t > ]-> G′` |
| `G —p→q:ℓ(t)→ G′` (⊢-Recv), `G —p→q→` | `G -[ q ⇐ p ∶ ℓ < t > ]-> G′`, `G -[ q ⇐ p ]->` |
| ⊢-Recv | adds `p ∉ R` (the paper's multicast rule) |

**2. Actions are sets of events** (`Vec (Maybe Event) N`), kept for a
future asynchronous semantics.  The rules ask about the event at one role;
in the synchronous case `MPST.Paper.Sync` shows these are the paper's
labelled steps `G -< p ⟶ Qs # c >-> G′` (`p ⇾ q # c` for one `q`).

**3. Notation**

| paper | Agda | why |
|---|---|---|
| `Γ; Δ ⊢_R P : G`, `Γ; Δ; Ξ ⊢_R P : G` | `Γ & Δ ⊢[ R ] P ∶ G`, `Γ & Δ & Ξ ⊢[ R ] P ∶ G` | `;` is reserved |
| `Δ, X : G`, `Ξ, G`, `Γ, x : t` | `Δ ▸ G`, `Ξ ▸ G`, `Γ ▸ t` | `_,_` is the pair; de Bruijn |
| `Δ, X : G ⊢ X : G` | `var : X ∶ G ∈ Δ → …` (lookup up to `≐`) | de Bruijn; classes compared by `≐` |
| `Γ ⊢ e : t`, `Bool` | `Γ ⊢e e ∶ t`, `s/bool` | existing names |
| `G —R→ G′`, `G —R→`, `G →`, `G →* G′` | `G -⟨ R ⟩-> G′`, `G -⟨ R ⟩->`, `G -→`, `G -→* G′` | `-[_]->` is the trace relation; `-->` starts a comment |
| `G —R̄→ G′`, `G —R̄→* G′`, `G —⊆R→ G′` | `G -[¬ R ]-> G′`, `G -[¬ R ]->* G′`, `G -[⊆ R ]-> G′` | |
| `α ⊆ R` | `Internal R α` | |
| `{ℓ(x_ℓ).P_ℓ}_{ℓ∈𝓛}`, `ℓ ∈ 𝓛 ∧ … P_ℓ …` | `Br : Vec (Maybe Proc) n`, `∃[ Pℓ ] Br ∋ ℓ ↦ Pℓ × …` | de Bruijn binder; finite family |
| `P is message-guarded` | `MessageGuarded P` | |

The single `∈`/`∉` lives in `MPST.Paper`; outside it, the proofs use
`∈αˢ`, `∈α`, `∈T`, `∈ᵛ` and `Data.Fin.Subset`'s `∈`.

**4. Representation**

| paper | Agda |
|---|---|
| sessions `R ◁ P ∣ C`, up to AC; →P-Par | a vector `Session` over an `Assignment`; no `P-Par` |
| `⊢_{R_k} P_k : [⟨G⟩_{R_k}]` | `⊢ᵛ[ Ps ] P ∶ G`: `[ G ]` in `view Ps` (views keep the states: no `⟨_⟩`) |
