{-# OPTIONS --guardedness #-}

-- The set-based type checker (TODO.md §7 step 6) — the replacement for
-- `Check/Alg.agda`.
--
-- The algorithm IS the shape of the rules in `Definitions/Typing/Sets.agda`:
-- one case per process form, each of which
--
--   1. decides that rule's own leaf family, pointwise on states, and
--   2. hands it to `Check/Wait.agda`'s `wait?`.
--
-- Nothing here walks the graph and the process at the same time, so there is
-- no interleaved search, no `Justified`/`FailedFrom`, and no four-component
-- measure: the recursion is structural on the process, exactly as the rules
-- are, and every graph walk is inside `wait?` or `reach¬P?`.
--
-- The two directions of each case are `Definitions/Typing/SetsAlg.agda`'s
-- lemmas, not re-derivations: `yes` builds the `⊢a` derivation the way
-- `set⇒alg` does (`wait⇒skip` then `skip/map` then `a/skip`), and `no` turns a
-- hypothetical `⊢a` derivation back into the `Wait` that was just refuted
-- (`sendSub`/`recvSub`/`varSub`/`recSub`) or into the premise that failed
-- (`inv/end`, `inv/if*`, `recGuard`).

open import Data.Bool using (Bool; true; false; T)
open import Data.Fin using (Fin)
  renaming (_≟_ to _≟Fin_; zero to fzero; suc to fsuc)
import Data.Fin.Properties as FinP
open import Data.List using (List; []; _∷_; filter)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as MemP
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
  using (_×_; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Vec
  using (Vec; []; _∷_; lookup)
  renaming (map to vmap)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (map′; _×-dec_)

open import Definitions.Behav using (BTheory; WellBehaved)
open import Definitions.Expr
open import Check.Core
import Check.Wait
import Definitions.Typing as Typing
import Definitions.Typing.Properties as Props
import Definitions.Typing.Algorithmic
import Definitions.Typing.Sets
import Definitions.Typing.SetsEquiv
import Definitions.Typing.SetsAlg
import Definitions.Typing.Norm

module Check.Sets (N : ℕ) where

  open Processes N using (module GraphChecker)
  open import Definitions.Graph.Core N
    renaming (_-<_>->_ to GStep)
  open import Definitions.Graph.Reachability N
    using (PathVia; path/nil; path/cons; reachVia?; ∈T?)

  module SetCheck
    (G : Graph)
    (wb : WellBehaved (graphTheory G))
    where

    open Typing.MPST wb
    open GraphChecker G wb
      using ( messageGuarded?; matchRecv?; MatchRecv
            ; findStep; findRecv; RecvWitness
            ; na?; bisim?~ )

    module NM = Definitions.Typing.Norm {N} {graphTheory G} wb

    module A = Definitions.Typing.Algorithmic {N} {graphTheory G} wb
    open A
      using ( _&_⊢a_∶_; _&_⊢blocked_∶_
            ; a/skip; a/if; a/end
            ; blocked/send; blocked/recv; blocked/var; blocked/rec
            ; alg/typing )

    open Definitions.Typing.Sets wb using (Pred; Reach₀; ⌈_⌉; WaitV)
    open Definitions.Typing.SetsEquiv wb using (wait⇒skip)
    open Definitions.Typing.SetsAlg wb
      using ( skip/map; Alg
            ; inv/end; inv/ifE; inv/ifT; inv/ifF
            ; sendSub; recvSub; varSub; recSub; recGuard; inv/sendE )

    private
      variable
        γ δ : ℕ

    -- ══════════════════════════════════════════════════════════════════
    --  `¬P`-reachability, via `reachVia?` on the `P`-free restriction
    --  (lifted unchanged from the deleted `Check/Alg.agda`)
    -- ══════════════════════════════════════════════════════════════════

    restrict : Part → Graph
    restrict P =
      graph (size G) (vmap (filter (λ e → P ∉α? proj₁ e)) (outgoing G))

    redges≡ :
      ∀ P s
      → edges (restrict P) s ≡ filter (λ e → P ∉α? proj₁ e) (edges G s)
    redges≡ P s = VecP.lookup-map s _ (outgoing G)

    rstep⇒ :
      ∀ {P s α t}
      → GStep {restrict P} s α t
      → (s -< α >-> t) × P ∉α α
    rstep⇒ {P} {s} {α} {t} gr
      with MemP.∈-filter⁻ (λ e → P ∉α? proj₁ e)
             (subst ((α , t) ∈_) (redges≡ P s)
               (step⇒listed {restrict P} gr))
    ... | mem , P∉α = listed⇒step {G = G} mem , P∉α

    rstep⇐ :
      ∀ {P s α t}
      → s -< α >-> t
      → P ∉α α
      → GStep {restrict P} s α t
    rstep⇐ {P} {s} {α} {t} gr P∉α =
      listed⇒step {G = restrict P}
        (subst ((α , t) ∈_) (sym (redges≡ P s))
          (MemP.∈-filter⁺ (λ e → P ∉α? proj₁ e)
            (step⇒listed {G = G} gr) P∉α))

    path→tr :
      ∀ {P a b n}
      → PathVia (restrict P) (λ _ → true) a b n
      → a -[¬ P ]->* b
    path→tr path/nil = skip/refl
    path→tr (path/cons _ gr rest) =
      let gr′ , P∉α = rstep⇒ gr
      in tr¬/step gr′ P∉α (path→tr rest)

    tr→path :
      ∀ {P a b}
      → a -[¬ P ]->* b
      → ∃[ n ] PathVia (restrict P) (λ _ → true) a b n
    tr→path ([] , tr/refl , []) = zero , path/nil
    tr→path (_ ∷ αs , tr/step gr tr , P∉α ∷ ps)
      with tr→path (αs , tr , ps)
    ... | n , rest = suc n , path/cons _ (rstep⇐ gr P∉α) rest

    reach¬P? : ∀ P a b → Dec (a -[¬ P ]->* b)
    reach¬P? P a b =
      map′ (λ { (_ , p) → path→tr p }) tr→path
        (reachVia? (restrict P) (λ _ → true) a b)

    -- `Reach₀ P 𝒜` for a decidable anchor set: one reachability query per
    -- candidate anchor.  This is `s/var`'s and `s/rec`'s leaf family.
    reach₀? :
      ∀ P (𝒜 : Pred) → (∀ a → Dec (𝒜 a)) → ∀ s → Dec (Reach₀ P 𝒜 s)
    reach₀? P 𝒜 𝒜? s =
      FinP.any? (λ a → 𝒜? a ×-dec reach¬P? P a s)

    -- ══════════════════════════════════════════════════════════════════
    --  The checker: one case per set rule
    -- ══════════════════════════════════════════════════════════════════

    open Check.Wait N using (module WaitCheck)
    open Props wb using (skip/bisim-back)

    -- One offered edge's obligation.  Outside the `mutual` block so that it
    -- REDUCES where it is used — inside, its clauses are not yet available.
    EdgeOK :
      ∀ {γ δ I}
      → Vec Sort γ → Vec (State G) δ
      → Part → Part → Vec (Proc (suc γ) δ) (suc I)
      → Edge (size G) → Set
    EdgeOK {I = I} Γ Δ P Q Br (α , t) =
      ∀ {j : Fin (suc I)}{U}
      → α ≡ (Q ⟶ P # j < U >)
      → Alg (U ∷ Γ) Δ (P ◂ lookup Br j) t

    mutual

      alg? :
        ∀ {γ δ}
          (Γ : Vec Sort γ)(Δ : Vec (State G) δ)
          (P : Part)(Pr : Proc γ δ)(s : State G)
        → Dec (Γ & Δ ⊢a P ◂ Pr ∶ s)

      -- s/end
      alg? Γ Δ P ∅ s with ∈T? G P s
      ... | yes inT = no λ td → inv/end td inT
      ... | no ¬inT = yes (a/end ¬inT)

      -- s/if
      alg? Γ Δ P (ifp E then A else B) s
        with checkExpression Γ E s/bool
      ... | no ¬etd = no λ td → ¬etd (inv/ifE td)
      ... | yes etd with alg? Γ Δ P A s | alg? Γ Δ P B s
      ...   | yes ta | yes tb = yes (a/if etd ta tb)
      ...   | no ¬ta | _      = no λ td → ¬ta (inv/ifT td)
      ...   | _      | no ¬tb = no λ td → ¬tb (inv/ifF td)

      -- s/send.  The sort is inferred ONCE, outside the set (`⊢e-unique`
      -- is what says every leaf agrees with it), and the leaf family is
      -- then a single fully-known action per state.
      alg? Γ Δ P (Q ! i < E >∙ Pr) s with inferExpression Γ E
      ... | no ¬typed = no λ td → ¬typed (inv/sendE td)
      ... | yes (S , etd)
        with WaitCheck.wait? G wb P _ (sendLeaf? Γ Δ P Q i S Pr) s
      ...   | yes w =
        yes (a/skip
              (skip/map (λ { (_ , gr , td) → blocked/send gr etd td })
                (wait⇒skip P (Q ! i < E >∙ Pr) _ w)))
      ...   | no ¬w = no λ td → ¬w (sendSub etd td)

      -- s/recv
      alg? Γ Δ P (Σ Q ？· Br) s
        with WaitCheck.wait? G wb P _ (recvLeaf? Γ Δ P Q Br) s
      ... | yes w =
        yes (a/skip
              (skip/map (λ { ((_ , _ , _ , gr) , conts) → blocked/recv gr conts })
                (wait⇒skip P (Σ Q ？· Br) _ w)))
      ... | no ¬w = no λ td → ¬w (recvSub td)

      -- s/var
      alg? Γ Δ P (v X) s
        with WaitCheck.wait? G wb P _
               (reach₀? P ⌈ lookup Δ X ⌉ (bisim?~ (lookup Δ X))) s
      ... | yes w =
        yes (a/skip
              (skip/map
                (λ { (_ , W~a , tr) →
                       let _ , tr′ , H~ = skip/bisim-back W~a tr
                       in blocked/var tr′ H~ })
                (wait⇒skip P (v X) _ w)))
      ... | no ¬w = no λ td → ¬w (varSub td)

      -- s/rec
      alg? Γ Δ P (rec Pr) s with messageGuarded? Pr
      ... | no ¬guarded = no λ td → ¬guarded (recGuard td)
      ... | yes guarded
        with WaitCheck.wait? G wb P _
               (reach₀? P (λ W → Alg Γ (W ∷ Δ) (P ◂ Pr) W)
                          (λ W → alg? Γ (W ∷ Δ) P Pr W)) s
      ...   | yes w =
        yes (a/skip
              (skip/map (λ { (_ , td , tr) → blocked/rec tr guarded td })
                (wait⇒skip P (rec Pr) _ w)))
      ...   | no ¬w = no λ td → ¬w (recSub td)

      -- `s/send`'s leaf family at one state.  At most one target, by
      -- `step-deterministic`, so a failure at the one found is a failure.
      sendLeaf? :
        ∀ {γ δ I}
          (Γ : Vec Sort γ)(Δ : Vec (State G) δ)
          (P Q : Part)(i : Fin (suc I))(S : Sort)(Pr : Proc γ δ)
          (u : State G)
        → Dec (∃[ u′ ] (u -< P ⟶ Q # i < S > >-> u′) × Alg Γ Δ (P ◂ Pr) u′)

      sendLeaf? Γ Δ P Q i S Pr u with findStep u (P ⟶ Q # i < S >)
      ... | no ¬st = no λ { (u′ , gr , _) → ¬st (u′ , gr) }
      ... | yes (u′ , gr) with alg? Γ Δ P Pr u′
      ...   | yes td = yes (u′ , gr , td)
      ...   | no ¬td =
        no λ { (u″ , gr″ , td″) →
                 ¬td (subst (Alg Γ Δ (P ◂ Pr)) (step-deterministic gr″ gr) td″) }

      -- `s/recv`'s leaf family at one state: one offered edge, and every
      -- offered edge's continuation typed.  A label the state does not offer
      -- imposes nothing — that is exactly `blocked/recv`.
      recvLeaf? :
        ∀ {γ δ I}
          (Γ : Vec Sort γ)(Δ : Vec (State G) δ)
          (P Q : Part)(Br : Vec (Proc (suc γ) δ) (suc I))
          (u : State G)
        → Dec ((Σ[ j ∈ Fin (suc I) ] ∃[ U ] ∃[ t ] (u -< Q ⟶ P # j < U > >-> t))
               × (∀ {j U t} → u -< Q ⟶ P # j < U > >-> t
                            → Alg (U ∷ Γ) Δ (P ◂ lookup Br j) t))

      recvLeaf? {I = I} Γ Δ P Q Br u
        with findRecv Q P I (edges G u)
      ... | no ¬found =
        no λ { ((j , U , t , gr) , _) →
                 ¬found (j , U , t , step⇒listed {G = G} gr) }
      ... | yes (j₀ , U₀ , t₀ , mem₀) with contsOK? Γ Δ P Q Br u
      ...   | yes conts =
        yes ((j₀ , U₀ , t₀ , listed⇒step {G = G} mem₀) , conts)
      ...   | no ¬conts = no λ { (_ , conts) → ¬conts conts }

      contsOK? :
        ∀ {γ δ I}
          (Γ : Vec Sort γ)(Δ : Vec (State G) δ)
          (P Q : Part)(Br : Vec (Proc (suc γ) δ) (suc I))
          (u : State G)
        → Dec (∀ {j U t} → u -< Q ⟶ P # j < U > >-> t
                         → Alg (U ∷ Γ) Δ (P ◂ lookup Br j) t)

      contsOK? {I = I} Γ Δ P Q Br u
        with All.all? (λ e → edgeOK? Γ Δ P Q Br e) (edges G u)
      ... | yes every =
        yes λ gr → All.lookup every (step⇒listed {G = G} gr) refl
      ... | no ¬every =
        no λ conts →
          ¬every (All.tabulate λ {e} mem eq →
                    conts (subst (λ α → u -< α >-> proj₂ e)
                            eq (listed⇒step {G = G} mem)))

      edgeOK? :
        ∀ {γ δ I}
          (Γ : Vec Sort γ)(Δ : Vec (State G) δ)
          (P Q : Part)(Br : Vec (Proc (suc γ) δ) (suc I))
          (e : Edge (size G))
        → Dec (EdgeOK Γ Δ P Q Br e)

      edgeOK? {I = I} Γ Δ P Q Br (α , t) with matchRecv? Q P I α
      ... | no ¬match =
        yes λ { {j}{U} eq → ⊥-elim (¬match (j , U , eq)) }
      ... | yes (j , U , refl) with algBr Γ Δ P Br j t
      ...   | yes td = yes λ { refl → td }
      ...   | no ¬td = no λ f → ¬td (f refl)

      -- Makes `lookup Br j` structural, as in `SetsAlg.agda`.
      algBr :
        ∀ {γ δ n}
          (Γ : Vec Sort γ)(Δ : Vec (State G) δ)
          (P : Part)(Br : Vec (Proc (suc γ) δ) n)(j : Fin n){U}(t : State G)
        → Dec (Alg (U ∷ Γ) Δ (P ◂ lookup Br j) t)

      algBr Γ Δ P (B ∷ Bs) fzero     {U} t = alg? (U ∷ Γ) Δ P B t
      algBr Γ Δ P (B ∷ Bs) (fsuc j)  {U} t = algBr Γ Δ P Bs j t

    -- ══════════════════════════════════════════════════════════════════
    --  Public entry points
    -- ══════════════════════════════════════════════════════════════════
    --
    -- `alg` is the set-based decision; `tc?` lifts it to the declarative
    -- judgment through the round trip, which is proved on both sides
    -- (`alg/typing` out, `norm` in).  There is deliberately no bespoke
    -- completeness argument for `⊢p` here.

    alg :
      ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
        (P : Part) (Pr : Proc γ δ) (s : State G)
      → Dec (Γ & Δ ⊢a P ◂ Pr ∶ s)
    alg = alg?

    tc? :
      ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
        (P : Part) (Pr : Proc γ δ) (s : State G)
      → Dec (Γ & Δ ⊢p P ◂ Pr ∶ s)
    tc? Γ Δ P Pr s =
      map′ alg/typing (λ td → NM.norm td skip/refl) (alg Γ Δ P Pr s)

    tcSession? : (M : Session) (s : State G) → Dec (⊢s M ∶ s)
    tcSession? M s = FinP.all? (λ P → tc? [] [] P (M [ P ]s) s)
