{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (_∈_)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Relation.Nullary using (¬_)

open import Data.Product using (Σ-syntax)

open import Definitions.Proc using (Assignment)

module Definitions.Typing.Declarative where

open import Definitions.Expr public
open import Definitions.Behav public

-- Processes
module MPST {N : ℕ} {B : BTheory N} (wb : WellBehaved B) where

  open BTheory B public
  open WellBehaved wb public

  open import Definitions.Common  N public
  open import Definitions.Proc    N public
  open import Definitions.Actions N public

  open Subst
  open Choice

  private
    variable
      γ δ ξ : ℕ

  infix  4 _&_⊢p_∶_
  infix  4 _&_⊢skip_∶_

  data _&_⊢skip_∶_
    (Leaf : NProc γ δ → Behav → Set)
    (Ξ : Vec Behav ξ)
    : NProc γ δ → Behav → Set
    where

   skip/main :
     ∀ {PPr G}
     → Leaf PPr G
     → Leaf & Ξ ⊢skip PPr ∶ G

   skip/step :
     ∀ {P Pr α G G'}
     → (gr : G -< α >-> G')
     → (na : P not-active-in G)
     → (ktd :
         ∀ {G″ β}
         → (gr′ : G -< β >-> G″)
         → Leaf & G ∷ Ξ ⊢skip P ◂ Pr ∶ G″)
     → Leaf & Ξ ⊢skip P ◂ Pr ∶ G

   skip/cycle :
     ∀ {P Pr X G}
     → lu Ξ X ~ G
     → P ∈T G
     → Leaf & Ξ ⊢skip P ◂ Pr ∶ G

  data _&_⊢p_∶_
   (Γ : Vec Sort γ)
   (Δ : Vec Behav δ)
   : NProc γ δ → Behav → Set
   where

   -- The annotated role acts, and it is one of the process's roles.
   t/send :
     ∀ {P Q Qs I}
       {i  : Fin (suc I)}
       {G G' : Behav}
       {Pr : Proc γ δ}
       {E  : Exp γ}
       {S  : Sort}
     → (Q∈  : Q ∈ P)
     → (foc : Focus P Q G)
     → (gr  : G -<[ Q ↦ (! Qs) # i < S > ]>-> G')
     → (etd : Γ ⊢e E ∶ S)
     → (td  : Γ & Δ ⊢p P ◂ Pr ∶ G')
     → Γ & Δ ⊢p P ◂ Q ⇒ Qs ! i < E >∙ Pr ∶ G

   t/recv :
     ∀ {P Q R I}
       {i  : Fin (suc I)}
       {T  : Sort}
       {G G' : Behav}
       {Br : Vec (Proc (suc γ) δ) (suc I)}
     → (R∈  : R ∈ Q)
     → (foc : Focus Q R G)
     → (gr  : G -<[ Q ∣ R ↦ (？ P) # i < T > ]>-> G')
     → (conts :
         ∀ {j U G″}
         → (gr′ : G -<[ Q ∣ R ↦ (？ P) # j < U > ]>-> G″)
         → (U ∷ Γ) & Δ ⊢p Q ◂ lu Br j ∶ G″)
     → Γ & Δ ⊢p Q ◂ R ⇐ P ？· Br ∶ G

   t/skip :
     ∀ {PPr G}
     → (Γ & Δ ⊢p_∶_) & [] ⊢skip PPr ∶ G
     → Γ & Δ ⊢p PPr ∶ G

   -- The run's end only up to `~`.
   t/unskip :
     ∀ {P Pr G G″ G'}
     → (tr : G -[¬ P ]->* G″)
     → (eq : G″ ~ G')
     → (td : Γ & Δ ⊢p P ◂ Pr ∶ G)
     → Γ & Δ ⊢p P ◂ Pr ∶ G'

   t/if :
     ∀ {P E Pr Pr' G}
     → (etd : Γ ⊢e E ∶ s/bool)
     → (ttd : Γ & Δ ⊢p P ◂ Pr ∶ G)
     → (ftd : Γ & Δ ⊢p P ◂ Pr' ∶ G)
     → Γ & Δ ⊢p P ◂ ifp E then Pr else Pr' ∶ G

   t/rec :
     ∀ {P Pr G}
     → (mg : MessageGuarded Pr)
     → (td : Γ & G ∷ Δ ⊢p P ◂ Pr ∶ G)
     → Γ & Δ ⊢p P ◂ rec Pr ∶ G

   t/var :
     ∀ {P X G}
     → (eq : lu Δ X ~ G)
     → Γ & Δ ⊢p P ◂ v X ∶ G

   t/end :
     ∀ {P G}
     → (done : ¬ P ∈T G)
     → Γ & Δ ⊢p P ◂ ∅ ∶ G

  infix 4 _&_&_⊢skip_∶_

  _&_&_⊢skip_∶_ :
    ∀ (Γ : Vec Sort γ)
      (Δ : Vec Behav δ)
      (Ξ : Vec Behav ξ)
    → NProc γ δ
    → Behav
    → Set
  Γ & Δ & Ξ ⊢skip PPr ∶ G =
    (Γ & Δ ⊢p_∶_) & Ξ ⊢skip PPr ∶ G

-- Sessions: one process per block, each typed against its block's local
-- view and carrying that view's `WellBehaved`.
module Sessions {N : ℕ} (B : BTheory N) where

  open import Definitions.Common N using (PartSet)
  open import Definitions.Proc N using (Proc; module Over; _◂_)
  open import Definitions.View B using (view)
  open BTheory B using (Behav)

  infix 4 ⊢ᵛ[_]_∶_ ⊢s[_]_∶_

  -- The process `Pr` of role set `Ps`, typed against `Ps`'s view.
  ⊢ᵛ[_]_∶_ : PartSet → Proc 0 0 → Behav → Set₁
  ⊢ᵛ[ Ps ] Pr ∶ G =
    Σ[ wb ∈ WellBehaved (view Ps) ] MPST._&_⊢p_∶_ wb [] [] (Ps ◂ Pr) G

  -- Every process of the session, at its block.
  ⊢s[_]_∶_ : ∀ {K} (Ρ : Assignment N K) → Over.Session Ρ → Behav → Set₁
  ⊢s[ Ρ ] M ∶ G = ∀ j → ⊢ᵛ[ lu (Assignment.roles Ρ) j ] lu M j ∶ G
