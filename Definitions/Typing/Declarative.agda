{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Function using (_∘_)

open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality using (_≡_)

module Definitions.Typing.Declarative where

open import Definitions.Expr public
open import Definitions.Guard public
open import Definitions.Behav public

-- Processes
module MPST {N : ℕ} {B : BTheory N} (wb : WellBehaved B) where

  open BTheory B public
  open WellBehaved wb public

  open import Definitions.Common  N public
  open import Definitions.Proc    N public
  open import Definitions.Actions N public

  open Subst
  open Action
  open Comm
  open Choice

  private
    variable
      γ δ ξ : ℕ

  data MessageGuarded : Proc γ δ → Set where
    mg/send :
      ∀ {Q I}
        {i  : Fin (suc I)}
        {E  : Exp γ}
        {Pr : Proc γ δ}
      → MessageGuarded (Q ! i < E >∙ Pr)

    mg/recv :
      ∀ {P I}
        {Br : Vec (Proc (suc γ) δ) (suc I)}
      → MessageGuarded (Σ P ？· Br)

    mg/if :
      ∀ {E : Exp γ}
        {Pr Pr' : Proc γ δ}
      → MessageGuarded Pr
      → MessageGuarded Pr'
      → MessageGuarded (ifp E then Pr else Pr')

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

   t/send :
     ∀ {P Q I}
       {i  : Fin (suc I)}
       {G G' : Behav}
       {Pr : Proc γ δ}
       {E  : Exp γ}
       {S  : Sort}
     → (gr  : G -< P ⟶ Q # i < S > >-> G')
     → (etd : Γ ⊢e E ∶ S)
     → (td  : Γ & Δ ⊢p P ◂ Pr ∶ G')
     → Γ & Δ ⊢p P ◂ Q ! i < E >∙ Pr ∶ G

   t/recv :
     ∀ {P Q I}
       {i  : Fin (suc I)}
       {T  : Sort}
       {G G' : Behav}
       {Br : Vec (Proc (suc γ) δ) (suc I)}
     → (gr : G -< P ⟶ Q # i < T > >-> G')
     → (conts :
         ∀ {j U G″}
         → (gr′ : G -< P ⟶ Q # j < U > >-> G″)
         → (U ∷ Γ) & Δ ⊢p Q ◂ lu Br j ∶ G″)
     → Γ & Δ ⊢p Q ◂ Σ P ？· Br ∶ G

   t/skip :
     ∀ {PPr G}
     → (Γ & Δ ⊢p_∶_) & [] ⊢skip PPr ∶ G
     → Γ & Δ ⊢p PPr ∶ G

   t/unskip :
     ∀ {P Pr G G'}
     → (tr : G -[¬ P ]->* G')
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
     -- TODO: I believe this is the key for NOT requiring backwards
     -- bisimilarity. Something more strict than arbitrary "~" (e.g. "common
     -- history" property and bisimilar?)
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

  data MainLeaf
    {ξ : ℕ}
    {Ξ : Vec Behav ξ}
    {Leaf : NProc δ γ → Behav → Set}
    : ∀ {PPr G PPr′ G′}
    → Leaf PPr′ G′
    → Leaf & Ξ ⊢skip PPr ∶ G
    → Set
    where

    main/here :
      ∀ {PPr G} {td : Leaf PPr G}
      → MainLeaf td (skip/main td)

    main/step :
      ∀ {P Pr α G G′}
        {gr : G -< α >-> G′}
        {na : P not-active-in G}
        {ktd :
          ∀ {G″ β}
          → (gr′ : G -< β >-> G″)
          → Leaf & G ∷ Ξ ⊢skip P ◂ Pr ∶ G″}
        {PPr′ G″}
        {td : Leaf PPr′ G″}
        {β H}
      → (gr′ : G -< β >-> H)
      → MainLeaf {Ξ = G ∷ Ξ} td (ktd gr′)
      → MainLeaf td (skip/step gr na ktd)

  ⊢s_∶_ : Session → Behav → Set
  ⊢s M ∶ G = ∀ P → [] & [] ⊢p P ◂ (M [ P ]s) ∶ G
