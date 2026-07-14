{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Data.Product using (∃-syntax; _,_; proj₁; proj₂)
open import Function using (_∘_)

open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality using (_≡_)

module Definitions.Typing where

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
        {S  : Vec Sort (suc I)}
        {Br : Vec (Proc (suc γ) δ) (suc I)}
      → MessageGuarded (Σ P ？[ S ]· Br)

    mg/if :
      ∀ {E : Exp γ}
        {Pr Pr' : Proc γ δ}
      → MessageGuarded Pr
      → MessageGuarded Pr'
      → MessageGuarded (ifp E then Pr else Pr')

  infix  4 _&_⊢p_∶_
  infix  4 _&_⊢skip[_]_∶_

  data Mode : Set where
    prod nonprod : Mode

  data _&_⊢skip[_]_∶_
    (Leaf : NProc γ δ → Behav → Set)
    (Ξ : Vec Behav ξ)
    : Mode → NProc γ δ → Behav → Set
    where

   skip/main :
     ∀ {PPr G}
     → Leaf PPr G
     → Leaf & Ξ ⊢skip[ prod ] PPr ∶ G

   skip/step :
     ∀ {P Pr α G G'}
     → (gr : G -< α >-> G')
     → (na : P not-active-in G)
     → (ktd :
         ∀ {G″ β}
         → (gr′ : G -< β >-> G″)
         → ∃[ m ] Leaf & G ∷ Ξ ⊢skip[ m ] P ◂ Pr ∶ G″)
     → proj₁ (ktd gr) ≡ prod
     → Leaf & Ξ ⊢skip[ prod ] P ◂ Pr ∶ G

   skip/cycle :
     ∀ {P Pr X G}
     → lu Ξ X ~ G
     → Leaf & Ξ ⊢skip[ nonprod ] P ◂ Pr ∶ G

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
       {S  : Vec Sort (suc I)}
       {Br : Vec (Proc (suc γ) δ) (suc I)}
     → (gr : G -< P ⟶ Q # i < T > >-> G')
     → (conts :
         ∀ {j U G″}
         → (gr′ : G -< P ⟶ Q # j < U > >-> G″)
         → (U ∷ Γ) & Δ ⊢p Q ◂ lu Br j ∶ G″)
     → Γ & Δ ⊢p Q ◂ Σ P ？[ S ]· Br ∶ G

   t/skip :
     ∀ {PPr G}
     → (Γ & Δ ⊢p_∶_) & [] ⊢skip[ prod ] PPr ∶ G
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

  infix 4 _&_&_⊢skip[_]_∶_

  _&_&_⊢skip[_]_∶_ :
    ∀ (Γ : Vec Sort γ)
      (Δ : Vec Behav δ)
      (Ξ : Vec Behav ξ)
    → Mode
    → NProc γ δ
    → Behav
    → Set
  Γ & Δ & Ξ ⊢skip[ m ] PPr ∶ G =
    ((_&_⊢p_∶_) Γ Δ) & Ξ ⊢skip[ m ] PPr ∶ G

  infix 4 _⊢head_∶_

  data _⊢head_∶_ {γ}
    (Γ : Vec Sort γ)
    : NProc γ 0 → Behav → Set
    where

    h/send :
      ∀ {P Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {E : Exp γ}
        {Pr : Proc γ 0}
        {G G′ : Behav}
      → G -< P ⟶ Q # i < S > >-> G′
      → Γ ⊢e E ∶ S
      → Γ ⊢head P ◂ Pr ∶ G′
      → Γ ⊢head P ◂ Q ! i < E >∙ Pr ∶ G

    h/recv :
      ∀ {P Q I}
        {i : Fin (suc I)}
        {T : Sort}
        {S : Vec Sort (suc I)}
        {Br : Vec (Proc (suc γ) 0) (suc I)}
        {G G′ : Behav}
      → G -< Q ⟶ P # i < T > >-> G′
      → (∀ {j U G″}
          → G -< Q ⟶ P # j < U > >-> G″
          → (U ∷ Γ) ⊢head P ◂ lu Br j ∶ G″)
      → Γ ⊢head P ◂ Σ Q ？[ S ]· Br ∶ G

    h/skip :
      ∀ {PPr G}
      → ((_⊢head_∶_) Γ) & [] ⊢skip[ prod ] PPr ∶ G
      → Γ ⊢head PPr ∶ G

    h/if :
      ∀ {P}
        {E : Exp γ}
        {Pr Pr′ : Proc γ 0}
        {G : Behav}
      → Γ ⊢e E ∶ s/bool
      → Γ ⊢head P ◂ Pr ∶ G
      → Γ ⊢head P ◂ Pr′ ∶ G
      → Γ ⊢head P ◂ ifp E then Pr else Pr′ ∶ G

    h/rec :
      ∀ {P}
        {Pr : Proc γ 1}
        {G G′ : Behav}
      → G -[¬ P ]->* G′
      → MessageGuarded Pr
      → Γ & G ∷ [] ⊢p P ◂ Pr ∶ G
      → Γ ⊢head P ◂ rec Pr ∶ G′

    h/end :
      ∀ {P}
        {G : Behav}
      → ¬ P ∈T G
      → Γ ⊢head P ◂ ∅ ∶ G

  infix  4 _&_⊢hskip[_]_∶_

  _&_⊢hskip[_]_∶_ :
    ∀ {γ ξ}
      (Γ : Vec Sort γ)
      (Ξ : Vec Behav ξ)
    → Mode
    → NProc γ 0
    → Behav
    → Set
  Γ & Ξ ⊢hskip[ m ] PPr ∶ G =
    ((_⊢head_∶_) Γ) & Ξ ⊢skip[ m ] PPr ∶ G

  mutual
    head/typing :
      ∀ {γ P Pr G}
        {Γ : Vec Sort γ}
      → Γ ⊢head P ◂ Pr ∶ G
      → Γ & [] ⊢p P ◂ Pr ∶ G
    head/typing (h/send gr etd td) =
      t/send gr etd (head/typing td)
    head/typing (h/recv gr conts) =
      t/recv gr (head/typing ∘ conts)
    head/typing (h/skip std) =
      t/skip (hskip/typing std)
    head/typing (h/if etd head₁ head₂) =
      t/if etd (head/typing head₁) (head/typing head₂)
    head/typing (h/rec tr guarded td) =
      t/unskip tr (t/rec guarded td)
    head/typing (h/end done) =
      t/end done

    hskip/typing :
      ∀ {γ ξ P Pr G m}
        {Γ : Vec Sort γ}
        {Ξ : Vec Behav ξ}
      → Γ & Ξ ⊢hskip[ m ] P ◂ Pr ∶ G
      → Γ & [] & Ξ ⊢skip[ m ] P ◂ Pr ∶ G
    hskip/typing (skip/main td) =
      skip/main (head/typing td)
    hskip/typing (skip/step gr na ktd mode-gr) =
      skip/step gr na
        (λ gr′ →
          let mode′ , std′ = ktd gr′
          in mode′ , hskip/typing std′)
        mode-gr
    hskip/typing (skip/cycle x) =
      skip/cycle x

  data MainLeaf
    {γ δ ξ : ℕ}
    {Γ : Vec Sort γ}
    {Δ : Vec Behav δ}
    {Ξ : Vec Behav ξ}
    : ∀ {m PPr G PPr′ G′}
    → Γ & Δ ⊢p PPr′ ∶ G′
    → Γ & Δ & Ξ ⊢skip[ m ] PPr ∶ G
    → Set
    where

    main/here :
      ∀ {PPr G}
        {td : Γ & Δ ⊢p PPr ∶ G}
      → MainLeaf td (skip/main td)

    main/step :
      ∀ {P Pr α G G′}
        {gr : G -< α >-> G′}
        {na : P not-active-in G}
        {ktd :
          ∀ {G″ β}
          → (gr′ : G -< β >-> G″)
          → ∃[ m ] Γ & Δ & G ∷ Ξ ⊢skip[ m ] P ◂ Pr ∶ G″}
        {ok : proj₁ (ktd gr) ≡ prod}
        {PPr′ G″}
        {td : Γ & Δ ⊢p PPr′ ∶ G″}
        {β H}
      → (gr′ : G -< β >-> H)
      → MainLeaf {Ξ = G ∷ Ξ} td (proj₂ (ktd gr′))
      → MainLeaf td (skip/step gr na ktd ok)

  ⊢s_∶_ : Session → Behav → Set
  ⊢s M ∶ G = ∀ P → [] & [] ⊢p P ◂ (M [ P ]s) ∶ G
