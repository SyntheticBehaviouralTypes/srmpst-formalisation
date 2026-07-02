{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Data.Product using (∃-syntax; proj₁; proj₂)

open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality using (_≡_)

module Definitions where

open import Definitions.Expr public
open import Definitions.Guard public
open import Definitions.Behav public

-- Processes
module MPST {N : ℕ} {B : BTheory N} (BP : BT-Prop B) where

  open BTheory B public
  open BT-Prop BP public

  open import Definitions.Common  N public
  open import Definitions.Proc    N public
  open import Definitions.Actions N public

  open Subst
  open Action
  open Comm
  open Choice
  open _~_

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
     ∀ {P Pr α G G'}
     → (gr : G -< α >-> G')
     → (na : P not-active-in G)
     → (ktd :
         ∀ {G″ β}
         → (gr′ : G -< β >-> G″)
         → ∃[ m ] (Γ & Δ ⊢p_∶_) & G ∷ [] ⊢skip[ m ] P ◂ Pr ∶ G″)
     → proj₁ (ktd gr) ≡ prod
     → Γ & Δ ⊢p P ◂ Pr ∶ G

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

  infix 4 _⊏td_

  data _⊏td_
    : ∀ {γ₀ δ₀ γ₁ δ₁}
        {Γ₀ : Vec Sort γ₀}
        {Δ₀ : Vec Behav δ₀}
        {Γ₁ : Vec Sort γ₁}
        {Δ₁ : Vec Behav δ₁}
        {PPr₀ : NProc γ₀ δ₀}
        {PPr₁ : NProc γ₁ δ₁}
        {G₀ G₁ : Behav}
    → Γ₁ & Δ₁ ⊢p PPr₁ ∶ G₁
    → Γ₀ & Δ₀ ⊢p PPr₀ ∶ G₀
    → Set
    where

    sub/send :
      ∀ {γ δ P Q I}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {i  : Fin (suc I)}
        {G G′ : Behav}
        {Pr : Proc γ δ}
        {E  : Exp γ}
        {S  : Sort}
        {gr  : G -< P ⟶ Q # i < S > >-> G′}
        {etd : Γ ⊢e E ∶ S}
        {td  : Γ & Δ ⊢p P ◂ Pr ∶ G′}
      → td ⊏td t/send gr etd td

    sub/recv :
      ∀ {γ δ P Q I}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {i  : Fin (suc I)}
        {T  : Sort}
        {G G′ : Behav}
        {S  : Vec Sort (suc I)}
        {Br : Vec (Proc (suc γ) δ) (suc I)}
        {gr : G -< P ⟶ Q # i < T > >-> G′}
        {conts :
          ∀ {j U G″}
          → (gr′ : G -< P ⟶ Q # j < U > >-> G″)
          → (U ∷ Γ) & Δ ⊢p Q ◂ lu Br j ∶ G″}
        {j U G″}
      → (gr′ : G -< P ⟶ Q # j < U > >-> G″)
      → conts gr′ ⊏td t/recv {S = S} {Br = Br} gr conts

    sub/skip :
      ∀ {γ δ P Pr α G G′}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {gr : G -< α >-> G′}
        {na : P not-active-in G}
        {ktd :
          ∀ {G″ β}
          → (gr′ : G -< β >-> G″)
          → ∃[ m ] Γ & Δ & G ∷ [] ⊢skip[ m ] P ◂ Pr ∶ G″}
        {ok : proj₁ (ktd gr) ≡ prod}
        {PPr′ G″}
        {td : Γ & Δ ⊢p PPr′ ∶ G″}
        {β H}
      → (gr′ : G -< β >-> H)
      → MainLeaf {Ξ = G ∷ []} td (proj₂ (ktd gr′))
      → td ⊏td t/skip gr na ktd ok

    sub/unskip :
      ∀ {γ δ P Pr G G′}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {tr : G -[¬ P ]->* G′}
        {td : Γ & Δ ⊢p P ◂ Pr ∶ G}
      → td ⊏td t/unskip tr td

    sub/if-then :
      ∀ {γ δ P E Pr Pr′ G}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {etd : Γ ⊢e E ∶ s/bool}
        {ttd : Γ & Δ ⊢p P ◂ Pr ∶ G}
        {ftd : Γ & Δ ⊢p P ◂ Pr′ ∶ G}
      → ttd ⊏td t/if etd ttd ftd

    sub/if-else :
      ∀ {γ δ P E Pr Pr′ G}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {etd : Γ ⊢e E ∶ s/bool}
        {ttd : Γ & Δ ⊢p P ◂ Pr ∶ G}
        {ftd : Γ & Δ ⊢p P ◂ Pr′ ∶ G}
      → ftd ⊏td t/if etd ttd ftd

    sub/rec :
      ∀ {γ δ P Pr G}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {mg : MessageGuarded Pr}
        {td : Γ & G ∷ Δ ⊢p P ◂ Pr ∶ G}
      → td ⊏td t/rec mg td

  data AccTd
    : ∀ {γ δ}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {PPr : NProc γ δ}
        {G : Behav}
    → Γ & Δ ⊢p PPr ∶ G
    → Set
    where

    acc/td :
      ∀ {γ δ}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {PPr : NProc γ δ}
        {G : Behav}
        {td : Γ & Δ ⊢p PPr ∶ G}
      → (∀ {γ′ δ′}
            {Γ′ : Vec Sort γ′}
            {Δ′ : Vec Behav δ′}
            {PPr′ : NProc γ′ δ′}
            {G′ : Behav}
            {td′ : Γ′ & Δ′ ⊢p PPr′ ∶ G′}
         → td′ ⊏td td
         → AccTd td′)
      → AccTd td

  mutual

    acc-td :
      ∀ {γ δ PPr G}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
      → (td : Γ & Δ ⊢p PPr ∶ G)
      → AccTd td

    acc-td (t/send _ _ td) =
      acc/td λ { sub/send → acc-td td }

    acc-td (t/recv _ conts) =
      acc/td λ { (sub/recv gr′) → acc-td (conts gr′) }

    acc-td (t/skip _ _ ktd _) =
      acc/td λ { (sub/skip gr′ leaf) → acc-skip (proj₂ (ktd gr′)) leaf }

    acc-td (t/unskip _ td) =
      acc/td λ { sub/unskip → acc-td td }

    acc-td (t/if _ ttd ftd) =
      acc/td λ
        { sub/if-then → acc-td ttd
        ; sub/if-else → acc-td ftd
        }

    acc-td (t/rec _ td) =
      acc/td λ { sub/rec → acc-td td }

    acc-td (t/var _) =
      acc/td λ ()

    acc-td (t/end _) =
      acc/td λ ()


    acc-skip :
      ∀ {γ δ ξ m PPr G PPr′ G′}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {Ξ : Vec Behav ξ}
        {td : Γ & Δ ⊢p PPr′ ∶ G′}
      → (std : Γ & Δ & Ξ ⊢skip[ m ] PPr ∶ G)
      → MainLeaf td std
      → AccTd td

    acc-skip (skip/main td) main/here =
      acc-td td

    acc-skip (skip/step _ _ ktd _) (main/step gr′ leaf) =
      acc-skip (proj₂ (ktd gr′)) leaf

  ⊢s_∶_ : Session → Behav → Set
  ⊢s M ∶ G = ∀ P → [] & [] ⊢p P ◂ (M [ P ]s) ∶ G
