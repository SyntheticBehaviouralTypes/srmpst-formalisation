{-# OPTIONS --guardedness #-}
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
  renaming (_≟_ to _≟f_)
open import Data.Nat using (ℕ ; zero; suc)
  renaming (_+_ to _+ℕ_)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec ; []; _∷_; lookup ; map; tabulate; _[_]≔_)
open import Data.Vec.Properties using (lookup-map; lookup∘update;
  lookup∘update′; lookup∘tabulate)
open import Function  using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong;
  cong₂; sym; subst)
open import Relation.Nullary using (Dec; ¬_; ¬?; yes; no; contraposition)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)

open import Definitions.Guard
open import Definitions.Expr
open import Definitions.Behav

module Definitions.Types (N : ℕ) where
  open import Definitions.Common(N)
  open import Definitions.Actions(N)

  module PreTypes where
    -- Global Types
    mutual
      data Global (δ : ℕ) : Guard → Set where
        end : Global δ ng
        μ : Global (suc δ) mg → Global δ ng
        var : Fin δ → Global δ ng
        _⟶_∶[_,_]_ :
          (P : Part) → (Q : Part) → (I : ℕ) →
          (pnq : False (P ≟f Q)) → Vec (Choice δ) (suc I) → Global δ mg
        >> : Global δ mg → Global δ ng

      record Choice (δ : ℕ) : Set where
        inductive
        constructor _··_
        field
          sort : Sort
          continuation : Global δ ng

    ch/sorts : ∀ {I n} → Vec (Choice n) I → Vec Sort I
    ch/sorts = Data.Vec.map Choice.sort

    _[_]sort : ∀{I n} → Vec (Choice n) I → Fin I → Sort
    Chs [ n ]sort = (lookup Chs n).Choice.sort

    _[_]cont : ∀{I δ} → Vec (Choice δ) I → Fin I → Global δ ng
    Chs [ n ]cont = (lookup Chs n).Choice.continuation

    lu/ch/sorts : ∀ {I n} i (Chs :  Vec (Choice n) I)
      → lookup (ch/sorts Chs) i ≡ Chs [ i ]sort
    lu/ch/sorts i = lookup-map i Choice.sort

    map/branch : ∀ {δ δ'}
      → (f : Global δ ng → Global δ' ng) → Choice δ → Choice δ'
    map/branch f (S ·· G) = S ·· f G

    map/choice : ∀ {δ δ' I}
      → (f : Global δ ng → Global δ' ng) → Vec (Choice δ) I → Vec (Choice δ') I
    map/choice f = map (map/branch f)

        -- P is a participant in G
    mutual
      data _∈G_ {δ} (P : Part) : {g : Guard} → Global δ g →  Set where
        in/mu : ∀{G} → P ∈G G → P ∈G (μ G)
        in/msg/send : ∀{Q pnq I Chs} → P ∈G (P ⟶ Q ∶[ I , pnq ] Chs)
        in/msg/recv : ∀{Q pnq I Chs} → P ∈G (Q ⟶ P ∶[ I , pnq ] Chs)
        in/msg/cont/i : ∀{P' Q' p'nq' I Chs} → (i : Fin (suc I)) →
          P ∈Ch lookup Chs i → P ∈G (P' ⟶ Q' ∶[ I , p'nq' ] Chs)
        in/>> : ∀{G} → P ∈G G → P ∈G (>> G)

      data _∈Ch_ {δ} (P : Part) : Choice δ →  Set where
        in/ch : ∀{S G} → P ∈G G →  P ∈Ch (S ·· G)

    inv/in/mu : ∀{P δ} {G : Global (suc δ) mg} → P ∈G μ G → P ∈G G
    inv/in/mu (in/mu prf) = prf

    inv/in/>> : ∀{P δ} {G : Global δ mg} → P ∈G >> G → P ∈G G
    inv/in/>> (in/>> prf) = prf

    inv/in/ch : ∀{P δ S} {G : Global δ ng} → P ∈Ch (S ·· G) → P ∈G G
    inv/in/ch (in/ch prf) = prf

    not-hd-not-cont : ∀{P  P' Q p'nq I δ}{Chs : Vec (Choice δ) (suc I)}
      → P ≢ P' → P ≢ Q → (∀ i → ¬ (P ∈Ch lookup Chs i))
      → ¬ P ∈G (P' ⟶ Q ∶[ I , p'nq ] Chs)
    not-hd-not-cont P≢P' P≢Q P∉Chs in/msg/send = P≢P' refl
    not-hd-not-cont P≢P' P≢Q P∉Chs in/msg/recv = P≢Q refl
    not-hd-not-cont P≢P' P≢Q P∉Chs (in/msg/cont/i i x) = P∉Chs i x

    mutual
      _∈G?_ : ∀ {δ g} → (P : Part) → (G : Global δ g)  → Dec (P ∈G G)
      P ∈G? end = no λ ()
      P ∈G? μ G with P ∈G? G
      ... | yes p∈GG = yes (in/mu p∈GG)
      ... | no eq = no (λ prf → eq (inv/in/mu prf))
      P ∈G? var x = no (λ ())
      P ∈G? (P' ⟶ Q ∶[ I , _ ] Chs) with P ≟f P' | P ≟f Q
      ... | yes refl | _ = yes in/msg/send
      ... | _ | yes refl = yes in/msg/recv
      ... | no P≢P' | no P≢Q with is-part-in-choice P Chs
      ... | inj₁ (i , eq) = yes (in/msg/cont/i i eq)
      ... | inj₂ f = no (not-hd-not-cont P≢P' P≢Q f)
      P ∈G? >> G with P ∈G? G
      ... | yes eq = yes (in/>> eq)
      ... | no eq = no (λ prf → eq (inv/in/>> prf))

      _∈Ch?_ : ∀ {δ} → (P : Part) → (Ch : Choice δ)  → Dec (P ∈Ch Ch)
      P ∈Ch? (S ·· G) with P ∈G? G
      ... | yes eq = yes (in/ch eq)
      ... | no eq = no λ prf → eq (inv/in/ch prf)

      is-part-in-choice : ∀ {δ I : ℕ} P (Chs : Vec (Choice δ) I)
        → (∃[ i ] P ∈Ch lookup Chs i) ⊎ (∀ i → ¬ P ∈Ch lookup Chs i)
      is-part-in-choice P [] = inj₂ λ ()
      is-part-in-choice P (C ∷ Chs) with P ∈Ch? C | is-part-in-choice P Chs
      ... | yes eq | _ = inj₁ (zero , eq)
      ... | no _ | inj₁ (i , eq) = inj₁ (suc i , eq)
      ... | no nC  | inj₂ nChs = inj₂ (λ{ zero → nC ; (suc i) → nChs i})

    ing : ∀{δ g} → Global δ g → Global δ ng
    ing {g = mg} G = >> G
    ing {g = ng} G = G

    ext : ∀ {δ δ'} → (rn : Fin δ → Fin δ') → Fin (suc δ) → Fin (suc δ')
    ext ρ zero = zero
    ext ρ (suc i) = suc (ρ i)

    -- a simultaneous renaming from δ to δ' vars (var for var)
    ren : (δ δ' : ℕ) -> Set
    ren δ δ' = Fin δ -> Fin δ'

    -- A variable renaming in global types
    mutual
      rename : ∀ {δ δ' g} → (ρ : ren δ δ') → Global δ g → Global δ' g
      rename ρ end = end
      rename ρ (μ g) = μ (rename (ext ρ) g)
      rename ρ (var x) = var (ρ x)
      rename ρ (P ⟶ Q ∶[ I , x ] Ch) = P ⟶ Q ∶[ I , x ] rename/choice ρ Ch
      rename ρ (>> g) = >> (rename ρ g)

      rename/choice : ∀ {δ δ' I}
        → (ρ : ren δ δ')
        → Vec (Choice δ) I → Vec (Choice δ') I
      rename/choice ρ [] = []
      rename/choice ρ (S ·· G ∷ Ch) = S ·· rename ρ G ∷ rename/choice ρ Ch

    -- a simultaneous substitution from δ to δ' vars (global type for var)
    sub : (δ δ' : ℕ) -> Set
    sub δ δ' = Fin δ -> Global δ' ng

    -- Notes: Variables are ng, so substitution must keep them ng
    exts : ∀ {δ δ'}
      → (σ : sub δ δ')
        ---------------------------------
      →  sub (suc δ) (suc δ')
    exts σ zero     =  var zero
    exts σ (suc x)  =  rename suc (σ x)

    -- simultaneous substitution
    mutual
      [_]G_ : ∀ {δ δ' g}
        → (ρ : sub δ δ')
        → Global δ g → Global δ' g
      [ ρ ]G end = end
      [ ρ ]G μ G = μ ([ exts ρ ]G G)
      [ ρ ]G var x =  ρ x
      [ ρ ]G (P ⟶ Q ∶[ I , x ] Ch) = P ⟶ Q ∶[ I , x ] ([ ρ ]Ch Ch)
      [ ρ ]G >> G = >> ([ ρ ]G G)

      [_]Ch_ : ∀ {δ δ' I}
        → (ρ : sub δ δ')
        → Vec (Choice δ) I → Vec (Choice δ') I
      [ ρ ]Ch [] = []
      [ ρ ]Ch ((S ·· G) ∷ Ch) = (S ·· ([ ρ ]G G)) ∷ ([ ρ ]Ch Ch)

    -- cons a new type to a substitution
    add-subst : ∀ {δ δ'}
      → (σ : sub δ δ')
      → Global δ' ng
        ---------------------------------
      → sub (suc δ) δ'
    add-subst σ G zero = G
    add-subst σ G (suc i) = σ i

    [_]₀_ : ∀ {δ g} → Global δ ng → Global (suc δ) g → Global δ g
    [_]₀_ {δ} G = [ add-subst var G ]G_

    unfold/global : Global 1 mg → Global 0 mg
    unfold/global G = [ add-subst var (μ G) ]G G

    extsN : ∀ δ {δ₀ δ₁}
      → (σ : sub δ₀ δ₁)
      → sub (δ +ℕ δ₀) (δ +ℕ δ₁)
    extsN zero σ i = σ i
    extsN (suc δ) σ i = exts (extsN δ σ) i

    rename/suc/var : ∀ {δ} {G : Global δ ng} {x : Fin δ} → G ≡ var x
      → rename suc G ≡ var (suc x)
    rename/suc/var refl = refl

    subst/var/id : ∀ {δ} (x : Fin (δ +ℕ 0)) → extsN δ (λ ()) x ≡ var x
    subst/var/id {zero} ()
    subst/var/id {suc δ} zero = refl
    subst/var/id {suc δ} (suc x) = rename/suc/var (subst/var/id x)

    mutual
      subst/id : ∀ {δ g} (G : Global (δ +ℕ 0) g) → [ extsN δ (λ ()) ]G G ≡ G
      subst/id end = refl
      subst/id (μ G) = cong μ (subst/id G)
      subst/id (var x) = subst/var/id x
      subst/id (P ⟶ Q ∶[ I , x ] Ch) = cong (P ⟶ Q ∶[ I , x ]_) (subst/Ch/id Ch)
      subst/id (>> G) = cong >> (subst/id G)

      subst/Ch/id : ∀ {δ I} (Ch : Vec (Choice (δ +ℕ 0)) I)
        → ([ extsN δ (λ ()) ]Ch Ch) ≡ Ch
      subst/Ch/id [] = refl
      subst/Ch/id ((S ·· G) ∷ Ch) =
        cong₂  _∷_ (cong (S ··_) (subst/id G)) (subst/Ch/id Ch)

    extN : ∀ {δ δ'} δ'' → (ρ : ren δ δ')
      → ren (δ'' +ℕ δ) (δ'' +ℕ δ')
    extN zero ρ = ρ
    extN (suc n) ρ = ext (extN n ρ)

    extsN/extN/id : ∀ {δ} {G₀ : Global δ ng} δ₁ (x : Fin (δ₁ +ℕ δ))
      → extsN δ₁ (add-subst var G₀) (extN δ₁ suc x) ≡ var x
    extsN/extN/id zero x = refl
    extsN/extN/id (suc δ₁) zero = refl
    extsN/extN/id {G₀ = G₀} (suc δ₁) (suc x)
      rewrite extsN/extN/id {G₀ = G₀} δ₁ x = refl


    mutual
      subst/rename/suc : ∀ {δ g G₀} δ' (G : Global (δ' +ℕ δ) g)
        → [ extsN δ' (add-subst var G₀) ]G rename (extN δ' suc) G ≡ G
      subst/rename/suc _ end = refl
      subst/rename/suc δ (μ G) = cong μ (subst/rename/suc (suc δ) G)
      subst/rename/suc δ (var x) = extsN/extN/id δ x
      subst/rename/suc δ (_ ⟶ _ ∶[ I , _ ] Ch) =
        cong (_ ⟶ _ ∶[ I , _ ]_) (subst/rename/ch/suc δ Ch)
      subst/rename/suc δ (>> G) = cong >> (subst/rename/suc δ G)

      subst/rename/ch/suc : ∀ {δ I} δ₁ {G₀ : Global δ ng}
        → (Ch : Vec (Choice (δ₁ +ℕ δ)) I)
        → ([ extsN δ₁ (add-subst var G₀) ]Ch rename/choice (extN δ₁ suc) Ch)
          ≡ Ch
      subst/rename/ch/suc δ₁ [] = refl
      subst/rename/ch/suc δ₁ ((S ·· G) ∷ Ch) =
        cong₂ _∷_
          (cong (_ ··_) (subst/rename/suc δ₁ G))
          (subst/rename/ch/suc δ₁ Ch)

    extN/extN : ∀ {δ δ'} δ₁ {ρ : Fin δ → Fin δ'}
      → (x : Fin (δ₁ +ℕ δ))
      → extN δ₁ suc (extN δ₁ ρ x) ≡ extN δ₁ (ext ρ) (extN δ₁ suc x)
    extN/extN zero x = refl
    extN/extN (suc δ₁) zero = refl
    extN/extN (suc δ₁) (suc x) = cong suc (extN/extN δ₁ x)

    mutual
      rename/rename : ∀{δ δ' g} δ'' {ρ : ren δ δ'} (G : Global (δ'' +ℕ δ) g)
        → rename (extN δ'' suc) (rename (extN δ'' ρ) G)
          ≡ rename (extN δ'' (ext ρ)) (rename (extN δ'' suc) G)
      rename/rename δ end = refl
      rename/rename δ (μ G) = cong μ (rename/rename (suc δ) G)
      rename/rename δ (var x) = cong var (extN/extN δ x)
      rename/rename δ (P ⟶ Q ∶[ I , x ] Ch) =
        cong (P ⟶ Q ∶[ I , x ]_) (rename/rename/Ch δ Ch)
      rename/rename δ (>> G) = cong >> (rename/rename δ G)

      rename/rename/Ch : ∀ {δ δ' I} δ₁ {ρ : ren δ δ'}
        → (Ch : Vec (Choice (δ₁ +ℕ δ)) I)
        → rename/choice (extN δ₁ suc) (rename/choice (extN δ₁ ρ) Ch)
          ≡ rename/choice (extN δ₁ (ext ρ)) (rename/choice (extN δ₁ suc) Ch)
      rename/rename/Ch δ₁ [] = refl
      rename/rename/Ch δ₁ ((S ·· G) ∷ Ch) =
        cong₂ _∷_
          (cong (_ ··_) (rename/rename δ₁ G))
          (rename/rename/Ch δ₁ Ch)

    exts/suc : ∀ {δ} {δ'} δ₁ (x : Fin (δ₁ +ℕ δ))
      → (σ : sub δ δ')
      → (extsN δ₁(exts σ) (extN δ₁ suc x))
        ≡ rename (extN δ₁ suc) (extsN δ₁ σ x)
    exts/suc zero x σ = refl
    exts/suc (suc δ₁) zero σ = refl
    exts/suc (suc δ₁) (suc x) σ rewrite exts/suc δ₁ x σ
      = rename/rename 0 (extsN δ₁ σ x)

    mutual
      exts/rename : ∀ {δ δ' g} δ'' (G : Global (δ'' +ℕ δ) g) (σ : sub δ δ')
        → [ extsN δ'' (exts σ) ]G rename (extN δ'' suc) G
          ≡ rename (extN δ'' suc) ([ extsN δ'' σ ]G G)
      exts/rename _ end σ = refl
      exts/rename δ (μ G) σ = cong μ (exts/rename (suc δ) G σ)
      exts/rename δ (var x) σ = exts/suc δ x σ
      exts/rename δ (_ ⟶ _ ∶[ I , _ ] Ch) σ =
        cong (_ ⟶ _ ∶[ I , _ ]_) (exts/rename/ch δ Ch σ)
      exts/rename δ (>> G) σ = cong >> (exts/rename δ G σ)

      exts/rename/ch : ∀ {δ δ' I} δ₁(Ch : Vec (Choice (δ₁ +ℕ δ)) I)
        → (σ : sub δ δ')
        → ([ extsN δ₁ (exts σ) ]Ch rename/choice (extN δ₁ suc) Ch)
          ≡ rename/choice (extN δ₁ suc) ([ extsN δ₁ σ ]Ch Ch)
      exts/rename/ch δ₁ [] _ = refl
      exts/rename/ch δ₁ ((S ·· G) ∷ Ch) σ =
        cong₂ _∷_
          (cong (_ ··_) (exts/rename δ₁ G σ))
          (exts/rename/ch δ₁ Ch σ)

      add-subst/exts : ∀ {δ} {δ'} {σ : sub δ δ'}
        {G₀ : Global δ' ng} (x : Fin (suc δ))
        → ([ add-subst var G₀ ]G ([ exts σ ]G var x)) ≡ ([ add-subst σ G₀ ]G var x)
      add-subst/exts zero = refl
      add-subst/exts {σ = σ} (suc x) = subst/rename/suc 0 (σ x)

      add-subst/var/comm : ∀ {δ δ'} δ'' {σ : sub δ δ'}
        {G₀ : Global δ' ng} (x : Fin (δ'' +ℕ suc δ))
        → [ extsN δ'' (add-subst var G₀) ]G ([ extsN δ'' (exts σ) ]G var x)
          ≡ [ extsN δ'' (add-subst σ G₀) ]G var x
      add-subst/var/comm zero x = add-subst/exts x
      add-subst/var/comm (suc δ'') zero = refl
      add-subst/var/comm (suc δ'') {σ = σ} {G₀ = G₀} (suc x)
        rewrite exts/rename 0 (extsN δ'' (exts σ) x) (extsN δ'' (add-subst var G₀))
        = cong (rename suc) (add-subst/var/comm δ'' x)

    mutual
      add-subst/comm : ∀ {δ δ'} δ'' {g} {σ : sub δ δ'}
        → {G₀ : Global δ' ng} (G : Global (δ'' +ℕ suc δ) g)
        → [ extsN δ'' (add-subst var G₀) ]G ([ extsN δ'' (exts σ) ]G G)
          ≡ [ extsN δ'' (add-subst σ G₀) ]G G
      add-subst/comm _ end = refl
      add-subst/comm δ (μ G) = cong μ (add-subst/comm (suc δ) G)
      add-subst/comm δ (var x) = add-subst/var/comm δ x
      add-subst/comm δ (P ⟶ Q ∶[ I , x ] Ch)
        = cong (P ⟶ Q ∶[ I , x ]_) (add-subst/Ch/comm δ Ch)
      add-subst/comm _ (>> G) = cong >> (add-subst/comm _ G)

      add-subst/Ch/comm : ∀ {δ δ'} δ'' {I} {σ : sub δ δ'}
        {G₀ : Global δ' ng} (Ch : Vec (Choice (δ'' +ℕ suc δ)) I)
        → ([ extsN δ'' (add-subst var G₀) ]Ch ([ extsN δ'' (exts σ) ]Ch Ch))
          ≡ ([ extsN δ'' (add-subst σ G₀) ]Ch Ch)
      add-subst/Ch/comm δ'' [] = refl
      add-subst/Ch/comm δ'' (S ·· G ∷ Ch)
        = cong₂ _∷_ (cong (S ··_) (add-subst/comm δ'' G))
                    (add-subst/Ch/comm δ'' Ch)

    open Choice

    lu/subst : ∀ {δ δ' I} (σ : sub δ δ') (Chs : Vec (Choice δ) I) i
      → [ σ ]G (Chs [ i ]cont) ≡ ([ σ ]Ch Chs) [ i ]cont
    lu/subst σ (x ∷ Chs) zero = refl
    lu/subst σ (x ∷ Chs) (suc i) = lu/subst σ Chs i


    open HeadAct

    ∈G-¬end : ∀ {P} {G : Global 0 ng} → P ∈G G → G ≢ end
    ∈G-¬end () refl

    mutual
      data _=<_>=>ᵣ_
        : {I : ℕ} → Vec (Choice 0) I → Action → Vec (Choice 0) I → Set where
        step/choice/nil : ∀{α} → [] =< α >=>ᵣ []

        step/choice/cons : ∀{G G' I S α} {Ch Ch' : Vec (Choice 0) I}
          → G -< α >-> G' → Ch =< α >=>ᵣ Ch'
          ----------------------------------------------
          → ((S ·· G) ∷ Ch) =< α >=>ᵣ ((S ·· G') ∷ Ch')

      data _-<_>->_ : Global 0 ng → Action → Global 0 ng → Set where
        step/i : ∀ {P Q I pnq Ch} (i : Fin (suc I)) →
          >> (P ⟶ Q ∶[ I , pnq ] Ch)
          -< P ⟶ Q # ch/sorts Ch , i >->
          (Ch [ i ]cont)

        step/unfold : ∀{G α G'} →
          >> ([ μ G ]₀ G) -< α >-> G'
          ---------------------------
          → μ G -< α >-> G'

        step/tl/I : ∀{α P Q I pnq Ch Ch'} →
          (P ⟶ Q # ch/sorts Ch) ⋔ (proj₁ α) →
          Ch =< α >=>ᵣ Ch' →
          >> (P ⟶ Q ∶[ I , pnq ] Ch) -< α >-> >> ((P ⟶ Q ∶[ I , pnq ] Ch'))


  GlobalTypes : BTheory N
  GlobalTypes .BTheory.Behav = PreTypes.Global 0 ng
  -- GlobalTypes .BTheory._∈B_ P = PreTypes._∈G_ P
  GlobalTypes .BTheory._-<_>->_ = PreTypes._-<_>->_

  open PreTypes hiding (_-<_>->_)
  open BTheory GlobalTypes

  ------------------------------------------------------------------------------

  ∉T-end-trace : ∀ {G''} → end ===> G'' → G'' ≡ end
  ∉T-end-trace (■ , snd) = refl

  ∉T-end : ∀ {P} → ¬ (P ∈T end)
  ∉T-end (BTheory.in/α () _)
  ∉T-end (BTheory.in/later () _)

  steps? : ∀ G → (∃[ α ] (∃[ G' ] (G -< α >-> G'))) ⊎ ended G
  steps? end = inj₂ λ P x → ∉T-end x  -- (λ P ())
  steps? (μ (P ⟶ Q ∶[ I , pnq ] x)) = inj₁ (_ , _ , step/unfold (step/i zero))
  steps? (>> (P ⟶ Q ∶[ I , pnq ] x)) = inj₁ (_ , _ , step/i zero)

  private
    step/choice/sort : ∀ {α I}{Ch Ch' : Vec (Choice 0) I} i
      → Ch =< α >=>ᵣ Ch'
      → Ch [ i ]sort ≡ Ch' [ i ]sort
    step/choice/sort zero (step/choice/cons x x₁) = refl
    step/choice/sort (suc i) (step/choice/cons x x₁) = step/choice/sort i x₁

    step/choice/sorts : ∀ {α I}{Ch Ch' : Vec (Choice 0) I}
      → Ch =< α >=>ᵣ Ch'
      → ch/sorts Ch ≡ ch/sorts Ch'
    step/choice/sorts step/choice/nil = refl
    step/choice/sorts (step/choice/cons x x₁) =
      cong (_ ∷_) (step/choice/sorts x₁)

    step/choice/cont : ∀ {α I}{Ch Ch' : Vec (Choice 0) I} i
      → Ch =< α >=>ᵣ Ch'
      → (Ch [ i ]cont) -< α >-> (Ch' [ i ]cont)
    step/choice/cont zero (step/choice/cons x x₁) = x
    step/choice/cont (suc i) (step/choice/cons x x₁) = step/choice/cont i x₁

    step/conts : ∀ {α I}{Ch Ch' : Vec (Choice 0) I}
      → (∀ i → Ch [ i ]sort ≡ Ch' [ i ]sort)
      → (∀ i → (Ch [ i ]cont) -< α >-> (Ch' [ i ]cont))
      → Ch =< α >=>ᵣ Ch'
    step/conts {Ch = []} {Ch' = []} x y = step/choice/nil
    step/conts {Ch = (S₁ ·· G₁) ∷ Ch} {Ch' = (S₂ ·· G₂) ∷ Ch'} x y
      rewrite x zero
      = step/choice/cons (y zero) (step/conts (λ i → x (suc i)) (λ i → y (suc i)))

    ¬Indep/≡act : ∀ {G α α' G' G''}
                → G -< α >-> G' → G -< α' >-> G''
                → ¬ (proj₁ α) ⋔ (proj₁ α')
                → proj₁ α ≡ proj₁ α'
    ¬Indep/≡act (step/i i) (step/i i₁) ii = refl
    ¬Indep/≡act (step/i i) (step/tl/I x x₁) ii = ⊥-elim (ii x)
    ¬Indep/≡act (step/tl/I x x₁) (step/i i) ii = ⊥-elim (ii (⋔sym x))
    ¬Indep/≡act
      (step/tl/I {Ch = (_ ·· G ) ∷ _} _ (step/choice/cons sG _))
      (step/tl/I {Ch = (_ ·· G') ∷ _} _ (step/choice/cons sG' _)) ii
      = ¬Indep/≡act sG sG' ii
    ¬Indep/≡act (step/unfold gr0) (step/unfold gr1) ii = ¬Indep/≡act gr0 gr1 ii

  step/acts/same : ∀ {G α α' G' G''}
                 → G -< α >-> G' → G -< α' >-> G''
                 → sender α ∈α α'
                 → proj₁ α ≡ proj₁ α'
  step/acts/same gr gr' (∈S refl)
    = ¬Indep/≡act gr gr' λ{ f → f (inj₁ (∈S refl)) }
  step/acts/same gr gr' (∈R refl)
    = ¬Indep/≡act gr gr' λ{ f → f (inj₁ (∈R refl)) }

  recv∈α/≡act : ∀ {G α α' G' G''}
              → G -< α >-> G' → G -< α' >-> G''
              → receiver α ∈α α'
              → proj₁ α ≡ proj₁ α'
  recv∈α/≡act gr gr' (∈S refl)
    = ¬Indep/≡act gr gr' λ{ f → f (inj₂ (∈S refl)) }
  recv∈α/≡act gr gr' (∈R refl)
    = ¬Indep/≡act gr gr' λ{ f → f (inj₂ (∈R refl)) }

  private
    step/¬Indep/same : ∀ {G₀ G₁ G₂ α α'}
      → receiver α ∈α α'
      → G₀ -< α >-> G₁
      → G₀ -< α' >-> G₂
      → sender α ∈α α'
    step/¬Indep/same x (step/i i) (step/i i₁) = ∈S refl
    step/¬Indep/same x (step/i i) (step/tl/I ii x₂) = ⊥-elim (ii (inj₂ x))
    step/¬Indep/same x (step/unfold gr) (step/unfold gr')
      = step/¬Indep/same x gr gr'
    step/¬Indep/same {α = α}{α' = α'} x (step/tl/I ii x₂) (step/i i)
      = ⊥-elim (⋔sym ii (inj₂ x))
    step/¬Indep/same i
      (step/tl/I _ (step/choice/cons x _))
      (step/tl/I _ (step/choice/cons y _)) = step/¬Indep/same i x y

  step/parts/det : ∀ {G α α' G' G''}
                 → G -< α >-> G' → G -< α' >-> G''
                 → sender α ≡ sender α'
                 → proj₁ α ≡ proj₁ α'
  step/parts/det gr gr' refl = step/acts/same gr gr' (∈S refl)

  private
    proj/step : ∀{I Ch Ch' α}(i : Fin (suc I))
      → Ch =< α >=>ᵣ Ch'
      → (Ch [ i ]cont) -< α >-> (Ch' [ i ]cont)
    proj/step {I = zero} zero (step/choice/cons x x₁) = x
    proj/step {I = suc I} zero (step/choice/cons x x₁) = x
    proj/step {I = suc I} (suc i) (step/choice/cons x x₁)
      = proj/step i x₁

    -- Stepping with a given `α` is deterministic.
  mutual
    step/det : ∀ {G α G' G''}
      → G -< α >-> G' → G -< α >-> G''
      --------------------------------
      → G' ≡ G''
    step/det (step/i i) (step/i .i) = refl
    step/det (step/i i) (step/tl/I x _) = ⊥-elim (x (inj₂ (∈R refl)))
    step/det (step/unfold x) (step/unfold y) = step/det x y
    step/det (step/tl/I x _) (step/i i) = ⊥-elim (x (inj₂ (∈R refl)))
    step/det (step/tl/I _ x) (step/tl/I _ y) =
      cong >> (cong (_ ⟶ _ ∶[ _ , _ ]_) (step/det/Ch x y))

    step/det/Ch : ∀ {α I} {Ch Ch' Ch'' : Vec (Choice 0) I}
      → (x : Ch =< α >=>ᵣ Ch') (y : Ch =< α >=>ᵣ Ch'')
      ----------------------------------------------------------
      → Ch' ≡ Ch''
    step/det/Ch step/choice/nil step/choice/nil = refl
    step/det/Ch (step/choice/cons x y) (step/choice/cons z t) =
      cong₂ _∷_
        (cong (_ ··_) (step/det x z))
        (step/det/Ch y t)

  private
    mutual
      step/alt : ∀ {p G i G'} → G -< p , i >-> G'
        → ∀ i → ∃[ G' ] (G -< p , i >-> G')
      step/alt (step/i _)  i = _ , step/i i
      step/alt (step/unfold rdyTr) i =
        let _ , rt = step/alt rdyTr i
        in _ , step/unfold rt
      step/alt (step/tl/I nPQ x) i =
        let _ , rt = step/alt/Ch x i
        in _ , step/tl/I nPQ rt

      step/alt/Ch : ∀ {p i I} {G G' : Vec (Choice 0) I} → G =< p , i >=>ᵣ G'
        → ∀ i → ∃[ G' ] (G =< p , i >=>ᵣ G')
      step/alt/Ch step/choice/nil i = [] , step/choice/nil
      step/alt/Ch (step/choice/cons rtG rtCh) i =
        let _ , rtG' = step/alt rtG i
            _ , rtCh' = step/alt/Ch rtCh i
        in _ , step/choice/cons rtG' rtCh'

  ready/all : ∀ {p G} → p [R] G → ∀ i → ∃[ G' ] (G -< p , i >-> G')
  ready/all R[ rt ] = step/alt rt

  private
    step/alt/id : ∀ {α G G'} (r : G -< α >-> G')
                → proj₁ (step/alt r (proj₂ α)) ≡ G'
    step/alt/id {α} r = step/det (proj₂ (step/alt r (proj₂ α))) r

    step/alt/Ch/id : ∀ {α I} {G G' : Vec (Choice 0) I} (r : G =< α >=>ᵣ G')
                   → proj₁ (step/alt/Ch r (proj₂ α)) ≡ G'
    step/alt/Ch/id {α} r = step/det/Ch (proj₂ (step/alt/Ch r (proj₂ α))) r

    record _[W]_ P (G : Global 0 ng) : Set where
      constructor W|_>_
      field
        {act}  : HeadAct
        ∉act : False (P ∈pr? act)
        actRdy : act [R] G

  mutual
    diamond : ∀ {G α G₁ α' G₂}
      → G -< α >-> G₁ → G -< α' >-> G₂
      → (nS  : (proj₁ α) ⋔ (proj₁ α'))
      → ∃[ G' ] (G₁ -< α' >-> G' × G₂ -< α >-> G')
    diamond (step/i i) (step/i i₁) f = ⊥-elim (f (inj₂ (∈R refl)))
    diamond (step/i i) (step/tl/I _ x₂) nS
      rewrite step/choice/sorts x₂
        = _ , (step/choice/cont i x₂ , step/i i)
    diamond (step/unfold x) (step/unfold y) nS = diamond x y nS
    diamond (step/tl/I x x₂) (step/i i) nS
      rewrite step/choice/sorts x₂
        = _ , (step/i i , step/choice/cont i x₂)
    diamond (step/tl/I x x₂) (step/tl/I x₃ x₅) nS =
      let _ , (sCh , sCh') = diamond/Ch x₂ x₅ nS
      in _ , (step/tl/I x₃ sCh , step/tl/I x sCh')

    diamond/Ch : ∀ {I α α'} {Ch Ch' Ch'' : Vec (Choice 0) I}
      → Ch =< α >=>ᵣ Ch' → Ch =< α' >=>ᵣ Ch''
      → (nS  : (proj₁ α) ⋔ (proj₁ α'))
      → ∃[ Ch''' ] (Ch' =< α' >=>ᵣ Ch''' × Ch'' =< α >=>ᵣ Ch''')
    diamond/Ch step/choice/nil step/choice/nil nS =
      [] , (step/choice/nil , step/choice/nil)
    diamond/Ch (step/choice/cons x x₁) (step/choice/cons y y₁) nS
      with diamond x y nS | diamond/Ch x₁ y₁ nS
    ... | _ , (sG , sG') | _ , (sCh , sCh') =
      _ , (step/choice/cons sG sCh , step/choice/cons sG' sCh')

  the-diamond : ∀ {G α G₁ α' G₂}
      → G -< α >-> G₁ → G -< α' >-> G₂
      → (nS  : α ∥ α')
      → ∃[ G' ] (G₁ -< α' >-> G' × G₂ -< α >-> G')
  the-diamond gr gr' (ii-≡snd refl x₁)
    with step/parts/det gr gr' refl
  ... | refl = ⊥-elim (x₁ refl)
  the-diamond gr gr' (ii-disj x) = diamond gr gr' x

  indep? : ∀ {G α₁ G₁ α₂ G₂}
    → G -< α₁ >-> G₁
    → G -< α₂ >-> G₂
    → (proj₁ α₁) ⋔ (proj₁ α₂) ⊎ proj₁ α₁ ≡ proj₁ α₂
  indep? (step/i i) (step/i i₁) = inj₂ refl
  indep? (step/i i) (step/tl/I nPQ _) = inj₁ nPQ
  indep? {α₁ = α₁} {α₂ = α₂}(step/tl/I nPQ _) (step/i i) = inj₁ (⋔sym nPQ)
  indep?
    (step/tl/I _ (step/choice/cons x _))
    (step/tl/I _ (step/choice/cons y _)) =
    indep? x y
  indep? (step/unfold x) (step/unfold y) =
    indep? x y

  private
    global/steps : ∀{α G G'} → G -< α >-> G' → G ===> G'
    global/steps gr = [ gr , tt ]◄ (■ , tt) -- tr/trans gr tt tr/refl

  private
    open Choice
    in-∈T/cont : ∀ {P δ I } Chs i {σ : sub δ 0}
      → (nn : P ∈T ([ σ ]G lookup Chs i .continuation))
      → ∀ {P' Q' p'nq'} → P ∈T >> (P' ⟶ Q' ∶[ I , p'nq' ] ([ σ ]Ch Chs))
    in-∈T/cont Chs i {σ = σ} n rewrite lu/subst σ Chs i = in/later (step/i i) n

  ~unfold : ∀ {G : Global 1 mg} → (μ G) ~ >> ([ add-subst var (μ G) ]G G)
  ~unfold .BTheory._~_.~L (step/unfold x) = _ , x , ~refl
  ~unfold .BTheory._~_.~R x = _ , step/unfold x , ~refl

  private
    in-∈T/unfold : ∀ {P} {G : Global (suc zero) mg}
      → P ∈T >> ([ μ G ]₀ G) → P ∈T μ G
    in-∈T/unfold ii = ∈~ (~sym ~unfold) ii

    transport/∈T : ∀ {P G G'} → G ≡ G' → P ∈T G → P ∈T G'
    transport/∈T refl x = x

    ∈G-∈T/aux : ∀ {P δ g} → {G : Global δ g}
      → P ∈G G → ∀ σ → P ∈T ([ σ ]G (ing G))
    ∈G-∈T/aux {δ = δ} {G = μ G} (in/mu x) σ
      = in-∈T/unfold (transport/∈T (cong >> rw) inT)
      where
        rw = sym (add-subst/comm 0 G)
        inT = ∈G-∈T/aux x (add-subst σ ([ σ ]G (μ G)))
    ∈G-∈T/aux in/msg/send σ = in/send (step/i zero)
    ∈G-∈T/aux in/msg/recv σ = in/recv (step/i zero)
    ∈G-∈T/aux (in/msg/cont/i i (in/ch x)) σ
      = in-∈T/cont _ i (∈G-∈T/aux x σ)
    ∈G-∈T/aux (in/>> x) σ = ∈G-∈T/aux x σ

  ∈G-∈T : ∀ {P} → {G : Global 0 ng} → P ∈G G → P ∈T G
  ∈G-∈T x = transport/∈T (subst/id _) (∈G-∈T/aux x (λ ()))

  private
    mutual
      inG/rename : ∀ {P δ g} δ' {G : Global (δ' +ℕ δ) g}
        → P ∈G rename (extN δ' suc) G → P ∈G G
      inG/rename {δ = δ} δ' {G = μ G} (in/mu x) = in/mu (inG/rename (suc δ') x)
      inG/rename δ' {G = P ⟶ Q ∶[ I , x₁ ] Ch} in/msg/send = in/msg/send
      inG/rename δ' {G = P ⟶ Q ∶[ I , x₁ ] Ch} in/msg/recv = in/msg/recv
      inG/rename δ' {G = P ⟶ Q ∶[ I , x₁ ] Ch} (in/msg/cont/i i x) =
        in/msg/cont/i i (inG/rename/Ch δ' Ch i x)
      inG/rename δ' {G = >> G} (in/>> x) = in/>> (inG/rename δ' x)

      inG/rename/Ch : ∀ {P δ I} δ' (Ch : Vec (Choice (δ' +ℕ δ)) I)
        → (i : Fin I) (x : P ∈Ch lookup (rename/choice (extN δ' suc) Ch) i)
        → P ∈Ch lookup Ch i
      inG/rename/Ch δ' ((S ·· G) ∷ Ch) zero (in/ch x) =
        in/ch (inG/rename δ' x)
      inG/rename/Ch δ' ((S ·· G) ∷ Ch) (suc i) x = inG/rename/Ch δ' Ch i x

    inG/ext/var : ∀ {P δ δ₁} {G' : Global δ ng} {x₁ : Fin (δ₁ +ℕ suc δ)}
      → (x : P ∈G extsN δ₁ (add-subst var G') x₁)
      → P ∈G G'
    inG/ext/var {δ₁ = zero} {x₁ = zero} x = x
    inG/ext/var {δ₁ = suc δ₁} {x₁ = suc x₁} x =
      inG/ext/var (inG/rename 0 x)

    mutual
      inG/subst : ∀ {P δ g} {G'} δ' {G : Global (δ' +ℕ suc δ) g}
        → P ∈G ([ extsN δ' (add-subst var G') ]G G)
        → P ∈G G' ⊎ P ∈G G
      inG/subst {G' = G'} δ {G = μ G} (in/mu x)
        with inG/subst {G' = G'} (suc δ) {G = G} x
      ... | inj₁ i = inj₁ i
      ... | inj₂ i = inj₂ (in/mu i)
      inG/subst δ {G = var x₁} x = inj₁ (inG/ext/var x)
      inG/subst δ {G = P ⟶ Q ∶[ I , x₁ ] Ch} in/msg/send = inj₂ in/msg/send
      inG/subst δ {G = P ⟶ Q ∶[ I , x₁ ] Ch} in/msg/recv = inj₂ in/msg/recv
      inG/subst δ {G = P ⟶ Q ∶[ I , x₁ ] Ch} (in/msg/cont/i i x)
        with inG/subst/Ch δ Ch i x
      ... | inj₁ i = inj₁ i
      ... | inj₂ j = inj₂ (in/msg/cont/i i j)
      inG/subst δ {G = >> G} (in/>> x) with inG/subst δ x
      ... | inj₁ i = inj₁ i
      ... | inj₂ i = inj₂ (in/>> i)

      inG/subst/Ch : ∀ {P δ I} {G'} δ'
        → (Ch : Vec (Choice (δ' +ℕ suc δ)) I) (i : Fin I)
        → P ∈Ch lookup ([ extsN δ' (add-subst var G') ]Ch Ch) i
        → P ∈G G' ⊎ P ∈Ch lookup Ch i
      inG/subst/Ch δ' ((_ ·· G) ∷ Ch) zero (in/ch x) with inG/subst δ' x
      ... | inj₁ i = inj₁ i
      ... | inj₂ i = inj₂ (in/ch i)
      inG/subst/Ch δ' (_  ∷ Ch) (suc i) x = inG/subst/Ch δ' Ch i x

    inG/fold : ∀ {P δ} {G : Global (suc δ) mg}
      → P ∈G ([ add-subst var (μ G) ]G G)
      → P ∈G μ G
    inG/fold {G = G} x with inG/subst {G' = μ G} 0 {G = G} x
    ... | inj₁ i = i
    ... | inj₂ i = in/mu i

  in/action/global : ∀ {G G' α}
    → G -< α >-> G'
    → (sender α ∈G G) × (receiver α ∈G G)
  in/action/global (step/i i) = in/>> in/msg/send , in/>> in/msg/recv
  in/action/global (step/unfold x) with in/action/global x
  ... | in/>> inS , in/>> inR = inG/fold inS , inG/fold inR
  in/action/global (step/tl/I x (step/choice/cons x₂ x₃))
    with in/action/global x₂
  ... | inS , inR = in/>> (in/msg/cont/i zero (in/ch inS))
                  , in/>> (in/msg/cont/i zero (in/ch inR))

  ∈α-∈G : ∀ {G G' α P} → G -< α ∋ P >-> G' → P ∈G G
  ∈α-∈G (tr , ∈S refl) = proj₁ (in/action/global tr)
  ∈α-∈G (tr , ∈R refl) = proj₂ (in/action/global tr)

  private
    mutual
      in/action/skip : ∀ {P G G'' α}
        → (inN : P ∈G G'') → (st : G -< α >-> G'')
        → P ∈G G
      in/action/skip inN (step/i i) = in/>> (in/msg/cont/i i (in/ch inN))
      in/action/skip inN (step/unfold st) with in/action/skip inN st
      ... | in/>> rr = inG/fold rr
      in/action/skip (in/>> in/msg/send) (step/tl/I _ _) = in/>> in/msg/send
      in/action/skip (in/>> in/msg/recv) (step/tl/I _ _) = in/>> in/msg/recv
      in/action/skip (in/>> (in/msg/cont/i i y)) (step/tl/I _ x) =
        in/>> (in/msg/cont/i i (in/action/skip/Ch i y x))

      in/action/skip/Ch : ∀ {P α I} {Ch Chs : Vec (Choice 0) I} (i : Fin I)
        → P ∈Ch lookup Chs i → Ch =< α >=>ᵣ Chs
        → P ∈Ch lookup Ch i
      in/action/skip/Ch zero (in/ch x) (step/choice/cons x₁ x₂) =
        in/ch (in/action/skip x x₁)
      in/action/skip/Ch (suc i) x (step/choice/cons x₁ x₂) =
        in/action/skip/Ch i x x₂

    ∈-trace/skip : ∀ {P G G''} → (inN : P ∈G G'') → (st : G ===> G'') → P ∈G G
    ∈-trace/skip i (■ , snd) = i
    ∈-trace/skip i ((x ◄ fst) , _ , snd)
      = in/action/skip (∈-trace/skip i (fst , snd)) x

    ∈T-∈G/aux : ∀ {P} {G : Global 0 ng} → P ∈T G → P ∈G G
    ∈T-∈G/aux (in/α x x₁) = ∈α-∈G (x , x₁)
    ∈T-∈G/aux (in/later x tr)
      = ∈-trace/skip (∈T-∈G/aux tr) ([ x , tt ]◄ (■ , tt)) -- (tr/trans x tt tr/refl)

  ∈T-∈G : ∀ {P} {G : Global 0 ng} → P ∈T G → P ∈G G
  ∈T-∈G inA = ∈T-∈G/aux inA

  private
    ∈T/step : ∀ {G α G' P}
      → G -< α >-> G' → P ∈T G'
      ------------------------
      → P ∈T G
    ∈T/step st a = in/later st a

  ∉G/step : ∀ {G α G' P}
    → G -< α >-> G' → ¬ (P ∈G G)
    ----------------------------
    → ¬ (P ∈G G')
  ∉G/step tr = contraposition λ x →
    ∈T-∈G (∈T/step tr (∈G-∈T x))

  open _~_

  in/bisim : ∀ {P G G'} → G ~ G' → P ∈G G → P ∈G G'
  in/bisim G~G' p∈G = ∈T-∈G (∈~ G~G' (∈G-∈T p∈G))


  private
    Indep/red : ∀{P Q I pnq Ch G α}{S : Vec Sort (suc I)}
      → (P ⟶ Q # S) ⋔ (proj₁ α)
      → >> (P ⟶ Q ∶[ I , pnq ] Ch) -< α >-> G
      → ∃[ Ch' ] Ch =< α >=>ᵣ Ch'
    Indep/red f (step/i i) = ⊥-elim (f (inj₂ (∈R refl)))
    Indep/red ind (step/tl/I nPQ chr) = _ , chr

    red/in/act : ∀{P Q I pnq Ch α G}
      → P ∈α α ⊎ Q ∈α α
      → >> (P ⟶ Q ∶[ I , pnq ] Ch) -< α >-> G
      → ∃[ i ] α ≡ (P ⟶ Q # ch/sorts Ch , i)
    red/in/act x (step/i i) = i , refl
    red/in/act x (step/tl/I nPQ _) = ⊥-elim (nPQ x)

    subst/act : ∀{G α α' G'} → α ≡ α' → G -< α' >-> G' → G -< α >-> G'
    subst/act refl x = x

    subst/act/sorts : ∀{G G' P Q I}{S S' : Vec Sort (suc I)}{i}
      → S ≡ S' → G -< P ⟶ Q # S , i >-> G' → G -< P ⟶ Q # S' , i >-> G'
    subst/act/sorts refl x = x

    step/all : ∀{I α} Ch
      → (f : ∀ (i : Fin I) → ∃[ G ] ((Ch [ i ]cont) -< α >-> G))
      → Vec (Choice 0) I
    step/all [] f = []
    step/all ((S ·· G) ∷ Ch) f with f zero
    ... | G' , _ = (S ·· G') ∷ step/all Ch λ i → f (suc i)

    step/all/Ch : ∀{I α} Ch
      → (f : ∀ (i : Fin I) → ∃[ G ] ((Ch [ i ]cont) -< α >-> G))
      → Ch =< α >=>ᵣ step/all Ch f
    step/all/Ch [] f = step/choice/nil
    step/all/Ch ((S ·· G) ∷ Ch) f with f zero
    ... | G' , G'r = step/choice/cons G'r (step/all/Ch Ch (λ i → f (suc i)))

    no-phantom-comm : ∀ {hα i j α' G G' Gᵢ Gⱼ'}
      → hα ∥ₕ (proj₁ α')
      → G -< α' >-> G'
      → G -< hα , i >-> Gᵢ
      → G' -< hα , j >-> Gⱼ'
      → ∃[ Gⱼ ] G -< hα , j >-> Gⱼ
    no-phantom-comm {j = j} _ _ gr1 _ = step/alt gr1 j

    mutual
      swap-act : ∀ { α α' G₀ G₁ }
        (ii : (proj₁ α) ⋔ (proj₁ α'))
        (r : G₀ -< α >-> G₁)
        → (∀ i → ∃[ Gi ] proj₁ (step/alt r i) -< α' >-> Gi)
        → ∃[ G₂ ] G₀ -< α' >-> G₂
      swap-act {α} {α'} {G₀} {G₁} ii (step/i i) x
        = _ , (step/tl/I ii (step/all/Ch _ x))
      swap-act {α} {α'} {G₀} {G₁} ii (step/unfold r) x
        = let _ , rr = swap-act ii r x
          in _ , (step/unfold rr)
      swap-act {α} {α'} {G₀} {G₁} ii (step/tl/I ii' r) x with x zero
      ... | _ , step/i i
        rewrite sym (step/choice/sorts (step/alt/Ch r zero .proj₂))
        = _ , step/i i
      ... | _ , step/tl/I f _
        = let _ , rk = swap-act/Ch ii r xCh
          in _ , (step/tl/I f rk)
        where
          xCh : ∀ i → ∃[ Ch' ] step/alt/Ch r i .proj₁ =< α' >=>ᵣ Ch'
          xCh i with x i
          xCh i | _ , step/i j = ⊥-elim (f (inj₂ (∈R refl))) -- (ii'' (inj₂ (∈R refl)))
          xCh i | _ , step/tl/I _ x = _ , x

      swap-act/Ch : ∀ { α α'}{I} {Ch Ch' : Vec (Choice 0) I}
        (ii : (proj₁ α) ⋔ (proj₁ α'))
        (r : Ch  =< α >=>ᵣ Ch')
        → (∀ i → ∃[ Ch' ] step/alt/Ch r i .proj₁ =< α' >=>ᵣ Ch')
        → ∃[ Ch' ] Ch =< α' >=>ᵣ Ch'
      swap-act/Ch ii step/choice/nil x = x zero
      swap-act/Ch {α}{α'} ii (step/choice/cons y r) x
        = let _ , ry = swap-act ii y xy
              _ , rk = swap-act/Ch ii r xr
          in _ , step/choice/cons ry rk
        where
          xy : ∀ i → ∃[ G' ] (step/alt y i .proj₁ -< α' >-> G')
          xy i with x i
          ... | _ , step/choice/cons x _ = _ , x
          xr : ∀ i → ∃[ G' ] (step/alt/Ch r i .proj₁ =< α' >=>ᵣ G')
          xr i with x i
          ... | _ , step/choice/cons _ x = _ , x

  snd≢rcv : ∀{G G' α} → G -< α >-> G' → False (sender α ≟f receiver α)
  snd≢rcv (step/i {pnq  = pnq} i) = pnq
  snd≢rcv (step/unfold x) = snd≢rcv x
  snd≢rcv (step/tl/I x (step/choice/cons k _)) = snd≢rcv k

  -- Backwards bisimulation
  private
    α-choices : Action → Set
    α-choices α = Vec (Choice 0) (suc (nacts α))

    mk-alt : ∀ {α G G'} (gr : G -< α >-> G') → Fin (suc (nacts α)) → Choice 0
    mk-alt {α = α} gr i = lookup (α-sorts α) i ·· (proj₁ (step/alt gr i))

    open Choice

    _[_]cont≔_ : ∀ {n} (C : Vec (Choice 0) n) → Fin n → Global 0 ng
      → Vec (Choice 0) n
    C [ i ]cont≔ G = C [ i ]≔ sort (lookup C i) ·· G

    mk-alts : ∀ {α G G'} (gr : G -< α >-> G') → α-choices α
    mk-alts {α = α} G = tabulate (mk-alt G)

    sorts/tabl : ∀ {n} (S : Vec Sort n) (gr : Fin n → Global 0 ng)
      → ch/sorts (tabulate (λ i → lookup S i ·· (gr i))) ≡ S
    sorts/tabl [] gr = refl
    sorts/tabl (x ∷ S) gr = cong (x ∷_) (sorts/tabl S (λ z → gr (suc z)))

    mk-branches : ∀ {α G G'} (gr : G -< α >-> G') G₀ → α-choices α
    mk-branches {α = α} G G₀
      = mk-alts G [ proj₂ α ]≔ lookup (α-sorts α) (proj₂ α) ·· G₀

    sorts/upd : ∀ {n} S (C : Vec (Choice 0) n) (i : Fin n) (G : Global 0 ng)
      → ch/sorts C ≡ S
      → ch/sorts (C [ i ]≔ lookup S i ·· G) ≡ S
    sorts/upd _ (x ∷ C) zero G refl = refl
    sorts/upd _ ((S ·· _) ∷ C) (suc i) G refl
      = cong (S ∷_) (sorts/upd _ C i G refl)

    sorts/tabulate : ∀ {α G G'} (gr : G -< α >-> G') G₀
      → ch/sorts (mk-branches gr G₀) ≡ α-sorts α
    sorts/tabulate {α = α} G G₀
      = sorts/upd (α-sorts α) (tabulate (mk-alt G)) (proj₂ α) G₀
                  (sorts/tabl (α-sorts α) (proj₁ ∘ step/alt G))

    mk-prefix : ∀ {α} → False (sender α ≟f receiver α)
      → ∀ {G G'} → G -< α >-> G' →  α-choices α → Global 0 ng
    mk-prefix {α = α} snd≢rcv gr C = >> (sender α ⟶ receiver α ∶[ _ , snd≢rcv ] C)

    stepback : ∀ {α} → False (sender α ≟f receiver α)
      → ∀ {G₀ G₁}(gr : G₀ -< α >-> G₁) G₂ → Global 0 ng
    stepback snd≢rcv gr G₂ = mk-prefix snd≢rcv gr (mk-branches gr G₂)

    stepback/α : ∀ {α} (s≢r : False (sender α ≟f receiver α))
      → ∀ {G₀ G₁} (gr : G₀ -< α >-> G₁) G₂
      → stepback s≢r gr G₂ -< α >-> G₂
    stepback/α {α = P ⟶ Q # S , i} snd≢rcv gr  G₂
      with step/i {P}{Q}{_}{snd≢rcv}{mk-branches gr G₂} i
    ... | sti rewrite sorts/tabulate gr G₂
              | lookup∘update i (mk-alts gr) (lookup S i ·· G₂) = sti

    open HeadAct
    stepback/α' : ∀ {α} (s≢r : False (psender α ≟f preceiver α))
      → ∀ {i j G₀ G'₁ G₁}
      → ∀ (gr : G₀ -< α , i >-> G₁) (gr' : G₀ -< α , j >-> G'₁) G₂
      → j ≢ i
      → stepback s≢r gr G₂ -< α , j >-> G'₁
    stepback/α' {α = P ⟶ Q # S} snd≢rcv {i = i}{j = j}gr gr' G₂ x
      with step/i {P}{Q}{_}{snd≢rcv}{mk-branches gr G₂} j
    ... | sti rewrite sorts/tabulate gr G₂
              | lookup∘update′ x (mk-alts gr) (lookup S i ·· G₂)
              | lookup∘tabulate (mk-alt gr) j
              | step/det (proj₂ (step/alt gr j)) gr'
                = sti

    stepback/sorts : ∀ {α G₀ G₁ G G'} G₂ nG
      (rG₀G₁  : G₀ -< α >-> G₁)
      (rGG'   : G -< α >-> G')
      → ∀ i → ((mk-branches rG₀G₁ G₂) [ i ]sort)
                            ≡ ((mk-branches rGG' nG) [ i ]sort)
    stepback/sorts {α = α , i} G₂ nG rG₀G₁ rGG' j with j ≟f i
    ... | yes refl
      rewrite lookup∘update i (mk-alts rG₀G₁) (lookup (sorts α) i ·· G₂)
              | lookup∘update i (mk-alts rGG') (lookup (sorts α) i ·· nG)
      = refl
    ... | no pf
      rewrite lookup∘update′ pf (mk-alts rG₀G₁) (lookup (sorts α) i ·· G₂)
              | lookup∘tabulate (mk-alt rG₀G₁) j
              | lookup∘update′ pf (mk-alts rGG') (lookup (sorts α) i ·· nG)
              | lookup∘tabulate (mk-alt rGG') j
              = refl

    stepback/cont : ∀ {α α' G₀ G₁ G G' G₂ nG}
      (ii : (proj₁ α) ⋔ (proj₁ α'))
      (rG₀G₁  : G₀ -< α >-> G₁)
      (rG₀G   : G₀ -< α' >-> G) -- because we need to know where 'G' comes from
      (rGG'   : G -< α >-> G')
      (rG₂Gn  : G₂ -< α' >-> nG) -- Because we need to know what G₂ reduces to
      → ∀ i → ((mk-branches rG₀G₁ G₂) [ i ]cont)
                            -< α' >-> ((mk-branches rGG' nG) [ i ]cont)
    stepback/cont {α = α , i}{α' = α'}{G₂ = G₂}{nG = nG} ii rG₀G₁ rG₀G rGG' rG₂Gn j
      with j ≟f i
    ... | yes refl
      rewrite lookup∘update i (mk-alts rG₀G₁) (lookup (sorts α) i ·· G₂)
              | lookup∘update i (mk-alts rGG') (lookup (sorts α) i ·· nG)
              = rG₂Gn
    ... | no pf
      rewrite lookup∘update′ pf (mk-alts rG₀G₁) (lookup (sorts α) i ·· G₂)
              | lookup∘tabulate (mk-alt rG₀G₁) j
              | lookup∘update′ pf (mk-alts rGG') (lookup (sorts α) i ·· nG)
              | lookup∘tabulate (mk-alt rGG') j
              = let G₁' , rG₀G₁' = step/alt rG₀G₁ j
                    G'' , rGG'' = step/alt rGG' j
                    _ , r₀ , r₁
                      = diamond rG₀G rG₀G₁' (⋔sym ii)
                    eq = step/det r₀ rGG''
              in subst (λ G → G₁' -< α' >-> G) eq r₁

    stepback/ch : ∀ {α α' G₀ G₁ G G' G₂ nG}
      (ii : (proj₁ α) ⋔ (proj₁ α'))
      (rG₀G₁  : G₀ -< α >-> G₁)
      (rG₀G   : G₀ -< α' >-> G) -- because we need to know where 'G' comes from
      (rGG'   : G -< α >-> G')
      (rG₂Gn  : G₂ -< α' >-> nG) -- Because we need to know what G₂ reduces to
      → mk-branches rG₀G₁ G₂ =< α' >=>ᵣ mk-branches rGG' nG
    stepback/ch {α = α}{G₂ = G₂}{nG = nG} ii rG₀G₁ rG₀G rGG' rG₂Gn
      = step/conts (stepback/sorts G₂ nG rG₀G₁ rGG')
                   (stepback/cont ii rG₀G₁ rG₀G rGG' rG₂Gn)

  private
    mk-branches/step : ∀ { α α' G₀ G₁ G₂ Ch }
      (ii : (proj₁ α) ⋔ (proj₁ α'))
      (r : G₀ -< α >-> G₁)
      (b   : G₁ ~ G₂)
      (k : mk-branches r G₂ =< α' >=>ᵣ Ch)
      → ∀ i → ∃[ Gi ] proj₁ (step/alt r i) -< α' >-> Gi
    mk-branches/step {α = α}{G₂ = G₂} ii r b k j with step/choice/cont j k
    ... | rk with j ≟f proj₂ α
    ... | yes refl
      rewrite lookup∘update (proj₂ α) (mk-alts r)
                            (lookup (α-sorts α) (proj₂ α) ·· G₂)
      | step/det (proj₂ (step/alt r (proj₂ α))) r
        = let _ , rb , bb = ~R b rk
          in _ , rb
    ... | no ne
      rewrite lookup∘update′ ne (mk-alts r)
                             (lookup (α-sorts α) (proj₂ α) ·· G₂)
      | lookup∘tabulate (mk-alt r) j
      = _ , rk

    record diamond-~ α α' G0 G1 G2 : Set where
      constructor mk-dia-~
      field
        d~-G3 : Global 0 ng
        d~-Gf : Global 0 ng
        d~-Gn : Global 0 ng
        d~-r03 : G0 -< α' >-> d~-G3
        d~-r3f : d~-G3 -< α >-> d~-Gf
        d~-r1f : G1 -< α' >-> d~-Gf
        d~-r2n : G2 -< α' >-> d~-Gn
        d~-f~n : d~-Gf ~ d~-Gn

    mk-branches/swap : ∀ { α α' G₀ G₁ G₂ Ch }
      (ii : (proj₁ α) ⋔ (proj₁ α'))
      (r : G₀ -< α >-> G₁)
      (b   : G₁ ~ G₂)
      (k : mk-branches r G₂ =< α' >=>ᵣ Ch)
      → diamond-~ α α' G₀ G₁ G₂
    mk-branches/swap ii r b k
      = let ki = mk-branches/step ii r b k
            G3 , rr = swap-act ii r ki
            nG , r0 , r1 = diamond r rr ii
            nG' , r2 , bb = ~L b r0
        in mk-dia-~ G3 nG nG' rr r1 r0 r2 bb

    lookup-≡ : ∀{I}{V V' : Vec (Choice 0) I} →
      (∀ i → lookup V i ≡ lookup V' i) → V ≡ V'
    lookup-≡ {_} {[]} {[]} f = refl
    lookup-≡ {_} {x ∷ V} {x₁ ∷ V'} f rewrite f zero
      = cong (_ ∷_) (lookup-≡ (λ i → f (suc i)))

    step-alt/◇ : ∀ {α α' G₀ G₁ G₂}
      → ∀ (ii : (proj₁ α) ⋔ (proj₁ α'))
      → ∀ (r : G₀ -< α >-> G₁) (r' : G₀ -< α' >-> G₂) i
      → proj₁ (step/alt (diamond r r' ii .proj₂ .proj₂) i)
        ≡ proj₁ (diamond (step/alt r i .proj₂) r' ii)
    step-alt/◇ ii r r' i
      with diamond (step/alt r i .proj₂) r' ii | diamond r r' ii
    ... | G' , r₀ , r₁ | G'' , r₂ , r₃ with step/alt r₃ i
    ... | Gf , r₄
      = step/det r₄ r₁

    open diamond-~
    mk-branches/swap/st : ∀ { α α' G₀ G₁ G₂ Ch }
      → ∀ (ii : (proj₁ α) ⋔ (proj₁ α')) (r : G₀ -< α >-> G₁) (b   : G₁ ~ G₂)
      → ∀ (k : mk-branches r G₂ =< α' >=>ᵣ Ch) i
      → lookup Ch i
      ≡ lookup (mk-branches (mk-branches/swap ii r b k .d~-r3f)
                            (mk-branches/swap ii r b k .d~-Gn)) i
    mk-branches/swap/st {α = α}{G₂ = G₂} ii r b k i
      with step/choice/sort i k | step/choice/cont i k | i  ≟f proj₂ α
    ... | sts | str | yes refl
      rewrite lookup∘update i (mk-alts (mk-branches/swap ii r b k .d~-r3f))
                (lookup (α-sorts α) i ·· mk-branches/swap ii r b k .d~-Gn)
      | lookup∘update i (mk-alts r) (lookup (α-sorts α) i ·· G₂)
        = let r2n = mk-branches/swap ii r b k .d~-r2n
          in cong₂ _··_ (sym sts) (step/det str r2n)
    ... | sts | str | no ne
      rewrite lookup∘update′ ne (mk-alts (mk-branches/swap ii r b k .d~-r3f))
                (lookup (α-sorts α) (α .proj₂)
                ·· mk-branches/swap ii r b k .d~-Gn)
      | lookup∘update′ ne (mk-alts r) (lookup (α-sorts α) (α .proj₂) ·· G₂)
      | lookup∘tabulate (mk-alt (mk-branches/swap ii r b k .d~-r3f)) i
      | lookup∘tabulate (mk-alt r) i
      | step-alt/◇ ii r (swap-act ii r (mk-branches/step ii r b k) .proj₂) i
      =
        let _ , ir = swap-act ii r (mk-branches/step ii r b k)
            _ , r₀ , r₁ = diamond (step/alt r i .proj₂) ir ii
        in
        cong₂ _··_ (sym sts) (step/det str r₀)

    mk-branches/swap/steps : ∀ { α α' G₀ G₁ G₂ Ch }
      (ii : (proj₁ α) ⋔ (proj₁ α'))
      (r : G₀ -< α >-> G₁)
      (b   : G₁ ~ G₂)
      (k : mk-branches r G₂ =< α' >=>ᵣ Ch)
      → Ch ≡ mk-branches (mk-branches/swap ii r b k .d~-r3f)
                         (mk-branches/swap ii r b k .d~-Gn)
    mk-branches/swap/steps ii r b k = lookup-≡ (mk-branches/swap/st ii r b k)

    stepback/~ : ∀ {α} (s≢r : False (sender α ≟f receiver α))
      → ∀ {G₀ G₁ G₂} (b : G₁ ~ G₂) (r : G₀ -< α >-> G₁)
      → G₀ ~ stepback s≢r r G₂
    stepback/~ {α = α , i} s≢r b r .~L {α = α' , j} r' with indep? r r'
    stepback/~ {α = α , i} s≢r b r .~L {α = α' , j} r' | inj₂ refl with j ≟f i
    stepback/~ {α = α , i} s≢r b r .~L {α = α' , j} r' | inj₂ refl | yes refl
      with step/det  r' r
    ... | refl = _ , stepback/α s≢r r _ , b
    stepback/~ {α = α , i} s≢r b r .~L {α = α' , j} r' | inj₂ refl | no pf
      = _ , stepback/α' s≢r r r' _ pf , ~refl
    stepback/~ {α = α} s≢r b rG₀G₁ .~L {α = α'} rG₀G | inj₁ ii
      = let G' , rG₁G' , rGG' = diamond rG₀G₁ rG₀G ii
            _ ,  rG₂Gn , Gn~G' = ~L b rG₁G'
        in _ , step/tl/I ii (stepback/ch ii rG₀G₁ rG₀G rGG' rG₂Gn)
           , stepback/~ {α = α} s≢r Gn~G' rGG'

    -- Other direction
    stepback/~ {α = α , i} s≢r b r .~R {α = α' , j} (step/i .j) with j ≟f i
    stepback/~ {α = α , i} s≢r {G₂ = G₂} b r .~R {α = α' , j} (step/i .j)
      | yes refl rewrite lookup∘update i (mk-alts r) (lookup (sorts α) i ·· G₂)
                 | sorts/tabulate r G₂
      = _ , r , b
    stepback/~ {α = α , i} s≢r {G₂ = G₂} b r .~R {α = α' , j} (step/i .j)
      | no ne rewrite lookup∘update′ ne (mk-alts r) (lookup (sorts α) i ·· G₂)
                      | sorts/tabulate r G₂
                      | lookup∘tabulate (mk-alt r) j
      = _ , proj₂ (step/alt r j) , ~refl
    stepback/~ {α = α} s≢r {G₂ = G₂} b r .~R {α = α'} (step/tl/I ii k)
      rewrite mk-branches/swap/steps ii r b k
      = _ , mk-branches/swap ii r b k .d~-r03
        , stepback/~ s≢r (mk-branches/swap ii r b k .d~-f~n)
                         (mk-branches/swap ii r b k .d~-r3f)

    -- NOTE: in a future where [G -< p , i >-> G'] may not impose the WF
    -- condition that all other alternatives [p , j] are possible in [G], we
    -- may rewrite the code below by querying [G] which are the cases [p , j]
    -- that it accepts. It should always possible to get a vector of supported
    -- communication labels at a particular state, for a particular pair of
    -- participants
    ~/stepback : ∀ {α G0 G1 G1'}
      → G1 ~ G1' → G0 -< α >-> G1 → ∃[ G0' ] (G0 ~ G0') × (G0' -< α >-> G1')
    ~/stepback b gr
      = _ , ((stepback/~ (snd≢rcv gr) b gr) , (stepback/α (snd≢rcv gr) gr _))

  S∉-indep : {G : Behav} {α α' : Action} {G' G'' : Behav} →
           G -< α >-> G' → G -< α' >-> G'' → sender α' ∉α α → α ∥ α'
  S∉-indep {_}{α}{α'} gr1 gr2 f with receiver α' ∈α? α
  S∉-indep {_}{α}{α'} gr1 gr2 f | yes pr with recv∈α/≡act gr2 gr1 pr
  ... | refl = ⊥-elim (f (∈S refl))
  S∉-indep {_}{α}{α'} gr1 gr2 f | no ¬pr
    = ii-disj λ{ (inj₁ (∈S refl)) → f (∈S refl)
               ; (inj₁ (∈R refl)) → ¬pr (∈S refl)
               ; (inj₂ (∈S refl)) → f (∈R refl)
               ; (inj₂ (∈R refl)) → ¬pr (∈R refl) }

  GT-Properties : BT-Prop GlobalTypes
  GT-Properties .BT-Prop.recv-act-eq = recv∈α/≡act
  GT-Properties .BT-Prop.snd≢rcv = λ x → toWitnessFalse (snd≢rcv x)
  GT-Properties .BT-Prop.step-det = step/det
  GT-Properties .BT-Prop.~stepback = ~/stepback
  GT-Properties .BT-Prop.diamond = the-diamond
  GT-Properties .BT-Prop.cond-comm = no-phantom-comm
