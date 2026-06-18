{-# OPTIONS --guardedness #-}

-- Server `S` offers `login`/`cancel` to client `C`; on `login`, `C`
-- forwards a password to the auth service `A`, which reports to `S`; on
-- `cancel`, `C` tells `A` to quit.  All five partitions are accepted.

module Examples.OAuth2 where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_; proj₁; ∃-syntax; _×_)
open import Data.List using (length)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Unit using (tt)
open import Data.Bool using (true)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr using (s/bool; s/nat; val; v/bool; v/nat)
open import Check

open import Definitions.Graph.Algebra 3
open import Data.Fin.Subset using (⁅_⁆)
open import Definitions.Actions 3 renaming (_<_> to mkChoice)
open import Definitions.Proc 3

S C A : Fin 3
S = zero
C = suc zero
A = suc (suc zero)

here : Fin 1
here = zero

-- the S→C choice: login/cancel (both carry a nat)
login cancel : Fin 2
login  = zero
cancel = suc zero

-- the C→A choice: passwd (nat) / quit (bool)
passwd quit : Fin 2
passwd = zero
quit   = suc zero

-- s0 --S→C[login]--> s1 --C→A[passwd]--> s2 --A→S[auth]--> ended
-- s0 --S→C[cancel]--> s3 --C→A[quit]----------------------> ended
oauth : OpenGraph 0
oauth = openGraph 4 (node zero)
  ( ( ((S ⟶ ⁅ C ⁆ # mkChoice login s/nat) , node (suc zero))
    ∷ ((S ⟶ ⁅ C ⁆ # mkChoice cancel s/nat) , node (suc (suc (suc zero))))
    ∷ [] )                                                            -- s0
  v∷ ( ((C ⟶ ⁅ A ⁆ # mkChoice passwd s/nat) , node (suc (suc zero)))
     ∷ [] )                                                           -- s1
  v∷ ( ((A ⟶ ⁅ S ⁆ # mkChoice here s/bool) , ended) ∷ [] )             -- s2
  v∷ ( ((C ⟶ ⁅ A ⁆ # mkChoice quit s/bool) , ended) ∷ [] )             -- s3
  v∷ v[]
  )

wbg : WBGraph {N = 3}
wbg = buildG oauth {p = tt}

s₀ = initial (proj₁ wbg)

open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_; safety; module Global)

-- the server picks `cancel`
p/S : Proc 0 0
p/S = S ⇒ ⁅ C ⁆ ! cancel < val (v/nat 0) >∙ ∅

-- the client covers both offers: forward the password, or tell `A` to quit
p/C : Proc 0 0
p/C = C ⇐ S ？·
        (  (C ⇒ ⁅ A ⁆ ! passwd < val (v/nat 0) >∙ ∅)
        v∷ (C ⇒ ⁅ A ⁆ ! quit < val (v/bool true) >∙ ∅)
        v∷ v[])

-- the auth service: authorize towards `S`, or stop
p/A : Proc 0 0
p/A = A ⇐ C ？·
        (  (A ⇒ ⁅ S ⁆ ! here < val (v/bool true) >∙ ∅)
        v∷ ∅
        v∷ v[])

-- {S} {C} {A}: one process per role.
module S∣C∣A where
  Ρ = singletons
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = p/S v∷ p/C v∷ p/A v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- ── Every other partition: each process against its block's view ───────

own/SC∣A own/SA∣C own/S∣CA : Fin 3 → Fin 2
own/SC∣A zero             = zero
own/SC∣A (suc zero)       = zero
own/SC∣A (suc (suc zero)) = suc zero
own/SA∣C zero             = zero
own/SA∣C (suc zero)       = suc zero
own/SA∣C (suc (suc zero)) = zero
own/S∣CA zero             = zero
own/S∣CA (suc zero)       = suc zero
own/S∣CA (suc (suc zero)) = suc zero

-- {S,C} {A}: the server's choice is internal; the client's forward to `A`
-- makes it (here: `login`, then `A`'s report reaches `S`).
module SC∣A where
  Ρ = byOwner own/SC∣A
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = (C ⇒ ⁅ A ⁆ ! passwd < val (v/nat 0) >∙ (S ⇐ A ？· (∅ v∷ v[]))) v∷ p/A v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- {S,A} {C}: `A→S` is internal.  The server cancels; `A` hears `quit`.
module SA∣C where
  Ρ = byOwner own/SA∣C
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = (S ⇒ ⁅ C ⁆ ! cancel < val (v/nat 0) >∙ (A ⇐ C ？· (∅ v∷ ∅ v∷ v[]))) v∷ p/C v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- {S} {C,A}: `C→A` is internal; on `login` the block reports to `S`.
module S∣CA where
  Ρ = byOwner own/S∣CA
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = p/S v∷ (C ⇐ S ？· ((A ⇒ ⁅ S ⁆ ! here < val (v/bool true) >∙ ∅) v∷ ∅ v∷ v[])) v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- {S,C,A}: everything is internal.
module SCA where
  Ρ : Assignment 1
  Ρ = byOwner λ _ → zero
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = ∅ v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed
