{-# OPTIONS --guardedness #-}

-- A recursive two-buyer protocol: `A` gets a price from seller `S`, then
-- repeatedly cancels or proposes a split to `B`, who answers `yes` (`A`
-- buys) or `no` (back to the proposal).  All five partitions are accepted.

module Examples.Rec2Buy where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_; proj₁; ∃-syntax; _×_)
open import Data.List using (length)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr
  using (s/nat; s/unit; val; v/nat; v/unit; is-zero; var)
open import Check

open import Definitions.Graph.Algebra 3 hiding (var)
open import Data.Fin.Subset using (⁅_⁆)
open import Definitions.Actions 3 renaming (_<_> to mkChoice)
open import Definitions.Proc 3

A B S : Fin 3
A = zero
B = suc zero
S = suc (suc zero)

here : Fin 1
here = zero

lbl0 lbl1 : Fin 2
lbl0 = zero
lbl1 = suc zero

private
  -- state references (`Ref 0 6`)
  t0 t1 t2 t3 t4 t5 : Ref 0 6
  t0 = node zero
  t1 = node (suc zero)
  t2 = node (suc (suc zero))
  t3 = node (suc (suc (suc zero)))
  t4 = node (suc (suc (suc (suc zero))))
  t5 = node (suc (suc (suc (suc (suc zero)))))

-- s0 --A→S item(nat)--> s1 --S→A price(nat)--> s2
-- s2 --A→B split(nat)--> s4 | --A→B cancel(unit)--> s3
-- s4 --B→A yes(nat)--> s5   | --B→A no(unit)-----> s2   (the loop)
-- s3 --A→S no(unit)--> ended;  s5 --A→S buy(unit)--> ended
rec2buy : OpenGraph 0
rec2buy = openGraph 6 (node zero)
  (  ( ((A ⟶ ⁅ S ⁆ # mkChoice here s/nat) , t1) ∷ [] )                    -- s0
  v∷ ( ((S ⟶ ⁅ A ⁆ # mkChoice here s/nat) , t2) ∷ [] )                    -- s1
  v∷ ( ((A ⟶ ⁅ B ⁆ # mkChoice lbl0 s/nat) , t4)                           -- s2: split
     ∷ ((A ⟶ ⁅ B ⁆ # mkChoice lbl1 s/unit) , t3)                          --     cancel
     ∷ [] )
  v∷ ( ((A ⟶ ⁅ S ⁆ # mkChoice lbl1 s/unit) , ended) ∷ [] )                 -- s3: no-s
  v∷ ( ((B ⟶ ⁅ A ⁆ # mkChoice lbl0 s/nat) , t5)                           -- s4: yes
     ∷ ((B ⟶ ⁅ A ⁆ # mkChoice lbl1 s/unit) , t2)                          --     no (loop)
     ∷ [] )
  v∷ ( ((A ⟶ ⁅ S ⁆ # mkChoice lbl0 s/unit) , ended) ∷ [] )                 -- s5: buy
  v∷ v[]
  )

wbg : WBGraph {N = 3}
wbg = buildG rec2buy {p = tt}

s₀ = initial (proj₁ wbg)

open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_; safety; module Global)

p/A : Proc 0 0
p/A =
  A ⇒ ⁅ S ⁆ ! here < val (v/nat 0) >∙
  (A ⇐ S ？·
    ( rec (ifp is-zero (var zero)
           then (A ⇒ ⁅ B ⁆ ! lbl0 < val (v/nat 0) >∙
                 (A ⇐ B ？·
                   (  (A ⇒ ⁅ S ⁆ ! lbl0 < val v/unit >∙ ∅)
                   v∷ v zero
                   v∷ v[])))
           else (A ⇒ ⁅ B ⁆ ! lbl1 < val v/unit >∙
                 (A ⇒ ⁅ S ⁆ ! lbl1 < val v/unit >∙ ∅)))
    v∷ v[]))

p/B : Proc 0 0
p/B =
  rec (B ⇐ A ？·
        (  (ifp is-zero (var zero)
            then (B ⇒ ⁅ A ⁆ ! lbl0 < val (v/nat 0) >∙ ∅)
            else (B ⇒ ⁅ A ⁆ ! lbl1 < val v/unit >∙ v zero))
        v∷ ∅
        v∷ v[]))

p/S : Proc 0 0
p/S =
  S ⇐ A ？·
    (  (S ⇒ ⁅ A ⁆ ! here < val (v/nat 0) >∙
        (S ⇐ A ？· (∅ v∷ ∅ v∷ v[])))
    v∷ v[])

-- {A} {B} {S}: one process per role.
module A∣B∣S where
  Ρ = singletons
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = p/A v∷ p/B v∷ p/S v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- ── Every other partition: each process against its block's view ───────

own/AB∣S own/AS∣B own/A∣BS : Fin 3 → Fin 2
own/AB∣S zero             = zero
own/AB∣S (suc zero)       = zero
own/AB∣S (suc (suc zero)) = suc zero
own/AS∣B zero             = zero
own/AS∣B (suc zero)       = suc zero
own/AS∣B (suc (suc zero)) = zero
own/A∣BS zero             = zero
own/A∣BS (suc zero)       = suc zero
own/A∣BS (suc (suc zero)) = suc zero

-- {A,B} {S}: the split/no loop is an internal cycle; its exits are the
-- two final sends to `S` (here: `no`, after an internal cancel).
module AB∣S where
  Ρ = byOwner own/AB∣S
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = (A ⇒ ⁅ S ⁆ ! here < val (v/nat 0) >∙
         (A ⇐ S ？· ((A ⇒ ⁅ S ⁆ ! lbl1 < val v/unit >∙ ∅) v∷ v[])))
    v∷ p/S
    v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- {A,S} {B}: item and price are internal; the block cancels.
module AS∣B where
  Ρ = byOwner own/AS∣B
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = (A ⇒ ⁅ B ⁆ ! lbl1 < val v/unit >∙ ∅) v∷ p/B v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- {A} {B,S}: `B` and `S` never talk; the one process interleaves them, one
-- role at a time (`S` quotes, `B` answers `yes`, `S` hears `buy`).
module A∣BS where
  Ρ = byOwner own/A∣BS
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = p/A
    v∷ (S ⇐ A ？·
         (  (S ⇒ ⁅ A ⁆ ! here < val (v/nat 0) >∙
             (B ⇐ A ？·
               (  (B ⇒ ⁅ A ⁆ ! lbl0 < val (v/nat 0) >∙ (S ⇐ A ？· (∅ v∷ ∅ v∷ v[])))
               v∷ (S ⇐ A ？· (∅ v∷ ∅ v∷ v[]))
               v∷ v[])))
         v∷ v[]))
    v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- {A,B,S}: everything is internal.
module ABS where
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
