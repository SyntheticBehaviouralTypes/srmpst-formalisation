{-# OPTIONS --guardedness #-}

-- A recursive two-buyer protocol: `A` asks seller `S` for an item, `S`
-- multicasts the price to both buyers, then `A` repeatedly cancels or
-- proposes a split to `B`, who answers `yes` (`A` buys) or `no` (back to
-- the proposal).  All five partitions are accepted.

module Examples.Rec2Buy where

open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_; proj₁; ∃-syntax; _×_)
open import Data.List using (length)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (from-yes)

open import Definitions.Expr
  using (s/nat; s/unit; val; v/nat; v/unit; is-zero; var)
open import Check

open import Definitions.Graph.Algebra 3 renaming (var to gvar)
open import Utils.SetLit using (⁅_⁆; _；_)
open import Definitions.Actions 3 renaming (_<_> to mkChoice)
open import Definitions.Proc 3

A B S : Fin 3
A = 0F
B = 1F
S = 2F

here : Fin 1
here = 0F

lbl0 lbl1 : Fin 2
lbl0 = 0F
lbl1 = 1F

-- A→S item(nat) . S→{A,B} price(nat) .
-- μ (  A→B split(nat)  . (B→A yes(nat) . A→S buy(unit) . end
--                        + B→A no(unit) . loop)
--    + A→B cancel(unit) . A→S no(unit) . end )
rec2buy : OpenGraph 0
rec2buy =
  (A ⟶ ⁅ S ⁆ # mkChoice here s/nat) ∙
  (S ⟶ ⁅ A ； B ⁆ # mkChoice here s/nat) ∙
  μ (choice
      ((A ⟶ ⁅ B ⁆ # mkChoice lbl0 s/nat) ⇒
        choice
          ((B ⟶ ⁅ A ⁆ # mkChoice lbl0 s/nat) ⇒
            ((A ⟶ ⁅ S ⁆ # mkChoice lbl0 s/unit) ∙ end))
          ( ((B ⟶ ⁅ A ⁆ # mkChoice lbl1 s/unit) ⇒ gvar 0F)
          ∷ []))
      ( ((A ⟶ ⁅ B ⁆ # mkChoice lbl1 s/unit) ⇒
          ((A ⟶ ⁅ S ⁆ # mkChoice lbl1 s/unit) ∙ end))
      ∷ []))

wbg : WBGraph {N = 3}
wbg = buildG rec2buy {p = tt}

s₀ = initial (proj₁ wbg)

open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_; safety; module Global)

p/A : Proc 0 0
p/A =
  A ⇒ ⁅ S ⁆ ! here < val (v/nat 0) >∙
  (A ⇐ S ？·
    ( rec (ifp is-zero (var 0F)
           then (A ⇒ ⁅ B ⁆ ! lbl0 < val (v/nat 0) >∙
                 (A ⇐ B ？·
                   (  (A ⇒ ⁅ S ⁆ ! lbl0 < val v/unit >∙ ∅)
                   v∷ v 0F
                   v∷ v[])))
           else (A ⇒ ⁅ B ⁆ ! lbl1 < val v/unit >∙
                 (A ⇒ ⁅ S ⁆ ! lbl1 < val v/unit >∙ ∅)))
    v∷ v[]))

-- `B` hears the price (`var 1F` in the loop) before judging a split
-- (`var 0F`).
p/B : Proc 0 0
p/B =
  B ⇐ S ？·
    (  rec (B ⇐ A ？·
             (  (ifp is-zero (var 0F)
                 then (B ⇒ ⁅ A ⁆ ! lbl0 < val (v/nat 0) >∙ ∅)
                 else (B ⇒ ⁅ A ⁆ ! lbl1 < val v/unit >∙ v 0F))
             v∷ ∅
             v∷ v[]))
    v∷ v[])

p/S : Proc 0 0
p/S =
  S ⇐ A ？·
    (  (S ⇒ ⁅ A ； B ⁆ ! here < val (v/nat 0) >∙
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
  M-typed = from-yes (typecheckSession wbg Ρ M)

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- ── Every other partition: each process against its block's view ───────

own/AB∣S own/AS∣B own/A∣BS : Fin 3 → Fin 2
own/AB∣S 0F = 0F
own/AB∣S 1F = 0F
own/AB∣S 2F = 1F
own/AS∣B 0F = 0F
own/AS∣B 1F = 1F
own/AS∣B 2F = 0F
own/A∣BS 0F = 0F
own/A∣BS 1F = 1F
own/A∣BS 2F = 1F

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
  M-typed = from-yes (typecheckSession wbg Ρ M)

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- {A,S} {B}: the item is internal; the block multicasts the price (`B`
-- is the only outsider who hears it), then cancels.
module AS∣B where
  Ρ = byOwner own/AS∣B
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = (S ⇒ ⁅ A ； B ⁆ ! here < val (v/nat 0) >∙
         (A ⇒ ⁅ B ⁆ ! lbl1 < val v/unit >∙ ∅))
    v∷ p/B
    v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = from-yes (typecheckSession wbg Ρ M)

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- {A} {B,S}: `B` and `S` never talk; the one process interleaves them, one
-- role at a time (`S` quotes to `A` and its own `B`, `B` answers `yes`,
-- `S` hears `buy`).
module A∣BS where
  Ρ = byOwner own/A∣BS
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = p/A
    v∷ (S ⇐ A ？·
         (  (S ⇒ ⁅ A ； B ⁆ ! here < val (v/nat 0) >∙
             (B ⇐ A ？·
               (  (B ⇒ ⁅ A ⁆ ! lbl0 < val (v/nat 0) >∙ (S ⇐ A ？· (∅ v∷ ∅ v∷ v[])))
               v∷ (S ⇐ A ？· (∅ v∷ ∅ v∷ v[]))
               v∷ v[])))
         v∷ v[]))
    v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = from-yes (typecheckSession wbg Ρ M)

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- {A,B,S}: everything is internal.
module ABS where
  Ρ : Assignment 1
  Ρ = byOwner λ _ → 0F
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = ∅ v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = from-yes (typecheckSession wbg Ρ M)

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed
