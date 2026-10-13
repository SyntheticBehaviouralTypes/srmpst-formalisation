{-# OPTIONS --guardedness #-}

-- A recursive two-buyer protocol: `A` asks seller `S` for an item, `S`
-- multicasts the price to both buyers, then `A` repeatedly cancels or
-- proposes a split to `B`, who answers `yes` (`A` buys) or `no` (back to
-- the proposal).  All five partitions are accepted.

module Examples.Rec2Buy where

open import Definitions.Expr.Syntax
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

open import Definitions.Graph.Algebra 3 hiding (var)
open import Utils.SetLit using (⁅_⁆; _；_)
open import Definitions.Actions 3
open import Definitions.Proc 3 hiding (rec; _⇐_？·_)
open import Definitions.Proc.Syntax 3
open import Utils.Branch using (⟪_⟫; _↦_; _∣_)

A B S : Fin 3
A = 0F
B = 1F
S = 2F

item price : Fin 1
item  = 0F
price = 0F

-- `A` to `B`: propose a split, or cancel
split cancel : Fin 2
split  = 0F
cancel = 1F

-- `B` to `A`: accept the split, or not
yes no : Fin 2
yes = 0F
no  = 1F

-- `A` to `S`: buy, or quit
buy quit : Fin 2
buy  = 0F
quit = 1F

-- `A` asks for an item, `S` quotes both buyers, then `A` proposes splits
-- until `B` says `yes` (then `A` buys) or `A` cancels (then quits); a `no`
-- from `B` loops.
rec2buy : OpenGraph 0
rec2buy =
  A ⟶ ⁅ S ⁆ # item < s/nat > ∙
  S ⟶ ⁅ A ； B ⁆ # price < s/nat > ∙
  μ X ·
    ⟪ A ⟶ ⁅ B ⁆ # split < s/nat >   ∙
        ⟪ B ⟶ ⁅ A ⁆ # yes < s/nat > ∙ A ⟶ ⁅ S ⁆ # buy < s/unit > ∙ end
        ∣ B ⟶ ⁅ A ⁆ # no < s/unit > ∙ X
        ⟫
    ∣ A ⟶ ⁅ B ⁆ # cancel < s/unit > ∙ A ⟶ ⁅ S ⁆ # quit < s/unit > ∙ end
    ⟫

wbg : WBGraph {N = 3}
wbg = buildG rec2buy

s₀ = initial (proj₁ wbg)

open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_; safety; module Global)

p/A : Proc 0 0
p/A =
  A ⇒ ⁅ S ⁆ ! item < 0 >∙
  A ⇐ S ？·
    ⟪ price ⟨ amount ⟩ ↦
        rec X ·
          ifp is-zero amount
          then A ⇒ ⁅ B ⁆ ! split < 0 >∙
               A ⇐ B ？·
                 ⟪ yes ↦ A ⇒ ⁅ S ⁆ ! buy < unit >∙ ∅
                 ∣ no  ↦ X
                 ⟫
          else A ⇒ ⁅ B ⁆ ! cancel < unit >∙
               A ⇒ ⁅ S ⁆ ! quit < unit >∙ ∅
    ⟫

-- `B` hears the price before judging each `share` it is offered (but
-- expressions cannot compare the two, so the price goes unused).
p/B : Proc 0 0
p/B =
  B ⇐ S ？·
    ⟪ price ↦
        rec X ·
          B ⇐ A ？·
            ⟪ split ⟨ share ⟩ ↦ ifp is-zero share
                                then B ⇒ ⁅ A ⁆ ! yes < 0 >∙ ∅
                                else B ⇒ ⁅ A ⁆ ! no < unit >∙ X
            ∣ cancel          ↦ ∅
            ⟫
    ⟫

p/S : Proc 0 0
p/S =
  S ⇐ A ？·
    ⟪ item ↦ S ⇒ ⁅ A ； B ⁆ ! price < 0 >∙
             S ⇐ A ？· ⟪ buy ↦ ∅ ∣ quit ↦ ∅ ⟫
    ⟫

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
-- two final sends to `S` (here: `quit`, after an internal cancel).
module AB∣S where
  Ρ = byOwner own/AB∣S
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = A ⇒ ⁅ S ⁆ ! item < 0 >∙
        A ⇐ S ？· ⟪ price ↦ A ⇒ ⁅ S ⁆ ! quit < unit >∙ ∅ ⟫
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
  M = S ⇒ ⁅ A ； B ⁆ ! price < 0 >∙
        A ⇒ ⁅ B ⁆ ! cancel < unit >∙ ∅
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
    v∷ S ⇐ A ？·
         ⟪ item ↦
             S ⇒ ⁅ A ； B ⁆ ! price < 0 >∙
             B ⇐ A ？·
               ⟪ split  ↦ B ⇒ ⁅ A ⁆ ! yes < 0 >∙
                          S ⇐ A ？· ⟪ buy ↦ ∅ ∣ quit ↦ ∅ ⟫
               ∣ cancel ↦ S ⇐ A ？· ⟪ buy ↦ ∅ ∣ quit ↦ ∅ ⟫
               ⟫
         ⟫
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
