{-# OPTIONS --guardedness #-}

-- A recursive master/workers protocol: `M` sends to `W1` then `W2`, the
-- workers report to `R`, and `R` tells `M` to loop or stop.  Of the 15
-- partitions, nine are accepted; those with a block among {M,R}, {M,W1},
-- {R,W2}, {W1,W2} are rejected by `Focus` (`M→W2` races `W1→R`).

module Examples.RecMW where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Sum using (_⊎_)
open import Data.Product using (proj₁; ∃-syntax; _×_)
open import Data.List using (length)
open import Data.Unit using (tt)
open import Data.Bool using (true; false)
import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness; does)

open import Definitions.Expr
  using (s/bool; s/nat; val; v/nat; v/bool; is-zero; var)
open import Check hiding (base; _∥_; _⨾_)

open import Definitions.Graph.Algebra 4 renaming (var to gvar)
open import Data.Fin.Subset using (⁅_⁆)
open import Definitions.Actions 4 renaming (_<_> to mkChoice)
open import Definitions.Proc 4

M R W1 W2 : Fin 4
M  = zero
R  = suc zero
W1 = suc (suc zero)
W2 = suc (suc (suc zero))

here : Fin 1
here = zero

-- M→W datum/stop ([nat, bool]); R→M continue/stop ([nat, bool])
lbl0 lbl1 : Fin 2
lbl0 = zero
lbl1 = suc zero

-- One round: `M→W1`, then `M→W2 ∥ W1→R`, then `W2→R`; `R` loops or stops.
recmw : OpenGraph 0
recmw =
  μ ( (M ⟶ ⁅ W1 ⁆ # mkChoice lbl0 s/nat) ∙
      (   ((M ⟶ ⁅ W2 ⁆ # mkChoice lbl0 s/nat) ∙ end)
        ∥ ((W1 ⟶ ⁅ R ⁆ # mkChoice here s/nat) ∙ end)
      ⨾ (W2 ⟶ ⁅ R ⁆ # mkChoice here s/nat) ∙
        choice ((R ⟶ ⁅ M ⁆ # mkChoice lbl0 s/nat) ⇒ gvar zero)
               ( ((R ⟶ ⁅ M ⁆ # mkChoice lbl1 s/bool) ⇒
                   ((M ⟶ ⁅ W1 ⁆ # mkChoice lbl1 s/bool) ∙
                    (M ⟶ ⁅ W2 ⁆ # mkChoice lbl1 s/bool) ∙ end))
               ∷ []) ) )

wbg : WBGraph {N = 4}
wbg = buildG recmw {p = tt}

s₀ = initial (proj₁ wbg)

open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_; safety; module Global)

-- ── One process per role ──────────────────────────────────────────────

p/M : Proc 0 0
p/M = rec (M ⇒ ⁅ W1 ⁆ ! lbl0 < val (v/nat 0) >∙
          (M ⇒ ⁅ W2 ⁆ ! lbl0 < val (v/nat 1) >∙
          (M ⇐ R ？·
            (  v zero
            v∷ (M ⇒ ⁅ W1 ⁆ ! lbl1 < val (v/bool false) >∙
                (M ⇒ ⁅ W2 ⁆ ! lbl1 < val (v/bool false) >∙ ∅))
            v∷ v[]))))

p/R : Proc 0 0
p/R = rec (R ⇐ W1 ？·
            (  (R ⇐ W2 ？·
                 (  (ifp is-zero (var zero)
                     then (R ⇒ ⁅ M ⁆ ! lbl1 < val (v/bool true) >∙ ∅)
                     else (R ⇒ ⁅ M ⁆ ! lbl0 < var (suc zero) >∙ v zero))
                 v∷ v[]))
            v∷ v[]))

-- both workers run the same shape: receive a datum, then loop reporting to
-- `R` until `M` says stop
p/W : Fin 4 → Proc 0 0
p/W W = W ⇐ M ？·
        (  (rec (W ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙
                 (W ⇐ M ？·
                   (v zero v∷ ∅ v∷ v[]))))
        v∷ ∅
        v∷ v[])

-- {M} {R} {W1} {W2}
-- (Sessions are named `Ms`: `M` is a role.)
module M∣R∣W1∣W2 where
  Ρ = singletons
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  Ms : Session
  Ms = p/M v∷ p/R v∷ p/W W1 v∷ p/W W2 v∷ v[]

  Ms-typed : ⊢s[ Ρ ] Ms ∶ s₀
  Ms-typed = toWitness {a? = typecheckSession wbg Ρ Ms} _

  Ms-safe : ∀ {αs Ms′} → Ms =[ αs ]⇒* Ms′
          → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] Ms′ ∶ G′
                    × (∀ n → ∃[ βs ] ∃[ Ms″ ] Ms′ =[ βs ]⇒* Ms″ × (finished Ms″ ⊎ length βs ≡ n))
  Ms-safe = safety Ρ Ms-typed

-- ══════════════════════════════════════════════════════════════════════
--  Every other partition (14), each process against its block's view
-- ══════════════════════════════════════════════════════════════════════

-- Blocks are numbered in the order of the owner map below; the session
-- lists their processes in that order.

-- ── Codes for blocks of two or three roles ────────────────────────────

-- {M,W1}: `M→W1` is internal; then `M→W2` and `W1→R` are two sends by
-- different own roles, enabled together: `Focus` refuses either order.
mw1₁ mw1₂ : Proc 0 0
mw1₁ = rec (M ⇒ ⁅ W2 ⁆ ! lbl0 < val (v/nat 0) >∙
            (W1 ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙
             (M ⇐ R ？· (v zero v∷ (M ⇒ ⁅ W2 ⁆ ! lbl1 < val (v/bool true) >∙ ∅) v∷ v[]))))
mw1₂ = rec (W1 ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙
            (M ⇒ ⁅ W2 ⁆ ! lbl0 < val (v/nat 0) >∙
             (M ⇐ R ？· (v zero v∷ (M ⇒ ⁅ W2 ⁆ ! lbl1 < val (v/bool true) >∙ ∅) v∷ v[]))))

-- {M,W2}: `M→W2` is internal; `W1→R` is none of its business.
mw2 : Proc 0 0
mw2 = rec (M ⇒ ⁅ W1 ⁆ ! lbl0 < val (v/nat 0) >∙
           (W2 ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙
            (M ⇐ R ？· (v zero v∷ (M ⇒ ⁅ W1 ⁆ ! lbl1 < val (v/bool true) >∙ ∅) v∷ v[]))))

-- {R,W1}: `W1→R` is internal; the block always continues.
w1r : Proc 0 0
w1r = rec (W1 ⇐ M ？·
            (  (R ⇐ W2 ？· ((R ⇒ ⁅ M ⁆ ! lbl0 < val (v/nat 0) >∙ v zero) v∷ v[]))
            v∷ ∅
            v∷ v[]))

-- {M,R}: after `M→W1`, `M` may send `M→W2` while `R` may receive `W1→R`:
-- `Focus` refuses either order.  (`R→M` is internal: here, stop.)
mr₁ mr₂ : Proc 0 0
mr₁ = M ⇒ ⁅ W1 ⁆ ! lbl0 < val (v/nat 0) >∙
      (M ⇒ ⁅ W2 ⁆ ! lbl0 < val (v/nat 0) >∙
       (R ⇐ W1 ？· ((R ⇐ W2 ？·
         ((M ⇒ ⁅ W1 ⁆ ! lbl1 < val (v/bool true) >∙
           (M ⇒ ⁅ W2 ⁆ ! lbl1 < val (v/bool true) >∙ ∅)) v∷ v[])) v∷ v[])))
mr₂ = M ⇒ ⁅ W1 ⁆ ! lbl0 < val (v/nat 0) >∙
      (R ⇐ W1 ？· ((M ⇒ ⁅ W2 ⁆ ! lbl0 < val (v/nat 0) >∙
       (R ⇐ W2 ？·
         ((M ⇒ ⁅ W1 ⁆ ! lbl1 < val (v/bool true) >∙
           (M ⇒ ⁅ W2 ⁆ ! lbl1 < val (v/bool true) >∙ ∅)) v∷ v[]))) v∷ v[]))

-- {R,W2}: after `M→W1`, `W2` may receive `M→W2` while `R` may receive
-- `W1→R` (from different senders): `Focus` refuses either order.
rw2₁ rw2₂ : Proc 0 0
rw2₁ = rec (W2 ⇐ M ？·
             (  (R ⇐ W1 ？· ((R ⇒ ⁅ M ⁆ ! lbl0 < val (v/nat 0) >∙ v zero) v∷ v[]))
             v∷ ∅
             v∷ v[]))
rw2₂ = rec (R ⇐ W1 ？·
             (  (W2 ⇐ M ？· ((R ⇒ ⁅ M ⁆ ! lbl0 < val (v/nat 0) >∙ v zero) v∷ ∅ v∷ v[]))
             v∷ v[]))

-- {W1,W2}: after `M→W1`, `W2` may receive `M→W2` while `W1` may send
-- `W1→R`: a mixed choice, refused in either order.
w12₁ w12₂ : Proc 0 0
w12₁ = rec (W1 ⇐ M ？·
             (  (W1 ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙
                  (W2 ⇐ M ？· ((W2 ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙ v zero) v∷ ∅ v∷ v[])))
             v∷ (W2 ⇐ M ？· (∅ v∷ ∅ v∷ v[]))
             v∷ v[]))
w12₂ = rec (W1 ⇐ M ？·
             (  (W2 ⇐ M ？· ((W1 ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙
                               (W2 ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙ v zero))
                             v∷ ∅ v∷ v[]))
             v∷ (W2 ⇐ M ？· (∅ v∷ ∅ v∷ v[]))
             v∷ v[]))

-- {M,R,W1}: `M→W1`, `W1→R`, `R→M` are internal; the block sends `M→W2`,
-- hears `W2→R`, and (internally) stops.
mrw1 : Proc 0 0
mrw1 = M ⇒ ⁅ W2 ⁆ ! lbl0 < val (v/nat 0) >∙
       (R ⇐ W2 ？· ((M ⇒ ⁅ W2 ⁆ ! lbl1 < val (v/bool false) >∙ ∅) v∷ v[]))

-- {M,R,W2}: symmetrically, with `W1` outside.
mrw2 : Proc 0 0
mrw2 = M ⇒ ⁅ W1 ⁆ ! lbl0 < val (v/nat 0) >∙
       (R ⇐ W1 ？· ((M ⇒ ⁅ W1 ⁆ ! lbl1 < val (v/bool false) >∙ ∅) v∷ v[]))

-- {M,W1,W2}: `M`'s sends are internal; the workers report in turn, and the
-- block follows `R`'s decision.
mw12 : Proc 0 0
mw12 = rec (W1 ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙
             (W2 ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙
              (M ⇐ R ？· (v zero v∷ ∅ v∷ v[]))))

-- {R,W1,W2}: the reports are internal; the workers hear `M`, `R` stops.
rw12 : Proc 0 0
rw12 = W1 ⇐ M ？·
         (  (W2 ⇐ M ？·
              (  (R ⇒ ⁅ M ⁆ ! lbl1 < val (v/bool true) >∙
                   (W1 ⇐ M ？· (∅ v∷ (W2 ⇐ M ？· (∅ v∷ ∅ v∷ v[])) v∷ v[])))
              v∷ ∅
              v∷ v[]))
         v∷ ∅
         v∷ v[])

-- ── Owner maps: M, R, W1, W2 ↦ block ──────────────────────────────────

own : ∀ {K} → Fin K → Fin K → Fin K → Fin K → Fin 4 → Fin K
own m r w₁ w₂ zero                   = m
own m r w₁ w₂ (suc zero)             = r
own m r w₁ w₂ (suc (suc zero))       = w₁
own m r w₁ w₂ (suc (suc (suc zero))) = w₂

b0 b1 b2 : ∀ {K} → Fin (3 Data.Nat.+ K)
b0 = zero
b1 = suc zero
b2 = suc (suc zero)

-- ── Two roles together, the others alone ──────────────────────────────

Ρ/MR∣W1∣W2 Ρ/MW1∣R∣W2 Ρ/MW2∣R∣W1 Ρ/RW1∣M∣W2 Ρ/RW2∣M∣W1 Ρ/W1W2∣M∣R : Assignment 3
Ρ/MR∣W1∣W2 = byOwner (own b0 b0 b1 b2)
Ρ/MW1∣R∣W2 = byOwner (own b0 b1 b0 b2)
Ρ/MW2∣R∣W1 = byOwner (own b0 b1 b2 b0)
Ρ/RW1∣M∣W2 = byOwner (own b1 b0 b0 b2)
Ρ/RW2∣M∣W1 = byOwner (own b1 b0 b2 b0)
Ρ/W1W2∣M∣R = byOwner (own b1 b2 b0 b0)

-- ── Two and two ───────────────────────────────────────────────────────

Ρ/MR∣W1W2 Ρ/MW1∣RW2 Ρ/MW2∣RW1 : Assignment 2
Ρ/MR∣W1W2 = byOwner (own zero zero (suc zero) (suc zero))
Ρ/MW1∣RW2 = byOwner (own zero (suc zero) zero (suc zero))
Ρ/MW2∣RW1 = byOwner (own zero (suc zero) (suc zero) zero)

-- ── Three and one ─────────────────────────────────────────────────────

Ρ/MRW1∣W2 Ρ/MRW2∣W1 Ρ/MW1W2∣R Ρ/RW1W2∣M : Assignment 2
Ρ/MRW1∣W2 = byOwner (own zero zero zero (suc zero))
Ρ/MRW2∣W1 = byOwner (own zero zero (suc zero) zero)
Ρ/MW1W2∣R = byOwner (own zero (suc zero) zero zero)
Ρ/RW1W2∣M = byOwner (own (suc zero) zero zero zero)

-- ── All four ──────────────────────────────────────────────────────────

Ρ/MRW1W2 : Assignment 1
Ρ/MRW1W2 = byOwner (own zero zero zero zero)

-- ── Rejected: a block with two own roles able to act at once ──────────

_ : does (typecheckSession wbg Ρ/MR∣W1∣W2 (mr₁ v∷ p/W W1 v∷ p/W W2 v∷ v[])) ≡ false
_ = refl
_ : does (typecheckSession wbg Ρ/MR∣W1∣W2 (mr₂ v∷ p/W W1 v∷ p/W W2 v∷ v[])) ≡ false
_ = refl

_ : does (typecheckSession wbg Ρ/MW1∣R∣W2 (mw1₁ v∷ p/R v∷ p/W W2 v∷ v[])) ≡ false
_ = refl
_ : does (typecheckSession wbg Ρ/MW1∣R∣W2 (mw1₂ v∷ p/R v∷ p/W W2 v∷ v[])) ≡ false
_ = refl

_ : does (typecheckSession wbg Ρ/RW2∣M∣W1 (rw2₁ v∷ p/M v∷ p/W W1 v∷ v[])) ≡ false
_ = refl
_ : does (typecheckSession wbg Ρ/RW2∣M∣W1 (rw2₂ v∷ p/M v∷ p/W W1 v∷ v[])) ≡ false
_ = refl

_ : does (typecheckSession wbg Ρ/W1W2∣M∣R (w12₁ v∷ p/M v∷ p/R v∷ v[])) ≡ false
_ = refl
_ : does (typecheckSession wbg Ρ/W1W2∣M∣R (w12₂ v∷ p/M v∷ p/R v∷ v[])) ≡ false
_ = refl

-- Two-and-two partitions containing a rejected block.
_ : does (typecheckSession wbg Ρ/MR∣W1W2 (mr₁ v∷ w12₁ v∷ v[])) ≡ false
_ = refl
_ : does (typecheckSession wbg Ρ/MW1∣RW2 (mw1₁ v∷ rw2₁ v∷ v[])) ≡ false
_ = refl

-- ── Accepted ──────────────────────────────────────────────────────────

module MW2∣R∣W1 where
  Ρ = Ρ/MW2∣R∣W1
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  Ms : Session
  Ms = mw2 v∷ p/R v∷ p/W W1 v∷ v[]

  Ms-typed : ⊢s[ Ρ ] Ms ∶ s₀
  Ms-typed = toWitness {a? = typecheckSession wbg Ρ Ms} _

  Ms-safe : ∀ {αs Ms′} → Ms =[ αs ]⇒* Ms′
          → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] Ms′ ∶ G′
                    × (∀ n → ∃[ βs ] ∃[ Ms″ ] Ms′ =[ βs ]⇒* Ms″ × (finished Ms″ ⊎ length βs ≡ n))
  Ms-safe = safety Ρ Ms-typed

module RW1∣M∣W2 where
  Ρ = Ρ/RW1∣M∣W2
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  Ms : Session
  Ms = w1r v∷ p/M v∷ p/W W2 v∷ v[]

  Ms-typed : ⊢s[ Ρ ] Ms ∶ s₀
  Ms-typed = toWitness {a? = typecheckSession wbg Ρ Ms} _

  Ms-safe : ∀ {αs Ms′} → Ms =[ αs ]⇒* Ms′
          → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] Ms′ ∶ G′
                    × (∀ n → ∃[ βs ] ∃[ Ms″ ] Ms′ =[ βs ]⇒* Ms″ × (finished Ms″ ⊎ length βs ≡ n))
  Ms-safe = safety Ρ Ms-typed

module MW2∣RW1 where
  Ρ = Ρ/MW2∣RW1
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  Ms : Session
  Ms = mw2 v∷ w1r v∷ v[]

  Ms-typed : ⊢s[ Ρ ] Ms ∶ s₀
  Ms-typed = toWitness {a? = typecheckSession wbg Ρ Ms} _

  Ms-safe : ∀ {αs Ms′} → Ms =[ αs ]⇒* Ms′
          → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] Ms′ ∶ G′
                    × (∀ n → ∃[ βs ] ∃[ Ms″ ] Ms′ =[ βs ]⇒* Ms″ × (finished Ms″ ⊎ length βs ≡ n))
  Ms-safe = safety Ρ Ms-typed

module MRW1∣W2 where
  Ρ = Ρ/MRW1∣W2
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  Ms : Session
  Ms = mrw1 v∷ p/W W2 v∷ v[]

  Ms-typed : ⊢s[ Ρ ] Ms ∶ s₀
  Ms-typed = toWitness {a? = typecheckSession wbg Ρ Ms} _

  Ms-safe : ∀ {αs Ms′} → Ms =[ αs ]⇒* Ms′
          → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] Ms′ ∶ G′
                    × (∀ n → ∃[ βs ] ∃[ Ms″ ] Ms′ =[ βs ]⇒* Ms″ × (finished Ms″ ⊎ length βs ≡ n))
  Ms-safe = safety Ρ Ms-typed

module MRW2∣W1 where
  Ρ = Ρ/MRW2∣W1
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  Ms : Session
  Ms = mrw2 v∷ p/W W1 v∷ v[]

  Ms-typed : ⊢s[ Ρ ] Ms ∶ s₀
  Ms-typed = toWitness {a? = typecheckSession wbg Ρ Ms} _

  Ms-safe : ∀ {αs Ms′} → Ms =[ αs ]⇒* Ms′
          → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] Ms′ ∶ G′
                    × (∀ n → ∃[ βs ] ∃[ Ms″ ] Ms′ =[ βs ]⇒* Ms″ × (finished Ms″ ⊎ length βs ≡ n))
  Ms-safe = safety Ρ Ms-typed

module MW1W2∣R where
  Ρ = Ρ/MW1W2∣R
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  Ms : Session
  Ms = mw12 v∷ p/R v∷ v[]

  Ms-typed : ⊢s[ Ρ ] Ms ∶ s₀
  Ms-typed = toWitness {a? = typecheckSession wbg Ρ Ms} _

  Ms-safe : ∀ {αs Ms′} → Ms =[ αs ]⇒* Ms′
          → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] Ms′ ∶ G′
                    × (∀ n → ∃[ βs ] ∃[ Ms″ ] Ms′ =[ βs ]⇒* Ms″ × (finished Ms″ ⊎ length βs ≡ n))
  Ms-safe = safety Ρ Ms-typed

module RW1W2∣M where
  Ρ = Ρ/RW1W2∣M
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  Ms : Session
  Ms = rw12 v∷ p/M v∷ v[]

  Ms-typed : ⊢s[ Ρ ] Ms ∶ s₀
  Ms-typed = toWitness {a? = typecheckSession wbg Ρ Ms} _

  Ms-safe : ∀ {αs Ms′} → Ms =[ αs ]⇒* Ms′
          → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] Ms′ ∶ G′
                    × (∀ n → ∃[ βs ] ∃[ Ms″ ] Ms′ =[ βs ]⇒* Ms″ × (finished Ms″ ⊎ length βs ≡ n))
  Ms-safe = safety Ρ Ms-typed

-- Everything is internal.
module MRW1W2 where
  Ρ = Ρ/MRW1W2
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  Ms : Session
  Ms = ∅ v∷ v[]

  Ms-typed : ⊢s[ Ρ ] Ms ∶ s₀
  Ms-typed = toWitness {a? = typecheckSession wbg Ρ Ms} _

  Ms-safe : ∀ {αs Ms′} → Ms =[ αs ]⇒* Ms′
          → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] Ms′ ∶ G′
                    × (∀ n → ∃[ βs ] ∃[ Ms″ ] Ms′ =[ βs ]⇒* Ms″ × (finished Ms″ ⊎ length βs ≡ n))
  Ms-safe = safety Ρ Ms-typed
