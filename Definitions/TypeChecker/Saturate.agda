{-# OPTIONS --guardedness #-}

-- Phase S of decidable.md v2: the saturation theorem
--
--     sat : Alg k Γ Δ P Pr s → Alg (F Pr) Γ Δ P Pr s
--
-- `Alg (suc k) = Φ (Alg k)` for a monotone operator `Φ`.  For fixed
-- `Γ Δ P Pr`, only the state `s` moves over the finite set `State G`, so the
-- Kleene chain of `Φ` stabilises within `size G` steps (pigeonhole on the
-- existing `wt`/`Incl` machinery in `LTS/Reachability.agda`).  With `sat` the
-- completeness proof (Phase C) needs no fuel bookkeeping.
--
-- This module imports only `Definitions.TypeChecker`; it is independent of the
-- rest of the completeness development.  A root import wires it into
-- `runall.sh`.

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
import Data.Fin as F
import Data.Fin.Properties as Fin
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as Nat
open import Data.Product
  using (_×_; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; lookup; tabulate)
import Data.List.Relation.Unary.All as All
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable
  using (⌊_⌋; toWitness; fromWitness; T?)

open import Definitions.Behav using (BTheory; WellBehaved)
open import Definitions.Expr using (Sort)
open import Definitions.TypeChecker
import Definitions.Typing as Typing

module Definitions.TypeChecker.Saturate (N : ℕ) where

  open Processes N
  open import LTS.Core N
  open import LTS.Reachability N
    using ( wt; Incl; wt/mono; wt/strict; wt-bound; wt-full
          ; ≡true→T; T→≡true )

  module GraphSaturate
    (G : Graph)
    (wb : WellBehaved (graphTheory G))
    where

    open GraphChecker G wb
    open Typing.MPST wb hiding (_,_)

    -- ── generic decidable helpers (private in `TypeChecker`; copied) ──
    private
      _×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
      yes a ×-dec yes b = yes (a , b)
      no ¬a ×-dec _     = no λ { (a , _) → ¬a a }
      _     ×-dec no ¬b = no λ { (_ , b) → ¬b b }

      _→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
      yes _ →-dec yes b = yes (λ _ → b)
      yes a →-dec no ¬b = no λ f → ¬b (f a)
      no ¬a →-dec _     = yes λ a → ⊥-elim (¬a a)

      _⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
      yes a ⊎-dec _     = yes (inj₁ a)
      no _  ⊎-dec yes b = yes (inj₂ b)
      no ¬a ⊎-dec no ¬b = no λ { (inj₁ a) → ¬a a ; (inj₂ b) → ¬b b }

      false≢true : false ≢ true
      false≢true ()

      -- refute an implication whose antecedent is decided
      ¬→→× : {A B : Set} → Dec A → ¬ (A → B) → A × ¬ B
      ¬→→× (yes a) ¬f = a , λ b → ¬f (λ _ → b)
      ¬→→× (no ¬a) ¬f = ⊥-elim (¬f λ a → ⊥-elim (¬a a))

      -- either the predicate holds everywhere or a concrete counterexample
      findCex : ∀ {n} (Q : Fin n → Set) → (∀ i → Dec (Q i))
              → (∀ i → Q i) ⊎ (Σ[ i ∈ Fin n ] ¬ Q i)
      findCex {zero}  Q Q? = inj₁ λ ()
      findCex {suc n} Q Q? with Q? F.zero
      ... | no ¬q0 = inj₂ (F.zero , ¬q0)
      ... | yes q0 with findCex (λ i → Q (F.suc i)) (λ i → Q? (F.suc i))
      ...   | inj₁ all = inj₁ λ { F.zero → q0 ; (F.suc i) → all i }
      ...   | inj₂ (i , ¬qi) = inj₂ (F.suc i , ¬qi)

    -- ════════════════════════════════════════════════════════════════
    --  S.1  The full budget `F`, the sub-budget `J`, and the arithmetic
    -- ════════════════════════════════════════════════════════════════

    F : ∀ {γ δ} → Proc γ δ → ℕ
    F Pr = suc (size G) * processFuel Pr

    J : ∀ {γ δ} → Proc γ δ → ℕ
    J Pr = suc (size G) * (processFuel Pr ∸ 1)

    -- every `processFuel` clause is `suc _`, so it un-predecessors exactly
    pf-suc : ∀ {γ δ} (Pr : Proc γ δ) → suc (processFuel Pr ∸ 1) ≡ processFuel Pr
    pf-suc (_ ! _ < _ >∙ _)      = refl
    pf-suc (Σ _ ？[ _ ]· _)      = refl
    pf-suc (ifp _ then _ else _) = refl
    pf-suc (rec _)               = refl
    pf-suc (v _)                 = refl
    pf-suc ∅                     = refl

    -- the single budget identity: `suc (J Pr + size G) ≡ F Pr`
    J+size≡F : ∀ {γ δ} (Pr : Proc γ δ) → suc (J Pr + size G) ≡ F Pr
    J+size≡F Pr =
      trans (cong suc (Nat.+-comm (J Pr) (size G)))
        (trans (sym (Nat.*-suc (suc (size G)) (processFuel Pr ∸ 1)))
               (cong (suc (size G) *_) (pf-suc Pr)))

    -- `J Pr + j₀ ≤ F Pr` whenever `j₀ ≤ size G` (used at the top of `sat`)
    bound : ∀ {γ δ} (Pr : Proc γ δ) (j₀ : ℕ) → j₀ ≤ size G → J Pr + j₀ ≤ F Pr
    bound Pr j₀ j₀≤ =
      Nat.≤-trans (Nat.+-monoʳ-≤ (J Pr) j₀≤)
        (Nat.≤-trans (Nat.n≤1+n (J Pr + size G))
          (Nat.≤-reflexive (J+size≡F Pr)))

    -- a branch's fuel is bounded by the whole branch-vector's fuel
    branchFuel-lb : ∀ {γ δ I} (Br : Vec (Proc γ δ) I) (j : Fin I)
                  → processFuel (lookup Br j) ≤ branchesFuel Br
    branchFuel-lb (Pr ∷ Br) F.zero =
      Nat.m≤m+n (processFuel Pr) (branchesFuel Br)
    branchFuel-lb (Pr ∷ Br) (F.suc j) =
      Nat.≤-trans (branchFuel-lb Br j)
        (Nat.m≤n+m (branchesFuel Br) (processFuel Pr))

    -- per-constructor subterm bounds (RHS is definitionally `J` of the
    -- compound process, since `processFuel` reduces to `suc _`)
    J-recv-bound : ∀ {γ δ I} (Br : Vec (Proc γ δ) (suc I)) (j : Fin (suc I))
                 → F (lookup Br j) ≤ suc (size G) * branchesFuel Br
    J-recv-bound Br j = Nat.*-monoʳ-≤ (suc (size G)) (branchFuel-lb Br j)

    J-if₁ : ∀ {γ δ} (Pr₁ Pr₂ : Proc γ δ)
          → F Pr₁ ≤ suc (size G) * (processFuel Pr₁ + processFuel Pr₂)
    J-if₁ Pr₁ Pr₂ =
      Nat.*-monoʳ-≤ (suc (size G)) (Nat.m≤m+n (processFuel Pr₁) (processFuel Pr₂))

    J-if₂ : ∀ {γ δ} (Pr₁ Pr₂ : Proc γ δ)
          → F Pr₂ ≤ suc (size G) * (processFuel Pr₁ + processFuel Pr₂)
    J-if₂ Pr₁ Pr₂ =
      Nat.*-monoʳ-≤ (suc (size G)) (Nat.m≤n+m (processFuel Pr₂) (processFuel Pr₁))

    -- ════════════════════════════════════════════════════════════════
    --  S.2  The per-level Kleene iteration `It` and its decision
    -- ════════════════════════════════════════════════════════════════

    It : ∀ {γ δ} → Vec Sort γ → Vec (State G) δ → Part → Proc γ δ
       → ℕ → State G → Set
    It Γ Δ P Pr zero    s = ⊥
    It Γ Δ P Pr (suc j) s =
        Direct (Alg (J Pr)) Γ Δ P Pr s
      ⊎ (Σ[ r ∈ State G ] Incoming P s (edges G r) × It Γ Δ P Pr j r)
      ⊎ SemSkipP (It Γ Δ P Pr j) P s

    It? : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
            (Pr : Proc γ δ) (j : ℕ) (s : State G)
        → Dec (It Γ Δ P Pr j s)
    It? Γ Δ P Pr zero    s = no λ ()
    It? Γ Δ P Pr (suc j) s =
      direct? (Alg (J Pr)) (checkWithFuelD (J Pr)) Γ Δ P Pr s
        ⊎-dec
        ( Fin.any? (λ r → findIncoming P s (edges G r)
                            ×-dec It? Γ Δ P Pr j r)
          ⊎-dec
          SkipDecide.semSkip? (It Γ Δ P Pr j) (It? Γ Δ P Pr j) P s )

    it-mono-≤ : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
                  (Pr : Proc γ δ) {k k′} → k ≤ k′
              → ∀ {s} → It Γ Δ P Pr k s → It Γ Δ P Pr k′ s
    it-mono-≤ Γ Δ P Pr z≤n ()
    it-mono-≤ Γ Δ P Pr (s≤s le) (inj₁ d) = inj₁ d
    it-mono-≤ Γ Δ P Pr (s≤s le) (inj₂ (inj₁ (r , inc , itr))) =
      inj₂ (inj₁ (r , inc , it-mono-≤ Γ Δ P Pr le itr))
    it-mono-≤ Γ Δ P Pr (s≤s le) (inj₂ (inj₂ sem)) =
      inj₂ (inj₂ (semSkipP-mono (λ {u} → it-mono-≤ Γ Δ P Pr le) sem))

    -- ════════════════════════════════════════════════════════════════
    --  S.3  Pigeonhole: the chain collapses within `size G` steps
    -- ════════════════════════════════════════════════════════════════

    vec : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
            (Pr : Proc γ δ) (j : ℕ)
        → Vec Bool (size G)
    vec Γ Δ P Pr j = tabulate (λ s → ⌊ It? Γ Δ P Pr j s ⌋)

    vecLookup : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
                  (Pr : Proc γ δ) (j : ℕ) (s : State G)
              → lookup (vec Γ Δ P Pr j) s ≡ ⌊ It? Γ Δ P Pr j s ⌋
    vecLookup Γ Δ P Pr j s = VecP.lookup∘tabulate _ s

    it→marked : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
                  (Pr : Proc γ δ) {j s}
              → It Γ Δ P Pr j s → lookup (vec Γ Δ P Pr j) s ≡ true
    it→marked Γ Δ P Pr {j} {s} it =
      trans (vecLookup Γ Δ P Pr j s) (T→≡true (fromWitness it))

    marked→it : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
                  (Pr : Proc γ δ) {j s}
              → lookup (vec Γ Δ P Pr j) s ≡ true → It Γ Δ P Pr j s
    marked→it Γ Δ P Pr {j} {s} p =
      toWitness (≡true→T (trans (sym (vecLookup Γ Δ P Pr j s)) p))

    it-unmarked : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
                    (Pr : Proc γ δ) {j s}
                → ¬ It Γ Δ P Pr j s → lookup (vec Γ Δ P Pr j) s ≡ false
    it-unmarked Γ Δ P Pr {j} {s} ¬it
      with It? Γ Δ P Pr j s | vecLookup Γ Δ P Pr j s
    ... | yes it | _  = ⊥-elim (¬it it)
    ... | no _   | eq = eq

    vec-incl : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
                 (Pr : Proc γ δ) (j : ℕ)
             → Incl (vec Γ Δ P Pr j) (vec Γ Δ P Pr (suc j))
    vec-incl Γ Δ P Pr j i Ti =
      ≡true→T (it→marked Γ Δ P Pr {suc j} {i}
        (it-mono-≤ Γ Δ P Pr (Nat.n≤1+n j)
          (marked→it Γ Δ P Pr {j} {i} (T→≡true Ti))))

    vec-neq : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
                (Pr : Proc γ δ) (j : ℕ) (s₀ : State G)
            → It Γ Δ P Pr (suc j) s₀ → ¬ It Γ Δ P Pr j s₀
            → vec Γ Δ P Pr j ≢ vec Γ Δ P Pr (suc j)
    vec-neq Γ Δ P Pr j s₀ itS ¬itJ e =
      false≢true
        (trans (sym (it-unmarked Γ Δ P Pr {j} {s₀} ¬itJ))
          (trans (cong (λ z → lookup z s₀) e)
            (it→marked Γ Δ P Pr {suc j} {s₀} itS)))

    -- one level is stable, or a concrete state where it grows
    stabOr : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
               (Pr : Proc γ δ) (j : ℕ)
           → (∀ s → It Γ Δ P Pr (suc j) s → It Γ Δ P Pr j s)
           ⊎ (Σ[ s ∈ State G ] It Γ Δ P Pr (suc j) s × ¬ It Γ Δ P Pr j s)
    stabOr Γ Δ P Pr j
      with findCex (λ s → It Γ Δ P Pr (suc j) s → It Γ Δ P Pr j s)
                   (λ s → It? Γ Δ P Pr (suc j) s →-dec It? Γ Δ P Pr j s)
    ... | inj₁ all = inj₁ all
    ... | inj₂ (s₀ , ¬q) = inj₂ (s₀ , ¬→→× (It? Γ Δ P Pr (suc j) s₀) ¬q)

    -- fuel-with-invariant search (mirrors `SkipSem.build`'s `fresh`/`fullEq`):
    -- `j + o ≡ size G` keeps `j ≤ size G`; `size G ≤ wt (vec j) + o` forces the
    -- vector full at `o = 0`, so the level cannot fail to stabilise there.
    search : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
               (Pr : Proc γ δ) (o j : ℕ)
           → j + o ≡ size G
           → size G ≤ wt (vec Γ Δ P Pr j) + o
           → Σ[ j′ ∈ ℕ ] j′ ≤ size G
               × (∀ s → It Γ Δ P Pr (suc j′) s → It Γ Δ P Pr j′ s)
    search Γ Δ P Pr zero j j+o inv with stabOr Γ Δ P Pr j
    ... | inj₁ st = j , subst (j ≤_) j+o (Nat.m≤m+n j zero) , st
    ... | inj₂ (s₀ , _ , ¬itJ) =
          ⊥-elim (¬itJ (marked→it Γ Δ P Pr full))
      where
        wtEq : wt (vec Γ Δ P Pr j) ≡ size G
        wtEq = Nat.≤-antisym (wt-bound (vec Γ Δ P Pr j))
                 (subst (size G ≤_) (Nat.+-identityʳ (wt (vec Γ Δ P Pr j))) inv)
        full : lookup (vec Γ Δ P Pr j) s₀ ≡ true
        full = wt-full {v = vec Γ Δ P Pr j} wtEq s₀
    search Γ Δ P Pr (suc o) j j+o inv with stabOr Γ Δ P Pr j
    ... | inj₁ st = j , subst (j ≤_) j+o (Nat.m≤m+n j (suc o)) , st
    ... | inj₂ (s₀ , itS , ¬itJ) = search Γ Δ P Pr o (suc j) j+o′ inv′
      where
        strict : suc (wt (vec Γ Δ P Pr j)) ≤ wt (vec Γ Δ P Pr (suc j))
        strict = wt/strict {left = vec Γ Δ P Pr j}
                           {right = vec Γ Δ P Pr (suc j)}
                   (vec-incl Γ Δ P Pr j) (vec-neq Γ Δ P Pr j s₀ itS ¬itJ)
        j+o′ : suc j + o ≡ size G
        j+o′ = trans (sym (Nat.+-suc j o)) j+o
        inv′ : size G ≤ wt (vec Γ Δ P Pr (suc j)) + o
        inv′ = Nat.≤-trans
                 (subst (size G ≤_) (Nat.+-suc (wt (vec Γ Δ P Pr j)) o) inv)
                 (Nat.+-monoˡ-≤ o strict)

    findStab : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
                 (Pr : Proc γ δ)
             → Σ[ j ∈ ℕ ] j ≤ size G
                 × (∀ s → It Γ Δ P Pr (suc j) s → It Γ Δ P Pr j s)
    findStab Γ Δ P Pr =
      search Γ Δ P Pr (size G) 0 refl
        (Nat.m≤n+m (size G) (wt (vec Γ Δ P Pr 0)))

    -- ════════════════════════════════════════════════════════════════
    --  S.4  Compressing the chain and re-entering `Alg`
    -- ════════════════════════════════════════════════════════════════

    -- once one level is stable, every higher level collapses to it
    collapse : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
                 (Pr : Proc γ δ) {j}
             → (∀ s → It Γ Δ P Pr (suc j) s → It Γ Δ P Pr j s)
             → ∀ d s → It Γ Δ P Pr (j + d) s → It Γ Δ P Pr j s
    collapse Γ Δ P Pr {j} st zero s it =
      subst (λ z → It Γ Δ P Pr z s) (Nat.+-identityʳ j) it
    collapse Γ Δ P Pr {j} st (suc d) s it =
      st s (step (subst (λ z → It Γ Δ P Pr z s) (Nat.+-suc j d) it))
      where
        md : ∀ u → It Γ Δ P Pr (j + d) u → It Γ Δ P Pr j u
        md = collapse Γ Δ P Pr {j} st d
        step : It Γ Δ P Pr (suc (j + d)) s → It Γ Δ P Pr (suc j) s
        step (inj₁ dd) = inj₁ dd
        step (inj₂ (inj₁ (r , inc , itr))) = inj₂ (inj₁ (r , inc , md r itr))
        step (inj₂ (inj₂ sem)) =
          inj₂ (inj₂ (semSkipP-mono (λ {u} → md u) sem))

    -- cap any `It k` down to `It (findStab .proj₁)`
    itCap : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
              (Pr : Proc γ δ) (k : ℕ) (s : State G)
          → It Γ Δ P Pr k s
          → It Γ Δ P Pr (proj₁ (findStab Γ Δ P Pr)) s
    itCap Γ Δ P Pr k s it
      with Nat.≤-total k (proj₁ (findStab Γ Δ P Pr))
    ... | inj₁ k≤j₀ = it-mono-≤ Γ Δ P Pr k≤j₀ it
    ... | inj₂ j₀≤k =
          collapse Γ Δ P Pr (proj₂ (proj₂ (findStab Γ Δ P Pr)))
            (k ∸ proj₁ (findStab Γ Δ P Pr)) s
            (subst (λ z → It Γ Δ P Pr z s) (sym (Nat.m+[n∸m]≡n j₀≤k)) it)

    -- an `It j` witness re-enters `Alg` at fuel `J Pr + j`
    It→Alg : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
               (Pr : Proc γ δ) (j : ℕ) (s : State G)
           → It Γ Δ P Pr j s → Alg (J Pr + j) Γ Δ P Pr s
    It→Alg Γ Δ P Pr (suc j) s (inj₁ d) =
      subst (λ z → Alg z Γ Δ P Pr s) (sym (Nat.+-suc (J Pr) j))
        (inj₁ (direct-mono (alg-mono (Nat.m≤m+n (J Pr) j)) Γ Δ P Pr s d))
    It→Alg Γ Δ P Pr (suc j) s (inj₂ (inj₁ (r , inc , itr))) =
      subst (λ z → Alg z Γ Δ P Pr s) (sym (Nat.+-suc (J Pr) j))
        (inj₂ (inj₁ (r , inc , It→Alg Γ Δ P Pr j r itr)))
    It→Alg Γ Δ P Pr (suc j) s (inj₂ (inj₂ sem)) =
      subst (λ z → Alg z Γ Δ P Pr s) (sym (Nat.+-suc (J Pr) j))
        (inj₂ (inj₂ (semSkipP-mono (λ {u} → It→Alg Γ Δ P Pr j u) sem)))

    -- ════════════════════════════════════════════════════════════════
    --  S.5  The saturation theorem
    -- ════════════════════════════════════════════════════════════════

    mutual
      sat : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
              (Pr : Proc γ δ) (s : State G) (k : ℕ)
          → Alg k Γ Δ P Pr s → Alg (F Pr) Γ Δ P Pr s
      sat Γ Δ P Pr s k a =
        alg-mono (bound Pr (proj₁ (findStab Γ Δ P Pr))
                           (proj₁ (proj₂ (findStab Γ Δ P Pr))))
          (It→Alg Γ Δ P Pr (proj₁ (findStab Γ Δ P Pr)) s
            (itCap Γ Δ P Pr k s (algk→It Γ Δ P Pr k s a)))

      -- `Alg k ⊆ It k` at the same level; the ONLY place the structural
      -- recursion on `Pr` enters (through `directSat`).
      algk→It : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
                  (Pr : Proc γ δ) (k : ℕ) (s : State G)
              → Alg k Γ Δ P Pr s → It Γ Δ P Pr k s
      algk→It Γ Δ P Pr zero s ()
      algk→It Γ Δ P Pr (suc k) s (inj₁ d) =
        inj₁ (directSat Γ Δ P Pr s d)
      algk→It Γ Δ P Pr (suc k) s (inj₂ (inj₁ (r , inc , a))) =
        inj₂ (inj₁ (r , inc , algk→It Γ Δ P Pr k r a))
      algk→It Γ Δ P Pr (suc k) s (inj₂ (inj₂ sem)) =
        inj₂ (inj₂ (semSkipP-mono (λ {u} → algk→It Γ Δ P Pr k u) sem))

      -- `Direct (Alg k) ⊆ Direct (Alg (J Pr))`: by cases on `Pr`, calling
      -- `sat` at the *visible* subterms.  Never route through `direct-mono`
      -- (its `mp` is quantified over arbitrary `Pr` and would wreck
      -- termination).
      directSat : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
                    (Pr : Proc γ δ) {k} (s : State G)
                → Direct (Alg k) Γ Δ P Pr s → Direct (Alg (J Pr)) Γ Δ P Pr s
      directSat Γ Δ P (_ ! _ < _ >∙ Pr′) s (S , t , etd , gr , a) =
        S , t , etd , gr , sat Γ Δ P Pr′ t _ a
      directSat Γ Δ Q (Σ_？[_]·_ P {I = I} S Br) s (rw , all) =
        rw ,
        All.map
          (λ f {j} {U} eq →
             alg-mono (J-recv-bound Br j) (satBr (U ∷ Γ) Δ Q Br j (f eq)))
          all
      directSat Γ Δ P (ifp _ then Pr₁ else Pr₂) s (etd , a₁ , a₂) =
          etd
        , alg-mono (J-if₁ Pr₁ Pr₂) (sat Γ Δ P Pr₁ s _ a₁)
        , alg-mono (J-if₂ Pr₁ Pr₂) (sat Γ Δ P Pr₂ s _ a₂)
      directSat Γ Δ P (rec Pr′) s (mg , a) =
        mg , sat Γ (s ∷ Δ) P Pr′ s _ a
      directSat Γ Δ P (v X) s eq = eq
      directSat Γ Δ P ∅ s ¬in = ¬in

      -- vector companion so `lookup Br j` is a structural subterm
      satBr : ∀ {γ δ I} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
                (Br : Vec (Proc γ δ) I) (j : Fin I) {k} {s : State G}
            → Alg k Γ Δ P (lookup Br j) s
            → Alg (F (lookup Br j)) Γ Δ P (lookup Br j) s
      satBr Γ Δ P (Pr ∷ Br) F.zero    a = sat Γ Δ P Pr _ _ a
      satBr Γ Δ P (Pr ∷ Br) (F.suc j) a = satBr Γ Δ P Br j a
