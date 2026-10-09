{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_; s≤s)
import Data.Nat.Properties as Nat
open import Data.Nat.GeneralisedArithmetic using (iterate)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (Bool; true; _∨_; T)
import Data.Bool.Properties as Bool
open import Data.Fin using () renaming (_≟_ to _≟Fin_)
import Data.Fin.Properties as FinP
open import Data.Fin.Subset
  using (Subset; _⊆_; ∣_∣; ⁅_⁆) renaming (_∈_ to _∈ˢ_)
open import Data.Fin.Subset.Properties
  using (⊆-refl; ⊆-trans; x∈⁅x⁆; x∈⁅y⁆⇒x≡y; ∣⁅x⁆∣≡1; ∣p∣≤n; p⊂q⇒∣p∣<∣q∣)
open import Data.List.Membership.Propositional using (find; lose)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (lookup; tabulate)
import Data.Vec.Properties as VecP
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; T?; _×?_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

module Definitions.Graph.Reachability (N : ℕ) where

  open import Definitions.Actions N using (Action; _∈αˢ_; _∈αˢ?_)
  open import Definitions.Behav using (BTheory)
  open import Definitions.Graph.Core N

  open import Utils.Bits
    using ( iterate-suc; iterate-add; iterate/stable; iterateFix
          ; iterateFix/iterate; ⊆∧≢⇒⊂ )
    renaming (_∈?_ to _∈ˢ?_)

  -- ══════════════════════════════════════════════════════════════════
  --  Reachability over a concrete finite graph
  -- ══════════════════════════════════════════════════════════════════

  module _ (G : Graph) where

    open BTheory (graphTheory G) using (_∈T_; in/α; in/later; tr/step)

    -- Graph transition with `G` fixed (State G alone does not determine G).
    Step : State G → Action → State G → Set
    Step s α t = _-<_>->_ {G} s α t

    -- ── One-step expansion ──

    OneStep : Subset (size G) → (State G → Bool) → State G → Set
    OneStep m ok t =
      ∃[ s ] (s ∈ˢ m × T (ok s) × Any (λ e → proj₂ e ≡ t) (edges G s))

    oneStep? : ∀ m ok t → Dec (OneStep m ok t)
    oneStep? m ok t =
      FinP.any? λ s →
        (s ∈ˢ? m) ×? T? (ok s) ×? Any.any? (λ e → proj₂ e ≟Fin t) (edges G s)

    expand : (State G → Bool) → Subset (size G) → Subset (size G)
    expand ok m = tabulate (λ t → lookup m t ∨ ⌊ oneStep? m ok t ⌋)

    expand-lookup :
      ∀ ok m t → lookup (expand ok m) t ≡ (lookup m t ∨ ⌊ oneStep? m ok t ⌋)
    expand-lookup ok m t = VecP.lookup∘tabulate _ t

    expand-infl : ∀ ok m → m ⊆ expand ok m
    expand-infl ok m {t} t∈ =
      VecP.lookup⇒[]= t (expand ok m)
        (trans (expand-lookup ok m t)
          (cong (_∨ ⌊ oneStep? m ok t ⌋) (VecP.[]=⇒lookup t∈)))

    expand-step :
      ∀ ok m {s α t}
      → s ∈ˢ m → T (ok s) → Step s α t → t ∈ˢ expand ok m
    expand-step ok m {s} {α} {t} ms oks gr
      with oneStep? m ok t | expand-lookup ok m t
    ... | yes _  | eqL =
      VecP.lookup⇒[]= t (expand ok m) (trans eqL (Bool.∨-zeroʳ (lookup m t)))
    ... | no ¬os | _   =
      ⊥-elim (¬os (s , ms , oks , lose (step⇒listed gr) refl))

    expand-sound :
      ∀ ok m {t}
      → t ∈ˢ expand ok m
      → t ∈ˢ m ⊎ (∃[ s ] (s ∈ˢ m × T (ok s) × ∃[ α ] (Step s α t)))
    expand-sound ok m {t} p with oneStep? m ok t | expand-lookup ok m t
    ... | yes (s , ms , oks , hit) | _ =
      let (α , _) , mem , u≡t = find hit
      in inj₂ (s , ms , oks , α , subst (Step s α) u≡t (listed⇒step mem))
    ... | no _ | eqL =
      inj₁ (VecP.lookup⇒[]= t m
        (trans (sym (trans eqL (Bool.∨-identityʳ (lookup m t))))
          (VecP.[]=⇒lookup p)))

    -- ── Bounded reachability paths ──

    data PathVia (ok : State G → Bool)
      : State G → State G → ℕ → Set where
      path/nil  : ∀ {s} → PathVia ok s s zero
      path/cons :
        ∀ {s α u t n}
        → T (ok s) → Step s α u → PathVia ok u t n
        → PathVia ok s t (suc n)

    pathVia-snoc :
      ∀ {ok s u t α n}
      → PathVia ok s u n → T (ok u) → Step u α t
      → PathVia ok s t (suc n)
    pathVia-snoc path/nil oku gr = path/cons oku gr path/nil
    pathVia-snoc (path/cons oks gr′ rest) oku gr =
      path/cons oks gr′ (pathVia-snoc rest oku gr)

    -- ── Completeness: every path is captured ──

    iterate-infl : ∀ ok m k → m ⊆ iterate (expand ok) m k
    iterate-infl ok m zero    = ⊆-refl
    iterate-infl ok m (suc k) =
      ⊆-trans (expand-infl ok m) (iterate-infl ok (expand ok m) k)

    complete-aux :
      ∀ ok m k {a t n}
      → a ∈ˢ m → PathVia ok a t n → n ≤ k
      → t ∈ˢ iterate (expand ok) m k
    complete-aux ok m k ma path/nil _ = iterate-infl ok m k ma
    complete-aux ok m (suc k) ma (path/cons oka gr rest) (s≤s n≤k) =
      complete-aux ok (expand ok m) k (expand-step ok m ma oka gr) rest n≤k

    reachVia : (State G → Bool) → State G → Subset (size G)
    reachVia ok s = iterate (expand ok) ⁅ s ⁆ (size G)

    -- ── Soundness ──

    iterate-sound :
      ∀ ok s k {t}
      → t ∈ˢ iterate (expand ok) ⁅ s ⁆ k
      → ∃[ n ] PathVia ok s t n
    iterate-sound ok s zero {t} p =
      zero , subst (λ z → PathVia ok s z zero) (sym (x∈⁅y⁆⇒x≡y s p)) path/nil
    iterate-sound ok s (suc k) {t} p
      with expand-sound ok (iterate (expand ok) ⁅ s ⁆ k)
             (subst (t ∈ˢ_) (iterate-suc (expand ok) ⁅ s ⁆ k) p)
    ... | inj₁ pt = iterate-sound ok s k pt
    ... | inj₂ (s′ , ms′ , oks′ , α , gr) with iterate-sound ok s k ms′
    ...   | n , path = suc n , pathVia-snoc path oks′ gr

    reachVia-sound :
      ∀ ok s {t} → t ∈ˢ reachVia ok s → ∃[ n ] PathVia ok s t n
    reachVia-sound ok s p = iterate-sound ok s (size G) p

    -- ── Fixpoint saturation (bounded by `size G`) ──

    grow :
      ∀ ok s k
      → (suc k ≤ ∣ iterate (expand ok) ⁅ s ⁆ k ∣)
      ⊎ (expand ok (iterate (expand ok) ⁅ s ⁆ k)
           ≡ iterate (expand ok) ⁅ s ⁆ k)
    grow ok s zero = inj₁ (Nat.≤-reflexive (sym (∣⁅x⁆∣≡1 s)))
    grow ok s (suc k) = go (grow ok s k)
      where
        X : Subset (size G)
        X = iterate (expand ok) ⁅ s ⁆ k

        X′≡ : iterate (expand ok) ⁅ s ⁆ (suc k) ≡ expand ok X
        X′≡ = iterate-suc (expand ok) ⁅ s ⁆ k

        fixStep :
          expand ok X ≡ X
          → expand ok (iterate (expand ok) ⁅ s ⁆ (suc k))
              ≡ iterate (expand ok) ⁅ s ⁆ (suc k)
        fixStep fix =
          trans (cong (expand ok) (trans X′≡ fix))
            (trans fix (sym (trans X′≡ fix)))

        go :
          (suc k ≤ ∣ X ∣) ⊎ (expand ok X ≡ X)
          → (suc (suc k) ≤ ∣ iterate (expand ok) ⁅ s ⁆ (suc k) ∣)
          ⊎ (expand ok (iterate (expand ok) ⁅ s ⁆ (suc k))
               ≡ iterate (expand ok) ⁅ s ⁆ (suc k))
        go (inj₂ fix) = inj₂ (fixStep fix)
        go (inj₁ bound) with VecP.≡-dec Bool._≟_ (expand ok X) X
        ... | yes fix = inj₂ (fixStep fix)
        ... | no ¬fix =
          inj₁ (subst (λ Y → suc (suc k) ≤ ∣ Y ∣) (sym X′≡)
                  (Nat.≤-trans (s≤s bound)
                    (p⊂q⇒∣p∣<∣q∣
                      (⊆∧≢⇒⊂ (expand-infl ok X) (λ e → ¬fix (sym e))))))

    reach-fixed : ∀ ok s → expand ok (reachVia ok s) ≡ reachVia ok s
    reach-fixed ok s with grow ok s (size G)
    ... | inj₂ fix = fix
    ... | inj₁ bound =
      ⊥-elim (Nat.<-irrefl refl (Nat.<-≤-trans bound (∣p∣≤n (reachVia ok s))))

    fix-iterate :
      ∀ ok s j → iterate (expand ok) (reachVia ok s) j ≡ reachVia ok s
    fix-iterate ok s =
      iterate/stable (expand ok) (reachVia ok s) (reach-fixed ok s)

    converge :
      ∀ ok s n → iterate (expand ok) ⁅ s ⁆ n ⊆ reachVia ok s
    converge ok s n {i} x with Nat.≤-total n (size G)
    ... | inj₁ n≤ =
      subst (λ z → i ∈ˢ iterate (expand ok) ⁅ s ⁆ z) (Nat.m+[n∸m]≡n n≤)
        (subst (i ∈ˢ_)
          (sym (iterate-add (expand ok) ⁅ s ⁆ n (size G ∸ n)))
          (iterate-infl ok (iterate (expand ok) ⁅ s ⁆ n) (size G ∸ n) x))
    ... | inj₂ ≤n =
      subst (i ∈ˢ_) eqn x
      where
        eqn : iterate (expand ok) ⁅ s ⁆ n ≡ reachVia ok s
        eqn =
          trans (cong (iterate (expand ok) ⁅ s ⁆) (sym (Nat.m+[n∸m]≡n ≤n)))
            (trans (iterate-add (expand ok) ⁅ s ⁆ (size G) (n ∸ size G))
              (fix-iterate ok s (n ∸ size G)))

    reachVia-complete :
      ∀ ok s {t n} → PathVia ok s t n → t ∈ˢ reachVia ok s
    reachVia-complete ok s {n = n} path =
      converge ok s n (complete-aux ok ⁅ s ⁆ n (x∈⁅x⁆ s) path Nat.≤-refl)

    -- ── The row to COMPUTE ──
    --
    -- `reachVia` is the specification; `reachFix` forces each round and
    -- stops at the fixpoint.
    reachFix : (State G → Bool) → State G → Subset (size G)
    reachFix ok s =
      iterateFix (VecP.≡-dec Bool._≟_) (size G) (expand ok) ⁅ s ⁆

    reachFix≡ : ∀ ok s → reachFix ok s ≡ reachVia ok s
    reachFix≡ ok s =
      iterateFix/iterate (VecP.≡-dec Bool._≟_) (size G) (expand ok) ⁅ s ⁆

    -- ══════════════════════════════════════════════════════════════
    --  Exact participation:  P ∈T s  ⇔  reach a P-active edge
    -- ══════════════════════════════════════════════════════════════

    reach→∈T :
      ∀ {P s t n}
      → PathVia (λ _ → true) s t n
      → Any (λ e → P ∈αˢ proj₁ e) (edges G t)
      → P ∈T s
    reach→∈T path/nil active =
      let _ , mem , px = find active in in/α (listed⇒step mem) px
    reach→∈T (path/cons _ gr rest) active = in/later gr (reach→∈T rest active)

    ∈T→reach :
      ∀ {P s} → P ∈T s
      → ∃[ t ] (∃[ n ] PathVia (λ _ → true) s t n
                × Any (λ e → P ∈αˢ proj₁ e) (edges G t))
    ∈T→reach {P} {s} (_ , _ , tr/step gr _ , here px) =
      s , zero , path/nil , lose (step⇒listed gr) px
    ∈T→reach {P} {s} (_ , t , tr/step gr tr , there mem)
      with ∈T→reach (_ , t , tr , mem)
    ... | t′ , n , path , active = t′ , suc n , path/cons tt gr path , active

    active? : ∀ P t → Dec (Any (λ e → P ∈αˢ proj₁ e) (edges G t))
    active? P t = Any.any? (λ e → P ∈αˢ? proj₁ e) (edges G t)
