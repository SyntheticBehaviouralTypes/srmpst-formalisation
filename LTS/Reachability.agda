{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as Nat
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; _∨_; T)
import Data.Bool.Properties as Bool
open import Data.Fin using (Fin)
  renaming (_≟_ to _≟Fin_)
import Data.Fin as F
import Data.Fin.Properties as FinP
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; lookup; tabulate)
import Data.Vec as V
import Data.Vec.Properties as VecP
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness; True; T?)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; _≢_)

module LTS.Reachability (N : ℕ) where

  open import Definitions.Actions N using (Action; _∈α_; _∈α?_)
  open import Definitions.Common N using (Part)
  open import Definitions.Behav using (BTheory)
  open import LTS.Core N

  data ReachableBy
    {G : Graph}
    (Allow : Action → Set)
    (s : State G)
    : State G → Set
    where

    reachable/refl :
      ReachableBy Allow s s

    reachable/step :
      ∀ {α u t}
      → _-<_>->_ {G} s α u
      → Allow α
      → ReachableBy {G} Allow u t
      → ReachableBy Allow s t

  Reachable : {G : Graph} → State G → State G → Set
  Reachable {G} = ReachableBy {G} (λ _ → ⊤)

  reachable/map :
    ∀ {G s t}
      {Allow Allow′ : Action → Set}
    → (∀ {α} → Allow α → Allow′ α)
    → ReachableBy {G} Allow s t
    → ReachableBy {G} Allow′ s t
  reachable/map inclusion reachable/refl =
    reachable/refl
  reachable/map inclusion (reachable/step gr allowed path) =
    reachable/step gr (inclusion allowed)
      (reachable/map {G = _} inclusion path)

  reachable/cat :
    ∀ {G s u t Allow}
    → ReachableBy {G} Allow s u
    → ReachableBy {G} Allow u t
    → ReachableBy {G} Allow s t
  reachable/cat reachable/refl right =
    right
  reachable/cat (reachable/step gr allowed left) right =
    reachable/step gr allowed (reachable/cat {G = _} left right)

  -- ══════════════════════════════════════════════════════════════════
  --  Graph-independent Bool-vector fixpoint infrastructure
  -- ══════════════════════════════════════════════════════════════════

  iter : ∀ {A : Set} → ℕ → (A → A) → A → A
  iter zero    f x = x
  iter (suc k) f x = iter k f (f x)

  iter-shift :
    ∀ {A} k (f : A → A) x → iter k f (f x) ≡ f (iter k f x)
  iter-shift zero    f x = refl
  iter-shift (suc k) f x = iter-shift k f (f x)

  iter-suc :
    ∀ {A} k (f : A → A) x → iter (suc k) f x ≡ f (iter k f x)
  iter-suc k f x = iter-shift k f x

  iter-add :
    ∀ {A} a b (f : A → A) x
    → iter (a + b) f x ≡ iter b f (iter a f x)
  iter-add zero    b f x = refl
  iter-add (suc a) b f x = iter-add a b f (f x)

  ≡true→T : ∀ {b} → b ≡ true → T b
  ≡true→T refl = tt

  T→≡true : ∀ {b} → T b → b ≡ true
  T→≡true {true}  _  = refl
  T→≡true {false} ()

  bitv : Bool → ℕ
  bitv false = zero
  bitv true  = suc zero

  wt : ∀ {n} → Vec Bool n → ℕ
  wt V.[]        = zero
  wt (b V.∷ row) = bitv b + wt row

  Incl : ∀ {n} → Vec Bool n → Vec Bool n → Set
  Incl left right =
    ∀ i → T (lookup left i) → T (lookup right i)

  Incl-refl : ∀ {n} {v : Vec Bool n} → Incl v v
  Incl-refl i x = x

  Incl-trans :
    ∀ {n} {a b c : Vec Bool n}
    → Incl a b → Incl b c → Incl a c
  Incl-trans ab bc i x = bc i (ab i x)

  Incl-≡ :
    ∀ {n} {a b : Vec Bool n} → a ≡ b → Incl a b
  Incl-≡ e i x = subst (λ z → T (lookup z i)) e x

  bitv/mono : ∀ l r → (T l → T r) → bitv l ≤ bitv r
  bitv/mono false r    _    = z≤n
  bitv/mono true  false incl = ⊥-elim (incl tt)
  bitv/mono true  true  _    = s≤s z≤n

  wt/mono :
    ∀ {n} {left right : Vec Bool n}
    → Incl left right
    → wt left ≤ wt right
  wt/mono {left = V.[]} {V.[]} _ = z≤n
  wt/mono {left = l V.∷ ls} {r V.∷ rs} incl =
    Nat.+-mono-≤
      (bitv/mono l r (incl F.zero))
      (wt/mono {left = ls} {right = rs} (λ i → incl (F.suc i)))

  wt/strict :
    ∀ {n} {left right : Vec Bool n}
    → Incl left right
    → left ≢ right
    → wt left < wt right
  wt/strict {left = V.[]} {V.[]} _ ne = ⊥-elim (ne refl)
  wt/strict {left = false V.∷ ls} {false V.∷ rs} incl ne =
    wt/strict {left = ls} {right = rs}
      (λ i → incl (F.suc i))
      (λ e → ne (cong (false V.∷_) e))
  wt/strict {left = false V.∷ ls} {true V.∷ rs} incl ne =
    s≤s (wt/mono {left = ls} {right = rs} (λ i → incl (F.suc i)))
  wt/strict {left = true V.∷ ls} {false V.∷ rs} incl ne =
    ⊥-elim (incl F.zero tt)
  wt/strict {left = true V.∷ ls} {true V.∷ rs} incl ne =
    s≤s (wt/strict {left = ls} {right = rs}
      (λ i → incl (F.suc i))
      (λ e → ne (cong (true V.∷_) e)))

  wt-bound : ∀ {n} (v : Vec Bool n) → wt v ≤ n
  wt-bound V.[]           = z≤n
  wt-bound (false V.∷ v)  =
    Nat.≤-trans (wt-bound v) (Nat.n≤1+n _)
  wt-bound (true V.∷ v)   = s≤s (wt-bound v)

  wt-pos :
    ∀ {n} {v : Vec Bool n} {i} → lookup v i ≡ true → 1 ≤ wt v
  wt-pos {v = b V.∷ v} {F.zero}  p rewrite p = s≤s z≤n
  wt-pos {v = b V.∷ v} {F.suc i} p =
    Nat.≤-trans (wt-pos {v = v} {i = i} p) (Nat.m≤n+m (wt v) (bitv b))

  -- ══════════════════════════════════════════════════════════════════
  --  Reachability over a concrete finite graph
  -- ══════════════════════════════════════════════════════════════════

  module _ (G : Graph) where

    open BTheory (graphTheory G) using (_∈T_; in/α; in/later)

    -- Graph transition with `G` fixed (State G alone does not determine G).
    Step : State G → Action → State G → Set
    Step s α t = _-<_>->_ {G} s α t

    -- ── Initial marking (only `s`) ──

    startMark : State G → Vec Bool (size G)
    startMark s = tabulate (λ t → ⌊ t ≟Fin s ⌋)

    ⌊≟⌋-refl : ∀ (s : State G) → ⌊ s ≟Fin s ⌋ ≡ true
    ⌊≟⌋-refl s with s ≟Fin s
    ... | yes _  = refl
    ... | no ¬p  = ⊥-elim (¬p refl)

    startMark-marks : ∀ s → lookup (startMark s) s ≡ true
    startMark-marks s = trans (VecP.lookup∘tabulate _ s) (⌊≟⌋-refl s)

    startMark-sound : ∀ {s t} → lookup (startMark s) t ≡ true → t ≡ s
    startMark-sound {s} {t} p =
      toWitness (≡true→T (trans (sym (VecP.lookup∘tabulate _ t)) p))

    -- ── One-step expansion ──

    OneStep : Vec Bool (size G) → (State G → Bool) → State G → Set
    OneStep m ok t =
      ∃[ s ] (T (lookup m s) × T (ok s) × Any (λ e → proj₂ e ≡ t) (edges G s))

    oneStepAt? :
      ∀ (m : Vec Bool (size G)) (ok : State G → Bool) (t s : State G)
      → Dec (T (lookup m s) × T (ok s)
             × Any (λ e → proj₂ e ≡ t) (edges G s))
    oneStepAt? m ok t s
      with T? (lookup m s) | T? (ok s)
         | Any.any? (λ e → proj₂ e ≟Fin t) (edges G s)
    ... | yes a | yes b | yes c = yes (a , b , c)
    ... | no ¬a | _     | _     = no λ { (a , _ , _) → ¬a a }
    ... | _     | no ¬b | _     = no λ { (_ , b , _) → ¬b b }
    ... | _     | _     | no ¬c = no λ { (_ , _ , c) → ¬c c }

    oneStep? : ∀ m ok t → Dec (OneStep m ok t)
    oneStep? m ok t = FinP.any? (oneStepAt? m ok t)

    expand : (State G → Bool) → Vec Bool (size G) → Vec Bool (size G)
    expand ok m = tabulate (λ t → lookup m t ∨ ⌊ oneStep? m ok t ⌋)

    expand-lookup :
      ∀ ok m t → lookup (expand ok m) t ≡ (lookup m t ∨ ⌊ oneStep? m ok t ⌋)
    expand-lookup ok m t = VecP.lookup∘tabulate _ t

    expand-infl :
      ∀ ok m t → lookup m t ≡ true → lookup (expand ok m) t ≡ true
    expand-infl ok m t p rewrite expand-lookup ok m t | p = refl

    expand-step :
      ∀ ok m {s α t}
      → lookup m s ≡ true → T (ok s) → Step s α t
      → lookup (expand ok m) t ≡ true
    expand-step ok m {s} {α} {t} ms oks gr
      with oneStep? m ok t | expand-lookup ok m t
    ... | yes _  | eqL = trans eqL (Bool.∨-zeroʳ (lookup m t))
    ... | no ¬os | _   =
      ⊥-elim (¬os
        (s , ≡true→T ms , oks
           , Any.map (λ px → sym (cong proj₂ px)) (step⇒listed {G = G} gr)))

    -- extract a graph edge witnessing the one-step successor
    findEdge :
      ∀ {t} (xs : List (Edge (size G)))
      → Any (λ e → proj₂ e ≡ t) xs
      → Σ[ α ∈ Action ] ((α , t) ∈ xs)
    findEdge (( α , u) ∷ xs) (here refl) = α , here refl
    findEdge (e ∷ xs) (there a) with findEdge xs a
    ... | α , mem = α , there mem

    expand-sound :
      ∀ ok m {t}
      → lookup (expand ok m) t ≡ true
      → (lookup m t ≡ true)
      ⊎ (∃[ s ] (lookup m s ≡ true × T (ok s) × ∃[ α ] (Step s α t)))
    expand-sound ok m {t} p with oneStep? m ok t | expand-lookup ok m t
    ... | yes (s , Tms , oks , anyWit) | _ =
      let (α , mem) = findEdge (edges G s) anyWit
      in inj₂ (s , T→≡true Tms , oks , α , listed⇒step {G = G} mem)
    ... | no _ | eqL =
      inj₁ (trans (sym (trans eqL (Bool.∨-identityʳ (lookup m t)))) p)

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

    -- ── Bridge to the declarative `Reachable` relation ──

    pathVia→reachable :
      ∀ {s t n} → PathVia (λ _ → true) s t n → Reachable {G} s t
    pathVia→reachable path/nil = reachable/refl
    pathVia→reachable (path/cons _ gr rest) =
      reachable/step gr tt (pathVia→reachable rest)

    reachable→pathVia :
      ∀ {s t} → Reachable {G} s t → ∃[ n ] PathVia (λ _ → true) s t n
    reachable→pathVia reachable/refl = zero , path/nil
    reachable→pathVia (reachable/step gr _ rest)
      with reachable→pathVia rest
    ... | n , p = suc n , path/cons tt gr p

    -- ── Completeness: every path is captured ──

    iter-infl :
      ∀ ok k m {i}
      → lookup m i ≡ true → lookup (iter k (expand ok) m) i ≡ true
    iter-infl ok zero    m p = p
    iter-infl ok (suc k) m {i} p =
      iter-infl ok k (expand ok m) (expand-infl ok m i p)

    complete-aux :
      ∀ ok (m : Vec Bool (size G)) k {a t n}
      → lookup m a ≡ true → PathVia ok a t n → n ≤ k
      → lookup (iter k (expand ok) m) t ≡ true
    complete-aux ok m k ma path/nil _ = iter-infl ok k m ma
    complete-aux ok m (suc k) ma (path/cons oka gr rest) (s≤s n≤k) =
      complete-aux ok (expand ok m) k (expand-step ok m ma oka gr) rest n≤k

    reachVia : (State G → Bool) → State G → Vec Bool (size G)
    reachVia ok s = iter (size G) (expand ok) (startMark s)

    -- ── Soundness ──

    iter-sound :
      ∀ ok (s : State G) k {t}
      → lookup (iter k (expand ok) (startMark s)) t ≡ true
      → ∃[ n ] PathVia ok s t n
    iter-sound ok s zero {t} p =
      zero , subst (λ z → PathVia ok s z zero) (sym (startMark-sound p)) path/nil
    iter-sound ok s (suc k) {t} p
      with expand-sound ok (iter k (expand ok) (startMark s))
             (subst (λ z → lookup z t ≡ true)
               (iter-suc k (expand ok) (startMark s)) p)
    ... | inj₁ pt = iter-sound ok s k pt
    ... | inj₂ (s′ , ms′ , oks′ , α , gr) with iter-sound ok s k ms′
    ...   | n , path = suc n , pathVia-snoc path oks′ gr

    reachVia-sound :
      ∀ ok s {t}
      → lookup (reachVia ok s) t ≡ true → ∃[ n ] PathVia ok s t n
    reachVia-sound ok s p = iter-sound ok s (size G) p

    -- ── Fixpoint saturation (bounded by `size G`) ──

    f-infl-row : ∀ ok X → Incl X (expand ok X)
    f-infl-row ok X i TXi = ≡true→T (expand-infl ok X i (T→≡true TXi))

    iter-extra :
      ∀ ok j X → Incl X (iter j (expand ok) X)
    iter-extra ok zero    X = Incl-refl {v = X}
    iter-extra ok (suc j) X =
      Incl-trans
        {a = X} {b = expand ok X} {c = iter j (expand ok) (expand ok X)}
        (f-infl-row ok X) (iter-extra ok j (expand ok X))

    grow :
      ∀ ok s k
      → (wt (startMark s) + k ≤ wt (iter k (expand ok) (startMark s)))
      ⊎ (expand ok (iter k (expand ok) (startMark s))
           ≡ iter k (expand ok) (startMark s))
    grow ok s zero = inj₁ (Nat.≤-reflexive (Nat.+-identityʳ (wt (startMark s))))
    grow ok s (suc k) = go (grow ok s k)
      where
        X : Vec Bool (size G)
        X = iter k (expand ok) (startMark s)

        fixStep :
          expand ok X ≡ X
          → expand ok (iter (suc k) (expand ok) (startMark s))
              ≡ iter (suc k) (expand ok) (startMark s)
        fixStep fix =
          let e : iter (suc k) (expand ok) (startMark s) ≡ X
              e = trans (iter-suc k (expand ok) (startMark s)) fix
          in trans (cong (expand ok) e) (trans fix (sym e))

        growStep :
          wt (startMark s) + k ≤ wt X
          → expand ok X ≢ X
          → wt (startMark s) + suc k
              ≤ wt (iter (suc k) (expand ok) (startMark s))
        growStep bound ¬fix =
          let strict : suc (wt X) ≤ wt (expand ok X)
              strict = wt/strict {left = X} {right = expand ok X}
                         (f-infl-row ok X) (λ e → ¬fix (sym e))
              weqn : wt (expand ok X)
                       ≡ wt (iter (suc k) (expand ok) (startMark s))
              weqn = cong wt (sym (iter-suc k (expand ok) (startMark s)))
              chain : suc (wt (startMark s) + k)
                        ≤ wt (iter (suc k) (expand ok) (startMark s))
              chain = subst (suc (wt (startMark s) + k) ≤_) weqn
                        (Nat.≤-trans (s≤s bound) strict)
          in subst (_≤ wt (iter (suc k) (expand ok) (startMark s)))
               (sym (Nat.+-suc (wt (startMark s)) k)) chain

        go :
          (wt (startMark s) + k ≤ wt X)
          ⊎ (expand ok X ≡ X)
          → (wt (startMark s) + suc k
               ≤ wt (iter (suc k) (expand ok) (startMark s)))
          ⊎ (expand ok (iter (suc k) (expand ok) (startMark s))
               ≡ iter (suc k) (expand ok) (startMark s))
        go (inj₂ fix) = inj₂ (fixStep fix)
        go (inj₁ bound) with VecP.≡-dec Bool._≟_ (expand ok X) X
        ... | yes fix = inj₂ (fixStep fix)
        ... | no ¬fix = inj₁ (growStep bound ¬fix)

    reach-fixed : ∀ ok s → expand ok (reachVia ok s) ≡ reachVia ok s
    reach-fixed ok s with grow ok s (size G)
    ... | inj₂ fix = fix
    ... | inj₁ bound = ⊥-elim (Nat.<-irrefl refl bad)
      where
        bad : size G < size G
        bad = Nat.≤-trans
                (Nat.+-monoˡ-≤ (size G)
                  (wt-pos {v = startMark s} {i = s} (startMark-marks s)))
                (Nat.≤-trans bound
                  (wt-bound (iter (size G) (expand ok) (startMark s))))

    fix-iter :
      ∀ ok s j → iter j (expand ok) (reachVia ok s) ≡ reachVia ok s
    fix-iter ok s zero = refl
    fix-iter ok s (suc j) =
      trans (iter-suc j (expand ok) (reachVia ok s))
        (trans (cong (expand ok) (fix-iter ok s j)) (reach-fixed ok s))

    converge :
      ∀ ok s n
      → Incl (iter n (expand ok) (startMark s)) (reachVia ok s)
    converge ok s n i x with Nat.≤-total n (size G)
    ... | inj₁ n≤ =
      subst (λ z → T (lookup (iter z (expand ok) (startMark s)) i))
        (Nat.m+[n∸m]≡n n≤)
        (subst (λ w → T (lookup w i))
          (sym (iter-add n (size G ∸ n) (expand ok) (startMark s)))
          (iter-extra ok (size G ∸ n) (iter n (expand ok) (startMark s)) i x))
    ... | inj₂ ≤n =
      subst (λ w → T (lookup w i)) eqn x
      where
        eqn : iter n (expand ok) (startMark s) ≡ reachVia ok s
        eqn =
          trans (cong (λ z → iter z (expand ok) (startMark s))
                   (sym (Nat.m+[n∸m]≡n ≤n)))
            (trans (iter-add (size G) (n ∸ size G) (expand ok) (startMark s))
              (fix-iter ok s (n ∸ size G)))

    reachVia-complete :
      ∀ ok s {t n} → PathVia ok s t n → lookup (reachVia ok s) t ≡ true
    reachVia-complete ok s {t} {n} path =
      T→≡true
        (converge ok s n t
          (≡true→T (complete-aux ok (startMark s) n (startMark-marks s) path Nat.≤-refl)))

    -- ══════════════════════════════════════════════════════════════
    --  Exact participation:  P ∈T s  ⇔  reach a P-active edge
    -- ══════════════════════════════════════════════════════════════

    ∈α-lift :
      ∀ {P x} {xs : List (Edge (size G))}
      → x ∈ xs → P ∈α proj₁ x → Any (λ e → P ∈α proj₁ e) xs
    ∈α-lift (here refl) px = here px
    ∈α-lift (there mem) px = there (∈α-lift mem px)

    anyActive→∈ :
      ∀ {P} (xs : List (Edge (size G)))
      → Any (λ e → P ∈α proj₁ e) xs
      → Σ[ e ∈ Edge (size G) ] (e ∈ xs × P ∈α proj₁ e)
    anyActive→∈ (e ∷ xs) (here px) = e , here refl , px
    anyActive→∈ (e ∷ xs) (there a) with anyActive→∈ xs a
    ... | e′ , mem , px = e′ , there mem , px

    activeToStep :
      ∀ {P s} → Any (λ e → P ∈α proj₁ e) (edges G s) → P ∈T s
    activeToStep {P} {s} a with anyActive→∈ (edges G s) a
    ... | (α , u) , mem , px = in/α (listed⇒step {G = G} mem) px

    reach→∈T :
      ∀ {P s t n}
      → PathVia (λ _ → true) s t n
      → Any (λ e → P ∈α proj₁ e) (edges G t)
      → P ∈T s
    reach→∈T path/nil active = activeToStep active
    reach→∈T (path/cons _ gr rest) active = in/later gr (reach→∈T rest active)

    ∈T→reach :
      ∀ {P s} → P ∈T s
      → ∃[ t ] (∃[ n ] PathVia (λ _ → true) s t n
                × Any (λ e → P ∈α proj₁ e) (edges G t))
    ∈T→reach {P} {s} (in/α gr px) =
      s , zero , path/nil , ∈α-lift (step⇒listed {G = G} gr) px
    ∈T→reach (in/later gr later) with ∈T→reach later
    ... | t , n , path , active = t , suc n , path/cons tt gr path , active

    active? : ∀ P t → Dec (Any (λ e → P ∈α proj₁ e) (edges G t))
    active? P t = Any.any? (λ e → P ∈α? proj₁ e) (edges G t)

    reachActiveAt? :
      ∀ P s t
      → Dec (T (lookup (reachVia (λ _ → true) s) t)
             × Any (λ e → P ∈α proj₁ e) (edges G t))
    reachActiveAt? P s t
      with T? (lookup (reachVia (λ _ → true) s) t) | active? P t
    ... | yes r | yes a = yes (r , a)
    ... | no ¬r | _     = no λ { (r , _) → ¬r r }
    ... | _     | no ¬a = no λ { (_ , a) → ¬a a }

    reachActive? :
      ∀ P s
      → Dec (∃[ t ] (T (lookup (reachVia (λ _ → true) s) t)
                     × Any (λ e → P ∈α proj₁ e) (edges G t)))
    reachActive? P s = FinP.any? (reachActiveAt? P s)

    ∈T? : ∀ (P : Part) (s : State G) → Dec (P ∈T s)
    ∈T? P s with reachActive? P s
    ... | yes (t , Tr , active) =
      yes (reach→∈T
             (proj₂ (reachVia-sound (λ _ → true) s (T→≡true Tr))) active)
    ... | no ¬ra = no λ P∈T → ¬ra (build P∈T)
      where
        build :
          P ∈T s
          → ∃[ t ] (T (lookup (reachVia (λ _ → true) s) t)
                    × Any (λ e → P ∈α proj₁ e) (edges G t))
        build P∈T with ∈T→reach P∈T
        ... | t , n , path , active =
          t , ≡true→T (reachVia-complete (λ _ → true) s path) , active
