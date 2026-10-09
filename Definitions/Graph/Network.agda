{-# OPTIONS --guardedness #-}

-- Networks of graphs: parallel (`∥`) and sequential (`⨾`) composition.
-- `NState n = Live n ⊎ ⊤`, with `nend` the one ended state.  `present` is
-- a finite graph with the same steps (`step⇒pres`, `pres⇒step`).

open import Data.Bool using (Bool; T)
open import Data.Fin using (Fin; inject₁; fromℕ) renaming (_≟_ to _≟Fin_)
open import Data.Fin.Relation.Unary.Top
  using (view; view-inject₁; view-fromℕ; ‵fromℕ; ‵inject₁)
open import Data.Fin.Properties using (+↔⊎; *↔×)
open import Function.Bundles using (_↔_; Inverse; mk↔ₛ′)
open import Function.Properties.Inverse using (↔-refl; ↔-trans)
open import Data.Sum.Function.Propositional using (_⊎-↔_)
open import Data.Product.Function.NonDependent.Propositional using (_×-↔_)
open import Data.List using (List; []; _++_)
import Data.List as List
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.DecPropositional as DecMem
import Data.List.Membership.Propositional.Properties as MemP
open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.Product using (_×_; _,_; Σ-syntax; map₂)
import Data.Product.Properties as ProdP
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum.Properties as SumP
open import Data.Unit using (⊤; tt)
import Data.Unit.Properties as UnitP
open import Data.Vec using (tabulate; lookup)
import Data.Vec.Properties as VecP
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)
open import Relation.Nullary.Decidable
  using (⌊_⌋; fromWitness; toWitness)

open import Definitions.Behav using (BTheory)

module Definitions.Graph.Network (N : ℕ) where

  open import Definitions.Actions N using (Action)
  open import Definitions.Graph.Action N using (_≟Action_)
  open import Definitions.Graph.Core N
    using (Graph; graph; edges; listed⇒step; step⇒listed)
    renaming (_-<_>->_ to GStep)
  open import Definitions.Graph.Algebra N
    using ( OpenGraph; nodes; root; table
          ; Ref; loop; node; ended
          ; RootedGraph; rooted; underlying )

  -- ── syntax ──

  infixr 7 _∥_
  infixr 6 _⨾_

  data Net : Set where
    base : OpenGraph 0 → Net
    _∥_  : Net → Net → Net
    _⨾_  : Net → Net → Net

  -- ── structured states ──

  lsize : Net → ℕ
  lsize (base G)  = nodes G
  lsize (n₁ ∥ n₂) = lsize n₂ + lsize n₁ * suc (lsize n₂)
  lsize (n₁ ⨾ n₂) = lsize n₂ + lsize n₁

  nsize : Net → ℕ
  nsize n = suc (lsize n)

  -- non-final states
  Live : Net → Set
  Live (base G)  = Fin (nodes G)
  Live (n₁ ∥ n₂) = Live n₂ ⊎ (Live n₁ × (Live n₂ ⊎ ⊤))
  Live (n₁ ⨾ n₂) = Live n₂ ⊎ Live n₁

  -- all states: the live ones plus THE unique ended state
  NState : Net → Set
  NState n = Live n ⊎ ⊤

  pattern live l = inj₁ l
  pattern nend   = inj₂ tt

  -- pairing view for `∥`: (end , end) is the product's end
  mkPair : ∀ {n₁ n₂} → NState n₁ → NState n₂ → NState (n₁ ∥ n₂)
  mkPair (live a) b        = live (inj₂ (a , b))
  mkPair nend     (live b) = live (inj₁ b)
  mkPair nend     nend     = nend

  -- right inclusion for `⨾`
  injR : ∀ {n₁ n₂} → NState n₂ → NState (n₁ ⨾ n₂)
  injR (live b) = live (inj₁ b)
  injR nend     = nend

  lEq? : ∀ n → DecidableEquality (Live n)
  lEq? (base G)  = _≟Fin_
  lEq? (n₁ ∥ n₂) =
    SumP.≡-dec (lEq? n₂)
      (ProdP.≡-dec (lEq? n₁) (SumP.≡-dec (lEq? n₂) UnitP._≟_))
  lEq? (n₁ ⨾ n₂) = SumP.≡-dec (lEq? n₂) (lEq? n₁)

  nEq? : ∀ n → DecidableEquality (NState n)
  nEq? n = SumP.≡-dec (lEq? n) UnitP._≟_

  -- ── semantics ──

  -- interpret a base graph's references as network states
  refState : ∀ (G : OpenGraph 0) → Ref 0 (nodes G) → NState (base G)
  refState G (loop ())
  refState G (node s) = live s
  refState G ended    = nend

  ninit : ∀ n → NState n
  ninit (base G)  = refState G (root G)
  ninit (n₁ ∥ n₂) = mkPair (ninit n₁) (ninit n₂)
  ninit (n₁ ⨾ n₂) with ninit n₁
  ... | live l = live (inj₂ l)
  ... | nend   = injR (ninit n₂)

  -- the seam: a step of `n₁` into its end is redirected to `n₂`'s start
  seamTo : ∀ n₁ n₂ → NState n₁ → NState (n₁ ⨾ n₂)
  seamTo n₁ n₂ (live l) = live (inj₂ l)
  seamTo n₁ n₂ nend     = injR (ninit n₂)

  nedges : ∀ n → NState n → List (Action × NState n)
  nedges n nend = []
  nedges (base G) (live s) =
    List.map (map₂ (refState G)) (lookup (table G) s)
  nedges (n₁ ∥ n₂) (live (inj₂ (a , b))) =
    List.map (map₂ (λ a′ → mkPair a′ b)) (nedges n₁ (live a))
    ++
    List.map (map₂ (mkPair (live a))) (nedges n₂ b)
  nedges (n₁ ∥ n₂) (live (inj₁ b)) =
    List.map (map₂ (mkPair nend)) (nedges n₂ (live b))
  nedges (n₁ ⨾ n₂) (live (inj₂ a)) =
    List.map (map₂ (seamTo n₁ n₂)) (nedges n₁ (live a))
  nedges (n₁ ⨾ n₂) (live (inj₁ b)) =
    List.map (map₂ injR) (nedges n₂ (live b))

  -- Boolean edge membership, so the step relation is propositional
  nstep? : ∀ n → NState n → Action → NState n → Bool
  nstep? n s α t =
    ⌊ DecMem._∈?_ (ProdP.≡-dec _≟Action_ (nEq? n)) (α , t) (nedges n s) ⌋

  -- A record, so its implicit states stay solvable (a raw `T (nstep? …)`
  -- reduces and loses them).
  record NStep (n : Net) (s : NState n) (α : Action) (t : NState n) : Set where
    constructor nstep
    field un : T (nstep? n s α t)

  open NStep public

  netTheory : Net → BTheory N
  netTheory n .BTheory.Behav = NState n
  netTheory n .BTheory._-<_>->_ = NStep n

  nlisted⇒step :
    ∀ n {s α t} → (α , t) ∈ nedges n s → NStep n s α t
  nlisted⇒step n m = nstep (fromWitness m)

  nstep⇒listed :
    ∀ n {s α t} → NStep n s α t → (α , t) ∈ nedges n s
  nstep⇒listed n st = toWitness (un st)

  -- ── the product steps: intro and inversion ──

  stepL :
    ∀ {n₁ n₂ a a′ α} (b : NState n₂)
    → NStep n₁ a α a′
    → NStep (n₁ ∥ n₂) (mkPair a b) α (mkPair a′ b)
  stepL {n₁} {n₂} {live a} b st =
    nlisted⇒step (n₁ ∥ n₂) {s = live (inj₂ (a , b))}
      (MemP.∈-++⁺ˡ
        (MemP.∈-map⁺ (map₂ (λ a′ → mkPair a′ b))
          (nstep⇒listed n₁ {s = live a} st)))
  stepL {n₁} {n₂} {nend} b ()

  stepR :
    ∀ {n₁ n₂ b b′ α} (a : NState n₁)
    → NStep n₂ b α b′
    → NStep (n₁ ∥ n₂) (mkPair a b) α (mkPair a b′)
  stepR {n₁} {n₂} {live b} (live a) st =
    nlisted⇒step (n₁ ∥ n₂) {s = live (inj₂ (a , live b))}
      (MemP.∈-++⁺ʳ _
        (MemP.∈-map⁺ (map₂ (mkPair (live a)))
          (nstep⇒listed n₂ {s = live b} st)))
  stepR {n₁} {n₂} {live b} nend st =
    nlisted⇒step (n₁ ∥ n₂) {s = live (inj₁ b)}
      (MemP.∈-map⁺ (map₂ (mkPair nend))
        (nstep⇒listed n₂ {s = live b} st))
  stepR {n₁} {n₂} {nend} a ()

  pstep-inv :
    ∀ n₁ n₂ {a b α t}
    → NStep (n₁ ∥ n₂) (mkPair a b) α t
    → (Σ[ a′ ∈ NState n₁ ] NStep n₁ a α a′ × t ≡ mkPair a′ b)
    ⊎ (Σ[ b′ ∈ NState n₂ ] NStep n₂ b α b′ × t ≡ mkPair a b′)
  pstep-inv n₁ n₂ {live a} {b} st
    with MemP.∈-++⁻
           (List.map (map₂ (λ a′ → mkPair a′ b)) (nedges n₁ (live a)))
           (nstep⇒listed (n₁ ∥ n₂) {s = live (inj₂ (a , b))} st)
  ... | inj₁ mL
    with MemP.∈-map⁻ (map₂ (λ a′ → mkPair a′ b)) mL
  ...   | (α₀ , a′) , m₀ , refl =
    inj₁ (a′ , nlisted⇒step n₁ {s = live a} m₀ , refl)
  pstep-inv n₁ n₂ {live a} {b} st
    | inj₂ mR
    with MemP.∈-map⁻ (map₂ (mkPair (live a))) mR
  ...   | (α₀ , b′) , m₀ , refl =
    inj₂ (b′ , nlisted⇒step n₂ {s = b} m₀ , refl)
  pstep-inv n₁ n₂ {nend} {live b} st
    with MemP.∈-map⁻ (map₂ (mkPair nend))
           (nstep⇒listed (n₁ ∥ n₂) {s = live (inj₁ b)} st)
  ... | (α₀ , b′) , m₀ , refl =
    inj₂ (b′ , nlisted⇒step n₂ {s = live b} m₀ , refl)
  pstep-inv n₁ n₂ {nend} {nend} ()

  -- ── the finite presentation ──

  -- `Fin (suc m)` is its `inject₁` part and its top, `fromℕ m`.
  private
    top↔ : ∀ {m} → Fin (suc m) ↔ (Fin m ⊎ ⊤)
    top↔ {m} = mk↔ₛ′ to from to∘from from∘to
      where
        to : Fin (suc m) → Fin m ⊎ ⊤
        to i with view i
        ... | ‵inject₁ s = inj₁ s
        ... | ‵fromℕ     = inj₂ tt

        from : Fin m ⊎ ⊤ → Fin (suc m)
        from (inj₁ s) = inject₁ s
        from (inj₂ _) = fromℕ m

        to∘from : ∀ x → to (from x) ≡ x
        to∘from (inj₁ s) rewrite view-inject₁ s = refl
        to∘from (inj₂ _) rewrite view-fromℕ m = refl

        from∘to : ∀ i → from (to i) ≡ i
        from∘to i with view i
        ... | ‵inject₁ _ = refl
        ... | ‵fromℕ     = refl

  -- `lsize` lays out `∥` as `Live n₂ ⊎ (Live n₁ × NState n₂)` and `⨾` as
  -- `Live n₂ ⊎ Live n₁`, so the encoding is `+↔⊎` and `*↔×` composed.
  mutual
    live↔ : ∀ n → Fin (lsize n) ↔ Live n
    live↔ (base G)  = ↔-refl
    live↔ (n₁ ∥ n₂) =
      ↔-trans (+↔⊎ {lsize n₂})
        (live↔ n₂ ⊎-↔ ↔-trans (*↔× {lsize n₁}) (live↔ n₁ ×-↔ state↔ n₂))
    live↔ (n₁ ⨾ n₂) =
      ↔-trans (+↔⊎ {lsize n₂}) (live↔ n₂ ⊎-↔ live↔ n₁)

    state↔ : ∀ n → Fin (nsize n) ↔ NState n
    state↔ n = ↔-trans top↔ (live↔ n ⊎-↔ ↔-refl)

  nst : ∀ n → Fin (nsize n) → NState n
  nst n = Inverse.to (state↔ n)

  nix : ∀ n → NState n → Fin (nsize n)
  nix n = Inverse.from (state↔ n)

  nst-nix : ∀ n s → nst n (nix n s) ≡ s
  nst-nix n = Inverse.strictlyInverseˡ (state↔ n)

  nix-nst : ∀ n i → nix n (nst n i) ≡ i
  nix-nst n = Inverse.strictlyInverseʳ (state↔ n)

  present : Net → RootedGraph
  present n =
    rooted
      (graph (nsize n)
        (tabulate λ i →
          List.map (map₂ (nix n)) (nedges n (nst n i))))
      (nix n (ninit n))

  private
    row-eq :
      ∀ n i
      → edges (underlying (present n)) i
        ≡ List.map (map₂ (nix n)) (nedges n (nst n i))
    row-eq n i =
      VecP.lookup∘tabulate
        (λ j → List.map (map₂ (nix n)) (nedges n (nst n j)))
        i

  -- transitions correspond across the presentation, in both directions
  step⇒pres :
    ∀ n {s α t}
    → NStep n s α t
    → GStep {underlying (present n)} (nix n s) α (nix n t)
  step⇒pres n {s} {α} {t} st =
    listed⇒step
      (subst ((α , nix n t) ∈_) (sym (row-eq n (nix n s)))
        (MemP.∈-map⁺ (map₂ (nix n))
          (subst (λ z → (α , t) ∈ nedges n z) (sym (nst-nix n s))
            (nstep⇒listed n {s = s} st))))

  pres⇒step :
    ∀ n {i α j}
    → GStep {underlying (present n)} i α j
    → NStep n (nst n i) α (nst n j)
  pres⇒step n {i} {α} {j} st
    with MemP.∈-map⁻ (map₂ (nix n))
           (subst ((α , j) ∈_) (row-eq n i)
             (step⇒listed st))
  ... | (α₀ , t₀) , m₀ , refl =
    subst (NStep n (nst n i) α₀) (sym (nst-nix n t₀))
      (nlisted⇒step n {s = nst n i} m₀)
