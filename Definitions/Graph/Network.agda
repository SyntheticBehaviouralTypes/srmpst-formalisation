{-# OPTIONS --guardedness #-}

-- Networks of graphs: *syntactic* parallel and sequential composition.
--
-- A network keeps its component open graphs — nothing is compiled or
-- flattened.  Its state space is structured:
--
--     NState n = Live n ⊎ ⊤
--
-- where `inj₂ tt` (pattern `nend`) is THE unique ended state of the network
-- and `Live n` are its non-final states:
--   * base graph: its allocated nodes (the open graph's `ended` reference is
--     interpreted as the network's end);
--   * `n₁ ∥ n₂`: pair states with at least one live side (`mkPair` builds
--     them from a pair of component states; (end , end) is the network's
--     end).  Each side transitions independently (`stepL`/`stepR`/
--     `pstep-inv`), which is what makes the cross-component diamond hold
--     trivially (`Definitions/Graph/NetworkWB.agda`);
--   * `n₁ ⨾ n₂` — run `n₁` to completion, then continue as `n₂`: the live
--     states of both sides; a step of `n₁` into its end is redirected to
--     `n₂`'s initial state, so the seam never duplicates an ended state.
--
-- For the (Fin-indexed) decision procedures every network has a finite
-- *presentation* (`present`, with `nix`/`nst` the state bijection and
-- `step⇒pres`/`pres⇒step` the transition correspondence) — a theorem-backed
-- view; the network itself is never materialized.

open import Data.Bool using (Bool; T)
open import Data.Fin
  using (Fin; combine; remQuot; splitAt; inject₁; fromℕ; _↑ˡ_; _↑ʳ_)
  renaming (_≟_ to _≟Fin_)
open import Data.Fin.Properties
  using ( remQuot-combine; combine-remQuot
        ; splitAt-↑ˡ; splitAt-↑ʳ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ )
open import Data.List using (List; []; _∷_; _++_)
import Data.List as List
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.DecPropositional as DecMem
import Data.List.Membership.Propositional.Properties as MemP
open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
import Data.Product.Properties as ProdP
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum.Properties as SumP
open import Data.Unit using (⊤; tt)
open import Data.Vec using (tabulate; lookup)
import Data.Vec.Properties as VecP
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable
  using (⌊_⌋; fromWitness; toWitness)

open import Definitions.Behav using (BTheory)

module Definitions.Graph.Network (N : ℕ) where

  open import Definitions.Actions N using (Action)
  open import Definitions.Graph.Action N using (_≟Action_)
  open import Definitions.Graph.Core N
    using (Graph; State; graph; size; edges; listed⇒step; step⇒listed)
    renaming (_-<_>->_ to GStep)
  open import Definitions.Graph.Algebra N
    using ( OpenGraph; openGraph; nodes; root; table
          ; Ref; loop; node; ended
          ; RootedGraph; rooted; underlying; initial )

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

  private
    ⊤Eq? : DecidableEquality ⊤
    ⊤Eq? tt tt = yes refl

  lEq? : ∀ n → DecidableEquality (Live n)
  lEq? (base G)  = _≟Fin_
  lEq? (n₁ ∥ n₂) =
    SumP.≡-dec (lEq? n₂)
      (ProdP.≡-dec (lEq? n₁) (SumP.≡-dec (lEq? n₂) ⊤Eq?))
  lEq? (n₁ ⨾ n₂) = SumP.≡-dec (lEq? n₂) (lEq? n₁)

  nEq? : ∀ n → DecidableEquality (NState n)
  nEq? n = SumP.≡-dec (lEq? n) ⊤Eq?

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
    List.map (λ e → proj₁ e , refState G (proj₂ e)) (lookup (table G) s)
  nedges (n₁ ∥ n₂) (live (inj₂ (a , b))) =
    List.map (λ e → proj₁ e , mkPair (proj₂ e) b) (nedges n₁ (live a))
    ++
    List.map (λ e → proj₁ e , mkPair (live a) (proj₂ e)) (nedges n₂ b)
  nedges (n₁ ∥ n₂) (live (inj₁ b)) =
    List.map (λ e → proj₁ e , mkPair nend (proj₂ e)) (nedges n₂ (live b))
  nedges (n₁ ⨾ n₂) (live (inj₂ a)) =
    List.map (λ e → proj₁ e , seamTo n₁ n₂ (proj₂ e)) (nedges n₁ (live a))
  nedges (n₁ ⨾ n₂) (live (inj₁ b)) =
    List.map (λ e → proj₁ e , injR (proj₂ e)) (nedges n₂ (live b))

  -- Boolean edge membership, so the step relation is propositional
  nstep? : ∀ n → NState n → Action → NState n → Bool
  nstep? n s α t =
    ⌊ DecMem._∈?_ (ProdP.≡-dec _≟Action_ (nEq? n)) (α , t) (nedges n s) ⌋

  -- The step relation is a *record* (a rigid head for unification — a raw
  -- `T (nstep? …)` makes every implicit source/target state unsolvable once
  -- goals reduce) wrapping the Boolean membership (so it is propositional).
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
        (MemP.∈-map⁺ (λ e → proj₁ e , mkPair (proj₂ e) b)
          (nstep⇒listed n₁ {s = live a} st)))
  stepL {n₁} {n₂} {nend} b ()

  stepR :
    ∀ {n₁ n₂ b b′ α} (a : NState n₁)
    → NStep n₂ b α b′
    → NStep (n₁ ∥ n₂) (mkPair a b) α (mkPair a b′)
  stepR {n₁} {n₂} {live b} (live a) st =
    nlisted⇒step (n₁ ∥ n₂) {s = live (inj₂ (a , live b))}
      (MemP.∈-++⁺ʳ _
        (MemP.∈-map⁺ (λ e → proj₁ e , mkPair (live a) (proj₂ e))
          (nstep⇒listed n₂ {s = live b} st)))
  stepR {n₁} {n₂} {live b} nend st =
    nlisted⇒step (n₁ ∥ n₂) {s = live (inj₁ b)}
      (MemP.∈-map⁺ (λ e → proj₁ e , mkPair nend (proj₂ e))
        (nstep⇒listed n₂ {s = live b} st))
  stepR {n₁} {n₂} {nend} a ()

  pstep-inv :
    ∀ n₁ n₂ {a b α t}
    → NStep (n₁ ∥ n₂) (mkPair a b) α t
    → (Σ[ a′ ∈ NState n₁ ] NStep n₁ a α a′ × t ≡ mkPair a′ b)
    ⊎ (Σ[ b′ ∈ NState n₂ ] NStep n₂ b α b′ × t ≡ mkPair a b′)
  pstep-inv n₁ n₂ {live a} {b} st
    with MemP.∈-++⁻
           (List.map (λ e → proj₁ e , mkPair (proj₂ e) b) (nedges n₁ (live a)))
           (nstep⇒listed (n₁ ∥ n₂) {s = live (inj₂ (a , b))} st)
  ... | inj₁ mL
    with MemP.∈-map⁻ (λ e → proj₁ e , mkPair (proj₂ e) b) mL
  ...   | (α₀ , a′) , m₀ , refl =
    inj₁ (a′ , nlisted⇒step n₁ {s = live a} m₀ , refl)
  pstep-inv n₁ n₂ {live a} {b} st
    | inj₂ mR
    with MemP.∈-map⁻ (λ e → proj₁ e , mkPair (live a) (proj₂ e)) mR
  ...   | (α₀ , b′) , m₀ , refl =
    inj₂ (b′ , nlisted⇒step n₂ {s = b} m₀ , refl)
  pstep-inv n₁ n₂ {nend} {live b} st
    with MemP.∈-map⁻ (λ e → proj₁ e , mkPair nend (proj₂ e))
           (nstep⇒listed (n₁ ∥ n₂) {s = live (inj₁ b)} st)
  ... | (α₀ , b′) , m₀ , refl =
    inj₂ (b′ , nlisted⇒step n₂ {s = live b} m₀ , refl)
  pstep-inv n₁ n₂ {nend} {nend} ()

  -- ── the finite presentation ──

  private
    data EndView : ∀ {m} → Fin (suc m) → Set where
      ev-node : ∀ {m} (s : Fin m) → EndView (inject₁ s)
      ev-end  : ∀ {m} → EndView (fromℕ m)

    endView : ∀ {m} (i : Fin (suc m)) → EndView i
    endView {ℕ.zero} Fin.zero    = ev-end
    endView {suc m}  Fin.zero    = ev-node Fin.zero
    endView {suc m}  (Fin.suc i) with endView i
    ... | ev-node s = ev-node (Fin.suc s)
    ... | ev-end    = ev-end

    endView-inject₁ :
      ∀ {m} (s : Fin m) → endView (inject₁ s) ≡ ev-node s
    endView-inject₁ Fin.zero    = refl
    endView-inject₁ (Fin.suc s) rewrite endView-inject₁ s = refl

    endView-fromℕ : ∀ {m} → endView (fromℕ m) ≡ ev-end
    endView-fromℕ {ℕ.zero} = refl
    endView-fromℕ {suc m}  rewrite endView-fromℕ {m} = refl

  mutual
    lix : ∀ n → Live n → Fin (lsize n)
    lix (base G)  s = s
    lix (n₁ ∥ n₂) (inj₁ b) = lix n₂ b ↑ˡ (lsize n₁ * suc (lsize n₂))
    lix (n₁ ∥ n₂) (inj₂ (a , b)) =
      lsize n₂ ↑ʳ combine (lix n₁ a) (nix n₂ b)
    lix (n₁ ⨾ n₂) (inj₁ b) = lix n₂ b ↑ˡ lsize n₁
    lix (n₁ ⨾ n₂) (inj₂ a) = lsize n₂ ↑ʳ lix n₁ a

    nix : ∀ n → NState n → Fin (nsize n)
    nix n (live l) = inject₁ (lix n l)
    nix n nend     = fromℕ (lsize n)

  mutual
    lst : ∀ n → Fin (lsize n) → Live n
    lst (base G)  i = i
    lst (n₁ ∥ n₂) i with splitAt (lsize n₂) i
    ... | inj₁ j = inj₁ (lst n₂ j)
    ... | inj₂ k =
      inj₂ ( lst n₁ (proj₁ (remQuot {lsize n₁} (suc (lsize n₂)) k))
           , nst n₂ (proj₂ (remQuot {lsize n₁} (suc (lsize n₂)) k)) )
    lst (n₁ ⨾ n₂) i with splitAt (lsize n₂) i
    ... | inj₁ j = inj₁ (lst n₂ j)
    ... | inj₂ k = inj₂ (lst n₁ k)

    nst : ∀ n → Fin (nsize n) → NState n
    nst n i with endView i
    ... | ev-node s = live (lst n s)
    ... | ev-end    = nend

  mutual
    lst-lix : ∀ n l → lst n (lix n l) ≡ l
    lst-lix (base G) l = refl
    lst-lix (n₁ ∥ n₂) (inj₁ b)
      rewrite splitAt-↑ˡ (lsize n₂) (lix n₂ b) (lsize n₁ * suc (lsize n₂)) =
      cong inj₁ (lst-lix n₂ b)
    lst-lix (n₁ ∥ n₂) (inj₂ (a , b))
      rewrite splitAt-↑ʳ (lsize n₂) (lsize n₁ * suc (lsize n₂))
                (combine (lix n₁ a) (nix n₂ b)) =
      cong inj₂
        (cong₂ _,_
          (trans
            (cong (lst n₁)
              (cong proj₁ (remQuot-combine {lsize n₁} {suc (lsize n₂)}
                             (lix n₁ a) (nix n₂ b))))
            (lst-lix n₁ a))
          (trans
            (cong (nst n₂)
              (cong proj₂ (remQuot-combine {lsize n₁} {suc (lsize n₂)}
                             (lix n₁ a) (nix n₂ b))))
            (nst-nix n₂ b)))
    lst-lix (n₁ ⨾ n₂) (inj₁ b)
      rewrite splitAt-↑ˡ (lsize n₂) (lix n₂ b) (lsize n₁) =
      cong inj₁ (lst-lix n₂ b)
    lst-lix (n₁ ⨾ n₂) (inj₂ a)
      rewrite splitAt-↑ʳ (lsize n₂) (lsize n₁) (lix n₁ a) =
      cong inj₂ (lst-lix n₁ a)

    nst-nix : ∀ n s → nst n (nix n s) ≡ s
    nst-nix n (live l) rewrite endView-inject₁ (lix n l) =
      cong live (lst-lix n l)
    nst-nix n nend rewrite endView-fromℕ {lsize n} = refl

  mutual
    lix-lst : ∀ n i → lix n (lst n i) ≡ i
    lix-lst (base G) i = refl
    lix-lst (n₁ ∥ n₂) i with splitAt (lsize n₂) i in eq
    ... | inj₁ j =
      trans (cong (_↑ˡ (lsize n₁ * suc (lsize n₂))) (lix-lst n₂ j))
        (splitAt⁻¹-↑ˡ eq)
    ... | inj₂ k =
      trans
        (cong (lsize n₂ ↑ʳ_)
          (trans
            (cong₂ combine
              (lix-lst n₁ (proj₁ (remQuot {lsize n₁} (suc (lsize n₂)) k)))
              (nix-nst n₂ (proj₂ (remQuot {lsize n₁} (suc (lsize n₂)) k))))
            (combine-remQuot {lsize n₁} (suc (lsize n₂)) k)))
        (splitAt⁻¹-↑ʳ eq)
    lix-lst (n₁ ⨾ n₂) i with splitAt (lsize n₂) i in eq
    ... | inj₁ j =
      trans (cong (_↑ˡ lsize n₁) (lix-lst n₂ j)) (splitAt⁻¹-↑ˡ eq)
    ... | inj₂ k =
      trans (cong (lsize n₂ ↑ʳ_) (lix-lst n₁ k)) (splitAt⁻¹-↑ʳ eq)

    nix-nst : ∀ n i → nix n (nst n i) ≡ i
    nix-nst n i with endView i
    ... | ev-node s = cong inject₁ (lix-lst n s)
    ... | ev-end    = refl

  present : Net → RootedGraph
  present n =
    rooted
      (graph (nsize n)
        (tabulate λ i →
          List.map (λ e → proj₁ e , nix n (proj₂ e)) (nedges n (nst n i))))
      (nix n (ninit n))

  private
    row-eq :
      ∀ n i
      → edges (underlying (present n)) i
        ≡ List.map (λ e → proj₁ e , nix n (proj₂ e)) (nedges n (nst n i))
    row-eq n i =
      VecP.lookup∘tabulate
        (λ j → List.map (λ e → proj₁ e , nix n (proj₂ e)) (nedges n (nst n j)))
        i

  -- transitions correspond across the presentation, in both directions
  step⇒pres :
    ∀ n {s α t}
    → NStep n s α t
    → GStep {underlying (present n)} (nix n s) α (nix n t)
  step⇒pres n {s} {α} {t} st =
    listed⇒step {G = underlying (present n)} {s = nix n s}
      (subst ((α , nix n t) ∈_) (sym (row-eq n (nix n s)))
        (MemP.∈-map⁺ (λ e → proj₁ e , nix n (proj₂ e))
          (subst (λ z → (α , t) ∈ nedges n z) (sym (nst-nix n s))
            (nstep⇒listed n {s = s} st))))

  pres⇒step :
    ∀ n {i α j}
    → GStep {underlying (present n)} i α j
    → NStep n (nst n i) α (nst n j)
  pres⇒step n {i} {α} {j} st
    with MemP.∈-map⁻ (λ e → proj₁ e , nix n (proj₂ e))
           (subst ((α , j) ∈_) (row-eq n i)
             (step⇒listed {G = underlying (present n)} {s = i} st))
  ... | (α₀ , t₀) , m₀ , refl =
    subst (NStep n (nst n i) α₀) (sym (nst-nix n t₀))
      (nlisted⇒step n {s = nst n i} m₀)
