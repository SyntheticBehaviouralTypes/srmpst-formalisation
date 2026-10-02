{-# OPTIONS --guardedness #-}

-- Is "the quotiented LTS is well behaved" a usable multi-role condition, and
-- which of the repo's protocols pass it?
--
-- A role assignment is a map `ρ : Part → Part` sending each role to the name
-- of its process (a process with no roles is simply never mentioned).  The
-- quotient relabels every edge `P ⟶ Qs # c` as `ρ P ⟶ image ρ Qs # c`, on
-- the SAME states.  It is admissible only if no edge has the sender's process
-- among its receivers' processes: that rules out internal steps (all roles in
-- one process) and mixed steps (a process both sending and receiving), which
-- have no single-role reading.  The verdict then runs `wellBehaved?` and
-- `synchronous?` on the quotient graph.
--
-- There is one quotient PER PROCESS: only the roles of a merger see it.  A
-- process `Ps` is typed, as a single role, against the quotient merging `Ps`
-- and leaving every other role individual; singleton processes are typed
-- against the original LTS.  The original is the specification every view
-- is derived from, so it must ALWAYS pass (`V (λ i → i)`), whether or not a
-- singleton exists.  Each `merge a b` below is the view of process `{a, b}`.
--
-- `V` is the strict quotient above; `HV` is the WEAK one (module `Hidden`),
-- which allows internal steps and hides them.
--
-- The graphs are copied from `Examples/` and `Tests/` (importing those would
-- re-run their typing decisions).  Every verdict is FORCED by `refl`.

module Tests.Quotient where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; not)
open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.List
  using (List; []; _∷_; foldr; any; all; allFin; _++_; concatMap; length; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing; maybe′; _>>=_) renaming (map to mapᵐ)
open import Data.Nat using (ℕ) renaming (zero to zeroℕ; suc to sucℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; lookup; tabulate; fromList)
  renaming ([] to v[]; _∷_ to _v∷_; map to mapV)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Definitions.Expr using (s/bool; s/nat; s/unit)

data Verdict : Set where
  inadmissible notWB notSync ok : Verdict

-- Relabelling can make distinct states bisimilar (NoSynGT's {B,C} view is
-- `A→BC . A→BC . end` with the middle state duplicated), and a bisimilar
-- duplicate breaks `stepback/~`.  A view is meant up to `~`, so every view
-- is minimised — states identified by the repo's own bisimilarity matrix —
-- before it is judged.
module Minimise (N : ℕ) where
  open import Definitions.Graph.Core N
  open import Definitions.Graph.Bisimulation N using (Matrix; related; approximation)

  seqL : ∀ {A : Set} → List (Maybe A) → Maybe (List A)
  seqL []             = just []
  seqL (m ∷ ms) with m | seqL ms
  ... | just a | just as = just (a ∷ as)
  ... | _      | _       = nothing

  seqV : ∀ {A : Set} {m} → Vec (Maybe A) m → Maybe (Vec A m)
  seqV v[]        = just v[]
  seqV (m v∷ ms) with m | seqV ms
  ... | just a | just as = just (a v∷ as)
  ... | _      | _       = nothing

  indexOf : ∀ {n} → Fin n → (xs : List (Fin n)) → Maybe (Fin (length xs))
  indexOf t []       = nothing
  indexOf t (x ∷ xs) = if ⌊ t ≟ x ⌋ then just zero else mapᵐ suc (indexOf t xs)

  -- `M` is the bisimilarity matrix, passed as an argument so it is shared.
  module _ (G : Graph) (M : Matrix G) where

    rep : State G → State G
    rep s = foldr (λ t r → if related G M t s then t else r) s (allFin (size G))

    kept : List (State G)
    kept = filterᵇ (λ s → ⌊ rep s ≟ s ⌋) (allFin (size G))

    minimal : Maybe Graph
    minimal =
      mapᵐ (graph (length kept))
        (seqV (mapV (λ s → seqL (Data.List.map
                                   (λ { (α , t) → mapᵐ (α ,_) (indexOf (rep t) kept) })
                                   (edges G s)))
                    (fromList kept)))

  minimise : Graph → Maybe Graph
  minimise G = minimal G (approximation G)

  -- The part of a graph reachable from `root`, renumbered.  Fuel: each step
  -- either shrinks the frontier or visits a new state.
  module _ {n : ℕ} (out : Vec (List (Edge n)) n) where

    visit : ℕ → List (Fin n) → List (Fin n) → List (Fin n)
    visit zeroℕ    vis _        = vis
    visit (sucℕ f) vis []       = vis
    visit (sucℕ f) vis (s ∷ fr) =
      if any (λ v → ⌊ v ≟ s ⌋) vis
      then visit (sucℕ f) vis fr
      else visit f (s ∷ vis) (Data.List.map proj₂ (lookup out s) ++ fr)

    module _ (root : Fin n) where

      reached : List (Fin n)
      reached = filterᵇ (λ s → any (λ v → ⌊ v ≟ s ⌋) (visit (sucℕ n) [] (root ∷ [])))
                        (allFin n)

      restrict : Maybe Graph
      restrict =
        mapᵐ (graph (length reached))
          (seqV (mapV (λ s → seqL (Data.List.map
                                     (λ { (α , t) → mapᵐ (α ,_) (indexOf t reached) })
                                     (lookup out s)))
                      (fromList reached)))

module Quotient (N : ℕ) where
  open import Definitions.Common N using (Part; PartSet)
  open import Definitions.Actions N
  open import Definitions.Graph.Core N
  open import Definitions.Graph.Decision N using (wellBehaved?; synchronous?)
  open Minimise N using (minimise)

  -- `merge a b`: role `b` joins `a`'s process.
  merge : Part → Part → Part → Part
  merge a b i = if ⌊ i ≟ b ⌋ then a else i

  module _ (ρ : Part → Part) where

    image : PartSet → PartSet
    image Qs = tabulate λ j → any (λ i → lookup Qs i ∧ ⌊ ρ i ≟ j ⌋) (allFin N)

    sender : Action → Maybe (Part × PartSet × Choice)
    sender α = foldr pick nothing (allFin N)
      where
        pick : Part → Maybe (Part × PartSet × Choice) → Maybe (Part × PartSet × Choice)
        pick P r with lookup α P
        ... | just ((! Qs) # c) = just (P , Qs , c)
        ... | _                 = r

    qAction : Action → Maybe Action
    qAction α with sender α
    ... | nothing          = nothing
    ... | just (P , Qs , c) =
      if lookup (image Qs) (ρ P) then nothing else just (ρ P ⟶ image Qs # c)

    qEdges : ∀ {n} → List (Edge n) → Maybe (List (Edge n))
    qEdges []             = just []
    qEdges ((α , t) ∷ es) with qAction α | qEdges es
    ... | just β | just es′ = just ((β , t) ∷ es′)
    ... | _      | _        = nothing

    qOut : ∀ {n m} → Vec (List (Edge n)) m → Maybe (Vec (List (Edge n)) m)
    qOut v[]        = just v[]
    qOut (es v∷ vs) with qEdges es | qOut vs
    ... | just es′ | just vs′ = just (es′ v∷ vs′)
    ... | _        | _        = nothing

    quotient : Graph → Maybe Graph
    quotient (graph n out) = mapᵐ (graph n) (qOut out)

    verdict : Graph → Verdict
    verdict G = maybe′ judge inadmissible (quotient G >>= minimise)
      where
        judge : Graph → Verdict
        judge G′ =
          if ⌊ wellBehaved? G′ ⌋
          then (if ⌊ synchronous? G′ ⌋ then ok else notSync)
          else notWB

-- The WEAK quotient: internal steps allowed, and hidden.
--
-- An edge relabels to its OUTSIDE part, `ρ P ⟶ (image ρ Qs ∖ ρ P) # c`; if
-- that is empty the edge is internal (τ).  A mixed multicast thus keeps its
-- outside receivers.  τ is EAGER, as in PLAN's strict `skip/step`: a state
-- with a τ step offers only what its τ-closure's stable states offer, so a
-- process with an internal choice makes it at its next external action.
-- States with the same closure SET offer the same weak behaviour, so they
-- are identified (else they survive as bisimilar duplicates and break
-- `stepback/~`); a state with several stable states in its closure is a
-- choice node.  Edges are only ever read off stable states, retargeted
-- through that identification, and the graph is renumbered to the
-- representatives.  An internal loop contributes only its exits.
module Hidden (N : ℕ) where
  open import Definitions.Common N using (Part; PartSet)
  open import Definitions.Actions N
  open import Definitions.Graph.Core N
  open import Definitions.Graph.Decision N using (wellBehaved?; synchronous?)
  open Quotient N using (image; sender)
  open Minimise N using (seqL; seqV; indexOf; minimise)

  module _ (ρ : Part → Part) where

    -- `just nothing`: internal; `just (just β)`: its outside part.
    hide : Action → Maybe (Maybe Action)
    hide α with sender ρ α
    ... | nothing          = nothing
    ... | just (P , Qs , c) =
      let Rs = tabulate λ j → lookup (image ρ Qs) j ∧ not ⌊ j ≟ ρ P ⌋
      in if any (lookup Rs) (allFin N) then just (just (ρ P ⟶ Rs # c))
         else just nothing

    module _ {n : ℕ} where

      classify : List (Edge n) → Maybe (List (Fin n) × List (Edge n))
      classify []             = just ([] , [])
      classify ((α , t) ∷ es) with hide α | classify es
      ... | just nothing  | just (ts , xs) = just (t ∷ ts , xs)
      ... | just (just β) | just (ts , xs) = just (ts , (β , t) ∷ xs)
      ... | _             | _              = nothing

      -- `cls s` = (τ-successors, outside edges) of `s`, computed once.
      module _ (cls : Vec (List (Fin n) × List (Edge n)) n) where

        -- The stable states reachable by τ, with a visited list, so an
        -- internal loop contributes only its exits.  The fuel `suc n`
        -- never runs out: each call extends the visited list.
        closure  : ℕ → List (Fin n) → Fin n → Maybe (List (Fin n))
        closures : ℕ → List (Fin n) → List (Fin n) → Maybe (List (Fin n))
        closure zeroℕ    vis s = nothing
        closure (sucℕ f) vis s with any (λ v → ⌊ v ≟ s ⌋) vis | proj₁ (lookup cls s)
        ... | true  | _        = just []
        ... | false | []       = just (s ∷ [])
        ... | false | (t ∷ ts) = closures f (s ∷ vis) (t ∷ ts)
        closures f vis []       = just []
        closures f vis (t ∷ ts) with closure f vis t | closures f vis ts
        ... | just a | just b = just (a ++ b)
        ... | _      | _      = nothing

        -- `clos s` = the closure of `s`, computed once.
        module _ (clos : Vec (List (Fin n)) n) where

          sameSet : List (Fin n) → List (Fin n) → Bool
          sameSet xs ys = all (λ x → any (λ y → ⌊ x ≟ y ⌋) ys) xs
                        ∧ all (λ y → any (λ x → ⌊ x ≟ y ⌋) xs) ys

          -- The first state with the same closure SET: states offering
          -- the same weak behaviour become one.
          rep : Fin n → Fin n
          rep t = foldr (λ s r → if sameSet (lookup clos s) (lookup clos t) then s else r)
                        t (allFin n)

          -- The weak edges of `s`, targets through `rep`.
          weakEdges : Fin n → List (Edge n)
          weakEdges s =
            Data.List.map (λ { (β , t) → (β , rep t) })
              (concatMap (λ u → proj₂ (lookup cls u)) (lookup clos s))

          -- Reachability in the weak graph.  Hiding τ orphans states (the
          -- branches behind a choice node), which are not part of the view.
          -- Fuel: each step either shrinks the frontier or visits a new state.
          visit : ℕ → List (Fin n) → List (Fin n) → List (Fin n)
          visit zeroℕ    vis _        = vis
          visit (sucℕ f) vis []       = vis
          visit (sucℕ f) vis (s ∷ fr) =
            if any (λ v → ⌊ v ≟ s ⌋) vis
            then visit (sucℕ f) vis fr
            else visit f (s ∷ vis)
                   (Data.List.map proj₂ (weakEdges s) ++ fr)

          module _ (root : Fin n) where

            reachable : List (Fin n)
            reachable = visit (sucℕ n) [] (rep root ∷ [])

            kept : List (Fin n)
            kept = filterᵇ (λ s → ⌊ rep s ≟ s ⌋ ∧ any (λ v → ⌊ v ≟ s ⌋) reachable)
                           (allFin n)

            edgesOf : Fin n → Maybe (List (Edge (length kept)))
            edgesOf s =
              seqL (Data.List.map
                      (λ { (β , t) → mapᵐ (β ,_) (indexOf t kept) })
                      (weakEdges s))

            weak : Maybe Graph
            weak = mapᵐ (graph (length kept)) (seqV (mapV edgesOf (fromList kept)))

    weakQuotient : (G : Graph) → State G → Maybe Graph
    weakQuotient (graph n out) root =
      seqV (mapV classify out)                         >>= λ cls →
      seqV (tabulate (closure cls (sucℕ n) []))        >>= λ clos →
      weak cls clos root

    verdict : (G : Graph) → State G → Verdict
    verdict G root = maybe′ judge inadmissible (weakQuotient G root >>= minimise)
      where
        judge : Graph → Verdict
        judge G′ =
          if ⌊ wellBehaved? G′ ⌋
          then (if ⌊ synchronous? G′ ⌋ then ok else notSync)
          else notWB

-- ORDERED views: a mixed choice is resolved by a fixed global order.
--
-- An action's key is (sender, receiver set), compared lexicographically on
-- role indices.  In process `p`'s view (the roles `i` with `ρ i ≡ p`), at
-- each state, an external edge is DROPPED when a smaller edge at the same
-- state conflicts with it: `p` sends in one and receives in the other
-- (mixed choice), or — with `senders = true` — `p` receives in both, from
-- different senders.  In a role-level well-behaved graph such a pair is
-- always a diamond (`recv-overlap` does not relate them, so `step-diamond`
-- commutes them), so pruning removes an interleaving, never a branch.  The
-- order is global, so every view drops the same one.  Pruning happens on the
-- ROLE-level graph, before quotienting; states it orphans are removed
-- (`restrict`, and `Hidden`'s own reachability).  The original LTS, for
-- singleton processes, is not pruned.
module Ordered (N : ℕ) where
  open import Definitions.Common N using (Part; PartSet)
  open import Definitions.Actions N
  open import Definitions.Graph.Core N
  open import Definitions.Graph.Decision N using (wellBehaved?; synchronous?)
  open Quotient N using (sender; qOut)
  open Minimise N using (minimise; restrict)
  open import Data.Nat using (_<ᵇ_)
  open import Data.Fin using (toℕ)

  -- lexicographic, `false < true`
  ltBits : ∀ {m} → Vec Bool m → Vec Bool m → Bool
  ltBits v[]       v[]       = false
  ltBits (x v∷ xs) (y v∷ ys) =
    if (x ∧ y) Data.Bool.∨ (not x ∧ not y) then ltBits xs ys else (not x ∧ y)

  module _ (ρ : Part → Part) (p : Part) (senders : Bool) where

    mine : Part → Bool
    mine i = ⌊ ρ i ≟ p ⌋

    -- (sender, receivers) of an action, if it is a multicast
    parts : Action → Maybe (Part × PartSet)
    parts α = mapᵐ (λ { (P , Qs , _) → (P , Qs) }) (sender ρ α)

    sends recvs : Action → Bool
    sends α = maybe′ (λ { (P , Qs) → mine P ∧ any (λ i → lookup Qs i ∧ not (mine i)) (allFin N) })
                     false (parts α)
    recvs α = maybe′ (λ { (P , Qs) → not (mine P) ∧ any (λ i → lookup Qs i ∧ mine i) (allFin N) })
                     false (parts α)

    lt : Action → Action → Bool
    lt α β with parts α | parts β
    ... | just (P , Qs) | just (P′ , Qs′) =
      (toℕ P <ᵇ toℕ P′) Data.Bool.∨ (⌊ P ≟ P′ ⌋ ∧ ltBits Qs Qs′)
    ... | _ | _ = false

    otherSender : Action → Action → Bool
    otherSender α β with parts α | parts β
    ... | just (P , _) | just (P′ , _) = not ⌊ P ≟ P′ ⌋
    ... | _ | _ = false

    conflict : Action → Action → Bool
    conflict α β = (sends α ∧ recvs β) Data.Bool.∨ (recvs α ∧ sends β)
                   Data.Bool.∨ (senders ∧ recvs α ∧ recvs β ∧ otherSender α β)

    pruneEdges : ∀ {n} → List (Edge n) → List (Edge n)
    pruneEdges es =
      filterᵇ (λ e → not (any (λ e′ → conflict (proj₁ e′) (proj₁ e) ∧ lt (proj₁ e′) (proj₁ e)) es))
              es

    judge : Graph → Verdict
    judge G′ =
      if ⌊ wellBehaved? G′ ⌋
      then (if ⌊ synchronous? G′ ⌋ then ok else notSync)
      else notWB

    -- strict view, pruned
    sverdict : (G : Graph) → State G → Verdict
    sverdict (graph n out) root with qOut ρ (mapV pruneEdges out)
    ... | nothing   = inadmissible
    ... | just out′ = maybe′ judge inadmissible (restrict out′ root >>= minimise)

    -- weak view, pruned
    hverdict : (G : Graph) → State G → Verdict
    hverdict (graph n out) root = Hidden.verdict N ρ (graph n (mapV pruneEdges out)) root

-- ══════════════════════════════════════════════════════════════════════
--  Three roles
-- ══════════════════════════════════════════════════════════════════════

module Three where
  open import Definitions.Graph.Algebra 3
  open import Data.Fin.Subset using (⁅_⁆; _∪_)
  open import Definitions.Actions 3 renaming (_<_> to mkChoice)
  open Quotient 3

  A B C : Fin 3
  A = zero
  B = suc zero
  C = suc (suc zero)

  here : Fin 1
  here = zero

  lbl0 lbl1 : Fin 2
  lbl0 = zero
  lbl1 = suc zero

  V : (Fin 3 → Fin 3) → OpenGraph 0 → Verdict
  V ρ g = verdict ρ (underlying (compile g))

  HV : (Fin 3 → Fin 3) → OpenGraph 0 → Verdict
  HV ρ g = Hidden.verdict 3 ρ (underlying (compile g)) (initial (compile g))

  -- ordered views of process `p`: weak (`OV`, `OV⁺` also orders receives
  -- from different senders) and strict (`OS`)
  OV OV⁺ OS : (Fin 3 → Fin 3) → Fin 3 → OpenGraph 0 → Verdict
  OV  ρ p g = Ordered.hverdict 3 ρ p false (underlying (compile g)) (initial (compile g))
  OV⁺ ρ p g = Ordered.hverdict 3 ρ p true  (underlying (compile g)) (initial (compile g))
  OS  ρ p g = Ordered.sverdict 3 ρ p false (underlying (compile g)) (initial (compile g))

  -- Examples/RoundRobin.agda, NonRecursive: A → B → C → A.
  -- Every pair of roles talks directly, so every merge has an internal step.
  module RoundRobin where
    round : OpenGraph 0
    round =
      (A ⟶ ⁅ B ⁆ # mkChoice here s/bool) ∙
      ((B ⟶ ⁅ C ⁆ # mkChoice here s/bool) ∙
       ((C ⟶ ⁅ A ⁆ # mkChoice here s/bool) ∙ end))

    _ : V (λ i → i) round ≡ ok
    _ = refl

    _ : V (merge A B) round ≡ inadmissible
    _ = refl
    _ : V (merge A C) round ≡ inadmissible
    _ = refl
    _ : V (merge B C) round ≡ inadmissible
    _ = refl

    _ : HV (merge A B) round ≡ ok
    _ = refl
    _ : HV (merge A C) round ≡ ok
    _ = refl
    _ : HV (merge B C) round ≡ ok
    _ = refl

    _ : OV (merge A B) A round ≡ ok
    _ = refl
    _ : OV (merge A C) A round ≡ ok
    _ = refl
    _ : OV (merge B C) B round ≡ ok
    _ = refl

  -- Examples/OAuth2.agda (S, C, A renamed A, B, C): S→C, C→A, A→S.
  module OAuth2 where
    S′ C′ A′ : Fin 3
    S′ = A
    C′ = B
    A′ = C

    oauth : OpenGraph 0
    oauth = openGraph 4 (node zero)
      ( ( ((S′ ⟶ ⁅ C′ ⁆ # mkChoice lbl0 s/nat) , node (suc zero))
        ∷ ((S′ ⟶ ⁅ C′ ⁆ # mkChoice lbl1 s/nat) , node (suc (suc (suc zero))))
        ∷ [] )
      v∷ ( ((C′ ⟶ ⁅ A′ ⁆ # mkChoice lbl0 s/nat) , node (suc (suc zero))) ∷ [] )
      v∷ ( ((A′ ⟶ ⁅ S′ ⁆ # mkChoice here s/bool) , ended) ∷ [] )
      v∷ ( ((C′ ⟶ ⁅ A′ ⁆ # mkChoice lbl1 s/bool) , ended) ∷ [] )
      v∷ v[]
      )

    _ : V (λ i → i) oauth ≡ ok
    _ = refl

    _ : V (merge S′ C′) oauth ≡ inadmissible
    _ = refl
    _ : V (merge S′ A′) oauth ≡ inadmissible
    _ = refl
    _ : V (merge C′ A′) oauth ≡ inadmissible
    _ = refl

    _ : HV (merge S′ C′) oauth ≡ ok
    _ = refl
    _ : HV (merge S′ A′) oauth ≡ ok
    _ = refl
    _ : HV (merge C′ A′) oauth ≡ ok
    _ = refl

    _ : OV (merge S′ C′) S′ oauth ≡ ok
    _ = refl
    _ : OV (merge S′ A′) S′ oauth ≡ ok
    _ = refl
    _ : OV (merge C′ A′) C′ oauth ≡ ok
    _ = refl

  -- Examples/Rec2Buy.agda (A, B, S): `B` and `S` never talk to each other.
  module Rec2Buy where
    S : Fin 3
    S = C

    rec2buy : OpenGraph 0
    rec2buy = openGraph 6 (node zero)
      (  ( ((A ⟶ ⁅ S ⁆ # mkChoice here s/nat) , node (suc zero)) ∷ [] )
      v∷ ( ((S ⟶ ⁅ A ⁆ # mkChoice here s/nat) , node (suc (suc zero))) ∷ [] )
      v∷ ( ((A ⟶ ⁅ B ⁆ # mkChoice lbl0 s/nat) , node (suc (suc (suc (suc zero)))))
         ∷ ((A ⟶ ⁅ B ⁆ # mkChoice lbl1 s/unit) , node (suc (suc (suc zero))))
         ∷ [] )
      v∷ ( ((A ⟶ ⁅ S ⁆ # mkChoice lbl1 s/unit) , ended) ∷ [] )
      v∷ ( ((B ⟶ ⁅ A ⁆ # mkChoice lbl0 s/nat) , node (suc (suc (suc (suc (suc zero))))))
         ∷ ((B ⟶ ⁅ A ⁆ # mkChoice lbl1 s/unit) , node (suc (suc zero)))
         ∷ [] )
      v∷ ( ((A ⟶ ⁅ S ⁆ # mkChoice lbl0 s/unit) , ended) ∷ [] )
      v∷ v[]
      )

    _ : V (λ i → i) rec2buy ≡ ok
    _ = refl

    _ : V (merge B S) rec2buy ≡ ok
    _ = refl
    _ : V (merge A B) rec2buy ≡ inadmissible
    _ = refl
    _ : V (merge A S) rec2buy ≡ inadmissible
    _ = refl

    _ : HV (merge B S) rec2buy ≡ ok
    _ = refl
    -- the split/no loop `A⟶B`, `B⟶A` becomes an internal τ-cycle; its
    -- exits are `A⟶S` buy / no, so `{A,B}` just picks one of them
    _ : HV (merge A B) rec2buy ≡ ok
    _ = refl
    _ : HV (merge A S) rec2buy ≡ ok
    _ = refl

    _ : OV (merge B S) B rec2buy ≡ ok
    _ = refl
    _ : OV (merge A B) A rec2buy ≡ ok
    _ = refl
    _ : OV (merge A S) A rec2buy ≡ ok
    _ = refl

  -- Examples/NoSynGT.agda: A messages B and C, in either order.  The {B,C}
  -- view is `A→BC . A→BC . end` once the two bisimilar middle states are
  -- identified (`Minimise`); without that it is wrongly `notWB`.
  module NoSynGT where
    nosyn : OpenGraph 0
    nosyn =
      choice
        ((A ⟶ ⁅ B ⁆ # mkChoice here s/unit) ⇒
          ((A ⟶ ⁅ C ⁆ # mkChoice here s/unit) ∙ end))
        ( ((A ⟶ ⁅ C ⁆ # mkChoice here s/unit) ⇒
            ((A ⟶ ⁅ B ⁆ # mkChoice here s/unit) ∙ end))
        ∷ [])

    _ : V (λ i → i) nosyn ≡ ok
    _ = refl

    _ : V (merge B C) nosyn ≡ ok
    _ = refl
    _ : V (merge A B) nosyn ≡ inadmissible
    _ = refl

    _ : HV (merge B C) nosyn ≡ ok
    _ = refl
    _ : HV (merge A B) nosyn ≡ ok
    _ = refl

    _ : OV (merge B C) B nosyn ≡ ok
    _ = refl
    _ : OV (merge A B) A nosyn ≡ ok
    _ = refl

  -- Examples/CounterExamples.agda: A → B (choice), B → C (forward).
  module Forward where
    round : OpenGraph 0
    round = openGraph 3 (node zero)
      ( ( ((A ⟶ ⁅ B ⁆ # mkChoice lbl0 s/bool) , node (suc zero))
        ∷ ((A ⟶ ⁅ B ⁆ # mkChoice lbl1 s/bool) , node (suc (suc zero)))
        ∷ [] )
      v∷ ( ((B ⟶ ⁅ C ⁆ # mkChoice lbl0 s/bool) , ended) ∷ [] )
      v∷ ( ((B ⟶ ⁅ C ⁆ # mkChoice lbl1 s/bool) , ended) ∷ [] )
      v∷ v[]
      )

    _ : V (λ i → i) round ≡ ok
    _ = refl

    _ : V (merge A C) round ≡ ok
    _ = refl
    _ : V (merge A B) round ≡ inadmissible
    _ = refl
    _ : V (merge B C) round ≡ inadmissible
    _ = refl

    _ : HV (merge A C) round ≡ ok
    _ = refl
    _ : HV (merge A B) round ≡ ok
    _ = refl
    _ : HV (merge B C) round ≡ ok
    _ = refl

    _ : OV (merge A C) A round ≡ ok
    _ = refl
    _ : OV (merge A B) A round ≡ ok
    _ = refl
    _ : OV (merge B C) B round ≡ ok
    _ = refl

  -- Tests/Multicast.agda, Once: A ⟶ {B, C}.  Merging the receivers makes
  -- it a plain send; merging the sender with a receiver is mixed.
  module Multicast where
    g : OpenGraph 0
    g = (A ⟶ (⁅ B ⁆ ∪ ⁅ C ⁆) # mkChoice here s/bool) ∙ end

    _ : V (λ i → i) g ≡ ok
    _ = refl

    _ : V (merge B C) g ≡ ok
    _ = refl
    _ : V (merge A B) g ≡ inadmissible
    _ = refl

    _ : HV (merge A B) g ≡ ok
    _ = refl

    _ : OV (merge B C) B g ≡ ok
    _ = refl
    _ : OV (merge A B) A g ≡ ok
    _ = refl

  -- Tests/LabelSorts.agda: A chooses to C, then sends B a nat or a bool.
  module LabelSorts where
    g : OpenGraph 0
    g =
      choice
        ((A ⟶ ⁅ C ⁆ # mkChoice lbl0 s/unit) ⇒
          ((A ⟶ ⁅ B ⁆ # mkChoice here s/nat) ∙ end))
        ( ((A ⟶ ⁅ C ⁆ # mkChoice lbl1 s/unit) ⇒
            ((A ⟶ ⁅ B ⁆ # mkChoice here s/bool) ∙ end))
        ∷ [])

    _ : V (λ i → i) g ≡ ok
    _ = refl

    _ : V (merge B C) g ≡ ok
    _ = refl
    _ : V (merge A B) g ≡ inadmissible
    _ = refl

    _ : HV (merge A B) g ≡ ok
    _ = refl
    _ : HV (merge A C) g ≡ notWB
    _ = refl

    -- ordering cannot help: the problem is a label with two sorts
    _ : OV (merge B C) B g ≡ ok
    _ = refl
    _ : OV (merge A B) A g ≡ ok
    _ = refl
    _ : OV⁺ (merge A C) A g ≡ notWB
    _ = refl

-- ══════════════════════════════════════════════════════════════════════
--  Four roles
-- ══════════════════════════════════════════════════════════════════════

module Four where
  open import Definitions.Graph.Algebra 4 renaming (var to gvar)
  open import Data.Fin.Subset using (⁅_⁆)
  open import Definitions.Actions 4 renaming (_<_> to mkChoice)
  open Quotient 4

  here : Fin 1
  here = zero

  lbl0 lbl1 : Fin 2
  lbl0 = zero
  lbl1 = suc zero

  V : (Fin 4 → Fin 4) → OpenGraph 0 → Verdict
  V ρ g = verdict ρ (underlying (compile g))

  HV : (Fin 4 → Fin 4) → OpenGraph 0 → Verdict
  HV ρ g = Hidden.verdict 4 ρ (underlying (compile g)) (initial (compile g))

  OV OV⁺ OS : (Fin 4 → Fin 4) → Fin 4 → OpenGraph 0 → Verdict
  OV  ρ p g = Ordered.hverdict 4 ρ p false (underlying (compile g)) (initial (compile g))
  OV⁺ ρ p g = Ordered.hverdict 4 ρ p true  (underlying (compile g)) (initial (compile g))
  OS  ρ p g = Ordered.sverdict 4 ρ p false (underlying (compile g)) (initial (compile g))

  -- Examples/RecMW.agda.  The only merge without an internal step is the
  -- worker pool {W1, W2}; it fails because the pool receives `M→W2` and
  -- sends `W1→R` concurrently.  Hiding internal steps rescues the merges
  -- whose process is not on both sides of the `M→W2 ∥ W1→R` diamond:
  -- {M,R} and {W2,R} each receive in both branches from different senders.
  module RecMW where
    M R W1 W2 : Fin 4
    M  = zero
    R  = suc zero
    W1 = suc (suc zero)
    W2 = suc (suc (suc zero))

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

    _ : V (λ i → i) recmw ≡ ok
    _ = refl

    _ : V (merge W1 W2) recmw ≡ notWB
    _ = refl
    _ : V (merge M R) recmw ≡ inadmissible
    _ = refl

    _ : HV (merge W1 W2) recmw ≡ notWB
    _ = refl
    _ : HV (merge M R) recmw ≡ notWB
    _ = refl
    _ : HV (merge M W1) recmw ≡ ok
    _ = refl
    _ : HV (merge M W2) recmw ≡ ok
    _ = refl
    _ : HV (merge W1 R) recmw ≡ ok
    _ = refl
    _ : HV (merge W2 R) recmw ≡ notWB
    _ = refl

    -- Ordered.  `M→W2` (key (M,{W2})) precedes `W1→R` (key (W1,{R})).
    -- Mixed choices: {W1,W2} and {M,R}; {W2,R} receives from two senders,
    -- so only `OV⁺` orders it.
    _ : OS (merge W1 W2) W1 recmw ≡ ok
    _ = refl
    _ : OV (merge W1 W2) W1 recmw ≡ ok
    _ = refl
    _ : OV (merge M R) M recmw ≡ ok
    _ = refl
    _ : OV (merge M W1) M recmw ≡ ok
    _ = refl
    _ : OV (merge M W2) M recmw ≡ ok
    _ = refl
    _ : OV (merge W1 R) W1 recmw ≡ ok
    _ = refl
    _ : OV (merge W2 R) W2 recmw ≡ notWB
    _ = refl
    _ : OV⁺ (merge W2 R) W2 recmw ≡ ok
    _ = refl

  -- PLAN §0: an internal choice, told to `R` by one message.
  --   P ⟶ Q # i . Q ⟶ R # i . end    under {P, Q} / {R}
  -- and the control: after the internal choice, outsiders `R`, `S` do
  -- different things per branch, and nobody tells them which.
  module InternalChoice where
    P Q R S : Fin 4
    P = zero
    Q = suc zero
    R = suc (suc zero)
    S = suc (suc (suc zero))

    told : OpenGraph 0
    told =
      choice
        ((P ⟶ ⁅ Q ⁆ # mkChoice lbl0 s/unit) ⇒
          ((Q ⟶ ⁅ R ⁆ # mkChoice lbl0 s/unit) ∙ end))
        ( ((P ⟶ ⁅ Q ⁆ # mkChoice lbl1 s/unit) ⇒
            ((Q ⟶ ⁅ R ⁆ # mkChoice lbl1 s/unit) ∙ end))
        ∷ [])

    untold : OpenGraph 0
    untold =
      choice
        ((P ⟶ ⁅ Q ⁆ # mkChoice lbl0 s/unit) ⇒
          ((R ⟶ ⁅ S ⁆ # mkChoice here s/unit) ∙ end))
        ( ((P ⟶ ⁅ Q ⁆ # mkChoice lbl1 s/unit) ⇒
            ((S ⟶ ⁅ R ⁆ # mkChoice here s/unit) ∙ end))
        ∷ [])

    -- The original must pass.  `untold` does not (`R⟶S` first appears after
    -- the unrelated `P⟶Q`), so it is not a valid original and its view
    -- verdict below is moot: synchrony of the original already forces
    -- outsiders' steps not to depend on an internal choice they were not told.
    _ : V (λ i → i) told ≡ ok
    _ = refl
    _ : V (λ i → i) untold ≡ notSync
    _ = refl

    _ : HV (merge P Q) told ≡ ok
    _ = refl
    _ : OV (merge P Q) P told ≡ ok
    _ = refl
    _ : HV (merge P Q) untold ≡ notWB
    _ = refl

  -- `P → Q . R → S . end` under {P, S} / {Q, R}.
  module Sequence where
    P Q R S : Fin 4
    P = zero
    Q = suc zero
    R = suc (suc zero)
    S = suc (suc (suc zero))

    -- As written: one order.
    seq : OpenGraph 0
    seq = (P ⟶ ⁅ Q ⁆ # mkChoice here s/unit) ∙
          ((R ⟶ ⁅ S ⁆ # mkChoice here s/unit) ∙ end)

    -- As role-level synchronisation demands: both orders.
    square : OpenGraph 0
    square = openGraph 3 (node zero)
      ( ( ((P ⟶ ⁅ Q ⁆ # mkChoice here s/unit) , node (suc zero))
        ∷ ((R ⟶ ⁅ S ⁆ # mkChoice here s/unit) , node (suc (suc zero)))
        ∷ [] )
      v∷ ( ((R ⟶ ⁅ S ⁆ # mkChoice here s/unit) , ended) ∷ [] )
      v∷ ( ((P ⟶ ⁅ Q ⁆ # mkChoice here s/unit) , ended) ∷ [] )
      v∷ v[]
      )

    -- `seq` is NOT a valid original: it fails `no-new-comm/step`, so it is
    -- never quotiented.  The valid original is the square.
    _ : V (λ i → i) seq ≡ notSync
    _ = refl
    _ : V (λ i → i) square ≡ ok
    _ = refl

    -- Both views of the square are rejected: a mixed choice at state 0,
    -- e.g. for {P,S}:  0 -[PS→Q]-> 1,  0 -[R→PS]-> 2.
    _ : V (merge P S) square ≡ notWB
    _ = refl
    _ : V (merge Q R) square ≡ notWB
    _ = refl

    -- Ordered: both views keep `P→Q` (key (P,{Q})) before `R→S`.
    --   {P,S}: PS→Q . R→PS        {Q,R}: P→QR . QR→S
    _ : OS (merge P S) P square ≡ ok
    _ = refl
    _ : OS (merge Q R) Q square ≡ ok
    _ = refl
