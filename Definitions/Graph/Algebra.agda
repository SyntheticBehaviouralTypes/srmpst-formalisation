{-# OPTIONS --guardedness #-}

open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; inject₁; fromℕ; combine; remQuot)
import Data.Fin as Fin
open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.Bool.ListAction using (any; all)
open import Data.List using (List; []; _∷_; _++_)
import Data.List as List
open import Data.List.NonEmpty using (_∷_)
open import Data.Maybe using (Maybe; just; nothing; is-just)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤?_)
open import Data.Product using (_×_; _,_; map₂; proj₁; proj₂)
open import Function using (_∘_)
open import Data.Fin.Relation.Unary.Top using (view; ‵fromℕ; ‵inject₁)
open import Data.Vec using (Vec; []; _∷_; _∷ʳ_; lookup; tabulate)
  renaming (_++_ to _v++_)
import Data.Vec as Vec
open import Relation.Nullary.Decidable using (True)

open import Utils.Branch using (Branch; branch; Branches; _↦_; Closes)
open import Utils.Binder using (bound)

module Definitions.Graph.Algebra (N : ℕ) where

  open import Definitions.Actions N using (Action; Event)
  open import Definitions.Graph.Action N using (eqVec; eqMaybeEvent; eqFin)
  open import Definitions.Graph.Core N using (Graph; State; graph)

  -- A recursion variable (`loop`), a node (`node`), or the one shared
  -- ended state (`ended`), so that no graph has a second stuck state.
  data Ref (δ n : ℕ) : Set where
    loop : Fin δ → Ref δ n
    node : Fin n → Ref δ n
    ended : Ref δ n

  record OpenGraph (δ : ℕ) : Set where
    constructor openGraph
    field
      nodes : ℕ
      root  : Ref δ nodes
      table : Vec (List (Action × Ref δ nodes)) nodes

  open OpenGraph public

  record RootedGraph : Set where
    constructor rooted
    field
      underlying : Graph
      initial    : State underlying

  open RootedGraph public

  private
    mapTable :
      ∀ {A B : Set} {n}
      → (A → B)
      → Vec (List (Action × A)) n
      → Vec (List (Action × B)) n
    mapTable f = Vec.map (List.map (map₂ f))

    leftRef : ∀ {δ m} n → Ref δ m → Ref δ (m + n)
    leftRef n (loop x) = loop x
    leftRef n (node s) = node (s ↑ˡ n)
    leftRef n ended     = ended

    rightRef : ∀ {δ n} m → Ref δ n → Ref δ (m + n)
    rightRef m (loop x) = loop x
    rightRef m (node s) = node (m ↑ʳ s)
    rightRef m ended     = ended

    shiftRef : ∀ {δ n} → Ref δ n → Ref δ (suc n)
    shiftRef (loop x) = loop x
    shiftRef (node s) = node (Fin.suc s)
    shiftRef ended     = ended

  -- the ended graph: no nodes at all, just the shared reference
  end : ∀ {δ} → OpenGraph δ
  end = openGraph 0 ended []

  var : ∀ {δ} → Fin δ → OpenGraph δ
  var x = openGraph 0 (loop x) []

  record Alternative (δ : ℕ) : Set where
    constructor _⇒_
    field
      action       : Action
      continuation : OpenGraph δ

  open Alternative public

  private
    record Forest (δ : ℕ) : Set where
      constructor forest
      field
        nodes/forest : ℕ
        roots/forest : List (Action × Ref δ nodes/forest)
        table/forest :
          Vec (List (Action × Ref δ nodes/forest)) nodes/forest

    collect : ∀ {δ} → List (Alternative δ) → Forest δ
    collect [] = forest 0 [] []
    collect ((α ⇒ continuation) ∷ alternatives)
      with continuation | collect alternatives
    ... | openGraph m root table
        | forest n roots tables =
      forest
        (m + n)
        ((α , leftRef n root)
          ∷ List.map (map₂ (rightRef m)) roots)
        (mapTable (leftRef n) table
          v++ mapTable (rightRef m) tables)

  choice :
    ∀ {δ}
    → Alternative δ
    → List (Alternative δ)
    → OpenGraph δ
  choice first rest with collect (first ∷ rest)
  ... | forest n roots table =
    openGraph
      (suc n)
      (node Fin.zero)
      (List.map (map₂ shiftRef) roots
        ∷ mapTable shiftRef table)

  -- ── MPST sequencing ──
  --
  -- `mpst` is `choice`, plus the steps that may fire *under* the pending
  -- choice (`step/tl/I` of the former global types): a step `β` sharing
  -- no role with any branch's action, taken by every branch at once.  The
  -- pending states are the tuples of branch residuals so reached; they
  -- come first, so with no such step `mpst` builds exactly `choice`.
  -- Steps out of a loop variable are not taken: the body is still open.
  private
    disjoint : ∀ {n} → Vec (Maybe Event) n → Vec (Maybe Event) n → Bool
    disjoint []       []       = true
    disjoint (a ∷ as) (b ∷ bs) = not (is-just a ∧ is-just b) ∧ disjoint as bs

    eqAction : Action → Action → Bool
    eqAction = eqVec eqMaybeEvent

    eqRef : ∀ {δ n} → Ref δ n → Ref δ n → Bool
    eqRef (loop x) (loop y) = eqFin x y
    eqRef (node s) (node t) = eqFin s t
    eqRef ended    ended    = true
    eqRef _        _        = false

    eqRefs : ∀ {δ n} → List (Ref δ n) → List (Ref δ n) → Bool
    eqRefs []       []       = true
    eqRefs (r ∷ rs) (s ∷ ss) = eqRef r s ∧ eqRefs rs ss
    eqRefs _        _        = false

    elem : ∀ {A : Set} → (A → A → Bool) → A → List A → Bool
    elem eq x = any (eq x)

    -- first occurrences, in order
    nub : ∀ {A : Set} → (A → A → Bool) → List A → List A
    nub {A} eq = go []
      where
        go : List A → List A → List A
        go kept []       = kept
        go kept (x ∷ xs) =
          if elem eq x kept then go kept xs else go (kept ++ x ∷ []) xs

    -- every way of picking one element from each list
    picks : ∀ {A : Set} → List (List A) → List (List A)
    picks []         = [] ∷ []
    picks (xs ∷ xss) =
      List.concatMap (λ x → List.map (x ∷_) (picks xss)) xs

    indexOf :
      ∀ {A : Set} → (A → A → Bool) → A → (xs : List A)
      → Maybe (Fin (List.length xs))
    indexOf eq y []       = nothing
    indexOf eq y (x ∷ xs) =
      if eq y x then just Fin.zero else Maybe.map Fin.suc (indexOf eq y xs)

    module Pending
      {δ m} (table : Vec (List (Action × Ref δ m)) m) (αs : List Action)
      where

      Tuple : Set
      Tuple = List (Ref δ m)

      out : Ref δ m → List (Action × Ref δ m)
      out (node s) = lookup table s
      out _        = []

      after : Action → Ref δ m → List (Ref δ m)
      after β r =
        List.map proj₂ (List.filterᵇ (eqAction β ∘ proj₁) (out r))

      -- the steps under the pending choice, out of the residuals `rs`
      under : Tuple → List (Action × Tuple)
      under []         = []
      under rs@(r ∷ _) =
        List.concatMap
          (λ β → List.map (β ,_) (picks (List.map (after β) rs)))
          (List.filterᵇ (λ β → all (disjoint β) αs)
            (nub eqAction (List.map proj₁ (out r))))

      -- breadth first; each pass retires one tuple, of at most
      -- `(suc δ + m) ^ length αs`
      explore : ℕ → List Tuple → List Tuple → List Tuple
      explore zero    seen _          = seen
      explore (suc k) seen []         = seen
      explore (suc k) seen (rs ∷ todo) = explore k (seen ++ new) (todo ++ new)
        where
          new = nub eqRefs
            (List.filterᵇ (λ ss → not (elem eqRefs ss seen))
              (List.map proj₂ (under rs)))

      reach : Tuple → List Tuple
      reach rs =
        explore (suc ((suc δ + m) ^ List.length αs)) (rs ∷ []) (rs ∷ [])

      -- the graph, given the pending tuples `seen` (an argument, so that
      -- normalisation computes them once)
      pending : List (Action × Ref δ m) → List Tuple → OpenGraph δ
      pending roots seen =
        openGraph (t + m) (here (List.map proj₂ roots))
          (Vec.map row (Vec.fromList seen) v++ mapTable (rightRef t) table)
        where
          t = List.length seen

          here : Tuple → Ref δ (t + m)
          here rs = Maybe.maybe (λ i → node (i ↑ˡ m)) ended
                      (indexOf eqRefs rs seen)

          row : Tuple → List (Action × Ref δ (t + m))
          row rs =
            List.zipWith (λ α r → α , rightRef t r) αs rs
              ++ List.map (map₂ here) (under rs)

  mpst : ∀ {δ} → Alternative δ → List (Alternative δ) → OpenGraph δ
  mpst first rest with collect (first ∷ rest)
  ... | forest m roots table
    with Pending.under table (List.map proj₁ roots) (List.map proj₂ roots)
  ...   | []    = choice first rest
  ...   | _ ∷ _ =
    Pending.pending table (List.map proj₁ roots) roots
      (Pending.reach table (List.map proj₁ roots) (List.map proj₂ roots))

  -- ── sequencing and branching ──
  --
  -- `α >> G`: `α`, then `G`.  `α ∙ G`: `α` before `G`'s steps that share
  -- a role with it; `G`'s other steps may come first.  Inside
  --
  --   ⟪ α₁ ∙ G₁
  --   ∣ α₂ ∙ G₂
  --   ⟫
  --
  -- (`Utils.Branch`) `αᵢ ∙ Gᵢ` is a branch, and the whole is `mpst` over
  -- the branches, in order.  Below `_⟶_#_` (4.5), so actions need no
  -- parentheses.
  infixr 4 _>>_ _∙_

  _>>_ : ∀ {δ} → Action → OpenGraph δ → OpenGraph δ
  α >> continuation = choice (α ⇒ continuation) []

  -- What `α ∙ G` builds: a graph, or one branch of a `⟪ ⟫`.
  record Prefix (δ : ℕ) (R : Set) : Set where
    field prefix : Action → OpenGraph δ → R

  open Prefix {{...}}

  _∙_ : ∀ {δ R} {{_ : Prefix δ R}} → Action → OpenGraph δ → R
  _∙_ = prefix

  instance
    prefix/graph : ∀ {δ} → Prefix δ (OpenGraph δ)
    prefix/graph = record { prefix = λ α continuation →
      mpst (α ⇒ continuation) [] }

    prefix/branch : ∀ {δ} → Prefix δ (Branches Action (OpenGraph δ))
    prefix/branch = record { prefix = _↦_ }

  instance
    closes/choice : ∀ {δ} → Closes Action (OpenGraph δ) (OpenGraph δ)
    closes/choice = record { close = λ where
      (b ∷ bs) → mpst (alt b) (List.map alt bs) }
      where
        alt : ∀ {δ} → Branch Action (OpenGraph δ) → Alternative δ
        alt (branch α continuation) = α ⇒ continuation

  private
    closeRef : ∀ {δ n} → Ref δ n → Ref (suc δ) n → Ref δ n
    closeRef root (loop Fin.zero) = root
    closeRef root (loop (Fin.suc x)) = loop x
    closeRef root (node s) = node s
    closeRef root ended = ended

    closeLoop : ∀ {δ n} → Ref (suc δ) n → Ref δ (suc n)
    closeLoop (loop Fin.zero) = node Fin.zero
    closeLoop (loop (Fin.suc x)) = loop x
    closeLoop (node s) = node (Fin.suc s)
    closeLoop ended = ended

  -- `μᵈ` binds `var 0F`; `μ λ X → G` binds `X` (`Utils.Binder`).
  μᵈ : ∀ {δ} → OpenGraph (suc δ) → OpenGraph δ
  μᵈ (openGraph n (loop Fin.zero) table) =
    openGraph
      (suc n)
      (node Fin.zero)
      ([] ∷ mapTable closeLoop table)
  μᵈ (openGraph n (loop (Fin.suc x)) table) =
    openGraph n (loop x) (mapTable (closeRef (loop x)) table)
  μᵈ (openGraph n (node root) table) =
    openGraph n (node root) (mapTable (closeRef (node root)) table)
  μᵈ (openGraph n ended table) =
    openGraph n ended (mapTable (closeRef ended) table)

  Loop : ℕ → Set
  Loop δ = ∀ {m} {p : True (suc δ ≤? m)} → OpenGraph m

  μ : ∀ {δ} → (Loop δ → OpenGraph (suc δ)) → OpenGraph δ
  μ {δ} body = μᵈ (body (λ {m} {p} → var (bound δ p)))

  -- ── compilation ──
  --
  -- The ended state is always emitted, as the last index.
  private
    closedRef : ∀ {n} → Ref 0 n → Fin (suc n)
    closedRef (loop ())
    closedRef (node s) = inject₁ s
    closedRef ended     = fromℕ _

  compile : OpenGraph 0 → RootedGraph
  compile (openGraph n root table) =
    rooted
      (graph (suc n) (mapTable closedRef table ∷ʳ []))
      (closedRef root)

  -- ── sequential composition ──
  --
  -- Every `ended` of the first graph becomes the root of the second.
  infixr 6 _⨾_

  _⨾_ : ∀ {δ} → OpenGraph δ → OpenGraph δ → OpenGraph δ
  openGraph m r₁ t₁ ⨾ openGraph n r₂ t₂ =
    openGraph (m + n)
      (seqRef r₁)
      (mapTable seqRef t₁ v++ mapTable (rightRef m) t₂)
    where
      seqRef : Ref _ m → Ref _ (m + n)
      seqRef (loop x) = loop x
      seqRef (node s) = node (s ↑ˡ n)
      seqRef ended    = rightRef m r₂

  -- ── parallel composition (interleaving product) ──
  --
  -- States are pairs of component states; (ended , ended) is `ended`.
  -- Components must be closed.
  infixr 7 _∥_

  _∥_ : ∀ {δ} → OpenGraph 0 → OpenGraph 0 → OpenGraph δ
  _∥_ {δ} (openGraph m₁ r₁ t₁) (openGraph m₂ r₂ t₂) =
    openGraph P (pair (closedRef r₁) (closedRef r₂)) (tabulate build)
    where
      -- suc P ≡ suc m₁ * suc m₂ definitionally: the last pair index is
      -- (ended , ended) and everything below it is a product node
      P : ℕ
      P = m₂ + m₁ * suc m₂

      pair : Fin (suc m₁) → Fin (suc m₂) → Ref δ P
      pair a b with combine a b | view (combine a b)
      ... | _ | ‵inject₁ c = node c
      ... | _ | ‵fromℕ     = ended

      leftMoves : Fin (suc m₁) → Fin (suc m₂) → List (Action × Ref δ P)
      leftMoves a b with view a
      ... | ‵inject₁ s =
        List.map (map₂ (λ r → pair (closedRef r) b)) (lookup t₁ s)
      ... | ‵fromℕ = []

      rightMoves : Fin (suc m₁) → Fin (suc m₂) → List (Action × Ref δ P)
      rightMoves a b with view b
      ... | ‵inject₁ s =
        List.map (map₂ (λ r → pair a (closedRef r))) (lookup t₂ s)
      ... | ‵fromℕ = []

      build : Fin P → List (Action × Ref δ P)
      build p with remQuot {suc m₁} (suc m₂) (inject₁ p)
      ... | a , b = leftMoves a b ++ rightMoves a b
