{-# OPTIONS --guardedness #-}

open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; inject₁; fromℕ; combine; remQuot)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; _++_)
import Data.List as List
open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.Product using (_×_; _,_; map₂)
open import Data.Fin.Relation.Unary.Top using (view; ‵fromℕ; ‵inject₁)
open import Data.Vec using (Vec; []; _∷_; _∷ʳ_; lookup; tabulate)
  renaming (_++_ to _v++_)
import Data.Vec as Vec

module Definitions.Graph.Algebra (N : ℕ) where

  open import Definitions.Actions N using (Action)
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

  infixr 8 _∙_

  _∙_ : ∀ {δ} → Action → OpenGraph δ → OpenGraph δ
  α ∙ continuation = choice (α ⇒ continuation) []

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

  μ : ∀ {δ} → OpenGraph (suc δ) → OpenGraph δ
  μ (openGraph n (loop Fin.zero) table) =
    openGraph
      (suc n)
      (node Fin.zero)
      ([] ∷ mapTable closeLoop table)
  μ (openGraph n (loop (Fin.suc x)) table) =
    openGraph n (loop x) (mapTable (closeRef (loop x)) table)
  μ (openGraph n (node root) table) =
    openGraph n (node root) (mapTable (closeRef (node root)) table)
  μ (openGraph n ended table) =
    openGraph n ended (mapTable (closeRef ended) table)

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
