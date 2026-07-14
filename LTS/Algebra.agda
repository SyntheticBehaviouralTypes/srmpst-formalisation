{-# OPTIONS --guardedness #-}

open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_)
import Data.List as List
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; _++_)
import Data.Vec as Vec

module LTS.Algebra (N : ℕ) where

  open import Definitions.Actions N using (Action)
  open import LTS.Core N using (Graph; State; graph)

  Ref : ℕ → ℕ → Set
  Ref δ n = Fin δ ⊎ Fin n

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
    mapEdge :
      ∀ {A B : Set}
      → (A → B)
      → Action × A
      → Action × B
    mapEdge f (α , target) = α , f target

    mapTable :
      ∀ {A B : Set} {n}
      → (A → B)
      → Vec (List (Action × A)) n
      → Vec (List (Action × B)) n
    mapTable f = Vec.map (List.map (mapEdge f))

    leftRef : ∀ {δ m} n → Ref δ m → Ref δ (m + n)
    leftRef n (inj₁ x) = inj₁ x
    leftRef n (inj₂ s) = inj₂ (s ↑ˡ n)

    rightRef : ∀ {δ n} m → Ref δ n → Ref δ (m + n)
    rightRef m (inj₁ x) = inj₁ x
    rightRef m (inj₂ s) = inj₂ (m ↑ʳ s)

    shiftRef : ∀ {δ n} → Ref δ n → Ref δ (suc n)
    shiftRef (inj₁ x) = inj₁ x
    shiftRef (inj₂ s) = inj₂ (Fin.suc s)

  end : ∀ {δ} → OpenGraph δ
  end = openGraph 1 (inj₂ Fin.zero) ([] ∷ [])

  var : ∀ {δ} → Fin δ → OpenGraph δ
  var x = openGraph 0 (inj₁ x) []

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
          ∷ List.map (mapEdge (rightRef m)) roots)
        (mapTable (leftRef n) table
          ++ mapTable (rightRef m) tables)

  choice :
    ∀ {δ}
    → Alternative δ
    → List (Alternative δ)
    → OpenGraph δ
  choice first rest with collect (first ∷ rest)
  ... | forest n roots table =
    openGraph
      (suc n)
      (inj₂ Fin.zero)
      (List.map (mapEdge shiftRef) roots
        ∷ mapTable shiftRef table)

  infixr 8 _∙_

  _∙_ : ∀ {δ} → Action → OpenGraph δ → OpenGraph δ
  α ∙ continuation = choice (α ⇒ continuation) []

  private
    closeRef : ∀ {δ n} → Ref δ n → Ref (suc δ) n → Ref δ n
    closeRef root (inj₁ Fin.zero) = root
    closeRef root (inj₁ (Fin.suc x)) = inj₁ x
    closeRef root (inj₂ s) = inj₂ s

    closeLoop : ∀ {δ n} → Ref (suc δ) n → Ref δ (suc n)
    closeLoop (inj₁ Fin.zero) = inj₂ Fin.zero
    closeLoop (inj₁ (Fin.suc x)) = inj₁ x
    closeLoop (inj₂ s) = inj₂ (Fin.suc s)

  μ : ∀ {δ} → OpenGraph (suc δ) → OpenGraph δ
  μ (openGraph n (inj₁ Fin.zero) table) =
    openGraph
      (suc n)
      (inj₂ Fin.zero)
      ([] ∷ mapTable closeLoop table)
  μ (openGraph n (inj₁ (Fin.suc x)) table) =
    openGraph n (inj₁ x) (mapTable (closeRef (inj₁ x)) table)
  μ (openGraph n (inj₂ root) table) =
    openGraph
      n
      (inj₂ root)
      (mapTable (closeRef (inj₂ root)) table)

  private
    closedRef : ∀ {n} → Ref 0 n → Fin n
    closedRef (inj₁ ())
    closedRef (inj₂ s) = s

  compile : OpenGraph 0 → RootedGraph
  compile (openGraph n root table) =
    rooted
      (graph n (mapTable closedRef table))
      (closedRef root)
