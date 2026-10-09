{-# OPTIONS --guardedness #-}

-- `waitFind`: a `WaitV` tree with an empty visited set has a leaf.  A
-- `wv/cycle` carries a `P ∈T` run; `findRun` follows it to a leaf, since
-- every ancestor is `P`-inactive.

open import Data.Nat using (ℕ)

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_)

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Empty using (⊥-elim)
open import Relation.Unary using () renaming (∅ to ∅S)

open import Data.List.Relation.Unary.Any using (Any; here; there)

open import Definitions.Typing.Declarative

module Definitions.Typing.MainLeaf {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  open MPST wb
  open import Definitions.Typing.Alg wb
    using (Behavs; WaitV; wv/leaf; wv/cycle; wv/step)

  module _ {P : PartSet}{L : Behavs} where

    -- The `wv/step` nodes on the path, one per growth of the visited set.
    data Anc : Behavs → Set₁ where

      anc/nil : Anc ∅S

      anc/cons :
        ∀ {V s}
        → (na : P not-active-in s)
        → (k  : ∀ {β u} → s -< β >-> u → WaitV P L (λ v → V v ⊎ (s ~ v)) u)
        → Anc V
        → Anc (λ v → V v ⊎ (s ~ v))

    -- A visited state is `~` to an ancestor node.
    ancLu :
      ∀ {V a}
      → Anc V
      → V a
      → Σ[ s ∈ Behav ] s ~ a × P not-active-in s
          × (∀ {β u} → s -< β >-> u
             → Σ[ V′ ∈ Behavs ] Anc V′ × WaitV P L V′ u)

    ancLu anc/nil ()

    ancLu (anc/cons na k anc) (inj₁ x) =
      ancLu anc x

    ancLu (anc/cons {s = s} na k anc) (inj₂ s~a) =
      s , s~a , na , λ gr → _ , anc/cons na k anc , k gr

    -- Structural on the `Any` witness: a cycle jumps back up the tree.
    findRun :
      ∀ {V G H αs}
      → Anc V
      → WaitV P L V G
      → G -[ αs ]-> H
      → Any (P ∈αˢ_) αs
      → ∃[ K ] L K

    findRun anc (wv/leaf x) _ _ =
      _ , x

    findRun anc (wv/step _ _ _) tr/refl ()

    findRun anc (wv/cycle _ _) tr/refl ()

    -- The run's first action is `P`'s, but this node is `P`-inactive.
    findRun anc (wv/step na _ _) (tr/step {α = α} gr tr) (here px) =
      ⊥-elim (∉αˢ→¬∈αˢ {P} {α} (na gr) px)

    findRun anc (wv/step na _ k) (tr/step gr tr) (there mem) =
      findRun (anc/cons na k anc) (k gr) tr mem

    -- At a cycle, replay the run at the ancestor it is `~` to.
    findRun anc (wv/cycle (_ , a∈ , a~G) _) (tr/step {α = α} gr tr) (here px)
      with ancLu anc a∈
    ... | _ , s~a , na , _ =
      ⊥-elim (∉αˢ→¬∈αˢ {P} {α} (na (~R→ (~trans s~a a~G) gr)) px)

    findRun anc (wv/cycle (_ , a∈ , a~G) _) (tr/step gr tr) (there mem)
      with ancLu anc a∈
    ... | _ , s~a , _ , k =
      let _ , grA , A′~G′ = ~R (~trans s~a a~G) gr
          _ , tr′ , _     = tr-transport (~sym A′~G′) tr
          _ , anc′ , w′   = k grA
      in findRun anc′ w′ tr′ mem

    -- Descend along `wv/step`'s own step; at a cycle, `findRun`.
    findLeaf :
      ∀ {V G}
      → Anc V
      → WaitV P L V G
      → ∃[ K ] L K

    findLeaf anc (wv/leaf x) =
      _ , x

    findLeaf anc (wv/step na gr k) =
      findLeaf (anc/cons na k anc) (k gr)

    findLeaf anc w@(wv/cycle _ (_ , _ , tr , mem)) =
      findRun anc w tr mem

  waitFind :
    ∀ {P}{L : Behavs}{G}
    → WaitV P L ∅S G
    → ∃[ K ] L K
  waitFind = findLeaf anc/nil
