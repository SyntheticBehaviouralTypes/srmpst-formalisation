{-# OPTIONS --guardedness #-}

-- `waitFind`: a `WaitV` tree with an empty visited set has a leaf.  A
-- `wv/cycle` carries a run to a step of `P` (`P ∈ G`); `findRun` follows
-- it to a leaf, since every ancestor is `P`-inactive.

open import Data.Nat using (ℕ)

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_)

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Empty using (⊥-elim)
open import Relation.Unary using () renaming (∅ to ∅S)

open import Relation.Nullary using (¬_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)

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
        → (na : ¬ s -⟨ P ⟩->)
        → (k  : ∀ {β u} → s -< β >-> u → WaitV P L (λ v → V v ⊎ (s ~ v)) u)
        → Anc V
        → Anc (λ v → V v ⊎ (s ~ v))

    -- A visited state is `~` to an ancestor node.
    ancLu :
      ∀ {V a}
      → Anc V
      → V a
      → Σ[ s ∈ Behav ] s ~ a × ¬ s -⟨ P ⟩->
          × (∀ {β u} → s -< β >-> u
             → Σ[ V′ ∈ Behavs ] Anc V′ × WaitV P L V′ u)

    ancLu anc/nil ()

    ancLu (anc/cons na k anc) (inj₁ x) =
      ancLu anc x

    ancLu (anc/cons {s = s} na k anc) (inj₂ s~a) =
      s , s~a , na , λ gr → _ , anc/cons na k anc , k gr

    -- Structural on the run, which is kept at a state `~` to the node's:
    -- a cycle jumps back up the tree.
    findRun :
      ∀ {V G G₀ H}
      → Anc V
      → WaitV P L V G
      → G ~ G₀ → G₀ -→* H → H -⟨ P ⟩->
      → ∃[ K ] L K

    findRun anc (wv/leaf x) _ _ _ =
      _ , x

    -- `P` acts here, but this node is `P`-inactive.
    findRun anc (wv/step na _ _) G~ ε act =
      ⊥-elim (¬act/~ G~ na act)

    findRun anc (wv/step na _ k) G~ ((_ , gr) ◅ run) act =
      let _ , gr′ , G′~ = ~R G~ gr
      in findRun (anc/cons na k anc) (k gr′) G′~ run act

    -- At a cycle, go on from the ancestor it is `~` to.
    findRun anc (wv/cycle (_ , a∈ , a~G) _) G~ ε act
      with ancLu anc a∈
    ... | _ , s~a , na , _ =
      ⊥-elim (¬act/~ (~trans (~trans s~a a~G) G~) na act)

    findRun anc (wv/cycle (_ , a∈ , a~G) _) G~ ((_ , gr) ◅ run) act
      with ancLu anc a∈
    ... | _ , s~a , _ , k =
      let _ , grA , A′~ = ~R (~trans (~trans s~a a~G) G~) gr
          _ , anc′ , w′ = k grA
      in findRun anc′ w′ A′~ run act

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

    findLeaf anc w@(wv/cycle _ (_ , run , act)) =
      findRun anc w ~refl run act

  waitFind :
    ∀ {P}{L : Behavs}{G}
    → WaitV P L ∅S G
    → ∃[ K ] L K
  waitFind = findLeaf anc/nil
