{-# OPTIONS --guardedness #-}

-- Checking one process against its block's local view: decide on
-- `viewGraph`, then move the answer to the view with `Transfer`.

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Vec using ([])
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)

open import Definitions.Behav using (Synchronous)
open import Definitions.Typing.Declarative using (module Sessions)
import Definitions.View as View
import Definitions.Transfer as Transfer
import Check.TypeCheck

module Check.View (N : ℕ) where

  open import Definitions.Common N using (PartSet)
  open import Definitions.Graph.Core N
  open import Definitions.Graph.Decision N using (wellBehaved?)
  open import Definitions.Graph.View N using (viewGraph; view⇒; view⇐)
  open Check.TypeCheck N using (module TypeCheck)

  module _ (G : Graph) (sync : Synchronous (graphTheory G)) (Ps : PartSet) where

    open Sessions (graphTheory G) using (⊢ᵛ[_]_∶_)

    private
      VG = viewGraph G Ps
      module V = View (graphTheory G)

      -- The graph to the view, and back.
      module ⇒V =
        Transfer (_-<_>->_ {VG}) (V._-<_>->ᵛ_ Ps) (view⇒ G Ps) (view⇐ G Ps)
      module V⇒ =
        Transfer (V._-<_>->ᵛ_ Ps) (_-<_>->_ {VG}) (view⇐ G Ps) (view⇒ G Ps)

      balG = V⇒.bal⇒ (V.balanced/view Ps (Synchronous.bal sync))

    -- Decides the view, then the process against it.
    typecheckView : ∀ Pr s → Dec (⊢ᵛ[ Ps ] Pr ∶ s)
    typecheckView Pr s with wellBehaved? VG
    ... | no ¬wbG = no λ (w , _) → ¬wbG (V⇒.wb⇒ w)
    ... | yes wbG =
      map′ (λ t → ⇒V.wb⇒ wbG , ⇒V.Typing.typing⇒ wbG (⇒V.wb⇒ wbG) t)
           (λ (w , t) → V⇒.Typing.typing⇒ w wbG t)
           (TypeCheck.tc? VG wbG balG [] [] Ps Pr s)
