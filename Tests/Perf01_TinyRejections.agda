{-# OPTIONS --guardedness #-}

-- Forced rejections of the unguarded `rec (v 0)` on tiny graphs, which
-- must be cheap.

module Tests.Perf01_TinyRejections where

open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (False)

open import Definitions.Expr using (s/bool)
open import Check
import Definitions.Typing as Typing

-- Pins `nchoices = 0`; a bare `0F` leaves it unsolved.
here : Fin 1
here = 0F

open import Data.Fin.Subset using (⁅_⁆)

-- A single state with no edges at all.
module MinimalGraph where
  open import Definitions.Graph.Algebra 1
  open import Definitions.Proc 1

  A : Fin 1
  A = 0F

  wbg : WBGraph {N = 1}
  wbg = buildG end

  open import Safety (wb-of wbg) (sync-of wbg) using (⊢ᵛ[_]_∶_)

  wtd : Dec (⊢ᵛ[ ⁅ A ⁆ ] rec (v 0F) ∶ initial (proj₁ wbg))
  wtd = typecheck wbg ⁅ A ⁆ (rec (v 0F))

  _ : False wtd
  _ = _

-- `A → B`, end: size 2, no choice.
module Size2Linear where
  open import Definitions.Graph.Algebra 2
  open import Definitions.Actions 2 renaming (_<_> to mkChoice)
  open import Definitions.Proc 2

  A B : Fin 2
  A = 0F
  B = 1F

  wbg : WBGraph {N = 2}
  wbg = buildG ((A ⟶ ⁅ B ⁆ # mkChoice here s/bool) ∙ end)

  open import Safety (wb-of wbg) (sync-of wbg) using (⊢ᵛ[_]_∶_)

  wtd : Dec (⊢ᵛ[ ⁅ A ⁆ ] rec (v 0F) ∶ initial (proj₁ wbg))
  wtd = typecheck wbg ⁅ A ⁆ (rec (v 0F))

  _ : False wtd
  _ = _

-- `A → B → C`, end: size 3, no choice; checking `A` (at the root) and `C`
-- (two hops deep).
module Size3Linear where
  open import Definitions.Graph.Algebra 3
  open import Definitions.Actions 3 renaming (_<_> to mkChoice)
  open import Definitions.Proc 3

  A B C : Fin 3
  A = 0F
  B = 1F
  C = 2F

  wbg : WBGraph {N = 3}
  wbg = buildG ((A ⟶ ⁅ B ⁆ # mkChoice here s/bool) ∙ ((B ⟶ ⁅ C ⁆ # mkChoice here s/bool) ∙ end))

  open import Safety (wb-of wbg) (sync-of wbg) using (⊢ᵛ[_]_∶_)

  wtdA : Dec (⊢ᵛ[ ⁅ A ⁆ ] rec (v 0F) ∶ initial (proj₁ wbg))
  wtdA = typecheck wbg ⁅ A ⁆ (rec (v 0F))

  _ : False wtdA
  _ = _

  wtdC : Dec (⊢ᵛ[ ⁅ C ⁆ ] rec (v 0F) ∶ initial (proj₁ wbg))
  wtdC = typecheck wbg ⁅ C ⁆ (rec (v 0F))

  _ : False wtdC
  _ = _

-- `A → B`, end, with a third participant `C` never mentioned: checking `C`
-- skips exactly one action.
module Size2LinearUninvolved where
  open import Definitions.Graph.Algebra 3
  open import Definitions.Actions 3 renaming (_<_> to mkChoice)
  open import Definitions.Proc 3

  A B C : Fin 3
  A = 0F
  B = 1F
  C = 2F

  wbg : WBGraph {N = 3}
  wbg = buildG ((A ⟶ ⁅ B ⁆ # mkChoice here s/bool) ∙ end)

  open import Safety (wb-of wbg) (sync-of wbg) using (⊢ᵛ[_]_∶_)

  wtd : Dec (⊢ᵛ[ ⁅ C ⁆ ] rec (v 0F) ∶ initial (proj₁ wbg))
  wtd = typecheck wbg ⁅ C ⁆ (rec (v 0F))

  _ : False wtd
  _ = _

-- A 2-way choice at the root, both branches to the shared `ended`.
module Size2Choice where
  open import Definitions.Graph.Algebra 2
  open import Definitions.Actions 2 renaming (_<_> to mkChoice)
  open import Definitions.Proc 2

  A B : Fin 2
  A = 0F
  B = 1F

  lbl0 lbl1 : Fin 2
  lbl0 = 0F
  lbl1 = 1F

  round : OpenGraph 0
  round = openGraph 1 (node 0F)
    ( ( ((A ⟶ ⁅ B ⁆ # mkChoice lbl0 s/bool) , ended)
      ∷ ((A ⟶ ⁅ B ⁆ # mkChoice lbl1 s/bool) , ended)
      ∷ [] )
    v∷ v[] )

  wbg : WBGraph {N = 2}
  wbg = buildG round {p = tt}

  open import Safety (wb-of wbg) (sync-of wbg) using (⊢ᵛ[_]_∶_)

  wtd : Dec (⊢ᵛ[ ⁅ A ⁆ ] rec (v 0F) ∶ initial (proj₁ wbg))
  wtd = typecheck wbg ⁅ A ⁆ (rec (v 0F))

  _ : False wtd
  _ = _

-- `Examples/CounterExamples.agda`'s graph (a 2-way `A → B` choice, one
-- branch continuing `B → C`), checking `A`, who is active at the root.
module Size3Choice where
  open import Definitions.Graph.Algebra 3
  open import Definitions.Actions 3 renaming (_<_> to mkChoice)
  open import Definitions.Proc 3

  A B C : Fin 3
  A = 0F
  B = 1F
  C = 2F

  lbl0 lbl1 : Fin 2
  lbl0 = 0F
  lbl1 = 1F

  round : OpenGraph 0
  round = openGraph 2 (node 0F)
    ( ( ((A ⟶ ⁅ B ⁆ # mkChoice lbl0 s/bool) , ended)
      ∷ ((A ⟶ ⁅ B ⁆ # mkChoice lbl1 s/bool) , node 1F)
      ∷ [] )                                              -- s0
    v∷ ( ((B ⟶ ⁅ C ⁆ # mkChoice here s/bool) , ended) ∷ [] )  -- s1
    v∷ v[]
    )

  wbg : WBGraph {N = 3}
  wbg = buildG round {p = tt}

  open import Safety (wb-of wbg) (sync-of wbg) using (⊢ᵛ[_]_∶_)

  wtd : Dec (⊢ᵛ[ ⁅ A ⁆ ] rec (v 0F) ∶ initial (proj₁ wbg))
  wtd = typecheck wbg ⁅ A ⁆ (rec (v 0F))

  _ : False wtd
  _ = _
