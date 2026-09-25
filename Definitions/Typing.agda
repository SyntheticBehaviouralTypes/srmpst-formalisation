{-# OPTIONS --guardedness #-}

-- Aggregator for the typing layer.  `Declarative.agda` holds the
-- paper-style judgment (`_&_⊢p_∶_` / `_&_⊢skip_∶_`); the set-indexed one
-- the checker decides is `Typing/Alg.agda`, imported separately.  Importers that
-- only need the declarative rules may import `Definitions.Typing.
-- Declarative` directly — this module exists so that
-- `open import Definitions.Typing` keeps meaning "the typing rules".

module Definitions.Typing where

open import Definitions.Typing.Declarative public
