{-# OPTIONS --guardedness #-}

-- Build root for Phase S of decidable.md v2: the saturation theorem
-- `sat : Alg k Γ Δ P Pr s → Alg (F Pr) Γ Δ P Pr s`.
--
-- Like `Complete.agda`, this is kept as a separate root so `runall.sh` type
-- checks it.  The module itself imports only `Definitions.TypeChecker`.

module Saturate where

import Definitions.TypeChecker.Saturate
