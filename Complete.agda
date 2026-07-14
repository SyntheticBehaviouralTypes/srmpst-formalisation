{-# OPTIONS --guardedness #-}

-- Build root for the completeness development (§5, §3.5, §6 of decidable.md).
-- Kept separate from the `Definitions` aggregator so that the completeness
-- module may import `Safety.Skip` without creating an import cycle.

module Complete where

import Definitions.TypeChecker.Complete
