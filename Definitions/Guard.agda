module Definitions.Guard where

data Guard : Set where
  -- respectively message (i.e: action) guarded, and not guarded
  mg ng : Guard

-- mg only if both are guarded (and gate if mg is true)
_|&|_ : Guard -> Guard -> Guard
mg |&| mg = mg
g |&| g' = ng
