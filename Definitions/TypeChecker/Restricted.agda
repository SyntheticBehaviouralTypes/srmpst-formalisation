{-# OPTIONS --guardedness #-}

-- The shape-restricted typing judgment and its decision procedure.
--
-- `R Γ Δ P Pr s` (notation `Γ & Δ ⊢r P ◂ Pr ∶ s`) mirrors the declarative
-- `_&_⊢p_∶_` (Definitions/Typing.agda) with restrictions that make it
-- directly decidable — no fuel, no saturation:
--
--   * `t/unskip` is confined to just before `rec` and `v`: the `rec`/`v`
--     clauses of the syntax-directed layer `D` carry an anchor
--     `Σ[ H ] (H -[¬ P ]->* s) × …` decided by a plain backward graph
--     search.  Everywhere else the rules are syntax-directed.  This is the
--     normal form `Safety/Head.agda`'s `td/head` establishes for the full
--     judgment, so nothing is lost.
--   * the `t/skip` alternative is the *semantic* characterization
--     `SemSkipP (D …) P s` (`Definitions/TypeChecker/Core.agda`, §3): every
--     state reachable from `s` while avoiding the directly-typable leaf set
--     is `P`-inactive and can itself reach a leaf.  This is exactly what a
--     `⊢skip[ prod ]` tree means: `SkipSem.theoremB` (Core) rebuilds a
--     genuine tree from it (used for soundness below), and `theoremA`
--     (Complete) recovers it from any tree (used for completeness).  A
--     syntactic "fresh-stepping tree" rule is NOT equivalent: prod trees may
--     have to revisit their spine (e.g. a same-comm branching `u ⇉ {t, ℓ}`
--     with a reply edge `t → u`, where the only prod tree runs
--     `u → t → u → ℓ` — and such graphs are well-behaved), so freshness
--     would lose completeness, while unrestricted trees cannot be searched
--     directly.  The semantic form is decidable through the `reachVia?`
--     fixed point (`SkipDecide.semSkip?`, Core) — with the cheap leaf
--     decider `D?` below, polynomially in the graph.
--
-- The restriction is *global*: the `rec` clause's body is typed in the
-- restricted judgment again (not in `⊢p`), so the checker never leaves this
-- judgment.  `D`/`R` are recursive *functions* on the process (not
-- datatypes): the skip alternative mentions `¬ (D …)` through `SemSkipP`'s
-- path filter, which strict positivity would forbid for a datatype — and
-- the recursion is structural on the process, which is also the whole
-- termination story for the decider `R?`/`D?`.
--
-- `sound` translates restricted derivations into the declarative judgment;
-- the converse (completeness) lives in `Definitions/TypeChecker/Complete.agda`
-- and makes the public `typecheck` a genuine `Dec` of the declarative
-- judgment.

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
  renaming (_≟_ to _≟Fin_)
import Data.Fin as F
import Data.Fin.Properties as FinP
open import Data.List using (List; []; _∷_; filter)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as MemP
import Data.List.Relation.Unary.All as All
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
  using (_×_; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; lookup)
  renaming (map to vmap)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable
  using (map′; _×-dec_; _⊎-dec_; ¬?)

open import Definitions.Behav using (BTheory; WellBehaved)
open import Definitions.Expr
open import Definitions.TypeChecker.Core
import Definitions.Typing as Typing

module Definitions.TypeChecker.Restricted (N : ℕ) where

  open Processes N using (module GraphChecker)
  open import LTS.Core N
    renaming (_-<_>->_ to GStep)
  open import LTS.Reachability N
    using (PathVia; path/nil; path/cons; reachVia?; ∈T?)

  module GraphRestricted
    (G : Graph)
    (wb : WellBehaved (graphTheory G))
    where

    open Typing.MPST wb
    open GraphChecker G wb
      using ( messageGuarded?; matchRecv?; MatchRecv
            ; findStep; findRecv; RecvWitness
            ; na?; bisim?~
            ; SemSkipP; semSkipP-mono
            ; module SkipDecide; module SkipSem )

    private
      variable
        γ δ ξ : ℕ

    -- ════════════════════════════════════════════════════════════════
    --  Backward ¬P-reachability, via the `reachVia?` fixed point on the
    --  P-free restriction of the graph (anchors for `rec` and `v`)
    -- ════════════════════════════════════════════════════════════════

    restrict : Part → Graph
    restrict P =
      graph (size G) (vmap (filter (λ e → P ∉α? proj₁ e)) (outgoing G))

    redges≡ :
      ∀ P s
      → edges (restrict P) s ≡ filter (λ e → P ∉α? proj₁ e) (edges G s)
    redges≡ P s = VecP.lookup-map s _ (outgoing G)

    rstep⇒ :
      ∀ {P s α t}
      → GStep {restrict P} s α t
      → (s -< α >-> t) × P ∉α α
    rstep⇒ {P} {s} {α} {t} gr
      with MemP.∈-filter⁻ (λ e → P ∉α? proj₁ e)
             (subst ((α , t) ∈_) (redges≡ P s)
               (step⇒listed {restrict P} gr))
    ... | mem , P∉α = listed⇒step {G = G} mem , P∉α

    rstep⇐ :
      ∀ {P s α t}
      → s -< α >-> t
      → P ∉α α
      → GStep {restrict P} s α t
    rstep⇐ {P} {s} {α} {t} gr P∉α =
      listed⇒step {G = restrict P}
        (subst ((α , t) ∈_) (sym (redges≡ P s))
          (MemP.∈-filter⁺ (λ e → P ∉α? proj₁ e)
            (step⇒listed {G = G} gr) P∉α))

    path→tr :
      ∀ {P a b n}
      → PathVia (restrict P) (λ _ → true) a b n
      → a -[¬ P ]->* b
    path→tr path/nil = skip/refl
    path→tr (path/cons _ gr rest) =
      let gr′ , P∉α = rstep⇒ gr
      in skip/step gr′ P∉α (path→tr rest)

    tr→path :
      ∀ {P a b}
      → a -[¬ P ]->* b
      → ∃[ n ] PathVia (restrict P) (λ _ → true) a b n
    tr→path skip/refl = zero , path/nil
    tr→path (skip/step gr P∉α tr) =
      let n , rest = tr→path tr
      in suc n , path/cons _ (rstep⇐ gr P∉α) rest

    reach¬P? : ∀ P a b → Dec (a -[¬ P ]->* b)
    reach¬P? P a b =
      map′ (λ { (_ , p) → path→tr p }) tr→path
        (reachVia? (restrict P) (λ _ → true) a b)

    varAnchor? :
      ∀ (Δ : Vec (State G) δ) (X : Fin δ) (P : Part) (s : State G)
      → Dec (Σ[ H ∈ State G ] (H -[¬ P ]->* s) × (lookup Δ X ~ H))
    varAnchor? Δ X P s =
      FinP.any? (λ H → reach¬P? P H s ×-dec bisim?~ (lookup Δ X) H)

    -- ════════════════════════════════════════════════════════════════
    --  The shape-restricted judgment (recursive functions on the process)
    -- ════════════════════════════════════════════════════════════════

    mutual

      -- the syntax-directed layer: one clause per process constructor
      D : ∀ {γ δ} → Vec Sort γ → Vec (State G) δ
        → Part → Proc γ δ → State G → Set
      D Γ Δ P (Q ! i < E >∙ Pr) s =
        Σ[ S ∈ Sort ] Σ[ t ∈ State G ]
          (Γ ⊢e E ∶ S)
          × (s -< P ⟶ Q # i < S > >-> t)
          × R Γ Δ P Pr t
      D Γ Δ Q (Σ_？[_]·_ P {I = I} S Br) s =
        RecvWitness P Q I (edges G s)
        × All.All (RecvAtR Γ Δ P Q Br) (edges G s)
      D Γ Δ P (ifp E then Pr else Pr′) s =
        (Γ ⊢e E ∶ s/bool) × R Γ Δ P Pr s × R Γ Δ P Pr′ s
      -- the only places `t/unskip` is allowed: parked just before `rec` …
      D Γ Δ P (rec Pr) s =
        Σ[ H ∈ State G ]
          (H -[¬ P ]->* s)
          × MessageGuarded Pr
          × R Γ (H ∷ Δ) P Pr H
      -- … and just before recursion variables
      D Γ Δ P (v X) s =
        Σ[ H ∈ State G ] (H -[¬ P ]->* s) × (lookup Δ X ~ H)
      D Γ Δ P ∅ s = ¬ P ∈T s

      -- vector companion so branch processes stay structural
      RBr : ∀ {γ δ I} → Vec Sort γ → Vec (State G) δ
          → Part → Vec (Proc γ δ) I → Fin I → State G → Set
      RBr Γ Δ Q (Pr ∷ Br) F.zero    t = R Γ Δ Q Pr t
      RBr Γ Δ Q (Pr ∷ Br) (F.suc j) t = RBr Γ Δ Q Br j t

      -- receive continuation obligation at a single graph edge
      RecvAtR : ∀ {γ δ I} → Vec Sort γ → Vec (State G) δ
              → (P Q : Part) → Vec (Proc (suc γ) δ) (suc I)
              → Edge (size G) → Set
      RecvAtR Γ Δ P Q Br (α , t) =
        ∀ {j U} → α ≡ (P ⟶ Q # j < U >)
        → RBr (U ∷ Γ) Δ Q Br j t

      -- the judgment: directly typable, or a semantic skip round
      R : ∀ {γ δ} → Vec Sort γ → Vec (State G) δ
        → Part → Proc γ δ → State G → Set
      R Γ Δ P Pr s =
        D Γ Δ P Pr s ⊎ SemSkipP (D Γ Δ P Pr) P s

    -- user-facing notation
    infix 4 _&_⊢d_∶_ _&_⊢r_∶_

    _&_⊢d_∶_ :
      Vec Sort γ → Vec (State G) δ → NProc γ δ → State G → Set
    Γ & Δ ⊢d (P ◂ Pr) ∶ s = D Γ Δ P Pr s

    _&_⊢r_∶_ :
      Vec Sort γ → Vec (State G) δ → NProc γ δ → State G → Set
    Γ & Δ ⊢r (P ◂ Pr) ∶ s = R Γ Δ P Pr s

    -- ════════════════════════════════════════════════════════════════
    --  The decision procedure (structural on the process)
    -- ════════════════════════════════════════════════════════════════

    mutual

      RBr? :
        ∀ {γ δ I} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (Q : Part)
          (Br : Vec (Proc γ δ) I) (j : Fin I) (t : State G)
        → Dec (RBr Γ Δ Q Br j t)
      RBr? Γ Δ Q (Pr ∷ Br) F.zero    t = R? Γ Δ Q Pr t
      RBr? Γ Δ Q (Pr ∷ Br) (F.suc j) t = RBr? Γ Δ Q Br j t

      recvAtR? :
        ∀ {γ δ I} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
          (P Q : Part) (Br : Vec (Proc (suc γ) δ) (suc I))
          (e : Edge (size G))
        → Dec (RecvAtR Γ Δ P Q Br e)
      recvAtR? {I = I} Γ Δ P Q Br (α , t) with matchRecv? P Q I α
      ... | no noMatch =
        yes λ { {j} {U} eq → ⊥-elim (noMatch (j , U , eq)) }
      ... | yes (j , U , refl) with RBr? (U ∷ Γ) Δ Q Br j t
      ...   | yes a = yes λ { refl → a }
      ...   | no ¬a = no λ f → ¬a (f refl)

      D? :
        ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
          (P : Part) (Pr : Proc γ δ) (s : State G)
        → Dec (D Γ Δ P Pr s)
      D? Γ Δ P (Q ! i < E >∙ Pr) s
        with inferExpression Γ E
      ... | no ¬E = no λ { (S , _ , etd , _ , _) → ¬E (S , etd) }
      ... | yes (S , etd) with findStep s (P ⟶ Q # i < S >)
      ...   | no ¬st =
        no λ { (_ , t , etd′ , gr , _) →
          ¬st (t , subst (λ σ → s -< P ⟶ Q # i < σ > >-> t)
                     (⊢e-unique etd′ etd) gr) }
      ...   | yes (t , gr) with R? Γ Δ P Pr t
      ...     | yes a = yes (S , t , etd , gr , a)
      ...     | no ¬a =
        no λ { (_ , t′ , etd′ , gr′ , a′) →
          ¬a (subst (λ u → R Γ Δ P Pr u)
                (step-deterministic
                  (subst (λ σ → s -< P ⟶ Q # i < σ > >-> t′)
                    (⊢e-unique etd′ etd) gr′)
                  gr)
                a′) }
      D? Γ Δ Q (Σ_？[_]·_ P {I = I} S Br) s
        with findRecv P Q I (edges G s)
           | All.all? (recvAtR? Γ Δ P Q Br) (edges G s)
      ... | no ¬rw | _ = no λ { (rw , _) → ¬rw rw }
      ... | yes _ | no ¬all = no λ { (_ , all) → ¬all all }
      ... | yes rw | yes all = yes (rw , all)
      D? Γ Δ P (ifp E then Pr else Pr′) s
        with inferExpression Γ E
           | R? Γ Δ P Pr s
           | R? Γ Δ P Pr′ s
      ... | yes (s/bool , etd) | yes a | yes a′ = yes (etd , a , a′)
      ... | yes (s/bool , _) | no ¬a | _ = no λ { (_ , a , _) → ¬a a }
      ... | yes (s/bool , _) | yes _ | no ¬a′ = no λ { (_ , _ , a′) → ¬a′ a′ }
      ... | yes (s/nat , etd) | _ | _ =
        no λ { (etd′ , _ , _) → s/nat≢s/bool (⊢e-unique etd etd′) }
      ... | yes (s/unit , etd) | _ | _ =
        no λ { (etd′ , _ , _) → s/unit≢s/bool (⊢e-unique etd etd′) }
      ... | no ¬E | _ | _ =
        no λ { (etd′ , _ , _) → ¬E (s/bool , etd′) }
      D? Γ Δ P (rec Pr) s
        with messageGuarded? Pr
      ... | no ¬mg = no λ { (_ , _ , mg , _) → ¬mg mg }
      ... | yes mg
        with FinP.any? (λ H → reach¬P? P H s ×-dec R? Γ (H ∷ Δ) P Pr H)
      ...   | yes (H , tr , td) = yes (H , tr , mg , td)
      ...   | no ¬a = no λ { (H , tr , _ , td) → ¬a (H , tr , td) }
      D? Γ Δ P (v X) s = varAnchor? Δ X P s
      D? Γ Δ P ∅ s = ¬? (∈T? G P s)

      R? :
        ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
          (P : Part) (Pr : Proc γ δ) (s : State G)
        → Dec (R Γ Δ P Pr s)
      R? Γ Δ P Pr s =
        D? Γ Δ P Pr s
          ⊎-dec
        SkipDecide.semSkip? (D Γ Δ P Pr) (D? Γ Δ P Pr) P s

    -- ════════════════════════════════════════════════════════════════
    --  Soundness: restricted ⇒ declarative
    --
    --  Organized as one function structural on the process, returning the
    --  pair of translations, so that the skip case can hand the *local*
    --  direct-translation to `SkipSem.theoremB` as its leaf function
    --  without creating a mutual-recursion knot through the module
    --  parameter (which the termination checker cannot see through).
    -- ════════════════════════════════════════════════════════════════

    record SoundAt {γ δ} (Pr : Proc γ δ) : Set where
      field
        dS : ∀ {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P s}
           → D Γ Δ P Pr s → Γ & Δ ⊢p P ◂ Pr ∶ s
        rS : ∀ {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P s}
           → R Γ Δ P Pr s → Γ & Δ ⊢p P ◂ Pr ∶ s

    -- a semantic skip round is a real `t/skip`: rebuild the tree with the
    -- existing constructor theorem (`SkipSem.theoremB`, Core §3.4)
    mkR :
      ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P} (Pr : Proc γ δ)
      → (dS : ∀ {s} → D Γ Δ P Pr s → Γ & Δ ⊢p P ◂ Pr ∶ s)
      → ∀ {s} → R Γ Δ P Pr s → Γ & Δ ⊢p P ◂ Pr ∶ s
    mkR Pr dS (inj₁ d)   = dS d
    mkR {Γ = Γ} {Δ} {P} Pr dS (inj₂ sem) =
      t/skip
        (SkipSem.theoremB Γ Δ P Pr
          (D Γ Δ P Pr) (D? Γ Δ P Pr) (λ t Dt → dS Dt)
          _ sem)

    soundAt : ∀ {γ δ} (Pr : Proc γ δ) → SoundAt Pr
    soundAt {γ} {δ} (Q ! i < E >∙ Pr) = record { dS = dS′ ; rS = mkR _ dS′ }
      where
        dS′ : ∀ {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P s}
            → D Γ Δ P (Q ! i < E >∙ Pr) s
            → Γ & Δ ⊢p P ◂ Q ! i < E >∙ Pr ∶ s
        dS′ (S , t , etd , gr , a) =
          t/send gr etd (SoundAt.rS (soundAt Pr) a)
    soundAt {γ} {δ} (Σ_？[_]·_ P {I = I} S Br) =
      record { dS = dS′ ; rS = mkR _ dS′ }
      where
        brS : ∀ {I′} (Br′ : Vec (Proc (suc γ) δ) I′) (j : Fin I′)
                {Γ : Vec Sort (suc γ)} {Δ : Vec (State G) δ} {Q t}
            → RBr Γ Δ Q Br′ j t → Γ & Δ ⊢p Q ◂ lookup Br′ j ∶ t
        brS (Pr ∷ Br′) F.zero    a = SoundAt.rS (soundAt Pr) a
        brS (Pr ∷ Br′) (F.suc j) a = brS Br′ j a

        dS′ : ∀ {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {Q s}
            → D Γ Δ Q (Σ P ？[ S ]· Br) s
            → Γ & Δ ⊢p Q ◂ Σ P ？[ S ]· Br ∶ s
        dS′ ((j , U , t , member) , all) =
          t/recv (listed⇒step {G = G} member)
            (λ gr′ → brS Br _ (All.lookup all (step⇒listed {G = G} gr′) refl))
    soundAt {γ} {δ} (ifp E then Pr else Pr′) =
      record { dS = dS′ ; rS = mkR _ dS′ }
      where
        dS′ : ∀ {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P s}
            → D Γ Δ P (ifp E then Pr else Pr′) s
            → Γ & Δ ⊢p P ◂ ifp E then Pr else Pr′ ∶ s
        dS′ (etd , a , a′) =
          t/if etd (SoundAt.rS (soundAt Pr) a) (SoundAt.rS (soundAt Pr′) a′)
    soundAt {γ} {δ} (rec Pr) = record { dS = dS′ ; rS = mkR _ dS′ }
      where
        dS′ : ∀ {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P s}
            → D Γ Δ P (rec Pr) s
            → Γ & Δ ⊢p P ◂ rec Pr ∶ s
        dS′ (H , tr , mg , a) =
          t/unskip tr (t/rec mg (SoundAt.rS (soundAt Pr) a))
    soundAt {γ} {δ} (v X) = record { dS = dS′ ; rS = mkR _ dS′ }
      where
        dS′ : ∀ {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P s}
            → D Γ Δ P (v X) s
            → Γ & Δ ⊢p P ◂ v X ∶ s
        dS′ (H , tr , eq) = t/unskip tr (t/var eq)
    soundAt {γ} {δ} ∅ = record { dS = dS′ ; rS = mkR _ dS′ }
      where
        dS′ : ∀ {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P s}
            → D Γ Δ P ∅ s
            → Γ & Δ ⊢p P ◂ ∅ ∶ s
        dS′ done = t/end done

    d-sound :
      ∀ {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P Pr s}
      → D Γ Δ P Pr s → Γ & Δ ⊢p P ◂ Pr ∶ s
    d-sound {Pr = Pr} = SoundAt.dS (soundAt Pr)

    r-sound :
      ∀ {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P Pr s}
      → R Γ Δ P Pr s → Γ & Δ ⊢p P ◂ Pr ∶ s
    r-sound {Pr = Pr} = SoundAt.rS (soundAt Pr)
