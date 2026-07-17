{-# OPTIONS --guardedness #-}

-- Completeness of the shape-restricted judgment, and the resulting genuine
-- decision procedure for the declarative judgment:
--
--     complete : Γ & Δ ⊢p P ◂ Pr ∶ G₀ → Δ ~ᵛ Δ′ → G₀ -[¬ P ]->* H → H ~ W
--              → R Γ Δ′ P Pr W
--
--     checkD : ∀ Γ Δ P Pr s → Dec (Γ & Δ ⊢p P ◂ Pr ∶ s)
--
-- The proof is the δ-general mirror of `Safety/Head.agda`'s `td/head`,
-- landing in `R` instead of `⊢head`, and additionally quantified over `~`
-- (state and `Δ`) so the induction hypothesis covers every transport:
--
--   * `t/send`/`t/recv`: the enabled action survives the `¬P`-trace
--     (`skip/advance`/`branch/before`, Definitions/Behav.agda) and the `~`
--     (`~L→`/`~R→`).
--   * `t/rec`/`t/var`: the trace parks in the anchor of the restricted
--     `rec`/`v` clauses; `skip/bisim` re-roots it through the `~` — the
--     move `h/rec` makes in `td/head`, now also available at variables.
--   * `t/unskip`: composes into the trace (`skip/cat`).
--   * `t/skip` (`cancel/skip`, the real work): walk the trace into the
--     tree, unfolding the visited entry at each step with the Leaf-generic
--     `skip/unfold-cycle` (Safety/Skip.agda) while carrying the
--     leaf-normalization property `LeafR` along (`leafR/bisim`/
--     `leafR/unfold`, mirroring Safety/Head.agda's `LeafHead` plumbing);
--     once the trace is exhausted, `theoremA`
--     (Definitions/TypeChecker/Complete.agda) turns the tree into
--     `SemSkipP` over its main-leaf set, the leaves normalize into `R` by
--     induction, and `flatten` absorbs the leaves' own skip rounds so the
--     result lands in `SemSkipP (D …)` — the skip alternative of `R`.

open import Data.Bool using (T; true)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
import Data.Fin as F
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product
  using (_×_; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; lookup; _++_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (map′; toWitness; ⌊_⌋)

open import Definitions.Behav using (BTheory; WellBehaved)
open import Definitions.Expr using (Sort)
open import Definitions.TypeChecker.Core
import Definitions.TypeChecker.Restricted
import Definitions.TypeChecker.Complete
import Definitions.Typing as Typing
import Safety.Skip
import Safety.Head

module Definitions.TypeChecker.Completeness (N : ℕ) where

  open Processes N using (module GraphChecker; ProcessTyping; SessionTyping)
  open import LTS.Core N
    renaming (_-<_>->_ to GStep)
  open import LTS.Decision N using (wellBehaved?)
  open import LTS.Algebra N
    using (RootedGraph; underlying; initial; OpenGraph; compile)
  open import LTS.Reachability N
    using (PathVia; path/nil; path/cons; PathViaP; pathP/nil; pathP/cons)

  module GraphCompleteness
    (G : Graph)
    (wb : WellBehaved (graphTheory G))
    where

    open Typing.MPST wb hiding (_,_)
    open GraphChecker G wb
      using (SemSkipP; NLP; ReachLP; semSkipP-mono; RecvWitness)
    open Definitions.TypeChecker.Restricted.GraphRestricted N G wb
    open Definitions.TypeChecker.Complete.GraphComplete N G wb
      using (theoremA; semSkipP-bisim)
    module SK = Safety.Skip {N} {graphTheory G} wb
    module SH = Safety.Head {N} {graphTheory G} wb

    private
      variable
        γ δ ξ ξ′ : ℕ

    -- ════════════════════════════════════════════════════════════════
    --  Leaf-transport for `skip/unfold-cycle` at arbitrary Δ
    -- ════════════════════════════════════════════════════════════════

    leafBisim :
      ∀ {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {PPr : NProc γ δ} {a b : State G}
      → a ~ b
      → Γ & Δ ⊢p PPr ∶ a
      → Γ & Δ ⊢p PPr ∶ b
    leafBisim {PPr = P ◂ Pr} a~b td = SK.td/bisim ~ᵛ-refl a~b td

    -- ════════════════════════════════════════════════════════════════
    --  The leaf-normalization property, and its plumbing through the
    --  cycle-unfolding of skip trees (mirrors `LeafHead` in Safety/Head)
    -- ════════════════════════════════════════════════════════════════

    LeafR :
      ∀ {m} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {Ξ : Vec (State G) ξ} {P} {Pr : Proc γ δ} {s}
      → Γ & Δ & Ξ ⊢skip[ m ] P ◂ Pr ∶ s
      → Set
    LeafR {Γ = Γ} {Δ} {P = P} {Pr} std =
      ∀ {ℓ} {td : Γ & Δ ⊢p P ◂ Pr ∶ ℓ}
      → MainLeaf td std
      → ∀ {Δ′ H W} → Δ ~ᵛ Δ′ → ℓ -[¬ P ]->* H → H ~ W
      → R Γ Δ′ P Pr W

    leafR/bisim :
      ∀ {m} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {Ξ Ξ′ : Vec (State G) ξ} {P} {Pr : Proc γ δ} {a b}
      → (Ξ~Ξ′ : Ξ ~ᵛ Ξ′)
      → (a~b : a ~ b)
      → (std : Γ & Δ & Ξ ⊢skip[ m ] P ◂ Pr ∶ a)
      → LeafR std
      → LeafR (SK.skip-leaf/bisim leafBisim Ξ~Ξ′ a~b std)
    leafR/bisim Ξ~Ξ′ a~b (skip/main td) lr main/here Δ~ tr H~W =
      let _ , tr₀ , H₀~H = SH.skip/bisim-back a~b tr
      in lr main/here Δ~ tr₀ (~trans H₀~H H~W)
    leafR/bisim Ξ~Ξ′ a~b (skip/step _ _ ktd _) lr (main/step gr′ leaf) =
      leafR/bisim
        (~ᵛ/∷ a~b Ξ~Ξ′)
        (~R→~ a~b gr′)
        (ktd (~R→ a~b gr′) .proj₂)
        (lr ∘ main/step (~R→ a~b gr′))
        leaf
    leafR/bisim Ξ~Ξ′ a~b (skip/cycle eq) lr ()

    leafR/unfold :
      ∀ {m m′} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {P} {Pr : Proc γ δ} {s H}
        {Ξ : Vec (State G) ξ} {Ξ′ : Vec (State G) ξ′}
      → (base : Γ & Δ & Ξ′ ++ Ξ ⊢skip[ m ] P ◂ Pr ∶ s)
      → LeafR base
      → (inner : Γ & Δ & Ξ′ ++ (s ∷ Ξ) ⊢skip[ m′ ] P ◂ Pr ∶ H)
      → LeafR inner
      → LeafR (SK.skip/unfold-cycle {Ξ = Ξ} {Ξ′ = Ξ′} leafBisim base inner
                 .proj₂ .proj₁)
    leafR/unfold base baseLR (skip/main td) innerLR main/here =
      innerLR main/here
    leafR/unfold {Ξ = Ξ} {Ξ′ = Ξ′}
      base baseLR
      (skip/step {G = H} gr na ktd ok)
      innerLR
      (main/step gr′ leaf) =
      leafR/unfold
        {Ξ′ = H ∷ Ξ′}
        (SK.skip/weaken-visited {H = H} {Ξ = Ξ′ ++ Ξ} {Ξ′ = []} base)
        (baseLR ∘ SH.mainLeaf/weaken-visited base)
        (ktd gr′ .proj₂)
        (innerLR ∘ main/step gr′)
        leaf
    leafR/unfold {Ξ = Ξ} {Ξ′ = Ξ′}
      base baseLR (skip/cycle {X = X} eq) innerLR leaf
      with SK.lookup/insert {Ξ = Ξ} {Ξ′ = Ξ′} (X , eq)
    ... | inj₁ s~H =
      leafR/bisim ~ᵛ-refl s~H base baseLR leaf
    ... | inj₂ _ with leaf
    ...   | ()

    unfold-top :
      ∀ {m} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {P} {Pr : Proc γ δ} {s H}
      → Γ & Δ & [] ⊢skip[ prod ] P ◂ Pr ∶ s
      → Γ & Δ & (s ∷ []) ⊢skip[ m ] P ◂ Pr ∶ H
      → Γ & Δ & [] ⊢skip[ prod ] P ◂ Pr ∶ H
    unfold-top base inner
      with SK.skip/unfold-cycle {Ξ = []} {Ξ′ = []} leafBisim base inner
    ... | prod , unfolded , _ = unfolded
    ... | nonprod , skip/cycle {X = ()} _ , _

    leafR/unfold-top :
      ∀ {m} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {P} {Pr : Proc γ δ} {s H}
      → (base : Γ & Δ & [] ⊢skip[ prod ] P ◂ Pr ∶ s)
      → LeafR base
      → (inner : Γ & Δ & (s ∷ []) ⊢skip[ m ] P ◂ Pr ∶ H)
      → LeafR inner
      → LeafR (unfold-top base inner)
    leafR/unfold-top base baseLR inner innerLR
      with SK.skip/unfold-cycle {Ξ = []} {Ξ′ = []} leafBisim base inner
         | leafR/unfold {Ξ = []} {Ξ′ = []} base baseLR inner innerLR
    ... | prod , unfolded , _ | lr = lr
    ... | nonprod , skip/cycle {X = ()} _ , _ | _

    -- ════════════════════════════════════════════════════════════════
    --  `flatten`: absorb the leaves' own skip rounds
    --
    --  `SemSkipP` over the full judgment `R` collapses to `SemSkipP` over
    --  the direct layer `D`: walk each `D`-avoiding path to its first
    --  `R`-state (decidable, `R?`); its skip round takes over from there.
    -- ════════════════════════════════════════════════════════════════

    private
      pathVia-cat :
        ∀ {a b c m n}
        → PathVia G (λ _ → true) a b m
        → PathVia G (λ _ → true) b c n
        → PathVia G (λ _ → true) a c (m + n)
      pathVia-cat path/nil q = q
      pathVia-cat (path/cons ok gr p) q = path/cons ok gr (pathVia-cat p q)

    flatten :
      ∀ {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P} {Pr : Proc γ δ} {W}
      → SemSkipP (λ t → R Γ Δ P Pr t) P W
      → SemSkipP (D Γ Δ P Pr) P W
    flatten {Γ = Γ} {Δ} {P} {Pr} {W} semR t (pathD , ¬Dt) =
      case-split (splitR pathD)
      where
        -- reach a D-state from a state whose skip round we already hold
        useSem :
          ∀ {u}
          → SemSkipP (D Γ Δ P Pr) P u
          → PathViaP G (λ x → ¬ D Γ Δ P Pr x) u t
          → (P not-active-in t) × ReachLP (D Γ Δ P Pr) t
        useSem semD suffix = semD t (suffix , ¬Dt)

        -- find the first R-state strictly before `t` on a D-avoiding path
        splitR :
          ∀ {a}
          → PathViaP G (λ x → ¬ D Γ Δ P Pr x) a t
          → PathViaP G (λ x → ¬ R Γ Δ P Pr x) a t
          ⊎ (Σ[ u ∈ State G ]
               SemSkipP (D Γ Δ P Pr) P u
             × PathViaP G (λ x → ¬ D Γ Δ P Pr x) u t)
        splitR pathP/nil = inj₁ pathP/nil
        splitR {a} p₀@(pathP/cons ¬Da gr rest) with R? Γ Δ P Pr a
        ... | yes (inj₁ d)   = ⊥-elim (¬Da d)
        ... | yes (inj₂ sem) = inj₂ (a , sem , p₀)
        ... | no ¬Ra with splitR rest
        ...   | inj₁ q  = inj₁ (pathP/cons ¬Ra gr q)
        ...   | inj₂ hit = inj₂ hit

        -- extend a reach of an R-state to a reach of a D-state
        extendR :
          ∀ {u} → ReachLP (λ x → R Γ Δ P Pr x) u
          → ReachLP (D Γ Δ P Pr) u
        extendR (ℓ , (n , p) , inj₁ d) = ℓ , (n , p) , d
        extendR (ℓ , (n , p) , inj₂ semDℓ) with D? Γ Δ P Pr ℓ
        ... | yes d = ℓ , (n , p) , d
        ... | no ¬Dℓ with semDℓ ℓ (pathP/nil , ¬Dℓ)
        ...   | _ , ℓ′ , (n′ , p′) , d =
          ℓ′ , (n + n′ , pathVia-cat p p′) , d

        case-split :
          PathViaP G (λ x → ¬ R Γ Δ P Pr x) W t
          ⊎ (Σ[ u ∈ State G ]
               SemSkipP (D Γ Δ P Pr) P u
             × PathViaP G (λ x → ¬ D Γ Δ P Pr x) u t)
          → (P not-active-in t) × ReachLP (D Γ Δ P Pr) t
        case-split (inj₂ (u , semDu , suffix)) = useSem semDu suffix
        case-split (inj₁ pathR) with R? Γ Δ P Pr t
        ... | yes (inj₁ d)    = ⊥-elim (¬Dt d)
        ... | yes (inj₂ semDt) = useSem semDt pathP/nil
        ... | no ¬Rt with semR t (pathR , ¬Rt)
        ...   | na , reachR = na , extendR reachR

    -- ════════════════════════════════════════════════════════════════
    --  The `t/skip` endgame: tree → SemSkipP over the main-leaf set →
    --  leaves normalize into `R` → flatten into `SemSkipP (D …)`
    -- ════════════════════════════════════════════════════════════════

    skipSem :
      ∀ {Γ : Vec Sort γ} {Δ Δ′ : Vec (State G) δ}
        {P} {Pr : Proc γ δ} {s W}
      → (std : Γ & Δ & [] ⊢skip[ prod ] P ◂ Pr ∶ s)
      → LeafR std
      → Δ ~ᵛ Δ′
      → s ~ W
      → SemSkipP (D Γ Δ′ P Pr) P W
    skipSem {Γ = Γ} {Δ} {Δ′} {P} {Pr} {s} {W} std lr Δ~ s~W =
      flatten
        (semSkipP-mono
          (λ { (ℓ , td , hml , ℓ~u) → lr hml Δ~ skip/refl ℓ~u })
          (semSkipP-bisim Lcl s~W (theoremA L Lcl std lc)))
      where
        L : State G → Set
        L u = ∃[ ℓ ] Σ[ td ∈ Γ & Δ ⊢p P ◂ Pr ∶ ℓ ] MainLeaf td std × ℓ ~ u

        Lcl : ∀ {u u′} → L u → u ~ u′ → L u′
        Lcl (ℓ , td , hml , ℓ~u) u~u′ = ℓ , td , hml , ~trans ℓ~u u~u′

        lc : ∀ {ℓ} {td} → MainLeaf {G′ = ℓ} td std → L ℓ
        lc {ℓ} {td} hml = ℓ , td , hml , ~refl

    -- walk the trace into the tree (mirror of `cancel/unskip`)
    cancel/skip :
      ∀ {Γ : Vec Sort γ} {Δ Δ′ : Vec (State G) δ}
        {P} {Pr : Proc γ δ} {G₀ H W}
      → (tr : G₀ -[¬ P ]->* H)
      → (std : Γ & Δ & [] ⊢skip[ prod ] P ◂ Pr ∶ G₀)
      → LeafR std
      → Δ ~ᵛ Δ′
      → H ~ W
      → R Γ Δ′ P Pr W
    cancel/skip skip/refl (skip/main _) lr Δ~ H~W =
      lr main/here Δ~ skip/refl H~W
    cancel/skip skip/refl std@(skip/step _ _ _ _) lr Δ~ H~W =
      inj₂ (skipSem std lr Δ~ H~W)
    cancel/skip tr@(skip/step _ _ _) (skip/main _) lr Δ~ H~W =
      lr main/here Δ~ tr H~W
    cancel/skip (skip/step gr P∉ tr) std@(skip/step _ _ ktd _) lr Δ~ H~W =
      cancel/skip tr
        (unfold-top std (ktd gr .proj₂))
        (leafR/unfold-top std lr (ktd gr .proj₂) (lr ∘ main/step gr))
        Δ~ H~W

    -- ════════════════════════════════════════════════════════════════
    --  Completeness
    -- ════════════════════════════════════════════════════════════════

    -- branch-vector companion for the receive case
    r→rbr :
      ∀ {I} {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {Q t}
        (Br : Vec (Proc γ δ) I) (j : Fin I)
      → R Γ Δ Q (lookup Br j) t
      → RBr Γ Δ Q Br j t
    r→rbr (Pr ∷ Br) F.zero    r = r
    r→rbr (Pr ∷ Br) (F.suc j) r = r→rbr Br j r

    mutual

      complete :
        ∀ {Γ : Vec Sort γ} {Δ Δ′ : Vec (State G) δ}
          {P} {Pr : Proc γ δ} {G₀ H W}
        → Γ & Δ ⊢p P ◂ Pr ∶ G₀
        → Δ ~ᵛ Δ′
        → G₀ -[¬ P ]->* H
        → H ~ W
        → R Γ Δ′ P Pr W
      complete (t/send gr etd td) Δ~ tr H~W =
        let _ , grH , trα = skip/advance tr gr (∈S refl)
        in inj₁ (_ , _ , etd , ~L→ H~W grH
                , complete td Δ~ trα (~L→~ H~W grH))
      complete {Γ = Γ} {Δ′ = Δ′} {P = Q} {W = W}
        (t/recv {P = P₁} {Br = Br} gr conts) Δ~ tr H~W =
        inj₁ (rw , All.tabulate at-edge)
        where
          adv = skip/advance tr gr (∈R refl)

          rw : RecvWitness P₁ Q _ (edges G W)
          rw = _ , _ , _ , step⇒listed {G = G} (~L→ H~W (proj₁ (proj₂ adv)))

          at-edge :
            ∀ {e} → e ∈ edges G W
            → RecvAtR Γ Δ′ P₁ Q Br e
          at-edge {β , u} mem {j} {U} eq =
            r→rbr Br j
              (complete (conts gr₀) Δ~ tr_j
                (~R→~ H~W grW))
            where
              grW : W -< P₁ ⟶ Q # j < U > >-> u
              grW = subst (λ b → W -< b >-> u) eq (listed⇒step {G = G} mem)

              bb = branch/before tr gr (~R→ H~W grW)

              gr₀  = proj₁ (proj₂ bb)
              tr_j = proj₂ (proj₂ bb)
      complete (t/skip std) Δ~ tr H~W =
        cancel/skip tr std (mainLeaf/r std) Δ~ H~W
      complete (t/unskip tr′ td) Δ~ tr H~W =
        complete td Δ~ (skip/cat tr′ tr) H~W
      complete (t/if etd ttd ftd) Δ~ tr H~W =
        inj₁ (etd , complete ttd Δ~ tr H~W , complete ftd Δ~ tr H~W)
      complete (t/rec mg td) Δ~ tr H~W =
        let H₀ , G₀~H₀ , tr₀ = SK.skip/bisim H~W tr
        in inj₁ (H₀ , tr₀ , mg
                , complete td (~ᵛ/∷ G₀~H₀ Δ~) skip/refl G₀~H₀)
      complete (t/var eq) Δ~ tr H~W =
        let H₀ , G₀~H₀ , tr₀ = SK.skip/bisim H~W tr
        in inj₁ (H₀ , tr₀ , ~trans (lookup/~ᵛ Δ~ _ eq) G₀~H₀)
      complete (t/end done) Δ~ tr H~W =
        inj₁ (λ P∈W → done (skip/∈T-back tr (∈~ (~sym H~W) P∈W)))

      mainLeaf/r :
        ∀ {m} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
          {Ξ : Vec (State G) ξ} {P} {Pr : Proc γ δ} {s}
        → (std : Γ & Δ & Ξ ⊢skip[ m ] P ◂ Pr ∶ s)
        → LeafR std
      mainLeaf/r (skip/main td) main/here Δ~ tr ~W =
        complete td Δ~ tr ~W
      mainLeaf/r (skip/step _ _ ktd _) (main/step gr′ leaf) =
        mainLeaf/r (ktd gr′ .proj₂) leaf
      mainLeaf/r (skip/cycle _) ()

    complete₀ :
      ∀ {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P} {Pr : Proc γ δ} {s}
      → Γ & Δ ⊢p P ◂ Pr ∶ s
      → R Γ Δ P Pr s
    complete₀ td = complete td ~ᵛ-refl skip/refl ~refl

    -- ════════════════════════════════════════════════════════════════
    --  The decision procedures for the declarative judgment
    -- ════════════════════════════════════════════════════════════════

    checkD :
      ∀ (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
        (P : Part) (Pr : Proc γ δ) (s : State G)
      → Dec (Γ & Δ ⊢p P ◂ Pr ∶ s)
    checkD Γ Δ P Pr s = map′ r-sound complete₀ (R? Γ Δ P Pr s)

    checkClosedD :
      ∀ (Γ : Vec Sort γ) (P : Part) (Pr : Proc γ 0) (s : State G)
      → Dec (Γ & [] ⊢p P ◂ Pr ∶ s)
    checkClosedD Γ P Pr s = checkD Γ [] P Pr s

    private
      allDec :
        ∀ {n} {A : Fin n → Set}
        → (∀ i → Dec (A i)) → Dec (∀ i → A i)
      allDec {zero}  d = yes (λ ())
      allDec {suc n} d with d F.zero | allDec (λ i → d (F.suc i))
      ... | yes a  | yes rest = yes λ { F.zero → a ; (F.suc i) → rest i }
      ... | no ¬a  | _        = no  λ f → ¬a (f F.zero)
      ... | _      | no ¬rest = no  λ f → ¬rest (λ i → f (F.suc i))

    checkSessionD : (M : Session) (s : State G) → Dec (⊢s M ∶ s)
    checkSessionD M s = allDec (λ P → checkClosedD [] P (M [ P ]s) s)

  -- ── The public interface (same types as before the overhaul) ──

  WBGraph : Set
  WBGraph = Σ[ R ∈ RootedGraph ] T ⌊ wellBehaved? (underlying R) ⌋

  wb-of : (WR : WBGraph) → WellBehaved (graphTheory (underlying (proj₁ WR)))
  wb-of WR = toWitness (proj₂ WR)

  buildG :
    (OG : OpenGraph 0) → {p : T ⌊ wellBehaved? (underlying (compile OG)) ⌋}
    → WBGraph
  buildG OG {p} = compile OG , p

  typecheck :
    (WR : WBGraph) (P : Processes.Common.Part N) (Pr : Processes.Syntax.Proc N 0 0)
    → Dec (ProcessTyping (underlying (proj₁ WR)) (wb-of WR) [] P Pr
             (initial (proj₁ WR)))
  typecheck WR P Pr =
    GraphCompleteness.checkClosedD (underlying (proj₁ WR)) (wb-of WR) [] P Pr
      (initial (proj₁ WR))

  typecheckSession :
    (WR : WBGraph) (M : Processes.Syntax.Session N)
    → Dec (SessionTyping (underlying (proj₁ WR)) (wb-of WR) M
             (initial (proj₁ WR)))
  typecheckSession WR M =
    GraphCompleteness.checkSessionD (underlying (proj₁ WR)) (wb-of WR) M
      (initial (proj₁ WR))
