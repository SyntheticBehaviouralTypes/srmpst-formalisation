{-# OPTIONS --guardedness #-}

-- The safety theorems, for a session typed by `⊢s[ Ρ ]` (each process
-- against its block's local view): preservation along the global view,
-- progress, no infinite τ run, and `safety` over whole runs.
-- `singleton/⊢s`: the one-role-per-process case, typed against `B`.

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; length)
open import Data.Fin.Subset using (_∈_; ⁅_⁆)
open import Data.Fin.Subset.Properties using (⊆-antisym; x∈⁅x⁆; x∈⁅y⁆⇒x≡y)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
open import Data.Vec using ([]) renaming (lookup to lu)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Definitions.Typing
import Definitions.Transfer as Transfer
import Definitions.Typing.AlgNorm as AlgNorm
import Definitions.Typing.AlgDeclarative as AlgDeclarative
import Safety.Preservation as Pres
import Safety.Progress as Prog
import Safety.Termination as Term

module Safety
  {N : ℕ} {B : BTheory N} (wb : WellBehaved B) (sync : Synchronous B) where

open BTheory B
open import Definitions.Proc N using (Assignment; module Over; singletons; _◂_)
open import Definitions.View B using (view; _-<_>->ᵛ_)
open import Definitions.View B public using (module Global)
open import Definitions.View.Lemmas B wb sync using (singleton⇒; singleton⇐)

open Sessions B public using (⊢ᵛ[_]_∶_; ⊢s[_]_∶_)

module _ {K : ℕ} (Ρ : Assignment K) where

  open Assignment Ρ using (roles)
  open Over Ρ
  open Global Ρ using (_-<_>->ᵍ_; _-[_]->ᵍ_)

  private
    wbs : ∀ M {G} → ⊢s[ Ρ ] M ∶ G → ∀ j → WellBehaved (view (lu roles j))
    wbs _ ts j = proj₁ (ts j)

    -- `Safety/` is proved over `⊢a`; this converts.
    lower : ∀ M {G} (ts : ⊢s[ Ρ ] M ∶ G) → Pres.Typed.⊢ᴸ_∶_ wb sync Ρ (wbs M ts) M G
    lower M ts j =
      AlgNorm.td⇒at (wbs M ts j) (Pres.balL wb sync Ρ j) (proj₂ (ts j))

    raise : ∀ {wbL} M {G} → Pres.Typed.⊢ᴸ_∶_ wb sync Ρ wbL M G → ⊢s[ Ρ ] M ∶ G
    raise {wbL} _ t j = wbL j , AlgDeclarative.at⇒typing (wbL j) (t j)

  preservation :
    ∀ {M M′ G α} → ⊢s[ Ρ ] M ∶ G → M [ just α ]⇒ M′
    → ∃[ G′ ] G -< α >->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
  preservation {M} {M′} ts st =
    let G′ , gv , t′ =
          Pres.Typed.Exists.preservation/comm wb sync Ρ (wbs M ts) (lower M ts) st
    in G′ , gv , raise M′ t′

  preservation/τ : ∀ {M M′ G} → ⊢s[ Ρ ] M ∶ G → M [ nothing ]⇒ M′ → ⊢s[ Ρ ] M′ ∶ G
  preservation/τ {M} {M′} ts st =
    raise M′ (Pres.Typed.preservation/τ wb sync Ρ (wbs M ts) (lower M ts) st)

  progress : ∀ {M G} → ⊢s[ Ρ ] M ∶ G → done M ⊎ ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′
  progress {M} ts = Prog.progress wb sync Ρ (wbs M ts) (lower M ts)

  progress/eventual :
    ∀ {M G} → ⊢s[ Ρ ] M ∶ G
    → ∃[ M′ ] ((M τ⇒ M′ × finished M′)
             ⊎ (∃[ M″ ] ∃[ α ] M τ⇒ M″ × M″ [ just α ]⇒ M′))
  progress/eventual {M} ts =
    Prog.progress/eventual wb sync Ρ (wbs M ts) (lower M ts)

  no-infinite-τ-reductions : ∀ M {G} → ⊢s[ Ρ ] M ∶ G → M ⇒∞ → ⊥
  no-infinite-τ-reductions M ts =
    Term.no-infinite-τ-reductions wb sync Ρ (wbs M ts) M (lower M ts)

  private
    preservation/τ* : ∀ {M M′ G} → ⊢s[ Ρ ] M ∶ G → M τ⇒ M′ → ⊢s[ Ρ ] M′ ∶ G
    preservation/τ* {M} {M′} ts r =
      raise M′ (Pres.Typed.preservation/τ* wb sync Ρ (wbs M ts) (lower M ts) r)

  -- Preservation along a run.
  replay :
    ∀ {M M′ G αs} → ⊢s[ Ρ ] M ∶ G → M =[ αs ]⇒* M′
    → ∃[ G′ ] G -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
  replay ts run/end        = _ , BTheory.tr/refl , ts
  replay ts (run/τ st r)   = replay (preservation/τ ts st) r
  replay ts (run/comm st r) with preservation ts st
  ... | _ , gv , ts₁ with replay ts₁ r
  ...   | G′ , tr , ts′ = G′ , BTheory.tr/step gv tr , ts′

  -- For every `n`: a run to `finished`, or through `n` communications.
  continue :
    ∀ {M G} → ⊢s[ Ρ ] M ∶ G
    → ∀ n → ∃[ βs ] ∃[ M″ ] M =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n)
  continue ts zero = [] , _ , run/end , inj₂ refl
  continue {M} ts (suc n) with progress/eventual {M} ts
  ... | M″ , inj₁ (r , fin) = [] , M″ , r , inj₁ fin
  ... | M₂ , inj₂ (M₁ , α , r , st) with preservation (preservation/τ* ts r) st
  ...   | _ , _ , ts₂ with continue ts₂ n
  ...     | βs , M″ , r′ , p = α ∷ βs , M″ , r ++ʳ run/comm st r′ , map₂ (cong suc) p

  -- `replay`, then `continue`.
  safety :
    ∀ {M M′ G αs} → ⊢s[ Ρ ] M ∶ G → M =[ αs ]⇒* M′
    → ∃[ G′ ] G -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
              × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  safety ts r with replay ts r
  ... | G′ , tr , ts′ = G′ , tr , ts′ , continue ts′

-- ══════════════════════════════════════════════════════════════════════
--  Single-role sessions: the singleton case
-- ══════════════════════════════════════════════════════════════════════

-- Role `P`'s block in `singletons` is `⁅ P ⁆`.
roles/singletons : ∀ P → lu (Assignment.roles singletons) P ≡ ⁅ P ⁆
roles/singletons P =
  ⊆-antisym
    (λ {R} R∈ → subst (_∈ ⁅ P ⁆) (sym (∈/owner R∈)) (x∈⁅x⁆ P))
    (λ {R} R∈ → subst (λ Y → R ∈ lu roles Y) (x∈⁅y⁆⇒x≡y P R∈) (owner/∈ R))
  where open Assignment singletons

-- Per-role typings against `B` type the single-role session.
singleton/⊢s :
  ∀ {M : Over.Session singletons} {G}
  → (∀ P → MPST._&_⊢p_∶_ wb [] [] (⁅ P ⁆ ◂ lu M P) G)
  → ⊢s[ singletons ] M ∶ G
singleton/⊢s {M} {G} td P =
  subst (λ Ps → ⊢ᵛ[ Ps ] lu M P ∶ G)
    (sym (roles/singletons P))
    (T.wb⇒ wb , T.Typing.typing⇒ wb (T.wb⇒ wb) (td P))
  where
    module T = Transfer _-<_>->_ (_-<_>->ᵛ_ ⁅ P ⁆) singleton⇒ singleton⇐
