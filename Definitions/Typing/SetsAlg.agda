{-# OPTIONS --guardedness #-}

-- TODO.md §7 step 5: `⊢a ⟺ ⊢set`.
--
-- This file has the SOUNDNESS half, `set⇒alg`: a set-based derivation types
-- every state of its set algorithmically.  This is the half that was FALSE
-- while `Wait` was a ν (`Tests/WaitNotSkip.agda`); with `WaitV` it is a direct
-- structural recursion.
--
-- The shape of every case is the same three moves:
--
--   1. `sub` turns the state's membership in `𝒮` into a `Wait`;
--   2. `wait⇒skip` (`SetsEquiv.agda`) turns that into a `⊢skip` tree whose
--      leaf family is the rule's own — one `Pred`, constant in the process;
--   3. `skip/map` rewrites those leaves into `⊢blocked` ones, which is where
--      the recursion on the sub-derivations happens, and `a/skip` closes it.
--
-- Step 3 is why `skip/map` only asks for the leaf translation at the tree's
-- OWN process: a `⊢skip` tree never changes the process it is about
-- (`skip/step` and `skip/cycle` both keep `P ◂ Pr` fixed), so the general map
-- over all of `NProc` — which is what a constant leaf family could not
-- provide — is never needed.

open import Data.Nat using (ℕ; suc)

open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_)

open import Relation.Nullary using (¬_)

open import Definitions.Expr using (⊢e-unique)

open import Definitions.Typing
import Definitions.Typing.Properties as Props

module Definitions.Typing.SetsAlg {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  open module M = MPST(wb)
  open M

  open Props wb using (skip/bisim; skip/bisim-back)

  open import Definitions.Typing.Sets wb
  open import Definitions.Typing.SetsEquiv wb using (wait⇒skip; skip⇒wait)
  open import Definitions.Typing.MainLeaf wb using (findMain)
  open import Definitions.Typing.AlgProperties wb using (alg/~)
  open import Definitions.Typing.Algorithmic wb

  private
    variable
      γ δ ξ : ℕ

  -- Rewriting the leaf family of a `⊢skip` tree.  The translation is only
  -- required at `PPr`, the process the tree is about, because that is the only
  -- process at which `skip/main` can fire inside it.
  skip/map :
    ∀ {L₁ L₂ : NProc γ δ → Behav → Set}
      {Ξ : Vec Behav ξ}{PPr G}
    → (∀ {H} → L₁ PPr H → L₂ PPr H)
    → L₁ & Ξ ⊢skip PPr ∶ G
    → L₂ & Ξ ⊢skip PPr ∶ G

  skip/map f (skip/main x) =
    skip/main (f x)

  skip/map f (skip/step gr na ktd) =
    skip/step gr na (λ gr′ → skip/map f (ktd gr′))

  skip/map f (skip/cycle eq inT) =
    skip/cycle eq inT

  -- ══════════════════════════════════════════════════════════════════
  --  Soundness: a set derivation types every state of its set
  -- ══════════════════════════════════════════════════════════════════

  set⇒alg :
    ∀ {Γ : Vec Sort γ}{Δ : Vec Behav δ}{PPr}{𝒮 : Pred}{G}
    → Γ & Δ ⊢ PPr ∶ 𝒮
    → 𝒮 G
    → Γ & Δ ⊢a PPr ∶ G

  set⇒alg (s/send {P = P}{Q = Q}{i = i}{E = E}{Pr = Pr} etd td _ sub) 𝒮G =
    a/skip
      (skip/map
        (λ { (_ , gr , 𝒯u′) → blocked/send gr etd (set⇒alg td 𝒯u′) })
        (wait⇒skip P (Q ! i < E >∙ Pr) _ (sub 𝒮G)))

  -- The `∃` conjunct supplies `blocked/recv`'s one required edge; the `∀`
  -- conjunct supplies its continuations.  Both come out of the same leaf.
  set⇒alg (s/recv {P = P}{Q = Q}{Br = Br} conts _ sub) 𝒮G =
    a/skip
      (skip/map
        (λ { ((_ , _ , _ , gr) , k) →
               blocked/recv gr (λ gr′ → set⇒alg (conts (k gr′)) (k gr′)) })
        (wait⇒skip Q (Σ P ？· Br) _ (sub 𝒮G)))

  set⇒alg (s/if etd ttd ftd) 𝒮G =
    a/if etd (set⇒alg ttd 𝒮G) (set⇒alg ftd 𝒮G)

  set⇒alg (s/end done) 𝒮G =
    a/end (done 𝒮G)

  -- `Reach₀` is oriented `~`-then-reach and `blocked/var` reach-then-`~`;
  -- `skip/bisim-back` is exactly that interchange.
  set⇒alg (s/var {P = P}{X = X} sub) 𝒮G =
    a/skip
      (skip/map
        (λ { (_ , anc~ , tr) →
               let _ , tr′ , H₀~H = skip/bisim-back anc~ tr
               in blocked/var tr′ H₀~H })
        (wait⇒skip P (v X) _ (sub 𝒮G)))

  -- `⌈ W ⌉ W` is `~refl`, so the body's set derivation at its own anchor is
  -- exactly what `blocked/rec` wants.
  set⇒alg (s/rec {P = P}{Pr = Pr} guarded td sub) 𝒮G =
    a/skip
      (skip/map
        (λ { (_ , 𝒜W , tr) → blocked/rec tr guarded (set⇒alg (td 𝒜W) ~refl) })
        (wait⇒skip P (rec Pr) _ (sub 𝒮G)))

  -- ══════════════════════════════════════════════════════════════════
  --  Completeness: `⊢a` at any state gives the set derivation at the
  --  LARGEST set, namely `⊢a`-typeability itself
  -- ══════════════════════════════════════════════════════════════════
  --
  -- Stating it at `Alg` rather than at `⌈ G ⌉` is what makes it provable:
  -- `s/send`'s `𝒯` must cover the continuation states of EVERY leaf of the
  -- skip tree at once, which no singleton does.  `Alg` is the canonical such
  -- set, and the rules' downward closure (`set/mono`) recovers every smaller
  -- one, `⌈ G ⌉` included.
  --
  -- The recursion is on the PROCESS, not on the derivation: the derivation a
  -- case needs comes out of `findMain`, which is not a subterm of the one it
  -- came from.  `algBr` is the mutual companion that makes `lu Br j`
  -- structural.

  Alg : ∀ {γ δ} → Vec Sort γ → Vec Behav δ → NProc γ δ → Pred
  Alg Γ Δ PPr G = Γ & Δ ⊢a PPr ∶ G

  -- Downward closure of `𝒮`: it occurs only in `⊆`-premises.
  set/mono :
    ∀ {Γ : Vec Sort γ}{Δ : Vec Behav δ}{PPr}{𝒮 𝒮′ : Pred}
    → (∀ {s} → 𝒮′ s → 𝒮 s)
    → Γ & Δ ⊢ PPr ∶ 𝒮
    → Γ & Δ ⊢ PPr ∶ 𝒮′

  set/mono f (s/send etd td tc sub) = s/send etd td tc (λ x → sub (f x))
  set/mono f (s/recv conts tc sub) = s/recv conts tc (λ x → sub (f x))
  set/mono f (s/if etd ttd ftd)   = s/if etd (set/mono f ttd) (set/mono f ftd)
  set/mono f (s/end done)         = s/end (λ x → done (f x))
  set/mono f (s/var sub)          = s/var (λ x → sub (f x))
  set/mono f (s/rec g td sub)     = s/rec g td (λ x → sub (f x))

  -- Inversions.  `ifp` and `∅` have no `⊢blocked` form, so `a/skip` at one of
  -- them would need a leafless tree — which `findMain` refutes constructively.
  module _ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{P} where

    inv/end :
      ∀ {G}
      → Γ & Δ ⊢a P ◂ ∅ ∶ G
      → ¬ P ∈T G

    inv/end (a/end done) = done
    inv/end (a/skip std) with findMain P ∅ (Γ & Δ ⊢blocked_∶_) std
    ... | _ , ()

    inv/ifE :
      ∀ {E}{A B : Proc γ δ}{G}
      → Γ & Δ ⊢a P ◂ ifp E then A else B ∶ G
      → Γ ⊢e E ∶ s/bool

    inv/ifE (a/if etd _ _) = etd
    inv/ifE {E}{A}{B} (a/skip std)
      with findMain P (ifp E then A else B) (Γ & Δ ⊢blocked_∶_) std
    ... | _ , ()

    inv/ifT :
      ∀ {E}{A B : Proc γ δ}{G}
      → Γ & Δ ⊢a P ◂ ifp E then A else B ∶ G
      → Γ & Δ ⊢a P ◂ A ∶ G

    inv/ifT (a/if _ ttd _) = ttd
    inv/ifT {E}{A}{B} (a/skip std)
      with findMain P (ifp E then A else B) (Γ & Δ ⊢blocked_∶_) std
    ... | _ , ()

    inv/ifF :
      ∀ {E}{A B : Proc γ δ}{G}
      → Γ & Δ ⊢a P ◂ ifp E then A else B ∶ G
      → Γ & Δ ⊢a P ◂ B ∶ G

    inv/ifF (a/if _ _ ftd) = ftd
    inv/ifF {E}{A}{B} (a/skip std)
      with findMain P (ifp E then A else B) (Γ & Δ ⊢blocked_∶_) std
    ... | _ , ()

  -- Leaf translations, the mirror images of `set⇒alg`'s.  The sort in
  -- `s/send`'s family is fixed once, outside the set; `⊢e-unique` is what says
  -- every leaf agrees with that choice.
  module _ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ} where

    sendLeaf :
      ∀ {P Q I}{i : Fin (suc I)}{S E}{Pr : Proc γ δ}{H}
      → Γ ⊢e E ∶ S
      → Γ & Δ ⊢blocked P ◂ Q ! i < E >∙ Pr ∶ H
      → ∃[ u′ ] (H -< P ⟶ Q # i < S > >-> u′) × Alg Γ Δ (P ◂ Pr) u′

    sendLeaf etd (blocked/send gr etd′ td)
      rewrite ⊢e-unique etd′ etd = _ , gr , td

    inv/sendE :
      ∀ {P Q I}{i : Fin (suc I)}{E}{Pr : Proc γ δ}{G}
      → Γ & Δ ⊢a P ◂ Q ! i < E >∙ Pr ∶ G
      → Σ[ S ∈ Sort ] Γ ⊢e E ∶ S

    inv/sendE {P}{Q}{i = i}{E}{Pr} (a/skip std)
      with findMain P (Q ! i < E >∙ Pr) (Γ & Δ ⊢blocked_∶_) std
    ... | _ , blocked/send _ etd _ = _ , etd

    sendSub :
      ∀ {P Q I}{i : Fin (suc I)}{S E}{Pr : Proc γ δ}{s}
      → Γ ⊢e E ∶ S
      → Γ & Δ ⊢a P ◂ Q ! i < E >∙ Pr ∶ s
      → Wait P (λ u → ∃[ u′ ] (u -< P ⟶ Q # i < S > >-> u′) × Alg Γ Δ (P ◂ Pr) u′) s

    sendSub etd (a/skip std) =
      skip⇒wait _ _ _ (skip/map (sendLeaf etd) std)

    recvLeaf :
      ∀ {P Q I}{Br : Vec (Proc (suc γ) δ) (suc I)}{H}
      → Γ & Δ ⊢blocked Q ◂ Σ P ？· Br ∶ H
      → (Σ[ j ∈ Fin (suc I) ] ∃[ U ] ∃[ t ] (H -< P ⟶ Q # j < U > >-> t))
      × (∀ {j U t} → H -< P ⟶ Q # j < U > >-> t → Alg (U ∷ Γ) Δ (Q ◂ lu Br j) t)

    recvLeaf (blocked/recv gr conts) =
      (_ , _ , _ , gr) , conts

    recvSub :
      ∀ {P Q I}{Br : Vec (Proc (suc γ) δ) (suc I)}{s}
      → Γ & Δ ⊢a Q ◂ Σ P ？· Br ∶ s
      → Wait Q
          (λ u → (Σ[ j ∈ Fin (suc I) ] ∃[ U ] ∃[ t ] (u -< P ⟶ Q # j < U > >-> t))
               × (∀ {j U t} → u -< P ⟶ Q # j < U > >-> t → Alg (U ∷ Γ) Δ (Q ◂ lu Br j) t))
          s

    recvSub (a/skip std) =
      skip⇒wait _ _ _ (skip/map recvLeaf std)

    varLeaf :
      ∀ {P}{X : Fin δ}{H}
      → Γ & Δ ⊢blocked P ◂ v X ∶ H
      → Reach₀ P ⌈ lu Δ X ⌉ H

    varLeaf (blocked/var tr H~G) =
      skip/bisim H~G tr

    varSub :
      ∀ {P}{X : Fin δ}{s}
      → Γ & Δ ⊢a P ◂ v X ∶ s
      → Wait P (Reach₀ P ⌈ lu Δ X ⌉) s

    varSub (a/skip std) =
      skip⇒wait _ _ _ (skip/map varLeaf std)

    recLeaf :
      ∀ {P}{Pr : Proc γ (suc δ)}{H}
      → Γ & Δ ⊢blocked P ◂ rec Pr ∶ H
      → Reach₀ P (λ W → Alg Γ (W ∷ Δ) (P ◂ Pr) W) H

    recLeaf (blocked/rec tr guarded td) =
      _ , td , tr

    recSub :
      ∀ {P}{Pr : Proc γ (suc δ)}{s}
      → Γ & Δ ⊢a P ◂ rec Pr ∶ s
      → Wait P (Reach₀ P (λ W → Alg Γ (W ∷ Δ) (P ◂ Pr) W)) s

    recSub (a/skip std) =
      skip⇒wait _ _ _ (skip/map recLeaf std)

    recGuard :
      ∀ {P}{Pr : Proc γ (suc δ)}{G}
      → Γ & Δ ⊢a P ◂ rec Pr ∶ G
      → MessageGuarded Pr

    recGuard {P}{Pr} (a/skip std)
      with findMain P (rec Pr) (Γ & Δ ⊢blocked_∶_) std
    ... | _ , blocked/rec _ guarded _ = guarded

  mutual

    alg⇒set :
      ∀ {Γ : Vec Sort γ}{Δ : Vec Behav δ}{P}(Pr : Proc γ δ){G}
      → Γ & Δ ⊢a P ◂ Pr ∶ G
      → Γ & Δ ⊢ P ◂ Pr ∶ Alg Γ Δ (P ◂ Pr)

    -- The leaf supplies the sort and the continuation's derivation; the
    -- recursion then covers EVERY state the continuation is typeable at.
    alg⇒set {Γ = Γ}{Δ = Δ}{P = P} (Q ! i < E >∙ Pr) (a/skip std)
      with findMain P (Q ! i < E >∙ Pr) (Γ & Δ ⊢blocked_∶_) std
    ... | _ , blocked/send _ etd td =
      s/send etd (alg⇒set Pr td) (λ G~H → alg/~ G~H) (sendSub etd)

    alg⇒set (Σ Q ？· Br) td =
      s/recv (λ {j} w → algBr Br j w) (λ G~H → alg/~ G~H) recvSub

    alg⇒set (ifp E then A else B) td =
      s/if
        (inv/ifE td)
        (set/mono inv/ifT (alg⇒set A (inv/ifT td)))
        (set/mono inv/ifF (alg⇒set B (inv/ifF td)))

    alg⇒set ∅ td =
      s/end inv/end

    alg⇒set (v X) td =
      s/var varSub

    alg⇒set (rec Pr) td =
      s/rec
        (recGuard td)
        (λ {W} 𝒜W → set/mono (λ W~s → alg/~ W~s 𝒜W) (alg⇒set Pr 𝒜W))
        recSub

    -- Makes `lu Br j` structural: `Br` shrinks going in, the branch shrinks
    -- coming out.
    algBr :
      ∀ {n}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{Q}
        (Br : Vec (Proc (suc γ) δ) n)(j : Fin n){U t}
      → (U ∷ Γ) & Δ ⊢a Q ◂ lu Br j ∶ t
      → (U ∷ Γ) & Δ ⊢ Q ◂ lu Br j ∶ Alg (U ∷ Γ) Δ (Q ◂ lu Br j)

    algBr (B ∷ Bs) fz      w = alg⇒set B w
    algBr (B ∷ Bs) (fs j)  w = algBr Bs j w

  -- ══════════════════════════════════════════════════════════════════
  --  `⊢a`'s pointwise shape, in the set world
  -- ══════════════════════════════════════════════════════════════════
  --
  -- `Safety/` needs "this process is typed AT this state", which is what `⊢a`
  -- said directly.  The set judgment says it about a whole set, so the
  -- pointwise form is the set plus a membership.  This is the form `Safety/`
  -- is stated over; `⊢a` is the thing being retired, not this.
  --
  -- `⊨⇒alg`/`alg⇒⊨` are the two halves of step 5 packaged for that use, so no
  -- `Safety/` file has to mention `Alg` or apply `alg⇒set` by hand.

  infix 4 _&_⊨_∶_

  _&_⊨_∶_ :
    ∀ {γ δ} → Vec Sort γ → Vec Behav δ → NProc γ δ → Behav → Set₁
  Γ & Δ ⊨ PPr ∶ G = Σ[ 𝒮 ∈ Pred ] (Γ & Δ ⊢ PPr ∶ 𝒮) × 𝒮 G

  ⊨⇒alg :
    ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{PPr}{G}
    → Γ & Δ ⊨ PPr ∶ G
    → Γ & Δ ⊢a PPr ∶ G
  ⊨⇒alg (_ , d , mem) = set⇒alg d mem

  alg⇒⊨ :
    ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{P}{Pr : Proc γ δ}{G}
    → Γ & Δ ⊢a P ◂ Pr ∶ G
    → Γ & Δ ⊨ P ◂ Pr ∶ G
  alg⇒⊨ {Pr = Pr} td = _ , alg⇒set Pr td , td

  -- Inversions for `Safety/`.  Each is ONE clause, because the set judgment is
  -- syntax directed: there is no `a/skip` wrapper to look past and no skip tree
  -- to chase.  Compare `Norm.agda`'s `a/if/inv`, which needs a second clause
  -- for `a/skip` and a walk over the tree beneath it.

  ⊨/if-inv :
    ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{P E}{A B : Proc γ δ}{G}
    → Γ & Δ ⊨ P ◂ ifp E then A else B ∶ G
    → (Γ ⊢e E ∶ s/bool) × (Γ & Δ ⊨ P ◂ A ∶ G) × (Γ & Δ ⊨ P ◂ B ∶ G)

  ⊨/if-inv (𝒮 , s/if etd ttd ftd , mem) =
    etd , (𝒮 , ttd , mem) , (𝒮 , ftd , mem)

  ⊨/rec-guarded :
    ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{P}{Pr : Proc γ (suc δ)}{G}
    → Γ & Δ ⊨ P ◂ rec Pr ∶ G
    → MessageGuarded Pr

  ⊨/rec-guarded (_ , s/rec guarded _ _ , _) = guarded

  ⊨/end-inv :
    ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{P}{G}
    → Γ & Δ ⊨ P ◂ ∅ ∶ G
    → ¬ P ∈T G

  ⊨/end-inv (_ , s/end done , mem) = done mem
