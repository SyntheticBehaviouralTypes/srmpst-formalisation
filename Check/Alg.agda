{-# OPTIONS --guardedness #-}

-- The set-based type checker (TODO.md §7 step 6) — the replacement for the
-- old, deleted 917-line `Check/Alg.agda`.
--
-- The algorithm IS the shape of the rules in `Definitions/Typing/Alg.agda`:
-- one case per process form, each of which
--
--   1. decides that rule's own leaf family, pointwise on states, and
--   2. hands it to `Check/Wait.agda`'s `wait?`.
--
-- Nothing here walks the graph and the process at the same time, so there is
-- no interleaved search, no `Justified`/`FailedFrom`, and no four-component
-- measure: the recursion is structural on the process, exactly as the rules
-- are, and every graph walk is inside `wait?` or `reach¬P?`.
--
-- The two directions of each case are `AlgNorm.agda`'s and
-- `AlgDeclarative.agda`'s lemmas, not re-derivations: `yes` builds the `⊢p`
-- derivation the way `alg⇒typing` does (`wait⇒skip` then `skip/map` then
-- `t/skip`), and `no` turns a hypothetical `⊢p` derivation back into the
-- `Wait` that was just refuted (`sendWait`/`recvWait`/`varWait`/`recWait`) or
-- into the premise that failed (`endNotin`, `ifTrue`/`ifFalse`, and
-- `waitFind` on `ifEWait`/`sendEWait`/`recGWait`).
--
-- It decides the DECLARATIVE judgment outright.  Until the old, deleted
-- two-tier `⊢a` was retired it decided that `⊢a` and crossed over by a round
-- trip; there is no crossing left.
--
-- WHY THIS STILL GOES THROUGH `⊢p` INTERNALLY (`Typ`/`tc?`), read before
-- "fixing" it: `a/send`'s `𝒯` (and `a/recv`'s `𝒯 j U`) is EXISTENTIAL and has
-- to cover the continuation state of EVERY leaf of the `Wait` search AT ONCE
-- — one leaf's own witness state is not enough (TODO.md §6, `AlgNorm.agda`'s
-- header).  `Typ` supplies that uniform, `~`-closed set FOR FREE, because
-- `typing⇒alg` (`AlgNorm.agda`) already proves "`⊢p` at one state converts to
-- `⊢a` at the WHOLE canonical set", by walking `⊢p`'s own `t/skip`/`t/unskip`
-- structure.  Building that same "one witness → uniform graph-wide `⊢a` set"
-- fact NATIVELY, without ever naming `⊢p`, means reproving `AlgNorm.agda`'s
-- entire construction (~800 lines: `sendWait`/`recvWait`/`varWait`/`recWait`,
-- `waitFollow`, the four leaf families and their `closed`/`adv` lemmas) a
-- second time over `⊢a`+`alg?` instead of `⊢p`.  That was attempted and
-- reverted here — see the conversation this file's history records — not
-- because it is impossible, but because it is a project on the scale of
-- `AlgNorm.agda` itself, not a cleanup.  Two independent obstacles surfaced,
-- both real: `_&_⊢a_∶_` is `Set₁` (its rules existentially quantify over
-- `Pred`, itself `Set₁`), so a raw `⊢a` term cannot sit inside `Pred`
-- (`Check/Wait.agda`'s leaf family is `Set`-valued) without reflecting it
-- through `T ⌊_⌋`/`toWitness`; and even after that fix, a leaf family built
-- from `alg?`'s OWN singleton-at-one-state answers is exactly the thing
-- `AlgNorm.agda`'s header warns does not combine into a uniform derivation.

open import Data.Bool using (Bool; true; false; T)
open import Data.Fin using (Fin)
  renaming (_≟_ to _≟Fin_; zero to fzero; suc to fsuc)
import Data.Fin.Properties as FinP
open import Data.List using (List; []; _∷_; filter)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as MemP
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
  using (_×_; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Vec
  using (Vec; []; _∷_; lookup)
  renaming (map to vmap)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (map′; _×-dec_)

open import Definitions.Behav using (BTheory; WellBehaved)
open import Definitions.Expr
open import Check.Core
import Check.Wait
import Definitions.Typing as Typing
import Definitions.Typing.Properties as Props
import Definitions.Typing.Alg
import Definitions.Typing.AlgDeclarative
import Definitions.Typing.AlgNorm

module Check.Alg (N : ℕ) where

  open Processes N using (module GraphChecker)
  open import Definitions.Graph.Core N
    renaming (_-<_>->_ to GStep)
  open import Definitions.Graph.Reachability N
    using (PathVia; path/nil; path/cons; reachVia?; ∈T?)

  module AlgCheck
    (G : Graph)
    (wb : WellBehaved (graphTheory G))
    where

    open Typing.MPST wb
    open GraphChecker G wb
      using ( messageGuarded?; matchRecv?; MatchRecv
            ; findStep; findRecv; RecvWitness
            ; na?; bisim?~ )

    open Definitions.Typing.Alg wb
      using ( Pred; Reach₀; ⌈_⌉; ⌈⌉/closed; reach₀/~; WaitV; Wait
            ; wv/leaf; wv/cycle; wv/step; wait/~; _&_⊢a_∶_
            ; a/send; a/recv; a/if; a/end; a/var; a/rec; alg/mono )

    -- `waitV/mono` (`Alg.agda`) is monotone in the VISITED set; refuting a
    -- hypothetical `sub` here needs monotonicity in the LEAF predicate
    -- instead — widening an arbitrary hypothetical leaf family to the
    -- canonical `Typ`-based one, so `¬w` (decided against the canonical
    -- one) can refute it.  Structural, no existing lemma covers this.
    waitLeaf/mono :
      ∀ {P}{𝒮 𝒮′ V : Pred}
      → (∀ {s} → 𝒮 s → 𝒮′ s)
      → ∀ {s} → WaitV P 𝒮 V s → WaitV P 𝒮′ V s
    waitLeaf/mono f (wv/leaf x)       = wv/leaf (f x)
    waitLeaf/mono f (wv/cycle a inT)  = wv/cycle a inT
    waitLeaf/mono f (wv/step na gr k) =
      wv/step na gr (λ gr′ → waitLeaf/mono f (k gr′))
    open Definitions.Typing.AlgNorm wb
      using ( Typ; typ/closed; waitFind; typing⇒alg
            ; SendL; sendL/closed; RecvL; recvL/closed; RecA; recA/closed )
    open Definitions.Typing.AlgDeclarative wb using (alg⇒typing)

    private
      variable
        γ δ : ℕ

    -- ══════════════════════════════════════════════════════════════════
    --  `¬P`-reachability, via `reachVia?` on the `P`-free restriction
    --  (lifted unchanged from the deleted `Check/Alg.agda`)
    -- ══════════════════════════════════════════════════════════════════

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
      in tr¬/step gr′ P∉α (path→tr rest)

    tr→path :
      ∀ {P a b}
      → a -[¬ P ]->* b
      → ∃[ n ] PathVia (restrict P) (λ _ → true) a b n
    tr→path ([] , tr/refl , []) = zero , path/nil
    tr→path (_ ∷ αs , tr/step gr tr , P∉α ∷ ps)
      with tr→path (αs , tr , ps)
    ... | n , rest = suc n , path/cons _ (rstep⇐ gr P∉α) rest

    reach¬P? : ∀ P a b → Dec (a -[¬ P ]->* b)
    reach¬P? P a b =
      map′ (λ { (_ , p) → path→tr p }) tr→path
        (reachVia? (restrict P) (λ _ → true) a b)

    -- `Reach₀ P 𝒜` for a decidable anchor set: one reachability query per
    -- candidate anchor.  This is `a/var`'s and `a/rec`'s leaf family.
    reach₀? :
      ∀ P (𝒜 : Pred) → (∀ a → Dec (𝒜 a)) → ∀ s → Dec (Reach₀ P 𝒜 s)
    reach₀? P 𝒜 𝒜? s =
      FinP.any? (λ a → 𝒜? a ×-dec reach¬P? P a s)

    -- ══════════════════════════════════════════════════════════════════
    --  The checker: one case per rule of `_&_⊢a_∶_`
    -- ══════════════════════════════════════════════════════════════════

    open Check.Wait N using (module WaitCheck)

    -- One offered edge's obligation.  Outside the `mutual` block so that it
    -- REDUCES where it is used — inside, its clauses are not yet available.
    EdgeOK :
      ∀ {γ δ I}
      → Vec Sort γ → Vec (State G) δ
      → Part → Part → Vec (Proc (suc γ) δ) (suc I)
      → Edge (size G) → Set
    EdgeOK {I = I} Γ Δ P Q Br (α , t) =
      ∀ {j : Fin (suc I)}{U}
      → α ≡ (Q ⟶ P # j < U >)
      → Typ (U ∷ Γ) Δ (P ◂ lookup Br j) t

    mutual

      -- `alg?` decides the judgment `⊢a` at the singleton `⌈ s ⌉` — one
      -- case per rule of `Definitions/Typing/Alg.agda`, building or
      -- refuting an actual `a/send`/`a/recv`/`a/if`/`a/end`/`a/var`/`a/rec`
      -- value.  `alg?`'s own cases never build a `⊢p` value directly, and
      -- never call `tc?` at their OWN query state — only `tc?` itself
      -- crosses to `⊢p`.
      alg? :
        ∀ {γ δ}
          (Γ : Vec Sort γ)(Δ : Vec (State G) δ)
          (P : Part)(Pr : Proc γ δ)(s : State G)
        → Dec (Γ & Δ ⊢a P ◂ Pr ∶ ⌈ s ⌉)

      -- `tc?` is the thin boundary that crosses `alg?` to `⊢p`, ONCE, via
      -- `alg⇒typing` (positive) / `typing⇒alg` (negative, contrapositive).
      -- Its own body is not structurally recursive — it only ever calls
      -- `alg?` at its OWN query state.  Agda's `mutual` needs it in this
      -- block regardless (`sendLeaf?`/`algBr` below call it, and it calls
      -- `alg?`, so the three are one recursive clique whether or not they
      -- are declared together); what changed is that its CLAUSE now sits
      -- at the end, after everything that actually recurses on the
      -- process, rather than wedged in front of `alg?`'s own cases.
      tc? :
        ∀ {γ δ}
          (Γ : Vec Sort γ)(Δ : Vec (State G) δ)
          (P : Part)(Pr : Proc γ δ)(s : State G)
        → Dec (Γ & Δ ⊢p P ◂ Pr ∶ s)

      -- a/end
      alg? Γ Δ P ∅ s with ∈T? G P s
      ... | yes inT = no λ { (a/end done) → done {s} ~refl inT }
      ... | no ¬inT =
        yes (a/end (λ {G} s~G inTG → ¬inT (∈~ (~sym s~G) inTG)))

      -- a/if
      alg? Γ Δ P (ifp E then A else B) s
        with checkExpression Γ E s/bool
      ... | no ¬etd = no λ { (a/if etd _ _) → ¬etd etd }
      ... | yes etd with alg? Γ Δ P A s | alg? Γ Δ P B s
      ...   | yes ta | yes tb = yes (a/if etd ta tb)
      ...   | no ¬ta | _      = no λ { (a/if _ ta′ _) → ¬ta ta′ }
      ...   | _      | no ¬tb = no λ { (a/if _ _ tb′) → ¬tb tb′ }

      -- a/send.  The sort is inferred ONCE, outside the set (`⊢e-unique`
      -- is what says every leaf agrees with it), and the leaf family is
      -- then a single fully-known action per state.  `SendL`/`sendL/closed`
      -- are already stated at `𝒯 = Typ`, so the `yes` branch's `sub` field
      -- is `w` itself, no rebuilding; the `no` branch refutes an ARBITRARY
      -- hypothetical `𝒯` by widening it to `Typ` via `alg⇒typing`.
      alg? Γ Δ P (Q ! i < E >∙ Pr) s with inferExpression Γ E
      ... | no ¬typed =
        no λ { (a/send etd _ _ _) → ¬typed (_ , etd) }
      ... | yes (S , etd)
        with WaitCheck.wait? G wb P (SendL P Q i S Pr)
               (sendLeaf? Γ Δ P Q i S Pr) s
      ...   | yes w =
        let _ , u′ , _ , tu′ = waitFind (Q ! i < E >∙ Pr) w
        in yes (a/send etd (typing⇒alg Pr tu′) typ/closed
                 (λ { {G} s~G → wait/~ sendL/closed s~G w }))
      ...   | no ¬w =
        no λ { (a/send {S = S₁} etd′ td tc sub) →
                 ¬w (subst (λ S₀ → Wait P (SendL P Q i S₀ Pr) s)
                      (⊢e-unique etd′ etd)
                      (waitLeaf/mono
                        (λ { (u′ , gr , tu′) → u′ , gr , alg⇒typing td tu′ })
                        (sub {s} ~refl))) }

      -- a/recv
      alg? Γ Δ P (Σ Q ？· Br) s
        with WaitCheck.wait? G wb P (RecvL Q P Br) (recvLeaf? Γ Δ P Q Br) s
      ... | yes w =
        yes (a/recv {𝒯 = λ j U t → Typ (U ∷ Γ) Δ (P ◂ lookup Br j) t}
              recvConts typ/closed recvSub)
        where
          recvConts :
            ∀ {j U t} → Typ (U ∷ Γ) Δ (P ◂ lookup Br j) t
            → (U ∷ Γ) & Δ ⊢a P ◂ lookup Br j ∶ Typ (U ∷ Γ) Δ (P ◂ lookup Br j)
          recvConts {j} tjut = typing⇒alg (lookup Br j) tjut

          recvSub : ∀ {G} → s ~ G → Wait P (RecvL Q P Br) G
          recvSub {G} s~G = wait/~ (recvL/closed {P = Q} {Q = P} {Br = Br}) s~G w
      ... | no ¬w =
        no λ { (a/recv conts tc sub) →
                 ¬w (waitLeaf/mono
                       (λ { (edge , k) →
                              edge , λ gr′ → alg⇒typing (conts (k gr′)) (k gr′) })
                       (sub {s} ~refl)) }

      -- a/var.  `Reach₀ P ⌈ lookup Δ X ⌉` is not existential — no widening
      -- needed on refutation.
      alg? Γ Δ P (v X) s
        with WaitCheck.wait? G wb P (Reach₀ P ⌈ lookup Δ X ⌉)
               (reach₀? P ⌈ lookup Δ X ⌉ (bisim?~ (lookup Δ X))) s
      ... | yes w =
        yes (a/var (λ { {G} s~G → wait/~ (reach₀/~ ⌈⌉/closed) s~G w }))
      ... | no ¬w = no λ { (a/var sub) → ¬w (sub {s} ~refl) }

      -- a/rec.  `RecA Pr` is the anchor set `Typ Γ (_ ∷ Δ) (P ◂ Pr)`
      -- pointwise — candidate membership is `tc?` at the extended `Δ`,
      -- structurally smaller on `Pr`.
      alg? Γ Δ P (rec Pr) s with messageGuarded? Pr
      ... | no ¬guarded = no λ { (a/rec mg _ _) → ¬guarded mg }
      ... | yes guarded
        with WaitCheck.wait? G wb P (Reach₀ P (RecA Pr))
               (reach₀? P (RecA Pr) (λ W → tc? Γ (W ∷ Δ) P Pr W)) s
      ...   | yes w =
        yes (a/rec guarded
              (λ aW → alg/mono (λ {G} W~G → typ/closed W~G aW)
                                (typing⇒alg Pr aW))
              (λ { {G} s~G → wait/~ (reach₀/~ recA/closed) s~G w }))
      ...   | no ¬w =
        no λ { (a/rec mg′ td sub) →
                 ¬w (waitLeaf/mono
                       (λ { (a , 𝒜a , tr) → a , alg⇒typing (td 𝒜a) ~refl , tr })
                       (sub {s} ~refl)) }

      -- `a/send`'s leaf family at one state.  At most one target, by
      -- `step-deterministic`, so a failure at the one found is a failure.
      sendLeaf? :
        ∀ {γ δ I}
          (Γ : Vec Sort γ)(Δ : Vec (State G) δ)
          (P Q : Part)(i : Fin (suc I))(S : Sort)(Pr : Proc γ δ)
          (u : State G)
        → Dec (∃[ u′ ] (u -< P ⟶ Q # i < S > >-> u′) × Typ Γ Δ (P ◂ Pr) u′)

      sendLeaf? Γ Δ P Q i S Pr u with findStep u (P ⟶ Q # i < S >)
      ... | no ¬st = no λ { (u′ , gr , _) → ¬st (u′ , gr) }
      ... | yes (u′ , gr) with tc? Γ Δ P Pr u′
      ...   | yes td = yes (u′ , gr , td)
      ...   | no ¬td =
        no λ { (u″ , gr″ , td″) →
                 ¬td (subst (Typ Γ Δ (P ◂ Pr)) (step-deterministic gr″ gr) td″) }

      -- `a/recv`'s leaf family at one state: one offered edge, and every
      -- offered edge's continuation typed.  A label the state does not offer
      -- imposes nothing — that is exactly `blocked/recv`.
      recvLeaf? :
        ∀ {γ δ I}
          (Γ : Vec Sort γ)(Δ : Vec (State G) δ)
          (P Q : Part)(Br : Vec (Proc (suc γ) δ) (suc I))
          (u : State G)
        → Dec ((Σ[ j ∈ Fin (suc I) ] ∃[ U ] ∃[ t ] (u -< Q ⟶ P # j < U > >-> t))
               × (∀ {j U t} → u -< Q ⟶ P # j < U > >-> t
                            → Typ (U ∷ Γ) Δ (P ◂ lookup Br j) t))

      recvLeaf? {I = I} Γ Δ P Q Br u
        with findRecv Q P I (edges G u)
      ... | no ¬found =
        no λ { ((j , U , t , gr) , _) →
                 ¬found (j , U , t , step⇒listed {G = G} gr) }
      ... | yes (j₀ , U₀ , t₀ , mem₀) with contsOK? Γ Δ P Q Br u
      ...   | yes conts =
        yes ((j₀ , U₀ , t₀ , listed⇒step {G = G} mem₀) , conts)
      ...   | no ¬conts = no λ { (_ , conts) → ¬conts conts }

      contsOK? :
        ∀ {γ δ I}
          (Γ : Vec Sort γ)(Δ : Vec (State G) δ)
          (P Q : Part)(Br : Vec (Proc (suc γ) δ) (suc I))
          (u : State G)
        → Dec (∀ {j U t} → u -< Q ⟶ P # j < U > >-> t
                         → Typ (U ∷ Γ) Δ (P ◂ lookup Br j) t)

      contsOK? {I = I} Γ Δ P Q Br u
        with All.all? (λ e → edgeOK? Γ Δ P Q Br e) (edges G u)
      ... | yes every =
        yes λ gr → All.lookup every (step⇒listed {G = G} gr) refl
      ... | no ¬every =
        no λ conts →
          ¬every (All.tabulate λ {e} mem eq →
                    conts (subst (λ α → u -< α >-> proj₂ e)
                            eq (listed⇒step {G = G} mem)))

      edgeOK? :
        ∀ {γ δ I}
          (Γ : Vec Sort γ)(Δ : Vec (State G) δ)
          (P Q : Part)(Br : Vec (Proc (suc γ) δ) (suc I))
          (e : Edge (size G))
        → Dec (EdgeOK Γ Δ P Q Br e)

      edgeOK? {I = I} Γ Δ P Q Br (α , t) with matchRecv? Q P I α
      ... | no ¬match =
        yes λ { {j}{U} eq → ⊥-elim (¬match (j , U , eq)) }
      ... | yes (j , U , refl) with algBr Γ Δ P Br j t
      ...   | yes td = yes λ { refl → td }
      ...   | no ¬td = no λ f → ¬td (f refl)

      -- Makes `lookup Br j` structural, as in the old, deleted `SetsAlg.agda`.
      algBr :
        ∀ {γ δ n}
          (Γ : Vec Sort γ)(Δ : Vec (State G) δ)
          (P : Part)(Br : Vec (Proc (suc γ) δ) n)(j : Fin n){U}(t : State G)
        → Dec (Typ (U ∷ Γ) Δ (P ◂ lookup Br j) t)

      algBr Γ Δ P (B ∷ Bs) fzero     {U} t = tc? (U ∷ Γ) Δ P B t
      algBr Γ Δ P (B ∷ Bs) (fsuc j)  {U} t = algBr Γ Δ P Bs j t

      tc? Γ Δ P Pr s with alg? Γ Δ P Pr s
      ... | yes d = yes (alg⇒typing d ~refl)
      ... | no ¬d =
        no λ td →
          ¬d (alg/mono (λ {G} s~G → typ/closed s~G td)
                        (typing⇒alg Pr td))

    -- ══════════════════════════════════════════════════════════════════
    --  Public entry points
    -- ══════════════════════════════════════════════════════════════════
    --
    -- `tc?` decides the DECLARATIVE judgment via `⊢a`: `alg?`
    -- builds/refutes an actual `_&_⊢a_∶_` value, and `tc?` crosses the
    -- equivalence exactly once, at the boundary — `alg⇒typing` for `yes`,
    -- `typing⇒alg` (contrapositive) for `no`.  `alg` is kept as the name
    -- the corpus already calls.

    alg :
      ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
        (P : Part) (Pr : Proc γ δ) (s : State G)
      → Dec (Γ & Δ ⊢p P ◂ Pr ∶ s)
    alg = tc?

    tcSession? : (M : Session) (s : State G) → Dec (⊢s M ∶ s)
    tcSession? M s = FinP.all? (λ P → tc? [] [] P (M [ P ]s) s)
