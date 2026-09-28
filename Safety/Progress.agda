{-# OPTIONS --guardedness #-}

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc)
open import Data.Fin
  using (Fin; zero)
  renaming (_≟_ to _≟f_; suc to fsuc)
open import Data.Vec
  using (Vec; []; _∷_; _[_]=_; lookup; tabulate)
open import Data.Vec.Properties using (lookup⇒[]=; lookup∘tabulate)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Fin.Subset using (_∈_; _∉_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; sym; trans)
open import Definitions.Typing

module Safety.Progress
  {N : ℕ}{B : BTheory N}(wb : WellBehaved B)(sync : Synchronous B) where
  private
    module M = MPST wb
  open M
  open Synchronous sync
  open import Definitions.Typing.Alg wb
    using ( a/send; a/recv; a/if; a/end; a/var; a/rec
          ; waitActive; waitStep; waitLeaf
          ; _⊢at_∶_; at/send-inv; at/recv-inv )
  open M.Subst
  open import Definitions.Typing.Substitution wb
  open import Safety.Preservation wb sync

  private
    recv≢send : ∀ {P Qs c c′} → just ((？ P) # c) ≢ just ((! Qs) # c′)
    recv≢send ()

    -- Over a finite index: either every `x` has `A x`, or some `x` gives
    -- a way out `B`.
    fin-collect :
      ∀ {n}{A : Fin n → Set}{B : Set}
      → (∀ x → A x ⊎ B) → (∀ x → A x) ⊎ B
    fin-collect {0} f = inj₁ λ ()
    fin-collect {suc n} {A} f
      with f zero | fin-collect {n} {A ∘ fsuc} (f ∘ fsuc)
    ... | inj₂ b | _       = inj₂ b
    ... | inj₁ _ | inj₂ b  = inj₂ b
    ... | inj₁ a | inj₁ as = inj₁ λ { zero → a ; (fsuc x) → as x }

  -- The judgment is syntax directed, so `MessageGuarded` narrows it to
  -- send/recv/if, and the tree walk is `waitActive`.
  guarded/active :
    ∀ {γ δ G P Pr}
      {Γ : Vec Sort γ}
      {ws : Vec Behav δ}
    → MessageGuarded Pr
    → Γ ⊢at P ◂ Pr ∶ (ws , G)
    → P ∈T G

  guarded/active {P = P} mg/send td
    with at/send-inv td
  ... | _ , _ , w , _ =
    waitActive (λ { (_ , (_ , eq , g)) → in/ev {P} g eq }) w

  guarded/active {P = P} mg/recv td =
    waitActive (λ { (_ , _ , _ , (_ , eq , g)) → in/ev {P} g eq })
      (proj₁ (at/recv-inv td))

  guarded/active (mg/if mg₁ _) (𝒮 , a/if _ ttd _ , mem) =
    guarded/active mg₁ (𝒮 , ttd , mem)

  -- `a/var` is impossible because Safety is all `δ = 0`, so `X : Fin 0`;
  -- `a/rec` unfolds the recursion, where the guarded body forces `P ∈T`.
  inactive/done :
    ∀ {G P Pr}
    → P ∉T G
    → [] ⊢at P ◂ Pr ∶ ([] , G)
    → done/proc Pr

  inactive/done P∉G td@(_ , a/send _ _ _ , _) =
    ⊥-elim (P∉G (guarded/active mg/send td))

  inactive/done P∉G td@(_ , a/recv _ _ , _) =
    ⊥-elim (P∉G (guarded/active mg/recv td))

  inactive/done P∉G (𝒮 , a/if _ ttd ftd , mem) =
    done-if
      (inactive/done P∉G (𝒮 , ttd , mem))
      (inactive/done P∉G (𝒮 , ftd , mem))

  inactive/done _ (_ , a/end _ , _) =
    done-∅

  inactive/done _ (_ , a/var {X = ()} _ , _)

  inactive/done P∉G td@(_ , a/rec guarded _ _ , _) =
    ⊥-elim
      (P∉G
        (guarded/active
          (guarded/subst-proc guarded)
          (at/rec/unfold sync td)))

  data SessionStatus
    (M : Session)
    (G : Behav)
    {I : ℕ}
    (Ps : Vec Part I)
    : Set
    where

    ss/step :
      ∀ {α G′}
      → G -< α >-> G′
      → SessionStatus M G Ps

    ss/if :
      ∀ {P E Pr Pr′}
      → [] ⊢e E ∶ s/bool
      → M [ P ]= ifp E then Pr else Pr′
      → SessionStatus M G Ps

    ss/rec :
      ∀ {P Pr}
      → M [ P ]= rec Pr
      → SessionStatus M G Ps

    ss/end :
      (∀ i → lookup Ps i ∉T G)
      → SessionStatus M G Ps

  status/cons :
    ∀ {I M G P}
      {Ps : Vec Part I}
    → P ∉T G
    → SessionStatus M G Ps
    → SessionStatus M G (P ∷ Ps)
  status/cons _ (ss/step gr) =
    ss/step gr
  status/cons _ (ss/if etd proc≡) =
    ss/if etd proc≡
  status/cons _ (ss/rec proc≡) =
    ss/rec proc≡
  status/cons P∉G (ss/end done) =
    ss/end λ
      { zero     → P∉G
      ; (fsuc i) → done i
      }

  -- The two communication rules both reduce to "the root steps": `waitStep`.
  head/status :
    ∀ {I M G P Pr}
      {Ps : Vec Part I}
    → SessionStatus M G Ps
    → M [ P ]= Pr
    → [] ⊢at P ◂ Pr ∶ ([] , G)
    → SessionStatus M G (P ∷ Ps)

  head/status _ _ td@(_ , a/send _ _ _ , _)
    with at/send-inv td
  ... | _ , _ , w , _
    with waitStep (λ { (_ , (_ , _ , g)) → _ , _ , g }) w
  ...   | _ , _ , gr = ss/step gr

  head/status _ _ td@(_ , a/recv _ _ , _)
    with waitStep (λ { (_ , _ , _ , (_ , _ , g)) → _ , _ , g })
           (proj₁ (at/recv-inv td))
  ... | _ , _ , gr = ss/step gr

  head/status _ proc≡ (_ , a/if etd _ _ , _) =
    ss/if etd proc≡

  head/status {G = G} tail _ (_ , a/end done , mem) =
    status/cons (done {[] , G} mem) tail

  head/status _ _ (_ , a/var {X = ()} _ , _)

  head/status _ proc≡ (_ , a/rec _ _ _ , _) =
    ss/rec proc≡

  session/status :
    ∀ {I M G}
    → (Ps : Vec Part I)
    → ⊢s M ∶ G
    → SessionStatus M G Ps

  session/status [] M⊢G =
    ss/end λ ()

  session/status {M = M} (P ∷ Ps) M⊢G =
    head/status
      (session/status Ps M⊢G)
      (lookup⇒[]= P M refl)
      (at/lookup M⊢G (lookup⇒[]= P M refl))

  all-parts/end :
    ∀ {G}
    → (∀ i → lookup (tabulate (λ P → P)) i ∉T G)
    → ∀ P → P ∉T G
  all-parts/end ended P P∈G =
    ended P
      (subst
        (λ Q → Q ∈T _)
        (sym (lookup∘tabulate (λ Q → Q) P))
        P∈G)

  if/progress :
    ∀ {M P E Pr Pr′}
    → [] ⊢e E ∶ s/bool
    → M [ P ]= ifp E then Pr else Pr′
    → ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′
  if/progress {P = P} etd proc≡
    with eval-bool etd
  ... | inj₁ e⇓true =
    nothing , _ , s/if/true P proc≡ e⇓true
  ... | inj₂ e⇓false =
    nothing , _ , s/if/false P proc≡ e⇓false

  -- A receiver `R` of the step `gr` is ACTIVE at `G`, so `waitLeaf` says its
  -- `Wait` is a leaf.  Either it is at the matching receive, with the
  -- step's arity, or it can take a τ step itself.
  recv-head :
    ∀ {M G G′ α P R I QPr}
      {i : Fin (suc I)}
      {S : Sort}
    → G -< α >-> G′
    → ev α R ≡ just ((？ P) # i < S >)
    → M [ R ]= QPr
    → [] ⊢at R ◂ QPr ∶ ([] , G)
    → (Σ[ Br ∈ Vec (Proc 1 0) (suc I) ] M [ R ]= Σ P ？· Br)
      ⊎ (∃[ β ] ∃[ M′ ] M [ β ]⇒ M′)

  -- `R` cannot be sending here: its event in `gr` is a receive, and the
  -- two steps would be the same communication.
  recv-head {R = R} gr eqR recv≡ td@(_ , a/send _ _ _ , _)
    with at/send-inv td
  ... | _ , _ , w , _
    with waitLeaf {R} gr (_ , eqR) w
  ...   | _ , (α″ , eq″ , g″)
    with comm-ev (recv-overlap {Q = R} gr g″ (_ , _ , eqR) (_ , eq″)) eqR
  ...     | _ , eq‴ =
    ⊥-elim (recv≢send (trans (sym eq‴) eq″))

  recv-head {P = P} {R} gr eqR recv≡ td@(_ , a/recv _ _ , _)
    with waitLeaf {R} gr (_ , eqR) (proj₁ (at/recv-inv td))
  ... | _ , _ , _ , (α‴ , eq‴ , g‴)
    with comm-ev (recv-overlap {Q = R} gr g‴ (_ , _ , eqR) (_ , eq‴)) eqR
  ...   | _ , eqP
    with trans (sym eqP) eq‴
  ...     | refl
    with step-arity-det gr g‴ eqR eq‴
  ...       | refl =
    inj₁ (_ , recv≡)

  recv-head gr eqR recv≡ (_ , a/if etd′ _ _ , _) =
    inj₂ (if/progress etd′ recv≡)

  recv-head {G = G} {R = R} gr eqR recv≡ (_ , a/end done , mem) =
    ⊥-elim (done {[] , G} mem (in/ev {R} gr eqR))

  recv-head gr eqR recv≡ (_ , a/var {X = ()} _ , _)

  recv-head {R = R} gr eqR recv≡ (_ , a/rec _ _ _ , _) =
    inj₂ (nothing , _ , s/rec R recv≡)

  -- `P`'s multicast is at the head of `P`; every receiver is at its
  -- receive (then `s/comm` fires) or some receiver has a τ step.
  receivers/progress :
    ∀ {M G G′ P Qs I}
      {i : Fin (suc I)}
      {S : Sort}
      {E : Exp 0}
      {Pr : Proc 0 0}
    → ⊢s M ∶ G
    → G -< P ⟶ Qs # i < S > >-> G′
    → P ∉ Qs
    → [] ⊢e E ∶ S
    → M [ P ]= Qs ! i < E >∙ Pr
    → ∃[ β ] ∃[ M′ ] M [ β ]⇒ M′

  receivers/progress {M} {G} {P = P} {Qs} {I} {i} {S}
    M⊢G g P∉Qs etd send≡
    with fin-collect
           {A = λ R → R ∈ Qs
                    → Σ[ Br ∈ Vec (Proc 1 0) (suc I) ] M [ R ]= Σ P ？· Br}
           each
    where
      each :
        ∀ R
        → (R ∈ Qs → Σ[ Br ∈ Vec (Proc 1 0) (suc I) ] M [ R ]= Σ P ？· Br)
          ⊎ (∃[ β ] ∃[ M′ ] M [ β ]⇒ M′)
      each R with R ∈? Qs
      ... | no R∉ = inj₁ (λ m → ⊥-elim (R∉ m))
      ... | yes m
        with recv-head {i = i} g
               (ev-recv {P} {Qs} {i < S >} {R} (λ { refl → P∉Qs m }) m)
               (lookup⇒[]= R M refl)
               (at/lookup M⊢G (lookup⇒[]= R M refl))
      ...   | inj₁ x = inj₁ (λ _ → x)
      ...   | inj₂ τ = inj₂ τ
  ... | inj₂ τ = τ
  ... | inj₁ recvs
    with eval-exp etd
  ...   | V , e⇓v =
    just (P ⟶ Qs # i < sort/value V >) , _ ,
    s/comm {Br = λ R m → proj₁ (recvs R m)}
      P send≡ e⇓v (λ R m → proj₂ (recvs R m))

  -- `P` is active at `G` (it is `gr`'s sender), so `waitLeaf` collapses the
  -- tree walk.
  sender/head-progress :
    ∀ {M G G′ α P Qs c}
      {Pr : Proc 0 0}
    → ⊢s M ∶ G
    → G -< α >-> G′
    → ev α P ≡ just ((! Qs) # c)
    → M [ P ]= Pr
    → [] ⊢at P ◂ Pr ∶ ([] , G)
    → ∃[ β ] ∃[ M′ ] M [ β ]⇒ M′

  sender/head-progress {P = P} M⊢G gr eqP send≡ td@(_ , a/send _ _ _ , _)
    with at/send-inv td
  ... | _ , etd , w , _
    with waitLeaf {P} gr (_ , eqP) w
  ...   | _ , (α′ , eq′ , g′)
    with send-action g′ eq′
  ...     | P∉Qs′ , refl =
    receivers/progress M⊢G g′ P∉Qs′ etd send≡

  -- `P` cannot be receiving: `P`'s event in `gr` is a send, and the two
  -- steps would be the same communication.
  sender/head-progress {P = P} M⊢G gr eqP send≡ td@(_ , a/recv _ _ , _)
    with waitLeaf {P} gr (_ , eqP) (proj₁ (at/recv-inv td))
  ... | _ , _ , _ , (α″ , eq″ , g″)
    with comm-ev (recv-overlap {Q = P} g″ gr (_ , _ , eq″) (_ , eqP)) eq″
  ...   | _ , eq‴ =
    ⊥-elim (recv≢send (trans (sym eq‴) eqP))

  sender/head-progress M⊢G gr eqP send≡ (_ , a/if etd _ _ , _) =
    if/progress etd send≡

  sender/head-progress {G = G} {P = P} M⊢G gr eqP send≡
    (_ , a/end done , mem) =
    ⊥-elim (done {[] , G} mem (in/ev {P} gr eqP))

  sender/head-progress M⊢G gr eqP send≡ (_ , a/var {X = ()} _ , _)

  sender/head-progress {P = P} M⊢G gr eqP send≡ (_ , a/rec _ _ _ , _) =
    nothing , _ , s/rec P send≡

  -- Every step is some `P`'s multicast (`balanced`): ask `P`.
  step/progress :
    ∀ {M G G′ α}
    → ⊢s M ∶ G
    → G -< α >-> G′
    → ∃[ β ] ∃[ M′ ] M [ β ]⇒ M′
  step/progress {M = M} M⊢G gr
    with balanced gr
  ... | P , Qs , c , _ , _ , refl =
    sender/head-progress
      M⊢G
      gr
      (ev-sender {P} {Qs} {c})
      (lookup⇒[]= P M refl)
      (at/lookup M⊢G (lookup⇒[]= P M refl))

  progress :
    ∀ {M G}
    → ⊢s M ∶ G
    → done M ⊎ ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′

  progress {M = M} M⊢G
    with session/status (tabulate (λ P → P)) M⊢G
  ... | ss/step gr =
    inj₂ (step/progress M⊢G gr)
  ... | ss/if etd proc≡ =
    inj₂ (if/progress etd proc≡)
  ... | ss/rec proc≡ =
    inj₂ (nothing , _ , s/rec _ proc≡)
  ... | ss/end ended =
    inj₁ λ P →
      inactive/done
        (all-parts/end ended P)
        (at/lookup M⊢G (lookup⇒[]= P M refl))
