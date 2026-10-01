# PLAN.md — one process, many roles

*Written 2026-09-28 on `set-typing`, after the multicast rework (`1b7f892`, `770b67f`).
Revised 2026-09-29: hidden internal communication (§5), corrected counterexample (§4.1(a)),
what `Focus` costs (§4.4), and the compatibility layer for tests (§3.3, §13).
Reviewed 2026-10-01 against `Alg.agda`, `AlgNorm.agda`, `Preservation.agda`,
`Progress.agda` and `Check/Alg.agda`, and revised the same day: internal steps are the
process's own choice (`t/hide`, D8); a process may order its sends (`FocusS`, D12);
`Internal` is by events, with `sync` on the equivalence (D10); cycle witnesses see the
assignment (D13). §16 lists what is still open. Nothing below is implemented yet.*

**Terminology.** A **role** is a name in the global specification: `Part = Fin N`. A
**process** is `Ps ◃ Pr`, code implementing a set of roles. "`X` takes part in `β`"
(`X ∈α β`) means role `X` has an event in action `β`. The word "participant" is not used.

**Ground rule.** Only three things are redesigned: the **process syntax**, minimally (an
optional acting role on sends and receives, §3.1), the **reduction semantics of sessions**
(`Definitions/Proc.agda`), and the **typing rules**, declarative (`Typing/Declarative.agda`)
and algorithmic (`Typing/Alg.agda`). The behavioural theory (`Behav.agda`: `BTheory`,
`WellBehaved`, `Synchronous`), actions (`Actions.agda`), the graph model and its decision
procedures (`Definitions/Graph/*`) do **not** change. One LTS still typechecks any number of
sessions, with any number of processes: nothing about the role assignment reaches the theory.
Everything downstream (`⊢a ⟺ ⊢p`, `Safety/`, `Check/`) is re-proved against the same axioms.
Every statement keeps its form **except preservation's**: a session step now matches a
*weak* graph step, which is some hidden internal steps followed by the action (§5.4, §9.1).

> **⚠ Soundness note — read §4.** Generalising the rules from `P : Part` to `Ps : PartSet`
> and nothing else **loses progress**: §4.1 gives two deadlocking sessions that the naive
> rules accept. Preservation and termination survive. The fix is one side condition per
> communication rule: `Focus` on `t/recv`/`a/recv`, and the weaker `FocusS` on
> `t/send`/`a/send` (§4.2). Both are trivially true for a single role, so every existing
> derivation, example and test carries over. §4.4 records exactly what they reject.

> **⚠ Proof risk — read §9.2.** Hiding internal communication (§5) needs one new lemma,
> `hidden/first`: a session step can always be matched by hidden steps followed by the
> action. It is today's `comm/ready` with the involved processes' chosen hidden steps
> taken in lockstep. The proof is written out in §9.2 but not mechanised; its termination
> is what D13 is for. Step 3 of §11 tests it before anything else is ported.

## 0. The change

A named process implements a **set** of roles: `Ps ◃ Pr` with `Ps : PartSet`. A session is
a vector of processes over a static role assignment whose sets partition `Fin N`.

**Semantics.** A multicast still happens in one step; what must be ready is every *role*,
not every *process*. A process implementing several receivers of one multicast does **one**
receive. A communication entirely inside one process is **hidden**: it has no syntax, and
the session never performs it (§5).

**Syntax.** A send or receive may name the role of the process that performs it:
`A ▹ Qs ! i < E >∙ Pr`, `R ▹Σ Q ？· Br`. The unannotated forms `Qs ! i < E >∙ Pr` and
`Σ Q ？· Br` remain, and mean "the process's only role". So an unannotated action is legal
exactly in a single-role process, and every existing process is unchanged.

**Typing.** The communication rules are today's, at the acting role, plus the `FocusS` or
`Focus` side condition. Everything else replaces `P` by `Ps`. A process skips steps it
takes no part in, as today; a step that happens entirely among its own roles is **its own
choice**: the derivation takes it (`t/hide`), and the code says nothing.

Graph: one step `R ⟶ {P,Q} # 0 < nat >`, then `end`.

```
{R} ◃ {P,Q} ! 0 < 3 >∙ ∅   ∥   {P,Q} ◃ P ▹Σ R ？· (∅ ∷ [])                              ⇒   ∅ ∥ ∅
{R} ◃ {P,Q} ! 0 < 3 >∙ ∅   ∥   {P} ◃ Σ R ？· (∅ ∷ [])   ∥   {Q} ◃ Σ R ？· (∅ ∷ [])      ⇒   ∅ ∥ ∅ ∥ ∅
```

Role assignments `[{R}, {P,Q}]` and `[{R}, {P}, {Q}]`; both sessions take the one step. In
the first, the receive is annotated with `P`; `Q ▹Σ R ？·` would do equally well. The
annotation says which role advances; every role of the process that the multicast targets
advances with it.

Graph: `P ⟶ {Q} # 0 < nat >`, then `Q ⟶ {R} # 0 < nat >`, then `end`.

```
{P,Q} ◃ Q ▹ {R} ! 0 < 3 >∙ ∅   ∥   {R} ◃ Σ Q ？· (∅ ∷ [])                               ⇒   ∅ ∥ ∅
```

`P ⟶ {Q}` is internal to `{P,Q}`: the derivation steps over it (`t/hide`), and the code is
only the send to `R`. The one session step matches the graph run `P⟶Q · Q⟶R`.

Graph: `P ⟶ {Q} # i < unit >` then `Q ⟶ {R} # i < unit >`, for `i ∈ {0,1}`: an internal
choice that `R` sees.

```
{P,Q} ◃ ifp E then Q ▹ {R} ! 0 < … >∙ ∅ else Q ▹ {R} ! 1 < … >∙ ∅   ∥   {R} ◃ Σ Q ？· (∅ ∷ ∅ ∷ [])
```

One message decides the branch. `t/if` types the `then` branch by `t/hide` of `P⟶Q#0`
then `t/send`, and the `else` branch likewise with `#1`. `{R}` is as it would be with
three processes.

## 1. Decisions

| # | decision | why |
|---|---|---|
| D1 | Sends and receives carry `Maybe Part`: the acting role, or `nothing` for "the only role". The existing syntax is kept as **pattern synonyms** for `nothing` (§3.1). | Tests and examples construct processes only. Proofs match on the real constructors; that change is mechanical. Checked in a scratch file: both surface forms, `{I}` implicit, fixity `infixr 8`, and matching on constructors and on synonyms. |
| D2 | The acting role is resolved by `Acts Ps r P`: `r ≡ just P × P ∈ Ps`, or `r ≡ nothing × Ps ≡ ⁅ P ⁆`. The rules and `s/comm` both use it. | `Acts` is functional (`acts-unique`), so the role the semantics fires and the role the typing checked are the same, with no argument. |
| D3 | The communication rules keep today's step premise **at the acting role**: `G -<[ P ↦ e ]>-> G′`, from `Behav.agda`, unchanged. | Send typing does not change; receive typing is today's, at one role. No new step relation. |
| D4 | One new premise per communication rule, **`FocusS Ps P G`** on sends and **`Focus Ps R G`** on receives (§4.2), plus two syntactic ones: a send reaches some role outside `Ps` (`Outward`), and a receive's sender is not in `Ps`. | §4. The two conditions are the only premises that mention the theory. |
| D5 | The set-level vocabulary (`Internal`, `Ext`, `_∈αs_`, `_idle-in_`, `_∈T*_`, `_-[¬*_]->*_`, `Focus`, `FocusS`, `Acts`, `Outward`) lives in a new `Typing/Roles.agda`, built from the unchanged role-level notions. So do `Hidden`, `_∈T⁺_` and the weak step `_=<_>=>_`, which depend on the assignment. | Ground rule. |
| D6 | Sessions: `Ρ : Roles k = Vec PartSet k`, `Session = Vec (Proc 0 0) k` indexed by process, `Partition Ρ` (an `owner` with two laws). **`⊢s` includes `Partition Ρ`** as a conjunct. | `Ρ` is static. Keeping the partition inside `⊢s` keeps every `Safety/` statement of the form `⊢s M ∶ G → …`. Preservation needs it: with two owners of `P`, the second is "uninvolved" in `P`'s step but cannot `t/unskip` across it. |
| D7 | The checker is keyed by role set (`Env Ps`, `Probing Ps`). It decides `Acts`, `Focus`, the syntactic premises, and `Partition Ρ`. | It decides the new rules and nothing else. `WBGraph`, `buildG` and `WBNet` are unchanged. |
| D8 | **Internal communication is hidden, and is the process's choice** (§5). A step all of whose roles belong to one process has no syntax and is never performed by the session. The process's derivation steps over it with **`t/hide`** (existential: the derivation picks the branch). `skip/step` is **strict**: it applies only at states with no internal step for `Ps`, so a pending internal step is always hidden before the process waits. Runs (`t/unskip`, `Focus`, `Wait`) are over *idle* steps only. Preservation matches a session step with a weak step `G =< α >=> G′`. | A process `{P,Q}` implementing `P ⟶ Q . Q ⟶ R` writes only its send to `R`; against an internal choice `P ⟶ Q # i . Q ⟶ R # i` it writes `ifp` over two sends, one per branch (§0). Universal quantification over internal branches (the 2026-09-29 design) rejects that. Strictness is what keeps the existential sound: a process may not wait with an internal step pending (§5.2). |
| D9 | **A compatibility layer** keeps the single-role API (§3.3): `_◂_` becomes a function `P ◂ Pr = ⁅ P ⁆ ◃ Pr`, the top-level `Session`/`⊢p`/`⊢s_∶_` are the `singletons` instance, and `tc?`/`typecheck`/`typecheckSession` keep their types. **Nothing is duplicated:** one definition each, no second constructor, no second proof. Goals display `⁅ P ⁆ ◃ Pr`; that is fine. | Examples and API-level tests compile unedited. Tests that build derivations or call checker internals by hand get mechanical `P ↦ ⁅ P ⁆` edits (§13). |
| D10 | **`Internal` is by events**: a step is internal to `Ps` when every role that takes part in it is in `Ps`. The `⊢a ⟺ ⊢p` modules (`AlgNorm`, `AlgEquiv`, `AlgDeclarative`) take `sync`, which today only `sendAt` has. A comment at `Internal` records this and the relaxation for non-synchronous theories (§2). | The natural definition. The equivalence needs the send and receive leaf steps to be `Ext` (`waitLeaf`), and with events that is `balanced`. Every theory the checker builds is synchronous, so nothing user-visible changes. The relaxation: define `Internal` by the roles an action *mentions* (those with an event, plus the `Qs`/`Q` named inside events); then `Outward`/`Q ∉ Ps` give `Ext` with no `sync`. |
| D11 | **Progress chases hidden steps through derivations**: it follows a non-done process's `t/hide`s, and at a strict wait takes a non-hidden step if one exists, else the hide of whichever process owns a hidden one (§9.3). | Hidden steps are chosen by derivations, so only the owner's derivation can move the graph along one. |
| D12 | **Sends may be ordered before sends.** `t/send`'s condition is `FocusS`: every external step reachable while idle involves the acting role, *or* involves roles of `Ps` only as senders. `t/recv` keeps `Focus`. | Send-before-send is always safe (§4.4): a receiver under `Focus` is at the receive of any enabled step targeting it, so a process holding one send behind another only waits for ready receivers. Progress's two uses of the send condition survive (§4.2). |
| D13 | **Cycle witnesses see the assignment.** `skip/cycle`/`wv/cycle` require `Ps ∈T⁺ G`: a run of steps idle for `Ps` **and hidden for no process**, then a step `Ps` takes part in. So `⊢p` is inside `Sessions Ρ`. | A per-process witness may run through *another* process's internal choice that that process never takes, and then the deferral is unjustified: §9.2 gives a typed session with no matching weak step. With `Hidden` in the witness, the lockstep of §9.2 terminates. Under `singletons` nothing is hidden, so the witness is today's `P ∈T G`. |

**Names.** The new operators are `_◃_`, `_∈αs_`/`_∉αs_`, `_idle-in_`, `_∈T*_`, `_∈T⁺_`,
`_-[¬*_]->*_`, `_==>*_` and `_=<_>=>_`. The starred ones are starred because the role-level
`_∈T_`/`_-[¬_]->*_` stay in scope through `MPST`. The new rules are `t/hide`, `skip/hide`
and `wv/hide`. The new identifiers are `Acts`, `Focus`, `FocusS`, `Internal`, `Ext`,
`Outward`, `Hidden`, `Roles`, `Partition`, `owner`, `Meets`, `singletons`, and the lemmas
`send/ext`, `recv/ext`, `ext-internal/⋄`, `disjoint/⋄`, `hide/advance`, `pull/β` and
`hidden/first`. The syntax adds `send`, `recv`, `_▹_!_<_>∙_` and `_▹Σ_？·_`; `▹` and `◃` are
used nowhere today. Throughout, `Ps` is a process's role set, `Qs` a multicast's receiver
set, `Ρ` the assignment, `r` an annotation, and `j`/`j₀` process indices.

## 2. `Definitions/Typing/Roles.agda` (new)

```agda
module Definitions.Typing.Roles {N}{B : BTheory N}(wb : WellBehaved B) where
  open MPST wb

  infix 4 _∈αs_ _∉αs_
  _∈αs_ : PartSet → Action → Set ; Ps ∈αs α = ∃[ R ] R ∈ Ps × R ∈α α
  _∉αs_ : PartSet → Action → Set ; Ps ∉αs α = ∀ R → R ∈ Ps → R ∉α α
  ∉αs→¬∈αs ¬∈αs→∉αs _∈αs?_ _∉αs?_ ∉αs→∉α ∈α→∈αs       -- pin `{Ps}{α}` at call sites

  -- Every role that takes part in `β` is one of `Ps`: a communication inside the
  -- process (D10).
  --
  -- SYNCHRONOUS THEORIES ONLY.  `Ext` for a rule's own step is derived from the
  -- rule's syntactic premise (`Outward Ps Qs`, `Q ∉ Ps`) through `balanced`: the
  -- receivers named in `P`'s send event take part in the step.  In a theory where
  -- actions are not balanced multicasts, this definition makes `send/ext` and
  -- `recv/ext` unprovable, and `AlgNorm`/`AlgEquiv`/`AlgDeclarative` would lose
  -- their `sync` discharge.  The relaxation is to define `Internal` by the roles
  -- an action MENTIONS: those with an event, plus the `Qs` of every send event and
  -- the `Q` of every receive event.  Under `balanced` the two definitions agree.
  Internal : PartSet → Action → Set ; Internal Ps β = ∀ X → X ∈α β → X ∈ Ps
  -- The complement: `Ps` takes part, and `β` reaches outside `Ps`.
  Ext      : PartSet → Action → Set ; Ext Ps β = Ps ∈αs β × ¬ Internal Ps β
  internal? ext?                                                -- decidable: `N` is finite
  -- `Ext` from the rules' syntactic premises, under `sync`.
  send/ext : Synchronous B → G -< β >-> G′ → P ∈ Ps → Outward Ps Qs → ev β P ≡ just ((! Qs) # c) → Ext Ps β
  recv/ext : Synchronous B → G -< β >-> G′ → R ∈ Ps → Q ∉ Ps        → ev β R ≡ just ((？ Q) # c) → Ext Ps β

  -- `Ps idle-in G`: every step at `G` is idle for `Ps`.  STRICT: an internal step at
  -- `G` makes this false, so a process with a pending internal step cannot wait (D8).
  _idle-in_   : PartSet → Behav → Set ; Ps idle-in G = ∀ {α G′} → G -< α >-> G′ → Ps ∉αs α
  -- `t/end`'s witness: no step `Ps` takes part in externally is reachable by ANY run.
  _∈T*_       : PartSet → Behav → Set
  Ps ∈T* G = ∃[ αs ] ∃[ G′ ] (G -[ αs ]-> G′) × Any (Ext Ps) αs
  -- `t/unskip`'s runs: idle steps only.  The environment never performs a process's
  -- internal steps, so a derivation that chose one branch is never moved along another.
  _-[¬*_]->*_ : Behav → PartSet → Behav → Set
  G -[¬* Ps ]->* G′ = ∃[ αs ] (G -[ αs ]-> G′) × All (Ps ∉αs_) αs

  -- The acting role of an annotation.  DEFINED in `Proc.agda` (the semantics uses it),
  -- re-exported here with its lemmas; shown here for reference.
  Acts : PartSet → Maybe Part → Part → Set
  Acts Ps (just r) P = r ≡ P × P ∈ Ps
  Acts Ps nothing  P = Ps ≡ ⁅ P ⁆
  acts-unique : Acts Ps r P → Acts Ps r P′ → P ≡ P′
  acts-∈      : Acts Ps r P → P ∈ Ps
  acts?       : ∀ Ps r → Dec (∃[ P ] Acts Ps r P)     -- `Subset` equality is `Vec Bool` equality

  -- A send reaches some role outside the process (else it would be internal, §5).
  Outward : PartSet → PartSet → Set ; Outward Ps Qs = ∃[ R ] R ∈ Qs × R ∉ Ps ; outward?

  -- Wherever the process can be while idle, every external step it takes part in
  -- involves `P`.  The receive condition.
  Focus : PartSet → Part → Behav → Set
  Focus Ps P G = ∀ {G′ β G″} → G -[¬* Ps ]->* G′ → G′ -< β >-> G″ → Ext Ps β → P ∈α β

  -- … or involves roles of `Ps` only as senders.  The send condition (D12).
  FocusS : PartSet → Part → Behav → Set
  FocusS Ps P G = ∀ {G′ β G″} → G -[¬* Ps ]->* G′ → G′ -< β >-> G″ → Ext Ps β
                → P ∈α β ⊎ (∀ R → R ∈ Ps → ¬ Recv β R)

  -- The assignment-level notions.  `⊢p` lives inside this module too (D13).
  module Sessions {k} (Ρ : Roles k) where
    Hidden : Action → Set ; Hidden β = ∃[ j ] Internal (lookup Ρ j) β ; hidden?

    -- The cycle witness (D13): the environment alone can make the process act.  A
    -- run of steps idle for `Ps` and hidden for nobody, then a step `Ps` takes part
    -- in.  `Ps ∈T⁺ G → Ps ∈T* G`; the converse fails exactly when every way to
    -- activity passes through somebody's internal step.
    _∈T⁺_ : PartSet → Behav → Set
    Ps ∈T⁺ G = ∃[ αs ] ∃[ G′ ] (G -[ αs ]-> G′) × All (λ β → Ps ∉αs β × ¬ Hidden β) αs
             × ∃[ γ ] ∃[ G″ ] G′ -< γ >-> G″ × Ext Ps γ

    -- A run of hidden steps, and a hidden run followed by one step (the weak step).
    infix 4 _==>*_ _=<_>=>_
    data _==>*_ : Behav → Behav → Set where
      h/refl : G ==>* G
      h/step : G -< β >-> G′ → Hidden β → G′ ==>* G″  → G ==>* G″
    data _=<_>=>_ : Behav → Action → Behav → Set where
      w/step : G -< α >-> G′                              → G =< α >=> G′
      w/hide : G -< β >-> G′ → Hidden β → G′ =< α >=> G″  → G =< α >=> G″
```

Lemmas. The idle-run lemmas are proved by picking the witness role, applying the
role-level lemma, and mapping `All`. The ones about internal steps use the diamond:

```agda
in/αs* in/later* skip/refl* tr¬/step* skip/one* skip/cat* ∈~* idle/bisim skip/bisim*
idle/⁅⁆  : P not-active-in G → ⁅ P ⁆ idle-in G                    -- for §13's tests
ext/comm : comm α ≡ comm β → Ext Ps α → Ext Ps β                    -- `comm-∈α` both ways
-- An external step of `Ps` and an internal step of `Ps` at one state are independent.
ext-internal/⋄ : G -< α >-> Gα → G -< β >-> Gβ → Ext Ps α → Internal Ps β → α ⋄ β
-- Steps with no role in common are independent (`ι` has a role: `balanced`).
disjoint/⋄   : (∀ X → X ∈α ι → X ∉α β) → X₀ ∈α ι → ι ⋄ β
-- An internal step of `Ps` survives an idle step of `Ps`, and vice versa.
hide/advance : G -< ι >-> Gι → Internal Ps ι → G -< β >-> Gβ → Ps ∉αs β
             → ∃[ G′ ] Gι -< β >-> G′ × Gβ -< ι >-> G′
-- Today's, at the witness role; the output run has the input run's labels.
skip/advance*  : G -[¬* Ps ]->* G′ → G -< α >-> Gα → Ps ∈αs α → ∃[ G′α ] G′ -< α >-> G′α × Gα -[¬* Ps ]->* G′α
branch/before* recv/same-comm*
focus/cat  focus/~  focus/⁅⁆                                      -- stability under `t/unskip`, `~`; free for one role
focusS/cat focusS/~ focusS/⁅⁆

-- in `Sessions Ρ`
inT⁺/singletons : Synchronous B → ⁅ P ⁆ ∈T⁺ G ⇔ P ∈T G
weak/step  : G -< α >-> G′ → G =< α >=> G′
hidden/weak : G ==>* G₁ → G₁ -< α >-> G′ → G =< α >=> G′
weak⇒run   : G =< α >=> G′ → ∃[ ιs ] G -[ ιs ++ α ∷ [] ]-> G′ × All Hidden ιs
weak/singletons : Synchronous B → G =< α >=> G′ ⇔ G -< α >-> G′  -- under `singletons`
```

`skip/advance*` and `branch/before*` are `-aux` recursions on the run, exactly like
`Behav.agda`'s: the run is a curried argument and is never repacked. They are re-stated
rather than derived from `Behav.agda`'s, because those pack the output run's labels
existentially, and the set-level versions need the output labels to be the input's (so
that idle for `Ps` is preserved). The bodies are the same ten lines at the witness role.

`weak/singletons` and `inT⁺/singletons` hold because `Hidden` is empty under
`singletons`: `Internal ⁅ P ⁆ β` needs every role of `β` to be `P`, and `balanced` gives
`β` a nonempty receiver set without `P`. These are the places the conservativity
argument needs `Synchronous`.

## 3. `Definitions/Proc.agda` — syntax and reduction semantics

### 3.1 Syntax

```agda
data Proc (γ δ : ℕ) : Set where
  send : Maybe Part → PartSet → {I : ℕ} → Fin (suc I) → Exp γ → Proc γ δ → Proc γ δ
  recv : Maybe Part → Part → {I : ℕ} → Vec (Proc (suc γ) δ) (suc I) → Proc γ δ
  ifp_then_else_ : Exp γ → Proc γ δ → Proc γ δ → Proc γ δ
  rec : Proc γ (suc δ) → Proc γ δ
  v   : Fin δ → Proc γ δ
  ∅   : Proc γ δ

pattern _!_<_>∙_     Qs i E Pr = send nothing  Qs i E Pr      -- today's syntax
pattern _▹_!_<_>∙_ P Qs i E Pr = send (just P) Qs i E Pr      -- `A ▹ ⁅ B ⁆ ! i < E >∙ Pr`
pattern Σ_？·_       Q Br      = recv nothing  Q Br
pattern _▹Σ_？·_   R Q Br      = recv (just R) Q Br           -- `D ▹Σ C ？· Br`
infixr 8 _!_<_>∙_ _▹_!_<_>∙_ Σ_？·_ _▹Σ_？·_

data NProc (γ δ : ℕ) : Set where
  _◃_ : PartSet → Proc γ δ → NProc γ δ                        -- was `_◂_ : Part → …`

_◂_ : Part → Proc γ δ → NProc γ δ                             -- compatibility, §3.3
P ◂ Pr = ⁅ P ⁆ ◃ Pr
```

Every function on `Proc` matches `send r Qs i E Pr` and `recv r Q Br`. This covers the
`Subst` functions, `MessageGuarded` (`mg/send`/`mg/recv`), `τ-depth/proc`, `guarded?` and
`probe`. A clause written with a pattern synonym covers `nothing` only, and coverage would
fail. `unfold/proc` and `done/proc` are otherwise unchanged.

There is no syntax for internal communication. A send's `Qs` may contain roles of the
process itself (a partly internal multicast `P ⟶ {Q,R}` with `P,Q ∈ Ps`). Those roles
advance with the send, and nothing is bound for them: the value is `E`, already in scope.

### 3.2 Role assignments and sessions

```agda
Roles : ℕ → Set ; Roles k = Vec PartSet k

record Partition {k} (Ρ : Roles k) : Set where
  field owner   : Part → Fin k
        owner-∈ : ∀ R → R ∈ lookup Ρ (owner R)
        ∈-owner : ∀ {R j} → R ∈ lookup Ρ j → j ≡ owner R
-- derived: owner-unique : R ∈ lookup Ρ j → R ∈ lookup Ρ j′ → j ≡ j′

Meets : PartSet → PartSet → Set ; Meets Ps Qs = ∃[ R ] R ∈ Ps × R ∈ Qs ; meets?
singletons : Roles N ; singletons = tabulate ⁅_⁆ ; partition/singletons

module Sessions {k} (Ρ : Roles k) where
  Session : Set ; Session = Vec (Proc 0 0) k

  -- sender → `Pr`; every OTHER `j` meeting `Qs` → `F j`; the rest unchanged.
  -- `j ≟ j₀` is tested first.  `F` needs no membership proof: `∈-irrelevant` goes.
  _[_↦_∣_↦_] : Session → Fin k → Proc 0 0 → PartSet → (Fin k → Proc 0 0) → Session
  upd-sender upd-recv upd-other

  data _[_]⇒_ (M : Session) : Maybe Action → Session → Set where
    s/comm :
      ∀ {P Qs I}{i : Fin (suc I)}{E V Pr r₀}
        {rs : Fin k → Maybe Part}{Br : Fin k → Vec (Proc 1 0) (suc I)}
      → (j₀ : Fin k)
      → M [ j₀ ]= send r₀ Qs i E Pr
      → Acts (lookup Ρ j₀) r₀ P                              -- the sending role
      → E ⇓ V
      → (recvs : ∀ j → j ≢ j₀ → Meets (lookup Ρ j) Qs
               → M [ j ]= recv (rs j) P (Br j)
               × ∃[ R ] Acts (lookup Ρ j) (rs j) R × R ∈ Qs)  -- listening on a targeted role
      → M [ just (P ⟶ Qs # i < sort/value V >) ]⇒
          M [ j₀ ↦ Pr ∣ Qs ↦ (λ j → Subst.[ val V / zero ]e lookup (Br j) i) ]
    s/if/true s/if/false s/rec                                -- indexed by `j : Fin k`
  _[_]⇒+_ _τ⇒_ _⇒∞ _⇏∞ ; done M = ∀ j → done/proc (lookup M j) ; finished
```

A process other than the sender that meets `Qs` receives **once**, as the role its
receive names, and that role must be one of the targeted ones. Every role of that process
in `Qs` advances with it. The sender's own roles in `Qs`, if any, advance with the send.

`Acts`, `Meets` and the session layer need `Data.Fin.Subset`; `Proc.agda` imports it
already. `Acts` is defined in `Proc.agda` (next to `Meets`) and re-exported by
`Typing/Roles.agda`, so the semantics does not import the typing layer.

### 3.3 Compatibility layer

- `_◂_` is the function above. It is used only to *build* terms and types; nothing
  matches on it.
- `Proc.agda` ends with `open Sessions singletons public`, so `Session`, `_[_]⇒_`, `done`,
  … at top level are today's (indexed by `Fin N`, one role per process). Files that need a
  general `Ρ` open `Sessions Ρ` and hide the top-level names.
- `MPST` does the same for `_&_⊢p_∶_`, `_&_⊢skip_∶_` and `⊢s_∶_`, which live in its
  `Sessions Ρ` (D13). `Alg`, `AlgNorm`, `AlgEquiv`, `AlgDeclarative`, `Properties` and
  `Substitution` take `Ρ` as a module parameter after `wb`.
- `tc?`, `typecheck` and `typecheckSession` keep their types (§10). The general versions are
  `tcAs?`, `typecheckAs` and `typecheckSessionAs`.

## 4. The side condition

### 4.1 Two deadlocks under the naive rules

**The naive rules.** These are §6.1's `t/send`/`t/recv` *without* `Focus`. The semantics is
§3's, and `⊢s M ∶ G = Partition Ρ × ∀ j → …`. Both graphs below are finite, have no internal
steps under their assignment, and every terminal state is the unique `ended`; no two states
are bisimilar. `Tests/MultiRole.agda` runs both graphs through
`wellBehaved?`/`synchronous?`; the checks by hand are below.

**About `_⋄_`.** Independence compares only *receivers*. So one sender's steps to
*different* receiver sets out of one state are independent, and `step-diamond` makes them
commute: that is concurrency, not choice. A choice is a choice of labels to one receiver
set, and roles left out are told later by their own labelled message (as `S` in
`Rec2Buy`). Both graphs below respect this.

#### (a) An orphan message

Roles `Q R R″ Z`, and assignment `Ρ = [ {Q} , {R,R″} , {Z} ]`. Every label is `0`.

```
u  --Q ⟶ {Z}  # 0<unit>-->  v        v  --Q ⟶ {R}  # 0<nat>-->   x
u  --Q ⟶ {R}  # 0<nat>-->   w₁       v  --Q ⟶ {R″} # 0<bool>-->  y
w₁ --Q ⟶ {Z}  # 0<unit>-->  x        x  --Q ⟶ {R″} # 0<bool>-->  ended
                                     y  --Q ⟶ {R}  # 0<nat>-->   ended
```

`Q` sends once to each of `Z`, `R` and `R″`, in any order that puts `Z` before `R″`. There
is no choice anywhere: all three sends happen.

**Well-behaved and synchronous.**

- `recv-overlap`: every step has a single receiver, which takes part in no other step out
  of the same state. The receivers are `Z` and `R` at `u`, `R` and `R″` at `v`, and one
  each elsewhere.
- `step-deterministic`, `step-sort-det`, `step-arity-det`: every state's actions are
  pairwise distinct, and each receiver has one label at one sort per state.
- `step-diamond`: `Q⟶Z ⋄ Q⟶R` at `u` closes at `x` (`u → v → x`, `u → w₁ → x`), and
  `Q⟶R ⋄ Q⟶R″` at `v` closes at `ended` (`v → x → ended`, `v → y → ended`). Every other
  state has one step.
- `no-new-branch/step`: for each state with two steps `β`, `γ`, the step with `γ`'s comm
  after `β` is `γ` itself, already available before `β`. That covers `Q⟶R` after `Q⟶Z`,
  `Q⟶Z` after `Q⟶R`, and the pair `Q⟶R`, `Q⟶R″` at `v` in both directions.
- `no-new-comm/step`: `Q` takes part in every step, so the premise never holds.
- `balanced`: each step is one multicast with `Nonempty Qs` and `Q ∉ Qs`.

**Processes.**

```
Y = {Q}    ◃ {Z} ! 0 < val v/unit >∙ ({R″} ! 0 < val (v/bool true) >∙ ({R} ! 0 < val (v/nat 0) >∙ ∅))
X = {R,R″} ◃ R ▹Σ Q ？· ((R″ ▹Σ Q ？· (∅ ∷ [])) ∷ [])
W = {Z}    ◃ Σ Q ？· (∅ ∷ [])
```

**Naive derivations at `u`.**

- `Y`: `t/send` for `Q⟶Z` at `u`, then `t/send` for `Q⟶R″` at `v`, `t/send` for `Q⟶R` at
  `y`, and `t/end` at `ended`.
- `X`: `Acts {R,R″} (just R) R`, and `Q ∉ {R,R″}`. It is typed by `t/recv` for `Q⟶R` at
  `u`. `conts` covers the one receive of `R` from `Q` at `u`, whose target is `w₁`. At `w₁`,
  `{R,R″}` is idle (`Q⟶Z`), so the continuation is typed by `t/skip` (`skip/step` to `x`),
  then `t/recv` as `R″` for `Q⟶R″` at `x`, then `t/end` at `ended`.
- `W`: `t/recv` for `Q⟶Z` at `u`, then `t/end` at `v`, since `Z` appears nowhere after `u`.

So `⊢s [ Y , X , W ] ∶ u` holds.

**Reduction.**

1. `s/comm` for `Q⟶Z` gives `M₁ = [ {R″} ! … , X , ∅ ]` at `v`. `X`'s derivation is
   `t/unskip` of the one at `u`, across the idle step `Q⟶Z`.
2. At `M₁`, `Y` sends to `{R″}`. The process meeting `{R″}` is `X`, but it listens as `R`,
   and `R ∉ {R″}`, so `recvs` fails.
3. No other step exists, and `M₁` is not `done`.

`progress` is false at `M₁`. The graph at `v` offers `Q⟶R` and `Q⟶R″` in either order;
`Y` fixed `R″` first and `X` fixed `R` first.

**Where the proof breaks.** In `Progress.receivers/progress`, the receiver process `X` of
`Q⟶R″` is active at `v` through `R″`. Its head acts as `R`. Today's `recv-head` concludes
by `recv-overlap` *at the head's role*, and `R` takes no part in `Q⟶R″`. The two steps
involve one process through two roles, and no axiom relates them.

**Annotating differently does not help.** `R″ ▹Σ Q ？·` does not type at `u`: nothing is
received by `R″` at `u`. And `t/skip` is unavailable, because `X` is active at `u`.

**Contrast with a single role.** With `{R}` and `{R″}` as separate processes, each is at
its own receive at `v`, and `Y` finds a taker in either order.

#### (b) A wait cycle

Roles `A B C D`, and assignment `Ρ = [ {A,D} , {B,C} ]`.

```
G₀ --A ⟶ {B} # 0<unit>--> G₁       G₁ --C ⟶ {D} # 0<unit>--> ended
G₀ --C ⟶ {D} # 0<unit>--> G₂       G₂ --A ⟶ {B} # 0<unit>--> ended
```

The graph is well-behaved and synchronous. `A⟶B ⋄ C⟶D` and the square commutes. The
receivers `B` and `D` take part in no other step, and there is one label per receiver per
state. `no-new-comm/step` holds (each step is available at `G₀`), there is no new branch,
and `G₁ ≁ G₂`.

```
X = {A,D} ◃ A ▹ {B} ! 0 < val v/unit >∙ D ▹Σ C ？· (∅ ∷ [])
Y = {B,C} ◃ C ▹ {D} ! 0 < val v/unit >∙ B ▹Σ A ？· (∅ ∷ [])
```

**Naive derivations.** `X` types by `t/send` for `A⟶B` at `G₀`, then `t/recv` for `C⟶D` at
role `D` at `G₁`, then `t/end`. `Y` types symmetrically through `G₂`. So
`⊢s [ X , Y ] ∶ G₀` holds.

**Stuck.** Both heads are sends. For `A⟶B`, the process meeting `{B}` is `Y`, and it is at a
send. For `C⟶D`, the process meeting `{D}` is `X`, also at a send. No `if` or `rec` is at
the head, so `progress` is false.

**Where the proof breaks.** This is `recv-head`'s send case. `Y` is active at `G₀` through
`B`, and its head sends as `C`. Today the case is refuted by `recv-overlap` at the
receiver's role against its own head step. Here `B` takes no part in `C⟶D`, and the two
steps are independent, which is exactly what `step-diamond` is for.

**In general.** Both (a) and (b) are one pattern: the graph leaves two steps unordered, and
two processes each fix an order on them, incompatibly. With one role, any two steps
involving that role at one state are related by `recv-overlap`, so no such pair exists.

### 4.2 `Focus`

```agda
Focus Ps P G = ∀ {G′ β G″} → G -[¬* Ps ]->* G′ → G′ -< β >-> G″ → Ext Ps β → P ∈α β
```

The condition reads: wherever the process can be while idle, every external step it takes
part in involves the acting role. It is `t/recv`'s premise, at the rule's own state; the
send rule has the weaker `FocusS` below. It quantifies over idle runs because `t/unskip`
moves derivations forward (`focus/cat`). Internal steps are excluded: they make no one wait
(§5.5).

**It rejects both deadlocks.**

- In (a), the run `u --Q⟶Z--> v` is idle for `{R,R″}`, and at `v` the step `Q⟶R″` involves
  `R″` but not `R`.
- In (b), `C⟶D` at `G₀` involves `D` but not `A`, and `A⟶B` involves `B` but not `C`.

**It suffices for progress.** Let `j` be a process that some enabled external step `α`
involves, and let its head act as `r` with `Focus`. Then `r ∈α α`, and `recv-overlap` at `r`
does the rest, as today:

- If `j` sends as `r` and `r` receives in `α`, the two steps have one `comm`, which is
  absurd.
- If `j` receives as `r` from `Q″`, the two steps have one `comm`. So `Q″` is `α`'s sender,
  and `step-arity-det` at `r` fixes the arity.

**For a single role it is free.** With `Ps = ⁅ P ⁆`, `Ext Ps β` already says `P ∈α β`
(`focus/⁅⁆`).

**`FocusS`, the send condition (D12).**

```agda
FocusS Ps P G = ∀ {G′ β G″} → G -[¬* Ps ]->* G′ → G′ -< β >-> G″ → Ext Ps β
              → P ∈α β ⊎ (∀ R → R ∈ Ps → ¬ Recv β R)
```

Every external step reachable while idle involves `P`, or involves roles of `Ps` only as
senders. It is `t/send`'s premise; `t/recv` keeps `Focus`. It accepts a process that
orders two of its own concurrent sends, and still rejects (b): `X`'s head sends as `A`, and
`C⟶D` at `G₀` has `D ∈ Ps` as a receiver.

It suffices for progress because the send condition is used in exactly two places, and
neither needs more:

- `sender/head-progress`, send case: it never used `Focus`. `waitLeaf` needs only `Ext`,
  and the leaf's own step drives `receivers/progress`.
- `recv-head`, send case: process `j` takes part in the enabled `α′` through a receiver
  `R_j ∈ Qs`, and its head sends as `r` with `FocusS` at the leaf. `α′` is `Ext` for `j`
  with the empty idle run, so either `r ∈α α′` — then `r` receives in `α′` and sends in
  the head, and `recv-overlap` at `r` is absurd — or no role of `Ps_j` receives in `α′`,
  which `R_j` does. Absurd either way, as today.

### 4.3 Where each premise is used

| premise | used by |
|---|---|
| `Acts` | everywhere a role is needed. `acts-unique` identifies the semantics' role with the typed one (`Preservation`, `Progress`). |
| `Outward Ps Qs` (send) | `send/ext` (under `sync`): the send step is `Ext Ps`, so `waitLeaf` finds the leaf (`AlgNorm.sendAt`, `Progress`), and a send is never also hidden. |
| `Q ∉ Ps` (receive) | `recv/ext`, likewise (`AlgNorm.recvAt`). And `Progress.sender/head-progress`: the sender's process, at a receive of one of its own roles targeted by its own role's multicast, is absurd. |
| `Focus` (receive) | `Progress` only: `sender/head-progress`'s receive case and `recv-head`'s receive case (§9.3); `hidden/first` (§9.2) to show a non-hidden step at a hide node's state is idle for the process. `AlgNorm` carries it (`focus/cat`, `focus/~`) and never inspects it. |
| `FocusS` (send) | `Progress` only: `recv-head`'s send case (§4.2). Carried like `Focus`. |
| `Partition` (in `⊢s`) | `Preservation.⊢s-comm-update` (uninvolved processes), `⊢s/hide` (§9.1), and `Progress` (`owner`). |

`j ≢ j₀` for receivers is now part of `s/comm` (`recvs`), not a typing premise: the old
`Apart Ps Qs` is gone.

Preservation and termination need no side condition beyond `Partition`. With the role
named, a receive's `conts` are today's `conts` at that role, and today's argument
(`recv-overlap` + `no-new-branch/step` at the role) covers every message the semantics lets
that process take.

### 4.4 What `Focus` rejects

**`Focus` rejects exactly the linearisations of concurrent actions of the process's own
roles.** Suppose `Focus Ps P G` fails for a process typed at an action as `P`. Then there
is an idle run `G → G′` and an external step `β` at `G′` with a role `P′ ∈ Ps` and without
`P`. `skip/advance*` keeps `P`'s action `α` enabled at `G′`; `active-inactive/⋄` gives
`α ⋄ β`; `step-diamond` commutes them. So the graph leaves `α` and `β` unordered, and the
process ordered them. Conversely, any such reachable pair makes `Focus` fail. So where the
graph orders the roles' external actions (`Rec2Buy`'s `{B,S}`), `Focus` holds whenever the
naive rules do, and costs nothing; and internal steps are never counted (§5.5).

**Which linearisations are safe.** Not all: (a) and (b) are linearisations. For two
concurrent external actions of one process, ordered "x before y":

| process order | against single-role peers | deadlocks against |
|---|---|---|
| send before send | safe | a process ordering the two *receives* the other way |
| receive before receive | safe | a process ordering the two *sends* the other way |
| send before receive | safe | the mirror image (b) |
| receive before send | safe | the mirror image (both wait at receives) |

A per-process judgment never sees the other process, so it may allow only a set of orders
that cannot close a wait cycle among themselves. **Send before send, and `Focus` on
receives** is such a set, and is what D12 adopts: a receiver with `Focus` is already at the
receive of any enabled step targeting it, so a process holding one send behind another
only ever waits for a ready receiver. `FocusS` is that condition. The other three orders
can only be allowed by a global discipline, such as a priority order on roles; they stay
rejected.

So what is rejected, in total: a process that orders a receive of one of its roles after
any concurrent action of another of its roles, or a send after a concurrent receive.

## 5. Hidden internal communication

### 5.1 The idea

A step `β` is **internal** to a process when every role that takes part in `β` is one of
its roles. The process does nothing for it: no syntax, no session step. For typing, it is
the process's **own choice**: a derivation steps over it with `t/hide` (`skip/hide` inside
a skip tree, `wv/hide` in `WaitV`), choosing which internal step to take when there are
several. Steps of others are skipped as today, universally.

For the graph, internal steps are what τ is for weak bisimulation: `Hidden β` says `β` is
internal to some process of `Ρ`, and `G =< α >=> G′` is some hidden steps followed by `α`.
Session steps are matched by weak steps (§9.1), whose hidden steps are the ones the
involved derivations chose.

### 5.2 What the typing means

- **An internal choice is made by the process.** `P ⟶ {Q} # i . Q ⟶ {R} # i` with
  `{P,Q}` types as `ifp E then Q ▹ {R} ! 0 … else Q ▹ {R} ! 1 …`: `t/if` at `G₀`, then in
  each branch `t/hide` of the matching `P⟶Q#i` and `t/send` at `Gᵢ`. One message. `{R}`
  skips both `P⟶Q#i` universally and its receive covers both labels, exactly as with three
  processes (§0).
- **A process hides before it waits** (strict `skip/step`, D8). At a state with an internal
  step for `Ps`, `skip/step` does not apply; the derivation must `t/hide` one, or act. This
  loses nothing: an internal step and an idle step commute (`hide/advance`), so hiding
  first and waiting after reaches the same states as waiting first. It is needed: without
  it, two processes could each wait on an idle witness that is the other's never-taken
  internal step, and no derivation would move the graph (§9.2's chase relies on "a state
  with only hidden steps has an owner at a hide").
- **Runs are idle.** `t/unskip`, `Focus`/`FocusS` and `Wait`'s walks range over steps
  idle for `Ps`. The environment never performs `Ps`'s internal steps, so a derivation that
  hid branch 0 is never moved along branch 1.
- **`t/end` is universal.** `¬ Ps ∈T* G`: no external step of `Ps` is reachable by *any*
  run, including runs through `Ps`'s own internal steps. A process may not declare itself
  done while one of its own internal choices leads to a message someone waits for. To
  finish after an internal dead end it writes `t/hide` then `t/end`.
- **Cycles need the environment** (D13). `skip/cycle`/`wv/cycle` require `Ps ∈T⁺ G`: a
  run of non-hidden steps idle for `Ps` to a step `Ps` takes part in. A process cannot
  defer around a loop that only its own, or another process's, internal choices close.

### 5.3 The theory lemmas still hold

Three facts about internal steps are needed, all from `recv-overlap` and `step-diamond`
in `Behav.agda`:

- **An external step of `Ps` survives an internal step of `Ps`** at the same state
  (`ext-internal/⋄`): `α ≢ β` since `α` has a role outside `Ps` and `β` has none; a receiver
  `Y` of `α` is not in `β`, else `recv-overlap` gives `comm α ≡ comm β` and `ext/comm`
  makes `β` external; symmetrically for receivers of `β`. Then `step-diamond`. This carries
  a leaf's step through the process's own hides (`waitLeaf*`, §6.4).
- **An internal step of `Ps` survives an idle step of `Ps`, and vice versa**
  (`hide/advance`): the two have no role in common, so `disjoint/⋄` and `step-diamond`.
  This advances a `wv/hide` node along idle runs (`waitFollow`, §6.4) and commutes hides
  of different processes in §9.2.
- **Idle runs are today's**: `skip/advance*`, `branch/before*`, `recv/same-comm*` are
  the role-level lemmas at the witness role.

Note what is **not** claimed: an internal step of `Ps` may involve `R` in general (`Ps =
{R,R′}`, `β = R′ ⟶ {R}`). It cannot at a state where `R` also has an external receive
enabled; that is `ext-internal/⋄`.

### 5.4 The weak step

```agda
Step G (just α) G′ = G =< α >=> G′          -- was `G -< α >-> G′`
Step G nothing  G′ = G ≡ G′
```

It is inductive, not a list with an `All`, so lemmas that walk hidden steps recurse on
`w/hide` directly (the curried-run pattern). There are no hidden steps after `α`: processes
skip those themselves. Under `singletons` there are no hidden steps at all
(`weak/singletons`).

The relation allows any hidden steps before `α`. The weak step that `preservation`
actually produces is narrower: every hidden step in it was chosen by the derivation of the
sender's process or of a receiver's, in the order the lockstep of §9.2 took them. Hidden
steps of uninvolved processes are never needed, because `no-new-comm/step` says `α` was
already enabled before them. The statement keeps the wider relation, since nothing
downstream needs the narrower one.

**When the session is `done`, the graph may still have hidden steps.** Every process has
`t/end`, so no `Ext` step is reachable for any of them, so every reachable step is hidden.
`finished`, `done` and the termination statements are about the session and do not change.

### 5.5 Interaction with `Focus`

`Focus` counts only external steps. An internal step makes no one wait: the process never
performs it, and no other process takes part. So it cannot be part of a wait cycle.
Everywhere `Progress` uses `Focus`, the step it is applied to has its sender in another
process, so the exemption never meets the proof.

### 5.6 Fallback

There is no fallback that keeps one message per internal choice. If `hidden/first` (§9.2)
cannot be mechanised, the options are, in order of preference:

1. **Forbid `wv/cycle` below a `wv/hide`.** Cycles then close only through regions the
   process walks idly, and §9.2's case 4 never meets a hide. Processes lose the ability to
   defer around a loop that passes through one of their own internal steps.
2. **Explicit internal sends.** The send stays in the syntax (`P ▹ {Q} ! i < E >∙ Pr` with
   `Qs ⊆ Ps`), `s/comm` fires it with no receiver process, the session step is labelled as
   usual, there are no hidden steps and `Step` is unchanged. An internal choice is then
   two messages, which §0's requirement rules out; this is the fallback of last resort.

## 6. Typing

### 6.1 `Typing/Declarative.agda`

```agda
t/send :
  ∀ {Ps r P Qs I}{i : Fin (suc I)}{G G′ Pr E S}
  → (acts : Acts Ps r P)
  → (out  : Outward Ps Qs)
  → (foc  : FocusS Ps P G)                                   -- D12
  → (gr   : G -<[ P ↦ (! Qs) # i < S > ]>-> G′)              -- today's premise
  → (etd  : Γ ⊢e E ∶ S)
  → (td   : Γ & Δ ⊢p Ps ◃ Pr ∶ G′)
  → Γ & Δ ⊢p Ps ◃ send r Qs i E Pr ∶ G

t/recv :
  ∀ {Ps r R Q I}{i : Fin (suc I)}{T G G′}{Br : Vec (Proc (suc γ) δ) (suc I)}
  → (acts : Acts Ps r R)
  → (ext  : Q ∉ Ps)
  → (foc  : Focus Ps R G)
  → (gr   : G -<[ R ↦ (？ Q) # i < T > ]>-> G′)              -- today's premise
  → (conts : ∀ {j U G″} → G -<[ R ↦ (？ Q) # j < U > ]>-> G″
           → (U ∷ Γ) & Δ ⊢p Ps ◃ lu Br j ∶ G″)               -- today's premise
  → Γ & Δ ⊢p Ps ◃ recv r Q Br ∶ G

t/hide     : (gr : G -< ι >-> G′) → (int : Internal Ps ι)   -- the process's own step: chosen
           → (td : Γ & Δ ⊢p Ps ◃ Pr ∶ G′) → Γ & Δ ⊢p Ps ◃ Pr ∶ G
skip/hide  : likewise inside `⊢skip`, with the same `Ξ`      -- hides do not grow the visited set
skip/step  : (gr : G -< α >-> G′) → (na : Ps idle-in G)      -- STRICT: no internal step at `G`
           → (ktd : ∀ {G″ β} → G -< β >-> G″ → Leaf & G ∷ Ξ ⊢skip Ps ◃ Pr ∶ G″) → …
skip/cycle : lu Ξ X ~ G → Ps ∈T⁺ G → …                       -- D13
t/unskip   : (tr : G -[¬* Ps ]->* G′) → …                     -- idle runs
t/end      : ¬ Ps ∈T* G → Γ & Δ ⊢p Ps ◃ ∅ ∶ G                 -- universal
t/if t/rec t/var                                            -- `P ↦ Ps`, otherwise unchanged
```

`Ps ∈T⁺ G` mentions `Hidden`, so `_&_⊢skip_∶_` and `_&_⊢p_∶_` are defined inside
`module Sessions {k} (Ρ : Roles k)` (D13), together with:

```agda
  ⊢s_∶_ : Session → Behav → Set
  ⊢s M ∶ G = Partition Ρ × (∀ j → [] & [] ⊢p lookup Ρ j ◃ lookup M j ∶ G)
open Sessions singletons public                               -- compatibility, §3.3
```

### 6.2 `Typing/Alg.agda`

`Post`, `Dom` and `Offers` are indexed by a role, as today: `Post P e 𝒮`, `Dom P e`,
`Offers Q R I` at the acting role. Everything that walks is indexed by the role set:
`Front Ps`, `Reach Ps`, `Wait Ps`, `Unskip Ps`, `Ended Ps`, `_⇝[ Ps ]_` and `WaitV Ps`.
The module takes `Ρ` after `wb` (D13).

```agda
-- `WaitV` gains a constructor and `wv/step` becomes strict.
wv/hide  : (gr : s -< ι >-> t) → Internal Ps ι → WaitV Ps L V t → WaitV Ps L V s   -- `V` unchanged
wv/step  : (na : Ps idle-in s) → (gr : s -< α >-> t) → (k : ∀ {β u} → s -< β >-> u → WaitV Ps L (V ∪ (s ~_)) u) → …
wv/cycle : (anc : ∃[ a ] V a × (a ~ s)) → (inT : Ps ∈T⁺ s) → …

-- The idle walk, and the hide walk.
s ⇝[ Ps ] t  = Ps idle-in s × ∃[ β ] s -< β >-> t
s ⇝h[ Ps ] t = ∃[ ι ] s -< ι >-> t × Internal Ps ι
Reach Ps 𝒮 (ws , t) = ∃[ s ] (ws , s) ∈ 𝒮 × Star (λ u v → u ⇝[ Ps ] v ⊎ u ⇝h[ Ps ] v) s t

Foc  : PartSet → Part → States δ ; Foc  Ps P (_ , s) = Focus  Ps P s
FocS : PartSet → Part → States δ ; FocS Ps P (_ , s) = FocusS Ps P s

a/send : (acts : Acts Ps r P) → (out : Outward Ps Qs) → let e = (! Qs) # i < S > in
         (etd : Γ ⊢e E ∶ S)
       → (rdy : 𝒮 ⊆ Wait Ps (Dom P e ∩ FocS Ps P))
       → (td  : Γ ⊢a Ps ◃ Pr ∶ Post P e (Front Ps 𝒮))
       → Γ ⊢a Ps ◃ send r Qs i E Pr ∶ 𝒮
a/recv : (acts : Acts Ps r R) → (ext : Q ∉ Ps)
       → (rdy : 𝒮 ⊆ Wait Ps (Offers Q R I ∩ Foc Ps R))
       → (conts : ∀ {j U} → let e = (？ Q) # j < U > in
                  Satisfiable (Post R e (Front Ps 𝒮)) → (U ∷ Γ) ⊢a Ps ◃ lu Br j ∶ Post R e (Front Ps 𝒮))
       → Γ ⊢a Ps ◃ recv r Q Br ∶ 𝒮
a/if a/end a/var a/rec                                      -- `P ↦ Ps`
```

`Act Ps` uses `Ext Ps α`. The `Reach` walk includes hide steps: `Post P e (Front Ps 𝒮)`
is "after any idle steps and own hides, then the action", which is what `at/send-inv`'s
continuation ranges over.

- **`waitLeaf*`** replaces `waitLeaf`: at a state with an `Ext Ps` step, a tree is a chain
  of `wv/hide`s ending in a leaf. `wv/step` is impossible (`na` is strict, and the `Ext`
  step is not idle); `wv/cycle` is impossible below hides alone (`V = ∅`). The leaf's state
  is reached by the chain, and the `Ext` step is carried to it by `ext-internal/⋄`.
- **`waitActive`** gives `Ps ∈T* s` (through hides as well: `in/later*` on any step).
  The strict `waitActive⁺`, giving `Ps ∈T⁺ s`, holds for trees with no `wv/hide` on the
  path to a leaf; §9.3 does not need it.
- Renamings: `alg/mono`, `after/mono`, `waitV/*`, `waitStep`, `at/if-inv`,
  `at/rec-guarded`. `at/send-inv`/`at/recv-inv` additionally return `Acts`,
  `Outward`/`ext`, and the leaf's `FocusS`/`Focus`.

### 6.3 `AlgEquiv`, `MainLeaf`, `Properties`, `AlgDeclarative`, `Substitution`

These are `P ↦ Ps` ports. All of them take `Ρ` (D13), and `AlgEquiv`, `AlgNorm` and
`AlgDeclarative` take `sync` (D10) for `send/ext`/`recv/ext`.

- `td/bisim`'s communication cases transport `foc` by `focus/~`/`focusS/~`. `t/unskip`
  uses `skip/bisim*`, `t/end` uses `∈~*`, `t/hide` uses `~L` on the internal step, and
  `skip/cycle` transports `∈T⁺` by `tr-transport` (labels unchanged, so `¬ Hidden` and
  idleness are kept).
- `wait⇒skip`/`skip⇒waitV` (`AlgEquiv`) map `wv/hide` and `skip/hide` one-for-one, like
  the cycle constructors.
- `alg⇒typing` hands the leaf's `FocusS`/`Focus` and the rule's `acts`/`out`/`ext` to the
  declarative rule; a `wv/hide` becomes `t/hide`.
- `findRun` (`MainLeaf`) descends through `wv/hide` as through `wv/step`; it is structural.
- The substitution lemmas pass the new premises through unchanged. They are state-free,
  apart from the two conditions, which are about `G` and not about the process.

### 6.4 `AlgNorm.agda` — `⊢p → ⊢a`

`Walk`, `Base`, `waitFind`, `waitFollow`, `Advances`, `Typed` and `Entry` keep their shape.
The families change as follows:

- **`Walk`** gains a `t/hide` case, `walk (t/hide gr int td) = wv/hide gr int (walk td)`,
  and `tree` the same for `skip/hide`.
- **`waitStep1`/`waitFollow`** (advancing a tree along an idle step `β`) gain the
  `wv/hide ι` case: `hide/advance` gives the square, and the subtree advances along the
  transported `β`, recursively. Structural.
- **`SendL`/`SendE`** add `FocusS Ps P` for the `P` of the `t/send` they came from. `P` is
  fixed by `acts` and `acts-unique`, since the process is fixed. `sendL/adv` is today's
  `skip/advance` at `P` (the step has `P`'s event), and `focusS/cat` along the idle step.
  `sendAt` is today's proof: `send-det` at `P`, then `step-deterministic`.
- **`RecvL`** adds `Focus Ps R`. `recvL/adv` is today's proof at role `R`:
  `recv/same-comm` and `branch/before` on the one-step idle run, then `t/unskip` on the
  run they return, and `focus/cat`.
- **`sendAt`/`recvAt`** take a state out of `Post P e (Front Ps 𝒮)`: a walk of idle
  steps and own hides from a typed state, then the action. Follow the walk with
  `waitFollow` for idle steps; for a hide step `ι` the tree at that state must be a
  `wv/hide` (strict `na` rules out `wv/step`; a leaf would be an `Ext` step, and then
  `waitLeaf*` applies instead), but not necessarily `wv/hide ι`: the walk's hide may differ
  from the tree's. So `Post` is restricted to walks whose hide steps are **the tree's own**;
  equivalently, `Reach` is defined from the derivation, not from the graph. This is the one
  place the existential shows in `Alg.agda`: `a/send`'s continuation set is the states the
  derivation's hides reach, and `alg⇒typing` builds the `t/hide`s from them. Then
  `waitLeaf*` (`send/ext`/`recv/ext` under `sync`) finds the leaf, and `send-det` /
  `recv/same-comm` finish as today.
- **`typing⇒alg`**, send and receive: `a/send`'s `rdy` maps the `SendE` leaf to
  `Dom P e ∩ FocS Ps P`; `acts`/`out`/`ext` come from any leaf via `waitFind` (they are
  state-free).
- `endL/adv`, `after/adv`, `recG/adv` and `ifE/adv` are renamings.

`typing⇒alg`/`td⇒at` keep `sync` and gain nothing else.

## 7. What does not change

The following are untouched: `Definitions/Common.agda`, `Expr.agda`, `Actions.agda`,
`Behav.agda`, `Definitions/Graph/*`, `Utils/*` and `Stale/*`. In particular these stay
exactly as they are:

- `_∈T_`, `_not-active-in_`, `_-[¬_]->*_`, `_-<[_↦_]>->_` and `_⋄_`;
- every `WellBehaved`/`Synchronous` field and derived lemma;
- `wellBehaved?`, `synchronous?`, `WBNet`, `PFree` and `Disjoint`.

`git diff --stat` after the work touches only `Proc.agda`, `Typing/`, `Safety/`, `Check/`,
`Tests/` (§13's list plus one new file), `Examples/` (additions only), and the docs.

## 8. Conservativity

With one role per process (`singletons`), the new system is today's:

- `Acts ⁅ P ⁆ nothing P` holds, so unannotated actions act as the only role;
- `Outward ⁅ P ⁆ Qs` is `balanced`'s nonempty `Qs` without `P`;
- `focus/⁅⁆` and `focusS/⁅⁆`: both conditions always hold;
- `Internal ⁅ P ⁆ β` is empty under `balanced`, so `t/hide` never applies, `⁅ P ⁆ idle-in G`
  is `P not-active-in G`, `Ext ⁅ P ⁆ β` is `P ∈α β`, `_∈T*_` is `_∈T_`, and idle runs are
  today's `_-[¬_]->*_`;
- `inT⁺/singletons`: nothing is hidden, so the cycle witness is today's `P ∈T G`;
- `weak/singletons`: `Step` is today's;
- `partition/singletons`: the `Partition` conjunct of `⊢s` always holds.

So every existing derivation has a counterpart, and every existing example keeps its
result. The examples compiling unedited is the witness (§14).

## 9. `Safety/`

```agda
module Safety {N}{B} (wb : WellBehaved B) (sync : Synchronous B) {k} (Ρ : Roles k) where
```

`Ρ` is the only new parameter. `Partition` comes out of `⊢s` (`part = proj₁ M⊢G`). The
statements of `preservation/τ*`, `progress` and `no-infinite-τ-reductions` are unchanged in
form; `preservation`'s `Step` is the weak step (§5.4). Each file opens `Proc.Sessions Ρ`,
`MPST.Sessions Ρ` and `Typing.Roles wb`, hiding the top-level `singletons` names.

### 9.1 Preservation

- `at/lookup` is unchanged. `⊢s-update`/`⊢s-comm-update` rebuild the pair.
- **`⊢s/hide`: `⊢s M ∶ G`, and process `j`'s derivation at `G` is `t/hide ι td`, give
  `⊢s M ∶ G′`** with `td` for `j` and `t/unskip (skip/one* ι idle)` for every other
  process: `ι` is internal to `j`, so idle for everyone else by partition. Only the owner's
  derivation can move the graph along a hidden step.
- **`preservation/comm`** first applies `hidden/first` (§9.2) to reach `G₁` with
  `⊢s M ∶ G₁` and the action enabled at `G₁`, then proceeds at `G₁` as below, and returns
  the weak step `G =< α >=> G′`.
- `⊢s-comm-update` cases on `j ≟ j₀`, then on `meets?`:
  - the sender becomes `Ptd`;
  - a receiver becomes `Rtd j`;
  - any other process becomes `t/unskip (skip/one* gr idle) (M⊢G j)`. Here
    `idle : lookup Ρ j ∉αs α` comes from `ev-other`: every role of `j` differs from `P`
    (`owner-unique`) and is not in `Qs` (else `j` would meet it).
- At `G₁`:
  - The sender's tree is a leaf (`hidden/first` ends there) at role `P′` with
    `Acts (lookup Ρ j₀) r₀ P′`, and `acts-unique` against `s/comm`'s `Acts` gives `P′ ≡ P`.
    Then `send-action` at `P`, as today.
  - Each receiver process `j` listens as `R` with `Acts (lookup Ρ j) (rs j) R` and `R ∈ Qs`.
    `j` takes part in `α` externally, so by `waitLeaf*` its tree is a hide chain
    `ι₁ … ιₘ` to a state `K` with the leaf; `acts-unique` makes the leaf's role `R`. The
    step `α` is carried to `K` by `ext-internal/⋄`, `conts` takes it at `R` (`ev-recv` with
    `R ≢ P` by partition), giving a typing at `K′`. The receiver's continuation at `G′`
    (after `α` at `G₁`) is `t/hide ι₁ (… t/hide ιₘ (that typing))`, with each square
    closed by `step-deterministic`. **Receivers' hides are not taken by the weak step**;
    they stay in the receiver's derivation.
- `comm/ready` keeps today's shape, but is indexed by receiver **processes** rather than
  roles: one sender tree, and one tree per process `j ≢ j₀` meeting `Qs`, with leaf family
  `Offers P R_j I` at that process's listening role `R_j` (from `recvs`). Two roles of `Qs`
  in one process share one tree.
  - In `receiver-step`, a receiver leaf at `H` is a step with `P ∈α β` (`recv-sender`) and
    receiver `R_j ∉ Ps₀` (partition). So it is not idle for `Ps₀`, against the sender's
    strict `na`; that is the contradiction.
  - `multicast-idle` becomes part of `pull/β` (§9.2).

### 9.2 `hidden/first` — the new lemma

```agda
hidden/first : ⊢s M ∶ G → M [ just α ]⇒ M′
             → ∃[ G₁ ] G ==>* G₁ × ⊢s M ∶ G₁ × ∃[ G′ ] G₁ -< α >-> G′
```

Every hidden step of the run is a `t/hide` of the sender's or of a receiver's derivation,
taken in the order below, and `⊢s M ∶ G₁` is built step by step with `⊢s/hide`.

**Why it is needed.** The sender's send may be enabled only after its own hides (`Q⟶R`
really comes after `P⟶Q`), and the sender may be deferring at a `wv/step` with the send
enabled only deeper, as today.

**Shape.** Today's `comm/ready` over the sender's tree with the receivers' trees in
lockstep. "Involved" means the sender `j₀` and the processes meeting `Qs`. Every tree is
kept rooted at the current state with `V = ∅`, re-rooting at cycles with
`waitV/unfold-top` as today. Cases on the sender's tree at the current state `H`:

1. **`wv/leaf`.** The send is enabled at `H`. The receivers' trees are hide chains ending
   in leaves (`waitLeaf*`), and are left as they are: those hides stay in the receivers'
   derivations after the step (§9.1). Done, with no hidden step.

2. **`wv/hide ι₀`.** Take `ι₀` into the weak step. Every receiver's tree advances along
   `ι₀`, which is idle for it: a `wv/step` by its `k`, a `wv/hide` by `hide/advance`, a
   leaf by `t/unskip`, a cycle by `unfold-top`. Recurse on the sender's subtree.

3. **`wv/step`.** `H` has no internal step for the sender, and every step at `H` is idle
   for it. No receiver is at a leaf (`receiver-step`). Choose a step `β` at `H`:
   - **Some step at `H` is internal to no involved process.** Take such a `β`. It is idle
     for every involved process: for a receiver at a `wv/step`, by its `na`; at a hide
     chain, by what the chain ends in: a leaf's `Focus` (an `Ext` step at the leaf's state
     not involving the acting role is absurd, and `β` carried there by `hide/advance` is
     `Ext` if it is for `j`), a `wv/step`'s `na`, or a cycle's ancestor, bisimilar to a
     `wv/step` state. Recurse on `k β`, receivers advanced as in case 2. The recursion
     returns a hidden run from `t` and `γ` after it; **pull `β` forward** through it and
     past `γ` with `pull/β`. `β` does not enter the weak step.
   - **Every step at `H` is internal to some involved process.** Not the sender (strict),
     so some receiver `j′`, which is therefore at a `wv/hide ι_{j′}` (strict, and not a
     leaf). Take `ι_{j′}` into the weak step. The sender advances by `k ι_{j′}`, the others
     as in case 2. Recurse.

4. **`wv/cycle`.** The witness `Ps₀ ∈T⁺ H` (D13) is a run of non-hidden steps idle for the
   sender, then an `Ext` step. Walk it as today's `comm/ready-from-∈T` does: every run
   step is case 3's first bullet, and `unfold-top` re-roots the sender at each cycle. A
   sender hide met on the way is case 2, and the remaining run is transported along it:
   `hide/advance` for its idle steps, `ext-internal/⋄` for its final `Ext` step, same
   length.

```agda
pull/β : (∀ j → involved j → lookup Ρ j ∉αs β)        -- β idle for the involved
       → G -< β >-> t → t ==>* G₁                      -- every step internal to an involved process
       → G₁ -<[ P ↦ e ]>-> G′
       → ∃[ G₁′ ] G ==>* G₁′ × ∃[ G″ ] G₁′ -<[ P ↦ e ]>-> G″
```

Induction on the hidden run. *Empty:* every role in `γ` is `P` or in `Qs`, hence in an
involved process (`owner`), hence not in `β`; `no-new-comm/step` gives `γ` at `G`. This is
today's `multicast-idle` with "idle process" for "idle role". *`ι` then the rest:* `ι` is
internal to an involved process, so `ι` and `β` have no role in common; `no-new-comm/step`
gives `ι` at `G`, `disjoint/⋄` and `step-diamond` give `β` after it, `step-deterministic`
identifies the state with the run's; recurse and prepend `ι`.

**Why uninvolved processes' internal steps are never taken.** Such a step has no role in
common with `γ`, so `no-new-comm/step` enables `γ` before it; it is case 3's first bullet.

**Why the result is `⊢s M ∶ G₁`.** `⊢s/hide` at each hidden step of the run (the owner is
the sender in case 2, a receiver in case 3's second bullet). At `G₁` the sender's tree is
a leaf by construction, and the receivers' are hide chains to leaves by `waitLeaf*`
(`send/ext`, and `R_j ∈α γ` with `P ∉ Ps_j`).

**Termination.** Lexicographic on: the length of the current `∈T⁺` run when inside case 4
(∞ outside it); the sender's tree; the sum of the receivers' hide-chain lengths. Case 2
and case 3's second bullet shrink a tree structurally and keep the run. Case 3's first
bullet is structural on the sender outside case 4, and shortens the run inside it.
Receivers' trees change only by subterms, by `hide/advance` (same chain), or by
`unfold-top` at a cycle, after which the re-rooted tree is at a hide or a `wv/step`
(never a leaf, by `receiver-step`), so the chain sum is bounded by the receivers' tops.

**Why D13 is needed here.** With a per-process witness (`Ps₀ ∈T* H`, or even one over
idle steps only), case 4's run may take a receiver's internal step `ι′_j` while `j` is at
`wv/hide ι_j` with `ι_j ≠ ι′_j`. The receiver's tree cannot follow the run, and taking
`ι_j` instead discards the run with nothing smaller to replace it. This is not a proof
artefact: let `H --ι_j--> H₁ --β--> H` with `β` idle for everyone, and `H --ι′_j--> H₀ --γ-->`
with `γ` the sender's send to `R ∈ Ps_j`. The sender cycles at `H` with witness `ι′_j γ`;
`j` hides `ι_j` at every visit to `H`, waits for `β` at `H₁`, and closes its cycle at `H₁`
with the witness `β ι′_j γ`. Both derivations exist with per-process witnesses. The
session step fires (`j` is at its receive syntactically) and no weak step matches `j`'s
choices: preservation is false. With D13, `j`'s cycle at `H₁` needs a non-hidden idle run
to a step `j` takes part in, which does not exist, so `j`'s finite tree must eventually
hide `ι′_j`.

### 9.3 Progress

- `session/status` recurses over `tabulate id : Vec (Fin k) k`.
  `ss/end : ∀ i → ¬ lookup Ρ (lookup js i) ∈T* G`, and `inactive/done` needs only that.
- **`ss/step` carries a hidden run, the typing at its end, and a non-hidden step** (D11):
  `ss/step : G ==>* G₁ → ⊢s M ∶ G₁ → G₁ -< α >-> G′ → ¬ Hidden α → SessionStatus M G js`.
  It is found by a **chase** from a process `j` with a send or receive head, keeping
  `⊢s M ∶ H` at the current state `H` and looking at `j`'s tree there:
  - `wv/hide ι`: take it (`⊢s/hide`); continue with the subtree.
  - `wv/leaf`: the leaf step is `Ext` for `j`, hence not hidden. Done.
  - `wv/cycle`: its `∈T⁺` witness begins with a non-hidden step at `H` (an idle one or the
    `Ext` one). Done.
  - `wv/step`: if some step at `H` is not hidden, done. Else pick a step `β`, internal to
    some `j′`. If `j′` is not done, its tree at `H` is a `wv/hide` (strict, and a leaf
    would be a non-hidden step): continue the chase with `j′`. If `j′` is done, its
    `t/end` transports along `β` (`in/later*`), `j`'s tree advances by `k β`, everyone
    else by `t/unskip`; take `β` and continue with `j`.

  Termination: each move replaces one non-done process's tree by a subterm (its own hide,
  or `k β`) and the others' by `waitFollow`, which only shrinks or re-roots at a cycle,
  and a cycle ends the chase at once. So the multiset of non-done trees decreases.
- `progress` on `ss/step`: `step/progress` at `G₁` with the carried `⊢s M ∶ G₁`. The
  conclusion `done M ⊎ ∃ step` does not mention the graph state, so proving it at `G₁` is
  proving it.
- `step/progress`: `balanced gr` gives the sender `P` of the non-hidden step `gr`. Its
  process is `owner P`, which takes part in `gr` through `P` (`owner-∈`), and `gr` is `Ext`
  for it (not internal, since not hidden).
- `sender/head-progress`. `gr` is `Ext` for `owner P`'s process, so by `waitLeaf*` its
  tree at `G₁` is a hide chain `ι₁ … ιₘ` to a leaf at `K`, and `gr` is carried to `K`.
  Take the hides first (`⊢s/hide` each, the others `t/unskip`), so the session is typed at
  `K` and the head's tree is the leaf. Then, with the head acting as `r`:
  - **Send.** The leaf's own step `α′` drives `receivers/progress`, as today. The send
    condition is not used here.
  - **Receive from `Q`**, under `Focus`, so `r ∈α gr`. Either `r ≡ P` (sends in `gr`,
    receives in the leaf's step), which is absurd by `recv-overlap` at `P`. Or `r ∈ Qs`
    receives from `P` in `gr`: `recv-overlap` at `r` makes `？ Q ≡ ？ P`, so `P` would be
    both in `Ps` (`owner`) and not (`ext`), which is absurd.
- `receivers/progress` collects over processes `j ≢ j₀` meeting `Qs′` (`fin-collect` over
  `Fin k`). `recv-head` on `j`: `α′` involves `j` through some `R_j ∈ Qs′` and is external
  for it (its sender is in `j₀`), so by `waitLeaf*` `j`'s tree is a hide chain to a leaf
  at `K_j`, with `α′` carried there. The head acts as `r`, and `r ≢ P′` by partition.
  - **At a send**, under `FocusS` at `K_j`: `r ∈α α′` (then `r` receives in `α′` and sends
    in the leaf's step, and `recv-overlap` at `r` is absurd), or no role of `Ps_j` receives
    in `α′` (but `R_j` does). Absurd.
  - **At a receive from `Q″` of arity `I`**, under `Focus` at `K_j`: `r ∈α α′`, so `r`
    receives from `P′` in `α′`; `recv-overlap` at `r` gives one `comm`; `comm-ev` and
    `ev-inv` give `Q″ ≡ P′`, and `step-arity-det` **at `r`** gives the arity. `r ∈ Qs′` by
    `ev-inv`, which supplies `recvs`' second component. The receive is syntactic, so the
    hides before it do not matter for `s/comm`; they are taken into the receiver's
    continuation by preservation (§9.1).
  - **At `if`/`rec`**: a τ step. **At `∅`**: absurd (`in/αs*`). **At `v`**: `Fin 0`.

  Then `s/comm j₀ send≡ acts e⇓v recvs`.

Never apply `step-arity-det`/`step-sort-det` across two different roles. Always go through
`comm α ≡ comm β` at one role first.

### 9.4 Termination

Internal steps produce no session steps, so nothing changes. Sums range over `k`, and
`sum/map-update<` is generic. `still-done`, `still-ended` and `final-run/*` recurse over
`Fin k`, and the `τ-depth` patterns use `send`/`recv`.

## 10. `Check/`

- **`Check/Alg.agda`.**
  - `Shared` gains the assignment: `hidden?` per edge, tabulated once per `Ρ`.
  - `Env Ps`:
    - `ok Ps s` holds when every edge at `s` is idle for `Ps` (strict: an internal edge
      makes it false);
    - `G¬ Ps` keeps the idle edges, as today's keeps the `¬P` ones;
    - `Gι Ps` lists the internal edges per state, for `wv/hide`;
    - `inT?` decides `_∈T*_`: reachability of an `ext? Ps` edge over all edges;
    - `inT⁺?` decides `_∈T⁺_`: reachability of an `ext? Ps` edge over idle, non-hidden
      edges;
    - `act?` and `idle` use `ext?`/`_∉αs?_`.
  - `focus? Ps P s` and `focusS? Ps P s`:
    `FinP.all? λ s′ → unskip? s s′ →-dec all-out? s′ (λ β _ → ext? Ps β →-dec …)`, with
    `P ∈α? β` for the first and `P ∈α? β ⊎-dec no-recv? Ps β` for the second. Tabulated
    per state (`memoB`), from the idle rows that `Unskip?` already needs.
  - **`Wait?`** gains the hide alternative: at a state with internal edges, `ok` is false,
    so the decision tries each internal edge (`Gι Ps`) in turn, with a **second visited
    set for hides** so an internal loop is cut (a hide back to a visited state can be
    dropped from any derivation). At a state with no internal edge it is today's.
  - `send-case`/`recv-case` resolve the role once by `acts?`, test `Outward`/`ext`
    syntactically, and use `Dom? P e`/`Offers? Q R I` as today, intersected with
    `focusS?`/`focus?`.
  - **`Post?`**: the continuation set is the states reached by the derivation's own hides;
    `probe` records, with each `Wait?` success, which internal edges it took, and the
    continuation is probed at the states after them. This is the existential made
    algorithmic, and the one place the checker's structure changes rather than its
    tables.
  - `Probing (Ps : PartSet) (E : Env Ps)`. The `probe` clauses match `send r …` and
    `recv r …`. `alg-empty?` checks the state-free premises.
  - `Graph/Reachability.agda` is untouched.
- **`Check/TypeCheck.agda`.**
  `tcAs? : ∀ {k}(Ρ : Roles k)(Γ Δ)(Ps : PartSet)(Pr)(s) → Dec (Γ & Δ ⊢p Ps ◃ Pr ∶ s)`, and
  `tc? Γ Δ P = tcAs? singletons Γ Δ ⁅ P ⁆` (same type as today, via `_◂_`).
  `tcSessionAs? : ∀ {k}(Ρ : Roles k)(M)(s) → Dec (Sessions.⊢s Ρ M ∶ s)`, which is
  `partition? Ρ ×-dec FinP.all? …`; `tcSession? = tcSessionAs? singletons`.
- **`Check/Core.agda`.** It gains `partition? : ∀ {k}(Ρ : Roles k) → Dec (Partition Ρ)`
  (for each role, exactly one `j`). `ProcessTyping` takes a `PartSet`, `SessionTyping`
  takes `Ρ`; single-role aliases keep today's names.
- **`Check/Graph.agda`, `Check/Network.agda`.** They gain `typecheckAs WR Ps Pr`,
  `typecheckSessionAs WR Ρ M` and `typecheckSessionNetAs w Ρ M`. `typecheck` and
  `typecheckSession` keep their types (via `⁅ P ⁆` and `singletons`).

## 11. Order of work

Each step ends with `agda <file>` on the files it touched. Do not run `runall.sh` before
step 9. The tree must be hole-free after every step.

1. `Definitions/Proc.agda`: §3, including every `Subst` clause, the pattern synonyms and
   the compatibility layer.
2. `Definitions/Typing/Roles.agda`: §2, including `ext-internal/⋄` and `weak/singletons`.
   It compiles against the unchanged theory.
3. **Spike §9.2's lockstep** in a scratch file against `Roles.agda`: `WaitV` with
   `wv/hide` and strict `wv/step` over abstract leaf families, as today's
   `comm/ready-or-∈T` has it (no `⊢s`, no processes), with one sender tree and a vector of
   receiver trees. The target is the statement of `hidden/first` with the trees in place
   of `⊢s`, including the termination measure. If it does not go through, take §5.6's
   first option now, and re-run the spike with cycles forbidden below hides.
4. `Typing/Declarative.agda`: §6.1, including `MessageGuarded`'s patterns.
5. `Typing/Alg.agda`, `AlgEquiv.agda`, `MainLeaf.agda`, `Properties.agda` and
   `AlgDeclarative.agda`: §6.2–6.3.
6. `Typing/AlgNorm.agda`: §6.4. Then `Typing/Substitution.agda`.
7. `Safety/Preservation.agda`, `Progress.agda`, `Termination.agda` and `Safety.agda`: §9.
8. `Check/*` and `Check.agda`: §10.
9. §13's test edits and `Tests/MultiRole.agda`. Check that every example compiles
   **without edits**. Then `git diff --stat` against §7, `./runall.sh --clean --tests` and
   `./runall.sh --CheckClosedProof`.
10. Docs (§12).

## 12. Tests and docs

- **Examples and API-level tests:** no edits. Processes use the synonyms; `P ◂ Pr` is the
  compatibility function; sessions go through `typecheckSession` (= `singletons`); `tc?`
  and `typecheck` take one role.
- **Tests that use internals:** mechanical edits only, listed in §13.
- **New `Tests/MultiRole.agda`**, with every result forced:
  1. §0's two multicast sessions: both accepted.
  2. §0's hidden example `P⟶{Q} . Q⟶{R}` with `{P,Q} ◃ Q ▹ {R}! ∙ ∅`: accepted.
  3. §0's internal choice `P ⟶ {Q} # i . Q ⟶ {R} # i` with `{P,Q} ◃ ifp … then … ! 0 …
     else … ! 1 …`: accepted, one message. The same process without the `ifp` (a single
     `! 0`): accepted (the derivation hides branch 0). An internal loop before an external
     send: accepted. An internal loop with no external step after it and the process
     `∅`: accepted (`t/end`). An internal dead end next to a live branch, with the process
     at the live branch's send: accepted (`t/hide` picks the live branch).
  4. A partly internal multicast `P ⟶ {Q,R}` with `{P,Q}`: accepted; `R`'s process must be
     at its receive.
  5. `Rec2Buy` with `{B,S}` as one process (`B ▹ …`/`S ▹ …` on each action), against the
     unchanged graph: accepted.
  6. §4.1(a) and §4.1(b): both graphs pass `wellBehaved?`/`synchronous?`, and both
     sessions are rejected (`Focus`).
  7. The send-before-send linearisation of §4.4 (`{A,C} ◃ A ▹ {B}! ∙ C ▹ {D}!`): accepted
     (D12). Its mirror with a receive first (`{B,D} ◃ B ▹Σ A ？· (D ▹Σ C ？· …)`): rejected.
     A send ordered before a concurrent receive ((b)'s `X` alone): rejected.
  8. A `Ρ` that is not a partition: rejected (`partition?`).
  9. An unannotated action in a two-role process: rejected (`Acts`). A fully internal send
     written out (`{P,Q} ◃ P ▹ {Q} ! …`): rejected (`Outward`).
  10. `pull/β`'s case, end to end: `G --Z⟶Z′--> t`, `G --P⟶R--> G′`, `t --P⟶R--> t′`,
      `G′ --Z⟶Z′--> t′`, with `Ρ = [{P},{R},{Z,Z′}]` and `{Z,Z′} ◃ ∅`. Accepted, and
      `preservation` on the session step `P⟶R` at `G` returns the weak step with **no**
      hidden prefix (the uninvolved internal step is dropped). Stated as a forced equality
      on the run's length if `preservation` is made to return one, otherwise as a comment.
  11. D13's example (§9.2): the sender's `∈T⁺` witness at `H` must not use `ι′_j`. With
      the graph as given, `{P} ◃ {R} ! …` is **rejected** at `H` unless some non-hidden
      idle run from `H` reaches its send; add such a run and it is accepted. And `j`'s
      process `R ▹Σ P ？· …` is accepted only with a derivation that hides `ι′_j`: forced
      as a comment, since derivations are not observable from `tc?`.
  12. A process that waits with an internal step pending is impossible to write, so this
      is a checker test: `Wait?` at a state with an internal edge never takes the
      `wv/step` branch. Forced through `Probing.Wait?` as `CheckAlgSanity` does.
- **`README.md`:** the process syntax (annotations and synonyms), `NProc`, `Roles`/`Session`,
  hidden internal communication, and the two rules with `Focus`.
- **`CLAUDE.md`:** `Typing/Roles.agda` in the layout, `Safety`'s `Ρ` parameter, the pattern
  synonym rule (§14), the compatibility layer, and the `_∈_` gotcha.
- **`FUTURE_WORK.md`:** §A: `PFree` is per role set in the projection statement. Add items
  for §4.4's send-before-send condition and, if §5.6 was taken, for hidden internal steps.

## 13. Existing tests that need edits

They call checker or typing internals with a `Part` where a `PartSet` is now expected.
Every edit is `P ↦ ⁅ P ⁆` or a one-line wrapper; no expected result changes.

| file | uses | edit |
|---|---|---|
| `Tests/SkipBeforeVar.agda` | `skip/step … na ktd` with `na : A not-active-in s` | `idle/⁅⁆ na`, a lemma `P not-active-in G → ⁅ P ⁆ idle-in G` in `Roles.agda` |
| `Tests/WaitNotSkip.agda` | `WaitV P …`, `wait⇒skip P …`, `P ∈T (g i)` | `⁅ P ⁆`; the modules are applied to `singletons`; a `wv/cycle` witness, if one is built, goes through `inT⁺/singletons` |
| `Tests/CheckAlgSanity.agda` | `env P`, `Env.inT?`, `Probing.Wait? P (env P)` | `⁅ P ⁆` |
| `Tests/AlgCheck.agda` | `alg? v[] A …` | `⁅ A ⁆` (`tc?` is unchanged) |

Everything else in `Tests/` and all of `Examples/` compiles unedited. If any other file
needs an edit, the port is wrong somewhere.

## 14. Gotchas specific to this port

- **Pattern synonyms cover `nothing` only.** A function on `Proc` written with
  `Qs ! i < E >∙ Pr` misses annotated sends. Proof files must match `send r …`/`recv r …`.
  Only `Tests/`/`Examples/` may use the synonyms, and there only as expressions or in
  matches that have a fallback clause.
- **`_◂_` is a function now.** Never match on it; match on `_◃_`.
- **Two `Session`s.** The top level is the `singletons` instance; `Sessions Ρ` is the
  general one. Hide one when opening the other.
- **Three `_∈_`s:** `Data.Fin.Subset` (a role in a set), `Relation.Unary` (a state in a set,
  in `Alg.agda`), and `Data.List.Membership` (edges, in `Check/Alg.agda`). Rename on import
  where two meet. `Data.Fin.Subset`'s `⊤`/`⊥` clash with `Data.Unit`/`Data.Empty`; rename
  them to `full`/`none`. `Data.Fin.Subset._⊆_` clashes with `Relation.Unary._⊆_`, which
  `Alg.agda` uses everywhere: never open `Subset`'s `_⊆_` there.
- **`Internal` is by events (D10), and `Ext` for a rule's own step needs `sync`.**
  `send/ext`/`recv/ext` are the lemmas to reach for; they take `sync`. The modules that
  use them (`AlgNorm`, `AlgEquiv`, `AlgDeclarative`) have it as a parameter. `Alg.agda`
  itself does not: `waitLeaf*` takes `Ext Ps α` as a hypothesis and the caller discharges
  it.
- **`⊢p` takes `Ρ` (D13).** Only `skip/cycle`'s witness looks at it. A lemma that does not
  mention cycles can be stated for any `Ρ` without using it.
- **`_∈αs_`/`_∉αs_` unfold through `lookup`.** Pin `{Ps}{α}`, as for `∉α→¬∈α` today.
- **Idle means idle.** Runs, `skip/step`'s `na`, `Focus`/`FocusS` and `Wait`'s walks are
  over steps idle for `Ps` (`_∉αs_`). Internal steps are never "skipped"; they are hidden
  by `t/hide`, one at a time, by choice. If a proof wants to move a derivation along an
  internal step the derivation did not choose, the proof is wrong.
- **Strict `wv/step`.** `na : Ps idle-in s` says every step at `s` is idle. A state with an
  internal step for `Ps` admits only `wv/hide`, a leaf, or (below a `wv/step`) a cycle.
  Proofs that case on a tree at a state with an `Ext` step use `waitLeaf*`, which returns
  a hide chain and a leaf, never a bare leaf.
- **Use `acts-unique` to align the typed role with the semantics' role.** Never re-derive it
  from the graph.
- **`Focus` is carried, not recomputed.** Keep `conts`/`ktd`/`k` as pattern variables
  (termination checker).
- **Conservativity needs `sync`.** `Internal ⁅ P ⁆ β` is empty only under `balanced`. The
  typing modules take `wb` only, so single-role typing equals today's for synchronous
  theories, which is every theory the checker builds.

## 15. Acceptance

- `./runall.sh --clean --tests` and `--CheckClosedProof` are green. There are no
  `postulate`s and no `TERMINATING` pragmas.
- `git diff --stat` touches nothing in §7's list, no `Examples/` file, and in `Tests/` only
  §13's files plus `Tests/MultiRole.agda`.
- `focus/⁅⁆`, `focusS/⁅⁆`, `inT⁺/singletons` and `weak/singletons` are proved, and the
  conservativity claim is witnessed by the untouched examples.
- §0's internal choice types with one message (test 3), and the send-before-send
  linearisation is accepted (test 7).
- `Tests/MultiRole.agda` compiles with every decision forced.
- `Safety.agda`'s only new parameter is `{k}(Ρ : Roles k)`, and `preservation`'s only
  change is `Step`.

## 16. Review of 2026-10-01: dubious points and alternatives

Each item names what is uncertain, the choice this plan makes, and what to do if the
choice fails. Ordered by how much of the plan depends on them. Decisions already taken
(D9's function, D10's events, D12's send condition) are not re-opened here.

1. **`hidden/first` (§9.2).** Proved on paper with a lexicographic measure; not
   mechanised. The bookkeeping is heavier than today's `comm/ready`: four node kinds, trees
   re-rooted at the current state, and the `∈T⁺` run transported along hides. *If it
   fails:* §5.6's first option (no cycles below hides) removes the run transport; the
   second option gives up one message per choice. Decide at step 3 of §11.

2. **`⊢p` depends on `Ρ` (D13).** Only through `skip/cycle`'s witness, but it means a
   process's typing is relative to how the *other* roles are grouped. §9.2 shows a
   per-process witness is unsound for preservation, and §5.6's option 1 does not remove
   the dependence: a run idle for `Ps` can still pass through another process's unchosen
   internal step, whether or not the deferring process has hides of its own. So `Ρ`
   stays. *Alternative worth checking at the spike:* a witness over runs that are idle
   for `Ps` and hidden for no process **that meets the run's final step** — still
   `Ρ`-dependent, but only through the processes the deferred action involves, which is
   the least a per-process judgment can get away with.

3. **Strict `skip/step` (D8).** A process cannot wait while it has an internal step
   pending. `hide/advance` shows hiding first reaches the same states, so no behaviour is
   lost, but a derivation is forced to commit to an internal branch before an idle step
   that might have informed the choice. It cannot be informed: information arrives by
   external receives, which are leaves, not idle steps. *If strictness bites in an
   example:* allow `wv/step` with internal steps present but require `k` to cover them
   too (universal for those) — the 2026-09-29 reading, for that state only.

4. **The existential in `Alg.agda` (§6.4).** `Post P e (Front Ps 𝒮)` must range over the
   derivation's own hides, not the graph's internal edges, else `sendAt`/`recvAt` cannot
   find the leaf. This makes `Reach`/`Front` carry derivation data, which today they do
   not; `⊢a` is then "typed on a set of states, each with its chosen hides". *Alternative:*
   keep `Reach` over all internal edges and require `a/send`'s continuation at *every*
   internal branch — which is the universal reading again, rejected by §0. So the
   derivation data stays; the cost is in `alg/mono` and `after/mono`.

5. **The weak step is wider than what preservation produces (§5.4).** Keep; nothing
   downstream needs the narrower form.

6. **The checker's search (§10).** Each state with internal edges branches the `Wait?`
   decision; with the hide-visited set it is finite, but `probe`'s memo table is keyed by
   state and process, and must now also be keyed by the chosen hides for the continuation.
   *If it is too slow:* memoise `Wait?` per `(Ps, s)` on success with the first hide
   sequence found; `⊢a`'s downward closure makes any witness as good as another.

7. **`Partition` inside `⊢s` (D6).** Re-proved by `partition?` on every session check and
   carried by every `Safety/` statement. *Alternative:* a parameter of `Safety`. Rejected
   for now: it would change every statement's hypotheses.

8. **Empty role sets.** `Partition` allows a process with no roles. It can only be typed
   as `∅` (or `if`/`rec` over `∅`): `Acts` never holds and `t/end`'s `¬ ∅ ∈T* G` is
   vacuous. Harmless; `partition?` need not reject it. Mention in `README.md`.

9. **`Rec2Buy` with `{B,S}` (test 5).** Checked by hand (§4.4): every state's external
   steps involve the acting role, and there are no internal steps. Not yet run. If it is
   rejected, §4.4's claim that `Focus` costs nothing on graph-ordered roles is wrong, and
   must be redone before anything else.
