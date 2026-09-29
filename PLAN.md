# PLAN.md — one process, many roles

*Written 2026-09-28 on `set-typing`, after the multicast rework (`1b7f892`, `770b67f`).
Revised 2026-09-29: hidden internal communication (§5), corrected counterexample (§4.1(a)),
what `Focus` costs (§4.4), and the compatibility layer for tests (§3.3, §13).
Nothing below is implemented yet.*

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
> rules accept. Preservation and termination survive. The fix is one side condition,
> `Focus`, on `t/send`/`t/recv` and `a/send`/`a/recv` (§4.2). It is trivially true for a
> single role, so every existing derivation, example and test carries over. §4.4 records
> exactly what `Focus` rejects.

> **⚠ Proof risk — read §9.2.** Hiding internal communication (§5) needs one new lemma,
> `hidden/first`: a session step can always be matched by hidden steps followed by the
> action. It is sketched but unproved. §5.6 gives the fallback if it fails.

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

**Typing.** The communication rules are today's, at the acting role, plus the `Focus` side
condition. Everything else replaces `P` by `Ps`, and "idle" becomes "silent": a process
skips steps it takes no part in **and** steps that happen entirely among its own roles.

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

`P ⟶ {Q}` is internal to `{P,Q}`: the process skips it as it skips steps of others, and
writes only its send to `R`. The one session step matches the graph run
`P⟶Q · Q⟶R`.

## 1. Decisions

| # | decision | why |
|---|---|---|
| D1 | Sends and receives carry `Maybe Part`: the acting role, or `nothing` for "the only role". The existing syntax is kept as **pattern synonyms** for `nothing` (§3.1). | Tests and examples construct processes only. Proofs match on the real constructors; that change is mechanical. Checked in a scratch file: both surface forms, `{I}` implicit, fixity `infixr 8`, and matching on constructors and on synonyms. |
| D2 | The acting role is resolved by `Acts Ps r P`: `r ≡ just P × P ∈ Ps`, or `r ≡ nothing × Ps ≡ ⁅ P ⁆`. The rules and `s/comm` both use it. | `Acts` is functional (`acts-unique`), so the role the semantics fires and the role the typing checked are the same, with no argument. |
| D3 | The communication rules keep today's step premise **at the acting role**: `G -<[ P ↦ e ]>-> G′`, from `Behav.agda`, unchanged. | Send typing does not change; receive typing is today's, at one role. No new step relation. |
| D4 | One new premise per communication rule, **`Focus Ps P G`** (§4.2), plus two syntactic ones: a send reaches some role outside `Ps` (`Outward`), and a receive's sender is not in `Ps`. | §4. `Focus` is the only premise that mentions the theory. |
| D5 | The set-level vocabulary (`Internal`, `Silent`, `Ext`, `_∈αs_`, `_idle-in_`, `_∈T*_`, `_-[¬*_]->*_`, `Focus`, `Acts`, `Outward`) lives in a new `Typing/Roles.agda`, built from the unchanged role-level notions. So do `Hidden` and the weak step `_=<_>=>_`, which depend on the assignment. | Ground rule. |
| D6 | Sessions: `Ρ : Roles k = Vec PartSet k`, `Session = Vec (Proc 0 0) k` indexed by process, `Partition Ρ` (an `owner` with two laws). **`⊢s` includes `Partition Ρ`** as a conjunct. | `Ρ` is static. Keeping the partition inside `⊢s` keeps every `Safety/` statement of the form `⊢s M ∶ G → …`. Preservation needs it: with two owners of `P`, the second is "uninvolved" in `P`'s step but cannot `t/unskip` across it. |
| D7 | The checker is keyed by role set (`Env Ps`, `Probing Ps`). It decides `Acts`, `Focus`, the syntactic premises, and `Partition Ρ`. | It decides the new rules and nothing else. `WBGraph`, `buildG` and `WBNet` are unchanged. |
| D8 | **Internal communication is hidden** (§5). A step all of whose participants belong to one process is *silent* for that process, like a step of others: `skip`, `t/unskip`, `Wait` and `Focus`'s runs all go through it. Preservation matches a session step with a weak step `G =< α >=> G′`. | A process `{P,Q}` implementing `P ⟶ Q . Q ⟶ R` writes only its send to `R`. The typing quantifies over all internal branches, like `skip`, so it stays syntax-directed. |
| D9 | **A compatibility layer** keeps the single-role API (§3.3): `_◂_` becomes a function `P ◂ Pr = ⁅ P ⁆ ◃ Pr`, the top-level `Session`/`⊢s_∶_` are the `singletons` instance, and `tc?`/`typecheck`/`typecheckSession` keep their types. | Examples and API-level tests compile unedited. Tests that build derivations or call checker internals by hand get mechanical `P ↦ ⁅ P ⁆` edits (§13). |

**Names.** The new operators are `_◃_`, `_∈αs_`/`_∉αs_`, `_idle-in_`, `_∈T*_`,
`_-[¬*_]->*_` and `_=<_>=>_`. The starred ones are starred because the role-level
`_∈T_`/`_-[¬_]->*_` stay in scope through `MPST`. The new identifiers are `Acts`, `Focus`,
`Internal`, `Silent`, `Ext`, `Outward`, `Hidden`, `Roles`, `Partition`, `owner`, `Meets` and
`singletons`. The syntax adds `send`, `recv`, `_▹_!_<_>∙_` and `_▹Σ_？·_`; `▹` and `◃` are
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

  -- Every participant of `β` is one of `Ps`: a communication inside the process.
  Internal : PartSet → Action → Set ; Internal Ps β = ∀ X → X ∈α β → X ∈ Ps
  -- `Ps` takes no part in `β`, or `β` is internal to `Ps`: the process does nothing.
  Silent   : PartSet → Action → Set ; Silent Ps β = Ps ∉αs β ⊎ Internal Ps β
  -- The complement: `Ps` takes part, together with someone outside.
  Ext      : PartSet → Action → Set ; Ext Ps β = Ps ∈αs β × ¬ Internal Ps β
  internal? silent? ext? ¬silent→ext ext→¬silent                -- decidable: `N` is finite

  _idle-in_   : PartSet → Behav → Set ; Ps idle-in G = ∀ {α G′} → G -< α >-> G′ → Silent Ps α
  _∈T*_       : PartSet → Behav → Set
  Ps ∈T* G = ∃[ αs ] ∃[ G′ ] (G -[ αs ]-> G′) × Any (Ext Ps) αs
  _-[¬*_]->*_ : Behav → PartSet → Behav → Set
  G -[¬* Ps ]->* G′ = ∃[ αs ] (G -[ αs ]-> G′) × All (Silent Ps) αs

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

  -- Wherever the process can be while silent, every external step it takes part in
  -- involves `P`.
  Focus : PartSet → Part → Behav → Set
  Focus Ps P G = ∀ {G′ β G″} → G -[¬* Ps ]->* G′ → G′ -< β >-> G″ → Ext Ps β → P ∈α β

  -- The assignment-level notions.
  module Sessions {k} (Ρ : Roles k) where
    Hidden : Action → Set ; Hidden β = ∃[ j ] Internal (lookup Ρ j) β

    infix 4 _=<_>=>_
    data _=<_>=>_ : Behav → Action → Behav → Set where
      w/step : G -< α >-> G′                              → G =< α >=> G′
      w/hide : G -< β >-> G′ → Hidden β → G′ =< α >=> G″  → G =< α >=> G″
```

Lemmas. Each set-level lemma is proved by picking the witness role, applying the
role-level lemma, and mapping `All`. The silent step case splits on `Silent` (§5.3):

```agda
in/αs* in/later* skip/refl* tr¬/step* skip/one* skip/cat* ∈~* idle/bisim skip/bisim*
¬*⇒¬  : R ∈ Ps → G -[¬* Ps ]->* G′ → (no internal step of the run involves R) → G -[¬ R ]->* G′
                                                                  -- weaken to one role; §6.4 discharges the side condition
ext/comm : comm α ≡ comm β → Ext Ps α → Ext Ps β                    -- `comm-∈α` both ways
ext-silent/⋄   : G -< α >-> Gα → G -< β >-> Gβ → Ext Ps α → Internal Ps β → α ⋄ β
skip/advance*  : G -[¬* Ps ]->* G′ → G -< α >-> Gα → Ext Ps α → ∃[ G′α ] G′ -< α >-> G′α × Gα -[¬* Ps ]->* G′α
branch/before* : G -[¬* Ps ]->* G′ → R ∈ Ps → Recv γ R → Ext Ps γ → G -< γ >-> Gᵢ → G′ -< γ′ >-> Gⱼ′
               → comm γ′ ≡ comm γ → ∃[ Gⱼ ] G -< γ′ >-> Gⱼ × Gⱼ -[¬* Ps ]->* Gⱼ′
focus/cat : Focus Ps P G → G -[¬* Ps ]->* G′ → Focus Ps P G′      -- stability under `t/unskip`
focus/~   : G ~ G′ → Focus Ps P G → Focus Ps P G′                 -- runs by `skip/bisim*`, steps by `~L`
focus/⁅⁆  : Focus ⁅ P ⁆ P G                                      -- `x∈⁅y⁆⇒x≡y`

-- in `Sessions Ρ`
weak/step  : G -< α >-> G′ → G =< α >=> G′
weak⇒run   : G =< α >=> G′ → ∃[ ιs ] G -[ ιs ++ α ∷ [] ]-> G′ × All Hidden ιs
weak/singletons : Synchronous B → G =< α >=> G′ ⇔ G -< α >-> G′  -- under `singletons`
```

`skip/advance*` and `branch/before*` are `-aux` recursions on the run, exactly like
`Behav.agda`'s: the run is a curried argument and is never repacked. An idle step uses
`active-inactive/⋄`, `no-new-branch/step`, `recv-idle/all` at the witness role, with
`∉αs→∉α`. An internal step uses `ext-silent/⋄` (§5.3).

`weak/singletons` holds because `Hidden` is empty under `singletons`: `Internal ⁅ P ⁆ β`
needs every participant of `β` to be `P`, and `balanced` gives `β` a nonempty receiver set
without `P`. This is the only place the conservativity argument needs `Synchronous`.

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
- `MPST` does the same for `⊢s_∶_`.
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

The condition reads: wherever the process can be while silent, every external step it
takes part in involves the acting role. It is a premise of both communication rules, at the
rule's own state. It quantifies over silent runs because `t/unskip` moves derivations
forward (`focus/cat`). Internal steps are excluded: they make no one wait (§5.5).

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

### 4.3 Where each premise is used

| premise | used by |
|---|---|
| `Acts` | everywhere a role is needed. `acts-unique` identifies the semantics' role with the typed one (`Preservation`, `Progress`). |
| `Outward Ps Qs` (send) | the step is external, so it is not also skipped (§5); `Focus` and `Dom` apply to it. |
| `Q ∉ Ps` (receive) | `Progress.sender/head-progress`: the sender's process, at a receive of one of its own roles targeted by its own role's multicast, is absurd. Also: the received step is external. |
| `Focus` | `Progress` only: `sender/head-progress` and `recv-head` (§9.3). `AlgNorm` carries it (`focus/cat`, `focus/~`) and never inspects it. |
| `Partition` (in `⊢s`) | `Preservation.⊢s-comm-update` (uninvolved processes), `⊢s/hidden` (§9.1), and `Progress` (`owner`). |

`j ≢ j₀` for receivers is now part of `s/comm` (`recvs`), not a typing premise: the old
`Apart Ps Qs` is gone.

Preservation and termination need no side condition beyond `Partition`. With the role
named, a receive's `conts` are today's `conts` at that role, and today's argument
(`recv-overlap` + `no-new-branch/step` at the role) covers every message the semantics lets
that process take.

### 4.4 What `Focus` rejects

**Exactly the linearisations of concurrent actions of the process's own roles.** Suppose
`Focus Ps P G` fails for a process typed at an action as `P`. Then there is a silent run
`G → G′` and an external step `β` at `G′` with a role `P′ ∈ Ps` and without `P`.
`skip/advance*` keeps `P`'s action `α` enabled at `G′`; `active-inactive/⋄` gives `α ⋄ β`;
`step-diamond` commutes them. So the graph leaves `α` and `β` unordered, and the process
ordered them. Conversely, any such reachable pair makes `Focus` fail. So:

- where the graph orders the roles' external actions (`Rec2Buy`'s `{B,S}`), `Focus` holds
  whenever the naive rules do, and costs nothing;
- internal steps are never counted (§5.5), so interleaving them with anything is accepted;
- relative to the naive rules ("any linearisation"), `Focus` rejects the linearisations and
  nothing else.

**Which linearisations are safe.** Not all: (a) and (b) are linearisations. For two
concurrent external actions of one process, ordered "x before y":

| process order | against single-role peers | deadlocks against |
|---|---|---|
| send before send | safe | a process ordering the two *receives* the other way |
| receive before receive | safe | a process ordering the two *sends* the other way |
| send before receive | safe | the mirror image (b) |
| receive before send | safe | the mirror image (both wait at receives) |

A per-process judgment never sees the other process, so it may allow only a set of orders
that cannot close a wait cycle among themselves. One such set is **send before send, and
`Focus` for everything else**: a receiver with `Focus` is already at the receive of any
enabled step involving it, so a process holding one send behind another only ever waits for
a ready receiver. Written as a condition on sends: along silent runs, no role of `Ps`
receives in an external step that does not involve `P`. It is set aside for simplicity
(`FUTURE_WORK.md`). The other three orders can only be allowed by a global discipline,
such as a priority order on roles.

## 5. Hidden internal communication

### 5.1 The idea

A step `β` is **internal** to a process when every participant of `β` is one of its roles.
The process does nothing for it: no syntax, no session step. For typing, the process treats
`β` like a step of others. Its idle steps and internal steps together are its **silent**
steps (`Silent`, §2), and `skip/step`, `t/unskip`, `Wait` and `Focus`'s runs all range over
silent steps.

For the graph, internal steps are what τ is for weak bisimulation: `Hidden β` says `β` is
internal to some process of `Ρ`, and `G =< α >=> G′` is some hidden steps followed by `α`.
Session steps are matched by weak steps (§9.1).

### 5.2 What the typing means

`skip/step`'s `ktd` quantifies over **all** silent successors, internal ones included. So a
process must behave correctly whichever internal branch the graph takes:

- an internal choice whose branches need different behaviour is **rejected**, for example
  `P ⟶ {Q} # 0 . Q ⟶ {R} # 0` against `P ⟶ {Q} # 1 . Q ⟶ {R} # 1` with `{P,Q}`: no
  single send to `R` types in both branches. The process's code never says which internal
  branch it takes, so it cannot depend on it;
- internal choices that do not matter, and internal loops (`skip/cycle`), are accepted.

`t/end`/`a/end` need `¬ Ps ∈T* G`: no *external* step involving `Ps` is reachable. Pending
internal steps may remain.

### 5.3 The theory lemmas still hold

`skip/advance*` needs: an external step `α` of `Ps` survives a silent step `β`. For an idle
`β` this is today's argument at a witness role. For an internal `β`, `ext-silent/⋄` shows
`α ⋄ β` from `recv-overlap` alone:

- `α ≢ β`: `α` has a participant outside `Ps`, and `β` has none.
- A receiver `Y` of `α` is not in `β`: else `recv-overlap` gives `comm α ≡ comm β`, and
  `ext/comm` makes `β` external, which is absurd. Symmetrically for receivers of `β`.

Then `step-diamond` commutes them. `branch/before*` works the same way: a receiving role `R`
of an external `γ` is not in an internal `β` (by `recv-overlap` and `ext/comm`), so
`recv-idle/all` and `no-new-branch/step` apply. No axiom is added, and `Behav.agda` is
untouched.

### 5.4 The weak step

```agda
Step G (just α) G′ = G =< α >=> G′          -- was `G -< α >-> G′`
Step G nothing  G′ = G ≡ G′
```

It is inductive, not a list with an `All`, so lemmas that walk hidden steps recurse on
`w/hide` directly (the curried-run pattern). There are no hidden steps after `α`: processes
skip those themselves. Under `singletons` there are no hidden steps at all
(`weak/singletons`).

### 5.5 Interaction with `Focus`

`Focus` counts only external steps. An internal step makes no one wait: the process never
performs it, and no other process takes part. So it cannot be part of a wait cycle.
Everywhere `Progress` uses `Focus`, the step it is applied to has its sender in another
process, so the exemption never meets the proof.

### 5.6 Fallback

If `hidden/first` (§9.2) cannot be proved, internal communication is made explicit instead.
The send stays in the syntax (`P ▹ {Q} ! i < E >∙ Pr` with `Qs ⊆ Ps`), `s/comm` fires it with
no receiver process, and the session step is labelled as usual. Then there are no hidden
steps, `Step` is unchanged, and `Focus` exempts fully internal sends. The typing loses the
"internal steps are invisible" property but keeps everything else in this plan.

## 6. Typing

### 6.1 `Typing/Declarative.agda`

```agda
t/send :
  ∀ {Ps r P Qs I}{i : Fin (suc I)}{G G′ Pr E S}
  → (acts : Acts Ps r P)
  → (out  : Outward Ps Qs)
  → (foc  : Focus Ps P G)
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

skip/step  : … (na : Ps idle-in G) …                        -- silent, §5
skip/cycle : lu Ξ X ~ G → Ps ∈T* G → …
t/unskip   : (tr : G -[¬* Ps ]->* G′) → …
t/end      : ¬ Ps ∈T* G → Γ & Δ ⊢p Ps ◃ ∅ ∶ G
t/if t/rec t/var                                            -- `P ↦ Ps`, otherwise unchanged

module Sessions {k} (Ρ : Roles k) where                     -- opens `Proc.Sessions Ρ`
  ⊢s_∶_ : Session → Behav → Set
  ⊢s M ∶ G = Partition Ρ × (∀ j → [] & [] ⊢p lookup Ρ j ◃ lookup M j ∶ G)
open Sessions singletons public using (⊢s_∶_)                 -- compatibility, §3.3
```

### 6.2 `Typing/Alg.agda`

`Post`, `Dom` and `Offers` are indexed by a role, as today: `Post P e 𝒮`, `Dom P e`,
`Offers Q R I` at the acting role. Everything that walks is indexed by the role set, and
walks silent steps: `Front Ps`, `Reach Ps`, `Wait Ps`, `Unskip Ps`, `Ended Ps`, `_⇝[ Ps ]_`
and `WaitV Ps`.

```agda
Foc : PartSet → Part → States δ ; Foc Ps P (_ , s) = Focus Ps P s

a/send : (acts : Acts Ps r P) → (out : Outward Ps Qs) → let e = (! Qs) # i < S > in
         (etd : Γ ⊢e E ∶ S)
       → (rdy : 𝒮 ⊆ Wait Ps (Dom P e ∩ Foc Ps P))
       → (td  : Γ ⊢a Ps ◃ Pr ∶ Post P e (Front Ps 𝒮))
       → Γ ⊢a Ps ◃ send r Qs i E Pr ∶ 𝒮
a/recv : (acts : Acts Ps r R) → (ext : Q ∉ Ps)
       → (rdy : 𝒮 ⊆ Wait Ps (Offers Q R I ∩ Foc Ps R))
       → (conts : ∀ {j U} → let e = (？ Q) # j < U > in
                  Satisfiable (Post R e (Front Ps 𝒮)) → (U ∷ Γ) ⊢a Ps ◃ lu Br j ∶ Post R e (Front Ps 𝒮))
       → Γ ⊢a Ps ◃ recv r Q Br ∶ 𝒮
a/if a/end a/var a/rec                                      -- `P ↦ Ps`
```

`Act Ps` uses `Ext Ps α`. `waitLeaf` takes a step with `Ext Ps α` against
`na gr : Silent Ps α` (`ext→¬silent`). The following are renamings: `alg/mono`,
`after/mono`, `waitV/*`, `waitActive`, `waitStep`, `at/if-inv` and `at/rec-guarded`.
`at/send-inv`/`at/recv-inv` additionally return `Acts`, `Outward`/`ext`, and the leaf's
`Focus`.

### 6.3 `AlgEquiv`, `MainLeaf`, `Properties`, `AlgDeclarative`, `Substitution`

These are `P ↦ Ps` ports, with `Silent` for idle.

- `td/bisim`'s communication cases transport `foc` by `focus/~`. `t/unskip` uses
  `skip/bisim*`, and `t/end` uses `∈~*`.
- `alg⇒typing` hands the leaf's `Focus` and the rule's `acts`/`out`/`ext` to the
  declarative rule.
- `findRun` uses `¬silent→ext`.
- The substitution lemmas pass the three new premises through unchanged. They are
  state-free, apart from `Focus`, which is about `G` and not about the process.

### 6.4 `AlgNorm.agda` — `⊢p → ⊢a`

`Walk`, `Base`, `waitFind`, `waitFollow`, `Advances`, `Typed` and `Entry` keep their shape.
The families change as follows:

- **`SendL`/`SendE`** add `Focus Ps P` for the `P` of the `t/send` they came from. `P` is
  fixed by `acts` and `acts-unique`, since the process is fixed. `sendL/adv` uses
  `skip/advance*` (the step is external by `out`), and `focus/cat` along the silent step.
  `sendAt` is today's proof: `send-det` at `P`, then `step-deterministic`.
- **`RecvL`** adds `Focus Ps R`. `recvL/adv` is today's proof at role `R`: `recv/same-comm`
  and `branch/before` on the idle part of the run (weakened by `¬*⇒¬`), with
  `branch/before*` for the whole silent run that `t/unskip` needs, and `focus/cat`.
  Today's proof uses role-level `branch/before` on a `¬ R` run. A silent run is one: `R`
  receives externally, and by §5.3 no internal step involves such an `R`. So `¬*⇒¬`
  extends to silent runs under that hypothesis.
- **`typing⇒alg`**, send and receive: `a/send`'s `rdy` maps the `SendE` leaf to
  `Dom P e ∩ Foc Ps P`; `acts`/`out`/`ext` come from any leaf via `waitFind` (they are
  state-free).
- `endL/adv`, `after/adv`, `recG/adv` and `ifE/adv` are renamings.

`typing⇒alg`/`td⇒at` keep their current hypothesis (`sync`) and nothing else.

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
- `focus/⁅⁆`: `Focus` always holds;
- `Silent ⁅ P ⁆ β` is `P ∉α β`, and `Ext ⁅ P ⁆ β` is `P ∈α β`, because `Internal ⁅ P ⁆ β`
  is empty under `balanced`; so `idle-in`, `_∈T*_` and silent runs are today's relations;
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
- **`⊢s/hidden : ⊢s M ∶ G → G -< β >-> G′ → Hidden β → ⊢s M ∶ G′`.** `β` is internal to one
  process `j_β`, so it is silent for `j_β` (internal) and for every other process (idle: by
  partition, none of their roles is in `β`). Every process takes `t/unskip (skip/one* …)`.
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
  - The sender's `Wait` leaf is at role `P′` with `Acts (lookup Ρ j₀) r₀ P′`, and
    `acts-unique` against `s/comm`'s `Acts` gives `P′ ≡ P`. Then `send-action` at `P`, as
    today.
  - Each receiver process `j` listens as `R` with `Acts (lookup Ρ j) (rs j) R` and `R ∈ Qs`.
    Its leaf is found by `waitLeaf`, since `j` takes part in `α` externally. `acts-unique`
    makes the leaf's role `R`. Its `conts` take the step at `R`, obtained from `ev-recv`
    with `R ≢ P` (by partition). This is `recv/cont` at role `R`, as today.
- `comm/ready` keeps today's shape: one sender tree, and one receiver tree per role
  `R ∈ Qs` outside the sender's process, taken from `owner R`'s process.
  - In `receiver-step`, the leaf's step has `P ∈α β` by `recv-sender`, which makes the
    silent sender process take part; that is the contradiction.
  - In `multicast-idle`, a role in `γ` is `P` or some `R ∈ Qs`, both in silent processes.

  **Caution:** the receiver tree for `R` is `owner R`'s process's tree, and its leaf family
  is at that process's listening role, which need not be `R`. `recv-sender` at the
  listening role still gives `P ∈α β`, and that is all `receiver-step` uses.

### 9.2 `hidden/first` — the new lemma (proof risk)

```agda
hidden/first : ⊢s M ∶ G → M [ just α ]⇒ M′
             → ∃[ G₁ ] (G -[ ιs ]-> G₁ with All Hidden ιs) × ⊢s M ∶ G₁ × ∃[ G′ ] G₁ -< α >-> G′
```

(stated with an inductive hidden-run relation, like `_=<_>=>_` without the final step).

**Why it is needed.** The sender's `Wait` leaf is reached from `G` by a run silent for its
own process. That run may contain its own internal steps, which must be kept (`Q⟶R` really
comes after `P⟶Q`), and steps among other processes, which the semantics has not
performed.

**Sketch.** Induction on the sender's `WaitV` derivation, keeping `⊢s M ∶ H` at the current
state `H` (by `⊢s/hidden`):

1. *Leaf at `H`:* the send is enabled at `H`; `send-action` makes it `α`.
2. *Skip at `H` with a hidden successor on the way to a leaf:* take it, keep typing by
   `⊢s/hidden`, recurse on the sub-derivation.
3. *Skip at `H` where the leaf lies only behind a step `β` among other processes:* show that
   `β` shares no role with `α`, then pull `α` back before `β` with `no-new-comm/step`. If `β`
   shared a role with `α`, it would be a receiver's role `Z ∈ Qs` (the sender's process is
   silent in `β`). `Z`'s process is at its receive as `R ∈ Qs` with `Focus`, and `β` is
   external for it (else it would be hidden), so `R ∈α β`; `recv-overlap` at `R` against its
   `Offers` step makes `β`'s sender `P`, contradicting that the sender is silent in `β`.

**Open points.** (i) Case 2 must pick a successor from which a real leaf is reachable; a
`WaitV` branch can instead end at a cycle (`skip/cycle`), for example an internal loop. The
existence of a leaf-reaching branch is part of the lemma. (ii) Case 3 pulls `α` back over
one step; over several, the receivers' typing at intermediate states needs the same
argument inductively. If either fails, use §5.6.

### 9.3 Progress

- `session/status` recurses over `tabulate id : Vec (Fin k) k`.
  `ss/end : ∀ i → ¬ lookup Ρ (lookup js i) ∈T* G`, and `inactive/done` needs only that.
- **Hidden steps first.** If the only steps enabled at `G` are hidden, the session state
  moves along them by `⊢s/hidden` to a state where an external step is enabled, and the
  argument below runs there. This uses the same normalisation as §9.2 (open point (i)),
  measured by the `WaitV` derivation of a process that is not done.
- `step/progress`: `balanced gr` gives the sender `P` of an external enabled step `gr`. Its
  process is `owner P`, which takes part in `gr` through `P` (`owner-∈`).
- `sender/head-progress`, with the head acting as `r` under `Focus`, so `r ∈α gr`:
  - **Send.** `r` cannot receive in `gr`: that would give one `comm` with `r`'s own send, by
    `recv-overlap` at `r`. So `r` is `gr`'s sender, `P`. The leaf's own step `α′` then
    drives `receivers/progress`, as today.
  - **Receive from `Q`.** Either `r ≡ P` (sends in `gr`, receives in `β`), which is absurd
    by `recv-overlap` at `P`. Or `r ∈ Qs` receives from `P` in `gr`: `recv-overlap` at `r`
    makes `？ Q ≡ ？ P`, so `P` would be both in `Ps` (`owner`) and not (`ext`), which is
    absurd.
- `receivers/progress` collects over processes `j ≢ j₀` meeting `Qs′` (`fin-collect` over
  `Fin k`). `recv-head` on `j`, whose head acts as `r` with `Focus`: `α′` involves `j` and
  is external for it (its sender is in `j₀`), so `r ∈α α′`; and `r ≢ P′` by partition, so
  `r` receives from `P′` in `α′`.
  - **At a send**: `recv-overlap` at `r`, which is absurd.
  - **At a receive from `Q″` of arity `I`**: `recv-overlap` at `r` gives one `comm`.
    `comm-ev` and `ev-inv` give `Q″ ≡ P′`, and `step-arity-det` **at `r`** gives the arity.
    `r ∈ Qs′` by `ev-inv`, which supplies `recvs`' second component.
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
  - `Env Ps`:
    - `ok Ps s` holds when every role of `Ps` is inactive at `s` (from the existing
      `active? G R s`), apart from internal edges;
    - `G¬ Ps` keeps the silent edges: `silent? Ps (proj₁ e)`;
    - `inT?` is reachability of an `ext? Ps` edge, over the rows shared through `Shared`;
    - `act?` and `idle` use `ext?`/`silent?`.
  - `focus? Ps P s`:
    `FinP.all? λ s′ → unskip? s s′ →-dec all-out? s′ (λ β _ → ext? Ps β →-dec P ∈α? β)`.
    It is tabulated per state (`memoB`), from the silent rows that `Unskip?` already needs.
  - `send-case`/`recv-case` resolve the role once by `acts?`, test `Outward`/`ext`
    syntactically, and use `Dom? P e`/`Offers? Q R I` as today, intersected with `focus?`.
  - `Probing (Ps : PartSet) (E : Env Ps)`. The `probe` clauses match `send r …` and
    `recv r …`. `alg-empty?` checks the state-free premises.
  - `Graph/Reachability.agda` is untouched.
- **`Check/TypeCheck.agda`.**
  `tcAs? : (Γ Δ)(Ps : PartSet)(Pr)(s) → Dec (Γ & Δ ⊢p Ps ◃ Pr ∶ s)`, and
  `tc? Γ Δ P = tcAs? Γ Δ ⁅ P ⁆` (same type as today, via `_◂_`).
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
2. `Definitions/Typing/Roles.agda`: §2, including `ext-silent/⋄` and `weak/singletons`.
   It compiles against the unchanged theory.
3. **Spike `hidden/first` (§9.2)** in a scratch file against `Roles.agda` and a stub
   `⊢s`, before porting anything else. If it does not go through, switch to §5.6 now.
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
  3. An internal choice whose branches need different sends to `R`: rejected. An internal
     choice whose branches agree: accepted. An internal loop before an external send:
     accepted.
  4. A partly internal multicast `P ⟶ {Q,R}` with `{P,Q}`: accepted; `R`'s process must be
     at its receive.
  5. `Rec2Buy` with `{B,S}` as one process (`B ▹ …`/`S ▹ …` on each action), against the
     unchanged graph: accepted.
  6. §4.1(a) and §4.1(b): both graphs pass `wellBehaved?`/`synchronous?`, and both
     sessions are rejected (`Focus`).
  7. The safe send linearisation of §4.4: rejected. This is recorded as the known cost.
  8. A `Ρ` that is not a partition: rejected (`partition?`).
  9. An unannotated action in a two-role process: rejected (`Acts`).
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
| `Tests/WaitNotSkip.agda` | `WaitV P …`, `wait⇒skip P …` | `⁅ P ⁆` |
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
  them to `full`/`none`.
- **`_∈αs_`/`_∉αs_` unfold through `lookup`.** Pin `{Ps}{α}`, as for `∉α→¬∈α` today.
- **Silent, not idle.** Every set-level "does nothing" is `Silent`. `_∉αs_` appears only
  inside `Silent` and in the partition arguments of §9.1.
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
- `focus/⁅⁆` and `weak/singletons` are proved, and the conservativity claim is witnessed
  by the untouched examples.
- `Tests/MultiRole.agda` compiles with every decision forced.
- `Safety.agda`'s only new parameter is `{k}(Ρ : Roles k)`, and `preservation`'s only
  change is `Step`.
