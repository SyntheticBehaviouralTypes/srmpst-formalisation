# PLAN.md — one process, many roles

*Written 2026-09-28 on `set-typing`, after the multicast rework (`1b7f892`, `770b67f`).
Nothing below is implemented yet.*

**Ground rule.** Only three things are redesigned: the **process syntax**, minimally (an
optional acting role on sends and receives, §3.1), the **reduction semantics of sessions**
(`Definitions/Proc.agda`), and the **typing rules**, declarative (`Typing/Declarative.agda`)
and algorithmic (`Typing/Alg.agda`). The behavioural theory (`Behav.agda`: `BTheory`,
`WellBehaved`, `Synchronous`), actions (`Actions.agda`), the graph model and its decision
procedures (`Definitions/Graph/*`) do **not** change. One LTS still typechecks any number of
sessions, with any number of processes: nothing about the role assignment reaches the theory.
Everything downstream (`⊢a ⟺ ⊢p`, `Safety/`, `Check/`) is re-proved against the same axioms
and keeps its statements, up to the new shape of processes and sessions.

> **⚠ Soundness note — read §4.** Generalising the rules from `P : Part` to `Ps : PartSet`
> and nothing else **loses progress**: §4.1 gives two deadlocking sessions that the naive
> rules accept. Preservation and termination survive. The fix is one side condition,
> `Focus`, on `t/send`/`t/recv` and `a/send`/`a/recv` (§4.2). It is trivially true for a
> single role, so every existing derivation, example and test carries over unchanged.
> §4.4 records what `Focus` rejects that is actually safe.

## 0. The change

A named process implements a **set** of roles: `Ps ◂ Pr` with `Ps : PartSet`. A session is
a vector of processes over a static role assignment whose sets partition `Fin N`.

**Semantics.** A multicast still happens in one step; what must be ready is every *role*,
not every *process*. A process implementing several receivers of one multicast does **one**
receive.

**Syntax.** A send or receive may name the role of the process that performs it:
`A ▹ Qs ! i < E >∙ Pr`, `R ▹Σ Q ？· Br`. The unannotated forms `Qs ! i < E >∙ Pr` and
`Σ Q ？· Br` remain, and mean "the process's only role". So an unannotated action is legal
exactly in a single-role process, and every existing process is unchanged.

**Typing.** The communication rules are today's, at the acting role, plus the `Focus` side
condition. Everything else replaces `P` by `Ps`.

Graph: one step `R ⟶ {P,Q} # 0 < nat >`, then `end`.

```
{R} ◂ {P,Q} ! 0 < 3 >∙ ∅   ∥   {P,Q} ◂ P ▹Σ R ？· (∅ ∷ [])                              ⇒   ∅ ∥ ∅
{R} ◂ {P,Q} ! 0 < 3 >∙ ∅   ∥   {P} ◂ Σ R ？· (∅ ∷ [])   ∥   {Q} ◂ Σ R ？· (∅ ∷ [])      ⇒   ∅ ∥ ∅ ∥ ∅
```

Role assignments `[{R}, {P,Q}]` and `[{R}, {P}, {Q}]`; both sessions take the one step. In
the first, the receive is annotated with `P`; `Q ▹Σ R ？·` would do equally well. The
annotation says which role advances; every role of the process that the multicast targets
advances with it.

## 1. Decisions

| # | decision | why |
|---|---|---|
| D1 | Sends and receives carry `Maybe Part`: the acting role, or `nothing` for "the only role". The existing syntax is kept as **pattern synonyms** for `nothing` (§3.1). | Tests and examples construct processes only, so they are untouched. Proofs match on the real constructors; that change is mechanical. Checked in a scratch file: both surface forms, `{I}` implicit, fixity `infixr 8`, and matching on constructors and on synonyms. |
| D2 | The acting role is resolved by `Acts Ps r P`: `r ≡ just P × P ∈ Ps`, or `r ≡ nothing × Ps ≡ ⁅ P ⁆`. The rules and `s/comm` both use it. | `Acts` is functional (`acts-unique`), so the role the semantics fires and the role the typing checked are the same, with no argument. |
| D3 | The communication rules keep today's step premise **at the acting role**: `G -<[ P ↦ e ]>-> G′`, from `Behav.agda`, unchanged. | "Send typing does not change"; receive typing is today's, at one role. No new step relation. |
| D4 | One new premise per communication rule, **`Focus Ps P G`** (§4.2), plus two syntactic ones: a send's receiver set misses `Ps`, and a receive's sender is not in `Ps`. | §4. `Focus` is the only premise that mentions the theory. |
| D5 | The set-level vocabulary (`_∈αs_`, `_idle-in_`, `_∈T*_`, `_-[¬*_]->*_`, `Focus`, `Acts`) lives in a new `Typing/Roles.agda`, built from the unchanged role-level notions. | Ground rule. |
| D6 | Sessions: `Ρ : Roles k = Vec PartSet k`, `Session = Vec (Proc 0 0) k` indexed by process, `Partition Ρ` (an `owner` with two laws). **`⊢s` includes `Partition Ρ`** as a conjunct. | `Ρ` is static. Keeping the partition inside `⊢s` keeps every `Safety/` statement literally `⊢s M ∶ G → …`. Preservation needs it: with two owners of `P`, the second is "uninvolved" in `P`'s step but cannot `t/unskip` across it. |
| D7 | The checker is keyed by role set (`Env Ps`, `Probing Ps`). It decides `Acts`, `Focus`, the syntactic premises, and `Partition Ρ`. | It decides the new rules and nothing else. `WBGraph`, `buildG` and `WBNet` are unchanged. |

**Names.** The new operators are `_∈αs_`/`_∉αs_`, `_idle-in_`, `_∈T*_` and `_-[¬*_]->*_`.
They are starred because the role-level `_∈T_`/`_-[¬_]->*_` stay in scope through `MPST`.
The new identifiers are `Acts`, `Focus`, `Apart`, `Roles`, `Partition`, `owner` and `Meets`.
The syntax adds `send`, `recv`, `_▹_!_<_>∙_` and `_▹Σ_？·_`; `▹` is used nowhere today.
Throughout, `Ps` is a process's role set, `Qs` a multicast's receiver set, `Ρ` the
assignment, `r` an annotation, and `j`/`j₀` process indices.

## 2. `Definitions/Typing/Roles.agda` (new)

```agda
module Definitions.Typing.Roles {N}{B : BTheory N}(wb : WellBehaved B) where
  open MPST wb

  infix 4 _∈αs_ _∉αs_
  _∈αs_ : PartSet → Action → Set ; Ps ∈αs α = ∃[ R ] R ∈ Ps × R ∈α α
  _∉αs_ : PartSet → Action → Set ; Ps ∉αs α = ∀ R → R ∈ Ps → R ∉α α
  ∉αs→¬∈αs ¬∈αs→∉αs _∈αs?_ _∉αs?_ ∉αs→∉α ∈α→∈αs       -- pin `{Ps}{α}` at call sites

  _idle-in_   : PartSet → Behav → Set ; Ps idle-in G = ∀ {α G′} → G -< α >-> G′ → Ps ∉αs α
  _∈T*_       : PartSet → Behav → Set ; Ps ∈T* G = ∃[ R ] R ∈ Ps × R ∈T G
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

  -- A process's roles and a receiver set are apart (no self-multicast).
  Apart : PartSet → PartSet → Set ; Apart Ps Qs = ∀ R → R ∈ Ps → R ∉ Qs

  -- Wherever the process can be while idle, every step it takes part in involves `P`.
  Focus : PartSet → Part → Behav → Set
  Focus Ps P G = ∀ {G′ β G″} → G -[¬* Ps ]->* G′ → G′ -< β >-> G″ → Ps ∈αs β → P ∈α β
```

Lemmas. Each is proved by picking the witness role, applying the role-level lemma, and
mapping `All`:

```agda
in/αs* in/later* skip/refl* tr¬/step* skip/one* skip/cat* ∈~* idle/bisim skip/bisim*
¬*⇒¬  : R ∈ Ps → G -[¬* Ps ]->* G′ → G -[¬ R ]->* G′           -- weaken to one role
skip/advance*  : G -[¬* Ps ]->* G′ → G -< α >-> Gα → Ps ∈αs α → ∃[ G′α ] G′ -< α >-> G′α × Gα -[¬* Ps ]->* G′α
branch/before* : G -[¬* Ps ]->* G′ → R ∈ Ps → Recv γ R → G -< γ >-> Gᵢ → G′ -< γ′ >-> Gⱼ′
               → comm γ′ ≡ comm γ → ∃[ Gⱼ ] G -< γ′ >-> Gⱼ × Gⱼ -[¬* Ps ]->* Gⱼ′
focus/cat : Focus Ps P G → G -[¬* Ps ]->* G′ → Focus Ps P G′      -- stability under `t/unskip`
focus/~   : G ~ G′ → Focus Ps P G → Focus Ps P G′                 -- runs by `skip/bisim*`, steps by `~L`
focus/⁅⁆  : Focus ⁅ P ⁆ P G                                      -- `x∈⁅y⁆⇒x≡y`
```

`skip/advance*` and `branch/before*` are `-aux` recursions on the run, exactly like
`Behav.agda`'s: the run is a curried argument and is never repacked (CLAUDE.md). Each step
uses `active-inactive/⋄`, `no-new-branch/step`, `recv-idle/all` at the witness role, with
`∉αs→∉α`.

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
  _◂_ : PartSet → Proc γ δ → NProc γ δ                        -- was `Part`
```

Every function on `Proc` matches `send r Qs i E Pr` and `recv r Q Br`. This covers the
`Subst` functions, `MessageGuarded` (`mg/send`/`mg/recv`), `τ-depth/proc`, `guarded?` and
`probe`. A clause written with a pattern synonym covers `nothing` only, and coverage would
fail. `unfold/proc` and `done/proc` are otherwise unchanged.

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
      → (recvs : ∀ j → Meets (lookup Ρ j) Qs
               → M [ j ]= recv (rs j) P (Br j)
               × ∃[ R ] Acts (lookup Ρ j) (rs j) R × R ∈ Qs)  -- listening on a targeted role
      → M [ just (P ⟶ Qs # i < sort/value V >) ]⇒
          M [ j₀ ↦ Pr ∣ Qs ↦ (λ j → Subst.[ val V / zero ]e lookup (Br j) i) ]
    s/if/true s/if/false s/rec                                -- indexed by `j : Fin k`
  _[_]⇒+_ _τ⇒_ _⇒∞ _⇏∞ ; done M = ∀ j → done/proc (lookup M j) ; finished
```

A process meeting `Qs` receives **once**, as the role its receive names, and that role must
be one of the targeted ones. Every role of that process in `Qs` advances with it. If
`j₀` itself meets `Qs`, then `recvs j₀` would require a process that is at a send to be at a
receive, so no step fires. `Apart` (§5.1) makes sure typed processes never do this.

`Acts`, `Meets` and the session layer need `Data.Fin.Subset`; `Proc.agda` imports it
already. `Acts` is defined in `Proc.agda` (next to `Meets`) and re-exported by
`Typing/Roles.agda`, so the semantics does not import the typing layer.

## 4. The side condition

### 4.1 Two deadlocks under the naive rules

**The naive rules.** These are §5.1's `t/send`/`t/recv` *without* `Focus`. The semantics is
§3's, and `⊢s M ∶ G = Partition Ρ × ∀ j → …`. Both graphs below are finite. Every terminal
state is the unique `ended`, and no two states are bisimilar. `Nonempty Qs` and `P ∉ Qs`
hold on every edge. `Tests/MultiRole.agda` should run both graphs through
`wellBehaved?`/`synchronous?`; the checks by hand are below.

#### (a) An orphan message

Roles `Q R R″ Z`, and assignment `Ρ = [ {Q} , {R,R″} , {Z} ]`.

```
u  --Q ⟶ {Z}  # 0<unit>-->  v        v  --Q ⟶ {R}  # 0<nat>-->   ended
u  --Q ⟶ {R}  # 0<nat>-->   w₁       v  --Q ⟶ {R″} # 0<bool>-->  ended
w₁ --Q ⟶ {Z}  # 0<unit>-->  ended
```

**Well-behaved and synchronous.**

- `recv-overlap`: the receivers at `u` are `Z` and `R`, and at `v` they are `R` and `R″`.
  None of them takes part in the other step.
- `step-deterministic`: every state's actions are pairwise distinct.
- `step-sort-det` and `step-arity-det`: each receiver has one label at one sort per state.
- `no-new-branch/step`: after `β = Q⟶Z`, the only step at `v` with the `comm` of `u`'s
  `Q⟶R # nat` is itself. The step `Q⟶R″` has a different `comm`, so the axiom says nothing
  about it.
- `step-diamond`: `Q⟶Z ⋄ Q⟶R`, and the square closes at `ended`.
- `no-new-comm/step`: `Q⟶R″` is new at `v`, but `Q` takes part in `Q⟶Z`, which the axiom
  allows.

**Processes.**

```
Y = {Q}    ◂ {Z} ! 0 < val v/unit >∙ ({R″} ! 0 < val (v/bool true) >∙ ∅)
X = {R,R″} ◂ R ▹Σ Q ？· (∅ ∷ [])
W = {Z}    ◂ Σ Q ？· (∅ ∷ [])
```

**Naive derivations at `u`.**

- `X`: `Acts {R,R″} (just R) R`, and `Q ∉ {R,R″}`. The step is `Q⟶R # nat` at role `R`.
  `conts` must cover every receive of `R` from `Q` at `u`; there is only that one, and its
  continuation types by `t/end` at `w₁`.
- `Y`: `t/send` for `Q⟶Z` at `u`, then `t/send` for `Q⟶R″` at `v`, then `t/end`.
- `W`: `t/recv` for `Q⟶Z`, then `t/end`.

So `⊢s [ Y , X , W ] ∶ u` holds.

**Reduction.**

1. `s/comm` for `Q⟶Z` gives `M₁ = [ {R″} ! … ∅ , X , ∅ ]`. It is typed at `v`, and `X`'s
   derivation is `t/unskip` of the one at `u`.
2. At `M₁`, `Y` sends to `{R″}`. The process meeting `{R″}` is `X`, but it listens as `R`,
   and `R ∉ {R″}`, so `recvs` fails.
3. No other step exists, and `M₁` is not `done`.

`progress` is false at `M₁`: the message to `R″` has no taker.

**Where the proof breaks.** In `Progress.receivers/progress`, the receiver process `X` of the
step `Q⟶R″` is active at `v` through `R″`. Its head acts as `R`. Today's `recv-head` concludes
from `recv-overlap` *at the head's role*, and `R` takes no part in `Q⟶R″`. The two steps
involve one process through two roles, and no axiom relates them.

**Annotating differently does not help.** `R″ ▹Σ Q ？·` does not type at `u`: nothing is
received by `R″` at `u`. And `t/skip` is unavailable, because `X` is active at `u`.

**Contrast with a single role.** Two receives involving one role `R` share a `comm` by
`recv-overlap`, and the later one existed before by `no-new-branch/step`. So a single-role
receiver always listens where the message arrives.

#### (b) A wait cycle

Roles `A B C D`, and assignment `Ρ = [ {A,D} , {B,C} ]`.

```
G₀ --A ⟶ {B} # 0<unit>--> G₁       G₁ --C ⟶ {D} # 0<unit>--> ended
G₀ --C ⟶ {D} # 0<unit>--> G₂       G₂ --A ⟶ {B} # 0<unit>--> ended
```

The graph is well-behaved and synchronous. `A⟶B ⋄ C⟶D` and the square commutes. The receivers
`B` and `D` take part in no other step, and there is one label per receiver per state. There
is no new branch and no new comm, and `G₁ ≁ G₂`.

```
X = {A,D} ◂ A ▹ {B} ! 0 < val v/unit >∙ D ▹Σ C ？· (∅ ∷ [])
Y = {B,C} ◂ C ▹ {D} ! 0 < val v/unit >∙ B ▹Σ A ？· (∅ ∷ [])
```

**Naive derivations.** `X` types by `t/send` for `A⟶B` at `G₀`, then `t/recv` for `C⟶D` at
role `D` at `G₁`, then `t/end`. `Y` types symmetrically through `G₂`. So
`⊢s [ X , Y ] ∶ G₀` holds.

**Stuck.** Both heads are sends. For `A⟶B`, the process meeting `{B}` is `Y`, and it is at a
send. For `C⟶D`, the process meeting `{D}` is `X`, also at a send. No `if` or `rec` is at
the head, so `progress` is false. This is the classical wait-for cycle: `X` needs `Y` at
`B`'s receive, and `Y` needs `X` at `D`'s receive.

**Where the proof breaks.** This is `recv-head`'s send case. `Y` is active at `G₀` through
`B`, and its head sends as `C`. Today the case is refuted by `recv-overlap` at the
receiver's role against its own head step. Here `B` takes no part in `C⟶D`, and the two
steps are independent, which is exactly what `step-diamond` is for.

**In general.** A multi-role process *linearises* independent steps that involve different
roles of its own. Two processes can linearise in orders that are incompatible. With one
role, any two steps involving that role at one state are related by `recv-overlap`, so no
wait-for edge can connect independent steps.

### 4.2 `Focus`

```agda
Focus Ps P G = ∀ {G′ β G″} → G -[¬* Ps ]->* G′ → G′ -< β >-> G″ → Ps ∈αs β → P ∈α β
```

The condition reads: wherever the process can be while idle, every step it takes part in
involves the acting role. It is a premise of both communication rules, at the rule's own
state. It quantifies over idle runs because `t/unskip` moves derivations forward
(`focus/cat`).

**It rejects both deadlocks.**

- In (a), the run `u --Q⟶Z--> v` is idle for `{R,R″}`, and at `v` the step `Q⟶R″` involves
  `R″` but not `R`.
- In (b), `C⟶D` at `G₀` involves `D` but not `A`, and `A⟶B` involves `B` but not `C`.

**It suffices for progress.** Let `j` be a process that some enabled step `α` involves, and
let its head act as `r` with `Focus`. Then `r ∈α α`, and `recv-overlap` at `r` does the
rest, as today:

- If `j` sends as `r` and `r` receives in `α`, the two steps have one `comm`, which is
  absurd.
- If `j` receives as `r` from `Q″`, the two steps have one `comm`. So `Q″` is `α`'s sender,
  and `step-arity-det` at `r` fixes the arity.

**For a single role it is free.** With `Ps = ⁅ P ⁆`, `Ps ∈αs β` already says `P ∈α β`
(`focus/⁅⁆`).

### 4.3 Where each premise is used

| premise | used by |
|---|---|
| `Acts` | everywhere a role is needed. `acts-unique` identifies the semantics' role with the typed one (`Preservation`, `Progress`). |
| `Apart Ps Qs` (send) | `Progress.receivers/progress`: a receiver process is not the sender's (`j ≢ j₀`). |
| `Q ∉ Ps` (receive) | `Progress.sender/head-progress`: the sender's process, at a receive of one of its own roles targeted by its own role's multicast, is absurd. |
| `Focus` | `Progress` only: `sender/head-progress` and `recv-head` (§7.2). `AlgNorm` carries it (`focus/cat`, `focus/~`) and never inspects it. |
| `Partition` (in `⊢s`) | `Preservation.⊢s-comm-update` (uninvolved processes), and `Progress` (`owner`). |

Preservation and termination need no side condition beyond `Partition`. With the role
named, a receive's `conts` are today's `conts` at that role, and today's argument
(`recv-overlap` + `no-new-branch/step` at the role) covers every message the semantics lets
that process take.

### 4.4 What `Focus` rejects that is safe

- **Linearising sends of different roles.** Against `A⟶B ∥ C⟶D`, the process
  `{A,C} ◂ A ▹ {B}! ∙ C ▹ {D}!` is rejected: at `G₀`, `C⟶D` involves `C` and not `A`. It is
  safe, because its receivers can only be at their receives. A finer condition for sends
  exists: no role of `Ps` receives along idle runs, and the send's continuation is
  quantified over all matching steps. It was considered and set aside for simplicity.
- **Linearising receives, or a receive against a send.** For example, against
  `A⟶B ∥ C⟶D`, `{B,D} ◂ B ▹Σ A ？· (D ▹Σ C ？· …)` is rejected. Whether it is safe depends
  on how the *senders* are implemented: it is safe against `{A}`, `{C}` and deadlocks
  against `{A,C} ◂ C ▹ {D}! ∙ A ▹ {B}!`. No per-process judgment against `G` can accept it.
  The framework already denies the same thing to a single role (`A⟶B ∥ C⟶B` is not
  well-behaved).

So a multi-role process is typed against the parts of the protocol that are already
sequential *from its own point of view*. For example, `Rec2Buy`'s `{B,S}` is accepted (§10),
while `RecMW`'s `{W1,W2}` on its diamondised graph is rejected.

## 5. Typing

### 5.1 `Typing/Declarative.agda`

```agda
t/send :
  ∀ {Ps r P Qs I}{i : Fin (suc I)}{G G′ Pr E S}
  → (acts : Acts Ps r P)
  → (apart : Apart Ps Qs)
  → (foc  : Focus Ps P G)
  → (gr   : G -<[ P ↦ (! Qs) # i < S > ]>-> G′)              -- today's premise
  → (etd  : Γ ⊢e E ∶ S)
  → (td   : Γ & Δ ⊢p Ps ◂ Pr ∶ G′)
  → Γ & Δ ⊢p Ps ◂ send r Qs i E Pr ∶ G

t/recv :
  ∀ {Ps r R Q I}{i : Fin (suc I)}{T G G′}{Br : Vec (Proc (suc γ) δ) (suc I)}
  → (acts : Acts Ps r R)
  → (ext  : Q ∉ Ps)
  → (foc  : Focus Ps R G)
  → (gr   : G -<[ R ↦ (？ Q) # i < T > ]>-> G′)              -- today's premise
  → (conts : ∀ {j U G″} → G -<[ R ↦ (？ Q) # j < U > ]>-> G″
           → (U ∷ Γ) & Δ ⊢p Ps ◂ lu Br j ∶ G″)               -- today's premise
  → Γ & Δ ⊢p Ps ◂ recv r Q Br ∶ G

skip/step  : … (na : Ps idle-in G) …
skip/cycle : lu Ξ X ~ G → Ps ∈T* G → …
t/unskip   : (tr : G -[¬* Ps ]->* G′) → …
t/end      : ¬ Ps ∈T* G → Γ & Δ ⊢p Ps ◂ ∅ ∶ G
t/if t/rec t/var                                            -- `P ↦ Ps`, otherwise unchanged

module Sessions {k} (Ρ : Roles k) where                     -- opens `Proc.Sessions Ρ`
  ⊢s_∶_ : Session → Behav → Set
  ⊢s M ∶ G = Partition Ρ × (∀ j → [] & [] ⊢p lookup Ρ j ◂ lookup M j ∶ G)
```

### 5.2 `Typing/Alg.agda`

`Post`, `Dom` and `Offers` are indexed by a role, as today: `Post P e 𝒮`, `Dom P e`,
`Offers Q R I` at the acting role. Everything that walks is indexed by the role set:
`Front Ps`, `Reach Ps`, `Wait Ps`, `Unskip Ps`, `Ended Ps`, `_⇝[ Ps ]_` and `WaitV Ps`.

```agda
Foc : PartSet → Part → States δ ; Foc Ps P (_ , s) = Focus Ps P s

a/send : (acts : Acts Ps r P) → (apart : Apart Ps Qs) → let e = (! Qs) # i < S > in
         (etd : Γ ⊢e E ∶ S)
       → (rdy : 𝒮 ⊆ Wait Ps (Dom P e ∩ Foc Ps P))
       → (td  : Γ ⊢a Ps ◂ Pr ∶ Post P e (Front Ps 𝒮))
       → Γ ⊢a Ps ◂ send r Qs i E Pr ∶ 𝒮
a/recv : (acts : Acts Ps r R) → (ext : Q ∉ Ps)
       → (rdy : 𝒮 ⊆ Wait Ps (Offers Q R I ∩ Foc Ps R))
       → (conts : ∀ {j U} → let e = (？ Q) # j < U > in
                  Satisfiable (Post R e (Front Ps 𝒮)) → (U ∷ Γ) ⊢a Ps ◂ lu Br j ∶ Post R e (Front Ps 𝒮))
       → Γ ⊢a Ps ◂ recv r Q Br ∶ 𝒮
a/if a/end a/var a/rec                                      -- `P ↦ Ps`
```

`Act Ps` uses `Ps ∈αs α`. `waitLeaf` takes a step with `Ps ∈αs α` against
`na gr : Ps ∉αs α`. The following are renamings: `alg/mono`, `after/mono`, `waitV/*`,
`waitActive`, `waitStep`, `at/if-inv` and `at/rec-guarded`. `at/send-inv`/`at/recv-inv`
additionally return `Acts`, `Apart`/`ext`, and the leaf's `Focus`.

### 5.3 `AlgEquiv`, `MainLeaf`, `Properties`, `AlgDeclarative`, `Substitution`

These are `P ↦ Ps` ports.

- `td/bisim`'s communication cases transport `foc` by `focus/~`. `t/unskip` uses
  `skip/bisim*`, and `t/end` uses `∈~*`.
- `alg⇒typing` hands the leaf's `Focus` and the rule's `acts`/`apart`/`ext` to the
  declarative rule.
- `findRun` uses `∉αs→¬∈αs`.
- The substitution lemmas pass the three new premises through unchanged. They are
  state-free, apart from `Focus`, which is about `G` and not about the process.

### 5.4 `AlgNorm.agda` — `⊢p → ⊢a`

`Walk`, `Base`, `waitFind`, `waitFollow`, `Advances`, `Typed` and `Entry` keep their shape.
The families change as follows:

- **`SendL`/`SendE`** add `Focus Ps P` for the `P` of the `t/send` they came from. `P` is
  fixed by `acts` and `acts-unique`, since the process is fixed. `sendL/adv` uses
  `skip/advance*`, and `focus/cat` along the idle step. `sendAt` is today's proof:
  `send-det` at `P`, then `step-deterministic`.
- **`RecvL`** adds `Focus Ps R`. `recvL/adv` is today's proof at role `R`: `recv/same-comm`
  and `branch/before` on the run weakened by `¬*⇒¬`, then `branch/before*` for the
  `¬* Ps` run that `t/unskip` needs, and `focus/cat`.
- **`typing⇒alg`**, send and receive: `a/send`'s `rdy` maps the `SendE` leaf to
  `Dom P e ∩ Foc Ps P`; `acts`/`apart`/`ext` come from any leaf via `waitFind` (they are
  state-free).
- `endL/adv`, `after/adv`, `recG/adv` and `ifE/adv` are renamings.

`typing⇒alg`/`td⇒at` keep their current hypothesis (`sync`) and nothing else.

## 6. What does not change

The following are untouched: `Definitions/Common.agda`, `Expr.agda`, `Actions.agda`,
`Behav.agda`, `Definitions/Graph/*`, `Utils/*` and `Stale/*`. In particular these stay
exactly as they are:

- `_∈T_`, `_not-active-in_`, `_-[¬_]->*_` and `_-<[_↦_]>->_`;
- every `WellBehaved`/`Synchronous` field and derived lemma;
- `wellBehaved?`, `synchronous?`, `WBNet`, `PFree` and `Disjoint`.

`git diff --stat` after the work touches only `Proc.agda`, `Typing/`, `Safety/`, `Check/`,
`Tests/` (new file only), `Examples/` (additions only), and the docs.

## 7. `Safety/`

```agda
module Safety {N}{B} (wb : WellBehaved B) (sync : Synchronous B) {k} (Ρ : Roles k) where
```

`Ρ` is the only new parameter. `Partition` comes out of `⊢s` (`part = proj₁ M⊢G`). The
statements of `preservation`, `preservation/τ*`, `progress` and `no-infinite-τ-reductions`
are unchanged in form. Each file opens `Proc.Sessions Ρ`, `MPST.Sessions Ρ` and
`Typing.Roles wb`.

### 7.1 Preservation

- `at/lookup` is unchanged. `⊢s-update`/`⊢s-comm-update` rebuild the pair.
- `⊢s-comm-update` cases on `j ≟ j₀`, then on `meets?`:
  - the sender becomes `Ptd`;
  - a receiver becomes `Rtd j`;
  - any other process becomes `t/unskip (skip/one* gr idle) (M⊢G j)`. Here
    `idle : lookup Ρ j ∉αs α` comes from `ev-other`: every role of `j` differs from `P`
    (`owner-unique`) and is not in `Qs` (else `j` would meet it).
- `preservation/comm`:
  - The sender's `Wait` leaf is at role `P′` with `Acts (lookup Ρ j₀) r₀ P′`, and
    `acts-unique` against `s/comm`'s `Acts` gives `P′ ≡ P`. Then `send-action` at `P`, as
    today.
  - Each receiver process `j` listens as `R` with `Acts (lookup Ρ j) (rs j) R` and `R ∈ Qs`.
    Its leaf at `G` is found by `waitLeaf`, since `j` is active through `R`. `acts-unique`
    makes the leaf's role `R`. Its `conts` take the step at `R`, obtained from `ev-recv`
    with `R ≢ P` (by partition). This is `recv/cont` at role `R`, as today.
- `comm/ready` keeps today's shape: one sender tree, and one receiver tree per role
  `R ∈ Qs`, taken from `owner R`'s process.
  - In `receiver-step`, the leaf's step has `P ∈α β` by `recv-sender`, which makes the idle
    sender process active; that is the contradiction.
  - In `multicast-idle`, a role in `γ` is `P` or some `R ∈ Qs`, both in idle processes.

  **Caution:** the receiver tree for `R` is `owner R`'s process's tree, and its leaf family
  is at that process's listening role, which need not be `R`. `recv-sender` at the
  listening role still gives `P ∈α β`, and that is all `receiver-step` uses.

### 7.2 Progress

- `session/status` recurses over `tabulate id : Vec (Fin k) k`.
  `ss/end : ∀ i → lookup Ρ (lookup js i) ∉T* G`, and `inactive/done` needs only that.
- `step/progress`: `balanced gr` gives the sender `P`. Its process is `owner P`, which is
  active through `P` (`owner-∈`).
- `sender/head-progress`, with the head acting as `r` under `Focus`, so `r ∈α gr`:
  - **Send.** `r` cannot receive in `gr`: that would give one `comm` with `r`'s own send, by
    `recv-overlap` at `r`. So `r` is `gr`'s sender, `P`. The leaf's own step `α′` then
    drives `receivers/progress`, as today.
  - **Receive from `Q`.** Either `r ≡ P` (sends in `gr`, receives in `β`), which is absurd
    by `recv-overlap` at `P`. Or `r ∈ Qs` receives from `P` in `gr`: `recv-overlap` at `r`
    makes `？ Q ≡ ？ P`, so `P` would be both in `Ps` (`owner`) and not (`ext`), which is
    absurd.
- `receivers/progress` collects over processes `j` meeting `Qs′` (`fin-collect` over
  `Fin k`). `j ≢ j₀` by `Apart`. `recv-head` on `j`, whose head acts as `r` with `Focus`:
  `α′` involves `j`, so `r ∈α α′`; and `r ≢ P′` by partition, so `r` receives from `P′` in
  `α′`.
  - **At a send**: `recv-overlap` at `r`, which is absurd.
  - **At a receive from `Q″` of arity `I`**: `recv-overlap` at `r` gives one `comm`.
    `comm-ev` and `ev-inv` give `Q″ ≡ P′`, and `step-arity-det` **at `r`** gives the arity.
    `r ∈ Qs′` by `ev-inv`, which supplies `recvs`' second component.
  - **At `if`/`rec`**: a τ step. **At `∅`**: absurd (`in/αs*`). **At `v`**: `Fin 0`.

  Then `s/comm j₀ send≡ acts e⇓v recvs`.

Never apply `step-arity-det`/`step-sort-det` across two different roles. Always go through
`comm α ≡ comm β` at one role first.

### 7.3 Termination

Sums range over `k`, and `sum/map-update<` is generic. `still-done`, `still-ended` and
`final-run/*` recurse over `Fin k`, and the `τ-depth` patterns use `send`/`recv`.

## 8. `Check/`

- **`Check/Alg.agda`.**
  - `Env Ps`:
    - `ok Ps s` holds when every role of `Ps` is inactive at `s` (from the existing
      `active? G R s`);
    - `G¬ Ps` filters edges by `Ps ∉αs? proj₁ e`;
    - `inT?` is `FinP.any? (λ R → R ∈? Ps ×-dec …)` over the role-level rows, which are
      shared through `Shared`;
    - `act?` and `idle` use `¬∈αs→∉αs`.
  - `focus? Ps P s`:
    `FinP.all? λ s′ → unskip? s s′ →-dec all-out? s′ (λ β _ → Ps ∈αs? β →-dec P ∈α? β)`.
    It is tabulated per state (`memoB`), from the `¬* Ps` rows that `Unskip?` already
    needs.
  - `send-case`/`recv-case` resolve the role once by `acts?`, test `Apart`/`ext`
    syntactically, and use `Dom? P e`/`Offers? Q R I` as today, intersected with
    `focus?`.
  - `Probing (Ps : PartSet) (E : Env Ps)`. The `probe` clauses match `send r …` and
    `recv r …`. `alg-empty?` checks the state-free premises.
  - `Graph/Reachability.agda` is untouched.
- **`Check/TypeCheck.agda`.**
  `tc? : (Γ Δ)(Ps : PartSet)(Pr)(s) → Dec (Γ & Δ ⊢p Ps ◂ Pr ∶ s)`;
  `tcSession? : ∀ {k}(Ρ : Roles k)(M)(s) → Dec (⊢s M ∶ s)`, which is
  `partition? Ρ ×-dec FinP.all? …`.
- **`Check/Core.agda`.** It gains `partition? : ∀ {k}(Ρ : Roles k) → Dec (Partition Ρ)`
  (for each role, exactly one `j`). `ProcessTyping` takes a `PartSet`, and `SessionTyping`
  takes `Ρ`.
- **`Check/Graph.agda`, `Check/Network.agda`.** They gain `typecheckSessionAs WR Ρ M` and
  `typecheckSessionNetAs w Ρ M`. The existing `typecheckSession WR M` becomes
  `typecheckSessionAs WR singletons M`, so its callers do not change. `typecheck WR P Pr`
  keeps its type via `⁅ P ⁆`, and a `typecheckAs WR Ps Pr` is added.

## 9. Order of work

Each step ends with `agda <file>` on the files it touched. Do not run `runall.sh` before
step 9. The tree must be hole-free after every step.

1. `Definitions/Proc.agda`: §3, including every `Subst` clause and the pattern synonyms.
2. `Definitions/Typing/Roles.agda`: §2. It compiles against the unchanged theory.
3. `Typing/Declarative.agda`: §5.1, including `MessageGuarded`'s patterns.
4. `Typing/Alg.agda`, `AlgEquiv.agda`, `MainLeaf.agda`, `Properties.agda` and
   `AlgDeclarative.agda`: §5.2–5.3.
5. `Typing/AlgNorm.agda`: §5.4. Then `Typing/Substitution.agda`.
6. `Safety/Preservation.agda`, `Progress.agda`, `Termination.agda` and `Safety.agda`: §7.
7. `Check/*` and `Check.agda`: §8.
8. `Tests/MultiRole.agda` (§10). Check that every existing test and example compiles
   **without edits**.
9. `git diff --stat` against §6. Then `./runall.sh --clean --tests` and
   `./runall.sh --CheckClosedProof`.
10. Docs (§10).

## 10. Tests and docs

- **Existing `Tests/` and `Examples/`:** no edits. Processes use the synonyms, sessions go
  through `typecheckSession` (= `singletons`), and `tc?`/`typecheck` take one role. If one
  of them needs an edit, the port is wrong somewhere.
- **New `Tests/MultiRole.agda`**, with every result forced:
  1. §0's two sessions: both accepted.
  2. `Rec2Buy` with `{B,S}` as one process (`B ▹ …`/`S ▹ …` on each action), against the
     unchanged graph: accepted.
  3. §4.1(a) and §4.1(b): both graphs pass `wellBehaved?`/`synchronous?`, and both
     sessions are rejected (`Focus`).
  4. The safe send linearisation of §4.4: rejected. This is recorded as the known cost.
  5. A `Ρ` that is not a partition: rejected (`partition?`).
  6. An unannotated action in a two-role process: rejected (`Acts`). A self-addressed
     multicast (`{P,P′} ◂ P ▹ {P′} ! …`): rejected (`Apart`).
- **`README.md`:** the process syntax (annotations and synonyms), `NProc`, `Roles`/`Session`,
  and the two rules with `Focus`.
- **`CLAUDE.md`:** `Typing/Roles.agda` in the layout, `Safety`'s `Ρ` parameter, the pattern
  synonym rule (§11), and the `_∈_` gotcha.
- **`FUTURE_WORK.md` §A:** `PFree` is per role set in the projection statement. Add an item
  for §4.4's finer send condition.

## 11. Gotchas specific to this port

- **Pattern synonyms cover `nothing` only.** A function on `Proc` written with
  `Qs ! i < E >∙ Pr` misses annotated sends. Proof files must match `send r …`/`recv r …`.
  Only `Tests/`/`Examples/` may use the synonyms, and there only as expressions or in
  matches that have a fallback clause.
- **Three `_∈_`s:** `Data.Fin.Subset` (a role in a set), `Relation.Unary` (a state in a set,
  in `Alg.agda`), and `Data.List.Membership` (edges, in `Check/Alg.agda`). Rename on import
  where two meet. `Data.Fin.Subset`'s `⊤`/`⊥` clash with `Data.Unit`/`Data.Empty`; rename
  them to `full`/`none`.
- **`_∈αs_`/`_∉αs_` unfold through `lookup`.** Pin `{Ps}{α}`, as for `∉α→¬∈α` today.
- **Use `acts-unique` to align the typed role with the semantics' role.** Never re-derive it
  from the graph.
- **`Focus` is carried, not recomputed.** Keep `conts`/`ktd`/`k` as pattern variables
  (termination checker).

## 12. Acceptance

- `./runall.sh --clean --tests` and `--CheckClosedProof` are green. There are no
  `postulate`s and no `TERMINATING` pragmas.
- `git diff --stat` touches nothing in §6's list, and no existing `Tests/`/`Examples/` file.
- `focus/⁅⁆` is proved, and the conservativity claim is witnessed by the untouched examples.
- `Tests/MultiRole.agda` compiles with every decision forced.
- `Safety.agda`'s only new parameter is `{k}(Ρ : Roles k)`.
