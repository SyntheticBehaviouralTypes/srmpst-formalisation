# ARCHIVED — 2026-07-21 — skip judgment redesign

> Historical record. Completed; the judgment it introduces is the one in
> `Definitions/Typing/Declarative.agda` today.

Status: Phases 1-7 DONE. The entire declarative layer (`Definitions/Typing.agda`),
its supporting bisimulation/substitution lemmas (`Safety/Skip.agda`,
`Typing/Substitution.agda`), and the full metatheory (`Safety/Head.agda`,
`Safety/Preservation.agda`, `Safety/Progress.agda`, `Safety/Termination.agda`) have
all been rewritten and typecheck — confirmed end to end via the root `Safety.agda`
compiling clean. Only Phase 8 remains: `Definitions/TypeChecker/*` still references
the old `Mode`-based `⊢skip[ prod ]` shape and needs its own design pass (see §3.8) —
deliberately scoped out of this implementation pass. `./runall.sh` confirms this is
the *only* remaining break (one error, in `TypeChecker/Core.agda`).

## 1. Motivation

The current `⊢skip[ prod / nonprod ]` judgment (`Definitions/Typing.agda`) encodes
"productivity" (not-vacuously-true) by threading a `Mode` through the tree, requiring a
*distinguished* transition per `skip/step` node whose continuation is tagged `prod`, and
hard-wiring `skip/cycle` to always be `nonprod`. This forces skip trees to sometimes
revisit the same graph state more than once to expose a "way out" (see
`Tests/Perf09_RevisitSpine.agda`, and case (b) in `CLAUDE.md`'s recurring-gotchas list),
which the algorithmic layer (`TypeChecker/Core.agda`'s `SemSkipP` + `reachVia?`) already
avoids semantically but the *declarative* judgment cannot.

Goal: redefine `⊢skip` so that a skip tree visits each state **at most once**, purely
syntactically (no `Dec`/`Bool`/semantic reachability sweep in the declarative rules —
that stays confined to the algorithmic layer, unchanged), while remaining sound (no
vacuous/non-terminating process is ever accepted).

## 2. Core design change — `Definitions/Typing.agda`

### 2.1 Drop `Mode` entirely

Delete the `Mode` datatype (`prod`/`nonprod`). `_&_⊢skip[_]_∶_` loses its `Mode` index
everywhere: `_&_⊢skip_∶_`, `_&_&_⊢skip[_]_∶_` → `_&_&_⊢skip_∶_`,
`_&_⊢hskip[_]_∶_` → `_&_⊢hskip_∶_`. `t/skip`/`h/skip` premises drop `[ prod ]`.

### 2.2 `skip/step`: restore a bare existence witness

```agda
skip/step :
  (gr  : G -< α >-> G')                -- NEW: only witnesses G is not a dead end
  (na  : P not-active-in G)
  (ktd : ∀ {G″ β} → G -< β >-> G″ → Leaf & G ∷ Ξ ⊢skip P ◂ Pr ∶ G″)
  → Leaf & Ξ ⊢skip P ◂ Pr ∶ G
```

`gr` carries **no** productivity obligation (no `proj₁ (ktd gr) ≡ prod` side condition,
which is gone along with `Mode`). Its only job: block the case where `G` has zero
outgoing edges, which would otherwise let `ktd = λ ()` vacuously discharge *any* `Pr`
(including ones that could never be typed) with no further work. `ktd`'s codomain drops
the `∃[ m ]` wrapper — it returns a plain `⊢skip` term now.

### 2.3 `skip/cycle` — DECIDED: Option A (`P ∈T G`)

```agda
skip/cycle :
  (eq  : lu Ξ X ~ G)
  (inT : P ∈T G)
  → Leaf & Ξ ⊢skip P ◂ Pr ∶ G
```

Soundness argument: every `Ξ` entry was pushed by a prior `skip/step`, hence satisfies
`na` (P inactive there). Bisimilarity requires exact action-for-action matching
(`_≲_`'s `simulate` field), so it preserves `na`-status — a `na`-failing state can never
be bisimilar to anything in `Ξ`. So whatever concrete path witnesses `P ∈T G`, `ktd`'s
totality forces it to be explored edge-by-edge, and the edge where `P` actually becomes
active originates at a state where `na` fails — which `skip/cycle` can never rescue (no
bisimilar `Ξ` entry can exist for it) and `skip/step` can't touch either (needs `na`) —
so it's forced through `skip/main`, i.e. a genuine `Leaf`. This is why the `rec (v X)`
counterexample (see §5) turned out **not** to break this option.

**Neither `skip/cycle` nor `skip/step` checks `MessageGuarded`, deliberately.** `Pr`
running through `⊢skip` need not be `rec`-headed (could be `∅`, a bare send/recv, an
`if`) — guardedness is exclusively `t/rec`'s concern, enforced through `Leaf` wherever a
real leaf is required.

**Lemmas needed for this option:**
- `na-bisim : G ~ G′ → P not-active-in G → P not-active-in G′` — **DONE.** Added to
  `Definitions/Behav.agda`, right after `∈~` (in the `BTheory`-derived section, no
  `WellBehaved` axioms needed — it only uses `_≲_`'s `simulate` via the existing `~R→`
  combinator). One-liner: `na-bisim G~G′ na gr = na (~R→ G~G′ gr)`. Typechecked in
  isolation (`agda Definitions/Behav.agda`), no errors.
- `∈T-bisim : G ~ G′ → P ∈T G → P ∈T G′` — **not needed as new**: this already exists
  as `∈~` (`Definitions/Behav.agda`, right before `na-bisim`). Use `∈~` directly
  wherever the plan below says "transport `inT`".

The soundness argument above is still a hand-argument, not yet a checked Agda proof —
it only becomes checkable once `Definitions/Typing.agda`'s `skip/cycle` actually has
this shape and the sites in §3 that consume it (especially `comm/ready-skip` and
`rec/guarded-skip`) are worked through. Treat it as plausible-but-unverified until then.

**Option B (rejected):** a new `Leaf`-tied reachability relation `_reaches_` was also
drafted (self-contained, would have sidestepped the `na`-bisimulation argument above at
the cost of a new datatype). Rejected as unnecessary complexity now that Option A's
argument is in hand — recorded in §5 for context, not to be revisited unless the §3
audits below turn up a real gap Option A can't close.

### 2.4 `MainLeaf` simplification

`main/step`'s `{ok : proj₁ (ktd gr) ≡ prod}` field is gone entirely:

```agda
main/step :
  (gr′ : G -< β >-> H)
  → MainLeaf td (ktd gr′)                  -- was: (proj₂ (ktd gr′)), with an `ok` field
  → MainLeaf td (skip/step gr na ktd)
```

## 3. Per-file impact

Legend: **[mech]** mechanical (drop `Mode`/`.proj₁`/`.proj₂` threading, no new proof
content) · **[new]** requires writing new proof content · **[rethink]** needs a careful
look at what the code was actually establishing, not just syntax surgery · **[audit]**
site flagged as possibly needing more than `inT : P ∈T G` alone provides — check before
or while implementing, since these are exactly where the §2.3 soundness argument has to
actually pay off.

### 3.1 `Definitions/Typing.agda` — core, see §2 above in full.

### 3.2 `Safety/Skip.agda`
- `skip/weaken-visited`, `skip-td/bisim`, `skip-leaf/bisim` — **[mech]** drop mode
  fields. `skip/cycle` case: weakening doesn't need to touch `inT` at all (`P ∈T G`
  doesn't mention `Ξ`). Bisimulation transport (`skip-td/bisim`/`skip-leaf/bisim`)
  transports `inT` via the existing `∈~` lemma (`∈~ G~G′ inT`).
- `mode/transport`, `selected-step-mode` — delete outright, dead code once `Mode` is gone.
- `skip/unfold-cycle` — **[mech]** drop the `(m′ ≡ prod → n ≡ prod)` conjunct from the
  return type entirely (nothing left to preserve). Body's `skip/cycle` case
  (`lookup/insert` split into "reuse `base`" vs "shift index") otherwise unchanged in
  shape; thread `inT` alongside `eq` in the "shift index" branch (no transport needed,
  same reasoning as weakening above).

### 3.3 `Safety/Head.agda` — largest surface, needs care, not blind translation
- `skip/if/inv`, `skip/rec/unfold`, `hskip/bisim`, `hskip/unfold-cycle`,
  `mainLeaf/weaken-visited`, `leafHead/bisim`, `skip/head`, `leafHead/unfold`,
  `cancel/unskip`, `mainLeaf/head` — **[mech]** drop mode fields/pairing throughout.
- **[audit]** Several sites currently discharge the `skip/cycle` case via an *impossible
  pattern* exploiting `Mode` (e.g. `... | nonprod , skip/cycle {X = ()} _ , _` around
  lines 210-212 and 364-366). Under the new rules `skip/cycle` is never impossible, so
  each needs a real case built from `inT : P ∈T G` alone (no leaf handed to you
  directly here — that's the whole point of choosing Option A, but it means these
  sites must reconstruct whatever they need from `inT` + surrounding context, not just
  project a leaf out). Go through each site individually: what does it actually need
  (a leaf? a fact about `G`? a further recursion?) and whether `P ∈T G` plus the
  `na`-bisimulation argument (§2.3) actually gets there. This is the main place the
  §2.3 soundness argument needs to be cashed out as real code, not just the sites in
  Preservation/Progress/Termination below.
- **[rethink]** `skip/if/inv`'s signature threads `(m ≡ prod → …)` through its return
  type (lines 51-54) — needs its own dedicated look at what it's actually expressing
  once `Mode` is gone, not a blind erasure.

### 3.4 `Safety/Preservation.agda`
- `send/cont-skip`/`recv/cont-skip` — **[mech]** drop `mode-gr`; bodies only ever used
  `na gr` on the actual transition, untouched.
- `comm/ready-skip` — **[new] [audit]**, the single largest piece of real work in this
  whole plan. Today it recurses on `headP grα` and uses `m′ ≡ prod` (`prodP`) purely to
  know that walk lands on a real leaf. Under the new rules `gr` is bare existence:
  following it via `ktd gr` is still a valid *structural* recursion (⊢skip is still an
  ordinary finite inductive datatype, so this still terminates), but is no longer
  guaranteed to land on `skip/main` directly — it's guaranteed to land on `skip/main`
  **or** `skip/cycle` (some branch must bottom out, being a finite term). In the latter
  case, this is exactly where the §2.3 `na`-bisimulation argument has to be replayed as
  an actual Agda proof, threaded through this specific mutual recursion (which is
  already juggling two participants' skip trees in lockstep) — not just an informal
  argument. Budget real time for this one specifically; it's the strongest test of
  whether Option A's soundness argument actually goes through as written, or needs
  strengthening.

### 3.5 `Safety/Progress.agda`
- `guarded/active-skip`, `inactive/done-skip` — drop `m ≡ prod` hypotheses.
  `skip/cycle` case (currently `()`) becomes real:
  - `guarded/active-skip` (`MessageGuarded Pr → ⊢hskip P◂Pr∶G → P∈T G`): **[audit, but
    likely easy]** — the `skip/cycle` case's conclusion is `P ∈T G`, and `skip/cycle`'s
    own field is `inT : P ∈T G` — so this case is just `guarded/active-skip guarded
    (skip/cycle eq inT) = inT`, a direct projection. Simpler than today (no more
    `m ≡ prod` threading, no vacuous `()` pattern).
  - `inactive/done-skip` (`P ∉T G → ⊢hskip P◂Pr∶G → done/proc Pr`): **[audit]** — here
    the hypothesis is `P ∉T G` and the field is `inT : P ∈T G` — these directly
    contradict, so `inactive/done-skip P∉G (skip/cycle eq inT) = ⊥-elim (P∉G inT)`.
    Also simpler than today. (No forward-propagation lemma needed after all — that was
    only going to be necessary under the rejected Option B.)
- `skip/status`, `receiver/hskip-progress`, `sender/hskip-progress` — **[mech]**, only
  match on `skip/main`/`skip/step`, no mode used in bodies beyond the `[ prod ]` index.

### 3.6 `Safety/Termination.agda`
- `rec/guarded-skip` (`⊢skip[m] P◂rec Pr∶G → m≡prod → MessageGuarded Pr`) — **[audit]**,
  drop `m ≡ prod`. This is the site that originally motivated the `rec (v X)`
  counterexample discussion, so it's the one to check most carefully: the `skip/cycle`
  case only hands you `inT : P ∈T G`, not a typing derivation for `rec Pr` at any
  state — unlike `guarded/active-skip`/`inactive/done-skip` above (§3.5), `P ∈T G`
  alone does **not** obviously give `MessageGuarded Pr` directly. Re-derive the full
  §2.3 argument concretely for this exact goal before assuming it goes through:
  the point is that `ktd`'s totality, applied along whatever path witnesses `inT`,
  eventually forces a real `Leaf (rec Pr)` at the `na`-failing boundary state, and
  *that* typing derivation (via `t/rec`) is where `MessageGuarded Pr` actually comes
  from — but wiring that up here means recursing through `ktd` along the witness path,
  not just consuming `inT` as an opaque fact. Expect this to need a genuine helper
  lemma, not a one-liner like the two in §3.5.

### 3.7 `Typing/Substitution.agda`
- `skip/subst-expr`, `skip/weaken-expr`, `skip/weaken-proc`, `skip/subst-proc` —
  **[mech]** drop mode threading in recursive `ktd` calls. `skip/cycle` cases carry
  `inT` through completely unchanged — `P ∈T G` mentions neither `Γ`, `Δ`, nor `Pr`,
  so none of these substitution/weakening operations touch it at all. Simpler than
  today (today's `skip/cycle eq` case is already a no-op here; `inT` just rides along).

### 3.8 `Definitions/TypeChecker/{Core,Restricted,Complete,Completeness}.agda`
Own pass, not mechanical, scope out separately once §3.1-§3.7 are settled and
`Definitions/Typing.agda` re-typechecks on its own:
- `Core.agda`'s `SemSkipP`/`ReachLP`, `Complete.agda`'s Theorem A/B, and
  `Completeness.agda` all exist to bridge `SemSkipP` to the *old* Mode-based `⊢skip`.
  With `Mode` gone and `skip/cycle` now carrying `P ∈T G` directly (a much simpler,
  non-`Leaf`-shaped fact than `SemSkipP`), expect the shape of this bridge to change
  rather than simply shrink — needs its own design pass, not estimated here.
- `Restricted.agda`'s `R = D ⊎ SemSkipP (D …)` and `SkipDecide.semSkip?` need rework
  since they're stated against the old shape.
- Do **not** fold this into the same implementation pass as §3.1-3.7 — scope and
  estimate it separately once the declarative side is settled and re-typechecks.

### 3.9 Tests
- `Tests/Perf09_RevisitSpine.agda` — doesn't hand-construct `⊢skip` terms, only calls
  `typecheck`. Not edited directly; re-run once `TypeChecker` (§3.8) is redone, to
  confirm it still accepts (and, ideally, that the accepted tree no longer needs to
  revisit `u`).
- No other `Tests`/`Examples` files reference `Mode`/`skip/step`/`skip/cycle` directly
  (checked via grep across the tree).

## 4. New lemmas required (summary, cross-referenced above)

| Lemma | Needed for | Status |
|---|---|---|
| `na-bisim : G ~ G′ → P not-active-in G → P not-active-in G′` | §2.3 soundness argument, §3.2 bisim transport | **DONE** — `Definitions/Behav.agda`, after `∈~` |
| `∈~ : G ~ G′ → P ∈T G → P ∈T G′` | §3.2 bisim transport | **already existed**, `Definitions/Behav.agda` |
| `comm/ready-skip`'s recursion, replaying the §2.3 argument concretely | §3.4 | not started — highest-risk item |
| `rec/guarded-skip`'s `skip/cycle` case, ditto | §3.6 | not started — second-highest-risk item |

## 5. Discussion record (for context, not to be re-litigated per-line)

- Initial design attempts considered a two-layer `⊢skip⁻`/`⊢skip⁺` stratification and a
  `SemSkipP`-style semantic premise baked into the declarative rule — both rejected:
  the user wants this established syntactically, not via semantic analysis in the
  typing rules.
- A design using `_-[¬ P ]->*_` + an explicit `Leaf` endpoint pairing, decoupled from
  `ktd`, was rejected: it broke `comm/ready-skip`'s lockstep-with-other-participants
  mechanism, whose actual purpose (driving other simultaneously-skipping participants'
  `ktd` forward along the same concrete transition) was underestimated.
- An initial version of §2.2 without a `gr` witness was unsound: `ktd` over an empty
  domain (a dead-end state) is vacuously total, accepting *any* `Pr` there, including
  ones that could never really be typed. Fixed by restoring `gr` as a bare existence
  witness (no productivity tag).
- A `_reaches_` relation (Option B, §2.3) was drafted as a `Leaf`-tied alternative to
  `P ∈T G`, specifically to sidestep needing the `na`-bisimulation argument. Tested
  against `Pr = rec (v X)` (never `MessageGuarded`, hence never `Leaf`-typeable, hence
  only escapable via `skip/cycle`): worked through concretely and found that `P ∈T G`
  alone (Option A) already handles this case too, because `ktd`'s totality plus
  bisimulation-preserving-`na` forces the search to hit a genuine `Leaf` requirement
  regardless of which option is used. Option B was rejected as unneeded complexity;
  Option A chosen.
- Neither option checks `MessageGuarded` itself — `Pr` need not be `rec`-headed, and
  guardedness is `t/rec`'s job alone, enforced through `Leaf`.

## 6. Suggested implementation order

1. ~~Decide §2.3 (A vs B).~~ **Done: A.**
2. ~~Write `na-bisim`.~~ **Done, `Definitions/Behav.agda`.**
3. `Definitions/Typing.agda` (§2, §3.1) — everything else depends on this compiling.
4. `Safety/Skip.agda` (§3.2) — bisim/weakening transport lemmas other files rely on.
5. `Typing/Substitution.agda` (§3.7) — mechanical, low risk, unblocks nothing else but
   also blocked by nothing else.
6. `Safety/Head.agda` (§3.3) — depends on §3.2's transport lemmas; do the `[audit]`
   items here before assuming the rest is mechanical.
7. `Safety/Preservation.agda`'s `comm/ready-skip` (§3.4) first among the remaining
   Safety files — highest risk, should surface any remaining gap in the §2.3 argument
   as early as possible. Then `Safety/Progress.agda` (§3.5, low risk per the audit
   above) and `Safety/Termination.agda` (§3.6, second-highest risk).
8. `Definitions/TypeChecker/*` (§3.8) — separate pass, re-scope once step 7 is green.
9. Re-run `./runall.sh` and `./runall.sh --CheckClosedProof`; re-run
   `Tests/Perf09_RevisitSpine.agda` specifically.

## 7. Open items

- [x] §2.3: Option A or B? → **A.**
- [x] Write `na-bisim`.
- [ ] Actually check the §2.3 soundness argument goes through in Agda once
      `Definitions/Typing.agda` is updated — it is currently a hand-argument.
- [ ] Work through `comm/ready-skip` (§3.4) and `rec/guarded-skip` (§3.6) concretely —
      flagged as the two sites where `P ∈T G` alone (no direct `Leaf`) is least
      obviously enough, and where the `na`-bisimulation argument has to actually be
      threaded through nontrivial existing recursions rather than just consumed as a
      fact.
- [ ] `skip/if/inv`'s `(m ≡ prod → …)`-shaped return type (§3.3) needs its own
      from-scratch look, not mechanical erasure. — **Done, see §8**: this turned out
      to be a genuine gap, not just an awkward shape, and is now the top blocker.
- [ ] Scope `Definitions/TypeChecker/*` rework (§3.8) as a separate task once the
      declarative layer is settled — do not estimate it together with the rest.

## 8. Implementation finding: `leaf-from-skip` is a real, shared gap

While implementing §3.3 (`Safety/Head.agda`), most of the `[audit]`-flagged sites
(`mainLeaf/weaken-visited`, `leafHead/bisim`, `leafHead/unfold`, `mainLeaf/head`, and
similar) turned out to be **fine, not at risk**: `MainLeaf` has no constructor at all
targeting a `skip/cycle` conclusion (only `main/here` for `skip/main`, `main/step` for
`skip/step`), so `MainLeaf td (skip/cycle ...)` is unconditionally empty regardless of
`Mode` — every site consuming a `MainLeaf` argument just discharges that case with
`()`, exactly as it did before. The earlier worry in §3.3 about these sites was
overstated.

`t/if/inv`/`skip/if/inv` (renamed `skip/if/split` for its half of the job) is
genuinely different: it has to *produce* `[] ⊢e E ∶ s/bool` directly from an arbitrary
`⊢skip` term, with no externally-supplied `MainLeaf`-style witness to fall back on.
Under Option A, `skip/cycle`'s `inT : P ∈T G` names a witnessing path but carries no
`ktd` to walk further — once a branch bottoms out at `skip/cycle`, there is no way,
from the `⊢skip` term alone, to reconstruct which state actually carries the real
`Leaf`. The na-bisimulation soundness argument (§2.3) shows a leaf exists somewhere;
it does not, as stated, hand you one constructively.

Bridged for now with a postulate in `Safety/Head.agda`:

```agda
postulate
  leaf-from-skip :
    ∀ {γ δ ξ PPr G} {Leaf : NProc γ δ → Behav → Set} {Ξ : Vec Behav ξ}
    → Leaf & Ξ ⊢skip PPr ∶ G
    → ∃[ H ] Leaf PPr H
```

plus `{-# TERMINATING #-}` on `t/if/inv`/`skip/if/split`'s mutual block (the
postulate's result has no structural relationship to its argument as far as the
termination checker can see). This is the same gap `comm/ready-skip`
(`Safety/Preservation.agda`) and `rec/guarded-skip` (`Safety/Termination.agda`) will
hit — do not re-derive it three times; prove it once and reuse it.

**Resolved** — no postulate left. Per the user's (1)/(2)/(3) breakdown: `leaf-or-∈T`
(point (1)/(2), given any `⊢skip` term, either a real leaf or the `P ∈T G` fact a
`skip/cycle` bottoms out with, propagated upward via `in/later`) is plain structural
recursion. Point (3), `leaf-from-∈T` — given `std` and a `P ∈T G` fact for the same
`G`, produce a leaf — decomposes the `P ∈T G` *trace* via `na` into an edge and a
smaller `P ∈T` fact; feeding that edge to `std`'s own `ktd` gives a fresh `⊢skip` term
one level "nested" (`Ξ = G ∷ []`). Rather than recursing into that directly (where it
could bottom out at a bare `skip/cycle` with no further `ktd`), it's folded straight
back down to `Ξ = []` via `skip/unfold-cycle {Ξ = []} {Ξ′ = []}` first — with both
index vectors empty, `lookup/insert`'s "cycle to an outer entry" branch is
unreachable, so the fold-back can never itself be a bare `skip/cycle`. Recursing on
the `P ∈T` trace (genuinely structurally decreasing) rather than on `⊢skip` directly
is what makes this go through. See `TODO.md`'s Phase 4.5 for the exact code and the
higher-order-unification snag hit along the way (fixed by reusing `ptd/bisim`).

`comm/ready-skip` (Phase 5, `Safety/Preservation.agda`) needed one further twist, not
a straight reuse: it involves *two* participants, and the first attempt (call
`leaf-or-∈T` on P's side alone, then combine with Q's untouched typing) failed with an
actual type error — P's leaf can end up rooted at a different state than Q's
still-at-`G` typing, since `leaf-or-∈T` doesn't coordinate with Q at all. Fixed by
defining `comm/ready-or-∈T` to carry Q's `⊢hskip` tree alongside P's, advancing Q via
its own `ktd` applied to the *same* edge at every step, so both stay rooted at the
same state throughout. `comm/ready-from-∈T` mirrors `leaf-from-∈T` for point (3),
again carrying Q's tree along. At the time, the whole `comm/ready*` mutual group
needed `{-# TERMINATING #-}` for the same cross-function-call reason as `t/if/inv` —
**superseded, see §9 below.**

## 9. Eliminating the remaining pragmas: route through `⊢head`

Three pragmas remained after §8: `t/if/inv` (`Safety/Head.agda`), `rec/guarded`
(`Safety/Termination.agda`), `comm/ready*` (`Safety/Preservation.agda`) — all with the
same root cause (recursing on `leaf-from-skip`'s *result*, not a syntactic subterm).
The user's key insight resolved all three: **each of these is only ever used at
`Γ = []`, `Δ = []`**, so `td/head` (already proven pragma-free — it recurses on the
*external trace* `G -[¬P]->* G′`, which keeps decreasing even when the `⊢skip` term
itself is folded) is directly applicable. Route the whole computation through `⊢head`
instead of raw `_⊢p_∶_`.

Why this specifically fixes the earlier gap: `⊢head` has no `t/unskip`-analogue
constructor (`h/send`/`h/recv`/`h/skip`/`h/if`/`h/rec`/`h/end` — nothing moves the
state out from under a witness). Over raw `_⊢p_∶_`, `t/unskip`'s trace could move a
`P ∈T G` witness to a state it no longer described, forcing `skip/∈T-back` to *grow*
it, and growth composed with a second genuine `skip/unfold-cycle` fold left no
argument position Agda could see decreasing across the cycle. That case simply
doesn't arise over `⊢head`.

- `t/if/inv` = `head/if/inv` ∘ `td/head`. `head/if/inv` mirrors `leaf-or-∈T`/
  `leaf-from-∈T`'s two-pair shape, but the two parts of the inversion need different
  treatment: `E`'s type doesn't mention `G` (extractable from a leaf at *any*
  reachable state), while the branch heads are pinned to `G` by `h/if`'s own typing
  rule, so `head/if/split` *rebuilds* an isomorphic `⊢hskip` tree (`skip/if/split`'s
  technique) rather than extracting a leaf existentially. First attempt kept a
  separate `head/if/etd` cluster duplicating `head/if/split`'s own walk — a real
  redundancy the user caught and asked to be removed; fixed by having
  `head/if/split` discover `E`'s type (or `P ∈T G`) as a byproduct of the same walk,
  riding along `gr` directly. The fold-fallback pair
  (`head/if/etd-from-∈T-skip`/`head/if/etd-from-∈T`) stays strictly separate from
  `head/if/inv`/`head/if/split`, for the same reason `leaf-from-∈T` stays separate
  from its callers: a leaf found via the fold could itself be `h/skip` again, and
  re-entering the fast path would need a fresh, unrelated `P ∈T G` witness each time.
- `rec/guarded` = `head/rec/guarded` ∘ `td/head` — simpler, since `h/rec` carries
  `MessageGuarded Pr` directly as a field and there's no second, `G`-pinned piece of
  information, so no rebuild is needed at all.
- `comm/ready*` split into two disjoint `mutual` groups: the fast path
  (`comm/ready`/`comm/ready-skip`/`comm/ready-or-∈T`, essentially unchanged) and a
  self-contained fold path (`comm/ready-from-∈T-skip`/`comm/ready-from-∈T`, carrying
  Q's `⊢hskip` tree in lockstep) that *never* calls back into the fast path — that
  back-edge is exactly what forced the old design's single big pragma.

All three files (`Safety/Head.agda`, `Safety/Termination.agda`,
`Safety/Preservation.agda`) typecheck clean with **zero pragmas and zero postulates**.
See `TODO.md`'s Phase 4.6 for the itemised breakdown.
