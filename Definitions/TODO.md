# TODO: simplify `t/skip` (minimal syntactic skip trees)

Status July 2026: parked by explicit decision; the checker currently uses the semantic
skip clause (`R = D ⊎ SemSkipP (D …)`, `Definitions/TypeChecker/Restricted.agda`),
which is equivalent to the present `⊢skip[ prod ]` and decidable in polynomial time.
This note records the design discussion about replacing/complementing it with a
*syntactic, minimal* tree judgment, so it can be resumed.

## The problem

`⊢skip`'s productivity is a **per-node** requirement (`skip/step`'s field
`proj₁ (ktd gr) ≡ prod`, `Definitions/Typing.agda`): every step node needs a prod
child, and `skip/cycle` is nonprod. Consequently prod trees may have to **revisit**
states — the visited vector `Ξ` stores bare states ("we have zero clue where the
escape is"), so a cycle cannot be credited with the ancestor's productivity. Minimal
(fresh-stepping) search is therefore incomplete for the current judgment.

Separating examples (all well-behaved graphs; `L` = the directly-typable leaf set):

1. `Tests/Perf09_RevisitSpine.agda` — `u ⇉ {t, ℓ}` (same-comm branches), `t → u`,
   `ℓ ∈ L`: the only prod tree runs `u → t → u → ℓ` (revisits `u`). Breaks:
   freshness-restricted trees.
2. **v-graph** — `u → g`, `g → ℓ ∈ L`, `g → v`, `v → u`: breaks "flag an ancestor
   established once its *witness subtree* is complete" (v hangs inside u's witness
   subtree, so u is still pending when v needs it).
3. **r,x,y-graph** — `r → ℓ ∈ L`, `r → x`, `x → y`, `y → x`, `y → r`: breaks the
   flagged-Ξ system below (y's genuine escape *terminates in an established
   ancestor*, which that system cannot credit as prod; forces one re-step of `r`).

## Candidate designs discussed

- **Flagged Ξ + nonprod steps** (proposed by David): `Ξ : Vec (State × Mode)`;
  a step extends `Ξ` with `(G, m)` where `m` is the step's own mode, justified
  *a posteriori* by the same node's prf (prod step ⇔ ∃ prod child); nonprod
  steps are admitted; `skip/cycle` closes **only on prod-flagged entries** and is
  **itself nonprod**. Sound (the prod skeleton is cycle-free — prod-ness never
  flows through a cycle, so the a-posteriori flags are non-circular; both
  restrictions are necessary: prod-cycles-as-prod lets `b ⇄ c` self-certify,
  cycles-on-nonprod let a leakless pocket seal itself). Equivalent in strength to
  the current judgment; handles examples 1–2 minimally; example 3 still forces
  bounded re-steps (only of prod nodes, ~one per nonprod pocket) — a decider needs
  a "re-step budget suffices" lemma, whose proof is again the semantic
  (distance-ordered) construction.
- **Spine certificates / escape forest** (fully minimal endpoint): establishment is
  *order*-justified instead of a-posteriori — a step constructor lays down a whole
  spine (path ending in `L` or an established state, interior `P`-inactive), all
  of whose states become established at once for the off-spine obligations; cycles
  close only on established states. Strictly positive (could be `r/skip`'s premise
  as a datatype), each state established once per branch, decidable by
  BFS/`reachVia?`, equivalent to `SemSkipP` both ways (shortest-path construction /
  suffix-escape induction). It is the tree re-association of a certified
  fixed-point run of `SemSkipP`.
- **Open**: David has an idea for a *purely syntactic rule* making example 3 go
  through (not yet written down — resume the discussion here).

Recurring conserved quantity: every candidate's completeness proof routes through
the semantic/distance-ordered construction, so `SemSkipP` (+ `theoremA`/`theoremB`)
stays the proof vehicle regardless of the surface syntax chosen.

Also parked: weakening productivity to root-level (`MainLeaf`-exists) would make
fresh trees complete but strictly weakens the judgment (accepts environment-
trappable, leaf-unreachable skip regions — the vacuous cycles the modes exclude)
and ripples through `Safety/`'s `spine`/`LeafHead` machinery. Rejected for now.
