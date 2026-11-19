
# SRMPST: Formalisation of A Synthetic Reconstruction of Multiparty Session Types

**Abstract:** This repository contains a complete Agda formalisation of the Synthetic Reconstruction of Multiparty Session Types (SRMPST). The formalisation provides mechanized proofs of fundamental safety and liveness properties for concurrent communicating systems, including type safety, progress, and deadlock freedom.

The metatheory is parameterised over an abstract **behavioural theory** (`BTheory`: a carrier with a labelled transition relation) satisfying a bundle of axioms (`WellBehaved`), plus the two facts that make it synchronous (`Synchronous`). Safety is proved once, for every such theory. A concrete instance, finite graphs, is shown separately to satisfy the axioms, and for it typing is **decidable**: the examples are type-checked by running the decision procedure, not by hand-written derivations.

The typing rules are **those of the ECOOP27 paper** (Fig. 4), stated on the bisimilarity classes of the theory (Fig. 3); see [Type System](#type-system).

Sends are **multicasts**: `Q ⇒ Qs ! ℓ < E >∙ Pr` sends label `ℓ` to every participant in the set `Qs`, and all of them receive in the same step.

## Status

- **Metatheory: complete.** Preservation, progress and termination are proved for every well-behaved synchronous theory.
- **Equivalence: complete.** The algorithmic judgment `⊢a` is proved equivalent to the paper's judgment `⊢`: `⊢a → ⊢` for every well-behaved theory, `⊢ → ⊢a` for every well-behaved synchronous one. There are no finiteness assumptions.
- **Graph model and decision procedure: complete.** Well-behavedness and typing are decidable for finite graphs. Every example is type-checked by running the procedure.
- **Nets (`∥`, `⨾`): supported by flattening.** Their well-behavedness is certified compositionally, but typing runs the graph checker on the flattened product. Checking a participant against only the sub-net it acts in is the main open line of work (`FUTURE_WORK.md` §A).

No file contains holes or postulates, and every `.agda` file outside `Stale/` type-checks.

## Repository Structure

### Core Modules

| Module | Description |
|--------|-------------|
| `Definitions.agda` | Aggregator: expressions, behavioural theory, typing |
| `Safety.agda` | Main safety theorems: preservation, progress, termination |
| `Check.agda` | The decision procedure: type checking over concrete graphs and nets |

### Definition Modules

- `Definitions/Common.agda` - Participants and sets of participants (`PartSet`)
- `Definitions/Actions.agda` - Choices (a label `ℓ : ℕ` and a sort), events, actions (one event per participant), the multicast `P ⟶ Qs # c`, and independence
- `Definitions/Expr.agda` - Expression language, evaluation and typing
- `Definitions/Proc.agda` - Process language syntax and operational semantics
- `Definitions/Behav.agda` - Behavioural theories (`BTheory`) with the paper's derived transitions and participation (`G -⟨ R ⟩-> G′`, `G -→* G′`, `G -[¬ R ]->* G′`, `R ∈T G`, `r first-in (R , G)`), bisimilarity, the `WellBehaved` axioms, and `Synchronous`
- `Definitions/Classes.agda` - The paper's bisimilarity classes `[ G ]`, their steps (the theory `B/∼`), class equality `≐`, and the lemmas between a class and its representatives
- `Utils/Family.agda` - Families indexed by a finite set of labels: a receive's branches, `Br ∋ ℓ ↦ P`

### Typing

- `Definitions/Typing/Declarative.agda` - The paper's typing judgments (module `MPST.Paper`, on classes): `Γ & Δ ⊢[ R ] P ∶ G` and the skipping judgment `Γ & Δ & Ξ ⊢[ R ] P ∶ G`; and the session judgments `⊢ᵛ[ Ps ] Pr ∶ G`, `⊢s[ Ρ ] M ∶ G`
- `Definitions/Typing/Alg.agda` - The set-indexed algorithmic judgment `⊢a`
- `Definitions/Typing/AlgDeclarative.agda`, `AlgNorm.agda` - `⊢a ⟺ ⊢` (the `→` for every well-behaved theory, the `←` for synchronous ones)
- `Definitions/Typing/AlgEquiv.agda` - `Wait ⟺ SkipT` (`SkipT`: skip trees on states, the shape of the skipping judgment)
- `Definitions/Typing/MainLeaf.agda` - Every `Wait` tree has a leaf (`waitFind`)
- `Definitions/Typing/Properties.agda`, `Substitution.agda` - Invariance under class equality (`td/≐`), substitution lemmas, `rec` unfolding

### Metatheory

Sessions are one process per block of an `Assignment` of roles to processes; a process may implement a set of roles, and is typed against its block's **local view** of the theory (its internal steps hidden, nothing renamed). One process per role is the assignment `singletons`.

- `Safety.agda` - The statements, over `⊢s[ Ρ ] M ∶ G`: `preservation`, `progress`, `no-infinite-τ-reductions`, and `safety` (any run is replayed by the global view and stays typed; from there, for every `n`, the session runs to a finished state or through `n` communications)
- `Safety/Preservation.agda`, `Progress.agda`, `Termination.agda` - Their proofs
- `Definitions/View.agda`, `Definitions/View/Lemmas.agda` - Local and global views, projection between them
- `Definitions/Transfer.agda`, `Definitions/Graph/View.agda`, `Check/View.agda` - A local view built as a graph, and the checker run against it

### Concrete Model and Decision Procedure

- `Definitions/Graph.agda`, `Definitions/Graph/*.agda` - Finite graphs as a behavioural theory, with decision procedures for `WellBehaved` and `Synchronous`; nets (`∥`, `⨾`) of graphs
- `Check/Alg.agda` - Deciding `⊢a` over a graph
- `Check/TypeCheck.agda` - Deciding `⊢` at the class of a state (`tc?`)
- `Check/Graph.agda`, `Check/Network.agda` - Deciding `⊢ᵛ` per process and `⊢s` per session, for any assignment (`typecheck`, `typecheckSession`, `typecheckNet`, `typecheckSessionNet`)

### Examples and Case Studies

- `Examples/SendRecv.agda` - Send/receive, with and without recursion
- `Examples/PingPong.agda` - Bidirectional communication protocol
- `Examples/RoundRobin.agda` - Cyclic communication patterns
- `Examples/NoSynGT.agda` - A session with no synchronous global type
- `Examples/CounterExamples.agda` - Processes the checker rejects
- `Examples/OAuth2.agda` - Multi-party authentication protocol (Figure 12, a)
- `Examples/Rec2Buy.agda` - Recursive two-buyer (Figure 12, b)
- `Examples/RecMW.agda` - Recursive map/reduce (Figure 12, c)
- `Examples/IndepW.agda` - Recursive multiparty worker, built as a net (Figure 12, d)

`Tests/` holds regression tests for the checker and specific counterexamples; `Tests/Multicast.agda` covers multicast sends (acceptance, order-free receiver sets, missing or wrong receivers, non-synchronous graphs, a multicast loop). `Stale/` holds retired material that is not type-checked, including the `∥` projection proof over the previous judgment (`FUTURE_WORK.md` §A).

### Design Records

- `FUTURE_WORK.md` - Open work: checking nets without flattening, plus one approach that was tried and reverted
- `docs/` - Dated, archived design notes (`docs/README.md` indexes them)

## Process Language

The formalisation defines a process calculus with the constructs of the POPL 2026 paper — send, receive, `let`, conditional, recursion, variable, end — (`γ` counts expression binders, `δ` recursion binders):

```agda
data Proc (γ δ : ℕ) : Set where
  _⇒_!_<_>∙_     : Part → PartSet → ℕ → Exp γ → Proc γ δ → Proc γ δ                  -- Role p sends ℓ to Qs
  _⇐_？·_         : Part → Part → {n : ℕ} → Vec (Maybe (Proc (suc γ) δ)) n → Proc γ δ  -- Role q receives from p
  letp_in′_      : Exp γ → Proc (suc γ) δ → Proc γ δ                                  -- let x = e in P
  ifp_then_else_ : Exp γ → Proc γ δ → Proc γ δ → Proc γ δ                            -- Conditional
  rec            : Proc γ (suc δ) → Proc γ δ                                          -- Recursion
  v              : Fin δ → Proc γ δ                                                   -- Process variable
  ∅              : Proc γ δ                                                           -- Termination
```

A process names the role that acts: `p ⇒ Qs ! ℓ < E >∙ Pr` is role `p` sending, `q ⇐ p ？· Br` role `q` receiving. A receive's branches are a family indexed by its labels `𝓛`: entry `ℓ` is `just P` exactly when `ℓ ∈ 𝓛` with branch `P` (`Br ∋ ℓ ↦ P`); the sort of a branch's variable comes from the matched step. `letp E in′ P` is `let x = E in P` (`let` and `in` are Agda keywords): `P` binds `x`, of `E`'s sort; it takes a silent step (`P-Let`) to `P` with `E`'s value for `x`. With named binders (`Definitions/Proc/Syntax.agda`) it is written `letp x ≔ E in′ P`.

`PartSet = Subset N` (`Data.Fin.Subset`): receiver sets have no order and no duplicates, so `⁅ B ⁆ ∪ ⁅ C ⁆` and `⁅ C ⁆ ∪ ⁅ B ⁆` are the same set.

## Actions

An action has **one event per participant**: `Action = Vec (Maybe Event) N`, where an event is a send `(! Qs) # c` or a receive `(？ P) # c` (`c` a label and sort). The theory, not the action type, says which events happen together. `P ⟶ Qs # c` is the multicast: `P` sends `c` to `Qs`, and every `Q ∈ Qs` receives `c` from `P`.

`WellBehaved` asks: a receiver of one step that takes part in another means they are the same communication (`recv-overlap`); determinism up to bisimilarity (`step-deterministic`: one action reaches bisimilar states); receives of one label agree on its sort (`step-sort-det`); no branch appears out of nowhere (`no-new-branch/step`); and independent steps commute up to bisimilarity (`step-diamond`; `α ⋄ β` means the actions differ and no receiver of either takes part in the other). `Synchronous` adds that every step is one multicast to a nonempty `Qs` with `P ∉ Qs` (`balanced`, also its own record `Balanced`) and that no communication appears out of nowhere (`no-new-comm/step`). `Safety/` takes it of the theory; `⊢ → ⊢a` needs only `Balanced`, which every view inherits, so views need no certificate beyond `WellBehaved`.

## Type System

The typing rules are the ECOOP27 paper's (Fig. 4), on the bisimilarity classes of the theory (Fig. 3, `Definitions/Classes.agda`): the class of `G` is `[ G ]`, a class step is `[G] —α→ [G′] ⟺ ∃ G″ ∼ G′ . G —α→ G″`, and two classes are equal (`≐`) when their representatives are bisimilar.

`Γ & Δ ⊢[ R ] P ∶ G` says that process `P`, implementing the roles `R`, is typed at the class `G`, under expression context `Γ` and recursion context `Δ`; `Γ & Δ & Ξ ⊢[ R ] P ∶ G` is the skipping judgment. There is one constructor per rule: `send`, `recv`, `skip`, `forward`, `if`, `end`, `rec`, `var`, `skip-main`, `skip-cycle`, `skip-step`. `send` and `recv` ask `p first-in (R , G)`: in every run of the others from `G`, the first step involving `R` involves `p`. `recv` also asks `p ∉ R`, and types the branch of every label offered (`G -[ q ⇐ p ∶ ℓ < t > ]-> G′`).

A whole session is typed by `⊢s[ Ρ ] M ∶ G`: every process is typed at `[ G ]`, against its own block's view (`⊢ᵛ[ Ps ] Pr ∶ G`, which carries that view's `WellBehaved`). `docs/2026-11-18-paper-rules.md` lists where the Agda notation differs from the paper's, and why.

---

## Technical Requirements

- Agda 2.8.0.2
- Agda Standard Library 2.4

There is no `.agda-lib` file: the standard library must be registered globally (`~/.agda/libraries`). Receiver sets use its `Data.Fin.Subset`.

## Checking the Proof and the Examples

With the appropriate version of Agda and its standard library installed, you can run from the root of the code repository the following commands:

- `./runall.sh` to type-check the main modules (incremental: reuses compiled files)
- `./runall.sh --tests` to also check everything under `Tests/` and `Examples/`, which runs the decision procedure
- `./runall.sh --clean` to rebuild from scratch
- `./runall.sh --CheckClosedProof` to check with `--no-allow-unsolved-metas`
- `./runall.sh --help` for usage information
- `./clean.sh` to remove the compiled files
