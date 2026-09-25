
# SRMPST: Formalisation of A Synthetic Reconstruction of Multiparty Session Types

**Abstract:** This repository contains a complete Agda formalisation of the Synthetic Reconstruction of Multiparty Session Types (SRMPST). The formalisation provides mechanized proofs of fundamental safety and liveness properties for concurrent communicating systems, including type safety, progress, and deadlock freedom.

The metatheory is parameterised over an abstract **behavioural theory** (`BTheory`: a carrier with a labelled transition relation) satisfying a bundle of axioms (`WellBehaved`). Safety is proved once, for every well-behaved theory. A concrete instance, finite graphs, is shown separately to satisfy the axioms, and for it typing is **decidable**: the examples are type-checked by running the decision procedure, not by hand-written derivations.

## Repository Structure

### Core Modules

| Module | Description |
|--------|-------------|
| `Definitions.agda` | Aggregator: expressions, behavioural theory, typing |
| `Safety.agda` | Main safety theorems: preservation, progress, termination |
| `Check.agda` | The decision procedure: type checking over concrete graphs and nets |

### Definition Modules

- `Definitions/Common.agda` - Participants and labels
- `Definitions/Actions.agda` - Communication actions and independence
- `Definitions/Expr.agda` - Expression language, evaluation and typing
- `Definitions/Proc.agda` - Process language syntax and operational semantics
- `Definitions/Guard.agda` - The guardedness lattice
- `Definitions/Behav.agda` - Behavioural theories (`BTheory`), bisimilarity, and the `WellBehaved` axioms

### Typing

- `Definitions/Typing/Declarative.agda` - The declarative typing judgment `⊢p` (and `⊢skip`, `⊢s`)
- `Definitions/Typing/Alg.agda` - The set-indexed algorithmic judgment `⊢a`
- `Definitions/Typing/AlgDeclarative.agda`, `AlgNorm.agda` - `⊢a ⟺ ⊢p`, for every well-behaved theory
- `Definitions/Typing/AlgEquiv.agda`, `MainLeaf.agda` - `Wait ⟺ ⊢skip`
- `Definitions/Typing/Properties.agda`, `Substitution.agda` - Bisimulation and substitution lemmas

### Metatheory

- `Safety/Preservation.agda` - Subject reduction (`preservation`, `preservation/τ*`)
- `Safety/Progress.agda` - A well-typed session is finished or can step (`progress`)
- `Safety/Termination.agda` - No infinite silent reductions (`no-infinite-τ-reductions`)

### Concrete Model and Decision Procedure

- `Definitions/Graph.agda`, `Definitions/Graph/*.agda` - Finite graphs as a behavioural theory, with a decision procedure for `WellBehaved`; nets (`∥`, `⨾`) of graphs
- `Check/Alg.agda` - Deciding `⊢a` over a graph
- `Check/TypeCheck.agda`, `Check/Graph.agda`, `Check/Network.agda` - Deciding `⊢p` and whole sessions (`typecheck`, `typecheckSession`, `typecheckNet`)

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

`Tests/` holds regression tests for the checker and specific counterexamples. `Stale/` holds retired counterexample material that is not type-checked.

## Process Language

The formalisation defines a process calculus with the following constructs (`γ` counts expression binders, `δ` recursion binders):

```agda
data Proc (γ δ : ℕ) : Set where
  _!_<_>∙_       : Part → {I : ℕ} → Fin (suc I) → Exp γ → Proc γ δ → Proc γ δ   -- Send
  Σ_？·_          : Part → {I : ℕ} → Vec (Proc (suc γ) δ) (suc I) → Proc γ δ     -- Receive (branching)
  ifp_then_else_ : Exp γ → Proc γ δ → Proc γ δ → Proc γ δ                      -- Conditional
  rec            : Proc γ (suc δ) → Proc γ δ                                    -- Recursion
  v              : Fin δ → Proc γ δ                                             -- Process variable
  ∅              : Proc γ δ                                                     -- Termination
```

## Type System

The typing judgment `Γ & Δ ⊢p P ◂ Pr ∶ G` establishes that process `Pr` implements participant `P` at behaviour `G`, under expression context `Γ` and recursion context `Δ`. A whole session is typed by `⊢s M ∶ G`: every participant's process is typed at `G`.

---

## Technical Requirements

- Agda 2.8.0
- Agda Standard Library 2.3

There is no `.agda-lib` file: the standard library must be registered globally (`~/.agda/libraries`).

## Checking the Proof and the Examples

With the appropriate version of Agda and its standard library installed, you can run from the root of the code repository the following commands:

- `./runall.sh` to type-check the main modules (incremental: reuses compiled files)
- `./runall.sh --tests` to also check everything under `Tests/` and `Examples/`, which runs the decision procedure
- `./runall.sh --clean` to rebuild from scratch
- `./runall.sh --CheckClosedProof` to check with `--no-allow-unsolved-metas`
- `./runall.sh --help` for usage information
- `./clean.sh` to remove the compiled files

No file contains holes or postulates.
