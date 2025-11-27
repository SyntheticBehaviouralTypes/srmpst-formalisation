# SRMPST: Formalisation of A Synthetic Reconstruction of Multiparty Session Types

**Abstract:** This repository contains a complete Agda formalisation of the Synthetic Reconstruction of Multiparty Session Types (SRMPST). The formalisation provides mechanized proofs of fundamental safety and liveness properties for concurrent communicating systems, including type safety, progress, and deadlock freedom.

## Repository Structure

### Core Modules

| Module | Description |
|--------|-------------|
| `Safety.agda` | Main safety theorems and mechanized proofs |
| `Definitions.agda` | Core type system and MPST framework |
| `SubstitutionProperties.agda` | Substitution lemmas and preservation properties |

### Definition Modules

- `Definitions/Proc.agda` - Process language syntax and operational semantics
- `Definitions/Behav.agda` - Session types and behavioral theory
- `Definitions/Actions.agda` - Communication actions and independence
- `Definitions/Expr.agda` - Expression language and evaluation
- `Definitions/Guard.agda` - Guard conditions for termination
- `Definitions/GlobalTypesWPar.agda` - Global types w/parallel composition

### Examples and Case Studies

- `Examples/PingPong.agda` - Bidirectional communication protocol
- `Examples/RoundRobin.agda` - Cyclic communication patterns
- `Examples/OAuth2.agda` - Multi-party authentication protocol (Figure 12, a)
- `Examples/Rec2Buy.agda` - Recursive two-buyer (Figure 12, b)
- `Examples/RecMW.agda` - Recursive map/reduce (Figure 12, c)
- `Examples/IndepW.agda` - Recursive multiparty worker (Figure 12, d)

## Process Language

The formalisation defines a process calculus with the following constructs:

```agda
data Proc (γ δ : ℕ) : Set where
  _!_<_>∙_    : Part → Label → Exp γ → Proc γ δ → Proc γ δ      -- Send
  Σ_？[_]·_   : Part → Vec Sort (suc I) → Vec (Proc (suc γ) δ) (suc I) → Proc γ δ  -- Receive
  ifp_then_else_ : Exp γ → Proc γ δ → Proc γ δ → Proc γ δ     -- Conditional
  rec         : Proc γ (suc δ) → Proc γ δ                      -- Recursion
  v           : Fin δ → Proc γ δ                               -- Process variable
  ∅           : Proc γ δ                                       -- Termination
```

## Type System

The typing judgment `Γ & Δ / G ↑ P ⊢p< g > Pr` establishes that process `Pr` implements participant `P` according to global type `G` under expression context `Γ` and behavioral context `Δ`.

---

## Technical Requirements

- Agda 2.8.0
- Agda Standard Library 2.3

## Checking the Proof and the Examples

With the appropriate version of Agda and its standard library installed, you can run from the root of the code repository the following commands:

- `./runall.sh` to compile all the files (allows unsolved metas by default)
- `./runall.sh --CheckClosedProof` to compile all files with strict checking (no unsolved metas)
- `./runall.sh --help` for usage information
- `./clean.sh` to remove the compiled files
