# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Cambridge Computer Science dissertation project implementing state-machine encodings of coinductive types in Lean 4. The project aims to provide more efficient computational behavior for coinductive types compared to the current progressive approximation approach used in mathlib's QPF (Quotient of Polynomial Functors) implementation.

The project consists of:
- **Proposal**: A Typst document (`proposal.typ`) describing the theoretical foundation and timeline
- **SME Implementation**: A Lean 4 library (`sme/`) implementing the state-machine encoding

## Architecture

### Core Components

The project is structured around implementing equivalences between two representations of coinductive types:

1. **Progressive Approximation Encoding** (current mathlib implementation): Trees built by progressive approximation where earlier trees must "agree" with later ones up to previous depth
2. **State-Machine Encoding** (this project): Direct coalgebra representation using `(α : Type, f : α → F α, a : α)` quotiented over bisimilarity

### Key Files

- `sme/Sme/Basic.lean`: Main module entry point (currently minimal)
- `sme/Sme/ForMathlib/Data/TypeVec.lean`: Extensions to mathlib's TypeVec with universe lifting utilities
- `sme/Sme/ForMathlib/Data/PFunctor/Multivariate/Basic.lean`: Extensions to multivariate polynomial functors with universe lifting

### Implementation Stages

The project follows a progressive implementation approach:

1. **Variable universe M types**: Universe polymorphic corecursors
2. **Stream special case**: Simple equivalence proof between representations for streams
3. **Univariate M types**: General univariate terminal coalgebras
4. **Multivariate M types**: Extension using TypeVecs (most complex due to TypeVec reasoning)
5. **Cofix types**: Quotient-based terminal coalgebras (challenging due to Lean's quotient handling)
6. **Non-termination monad**: Practical example demonstrating the approach

## Development Commands

This is a Lean 4 library project using Lake as the build system.

### Basic Commands
- `lake build`: Build the library and check all proofs
- `lake exe cache get`: Download cached mathlib build artifacts (faster than building from source)

### Dependencies
- **mathlib**: Complete mathematical library for Lean 4
- Uses Lean toolchain specified in `sme/lean-toolchain`

### Project Structure
```
sme/
├── lakefile.lean          # Lake build configuration
├── lean-toolchain        # Lean version specification
├── Sme.lean              # Main module file
└── Sme/                  # Source directory
    ├── Basic.lean        # Basic definitions (placeholder)
    └── ForMathlib/       # Extensions intended for mathlib
        └── Data/
            ├── TypeVec.lean              # TypeVec extensions
            └── PFunctor/Multivariate/    # PFunctor extensions
                └── Basic.lean
```

## Key Concepts

### TypeVec Extensions
The `TypeVec.lean` file provides crucial universe lifting utilities:
- `uLift`: Lift TypeVecs to higher universes
- Universe polymorphic arrows with lifting/lowering operations
- Essential for handling universe level constraints in polynomial functor constructions

### Polynomial Functor Extensions
Extensions to multivariate polynomial functors supporting universe lifting operations, necessary for the equivalence proofs between different representations.

## Notes

- This is research code for a dissertation, not production software
- The main complexity lies in working with TypeVecs and universe polymorphism
- Quotient reasoning for Cofix types is expected to be the most challenging aspect
- Performance improvements are a key success metric (targeting O(n) vs current O(n²) for stream access)