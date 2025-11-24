# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```bash
lake build              # Build the library and executable
lake test               # Run tests
lake exe json-subtyping # Run the executable
```

## Project Overview

This project implements a TypeScript-like type system for JSON in Lean 4, enabling compile-time and runtime type checking with structural subtyping.

### Core Concept

The goal is to represent JSON schemas as Lean types with:
- Type checking: `JsonType.check (t : JsonType) (x : Json) : Bool`
- Typed JSON values: `TypedJson (t : JsonType) := Subtype (t.check · = true)`

### Type System Features (from blueprint/src/plan.typ)

**JSON Types supported:**
- Primitives: `null`, `bool`, `number`, `string`, `any`, `never`
- Literals: string literals, number literals
- Combinators: unions (`|`), intersections (`&`), arrays (`[]`), tuples, objects

**Key algorithms to implement:**
1. **Type checking** - Verify a JSON value conforms to a type ✅
2. **Subtype checking** - Decidable `τ₁ <: τ₂` relation for compile-time coercion
3. **Normalization** - DNF conversion, object field merging, never elimination
4. **Type narrowing** - TypeScript-style flow typing based on discriminants

### Subtyping Rules

The subtyping relation follows standard structural subtyping:
- Reflexivity and `τ <: any`
- Covariant arrays/tuples
- Union: `τ <: τ₁ | τ₂` if `τ <: τ₁` or `τ <: τ₂`
- Intersection: extract via `τ <: τ₁ & τ₂` implies `τ <: τ₁`
- Objects: width and depth subtyping (more fields, covariant field types)

### Architecture

- `JsonSubtyping/Basic.lean` - Core type definitions and `JsonType.check`
- `JsonSubtyping.lean` - Library root module
- `Main.lean` - Executable entry point
- `Tests/Check.lean` - Tests for `JsonType.check`
- `Tests/Examples.lean` - Example type definitions
- `blueprint/src/plan.typ` - Detailed design specification with typing rules
