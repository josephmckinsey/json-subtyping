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
2. **Subtype checking** - Decidable `τ₁ <: τ₂` relation for compile-time coercion ✅
3. **Subtype soundness** - Prove that subtyping preserves checking (see below)
4. **Normalization** - DNF conversion, object field merging, never elimination
5. **Type narrowing** - TypeScript-style flow typing based on discriminants

### Subtyping Rules

The subtyping relation follows standard structural subtyping:
- Reflexivity and `τ <: any`
- Covariant arrays/tuples
- Union: `τ <: τ₁ | τ₂` if `τ <: τ₁` or `τ <: τ₂`
- Intersection: extract via `τ <: τ₁ & τ₂` implies `τ <: τ₁`
- Objects: width and depth subtyping (more fields, covariant field types)

### Architecture

- `JsonSubtyping/Basic.lean` - Core type definitions, `JsonType.check`, and `TypedJson`
- `JsonSubtyping/Subtype.lean` - Subtype checking implementation
- `JsonSubtyping/JsonLemmas.lean` - Json infrastructure: `Json.beq`, sizeOf lemmas
- `JsonSubtyping.lean` - Library root module
- `Main.lean` - Executable entry point
- `Tests/Check.lean` - Tests for `JsonType.check`
- `Tests/Subtype.lean` - Tests for subtype checking
- `Tests/TypedJson.lean` - Tests for TypedJson constructors
- `Tests/Examples.lean` - Example type definitions
- `blueprint/src/plan.typ` - Detailed design specification with typing rules

### Current Status / TODOs

**Completed:**
- ✅ `JsonType.check` - Runtime type checking
- ✅ `Json.beq_refl` - Reflexivity of JSON equality
- ✅ `JsonType.subtype` - Decidable subtype checking with all rules from plan.typ
- ✅ TypedJson constructors (null, literals, coercions)
- ✅ Tests for type checking and subtyping

**Priority TODOs:**

1. **Subtype soundness theorem** (CRITICAL for coercion)
   - Need to prove: `t1.check x = true → t1.subtype t2 = true → t2.check x = true`
   - This is the fundamental property that justifies coercing `TypedJson t1` to `TypedJson t2`
   - Without this theorem, we cannot safely implement coercion between subtypes
   - Will likely require induction on both the structure of types and the subtype derivation

2. **Coercion implementation**
   - Once soundness is proven, implement: `coerce : TypedJson t1 → (h : t1.subtype t2 = true) → TypedJson t2`
   - This will allow compile-time type narrowing and widening

3. **Normalization** (COMPLEX - may involve mutual induction)
   - Key lemma required: `(norm t).check x ↔ t.check x` (normalization preserves checking)
   - DNF conversion for unions/intersections
   - Object field sorting and merging for intersections
   - Never elimination
   - Termination may be challenging due to mutual recursion between normalization and subtyping
   - Consider deferring until after soundness proof for non-normalized subtyping

4. **Type inference helpers**
   - Field access with type information
   - Object construction helpers
   - Type narrowing macros (TypeScript-style flow typing)

**Known challenges:**
- Normalization will likely require mutual induction with subtyping, making termination proofs complex
- Soundness proof will be substantial and may reveal edge cases in our subtype checking algorithm
