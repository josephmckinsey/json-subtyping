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
- Typed JSON values: `TypedJson (t : JsonType)`

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
- `JsonSubtyping/ObjectSubtype.lean` - ObjectSubtype lemmas
- `JsonSubtyping/Subtype.lean` - Subtype checking implementation and coercion
- `JsonSubtyping/Constructors.lean` - TypedJson constructors (arrays, tuples, objects) and `obj{...}` notation
- `JsonSubtyping/FieldAccess.lean` - Type-safe field access with `getKey`, `getKey?`, and `TypedJson.get`
- `JsonSubtyping/JsonToLean.lean` - Value extraction: primitives (`toString`, `toFloat`, `toBool`), tuple destructuring (`toProd`, `toProd3`), and array extraction (`toArray`)
- `JsonSubtyping/JsonLemmas.lean` - Json infrastructure: `Json.beq`, sizeOf lemmas
- `JsonSubtyping.lean` - Library root module
- `Main.lean` - Executable entry point
- `Tests/Check.lean` - Tests for `JsonType.check`
- `Tests/Subtype.lean` - Tests for subtype checking
- `Tests/TypedJson.lean` - Tests for TypedJson constructors and notation
- `Tests/JsonToLean.lean` - Tests for value extraction and tuple destructuring
- `Tests/Examples.lean` - Example type definitions
- `blueprint/src/plan.typ` - Detailed design specification with typing rules

### Current Status / TODOs

**Completed:**
- ✅ `JsonType.check` - Runtime type checking
- ✅ `Json.beq_refl` - Reflexivity of JSON equality
- ✅ `JsonType.subtype` - Decidable subtype checking with all rules from plan.typ
- ✅ Subtype soundness theorem and coercion implementation
- ✅ TypedJson constructors:
  - Primitives: `null`, `true`, `false`, string/number literals
  - Arrays: `arr` (from Array), `arrFromList` (from List)
  - Tuples: `prod` (2-element), `tuple3` (3-element)
  - Objects: `ObjectFields` HList with `obj{...}` notation, `mkObj` with automatic duplicate checking
- ✅ Field access with type information:
  - `JsonType.getKey?` - Optional field type extraction
  - `JsonType.getKey` - Extract field type with proof of membership
  - `TypedJson.get` - Type-safe field access with compile-time membership checking
  - Membership notation (`key ∈ t`) with decidability
  - Correctness theorem: `getKey?_correctness` proves extracted types are sound
- ✅ Value extraction operations:
  - Primitive extraction: `toString`, `toJsonNumber`, `toFloat`, `toBool`
  - Tuple destructuring: `toProd` (2-element), `toProd3` (3-element)
  - Array extraction: `toArray` - converts `TypedJson (.array t)` to `Array (TypedJson t)`
  - Helper theorems: `tupleLength`, `tupleCheckAux`, `tupleCheck` for extracting proofs from `tupleCheckRec`
- ✅ Inhabited instances for TypedJson (primitives, arrays, tuples, literals, unions)
- ✅ Tests for type checking, subtyping, constructors, and value extraction

**TypedJson Constructor Design:**

The object construction system uses a heterogeneous list (HList) approach:
- `ObjectFields` is an inductive type indexed by `List (String × JsonType)`
- Field names and types are compile-time parameters (enabling `native_decide` for duplicate checking)
- Field values are `TypedJson` carrying runtime proofs of type correctness
- The `obj{"key": value, ...}` notation expands to `ObjectFields.cons` chains
- `mkObj` converts `ObjectFields` to `TypedJson (.object ...)` with automatic duplicate detection via `native_decide`

Key limitation: Field names must be compile-time string literals for duplicate checking to work automatically.

**Field Access Design:**

The field access system provides type-safe property access for TypedJson values:
- `getKey?` computes the type of a field if it exists (returns `Option JsonType`)
- `getKey` extracts the field type given a proof of membership
- `TypedJson.get` accesses fields with compile-time membership checking via `native_decide`
- For unions: key must exist in ALL branches, field type is the union of branch types
- For intersections: key exists in ANY branch, field type is intersection if in both
- `getKey?_correctness` proves that if `getKey? key = some v`, then accessing that field returns a value that checks against `v`

**Array Extraction Design:**

The array extraction system provides seamless integration with Lean's standard array operations:
- `toArray` converts `TypedJson (.array t)` to `Array (TypedJson t)` - the inverse of the `arr` constructor
- Uses `Array.attach` and `Array.all_eq_true'` to extract element type proofs from the check property
- Once extracted, users get all standard Lean array operations for free: indexing (`[i]`, `[i]?`, `[i]!`), iteration (`for-in`), mapping, filtering, etc.
- Design philosophy: Leverage Lean's existing infrastructure rather than reimplementing custom operations

**Priority TODOs:**

1. **Normalization** (COMPLEX - may involve mutual induction)
   - Key lemma required: `(norm t).check x ↔ t.check x` (normalization preserves checking)
   - DNF conversion for unions/intersections
   - Object field sorting and merging for intersections
   - Never elimination
   - Termination may be challenging due to mutual recursion between normalization and subtyping

2. **Additional accessor operations**
   - Optional field access for nullable fields
   - Tuple destructuring for larger tuples (4+elements)

3. **Type narrowing**
   - Type narrowing macros (TypeScript-style flow typing based on discriminants)

**Known challenges:**
- Normalization will likely require mutual induction with subtyping, making termination proofs complex
