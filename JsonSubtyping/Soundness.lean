/-
  Soundness proof for JsonType.subtype

  Main theorem: If t1.check x = true and t1.subtype t2 = true, then t2.check x = true

  This ensures that the subtyping relation is sound: any value that satisfies a subtype
  also satisfies its supertype.
-/

import JsonSubtyping.Subtype

open Lean (Json)

namespace JsonType

/-! ## Helper Lemmas

We need a few critical lemmas to prove soundness. These are proven separately.
-/

/-- If Json.beq returns true for a value and a string constructor, the value must be a string -/
theorem Json.beq_str_constructor (x : Json) (s : String) :
    Json.beq x (.str s) = true → ∃ s', x = .str s' := by
  sorry

/-- If Json.beq returns true for a value and a number constructor, the value must be a number -/
theorem Json.beq_num_constructor (x : Json) (n : Lean.JsonNumber) :
    Json.beq x (.num n) = true → ∃ n', x = .num n' := by
  sorry

/-- If Json.beq returns true for a value and a bool constructor, the value must be a bool -/
theorem Json.beq_bool_constructor (x : Json) (b : Bool) :
    Json.beq x (.bool b) = true → ∃ b', x = .bool b' := by
  sorry

/-- If two JsonTypes are equal via BEq, their check functions agree -/
theorem beq_check_eq (t1 t2 : JsonType) (x : Json) :
    (t1 == t2) = true → t1.check x = t2.check x := by
  sorry

/-! ## Main Soundness Theorem -/

theorem any_check_eq_true {x : Json} : JsonType.any.check x = true := by simp [JsonType.check]

theorem never_check_eq_false {x : Json} : JsonType.never.check x = false := by simp [JsonType.check]

@[simp]
theorem subtype_refl (t : JsonType) : t <: t := by cases t <;> simp [subtype]

theorem elem_subtype_of_array (t1 t2 : JsonType) : (t1.array <: t2.array) → t1 <: t2 := by
  intro h
  have : (t1 = t2) = true ∨ (t1 <: t2) = true := by
    unfold JsonType.subtype at h
    simp at h
    grind
  simp at this
  rcases this with rfl | this
  · simp
  exact this

/-- Soundness of subtyping: if x satisfies t1 and t1 is a subtype of t2, then x satisfies t2 -/
theorem subtype_sound (t1 t2 : JsonType) (x : Json) :
    t1.check x = true → t1.subtype t2 = true → t2.check x = true := fun h_check h_sub =>
  match t1, t2 with
  -- Trivial cases
  | _, .any => any_check_eq_true
  | .never, _ => by rw [never_check_eq_false] at h_check; contradiction
  | t1, t2 =>
      if h : t1 == t2 then beq_check_eq t1 t2 x h ▸ h_check
      else match t1, t2 with
        -- Arrays: τ₁[] <: τ₂[] if τ₁ <: τ₂
        | .array elem1, .array elem2 => sorry
        -- Tuples to tuples: [τ₁,...,τₙ] <: [σ₁,...,σₙ] if τᵢ <: σᵢ for all i
        | .tuple elems1, .tuple elems2 => sorry
        -- Tuples to arrays: [τ₁,...,τₙ] <: τ[] if all τᵢ <: τ
        | .tuple elems, .array elemType => sorry
        -- Unions: τ <: τ₁ | τ₂ if τ <: τ₁ or τ <: τ₂
        | t, .union t1 t2 => sorry
        -- Intersections: τ₁ & τ₂ <: τ if τ₁ <: τ or τ₂ <: τ
        | .inter t1 t2, t => sorry
        -- Intersections: τ <: τ₁ & τ₂ if τ <: τ₁ and τ <: τ₂
        | t, .inter t1 t2 => sorry
        -- Literals are subtypes of their base types
        | .strLit _, .string => sorry
        | .numLit _, .number => sorry
        | .boolLit _, .bool => sorry
        -- Objects: width and depth subtyping
        -- All fields in τ₂ (both required and optional) must exist in τ₁ with subtype
        -- Required fields in τ₂ must come from req1
        -- Optional fields in τ₂ can come from either req1 or opt1
        | .object req1 opt1, .object req2 opt2 =>
          sorry
        | _, _ => sorry


end JsonType
