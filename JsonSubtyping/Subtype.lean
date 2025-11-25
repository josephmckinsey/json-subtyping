import JsonSubtyping.Basic

namespace JsonType

/-- Check if t1 is a subtype of t2 (t1 <: t2) -/
def subtype (t1 t2 : JsonType) : Bool :=
  match t1, t2 with
  -- Trivial cases
  | _, .any => true
  | .never, _ => true
  | t1, t2 =>
      if t1 == t2 then true
      else match t1, t2 with
        -- Arrays: τ₁[] <: τ₂[] if τ₁ <: τ₂
        | .array elem1, .array elem2 => subtype elem1 elem2

        -- Tuples to tuples: [τ₁,...,τₙ] <: [σ₁,...,σₙ] if τᵢ <: σᵢ for all i
        | .tuple elems1, .tuple elems2 =>
            elems1.length == elems2.length &&
            (elems1.attach.zip elems2.attach).all (fun (⟨t1, _h1⟩, ⟨t2, _h2⟩) => subtype t1 t2)

        -- Tuples to arrays: [τ₁,...,τₙ] <: τ[] if all τᵢ <: τ
        | .tuple elems, .array elemType =>
            elems.attach.all (fun ⟨t, _h⟩ => subtype t elemType)

        -- Unions: τ <: τ₁ | τ₂ if τ <: τ₁ or τ <: τ₂
        | t, .union t1 t2 => subtype t t1 || subtype t t2

        -- Intersections: τ₁ & τ₂ <: τ if τ₁ <: τ or τ₂ <: τ
        | .inter t1 t2, t => subtype t1 t || subtype t2 t

        -- Intersections: τ <: τ₁ & τ₂ if τ <: τ₁ and τ <: τ₂
        | t, .inter t1 t2 => subtype t t1 && subtype t t2

        -- Literals are subtypes of their base types
        | .strLit _, .string => true
        | .numLit _, .number => true
        | .boolLit _, .bool => true

        -- Objects: width and depth subtyping
        -- All fields in τ₂ (both required and optional) must exist in τ₁ with subtype
        -- Required fields in τ₂ must come from req1
        -- Optional fields in τ₂ can come from either req1 or opt1
        | .object req1 opt1, .object req2 opt2 =>
            let allFields1 := (req1 ++ opt1).attach
            -- All required fields in req2 must exist in req1 (required) with subtype
            let reqCheck := req2.attach.all fun ⟨(name2, type2), _h1⟩ =>
              req1.attach.any fun ⟨(name1, type1), _h2⟩ =>
                name1 == name2 && subtype type1 type2
            -- All optional fields in opt2 must exist in allFields1 with subtype
            let optCheck := opt2.attach.all fun ⟨(name2, type2), _h1⟩ =>
              allFields1.any fun ⟨(name1, type1), _h2⟩ =>
                name1 == name2 && subtype type1 type2
            reqCheck && optCheck

        | _, _ => false
termination_by sizeOf t1 + sizeOf t2
decreasing_by
  · decreasing_trivial
  · suffices sizeOf t1 < sizeOf elems1 ∧ sizeOf t2 < sizeOf elems2 by
      simp; omega
    exact ⟨List.sizeOf_lt_of_mem _h1, List.sizeOf_lt_of_mem _h2⟩
  · suffices sizeOf t < sizeOf elems by
      simp; omega
    exact List.sizeOf_lt_of_mem _h
  · decreasing_trivial
  · decreasing_trivial
  · decreasing_trivial
  · decreasing_trivial
  · decreasing_trivial
  · decreasing_trivial
  · have : sizeOf req1 + sizeOf opt1 < sizeOf (object req1 opt1) := by simp
    have : sizeOf req2 + sizeOf opt2 < sizeOf (object req2 opt2) := by simp
    have h1_size := List.sizeOf_lt_of_mem _h1
    simp at h1_size
    have h2_size := List.sizeOf_lt_of_mem _h2
    simp at h2_size
    omega
  · have : sizeOf req1 + sizeOf opt1 < sizeOf (object req1 opt1) := by simp
    have : sizeOf req2 + sizeOf opt2 < sizeOf (object req2 opt2) := by simp
    have h1_size := List.sizeOf_lt_of_mem _h1
    simp at h1_size
    rw [List.mem_append] at _h2
    rcases _h2 with h2 | h2 <;> {
      have h2_size := List.sizeOf_lt_of_mem h2
      simp at h2_size
      omega
    }

-- Notation for subtyping
scoped infix:50 " <: " => JsonType.subtype

end JsonType
