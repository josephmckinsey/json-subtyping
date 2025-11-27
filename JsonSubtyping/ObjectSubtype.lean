/-
  Object subtyping implementation and helper lemmas.

  Objects have required and optional fields, with subtyping rules:
  - All required fields in τ₂ must be required in τ₁ with subtype
  - All optional fields in τ₂ must exist (required or optional) in τ₁ with subtype
  - This gives width subtyping (extra fields allowed) and depth subtyping (covariant)

  KEY INSIGHT: We work purely with `get?` and avoid TreeMap lemmas that require WF proofs,
  since Json.obj doesn't carry a well-formedness invariant.
-/

import JsonSubtyping.Basic

open Lean (Json)

namespace JsonType

/-! ## Helper Lemmas about Field Checking -/

/-- checkRequiredField returns true iff get? returns some value that passes the checker -/
theorem checkRequiredField_iff (k : String) (checker : Json → Bool)
    (jsonFields : Std.TreeMap.Raw String Json compare) :
    checkRequiredField k checker jsonFields = true ↔
    ∃val, jsonFields.get? k = some val ∧ checker val = true := by
  unfold checkRequiredField
  cases h : jsonFields.get? k with
  | none => simp
  | some val => simp

/-- checkOptionalField returns true iff get? returns none OR some value that passes -/
theorem checkOptionalField_iff (k : String) (checker : Json → Bool)
    (jsonFields : Std.TreeMap.Raw String Json compare) :
    checkOptionalField k checker jsonFields = true ↔
    (jsonFields.get? k = none ∨ ∃val, jsonFields.get? k = some val ∧ checker val = true) := by
  unfold checkOptionalField
  cases h : jsonFields.get? k with
  | none => simp
  | some val => simp

/-! ## Key Lemmas: Relating check functions to individual fields -/

/-- If requiredFieldsCheck passes and (k,v) is in the field list,
    then get? k returns some value that checks against v. -/
theorem requiredFieldsCheck_implies_get? (req : List (String × JsonType))
    (k : String) (v : JsonType) (jsonFields : Std.TreeMap.Raw String Json compare)
    (kvMem : (k, v) ∈ req) :
    requiredFieldsCheck req (fun p _h => p.2.check) jsonFields = true →
    ∃val, jsonFields.get? k = some val ∧ v.check val = true := by
  intro hcheck
  simp only [requiredFieldsCheck, List.all_eq_true] at hcheck
  simpa [checkRequiredField_iff] using hcheck ⟨(k, v), kvMem⟩ (by simp)

/-- If optionalFieldsCheck passes and (k,v) is in the field list,
    then get? k returns none OR some value that checks against v. -/
theorem optionalFieldsCheck_implies_get? (opt : List (String × JsonType))
    (k : String) (v : JsonType) (jsonFields : Std.TreeMap.Raw String Json compare)
    (kvMem : (k, v) ∈ opt) :
    optionalFieldsCheck opt (fun p _h => p.2.check) jsonFields = true →
    (jsonFields.get? k = none ∨ ∃val, jsonFields.get? k = some val ∧ v.check val = true) := by
  intro hcheck
  simp only [optionalFieldsCheck, List.all_eq_true] at hcheck
  simpa [checkOptionalField_iff] using hcheck ⟨(k, v), kvMem⟩ (by simp)

/-! ## Subtyping for Required Fields

**Theorem**: If all fields in req2 exist in req1 with subtypes,
            then requiredFieldsCheck req1 implies requiredFieldsCheck req2.

**Proof strategy**:
- Show all fields in req2 check by using List.all_eq_true
- For each field (k, v) in req2:
  - By hypothesis: ∃(k', v') ∈ req1 where k = k' and v' <: v
  - By requiredFieldsCheck_implies_get?: jsonFields.get? k = some val and v'.check val
  - By subtyping soundness: v.check val
  - Therefore: field checks
-/

def FieldsWeakerThan (source target : List (String × JsonType)) : Prop :=
  (∀p ∈ target, ∃q ∈ source, p.1 = q.1 ∧ (∀v, q.2.check v = true → p.2.check v = true))


theorem requiredFieldsSubtype (req1 req2 : List (String × JsonType))
    (h : FieldsWeakerThan req1 req2) :
    ∀jsonFields,
    requiredFieldsCheck req1 (fun p _h => p.2.check) jsonFields = true →
    requiredFieldsCheck req2 (fun p _h => p.2.check) jsonFields = true := by
  intro jsonFields req1Checks
  unfold requiredFieldsCheck
  rw [List.all_eq_true]
  intro ⟨⟨k, v⟩, kv_in_req2⟩ _
  -- Get the matching field from req1
  obtain ⟨⟨k', v'⟩, q_mem, ⟨rfl, v_sub⟩⟩ := h (k, v) kv_in_req2
  -- By our key lemma, jsonFields.get? k = some val and v'.check val
  obtain ⟨val, get_eq, v'_checks⟩ := requiredFieldsCheck_implies_get? req1 k v' jsonFields q_mem req1Checks
  -- Use the iff lemma to show this field checks
  rw [checkRequiredField_iff]
  exact ⟨val, get_eq, v_sub val v'_checks⟩

/-! ## Subtyping for Optional Fields

**Theorem**: If all fields in opt2 exist in (req1 ++ opt1) with subtypes,
            then (requiredFieldsCheck req1 && optionalFieldsCheck opt1) implies optionalFieldsCheck opt2.

**Proof sketch**:
Similar to required, but:
- Field can come from either req1 or opt1
- If field is missing, that's OK (returns true)
-/

theorem optionalFieldsSubtype (req1 opt1 opt2 : List (String × JsonType))
    (h : FieldsWeakerThan (req1 ++ opt1) opt2) :
    ∀jsonFields,
    (requiredFieldsCheck req1 (fun p _h => p.2.check) jsonFields &&
     optionalFieldsCheck opt1 (fun p _h => p.2.check) jsonFields) = true →
    optionalFieldsCheck opt2 (fun p _h => p.2.check) jsonFields = true := by
  intro jsonFields both_check
  simp only [Bool.and_eq_true] at both_check
  obtain ⟨req1_checks, opt1_checks⟩ := both_check
  unfold optionalFieldsCheck
  rw [List.all_eq_true]
  intro ⟨⟨k, v⟩, kv_in_opt2⟩ _
  -- Get the matching field from req1 ++ opt1
  obtain ⟨⟨k', v'⟩, q_mem, ⟨rfl, v_sub⟩⟩ := h (k, v) kv_in_opt2
  -- The field might be in req1 or opt1
  rw [List.mem_append] at q_mem
  cases q_mem with
  | inl q_in_req1 =>
    -- Field is in req1 (required), so it must exist
    obtain ⟨val, get_eq, v'_checks⟩ := requiredFieldsCheck_implies_get? req1 k v' jsonFields q_in_req1 req1_checks
    simp [checkOptionalField_iff, get_eq, v_sub val v'_checks]
  | inr q_in_opt1 =>
    -- Field is in opt1 (optional), so it might be missing or present
    obtain (missing | ⟨val, get_eq, v'_checks⟩) := optionalFieldsCheck_implies_get? opt1 k v' jsonFields q_in_opt1 opt1_checks
    · simp [checkOptionalField_iff, missing]
    · simp [checkOptionalField_iff, get_eq, v_sub val v'_checks]

/-! ## Putting It Together

If both required and optional subtyping hold, then object subtyping holds.
-/

theorem objectSubtypeProof (req1 opt1 req2 opt2 : List (String × JsonType))
    (reqH : FieldsWeakerThan req1 req2)
    (optH : FieldsWeakerThan (req1 ++ opt1) opt2) :
    ∀j, (JsonType.object req1 opt1).check j = true →
        (JsonType.object req2 opt2).check j = true := by
  intro j h
  unfold JsonType.check at h ⊢
  cases j with
  | obj fields =>
    -- The object checks split into required && optional
    -- h says: req1 checks && opt1 checks
    -- We need: req2 checks && opt2 checks
    simp only [Bool.and_eq_true] at h ⊢
    obtain ⟨req1_checks, opt1_checks⟩ := h
    constructor
    · exact requiredFieldsSubtype req1 req2 reqH fields req1_checks
    · exact optionalFieldsSubtype req1 opt1 opt2 optH fields (by simp [req1_checks, opt1_checks])
  | _ => simp at h

end JsonType
