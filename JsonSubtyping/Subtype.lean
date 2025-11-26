import JsonSubtyping.Basic

open Lean (Json)

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
theorem beq_check_eq {t1 t2 : JsonType} (x : Json) :
    (t1 == t2) = true → t1.check x = t2.check x := by
  intro h; simp at h; rw [h]

inductive DecideSubtype (t1 t2 : JsonType) where
  | none : DecideSubtype t1 t2
  | isSubtype : (∀j, t1.check j = true → t2.check j = true) → DecideSubtype t1 t2

/-! ## Main Soundness Theorem -/


namespace JsonType

theorem any_check_eq_true {x : Json} : any.check x = true := by simp [JsonType.check]

theorem never_check_eq_false {x : Json} : JsonType.never.check x = false := by simp [JsonType.check]

def arraySubtype {elem1 elem2 : JsonType} :
    DecideSubtype elem1 elem2 → DecideSubtype elem1.array elem2.array
  | .none => .none
  | .isSubtype h => .isSubtype fun j h' => by
    unfold JsonType.check at h'
    cases j <;> (try simp only [Bool.false_eq_true] at h')
    next js =>
      unfold JsonType.check
      simp only
      rw [Array.all_eq_true'] at h'
      rw [Array.all_eq_true']
      intro x xInJs
      apply h x (h' x xInJs)

/-- Helper lemma: tupleCheckRec of nil is false. -/
@[simp]
theorem tupleCheckRec_nil (t : JsonType) (ts : List JsonType)
    (checker : (t' : JsonType) → t' ∈ (t::ts) → Json → Bool) :
    tupleCheckRec (t::ts) checker [] = false :=
  rfl

/-- Helper lemma: tupleCheckRec decomposes into head and tail -/
@[simp]
theorem tupleCheckRec_cons (t : JsonType) (ts : List JsonType) (v : Json) (vs : List Json)
    (checker : (t' : JsonType) → t' ∈ (t::ts) → Json → Bool) :
    tupleCheckRec (t::ts) checker (v::vs) =
    (checker t List.mem_cons_self v &&
     tupleCheckRec ts (fun t' h => checker t' (List.mem_cons_of_mem t h)) vs) := by
  rfl

/-- Helper lemma: tupleCheckRec decomposes into head and tail -/
@[simp]
theorem emptyTupleCheckRec (v : List Json)
    (checker : (t' : JsonType) → t' ∈ [] → Json → Bool) :
    tupleCheckRec [] checker v = v.isEmpty := by
  rcases v <;> simp [tupleCheckRec]

/-- Helper for tuple-to-array subtyping: if all tuple elements are subtypes of arrayElemType,
    then the tuple is a subtype of the array -/
def tupleToArraySubtype (tupleElems : List JsonType) (arrayElemType : JsonType)
    (h : ∀t ∈ tupleElems, DecideSubtype t arrayElemType) :
    DecideSubtype (.tuple tupleElems) (.array arrayElemType) :=
  match tupleElems with
  | [] => .isSubtype fun j => by
      unfold check
      cases j <;> grind [emptyTupleCheckRec] -- grind nice.
  | t::ts =>
    match h t List.mem_cons_self,
      tupleToArraySubtype ts arrayElemType (fun t' th => h t' (List.mem_cons_of_mem t th)) with
    | .isSubtype h1, .isSubtype h2 => .isSubtype (by
      intro j jIsTuple
      unfold check at jIsTuple ⊢
      cases j with
      | arr js =>
        simp only at jIsTuple ⊢
        cases h' : js.toList with
        | nil => simp [h'] at jIsTuple
        | cons v vs =>
          -- jIsTuple says: t.check v && tupleCheckRec ts ... vs
          -- We need to show: all elements in js check against arrayElemType
          -- Key: js.toList = v::vs, so all elements are either v (checks by h1) or in vs (checks by h2)
          simp only [h', tupleCheckRec_cons, Bool.and_eq_true, Array.all_eq_true'] at jIsTuple ⊢
          obtain ⟨hv, hvs⟩ := jIsTuple
          intro x xInJs
          replace xInJs : x ∈ js.toList := xInJs.val
          rw [h'] at xInJs
          cases xInJs with
          | head => exact h1 v hv
          | tail t xInVs =>
            -- x is in vs, and vs checks against tuple ts
            -- By h2, the array {toList := vs} checks against arrayElemType
            have := h2 (.arr { toList := vs })
            simp only [check, Array.all_eq_true'] at this
            apply this hvs x (List.mem_toArray.mpr xInVs)
      | _ => simp at jIsTuple
    )
    | _, _ => .none

def tupleSubtype (elems : List (JsonType × JsonType)) (h : ∀t ∈ elems, DecideSubtype t.1 t.2) :
    DecideSubtype (.tuple (elems.map Prod.fst)) (.tuple (elems.map Prod.snd)) :=
  match elems with
  | .nil => .isSubtype fun j => by
      unfold check
      cases j <;> simp
  | (t1, t2)::ts =>
    match h (t1, t2) List.mem_cons_self,
      tupleSubtype ts (fun t' th => h t' (List.mem_cons_of_mem _ th)) with
    | .isSubtype h1, .isSubtype h2 => DecideSubtype.isSubtype (by
      intro j jIsTuple
      unfold check at jIsTuple ⊢
      -- j must be an array
      cases j with
      | arr js =>
        simp only [List.map_cons] at jIsTuple ⊢
        -- Case split on whether js.toList is empty or cons
        cases h' : js.toList with
        | nil => simp [h'] at jIsTuple
        | cons v vs =>
          -- The interesting case: v::vs checks against (t1::ts.map fst)
          simp only [h', tupleCheckRec_cons, Bool.and_eq_true] at jIsTuple ⊢
          obtain ⟨hv, hvs⟩ := jIsTuple
          constructor
          · exact h1 v hv
          · have := h2 (.arr { toList := vs })
            simp only [check] at this
            exact this hvs
      | _ => simp at jIsTuple
    )
    | _, _ => .none


/-- Check if t1 is a subtype of t2 (t1 <: t2) -/
def subtype (t1 t2 : JsonType) : DecideSubtype t1 t2 :=
  match t1, t2 with
  -- Trivial cases
  | _, .any => .isSubtype fun _ _ => any_check_eq_true
  | .never, _ => .isSubtype fun  _ h => by rw [never_check_eq_false] at h; contradiction
  | t1, t2 =>
      if t1eqt2 : t1 == t2 then .isSubtype fun j h => beq_check_eq j t1eqt2 ▸ h
      else match t1, t2 with
        -- Arrays: τ₁[] <: τ₂[] if τ₁ <: τ₂
        | .array elem1, .array elem2 => arraySubtype (subtype elem1 elem2)

        -- Tuples to tuples: [τ₁,...,τₙ] <: [σ₁,...,σₙ] if τᵢ <: σᵢ for all i
        | .tuple elems1, .tuple elems2 =>
          if lengthEq : elems1.length = elems2.length then
            have := tupleSubtype (elems1.zip elems2) (fun t th => subtype t.1 t.2)
            by {
              rw [List.map_fst_zip (Nat.le_of_eq lengthEq),
              List.map_snd_zip (Nat.le_of_eq lengthEq.symm)] at this
              exact this
            }
          else
            .none
        -- Tuples to arrays: [τ₁,...,τₙ] <: τ[] if all τᵢ <: τ
        | .tuple elems, .array elemType =>
            tupleToArraySubtype elems elemType (fun t _h => subtype t elemType)
        /-
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
        -/

        | _, _ => .none
termination_by sizeOf t1 + sizeOf t2
decreasing_by
  · decreasing_trivial
  · rcases t with ⟨t1, t2⟩
    have ⟨th1, th2⟩ := List.of_mem_zip th
    have := List.sizeOf_lt_of_mem th1
    have := List.sizeOf_lt_of_mem th2
    simp; omega
  · have := List.sizeOf_lt_of_mem _h
    simp; omega
  /-
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
  -/

-- Notation for subtyping
scoped infix:50 " <: " => JsonType.subtype

end JsonType
