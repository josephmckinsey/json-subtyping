import JsonSubtyping.Subtype
import JsonSubtyping.FieldAccess

open Lean (Json)

def TypedJson.inl {t1 t2 : JsonType} (x : TypedJson t1) : TypedJson (t1.union t2) :=
  match x with
  | ⟨x, h⟩ => ⟨x,
    JsonType.unionCheck t1 t2 x ▸ Bool.or_eq_true _ _ ▸
      Or.inl h
    ⟩

def TypedJson.inr {t1 t2 : JsonType} (x : TypedJson t2) : TypedJson (t1.union t2) :=
  match x with
  | ⟨x, h⟩ => ⟨x,
    JsonType.unionCheck t1 t2 x ▸ Bool.or_eq_true _ _ ▸
      Or.inr h
  ⟩

universe u in
def TypedJson.unionElim {t1 t2 : JsonType}
    {motive : (x : TypedJson (t1.union t2)) → Type u}
    (left : (x : TypedJson t1) → motive x.inl)
    (right : (x : TypedJson t2) → motive x.inr)
    (tj : TypedJson (t1.union t2)) : motive tj :=
  let ⟨j, h⟩ := tj
  if h' : t1.check j then
    left ⟨j, h'⟩
  else
    right ⟨j, by grind⟩  -- I'm lazy

universe u in
def TypedJson.unionSplit {t1 t2 : JsonType}
    {motive : Type u}
    (left : (x : TypedJson t1) → motive)
    (right : (x : TypedJson t2) → motive)
    (tj : TypedJson (t1.union t2)) : motive :=
  tj.unionElim (motive := fun _ => motive) left right

def JsonType.canMismatchPropertyStr (t : JsonType) (key : String) (str : String) : Bool :=
  match t.getKey? key with
  | .some kt => !(kt.subtype (.strLit str)).subtypeToBool
  | .none => true

def JsonType.canBeObject (t : JsonType) : Bool :=
  match t with
  | .object _ _ => true
  | .union t1 t2 => t1.canBeObject || t2.canBeObject
  | .inter t1 t2 => t1.canBeObject && t2.canBeObject
  | .any => true
  | _ => false

theorem JsonType.canBeObject_correctness
    {t : JsonType} {x : Json} (h : t.check x = true)
    (h' : t.canBeObject = false) :
    x.getObj? = .error "object expected" :=
  match t with
  | .object _ _ => by simp [canBeObject] at h'
  | .union t1 t2 => by
    simp only [canBeObject, Bool.or_eq_false_iff] at h'
    simp only [unionCheck, Bool.or_eq_true] at h
    rcases h with h | h
    · exact JsonType.canBeObject_correctness h h'.1
    exact JsonType.canBeObject_correctness h h'.2
  | .inter t1 t2 => by
    simp only [canBeObject, Bool.and_eq_false_iff] at h'
    simp only [interCheck, Bool.and_eq_true] at h
    rcases h' with h' | h'
    · exact JsonType.canBeObject_correctness h.1 h'
    exact JsonType.canBeObject_correctness h.2 h'
  | .any => by simp [canBeObject] at h'
  | .strLit _ | .boolLit _ | .numLit _ | .number | .never
  | .null | .array _ | .string | .bool | .tuple _h => by
    rcases x <;> simp [JsonType.check, Json.beq, Json.isNull] at h
    <;> {
      simp [Json.getObj?]
      exact rfl
    }

theorem JsonType.canBeObject_correctness'
    {t : JsonType} (key : String) {x : Json} (h : t.check x = true)
    (h' : t.canBeObject = false) :
    x.getObjVal? key = .error "object expected" := by
  have := canBeObject_correctness h h'
  simp [Json.getObj?] at this
  rcases x <;> {
    simp [Json.getObjVal?] at ⊢ this
    try rfl
    try contradiction
  }

def JsonType.canMatchPropertyStr (t : JsonType) (key : String) (str : String) : Bool :=
  t.canBeObject &&
  match t.getKey? key with
  | .some kt => kt.check str
  | .none => true -- we have no information about key


/-!
For narrowing, we need theorems that say:
- When we observe x.getObjVal? key = .ok str at runtime, type must canMatchPropertyStr
- When we observe x.getObjVal? key ≠ .ok str at runtime, type must canMismatchPropertyStr

If we have a type which is a bunch of unions,
we can filter them according to these properties.
-/

theorem JsonType.canMatchPropertyStr_correctness
    {t : JsonType} {key : String} {str : String} {x : Json}
    (h : x.getObjVal? key = .ok str)
    (h' : t.check x = true) : t.canMatchPropertyStr key str = true := by
  simp only [canMatchPropertyStr]
  -- Show that both parts of the AND are true
  if hobj : t.canBeObject = false then
    have := canBeObject_correctness' key h' hobj
    simp [h] at this
  else
    simp only [hobj]
    match getKeyEq : t.getKey? key with
    | some kt =>
      obtain ⟨y, hy, hcheck⟩ := getKey?_correctness h' getKeyEq
      rw [h, Except.ok.injEq] at hy
      rw [← hy] at hcheck
      simp [hcheck]
    | none => rfl

-- Helper for the original direction (before renaming)
theorem JsonType.requiresPropertyStr_correctness
    {t : JsonType} {key : String} {str : String} {x : Json}
    (h : t.canMismatchPropertyStr key str = false)
    (h' : t.check x = true) : x.getObjVal? key = .ok str := by
  simp [canMismatchPropertyStr] at h
  match getKeyEq : t.getKey? key with
  | some kt =>
    simp only [getKeyEq, Bool.not_eq_false'] at h
    obtain ⟨y, yh, yh'⟩ := getKey?_correctness h' getKeyEq
    have := DecideSubtype.toBool_correct _ h y yh'
    simp [check] at this
    grind
  | none => simp [getKeyEq] at h

theorem JsonType.canMismatchPropertyStr_correctness
    {t : JsonType} {key : String} {str : String} {x : Json}
    (h : x.getObjVal? key ≠ .ok str)
    (h' : t.check x = true) : t.canMismatchPropertyStr key str = true := by
  grind [requiresPropertyStr_correctness]

def JsonType.mkListFromUnion (t : JsonType) : List JsonType :=
  match _h : t with
  | .union t1 t2 => t1.mkListFromUnion ++ t2.mkListFromUnion
  | _ => [t]

def JsonType.mkUnionFromList : List JsonType → JsonType
  | [] => .never
  | [t] => t
  | t::ts => .union t (mkUnionFromList ts)

theorem JsonType.mkList_correctness (t : JsonType) (x : Json) :
    t.check x = true ↔ t.mkListFromUnion.any (·.check x) := by
  unfold mkListFromUnion
  split
  · next t1 t2 =>
    simp [t1.mkList_correctness, t2.mkList_correctness]
  simp

theorem JsonType.mkUnion_correctness (ts : List JsonType) (x : Json) :
    ts.any (·.check x) = true ↔ (mkUnionFromList ts).check x = true := by
  unfold mkUnionFromList
  split
  · simpa using never_check_eq_false
  · next _ t => simp
  · next _ t ts _ => simp [mkUnion_correctness ts]

def JsonType.filterUnion (t : JsonType) (f : JsonType → Bool) : JsonType :=
  .mkUnionFromList (t.mkListFromUnion.filter f)

theorem JsonType.filterUnion_correctness
    {t : JsonType} {f : JsonType → Bool} {x : Json}
    (h : t.check x = true)
    (h' : ∀ t' ∈ t.mkListFromUnion, t'.check x = true → f t' = true) :
    (t.filterUnion f).check x = true := by
  unfold filterUnion
  rw [mkList_correctness] at h
  rw [← mkUnion_correctness, List.any_filter]
  simp only [List.any_eq_true, Bool.and_eq_true] at h ⊢
  obtain ⟨t', ht'_mem, ht'_check⟩ := h
  exact ⟨t', ht'_mem, h' t' ht'_mem ht'_check, ht'_check⟩

theorem JsonType.narrowMatch_correctness
    (t : JsonType) (key : String) (str : String) (x : Json)
    (h : x.getObjVal? key = .ok str) (h' : t.check x = true) :
    (t.filterUnion (·.canMatchPropertyStr key str)).check x = true :=
  filterUnion_correctness h' (fun _ _ ht'_check =>
    canMatchPropertyStr_correctness h ht'_check)

theorem JsonType.narrowMismatch_correctness
    (t : JsonType) (key : String) (str : String) (x : Json)
    (h : x.getObjVal? key ≠ .ok str) (h' : t.check x = true) :
    (t.filterUnion (·.canMismatchPropertyStr key str)).check x = true :=
  filterUnion_correctness h' (fun _ _ ht'_check =>
    canMismatchPropertyStr_correctness h ht'_check)

/-- Narrow a TypedJson based on observing that a field has a specific string value -/
def TypedJson.narrowKeyStr {t : JsonType} (tj : TypedJson t) (key : String) (str : String)
    (h : tj.val.getObjVal? key = .ok str) :
    TypedJson (t.filterUnion (·.canMatchPropertyStr key str)) :=
  ⟨tj.val, JsonType.narrowMatch_correctness t key str tj.val h tj.property⟩

/-- Narrow a TypedJson based on observing that a field doesn't have a specific string value -/
def TypedJson.narrowNotKeyStr {t : JsonType} (tj : TypedJson t) (key : String) (str : String)
    (h : tj.val.getObjVal? key ≠ .ok str) :
    TypedJson (t.filterUnion (·.canMismatchPropertyStr key str)) :=
  ⟨tj.val, JsonType.narrowMismatch_correctness t key str tj.val h tj.property⟩
