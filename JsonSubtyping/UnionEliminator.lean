import JsonSubtyping.Basic
import JsonSubtyping.Subtype
import JsonSubtyping.JsonToLean
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

def unionExample : TypedJson (JsonType.number.union .string) :=
  ("hi" : TypedJson .string).coe

def testUnionElim : IO Unit :=
  unionExample.unionSplit
    (fun n => IO.println s!"A number: {n.toFloat}")
    (fun s => IO.println s!"A string: {s.toString}")

def JsonType.hasPropertyStr (t : JsonType) (key : String) (str : String) : Bool :=
  match t.getKey? key with
  | .some kt => (kt.subtype (.strLit str)).subtypeToBool
  | .none => false

def JsonType.canBeObject (t : JsonType) : Bool :=
  match t with
  | .object _ _ => true
  | .union t1 t2 => t1.canBeObject || t2.canBeObject
  | .inter t1 t2 => t1.canBeObject && t2.canBeObject
  | .any => true
  | _ => false

theorem JsonType.canBeObject_correctness
    (t : JsonType) (x : Json) (h : t.check x = true)
    (h' : t.canBeObject = false) :
    x.getObj? = .error "object expected" :=
  match t with
  | .object _ _ => by simp [canBeObject] at h'
  | .union t1 t2 => by
    simp only [canBeObject, Bool.or_eq_false_iff] at h'
    simp only [unionCheck, Bool.or_eq_true] at h
    rcases h with h | h
    · exact JsonType.canBeObject_correctness t1 x h h'.1
    exact JsonType.canBeObject_correctness t2 x h h'.2
  | .inter t1 t2 => by
    simp only [canBeObject, Bool.and_eq_false_iff] at h'
    simp only [interCheck, Bool.and_eq_true] at h
    rcases h' with h' | h'
    · exact JsonType.canBeObject_correctness t1 x h.1 h'
    exact JsonType.canBeObject_correctness t2 x h.2 h'
  | .any => by simp [canBeObject] at h'
  | .strLit _ | .boolLit _ | .numLit _ | .number | .never
  | .null | .array _ | .string | .bool | .tuple _h => by
    rcases x <;> simp [JsonType.check, Json.beq, Json.isNull] at h
    <;> {
      simp [Json.getObj?]
      exact rfl
    }

theorem JsonType.canBeObject_correctness'
    (t : JsonType) (key : String) (x : Json) (h : t.check x = true)
    (h' : t.canBeObject = false) :
    x.getObjVal? key = .error "object expected" := by
  have := t.canBeObject_correctness x h h'
  simp [Json.getObj?] at this
  rcases x <;> {
    simp [Json.getObjVal?] at ⊢ this
    try rfl
    try contradiction
  }

def JsonType.notHasPropertyStr (t : JsonType) (key : String) (str : String) : Bool :=
  t.canBeObject == false ||
  match t.getKey? key with
  | .some kt => kt.check str == false
  | .none => false -- we have no information about key


theorem JsonType.hasPropertyStr_correctness
    (t : JsonType) (key : String) (str : String)
    (h : t.hasPropertyStr key str = true)
    (h' : t.check x = true) : x.getObjVal? key = .ok str := by
  simp [hasPropertyStr] at h
  match getKeyEq : t.getKey? key with
  | some kt =>
    simp only [getKeyEq] at h
    obtain ⟨y, yh, yh'⟩ := getKey?_correctness h' getKeyEq
    have := DecideSubtype.toBool_correct _ h y yh'
    simp [check] at this
    grind
  | none => simp [getKeyEq] at h


theorem JsonType.notHasPropertyStr_correctness
    (t : JsonType) (key : String) (str : String)
    (h : t.notHasPropertyStr key str = true)
    (h' : t.check x = true) : x.getObjVal? key ≠ .ok str := by
  simp [notHasPropertyStr] at h
  if isObject : t.canBeObject = false then
    simp [t.canBeObject_correctness' key x h' isObject]
  else
  simp only [Bool.not_eq_false _ ▸ isObject, Bool.true_eq_false, false_or] at h
  match getKeyEq : t.getKey? key with
  | some kt =>
    simp only [getKeyEq] at h
    obtain ⟨y, yh, yh'⟩ := getKey?_correctness h' getKeyEq
    intro neg
    rw [yh, Except.ok.injEq] at neg
    rw [neg] at yh'
    simp [yh'] at h
  | none => simp [getKeyEq] at h

/-!
The contrapositives are in fact what we actually want
for narrowing.

Within an if statement where x.getObjVal? key = some str,
t.notHasPropertyStr key str = false.

Within an if statement where x.getObjVal? key ≠ some str,
then t.hasPropertyStr key str = false.

If we have a type which is a bunch of unions,
then we can filter them according to these properties.
-/
