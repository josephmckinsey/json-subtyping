import JsonSubtyping.Basic

open Lean (Json)

def JsonType.toString_of_check {x : Json} (h : string.check x) : String := by
  rcases x <;> simp [check] at h
  next s => exact s

theorem JsonType.toString_eq {x : Json} (h : string.check x) :
  x = .str (toString_of_check h)  := by
  rcases x <;> unfold toString_of_check <;> simp [check] at h ⊢

def JsonType.toJsonNumber_from_check {x : Json} (h : number.check x) : Lean.JsonNumber := by
  rcases x <;> simp [check] at h
  next n => exact n

theorem JsonType.toJsonNumber_eq {x : Json} (h : number.check x) :
  x = .num (toJsonNumber_from_check h)  := by
  rcases x <;> unfold toJsonNumber_from_check <;> simp [check] at h ⊢

def JsonType.toBool_from_check {x : Json} (h : bool.check x) : Bool := by
  rcases x <;> simp [check] at h
  next b => exact b

theorem JsonType.toBool_eq {x : Json} (h : bool.check x) :
  x = .bool (toBool_from_check h)  := by
  rcases x <;> unfold toBool_from_check <;> simp [check] at h ⊢

namespace TypedJson

def toString : TypedJson .string → String
  | ⟨_, property⟩ => JsonType.toString_of_check property

theorem toString_eq {tj : TypedJson .string} : tj = tj.toString := by
  simp [toString, <-JsonType.toString_eq]

def toJsonNumber : TypedJson .number → Lean.JsonNumber
  | ⟨_, property⟩ => JsonType.toJsonNumber_from_check property

theorem toJsonNumber_eq {tj : TypedJson .number} : tj = tj.toJsonNumber := by
  simp [toJsonNumber, <-JsonType.toJsonNumber_eq]

def toFloat (j : TypedJson .number) : Float := j.toJsonNumber.toFloat

def toBool : TypedJson .bool → Bool
  | ⟨_, property⟩ => JsonType.toBool_from_check property

theorem toBool_eq {tj : TypedJson .bool} : tj = tj.toBool := by
  simp [toBool, <-JsonType.toBool_eq]

/-! ## Tuple Destructuring -/

theorem tupleLength (ts : List JsonType) (xs : List Json)
    (h : tupleCheckRec ts (fun t _h => t.check) xs) :
    xs.length = ts.length := by
  induction xs generalizing ts with
  | nil => simp [tupleCheckRec] at h; simp [h]
  | cons x xs ih =>
    unfold tupleCheckRec at h
    cases ts with
    | nil => simp at h
    | cons t ts =>
      simp at h
      replace ih := ih ts h.2
      grind

theorem tupleCheckAux (ts : List JsonType) (xs : List Json)
    (h : tupleCheckRec ts (fun t _h => t.check) xs) (i : Nat) (mem : i < ts.length)
    (mem' : i < xs.length) :
    ts[i].check xs[i] := by
  induction xs generalizing ts i with
  | nil => simp at mem'
  | cons x xs ih =>
    unfold tupleCheckRec at h
    cases ts with
    | nil => simp at h
    | cons t ts =>
      simp at h
      rw [List.getElem_cons, List.getElem_cons]
      cases i with
      | zero => simpa using h.1
      | succ i => simpa using (
        ih ts h.2 i (by simp at mem; omega) (by simp at mem'; omega)
      )

def tupleCheck (ts : List JsonType) (xs : List Json)
    (h : tupleCheckRec ts (fun t _h => t.check) xs) (i : Nat) (mem : i < ts.length) :=
  tupleCheckAux ts xs h i mem (tupleLength ts xs h ▸ mem)

/-- Extract components from a 2-element tuple -/
def toProd {t1 t2 : JsonType} (tj : TypedJson (.tuple [t1, t2])) : (TypedJson t1 × TypedJson t2) :=
  match tj with
  | ⟨val, h⟩ =>
    match val with
    | .arr arr => by
      simp only [JsonType.check] at h
      have arrSize : arr.size = 2 := by
        rw [Array.size_eq_length_toList, tupleLength [t1, t2] _ h]
        simp
      refine ⟨⟨arr[0], ?_⟩, ⟨arr[1], ?_⟩⟩
      · exact tupleCheck [t1, t2] arr.toList h 0 (by simp)
      exact tupleCheck [t1, t2] arr.toList h 1 (by simp)
    | .null | .bool _ | .num _ | .str _ | .obj _ => by
      simp [JsonType.check] at h

/-- Extract components from a 3-element tuple -/
def toProd3 {t1 t2 t3 : JsonType} (tj : TypedJson (.tuple [t1, t2, t3])) : (TypedJson t1 × TypedJson t2 × TypedJson t3) :=
  match tj with
  | ⟨val, h⟩ =>
    match val with
    | .arr arr => by
      simp only [JsonType.check] at h
      have arrSize : arr.size = 3 := by
        rw [Array.size_eq_length_toList, tupleLength [t1, t2, t3] _ h]
        simp
      refine ⟨⟨arr[0], ?_⟩, ⟨arr[1], ?_⟩, ⟨arr[2], ?_⟩⟩
      · exact tupleCheck [t1, t2, t3] arr.toList h 0 (by simp)
      · exact tupleCheck [t1, t2, t3] arr.toList h 1 (by simp)
      exact tupleCheck [t1, t2, t3] arr.toList h 2 (by simp)
    | .null | .bool _ | .num _ | .str _ | .obj _ => by
      simp [JsonType.check] at h

/-! ## Array Extraction -/

/-- Extract an `Array (TypedJson t)` from a `TypedJson (.array t)`.
    This is the inverse of the `arr` constructor and enables using all standard
    Lean array operations (indexing, head?, tail, map, filter, etc.). -/
def toArray {elemType : JsonType} (arr : TypedJson (.array elemType)) :
    Array (TypedJson elemType) :=
  match arr with
  | ⟨.arr xs, property⟩ =>
      xs.attach.map fun ⟨x, mem⟩ =>
        ⟨x, by
          simp only [JsonType.check] at property
          rw [Array.all_eq_true'] at property
          exact property x mem
        ⟩
  | ⟨.null, property⟩ => by simp [JsonType.check] at property
  | ⟨.bool _, property⟩ => by simp [JsonType.check] at property
  | ⟨.num _, property⟩ => by simp [JsonType.check] at property
  | ⟨.str _, property⟩ => by simp [JsonType.check] at property
  | ⟨.obj _, property⟩ => by simp [JsonType.check] at property

end TypedJson
