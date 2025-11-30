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

end TypedJson
