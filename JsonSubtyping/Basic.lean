import JsonSubtyping.JsonLemmas

open Lean (Json)

/-- JSON type schema for TypeScript-like structural typing -/
inductive JsonType where
  | null
  | bool
  | number
  | string
  | any
  | never
  /-- String literal type -/
  | strLit (s : String)
  /-- Number literal type (using Int for simplicity) -/
  | numLit (n : Int)
  /-- Boolean literal type -/
  | boolLit (b : Bool)
  /-- Object type with required and optional fields -/
  | object (required : List (String × JsonType)) (optional : List (String × JsonType))
  /-- Tuple type -/
  | tuple (elements : List JsonType)
  /-- Array type -/
  | array (elementType : JsonType)
  /-- Union type -/
  | union (t1 t2 : JsonType)
  /-- Intersection type -/
  | inter (t1 t2 : JsonType)
  deriving Repr, BEq, Inhabited

instance : AndOp JsonType where
  and := JsonType.inter

instance : OrOp JsonType where
  or := JsonType.union

set_option linter.unusedVariables false in
/-- Check if a JSON value conforms to a JsonType schema -/
def JsonType.check (t : JsonType) (v : Json) : Bool :=
  match t with
  | .null => v.isNull
  | .bool => (v matches .bool _)
  | .number => (v matches .num _)
  | .string => (v matches .str _)
  | .any => true
  | .never => false
  | .strLit s => v.beq (.str s)
  | .numLit n => match v with
    | .num x => x == Lean.JsonNumber.fromInt n
    | _ => false
  | .boolLit b => v.beq (.bool b)
  | .array elemType => match v with
    | .arr xs => xs.all elemType.check
    | _ => false
  | .tuple elemTypes => match v with
    | .arr xs =>
      xs.size == elemTypes.length &&
      (xs.toList.zip elemTypes.attach).all fun (x, ⟨t, h⟩) => t.check x
    | _ => false
  | .union t1 t2 => t1.check v || t2.check v
  | .inter t1 t2 => t1.check v && t2.check v
  | .object required optional => match v with
    | .obj fields =>
      -- All required fields must be present and match their types
      (required.attach.all fun ⟨(name, fieldType), h⟩ =>
        match fields.get? name with
        | some fieldVal => fieldType.check fieldVal
        | none => false)
      &&
      -- All optional fields that are present must match their types
      (optional.attach.all fun ⟨(name, fieldType), h⟩ =>
        match fields.get? name with
        | some fieldVal => fieldType.check fieldVal
        | none => true)
    | _ => false
termination_by t
decreasing_by
  · simp only [array.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one]
  · simp +arith only [tuple.sizeOf_spec, ge_iff_le]
    suffices sizeOf t < sizeOf elemTypes by
      grind
    exact List.sizeOf_lt_of_mem h
  · simp +arith
  · simp +arith
  · simp +arith
  · simp +arith
  · simp +arith only [object.sizeOf_spec, ge_iff_le]
    have := List.sizeOf_lt_of_mem h
    have : sizeOf fieldType < sizeOf (name, fieldType) := by
      simp +arith
    grind
  · simp +arith only [object.sizeOf_spec, ge_iff_le]
    have := List.sizeOf_lt_of_mem h
    have : sizeOf fieldType < sizeOf (name, fieldType) := by
      simp +arith
    grind

/-- A JSON value that conforms to a specific JsonType schema -/
abbrev TypedJson (t : JsonType) := Subtype (t.check · = true)

namespace TypedJson

-- Basic constructors
-- We could use native_decide for this. Ordinary decide does _not_ work becuase we use
-- well-foundedness to prove things :(
def null : TypedJson .null := ⟨Json.null, by simp [JsonType.check, Json.isNull]⟩
def true : TypedJson .bool := ⟨.bool Bool.true, by simp [JsonType.check]⟩
def false : TypedJson .bool := ⟨.bool Bool.false, by simp [JsonType.check]⟩

-- Coercions from Lean types
instance : Coe String (TypedJson .string) where
  coe s := ⟨.str s, by simp [JsonType.check]⟩

instance : Coe Int (TypedJson .number) where
  coe n := ⟨.num (Lean.JsonNumber.fromInt n), by simp [JsonType.check]⟩

instance : Coe Nat (TypedJson .number) where
  coe n := ⟨.num (Lean.JsonNumber.fromInt n), by simp [JsonType.check]⟩

instance : Coe Bool (TypedJson .bool) where
  coe b := ⟨.bool b, by simp [JsonType.check]⟩

-- Literal type constructors
def strLit (s : String) : TypedJson (.strLit s) := ⟨.str s, by
    simp [JsonType.check, Json.beq_refl]
  ⟩
def numLit (n : Int) : TypedJson (.numLit n) := ⟨.num (Lean.JsonNumber.fromInt n), by simp [JsonType.check]⟩
def boolLit (b : Bool) : TypedJson (.boolLit b) := ⟨.bool b, by simp [JsonType.check, Json.beq_refl]⟩

-- Any type accepts anything
instance : Coe Json (TypedJson .any) where
  coe v := ⟨v, by simp [JsonType.check]⟩

end TypedJson
