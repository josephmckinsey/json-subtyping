import Lean.Data.Json

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

/-- Check if a JSON value conforms to a JsonType schema -/
def JsonType.check (t : JsonType) (v : Json) : Bool :=
  match t with
  | .null => v.isNull
  | .bool => (v matches .bool _)
  | .number => (v matches .num _)
  | .string => (v matches .str _)
  | .any => true
  | .never => false
  | .strLit s => v == .str s
  | .numLit n => match v with
    | .num x => x == Lean.JsonNumber.fromInt n
    | _ => false
  | .boolLit b => v == .bool b
  | .array elemType => match v with
    | .arr xs => xs.all elemType.check
    | _ => false
  | .tuple elemTypes => match v with
    | .arr xs =>
      xs.size == elemTypes.length &&
      (xs.toList.zip elemTypes).all fun (x, t) => t.check x
    | _ => false
  | .union t1 t2 => t1.check v || t2.check v
  | .inter t1 t2 => t1.check v && t2.check v
  | .object required optional => match v with
    | .obj fields =>
      -- All required fields must be present and match their types
      required.all fun (name, fieldType) =>
        match fields.get? name with
        | some fieldVal => fieldType.check fieldVal
        | none => false
      &&
      -- All optional fields that are present must match their types
      optional.all fun (name, fieldType) =>
        match fields.get? name with
        | some fieldVal => fieldType.check fieldVal
        | none => true
    | _ => false
