import JsonSubtyping.UnionEliminator
import JsonSubtyping.JsonToLean

open Lean (Json)

-- Basic union elimination test
def unionExample : TypedJson (JsonType.number.union .string) :=
  ("hi" : TypedJson .string).coe

def testUnionElim : IO Unit :=
  unionExample.unionSplit
    (fun n => IO.println s!"A number: {n.toFloat}")
    (fun s => IO.println s!"A string: {s.toString}")

def circleType : JsonType :=
  .object [("type", .strLit "circle"), ("radius", .number)] []

def squareType : JsonType :=
  .object [("type", .strLit "square"), ("side", .number)] []

def shapeType : JsonType := circleType.union squareType

def calculateArea (shape : TypedJson shapeType) : IO Unit := do
  match h : shape.val.getObjVal? "type" with
  | .ok "circle" =>
    let circle : TypedJson circleType := (shape.narrowKeyStr "type" "circle" h).coe
    IO.println "Computing circle area"
  | .ok "square" =>
    let square : TypedJson squareType := (shape.narrowKeyStr "type" "square" h).coe
    IO.println "Computing square area"
  | _ => IO.println "Unknown shape type"

-- Note: narrowNotKeyStr is useful in else branches or when you have explicit proof of inequality
example (shape : TypedJson shapeType)
    (h : shape.val.getObjVal? "type" ≠ .ok "circle") :
    TypedJson squareType :=
  (shape.narrowNotKeyStr "type" "circle" h).coe
