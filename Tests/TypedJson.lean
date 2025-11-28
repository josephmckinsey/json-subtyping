import JsonSubtyping

open Lean (Json JsonNumber)
open TypedJson JsonType

def _test1 : TypedJson .null := null
def _test2 : TypedJson .bool := true
def _test3 : TypedJson .string := "hello"
def _test4 : TypedJson .number := (42 : Int)
def _test5 : TypedJson .number := 100
def _test6 : TypedJson (.strLit "specific") := strLit "specific"
def _test7 : TypedJson (.numLit 42) := numLit 42

-- Tests for TypedJson.coe (subtype coercion)

-- Literal to base type
def testStrLitToString : TypedJson .string :=
  (TypedJson.strLit "hello").coe

def testNumLitToNumber : TypedJson .number :=
  (TypedJson.numLit 42).coe

-- Coercion to any
def testStringToAny : TypedJson .any :=
  coe ("hello" : TypedJson .string)

-- String to union
def testStringToUnion : TypedJson (.string ||| .number) :=
  ("hello" : TypedJson .string).coe

-- Tuple to array
def testTupleToArray : TypedJson (.array .number) :=
  (.mk (Json.arr #[.num 1, .num 2, .num 3]) : TypedJson (tuple [.number, .number, .number])).coe

-- Intersection extraction
def testInterToString : TypedJson .string :=
  (.mk (Json.str "hello") : TypedJson (.string &&& .any)).coe

-- Object width subtyping
def testObjectWidth : TypedJson (object [("name", .string)] []) :=
  (.mk (Json.mkObj [("name", .str "Alice"), ("age", .num 30)]) :
   TypedJson (object [("name", .string), ("age", .number)] [])).coe

-- Object depth subtyping
def testObjectDepth : TypedJson (object [("name", .string)] []) :=
  (.mk (Json.mkObj [("name", .str "Alice")]) :
   TypedJson (object [("name", .strLit "Alice")] [])).coe

-- Array covariance
def testArrayCov : TypedJson (.array .any) :=
  (⟨Json.arr #[.num 1, .num 2], by native_decide⟩ : TypedJson (.array .number)).coe

-- Array construction
def testArr : TypedJson (.array .number) :=
  arr #[1, 2, 3]

-- Tuple construction
def testProd : TypedJson (tuple [.string, .number]) :=
  prod "hello" 42

def testTuple3 : TypedJson (tuple [.string, .number, .bool]) :=
  tuple3 "hello" 42 true

-- Object construction with obj{} notation
def testObjFields : ObjectFields [("name", .strLit "Alice"), ("age", .numLit 30)] :=
  obj{"name": .strLit "Alice", "age": .numLit 30}

def testObjFieldsRuntime (s : String) (n : Nat) : ObjectFields [("name", .strLit s), ("age", .numLit n)] :=
  obj{"name": .strLit s, "age": .numLit n}

def testMkObj (s : String) (n : Nat) : TypedJson (.object [("name", .string), ("age", .number)] []) :=
  mkObj obj{"name": (s : TypedJson .string), "age": (n : TypedJson .number)}
