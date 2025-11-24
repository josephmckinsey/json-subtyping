import JsonSubtyping

open Lean (Json JsonNumber)
open Lean.Json (mkObj)
open JsonType

-- Test runner
def runTests (tests : List (JsonType × Json × Bool)) : Bool :=
  tests.all fun (t, v, expected) => t.check v == expected

-- Primitive type tests
def primitiveTests : List (JsonType × Json × Bool) := [
  -- null
  (null, Json.null, true),
  (null, .bool false, false),
  (null, .num 42, false),
  -- bool
  (bool, .bool true, true),
  (bool, .bool false, true),
  (bool, Json.null, false),
  (bool, .num 1, false),
  -- number
  (number, .num 42, true),
  (number, .num 3.14, true),
  (number, .str "42", false),
  -- string
  (string, .str "hello", true),
  (string, .str "", true),
  (string, .num 42, false),
  -- any
  (any, Json.null, true),
  (any, .bool true, true),
  (any, .num 42, true),
  (any, .str "x", true),
  -- never
  (never, Json.null, false),
  (never, .bool true, false),
  (never, .num 42, false)
]

#guard runTests primitiveTests

-- Literal type tests
def literalTests : List (JsonType × Json × Bool) := [
  (strLit "hello", .str "hello", true),
  (strLit "hello", .str "world", false),
  (strLit "hello", .num 42, false),
  (numLit 42, .num 42, true),
  (numLit 42, .num 43, false),
  (numLit 42, .str "42", false),
  (boolLit true, .bool true, true),
  (boolLit true, .bool false, false),
  (boolLit false, .bool false, true)
]

#guard runTests literalTests

-- Array type tests
def arrayTests : List (JsonType × Json × Bool) := [
  (array number, .arr #[.num 1, .num 2, .num 3], true),
  (array number, .arr #[], true),
  (array number, .arr #[.num 1, .str "x"], false),
  (array string, .arr #[.str "a", .str "b"], true),
  (array any, .arr #[.num 1, .str "x", .bool true], true)
]

#guard runTests arrayTests

-- Tuple type tests
def tupleTests : List (JsonType × Json × Bool) := [
  (tuple [number, string], .arr #[.num 42, .str "hello"], true),
  (tuple [number, string], .arr #[.str "hello", .num 42], false),
  (tuple [number, string], .arr #[.num 42], false),
  (tuple [number, string], .arr #[.num 42, .str "hello", .bool true], false),
  (tuple [], .arr #[], true)
]

#guard runTests tupleTests

-- Union and intersection tests
def combinatorTests : List (JsonType × Json × Bool) := [
  -- unions
  (string ||| number, .str "hello", true),
  (string ||| number, .num 42, true),
  (string ||| number, .bool true, false),
  (string ||| null, .str "hello", true),
  (string ||| null, Json.null, true),
  -- intersections
  (any &&& string, .str "hello", true),
  (any &&& string, .num 42, false),
  (string &&& number, .str "hello", false)
]

#guard runTests combinatorTests

-- Object type definitions
def simpleObj : JsonType := object [("name", string), ("age", number)] []
def withOptional : JsonType := object [("id", number)] [("name", string)]
def circleType : JsonType := object [("kind", strLit "circle"), ("radius", number)] []
def rectType : JsonType := object [("kind", strLit "rect"), ("width", number), ("height", number)] []
def shapeType : JsonType := circleType ||| rectType
def nestedType : JsonType := object [("data", array number)] []
def personArray : JsonType := array (object [("name", string)] [])

-- Object tests
def objectTests : List (JsonType × Json × Bool) := [
  -- required fields
  (simpleObj, mkObj [("name", .str "Alice"), ("age", .num 30)], true),
  (simpleObj, mkObj [("name", .str "Alice")], false),  -- missing age
  (simpleObj, mkObj [("age", .num 30)], false),  -- missing name
  (simpleObj, mkObj [("name", .num 123), ("age", .num 30)], false),  -- wrong type
  (simpleObj, mkObj [("name", .str "Alice"), ("age", .num 30), ("extra", .bool true)], true),  -- extra ok
  -- optional fields
  (withOptional, mkObj [("id", .num 1)], true),
  (withOptional, mkObj [("id", .num 1), ("name", .str "test")], true),
  (withOptional, mkObj [("id", .num 1), ("name", .num 123)], false),  -- wrong type for optional
  (withOptional, mkObj [("name", .str "test")], false),  -- missing required
  -- discriminated unions
  (shapeType, mkObj [("kind", .str "circle"), ("radius", .num 5)], true),
  (shapeType, mkObj [("kind", .str "rect"), ("width", .num 10), ("height", .num 20)], true),
  (shapeType, mkObj [("kind", .str "circle"), ("width", .num 10)], false),
  (shapeType, mkObj [("kind", .str "triangle"), ("base", .num 10)], false),
  -- nested types
  (nestedType, mkObj [("data", .arr #[.num 1, .num 2, .num 3])], true),
  (nestedType, mkObj [("data", .arr #[])], true),
  (nestedType, mkObj [("data", .arr #[.str "x"])], false),
  -- array of objects
  (personArray, .arr #[mkObj [("name", .str "Alice")], mkObj [("name", .str "Bob")]], true),
  (personArray, .arr #[mkObj [("name", .str "Alice")], mkObj [("age", .num 30)]], false)
]

#guard runTests objectTests
