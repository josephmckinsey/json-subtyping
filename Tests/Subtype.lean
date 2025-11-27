import JsonSubtyping

open JsonType

-- Test runner
def runTests (tests : List (JsonType × JsonType × Bool)) : Bool :=
  tests.all fun (t1, t2, expected) =>
    match (t1.subtype t2) with
    | .isSubtype _ => expected
    | .none => !expected

def filterOutTests (tests : List (JsonType × JsonType × Bool)) :
    List (JsonType × JsonType × Bool) :=
  tests.filter fun (t1, t2, expected) =>
    !match (t1.subtype t2) with
    | .isSubtype _ => expected
    | .none => !expected


-- Trivial subtyping tests
def trivialTests : List (JsonType × JsonType × Bool) := [
  -- Reflexivity
  (string, string, true),
  (number, number, true),
  (bool, bool, true),
  -- any is a supertype of everything
  (string, any, true),
  (number, any, true),
  (bool, any, true),
  (null, any, true),
  -- never is a subtype of everything
  (never, string, true),
  (never, number, true),
  (never, any, true),
  -- Non-matching primitives
  (string, number, false),
  (number, bool, false),
  (bool, null, false)
]

#guard runTests trivialTests

-- Array subtyping tests
def arrayTests : List (JsonType × JsonType × Bool) := [
  -- Covariant arrays
  (array number, array number, true),
  (array number, array any, true),
  (array never, array number, true),
  -- Arrays don't match non-arrays
  (array number, number, false),
  (string, array string, false)
]

#guard runTests arrayTests

-- Tuple subtyping tests
def tupleTests : List (JsonType × JsonType × Bool) := [
  -- Tuple to tuple (same length, covariant)
  (tuple [number, string], tuple [number, string], true),
  (tuple [number, string], tuple [any, any], true),
  (tuple [never, never], tuple [number, string], true),
  -- Tuple to tuple (different lengths)
  (tuple [number], tuple [number, string], false),
  (tuple [number, string], tuple [number], false),
  -- Tuple to array
  (tuple [number, number, number], array number, true),
  (tuple [number, string], array any, true),
  (tuple [number, string], array number, false),  -- not all elements are numbers
  -- Empty tuple
  (tuple [], tuple [], true),
  (tuple [], array number, true)
]

#guard runTests tupleTests

-- Union subtyping tests
def unionTests : List (JsonType × JsonType × Bool) := [
  -- Subtype if it matches either side
  (string, string ||| number, true),
  (number, string ||| number, true),
  (bool, string ||| number, false),
  -- Union is not a subtype unless we match one side
  (string ||| number, string, false),
  (string ||| number, any, true)
]

#guard runTests unionTests

-- Intersection subtyping tests
def intersectionTests : List (JsonType × JsonType × Bool) := [
  -- Intersection is a subtype of both sides
  (string &&& any, string, true),
  (string &&& any, any, true),
  -- Other types are not subtypes of intersections (generally)
  (string, string &&& any, true),  -- actually true since string <: any
  (number, string &&& any, false)
]

#guard runTests intersectionTests

-- Object subtyping tests
def objectTests : List (JsonType × JsonType × Bool) := [
  -- Width subtyping (extra fields ok)
  (object [("name", string), ("age", number)] [],
   object [("name", string)] [],
   true),

  -- Missing required field
  (object [("age", number)] [],
   object [("name", string)] [],
   false),

  -- Depth subtyping (covariant field types)
  (object [("name", strLit "Alice")] [],
   object [("name", string)] [],
   true),

  -- Required fields can satisfy optional fields
  (object [("id", number), ("name", string)] [],
   object [("id", number)] [("name", string)],
   true),

  -- Optional fields can be missing when they exist in subtype
  (object [("id", number)] [("name", string)],
   object [("id", number)] [("name", string)],
   true),

  -- Incompatible types for shared optional field
  (object [("name", number)] [],
   object [] [("name", string)],
   false),

  -- Optional field in subtype, required in supertype - not ok
  (object [("id", number)] [("name", string)],
   object [("id", number), ("name", string)] [],
   false),

  -- Empty objects
  (object [] [], object [] [], true),
  (object [("x", number)] [], object [] [], true),

  -- An empty object type accepts {x: 42}, but {x?: string} does not
  (object [] [],
   object [] [("x", string)],
   false),  -- Should be false, but current implementation returns true!

  -- Related: object with unconstrained field should not be subtype of object with constrained optional field
  (object [("y", number)] [],
   object [] [("x", string)],
   false),

  -- But this should work: optional field exists in both
  (object [] [("x", string)],
   object [] [("x", any)],
   true)
]

#guard runTests objectTests

-- Literal type tests
def literalTests : List (JsonType × JsonType × Bool) := [
  -- String literals
  (strLit "hello", strLit "hello", true),
  (strLit "hello", string, true),
  (strLit "hello", strLit "world", false),
  (string, strLit "hello", false),

  -- Number literals
  (numLit 42, numLit 42, true),
  (numLit 42, number, true),
  (numLit 42, numLit 43, false),
  (number, numLit 42, false),

  -- Bool literals
  (boolLit true, boolLit true, true),
  (boolLit true, bool, true),
  (boolLit true, boolLit false, false),
  (bool, boolLit true, false)
]

#guard runTests literalTests
