import JsonSubtyping.JsonLemmas

open Lean (Json JsonNumber)
open Lean.Json (mkObj)

-- Test that our custom Json.beq matches Lean's original built-in BEq instance
-- We use @BEq.beq to explicitly select which instance

-- Helper to check equivalence between custom beq and stdlib beq
def checkEquiv (x y : Json) : Bool :=
  Json.beq x y == @BEq.beq _ Lean.Json.instBEq x y

-- Primitives: null
#guard checkEquiv .null .null
#guard checkEquiv .null (.bool false)

-- Primitives: booleans
#guard checkEquiv (.bool true) (.bool true)
#guard checkEquiv (.bool false) (.bool false)
#guard checkEquiv (.bool true) (.bool false)
#guard checkEquiv (.bool true) .null

-- Primitives: numbers
#guard checkEquiv (.num 0) (.num 0)
#guard checkEquiv (.num 42) (.num 42)
#guard checkEquiv (.num 3.14) (.num 3.14)
#guard checkEquiv (.num 1) (.num 2)
#guard checkEquiv (.num 1) (.str "1")

-- Primitives: strings
#guard checkEquiv (.str "") (.str "")
#guard checkEquiv (.str "hello") (.str "hello")
#guard checkEquiv (.str "a") (.str "b")
#guard checkEquiv (.str "test") (.num 42)

-- Arrays: empty and simple
#guard checkEquiv (.arr #[]) (.arr #[])
#guard checkEquiv (.arr #[.num 1]) (.arr #[.num 1])
#guard checkEquiv (.arr #[.num 1, .num 2, .num 3]) (.arr #[.num 1, .num 2, .num 3])
#guard checkEquiv (.arr #[.str "a", .str "b"]) (.arr #[.str "a", .str "b"])

-- Arrays: different values
#guard checkEquiv (.arr #[.num 1]) (.arr #[.num 2])
#guard checkEquiv (.arr #[.num 1, .num 2]) (.arr #[.num 1])
#guard checkEquiv (.arr #[.num 1]) (.arr #[.num 1, .num 2])
#guard checkEquiv (.arr #[.num 1, .num 2]) (.arr #[.num 2, .num 1])

-- Arrays: nested
#guard checkEquiv (.arr #[.arr #[.num 1, .num 2], .arr #[.num 3]])
                  (.arr #[.arr #[.num 1, .num 2], .arr #[.num 3]])
#guard checkEquiv (.arr #[.arr #[.num 1]]) (.arr #[.arr #[.num 2]])

-- Arrays: mixed types
#guard checkEquiv (.arr #[.null, .bool true, .num 42, .str "test"])
                  (.arr #[.null, .bool true, .num 42, .str "test"])

-- Objects: empty and simple
#guard checkEquiv (mkObj []) (mkObj [])
#guard checkEquiv (mkObj [("name", .str "Alice")]) (mkObj [("name", .str "Alice")])
#guard checkEquiv (mkObj [("age", .num 30), ("name", .str "Bob")])
                  (mkObj [("age", .num 30), ("name", .str "Bob")])

-- Objects: different values
#guard checkEquiv (mkObj [("a", .num 1)]) (mkObj [("a", .num 2)])
#guard checkEquiv (mkObj [("a", .num 1)]) (mkObj [("b", .num 1)])
#guard checkEquiv (mkObj [("a", .num 1), ("b", .num 2)]) (mkObj [("a", .num 1)])

-- Objects: nested
#guard checkEquiv (mkObj [("person", mkObj [("name", .str "Alice")])])
                  (mkObj [("person", mkObj [("name", .str "Alice")])])
#guard checkEquiv (mkObj [("x", mkObj [("y", .num 1)])]) (mkObj [("x", mkObj [("y", .num 2)])])

-- Objects: with arrays
#guard checkEquiv (mkObj [("nums", .arr #[.num 1, .num 2, .num 3])])
                  (mkObj [("nums", .arr #[.num 1, .num 2, .num 3])])
#guard checkEquiv (mkObj [("nums", .arr #[.num 1])]) (mkObj [("nums", .arr #[.num 2])])

-- Complex nested structure
def complexJson : Json := mkObj [
  ("id", .num 1),
  ("name", .str "test"),
  ("active", .bool true),
  ("tags", .arr #[.str "a", .str "b"]),
  ("meta", mkObj [("created", .str "2024-01-01"), ("count", .num 5)])
]

def complexJson2 : Json := mkObj [
  ("id", .num 1),
  ("name", .str "different"),
  ("active", .bool true),
  ("tags", .arr #[.str "a", .str "b"]),
  ("meta", mkObj [("created", .str "2024-01-01"), ("count", .num 5)])
]

#guard checkEquiv complexJson complexJson
#guard checkEquiv complexJson complexJson2
