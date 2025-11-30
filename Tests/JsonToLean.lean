import JsonSubtyping.Basic
import JsonSubtyping.JsonToLean
import JsonSubtyping.Constructors

open Lean (Json)

namespace Tests.JsonToLean

def testString : TypedJson .string := "hello"

def testNumber : TypedJson .number := 42

def testBool : TypedJson .bool := true

def testNegativeNumber : TypedJson .number := (-100 : Int)

def testDecimalNumber : TypedJson .number :=
  .mk (.num ⟨12345, 3⟩)

example : testString.toString = "hello" := rfl

example : testNumber.toJsonNumber = ⟨42, 0⟩ := rfl

example : testNumber.toFloat == 42.0 := by native_decide

example : testBool.toBool = true := rfl

example : testNegativeNumber.toJsonNumber = ⟨-100, 0⟩ := rfl

example : testDecimalNumber.toJsonNumber = ⟨12345, 3⟩ := rfl

example : testDecimalNumber.toFloat == 12.345 := by native_decide

def testProd : TypedJson (.tuple [.number, .string]) := .prod 3 "3"

example : testProd.toProd == ((3 : TypedJson .number), ("3" : TypedJson .string)) := by native_decide

def testTuple3 : TypedJson (.tuple [.number, .string, .array .number]) := .tuple3 3 "3" (.arr #[3])

example : testTuple3.toProd3 = (
    (3 : TypedJson .number),
    ("3" : TypedJson .string),
    (.arr #[3] : TypedJson (.array .number))
  ) := rfl

/-! ## Array Extraction Tests -/

-- Basic extraction
def testArray : TypedJson (.array .number) := .arr #[1, 2, 3]

example : testArray.toArray[0]? == some (1 : TypedJson .number) := by native_decide
example : testArray.toArray[2]? == some (3 : TypedJson .number) := by native_decide

-- Empty array
def emptyArray : TypedJson (.array .string) := .arr #[]

example : emptyArray.toArray.size = 0 := by native_decide
example : emptyArray.toArray.isEmpty = true := by native_decide

-- Iteration using foldl (demonstrates real usage)
def sumArray (arr : TypedJson (.array .number)) : Float :=
  let xs := arr.toArray
  xs.foldl (fun acc x => acc + x.toFloat) 0.0

#eval sumArray testArray  -- Should print 6.0

-- Nested arrays (demonstrates chaining toArray calls)
def nestedArray : TypedJson (.array (.array .number)) :=
  .arr #[.arr #[1, 2], .arr #[3, 4]]

example : nestedArray.toArray[0]!.toArray[0]! == (1 : TypedJson .number) := by native_decide
example : nestedArray.toArray[0]!.toArray[1]! == (2 : TypedJson .number) := by native_decide
example : nestedArray.toArray[1]!.toArray[0]! == (3 : TypedJson .number) := by native_decide
example : nestedArray.toArray[1]!.toArray[1]! == (4 : TypedJson .number) := by native_decide

-- Round-trip: arr → toArray → arr (proves correctness)
example : (.arr testArray.toArray) == testArray := by native_decide
example : (.arr emptyArray.toArray) == emptyArray := by native_decide

-- Array mapping example (demonstrates standard operations work)
def doubleArray (arr : TypedJson (.array .number)) : Array (TypedJson .number) :=
  arr.toArray.map (fun x => ⟨.num (⟨x.toJsonNumber.mantissa * 2, x.toJsonNumber.exponent⟩), by simp [JsonType.check]⟩)

-- String extraction example (demonstrates composition with toString)
def stringArray : TypedJson (.array .string) := .arr #["hello", "world", "!"]
example : stringArray.toArray[0]!.toString = "hello" := by native_decide

end Tests.JsonToLean
