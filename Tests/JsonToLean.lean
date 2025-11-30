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

end Tests.JsonToLean
