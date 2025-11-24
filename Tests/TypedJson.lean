import JsonSubtyping

open Lean (Json JsonNumber)
open TypedJson

def _test1 : TypedJson .null := null
def _test2 : TypedJson .bool := true
def _test3 : TypedJson .string := "hello"
def _test4 : TypedJson .number := (42 : Int)
def _test5 : TypedJson .number := 100
def _test6 : TypedJson (.strLit "specific") := strLit "specific"
def _test7 : TypedJson (.numLit 42) := numLit 42
