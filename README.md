# json-subtyping

This is a gradual subtype system for JSON in Lean. JSON
properties are described using `JsonType`s which mirrors
TypeScript's type definitions.

```lean
-- JsonType Constructors
null, bool, number, string, any, never
strLit "ok", numLit 42, boolLit true
t1 ||| t2 -- union
t1 &&& t2 -- intersection
array t1
tuple [t1, t2, t3]
object [(k1, t1)] [(k2, t2)] -- required and optional 
```

You can use `JsonType`s to check a `Json` value with `JsonType.check`. You can also bundle the type check in `TypedJson`:

```lean
/-- A JSON value that conforms to a specific JsonType schema -/
structure TypedJson (t : JsonType) where
  val : Json
  property : t.check val = true := by native_decide
```

The interface for `TypedJson` lets you:
- Safe property access with `(x : TypedJson t).get`
- Safe coercions `(x : TypedJson t).toString`, etc.
- Subtype coercion with `(x : TypedJson t).coe`
- Compile-time type-checked object construction
- Some type narrowing

All operations do nothing to the `Json` and only manipulate the `property` in a `TypedJson` using theorems and decision procedures. By constructing functions on `JsonType`, we can prove properties about results such as `x.getObjVal? key` or subtyping relationships between `JsonType`. The **proofs** of new `t.check x` propositions are used to construct new `TypedJson`.

## Example Usage

```lean
import JsonSubtyping.UnionEliminator
import JsonSubtyping.JsonToLean
import JsonSubtyping.Constructors

/-! # JSON Subtyping Example: API Response Handling -/

-- Define discriminated union for API responses
def successType : JsonType := .object [("status", .strLit "ok"), ("data", .string)] []
def errorType : JsonType := .object [("status", .strLit "error"), ("message", .string)] []
def responseType : JsonType := successType ||| errorType

-- Create responses
def successResp : TypedJson responseType :=
  (TypedJson.mkObj obj{
    "status": .strLit "ok",
    "data": ("Hello" : TypedJson .string)
  }).coe -- You can automatically coerce to a super-type
  -- The appropriate subtype will be checked automatically.

def errorResp : TypedJson responseType :=
  -- Or you can check Json types using native_decide
  ⟨Lean.Json.mkObj [
    ("status", "error"),
    ("message", "Not found")
  ], by native_decide⟩

-- Handle response with type narrowing
def handleResponse (resp : TypedJson responseType) : IO Unit := do
  match h : resp.val.getObjVal? "status" with
  | .ok "ok" =>
    let success : TypedJson successType := (resp.narrowKeyStr "status" "ok" h).coe
    -- Field access is checked
    let data := success.get "data"
    IO.println s!"Success: {data.toString}"
  | .ok "error" =>
    let error : TypedJson errorType := (resp.narrowKeyStr "status" "error" h).coe
    let msg := error.get "message"
    IO.println s!"Error: {msg.toString}"
  | _ => IO.println "Unknown status"

-- Array processing
def scoreType : JsonType := .array .number
def scores : TypedJson scoreType := TypedJson.arr #[95, 87, 92]

def average (arr : TypedJson scoreType) : Float :=
  let elements := arr.toArray
  elements.foldl (fun sum x => sum + x.toFloat) 0 / elements.size.toFloat

-- Tuple destructuring
def pointType : JsonType := .tuple [.number, .number]
def point : TypedJson pointType := TypedJson.prod 3 4

def distance (p : TypedJson pointType) : Float :=
  let (x, y) := p.toProd
  Float.sqrt (x.toFloat ^ 2 + y.toFloat ^ 2)

def main : IO Unit := do
  handleResponse successResp
  handleResponse errorResp
  IO.println ""
  IO.println s!"Average score: {average scores}"
  IO.println s!"Distance: {distance point}"

/--
info: Success: Hello
Error: Not found

Average score: 91.333333
Distance: 5.000000
-/
#guard_msgs in
#eval main
```

## Why do this?

After spending far too long converting JSON Schema to `inductive` declarations, I decided that this was in general a better approach for compile-time support for complex JSON configuration such as for plotting libraries like VegaLite. When every field can be a `String` or an `ExprRef`, some automatic subtyping can come in handy.

## Caveats

In TypeScript, `any` is an escape hatch equal to all types, but here `any` refers to top of the type system where we have no properties. This is known as `unknown` in TypeScript.

I've vibe-coded some proofs with CLAUDE.md. Since everything is in fact proved here, I feel pretty comfortable with this.
