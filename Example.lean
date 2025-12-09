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
  }).coe

def errorResp : TypedJson responseType :=
  ⟨Lean.Json.mkObj [
    ("status", "error"),
    ("message", "Not found")
  ], by native_decide⟩

-- Handle response with type narrowing
def handleResponse (resp : TypedJson responseType) : IO Unit := do
  match h : resp.val.getObjVal? "status" with
  | .ok "ok" =>
    let success : TypedJson successType := (resp.narrowKeyStr "status" "ok" h).coe
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
