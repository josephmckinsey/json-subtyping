import JsonSubtyping.JsonLemmas
import JsonSubtyping.ListAttach

open Lean (Json)

/-- JSON type schema for TypeScript-like structural typing -/
inductive JsonType where
  | null
  | bool
  | number
  | string
  | any
  | never
  /-- String literal type -/
  | strLit (s : String)
  /-- Number literal type (using Int for simplicity) -/
  | numLit (n : Int)
  /-- Boolean literal type -/
  | boolLit (b : Bool)
  /-- Object type with required and optional fields -/
  | object (required : List (String × JsonType)) (optional : List (String × JsonType))
  /-- Tuple type -/
  | tuple (elements : List JsonType)
  /-- Array type -/
  | array (elementType : JsonType)
  /-- Union type -/
  | union (t1 t2 : JsonType)
  /-- Intersection type -/
  | inter (t1 t2 : JsonType)
  deriving Repr, Inhabited

/-- Manual BEq function for JsonType (not opaque like derived instances) -/
def JsonType.beq : JsonType → JsonType → Bool
  | .null, .null => true
  | .bool, .bool => true
  | .number, .number => true
  | .string, .string => true
  | .any, .any => true
  | .never, .never => true
  | .strLit s1, .strLit s2 => s1 == s2
  | .numLit n1, .numLit n2 => n1 == n2
  | .boolLit b1, .boolLit b2 => b1 == b2
  | .object req1 opt1, .object req2 opt2 =>
    (List.beq' req1 req2 (fun a _h1 b _h2 => a.fst == b.fst && a.snd.beq b.snd)) &&
    (List.beq' opt1 opt2 (fun a _h1 b _h2 => a.fst == b.fst && a.snd.beq b.snd))
  | .tuple elems1, .tuple elems2 => List.beq' elems1 elems2 fun a _h1 b _h2 => a.beq b
  | .array elem1, .array elem2 => beq elem1 elem2
  | .union t1a t1b, .union t2a t2b => beq t1a t2a && beq t1b t2b
  | .inter t1a t1b, .inter t2a t2b => beq t1a t2a && beq t1b t2b
  | _, _ => false
termination_by t1 => t1
decreasing_by
  · have := List.sizeOf_lt_of_mem _h1
    have : sizeOf a.snd < sizeOf a := by rcases a; simp +arith
    simp only [object.sizeOf_spec]
    omega
  · have := List.sizeOf_lt_of_mem _h1
    have : sizeOf a.snd < sizeOf a := by rcases a; simp +arith
    simp only [object.sizeOf_spec]
    omega
  · have := List.sizeOf_lt_of_mem _h1
    simp
    omega
  · decreasing_trivial
  · decreasing_trivial
  · decreasing_trivial
  · decreasing_trivial
  · decreasing_trivial


instance : BEq JsonType where
  beq := JsonType.beq

/-- Custom induction principle for JsonType based on well-founded recursion on sizeOf -/
def JsonType.inductionOn {motive : JsonType → Prop}
    (t : JsonType)
    (null : motive .null)
    (bool : motive .bool)
    (number : motive .number)
    (string : motive .string)
    (any : motive .any)
    (never : motive .never)
    (strLit : ∀ s, motive (.strLit s))
    (numLit : ∀ n, motive (.numLit n))
    (boolLit : ∀ b, motive (.boolLit b))
    (object : ∀ (req opt : List (String × JsonType)),
              (∀ name type, (name, type) ∈ req → motive type) →
              (∀ name type, (name, type) ∈ opt → motive type) →
              motive (.object req opt))
    (tuple : ∀ (elems : List JsonType),
             (∀ t, t ∈ elems → motive t) →
             motive (.tuple elems))
    (array : ∀ elem, motive elem → motive (.array elem))
    (union : ∀ t1 t2, motive t1 → motive t2 → motive (.union t1 t2))
    (inter : ∀ t1 t2, motive t1 → motive t2 → motive (.inter t1 t2)) :
    motive t :=
  match t with
  | .null => null
  | .bool => bool
  | .number => number
  | .string => string
  | .any => any
  | .never => never
  | .strLit s => strLit s
  | .numLit n => numLit n
  | .boolLit b => boolLit b
  | .object req opt =>
      object req opt
        (fun name type _tMem => JsonType.inductionOn type null bool number string any never strLit numLit boolLit object tuple array union inter)
        (fun name type _tMem => JsonType.inductionOn type null bool number string any never strLit numLit boolLit object tuple array union inter)
  | .tuple elems =>
      tuple elems (fun t _tMem => JsonType.inductionOn t null bool number string any never strLit numLit boolLit object tuple array union inter)
  | .array elem =>
      array elem (JsonType.inductionOn elem null bool number string any never strLit numLit boolLit object tuple array union inter)
  | .union t1 t2 =>
      union t1 t2
        (JsonType.inductionOn t1 null bool number string any never strLit numLit boolLit object tuple array union inter)
        (JsonType.inductionOn t2 null bool number string any never strLit numLit boolLit object tuple array union inter)
  | .inter t1 t2 =>
      inter t1 t2
        (JsonType.inductionOn t1 null bool number string any never strLit numLit boolLit object tuple array union inter)
        (JsonType.inductionOn t2 null bool number string any never strLit numLit boolLit object tuple array union inter)
termination_by t
decreasing_by
  · -- object required fields
    simp [JsonType.object.sizeOf_spec]
    have := List.sizeOf_lt_of_mem _tMem
    have : sizeOf type < sizeOf (name, type) := by simp +arith
    omega
  · -- object optional fields
    simp [JsonType.object.sizeOf_spec]
    have := List.sizeOf_lt_of_mem _tMem
    have : sizeOf type < sizeOf (name, type) := by simp +arith
    omega
  · -- tuple elements
    simp +arith only [JsonType.tuple.sizeOf_spec]
    have := List.sizeOf_lt_of_mem _tMem
    omega
  · decreasing_trivial
  · decreasing_trivial
  · decreasing_trivial
  · decreasing_trivial
  · decreasing_trivial

/-- Reflexivity of JsonType.beq -/
theorem JsonType.beq_refl (t : JsonType) : t.beq t = true := by
  induction t using JsonType.inductionOn with
  | null | bool | number | string | any | never => simp [beq]
  | strLit s => simp [beq]
  | numLit n => simp [beq]
  | boolLit b => simp [beq]
  | object req opt ih_req ih_opt =>
    unfold beq
    rw [Bool.and_eq_true, List.beq'_refl, List.beq'_refl]
    · simp
    · simp only [BEq.rfl, Bool.true_and, Prod.forall]
      intro k v mem
      apply ih_opt _ _ mem
    simp only [BEq.rfl, Bool.true_and, Prod.forall]
    intro k v mem
    apply ih_req _ _ mem
  | tuple elems ih =>
    unfold beq
    apply List.beq'_refl
    exact ih
  | array elem ih =>
    simp [beq, ih]
  | union t1 t2 ih1 ih2 =>
    simp [beq, ih1, ih2]
  | inter t1 t2 ih1 ih2 =>
    simp [beq, ih1, ih2]

/-- If beq returns true, the types are equal -/
theorem JsonType.eq_of_beq {t1 t2 : JsonType} : t1.beq t2 = true → t1 = t2 := by
  induction t1 using JsonType.inductionOn generalizing t2 with
  | null | bool | number | string | any | never => unfold beq; cases t2 <;> simp
  | strLit _ | numLit _ | boolLit _ => unfold beq; cases t2 <;> simp
  | object req1 opt1 ih1 ih2 =>
    unfold beq; cases t2 <;> (try simp)
    next req2 opt2 =>
      intro h1 h2
      constructor
      · apply List.eq_of_beq' req1 req2 (fun a _h1 b _h2 => a.fst == b.fst && a.snd.beq b.snd)
        · intro ⟨k1, v1⟩ kv1Mem ⟨k2, v2⟩ kv2Mem h
          grind -- magic!
        exact h1
      apply List.eq_of_beq' opt1 opt2 (fun a _h1 b _h2 => a.fst == b.fst && a.snd.beq b.snd)
      · intro ⟨k1, v1⟩ kv1Mem ⟨k2, v2⟩ kv2Mem h
        grind -- magic!
      exact h2
  | tuple ts ih =>
    unfold beq; cases t2 <;> (try simp)
    next ts' =>
      intro h
      apply List.eq_of_beq'
      · intro a ha b hb h'
        apply ih a ha h'
      exact h
  | array t1 ih =>
    unfold beq; cases t2 <;> (try simp)
    exact (fun h => ih h)
  | union t t' ih1 ih2 =>
    unfold beq; cases t2 <;> (try simp)
    next s1 s2 =>
      intro h1 h2
      replace h1 := ih1 h1
      replace h2 := ih2 h2
      exact ⟨h1, h2⟩
  | inter t t' ih1 ih2 =>
    unfold beq; cases t2 <;> (try simp)
    next s1 s2 =>
      intro h1 h2
      replace h1 := ih1 h1
      replace h2 := ih2 h2
      exact ⟨h1, h2⟩

instance : LawfulBEq JsonType where
  rfl := JsonType.beq_refl _
  eq_of_beq := JsonType.eq_of_beq

instance : AndOp JsonType where
  and := JsonType.inter

instance : OrOp JsonType where
  or := JsonType.union

set_option linter.unusedVariables false in
/-- Check if a JSON value conforms to a JsonType schema -/
def JsonType.check (t : JsonType) (v : Json) : Bool :=
  match t with
  | .null => v.isNull
  | .bool => (v matches .bool _)
  | .number => (v matches .num _)
  | .string => (v matches .str _)
  | .any => true
  | .never => false
  | .strLit s => v.beq (.str s)
  | .numLit n => match v with
    | .num x => x == Lean.JsonNumber.fromInt n
    | _ => false
  | .boolLit b => v.beq (.bool b)
  | .array elemType => match v with
    | .arr xs => xs.all elemType.check
    | _ => false
  | .tuple elemTypes => match v with
    | .arr xs =>
      xs.size == elemTypes.length &&
      (xs.toList.zip elemTypes.attach).all fun (x, ⟨t, h⟩) => t.check x
    | _ => false
  | .union t1 t2 => t1.check v || t2.check v
  | .inter t1 t2 => t1.check v && t2.check v
  | .object required optional => match v with
    | .obj fields =>
      -- All required fields must be present and match their types
      (required.attach.all fun ⟨(name, fieldType), h⟩ =>
        match fields.get? name with
        | some fieldVal => fieldType.check fieldVal
        | none => false)
      &&
      -- All optional fields that are present must match their types
      (optional.attach.all fun ⟨(name, fieldType), h⟩ =>
        match fields.get? name with
        | some fieldVal => fieldType.check fieldVal
        | none => true)
    | _ => false
termination_by t
decreasing_by
  · simp only [array.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one]
  · simp +arith only [tuple.sizeOf_spec, ge_iff_le]
    suffices sizeOf t < sizeOf elemTypes by
      grind
    exact List.sizeOf_lt_of_mem h
  · simp +arith
  · simp +arith
  · simp +arith
  · simp +arith
  · simp +arith only [object.sizeOf_spec, ge_iff_le]
    have := List.sizeOf_lt_of_mem h
    have : sizeOf fieldType < sizeOf (name, fieldType) := by
      simp +arith
    grind
  · simp +arith only [object.sizeOf_spec, ge_iff_le]
    have := List.sizeOf_lt_of_mem h
    have : sizeOf fieldType < sizeOf (name, fieldType) := by
      simp +arith
    grind

/-- A JSON value that conforms to a specific JsonType schema -/
abbrev TypedJson (t : JsonType) := Subtype (t.check · = true)

namespace TypedJson

-- Basic constructors
-- We could use native_decide for this. Ordinary decide does _not_ work becuase we use
-- well-foundedness to prove things :(
def null : TypedJson .null := ⟨Json.null, by simp [JsonType.check, Json.isNull]⟩

-- Coercions from Lean types
instance : Coe String (TypedJson .string) where
  coe s := ⟨.str s, by simp [JsonType.check]⟩

instance : Coe Int (TypedJson .number) where
  coe n := ⟨.num (Lean.JsonNumber.fromInt n), by simp [JsonType.check]⟩

instance : Coe Nat (TypedJson .number) where
  coe n := ⟨.num (Lean.JsonNumber.fromInt n), by simp [JsonType.check]⟩

instance : OfNat (TypedJson .number) n where
  ofNat := ⟨.num (Lean.JsonNumber.fromInt n), by simp [JsonType.check]⟩

instance : Coe Bool (TypedJson .bool) where
  coe b := ⟨.bool b, by simp [JsonType.check]⟩

-- Literal type constructors
def strLit (s : String) : TypedJson (.strLit s) := ⟨.str s, by
    simp [JsonType.check, Json.beq_refl]
  ⟩
def numLit (n : Int) : TypedJson (.numLit n) := ⟨.num (Lean.JsonNumber.fromInt n), by simp [JsonType.check]⟩
def boolLit (b : Bool) : TypedJson (.boolLit b) := ⟨.bool b, by simp [JsonType.check, Json.beq_refl]⟩

-- Any type accepts anything
instance : Coe Json (TypedJson .any) where
  coe v := ⟨v, by simp [JsonType.check]⟩

end TypedJson
