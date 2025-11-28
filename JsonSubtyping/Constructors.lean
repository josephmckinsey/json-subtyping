import JsonSubtyping.Basic
import JsonSubtyping.Subtype
import Std.Data.TreeMap.Raw.Lemmas

open Lean (Json JsonNumber)

namespace TypedJson

/-! ## Array Construction -/

/-- Construct an array from an Array of typed elements -/
def arr {t : JsonType} (elements : Array (TypedJson t)) : TypedJson (.array t) :=
  ⟨.arr (elements.map (·.val)), by
    simp only [JsonType.check, Array.all_eq_true']
    intro x xMem
    obtain ⟨i, h_lt, h_eq⟩ := Array.mem_iff_getElem.mp xMem
    have h_size : i < elements.size := by simp [Array.size_map] at h_lt; exact h_lt
    rw [Array.getElem_map] at h_eq
    rw [← h_eq]
    exact (elements[i]'h_size).property
  ⟩

/-- Construct an array from a List of typed elements -/
def arrFromList {t : JsonType} (elements : List (TypedJson t)) : TypedJson (.array t) :=
  arr elements.toArray

/-! ## Tuple Construction (using iterated products) -/

/-- Construct a 2-element tuple from a pair -/
def prod {t1 t2 : JsonType}
    (v1 : TypedJson t1) (v2 : TypedJson t2) :
    TypedJson (.tuple [t1, t2]) :=
  ⟨.arr #[v1.val, v2.val], by
    rcases v1 with ⟨v1, h1⟩
    rcases v2 with ⟨v2, h2⟩
    simpa [JsonType.check] using ⟨h1, h2⟩
  ⟩

/-- Construct a 3-element tuple from a nested pair -/
def tuple3 {t1 t2 t3 : JsonType}
    (v1 : TypedJson t1) (v2 : TypedJson t2) (v3 : TypedJson t3) :
    TypedJson (.tuple [t1, t2, t3]) :=
  ⟨.arr #[v1.val, v2.val, v3.val], by
    rcases v1 with ⟨v1, h1⟩
    rcases v2 with ⟨v2, h2⟩
    rcases v3 with ⟨v3, h3⟩
    simpa [JsonType.check] using ⟨h1, h2, h3⟩
  ⟩

/-! ## Object Construction

We use a heterogeneous list (HList) to represent object fields where:
- Field names and types are in the type parameter `req : List (String × JsonType)`
- Field values are `TypedJson` carrying proofs of type correctness
- Duplicate field detection happens at construction time via `native_decide` on the `req` parameter

This design resolves two competing forces:
1. Field names/types must be compile-time concrete for `native_decide`
2. We need structural guarantees (no duplicates, correct types) for soundness

Alternative designs considered:
- Binding `List.Pairwise` directly into the inductive type (too restrictive)
- Parallel lists with length/alignment proofs (awkward for users)
- Set-based representation (loses compile-time field information)
-/

/-- Heterogeneous list of object fields indexed by schema.
    Each field carries a TypedJson value with proof that it checks against its type. -/
inductive ObjectFields : List (String × JsonType) → Type where
  | nil : ObjectFields []
  | cons {ty : JsonType} {rest : List (String × JsonType)} (name : String) :
      TypedJson ty → ObjectFields rest → ObjectFields ((name, ty) :: rest)

namespace ObjectFields

/-- Convert ObjectFields to a list of (String, Json) pairs for Json.mkObj -/
def toList : {req : List (String × JsonType)} → ObjectFields req → List (String × Json)
  | _, .nil => []
  | _, .cons n v rest => (n, v.val) :: toList rest

/-! ### Soundness Lemmas

The following lemmas establish the correspondence between the `ObjectFields` HList
and the resulting `TreeMap` after calling `TreeMap.Raw.ofList`:

1. `mem_toList_exists_in_req`: Every field in `toList` has a corresponding type in `req`
2. `mem_req_exists_in_toList`: Every required field exists in `toList` with correct type
3. `toList_preserves_pairwise`: The pairwise distinctness property transfers to `toList`

These lemmas combine to prove the main `check` theorem.
-/

/-- If a field appears in the converted list, it must have a type in the schema. -/
theorem mem_toList_exists_in_req {req : List (String × JsonType)} {fields : ObjectFields req}
    {field : String} {json : Json} (mem : (field, json) ∈ fields.toList) :
    ∃ty, (field, ty) ∈ req := by
  induction fields with
  | nil => simp [ObjectFields.toList] at mem
  | @cons ty req' n v rest ih =>
    rw [ObjectFields.toList, List.mem_cons] at mem
    grind

/-- If a field is required in the schema, it exists in the converted list with correct type. -/
theorem mem_req_exists_in_toList {req : List (String × JsonType)} (fields : ObjectFields req)
    {field : String} {type : JsonType} (mem : (field, type) ∈ req) :
    ∃j, (field, j) ∈ fields.toList ∧ type.check j := by
  induction fields with
  | nil => simp at mem
  | @cons ty req' n v rest ih =>
    simp only [List.mem_cons, Prod.mk.injEq] at mem
    rcases mem with mem | mem
    · refine ⟨v.val, ?_, ?_⟩
      · simp [mem.1, ObjectFields.toList]
      exact mem.2 ▸ v.property
    obtain ⟨j, h, h'⟩ := ih mem
    refine ⟨j, List.mem_of_mem_tail h, h'⟩

/-- Pairwise distinctness of fields in the schema implies distinctness in the converted list. -/
theorem toList_preserves_pairwise {req : List (String × JsonType)} (fields : ObjectFields req)
    (noDups : req.Pairwise (fun a b => ¬compare a.1 b.1 = .eq)) :
    fields.toList.Pairwise (fun a b => ¬compare a.1 b.1 = .eq) := by
  induction fields with
  | nil => simp [toList]
  | @cons ty req' n v rest ih =>
    replace ih := ih (List.Pairwise.of_cons noDups)
    rw [ObjectFields.toList]
    refine List.Pairwise.cons ?_ ih
    intro ⟨field, json⟩ h
    rw [List.pairwise_cons] at noDups
    obtain ⟨ty2, h⟩ := mem_toList_exists_in_req h
    exact noDups.1 (field, ty2) h

/-- Main soundness theorem: ObjectFields with distinct field names produces a valid object.

    Proof strategy:
    1. Transfer pairwise distinctness from `req` to `toList` via `toList_preserves_pairwise`
    2. For each required field in `req`, use `mem_req_exists_in_toList` to find its value
    3. Use `TreeMap.getElem?_ofList_of_mem` to show the field lookup succeeds
    4. The TypedJson proof in ObjectFields.cons guarantees type correctness
-/
theorem check {req : List (String × JsonType)} (fields : ObjectFields req)
    (noDups : req.Pairwise (fun a b => ¬compare a.1 b.1 = .eq)) :
    requiredFieldsCheck req (fun p _h => p.2.check)
      (Std.TreeMap.Raw.ofList fields.toList) = true := by
  replace noDupsBetter : List.Pairwise (fun a b => ¬compare a.fst b.fst = Ordering.eq)
      fields.toList := toList_preserves_pairwise _ noDups
  rw [requiredFieldsCheck]
  simp only [List.all_eq_true, List.mem_attach, forall_const, Subtype.forall, Prod.forall]
  intro n2 t2 mem
  rw [JsonType.checkRequiredField_iff]
  obtain ⟨j, h, h'⟩ := mem_req_exists_in_toList fields mem
  refine ⟨j, ?_, h'⟩
  rw [Std.TreeMap.Raw.get?_eq_getElem?]
  apply Std.TreeMap.Raw.getElem?_ofList_of_mem Std.compare_self
  · exact noDupsBetter
  exact h

end ObjectFields

/-- Construct an object from ObjectFields -/
def mkObj {req : List (String × JsonType)} (fields : ObjectFields req)
    (noDups : req.Pairwise (fun a b => ¬compare a.1 b.1 = .eq) := by native_decide) :
    TypedJson (.object req []) :=
  ⟨Json.mkObj fields.toList, by
    unfold JsonType.check Json.mkObj
    simp only [Bool.and_eq_true]
    constructor
    · exact ObjectFields.check fields noDups
    · -- Optional fields are empty, so optionalFieldsCheck trivially holds
      simp [optionalFieldsCheck]
  ⟩

end TypedJson
