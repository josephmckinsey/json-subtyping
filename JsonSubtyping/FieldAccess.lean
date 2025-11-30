/-
  Field accessor functions for TypedJson objects.

  Provides type-safe field access with compile-time membership checking:
  - `hasKey` - Decidable membership predicate for keys
  - `getKey` - Extract field type with proof of membership
  - `getKey?` - Optional field type extraction
  - `getProperty` - Access fields from TypedJson values

  Supports objects, unions (key must exist in all branches), and
  intersections (key exists in any branch).
-/

import JsonSubtyping.Basic
import JsonSubtyping.ObjectSubtype

open Lean (Json)

namespace JsonType

/-! ## Membership Predicate -/

/-! ## Type Extraction -/

/-- Extract the JsonType for a key, returning None if key doesn't exist.
    This is the primitive operation that does a single traversal. -/
def getKey? (t : JsonType) (key : String) : Option JsonType :=
  match t with
  | .object req _ => req.lookup key
  | .union t1 t2 =>
    -- Key must exist in BOTH branches (intersection of field sets)
    -- Field type is UNION (could be from either branch at runtime)
    match t1.getKey? key, t2.getKey? key with
    | some ty1, some ty2 => some (.union ty1 ty2)
    | _, _ => none
  | .inter t1 t2 =>
    -- Key exists in ANY branch (union of field sets)
    -- Field type is INTERSECTION if in both, otherwise just the one
    match t1.getKey? key, t2.getKey? key with
    | some ty1, some ty2 => some (.inter ty1 ty2)  -- In both: intersect types
    | some ty, none | none, some ty => some ty   -- In one: use that type
    | none, none => none
  | _ => none

theorem List.mem_of_lookup_eq_some [BEq α] [BEq β] [LawfulBEq α] {a : α} {b : β} {xs : List (α × β)}
    (h : List.lookup a xs = some b) : (a, b) ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    rw [List.lookup_cons] at h
    rcases h' : a == x.fst with rfl | rfl
    · simp [h'] at h
      exact List.mem_cons_of_mem x (ih h)
    simp [h'] at h
    simp at h'
    grind


theorem getKey?_correctness {t : JsonType} {key : String}
    {v : JsonType} {x : Json} (h : t.check x) (h' : t.getKey? key = some v) :
    ∃y, x.getObjVal? key = .ok y ∧ v.check y := by
  match t with
  | .object req _ =>
    simp [getKey?] at h'
    rcases x <;> simp [check] at h
    next opt fields =>
      have : (key, v) ∈ req := List.mem_of_lookup_eq_some h'
      rw [Json.getObjVal?]
      obtain ⟨y, h1, h2⟩ := requiredFieldsCheck_implies_get? req key v fields this h.1
      exact h1 ▸ ⟨y, rfl, h2⟩
  | .union t1 t2 =>
    -- Key must exist in BOTH branches (intersection of field sets)
    -- Field type is UNION (could be from either branch at runtime)
    simp [getKey?] at h'
    match h1 : t1.getKey? key, h2 : t2.getKey? key with
    | some ty1, some ty2 =>
      rw [h1, h2] at h'
      simp at h'
      obtain ⟨y, h'', hOr⟩ : ∃ y, x.getObjVal? key = Except.ok y ∧
          (ty1.check y ∨ ty2.check y) := by
        simp [check] at h
        rcases h with h | h
        · obtain ⟨y, h1, h1'⟩ := getKey?_correctness h h1
          exact ⟨y, h1, .inl h1'⟩
        obtain ⟨y, h2, h2'⟩ := getKey?_correctness h h2
        exact ⟨y, h2, .inr h2'⟩
      refine ⟨y, h'', ?_⟩
      simpa [<-h', check] using hOr
    | .none, _ => rw [h1] at h'; contradiction
    | _, .none => rw [h2] at h'; simp at h'
  | .inter t1 t2 =>
    simp [getKey?] at h'
    -- Key exists in ANY branch (union of field sets)
    -- Field type is INTERSECTION if in both, otherwise just the one
    simp [check] at h
    match h1 : t1.getKey? key, h2 : t2.getKey? key with
    | some ty1, some ty2 =>
      rw [h1, h2] at h'
      simp at h'
      obtain ⟨y, h'', hAnd⟩ : ∃ y, x.getObjVal? key = Except.ok y ∧
          (ty1.check y ∧ ty2.check y) := by
        obtain ⟨y1, h1, h1'⟩ := getKey?_correctness h.1 h1
        obtain ⟨y2, h2, h2'⟩ := getKey?_correctness h.2 h2
        refine ⟨y1, h1, ?_⟩
        rw [h1, Except.ok.injEq] at h2
        exact ⟨h1', h2 ▸ h2'⟩
      refine ⟨y, h'', ?_⟩
      simpa [<-h', check] using hAnd
    | some ty, none =>
        rw [h1, h2] at h'
        simp at h'
        obtain ⟨y, h1, h1'⟩ := getKey?_correctness h.1 h1
        refine ⟨y, h1, h' ▸ h1'⟩
    | none, some ty =>
        rw [h1, h2] at h'
        simp at h'
        obtain ⟨y, h2, h2'⟩ := getKey?_correctness h.2 h2
        refine ⟨y, h2, h' ▸ h2'⟩
    | none, none => rw [h1, h2] at h'; simp at h'

/-- Membership instance to enable `key ∈ t` notation.
    Defined as: key exists if getKey? returns Some. -/
instance : Membership String JsonType where
  mem := fun t key => (t.getKey? key).isSome

-- Simplification lemma to unfold membership
@[simp] theorem mem_iff (t : JsonType) (key : String) : (key ∈ t) ↔ (t.getKey? key).isSome := Iff.rfl

/-! ## Decidability Instance -/

/-- Decidability for membership comes from Option.isSome decidability -/
instance (t : JsonType) (key : String) : Decidable (key ∈ t) :=
  inferInstanceAs (Decidable (t.getKey? key).isSome)

/-- Extract the JsonType for a key, given proof of membership.
    Unpacks the Option using the membership proof. -/
@[reducible]
def getKey (t : JsonType) (key : String) (mem : key ∈ t) : JsonType :=
  (t.getKey? key).get mem

end JsonType

/-! ## TypedJson Field Access -/

namespace TypedJson

/-- Access a field from a TypedJson object with proof of membership.
    For now, this only supports object types.
    Union/intersection support will be added in a future update. -/
def get {t : JsonType} (tj : TypedJson t) (key : String)
    (mem : key ∈ t := by native_decide) : TypedJson (t.getKey key mem) :=
  match tj with
  | ⟨x, h⟩ => match h' : x.getObjVal? key with
    | .ok y => ⟨y, by
      obtain ⟨v, getKey_eq⟩ : ∃ v, t.getKey? key = some v :=
        Option.isSome_iff_exists.mp mem
      simp only [JsonType.getKey, getKey_eq, Option.get_some] -- rw didn't work
      obtain ⟨y', h''⟩ := t.getKey?_correctness h getKey_eq
      rw [h''.1] at h'
      simp only [Except.ok.injEq] at h'
      exact h' ▸ h''.2
    ⟩
    | .error _ => False.elim (by
      obtain ⟨v, getKey_eq⟩ : ∃ v, t.getKey? key = some v :=
        Option.isSome_iff_exists.mp mem
      obtain ⟨y, h''⟩ := t.getKey?_correctness h getKey_eq
      rw [h''.1] at h'
      contradiction
    )

end TypedJson
