/-
  Lemmas and infrastructure for working with Lean.Json

  ## TODO for next session:

  The main challenge is that `Json` is a nested inductive type (contains `Array Json`
  and `TreeMap.Raw String Json`), which means:

  1. The standard `induction` tactic doesn't work
  2. We need custom induction principles using well-founded recursion on `sizeOf`
  3. Or we need to use `Json.rec` manually with the right motive

  Key tasks:
  - [ ] Define a usable induction principle for Json (maybe wrapping Json.rec)
  - [ ] Prove `Json.beq_refl : ∀ x, Json.beq x x = true` using that principle
  - [ ] Consider proving `LawfulBEq` for our custom `Json.beq`

  References:
  - `Json.rec` exists but is awkward to use directly
  - See Lean 4 docs on nested inductives: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/
-/

import Lean.Data.Json

open Lean (Json)

-- sizeOf lemmas for TreeMap internals
open Std.DTreeMap.Internal in
theorem Impl.sizeOf_lt_of_mem {α : Type u} {β : α → Type v} [SizeOf α] [(a : α) → SizeOf (β a)]
    {t : Impl α β} {k : α} {v : β k} (h : ⟨k, v⟩ ∈ t.toListModel) :
    sizeOf v < sizeOf t := by
  induction t with
  | leaf => simp [Impl.toListModel] at h
  | inner sz k' v' l r ihl ihr =>
    simp only [Impl.toListModel_inner, List.mem_append, List.mem_cons] at h
    rw [Impl.inner.sizeOf_spec]
    rcases h with hl | heq | hr
    · have := ihl hl; omega
    · cases heq; omega
    · have := ihr hr; omega

theorem TreeMap.Raw.sizeOf_lt_of_mem {α β : Type} {cmp : α → α → Ordering}
    [SizeOf α] [SizeOf β] {t : Std.TreeMap.Raw α β cmp} {k : α} {v : β}
    (h : ⟨k, v⟩ ∈ t.inner.inner.toListModel) :
    sizeOf v < sizeOf t := by
  have h1 : sizeOf t = 1 + sizeOf t.inner := Std.TreeMap.Raw.mk.sizeOf_spec t.inner
  have h2 : sizeOf t.inner = 1 + sizeOf t.inner.inner := Std.DTreeMap.Raw.mk.sizeOf_spec t.inner.inner
  have h3 := Impl.sizeOf_lt_of_mem h
  omega

theorem TreeMap.Raw.inne_toListModel_eq_toList {α : Type} {β : α → Type} {cmp : α → α → Ordering}
    {t : Std.DTreeMap.Raw α β cmp} :
    t.inner.toListModel = t.inner.toList := by
    exact Eq.symm Std.DTreeMap.Internal.Impl.toList_eq_toListModel

set_option linter.unusedVariables false in
/-- Custom BEq for Json that we can prove properties about.

    The stdlib's BEq for Json uses a private partial function, so we can't
    unfold it or prove anything about it. This version uses well-founded
    recursion so we can prove `beq_refl` etc.

    We should probably actually use a custom recursor somehow. -/
def Lean.Json.beq : Json → Json → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | .arr a, .arr b => a.size == b.size && (a.attach.zip b).all fun (⟨x, _⟩, y) => Lean.Json.beq x y
  | .obj a, .obj b =>
    let szA := a.size
    let szB := b.size
    szA == szB && a.inner.inner.toList.attach.all fun ⟨⟨field, fa⟩, h⟩ =>
      match b.get? field with
      | none => false
      | some fb => Lean.Json.beq fa fb
  | _, _ => false
termination_by x => x
decreasing_by
  · decreasing_tactic
  · rw [Std.DTreeMap.Internal.Impl.toList_eq_toListModel] at h
    have := TreeMap.Raw.sizeOf_lt_of_mem h
    simp +arith
    omega

/-- TODO: Prove this using a custom induction principle for Json.

    The challenge is that `induction` doesn't work on nested inductives.
    Options:
    1. Use `Json.rec` directly (awkward)
    2. Define a wrapper induction principle using well-founded recursion
    3. Use strong induction on `sizeOf`

    Once we have this, we can prove things like `LawfulBEq` for `Json.beq`. -/
theorem Json.beq_refl (x : Json) : Json.beq x x = true := by
  sorry

-- TODO: Once beq_refl is proven, we can add:
-- instance : LawfulBEq Json where
--   eq_of_beq := ...
--   rfl := Json.beq_refl
