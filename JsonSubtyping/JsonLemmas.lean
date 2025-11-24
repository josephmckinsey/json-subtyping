/-
  Lemmas and infrastructure for working with Lean.Json

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
  | .arr a, .arr b => a.size == b.size && (a.attach.zip b.attach).all fun (⟨x, h1⟩, ⟨y, h2⟩) => Lean.Json.beq x y
  | .obj a, .obj b =>
    let aList := a.inner.inner.toList
    let bList := b.inner.inner.toList
    aList.length == bList.length &&
      (aList.attach.zip bList.attach).all fun (⟨⟨fa, va⟩, h1⟩, ⟨⟨fb, vb⟩, h2⟩) =>
      fa == fb && Lean.Json.beq va vb
  | _, _ => false
termination_by x => x
decreasing_by
  · decreasing_tactic
  · have : aList = a.inner.inner.toList := rfl
    rw [this, Std.DTreeMap.Internal.Impl.toList_eq_toListModel] at h1
    have := TreeMap.Raw.sizeOf_lt_of_mem h1
    simp +arith
    omega

set_option linter.unusedVariables false in
/-- Custom recursor principle for Json based on well-founded recursion on sizeOf.

    This handles arrays and objects by giving us the induction hypothesis for their elements. -/
def Json.recOn {motive : Json → Sort u}
    (x : Json)
    (null : motive .null)
    (bool : ∀ b, motive (.bool b))
    (num : ∀ n, motive (.num n))
    (str : ∀ s, motive (.str s))
    (arr : ∀ (a : Array Json), (∀ j, j ∈ a → motive j) → motive (.arr a))
    (obj : ∀ (o : Std.TreeMap.Raw String Json compare),
           (∀ field value, ⟨field, value⟩ ∈ o.inner.inner.toList → motive value) →
           motive (.obj o)) :
    motive x :=
  match x with
  | .null => null
  | .bool b => bool b
  | .num n => num n
  | .str s => str s
  | .arr a => arr a (fun j jMem => Json.recOn j null bool num str arr obj)
  | .obj o => obj o (fun k v vMem => Json.recOn v null bool num str arr obj)
termination_by x
decreasing_by
  · suffices sizeOf j < sizeOf a by simp +arith; omega
    exact Array.sizeOf_lt_of_mem jMem
  suffices sizeOf v < sizeOf o by simp +arith; omega
  apply TreeMap.Raw.sizeOf_lt_of_mem
  rw [<-Std.DTreeMap.Internal.Impl.toList_eq_toListModel]
  exact vMem

set_option linter.unusedVariables false in
/-- Custom induction principle for Json based on well-founded recursion on sizeOf.

    This handles arrays and objects by giving us the induction hypothesis for their elements. -/
theorem Json.inductionOn {motive : Json → Prop}
    (x : Json)
    (null : motive .null)
    (bool : ∀ b, motive (.bool b))
    (num : ∀ n, motive (.num n))
    (str : ∀ s, motive (.str s))
    (arr : ∀ (a : Array Json), (∀ j, j ∈ a → motive j) → motive (.arr a))
    (obj : ∀ (o : Std.TreeMap.Raw String Json compare),
           (∀ field value, ⟨field, value⟩ ∈ o.inner.inner.toList → motive value) →
           motive (.obj o)) :
    motive x := Json.recOn x null bool num str arr obj


/-- TODO: Prove this using a custom induction principle for Json.

    The challenge is that `induction` doesn't work on nested inductives.
    Options:
    1. Use `Json.rec` directly (awkward)
    2. Define a wrapper induction principle using well-founded recursion
    3. Use strong induction on `sizeOf`

    Once we have this, we can prove things like `LawfulBEq` for `Json.beq`. -/
theorem Json.beq_refl (x : Json) : Json.beq x x = true := by
  induction x using Json.inductionOn with
  | null => simp [Json.beq]
  | bool b => simp [Json.beq]
  | num n => simp [Json.beq]
  | str s => simp [Json.beq]
  | arr x ih =>
    unfold Json.beq
    simp only [BEq.rfl, Bool.true_and]
    apply Array.all_eq_true'.mpr
    intro ⟨⟨a1, h1⟩, ⟨a2, h2⟩⟩ aMem
    have a1_eq_a2 : a1 = a2 := by
      simp [Array.zip_eq_zipWith] at aMem
      exact aMem
    simpa [<-a1_eq_a2] using ih a1 h1
  | obj x ih =>
    unfold Json.beq
    extract_lets aList
    simp only [BEq.rfl, Bool.true_and, List.all_eq_true, Bool.and_eq_true]
    intro ⟨f1, f2⟩ mem
    have : f1 = f2 := by
      simp [List.zip_eq_zipWith] at mem
      exact mem
    rw [<-this]
    let ⟨⟨k, v⟩ , h⟩ := f1
    simpa using ih k v h

instance alternateBEqJson : BEq Json where
  beq := Lean.Json.beq

/-
A LawfulBEq instance cannot be instantiated unfortunately, since
Std.TreeMap.Raw only gives equivalence. We'd have to make it equivalent.

instance : LawfulBEq Json where
  rfl := Json.beq_refl _
  eq_of_beq := sorry
-/
