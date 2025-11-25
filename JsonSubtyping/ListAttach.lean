/--
Checks whether two lists have the same length and their elements are pairwise `BEq`.
The comparison function receives membership proofs for the elements, which is useful
for termination checking in nested inductive types.
-/
def List.beq' : (as : List α) → (bs : List α) → (f : (a : α) → a ∈ as → (b : α) → b ∈ bs → Bool) → Bool
  | [],    [],    _f => true
  | a::as, b::bs, f  => f a List.mem_cons_self b List.mem_cons_self &&
                        List.beq' as bs (fun x hx y hy => f x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem b hy))
  | _,     _,     _f => false

theorem List.beq'_eq_beq [BEq α] (as bs : List α) :
  List.beq' as bs (fun a _ha b _hb => (a : α) == (b : α)) = (as == bs) := by
  induction as generalizing bs with
  | nil => cases bs <;> first | rfl | contradiction
  | cons a as ih =>
    cases bs with
    | nil => simp [List.beq']
    | cons b bs =>
      simp [List.beq', ih bs]

/-! To be able to use List equality within nested inductive types, we need to be able
to carry additional assumptions.

We want to prove that as.beq' f as = true as long as f a a = true for all a in as.

We want to prove that as.beq' f bs = true implies as = bs as long as f a b = true implies
a = b for all a in as and b in bs.
-/

/-- Reflexivity for List.beq' given element-wise reflexivity -/
theorem List.beq'_refl {α : Type _} (as : List α)
    (f : (a : α) → a ∈ as → (b : α) → b ∈ as → Bool)
    (h : ∀ a (ha : a ∈ as), f a ha a ha = true) :
    as.beq' as f = true := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp [List.beq', Bool.and_eq_true]
    constructor
    · exact h a List.mem_cons_self
    · apply ih
      · intro x hx
        exact h x (List.mem_cons_of_mem a hx)

/-- Soundness for List.beq' given element-wise soundness -/
theorem List.eq_of_beq' {α : Type _} (as bs : List α)
    (f : (a : α) → a ∈ as → (b : α) → b ∈ bs → Bool)
    (h : ∀ a (ha : a ∈ as) b (hb : b ∈ bs), f a ha b hb = true → a = b) :
    as.beq' bs f = true → as = bs := by
  intro h_beq
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => rfl
    | cons b bs => simp [List.beq'] at h_beq
  | cons a as ih =>
    cases bs with
    | nil => simp [List.beq'] at h_beq
    | cons b bs =>
      simp [List.beq', Bool.and_eq_true] at h_beq
      obtain ⟨h_head, h_tail⟩ := h_beq
      -- Prove a = b using the soundness assumption
      have a_eq_b : a = b := h a List.mem_cons_self b List.mem_cons_self h_head
      -- Prove as = bs using IH
      have as_eq_bs : as = bs := by
        apply ih
        · intro x hx y hy
          exact h x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem b hy)
        · exact h_tail
      -- Combine to prove a::as = b::bs
      rw [a_eq_b, as_eq_bs]
