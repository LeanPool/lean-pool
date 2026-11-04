/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.TautoSet

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

lemma eq_finZeroElim {α : Sort u} (x : Fin 0 → α) : x = finZeroElim :=
  funext (by rintro ⟨_, _⟩; contradiction)

@[grind .]
lemma Nat.sub_one_lt' [NeZero n] : n - 1 < n :=
  _root_.Nat.sub_one_lt <| NeZero.ne n

namespace Fin

open _root_.Fin

variable {n : ℕ} {i : Fin n}

lemma isEmpty_embedding_lt (hn : n > m) : IsEmpty (Fin n ↪ Fin m) := by
  apply Function.Embedding.isEmpty_of_card_lt; simpa;

@[grind .]
lemma lt_last : n < Fin.last (n + 1) := by
  induction n with
  | zero => simp;
  | succ n ih => simp;

@[grind <=]
lemma lt_sub_one_of_pos {a : Fin n} (hn : 0 < n) : a ≤ ⟨n - 1, by omega⟩ := by
  apply Nat.le_sub_one_of_lt; omega;

section last'

variable [NeZero n]

/-- The last element of `Fin n` when `n` is `NeZero`. -/
def last' : Fin n :=
  ⟨n - 1, Nat.sub_one_lt'⟩

@[simp, grind .]
lemma lt_last' : i ≤ Fin.last' := by apply Nat.le_sub_one_of_lt; apply Fin.is_lt;

end last'

section

lemma pos_of_coe_ne_zero {i : Fin (n + 1)} (h : (i : ℕ) ≠ 0) : 0 < i :=
  Nat.pos_of_ne_zero h

lemma one_pos'' : (0 : Fin (n + 2)) < 1 :=
  pos_of_coe_ne_zero (Nat.succ_ne_zero 0)

@[simp]
lemma two_pos : (0 : Fin (n + 3)) < 2 :=
  pos_of_coe_ne_zero (Nat.succ_ne_zero 1)

@[simp]
lemma three_pos : (0 : Fin (n + 4)) < 3 :=
  pos_of_coe_ne_zero (Nat.succ_ne_zero 2)

@[simp]
lemma four_pos : (0 : Fin (n + 5)) < 4 :=
  pos_of_coe_ne_zero (Nat.succ_ne_zero 3)

@[simp]
lemma five_pos : (0 : Fin (n + 6)) < 5 :=
  pos_of_coe_ne_zero (Nat.succ_ne_zero 4)

end

lemma forall_fin_iff_zero_and_forall_succ {P : Fin (k + 1) → Prop} :
    (∀ i, P i) ↔ P 0 ∧ ∀ i : Fin k, P i.succ :=
  ⟨fun h ↦ ⟨h 0, fun i ↦ h i.succ⟩, by
    rintro ⟨hz, hs⟩ i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hz
    · exact hs i⟩

lemma exists_fin_iff_zero_or_exists_succ {P : Fin (k + 1) → Prop} :
    (∃ i, P i) ↔ P 0 ∨ ∃ i : Fin k, P i.succ :=
  ⟨by
    rintro ⟨i, hi⟩
    cases i using Fin.cases
    · left; exact hi
    · right; exact ⟨_, hi⟩, by
    rintro (hz | ⟨i, h⟩)
    · exact ⟨0, hz⟩
    · exact ⟨_, h⟩⟩

lemma funext_two {α : Type*} {f g : Fin (k + 2) → α} (h0 : f 0 = g 0)
    (h1 : f (Fin.succ 0) = g (Fin.succ 0)) (hs : ∀ i : Fin k, f i.succ.succ = g i.succ.succ) :
    f = g := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact h0
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact h1
    · exact hs i

/-- The add Cast construction in `Fin`. -/
@[inline]
def addCast (m) : Fin n → Fin (m + n) :=
  castLE <| Nat.le_add_left n m

@[simp]
lemma addCast_val (i : Fin n) : (addCast m i : ℕ) = i :=
  rfl

namespace Fin1

variable {n : Fin 1}

lemma eq_one : n = 0 := by cases n; omega;

@[simp]
lemma not_lt_zero : ¬0 < n := by simp [eq_one];

end Fin1

end Fin

end

end PointwiseComposition
