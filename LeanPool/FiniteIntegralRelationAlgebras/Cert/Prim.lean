/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Bitwise

/-!
# Kernel-friendly primitives

Small list and loop primitives written directly with recursors, which the kernel reduces several
times faster than definitions produced by the equation compiler, together with their
specifications.
-/

@[expose] public section

namespace RACert

universe u

/-- `l[i]` with default `d`, by direct recursion. -/
noncomputable def nth {α : Type u} (d : α) (l : List α) : ℕ → α :=
  List.rec (motive := fun _ => ℕ → α) (fun _ => d)
    (fun x _ ih i => Nat.rec (motive := fun _ => α) x (fun j _ => ih j) i) l

@[simp]
theorem nth_nil {α : Type u} (d : α) (i : ℕ) : nth d [] i = d := rfl

@[simp]
theorem nth_cons_zero {α : Type u} (d x : α) (l : List α) : nth d (x :: l) 0 = x := rfl

@[simp]
theorem nth_cons_succ {α : Type u} (d x : α) (l : List α) (i : ℕ) :
    nth d (x :: l) (i + 1) = nth d l i := rfl

theorem nth_eq_getD {α : Type u} (d : α) (l : List α) (i : ℕ) : nth d l i = l.getD i d := by
  induction l generalizing i with
  | nil => simp
  | cons x l ih => cases i <;> simp [ih]

/-- `∀ i < k, f i`, as a Boolean, checked from `k - 1` downwards with short-circuiting. -/
noncomputable def allRange (k : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => Bool.rec (motive := fun _ => Bool) false ih (f i)) k

@[simp]
theorem allRange_zero (f : ℕ → Bool) : allRange 0 f = true := rfl

theorem allRange_succ (k : ℕ) (f : ℕ → Bool) : allRange (k + 1) f = (f k && allRange k f) := by
  change Bool.rec (motive := fun _ => Bool) false (allRange k f) (f k) = _
  cases f k <;> rfl

theorem allRange_iff {k : ℕ} {f : ℕ → Bool} : allRange k f = true ↔ ∀ i < k, f i = true := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [allRange_succ, Bool.and_eq_true, ih]
    exact ⟨fun ⟨h1, h2⟩ i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      exacts [h2 i h, h1], fun h => ⟨h k (Nat.lt_succ_self k), fun i hi => h i (by omega)⟩⟩

/-- The bit mask with exactly the bits listed in `l` set. -/
def maskOf (l : List ℕ) : ℕ := l.foldl (fun m c => Nat.lor m (Nat.shiftLeft 1 c)) 0

theorem testBit_foldl_mask (l : List ℕ) (m x : ℕ) :
    (l.foldl (fun m c => Nat.lor m (Nat.shiftLeft 1 c)) m).testBit x =
      (m.testBit x || decide (x ∈ l)) := by
  induction l generalizing m with
  | nil => simp
  | cons c l ih =>
    rw [List.foldl_cons, ih]
    change ((m ||| 1 <<< c).testBit x || decide (x ∈ l)) = _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_assoc]
    congr 1
    rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff,
      decide_eq_true_iff, List.mem_cons]
    exact or_congr_left eq_comm

theorem testBit_maskOf (l : List ℕ) (x : ℕ) : (maskOf l).testBit x = decide (x ∈ l) := by
  rw [maskOf, testBit_foldl_mask]
  simp

end RACert
