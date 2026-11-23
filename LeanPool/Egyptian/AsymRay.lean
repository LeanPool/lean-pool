/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Assembly

/-! Prefixes and concatenation of the infinite greedy rays in §4. -/

@[expose] public section

namespace Egyptian

/-- Prepend a finite denominator list to an infinite sequence. -/
def prepend : List ℕ → (ℕ → ℕ) → ℕ → ℕ
  | [], d => d
  | x :: xs, d => fun | 0 => x | n+1 => prepend xs d n

/-- The sequence obtained by following the given prefix with the greedy unit tail. -/
def unitRay (xs : List ℕ) (T : ℕ) := prepend xs (fun j => unitIter T j + 1)

theorem prepend_tail (xs : List ℕ) (d : ℕ → ℕ) (j : ℕ) :
    prepend xs d (xs.length+j) = d j := by
  induction xs with
  | nil => simp [prepend]
  | cons x xs ih =>
    simpa only [List.length_cons, Nat.succ_add, prepend] using ih

theorem prepend_append (xs ys : List ℕ) (d : ℕ → ℕ) :
    prepend (xs++ys) d = prepend xs (prepend ys d) := by
  induction xs with
  | nil => rfl
  | cons x xs h => funext n; cases n <;> simp [prepend, h]

private theorem prefix_succ (d : ℕ → ℕ) (n : ℕ) :
    prefixTuple d (n+1) = d 0 :: prefixTuple (fun i => d (i+1)) n := by
  simp only [prefixTuple, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem prefix_prepend (xs : List ℕ) (d : ℕ → ℕ) (j : ℕ) :
    prefixTuple (prepend xs d) (xs.length+j) = xs ++ prefixTuple d j := by
  induction xs with
  | nil => simp [prepend]
  | cons x xs ih =>
    rw [List.length_cons, Nat.succ_add, prefix_succ]
    exact congrArg (List.cons x) ih

theorem prepend_prefix_cancel (d : ℕ → ℕ) (n : ℕ) :
    prepend (prefixTuple d n) (fun j => d (n+j)) = d := by
  induction n generalizing d with
  | zero => simp [prefixTuple, prepend]
  | succ n ih =>
    rw [prefix_succ]
    funext j
    cases j with
    | zero => rfl
    | succ j =>
      have h := congrFun (ih (fun i => d (i+1))) j
      simpa only [prepend, Nat.succ_add] using h

theorem unit_iter_step_start (T i : ℕ) :
    unitIter (T*(T+1)) i = unitIter T (i+1) := by
  induction i with
  | zero => rfl
  | succ i h => exact congrArg (fun n => n*(n+1)) h

theorem prefix_unitRay (T n : ℕ) : prefixTuple (unitRay [] T) n = unitDigits T n := by
  induction n generalizing T with
  | zero => rfl
  | succ n ih =>
    rw [prefix_succ, unitDigits, ← ih]
    unfold unitRay
    simp only [prepend, ← unit_iter_step_start]
    rfl

end Egyptian
