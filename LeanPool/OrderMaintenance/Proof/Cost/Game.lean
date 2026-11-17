/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

public import LeanPool.OrderMaintenance.Proof.Cost.Reserve
public import LeanPool.OrderMaintenance.Proof.Cost.Zeroing


/-!
# Lemma R: chunk sizes through the zeroing game (`docs/PROOF.md` §4.4)

The game's variables are the chunks `1 … n`. The value of a quiet chunk is how far its size exceeds
`θ`; other chunks have value 0. A round runs from one pop of the priority queue to the next: the
pop zeroes a maximal value, and the round's insertions add at most `R`. `GameInv` is Theorem Z's
invariant at the start of the current round, together with this round's adds so far. It bounds
every quiet chunk's size by `θ + R·(H_{n−1} + 1)` (Lemma R).
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
/-- The value of chunk `c` in the game. -/
def gval (s : Core) (c : Nat) : Nat :=
  if LiveC s c ∧ cSt s c = .quiet then cSz s c - s.P.theta else 0

/-- The game's variables: chunk `i + 1` for `i < n`. -/
noncomputable def gvec (n : Nat) (s : Core) : Fin n → ℝ := fun i => (gval s (i.val + 1) : ℝ)

/-- The game's state in the current round: Theorem Z's invariant at the round's start (`y`, with
`i` zeroed by the pop), and the adds `a` of the `ip` insertions since. -/
structure GameInv (n : Nat) (R : Nat) (s : Core) (y : Fin n → ℝ) (i : Fin n) (a : Fin n → ℝ)
    (ip : Nat) : Prop where
  inv : Inv (R : ℝ) y
  max : ∀ j, y j ≤ y i
  apos : ∀ j, 0 ≤ a j
  asum : ∑ j, a j ≤ (ip : ℝ)
  le : ∀ j, gvec n s j ≤ (if j = i then 0 else y j) + a j
  ip : ip ≤ R

theorem GameInv.round {n R : Nat} {s : Core} {y : Fin n → ℝ} {i : Fin n} {a : Fin n → ℝ}
    {ip : Nat} (h : GameInv n R s y i a ip) : Round (R : ℝ) y (gvec n s) := by
  refine ⟨i, h.max, a, h.apos, le_trans h.asum (by exact_mod_cast h.ip), fun j => ⟨?_, h.le j⟩⟩
  unfold gvec; positivity

/-- The current values satisfy Theorem Z's invariant. -/
theorem GameInv.cur {n R : Nat} {s : Core} {y : Fin n → ℝ} {i : Fin n} {a : Fin n → ℝ}
    {ip : Nat} (h : GameInv n R s y i a ip) : Inv (R : ℝ) (gvec n s) :=
  inv_round h.inv h.round

/-- **Lemma R** (the bound): every game value is at most `R·(H_{n−1} + 1)`. -/
theorem GameInv.bound {n R : Nat} {s : Core} {y : Fin n → ℝ} {i : Fin n} {a : Fin n → ℝ}
    {ip : Nat} (h : GameInv n R s y i a ip) (j : Fin n) :
    gvec n s j ≤ (R : ℝ) * (Hn (n - 1) + 1) := by
  have := h.cur.2 {j} (by simp)
  simpa [Zeroing.bound, Zeroing.Hn] using this

/-- Values that did not grow keep the invariant. -/
theorem GameInv.mono {n R : Nat} {s s' : Core} {y : Fin n → ℝ} {i : Fin n} {a : Fin n → ℝ}
    {ip : Nat} (h : GameInv n R s y i a ip) (hle : ∀ j, gvec n s' j ≤ gvec n s j) :
    GameInv n R s' y i a ip :=
  { h with le := fun j => le_trans (hle j) (h.le j) }

/-- An insertion: one value grows by at most one; one more insertion in the round. -/
theorem GameInv.insert {n R : Nat} {s s' : Core} {y : Fin n → ℝ} {i : Fin n} {a : Fin n → ℝ}
    {ip : Nat} (h : GameInv n R s y i a ip) (jc : Fin n)
    (hle : ∀ j, gvec n s' j ≤ gvec n s j + (if j = jc then 1 else 0)) (hip : ip + 1 ≤ R) :
    GameInv n R s' y i (fun j => a j + if j = jc then 1 else 0) (ip + 1) where
  inv := h.inv
  max := h.max
  apos j := by have := h.apos j; split <;> linarith
  asum := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    push_cast; linarith [h.asum]
  le j := by
    have h1 := hle j; have h2 := h.le j
    by_cases hji : j = i <;> by_cases hjc : j = jc <;> simp only [hji, hjc, ite_true, ite_false]
      at h1 h2 ⊢ <;>
      linarith
  ip := hip

/-- An insertion into no game variable. -/
theorem GameInv.insert0 {n R : Nat} {s s' : Core} {y : Fin n → ℝ} {i : Fin n} {a : Fin n → ℝ}
    {ip : Nat} (h : GameInv n R s y i a ip) (hle : ∀ j, gvec n s' j ≤ gvec n s j)
    (hip : ip + 1 ≤ R) : GameInv n R s' y i a (ip + 1) :=
  { h with le := fun j => le_trans (hle j) (h.le j),
           asum := le_trans h.asum (by push_cast; linarith), ip := hip }

/-- **The pop**: zeroing a maximal value starts a new round. -/
theorem GameInv.pop {n R : Nat} {s s' : Core} {y : Fin n → ℝ} {i : Fin n} {a : Fin n → ℝ}
    {ip : Nat} (h : GameInv n R s y i a ip) (jm : Fin n) (hmax : ∀ j, gvec n s j ≤ gvec n s jm)
    (hle : ∀ j, gvec n s' j ≤ if j = jm then 0 else gvec n s j) :
    GameInv n R s' (gvec n s) jm (fun _ => 0) 0 where
  inv := h.cur
  max := hmax
  apos _ := le_rfl
  asum := by simp
  le j := by simpa using hle j
  ip := Nat.zero_le _

/-- **Idle**: when every value is 0, a new round may start. -/
theorem GameInv.reset {n R : Nat} {s : Core} (hz : ∀ j, gvec n s j = 0) (i : Fin n) :
    GameInv n R s 0 i (fun _ => 0) 0 where
  inv := inv_zero (by positivity)
  max _ := le_rfl
  apos _ := le_rfl
  asum := by simp
  le j := by simp [hz j]
  ip := Nat.zero_le _

end OrderMaintenance.Proof
