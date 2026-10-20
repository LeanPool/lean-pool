/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Group.End

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Positivity.Finset


/-!
# Identical-machine scheduling

Machine loads and makespans, list schedules with arbitrary tie breaking, LPT schedules,
and the two families attaining Graham's bounds. Processing times are real numbers;
nonnegativity and positivity are imposed by the individual results that require them.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- The load of machine `i` from the jobs of index below `k` under the assignment `σ`. -/
def loadBefore {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (k : ℕ) (i : Fin m) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i), p j

/-- The load of machine `i`: the total length of the jobs assigned to it. -/
def load {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (i : Fin m) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin n => σ j = i), p j

/-- The makespan of an assignment: its largest machine load. -/
def makespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) : ℝ :=
  univ.sup' univ_nonempty (load p σ)

/-- The optimal makespan: the least makespan over all assignments of the `n` jobs to the `m`
machines. -/
def optMakespan (m : ℕ) [NeZero m] {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  univ.inf' univ_nonempty (fun σ : Fin n → Fin m => makespan p σ)

/-- A list schedule in the index order: each job `k` goes to a machine whose load from the jobs
before `k` is least,
under any tie-breaking. -/
def IsListSchedule {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) : Prop :=
  ∀ k : Fin n, ∀ i : Fin m, loadBefore p σ k (σ k) ≤ loadBefore p σ k i

/-- An LPT schedule: a list schedule of the jobs taken in some nonincreasing order of length. -/
def IsLPTSchedule {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) : Prop :=
  ∃ π : Equiv.Perm (Fin n), Antitone (p ∘ π) ∧ IsListSchedule (p ∘ π) (σ ∘ π)

/-- Graham's instance for LPT: the `2m + 1` lengths `2m − 1, 2m − 1, 2m − 2, 2m − 2, …, m + 1, m +
1, m, m, m`. -/
def grahamJobs (m : ℕ) : Fin (2 * m + 1) → ℝ := fun j =>
  if (j : ℕ) < 2 * m then 2 * (m : ℝ) - 1 - (((j : ℕ) / 2 : ℕ) : ℝ) else (m : ℝ)

/-- The order `2m − 1, …, m + 1, m, m, 2m − 1, …, m + 1, m` of Graham's instance, as the job at
each position:
position `i < m − 1` holds job `2i` (length `2m − 1 − i`), positions `m − 1` and `m` hold jobs `2m
− 2` and `2m − 1`
(length `m`), position `m + 1 + a` with `a < m − 1` holds job `2a + 1` (length `2m − 1 − a`), and
position `2m` holds
job `2m` (length `m`). -/
def grahamOrder (m : ℕ) (i : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
  if h : (i : ℕ) < m - 1 then
    ⟨2 * i, Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left h Nat.two_pos)
      (Nat.mul_le_mul_left 2 (Nat.sub_le m 1)))⟩
  else if (i : ℕ) = m - 1 then ⟨2 * m - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  else if (i : ℕ) = m then ⟨2 * m - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  else if h' : (i : ℕ) < 2 * m then
    ⟨2 * ((i : ℕ) - m - 1) + 1, Nat.succ_lt_succ (Nat.mul_lt_mul_of_pos_left
      (Nat.lt_of_le_of_lt
        (Nat.sub_le_sub_right (Nat.sub_le_iff_le_add.2 (Nat.two_mul m ▸ Nat.le_of_lt h')) 1)
        (Nat.sub_one_lt (Nat.ne_of_gt (Nat.lt_of_mul_lt_mul_left (a := 2) (b := 0)
          (Nat.lt_of_le_of_lt (Nat.zero_le i) h')))))
      Nat.two_pos)⟩
  else ⟨2 * m, Nat.lt_succ_self _⟩

/-- Graham's instance for list scheduling: `m(m − 1)` unit jobs followed by one job of length `m`.
-/
def unitJobs (m : ℕ) : Fin (m * (m - 1) + 1) → ℝ := fun j =>
  if (j : ℕ) < m * (m - 1) then 1 else (m : ℝ)

end GrahamLPT
