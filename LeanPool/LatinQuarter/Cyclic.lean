/-
Copyright (c) 2026 Richard Bean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Bean
-/
module

public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Linarith
public import LeanPool.LatinQuarter.Basic

/-!
# The cyclic Latin square and its corner set
-/

@[expose] public section

namespace LatinQuarter

/-- The addition table of `Fin n`, used to attain the critical-set bound. -/
def cyclic (n : ℕ) : Square n := fun r c => r + c

theorem cyclic_isLatin (n : ℕ) (hn : 0 < n) : IsLatin (cyclic n) := by
  let : NeZero n := ⟨by omega⟩
  exact ⟨fun r => (Equiv.addLeft r).bijective, fun c => (Equiv.addRight c).bijective⟩

/-- The two opposite triangular corners in the cyclic Latin square. -/
def cornerSet (n : ℕ) : Finset (Cell n) :=
  Finset.univ.filter (fun p => p.1.val + p.2.val < n / 2 ∨
    n + n / 2 ≤ p.1.val + p.2.val)

@[simp] theorem mem_cornerSet {n : ℕ} (r c : Fin n) :
    (r, c) ∈ cornerSet n ↔ r.val + c.val < n / 2 ∨
      n + n / 2 ≤ r.val + c.val := by simp [cornerSet]

/-- Rows are visited from top to bottom, and each row from right to left. -/
def fillingOrder {n : ℕ} (r c : Fin n) : ℕ := r.val * n + (n - 1 - c.val)

theorem fillingOrder_row {n : ℕ} (r i c d : Fin n) (hi : i < r) :
    fillingOrder i d < fillingOrder r c := by
  have hn := c.isLt
  have hd := d.isLt
  have hi' : i.val + 1 ≤ r.val := hi
  have hm := Nat.mul_le_mul_right n hi'
  have hrem : n - 1 - d.val < n := by omega
  unfold fillingOrder
  nlinarith

theorem fillingOrder_column {n : ℕ} (r c j : Fin n) (hj : c < j) :
    fillingOrder r j < fillingOrder r c := by
  have hc := c.isLt
  have hjn := j.isLt
  unfold fillingOrder
  omega

/-- Every non-corner cell is forced by the cells preceding it. -/
theorem corner_forcing_step {n : ℕ} (hn : 0 < n) (M : Square n)
    (hM : IsLatin M) (ha : Agrees (cornerSet n) (cyclic n) M)
    (r c : Fin n)
    (hprev : ∀ i j, fillingOrder i j < fillingOrder r c → M i j = cyclic n i j) :
    M r c = cyclic n r c := by
  classical
  by_cases hrc : (r, c) ∈ cornerSet n
  · exact ha (r, c) hrc
  have hL := cyclic_isLatin n hn
  obtain ⟨j, hj⟩ := (hL.1 r).surjective (M r c)
  by_cases hjc : j = c
  · simpa [hjc] using hj.symm
  have hrow : M r j ≠ M r c := fun he => hjc ((hM.1 r).injective he)
  by_cases hjright : c < j
  · have he := hprev r j (fillingOrder_column r c j hjright)
    exact (hrow (he.trans hj)).elim
  by_cases hrj : (r, j) ∈ cornerSet n
  · exact (hrow ((ha (r, j) hrj).trans hj)).elim
  have hjlt : j.val < c.val := by
    have hne : j.val ≠ c.val := fun he => hjc (Fin.ext he)
    change ¬c.val < j.val at hjright
    omega
  have hband : n / 2 ≤ r.val + j.val ∧ r.val + j.val < n + n / 2 := by
    simpa only [mem_cornerSet, not_or, not_lt, not_le] using hrj
  let u := r.val + j.val
  by_cases huc : c.val ≤ u
  · let i : Fin n := ⟨u - c.val, by have := r.isLt; dsimp [u]; omega⟩
    have hir : i < r := by change u - c.val < r.val; dsimp [u]; omega
    have hiadd : cyclic n i c = cyclic n r j := by
      apply Fin.ext
      change (i.val + c.val) % n = (r.val + j.val) % n
      have he : i.val + c.val = r.val + j.val := by dsimp [i, u]; omega
      rw [he]
    have he := hprev i c (fillingOrder_row r i c c hir)
    have hirEq := (hM.2 c).injective (he.trans (hiadd.trans hj))
    exact (ne_of_lt hir hirEq).elim
  · let i : Fin n := ⟨u + n - c.val, by have := c.isLt; omega⟩
    have hiadd : cyclic n i c = cyclic n r j := by
      apply Fin.ext
      change (i.val + c.val) % n = (r.val + j.val) % n
      have he : i.val + c.val = u + n := by have := c.isLt; dsimp [i]; omega
      rw [he, Nat.add_mod_right]
    have hic : (i, c) ∈ cornerSet n := by
      apply (mem_cornerSet i c).mpr
      right
      have := c.isLt
      dsimp [i, u]
      omega
    have hirEq := (hM.2 c).injective ((ha (i, c) hic).trans (hiadd.trans hj))
    have he : cyclic n r c = cyclic n r j := by
      change i = r at hirEq
      rw [hirEq] at hiadd
      exact hiadd
    exact (hjc ((hL.1 r).injective he).symm).elim

theorem cornerSet_isDefining (n : ℕ) (hn : 0 < n) :
    IsDefining (cornerSet n) (cyclic n) := by
  refine ⟨cyclic_isLatin n hn, ?_⟩
  intro M hM ha
  have all : ∀ m : ℕ, ∀ r c : Fin n, fillingOrder r c = m → M r c = cyclic n r c := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro r c hrc
      apply corner_forcing_step hn M hM ha r c
      intro i j hij
      exact ih (fillingOrder i j) (by omega) i j rfl
  funext r c
  exact all _ r c rfl

end LatinQuarter
