/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.DiamondExceptionalLattice
public import Mathlib.Tactic

-- [TABLET NODE: P5435T1PeriodGap]

/-!
# P5435T1PeriodGap

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5435T1PeriodGap (K : DiamondParameter) :
    ∀ v ∈ DiamondExceptionalLattice K, v ≠ 0 →
      2 * (K.1 : Int) ≤ |v.re| + |v.im| := by
-- BODY
  let k : Int := K.1
  have hk : 0 < k := by dsimp [k]; exact_mod_cast K.2
  let H : AddSubgroup GaussianInt :=
    { carrier := {v | ∃ m n : Int, v.re = n*(k+1) ∧ v.im = k*(n-2*m)}
      zero_mem' := ⟨0, 0, by simp, by simp⟩
      add_mem' := by
        rintro u v ⟨m, n, hr, hi⟩ ⟨m', n', hr', hi'⟩
        refine ⟨m+m', n+n', ?_, ?_⟩
        · simp only [Zsqrtd.re_add, hr, hr']; ring
        · simp only [Zsqrtd.im_add, hi, hi']; ring
      neg_mem' := by
        rintro v ⟨m, n, hr, hi⟩
        refine ⟨-m, -n, ?_, ?_⟩
        · simp only [Zsqrtd.re_neg, hr]; ring
        · simp only [Zsqrtd.im_neg, hi]; ring }
  have hgen : {v : GaussianInt | v = ⟨0, -(2 * K.1 : Int)⟩ ∨
      v = ⟨(K.1 + 1 : Int), (K.1 : Int)⟩} ⊆ H := by
    intro v hv
    rcases hv with rfl | rfl
    · refine ⟨1, 0, by simp, ?_⟩
      change -(2*k) = k*(0-2*1)
      ring
    · exact ⟨0, 1, by simp [k], by simp [k]⟩
  intro v hv hne
  obtain ⟨m, n, hr, hi⟩ := ((AddSubgroup.closure_le H).mpr hgen) hv
  change 2*k ≤ |v.re| + |v.im|
  rw [hr, hi, abs_mul, abs_mul, abs_of_pos hk, abs_of_pos (by omega : 0 < k+1)]
  by_cases hn : n=0
  · subst n
    have hm : m ≠ 0 := by
      intro hm
      apply hne
      ext <;> simp_all
    have hab : 1 ≤ |m| := by have h := abs_pos.mpr hm; omega
    rw [zero_sub, abs_neg, abs_mul]
    norm_num
    nlinarith
  · have han : 1 ≤ |n| := by have h := abs_pos.mpr hn; omega
    by_cases hlarge : 2 ≤ |n|
    · have hnonneg := abs_nonneg (n-2*m)
      nlinarith
    · have hone : n=1 ∨ n = -1 := by
        simp only [abs_eq_max_neg] at han hlarge
        omega
      have hodd : n-2*m ≠ 0 := by rcases hone with rfl | rfl <;> omega
      have ham : 1 ≤ |n-2*m| := by have h := abs_pos.mpr hodd; omega
      nlinarith

end ApollonianSuperharmonic

end
