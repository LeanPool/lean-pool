/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.DiamondVertexDomains
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

-- [TABLET NODE: P4818T1ClosedOverlaps]

/-!
# P4818T1ClosedOverlaps

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4818T1ClosedOverlaps (K : DiamondParameter) :
    let k : Int := K.1
    let a : GaussianInt := ⟨0, -2 * k⟩
    let b : GaussianInt := ⟨k + 1, k⟩
    let c : GaussianInt := ⟨-k - 1, k⟩
    (∀ (x : GaussianInt) (m n : Int),
      x ∈ DiamondVertexDomains K false →
      x + m • a + n • b ∈ DiamondVertexDomains K false →
      (m = 0 ∧ n = 0) ∨ (m = 1 ∧ n = 0) ∨ (m = -1 ∧ n = 0) ∨
      (m = 0 ∧ n = 1) ∨ (m = 0 ∧ n = -1) ∨
      (m = 1 ∧ n = 1) ∨ (m = -1 ∧ n = -1)) ∧
    (∀ x, (x ∈ DiamondVertexDomains K false ∧
      x + a ∈ DiamondVertexDomains K false) ↔
      ∃ r : Int, -1 ≤ r ∧ r ≤ 1 ∧ x = ⟨r, 2 * k⟩) ∧
    (∀ x, (x ∈ DiamondVertexDomains K false ∧
      x + b ∈ DiamondVertexDomains K false) ↔
      (∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ x = ⟨-j, j⟩) ∨
      (∃ j : Int, 0 ≤ j ∧ j < k ∧ x = ⟨-1 - j, j⟩)) ∧
    (∀ x, (x ∈ DiamondVertexDomains K false ∧
      x + c ∈ DiamondVertexDomains K false) ↔
      ∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ (x = ⟨j, j - 1⟩ ∨ x = ⟨j, j⟩)) := by
-- BODY
  change {k : Nat // 0 < k} at K
  dsimp only
  let k : Int := K.1
  let a : GaussianInt := ⟨0, -2 * k⟩
  let b : GaussianInt := ⟨k + 1, k⟩
  let c : GaussianInt := ⟨-k - 1, k⟩
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast K.2
  have mem (z : GaussianInt) : z ∈ DiamondVertexDomains K false ↔
      -k ≤ z.re ∧ z.re ≤ k ∧ 0 ≤ z.im ∧ z.im ≤ 2 * k ∧
      z.re + z.im ≤ 2 * k + 1 ∧ -z.re + z.im ≤ 2 * k + 1 ∧
      z.re - z.im ≤ 1 ∧ -z.re - z.im ≤ 1 := by
    have raw : z ∈ DiamondVertexDomains K false ↔
        z.re.natAbs ≤ K.1 ∧ (z.im - k).natAbs ≤ K.1 ∧
        z.re.natAbs + (z.im - k).natAbs ≤ K.1 + 1 := by
      change max z.re.natAbs (max (z.im - k).natAbs
        (z.re.natAbs + (z.im - k).natAbs - 1)) ≤ K.1 ↔ _
      simp only [max_le_iff, Nat.sub_le_iff_le_add]
    rw [raw]
    have h1 := Int.natCast_natAbs z.re
    have h2 := Int.natCast_natAbs (z.im - k)
    by_cases hr : 0 ≤ z.re <;> by_cases hi : 0 ≤ z.im - k
    · rw [abs_of_nonneg hr] at h1
      rw [abs_of_nonneg hi] at h2
      omega
    · rw [abs_of_nonneg hr] at h1
      rw [abs_of_neg (by omega : z.im - k < 0)] at h2
      omega
    · rw [abs_of_neg (by omega : z.re < 0)] at h1
      rw [abs_of_nonneg hi] at h2
      omega
    · rw [abs_of_neg (by omega : z.re < 0)] at h1
      rw [abs_of_neg (by omega : z.im - k < 0)] at h2
      omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x m n hx hy
    have hx' := (mem x).mp hx
    have hy' := (mem (x + m • a + n • b)).mp hy
    have hr : (x + m • a + n • b).re = x.re + n * (k + 1) := by
      simp [a, b, zsmul_eq_mul]
    have hi : (x + m • a + n • b).im = x.im + k * (n - 2 * m) := by
      simp [a, b, zsmul_eq_mul]
      ring
    rw [hr, hi] at hy'
    have hnl : -1 ≤ n := by
      by_contra hn
      have hn' : n ≤ -2 := by omega
      have hmul := mul_le_mul_of_nonneg_right hn' (by omega : 0 ≤ k + 1)
      nlinarith only [hx'.1, hx'.2.1, hy'.1, hy'.2.1, hmul]
    have hnu : n ≤ 1 := by
      by_contra hn
      have hn' : 2 ≤ n := by omega
      have hmul := mul_le_mul_of_nonneg_right hn' (by omega : 0 ≤ k + 1)
      nlinarith only [hx'.1, hx'.2.1, hy'.1, hy'.2.1, hmul]
    have hvl : -2 ≤ n - 2 * m := by
      by_contra hv
      have hv' : n - 2 * m ≤ -3 := by omega
      have hmul := mul_le_mul_of_nonneg_left hv' hk.le
      nlinarith only [hx'.2.2.1, hx'.2.2.2.1, hy'.2.2.1,
        hy'.2.2.2.1, hmul, hk]
    have hvu : n - 2 * m ≤ 2 := by
      by_contra hv
      have hv' : 3 ≤ n - 2 * m := by omega
      have hmul := mul_le_mul_of_nonneg_left hv' hk.le
      nlinarith only [hx'.2.2.1, hx'.2.2.2.1, hy'.2.2.1,
        hy'.2.2.2.1, hmul, hk]
    omega
  · intro x
    constructor
    · rintro ⟨hx, hy⟩
      have hx' := (mem x).mp hx
      have hy' := (mem (x + a)).mp hy
      simp only [Zsqrtd.re_add, Zsqrtd.im_add] at hy'
      dsimp [a] at hy'
      refine ⟨x.re, by omega, by omega, ?_⟩
      ext
      · rfl
      · change x.im = 2 * k
        omega
    · rintro ⟨r, hr, hr', rfl⟩
      simp only [mem, Zsqrtd.re_add, Zsqrtd.im_add]
      omega
  · intro x
    constructor
    · rintro ⟨hx, hy⟩
      have hx' := (mem x).mp hx
      have hy' := (mem (x + b)).mp hy
      simp only [Zsqrtd.re_add, Zsqrtd.im_add] at hy'
      dsimp [b] at hy'
      by_cases he : x.im = -x.re
      · left
        refine ⟨-x.re, by omega, by omega, ?_⟩
        ext <;> simp [he]
      · right
        refine ⟨x.im, by omega, by omega, ?_⟩
        ext
        · change x.re = -1 - x.im
          omega
        · rfl
    · rintro (⟨j, hj, hjk, rfl⟩ | ⟨j, hj, hjk, rfl⟩)
      all_goals
        simp only [mem, Zsqrtd.re_add, Zsqrtd.im_add]
        omega
  · intro x
    constructor
    · rintro ⟨hx, hy⟩
      have hx' := (mem x).mp hx
      have hy' := (mem (x + c)).mp hy
      simp only [Zsqrtd.re_add, Zsqrtd.im_add] at hy'
      dsimp [c] at hy'
      refine ⟨x.re, by omega, by omega, ?_⟩
      by_cases he : x.im = x.re
      · right
        ext <;> simp [he]
      · left
        ext
        · rfl
        · change x.im = x.re - 1
          omega
    · rintro ⟨j, hj, hjk, rfl | rfl⟩
      all_goals
        simp only [mem, Zsqrtd.re_add, Zsqrtd.im_add]
        omega

end ApollonianSuperharmonic

end
