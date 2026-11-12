/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4818T1HalfOpen
public import LeanPool.ApollonianSuperharmonic.P4818T1ClosedOverlaps
public import Mathlib.Tactic.Ring

-- [TABLET NODE: P4818T1BoundaryRecovery]

/-!
# P4818T1BoundaryRecovery

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4818T1BoundaryRecovery (K : DiamondParameter)
    (P : GaussianInt → Prop)
    (hH : ∀ x, x ∈ P4818T1HalfOpen K → P x)
    (ha : ∀ x, x ∈ DiamondVertexDomains K false →
      x + ⟨0, -(2 * K.1 : Int)⟩ ∈ DiamondVertexDomains K false →
      (P x ↔ P (x + ⟨0, -(2 * K.1 : Int)⟩)))
    (hb : ∀ x, x ∈ DiamondVertexDomains K false →
      x + ⟨(K.1 + 1 : Int), (K.1 : Int)⟩ ∈ DiamondVertexDomains K false →
      (P x ↔ P (x + ⟨(K.1 + 1 : Int), (K.1 : Int)⟩)))
    (hc : ∀ x, x ∈ DiamondVertexDomains K false →
      x + ⟨-(K.1 : Int) - 1, (K.1 : Int)⟩ ∈ DiamondVertexDomains K false →
      (P x ↔ P (x + ⟨-(K.1 : Int) - 1, (K.1 : Int)⟩))) :
    ∀ x, x ∈ DiamondVertexDomains K false → P x := by
-- BODY
  classical
  let k : Int := K.1
  let a : GaussianInt := ⟨0, -2 * k⟩
  let b : GaussianInt := ⟨k + 1, k⟩
  let c : GaussianInt := ⟨-k - 1, k⟩
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast K.2
  obtain ⟨_, hA, hB, hC⟩ := P4818T1ClosedOverlaps K
  have ha' : ∀ x, x ∈ DiamondVertexDomains K false →
      x + a ∈ DiamondVertexDomains K false → (P x ↔ P (x + a)) := by
    simpa only [a, k, neg_mul] using ha
  have hb' : ∀ x, x ∈ DiamondVertexDomains K false →
      x + b ∈ DiamondVertexDomains K false → (P x ↔ P (x + b)) := hb
  have hc' : ∀ x, x ∈ DiamondVertexDomains K false →
      x + c ∈ DiamondVertexDomains K false → (P x ↔ P (x + c)) := hc
  have low (x : GaussianInt) (hx : x ∈ DiamondVertexDomains K false)
      (hy : x.im < k) : x ∈ P4818T1HalfOpen K := by
    refine ⟨hx, ?_, ?_, ?_⟩
    · rintro ⟨he, _, _⟩
      change x.im = 2 * k at he
      omega
    · rintro (⟨j, hj, _, he⟩ | ⟨j, hj, _, he⟩)
      all_goals
        have hi := congrArg Zsqrtd.im he
        change x.im = k + j at hi
        omega
    · rintro (⟨j, hj, _, he⟩ | ⟨j, hj, _, he⟩)
      · have hi := congrArg Zsqrtd.im he
        change x.im = k + j - 1 at hi
        omega
      · have hi := congrArg Zsqrtd.im he
        change x.im = k + j at hi
        omega
  have bottom (r : Int) (hr : -1 ≤ r) (hr' : r ≤ 1) :
      P ⟨r, 0⟩ := by
    have hp := (hA ⟨r, 2 * k⟩).mpr ⟨r, hr, hr', rfl⟩
    have hd := hp.2
    have he : (⟨r, 2 * k⟩ : GaussianInt) + a = ⟨r, 0⟩ := by
      ext <;> simp [a]
    change (⟨r, 2 * k⟩ : GaussianInt) + a ∈ DiamondVertexDomains K false at hd
    rw [he] at hd
    exact hH _ (low _ hd hk)
  have top (r : Int) (hr : -1 ≤ r) (hr' : r ≤ 1) :
      P ⟨r, 2 * k⟩ := by
    have hp := (hA ⟨r, 2 * k⟩).mpr ⟨r, hr, hr', rfl⟩
    have h := ha' _ hp.1 hp.2
    have he : (⟨r, 2 * k⟩ : GaussianInt) + a = ⟨r, 0⟩ := by
      ext <;> simp [a]
    rw [he] at h
    exact h.mpr (bottom r hr hr')
  have middleR : P ⟨k, k⟩ := by
    have hp := (hB ⟨-1, 0⟩).mpr (Or.inr ⟨0, by decide, hk, rfl⟩)
    have h := (hb' _ hp.1 hp.2).mp (bottom (-1) (by decide) (by decide))
    have he : (⟨-1, 0⟩ : GaussianInt) + b = ⟨k, k⟩ := by
      ext <;> simp [b]
    simpa only [he] using h
  have middleL : P ⟨-k, k⟩ := by
    have hp := (hC ⟨1, 0⟩).mpr ⟨1, by decide, by omega, Or.inl (by simp)⟩
    have h := (hc' _ hp.1 hp.2).mp (bottom 1 (by decide) (by decide))
    have he : (⟨1, 0⟩ : GaussianInt) + c = ⟨-k, k⟩ := by
      ext <;> simp [c]
    simpa only [he] using h
  have bFirst (j : Int) (hj : 1 ≤ j) (hjk : j ≤ k) : P ⟨-j, j⟩ := by
    by_cases he : j = k
    · simpa only [he] using middleL
    · have hp := (hB ⟨-j, j⟩).mpr (Or.inl ⟨j, hj, hjk, rfl⟩)
      exact hH _ (low _ hp.1 (by change j < k; omega))
  have bSecond (j : Int) (hj : 0 ≤ j) (hjk : j < k) : P ⟨-1 - j, j⟩ := by
    have hp := (hB ⟨-1 - j, j⟩).mpr (Or.inr ⟨j, hj, hjk, rfl⟩)
    exact hH _ (low _ hp.1 hjk)
  have cFirst (j : Int) (hj : 1 ≤ j) (hjk : j ≤ k) : P ⟨j, j - 1⟩ := by
    have hp := (hC ⟨j, j - 1⟩).mpr ⟨j, hj, hjk, Or.inl rfl⟩
    exact hH _ (low _ hp.1 (by change j - 1 < k; omega))
  have cSecond (j : Int) (hj : 1 ≤ j) (hjk : j ≤ k) : P ⟨j, j⟩ := by
    by_cases he : j = k
    · simpa only [he] using middleR
    · have hp := (hC ⟨j, j⟩).mpr ⟨j, hj, hjk, Or.inr rfl⟩
      exact hH _ (low _ hp.1 (by change j < k; omega))
  intro x hx
  by_cases hUa : x.im = 2 * k ∧ -1 ≤ x.re ∧ x.re ≤ 1
  · have he : x = (⟨x.re, 2 * k⟩ : GaussianInt) := by
      ext <;> simp [hUa.1]
    rw [he]
    exact top x.re hUa.2.1 hUa.2.2
  by_cases hUb :
      (∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ x = ⟨k + 1 - j, k + j⟩) ∨
      (∃ j : Int, 0 ≤ j ∧ j < k ∧ x = ⟨k - j, k + j⟩)
  · rcases hUb with ⟨j, hj, hjk, rfl⟩ | ⟨j, hj, hjk, rfl⟩
    · have hp := (hB ⟨-j, j⟩).mpr (Or.inl ⟨j, hj, hjk, rfl⟩)
      have h := (hb' _ hp.1 hp.2).mp (bFirst j hj hjk)
      have he : (⟨-j, j⟩ : GaussianInt) + b = ⟨k + 1 - j, k + j⟩ := by
        ext <;> simp [b] <;> ring
      simpa only [he] using h
    · have hp := (hB ⟨-1 - j, j⟩).mpr (Or.inr ⟨j, hj, hjk, rfl⟩)
      have h := (hb' _ hp.1 hp.2).mp (bSecond j hj hjk)
      have he : (⟨-1 - j, j⟩ : GaussianInt) + b = ⟨k - j, k + j⟩ := by
        ext <;> simp [b] <;> ring
      simpa only [he] using h
  by_cases hUc :
      (∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ x = ⟨j - k - 1, k + j - 1⟩) ∨
      (∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ x = ⟨j - k - 1, k + j⟩)
  · rcases hUc with ⟨j, hj, hjk, rfl⟩ | ⟨j, hj, hjk, rfl⟩
    · have hp := (hC ⟨j, j - 1⟩).mpr ⟨j, hj, hjk, Or.inl rfl⟩
      have h := (hc' _ hp.1 hp.2).mp (cFirst j hj hjk)
      have he : (⟨j, j - 1⟩ : GaussianInt) + c = ⟨j - k - 1, k + j - 1⟩ := by
        ext <;> simp [c] <;> ring
      simpa only [he] using h
    · have hp := (hC ⟨j, j⟩).mpr ⟨j, hj, hjk, Or.inr rfl⟩
      have h := (hc' _ hp.1 hp.2).mp (cSecond j hj hjk)
      have he : (⟨j, j⟩ : GaussianInt) + c = ⟨j - k - 1, k + j⟩ := by
        ext <;> simp [c] <;> ring
      simpa only [he] using h
  exact hH x ⟨hx, hUa, hUb, hUc⟩

end ApollonianSuperharmonic

end
