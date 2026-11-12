/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian

-- [TABLET NODE: P4849T1MinimumTruncation]

/-!
# P4849T1MinimumTruncation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4849T1MinimumTruncation (g q : IntegerLatticeFunction)
    (hg : ∀ x, FourNeighborLaplacian g x ≤ 1)
    (hq : ∀ x, 0 ≤ q x)
    (hplus : ∀ x, FourNeighborLaplacian (fun y => g y + q y) x ≤ 1) :
    ∀ x, FourNeighborLaplacian
      (fun y => g y + Set.indicator {z | 0 < q z} (fun _ => (1 : ℤ)) y) x ≤ 1 := by
-- BODY
  classical
  let I : GaussianInt → ℤ := Set.indicator {z | 0 < q z} (fun _ => (1 : ℤ))
  have hI (y : GaussianInt) : I y ≤ 1 ∧ I y ≤ q y := by
    by_cases hy : 0 < q y
    · simp [I, hy]
      omega
    · simp [I, hy, hq y]
  intro x
  change FourNeighborLaplacian (fun y => g y + I y) x ≤ 1
  by_cases hx : 0 < q x
  · have hIx : I x = 1 := by simp [I, hx]
    have h := hg x
    simp only [FourNeighborLaplacian] at h ⊢
    rw [hIx]
    linarith [(hI (x + 1)).1, (hI (x - 1)).1,
      (hI (x + ⟨0, 1⟩)).1, (hI (x - ⟨0, 1⟩)).1]
  · have hqx : q x = 0 := by have := hq x; omega
    have hIx : I x = 0 := by simp [I, hx]
    have h := hplus x
    simp only [FourNeighborLaplacian] at h ⊢
    rw [hIx]
    rw [hqx] at h
    linarith [(hI (x + 1)).2, (hI (x - 1)).2,
      (hI (x + ⟨0, 1⟩)).2, (hI (x - ⟨0, 1⟩)).2]

end ApollonianSuperharmonic

end
