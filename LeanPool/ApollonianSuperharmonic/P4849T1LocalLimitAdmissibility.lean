/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian

-- [TABLET NODE: P4849T1LocalLimitAdmissibility]

/-!
# P4849T1LocalLimitAdmissibility

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4849T1LocalLimitAdmissibility (g : IntegerLatticeFunction)
    (C : ℕ → Set GaussianInt) (L : Set GaussianInt)
    (hC : ∀ n x, FourNeighborLaplacian
      (fun y => g y + Set.indicator (C n) (fun _ => (1 : ℤ)) y) x ≤ 1)
    (hlocal : ∀ F : Finset GaussianInt, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ F,
      (x ∈ C n ↔ x ∈ L)) :
    ∀ x, FourNeighborLaplacian
      (fun y => g y + Set.indicator L (fun _ => (1 : ℤ)) y) x ≤ 1 := by
-- BODY
  classical
  intro x
  obtain ⟨N, hN⟩ := hlocal {x, x + 1, x - 1, x + ⟨0, 1⟩, x - ⟨0, 1⟩}
  have heq (y : GaussianInt)
      (hy : y ∈ ({x, x + 1, x - 1, x + ⟨0, 1⟩, x - ⟨0, 1⟩} : Finset GaussianInt)) :
      Set.indicator (C N) (fun _ => (1 : ℤ)) y =
        Set.indicator L (fun _ => (1 : ℤ)) y := by
    have h := hN N le_rfl y hy
    by_cases hc : y ∈ C N
    · simp [hc, h.mp hc]
    · have hl : y ∉ L := fun hl => hc (h.mpr hl)
      simp [hc, hl]
  have h := hC N x
  simp only [FourNeighborLaplacian] at h ⊢
  simpa only [heq x (by simp), heq (x + 1) (by simp),
    heq (x - 1) (by simp), heq (x + ⟨0, 1⟩) (by simp),
    heq (x - ⟨0, 1⟩) (by simp)] using h

end ApollonianSuperharmonic

end
