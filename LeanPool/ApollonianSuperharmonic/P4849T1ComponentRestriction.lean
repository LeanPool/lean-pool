/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4849T1Component
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian

-- [TABLET NODE: P4849T1ComponentRestriction]

/-!
# P4849T1ComponentRestriction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4849T1ComponentRestriction (g : IntegerLatticeFunction)
    (A C : Set GaussianInt)
    (hg : ∀ x, FourNeighborLaplacian g x ≤ 1)
    (hA : ∀ x, FourNeighborLaplacian
      (fun y => g y + Set.indicator A (fun _ => (1 : ℤ)) y) x ≤ 1)
    (hC : P4849T1Component A C) :
    ∀ x, FourNeighborLaplacian
      (fun y => g y + Set.indicator C (fun _ => (1 : ℤ)) y) x ≤ 1 := by
-- BODY
  classical
  have symm {x y : GaussianInt} (h : FourNeighborAdjacent x y) :
      FourNeighborAdjacent y x := by
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl (by rw [h]; abel))
    · exact Or.inl (by rw [h]; abel)
    · exact Or.inr (Or.inr (Or.inr (by rw [h]; abel)))
    · exact Or.inr (Or.inr (Or.inl (by rw [h]; abel)))
  let I (S : Set GaussianInt) (y : GaussianInt) : ℤ :=
    Set.indicator S (fun _ => (1 : ℤ)) y
  have hsub (y : GaussianInt) : I C y ≤ I A y := by
    by_cases hy : y ∈ C
    · simp [I, hy, hC.2.1 hy]
    · simp [I, hy]
      by_cases ha : y ∈ A <;> simp [ha]
  intro x
  change FourNeighborLaplacian (fun y => g y + I C y) x ≤ 1
  by_cases hx : x ∈ C
  · have heq (y : GaussianInt) (hy : FourNeighborAdjacent x y) : I C y = I A y := by
      by_cases ha : y ∈ A
      · simp [I, ha, hC.2.2 x hx y ha hy]
      · have hc : y ∉ C := fun hc => ha (hC.2.1 hc)
        simp [I, ha, hc]
    have h := hA x
    change FourNeighborLaplacian (fun y => g y + I A y) x ≤ 1 at h
    simp only [FourNeighborLaplacian] at h ⊢
    rw [heq (x + 1) (Or.inl rfl),
      heq (x - 1) (Or.inr (Or.inl rfl)),
      heq (x + ⟨0, 1⟩) (Or.inr (Or.inr (Or.inl rfl))),
      heq (x - ⟨0, 1⟩) (Or.inr (Or.inr (Or.inr rfl)))]
    simpa [I, hx, hC.2.1 hx] using h
  · by_cases ha : x ∈ A
    · have hzero (y : GaussianInt) (hy : FourNeighborAdjacent x y) : I C y = 0 := by
        have hc : y ∉ C := fun hc => hx (hC.2.2 y hc x ha (symm hy))
        simp [I, hc]
      simp only [FourNeighborLaplacian]
      rw [hzero (x + 1) (Or.inl rfl),
        hzero (x - 1) (Or.inr (Or.inl rfl)),
        hzero (x + ⟨0, 1⟩) (Or.inr (Or.inr (Or.inl rfl))),
        hzero (x - ⟨0, 1⟩) (Or.inr (Or.inr (Or.inr rfl)))]
      simpa [I, hx, FourNeighborLaplacian] using hg x
    · have h := hA x
      change FourNeighborLaplacian (fun y => g y + I A y) x ≤ 1 at h
      have hIx : I C x = 0 := by simp [I, hx]
      have hAx : I A x = 0 := by simp [I, ha]
      simp only [FourNeighborLaplacian] at h ⊢
      rw [hIx]
      rw [hAx] at h
      linarith [hsub (x + 1), hsub (x - 1),
        hsub (x + ⟨0, 1⟩), hsub (x - ⟨0, 1⟩)]

end ApollonianSuperharmonic

end
