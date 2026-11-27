/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelLocalBound

/-!
# The actual two-ball cutoff partition and four original kernel patches

On the total source support the two translated cutoffs sum to one. Their
four products therefore reconstruct the original kernel from the actual
local patch values; no decomposition of a completed source is assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Set Metric
open scoped SchwartzMap

theorem jointUnitCutoffTest_zero_other (a b x : EuclideanSpace ℝ (Fin 3))
    (hab : 5 ≤ dist a b) (hx : x ∈ closedBall a 1) :
    (jointUnitCutoffTest b).1 x = 0 := by
  apply (jointUnitBump b).zero_of_le_dist
  change 2 ≤ dist x b
  have hax : dist a x ≤ 1 := by simpa only [mem_closedBall, dist_comm] using hx
  linarith [dist_triangle a x b]

theorem jointUnitCutoffTest_sum_eq_one (c : Fin 2 → EuclideanSpace ℝ (Fin 3))
    (hc : 5 ≤ dist (c 0) (c 1)) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ closedBall (c 0) 1 ∪ closedBall (c 1) 1) :
    (∑ i : Fin 2, ((jointUnitCutoffTest (c i)).1 x : ℂ)) = 1 := by
  rw [Fin.sum_univ_two]
  rcases hx with hx | hx
  · rw [jointUnitCutoffTest_eq_one _ _ hx, jointUnitCutoffTest_zero_other _ _ _ hc hx]
    norm_num
  · rw [jointUnitCutoffTest_eq_one _ _ hx,
      jointUnitCutoffTest_zero_other (c 1) (c 0) x (by simpa only [dist_comm] using hc) hx]
    norm_num

theorem jointUnitCutoffTest_nonzero_locates (c : Fin 2 → EuclideanSpace ℝ (Fin 3))
    (hc : 5 ≤ dist (c 0) (c 1)) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ closedBall (c 0) 1 ∪ closedBall (c 1) 1)
    (i : Fin 2) (hi : (jointUnitCutoffTest (c i)).1 x ≠ 0) :
    x ∈ closedBall (c i) 1 := by
  fin_cases i
  · rcases hx with hx | hx
    · exact hx
    · exact False.elim (hi (jointUnitCutoffTest_zero_other (c 1) (c 0) x
        (by simpa only [dist_comm] using hc) hx))
  · rcases hx with hx | hx
    · exact False.elim (hi (jointUnitCutoffTest_zero_other (c 0) (c 1) x hc hx))
    · exact hx

/-- Four literal locally cut off kernels agree with the original scalar
kernel everywhere that both original test sources can be nonzero. -/
theorem jointLocalKernel_four_patches_eq (c : Fin 2 → EuclideanSpace ℝ (Fin 3))
    (hc : 5 ≤ dist (c 0) (c 1)) (H : Fin 2 → Fin 2 → JointKernelSpace → ℂ)
    (O : Fin 2 → Fin 2 → Set JointKernelSpace) (hO : ∀ i j, IsOpen (O i j))
    (hbox : ∀ i j, jointKernelBox (c i) (c j) 2 ⊆ O i j)
    (hH : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (H i j) (O i j))
    (F : JointKernelSpace → ℂ)
    (hF : ∀ i j x, x.fst ∈ closedBall (c i) 1 → x.snd ∈ closedBall (c j) 1 → H i j x = F x)
    (x : JointKernelSpace)
    (hx : x.fst ∈ closedBall (c 0) 1 ∪ closedBall (c 1) 1)
    (hy : x.snd ∈ closedBall (c 0) 1 ∪ closedBall (c 1) 1) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      cutOffJointLocalKernel (c i) (c j) (H i j) (O i j) (hO i j) (hbox i j) (hH i j) x) = F x := by
  simp only [cutOffJointLocalKernel_apply, jointSmoothCutoff_apply]
  calc
    _ = ∑ i : Fin 2, ∑ j : Fin 2,
        (((jointUnitCutoffTest (c i)).1 x.fst : ℂ) *
          ((jointUnitCutoffTest (c j)).1 x.snd : ℂ)) * F x := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hi0 : (jointUnitCutoffTest (c i)).1 x.fst = 0
      · simp only [hi0, Complex.ofReal_zero, zero_mul]
      by_cases hj0 : (jointUnitCutoffTest (c j)).1 x.snd = 0
      · simp only [hj0, Complex.ofReal_zero, mul_zero, zero_mul]
      rw [hF i j x (jointUnitCutoffTest_nonzero_locates c hc x.fst hx i hi0)
        (jointUnitCutoffTest_nonzero_locates c hc x.snd hy j hj0)]
    _ = ((∑ i : Fin 2, ((jointUnitCutoffTest (c i)).1 x.fst : ℂ)) *
        (∑ j : Fin 2, ((jointUnitCutoffTest (c j)).1 x.snd : ℂ))) * F x := by
      rw [Fintype.sum_mul_sum]
      simp only [Finset.sum_mul]
    _ = F x := by rw [jointUnitCutoffTest_sum_eq_one c hc _ hx,
      jointUnitCutoffTest_sum_eq_one c hc _ hy, one_mul, one_mul]

end VacuumBellSeparation
