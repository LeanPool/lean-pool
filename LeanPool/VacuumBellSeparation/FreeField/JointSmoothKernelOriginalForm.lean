/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelFourPatches

/-!
# Four-patch operators represent the original joint-source kernel

The identities below use the original test sources in the total covariance
completion. The four-patch integral theorem proves convergence of the
original kernel pairing before the completed operator is identified.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open MeasureTheory Set Metric
open scoped SchwartzMap InnerProductSpace

theorem jointFourFieldKernelOperator_pairing {μ : ℝ} (hμ : 0 < μ)
    (c : Fin 2 → EuclideanSpace ℝ (Fin 3))
    (K : Fin 2 → Fin 2 → SchwartzMap JointKernelSpace ℂ) (F : JointKernelSpace → ℂ)
    (hF : ∀ x, x.fst ∈ closedBall (c 0) 1 ∪ closedBall (c 1) 1 →
      x.snd ∈ closedBall (c 0) 1 ∪ closedBall (c 1) 1 →
      (∑ i : Fin 2, ∑ j : Fin 2, K i j x) = F x)
    (u v : SourceTestSpace hμ (ball (c 0) 1 ∪ ball (c 1) 1)) :
    inner ℝ (u : SourceHilbert hμ (ball (c 0) 1 ∪ ball (c 1) 1))
      (jointFourFieldKernelOperator hμ (ball (c 0) 1 ∪ ball (c 1) 1) K
        (v : SourceHilbert hμ (ball (c 0) 1 ∪ ball (c 1) 1))) =
      (∫ x : JointKernelSpace, (u.1.1.1 x.fst : ℂ) * (v.1.1.1 x.snd : ℂ) * F x).re := by
  have hu : Function.support u.1.1.1 ⊆ closedBall (c 0) 1 ∪ closedBall (c 1) 1 :=
    ((subset_tsupport _).trans u.2.1).trans
      (union_subset_union ball_subset_closedBall ball_subset_closedBall)
  have hv : Function.support v.1.1.1 ⊆ closedBall (c 0) 1 ∪ closedBall (c 1) 1 :=
    ((subset_tsupport _).trans v.2.1).trans
      (union_subset_union ball_subset_closedBall ball_subset_closedBall)
  rw [(jointKernel_four_integrals c K F hF u.1.1 v.1.1 hu hv).2]
  simp only [jointFourFieldKernelOperator, sum_apply, inner_sum,
    jointFieldKernelOperator_pairing, Complex.re_sum]

theorem jointFourMomentumKernelOperator_pairing {μ : ℝ} (hμ : 0 < μ)
    (c : Fin 2 → EuclideanSpace ℝ (Fin 3))
    (K : Fin 2 → Fin 2 → SchwartzMap JointKernelSpace ℂ) (F : JointKernelSpace → ℂ)
    (hF : ∀ x, x.fst ∈ closedBall (c 0) 1 ∪ closedBall (c 1) 1 →
      x.snd ∈ closedBall (c 0) 1 ∪ closedBall (c 1) 1 →
      (∑ i : Fin 2, ∑ j : Fin 2, K i j x) = F x)
    (u v : SourceTestSpace hμ (ball (c 0) 1 ∪ ball (c 1) 1)) :
    inner ℝ (u : SourceHilbert hμ (ball (c 0) 1 ∪ ball (c 1) 1))
      (jointFourMomentumKernelOperator hμ (c 0) (c 1) K
        (v : SourceHilbert hμ (ball (c 0) 1 ∪ ball (c 1) 1))) =
      (∫ x : JointKernelSpace, (u.1.2.1 x.fst : ℂ) * (v.1.2.1 x.snd : ℂ) * F x).re := by
  have hu : Function.support u.1.2.1 ⊆ closedBall (c 0) 1 ∪ closedBall (c 1) 1 :=
    ((subset_tsupport _).trans u.2.2).trans
      (union_subset_union ball_subset_closedBall ball_subset_closedBall)
  have hv : Function.support v.1.2.1 ⊆ closedBall (c 0) 1 ∪ closedBall (c 1) 1 :=
    ((subset_tsupport _).trans v.2.2).trans
      (union_subset_union ball_subset_closedBall ball_subset_closedBall)
  rw [(jointKernel_four_integrals c K F hF u.1.2 v.1.2 hu hv).2]
  simp only [jointFourMomentumKernelOperator, sum_apply, inner_sum,
    jointMomentumKernelOperator_pairing, Complex.re_sum]

/-- Actual local kernels suffice to construct a bounded operator for the
original field kernel in the total-source completion. -/
theorem exists_jointLocalFieldKernelOperator {μ M : ℝ} (hμ : 0 < μ) (hM : 0 ≤ M)
    (c : Fin 2 → EuclideanSpace ℝ (Fin 3)) (hc : 5 ≤ dist (c 0) (c 1))
    (H : Fin 2 → Fin 2 → JointKernelSpace → ℂ)
    (O : Fin 2 → Fin 2 → Set JointKernelSpace) (hO : ∀ i j, IsOpen (O i j))
    (hbox : ∀ i j, jointKernelBox (c i) (c j) 2 ⊆ O i j)
    (hH : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (H i j) (O i j))
    (hbound : ∀ i j n, n ≤ 2 → ∀ x ∈ jointKernelBox (c i) (c j) 2,
      ‖iteratedFDeriv ℝ n (H i j) x‖ ≤ M)
    (F : JointKernelSpace → ℂ)
    (hF : ∀ i j x, x.fst ∈ closedBall (c i) 1 → x.snd ∈ closedBall (c j) 1 → H i j x = F x) :
    ∃ A : SourceHilbert hμ (ball (c 0) 1 ∪ ball (c 1) 1) →L[ℝ]
        SourceHilbert hμ (ball (c 0) 1 ∪ ball (c 1) 1),
      ‖A‖ ≤ (4 * jointSmoothKernelUniversalConstant) * max 1 μ * M ∧
      ∀ u v : SourceTestSpace hμ (ball (c 0) 1 ∪ ball (c 1) 1),
        inner ℝ (u : SourceHilbert hμ (ball (c 0) 1 ∪ ball (c 1) 1))
          (A (v : SourceHilbert hμ (ball (c 0) 1 ∪ ball (c 1) 1))) =
            (∫ x : JointKernelSpace, (u.1.1.1 x.fst : ℂ) * (v.1.1.1 x.snd : ℂ) * F x).re := by
  let K := fun i j => cutOffJointLocalKernel (c i) (c j) (H i j) (O i j)
    (hO i j) (hbox i j) (hH i j)
  refine ⟨jointFourFieldKernelOperator hμ _ K,
    (jointLocalKernel_four_operator_bounds hμ hM c H O hO hbox hH hbound).1, ?_⟩
  intro u v
  exact jointFourFieldKernelOperator_pairing hμ c K F
    (jointLocalKernel_four_patches_eq c hc H O hO hbox hH F hF) u v

/-- The corresponding momentum operator has a mass-independent norm bound. -/
theorem exists_jointLocalMomentumKernelOperator {μ M : ℝ} (hμ : 0 < μ) (hM : 0 ≤ M)
    (c : Fin 2 → EuclideanSpace ℝ (Fin 3)) (hc : 5 ≤ dist (c 0) (c 1))
    (H : Fin 2 → Fin 2 → JointKernelSpace → ℂ)
    (O : Fin 2 → Fin 2 → Set JointKernelSpace) (hO : ∀ i j, IsOpen (O i j))
    (hbox : ∀ i j, jointKernelBox (c i) (c j) 2 ⊆ O i j)
    (hH : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (H i j) (O i j))
    (hbound : ∀ i j n, n ≤ 2 → ∀ x ∈ jointKernelBox (c i) (c j) 2,
      ‖iteratedFDeriv ℝ n (H i j) x‖ ≤ M)
    (F : JointKernelSpace → ℂ)
    (hF : ∀ i j x, x.fst ∈ closedBall (c i) 1 → x.snd ∈ closedBall (c j) 1 → H i j x = F x) :
    ∃ A : SourceHilbert hμ (ball (c 0) 1 ∪ ball (c 1) 1) →L[ℝ]
        SourceHilbert hμ (ball (c 0) 1 ∪ ball (c 1) 1),
      ‖A‖ ≤ (4 * jointSmoothKernelUniversalConstant) * M ∧
      ∀ u v : SourceTestSpace hμ (ball (c 0) 1 ∪ ball (c 1) 1),
        inner ℝ (u : SourceHilbert hμ (ball (c 0) 1 ∪ ball (c 1) 1))
          (A (v : SourceHilbert hμ (ball (c 0) 1 ∪ ball (c 1) 1))) =
            (∫ x : JointKernelSpace, (u.1.2.1 x.fst : ℂ) * (v.1.2.1 x.snd : ℂ) * F x).re := by
  let K := fun i j => cutOffJointLocalKernel (c i) (c j) (H i j) (O i j)
    (hO i j) (hbox i j) (hH i j)
  refine ⟨jointFourMomentumKernelOperator hμ (c 0) (c 1) K,
    (jointLocalKernel_four_operator_bounds hμ hM c H O hO hbox hH hbound).2, ?_⟩
  intro u v
  exact jointFourMomentumKernelOperator_pairing hμ c K F
    (jointLocalKernel_four_patches_eq c hc H O hO hbox hH F hF) u v

end VacuumBellSeparation
