/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelFourPatches
public import LeanPool.VacuumBellSeparation.Gaussian.CompletionOperatorDetermination

/-! # Kernel subtraction on the original source completion -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open MeasureTheory
open scoped SchwartzMap InnerProductSpace

theorem jointKernelTestPair_sub_kernel (K L : SchwartzMap JointKernelSpace ℂ)
    (f g : SpatialTestFunction) :
    jointKernelTestPair (K - L) f g = jointKernelTestPair K f g - jointKernelTestPair L f g := by
  unfold jointKernelTestPair
  change (∫ x : JointKernelSpace, (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * (K x - L x)).re = _
  simp only [mul_sub]
  rw [integral_sub (integrable_jointKernelTest K f g) (integrable_jointKernelTest L f g),
    Complex.sub_re]

theorem jointFieldKernelOperator_sub {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (K L : SchwartzMap JointKernelSpace ℂ) :
    jointFieldKernelOperator hμ U (K - L) =
      jointFieldKernelOperator hμ U K - jointFieldKernelOperator hμ U L := by
  apply Gaussian.completionOperator_eq_of_test_pairings
  intro u v
  simp only [sub_apply, inner_sub_right, jointFieldKernelOperator_pairing]
  exact jointKernelTestPair_sub_kernel K L u.1.1 v.1.1

theorem jointMomentumKernelOperator_sub {μ : ℝ} (hμ : 0 < μ)
    (p q : EuclideanSpace ℝ (Fin 3)) (K L : SchwartzMap JointKernelSpace ℂ) :
    jointMomentumKernelOperator hμ p q (K - L) =
      jointMomentumKernelOperator hμ p q K - jointMomentumKernelOperator hμ p q L := by
  apply Gaussian.completionOperator_eq_of_test_pairings
  intro u v
  simp only [sub_apply, inner_sub_right, jointMomentumKernelOperator_pairing]
  exact jointKernelTestPair_sub_kernel K L u.1.2 v.1.2

theorem jointFourFieldKernelOperator_sub {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3)))
    (K L : Fin 2 → Fin 2 → SchwartzMap JointKernelSpace ℂ) :
    jointFourFieldKernelOperator hμ U (fun i j => K i j - L i j) =
      jointFourFieldKernelOperator hμ U K - jointFourFieldKernelOperator hμ U L := by
  simp only [jointFourFieldKernelOperator, jointFieldKernelOperator_sub, Finset.sum_sub_distrib]

theorem jointFourMomentumKernelOperator_sub {μ : ℝ} (hμ : 0 < μ)
    (p q : EuclideanSpace ℝ (Fin 3))
    (K L : Fin 2 → Fin 2 → SchwartzMap JointKernelSpace ℂ) :
    jointFourMomentumKernelOperator hμ p q (fun i j => K i j - L i j) =
      jointFourMomentumKernelOperator hμ p q K - jointFourMomentumKernelOperator hμ p q L := by
  simp only [jointFourMomentumKernelOperator, jointMomentumKernelOperator_sub,
    Finset.sum_sub_distrib]

end VacuumBellSeparation
