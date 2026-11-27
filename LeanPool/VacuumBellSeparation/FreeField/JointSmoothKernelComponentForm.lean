/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelOriginalForm

/-! # Original test pairings supported in a single component -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open MeasureTheory Set Metric
open scoped SchwartzMap InnerProductSpace

theorem jointUnitCutoffTest_eq_ite (c : Fin 2 → EuclideanSpace ℝ (Fin 3))
    (hc : 5 ≤ dist (c 0) (c 1)) (a i : Fin 2) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ closedBall (c a) 1) :
    (jointUnitCutoffTest (c i)).1 x = if i = a then 1 else 0 := by
  by_cases hia : i = a
  · subst i
    rw [ite_eq_left rfl]
    exact jointUnitCutoffTest_eq_one _ _ hx
  · rw [ite_eq_right hia]
    have hd : 5 ≤ dist (c a) (c i) := by
      fin_cases a <;> fin_cases i
      · exact (hia rfl).elim
      · exact hc
      · rw [dist_comm]
        exact hc
      · exact (hia rfl).elim
    exact jointUnitCutoffTest_zero_other _ _ _ hd hx

theorem jointSmoothCutoff_four_sum_on_component (c : Fin 2 → EuclideanSpace ℝ (Fin 3))
    (hc : 5 ≤ dist (c 0) (c 1)) (H : Fin 2 → Fin 2 → JointKernelSpace → ℂ)
    (a b : Fin 2) (x : JointKernelSpace)
    (hx : x.fst ∈ closedBall (c a) 1) (hy : x.snd ∈ closedBall (c b) 1) :
    (∑ i : Fin 2, ∑ j : Fin 2, jointSmoothCutoff (c i) (c j) x * H i j x) = H a b x := by
  classical
  simp only [jointSmoothCutoff_apply, jointUnitCutoffTest_eq_ite c hc a _ _ hx,
    jointUnitCutoffTest_eq_ite c hc b _ _ hy]
  fin_cases a <;> fin_cases b <;> norm_num [Fin.sum_univ_two]

theorem jointKernel_four_integrals_on_component
    (p q : EuclideanSpace ℝ (Fin 3))
    (K : Fin 2 → Fin 2 → SchwartzMap JointKernelSpace ℂ) (H : JointKernelSpace → ℂ)
    (hK : ∀ x, x.fst ∈ closedBall p 1 → x.snd ∈ closedBall q 1 →
      (∑ i : Fin 2, ∑ j : Fin 2, K i j x) = H x)
    (f g : SpatialTestFunction)
    (hf : Function.support f.1 ⊆ closedBall p 1) (hg : Function.support g.1 ⊆ closedBall q 1) :
    (∫ x : JointKernelSpace, (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * H x) =
      ∑ i : Fin 2, ∑ j : Fin 2,
        ∫ x : JointKernelSpace, (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * K i j x := by
  have he (x : JointKernelSpace) :
      (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * H x =
        ∑ i : Fin 2, ∑ j : Fin 2, (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * K i j x := by
    by_cases hx : f.1 x.fst = 0
    · simp only [hx, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero]
    by_cases hy : g.1 x.snd = 0
    · simp only [hy, Complex.ofReal_zero, mul_zero, zero_mul, Finset.sum_const_zero]
    rw [← hK x (hf hx) (hg hy)]
    simp only [Finset.mul_sum]
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => integrable_jointKernelTest (K i j) f g))]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_finsetSum Finset.univ (fun j _ => integrable_jointKernelTest (K i j) f g)

theorem jointFourFieldKernelOperator_pairing_component {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (p q : EuclideanSpace ℝ (Fin 3))
    (K : Fin 2 → Fin 2 → SchwartzMap JointKernelSpace ℂ) (H : JointKernelSpace → ℂ)
    (hK : ∀ x, x.fst ∈ closedBall p 1 → x.snd ∈ closedBall q 1 →
      (∑ i : Fin 2, ∑ j : Fin 2, K i j x) = H x)
    (u v : SourceTestSpace hμ U)
    (hu : Function.support u.1.1.1 ⊆ closedBall p 1)
    (hv : Function.support v.1.1.1 ⊆ closedBall q 1) :
    inner ℝ (u : SourceHilbert hμ U)
      (jointFourFieldKernelOperator hμ U K (v : SourceHilbert hμ U)) =
        (∫ x : JointKernelSpace, (u.1.1.1 x.fst : ℂ) * (v.1.1.1 x.snd : ℂ) * H x).re := by
  rw [jointKernel_four_integrals_on_component p q K H hK u.1.1 v.1.1 hu hv]
  simp only [jointFourFieldKernelOperator, sum_apply, inner_sum,
    jointFieldKernelOperator_pairing, Complex.re_sum]

theorem jointFourMomentumKernelOperator_pairing_component {μ : ℝ} (hμ : 0 < μ)
    (c₀ c₁ p q : EuclideanSpace ℝ (Fin 3))
    (K : Fin 2 → Fin 2 → SchwartzMap JointKernelSpace ℂ) (H : JointKernelSpace → ℂ)
    (hK : ∀ x, x.fst ∈ closedBall p 1 → x.snd ∈ closedBall q 1 →
      (∑ i : Fin 2, ∑ j : Fin 2, K i j x) = H x)
    (u v : SourceTestSpace hμ (ball c₀ 1 ∪ ball c₁ 1))
    (hu : Function.support u.1.2.1 ⊆ closedBall p 1)
    (hv : Function.support v.1.2.1 ⊆ closedBall q 1) :
    inner ℝ (u : SourceHilbert hμ (ball c₀ 1 ∪ ball c₁ 1))
      (jointFourMomentumKernelOperator hμ c₀ c₁ K
        (v : SourceHilbert hμ (ball c₀ 1 ∪ ball c₁ 1))) =
        (∫ x : JointKernelSpace, (u.1.2.1 x.fst : ℂ) * (v.1.2.1 x.snd : ℂ) * H x).re := by
  rw [jointKernel_four_integrals_on_component p q K H hK u.1.2 v.1.2 hu hv]
  simp only [jointFourMomentumKernelOperator, sum_apply, inner_sum,
    jointMomentumKernelOperator_pairing, Complex.re_sum]

end VacuumBellSeparation
