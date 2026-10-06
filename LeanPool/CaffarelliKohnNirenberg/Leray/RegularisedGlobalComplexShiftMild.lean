/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedGlobalRealRestart
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedGlobalComplexShiftPath
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTensorPhysicalRealification
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedHeatStokesRealification

/-!
# Complex mild equation after a global restart

Every nonnegative shift of the global real mild curve satisfies the
corresponding translated complex L² Volterra equation.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The shifted global mild curve solves the complex linear equation
with its own L² path as prescribed tensor coefficient. -/
theorem regularisedGlobalComplexShiftPath_linearMild
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b₀ : RealVectorL2) (hbJ : RegularizedMildJData b₀)
    (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T)
    (t : RegularizedMildTimeInterval T) :
    let g := regularisedGlobalComplexShiftPath ρ ε hε b₀ hbJ a T
    g t = heatSemigroup t.1 t.2.1
        (complexifyVectorL2
          (regularizedGlobalMildCurve ρ ε hε b₀ hbJ a)) -
      ∫ τ in (0 : ℝ)..T,
        if h : 0 < τ ∧ τ < t.1 then
          stokesL2Operator h.1
            (regularisedTensorPhysicalMap ρ ε hε
              (g (regularizedMildTimeClamp T hT (t.1 - τ)))
              (g (regularizedMildTimeClamp T hT (t.1 - τ))))
        else 0 := by
  dsimp only
  let v := regularizedGlobalMildCurve_shiftPath ρ ε hε b₀ hbJ a T
  let F := regularizedMildClampedTensorTrajectory ρ ε hε T hT v
  have hvbound : ∀ q, ‖v q‖ ≤ ‖b₀‖ := by
    intro q
    exact regularizedGlobalMildCurve_norm_le_initial
      ρ ε hε b₀ hbJ (a + q.1) (add_nonneg ha q.2.1)
  have hFcont : Continuous F :=
    regularizedMildClampedTensorTrajectory_continuous ρ ε hε T hT v
  have hFbound : ∀ s, ‖F s‖ ≤
      regularizedMildMollifierConstant ρ ε * ‖b₀‖ ^ 2 :=
    regularizedMildClampedTensorTrajectory_norm_le
      ρ ε hε T hT v ‖b₀‖ (norm_nonneg b₀) hvbound
  have hC : 0 ≤ regularizedMildMollifierConstant ρ ε * ‖b₀‖ ^ 2 :=
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  have hInt : IntervalIntegrable
      (mildShiftedStokesIntegrand F t.1) volume 0 T :=
    mildShiftedStokesIntegrand_intervalIntegrable F hFcont _ hFbound hC T t.1 hT
  have hTrajectory : IsRegularizedMildTrajectory ρ ε hε
      (regularizedGlobalMildCurve ρ ε hε b₀ hbJ a) T v :=
    regularizedGlobalMildCurve_shift_isTrajectory
      ρ ε hε b₀ hbJ a T ha hT
  have hlocal : v t = regularizedMildLocalMap ρ ε hε
      (regularizedGlobalMildCurve ρ ε hε b₀ hbJ a) T hT v t := by
    exact (hTrajectory t).trans
      (regularizedMildLocalMap_eq_rightHandSide ρ ε hε
        (regularizedGlobalMildCurve ρ ε hε b₀ hbJ a) T hT v t).symm
  rw [regularizedMildLocalMap_eq_shifted] at hlocal
  change complexifyVectorL2 (v t) = _
  rw [hlocal, map_sub, ← heatSemigroup_complexify_real]
  have hphysicalIntegral :
      complexifyVectorL2
        (∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand F t.1 τ) =
      ∫ τ in (0 : ℝ)..T,
        if h : 0 < τ ∧ τ < t.1 then
          stokesL2Operator h.1
            (regularisedTensorPhysicalMap ρ ε hε
              (regularisedGlobalComplexShiftPath ρ ε hε b₀ hbJ a T
                (regularizedMildTimeClamp T hT (t.1 - τ)))
              (regularisedGlobalComplexShiftPath ρ ε hε b₀ hbJ a T
                (regularizedMildTimeClamp T hT (t.1 - τ))))
        else 0 := by
    calc
      complexifyVectorL2
          (∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand F t.1 τ) =
        ∫ τ in (0 : ℝ)..T,
          complexifyVectorL2 (mildShiftedStokesIntegrand F t.1 τ) :=
            (complexifyVectorL2.intervalIntegral_comp_comm hInt).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro τ _
        by_cases h : 0 < τ ∧ τ < t.1
        · simp only [mildShiftedStokesIntegrand, dite_eq_left h]
          rw [← stokesL2Operator_complexify_real]
          apply congrArg (stokesL2Operator h.1)
          change complexifyTensorL2
              (regularizedMildTensor ρ ε hε
                (v (regularizedMildTimeClamp T hT (t.1 - τ)))) = _
          rw [← regularisedTensorPhysicalMap_real_diagonal]
          rfl
        · simp [mildShiftedStokesIntegrand, h]
  rw [hphysicalIntegral]

end CKN.Leray

end
