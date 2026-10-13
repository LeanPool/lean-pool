/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.QuantitativeCutoff
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.AxisCube

/-!
# NestedCubeCutoff

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Smooth cutoffs between nested concentric cubes
-/

noncomputable section

namespace HCPolySupport

open Set

variable {d : ℕ}

/-- A closed concentric cube of smaller relative radius lies in the open
concentric cube of any strictly larger relative radius. -/
theorem scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt
    (Q : TriadicCube d) {rho sigma : ℝ} (hrhoSigma : rho < sigma) :
    scaledClosedCubeSet Q rho ⊆ scaledOpenCubeSet Q sigma := by
  intro x hx i
  exact (hx i).trans_lt
    (mul_lt_mul_of_pos_right hrhoSigma (cubeRadius_pos Q))

/-- The canonical cutoff's topological support lies in every strictly larger
open concentric cube. -/
theorem QuantitativeCubeCutoff.canonicalFun_tsupport_subset_scaledOpenCubeSet
    (Q : TriadicCube d) {rhoInner rhoTransition rhoOuter : ℝ}
    (hrhoInner : 0 < rhoInner) (hinnerTransition : rhoInner < rhoTransition)
    (htransitionOuter : rhoTransition < rhoOuter) :
    tsupport (QuantitativeCubeCutoff.canonicalFun Q rhoInner rhoTransition) ⊆
      scaledOpenCubeSet Q rhoOuter :=
  (QuantitativeCubeCutoff.canonicalFun_tsupport_subset_scaledClosedCubeSet
      hrhoInner hinnerTransition).trans
    (scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt Q htransitionOuter)

/-- The squared coordinate-gradient of the canonical cutoff is controlled by
its explicit Fréchet-derivative bound. -/
theorem QuantitativeCubeCutoff.vecNormSq_canonicalFun_gradient_le
    (Q : TriadicCube d) {rhoInner rhoTransition : ℝ}
    (hrhoInner : 0 < rhoInner) (hinnerTransition : rhoInner < rhoTransition)
    (x : Vec d) :
    vecNormSq (fun i =>
        (fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q rhoInner rhoTransition) x)
          (basisVec i)) ≤
      (d : ℝ) *
        ((d : ℝ) * smoothTransitionProfile.derivBound *
          (2 / ((rhoTransition - rhoInner) * cubeRadius Q))) ^ 2 := by
  let C : ℝ :=
    (d : ℝ) * smoothTransitionProfile.derivBound *
      (2 / ((rhoTransition - rhoInner) * cubeRadius Q))
  have hgrad :
      ‖fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q rhoInner rhoTransition) x‖ ≤ C :=
    QuantitativeCubeCutoff.canonicalFun_gradient_bound Q hrhoInner hinnerTransition x
  have hC : 0 ≤ C := (norm_nonneg _).trans hgrad
  have hcoord : ∀ i : Fin d,
      ((fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q rhoInner rhoTransition) x)
          (basisVec i)) ^ 2 ≤ C ^ 2 := by
    intro i
    have hbasis : ‖basisVec (d := d) i‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
      intro j
      rw [basisVec_apply]
      by_cases hji : j = i <;> simp [hji]
    have happ :
        ‖(fderiv ℝ
            (QuantitativeCubeCutoff.canonicalFun Q rhoInner rhoTransition) x)
            (basisVec i)‖ ≤
          ‖fderiv ℝ
            (QuantitativeCubeCutoff.canonicalFun Q rhoInner rhoTransition) x‖ := by
      calc
        _ ≤ ‖fderiv ℝ
              (QuantitativeCubeCutoff.canonicalFun Q rhoInner rhoTransition) x‖ *
              ‖basisVec i‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ _ := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hbasis (norm_nonneg _)
    have habs :
        |(fderiv ℝ
            (QuantitativeCubeCutoff.canonicalFun Q rhoInner rhoTransition) x)
            (basisVec i)| ≤ C := by
      rw [← Real.norm_eq_abs]
      exact happ.trans hgrad
    have hsq := (sq_le_sq₀ (abs_nonneg _) hC).2 habs
    rwa [sq_abs] at hsq
  calc
    vecNormSq (fun i =>
        (fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q rhoInner rhoTransition) x)
          (basisVec i)) =
        ∑ i : Fin d,
          ((fderiv ℝ
              (QuantitativeCubeCutoff.canonicalFun Q rhoInner rhoTransition) x)
              (basisVec i)) ^ 2 := by
      simp only [vecNormSq, vecDot, pow_two]
    _ ≤ ∑ _i : Fin d, C ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
    _ = (d : ℝ) * C ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    _ = _ := rfl

end HCPolySupport
