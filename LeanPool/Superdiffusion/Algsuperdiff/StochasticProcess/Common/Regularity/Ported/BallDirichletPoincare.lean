/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.ZerothOrderCarrier
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.NormalizedEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.UnitCubeDirichletPoincare
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderAeLimit
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CubeMoments
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCalderonZygmund.StoppingCubeGeometry
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ZeroExtensionGraph

/-!
# BallDirichletPoincare

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Explicit Dirichlet Poincaré inequality on Euclidean balls

The ball datum is extended by zero to the equal-radius sup ball, realized as
an axis cube.  This is the ball-specific bridge required by the zeroth-order
energy comparison.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.Schauder
open HCPolySupport.CubeCalderonZygmund

noncomputable section

variable {d : ℕ}

private theorem normalizedL2On_gradCoord_le_vectorNormalizedL2On'
    {W : Set (Vec d)} (hWm : MeasurableSet W)
    {u : H1Function W} (i : Fin d) :
    normalizedL2On W (fun x => u.grad x i) ≤ vectorNormalizedL2On W u.grad := by
  unfold normalizedL2On vectorNormalizedL2On volumeAverage
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply setIntegral_mono_on
  · exact (u.gradMemL2 i).integrable_sq
  · simpa only [euclideanNorm_sq] using
      (integrableOn_vecNormSq_of_memVectorL2 u.grad_memVectorL2)
  · exact hWm
  · intro x _
    simpa only [euclideanNorm_sq] using
      (WeakPoissonEquationOn.coord_sq_le_vecNormSq (u.grad x) i)

/-- Normalized Dirichlet Poincaré on a Euclidean ball, with an explicit
dimension-only constant inherited from the unit axis cube. -/
theorem normalizedL2On_euclideanBall_le_vectorGradient [NeZero d]
    (z : Vec d) {r : ℝ} (hr : 0 < r)
    (rho : H10Function (euclideanBall z r)) :
    normalizedL2On (euclideanBall z r) rho.toH1Function.toFun ≤
      unitCubeDirichletPoincareExplicit d * (2 * r) * (d : ℝ) *
        vectorNormalizedL2On (euclideanBall z r) rho.toH1Function.grad := by
  let W : Set (Vec d) := euclideanBall z r
  let c : Vec d := stoppingAxisCubeCorner z 1 r
  let Q : Set (Vec d) := axisCube c (2 * r)
  have hball : axisCube (stoppingAxisCubeCorner z 1 r) (2 * r) = Metric.ball z r := by
    simpa only [stoppingAxisCubeSide, one_mul, mul_one] using
      (axisCube_stoppingAxisCubeCorner_eq_ball (d := d) z (S := 1) (r := r)
        (by norm_num) hr)
  have hWQ : W ⊆ Q := by
    dsimp only [W, Q, c]
    rw [hball]
    exact euclideanBall_subset_ball z hr
  let rhoQ : H10Function Q :=
    rho.extendByZeroToOpenSuperset (isOpen_euclideanBall z r).measurableSet
      (isOpen_axisCube c (2 * r)) hWQ
  have hraw := scaled_dirichlet_poincare_explicit c (by positivity : 0 < 2 * r) rhoQ
  have hval : eLpNorm rhoQ.toH1Function.toFun 2 (volume.restrict Q) =
      eLpNorm rho.toH1Function.toFun 2 (volume.restrict W) := by
    change eLpNorm (Set.indicator W rho.toH1Function.toFun) 2 (volume.restrict Q) = _
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (isOpen_euclideanBall z r).measurableSet,
      Measure.restrict_restrict (isOpen_euclideanBall z r).measurableSet,
      Set.inter_eq_left.mpr hWQ]
  have hgrad : ∀ i : Fin d,
      eLpNorm (fun x => rhoQ.toH1Function.grad x i) 2 (volume.restrict Q) =
        eLpNorm (fun x => rho.toH1Function.grad x i) 2 (volume.restrict W) := by
    intro i
    change eLpNorm (fun x => Set.indicator W rho.toH1Function.grad x i) 2
        (volume.restrict Q) = _
    rw [show (fun x => Set.indicator W rho.toH1Function.grad x i) =
        Set.indicator W (fun x => rho.toH1Function.grad x i) by
          funext x
          by_cases hx : x ∈ W <;> simp [hx],
      eLpNorm_indicator_eq_eLpNorm_restrict (isOpen_euclideanBall z r).measurableSet,
      Measure.restrict_restrict (isOpen_euclideanBall z r).measurableSet,
      Set.inter_eq_left.mpr hWQ]
  rw [hval, show (∑ i : Fin d, (eLpNorm (fun x => rhoQ.toH1Function.grad x i) 2
      (volume.restrict Q)).toReal) =
      ∑ i : Fin d, (eLpNorm (fun x => rho.toH1Function.grad x i) 2
        (volume.restrict W)).toReal from
      Finset.sum_congr rfl fun i _ => by rw [hgrad i]] at hraw
  have hWpos : 0 < (volume W).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg
    (Ne.symm (HCPolySupport.Book.Ch01.volume_euclideanBall_toReal_ne_zero z hr))
  have hleft := normalizedL2On_eq_toReal_eLpNorm_div rho.toH1Function.memL2
  have hcoord : ∀ i : Fin d,
      normalizedL2On W (fun x => rho.toH1Function.grad x i) =
        (eLpNorm (fun x => rho.toH1Function.grad x i) 2
          (volume.restrict W)).toReal / Real.sqrt ((volume W).toReal) :=
    fun i => normalizedL2On_eq_toReal_eLpNorm_div (rho.toH1Function.gradMemL2 i)
  have hdiv := div_le_div_of_nonneg_right hraw
    (Real.sqrt_nonneg ((volume W).toReal))
  calc
    normalizedL2On W rho.toH1Function.toFun ≤
        unitCubeDirichletPoincareExplicit d * (2 * r) *
          ∑ i : Fin d, normalizedL2On W (fun x => rho.toH1Function.grad x i) := by
      rw [hleft]
      exact hdiv.trans_eq (by
        rw [mul_div_assoc, Finset.sum_div]
        congr 2
        funext i
        exact (hcoord i).symm)
    _ ≤ unitCubeDirichletPoincareExplicit d * (2 * r) *
        ((d : ℝ) * vectorNormalizedL2On W rho.toH1Function.grad) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (unitCubeDirichletPoincareExplicit_nonneg d) (by positivity))
      calc
        ∑ i : Fin d, normalizedL2On W (fun x => rho.toH1Function.grad x i) ≤
            ∑ _i : Fin d, vectorNormalizedL2On W rho.toH1Function.grad :=
          Finset.sum_le_sum fun i _ =>
            normalizedL2On_gradCoord_le_vectorNormalizedL2On'
              (isOpen_euclideanBall z r).measurableSet i
        _ = (d : ℝ) * vectorNormalizedL2On W rho.toH1Function.grad := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = _ := by ring

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
