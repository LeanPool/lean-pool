/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.GradientScaleReadout
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SandwichNondegeneracy
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CubeMoments
public import LeanPool.HighContrastHomogenization.Support.Sobolev.MatchedPair.ScaledPoincare
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCalderonZygmund.StoppingCubeGeometry
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.H1Casts
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.EnergyIntegrand

/-!
# BallPoincare

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Poincare readout on local sup-balls
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport
open Algsuperdiff.Section4.Support
open HCPolySupport.CubeCalderonZygmund
open HCPolySupport.Book.Ch03
open Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

private theorem normalizedL2On_gradCoord_le_vectorNormalizedL2On
    {W : Set (Vec d)} (hWm : MeasurableSet W)
    {u : H1Function W} (i : Fin d) :
    normalizedL2On W (fun x => u.grad x i) ≤
      vectorNormalizedL2On W u.grad := by
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

/-- Normalized mean-zero Poincare on an arbitrary positive axis cube, with
the gradient already aggregated in the Euclidean vector carrier. -/
theorem normalizedL2On_axisCube_sub_average_le_vectorGradient
    (z : Vec d) {L : ℝ} (hL : 0 < L)
    (u : H1Function (axisCube z L)) :
    normalizedL2On (axisCube z L)
        (fun x => u.toFun x - volumeAverage (axisCube z L) u.toFun) ≤
      unitMeanZeroPoincareConst d * L * (d : ℝ) *
        vectorNormalizedL2On (axisCube z L) u.grad := by
  let W : Set (Vec d) := axisCube z L
  have hraw := scaled_meanZero_poincare z hL u
  have hWpos : 0 < (volume W).toReal := by
    dsimp only [W]
    rw [volume_axisCube_toReal z hL.le]
    exact pow_pos hL d
  have hWtop : volume W ≠ ⊤ := by
    exact (ENNReal.toReal_ne_zero.mp hWpos.ne').2
  let : IsFiniteMeasure (volume.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr hWtop
  have hleftMem : MemLp
      (fun x => u.toFun x - volumeAverage W u.toFun) 2
      (volume.restrict W) := u.memL2.sub (memLp_const _)
  have hgradMem : ∀ i : Fin d,
      MemLp (fun x => u.grad x i) 2 (volume.restrict W) :=
    fun i => u.gradMemL2 i
  have hsqrt : 0 ≤ Real.sqrt ((volume W).toReal) := Real.sqrt_nonneg _
  have hdiv := div_le_div_of_nonneg_right hraw hsqrt
  have hleftEq := normalizedL2On_eq_toReal_eLpNorm_div hleftMem
  have hcoord : ∀ i : Fin d,
      normalizedL2On W (fun x => u.grad x i) =
        (eLpNorm (fun x => u.grad x i) 2 (volume.restrict W)).toReal /
          Real.sqrt ((volume W).toReal) :=
    fun i => normalizedL2On_eq_toReal_eLpNorm_div (hgradMem i)
  have hnormalized :
      normalizedL2On W
          (fun x => u.toFun x - volumeAverage W u.toFun) ≤
        unitMeanZeroPoincareConst d * L *
          ∑ i : Fin d, normalizedL2On W (fun x => u.grad x i) := by
    rw [hleftEq]
    refine hdiv.trans_eq ?_
    calc
      (unitMeanZeroPoincareConst d * L *
            ∑ i : Fin d,
              (eLpNorm (fun x => u.grad x i) 2
                (volume.restrict W)).toReal) /
          Real.sqrt ((volume W).toReal) =
        unitMeanZeroPoincareConst d * L *
          ∑ i : Fin d,
            ((eLpNorm (fun x => u.grad x i) 2
              (volume.restrict W)).toReal /
              Real.sqrt ((volume W).toReal)) := by
        rw [mul_div_assoc, Finset.sum_div]
      _ = unitMeanZeroPoincareConst d * L *
          ∑ i : Fin d, normalizedL2On W (fun x => u.grad x i) := by
        congr 2
        funext i
        exact (hcoord i).symm
  have hcoordLe :
      ∑ i : Fin d, normalizedL2On W (fun x => u.grad x i) ≤
        (d : ℝ) * vectorNormalizedL2On W u.grad := by
    calc
      ∑ i : Fin d, normalizedL2On W (fun x => u.grad x i) ≤
          ∑ _i : Fin d, vectorNormalizedL2On W u.grad :=
        Finset.sum_le_sum fun i _ =>
          normalizedL2On_gradCoord_le_vectorNormalizedL2On
            (measurableSet_axisCube z L) i
      _ = (d : ℝ) * vectorNormalizedL2On W u.grad := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  exact hnormalized.trans (by
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left hcoordLe
        (mul_nonneg (unitMeanZeroPoincareConst_nonneg d) hL.le)))

/-- The same Poincare row on the open sup-ball realization. -/
theorem normalizedL2On_metricBall_sub_average_le_vectorGradient
    (x : Vec d) {r : ℝ} (hr : 0 < r)
    (u : H1Function (Metric.ball x r)) :
    normalizedL2On (Metric.ball x r)
        (fun y => u.toFun y - volumeAverage (Metric.ball x r) u.toFun) ≤
      unitMeanZeroPoincareConst d * (2 * r) * (d : ℝ) *
        vectorNormalizedL2On (Metric.ball x r) u.grad := by
  have hset := axisCube_stoppingAxisCubeCorner_eq_ball
    (d := d) x (S := 1) (r := r) (by norm_num) hr
  have hset' :
      axisCube (stoppingAxisCubeCorner x 1 r) (stoppingAxisCubeSide 1 r) =
        Metric.ball x r := by
    simpa only [one_mul] using hset
  have hset2 :
      axisCube (stoppingAxisCubeCorner x 1 r) (2 * r) = Metric.ball x r := by
    simpa only [stoppingAxisCubeSide, mul_one] using hset'
  have hraw := normalizedL2On_axisCube_sub_average_le_vectorGradient
    (stoppingAxisCubeCorner x 1 r)
    (show 0 < stoppingAxisCubeSide 1 r by
      simp only [stoppingAxisCubeSide]
      positivity)
    (Book.Ch03.castH1Domain hset'.symm u)
  rw [castH1Domain_toFun, castH1Domain_grad] at hraw
  simpa only [hset', hset2, stoppingAxisCubeSide, mul_one] using! hraw

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
