/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.LocalizedInteriorPointwise
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Conservativity
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.LocalizedTailData

/-!
# LocalizedConservativity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Localized split-skew decay of the whole-space boundary defect

The boundary defect on the `m`th exhaustion cube is a bounded homogeneous
`H¹` solution.  The rough skew size and the smooth skew divergence are read on
the full topological support of the cutoff.  For the
cubic cutoff that support lies in the origin-centred ball of radius `3^m`.

This module carries the split datum explicitly.  It assumes no global
small-contrast or global upper-ellipticity bound.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Topology
open MarkovProcess.Semigroup
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- The explicit localized split-skew upper bound for the boundary defect.
All structural assumptions are carried by `A` and `L`; the three displayed
geometric hypotheses merely place the fixed freezing ball inside the cube and
separate it from the cutoff transition. -/
theorem abs_analyticCubeBoundaryRemainder_le_localized
    (L : WholeSpaceLocalizedSplitData A) (mu : PositiveShift) (m : ℕ)
    (x : Vec d)
    (hball : euclideanBall x (L.freezingRadius x) ⊆ wholeSpaceCube d m)
    (hinnerBall : euclideanBall x (L.freezingRadius x / 2) ⊆
      euclideanBall 0 (cubeBoundaryCutoffInnerRadius m))
    (hlayerLe : -cubeBoundaryCutoffInnerRadius m + 1 ≤
      -(euclideanNorm (x - 0) + L.freezingRadius x / 2)) :
    |1 - (mu : ℝ) *
        A.analyticCubeResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
          measurable_const (D := 1) (fun _ ↦ by norm_num) m x| ≤
      Decay.localizedInteriorDecayConstant d A.nu (mu : ℝ)
          (L.roughBound 0 ((3 : ℝ) ^ m))
          (L.smoothDivBound 0 ((3 : ℝ) ^ m)) 1
          (cubeBoundaryCutoffUniformGradientBudget (d := d))
          (volume (wholeSpaceCube d m)).toReal L.holderExponent
          ((mu : ℝ) * (min (mu : ℝ) A.nu)⁻¹ *
            (volume (wholeSpaceCube d m)).toReal)
          (L.freezingRadius x) *
        Real.exp (-(Decay.agmonRate A.nu
            (Decay.localizedInteriorUpper A.nu (mu : ℝ)
              (L.roughBound 0 ((3 : ℝ) ^ m))
              (L.smoothDivBound 0 ((3 : ℝ) ^ m))) (mu : ℝ) *
          L.holderExponent / (L.holderExponent + (d : ℝ) / 2) *
            (-(euclideanNorm (x - 0) + L.freezingRadius x / 2) -
              (-cubeBoundaryCutoffInnerRadius m + 1)))) := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  let eta := cubeBoundaryCutoff (d := d) m
  let psi := Decay.inwardPhase (0 : Vec d) 1
  let radius : ℝ := (3 : ℝ) ^ m
  let Ks := L.roughBound 0 radius
  let Kl := L.smoothDivBound 0 radius
  let Ceta := cubeBoundaryCutoffUniformGradientBudget (d := d)
  have hradius : 0 ≤ radius := (pow_pos (by norm_num) m).le
  have hKs : 0 ≤ Ks := L.roughBound_nonneg 0 radius hradius
  have hKl : 0 ≤ Kl := L.smoothDivBound_nonneg 0 radius hradius
  have hCeta : 0 ≤ Ceta := by
    dsimp only [Ceta, cubeBoundaryCutoffUniformGradientBudget]
    exact mul_nonneg (Nat.cast_nonneg d) (sq_nonneg _)
  have hetaGrad : ∀ y ∈ wholeSpaceCube d m,
      vecNormSq (fun i ↦ (fderiv ℝ eta y) (basisVec i)) ≤ Ceta := by
    intro y hy
    exact cubeBoundaryCutoff_gradSq_le_uniform (d := d) m y
  have hlayer : ∀ y ∈ wholeSpaceCube d m, fderiv ℝ eta y ≠ 0 →
      psi y ≤ -cubeBoundaryCutoffInnerRadius m + 1 := by
    intro y hyU hyderiv
    exact Decay.inwardPhase_le_of_le_euclideanNorm (z := (0 : Vec d))
      (delta := 1) (by norm_num)
      (cubeBoundaryCutoffInnerRadius_le_euclideanNorm hyderiv)
  have hvol : (volume {y ∈ wholeSpaceCube d m |
      fderiv ℝ eta y ≠ 0}).toReal ≤
      (volume (wholeSpaceCube d m)).toReal := by
    apply ENNReal.toReal_mono
    · exact hU.isBoundedDomain.isBounded.measure_lt_top.ne
    · exact measure_mono fun y hy ↦ hy.1
  have hinner : ∀ y ∈ euclideanBall x (L.freezingRadius x / 2), eta y = 1 :=
    fun y hy ↦ cubeBoundaryCutoff_eq_one (hinnerBall hy)
  have hphase : ∀ y ∈ euclideanBall x (L.freezingRadius x / 2),
      -(euclideanNorm (x - 0) + L.freezingRadius x / 2) ≤ psi y := by
    intro y hy
    exact Decay.le_inwardPhase_of_mem_euclideanBall (z := (0 : Vec d))
      (delta := 1) (by norm_num) (half_pos (L.freezingRadius_pos x)).le hy
  obtain ⟨v, hvcont, hvae, hvbound⟩ :=
    Decay.interior_abs_center_le_exp_localized hU A.hd
      L.holderExponent_mem L.delta_nonneg L.delta_le A.hnu hKs hKl
      mu.property (by norm_num) A.hameas (L.roughEllipticity m)
      L.split L.ksSkew L.klSkew L.klContDiff
      (A.cubeBoundaryRemainder_isScalarForcedWeakSolution mu m)
      (A.cubeBoundaryRemainder_abs_le_one_ae mu m)
      (contDiff_cubeBoundaryCutoff (d := d) m)
      (hasCompactSupport_cubeBoundaryCutoff (d := d) m)
      (tsupport_cubeBoundaryCutoff_subset (d := d) m)
      (tsupport_cubeBoundaryCutoff_subset_euclideanBall (d := d) m)
      hCeta hetaGrad hlayer hvol
      (Decay.contDiff_inwardPhase (z := (0 : Vec d)) (delta := 1) (by norm_num))
      (Filter.Eventually.of_forall fun y ↦
        Decay.vecNormSq_fderiv_inwardPhase_le_one
          (z := (0 : Vec d)) (delta := 1) (by norm_num) y)
      (L.roughBound_spec 0 radius hradius)
      (L.smoothDivBound_spec 0 radius hradius)
      (L.freezingRadius_pos x) hball (L.smallContrast x)
      (A.cubeBoundaryRemainder_gradient_budget mu m hball)
      hinner hphase hlayerLe
  let w : Vec d → ℝ := fun y ↦ 1 - (mu : ℝ) *
    A.analyticCubeResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
      measurable_const (D := 1) (fun _ ↦ by norm_num) m y
  have hhalf : euclideanBall x (L.freezingRadius x / 2) ⊆
      euclideanBall x (L.freezingRadius x) :=
    euclideanBall_subset_euclideanBall (half_pos (L.freezingRadius_pos x)).le
      (by linarith only [L.freezingRadius_pos x])
  have hwcont : ContinuousOn w (euclideanBall x (L.freezingRadius x / 2)) :=
    continuousOn_const.sub (continuousOn_const.mul
      ((A.continuousOn_analyticCubeResolvent mu measurable_const
        (D := 1) (fun _ ↦ by norm_num) m).mono (hhalf.trans hball)))
  have huv : v =ᵐ[volume.restrict (euclideanBall x
      (L.freezingRadius x / 2))] w := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hhalf hvae,
      ae_restrict_of_ae_restrict_of_subset (hhalf.trans hball)
        (A.cubeBoundaryRemainder_ae mu m)] with y hv hu
    rw [hv, hu]
  exact Decay.abs_center_le_of_ae_eq_euclideanBall
    (half_pos (L.freezingRadius_pos x))
    hvcont hwcont huv hvbound

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
