/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.ZerothOrderEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.HarmonicGradientSubmean

/-!
# ZerothOrderOneStep

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# One dyadic comparison with a bounded scalar source
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

private theorem vectorNormalizedL2On_le_of_integral_vecNormSq_le'
    {W : Set (Vec d)} {F G : Vec d → Vec d}
    (h : (∫ x in W, vecNormSq (F x) ∂volume) ≤
      ∫ x in W, vecNormSq (G x) ∂volume) :
    vectorNormalizedL2On W F ≤ vectorNormalizedL2On W G := by
  unfold vectorNormalizedL2On normalizedL2On volumeAverage
  have hmul := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (volume W).toReal⁻¹)
  apply Real.sqrt_le_sqrt
  simpa only [euclideanNorm_sq] using hmul

/-- The half-ball one-step estimate with an additional scalar source. -/
theorem oneStep_normalizedGradient_half_zerothOrder [NeZero d]
    (z : Vec d) {r : ℝ} (hr : 0 < r)
    {a : CoeffField d} {u : H1Function (euclideanBall z r)}
    {g : Vec d → ℝ} {f : Vec d → Vec d} {delta alpha : ℝ}
    (hmeas : Measurable a)
    (ha : CoefficientIdentityDistanceLE (euclideanBall z r) a delta)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a (euclideanBall z r) u g f)
    (hg : MemLp g 2 (volume.restrict (euclideanBall z r)))
    (hf : MemVectorL2 (euclideanBall z r) f) :
    vectorNormalizedL2On (euclideanBall z (r / 2)) u.grad ≤
      (1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) *
          vectorNormalizedL2On (euclideanBall z r) u.grad +
        2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
          vectorNormalizedL2On (euclideanBall z r) f +
        4 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
          unitCubeDirichletPoincareExplicit d * (d : ℝ) * r *
          normalizedL2On (euclideanBall z r) g := by
  let W : Set (Vec d) := euclideanBall z r
  let V : Set (Vec d) := euclideanBall z (r / 2)
  let finiteVolumeW : IsFiniteMeasure (volumeMeasureOn W) :=
    HCPolySupport.Book.Ch01.isFiniteMeasure_volumeMeasureOn_euclideanBall z r
  have hW : 0 < (volume W).toReal := by
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (HCPolySupport.Book.Ch01.volume_euclideanBall_toReal_ne_zero z hr))
  have hV : 0 < (volume V).toReal := by
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (HCPolySupport.Book.Ch01.volume_euclideanBall_toReal_ne_zero z
        (by positivity : 0 < r / 2)))
  have hsub : V ⊆ W :=
    euclideanBall_subset_euclideanBall (by positivity : 0 ≤ r / 2)
      (by linarith only [hr])
  obtain ⟨h, rho, hh, _hfun, hgrad, hdir⟩ :=
    exists_unitHarmonicReplacement_euclideanBall z hr u
  have hR : MemVectorL2 W rho.toH1Function.grad := rho.toH1Function.grad_memVectorL2
  have hH : MemVectorL2 W h.grad := h.grad_memVectorL2
  have hRV : MemVectorL2 V rho.toH1Function.grad :=
    hR.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hHV : MemVectorL2 V h.grad :=
    hH.mono_measure (Measure.restrict_mono hsub le_rfl)
  have htri : vectorNormalizedL2On V u.grad ≤
      vectorNormalizedL2On V h.grad + vectorNormalizedL2On V rho.toH1Function.grad := by
    have hbase := vectorNormalizedL2On_sub_le hHV hRV
    have heq : (fun x => h.grad x - rho.toH1Function.grad x) = u.grad := by
      funext x
      exact ((eq_sub_iff_add_eq).2 (hgrad x).symm).symm
    rwa [heq] at hbase
  have hhmono : vectorNormalizedL2On V h.grad ≤ vectorNormalizedL2On W h.grad :=
    vectorNormalizedL2On_grad_mono_euclideanBall hr (by positivity)
      (by linarith only [hr]) h hh
  have hrhoRestrict : vectorNormalizedL2On V rho.toH1Function.grad ≤
      (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
        vectorNormalizedL2On W rho.toH1Function.grad := by
    have hbase := vectorNormalizedL2On_le_of_subset hsub hW hV
      (memHilbertVectorL2_hilbertifyVecField hR)
    rw [sqrt_volume_ratio_half_euclideanBall z hr] at hbase
    exact hbase
  have hcomp := harmonicComparison_normalizedEnergy_zerothOrder z hr hmeas ha
    halpha0 halpha1 hdelta0 hdelta hu hg hf hh hgrad
  have hhdir : vectorNormalizedL2On W h.grad ≤ vectorNormalizedL2On W u.grad := by
    apply vectorNormalizedL2On_le_of_integral_vecNormSq_le'
    simpa only [W, vecNormSq] using hdir
  have hq : 0 ≤ (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hrho := mul_le_mul_of_nonneg_left hcomp hq
  calc
    vectorNormalizedL2On V u.grad ≤
        vectorNormalizedL2On V h.grad + vectorNormalizedL2On V rho.toH1Function.grad := htri
    _ ≤ vectorNormalizedL2On W h.grad +
        (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
          vectorNormalizedL2On W rho.toH1Function.grad :=
      add_le_add hhmono hrhoRestrict
    _ ≤ vectorNormalizedL2On W h.grad +
        (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
          (2 * delta * vectorNormalizedL2On W h.grad +
            2 * vectorNormalizedL2On W f +
            4 * unitCubeDirichletPoincareExplicit d * (d : ℝ) * r *
              normalizedL2On W g) := add_le_add le_rfl hrho
    _ ≤ (1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) *
          vectorNormalizedL2On W u.grad +
        2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) * vectorNormalizedL2On W f +
        4 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) * unitCubeDirichletPoincareExplicit d *
          (d : ℝ) * r * normalizedL2On W g := by
      have hcoef : 0 ≤ 1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) := by
        positivity
      have hm := mul_le_mul_of_nonneg_left hhdir hcoef
      have hadd := add_le_add_right hm
        (2 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) * vectorNormalizedL2On W f +
          4 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) * unitCubeDirichletPoincareExplicit d *
            (d : ℝ) * r * normalizedL2On W g)
      convert hadd using 1
      all_goals first | rfl | ring

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
