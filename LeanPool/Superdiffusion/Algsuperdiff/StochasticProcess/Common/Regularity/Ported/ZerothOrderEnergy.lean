/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.ZerothOrderTesting
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.ScalarForcing
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.UnitCubeDirichletPoincare

/-!
# ZerothOrderEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Energy comparison with a bounded scalar source
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport
open Algsuperdiff.Section4.Support
open HCPolySupport.Book.Ch05.Section53.JUpperBoundWeakNorms

noncomputable section

variable {d : ℕ}

private theorem abs_integral_mul_le_sqrt_sq_mul_sqrt_sq
    {W : Set (Vec d)} [IsFiniteMeasure (volume.restrict W)]
    {F G : Vec d → ℝ} (hF : MemLp F 2 (volume.restrict W))
    (hG : MemLp G 2 (volume.restrict W)) :
    |∫ x in W, F x * G x ∂volume| ≤
      Real.sqrt (∫ x in W, F x ^ 2 ∂volume) *
        Real.sqrt (∫ x in W, G x ^ 2 ∂volume) := by
  have hFG : IntegrableOn (fun x => |F x| * |G x|) W := by
    have hm := hF.norm.mul (r := 1) hG.norm
    simpa only [Real.norm_eq_abs, Pi.mul_apply, mul_comm] using!
      hm.integrable (by norm_num)
  have habs : |∫ x in W, F x * G x ∂volume| ≤
      ∫ x in W, |F x| * |G x| ∂volume := by
    calc
      |∫ x in W, F x * G x ∂volume| ≤ ∫ x in W, |F x * G x| ∂volume :=
        abs_integral_le_integral_abs
      _ = ∫ x in W, |F x| * |G x| ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        rw [abs_mul]
  have hcs :=
    integral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq_of_ae_nonneg
      (μ := volume.restrict W) hF.norm.integrable_sq hG.norm.integrable_sq
      (Filter.Eventually.of_forall fun x => abs_nonneg (F x))
      (Filter.Eventually.of_forall fun x => abs_nonneg (G x))
  simpa only [Real.norm_eq_abs, sq_abs] using habs.trans hcs

private theorem sqrt_integral_sq_eq_sqrt_volume_mul_normalizedL2On
    {W : Set (Vec d)} {F : Vec d → ℝ}
    (hW : 0 < (volume W).toReal) (hF : MemLp F 2 (volume.restrict W)) :
    Real.sqrt (∫ x in W, F x ^ 2 ∂volume) =
      Real.sqrt ((volume W).toReal) * normalizedL2On W F := by
  have hsq := HCPolySupport.toReal_eLpNorm_two_sq_eq_integral_sq hF
  have hnorm0 : 0 ≤ (eLpNorm F 2 (volume.restrict W)).toReal :=
    ENNReal.toReal_nonneg
  calc
    Real.sqrt (∫ x in W, F x ^ 2 ∂volume) =
        Real.sqrt ((eLpNorm F 2 (volume.restrict W)).toReal ^ 2) := by
      rw [hsq]
    _ = (eLpNorm F 2 (volume.restrict W)).toReal := Real.sqrt_sq hnorm0
    _ = Real.sqrt ((volume W).toReal) * normalizedL2On W F :=
      toReal_eLpNorm_eq_sqrt_volume_mul_normalizedL2On hW hF

/-- Normalized harmonic comparison with the extra Poincaré-priced scalar
source. -/
theorem harmonicComparison_normalizedEnergy_zerothOrder [NeZero d]
    (z : Vec d) {r : ℝ} (hr : 0 < r)
    {a : CoeffField d} {u h : H1Function (euclideanBall z r)}
    {rho : H10Function (euclideanBall z r)}
    {g : Vec d → ℝ} {f : Vec d → Vec d} {delta alpha : ℝ}
    (hmeas : Measurable a)
    (ha : CoefficientIdentityDistanceLE (euclideanBall z r) a delta)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a (euclideanBall z r) u g f)
    (hg : MemLp g 2 (volume.restrict (euclideanBall z r)))
    (hf : MemVectorL2 (euclideanBall z r) f)
    (hh : IsUnitWeaklyHarmonicOn (euclideanBall z r) h)
    (hgrad : ∀ x, h.grad x = u.grad x + rho.toH1Function.grad x) :
    vectorNormalizedL2On (euclideanBall z r) rho.toH1Function.grad ≤
      2 * delta * vectorNormalizedL2On (euclideanBall z r) h.grad +
        2 * vectorNormalizedL2On (euclideanBall z r) f +
        4 * unitCubeDirichletPoincareExplicit d * (d : ℝ) * r *
          normalizedL2On (euclideanBall z r) g := by
  let W : Set (Vec d) := euclideanBall z r
  let finiteVolumeW : IsFiniteMeasure (volume.restrict W) :=
    HCPolySupport.Book.Ch01.isFiniteMeasure_volumeMeasureOn_euclideanBall z r
  have hW : 0 < (volume W).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg
    (Ne.symm (HCPolySupport.Book.Ch01.volume_euclideanBall_toReal_ne_zero z hr))
  have hR := rho.toH1Function.grad_memVectorL2
  have hscalar := abs_integral_mul_le_sqrt_sq_mul_sqrt_sq hg rho.toH1Function.memL2
  have hpo := normalizedL2On_euclideanBall_le_vectorGradient z hr rho
  let hs : ℝ := Real.sqrt ((volume W).toReal)
  have hpomul := mul_le_mul_of_nonneg_left hpo
    (Real.sqrt_nonneg ((volume W).toReal))
  have hrhoNorm := sqrt_integral_sq_eq_sqrt_volume_mul_normalizedL2On
    hW rho.toH1Function.memL2
  have hgradNorm :=
    sqrt_integral_vecNormSq_eq_sqrt_volume_mul_vectorNormalizedL2On hW hR
  have hrhoRaw : Real.sqrt (∫ x in W, rho.toH1Function.toFun x ^ 2 ∂volume) ≤
      unitCubeDirichletPoincareExplicit d * (2 * r) * (d : ℝ) *
        Real.sqrt (∫ x in W, vecNormSq (rho.toH1Function.grad x) ∂volume) := by
    rw [hrhoNorm, hgradNorm]
    calc
      Real.sqrt ((volume W).toReal) * normalizedL2On W rho.toH1Function.toFun ≤
          Real.sqrt ((volume W).toReal) *
            (unitCubeDirichletPoincareExplicit d * (2 * r) * (d : ℝ) *
              vectorNormalizedL2On W rho.toH1Function.grad) := hpomul
      _ = unitCubeDirichletPoincareExplicit d * (2 * r) * (d : ℝ) *
          (Real.sqrt ((volume W).toReal) *
            vectorNormalizedL2On W rho.toH1Function.grad) := by ring
  let Z : ℝ := 2 * unitCubeDirichletPoincareExplicit d * (d : ℝ) * r *
    Real.sqrt (∫ x in W, g x ^ 2 ∂volume)
  have hzeroth : |∫ x in W, g x * rho.toH1Function.toFun x ∂volume| ≤
      Z * Real.sqrt (∫ x in W, vecNormSq (rho.toH1Function.grad x) ∂volume) := by
    refine hscalar.trans ?_
    have hmul := mul_le_mul_of_nonneg_left hrhoRaw
      (Real.sqrt_nonneg (∫ x in W, g x ^ 2 ∂volume))
    calc
      Real.sqrt (∫ x in W, g x ^ 2 ∂volume) *
          Real.sqrt (∫ x in W, rho.toH1Function.toFun x ^ 2 ∂volume) ≤
        Real.sqrt (∫ x in W, g x ^ 2 ∂volume) *
          (unitCubeDirichletPoincareExplicit d * (2 * r) * (d : ℝ) *
            Real.sqrt (∫ x in W,
              vecNormSq (rho.toH1Function.grad x) ∂volume)) := hmul
      _ = Z * Real.sqrt (∫ x in W,
          vecNormSq (rho.toH1Function.grad x) ∂volume) := by
        dsimp only [Z]
        ring
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (unitCubeDirichletPoincareExplicit_nonneg d))
          (Nat.cast_nonneg d)) hr.le)
      (Real.sqrt_nonneg _)
  have hraw := harmonicComparison_gradientEnergy_with_test hmeas ha halpha0 halpha1
    hdelta0 hdelta (htest := hu rho) hzeroth hZ hf hh hgrad
  rw [sqrt_integral_vecNormSq_eq_sqrt_volume_mul_vectorNormalizedL2On hW hR,
    sqrt_integral_vecNormSq_eq_sqrt_volume_mul_vectorNormalizedL2On hW h.grad_memVectorL2,
    sqrt_integral_vecNormSq_eq_sqrt_volume_mul_vectorNormalizedL2On hW hf] at hraw
  have hgraw : Real.sqrt (∫ x in W, g x ^ 2 ∂volume) =
      hs * normalizedL2On W g := by
    dsimp only [hs]
    exact sqrt_integral_sq_eq_sqrt_volume_mul_normalizedL2On hW hg
  dsimp only [Z] at hraw
  rw [hgraw] at hraw
  have hspos : 0 < hs := by
    dsimp only [hs]
    exact Real.sqrt_pos.2 hW
  apply (mul_le_mul_iff_of_pos_left hspos).mp
  convert hraw using 1
  all_goals first | rfl | ring

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
