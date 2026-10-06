/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingFourierField
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalVelocity
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Continuous spatial L² curves from damped Fourier multipliers

A bounded frequency multiplier acts continuously on the weighted
Bessel frequency trajectory. Inverse Fourier transformation gives the
continuous spatial L² derivative curve.
-/

public section

open CKN

open MeasureTheory FourierTransform Complex
open scoped ENNReal FourierTransform Real


noncomputable section

namespace ESS

open CKN.Leray
open CKN.Foundation.Parabolic

/-- The bounded frequency symbol for an ordered derivative of a
high-Bessel field. -/
@[expose] def lps_dampedWeightSymbol (n : ℕ) (α : List (Fin 3))
    (ξ : L2Vec3) : ℂ :=
  lps_dampedFourierWordSymbol n α ξ *
    (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ)

/-- The ordered derivative symbol is continuous in frequency. -/
theorem lps_dampedWeightSymbol_continuous
    (n : ℕ) (α : List (Fin 3)) :
    Continuous (lps_dampedWeightSymbol n α) :=
  (lps_dampedFourierWordSymbol_continuous n α).mul
    CKN.Leray.regR12Weight_continuous

/-- The ordered derivative symbol is an essentially bounded scalar
multiplier (`prop:lps-smoothing`). -/
@[expose] def lps_dampedWeightLp
    (n : ℕ) (α : List (Fin 3))
    (hα : α.length ≤ 2 * (n + 1)) :
    Lp (α := L2Vec3) ℂ ∞ :=
  (memLp_top_of_bound
    (lps_dampedWeightSymbol_continuous n α).aestronglyMeasurable
    ((2 * π) ^ α.length)
    (Filter.Eventually.of_forall fun ξ =>
      lps_dampedFourierWordSymbol_weighted_norm_le n α hα ξ)).toLp
    (lps_dampedWeightSymbol n α)

/-- Applying the ordered bounded multiplier and inverse Fourier
transform to a continuous high-Bessel frequency path gives a
continuous complex spatial `L²` curve
(`prop:lps-smoothing`). -/
theorem lps_dampedFourierCurve_continuous
    {I : Type*} [TopologicalSpace I]
    (n : ℕ) (α : List (Fin 3))
    (hα : α.length ≤ 2 * (n + 1))
    (G : I → ComplexVectorL2) (hG : Continuous G) :
    Continuous (fun t : I =>
      (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).symm
        ((lps_dampedWeightLp n α hα) • G t)) := by
  let A : Lp (α := L2Vec3) ℂ ∞ := lps_dampedWeightLp n α hα
  have hdiff (x y : ComplexVectorL2) :
      A • x - A • y = A • (x - y) := by
    simp only [sub_eq_add_neg, Lp.add_smul, Lp.smul_neg]
  have hLip : LipschitzWith ⟨‖A‖, norm_nonneg A⟩
      (fun x : ComplexVectorL2 => A • x) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, hdiff]
    exact Lp.norm_smul_le A (x - y)
  have hAG : Continuous (fun t : I => A • G t) :=
    hLip.continuous.comp hG
  exact (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).symm.continuous.comp
    hAG

/-- The bounded scalar multiplier agrees almost everywhere with its
frequency formula. -/
theorem lps_dampedWeightLp_ae_eq
    (n : ℕ) (α : List (Fin 3))
    (hα : α.length ≤ 2 * (n + 1)) :
    ((lps_dampedWeightLp n α hα : Lp (α := L2Vec3) ℂ ∞) :
      L2Vec3 → ℂ) =ᵐ[volume]
      lps_dampedWeightSymbol n α := by
  unfold lps_dampedWeightLp
  exact (memLp_top_of_bound
    (lps_dampedWeightSymbol_continuous n α).aestronglyMeasurable
    ((2 * π) ^ α.length)
    (Filter.Eventually.of_forall fun ξ =>
      lps_dampedFourierWordSymbol_weighted_norm_le n α hα ξ)).coeFn_toLp

/-- The classical inverse Fourier field agrees almost everywhere with
the continuous spatial `L²` curve obtained from its bounded multiplier
(`prop:lps-smoothing`). -/
theorem lps_dampedSpaceTimeField_ae_eq_curve
    (n : ℕ) (α : List (Fin 3))
    (hα : α.length ≤ 2 * (n + 1))
    (G : ComplexVectorL2) :
    CKN.Leray.regR12WeightedField
      (lps_dampedFourierWordSymbol n α) G =ᵐ[volume]
      ((Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).symm
        ((lps_dampedWeightLp n α hα) • G) : ComplexVectorL2) := by
  let A : Lp (α := L2Vec3) ℂ ∞ := lps_dampedWeightLp n α hα
  let H : ComplexVectorL2 :=
    (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).symm (A • G)
  have hGH :
      ((Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 H : ComplexVectorL2) :
        L2Vec3 → ComplexVec3) =ᵐ[volume]
      fun ξ => lps_dampedFourierWordSymbol n α ξ •
        (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
          (G : L2Vec3 → ComplexVec3) ξ := by
    simp only [H, LinearIsometryEquiv.apply_symm_apply]
    filter_upwards [Lp.coeFn_lpSMul (r := 2) A G,
      lps_dampedWeightLp_ae_eq n α hα] with ξ hsmul hA
    rw [hsmul]
    change A ξ = lps_dampedWeightSymbol n α ξ at hA
    change A ξ • G ξ = _
    rw [hA]
    simp only [lps_dampedWeightSymbol, smul_smul]
  exact CKN.Leray.regR12WeightedField_ae_eq
    (lps_dampedFourierWordSymbol n α)
    (lps_dampedFourierWordSymbol_continuous n α).aestronglyMeasurable
    ((2 * π) ^ α.length) (by positivity)
    (lps_dampedFourierWordSymbol_norm_le n α hα) G H hGH

/-- The real coordinate of an ordered Fourier derivative is a continuous
spatial `L²` trajectory after transport from `L2Vec3` to `Vec3`. -/
@[expose] def lps_dampedScalarCurve
    (n : ℕ) (α : List (Fin 3)) (hα : α.length ≤ 2 * (n + 1))
    (i : Fin 3) (G : ℝ → ComplexVectorL2) (t : ℝ) :
    Lp ℝ 2 (volume : Measure Vec3) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (WithLp.toLp 2)
      CKN.Leray.vec3ToL2Vec3_measurePreserving)
    ((CKN.Leray.regR12CoordCLM i).compLpL 2 volume
      ((Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).symm
        ((lps_dampedWeightLp n α hα) • G t)))

/-- The physical real coordinate inherits the continuous `L²` curve of
the weighted Fourier trajectory (`prop:lps-smoothing`). -/
theorem lps_dampedScalarCurve_continuous
    (n : ℕ) (α : List (Fin 3)) (hα : α.length ≤ 2 * (n + 1))
    (i : Fin 3) (G : ℝ → ComplexVectorL2) (hG : Continuous G) :
    Continuous (lps_dampedScalarCurve n α hα i G) := by
  unfold lps_dampedScalarCurve
  exact (Lp.compMeasurePreservingₗᵢ ℝ (WithLp.toLp 2)
      CKN.Leray.vec3ToL2Vec3_measurePreserving).continuous.comp
    (((CKN.Leray.regR12CoordCLM i).compLpL 2 volume).continuous.comp
      (lps_dampedFourierCurve_continuous n α hα G hG))

/-- On each slice the Fourier scalar curve represents the classical
ordered inverse Fourier field almost everywhere. -/
theorem lps_dampedScalarCurve_ae_eq
    (n : ℕ) (α : List (Fin 3)) (hα : α.length ≤ 2 * (n + 1))
    (i : Fin 3) (G : ℝ → ComplexVectorL2) (t : ℝ) :
    (lps_dampedScalarCurve n α hα i G t : Vec3 → ℝ) =ᵐ[volume]
      fun x : Vec3 => CKN.Leray.regR12SpaceTimeField
        (CKN.Leray.regR12CoordCLM i)
        (lps_dampedFourierWordSymbol n α) G (x, t) := by
  let H : ComplexVectorL2 :=
    (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).symm
      ((lps_dampedWeightLp n α hα) • G t)
  have htransport := Lp.coeFn_compMeasurePreserving
    ((CKN.Leray.regR12CoordCLM i).compLpL 2 volume H)
    CKN.Leray.vec3ToL2Vec3_measurePreserving
  have hcoord := (CKN.Leray.regR12CoordCLM i).coeFn_compLpL
    (p := 2) (μ := volume) H
  have hfield := lps_dampedSpaceTimeField_ae_eq_curve n α hα (G t)
  have hcoord' :=
    CKN.Leray.vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hcoord
  have hfield' :=
    CKN.Leray.vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hfield
  filter_upwards [htransport, hcoord', hfield'] with x hx hc hf
  have hdef : lps_dampedScalarCurve n α hα i G t =
      Lp.compMeasurePreserving (WithLp.toLp 2)
        CKN.Leray.vec3ToL2Vec3_measurePreserving
        ((CKN.Leray.regR12CoordCLM i).compLpL 2 volume H) := rfl
  calc
    (lps_dampedScalarCurve n α hα i G t : Vec3 → ℝ) x =
        CKN.Leray.regR12CoordCLM i (H (WithLp.toLp 2 x)) := by
          rw [hdef]
          simpa only [Function.comp_apply] using hx.trans hc
    _ = CKN.Leray.regR12SpaceTimeField
        (CKN.Leray.regR12CoordCLM i)
        (lps_dampedFourierWordSymbol n α) G (x, t) := by
          exact congrArg (CKN.Leray.regR12CoordCLM i) hf.symm

end ESS
