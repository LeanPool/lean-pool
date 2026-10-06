/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedFourierMild
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildIntegral
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierCoordinateL2Bridge

/-!
# The forced regularized mild equation

The forced mild equation `eq:reg-mild-forced` with values in real spatial
`L²`: the heat evolution of the datum, minus the Stokes Duhamel integral of
the regularized tensor, plus the heat Duhamel integral of the Leray
projection of the force. The right-hand side is the real part of the inverse
transform of its frequency form `forcedFourierMild`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

open Classical in
/-- The spatial `L²` class of a time slice of a force, set to zero at the
times where the slice is not square integrable. -/
@[expose]
def forcedForceSlice (f : ParabolicPoint → Vec3) (s : ℝ) : RealVectorL2 :=
  if h : MemLp (fun x : Vec3 => f (x, s)) 2 volume then
    realVectorL2OfCoordinateFunction (fun x : Vec3 => f (x, s)) h
  else 0

/-- The heat evolution of the Leray projection, `S(τ) ℙ`, on real `L²`. -/
@[expose]
def forcedHeatLeray (τ : ℝ) (hτ : 0 ≤ τ) (v : RealVectorL2) : RealVectorL2 :=
  realPartVectorL2 (heatSemigroup τ hτ (lerayProjectionL2 (complexifyVectorL2 v)))

/-- The force Duhamel integrand of `eq:reg-mild-forced`. -/
@[expose]
def forcedForceIntegrand (h : ℝ → RealVectorL2) (t s : ℝ) : RealVectorL2 :=
  if hs : s ≤ t then forcedHeatLeray (t - s) (sub_nonneg.2 hs) (h s) else 0

/-- The force Duhamel integral `∫₀ᵗ S(t-s) ℙ f(s) ds` of `eq:reg-mild-forced`. -/
@[expose]
def forcedForceDuhamel (h : ℝ → RealVectorL2) (t : ℝ) : RealVectorL2 :=
  ∫ s in Ioc 0 t, forcedForceIntegrand h t s

/-- The right-hand side of the forced mild equation `eq:reg-mild-forced` for a
datum, a force curve and a tensor curve. -/
@[expose]
def forcedMildRHS (b : RealVectorL2) (h : ℝ → RealVectorL2) (F : ℝ → RealTensorL2)
    (t : ℝ) (ht : 0 ≤ t) : RealVectorL2 :=
  realHeatOperator t ht b - regularizedMildStokesIntegral F t + forcedForceDuhamel h t

/-- The real part of the inverse transform, as a real continuous linear map. -/
@[expose]
def forcedRealInverse : ComplexVectorL2 →L[ℝ] RealVectorL2 :=
  realPartVectorL2.comp
    ((Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).symm.toContinuousLinearEquiv.toContinuousLinearMap
      |>.restrictScalars ℝ)

theorem forcedRealInverse_apply (w : ComplexVectorL2) :
    forcedRealInverse w =
      realPartVectorL2 ((Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).symm w) := rfl

/-- The frequency form of the Stokes integrand inverts to the real Stokes
integrand. -/
theorem forcedRealInverse_stokesIntegrand (F : ℝ → RealTensorL2) (t s : ℝ) :
    forcedRealInverse (forcedFourierStokesIntegrand
      (fun r => Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3 (complexifyTensorL2 (F r))) t s) =
      regularizedMildStokesIntegrand F t s := by
  unfold forcedFourierStokesIntegrand regularizedMildStokesIntegrand
  by_cases hs : s < t
  · rw [dite_eq_left hs, dite_eq_left hs]
    rfl
  · rw [dite_eq_right hs, dite_eq_right hs, map_zero]

/-- The frequency form of the force integrand inverts to the real force
integrand. -/
theorem forcedRealInverse_forceIntegrand (h : ℝ → RealVectorL2) (t s : ℝ) :
    forcedRealInverse (forcedFourierForceIntegrand
      (fun r => Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (complexifyVectorL2 (h r))) t s) =
      forcedForceIntegrand h t s := by
  unfold forcedFourierForceIntegrand forcedForceIntegrand
  by_cases hs : s ≤ t
  · rw [dite_eq_left hs, dite_eq_left hs, forcedRealInverse_apply]
    unfold forcedHeatLeray heatSemigroup lerayProjectionL2
    simp only [LinearIsometryEquiv.apply_symm_apply]
  · rw [dite_eq_right hs, dite_eq_right hs, map_zero]

/-- The heat evolution is the inverse of its frequency form. -/
theorem forcedRealInverse_heat (b : RealVectorL2) (t : ℝ) (ht : 0 ≤ t) :
    forcedRealInverse (heatMultiplier t ht •
      Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (complexifyVectorL2 b)) =
      realHeatOperator t ht b := rfl

/-- The transformed tensor curve. -/
@[expose]
def forcedFourierTensorCurve (F : ℝ → RealTensorL2) (s : ℝ) : ComplexTensorL2 :=
  Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3 (complexifyTensorL2 (F s))

/-- The transformed force curve. -/
@[expose]
def forcedFourierForceCurve (h : ℝ → RealVectorL2) (s : ℝ) : ComplexVectorL2 :=
  Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (complexifyVectorL2 (h s))

theorem stronglyMeasurable_forcedFourierTensorCurve {F : ℝ → RealTensorL2}
    (hF : StronglyMeasurable F) : StronglyMeasurable (forcedFourierTensorCurve F) :=
  ((Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3).continuous.comp
    complexifyTensorL2.continuous).comp_stronglyMeasurable hF

theorem stronglyMeasurable_forcedFourierForceCurve {h : ℝ → RealVectorL2}
    (hh : StronglyMeasurable h) : StronglyMeasurable (forcedFourierForceCurve h) :=
  ((Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).continuous.comp
    complexifyVectorL2.continuous).comp_stronglyMeasurable hh

theorem norm_forcedFourierTensorCurve_le (F : ℝ → RealTensorL2) (s : ℝ) :
    ‖forcedFourierTensorCurve F s‖ ≤ ‖F s‖ := by
  rw [forcedFourierTensorCurve, LinearIsometryEquiv.norm_map]
  exact complexifyTensorL2_norm_le _

theorem norm_forcedFourierForceCurve_le (h : ℝ → RealVectorL2) (s : ℝ) :
    ‖forcedFourierForceCurve h s‖ ≤ ‖h s‖ := by
  rw [forcedFourierForceCurve, LinearIsometryEquiv.norm_map]
  exact complexifyVectorL2_norm_le _

/-- Integrability of the frequency Duhamel integrands of the forced mild
equation, for a bounded tensor curve and an integrable force curve. -/
theorem integrableOn_forcedFourier_integrands {F : ℝ → RealTensorL2}
    (hF : StronglyMeasurable F) {h : ℝ → RealVectorL2} (hh : StronglyMeasurable h)
    {t C : ℝ} (ht : 0 ≤ t) (hFC : ∀ s ∈ Ioc 0 t, ‖F s‖ ≤ C)
    (hH : IntegrableOn (fun s => ‖h s‖) (Ioc 0 t)) :
    IntegrableOn (forcedFourierStokesIntegrand (forcedFourierTensorCurve F) t) (Ioc 0 t) ∧
      IntegrableOn (forcedFourierForceIntegrand (forcedFourierForceCurve h) t) (Ioc 0 t) := by
  obtain ⟨Fh, hFh, hrepF⟩ := exists_jointRep_of_stronglyMeasurable (μ := volume)
    (forcedFourierTensorCurve F) (stronglyMeasurable_forcedFourierTensorCurve hF)
  obtain ⟨Hh, hHh, hrepH⟩ := exists_jointRep_of_stronglyMeasurable (μ := volume)
    (forcedFourierForceCurve h) (stronglyMeasurable_forcedFourierForceCurve hh)
  refine ⟨integrableOn_forcedFourierStokesIntegrand hFh.measurable hrepF ht
    (fun s hs => (norm_forcedFourierTensorCurve_le F s).trans (hFC s hs)), ?_⟩
  refine integrableOn_forcedFourierForceIntegrand hHh.measurable hrepH ?_
  refine Integrable.mono' hH ?_ (Eventually.of_forall fun s => ?_)
  · exact (stronglyMeasurable_forcedFourierForceCurve hh).norm.aestronglyMeasurable
  · rw [norm_norm]
    exact norm_forcedFourierForceCurve_le h s

/-- The right-hand side of the forced mild equation is the real part of the
inverse transform of its frequency form. -/
theorem forcedMildRHS_eq_forcedRealInverse (b : RealVectorL2) {F : ℝ → RealTensorL2}
    (hF : StronglyMeasurable F) {h : ℝ → RealVectorL2} (hh : StronglyMeasurable h)
    {t C : ℝ} (ht : 0 ≤ t) (hFC : ∀ s ∈ Ioc 0 t, ‖F s‖ ≤ C)
    (hH : IntegrableOn (fun s => ‖h s‖) (Ioc 0 t)) :
    forcedMildRHS b h F t ht = forcedRealInverse (forcedFourierMild
      (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (complexifyVectorL2 b))
      (forcedFourierTensorCurve F) (forcedFourierForceCurve h) t ht) := by
  obtain ⟨hS, hFI⟩ := integrableOn_forcedFourier_integrands hF hh ht hFC hH
  have hsum : Integrable (fun s => -forcedFourierStokesIntegrand (forcedFourierTensorCurve F) t s +
      forcedFourierForceIntegrand (forcedFourierForceCurve h) t s) (volume.restrict (Ioc 0 t)) :=
    hS.neg.add hFI
  unfold forcedFourierMild
  rw [map_add, forcedRealInverse_heat, ← forcedRealInverse.integral_comp_comm hsum]
  have hS' : IntegrableOn (fun s => forcedRealInverse
      (forcedFourierStokesIntegrand (forcedFourierTensorCurve F) t s)) (Ioc 0 t) :=
    forcedRealInverse.integrable_comp hS
  have hFI' : IntegrableOn (fun s => forcedRealInverse
      (forcedFourierForceIntegrand (forcedFourierForceCurve h) t s)) (Ioc 0 t) :=
    forcedRealInverse.integrable_comp hFI
  have hnegS : Integrable (fun s => -forcedRealInverse
      (forcedFourierStokesIntegrand (forcedFourierTensorCurve F) t s))
      (volume.restrict (Ioc 0 t)) := hS'.neg
  simp_rw [map_add, map_neg]
  rw [integral_add hnegS hFI', integral_neg]
  unfold forcedMildRHS forcedForceDuhamel regularizedMildStokesIntegral
  rw [integral_Icc_eq_integral_Ioc, sub_eq_add_neg, add_assoc]
  congr 2
  · congr 1
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    exact (forcedRealInverse_stokesIntegrand F t s).symm
  · refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    exact (forcedRealInverse_forceIntegrand h t s).symm

end CKN.Leray

end
