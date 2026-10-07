/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzTensor
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedDuhamelPairing

/-!
# Realification of Schwartz mollification

The complex Schwartz convolution of a real Schwartz field is the
complexification of the real regularized convolution.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Complexification commutes with convolution by the real mollifier
on Schwartz velocity fields. -/
theorem regularisedSchwartzMollify_complexifyReal_apply
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (φ : 𝓢(L2Vec3, L2Vec3)) (x : L2Vec3) :
    regularisedSchwartzMollify ρ ε hε
        (complexifyRealSchwartz φ) x =
      complexifyValue (regMollifyVector ρ ε hε φ x) := by
  rw [regularisedSchwartzMollify_apply]
  change (∫ y : L2Vec3,
    (ContinuousLinearMap.lsmul ℂ ℂ)
      ((regMollifierKernel ρ ε hε y : ℝ) : ℂ)
      (complexifyRealSchwartz φ (x - y))) = _
  have hInt : Integrable (fun y : L2Vec3 =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (regMollifierKernel ρ ε hε y) (φ (x - y))) volume := by
    exact ((ConvolutionExists.of_memLp_memLp
      (L := (ContinuousLinearMap.lsmul ℝ ℝ))
      (regMollifierKernel_memLp_two ρ ε hε)
      (φ.memLp (p := 2))) x).integrable
  rw [show complexifyValue (regMollifyVector ρ ε hε φ x) =
    complexifyValue (∫ y : L2Vec3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (regMollifierKernel ρ ε hε y) (φ (x - y))) from rfl]
  conv_rhs => rw [← complexifyValue.integral_comp_comm hInt]
  apply integral_congr_ae
  filter_upwards with y
  apply PiLp.ext
  intro i
  simp [complexifyRealSchwartz, complexifyValue,
    complexifyValueLinear, complexifyFrequency]

/-- The complex Schwartz tensor of a real Schwartz velocity agrees
pointwise with the complexification of the real mild tensor field. -/
theorem regularisedSchwartzTensor_complexifyReal_apply
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (φ : 𝓢(L2Vec3, L2Vec3)) (x : L2Vec3) :
    regularisedSchwartzTensor ρ ε hε
        (complexifyRealSchwartz φ) x =
      complexifyTensorValue
        (regularizedTensorOuter (regMollifyVector ρ ε hε φ x) (φ x)) := by
  rw [regularisedSchwartzTensor_apply,
    regularisedSchwartzMollify_complexifyReal_apply]
  apply PiLp.ext
  intro i
  apply PiLp.ext
  intro j
  simp [regularisedComplexTensorOuter, regularizedTensorOuter,
    complexifyTensorValue, complexifyTensorLinear,
    complexifyRealSchwartz, complexifyValue,
    complexifyValueLinear, complexifyFrequency]

private theorem regularisedSchwartzMollify_toLp_eq
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (φ : 𝓢(L2Vec3, L2Vec3)) :
    regMollifyVector ρ ε hε (φ.toLp 2) =
      regMollifyVector ρ ε hε φ := by
  have hφ : (φ.toLp 2 : RealVectorL2) =ᵐ[volume] φ := φ.coeFn_toLp 2 volume
  unfold regMollifyVector
  exact MeasureTheory.convolution_congr (L := _)
    (Filter.Eventually.of_forall fun _ => rfl) hφ

private theorem regularisedSchwartzTensor_complexifyReal_ae_raw
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (φ : 𝓢(L2Vec3, L2Vec3)) :
    ((regularisedSchwartzTensor ρ ε hε
        (complexifyRealSchwartz φ)).toLp 2 : ComplexTensorL2) =ᵐ[volume]
      fun x => complexifyTensorValue
        (regularizedMildTensorField ρ ε hε (φ.toLp 2) x) := by
  have hφ : (φ.toLp 2 : RealVectorL2) =ᵐ[volume] φ := φ.coeFn_toLp 2 volume
  have hconv : regMollifyVector ρ ε hε (φ.toLp 2) =
      regMollifyVector ρ ε hε φ :=
    regularisedSchwartzMollify_toLp_eq ρ ε hε φ
  have hleft :=
    (regularisedSchwartzTensor ρ ε hε
      (complexifyRealSchwartz φ)).coeFn_toLp 2 volume
  filter_upwards [hleft, hφ] with x hl hφx
  rw [hl, regularisedSchwartzTensor_complexifyReal_apply]
  simp only [regularizedMildTensorField, hconv, hφx]

private theorem regularisedMildTensor_schwartz_ae
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (φ : 𝓢(L2Vec3, L2Vec3)) :
    (regularizedMildTensor ρ ε hε (φ.toLp 2) : RealTensorL2) =ᵐ[volume]
      regularizedMildTensorField ρ ε hε (φ.toLp 2) :=
  MemLp.coeFn_toLp _

/-- On real Schwartz data, the complex Schwartz tensor represents
the same L² class as the complexified real mild nonlinearity. -/
theorem regularisedSchwartzTensor_complexifyReal_toLp
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (φ : 𝓢(L2Vec3, L2Vec3)) :
    ((regularisedSchwartzTensor ρ ε hε
        (complexifyRealSchwartz φ)).toLp 2 : ComplexTensorL2) =
      complexifyTensorL2 (regularizedMildTensor ρ ε hε (φ.toLp 2)) := by
  apply Lp.ext
  change
    ((regularisedSchwartzTensor ρ ε hε
        (complexifyRealSchwartz φ)).toLp 2 : ComplexTensorL2) =ᵐ[volume]
      (complexifyTensorValue.compLpL 2 volume)
        (regularizedMildTensor ρ ε hε (φ.toLp 2))
  have hraw := regularisedSchwartzTensor_complexifyReal_ae_raw ρ ε hε φ
  have hright :
      (regularizedMildTensor ρ ε hε (φ.toLp 2) : RealTensorL2) =ᵐ[volume]
        regularizedMildTensorField ρ ε hε (φ.toLp 2) :=
    regularisedMildTensor_schwartz_ae ρ ε hε φ
  have hcomplex := complexifyTensorValue.coeFn_compLpL
    (regularizedMildTensor ρ ε hε (φ.toLp 2))
  exact hraw.trans ((hright.symm.fun_comp complexifyTensorValue).trans hcomplex.symm)

end CKN.Leray

end
