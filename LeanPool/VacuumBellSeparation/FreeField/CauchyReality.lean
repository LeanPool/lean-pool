/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CauchyPointwiseEquation
public import LeanPool.VacuumBellSeparation.FreeField.SourceDistributionReality

/-!
# Reality of the actual cosine/sine Cauchy solution

Complex conjugation is the existing actual real-linear Schwartz operation.
The literal Fourier transform has conjugate reflection symmetry. Real even
Fourier multipliers consequently preserve real spatial data. The actual
cosine/sine Cauchy solution is therefore real; its actual time derivative is
real as well.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter FourierTransform
open scoped FourierTransform ComplexConjugate

theorem conj_real_fourierCharacter (r : ℝ) : conj (𝐞 r : ℂ) = (𝐞 (-r) : ℂ) := by
  simp only [Real.fourierChar_apply, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem fourier_spatialSchwartzConjugate_apply (f : SpatialSchwartz)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    (𝓕 (spatialSchwartzConjugate f)) ξ = conj ((𝓕 f) (-ξ)) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [Circle.smul_def, smul_eq_mul, spatialSchwartzConjugate_apply,
      map_mul, conj_real_fourierCharacter, inner_neg_right, neg_neg]

theorem spatialSchwartzConjugate_fourierMultiplier
    (w : EuclideanSpace ℝ (Fin 3) → ℂ) (hw : Function.HasTemperateGrowth w)
    (hwr : ∀ ξ, conj (w (-ξ)) = w ξ) (f : SpatialSchwartz) :
    spatialSchwartzConjugate (SchwartzMap.fourierMultiplierCLM ℂ w f) =
      SchwartzMap.fourierMultiplierCLM ℂ w (spatialSchwartzConjugate f) := by
  apply (fourierCLE ℂ SpatialSchwartz).injective
  ext ξ
  change (𝓕 (spatialSchwartzConjugate (SchwartzMap.fourierMultiplierCLM ℂ w f))) ξ =
    (𝓕 (SchwartzMap.fourierMultiplierCLM ℂ w (spatialSchwartzConjugate f))) ξ
  rw [fourier_spatialSchwartzConjugate_apply]
  simp only [SchwartzMap.fourierMultiplierCLM_apply, fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply hw, smul_eq_mul, map_mul, hwr,
    fourier_spatialSchwartzConjugate_apply]

theorem massiveSchwartzSymbol_neg (m r : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    massiveSchwartzSymbol m r (-ξ) = massiveSchwartzSymbol m r ξ := by
  simp only [massiveSchwartzSymbol, smul_neg, norm_neg]

theorem spatialSchwartzConjugate_massiveSchwartzCosine (m t : ℝ) (f : SpatialSchwartz) :
    spatialSchwartzConjugate (massiveSchwartzCosine m t f) =
      massiveSchwartzCosine m t (spatialSchwartzConjugate f) := by
  apply spatialSchwartzConjugate_fourierMultiplier _ (hasTemperateGrowth_massiveCosine m t)
  intro ξ
  simp only [Complex.conj_ofReal, massiveSchwartzSymbol_neg]

theorem spatialSchwartzConjugate_massiveSchwartzSine (m t : ℝ) (f : SpatialSchwartz) :
    spatialSchwartzConjugate (massiveSchwartzSine m t f) =
      massiveSchwartzSine m t (spatialSchwartzConjugate f) := by
  apply spatialSchwartzConjugate_fourierMultiplier _ (hasTemperateGrowth_massiveSine m t)
  intro ξ
  simp only [Complex.conj_ofReal, massiveSchwartzSymbol_neg]

theorem spatialSchwartzConjugate_massiveSchwartzCauchy (m t : ℝ) (f g : SpatialSchwartz) :
    spatialSchwartzConjugate (massiveSchwartzCauchy m t f g) =
      massiveSchwartzCauchy m t (spatialSchwartzConjugate f) (spatialSchwartzConjugate g) := by
  simp only [massiveSchwartzCauchy, map_add, spatialSchwartzConjugate_massiveSchwartzCosine,
    spatialSchwartzConjugate_massiveSchwartzSine]

theorem massiveSchwartzCauchy_real (m t : ℝ) (f g : SpatialSchwartz)
    (hf : spatialSchwartzConjugate f = f) (hg : spatialSchwartzConjugate g = g)
    (x : EuclideanSpace ℝ (Fin 3)) :
    conj (massiveSchwartzCauchy m t f g x) = massiveSchwartzCauchy m t f g x := by
  have h := spatialSchwartzConjugate_massiveSchwartzCauchy m t f g
  rw [hf, hg] at h
  exact DFunLike.congr_fun h x

theorem massiveSchwartzCauchyVelocity_real (m t : ℝ) (f g : SpatialSchwartz)
    (hf : spatialSchwartzConjugate f = f) (hg : spatialSchwartzConjugate g = g)
    (x : EuclideanSpace ℝ (Fin 3)) :
    conj (massiveSchwartzCauchyVelocity m t f g x) = massiveSchwartzCauchyVelocity m t f g x := by
  have h := hasDerivAt_massiveSchwartzCauchy_pointwise m t f g x
  have hc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h
  have heq : (fun s => conj (massiveSchwartzCauchy m s f g x)) =
      (fun s => massiveSchwartzCauchy m s f g x) :=
    funext (fun s => massiveSchwartzCauchy_real m s f g hf hg x)
  change HasDerivAt (fun s => conj (massiveSchwartzCauchy m s f g x))
    (conj (massiveSchwartzCauchyVelocity m t f g x)) t at hc
  rw [heq] at hc
  exact hc.unique h

end VacuumBellSeparation
