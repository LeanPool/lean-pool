/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Support.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpAdjoint

/-!
# FiniteLpLpData

Ported from scottnarmstrong/CoarseGraining at c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Supplied-solution cube Calderón--Zygmund estimates for `L^p` data

This file removes the auxiliary `L²` assumption on the datum in the centered-cube
finite-exponent Calderón--Zygmund estimate.  Below exponent two the proof uses
the existing adjoint-duality argument directly.  At and above exponent two,
finite normalized cube volume supplies the required `L²` membership internally.
-/

namespace HCPolySupport

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

private theorem centeredCube_normalizedVolume_eq_smul_openCubeVolume_lpData
    {d : ℕ} (m : ℤ) :
    (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) := by
  change (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume = _
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- Multiplying an unnormalized centered-cube weak equation by the reciprocal
cube volume gives its normalized-volume form. -/
private theorem centeredCube_normalizedWeak_of_rawWeak
    {d : ℕ} (m : ℤ) {sigma0 : ℝ}
    (u : H10Function (openCubeSet (originCube d m))) (h : Vec d → Vec d)
    (hsolution : ∀ psi : H10Function (openCubeSet (originCube d m)),
      sigma0 * ∫ x in openCubeSet (originCube d m),
          vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume =
        -∫ x in openCubeSet (originCube d m),
          vecDot (h x) (psi.toH1Function.grad x) ∂volume) :
    ∀ psi : H10Function (openCubeSet (originCube d m)),
      sigma0 * ∫ x,
          vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x)
            ∂(centeredCubeDomain d m).normalizedVolume =
        -∫ x, vecDot (h x) (psi.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume := by
  intro psi
  rw [centeredCube_normalizedVolume_eq_smul_openCubeVolume_lpData,
    integral_smul_measure, integral_smul_measure, smul_eq_mul, smul_eq_mul]
  calc
    sigma0 *
        ((ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
          ∫ x in openCubeSet (originCube d m),
            vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume) =
        (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
          (sigma0 * ∫ x in openCubeSet (originCube d m),
            vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume) := by
          ring
    _ = (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
          (-∫ x in openCubeSet (originCube d m),
            vecDot (h x) (psi.toH1Function.grad x) ∂volume) := by
          rw [hsolution psi]
    _ = -((ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
          ∫ x in openCubeSet (originCube d m),
            vecDot (h x) (psi.toH1Function.grad x) ∂volume) := by
          ring

private theorem centeredCubeH10ScalarDivergence_cz_lpData_of_lt_two
    (d : ℕ) [NeZero d] (q : FiniteLpExponent)
    (hq : q.exponent.toReal < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (sigma0 : ℝ)
      (h : CubeEuclideanLpField (originCube d m) q)
      (u : H10Function (openCubeSet (originCube d m))), 0 < sigma0 →
      (∀ psi : H10Function (openCubeSet (originCube d m)),
        sigma0 * ∫ x in openCubeSet (originCube d m),
            vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume =
          -∫ x in openCubeSet (originCube d m),
            vecDot (h.toField x) (psi.toH1Function.grad x) ∂volume) →
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        u.toH1Function.grad ≤ C * (ENNReal.ofReal sigma0)⁻¹ *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
            h.toField := by
  obtain ⟨C, hCtop, hC⟩ := centeredCubeH10ScalarDivergence_cz_of_two_lt d
    q.conjugate (INTERNAL.conjugate_toReal_gt_two_of_lt_two q hq)
  refine ⟨C, hCtop, ?_⟩
  intro m sigma0 h u hsigma0 hsolution
  refine cubeEuclideanLpENorm_le_of_adjoint_bound (originCube d m) q h
    u.toH1Function.grad_memVectorL2 (K := C * (ENNReal.ofReal sigma0)⁻¹) ?_ ?_
  · exact ENNReal.mul_ne_top hCtop.ne
      (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hsigma0)))
  · intro Gfield hGtwo
    let v := openCubeSetScalarDivergenceSolution (originCube d m) hsigma0 Gfield.toField hGtwo
    refine ⟨v.toH1Function.grad, v.toH1Function.grad_memVectorL2, ?_, ?_⟩
    · apply hC m sigma0 Gfield v hsigma0
      intro psi
      exact INTERNAL.openCubeSetScalarDivergenceSolution_normalized_weak
        m hsigma0 Gfield.toField hGtwo psi
    · exact INTERNAL.openCubeSetScalarDivergenceSolution_normalized_cross_pairing
        m hsigma0 u h.toField Gfield.toField
        (centeredCube_normalizedWeak_of_rawWeak m u h.toField hsolution) hGtwo

/-- The supplied-solution centered-cube Calderón--Zygmund estimate for every
finite exponent and an `L^p` datum.  No auxiliary `L²` hypothesis is exposed. -/
theorem centeredCubeH10ScalarDivergence_cz_lpData
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (sigma0 : ℝ)
      (h : CubeEuclideanLpField (originCube d m) q)
      (u : H10Function (openCubeSet (originCube d m))), 0 < sigma0 →
      (∀ psi : H10Function (openCubeSet (originCube d m)),
        sigma0 * ∫ x in openCubeSet (originCube d m),
            vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume =
          -∫ x in openCubeSet (originCube d m),
            vecDot (h.toField x) (psi.toH1Function.grad x) ∂volume) →
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        u.toH1Function.grad ≤ C * (ENNReal.ofReal sigma0)⁻¹ *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
            h.toField := by
  by_cases hlt : q.exponent.toReal < 2
  · exact centeredCubeH10ScalarDivergence_cz_lpData_of_lt_two d q hlt
  obtain ⟨C, hCtop, hC⟩ := centeredCubeH10ScalarDivergence_cz d q
  refine ⟨C, hCtop, ?_⟩
  intro m sigma0 h u hsigma0 hsolution
  have htwo_le : (2 : ℝ≥0∞) ≤ q.exponent := by
    apply (ENNReal.toReal_le_toReal (by norm_num) q.lt_top.ne).mp
    simpa only [ENNReal.toReal_ofNat] using le_of_not_gt hlt
  let hL2Lp : CubeEuclideanL2LpField (originCube d m) q :=
    { toCubeEuclideanLpField := h
      euclideanMemL2 := h.euclideanMemLp.mono_exponent htwo_le }
  have hnormalized : IsCenteredCubeH10ScalarDivergenceSolution m sigma0 u
      hL2Lp.toLpTwo := by
    intro psi
    simpa only [hL2Lp, CubeEuclideanL2LpField.toLpTwo] using
      centeredCube_normalizedWeak_of_rawWeak m u h.toField hsolution psi
  simpa only [hL2Lp] using hC m sigma0 hL2Lp u hsigma0 hnormalized

end CubeCalderonZygmund

end
end HCPolySupport
