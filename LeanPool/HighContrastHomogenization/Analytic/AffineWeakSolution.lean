/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffinePairing
public import LeanPool.HighContrastHomogenization.Analytic.AffineWeakGradient

/-!
# High-contrast homogenization: Analytic.AffineWeakSolution

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine transport of weak solutions

The divergence-form coefficient, transpose gradient, and inverse-coordinate
domain transform together.  Both absolute convergence of every weak pairing
and its vanishing are preserved in each direction.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

private theorem affineCoefficient_pairing {L : Mat d} (hL : IsUnit L.det)
    (a : CoeffField d) (y ξ ζ : Vec d) :
    vecDot (matVecMul (matTranspose L) ξ)
        (matVecMul (affineCoefficient L hL a y)
          (matVecMul (matTranspose L) ζ)) =
      vecDot ξ (matVecMul (a (matVecMul L y)) ζ) := by
  rw [affineCoefficient_flux hL]
  calc
    vecDot (matVecMul (matTranspose L) ξ)
        (matVecMul L⁻¹ (matVecMul (a (matVecMul L y)) ζ)) =
        vecDot (matVecMul L⁻¹ (matVecMul (a (matVecMul L y)) ζ))
          (matVecMul (matTranspose L) ξ) := vecDot_comm _ _
    _ = vecDot
          (matVecMul L (matVecMul L⁻¹ (matVecMul (a (matVecMul L y)) ζ))) ξ :=
        vecDot_matVecMul_transpose _ _ L
    _ = vecDot (matVecMul (a (matVecMul L y)) ζ) ξ := by
      rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one]
    _ = vecDot ξ (matVecMul (a (matVecMul L y)) ζ) := vecDot_comm _ _

private theorem affineWeakIntegrand_comp_matVecMul {L : Mat d}
    (hL : IsUnit L.det) (a : CoeffField d) (F : Vec d → Vec d)
    {psi : Vec d → ℝ} (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) (y : Vec d) :
    vecDot (smoothGrad (fun z ↦ psi (matVecMul L z)) y)
        (matVecMul (affineCoefficient L hL a y)
          (matVecMul (matTranspose L) (F (matVecMul L y)))) =
      vecDot (smoothGrad psi (matVecMul L y))
        (matVecMul (a (matVecMul L y)) (F (matVecMul L y))) := by
  rw [smoothGrad_comp_matVecMul L hpsi]
  exact affineCoefficient_pairing hL a y _ _

private theorem isWeakSolutionOn_affinePullback {L : Mat d}
    (hL : IsUnit L.det) {U : Set (Vec d)} (hU : MeasurableSet U)
    (a : CoeffField d) (F : Vec d → Vec d)
    (hsol : IsWeakSolutionOn a U F) :
    IsWeakSolutionOn (affineCoefficient L hL a) (matImage L⁻¹ U)
      (fun y ↦ matVecMul (matTranspose L) (F (matVecMul L y))) := by
  let V : Set (Vec d) := matImage L⁻¹ U
  have hV : MeasurableSet V := measurableSet_affinePullback hL hU
  have hLV : matImage L V = U := by
    exact matImage_matImage_inv hL U
  intro phi hphi
  let psi : Vec d → ℝ := fun x ↦ phi (matVecMul L⁻¹ x)
  have hpsi : IsLocalTest U psi := isLocalTest_comp_matVecMul_inv hL hphi
  let p : Vec d → ℝ := fun x ↦
    vecDot (smoothGrad psi x) (matVecMul (a x) (F x))
  let q : Vec d → ℝ := fun y ↦
    vecDot (smoothGrad phi y)
      (matVecMul (affineCoefficient L hL a y)
        (matVecMul (matTranspose L) (F (matVecMul L y))))
  have hcompose : (fun y ↦ psi (matVecMul L y)) = phi := by
    funext y
    simp only [psi, matVecMul_mul, Matrix.nonsing_inv_mul L hL, matVecMul_one]
  have hpq : ∀ y, q y = p (matVecMul L y) := by
    intro y
    change vecDot (smoothGrad phi y)
        (matVecMul (affineCoefficient L hL a y)
          (matVecMul (matTranspose L) (F (matVecMul L y)))) = _
    rw [← hcompose]
    exact affineWeakIntegrand_comp_matVecMul hL a F hpsi.contDiff y
  have hp := hsol psi hpsi
  have hpImage : IntegrableOn p (matImage L V) volume := by
    simpa only [hLV, p] using hp.1
  have hpComp : IntegrableOn (fun y ↦ p (matVecMul L y)) V volume :=
    (integrableOn_matImage_iff hL hV p).mp hpImage
  refine ⟨?_, ?_⟩
  · apply hpComp.congr
    filter_upwards with y
    exact (hpq y).symm
  · have hchange := setIntegral_matImage hL hV p
    rw [hLV] at hchange
    have hpzero : ∫ x in U, p x ∂volume = 0 := by simpa only [p] using hp.2
    have hqint : (∫ y in V, q y ∂volume) =
        ∫ y in V, p (matVecMul L y) ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall hpq)
    rw [hpzero, smul_eq_mul, ← hqint] at hchange
    exact (mul_eq_zero.mp hchange.symm).resolve_left
      (abs_ne_zero.mpr hL.ne_zero)

private theorem isWeakSolutionOn_affinePullback_reverse {L : Mat d}
    (hL : IsUnit L.det) {U : Set (Vec d)} (hU : MeasurableSet U)
    (a : CoeffField d) (F : Vec d → Vec d)
    (hsol : IsWeakSolutionOn (affineCoefficient L hL a) (matImage L⁻¹ U)
      (fun y ↦ matVecMul (matTranspose L) (F (matVecMul L y)))) :
    IsWeakSolutionOn a U F := by
  let V : Set (Vec d) := matImage L⁻¹ U
  have hV : MeasurableSet V := measurableSet_affinePullback hL hU
  have hLV : matImage L V = U := matImage_matImage_inv hL U
  intro psi hpsi
  let phi : Vec d → ℝ := fun y ↦ psi (matVecMul L y)
  have hphi : IsLocalTest V phi := isLocalTest_comp_matVecMul hL hpsi
  let p : Vec d → ℝ := fun x ↦
    vecDot (smoothGrad psi x) (matVecMul (a x) (F x))
  let q : Vec d → ℝ := fun y ↦
    vecDot (smoothGrad phi y)
      (matVecMul (affineCoefficient L hL a y)
        (matVecMul (matTranspose L) (F (matVecMul L y))))
  have hpq : ∀ y, q y = p (matVecMul L y) := by
    intro y
    exact affineWeakIntegrand_comp_matVecMul hL a F hpsi.contDiff y
  have hq := hsol phi hphi
  have hpComp : IntegrableOn (fun y ↦ p (matVecMul L y)) V volume := by
    apply hq.1.congr
    filter_upwards with y
    exact hpq y
  have hpImage := (integrableOn_matImage_iff hL hV p).mpr hpComp
  refine ⟨?_, ?_⟩
  · simpa only [hLV, p] using hpImage
  · have hchange := setIntegral_matImage hL hV p
    rw [hLV, smul_eq_mul] at hchange
    have hqzero : ∫ y in V, q y ∂volume = 0 := by simpa only [q] using hq.2
    calc
      ∫ x in U, p x ∂volume =
          |L.det| * ∫ y in V, p (matVecMul L y) ∂volume := hchange
      _ = |L.det| * ∫ y in V, q y ∂volume := by
        congr 1
        exact integral_congr_ae
          (Filter.Eventually.of_forall fun y ↦ (hpq y).symm)
      _ = 0 := by rw [hqzero, mul_zero]

/-- Weak solutions, including integrability of every test pairing, are
equivalent before and after an invertible divergence-form pullback. -/
theorem isWeakSolutionOn_affinePullback_iff {L : Mat d}
    (hL : IsUnit L.det) {U : Set (Vec d)} (hU : MeasurableSet U)
    (a : CoeffField d) (F : Vec d → Vec d) :
    IsWeakSolutionOn a U F ↔
      IsWeakSolutionOn (affineCoefficient L hL a) (matImage L⁻¹ U)
        (fun y ↦ matVecMul (matTranspose L) (F (matVecMul L y))) :=
  ⟨isWeakSolutionOn_affinePullback hL hU a F,
    isWeakSolutionOn_affinePullback_reverse hL hU a F⟩

end

end HighContrast
end HCPolySupport
