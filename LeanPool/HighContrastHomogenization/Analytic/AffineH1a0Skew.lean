/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineH1a0Pairing
public import LeanPool.HighContrastHomogenization.Analytic.TestNorms

/-!
# High-contrast homogenization: Analytic.AffineH1a0Skew

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Skew-flux pairings under affine transport

The divergence-form pullback preserves the skew-flux integrand under the dual
actions on gradients and fluxes.  The determinant Jacobian then controls the
associated coefficient-weighted dual norm.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem matTranspose_smoothGrad_comp_inv {L : Mat d}
    (hL : IsUnit L.det) {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : Vec d) :
    matVecMul (matTranspose L)
        (smoothGrad (fun y ↦ f (matVecMul L⁻¹ y)) x) =
      smoothGrad f (matVecMul L⁻¹ x) := by
  rw [smoothGrad_comp_matVecMul L⁻¹ hf]
  have hLT : IsUnit (matTranspose L).det := by
    simpa [matTranspose] using Matrix.isUnit_det_transpose L hL
  have hinvT : matTranspose L⁻¹ = (matTranspose L)⁻¹ := by
    simpa [matTranspose] using Matrix.transpose_nonsing_inv (A := L)
  rw [hinvT, matVecMul_mul, Matrix.mul_nonsing_inv _ hLT, matVecMul_one]

private theorem affineCoefficient_skew_pairing {L : Mat d}
    (hL : IsUnit L.det) (b : CoeffField d) (y ξ ζ : Vec d) :
    vecDot (matVecMul (matTranspose L) ξ)
        (matVecMul (skewPart (affineCoefficient L hL b y))
          (matVecMul (matTranspose L) ζ)) =
      vecDot ξ (matVecMul (skewPart (b (matVecMul L y))) ζ) := by
  rw [skewPart_affineCoefficient_apply]
  have hflux :
      matVecMul
          (L⁻¹ * skewPart (b (matVecMul L y)) * matTranspose L⁻¹)
          (matVecMul (matTranspose L) ζ) =
        matVecMul L⁻¹ (matVecMul (skewPart (b (matVecMul L y))) ζ) := by
    simpa only [affineCoefficient_apply] using
      affineCoefficient_flux hL (fun x ↦ skewPart (b x)) y ζ
  rw [hflux]
  calc
    vecDot (matVecMul (matTranspose L) ξ)
        (matVecMul L⁻¹ (matVecMul (skewPart (b (matVecMul L y))) ζ)) =
        vecDot (matVecMul L⁻¹ (matVecMul (skewPart (b (matVecMul L y))) ζ))
          (matVecMul (matTranspose L) ξ) := vecDot_comm _ _
    _ = vecDot
          (matVecMul L
            (matVecMul L⁻¹ (matVecMul (skewPart (b (matVecMul L y))) ζ))) ξ :=
      vecDot_matVecMul_transpose _ _ L
    _ = vecDot (matVecMul (skewPart (b (matVecMul L y))) ζ) ξ := by
      rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one]
    _ = vecDot ξ (matVecMul (skewPart (b (matVecMul L y))) ζ) := vecDot_comm _ _

/-- The skew-flux pairing has the exact inverse-determinant Jacobian under
affine pullback. -/
theorem skewFluxPairing_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (b : CoeffField d)
    (F : Vec d → Vec d) {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    skewFluxPairing (affineCoefficient L hL b) (matImage L⁻¹ U)
        (fun y ↦ matVecMul (matTranspose L) (F (matVecMul L y))) f =
      ENNReal.ofReal |L.det|⁻¹ *
        skewFluxPairing b U F (fun x ↦ f (matVecMul L⁻¹ x)) := by
  classical
  let V : Set (Vec d) := matImage L⁻¹ U
  let fL : Vec d → Vec d :=
    fun y ↦ matVecMul (matTranspose L) (F (matVecMul L y))
  let ψ : Vec d → ℝ := fun x ↦ f (matVecMul L⁻¹ x)
  let gL : Vec d → ℝ :=
    fun y ↦ vecDot (smoothGrad f y)
      (matVecMul (skewPart (affineCoefficient L hL b y)) (fL y))
  let g : Vec d → ℝ :=
    fun x ↦ vecDot (smoothGrad ψ x) (matVecMul (skewPart (b x)) (F x))
  have hLinv : IsUnit (L⁻¹).det := Matrix.isUnit_nonsing_inv_det L hL
  have hpoint : ∀ x, gL (matVecMul L⁻¹ x) = g x := by
    intro x
    have hpair := affineCoefficient_skew_pairing hL b (matVecMul L⁻¹ x)
      (smoothGrad ψ x) (F x)
    simpa only [gL, g, fL, ψ, matTranspose_smoothGrad_comp_inv hL hf,
      matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one] using hpair
  have hint : IntegrableOn gL V volume ↔ IntegrableOn g U volume := by
    have h := integrableOn_matImage_iff hLinv hU gL
    rw [show matImage L⁻¹ U = V by rfl] at h
    simpa only [hpoint] using h
  have hchange : ∫ y in V, gL y ∂volume = |L.det|⁻¹ * ∫ x in U, g x ∂volume := by
    have h := setIntegral_matImage hLinv hU gL
    rw [show matImage L⁻¹ U = V by rfl] at h
    simp_rw [hpoint] at h
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', abs_inv] at h
    simpa only [smul_eq_mul] using h
  unfold skewFluxPairing
  change (if IntegrableOn gL V volume then ENNReal.ofReal (∫ y in V, gL y ∂volume)
      else ⊤) = ENNReal.ofReal |L.det|⁻¹ *
        (if IntegrableOn g U volume then ENNReal.ofReal (∫ x in U, g x ∂volume)
          else ⊤)
  by_cases hg : IntegrableOn g U volume
  · rw [ite_eq_left (hint.mpr hg), ite_eq_left hg, hchange,
      ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg L.det))]
  · rw [ite_eq_right (mt hint.mp hg), ite_eq_right hg]
    exact (ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr
      (inv_pos.mpr (abs_pos.mpr hL.ne_zero)))).symm

private theorem affineCoefficient_inv_affineCoefficient {L : Mat d}
    (hL : IsUnit L.det) (b : CoeffField d) (x : Vec d) :
    affineCoefficient L⁻¹ (Matrix.isUnit_nonsing_inv_det L hL)
        (affineCoefficient L hL b) x = b x := by
  rw [affineCoefficient_apply, affineCoefficient_apply,
    Matrix.nonsing_inv_nonsing_inv L hL]
  have hLT : IsUnit (matTranspose L).det := by
    simpa [matTranspose] using Matrix.isUnit_det_transpose L hL
  have hinvT : matTranspose L⁻¹ = (matTranspose L)⁻¹ := by
    simpa [matTranspose] using Matrix.transpose_nonsing_inv (A := L)
  rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one, hinvT,
    ← Matrix.mul_assoc L (L⁻¹ * b x) (matTranspose L)⁻¹,
    ← Matrix.mul_assoc L L⁻¹ (b x),
    Matrix.mul_assoc ((L * L⁻¹) * b x) (matTranspose L)⁻¹ (matTranspose L),
    Matrix.nonsing_inv_mul _ hLT, Matrix.mul_one, Matrix.mul_nonsing_inv L hL,
    Matrix.one_mul]

/-- Pulling a field from the affine domain back to the original domain costs
the maximum of the value and energy Jacobian factors. -/
theorem h1sNormSqOn_affinePushforward_le {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (b : CoeffField d)
    (f : Vec d → ℝ) (Df : Vec d → Vec d) :
    h1sNormSqOn b U (fun x ↦ f (matVecMul L⁻¹ x))
        (fun x ↦ matVecMul (matTranspose L⁻¹) (Df (matVecMul L⁻¹ x))) ≤
      max ((ENNReal.ofReal |L.det|) ^ 2) (ENNReal.ofReal |L.det|) *
        h1sNormSqOn (affineCoefficient L hL b) (matImage L⁻¹ U) f Df := by
  have hLinv : IsUnit (L⁻¹).det := Matrix.isUnit_nonsing_inv_det L hL
  have hV : MeasurableSet (matImage L⁻¹ U) := measurableSet_affinePullback hL hU
  have hcoeff :
      affineCoefficient L⁻¹ hLinv (affineCoefficient L hL b) = b := by
    funext x
    exact affineCoefficient_inv_affineCoefficient hL b x
  have hdet : ENNReal.ofReal |(L⁻¹).det|⁻¹ = ENNReal.ofReal |L.det| := by
    congr 1
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', abs_inv, inv_inv]
  have h := h1sNormSqOn_affinePullback_le hLinv hV
    (affineCoefficient L hL b) f Df
  rw [Matrix.nonsing_inv_nonsing_inv L hL, matImage_matImage_inv hL,
    hcoeff, hdet] at h
  exact h

private theorem sEnergyOn_const_smul (b : CoeffField d) (U : Set (Vec d))
    (c : ℝ) (F : Vec d → Vec d) :
    sEnergyOn b U (fun x ↦ c • F x) =
      ENNReal.ofReal (c ^ 2) * sEnergyOn b U F := by
  unfold sEnergyOn
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (sq_nonneg c), matVecMul_smul,
    vecDot_smul_left, vecDot_smul_right]
  congr 1
  ring

private theorem h1sNormSqOn_const_mul (b : CoeffField d) (U : Set (Vec d))
    {c : ℝ} (hc : 0 ≤ c) (u : Vec d → ℝ) (Du : Vec d → Vec d) :
    h1sNormSqOn b U (fun x ↦ c * u x) (fun x ↦ c • Du x) =
      ENNReal.ofReal (c ^ 2) * h1sNormSqOn b U u Du := by
  have hL1 : (∫⁻ x in U, ENNReal.ofReal |c * u x| ∂volume) =
      ENNReal.ofReal c * ∫⁻ x in U, ENNReal.ofReal |u x| ∂volume := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x
    rw [abs_mul, abs_of_nonneg hc, ENNReal.ofReal_mul hc]
  unfold h1sNormSqOn
  rw [hL1, sEnergyOn_const_smul, mul_pow, ← ENNReal.ofReal_pow hc 2, mul_add]

private theorem isLocalTest_const_mul {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : IsLocalTest U f) (c : ℝ) : IsLocalTest U (fun x ↦ c * f x) := by
  refine ⟨contDiff_const.mul hf.contDiff, ?_, ?_⟩
  · simpa [Pi.smul_apply, smul_eq_mul] using!
      hf.hasCompactSupport.smul_left (f := fun _ : Vec d ↦ c)
  · simpa [Pi.smul_apply, smul_eq_mul] using
      (tsupport_smul_subset_right (fun _ : Vec d ↦ c) f).trans hf.tsupport_subset

private theorem skewFluxPairing_const_mul {b : CoeffField d} {U : Set (Vec d)}
    (F : Vec d → Vec d) {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {c : ℝ} (hc : 0 < c) :
    skewFluxPairing b U F (fun x ↦ c * f x) =
      ENNReal.ofReal c * skewFluxPairing b U F f := by
  classical
  let g : Vec d → ℝ :=
    fun x ↦ vecDot (smoothGrad f x) (matVecMul (skewPart (b x)) (F x))
  have hpoint : ∀ x,
      vecDot (smoothGrad (fun y ↦ c * f y) x)
          (matVecMul (skewPart (b x)) (F x)) = c * g x := by
    intro x
    rw [smoothGrad_const_mul (hf.differentiable (by simp)) c, vecDot_smul_left]
  have hint : IntegrableOn (fun x ↦ c * g x) U volume ↔
      IntegrableOn g U volume :=
    integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc.ne') g
  unfold skewFluxPairing
  simp_rw [hpoint]
  by_cases hg : IntegrableOn g U volume
  · rw [ite_eq_left (hint.mpr hg), ite_eq_left hg, integral_const_mul,
      ENNReal.ofReal_mul hc.le]
  · rw [ite_eq_right (mt hint.mp hg), ite_eq_right hg]
    exact (ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hc)).symm

/-- The affine pullback of a skew flux is controlled in its weighted dual norm
by a finite determinant factor. -/
theorem skewFluxDualNorm_affinePullback_le {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (b : CoeffField d)
    (F : Vec d → Vec d) :
    skewFluxDualNorm (affineCoefficient L hL b) (matImage L⁻¹ U)
        (fun y ↦ matVecMul (matTranspose L) (F (matVecMul L y))) ≤
      ENNReal.ofReal (|L.det|⁻¹ * max |L.det| 1) * skewFluxDualNorm b U F := by
  classical
  let D : ℝ := |L.det|
  let q : ℝ := max D 1
  have hD : 0 < D := abs_pos.mpr hL.ne_zero
  have hq : 0 < q := lt_of_lt_of_le zero_lt_one (le_max_right D 1)
  have hDq : D ≤ q := le_max_left D 1
  have hq1 : 1 ≤ q := le_max_right D 1
  have hDsq : D ^ 2 ≤ q ^ 2 := by gcongr
  have hDqsq : D ≤ q ^ 2 := by
    calc D ≤ q := hDq
      _ ≤ q ^ 2 := by nlinarith only [hq1]
  have hK : max ((ENNReal.ofReal D) ^ 2) (ENNReal.ofReal D) ≤
      ENNReal.ofReal (q ^ 2) := by
    refine max_le ?_ ?_
    · rw [← ENNReal.ofReal_pow hD.le 2]
      exact ENNReal.ofReal_le_ofReal hDsq
    · exact ENNReal.ofReal_le_ofReal hDqsq
  change skewFluxDualNorm (affineCoefficient L hL b) (matImage L⁻¹ U)
      (fun y ↦ matVecMul (matTranspose L) (F (matVecMul L y))) ≤
    ENNReal.ofReal (D⁻¹ * q) * skewFluxDualNorm b U F
  unfold skewFluxDualNorm
  refine iSup_le fun f ↦ ?_
  let ψ : Vec d → ℝ := fun x ↦ f.1 (matVecMul L⁻¹ x)
  have hψtest : IsLocalTest U ψ := isLocalTest_comp_matVecMul_inv hL f.2.1
  have hgrad :
      (fun x ↦ matVecMul (matTranspose L⁻¹)
        (smoothGrad f.1 (matVecMul L⁻¹ x))) = smoothGrad ψ := by
    funext x
    exact (smoothGrad_comp_matVecMul L⁻¹ f.2.1.contDiff x).symm
  have hrev := h1sNormSqOn_affinePushforward_le hL hU b f.1 (smoothGrad f.1)
  rw [hgrad] at hrev
  have hψnorm : h1sNormSqOn b U ψ (smoothGrad ψ) ≤ ENNReal.ofReal (q ^ 2) :=
    hrev.trans <| calc
      max ((ENNReal.ofReal D) ^ 2) (ENNReal.ofReal D) *
          h1sNormSqOn (affineCoefficient L hL b) (matImage L⁻¹ U) f.1
            (smoothGrad f.1) ≤
          max ((ENNReal.ofReal D) ^ 2) (ENNReal.ofReal D) * 1 := by
        gcongr
        exact f.2.2
      _ = max ((ENNReal.ofReal D) ^ 2) (ENNReal.ofReal D) := mul_one _
      _ ≤ ENNReal.ofReal (q ^ 2) := hK
  let c : ℝ := q⁻¹
  have hc : 0 < c := inv_pos.mpr hq
  have hcq : c ^ 2 * q ^ 2 = 1 := by
    dsimp [c]
    field_simp
  have hgradc : (fun x ↦ c • smoothGrad ψ x) =
      smoothGrad (fun x ↦ c * ψ x) := by
    funext x
    exact (smoothGrad_const_mul (hψtest.contDiff.differentiable (by simp)) c x).symm
  have hscaled :
      h1sNormSqOn b U (fun x ↦ c * ψ x)
          (smoothGrad (fun x ↦ c * ψ x)) ≤ 1 := by
    rw [← hgradc, h1sNormSqOn_const_mul b U hc.le]
    calc
      ENNReal.ofReal (c ^ 2) * h1sNormSqOn b U ψ (smoothGrad ψ) ≤
          ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (q ^ 2) := by gcongr
      _ = ENNReal.ofReal (c ^ 2 * q ^ 2) :=
        (ENNReal.ofReal_mul (sq_nonneg c)).symm
      _ = 1 := by rw [hcq, ENNReal.ofReal_one]
  let fscaled : {f : Vec d → ℝ //
      IsLocalTest U f ∧ h1sNormSqOn b U f (smoothGrad f) ≤ 1} :=
    ⟨fun x ↦ c * ψ x, isLocalTest_const_mul hψtest c, hscaled⟩
  have hsup : skewFluxPairing b U F fscaled.1 ≤
      ⨆ f : {f : Vec d → ℝ //
        IsLocalTest U f ∧ h1sNormSqOn b U f (smoothGrad f) ≤ 1},
        skewFluxPairing b U F f.1 :=
    le_iSup (fun f : {f : Vec d → ℝ //
      IsLocalTest U f ∧ h1sNormSqOn b U f (smoothGrad f) ≤ 1} ↦
        skewFluxPairing b U F f.1) fscaled
  have hscale := skewFluxPairing_const_mul (b := b) (U := U) F hψtest.contDiff hc
  have hqc : ENNReal.ofReal q * ENNReal.ofReal c = 1 := by
    rw [← ENNReal.ofReal_mul hq.le]
    have : q * c = 1 := by
      dsimp [c]
      exact mul_inv_cancel₀ hq.ne'
    rw [this, ENNReal.ofReal_one]
  have hpair : skewFluxPairing b U F ψ ≤
      ENNReal.ofReal q *
        ⨆ f : {f : Vec d → ℝ //
          IsLocalTest U f ∧ h1sNormSqOn b U f (smoothGrad f) ≤ 1},
          skewFluxPairing b U F f.1 := by
    calc
      skewFluxPairing b U F ψ =
          ENNReal.ofReal q * (ENNReal.ofReal c * skewFluxPairing b U F ψ) := by
        rw [← mul_assoc, hqc, one_mul]
      _ = ENNReal.ofReal q * skewFluxPairing b U F fscaled.1 := by rw [hscale]
      _ ≤ ENNReal.ofReal q *
          ⨆ f : {f : Vec d → ℝ //
            IsLocalTest U f ∧ h1sNormSqOn b U f (smoothGrad f) ≤ 1},
            skewFluxPairing b U F f.1 := by gcongr
  rw [skewFluxPairing_affinePullback hL hU b F f.2.1.contDiff]
  calc
    ENNReal.ofReal D⁻¹ * skewFluxPairing b U F ψ ≤
        ENNReal.ofReal D⁻¹ * (ENNReal.ofReal q *
          ⨆ f : {f : Vec d → ℝ //
            IsLocalTest U f ∧ h1sNormSqOn b U f (smoothGrad f) ≤ 1},
            skewFluxPairing b U F f.1) := by gcongr
    _ = ENNReal.ofReal (D⁻¹ * q) *
          ⨆ f : {f : Vec d → ℝ //
            IsLocalTest U f ∧ h1sNormSqOn b U f (smoothGrad f) ≤ 1},
            skewFluxPairing b U F f.1 := by
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr hD.le)]
      ac_rfl

end

end HighContrast
end HCPolySupport
