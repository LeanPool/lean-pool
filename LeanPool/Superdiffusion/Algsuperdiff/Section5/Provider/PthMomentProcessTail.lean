/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.PthMomentProcessScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.PthMoment

/-!
# PthMomentProcessTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Moment integration from a restricted triadic displacement tail

The displacement comparison is available at triadic radii no smaller than the normalization
scale.  This file interpolates that restricted family to a continuous exponential tail and then
integrates it.  The bounded-probability branch handles all smaller radii.
-/

namespace Algsuperdiff.Section5.Provider

open MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

private theorem one_le_mul_max_inv_sq {x : ℝ} (hx : 0 < x) :
    1 ≤ x * (max 1 x⁻¹) ^ (2 : ℕ) := by
  rcases le_total x 1 with hx1 | h1x
  · have hinv : 1 ≤ x⁻¹ := by
      rw [← one_div]
      exact (le_div_iff₀ hx).2 (by simpa using hx1)
    have hmax : max 1 x⁻¹ = x⁻¹ := max_eq_right hinv
    rw [hmax, pow_two]
    field_simp
    exact hx1
  · calc
      1 ≤ x := h1x
      _ = x * 1 ^ (2 : ℕ) := by ring
      _ ≤ x * (max 1 x⁻¹) ^ (2 : ℕ) := by
        gcongr
        exact le_max_left _ _

/-- A square-exponential tail at every triadic radius gives the normalized
exponential tail used by the moment integrator.  The explicit enlargement
factor pays only for interpolation between adjacent powers of three and for
the bounded-probability range below `log 2`. -/
theorem measureReal_lt_div_le_two_mul_exp_neg_of_triadic_sq_tail
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {Z : Omega → ℝ} {R c : ℝ} (hR : 0 < R) (hc : 0 < c) (hc1 : c ≤ 1)
    (htail : ∀ k : ℤ,
      R ≤ (3 : ℝ) ^ k →
      mu.real {omega | (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ Z omega} ≤
        Real.exp (-c * (((3 : ℝ) ^ k / R) ^ (2 : ℕ)))) :
    let A := (3 / 2 : ℝ) * max 1 (c * Real.log 2)⁻¹
    ∀ s : ℝ, 0 < s →
      mu.real {omega | s < Z omega / (A * R)} ≤ 2 * Real.exp (-s) := by
  let B : ℝ := max 1 (c * Real.log 2)⁻¹
  let A : ℝ := (3 / 2 : ℝ) * B
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : 0 < c * Real.log 2 := mul_pos hc hlog
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hA : 0 < A := mul_pos (by norm_num) hB
  change ∀ s : ℝ, 0 < s →
      mu.real {omega | s < Z omega / (A * R)} ≤ 2 * Real.exp (-s)
  intro s hs
  by_cases hslog : s ≤ Real.log 2
  · have hprob : mu.real {omega | s < Z omega / (A * R)} ≤ 1 :=
      measureReal_le_one
    have hexp : (1 / 2 : ℝ) ≤ Real.exp (-s) := by
      calc
        (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          norm_num
        _ ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith only [hslog])
    exact hprob.trans (by linarith only [hexp])
  · have hslog' : Real.log 2 < s := lt_of_not_ge hslog
    have hv : 0 < 2 * A * R * s := by positivity
    obtain ⟨k, hkLower, hkUpper⟩ :=
      Algsuperdiff.Section5.Support.exists_auxiliaryScale hv
    have hthreshold : (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ A * R * s := by
      calc
        (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤
            (1 / 2 : ℝ) * (2 * A * R * s) :=
          mul_le_mul_of_nonneg_left hkLower (by norm_num)
        _ = A * R * s := by ring
    have hsubset : {omega | s < Z omega / (A * R)} ⊆
        {omega | (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ Z omega} := by
      intro omega homega
      have hAR : 0 < A * R := mul_pos hA hR
      change s < Z omega / (A * R) at homega
      have hZ : A * R * s < Z omega := by
        have := (lt_div_iff₀ hAR).mp homega
        simpa only [mul_comm] using this
      exact (hthreshold.trans_lt hZ).le
    have hkUpper' : 2 * A * R * s < 3 * (3 : ℝ) ^ k := by
      simpa only [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one, mul_comm] using
        hkUpper
    have hratio : B * s < (3 : ℝ) ^ k / R := by
      have hrewrite : 2 * A * R * s = 3 * (B * s) * R := by
        dsimp only [A]
        ring
      rw [hrewrite] at hkUpper'
      have hthree : 0 < (3 : ℝ) := by norm_num
      have hcancel : B * s * R < (3 : ℝ) ^ k := by
        linarith only [hkUpper']
      exact (lt_div_iff₀ hR).2 hcancel
    have htailRange : R ≤ (3 : ℝ) ^ k := by
      have hinvB : (c * Real.log 2)⁻¹ ≤ B := le_max_right _ _
      have hinvPos : 0 < (c * Real.log 2)⁻¹ := inv_pos.mpr hx
      have hprod : (c * Real.log 2)⁻¹ * Real.log 2 < B * s := by
        calc
          (c * Real.log 2)⁻¹ * Real.log 2 <
              (c * Real.log 2)⁻¹ * s :=
            mul_lt_mul_of_pos_left hslog' hinvPos
          _ ≤ B * s := mul_le_mul_of_nonneg_right hinvB hs.le
      have hone : 1 ≤ (c * Real.log 2)⁻¹ * Real.log 2 := by
        have heq : (c * Real.log 2)⁻¹ * Real.log 2 = c⁻¹ := by
          field_simp
        rw [heq]
        have hinv : (1 : ℝ) ≤ 1 / c := by
          rw [le_div_iff₀ hc]
          simpa only [one_mul] using hc1
        simpa only [one_div] using hinv
      have hratioOne : 1 < (3 : ℝ) ^ k / R := hone.trans_lt (hprod.trans hratio)
      simpa only [one_mul] using (le_div_iff₀ hR).mp hratioOne.le
    have hcore : 1 ≤ c * B ^ (2 : ℕ) * s := by
      have hxB := one_le_mul_max_inv_sq hx
      change 1 ≤ c * (max 1 (c * Real.log 2)⁻¹) ^ (2 : ℕ) * s
      calc
        1 ≤ (c * Real.log 2) * (max 1 (c * Real.log 2)⁻¹) ^ (2 : ℕ) := hxB
        _ = c * (max 1 (c * Real.log 2)⁻¹) ^ (2 : ℕ) * Real.log 2 := by ring
        _ ≤ c * (max 1 (c * Real.log 2)⁻¹) ^ (2 : ℕ) * s := by
          have hcB : 0 ≤ c * (max 1 (c * Real.log 2)⁻¹) ^ (2 : ℕ) := by positivity
          exact mul_le_mul_of_nonneg_left hslog'.le hcB
    have hexponent : s ≤ c * (((3 : ℝ) ^ k / R) ^ (2 : ℕ)) := by
      have hs0 : 0 ≤ s := hs.le
      have hsq : (B * s) ^ (2 : ℕ) ≤ (((3 : ℝ) ^ k / R) ^ (2 : ℕ)) :=
        pow_le_pow_left₀ (mul_nonneg hB.le hs0) hratio.le 2
      calc
        s = 1 * s := (one_mul s).symm
        _ ≤ (c * B ^ (2 : ℕ) * s) * s :=
          mul_le_mul_of_nonneg_right hcore hs0
        _ = c * (B * s) ^ (2 : ℕ) := by ring
        _ ≤ c * (((3 : ℝ) ^ k / R) ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hsq hc.le
    calc
      mu.real {omega | s < Z omega / (A * R)} ≤
          mu.real {omega | (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ Z omega} :=
        measureReal_mono hsubset
      _ ≤ Real.exp (-c * (((3 : ℝ) ^ k / R) ^ (2 : ℕ))) := htail k htailRange
      _ ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith only [hexponent])
      _ ≤ 2 * Real.exp (-s) := by
        exact le_mul_of_one_le_left (Real.exp_nonneg _) (by norm_num)

/-- The C2 integration step from a triadic square-exponential tail. -/
theorem integral_rpow_le_of_triadic_sq_tail
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {Z : Omega → ℝ} (hZ : AEMeasurable Z mu) (hZ0 : 0 ≤ᵐ[mu] Z)
    {R c p : ℝ} (hR : 0 < R) (hc : 0 < c) (hc1 : c ≤ 1) (hp : 1 ≤ p)
    (htail : ∀ k : ℤ,
      R ≤ (3 : ℝ) ^ k →
      mu.real {omega | (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ Z omega} ≤
        Real.exp (-c * (((3 : ℝ) ^ k / R) ^ (2 : ℕ)))) :
    let A := (3 / 2 : ℝ) * max 1 (c * Real.log 2)⁻¹
    Integrable (fun omega => Z omega ^ p) mu ∧
      ∫ omega, Z omega ^ p ∂mu ≤ (6 * p * (A * R)) ^ p := by
  let A : ℝ := (3 / 2 : ℝ) * max 1 (c * Real.log 2)⁻¹
  have hA : 0 < A := mul_pos (by norm_num)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  let W : Omega → ℝ := fun omega => Z omega / (A * R)
  have hW : AEMeasurable W mu := hZ.div_const _
  have hW0 : 0 ≤ᵐ[mu] W := by
    filter_upwards [hZ0] with omega homega
    exact div_nonneg homega (mul_nonneg hA.le hR.le)
  have hWtail := measureReal_lt_div_le_two_mul_exp_neg_of_triadic_sq_tail
    mu hR hc hc1 htail
  obtain ⟨hWint, hWmoment⟩ := integral_rpow_le_of_exp_tail mu hW hW0 hWtail hp
  have hscale : ∀ᵐ omega ∂mu, Z omega ^ p = (A * R) ^ p * W omega ^ p := by
    filter_upwards [hZ0] with omega homega
    rw [← Real.mul_rpow (mul_nonneg hA.le hR.le)
      (div_nonneg homega (mul_nonneg hA.le hR.le))]
    congr 2
    exact (mul_div_cancel₀ (Z omega) (mul_ne_zero hA.ne' hR.ne')).symm
  have hscaled : Integrable (fun omega => (A * R) ^ p * W omega ^ p) mu :=
    hWint.const_mul _
  refine ⟨?_, ?_⟩
  · refine hscaled.congr ?_
    filter_upwards [hscale] with omega homega
    exact homega.symm
  · rw [integral_congr_ae hscale, integral_const_mul]
    calc
      (A * R) ^ p * ∫ omega, W omega ^ p ∂mu ≤
          (A * R) ^ p * (6 * p) ^ p :=
        mul_le_mul_of_nonneg_left hWmoment (Real.rpow_nonneg (by positivity) _)
      _ = (6 * p * (A * R)) ^ p := by
        rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 6 * p)
          (mul_nonneg hA.le hR.le)]
        ring

end

end Algsuperdiff.Section5.Provider
