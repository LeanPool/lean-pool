/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessPriceAtPrintOrder

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.EnergyPriceEccentricityCollapse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The `Kenergy` collapse and the order-uniform geometric factor

Two arithmetic facts the interface modules need and that nothing else supplies.

**(1) The `Kenergy` collapse.** read off, from the two definitions,
that `gaugeWitnessEnergyPriceW` collapses to a law-free constant times
`E ^ (d + 2s + 2q)`; that reading needs
`lawFreeCubeEnergyConstantW`'s `rpow` squaring unfolded together with the
`gaugeWitnessEnergyPriceW` product regrouping, none of whose definitional lemmas
the energy modules exports."  Both steps are done here.  The squaring is
`(s ^ (−1/2)) ^ 2 = s⁻¹` for `s > 0`, and the window enters through
`Cwit ^ 2 + 1 ≤ (A ^ 2 + 1) · E ^ (2 q)` at `Cwit = A · E ^ q`, `E ≥ 1`.

**(2) The order-uniform geometric factor.**  `witnessGeometricFactor d ρ r`
carries the order `r = responseWindowOrder g`, hence `g`.  The frozen hole fixes
`C₀ : ℝ → ℝ → ℝ → ℝ` **before** `∀ g`, so no `g`-dependent factor may sit in
`C₀`; and `Lg` is chosen before `ρ`, so no `ρ`-dependent factor may sit in `Lg`
either.  The escape is that `witnessGeometricFactor` is bounded, uniformly over
the whole printed order window `r ∈ [0, 1/2]`, by a function of `(d, ρ)` alone —
which is inside `C₀ s₀ ρ Rad`'s permitted dependence.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## (1) The `Kenergy` collapse -/

/-- The law-free cube energy constant, unfolded: the `rpow` squaring is exact. -/
theorem lawFreeCubeEnergyConstantW_eq (C : ℝ) (d : ℕ) {s : ℝ} (hs : 0 < s)
    (Cwit : ℝ) :
    EnergyPrice.lawFreeCubeEnergyConstantW C d s Cwit =
      C ^ 2 * s⁻¹ * (2 * (d : ℝ) * (Cwit ^ 2 + 1)) := by
  have hwin : (0 : ℝ) ≤ EnergyPrice.ellipticityWindow d Cwit :=
    EnergyPrice.ellipticityWindow_nonneg d Cwit
  have hsq : (Real.rpow (EnergyPrice.ellipticityWindow d Cwit) (1 / 2 : ℝ)) ^ 2 =
      EnergyPrice.ellipticityWindow d Cwit := by
    change ((EnergyPrice.ellipticityWindow d Cwit) ^ (1 / 2 : ℝ)) ^ 2 =
      EnergyPrice.ellipticityWindow d Cwit
    rw [← Real.rpow_natCast
      ((EnergyPrice.ellipticityWindow d Cwit) ^ (1 / 2 : ℝ)) 2,
      ← Real.rpow_mul hwin,
      show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by push_cast; ring,
      Real.rpow_one]
  have hs2 : (Real.rpow s (-(1 / 2 : ℝ))) ^ 2 = s⁻¹ := by
    change (s ^ (-(1 / 2 : ℝ))) ^ 2 = s⁻¹
    rw [← Real.rpow_natCast (s ^ (-(1 / 2 : ℝ))) 2,
      ← Real.rpow_mul hs.le,
      show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -(1 : ℝ) by push_cast; ring,
      Real.rpow_neg hs.le, Real.rpow_one]
  rw [EnergyPrice.lawFreeCubeEnergyConstantW, mul_pow, mul_pow, hsq, hs2,
    EnergyPrice.ellipticityWindow]

/-- The law-free part of the collapsed energy price. -/
@[expose]
noncomputable def collapsedEnergyLawFree (C : ℝ) (d : ℕ) (s A : ℝ) : ℝ :=
  C ^ 2 * s⁻¹ * (2 * (d : ℝ) * (A ^ 2 + 1)) *
      BufferToCell.positiveBesovContinuousComparisonConstant d *
    EnergyPrice.gaugeFrameConstant d s

/-- **The `Kenergy` collapse, proved.**  At `Cwit = A · E ^ q` with
`E = max 1 (witnessEccentricity (symmPart abar))`, the windowed gauge energy
price is below a law-free constant times `E ^ (d + 2 s + 2 q)`. -/
theorem gaugeWitnessEnergyPriceW_le_collapsed (C : ℝ) {s A q : ℝ}
    (hs : 0 < s) (hq : 0 ≤ q) (hsd : 0 ≤ (d : ℝ) + 2 * s) (abar : Mat d) :
    EnergyPrice.gaugeWitnessEnergyPriceW C d s
        (A * (max 1 (witnessEccentricity (symmPart abar))) ^ q) abar ≤
      collapsedEnergyLawFree C d s A *
        (max 1 (witnessEccentricity (symmPart abar))) ^
          ((d : ℝ) + 2 * s + 2 * q) := by
  set E : ℝ := max 1 (witnessEccentricity (symmPart abar)) with hE
  have hE1 : (1 : ℝ) ≤ E := le_max_left _ _
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE1
  have hC20 : (0 : ℝ) ≤ C ^ 2 := sq_nonneg C
  have hsinv0 : (0 : ℝ) ≤ s⁻¹ := (inv_pos.mpr hs).le
  have hCbesov0 : (0 : ℝ) ≤
      BufferToCell.positiveBesovContinuousComparisonConstant d :=
    (BufferToCell.positiveBesovContinuousComparisonConstant_pos d).le
  have hframe0 : (0 : ℝ) ≤ EnergyPrice.gaugeFrameConstant d s :=
    EnergyPrice.gaugeFrameConstant_nonneg d s
  have hone2q : (1 : ℝ) ≤ E ^ (2 * q) := by
    have h := Real.rpow_le_rpow (z := 2 * q) zero_le_one hE1
      (by linarith only [hq])
    rwa [Real.one_rpow] at h
  -- the window factor
  have hwindow : (A * E ^ q) ^ 2 + 1 ≤ (A ^ 2 + 1) * E ^ (2 * q) := by
    have hsplit : (A * E ^ q) ^ 2 = A ^ 2 * E ^ (2 * q) := by
      rw [mul_pow, ← Real.rpow_natCast (E ^ q) 2, ← Real.rpow_mul hE0.le]
      congr 2
      push_cast
      ring
    rw [hsplit]
    have hA2 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
    calc A ^ 2 * E ^ (2 * q) + 1 ≤ A ^ 2 * E ^ (2 * q) + E ^ (2 * q) := by
          linarith only [hone2q]
      _ = (A ^ 2 + 1) * E ^ (2 * q) := by ring
  -- the eccentricity factor
  have heccle : witnessEccentricity (symmPart abar) ^ ((d : ℝ) + 2 * s) ≤
      E ^ ((d : ℝ) + 2 * s) :=
    Real.rpow_le_rpow (witnessEccentricity_nonneg _) (le_max_right _ _) hsd
  have hKle : C ^ 2 * s⁻¹ * (2 * (d : ℝ) * ((A * E ^ q) ^ 2 + 1)) ≤
      (C ^ 2 * s⁻¹ * (2 * (d : ℝ) * (A ^ 2 + 1))) * E ^ (2 * q) := by
    have hpre : (0 : ℝ) ≤ C ^ 2 * s⁻¹ * (2 * (d : ℝ)) := by
      have h3 : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
      exact mul_nonneg (mul_nonneg hC20 hsinv0) h3
    have hstep := mul_le_mul_of_nonneg_left hwindow hpre
    calc C ^ 2 * s⁻¹ * (2 * (d : ℝ) * ((A * E ^ q) ^ 2 + 1))
        = C ^ 2 * s⁻¹ * (2 * (d : ℝ)) * ((A * E ^ q) ^ 2 + 1) := by ring
      _ ≤ C ^ 2 * s⁻¹ * (2 * (d : ℝ)) * ((A ^ 2 + 1) * E ^ (2 * q)) := hstep
      _ = (C ^ 2 * s⁻¹ * (2 * (d : ℝ) * (A ^ 2 + 1))) * E ^ (2 * q) := by ring
  have hexp : E ^ (2 * q) * E ^ ((d : ℝ) + 2 * s) =
      E ^ ((d : ℝ) + 2 * s + 2 * q) := by
    rw [← Real.rpow_add hE0]
    congr 1
    ring
  have hb0' : (0 : ℝ) ≤
      (C ^ 2 * s⁻¹ * (2 * (d : ℝ) * (A ^ 2 + 1))) * E ^ (2 * q) *
        BufferToCell.positiveBesovContinuousComparisonConstant d := by
    have h3 : (0 : ℝ) ≤ 2 * (d : ℝ) * (A ^ 2 + 1) := by positivity
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hC20 hsinv0) h3)
        (Real.rpow_nonneg hE0.le _)) hCbesov0
  have hR0 : (0 : ℝ) ≤ EnergyPrice.gaugeFrameConstant d s *
      witnessEccentricity (symmPart abar) ^ ((d : ℝ) + 2 * s) :=
    mul_nonneg hframe0 (Real.rpow_nonneg (witnessEccentricity_nonneg _) _)
  rw [EnergyPrice.gaugeWitnessEnergyPriceW, lawFreeCubeEnergyConstantW_eq C d hs,
    collapsedEnergyLawFree]
  calc C ^ 2 * s⁻¹ * (2 * (d : ℝ) * ((A * E ^ q) ^ 2 + 1)) *
          BufferToCell.positiveBesovContinuousComparisonConstant d *
          (EnergyPrice.gaugeFrameConstant d s *
            witnessEccentricity (symmPart abar) ^ ((d : ℝ) + 2 * s))
      ≤ (C ^ 2 * s⁻¹ * (2 * (d : ℝ) * (A ^ 2 + 1))) * E ^ (2 * q) *
          BufferToCell.positiveBesovContinuousComparisonConstant d *
          (EnergyPrice.gaugeFrameConstant d s * E ^ ((d : ℝ) + 2 * s)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hKle hCbesov0)
          (mul_le_mul_of_nonneg_left heccle hframe0) hR0 hb0'
    _ = C ^ 2 * s⁻¹ * (2 * (d : ℝ) * (A ^ 2 + 1)) *
          BufferToCell.positiveBesovContinuousComparisonConstant d *
          EnergyPrice.gaugeFrameConstant d s *
          (E ^ (2 * q) * E ^ ((d : ℝ) + 2 * s)) := by ring
    _ = C ^ 2 * s⁻¹ * (2 * (d : ℝ) * (A ^ 2 + 1)) *
          BufferToCell.positiveBesovContinuousComparisonConstant d *
          EnergyPrice.gaugeFrameConstant d s *
          E ^ ((d : ℝ) + 2 * s + 2 * q) := by rw [hexp]

/-! ## (2) The order-uniform geometric factor -/

/-- The order-uniform geometric factor: a function of `(d, ρ)` alone. -/
@[expose]
noncomputable def uniformWitnessGeometricFactor (d : ℕ) (rho : ℝ) : ℝ :=
  max 1 ((rho / (3 * Real.sqrt (d : ℝ))) ^ (-(1 / 2 : ℝ)))

theorem one_le_uniformWitnessGeometricFactor (d : ℕ) (rho : ℝ) :
    1 ≤ uniformWitnessGeometricFactor d rho := le_max_left _ _

/-- **The geometric factor is bounded uniformly over the printed order
window.**  `witnessGeometricFactor d ρ r` carries the order `r`, hence `g`; this
bound removes both, at the cost of the worst case `r = 1/2`, and leaves a
function of `(d, ρ)` — exactly `C₀ s₀ ρ Rad`'s permitted dependence. -/
theorem witnessGeometricFactor_le_uniform [NeZero d] {rho r : ℝ}
    (hrho : 0 < rho) (hr : 0 ≤ r) (hrHalf : r ≤ 1 / 2) :
    witnessGeometricFactor d rho r ≤ uniformWitnessGeometricFactor d rho := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hsqrtd : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
    have h := Real.sqrt_le_sqrt hd1
    rwa [Real.sqrt_one] at h
  have hden : (0 : ℝ) < 3 * Real.sqrt (d : ℝ) := by linarith only [hsqrtd]
  have hpos : (0 : ℝ) < rho / (3 * Real.sqrt (d : ℝ)) := div_pos hrho hden
  rw [witnessGeometricFactor, uniformWitnessGeometricFactor]
  rcases le_or_gt (rho / (3 * Real.sqrt (d : ℝ))) 1 with hle1 | hgt1
  · refine le_trans ?_ (le_max_right _ _)
    exact Real.rpow_le_rpow_of_exponent_ge hpos hle1
      (by linarith only [hrHalf])
  · refine le_trans ?_ (le_max_left _ _)
    have hone : (rho / (3 * Real.sqrt (d : ℝ))) ^ (-r) ≤
        (rho / (3 * Real.sqrt (d : ℝ))) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hgt1.le (by linarith only [hr])
    rwa [Real.rpow_zero] at hone

end

end RowSupply
end HighContrast
end HCPolySupport
