/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessHeadBound

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.FrozenHeadClassSplit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# (ii), part two: the head constant, split into the `C₀`, fold and `Lg` classes

that module discharges the `hhead` premise at `frozenWitnessHeadConstant`, which still
carries `abar` (through the output factor's fold) and `(g, κ)` (through
`fluxLgFactor` and the amplitude's `Lg` half).  The clause permits `abar` only
in `pEcc` and `(g, κ)` only in `Lg`, so the constant must be split.

This module performs that split, at the `KenergyBound` that module + that module
produce:

```
frozenWitnessHeadConstant … (collapsedEnergyLawFree C d s (AC0 · ALg) · E^(d+2s+2q)) abar
  ≤ frozenHeadC0Factor C d s ρ Rad cnorm Cdual hardyReal
      · E ^ (d + 1 + q)
      · frozenHeadLgFactor d g κ
```

with `E := max 1 (witnessEccentricity (symmPart abar))` and
`q := witnessErrorEccentricityExponent g κ`.  Three facts do the work:

* `collapsedEnergyLawFree_mul_split` — `A ↦ C² s⁻¹ (2d(A²+1)) · …` is
  submultiplicative in the split amplitude, because
  `(AC0·ALg)² + 1 ≤ (AC0²+1)(ALg²+1)`;
* the order trim `d + 2s + 2q ≤ d + 1 + 2q`, from `s < 1/2` — the same trim
  that module and that module use, and the reason `pEcc` may be `(d, g, κ)`-level;
* `(d+1)/2 + (d+1+2q)/2 = d + 1 + q`, which is exactly's
  "`pEcc` = the sum of the rate-leg and energy-leg exponents".
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Nonnegativity of the two flux classes -/

theorem fluxC0Factor_nonneg (d : ℕ) [NeZero d] {s₀ : ℝ} (hs₀ : 0 < s₀)
    (Rad cnorm : ℝ) : 0 ≤ fluxC0Factor d s₀ Rad cnorm := by
  have hflux0 : (0 : ℝ) ≤ coarseFluxResponseConstant d := by
    rw [coarseFluxResponseConstant]
    exact mul_nonneg (by positivity) (le_trans zero_le_one (le_max_left _ _))
  have hnorm0 : (0 : ℝ) ≤
      Book.Ch03.constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) := by
    rw [Book.Ch03.constantCoeffMatrixNormHalf]
    exact Real.rpow_nonneg (Book.Ch02.matrixNorm_nonneg _) _
  have hm1 : (0 : ℝ) ≤ max 1 ((2 * Rad) ^ (1 / 2 : ℝ)) :=
    le_trans zero_le_one (le_max_left _ _)
  have hm2 : (0 : ℝ) ≤ 3 * max 1 ((1 + 3 * (2 * Rad)) ^ (1 / 2 : ℝ)) := by
    have h : (1 : ℝ) ≤ max 1 ((1 + 3 * (2 * Rad)) ^ (1 / 2 : ℝ)) :=
      le_max_left _ _
    linarith only [h]
  have hm3 : (0 : ℝ) ≤ max 1 ((Rad / cnorm) ^ (1 / 2 : ℝ)) :=
    le_trans zero_le_one (le_max_left _ _)
  rw [fluxC0Factor]
  exact mul_nonneg (mul_nonneg hm1 hm2)
    (mul_nonneg (mul_nonneg (mul_nonneg hflux0 (inv_nonneg.mpr hs₀.le)) hnorm0)
      hm3)

theorem fluxLgFactor_nonneg (d : ℕ) [NeZero d] (g kappaRate : ℝ) :
    0 ≤ fluxLgFactor d g kappaRate := by
  rw [fluxLgFactor]
  exact mul_nonneg
    (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    (mul_nonneg (foldedResponseFillingConstant_nonneg d g)
      (activationFoldConstant_nonneg d g kappaRate _))

/-! ## The collapsed constant -/

theorem collapsedEnergyLawFree_nonneg (C : ℝ) (d : ℕ) [NeZero d] {s : ℝ}
    (hs : 0 < s) (A : ℝ) : 0 ≤ collapsedEnergyLawFree C d s A := by
  have hCbesov0 : (0 : ℝ) ≤
      BufferToCell.positiveBesovContinuousComparisonConstant d :=
    (BufferToCell.positiveBesovContinuousComparisonConstant_pos d).le
  have hframe0 : (0 : ℝ) ≤ EnergyPrice.gaugeFrameConstant d s :=
    EnergyPrice.gaugeFrameConstant_nonneg d s
  have hd0 : (0 : ℝ) ≤ 2 * (d : ℝ) * (A ^ 2 + 1) := by positivity
  rw [collapsedEnergyLawFree]
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (sq_nonneg C) (inv_nonneg.mpr hs.le)) hd0) hCbesov0) hframe0

/-- **The collapsed law-free constant splits multiplicatively.** -/
theorem collapsedEnergyLawFree_mul_split (C : ℝ) (d : ℕ) [NeZero d] {s : ℝ}
    (hs : 0 < s) (A B : ℝ) :
    collapsedEnergyLawFree C d s (A * B) ≤
      collapsedEnergyLawFree C d s A * (B ^ 2 + 1) := by
  have hCbesov0 : (0 : ℝ) ≤
      BufferToCell.positiveBesovContinuousComparisonConstant d :=
    (BufferToCell.positiveBesovContinuousComparisonConstant_pos d).le
  have hframe0 : (0 : ℝ) ≤ EnergyPrice.gaugeFrameConstant d s :=
    EnergyPrice.gaugeFrameConstant_nonneg d s
  have hhead0 : (0 : ℝ) ≤ C ^ 2 * s⁻¹ :=
    mul_nonneg (sq_nonneg C) (inv_nonneg.mpr hs.le)
  have hd0 : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
  have hkey : (A * B) ^ 2 + 1 ≤ (A ^ 2 + 1) * (B ^ 2 + 1) := by
    have h1 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
    have h2 : (0 : ℝ) ≤ B ^ 2 := sq_nonneg B
    have hexp : (A ^ 2 + 1) * (B ^ 2 + 1) =
        A ^ 2 * B ^ 2 + A ^ 2 + B ^ 2 + 1 := by ring
    have hlhs : (A * B) ^ 2 + 1 = A ^ 2 * B ^ 2 + 1 := by ring
    rw [hexp, hlhs]
    linarith only [h1, h2]
  have hstep : C ^ 2 * s⁻¹ * (2 * (d : ℝ) * ((A * B) ^ 2 + 1)) ≤
      C ^ 2 * s⁻¹ * (2 * (d : ℝ) * ((A ^ 2 + 1) * (B ^ 2 + 1))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey hd0) hhead0
  have hfull : C ^ 2 * s⁻¹ * (2 * (d : ℝ) * ((A * B) ^ 2 + 1)) *
        BufferToCell.positiveBesovContinuousComparisonConstant d *
        EnergyPrice.gaugeFrameConstant d s ≤
      C ^ 2 * s⁻¹ * (2 * (d : ℝ) * ((A ^ 2 + 1) * (B ^ 2 + 1))) *
        BufferToCell.positiveBesovContinuousComparisonConstant d *
        EnergyPrice.gaugeFrameConstant d s :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hstep hCbesov0) hframe0
  rw [collapsedEnergyLawFree, collapsedEnergyLawFree]
  refine hfull.trans (le_of_eq ?_)
  ring

/-! ## A square root of a power -/

theorem sqrt_rpow_eq {E : ℝ} (hE : 0 ≤ E) (t : ℝ) :
    Real.sqrt (E ^ t) = E ^ (t / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hE]
  congr 1
  ring

/-! ## The three classes of the head constant -/

/-- The `C₀`-slot class of the head constant: `(d, s, ρ, Rad, cnorm)`-level. -/
@[expose]
noncomputable def frozenHeadC0Factor (C : ℝ) (d : ℕ) [NeZero d]
    (s rho Rad cnorm Cdual hardyReal : ℝ) : ℝ :=
  gaugeOutputLawFree d s rho * Cdual *
    (2 * ((fractionalDualToBesovConstant d).toReal *
      (fluxC0Factor d s Rad cnorm *
          Real.sqrt (collapsedEnergyLawFree C d s
            (witnessAmplitudeC0Factor d rho Rad)) *
        Real.sqrt hardyReal)))

/-- The `Lg`-slot class of the head constant: `(d, g, κ)`-level. -/
@[expose]
noncomputable def frozenHeadLgFactor (d : ℕ) [NeZero d] (g kappaRate : ℝ) : ℝ :=
  fluxLgFactor d g kappaRate *
    Real.sqrt (witnessAmplitudeLgFactor d g kappaRate ^ 2 + 1)

theorem frozenHeadLgFactor_nonneg (d : ℕ) [NeZero d] (g kappaRate : ℝ) :
    0 ≤ frozenHeadLgFactor d g kappaRate :=
  mul_nonneg (fluxLgFactor_nonneg d g kappaRate) (Real.sqrt_nonneg _)

/-- The monotone slot of the head constant. -/
theorem headSlot_mono {X Cb F v w hr : ℝ}
    (hvw : v ≤ w) (hX0 : 0 ≤ X) (hCb0 : 0 ≤ Cb) (hF0 : 0 ≤ F)
    (hhr0 : 0 ≤ hr) :
    X * (2 * (Cb * (F * v * hr))) ≤ X * (2 * (Cb * (F * w * hr))) := by
  have h1 : F * v ≤ F * w := mul_le_mul_of_nonneg_left hvw hF0
  have h2 : F * v * hr ≤ F * w * hr := mul_le_mul_of_nonneg_right h1 hhr0
  have h3 : Cb * (F * v * hr) ≤ Cb * (F * w * hr) :=
    mul_le_mul_of_nonneg_left h2 hCb0
  have h4 : 2 * (Cb * (F * v * hr)) ≤ 2 * (Cb * (F * w * hr)) := by
    linarith only [h3]
  exact mul_le_mul_of_nonneg_left h4 hX0

/-! ## The split -/

/-- **(ii), part two.**  The head constant from the modules named above, at the `KenergyBound`
from the modules named above, is below the product of its `C₀` class, a fixed eccentricity power,
and its `Lg` class. -/
theorem frozenWitnessHeadConstant_le_classes (C : ℝ) [NeZero d]
    {g kappaRate s rho Rad cnorm Cdual hardyReal : ℝ} {abar : Mat d}
    (hs : 0 < s) (hsHalf : s ≤ 1 / 2) (hCdual : 0 ≤ Cdual) :
    frozenWitnessHeadConstant d g kappaRate s rho Rad cnorm Cdual hardyReal
        (collapsedEnergyLawFree C d s
            (witnessAmplitudeC0Factor d rho Rad *
              witnessAmplitudeLgFactor d g kappaRate) *
          (max 1 (witnessEccentricity (symmPart abar))) ^
            ((d : ℝ) + 2 * s +
              2 * witnessErrorEccentricityExponent g kappaRate)) abar ≤
      frozenHeadC0Factor C d s rho Rad cnorm Cdual hardyReal *
          (max 1 (witnessEccentricity (symmPart abar))) ^
            ((d : ℝ) + 1 + witnessErrorEccentricityExponent g kappaRate) *
        frozenHeadLgFactor d g kappaRate := by
  set E : ℝ := max 1 (witnessEccentricity (symmPart abar)) with hEdef
  set q : ℝ := witnessErrorEccentricityExponent g kappaRate with hqdef
  set AC0 : ℝ := witnessAmplitudeC0Factor d rho Rad with hAC0
  set ALg : ℝ := witnessAmplitudeLgFactor d g kappaRate with hALg
  have hE1 : (1 : ℝ) ≤ E := le_max_left _ _
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE1
  have hcollAB0 : (0 : ℝ) ≤ collapsedEnergyLawFree C d s (AC0 * ALg) :=
    collapsedEnergyLawFree_nonneg C d hs _
  have hcollA0 : (0 : ℝ) ≤ collapsedEnergyLawFree C d s AC0 :=
    collapsedEnergyLawFree_nonneg C d hs _
  have hALg21 : (0 : ℝ) ≤ ALg ^ 2 + 1 := by positivity
  -- the square root of the energy bound
  have hexp : (d : ℝ) + 2 * s + 2 * q ≤ (d : ℝ) + 1 + 2 * q := by
    linarith only [hsHalf]
  have hEpow : E ^ ((d : ℝ) + 2 * s + 2 * q) ≤ E ^ ((d : ℝ) + 1 + 2 * q) :=
    Real.rpow_le_rpow_of_exponent_le hE1 hexp
  have hsqrtKB : Real.sqrt (collapsedEnergyLawFree C d s (AC0 * ALg) *
        E ^ ((d : ℝ) + 2 * s + 2 * q)) ≤
      Real.sqrt (collapsedEnergyLawFree C d s AC0) * Real.sqrt (ALg ^ 2 + 1) *
        E ^ (((d : ℝ) + 1 + 2 * q) / 2) := by
    have hstep1 : collapsedEnergyLawFree C d s (AC0 * ALg) *
          E ^ ((d : ℝ) + 2 * s + 2 * q) ≤
        (collapsedEnergyLawFree C d s AC0 * (ALg ^ 2 + 1)) *
          E ^ ((d : ℝ) + 1 + 2 * q) :=
      mul_le_mul (collapsedEnergyLawFree_mul_split C d hs AC0 ALg) hEpow
        (Real.rpow_nonneg hE0.le _) (mul_nonneg hcollA0 hALg21)
    refine (Real.sqrt_le_sqrt hstep1).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (mul_nonneg hcollA0 hALg21),
      Real.sqrt_mul hcollA0, sqrt_rpow_eq hE0.le]
  -- the monotone substitution
  have hfold0 : (0 : ℝ) < eccentricityFoldFactor abar (((d : ℝ) + 1) / 2) :=
    eccentricityFoldFactor_pos abar _
  have hX0 : (0 : ℝ) ≤ gaugeOutputLawFree d s rho *
      eccentricityFoldFactor abar (((d : ℝ) + 1) / 2) * Cdual :=
    mul_nonneg (mul_nonneg (gaugeOutputLawFree_nonneg d s rho) hfold0.le) hCdual
  have hF0 : (0 : ℝ) ≤ fluxC0Factor d s Rad cnorm * fluxLgFactor d g kappaRate :=
    mul_nonneg (fluxC0Factor_nonneg d hs Rad cnorm)
      (fluxLgFactor_nonneg d g kappaRate)
  have hmono := headSlot_mono (X := gaugeOutputLawFree d s rho *
      eccentricityFoldFactor abar (((d : ℝ) + 1) / 2) * Cdual)
    (Cb := (fractionalDualToBesovConstant d).toReal)
    (F := fluxC0Factor d s Rad cnorm * fluxLgFactor d g kappaRate)
    (hr := Real.sqrt hardyReal) hsqrtKB hX0 ENNReal.toReal_nonneg hF0
    (Real.sqrt_nonneg _)
  rw [frozenWitnessHeadConstant]
  refine hmono.trans (le_of_eq ?_)
  -- the fold factor is the eccentricity power, and the two powers add
  have hfoldEq : eccentricityFoldFactor abar (((d : ℝ) + 1) / 2) =
      E ^ (((d : ℝ) + 1) / 2) := by
    rw [hEdef]
    exact (max_one_witnessEccentricity_rpow_eq_fold abar (by positivity)).symm
  have hEsum : E ^ ((d : ℝ) + 1 + q) =
      E ^ (((d : ℝ) + 1) / 2) * E ^ (((d : ℝ) + 1 + 2 * q) / 2) := by
    rw [← Real.rpow_add hE0]
    congr 1
    ring
  rw [frozenHeadC0Factor, frozenHeadLgFactor, hfoldEq, hEsum]
  ring

end

end RowSupply
end HighContrast
end HCPolySupport
