/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessRouteEnergyCollapse
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FoldedAnchoredResponseFrame
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FluxConstantSlotSplit
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.EnergyPrice.ResidualWindowFillingBound

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.WitnessAmplitudeLawFree

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# (i) The explicit law-free amplitude `Alaw`, split into the `C₀` and `Lg` classes

that module reduced the fifth head factor to *any* law-free `Alaw` dominating the
witness-route amplitude

```
A = lambdaRouteClaw d b λ abar · (witnessGeometricFactor d ρ b ·
      frameFoldConstant d g κ J) ,      b := responseWindowOrder g .
```

This module renders `Alaw` explicitly and **splits it by slot**, exactly as
the flux-constant split gives:

* `witnessAmplitudeC0Factor d ρ Rad` — `(d, ρ, Rad)`-level, the `C₀` slot;
* `witnessAmplitudeLgFactor d g κ` — `(d, g, κ)`-level, the `Lg` slot.

No factor lands in two classes and no factor sees `abar`.  The three bounds are used exactly once
each:

| factor of `A` | trimmed by | slot |
|---|---|---|
| `observationFillingCoefficient d λ abar`, `λ ∈ Icc 1 3` |
`EnergyPrice.observationFillingCoefficient_le_of_residualWindow` (E23) → `max 1 (54 d² Rad)` |
`C₀` |
| `(geometricDiscount (1 − 2b) 1)⁻¹` | — | `Lg` (through `g`) |
| `witnessGeometricFactor d ρ b` | the `witnessGeometricFactor_le_uniform` premise | `C₀` |
| `activationFoldConstant d g κ (max b κ)` | — | `Lg` |
| `max 1 (3 ^ ((b − κ)(J + 2)))` | the `max_one_rpow_three_bracket_le` premise, at `3 ^ J ≤ 1 + 6
Rad` | `C₀` |

**The upper bracket is what this module contributes.**  The two neighbouring
modules carry
only `2 Rad ≤ 3 ^ J`; the last row needs `3 ^ J ≤ 1 + 3 (2 Rad)`, which
`Entry.exists_pow_three_bracket` produces at the same time.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The two classes -/

/-- The `C₀`-slot half of the law-free witness amplitude: `(d, ρ, Rad)`. -/
@[expose]
noncomputable def witnessAmplitudeC0Factor (d : ℕ) (rho Rad : ℝ) : ℝ :=
  Real.sqrt (max 1 (54 * (d : ℝ) ^ 2 * Rad)) *
    (uniformWitnessGeometricFactor d rho *
      (3 * max 1 ((1 + 3 * (2 * Rad)) ^ (1 / 2 : ℝ))))

/-- The `Lg`-slot half of the law-free witness amplitude: `(d, g, κ)`. -/
@[expose]
noncomputable def witnessAmplitudeLgFactor (d : ℕ)
    (g kappaRate : ℝ) : ℝ :=
  Real.sqrt ((Book.Ch02.geometricDiscount
      (1 - 2 * responseWindowOrder g) 1)⁻¹) *
    activationFoldConstant d g kappaRate
      (max (responseWindowOrder g) kappaRate)

/-! ## The geometric gap of the response window -/

/-- The response-window discount is positive on the printed `g`-window. -/
theorem geometricDiscount_responseWindow_pos {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    0 < Book.Ch02.geometricDiscount (1 - 2 * responseWindowOrder g) 1 := by
  have hg1 : g < 1 := hg.2
  have hb : responseWindowOrder g < 1 / 2 := by
    rw [responseWindowOrder]
    linarith only [hg1]
  have hneg : -(1 - 2 * responseWindowOrder g) * 1 < 0 := by
    linarith only [hb]
  have hlt : Real.rpow (3 : ℝ) (-(1 - 2 * responseWindowOrder g) * 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
  rw [Book.Ch02.geometricDiscount]
  linarith only [hlt]

/-! ## The amplitude bound -/

/-- **(i), closed.**  The witness-route amplitude is below the product of its
two law-free classes, with no `abar` and no `λ` left. -/
theorem witnessRouteAmplitude_le_classes [NeZero d]
    {abar : Mat d} {U : Set (Vec d)} {g kappaRate rho Rad lambda : ℝ} {J : ℕ}
    (hS : (symmPart abar).PosDef)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hkappa : 0 < kappaRate)
    (hlambda : lambda ∈ Set.Icc (1 : ℝ) 3)
    (hinner : ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U)
    (hsandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ U) rho Rad)
    (hJupper : (3 : ℝ) ^ ((J : ℕ) : ℤ) ≤ 1 + 3 * (2 * Rad)) :
    lambdaRouteClaw d (responseWindowOrder g) lambda abar *
        (witnessGeometricFactor d rho (responseWindowOrder g) *
          frameFoldConstant d g kappaRate ((J : ℕ) : ℝ)) ≤
      witnessAmplitudeC0Factor d rho Rad *
        witnessAmplitudeLgFactor d g kappaRate := by
  obtain ⟨hrho, hRad, cc, -, hOut⟩ := hsandwich
  have hg0 : (0 : ℝ) ≤ g := hg.1
  have hg1 : g < 1 := hg.2
  have hb0 : (0 : ℝ) ≤ responseWindowOrder g := by
    rw [responseWindowOrder]
    linarith only [hg0]
  have hbHalf : responseWindowOrder g ≤ 1 / 2 := by
    rw [responseWindowOrder]
    linarith only [hg1]
  -- the λ-route constant
  have hDpos := geometricDiscount_responseWindow_pos hg
  have hDinv : (0 : ℝ) ≤
      (Book.Ch02.geometricDiscount (1 - 2 * responseWindowOrder g) 1)⁻¹ :=
    (inv_pos.mpr hDpos).le
  have hfill := EnergyPrice.observationFillingCoefficient_le_of_residualWindow
    hS hlambda hRad hinner hOut
  have hFb0 : (0 : ℝ) ≤ max 1 (54 * (d : ℝ) ^ 2 * Rad) :=
    le_trans zero_le_one (le_max_left _ _)
  have hClaw : lambdaRouteClaw d (responseWindowOrder g) lambda abar ≤
      Real.sqrt (max 1 (54 * (d : ℝ) ^ 2 * Rad)) *
        Real.sqrt ((Book.Ch02.geometricDiscount
          (1 - 2 * responseWindowOrder g) 1)⁻¹) := by
    rw [lambdaRouteClaw, ← Real.sqrt_mul hFb0]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hfill hDinv)
  -- the geometric factor
  have hCgeo := witnessGeometricFactor_le_uniform (d := d) hrho hb0 hbHalf
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hden : (0 : ℝ) < 3 * Real.sqrt (d : ℝ) := by
    have hsq : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd0
    linarith only [hsq]
  have hCgeo0 : (0 : ℝ) ≤ witnessGeometricFactor d rho (responseWindowOrder g) := by
    rw [witnessGeometricFactor]
    exact Real.rpow_nonneg (div_pos hrho hden).le _
  -- the frame fold constant
  have hJr : (0 : ℝ) ≤ ((J : ℕ) : ℝ) := Nat.cast_nonneg _
  have hJupperR : (3 : ℝ) ^ ((J : ℕ) : ℝ) ≤ 1 + 3 * (2 * Rad) := by
    rw [Real.rpow_natCast]
    rwa [zpow_natCast] at hJupper
  have hB1 : (1 : ℝ) ≤ 1 + 3 * (2 * Rad) := by linarith only [hRad]
  have he2 : responseWindowOrder g - kappaRate ≤ 1 / 2 := by
    linarith only [hbHalf, hkappa]
  have hbracket := max_one_rpow_three_bracket_le he2 hJr hB1 hJupperR
  have hact0 : (0 : ℝ) ≤ activationFoldConstant d g kappaRate
      (max (responseWindowOrder g) kappaRate) :=
    activationFoldConstant_nonneg d g kappaRate _
  have hfold : frameFoldConstant d g kappaRate ((J : ℕ) : ℝ) ≤
      activationFoldConstant d g kappaRate
          (max (responseWindowOrder g) kappaRate) *
        (3 * max 1 ((1 + 3 * (2 * Rad)) ^ (1 / 2 : ℝ))) := by
    rw [frameFoldConstant]
    exact mul_le_mul_of_nonneg_left hbracket hact0
  have hfold0 : (0 : ℝ) ≤ frameFoldConstant d g kappaRate ((J : ℕ) : ℝ) :=
    frameFoldConstant_nonneg d g kappaRate _
  have hunif0 : (0 : ℝ) ≤ uniformWitnessGeometricFactor d rho :=
    le_trans zero_le_one (one_le_uniformWitnessGeometricFactor d rho)
  have hbrk0 : (0 : ℝ) ≤ 3 * max 1 ((1 + 3 * (2 * Rad)) ^ (1 / 2 : ℝ)) := by
    have : (0 : ℝ) ≤ max 1 ((1 + 3 * (2 * Rad)) ^ (1 / 2 : ℝ)) :=
      le_trans zero_le_one (le_max_left _ _)
    linarith only [this]
  have hinner2 : witnessGeometricFactor d rho (responseWindowOrder g) *
      frameFoldConstant d g kappaRate ((J : ℕ) : ℝ) ≤
      uniformWitnessGeometricFactor d rho *
        (activationFoldConstant d g kappaRate
            (max (responseWindowOrder g) kappaRate) *
          (3 * max 1 ((1 + 3 * (2 * Rad)) ^ (1 / 2 : ℝ)))) :=
    mul_le_mul hCgeo hfold hfold0 hunif0
  have hprod := mul_le_mul hClaw hinner2
    (mul_nonneg hCgeo0 hfold0)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  refine hprod.trans (le_of_eq ?_)
  rw [witnessAmplitudeC0Factor, witnessAmplitudeLgFactor]
  ring

end

end RowSupply
end HighContrast
end HCPolySupport
