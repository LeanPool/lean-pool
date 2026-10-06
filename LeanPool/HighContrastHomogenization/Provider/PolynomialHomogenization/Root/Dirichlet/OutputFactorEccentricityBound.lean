/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.EnergyPriceEccentricityCollapse
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.EnergyPrice.GaugeFrameEccentricity
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootInterface.ProviderSurface

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.OutputFactorEccentricityBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# (β): the output factor, and the correction to classified

```
outputFactor = √(hsAffineFactor (matSqrt (symmPart abar))⁻¹ s ‖matSqrt (symmPart abar)‖)
```

as "none — it CANCELS". corrected that: the factor cancels on the
*left* of the terminal bound, but it also occurs **inside** `hRate`'s left-hand
side, where that module carries it into its own `C₀`.  A law-free `C₀` therefore needs
it bounded.

**It cannot be bounded by a law-free constant times an eccentricity power
alone.**  `hsAffineFactor` is homogeneous of degree `s` in the absolute scale of
`symmPart abar`, while the witness eccentricity is scale *invariant*: at
`abar = t • 1` the eccentricity is `1` for every `t > 0` while the factor is
`t ^ s`.  The dispatch's `(β)` is false as literally stated.

**The correct form, proved here.**  The frozen inner-ellipsoid normalization ties the gauge
cube side to that same absolute scale from *both* sides
(`witnessCubeScale_two_sided`), and the ball sandwich's inner radius
`ρ` is below the gauge scale.  So the cube side is bounded below by `2ρ/(3√d)`,
and dividing the energy's paired estimate

```
hsAffineFactor L⁻¹ s ‖L‖ * ell ^ (2 s) ≤ gaugeFrameConstant d s * ecc ^ (d + 2 s)
```

by that lower bound leaves a head depending on `(d, s, ρ)` **only** — which is
exactly `C₀ s₀ ρ Rad`'s permitted dependence — times `ecc ^ (d + 2 s)`.  The
`s`-dependence of the eccentricity exponent is then trimmed away by `s < 1/2`
and the monotonicity of the fold factor, leaving the `(d)`-level exponent
`(d + 1) / 2` that the `pEcc` slot can carry.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

open scoped ENNReal Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The law-free head -/

/-- The square of the output factor's law-free head: `(d, s, ρ)`-level, which is
`C₀ s₀ ρ Rad`'s permitted dependence. -/
@[expose]
noncomputable def gaugeOutputLawFreeSq (d : ℕ) (s rho : ℝ) : ℝ :=
  EnergyPrice.gaugeFrameConstant d s *
    ((3 * Real.sqrt (d : ℝ)) / (2 * rho)) ^ (2 * s)

/-- The output factor's law-free head. -/
@[expose]
noncomputable def gaugeOutputLawFree (d : ℕ) (s rho : ℝ) : ℝ :=
  Real.sqrt (gaugeOutputLawFreeSq d s rho)

theorem gaugeOutputLawFreeSq_nonneg (d : ℕ) {s rho : ℝ} (hrho : 0 ≤ rho) :
    0 ≤ gaugeOutputLawFreeSq d s rho := by
  have hnum : (0 : ℝ) ≤ 3 * Real.sqrt (d : ℝ) := by positivity
  have hden : (0 : ℝ) ≤ 2 * rho := by linarith only [hrho]
  rw [gaugeOutputLawFreeSq]
  exact mul_nonneg (EnergyPrice.gaugeFrameConstant_nonneg d s)
    (Real.rpow_nonneg (div_nonneg hnum hden) _)

theorem gaugeOutputLawFree_nonneg (d : ℕ) (s rho : ℝ) :
    0 ≤ gaugeOutputLawFree d s rho := Real.sqrt_nonneg _

/-! ## The bound -/

/-- **(β), the corrected form.**  The affine distortion factor of the gauge
frame change is below a `(d, s, ρ)`-level head times the `(d + 2 s)`-power of
the witness eccentricity.  The inner sandwich radius `ρ` is what pays the
absolute scale that the eccentricity cannot see. -/
theorem hsAffineFactor_le_gaugeOutputLawFreeSq_mul_eccentricityPow [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {U : Set (Vec d)} {j : ℤ} {z : Vec d} {rho Rad s : ℝ}
    (hs : 0 < s) (hsHalf : s < 1 / 2)
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j))
    (hUsub : U ⊆ ellipsoid abar 1)
    (hinner : ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U)
    (hsandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ U) rho Rad) :
    hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
        ‖matSqrt (symmPart abar)‖ ≤
      gaugeOutputLawFreeSq d s rho *
        witnessEccentricity (symmPart abar) ^ ((d : ℝ) + 2 * s) := by
  obtain ⟨hlow, hup, hrhoAlpha⟩ :=
    witnessCubeScale_two_sided hS hU hUsub hinner hsandwich
  have hrho : 0 < rho := hsandwich.1
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hsqrtd : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
    have h := Real.sqrt_le_sqrt hd1
    rwa [Real.sqrt_one] at h
  have hden : (0 : ℝ) < 3 * Real.sqrt (d : ℝ) := by linarith only [hsqrtd]
  have hell0 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hellBound : (3 : ℝ) ^ j ≤ 2 * ‖(matSqrt (symmPart abar))⁻¹‖ := by
    rw [norm_inv_matSqrt_eq_sqrt_specBound hS]
    exact hup
  have hkey := EnergyPrice.hsAffineFactor_mul_cubeSide_le_witnessEccentricity_rpow
    hS hs hsHalf hell0.le hellBound
  -- the lower bound on the cube side, through `ρ`
  have hw0 : (0 : ℝ) < 2 * rho / (3 * Real.sqrt (d : ℝ)) :=
    div_pos (by linarith only [hrho]) hden
  have hwle : 2 * rho / (3 * Real.sqrt (d : ℝ)) ≤ (3 : ℝ) ^ j := by
    have hinvNonneg : (0 : ℝ) ≤ 1 / (3 * Real.sqrt (d : ℝ)) :=
      le_of_lt (one_div_pos.mpr hden)
    have hmono : rho * (1 / (3 * Real.sqrt (d : ℝ))) ≤
        Real.sqrt (specBound ((symmPart abar)⁻¹)) *
          (1 / (3 * Real.sqrt (d : ℝ))) :=
      mul_le_mul_of_nonneg_right hrhoAlpha hinvNonneg
    have hrewrite : 2 * rho / (3 * Real.sqrt (d : ℝ)) =
        2 * (rho * (1 / (3 * Real.sqrt (d : ℝ)))) := by ring
    rw [hrewrite]
    linarith only [hlow, hmono]
  have hpow : (2 * rho / (3 * Real.sqrt (d : ℝ))) ^ (2 * s) ≤
      ((3 : ℝ) ^ j) ^ (2 * s) :=
    Real.rpow_le_rpow hw0.le hwle (by linarith only [hs])
  have hA0 : (0 : ℝ) ≤ hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
      ‖matSqrt (symmPart abar)‖ := by
    rw [hsAffineFactor]
    exact le_trans (Real.rpow_nonneg (abs_nonneg _) _) (le_max_left _ _)
  have hstep : hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
        ‖matSqrt (symmPart abar)‖ *
        (2 * rho / (3 * Real.sqrt (d : ℝ))) ^ (2 * s) ≤
      EnergyPrice.gaugeFrameConstant d s *
        witnessEccentricity (symmPart abar) ^ ((d : ℝ) + 2 * s) :=
    le_trans (mul_le_mul_of_nonneg_left hpow hA0) hkey
  have hwpow0 : (0 : ℝ) < (2 * rho / (3 * Real.sqrt (d : ℝ))) ^ (2 * s) :=
    Real.rpow_pos_of_pos hw0 _
  have hwne : (2 * rho / (3 * Real.sqrt (d : ℝ))) ^ (2 * s) ≠ 0 :=
    ne_of_gt hwpow0
  have hinvpow : ((3 * Real.sqrt (d : ℝ)) / (2 * rho)) ^ (2 * s) =
      ((2 * rho / (3 * Real.sqrt (d : ℝ))) ^ (2 * s))⁻¹ := by
    have hswap : (3 * Real.sqrt (d : ℝ)) / (2 * rho) =
        (2 * rho / (3 * Real.sqrt (d : ℝ)))⁻¹ := by
      rw [inv_div]
    rw [hswap, Real.inv_rpow hw0.le]
  rw [gaugeOutputLawFreeSq, hinvpow]
  calc hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
        ‖matSqrt (symmPart abar)‖
      = hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
            ‖matSqrt (symmPart abar)‖ *
          (2 * rho / (3 * Real.sqrt (d : ℝ))) ^ (2 * s) *
          ((2 * rho / (3 * Real.sqrt (d : ℝ))) ^ (2 * s))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hwne, mul_one]
    _ ≤ EnergyPrice.gaugeFrameConstant d s *
          witnessEccentricity (symmPart abar) ^ ((d : ℝ) + 2 * s) *
          ((2 * rho / (3 * Real.sqrt (d : ℝ))) ^ (2 * s))⁻¹ :=
        mul_le_mul_of_nonneg_right hstep (le_of_lt (inv_pos.mpr hwpow0))
    _ = EnergyPrice.gaugeFrameConstant d s *
          ((2 * rho / (3 * Real.sqrt (d : ℝ))) ^ (2 * s))⁻¹ *
          witnessEccentricity (symmPart abar) ^ ((d : ℝ) + 2 * s) := by ring

/-- **(β) in the fold slot.**  The output factor itself is below the law-free
head times the fold factor at the `(d)`-level exponent `(d + 1) / 2`; the
`s`-dependence of the exponent is trimmed by `s < 1/2`, exactly as that module trims the
geometric factor's order dependence. -/
theorem outputFactor_le_gaugeOutputLawFree_mul_fold [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {U : Set (Vec d)} {j : ℤ} {z : Vec d} {rho Rad s : ℝ}
    (hs : 0 < s) (hsHalf : s < 1 / 2)
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j))
    (hUsub : U ⊆ ellipsoid abar 1)
    (hinner : ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U)
    (hsandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ U) rho Rad) :
    Real.sqrt (hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
        ‖matSqrt (symmPart abar)‖) ≤
      gaugeOutputLawFree d s rho *
        eccentricityFoldFactor abar (((d : ℝ) + 1) / 2) := by
  have hmain := hsAffineFactor_le_gaugeOutputLawFreeSq_mul_eccentricityPow
    hS hs hsHalf hU hUsub hinner hsandwich
  have hrho : 0 < rho := hsandwich.1
  have hC0 : (0 : ℝ) ≤ gaugeOutputLawFreeSq d s rho :=
    gaugeOutputLawFreeSq_nonneg d hrho.le
  have hE0 : (0 : ℝ) ≤ witnessEccentricity (symmPart abar) :=
    witnessEccentricity_nonneg _
  have hdR : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  calc Real.sqrt (hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
          ‖matSqrt (symmPart abar)‖)
      ≤ Real.sqrt (gaugeOutputLawFreeSq d s rho *
          witnessEccentricity (symmPart abar) ^ ((d : ℝ) + 2 * s)) :=
        Real.sqrt_le_sqrt hmain
    _ = gaugeOutputLawFree d s rho *
          witnessEccentricity (symmPart abar) ^ (((d : ℝ) + 2 * s) / 2) := by
        rw [Real.sqrt_mul hC0, gaugeOutputLawFree]
        congr 1
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hE0]
        congr 1
        ring
    _ ≤ gaugeOutputLawFree d s rho *
          eccentricityFoldFactor abar (((d : ℝ) + 1) / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (gaugeOutputLawFree_nonneg d s rho)
        refine le_trans (rpow_le_eccentricityFoldFactor abar _) ?_
        exact RootInterface.eccentricityFoldFactor_mono abar
          (by linarith only [hdR, hs]) (by linarith only [hsHalf])

end

end RowSupply
end HighContrast
end HCPolySupport
