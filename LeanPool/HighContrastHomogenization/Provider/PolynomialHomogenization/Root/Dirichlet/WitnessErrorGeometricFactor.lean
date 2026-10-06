/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessErrorEccentricityBound

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.WitnessErrorGeometricFactor

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The witness error bound at a supplied generation factor

`HCPoly.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessErrorEccentricityBound`
takes `0 ≤ j` — the witness cube
index nonnegative — as its one geometric binder, to kill the `3 ^ (−r j)` factor
of the λ-route.

**That hypothesis is false in general.**  The frozen clause carries
`U ⊆ ellipsoid abar 1`, and

```
ellipsoid abar r = {x | vecDot x ((symmPart abar)⁻¹ x) ≤ specBound (symmPart abar)⁻¹ * r ^ 2}
```

is, in gauge coordinates `x = matSqrt (symmPart abar) y`, exactly the ball of
radius `α r` with `α = √(specBound (symmPart abar)⁻¹)`.  So the witness cube of
side `3 ^ j`, translated, sits inside the ball of radius `α`, forcing
`3 ^ j * √d ≤ 2 α`.  Taking `abar = 1` gives `α = 1` and `3 ^ j ≤ 2 / √d`, which
is `< 1` for every `d ≥ 5`: **`j < 0` there, necessarily.**

The correct hypothesis is therefore not a sign but a *bound*: the factor
`3 ^ (−r j)` must be supplied as below a constant.  It is law-free in the
frozen data: the same two-sided geometry gives `3 ^ j ≥ 2 α / (3 √d)` from the inner-ellipsoid
normalization inner premise `ellipsoid abar (1/(3√d)) ⊆ U`, and the ball sandwich's inner
radius gives `α ≥ ρ / 2`, so `3 ^ (−r j) ≤ (ρ / (3 √d)) ^ (−r)` — a function of
`(d, ρ, r)` only, and `ρ` is one of `C₀ s₀ ρ Rad`'s own parameters.

This module restates the bound against that supplied factor, so the consumer may
feed whichever geometric estimate it holds.  The two-sided cube/ball geometry
itself is **not** built here and is named in the residue.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

noncomputable section

variable {d : ℕ}

/-- **21c, in its usable form.**  The λ-route's law-level tail is below a
law-free constant — the supplied generation factor times the frame fold
constant — multiplied by a fixed power of the witness eccentricity. -/
theorem witnessErrorFactor_le_geo_mul_eccentricityPow [NeZero d]
    {abar : Mat d} {g kappaRate deltaScaled Cgeo : ℝ} {G L J : ℕ} {M j : ℤ}
    (hkappa : 0 < kappaRate)
    (hrho : 0 ≤ Certificate.printRowOrder g)
    (hgeom : 0 < 1 - (3 : ℝ) ^
      (-(2 * responseWindowOrder g - Certificate.printRowOrder g)))
    (hP : 0 < Certificate.shiftedTailAbsorptionPrefactor d
      (responseWindowOrder g) (Certificate.printRowOrder g) G)
    (hLeq : L = Certificate.formulaicNormalizedReferenceTailShift d
      (responseWindowOrder g) (Certificate.printRowOrder g)
        (2 * kappaRate) G)
    (hGupper : (3 : ℝ) ^ ((G : ℕ) : ℝ) ≤
      1 + 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d))
    (hM1 : (1 : ℤ) ≤ M) (hMle : M ≤ (L : ℤ) + (J : ℤ) + 2)
    (hCgeo : (3 : ℝ) ^ (-responseWindowOrder g * (j : ℝ)) ≤ Cgeo)
    (hdelta1 : Real.sqrt deltaScaled ≤ 1) :
    (3 : ℝ) ^ ((responseWindowOrder g - kappaRate) * (M : ℝ) -
          responseWindowOrder g * (j : ℝ) +
          kappaRate * ((L : ℕ) : ℝ)) *
        Real.sqrt deltaScaled ≤
      (Cgeo * frameFoldConstant d g kappaRate ((J : ℕ) : ℝ)) *
        (max 1 (witnessEccentricity (symmPart abar))) ^
          witnessErrorEccentricityExponent g kappaRate := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hgeo0 : (0 : ℝ) ≤ Cgeo :=
    le_trans (Real.rpow_nonneg h3.le _) hCgeo
  have hcongr : (responseWindowOrder g - kappaRate) * (M : ℝ) -
      responseWindowOrder g * (j : ℝ) + kappaRate * ((L : ℕ) : ℝ) =
      ((responseWindowOrder g - kappaRate) * (M : ℝ) +
        kappaRate * ((L : ℕ) : ℝ)) + (-responseWindowOrder g * (j : ℝ)) := by
    ring
  have hsplit : (3 : ℝ) ^ ((responseWindowOrder g - kappaRate) * (M : ℝ) -
        responseWindowOrder g * (j : ℝ) + kappaRate * ((L : ℕ) : ℝ)) =
      (3 : ℝ) ^ ((responseWindowOrder g - kappaRate) * (M : ℝ) +
          kappaRate * ((L : ℕ) : ℝ)) *
        (3 : ℝ) ^ (-responseWindowOrder g * (j : ℝ)) := by
    rw [hcongr, Real.rpow_add h3]
  have hA0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((responseWindowOrder g - kappaRate) *
      (M : ℝ) + kappaRate * ((L : ℕ) : ℝ)) := Real.rpow_nonneg h3.le _
  have hgeoTerm0 : (0 : ℝ) ≤
      (3 : ℝ) ^ (-responseWindowOrder g * (j : ℝ)) := Real.rpow_nonneg h3.le _
  have hfold := rpow_three_frameExponent_le_fold_of_bounds (abar := abar)
    (g := g) (kappaRate := kappaRate) (G := G) (L := L) (J := J) (M := M)
    hkappa hrho hgeom hP hLeq hGupper hM1 hMle
  have hfoldE : (3 : ℝ) ^ ((responseWindowOrder g - kappaRate) * (M : ℝ) +
        kappaRate * ((L : ℕ) : ℝ)) ≤
      frameFoldConstant d g kappaRate ((J : ℕ) : ℝ) *
        (max 1 (witnessEccentricity (symmPart abar))) ^
          witnessErrorEccentricityExponent g kappaRate := by
    refine hfold.trans (le_of_eq ?_)
    rw [← foldedFrameEccentricityExponent,
      eccentricityFoldFactor_rpow_eq_witnessPow abar hkappa hrho]
  have hFFC0 : (0 : ℝ) ≤ frameFoldConstant d g kappaRate ((J : ℕ) : ℝ) *
      (max 1 (witnessEccentricity (symmPart abar))) ^
        witnessErrorEccentricityExponent g kappaRate :=
    mul_nonneg (frameFoldConstant_nonneg d g kappaRate ((J : ℕ) : ℝ))
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  rw [hsplit]
  calc (3 : ℝ) ^ ((responseWindowOrder g - kappaRate) * (M : ℝ) +
            kappaRate * ((L : ℕ) : ℝ)) *
          (3 : ℝ) ^ (-responseWindowOrder g * (j : ℝ)) *
          Real.sqrt deltaScaled
      ≤ (3 : ℝ) ^ ((responseWindowOrder g - kappaRate) * (M : ℝ) +
            kappaRate * ((L : ℕ) : ℝ)) *
          (3 : ℝ) ^ (-responseWindowOrder g * (j : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hdelta1 (mul_nonneg hA0 hgeoTerm0)
    _ = (3 : ℝ) ^ ((responseWindowOrder g - kappaRate) * (M : ℝ) +
            kappaRate * ((L : ℕ) : ℝ)) *
          (3 : ℝ) ^ (-responseWindowOrder g * (j : ℝ)) := by rw [mul_one]
    _ ≤ (frameFoldConstant d g kappaRate ((J : ℕ) : ℝ) *
            (max 1 (witnessEccentricity (symmPart abar))) ^
              witnessErrorEccentricityExponent g kappaRate) * Cgeo :=
        mul_le_mul hfoldE hCgeo hgeoTerm0 hFFC0
    _ = (Cgeo * frameFoldConstant d g kappaRate ((J : ℕ) : ℝ)) *
          (max 1 (witnessEccentricity (symmPart abar))) ^
            witnessErrorEccentricityExponent g kappaRate := by ring

end

end RowSupply
end HighContrast
end HCPolySupport
