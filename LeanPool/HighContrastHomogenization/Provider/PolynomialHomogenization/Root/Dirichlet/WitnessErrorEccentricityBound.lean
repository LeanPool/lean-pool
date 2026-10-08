/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FoldedAnchoredResponseFrame

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.WitnessErrorEccentricityBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The witness observation error, bounded by an eccentricity power

The energy module's residue is: with `Cwit` selected
before every law binder,

```
Book.Ch02.HomogenizationErrorOnCube (originCube d j) s .infinity (.finite 2)
  aFam (1 : Mat d) ≤ Cwit
```

and its λ-route bounds the left side by

```
√( max 1 (54 d² Rad) · geometricDiscount (1 − 2r) 1 ⁻¹ )
  · 3 ^ ((r − κ) M − r j + κ L) · √δ'
```

with `r = responseWindowOrder g`.  The first factor is law-free and proved in
that module.  The other two are what the *rate* leg pays for by the printed fold
of the response order, and the energy leg has no rate factor to absorb them
into — which is where that module stopped.

This module supplies the missing law-level bound: the parent-gap power together
with the certificate amplitude is below a law-free constant times a fixed power
of the witness eccentricity.  It is exactly the leak quantification of
this module, generalised from the anchored provider's particular parent generation
`M = max (max L (J+1)) 1` to any `M` with `1 ≤ M ≤ L + J + 2`, which is the form
the energy route's parent selection produces.

The exponent is
`q = printRowOrder g · max (responseWindowOrder g) kappaRate / (2 kappaRate)`,
a function of `(g, kappaRate)` only.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

noncomputable section

variable {d : ℕ}

/-! ## The frame exponent fold at a general parent generation -/

/-- **The frame exponent folds at any admissible parent generation.**  This is
`HCPoly.Provider.PolynomialHomogenization.Root.Dirichlet.FrameExponentFold`'s
theorem with the anchored provider's explicit
`M = max (max L (J+1)) 1` replaced by the two inequalities it was used through,
so that the energy route's own parent selection qualifies. -/
theorem rpow_three_frameExponent_le_fold_of_bounds
    {abar : Mat d} {g kappaRate : ℝ} {G L J : ℕ} {M : ℤ}
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
    (hM1 : (1 : ℤ) ≤ M) (hMle : M ≤ (L : ℤ) + (J : ℤ) + 2) :
    (3 : ℝ) ^ ((responseWindowOrder g - kappaRate) * (M : ℝ) +
        kappaRate * ((L : ℕ) : ℝ)) ≤
      frameFoldConstant d g kappaRate ((J : ℕ) : ℝ) *
        (eccentricityFoldFactor abar
          (Certificate.printRowOrder g *
            max (responseWindowOrder g) kappaRate /
              (2 * kappaRate * kappaRate))) ^ kappaRate := by
  have hM1R : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hMleR : (M : ℝ) ≤ ((L : ℕ) : ℝ) + ((J : ℕ) : ℝ) + 2 := by
    exact_mod_cast hMle
  have hL0 : (0 : ℝ) ≤ ((L : ℕ) : ℝ) := Nat.cast_nonneg L
  have hsplit := rpow_three_frameExponent_le (b := responseWindowOrder g)
    (kappa := kappaRate) (M := (M : ℝ)) (L := ((L : ℕ) : ℝ))
    (J := ((J : ℕ) : ℝ)) hM1R hMleR hL0
  have hmaxOrder : (0 : ℝ) ≤ max (responseWindowOrder g) kappaRate :=
    le_trans hkappa.le (le_max_right _ _)
  have hfold := rpow_activation_le_foldFactor (abar := abar) (g := g)
    (kappaRate := kappaRate) (c := max (responseWindowOrder g) kappaRate)
    (G := G) (L := L) hkappa hmaxOrder hrho hgeom hP hLeq hGupper
  have hbracket0 : (0 : ℝ) ≤
      max 1 ((3 : ℝ) ^ ((responseWindowOrder g - kappaRate) *
        (((J : ℕ) : ℝ) + 2))) := le_trans zero_le_one (le_max_left _ _)
  refine hsplit.trans ?_
  calc (((3 : ℝ) ^ ((L : ℕ) : ℝ)) ^ (max (responseWindowOrder g) kappaRate)) *
        max 1 ((3 : ℝ) ^ ((responseWindowOrder g - kappaRate) *
          (((J : ℕ) : ℝ) + 2)))
      ≤ (activationFoldConstant d g kappaRate
            (max (responseWindowOrder g) kappaRate) *
          (eccentricityFoldFactor abar
            (Certificate.printRowOrder g *
              max (responseWindowOrder g) kappaRate /
                (2 * kappaRate * kappaRate))) ^ kappaRate) *
          max 1 ((3 : ℝ) ^ ((responseWindowOrder g - kappaRate) *
            (((J : ℕ) : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_right hfold hbracket0
    _ = frameFoldConstant d g kappaRate ((J : ℕ) : ℝ) *
          (eccentricityFoldFactor abar
            (Certificate.printRowOrder g *
              max (responseWindowOrder g) kappaRate /
                (2 * kappaRate * kappaRate))) ^ kappaRate := by
        rw [frameFoldConstant]; ring

/-! ## The eccentricity exponent of the witness error -/

/-- The law-free exponent of the witness eccentricity in the energy leg's
constant: the fold exponent multiplied by the rate. -/
@[expose]
def witnessErrorEccentricityExponent (g kappaRate : ℝ) : ℝ :=
  Certificate.printRowOrder g * max (responseWindowOrder g) kappaRate /
    (2 * kappaRate)

theorem foldedFrameEccentricityExponent_nonneg_of_orders {g kappaRate : ℝ}
    (hkappa : 0 < kappaRate)
    (hrho : 0 ≤ Certificate.printRowOrder g) :
    0 ≤ foldedFrameEccentricityExponent g kappaRate := by
  have hmax : (0 : ℝ) ≤ max (responseWindowOrder g) kappaRate :=
    le_trans hkappa.le (le_max_right _ _)
  have hden : (0 : ℝ) ≤ 2 * kappaRate * kappaRate := by positivity
  rw [foldedFrameEccentricityExponent]
  exact div_nonneg (mul_nonneg hrho hmax) hden

/-- The folded factor raised to the rate is a single power of the truncated
witness eccentricity, at the law-free exponent above. -/
theorem eccentricityFoldFactor_rpow_eq_witnessPow (abar : Mat d)
    {g kappaRate : ℝ} (hkappa : 0 < kappaRate)
    (hrho : 0 ≤ Certificate.printRowOrder g) :
    (eccentricityFoldFactor abar
        (foldedFrameEccentricityExponent g kappaRate)) ^ kappaRate =
      (max 1 (witnessEccentricity (symmPart abar))) ^
        witnessErrorEccentricityExponent g kappaRate := by
  have hp : 0 ≤ foldedFrameEccentricityExponent g kappaRate :=
    foldedFrameEccentricityExponent_nonneg_of_orders hkappa hrho
  have hE0 : (0 : ℝ) ≤ max 1 (witnessEccentricity (symmPart abar)) :=
    le_trans zero_le_one (le_max_left _ _)
  rw [eccentricityFoldFactor_eq_max_rpow abar hp, ← Real.rpow_mul hE0,
    foldedFrameEccentricityExponent, witnessErrorEccentricityExponent]
  congr 1
  field_simp

/-! ## The witness error bound -/

end

end RowSupply
end HighContrast
end HCPolySupport
