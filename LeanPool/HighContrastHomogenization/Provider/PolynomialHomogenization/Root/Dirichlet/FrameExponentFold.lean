/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.ActivationFold

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.Root.Dirichlet.FrameExponentFold

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The response frame exponent, folded

The frame exponent of the response aggregation splits into the activation
length and the outer sandwich bracket; the activation half folds into the
eccentricity fold factor at the rate, and the bracket half is a factor in the
sandwich radius alone.

This is the arithmetic content of the folded-scale response provider: after it,
the only law-dependent quantity left in the response frame is the fold factor,
which the bumped homogenization length pays for, and everything else is built
from the dimension, the orders and the outer sandwich radius.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

noncomputable section

variable {d : ℕ}

/-- The law-free part of the folded frame constant: the activation constant at
the collapsed order, times the outer bracket's contribution. -/
@[expose]
def frameFoldConstant (d : ℕ) (g kappaRate J : ℝ) : ℝ :=
  activationFoldConstant d g kappaRate
      (max (responseWindowOrder g) kappaRate) *
    max 1 ((3 : ℝ) ^ ((responseWindowOrder g - kappaRate) * (J + 2)))

/-- **The frame exponent folds.**  The whole law dependence of the response
frame exponent is the eccentricity fold factor raised to the rate; the
remaining constant is built from the dimension, the orders and the bracket of
the outer sandwich radius. -/
theorem rpow_three_frameExponent_le_fold
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
    (hMeq : M = max (max (L : ℤ) ((J : ℤ) + 1)) 1) :
    (3 : ℝ) ^ ((responseWindowOrder g - kappaRate) * (M : ℝ) +
        kappaRate * ((L : ℕ) : ℝ)) ≤
      frameFoldConstant d g kappaRate ((J : ℕ) : ℝ) *
        (eccentricityFoldFactor abar
          (Certificate.printRowOrder g *
            max (responseWindowOrder g) kappaRate /
              (2 * kappaRate * kappaRate))) ^ kappaRate := by
  have hM1int : (1 : ℤ) ≤ M := by
    rw [hMeq]; exact le_max_right _ _
  have hMleint : M ≤ (L : ℤ) + (J : ℤ) + 2 := by
    rw [hMeq]
    have hL0 : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
    have hJ0 : (0 : ℤ) ≤ (J : ℤ) := Int.natCast_nonneg J
    omega
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1int
  have hMle : (M : ℝ) ≤ ((L : ℕ) : ℝ) + ((J : ℕ) : ℝ) + 2 := by
    exact_mod_cast hMleint
  have hL0 : (0 : ℝ) ≤ ((L : ℕ) : ℝ) := Nat.cast_nonneg L
  have hsplit := rpow_three_frameExponent_le (b := responseWindowOrder g)
    (kappa := kappaRate) (M := (M : ℝ)) (L := ((L : ℕ) : ℝ))
    (J := ((J : ℕ) : ℝ)) hM1 hMle hL0
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

end

end RowSupply
end HighContrast
end HCPolySupport
