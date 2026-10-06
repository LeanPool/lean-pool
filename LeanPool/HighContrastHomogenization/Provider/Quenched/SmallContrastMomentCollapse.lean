/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntrySupplyFree

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastMomentCollapse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The moment collapse past the burn-in

The shared interface for the free-threshold wave: past the burn-in depth,
the deepened moment excess is at most one, so the deepened first moment is
at most `2` and the deepened second moment integrates to at most `2`.
The burn-in condition transports monotonically to deeper anchors.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder ENNReal

noncomputable section

variable {d : ℕ}

/-- The burn-in condition transports to any deeper anchor. -/
theorem burn_condition_mono {K : ℝ} {M : ℕ} {sKw jb w : ℤ} {Gacc : ℕ}
    (hjw : jb ≤ w)
    (hburn : 1 + 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
        growthBar K ^ IndependentSums.natTriangular (2 + M) ≤
      (3 : ℝ) ^ ((M : ℝ) *
        ((jb + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) :
    1 + 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
        growthBar K ^ IndependentSums.natTriangular (2 + M) ≤
      (3 : ℝ) ^ ((M : ℝ) *
        ((w + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ)) := by
  refine hburn.trans ?_
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hcast : ((jb + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ) ≤
      ((w + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ) := by
    exact_mod_cast (by omega :
      jb + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw ≤
        w + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw)
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  exact mul_le_mul_of_nonneg_left hcast hM0

/-- The crude moment constants are monotone in the order. -/
theorem crudeMoment_mono_order {K : ℝ} (M : ℕ) :
    1 + 2 * ((1 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
      growthBar K ^ IndependentSums.natTriangular (1 + M) ≤
      1 + 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
        growthBar K ^ IndependentSums.natTriangular (2 + M) := by
  have hbar2 : (2 : ℝ) ≤ growthBar K := le_max_left _ _
  have hlog0 : 0 ≤ Real.log (growthBar K) :=
    Real.log_nonneg (by linarith only [hbar2])
  have hgKpow : ∀ N : ℕ, (0 : ℝ) ≤
      growthBar K ^ IndependentSums.natTriangular N := fun N =>
    pow_nonneg (by linarith only [hbar2]) _
  have htri : IndependentSums.natTriangular (1 + M) ≤
      IndependentSums.natTriangular (2 + M) := by
    have h21 : 2 + M = (1 + M) + 1 := by omega
    rw [h21]
    show IndependentSums.natTriangular (1 + M) ≤
      IndependentSums.natTriangular (1 + M) + (1 + M)
    omega
  have hpowle : growthBar K ^ IndependentSums.natTriangular (1 + M) ≤
      growthBar K ^ IndependentSums.natTriangular (2 + M) :=
    pow_le_pow_right₀ (by linarith only [hbar2]) htri
  have hco : ((1 + M : ℕ) : ℝ) ≤ ((2 + M : ℕ) : ℝ) := by
    push_cast
    linarith only []
  have hlogfac : (0 : ℝ) ≤ 1 + Real.log (growthBar K) := by
    linarith only [hlog0]
  have hfac1 : 2 * ((1 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) ≤
      2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) :=
    mul_le_mul_of_nonneg_right (by linarith only [hco]) hlogfac
  have hstep1 : 2 * ((1 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
      growthBar K ^ IndependentSums.natTriangular (1 + M) ≤
      2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
        growthBar K ^ IndependentSums.natTriangular (1 + M) :=
    mul_le_mul_of_nonneg_right hfac1 (hgKpow (1 + M))
  have hcL1 : (0 : ℝ) ≤
      2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) := by
    positivity
  have hstep2 : 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
      growthBar K ^ IndependentSums.natTriangular (1 + M) ≤
      2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
        growthBar K ^ IndependentSums.natTriangular (2 + M) :=
    mul_le_mul_of_nonneg_left hpowle hcL1
  linarith only [hstep1, hstep2]

/-- Past the burn-in, the decayed excess at either order is at most one. -/
theorem deepened_excess_le_one {K : ℝ} {M : ℕ} {sKw w : ℤ} {Gacc : ℕ}
    (hburnW : 1 + 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
        growthBar K ^ IndependentSums.natTriangular (2 + M) ≤
      (3 : ℝ) ^ ((M : ℝ) *
        ((w + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) :
    (3 : ℝ) ^ (-((M : ℝ) *
        ((w + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) *
      (1 + 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
        growthBar K ^ IndependentSums.natTriangular (2 + M)) ≤ 1 := by
  have hnegpos : (0 : ℝ) < (3 : ℝ) ^ (-((M : ℝ) *
      ((w + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hprod : (3 : ℝ) ^ (-((M : ℝ) *
      ((w + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) *
      (3 : ℝ) ^ ((M : ℝ) *
        ((w + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    simp
  calc
    (3 : ℝ) ^ (-((M : ℝ) *
        ((w + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) *
        (1 + 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
          growthBar K ^ IndependentSums.natTriangular (2 + M)) ≤
        (3 : ℝ) ^ (-((M : ℝ) *
          ((w + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) *
          (3 : ℝ) ^ ((M : ℝ) *
            ((w + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hburnW hnegpos.le
    _ = 1 := hprod

/-- **The collapsed second moment**: past the burn-in, the second moment of
the normalized source scale at the window top is at most `2`. -/
theorem lintegral_nss_sq_collapsed [NeZero d]
    {g : ℝ}
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {sKw : ℤ} (hsKw : growthBar K ≤ (3 : ℝ) ^ sKw)
    (w : ℤ) {Gacc : ℕ} (M : ℕ)
    (hDw : 0 ≤ w + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw)
    (hburnW : 1 + 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
        growthBar K ^ IndependentSums.natTriangular (2 + M) ≤
      (3 : ℝ) ^ ((M : ℝ) *
        ((w + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) :
    ∫⁻ a, ENNReal.ofReal
      (normalizedSourceScale S (w + ((Gacc + 1 : ℕ) : ℤ) - 1) a ^
        ((2 : ℕ) : ℝ)) ∂P ≤ ENNReal.ofReal 2 := by
  have hmom := lintegral_normalizedSourceScale_pow_deepened hdag hsKw 2 M
    (by omega) hDw
  rw [show sKw + (w + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw) =
      w + ((Gacc + 1 : ℕ) : ℤ) - 1 from by ring] at hmom
  refine hmom.trans (ENNReal.ofReal_le_ofReal ?_)
  have := deepened_excess_le_one hburnW
  linarith only [this]

end

end HCPolySupport.HighContrast.Quenched
