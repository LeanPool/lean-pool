/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.HomogenizedEccentricityBound
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.ScalarTailScaleFold
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootInterfaceArithmetic

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.EccentricityFoldFactor

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Folding the homogenized eccentricity into the homogenization length

The reference text's homogenization length carries the aspect ratio of the
homogenized matrix: the estimate with a law-free amplitude is read above a
length that has been enlarged by the corresponding root.  Replacing the
homogenization length `X` by `X * G`, the polynomial length `Lpoly` by
`Lpoly * G` and the length constant by a correspondingly larger one, for a
common positive factor `G` determined by the homogenized matrix, leaves every
clause of the statement valid: the exceedance event is literally unchanged
because the common factor cancels on both sides of its threshold, the length
bound survives because the factor is itself polynomial in the reference datum,
and each remaining clause is weakened, its premise being harder to satisfy and
its right-hand side larger.

This file proves those clause transfers, and the bound on the fold factor built
from the eccentricity of the homogenized matrix.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The fold factor -/

/-- The witness eccentricity is a square root, hence nonnegative. -/
theorem witnessEccentricity_nonneg (m : Mat d) : 0 ≤ witnessEccentricity m :=
  Real.sqrt_nonneg _

/-- The fold factor attached to a homogenized matrix: a power of its witness
eccentricity, read at least one. -/
@[expose]
def eccentricityFoldFactor (abar : Mat d) (p : ℝ) : ℝ :=
  max 1 (witnessEccentricity (symmPart abar) ^ p)

theorem one_le_eccentricityFoldFactor (abar : Mat d) (p : ℝ) :
    1 ≤ eccentricityFoldFactor abar p :=
  le_max_left _ _

theorem eccentricityFoldFactor_pos (abar : Mat d) (p : ℝ) :
    0 < eccentricityFoldFactor abar p :=
  lt_of_lt_of_le zero_lt_one (one_le_eccentricityFoldFactor abar p)

theorem rpow_le_eccentricityFoldFactor (abar : Mat d) (p : ℝ) :
    witnessEccentricity (symmPart abar) ^ p ≤ eccentricityFoldFactor abar p :=
  le_max_right _ _

/-- **The fold factor is polynomial in the reference datum.**  With the law-level
eccentricity bound, the fold factor is below the printed polynomial length base
raised to a law-free exponent. -/
theorem eccentricityFoldFactor_le_rpow {abar : Mat d} {base p : ℝ}
    (hbase : 1 ≤ base) (hp : 0 ≤ p)
    (hecc : witnessEccentricity (symmPart abar) ≤ base ^ (5 : ℝ)) :
    eccentricityFoldFactor abar p ≤ base ^ (5 * p) := by
  have hbase0 : (0 : ℝ) < base := lt_of_lt_of_le zero_lt_one hbase
  have hone : (1 : ℝ) ≤ base ^ (5 * p) :=
    one_le_rpow_of_one_le hbase (by positivity)
  refine max_le hone ?_
  have hstep : witnessEccentricity (symmPart abar) ^ p ≤ (base ^ (5 : ℝ)) ^ p :=
    Real.rpow_le_rpow (witnessEccentricity_nonneg _) hecc hp
  rwa [← Real.rpow_mul hbase0.le] at hstep

/-! ## The polynomial length clause -/

/-- The polynomial length bound survives the fold: the product of a length below
`base ^ C` and a factor below `base ^ C'` is below `base ^ (C + C')`. -/
theorem mul_le_rpow_add {base Lpoly G C C' : ℝ}
    (hbase : 1 ≤ base) (hG : 0 ≤ G)
    (hLbound : Lpoly ≤ base ^ C) (hGbound : G ≤ base ^ C') :
    Lpoly * G ≤ base ^ (C + C') := by
  have hbase0 : (0 : ℝ) < base := lt_of_lt_of_le zero_lt_one hbase
  have hCnonneg : (0 : ℝ) ≤ base ^ C := (Real.rpow_pos_of_pos hbase0 C).le
  rw [Real.rpow_add hbase0]
  exact mul_le_mul hLbound hGbound hG hCnonneg

/-! ## The exceedance event -/

/-- **The exceedance event is unchanged by the fold.**  Multiplying both the
polynomial length and the homogenization length by the same positive factor
leaves the threshold event fixed, so the two-part tail bound transfers after the
length constant is enlarged. -/
theorem measureReal_foldedThreshold_le {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsFiniteMeasure P] {X : Omega → ℝ} {c c' L t G : ℝ}
    (hL : 0 ≤ L) (ht : 0 ≤ t) (hG : 0 < G) (hcc : c ≤ c') :
    P.real {a | c' * (L * G) * t ≤ X a * G} ≤ P.real {a | c * L * t ≤ X a} := by
  refine measureReal_mono (fun a ha => ?_) (measure_ne_top P _)
  have hmem : c' * (L * G) * t ≤ X a * G := ha
  have hstep : c' * L * t * G ≤ X a * G := by
    calc c' * L * t * G = c' * (L * G) * t := by ring
      _ ≤ X a * G := hmem
  have hcancel : c' * L * t ≤ X a := le_of_mul_le_mul_right hstep hG
  exact le_trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcc hL) ht) hcancel

/-! ## The remaining clauses -/

/-- **The corrector decay factor is larger at the folded length.**  Its base is a
ratio with the homogenization length in the denominator and a negative exponent,
so enlarging the length enlarges the factor. -/
theorem corrector_factor_mono {r x x' kappa : ℝ}
    (hx : 0 < x) (hxx : x ≤ x') (hr : 0 < r) (hkappa : 0 < kappa) :
    (r / x) ^ (-kappa) ≤ (r / x') ^ (-kappa) := by
  have hx' : (0 : ℝ) < x' := lt_of_lt_of_le hx hxx
  have h1 : (0 : ℝ) < r / x := div_pos hr hx
  have h2 : (0 : ℝ) < r / x' := div_pos hr hx'
  exact (Real.rpow_le_rpow_iff_of_neg h1 h2 (neg_neg_of_pos hkappa)).2
    (div_le_div_of_nonneg_left hr.le hx hxx)

/-- **The regularity radius window shrinks under the fold.**  The frozen
Lipschitz and `C¹` clauses quantify over radii above the homogenization length,
so the folded window is contained in the unfolded one. -/
theorem Icc_foldedScale_subset {x x' R : ℝ} (hxx : x ≤ x') :
    Set.Icc x' R ⊆ Set.Icc x R :=
  Set.Icc_subset_Icc_left hxx

/-! ## The folded length itself -/

end

end RowSupply
end HighContrast
end HCPolySupport
