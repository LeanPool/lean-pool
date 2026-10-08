/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowCellBounds
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneySquareWeights
public import LeanPool.HighContrastHomogenization.Setup.TransportObjects

/-!
# High-contrast homogenization: Provider.Transport.TransportCoefficients

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The transport source coefficients

The source residual the transport pays at a target level of the new grid is
measured by the two source coefficients of the transport estimate: the
continued one `𝖣_cont^{tr,𝒮}(q,q') = C_dK(q,q')κ_𝐄B_qB_{q'}χ_g𝒰²`, which the
old-times-new
orientation of the boundary rows produces, and the early one
`𝖣_early^{tr,𝒮}(q') = C_dκ_𝐄B_{q'}²𝒰²`, which the new-squared orientation of the
whole-cell rows produces.  The total coefficient
`𝖣_src^{tr,𝒮} = 1 + 𝖣_cont^{tr,𝒮} + 𝖣_early^{tr,𝒮}` is what the transported
source majorant is built from.

This file records the order relations between the three that every source
estimate reads.  Each factor of the two rows is nonnegative — the cross-grid
factor is at least one, the reference ratio is an infimum of nonnegative
numbers, the boundary constant is a nonnegative multiple of a square root, and
the geometric series `χ_g` is positive below the critical exponent — so the two
rows are nonnegative, the total is at least one, and it dominates each of them.
Without the last two the printed majorant would not majorize the printed rows
and the source estimate would be false as written.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

noncomputable section

variable {d : ℕ}

/-- The reference ratio is nonnegative, being an infimum of nonnegative
numbers. -/
theorem zero_le_kappaRef (E : BlockMat d) : 0 ≤ kappaRef E := by
  rw [kappaRef, blockSize]
  exact Real.sInf_nonneg fun _ hx => hx.1

/-- The geometric series `χ_g = (3^{1-g} - 1)^{-1}` is positive below the
critical exponent. -/
theorem zero_lt_chiG {g : ℝ} (hg : g < 1) : 0 < chiG g := by
  have h : (1 : ℝ) < (3 : ℝ) ^ (1 - g) :=
    (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr
      (Or.inl ⟨by norm_num, by linarith only [hg]⟩)
  exact inv_pos.mpr (by linarith only [h])

/-- The continued transport coefficient
`𝖣_cont^{tr,𝒮}(q,q') = C_dK(q,q')κ_𝐄B_qB_{q'}χ_g𝒰²` is nonnegative. -/
theorem zero_le_transportContCoeff {Cd g : ℝ} (hCd : 0 ≤ Cd) (hg : g < 1)
    (E : BlockMat d) (jStar : ℤ) (mu mu' : Mat d) :
    0 ≤ transportContCoeff Cd g E jStar mu mu' :=
  mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCd
    (le_trans zero_le_one (one_le_gridRatio _ _))) (zero_le_kappaRef E))
    (zero_le_boundaryConst hCd hg mu)) (zero_le_boundaryConst hCd hg mu'))
    (zero_lt_chiG hg).le) (by norm_num)

/-- The early transport coefficient `𝖣_early^{tr,𝒮}(q') = C_dκ_𝐄B_{q'}²𝒰²` is
nonnegative. -/
theorem zero_le_transportEarlyCoeff {Cd g : ℝ} (hCd : 0 ≤ Cd) (hg : g < 1)
    (E : BlockMat d) (mu' : Mat d) : 0 ≤ transportEarlyCoeff Cd g E mu' :=
  mul_nonneg (mul_nonneg (mul_nonneg hCd (zero_le_kappaRef E))
    (pow_nonneg (zero_le_boundaryConst hCd hg mu') 2)) (by norm_num)

/-- **The total transport source coefficient is at least one**, being one plus
the two nonnegative rows. -/
theorem one_le_transportSrcCoeff {Cd g : ℝ} (hCd : 0 ≤ Cd) (hg : g < 1)
    (E : BlockMat d) (jStar : ℤ) (mu mu' : Mat d) :
    1 ≤ transportSrcCoeff Cd g E jStar mu mu' := by
  have hc := zero_le_transportContCoeff hCd hg E jStar mu mu'
  have he := zero_le_transportEarlyCoeff hCd hg E mu'
  rw [transportSrcCoeff]
  linarith only [hc, he]

/-- The continued row is dominated by the total source coefficient. -/
theorem transportContCoeff_le_transportSrcCoeff {Cd g : ℝ} (hCd : 0 ≤ Cd)
    (hg : g < 1) (E : BlockMat d) (jStar : ℤ) (mu mu' : Mat d) :
    transportContCoeff Cd g E jStar mu mu' ≤
      transportSrcCoeff Cd g E jStar mu mu' := by
  have he := zero_le_transportEarlyCoeff hCd hg E mu'
  rw [transportSrcCoeff]
  linarith only [he]

/-- The early row is dominated by the total source coefficient. -/
theorem transportEarlyCoeff_le_transportSrcCoeff {Cd g : ℝ} (hCd : 0 ≤ Cd)
    (hg : g < 1) (E : BlockMat d) (jStar : ℤ) (mu mu' : Mat d) :
    transportEarlyCoeff Cd g E mu' ≤ transportSrcCoeff Cd g E jStar mu mu' := by
  have hc := zero_le_transportContCoeff hCd hg E jStar mu mu'
  rw [transportSrcCoeff]
  linarith only [hc]

end

end Transport
end HighContrast
end HCPolySupport
