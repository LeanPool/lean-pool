/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Initialization.Boundary
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.ColourSeparation
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyRows
public import LeanPool.HighContrastHomogenization.Geometry.DeterminantLoss
public import LeanPool.HighContrastHomogenization.Geometry.OperatorOrder

/-!
# High-contrast homogenization: Provider.Window.BurnSeries

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Rounded-grid and burn-series bounds

The inverse of a rounded grid is uniformly bounded.  The Whitney decay and
the source burn discount combine into the geometric series defining `zetaG`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Window

open scoped MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The inverse spectral norm of a rounded grid is at most `101 / 100`. -/
theorem norm_inv_roundedGrid_le {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {m : Mat d} (hm : m.PosDef) :
    ‖(roundedGrid l m)⁻¹‖ ≤ (101 / 100 : ℝ) := by
  let q : Mat d := roundedGrid l m
  have hq : q.PosDef := Recurrence.posDef_roundedGrid hl hm
  have hc : (0 : ℝ) < 100 / 101 := by norm_num
  have hcI : ((100 / 101 : ℝ) • (1 : Mat d)).PosDef :=
    Matrix.PosDef.one.smul hc
  have hlo : (100 / 101 : ℝ) • (1 : Mat d) ≤ q := by
    refine Matrix.le_iff.mpr <|
      Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        (hq.isHermitian.sub hcI.isHermitian) ?_
    intro x
    have h := Recurrence.dotProduct_mulVec_roundedGrid_ge hl hm x
    change 0 ≤ dotProduct x
      (Matrix.mulVec (q - (100 / 101 : ℝ) • (1 : Mat d)) x)
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul]
    simpa only [smul_eq_mul] using! sub_nonneg.mpr h
  have hinv : q⁻¹ ≤ (101 / 100 : ℝ) • (1 : Mat d) := by
    have h := inv_le_inv_of_le hcI hq hlo
    rw [inv_smul_of_isUnit hc.ne' (by simp : IsUnit (1 : Mat d).det), inv_one] at h
    norm_num at h
    exact h
  exact norm_le_of_le_smul_one hq.inv.posSemidef (by norm_num) hinv

/-- Lowering the cell scale by `u` increases the burn discount by at most
`3^(g u)`. -/
theorem burnDiscount_sub_nat_le {g : ℝ} (hg : 0 ≤ g) (jStar r : ℤ) (u : ℕ) :
    burnDiscount g jStar (r - (u : ℤ)) ≤
      burnDiscount g jStar r * (3 : ℝ) ^ (g * (u : ℝ)) := by
  let A : ℝ := (jStar : ℝ) - (r : ℝ)
  have hu : (0 : ℝ) ≤ u := by positivity
  have hmax : max (A + (u : ℝ)) 0 ≤ max A 0 + (u : ℝ) := by
    refine max_le ?_ ?_
    · linarith only [le_max_left A 0]
    · linarith only [le_max_right A 0, hu]
  have hexp : g * max (A + (u : ℝ)) 0 ≤
      g * max A 0 + g * (u : ℝ) := by
    have := mul_le_mul_of_nonneg_left hmax hg
    linarith only [this]
  rw [burnDiscount, burnDiscount]
  have hcast : (jStar : ℝ) - ((r - (u : ℤ) : ℤ) : ℝ) = A + (u : ℝ) := by
    dsimp [A]
    push_cast
    ring
  rw [hcast]
  calc
    (3 : ℝ) ^ (g * max (A + (u : ℝ)) 0) ≤
        (3 : ℝ) ^ (g * max A 0 + g * (u : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (3 : ℝ) ^ (g * max A 0) * (3 : ℝ) ^ (g * (u : ℝ)) := by
      rw [Real.rpow_add (by norm_num)]

/-- The Whitney factor and burn discount have the `zetaG` total printed in
the source-window estimate. -/
theorem summable_zpow_mul_burnDiscount_and_tsum_le {g : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (jStar r : ℤ) :
    Summable (fun u : ℕ =>
      (3 : ℝ) ^ (-(u : ℤ)) * burnDiscount g jStar (r - (u : ℤ))) ∧
    ∑' u : ℕ, (3 : ℝ) ^ (-(u : ℤ)) *
        burnDiscount g jStar (r - (u : ℤ)) ≤
      zetaG g * burnDiscount g jStar r := by
  let ratio : ℝ := (3 : ℝ) ^ (-(1 - g))
  have hratio0 : 0 ≤ ratio := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hratio1 : ratio < 1 := by
    dsimp [ratio]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hg.2])
  have hgeom : Summable fun u : ℕ => ratio ^ u :=
    summable_geometric_of_lt_one hratio0 hratio1
  have hpoint : ∀ u : ℕ,
      (3 : ℝ) ^ (-(u : ℤ)) * burnDiscount g jStar (r - (u : ℤ)) ≤
        ratio ^ u * burnDiscount g jStar r := by
    intro u
    have hburn := burnDiscount_sub_nat_le hg.1 jStar r u
    have hz : (0 : ℝ) ≤ (3 : ℝ) ^ (-(u : ℤ)) := by positivity
    refine (mul_le_mul_of_nonneg_left hburn hz).trans_eq ?_
    dsimp [ratio]
    have hzrw : (3 : ℝ) ^ (-(u : ℤ)) = (3 : ℝ) ^ (-(u : ℝ)) := by
      rw [← Real.rpow_intCast]
      norm_num
    calc
      (3 : ℝ) ^ (-(u : ℤ)) *
          (burnDiscount g jStar r * (3 : ℝ) ^ (g * (u : ℝ))) =
          ((3 : ℝ) ^ (-(u : ℝ)) * (3 : ℝ) ^ (g * (u : ℝ))) *
            burnDiscount g jStar r := by
        rw [hzrw]
        ring
      _ = (3 : ℝ) ^ (-(u : ℝ) + g * (u : ℝ)) *
            burnDiscount g jStar r := by
        rw [← Real.rpow_add (by norm_num)]
      _ = (3 : ℝ) ^ (-(1 - g) * (u : ℝ)) *
            burnDiscount g jStar r := by ring_nf
      _ = ((3 : ℝ) ^ (-(1 - g))) ^ u * burnDiscount g jStar r := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hleft0 : ∀ u : ℕ, 0 ≤
      (3 : ℝ) ^ (-(u : ℤ)) * burnDiscount g jStar (r - (u : ℤ)) :=
    fun _ => mul_nonneg (by positivity) (by rw [burnDiscount]; positivity)
  have hrightSummable : Summable fun u : ℕ =>
      ratio ^ u * burnDiscount g jStar r := hgeom.mul_right _
  have hleftSummable := Summable.of_nonneg_of_le hleft0 hpoint hrightSummable
  refine ⟨hleftSummable, (hleftSummable.tsum_le_tsum hpoint hrightSummable).trans_eq ?_⟩
  rw [tsum_mul_right, tsum_geometric_of_lt_one hratio0 hratio1]
  rfl

end

end Window
end HighContrast
end HCPolySupport
