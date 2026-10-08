/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.EccentricityFoldFactor

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.Root.Dirichlet.FoldedFrameExponent

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The frame exponent, split into its two lengths

The response aggregation's frame exponent is `(b - kappa) M + kappa L`, where
`L` is the certificate's activation generation and `M` is the enclosing parent
generation, itself bounded by `L + J + 2` with `J` the bracket of the outer
sandwich radius.  Splitting `M` separates the two lengths: the part carried by
`L` collapses to the single power `max b kappa` of the activation length, and
the part carried by `J` is a factor in the sandwich radius alone.

The split is uniform in the sign of `b - kappa`, which the response window's
order data does not fix, so both cases are handled: the parent generation is at
least one, so a negative exponent is already harmless, and a nonnegative one is
carried by the upper bound on the parent.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

noncomputable section

/-! ## Two elementary truncations -/

/-- A triadic power at an exponent between one and an upper bound is below the
truncation of the power at that upper bound, whatever the sign of the rate. -/
theorem rpow_three_mul_le_max_one_of_le {e m n : ℝ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (3 : ℝ) ^ (e * m) ≤ max 1 ((3 : ℝ) ^ (e * n)) := by
  rcases le_or_gt 0 e with he | he
  · refine le_trans ?_ (le_max_right _ _)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left hmn he)
  · refine le_trans ?_ (le_max_left _ _)
    have hle : e * m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg he.le
      (le_trans zero_le_one hm)
    calc (3 : ℝ) ^ (e * m) ≤ (3 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = 1 := Real.rpow_zero _

/-- Truncation at one is submultiplicative on nonnegative factors. -/
theorem max_one_mul_le_mul_max_one {X Y : ℝ} (hY : 0 ≤ Y) :
    max 1 (X * Y) ≤ max 1 X * max 1 Y := by
  have hX1 : (1 : ℝ) ≤ max 1 X := le_max_left _ _
  have hY1 : (1 : ℝ) ≤ max 1 Y := le_max_left _ _
  refine max_le ?_ ?_
  · calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ max 1 X * max 1 Y :=
        mul_le_mul hX1 hY1 zero_le_one (le_trans zero_le_one hX1)
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) hY
      (le_trans zero_le_one hX1)

/-! ## The activation half -/

/-- **The activation half collapses.**  Truncating the parent's contribution at
one and multiplying by the certificate's own contribution gives a single power
of the activation length, at the larger of the two orders. -/
theorem max_one_rpow_mul_rpow_le {b kappa L : ℝ} (hL : 0 ≤ L) :
    max 1 ((3 : ℝ) ^ ((b - kappa) * L)) * (3 : ℝ) ^ (kappa * L) ≤
      (3 : ℝ) ^ (max b kappa * L) := by
  rcases le_or_gt kappa b with hbk | hbk
  · have hnonneg : 0 ≤ (b - kappa) * L :=
      mul_nonneg (by linarith only [hbk]) hL
    have hone : (1 : ℝ) ≤ (3 : ℝ) ^ ((b - kappa) * L) := by
      calc (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 3).symm
        _ ≤ (3 : ℝ) ^ ((b - kappa) * L) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hnonneg
    rw [max_eq_right hone, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      max_eq_left hbk]
    apply le_of_eq
    congr 1
    ring
  · have hnonpos : (b - kappa) * L ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith only [hbk]) hL
    have hone : (3 : ℝ) ^ ((b - kappa) * L) ≤ 1 := by
      calc (3 : ℝ) ^ ((b - kappa) * L) ≤ (3 : ℝ) ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hnonpos
        _ = 1 := Real.rpow_zero _
    rw [max_eq_left hone, one_mul, max_eq_right hbk.le]

/-- The triadic power at a scaled generation is the generation's power raised to
the scale. -/
theorem rpow_three_mul_eq_rpow_rpow (c L : ℝ) :
    (3 : ℝ) ^ (c * L) = ((3 : ℝ) ^ L) ^ c := by
  rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

/-! ## The split -/

/-- **The frame exponent splits.**  The activation length carries a single
power at the larger of the two orders; the outer sandwich bracket carries the
rest, truncated at one. -/
theorem rpow_three_frameExponent_le {b kappa M L J : ℝ}
    (hM1 : 1 ≤ M) (hMle : M ≤ L + J + 2) (hL : 0 ≤ L) :
    (3 : ℝ) ^ ((b - kappa) * M + kappa * L) ≤
      ((3 : ℝ) ^ L) ^ (max b kappa) *
        max 1 ((3 : ℝ) ^ ((b - kappa) * (J + 2))) := by
  have hsplit : (3 : ℝ) ^ ((b - kappa) * M + kappa * L) =
      (3 : ℝ) ^ ((b - kappa) * M) * (3 : ℝ) ^ (kappa * L) :=
    Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _
  have hparent : (3 : ℝ) ^ ((b - kappa) * M) ≤
      max 1 ((3 : ℝ) ^ ((b - kappa) * (L + J + 2))) :=
    rpow_three_mul_le_max_one_of_le hM1 hMle
  have hfactor : (3 : ℝ) ^ ((b - kappa) * (L + J + 2)) =
      (3 : ℝ) ^ ((b - kappa) * L) * (3 : ℝ) ^ ((b - kappa) * (J + 2)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hsub : max 1 ((3 : ℝ) ^ ((b - kappa) * (L + J + 2))) ≤
      max 1 ((3 : ℝ) ^ ((b - kappa) * L)) *
        max 1 ((3 : ℝ) ^ ((b - kappa) * (J + 2))) := by
    rw [hfactor]
    exact max_one_mul_le_mul_max_one (Real.rpow_nonneg (by norm_num) _)
  have hpos : (0 : ℝ) ≤ (3 : ℝ) ^ (kappa * L) :=
    Real.rpow_nonneg (by norm_num) _
  have hmaxJ : (0 : ℝ) ≤ max 1 ((3 : ℝ) ^ ((b - kappa) * (J + 2))) :=
    le_trans zero_le_one (le_max_left _ _)
  calc (3 : ℝ) ^ ((b - kappa) * M + kappa * L)
      = (3 : ℝ) ^ ((b - kappa) * M) * (3 : ℝ) ^ (kappa * L) := hsplit
    _ ≤ (max 1 ((3 : ℝ) ^ ((b - kappa) * L)) *
          max 1 ((3 : ℝ) ^ ((b - kappa) * (J + 2)))) * (3 : ℝ) ^ (kappa * L) :=
        mul_le_mul_of_nonneg_right (hparent.trans hsub) hpos
    _ = (max 1 ((3 : ℝ) ^ ((b - kappa) * L)) * (3 : ℝ) ^ (kappa * L)) *
          max 1 ((3 : ℝ) ^ ((b - kappa) * (J + 2))) := by ring
    _ ≤ (3 : ℝ) ^ (max b kappa * L) *
          max 1 ((3 : ℝ) ^ ((b - kappa) * (J + 2))) :=
        mul_le_mul_of_nonneg_right (max_one_rpow_mul_rpow_le hL) hmaxJ
    _ = ((3 : ℝ) ^ L) ^ (max b kappa) *
          max 1 ((3 : ℝ) ^ ((b - kappa) * (J + 2))) := by
        rw [rpow_three_mul_eq_rpow_rpow]

end

end RowSupply
end HighContrast
end HCPolySupport
