/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.AffineDetBound

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.GaugeAffineFactor

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The normalized-root affine loss in the negative-one transport is bounded
by a dimension-only factor times the witness eccentricity. -/
theorem sqrt_H1AffineFactor_normalizedRoot_le
    [NeZero d] {S : Mat d} (hS : S.PosDef) :
    Real.sqrt (h1AffineFactor (Selection.normalizedRoot S)) ≤
      Real.sqrt d * witnessEccentricity S := by
  let q : Mat d := Selection.normalizedRoot S
  have hqT : matTranspose q = q := by
    have hq := normalizedRoot_posDef_of_posDef hS
    simpa only [matTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using! hq.isHermitian
  have hdet := absDet_rpow_two_div_le q
  have hnorm : ‖matTranspose q‖ ^ 2 ≤
      (Real.sqrt d * ‖q‖) ^ 2 := by
    rw [hqT]
    have hd : (1 : ℝ) ≤ Real.sqrt d := by
      rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
      · simpa only [one_pow] using
          (show (1 : ℝ) ≤ (d : ℝ) by
            exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)))
      · exact Nat.cast_nonneg d
    have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
    exact pow_le_pow_left₀ hq0
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hd hq0) 2
  have hfactor : h1AffineFactor q ≤
      (Real.sqrt d * ‖q‖) ^ 2 := by
    unfold h1AffineFactor
    exact max_le hdet hnorm
  calc
    Real.sqrt (h1AffineFactor q) ≤
        Real.sqrt ((Real.sqrt d * ‖q‖) ^ 2) :=
      Real.sqrt_le_sqrt hfactor
    _ = Real.sqrt d * ‖q‖ := Real.sqrt_sq (by positivity)
    _ = Real.sqrt d * witnessEccentricity S := by
      rw [Selection.norm_normalizedRoot_eq_witnessEccentricity hS]

end

end HighContrast
end HCPolySupport
