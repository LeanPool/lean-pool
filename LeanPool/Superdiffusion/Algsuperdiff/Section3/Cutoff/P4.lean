/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Definitions

/-!
# P4

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Dimension-only parameters for the cutoff `(P4)` route

The quantitative coarse-grained ellipticity input in CoarseGraining separates
its dimension-only exponent inequalities from its two genuine coefficient-law
moment obligations.  This file fixes the former once and for all for the actual
Section 3 cutoff route.  It deliberately does **not** assert those moments:
they must be proved for `coefficientCutoffLaw` from the cutoff's local
controls.

The choice is
`sUpper = sLower = 1/4` and `xi = 8*d + 1`.  It works for every manuscript
dimension `d >= 2`, and introduces no analytic assumption.
-/

namespace Algsuperdiff.Section3.Cutoff

open HCPolySupport.Book

noncomputable section

/-- The explicit dimension-only `(P4)` parameters used for actual cutoff laws.  The two
law-dependent integrability fields of `QuantitativeCoarseGrainedEllipticity`
are intentionally absent here and are proved only after the local
coarse-ellipticity observables are constructed. -/
def cutoffP4Params (d : ℕ) (hd : 2 ≤ d) :
    Ch05.QuantitativeCoarseGrainedEllipticityParams d where
  sUpper := (1 : ℝ) / 4
  sLower := (1 : ℝ) / 4
  xi := 8 * d + 1
  two_le_dim := hd
  sUpper_nonneg := by norm_num
  sUpper_lt_one := by norm_num
  sLower_nonneg := by norm_num
  sLower_lt_one := by norm_num
  xi_gt_two_mul_dim := by
    norm_num
    exact_mod_cast (show 2 * d < 8 * d + 1 by omega)
  sum_lt_one := by norm_num
  dim_div_xi_lt_min := by
    rw [min_eq_left]
    · have hxi : (0 : ℝ) < (8 * d + 1 : ℕ) := by positivity
      rw [div_lt_iff₀ hxi]
      norm_num
      have hdReal : (0 : ℝ) ≤ d := by positivity
      nlinarith
    · norm_num

/-- The selected upper exponent is literally one quarter. -/
@[simp]
theorem cutoffP4Params_sUpper (d : ℕ) (hd : 2 ≤ d) :
    (cutoffP4Params d hd).sUpper = (1 : ℝ) / 4 :=
  rfl

/-- The selected lower exponent is literally one quarter. -/
@[simp]
theorem cutoffP4Params_sLower (d : ℕ) (hd : 2 ≤ d) :
    (cutoffP4Params d hd).sLower = (1 : ℝ) / 4 :=
  rfl

end

end Algsuperdiff.Section3.Cutoff
