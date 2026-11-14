/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.Carrier

/-!
# SourceExponent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Arithmetic of the source exponent

The energy test uses the embedding `L^p(B_1) ⊆ L²(B_r)`.  It is valid in
the manuscript's regime `d ≥ 2`; this file makes that otherwise implicit
dimension restriction and the identity `d / p = 1 - alpha` explicit.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

/-- In the intended PDE dimensions, the printed exponent is at least two, so
the `L^p` datum can be used in the quadratic energy test. -/
theorem two_le_schauderSourceExponent {d : ℕ} {alpha : ℝ}
    (hd : 2 ≤ d) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) :
    2 ≤ schauderSourceExponent d alpha := by
  unfold schauderSourceExponent
  have hden : 0 < 1 - alpha := sub_pos.mpr halpha1
  apply (le_div_iff₀ hden).2
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith only [hdreal, halpha0]

/-- The scale exponent in the forcing row is exactly `1-alpha`. -/
theorem dimension_div_schauderSourceExponent {d : ℕ} {alpha : ℝ}
    (hd : 1 ≤ d) (halpha : alpha < 1) :
    (d : ℝ) / schauderSourceExponent d alpha = 1 - alpha := by
  unfold schauderSourceExponent
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have ha0 : 1 - alpha ≠ 0 := ne_of_gt (sub_pos.mpr halpha)
  field_simp

end


end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
