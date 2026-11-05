/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryWindowPoincare
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet

/-!
# BoundaryWindowNormalized

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The window norms in the anchor's volume-normalized carrier

The boundary window estimates are stated against CoarseGraining's own domain
measure `volume.restrict W'`, while the frozen statement prices every window
norm against the **volume-normalized** measure
`Support.normalizedVolumeMeasureOn W'`.  This file records the identity that
relates the two carriers: an `L²` norm against the normalized measure is the
restricted one times the scalar `(vol W')^{-1/2}`, which does not depend on the
function.  Since the boundary estimates are homogeneous — the *same* window on
both sides — that scalar cancels exactly and no constant changes.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The volume-normalized `L²` norm is the restricted one times a scalar that
does not depend on the function. -/
theorem eLpNorm_normalizedVolumeMeasureOn_eq (A : Set (Vec d)) (f : Vec d → ℝ) :
    eLpNorm f 2 (Support.normalizedVolumeMeasureOn A) =
      ((volume A)⁻¹) ^ (1 / 2 : ℝ) * eLpNorm f 2 (volume.restrict A) := by
  rw [Support.normalizedVolumeMeasureOn_def,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  norm_num

end

end Algsuperdiff.Section4.Provider.ExcessDecay
