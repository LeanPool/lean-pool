/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.CampanatoRepresentative
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Campanato.TriadicRadii

/-!
# TriadicTelescope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Canonical averages on shrinking triadic balls

This file records the means of a function on the balls with radii
`R 3 ^ (-k)` and the corresponding limit-based representative.

## Main definitions

* `campanatoAverage f R x k`, `campanatoRepresentative f R x`.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Campanato

open HCPolySupport Filter
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

variable {d : ℕ}

/-! ## Averages and representative -/

/-- The mean of `f` over the sup-ball of radius `R 3 ^ (-k)` centred at `x`. -/
def campanatoAverage (f : Vec d → ℝ) (R : ℝ) (x : Vec d) (k : ℕ) : ℝ :=
  volumeAverage (Metric.ball x (triadicRadius R k)) f

/-- **The canonical Campanato representative**: the limit of the means over the
shrinking triadic balls at `x`. -/
def campanatoRepresentative (f : Vec d → ℝ) (R : ℝ) (x : Vec d) : ℝ :=
  limUnder atTop (campanatoAverage f R x)

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Campanato
