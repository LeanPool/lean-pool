/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LocalProbability
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.OscillationProbability

/-!
# UnionBounds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Union bounds for the bad events of ABK26, Section 3.3

This module assembles the two per-event probability bounds of
`l.bad.event.probabilities` (ABK26) into bounds for the three composite events
of `sss.bad.cubes`:

* `B_osc(z + square_j)` — the scale union `union_{L > j} B_{osc,L}(z+square_j)`
  of `e.Bosc.decomp`;
* `B(z + square_j) = B_osc union B_loc` of `e.B.def`;
* `B^*(z + square_j)` — the nine-generation extension of
  `e.Bext.def`.

The last is the object whose probability enters the density threshold of
`l.percolation.bad.clusters` (`e.density.bound.bad.clusters`, ABK26).

## The oscillation union bound

The summation is elementary: writing `kappa = delta_osc(d)^2 c_star gamma^{-1}
/ 25` for the rate of `measureReal_badOscAt_le`, the manuscript's admissibility
gate `unitGate` (supplied by `unitGate_of_admissible`) says exactly `1 <=
kappa`, and

```
sum_{n >= 1} exp(- kappa 3^{2(4/5 - gamma) n}) <= sum_{n >= 1} exp(- 3 kappa n)
                                              <= exp(- kappa) .
```

No hypothesis beyond the gate that `measureReal_badOscAt_le` already carries is
used.

## Gates carried

Every statement below that consumes the local branch carries the same gate
verbatim and adds nothing else.  The bound `E^{-2} <= c_star`, used to express
the oscillation rate through `E`, is the manuscript's own admissibility `E >= C
c_star^{-1}` at `C >= 1` together with `E >= 1`.

## Main definitions

* `badRateConst`: the dimension-only rate `c(d) = min(delta_osc(d)^2/25, 1/512)`
  shared by the two branches of `e.B.def`.

## Main results

* `badRateConst_pos`: that rate is strictly positive.

## References

* ABK26, `sss.bad.cubes`.
* ABK26, `l.bad.event.probabilities`.
* ABK26, `l.percolation.bad.clusters`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The combined bad event -/

/-- The dimension-only rate `c(d) = min(delta_osc(d)^2/25, 1/512)` common to the
two branches of `e.B.def`. -/
def badRateConst (d : ℕ) : ℝ := min ((1 / 25 : ℝ) * deltaOsc d ^ 2) (1 / 512)

theorem badRateConst_pos (d : ℕ) : 0 < badRateConst d := by
  refine lt_min ?_ (by norm_num)
  have := deltaOsc_pos d
  positivity

end

end Algsuperdiff.Section3.Provider.BadEvents
