/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LocalProbability
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.OscillationProbability
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound

/-!
# AdmissibleGates

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The bad-event probability bounds under the printed admissibility

ABK26's Lemma `l.bad.event.probabilities` states its two probability bounds
under the admissibility display `e.bad.event.admissibility.prelim`,

```
E >= C(d) c_star^{-1} ,      gamma <= E^{-5} ,
```

with `C(d)` chosen by the lemma.  The two proofs in `LocalProbability.lean` and
`OscillationProbability.lean` carry, instead of that display, the explicit
proof-side gates `4 <= E` and `gamma <= 1/20` that the manuscript's own argument
uses.  This module proves the local gate implications: with the absolute bound
`Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves` in hand, the
single dimension-only choice

```
C(d) := max (25 / delta_osc(d)^2) 6
```

turns the printed admissibility into all three proof-side gates
(`unitGate`, `4 <= E`, `gamma <= 1/20`) and into the consequence
`E^{-2} <= c_star` of the same display.  Consumers may therefore cite the
manuscript's admissibility verbatim, at one dimension-only constant.

## Main definitions

* `admissibleConst`: the dimension-only constant `C(d)` above.

## Main results

* `gamma_le_one_div_twenty_of_four_le`: under `4 <= E`, the printed scale
  restriction `gamma <= E^{-5}` yields the oscillation branch's proof-side gate
  `gamma <= 1/20`.

## References

* ABK26, `l.bad.event.probabilities`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- A dimension-only local choice of the constant `C(d)` in the manuscript's
admissibility display `e.bad.event.admissibility.prelim`.  The first entry opens
the oscillation weak-Orlicz tail (`unitGate_of_admissible`), the second is
`4 C_0` for the absolute shell bound `C_0 = 3/2` of
`Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves`. -/
def admissibleConst (d : ℕ) : ℝ := max (25 / deltaOsc d ^ 2) 6

/-- With `4 <= E`, the printed scale restriction `gamma <= E^{-5}` implies the
oscillation branch's proof-side gate `gamma <= 1/20` (indeed `gamma <= 1/1024`). -/
theorem gamma_le_one_div_twenty_of_four_le (M : ABKModel d) {E : ℝ} (hE4 : 4 ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) : M.gamma ≤ 1 / 20 := by
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hE0 : (0 : ℝ) < E := by linarith
  have hsq : (16 : ℝ) ≤ E ^ 2 := by nlinarith
  have hquart : (256 : ℝ) ≤ E ^ 4 := by nlinarith
  have hfive : (1024 : ℝ) ≤ E ^ (5 : ℕ) := by nlinarith
  have hpos5 : (0 : ℝ) < E ^ (5 : ℕ) := by linarith
  have hEpow : E ^ (-5 : ℤ) = (E ^ (5 : ℕ))⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have hgle : M.gamma ≤ (E ^ (5 : ℕ))⁻¹ := by
    rw [← hEpow]
    exact hgamma
  have hgammaInv : E ^ (5 : ℕ) ≤ M.gamma⁻¹ := by
    rw [le_inv_comm₀ hpos5 hg]
    exact hgle
  have h20 : M.gamma ≤ (20 : ℝ)⁻¹ := (le_inv_comm₀ (by norm_num) hg).mp (by linarith)
  rw [show (20 : ℝ)⁻¹ = 1 / 20 by norm_num] at h20
  exact h20

end

end Algsuperdiff.Section3.Provider.BadEvents
