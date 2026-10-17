/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.ClosureInteriorSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.ClosureTerminal
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5SampDef
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.StepProducers

/-!
# ClosureTerminalStrip

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two terminal compositions of the closure chain

ABK26, `l.approximate.recurrence.formula`, `l.integrate.approx.recurrence`.

## What this module composes

`Closure.ClosureTerminal.diffusivity_asymptotics_of_twoSidedClosure` turns
`Closure.NodeContract.TwoSidedClosure d` into the three conclusions carried by
`Algsuperdiff.Frozen.Section3.diffusivity_asymptotics`.  This module runs the
consumed route to that contract all the way through:

| route | `ClosureSplitInput` producer | surviving inputs |
|---|---|---|
| interior mesh + strip | `Closure.ClosureInteriorSplit.closureSplitInput_of_interiorEnvelope` |
`ClosureInteriorBesovEnvelopeInput d`, `ClosureStripRemainder d` |

A full-mesh sibling route once ran here as well, on the single input
`Closure.GammaTenCloserAssembly.ClosureBesovEnvelopeInput d`.  It had no consumer
once the interior route carried the terminal, and its composition was removed;
git history keeps it.

The Step-4 and Step-5 endpoints are supplied outright, by
`Closure.StepProducers.closureStep4Input` and
`Closure.Step5SampDef.closureStep5Input`; the window conversion from the
contract's wide shell budget `h <= 6 cstar cgamma^{-1}` to the flow spine's
narrow `(m : R) <= (n : R) + cstar cgamma^{-1}`, and from `shellDrift` to
`recurrenceIncrement`, is done by `Closure.ClosureTerminal`.

## What is proved

* `twoSidedClosure_of_interiorEnvelope` --- the closure contract from the
  interior-mesh oscillation input and the strip residual.
* `diffusivity_asymptotics_of_strip` --- **the terminal composition**: the frozen
  conclusion from the same two inputs.

## Binders, named and cited

* `hd : 2 <= d` --- the manuscript's standing dimension hypothesis, which is
  the closure contract's own leading antecedent.
* `hosc` --- the Step-2 oscillation envelope, a conditional A obligation:
  `Closure.ClosureInteriorSplit.ClosureInteriorBesovEnvelopeInput`, stated on
  the interior mesh.  It is the manuscript's `e.lower.bound.oscillations` read
  at the Besov tower of the gauged `bfF_z`.
* `hstrip` --- `Closure.ClosureInteriorSplit.ClosureStripRemainder`, the
  boundary-strip second moment and its absorption gate, i.e. the `hstrip` and
  `hgate` binders that
  `Closure.GammaTenStripAssembly.fluctuationEnergyAverage_le_of_interior_cell_fold_grid_load`
  exposes and does not prove (that module's header, "The residual this module
  isolates").

Nothing else survives: every premise of the two theorems below beyond these is
a premise of `Algsuperdiff.Frozen.Section3.diffusivity_asymptotics` itself,
carried verbatim except for the landmark gate on `m0`, which is the `mStarStar
M < m0`; see the next section.

## The scale gate on `m0` (-bin statement change)

The landmark gate carried below is `mStarStar M < m0`, **not** the printed `m0
in (mstar, infty) cap Z`.

## Scope

Internal Provider infrastructure: two conditional A.  There is no `sorry`, no
`admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula`; `e.what.do.we.have`.
* ABK26, `l.integrate.approx.recurrence`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open Algsuperdiff.Section3

noncomputable section

/-! ## The interior-mesh contract -/

/-- **The closure contract from the interior-mesh oscillation input and the strip
residual.**

`Closure.ClosureFinal.twoSidedClosure_of_endpoints` with the `ClosureSplitInput`
endpoint supplied through the strip bridge rather than through the full-mesh
fold, and with the Step-4 and Step-5 endpoints supplied outright.

exactly on `ClosureInteriorBesovEnvelopeInput d` and `ClosureStripRemainder d`. -/
theorem twoSidedClosure_of_interiorEnvelope (d : ℕ) [NeZero d]
    (hosc : ClosureInteriorBesovEnvelopeInput d) (hstrip : ClosureStripRemainder d) :
    TwoSidedClosure d :=
  twoSidedClosure_of_endpoints d
    (fun hd => closureSplitInput_of_interiorEnvelope d hd hosc hstrip hd)
    (closureStep4Input d) (closureStep5Input d)

/-! ## The terminal composition -/

/-- **The diffusivity asymptotics from the interior-mesh oscillation input and
the strip residual.**

The whole closure chain, run end to end: the interior-mesh Besov envelope feeds
`Closure.GammaTenStripAssembly`'s strip bridge, the bridge feeds
`Closure.ClosureFinal.ClosureSplitInput`, the three endpoints feed
`Closure.NodeContract.TwoSidedClosure`, and the contract feeds the flow spine
through `Closure.ClosureTerminal`.  The conclusion is the conclusion block of
`Algsuperdiff.Frozen.Section3.diffusivity_asymptotics`, on that statement's own
premise list with the landmark gate weakened to the `mStarStar M < m0` (
option (i)).

exactly on `hd : 2 <= d`, on `ClosureInteriorBesovEnvelopeInput d` and on
`ClosureStripRemainder d`; both inputs are carried as `Prop` binders and
neither is proved here. -/
theorem diffusivity_asymptotics_of_strip (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hosc : ClosureInteriorBesovEnvelopeInput d) (hstrip : ClosureStripRemainder d) :
    ∃ Cflow : ℝ, 0 < Cflow ∧
      ∀ (M : ABKModel d) (m0 : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        Cflow * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        (∀ m : ℤ, m ≤ m0 →
          |(Annealed.sigmaBar M m : ℝ) -
              Real.sqrt
                (M.nu ^ 2 +
                  Disorder.cstar M * M.gamma⁻¹ *
                    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))|
            ≤ Cflow * (Disorder.cstar M)⁻¹ * (E : ℝ) *
              Real.sqrt M.gamma * |Real.log M.gamma| *
                (Annealed.sigmaBar M m : ℝ)) ∧
        (1 / 4 : ℝ) *
            max
              (Disorder.cstar M * M.gamma⁻¹ *
                (3 : ℝ) ^ (2 * M.gamma * (m0 : ℝ)))
              (M.nu ^ 2)
          ≤ (Annealed.sigmaBar M m0 : ℝ) ^ 2 ∧
        (Annealed.sigmaBar M m0 : ℝ) ^ 2
          ≤ 4 *
            max
              (Disorder.cstar M * M.gamma⁻¹ *
                (3 : ℝ) ^ (2 * M.gamma * (m0 : ℝ)))
              (M.nu ^ 2) :=
  diffusivity_asymptotics_of_twoSidedClosure d hd
    (twoSidedClosure_of_interiorEnvelope d hosc hstrip)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
