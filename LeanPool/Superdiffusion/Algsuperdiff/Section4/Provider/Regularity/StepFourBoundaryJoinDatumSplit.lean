/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourBoundaryBudgetErrorWeighted
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EdBridgeStepFourDatumSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EdBridgeStepFourGeneral
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootInterfaceGate

/-!
# StepFourBoundaryJoinDatumSplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary Step-4 slot at every centre, with the printed datum leg

## What this module settles

`StepFourBoundaryJoin.excessDecay_stepFour_slot_allCentres` is the Step-4 slot
at every centre, with the interior/met-face disjunction discharged geometrically
— but it is a **conditional interface**, not a boundary `hstep4` producer,
because its carried competitor package forces the join's own competitor to
vanish on the met face (`oddCompetitor_eq_zero_on_metUpperFace`).  That
obstruction is removed here: the package is asked of the Weyl representative `V`
of the manuscript's shifted competitor `v − ℓ_h − v₁`, which is exactly the
object the reflection chain produces from the proved zero-trace supplier, and
whose met-face trace `h − ℓ_h − v₁` genuinely vanishes.

* `excessDecay_stepFour_slot_allCentres_datumSplit` — the Step-4 slot with **no
  geometric hypothesis at all**, at every centre including the boundary lattice
  centres where the cube gate fails, and with the printed datum leg in the
  `δ` slot.  Its only remaining window input is the chain's own competitor
  package `(V, v₁, ℓ_h)` at the datum scale `K_h`.

## The consumption match

The new leg is exactly the `A^h_n` leg of the budget: same `n`-power, same datum
kind, same geometric domination, so it is absorbed by widening that leg's
constant and not by touching the `ε`-free flat slot `F` (which is the anchor's
`K_hinf` leg).  Here that is machine-checked in both budgets:

* `edBridgeDatumLeg_at_budgetIndex` — the slot's leg at budget index `j` is
  `edBridgeDatumLegConst d Cs k · (3^{j/2} · K_h)`, i.e. the `A^h_j` shape
  verbatim;
* `stepFourDeltaOut_add_datumLeg_le_boundaryFourLegs` — the four-leg grouping
  with the `A^h` constant widened from `C_bd` to `C_bd + C_leg`, `F` untouched;
* `stepFourDeltaOutErrorWeighted_add_datumLeg_le_boundaryThreeLegs` — the same
  for the error-weighted three-leg grouping (where `F` is already gone), again only
  `A^h`'s constant moving.

So the budget's geometric sums take the new output with no structural change:
`K_h/(1−r₂)` is the only summand that grows, and it grows by a constant factor.

## References

* ABK26, `l.excess.decay.good.scales`; `t.regularity` Steps 4--5.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 3. The budget composition: only `A^h`'s constant moves -/

/-- **The error-weighted three-leg grouping with the datum leg absorbed.**

The error-weighted budget has no `ε`-free flat summand at all; the datum leg is
still absorbed into `A^h`, whose constant widens from `C_bd` to
`C_bd + C_leg`. -/
theorem stepFourDeltaOutErrorWeighted_add_datumLeg_le_boundaryThreeLegs
    {Crem Vd Cst s epsj Khinf SigInvN Kg Kh Cleg : ℝ} {n : ℤ}
    (hCV : 0 ≤ Crem * Vd) (hCst : 0 ≤ Cst) (hs : 0 < s) (heps0 : 0 ≤ epsj)
    (hKhinf : 0 ≤ Khinf) (hSig0 : 0 ≤ SigInvN) (hKg0 : 0 ≤ Kg) (hKh0 : 0 ≤ Kh) :
    stepFourDeltaOutErrorWeighted Crem Vd Cst s epsj Khinf SigInvN Kg Kh n +
        Cleg * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) ≤
      stepFourBoundaryDeltaConst Crem Vd Cst s *
          ((3 : ℝ) ^ ((n : ℝ) / 2) * SigInvN * Kg) +
        ((stepFourBoundaryDeltaConst Crem Vd Cst s + Cleg) *
            ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) +
          epsj * (2 * stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf)) := by
  have h := stepFourDeltaOutErrorWeighted_le_boundaryThreeLegs (Crem := Crem) (Vd := Vd) (Cst :=
    Cst)
    (s := s) (epsj := epsj) (Khinf := Khinf) (SigInvN := SigInvN) (Kg := Kg) (Kh := Kh)
    (n := n) hCV hCst hs heps0 hKhinf hSig0 hKg0 hKh0
  have hid : (stepFourBoundaryDeltaConst Crem Vd Cst s + Cleg) *
        ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh)
      = stepFourBoundaryDeltaConst Crem Vd Cst s * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh)
        + Cleg * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) := by ring
  linarith only [h, hid]

end

end Algsuperdiff.Section4.Provider.Regularity
