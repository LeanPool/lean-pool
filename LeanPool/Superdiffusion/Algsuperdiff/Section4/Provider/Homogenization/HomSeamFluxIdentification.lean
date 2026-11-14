/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxLane
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxLevelChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineResidueCore
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.FluxCorrectedTwoScaleCarrier

/-!
# HomSeamFluxIdentification

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The coefficient input of the `ã` seam, PRODUCED

## What this file settles

`HomSeamFluxCoefficient.FluxCorrectedParentIdentification` — the ONE honest
coefficient input of the print-accurate `ã_{L,m}` chain, i.e. the standing
`bounds_mathcal_E_aL` provider obligation restricted to one sample — is
DISCHARGED almost surely:

```text
  ∀ᵐ ω ∂ cutoffSampleLaw M, FluxCorrectedParentIdentification M m (homK M) ω.
```

It is not a commutation, and it is not pointwise: it is produced on the
countable intersection over `L ≥ m` of the coarse-block events.  The four
obstructions are settled as follows.

* **INDEX.**  The obligation's truncation index is `n = m − k` (`homN M m`),
  not the matched index `n = m` of the one-argument chain.  The
  two-argument carrier theorem (`Support.FluxCorrectedTwoScaleCarrier`,
  `ae_forall_parentTruncatedTwo_fluxCorrected_eq_representative`)
  carries every `n ≤ m`, so the two ranges are LITERALLY the same range here
  (`(originCube d m).scale − (homK M: ℤ)` is `homN M m` by `rfl`) and the
  relation is an EQUALITY, not a domination; the domination is only the final
  `L ≥ m` supremum step.
* **SUMMABILITY.**  No summability hypothesis is needed: `CoarseGraining`'s own
  `parentTruncatedHomogenizationErrorInfinityTwoScalar_eq_ofReal` already
  performs the `ℝ≥0∞ → ℝ` conversion, and it discharges summability internally
  from the uniform response bound of the parent `CoeffOn`'s ellipticity
  constants (`summable_rootPointwise_infinity_two_terms`).  So the real square
  root never junks to `0`, and the moment anchor is NOT consumed here.
* **FAMILY.**  `rootPointwiseCoeffFamily` versus `fluxCorrectedCoeffFamily`:
  the congruence is proved in this repo as
  `Support.normalizedBlockResponseMax_congr_of_aeeq`, from `CoarseGraining`'s
  `Ch02.doubledResponseJ_eq_ofAEEq`.  No non-a.e.-invariant step appears: the
  response reads the coefficient only through its a.e. class.
* **SIGMA PIN.**  Pinned in `HomSeamFluxCoefficient`: the identification is
  typed at `Annealed.sigmaBar M m`, the pin its right-hand observable already
  carried.

## What is supplied downstream

`ae_fluxCorrectedParentIdentification` states the identification event ONCE, on
the one measure `cutoffSampleLaw M`; a residue carrying every other conjunct
re-attaches it by a single application.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The a.e. production -/

/-- **THE COEFFICIENT INPUT, PRODUCED.**

Almost surely, at every admissible `L` and every fractional order,
`CoarseGraining`'s literal `q = 2` truncated parent error of the printed
flux-corrected field `ã_{L,m}` on `□_m`, truncated at the mesoscale `n = m −
k`, is below the measurable two-argument flux-corrected observable at the same
order.

The `L`-term is in fact an EQUALITY with the observable's `L`-th entry
(`Support.ae_forall_parentTruncatedTwo_fluxCorrected_eq_representative`); the
`≤` is only the passage to the supremum over `L ≥ m`. -/
theorem ae_fluxCorrectedParentIdentification [NeZero d] (M : ABKModel d) (m : ℤ) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      FluxCorrectedParentIdentification M m (homK M) omega := by
  filter_upwards [ae_forall_parentTruncatedTwo_fluxCorrected_eq_representative M m
    ((originCube d m).scale - ((homK M : ℕ) : ℤ)) (recutParentScale m (homK M))]
    with omega homega L hL t
  rw [homega L hL t]
  exact le_fluxCorrectedTwoScaleErrorObservableSup M m (homN M m) ⟨t.1, t.2.1⟩ omega hL

end

end Algsuperdiff.Section4.Provider.Homogenization
