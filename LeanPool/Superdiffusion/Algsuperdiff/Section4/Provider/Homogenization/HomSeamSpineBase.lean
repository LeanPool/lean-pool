/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxLane

/-!
# HomSeamSpineBase

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5: the spine at a FREE `EthmB` base and a FREE `Y`

## Why this file exists

The authorized re-pin moves the `EthmB(m)` base exponent from the printed
`s = |log γ|⁻¹` to `s/8`, and the index change enlarges the printed `Y` slot
by two more error factors (`HomSpineTopScale.stepTwoEnlargedY`).  Both moves are
INSIDE the own carrier `ethmB M Cgap Y m n sb`, and every
spine module (`HomSpineFinalWitness`, `HomSpineFinalEndpoint`) hard-codes

```text
  Y  = homMinimalScaleFactor (1 - α) X,      sb = ⟨homS M, hs⟩.
```

This file re-states that chain with `Y` and `sb` FREE, and with the single thing
those modules used them for — Step 1's moment display — taken as an explicit
hypothesis `StepOneDisplayAt`.  Nothing else changes: the real cut `E_B`, the
linkage, clauses (C1)/(C2), and the passage to the root's conclusion body are
the arguments verbatim.

## The statement

```text
  StepOneDisplayAt   — Step 1's display as a named input, at a free `(Y, sb)`.
```

`hY` does NOT appear: at a free `Y` the Theorem-C exponential moment is not a
statement about `Y` at all, and the composite it fed (`Y`'s own `2p`-moment)
lives inside `StepOneDisplayAt`, where the consumer discharges it.
-/

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. Step 1's display, as a named input at a free base -/

/-- **STEP 1's DISPLAY the `𝓔` estimate at a free `Y` and a free base.**

Step 1's own display is exactly this `Prop` at `Y =
homMinimalScaleFactor (1-α) X` and `sb = ⟨homS M, hs⟩`; the `s/8` sibling at
the enlarged `Y` is this file.  The `p`-range is the display's own, at the
display's own constant. -/
def StepOneDisplayAt (M : ABKModel d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (m : ℤ) (sb : {s : ℝ // 0 < s}) (C0 : ℝ) : Prop :=
  ∀ p : ℝ, 1 ≤ p → p ≤ C0⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
    (∫⁻ omega, ethmB M Cgap Y m (homN M m) sb omega ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal
          (C0 * (1 + Cgap) * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
            Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ)) ^ p

end

end Algsuperdiff.Section4.Provider.Homogenization
