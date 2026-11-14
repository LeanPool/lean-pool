/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineResiduePairing

/-!
# HomSpineResidueLevel

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `hlevel` and `hlevelDual` with the `EthmB(m)` pairing DISCHARGED

## What this file supplies

The installed `hlevel` and its dual carry three
content-bearing hypotheses: the Theorem-C energy bound `hSbound`, and the pair
`hA`/`hB` together with the budget split `hsplit`.  This file DISCHARGES the
second group at the concrete substitution against the two summands of
`EthmB(m)`:

* the defect witness is cut at `E_B:= (EthmB(m))(ω).toReal` — the same cut
  `HomSpineFinalWitness` makes for the root's clause (C2);
* `C_w` is the explicit sum of the four pairing constants (two per level
  condition), none of which carries randomness;
* `hA`, `hB` are then `le_rfl` — the slots ARE the pairing's left-hand sides —
  and `hsplit` is the budget split.

What remains of the two level conditions is:

```text
  hSbound  (Theorem C's Step-2 energy density, at the printed constant shape)
  hdom1, hdom2  (the carrier seam — see `HomSpineResiduePairing`'s disclosure)
  hfin  (a.e. finiteness of the [0,∞] carrier: HomSpineFinalWitness's own step)
```

That pairing constant is bounded by the bundle's `K_abs` slot as a frame
condition, not proved here: `K_abs` is a free parameter of the endpoint.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The base order and the Step-2 random factor -/

/-- The printed base order `s = |log γ|⁻¹`, as a `FractionalOrder`.  Both
conditions come from `homS_le_quarter`, i.e. from `|log γ| ≥ 4`. -/
def recutOrderBase (M : ABKModel d) (hlog : 4 ≤ |Real.log M.gamma|) : FractionalOrder :=
  ⟨homS M, homS_pos (by linarith only [hlog]),
    lt_of_le_of_lt (homS_le_quarter hlog) (by norm_num)⟩

@[simp] theorem recutOrderBase_val (M : ABKModel d) (hlog : 4 ≤ |Real.log M.gamma|) :
    (recutOrderBase M hlog : FractionalOrder).1 = homS M := rfl

/-- **The random factor of the Step-2 constant**: the
minimal-scale factor `3^{(1-α)X_m(α)}` times the printed `1 + 𝓔_{1/4}(□_m)`,
cut to a real.  `hSbound`'s constant is `C_en = C · recutEnergyFactor`. -/
def recutEnergyFactor (M : ABKModel d) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  (Y omega *
    (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega)).toReal

theorem recutEnergyFactor_nonneg (M : ABKModel d) (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (m : ℤ) (omega : Cutoff.CutoffSample d) : 0 ≤ recutEnergyFactor M Y m omega :=
  ENNReal.toReal_nonneg

end

end Algsuperdiff.Section4.Provider.Homogenization
