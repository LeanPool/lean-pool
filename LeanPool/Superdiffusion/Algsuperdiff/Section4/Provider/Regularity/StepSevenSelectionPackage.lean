/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenGoodScales
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenSandwich
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepThreePackage

/-!
# StepSevenSelectionPackage

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7a, assembled: the good-scale selection package

## What is delivered

`StepSevenSelectionData` collects, at a fixed printed centre `z ∈ 3^n ℤ^d ∩
□_m` and a fixed sample `ω`, everything ABK26 `t.regularity` Step 7 produces
before the first analytic estimate:

* the two extreme good scales `n'`, `m'` of `[n+3, m-3]`, with `n' < m'`;
* their proximity to the window ends — the sharp `n' - n ≤ |𝓑_z| + 3`, `m - m' ≤
  |𝓑_z| + 3` and the printed `max{n'-n, m-m'} ≤ |𝓑_z| + 6`;
* the good-event memberships `ω ∈ 𝒢(n', z; ⅛s, ⅛ s δ^{1/2})` and
  `ω ∈ 𝒢(m', z; ⅛s, ⅛ s δ^{1/2})` — the indicator Step 7b
  (`l.lambdas.stability`) is applied against;
* the sandwich centres `z'`, `z'' ∈ □_m` with, for `(y',k')` ranging over
  `{(z',m'), (z'',n')}`,
  `(z + □_{k'-1}) ∩ □_m ⊆ y' + □_{k'-1} ⊆ (z + □_{k'}) ∩ □_m`.

`exists_stepSevenSelectionData_of_stepThreeWindowsAndBudget` builds the package
at a printed centre from the Step-3 window/budget conclusion alone, so the
selection is a drop-in successor of the Step-3 endpoint.

## What is not here

Nothing analytic.  No `λ`/`Λ` transport (Step 7b), no coarse-grained
Caccioppoli (Step 7c), no `σ` comparison, no volume factor.  In particular the
package makes no claim about the window `(z + □_{m'-1}) ∩ □_m` beyond the
inclusions above; the one-scale-below reading of the Step-7 oscillation endpoint
is a Step-7c matter and is only enabled here (by `n' < m'`, which puts `m'-1` in `[n',
m']`).

## References

* ABK26, `t.regularity` Step 7.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

variable {d : ℕ}

/-! ## 1. The package -/

/-- **The Step-7a selection package** at one centre and one sample.  See the module
docstring for the six items. -/
structure StepSevenSelectionData (M : ABKModel d) (delta : ℝ) (n m : ℤ)
    (z : Vec d) (omega : Cutoff.CutoffSample d) (n' m' : ℤ) (zp zpp : Vec d) :
    Prop where
  /-- `n'` and `m'` are the extreme good scales of `[n+3, m-3]`. -/
  selection : StepSevenSelection (stepThreeBadSet M delta n m z omega) n m n' m'
  /-- `n' < m'`, the side condition. -/
  scales_lt : n' < m'
  /-- The sharp lower gap. -/
  lower_gap : n' - n ≤ ((stepThreeBadSet M delta n m z omega).card : ℤ) + 3
  /-- The sharp upper gap (the form consumes). -/
  upper_gap : m - m' ≤ ((stepThreeBadSet M delta n m z omega).card : ℤ) + 3
  /-- The printed observation `max{n'-n, m-m'} ≤ |𝓑_z| + 6`. -/
  max_gap : max (n' - n) (m - m') ≤ ((stepThreeBadSet M delta n m z omega).card : ℤ) + 6
  /-- The good event at the lower selected scale. -/
  good_lower : omega ∈ stepThreeGoodEvent M delta n' z
  /-- The good event at the upper selected scale. -/
  good_upper : omega ∈ stepThreeGoodEvent M delta m' z
  /-- `z' ∈ □_m`. -/
  upper_centre_mem : zp ∈ openCubeSet (originCube d m)
  /-- `z'' ∈ □_m`. -/
  lower_centre_mem : zpp ∈ openCubeSet (originCube d m)
  /-- `(z + □_{m'-1}) ∩ □_m ⊆ z' + □_{m'-1}`. -/
  upper_sandwich_in : truncatedWindow z m (m' - 1) ⊆
    (fun v => zp + v) '' openCubeSet (originCube d (m' - 1))
  /-- `z' + □_{m'-1} ⊆ (z + □_{m'}) ∩ □_m`. -/
  upper_sandwich_out : (fun v => zp + v) '' openCubeSet (originCube d (m' - 1)) ⊆
    truncatedWindow z m m'
  /-- `(z + □_{n'-1}) ∩ □_m ⊆ z'' + □_{n'-1}`. -/
  lower_sandwich_in : truncatedWindow z m (n' - 1) ⊆
    (fun v => zpp + v) '' openCubeSet (originCube d (n' - 1))
  /-- `z'' + □_{n'-1} ⊆ (z + □_{n'}) ∩ □_m`. -/
  lower_sandwich_out : (fun v => zpp + v) '' openCubeSet (originCube d (n' - 1)) ⊆
    truncatedWindow z m n'

/-! ## 2. The package from the centre condition and the separation -/

/-- **Step 7a at one centre**: the whole package from `z ∈ □_m`'s separation `|𝓑_z|
+ 7 ≤ m - n`.  The scale conditions `n' - 1 ≤ m`, `m' - 1 ≤ m` the sandwich
needs come from the selection's own range `[n+3, m-3]`. -/
theorem exists_stepSevenSelectionData {M : ABKModel d} {delta : ℝ} {n m : ℤ}
    {z : Vec d} {omega : Cutoff.CutoffSample d}
    (hz : z ∈ openCubeSet (originCube d m))
    (hsep : StepOneBadSetSeparation (stepThreeBadSet M delta n m z omega).card n m) :
    ∃ (n' m' : ℤ) (zp zpp : Vec d),
      StepSevenSelectionData M delta n m z omega n' m' zp zpp := by
  obtain ⟨n', m', hsel, hlt⟩ := exists_stepSevenSelection_stepThreeBadSet hsep
  have hgood := mem_stepThreeGoodEvent_of_stepSevenSelection hsel
  obtain ⟨zp, hzp, hzp1, hzp2⟩ :=
    exists_stepSevenSandwich z hz (by linarith only [hsel.upper_hi] : m' - 1 ≤ m)
  obtain ⟨zpp, hzpp, hzpp1, hzpp2⟩ :=
    exists_stepSevenSandwich z hz (by linarith only [hsel.lower_hi] : n' - 1 ≤ m)
  exact ⟨n', m', zp, zpp,
    { selection := hsel
      scales_lt := hlt
      lower_gap := hsel.lower_gap
      upper_gap := hsel.upper_gap
      max_gap := hsel.max_gap_le
      good_lower := hgood.1
      good_upper := hgood.2
      upper_centre_mem := hzp
      lower_centre_mem := hzpp
      upper_sandwich_in := hzp1
      upper_sandwich_out := hzp2
      lower_sandwich_in := hzpp1
      lower_sandwich_out := hzpp2 }⟩

/-- **Step 7a at every printed centre**, straight's per-window conclusion
`StepThreeWindowsAndBudget` (whose fourth component IS the separation). -/
theorem exists_stepSevenSelectionData_of_stepThreeWindowsAndBudget
    {M : ABKModel d} {delta : ℝ} {n m : ℤ} {omega : Cutoff.CutoffSample d}
    (hbudget : StepThreeWindowsAndBudget M delta n m omega) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeCubeSet d n m) :
    ∃ (n' m' : ℤ) (zp zpp : Vec d),
      StepSevenSelectionData M delta n m (Support.triadicLatticePoint n v) omega
        n' m' zp zpp :=
  exists_stepSevenSelectionData (mem_openCubeSet_of_mem_latticeCubeSet hv)
    (hbudget v hv).2.2.2

end Algsuperdiff.Section4.Provider.Regularity
