/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepThreeBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepThreeWindows

/-!
# StepThreePackage

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 3, assembled: one a.e. statement carrying the windows,
# the bad-scale budget, the separation, and the `ε_j(z)` caps

## What is delivered

`StepThreeWindowsAndBudget` states ABK26 `t.regularity` Step 3 at one window
`[n, m]`, uniformly over the printed triadic lattice centres `z ∈ 3^n ℤ^d ∩
□_m`:

* `U_j := (z + □_j) ∩ □_m` is an admissible iteration-lemma family
  (`IterationWindowFamily`: measurable, nested, sandwiched);
* `𝓑_z ⊆ [n, m]`, the iteration lemma's `B`-binder;
* `|𝓑_z| ≤ δ(m - n + 1)`, `e.bad.scale.proportion.bound`;
* `|𝓑_z| + 7 ≤ m - n`, the separation.

`stepThreeWindowsAndBudget_of_goodScaleWindows` produces all four from the
producer's good-scales clause alone, at `δ ∈ [0, 1/2]` and a window of at least
14 scales.  This is what the Step-4 excess-decay application and the Step-5
iteration application read off Step 3.

## What is not formed here

The excess `E_j := E(u, U_j) = 3^{-j} min_ℓ ‖u - ℓ‖_{L²(U_j)}` and the optimal
affine functions `ℓ_j` are NOT formed: they are functions of the solution `u`,
which enters only with Step 4's excess-decay lemma, and the development already
carries their carriers (`Support.affineExcess`, `Support.IsAffineMinimizer`)
for the frozen iteration lemma.  Step 3's own content — the windows, the bad
set, the budget — is what this module delivers.  Nothing about `u`, `g`, `h`,
`L` or the truncated operator `a_L` appears here; the `L`-reconciliation gap is
untouched.

## References

* ABK26, `t.regularity` Steps 1--3.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-! ## 1. The per-window conclusion -/

/-- **The Step-3 conclusion at one window `[n, m]`**, uniformly over the printed
lattice centres `z ∈ 3^n ℤ^d ∩ □_m`: the window family is an admissible
iteration family, the bad set sits in the counting window, it obeys
`e.bad.scale.proportion.bound`, and it satisfies the separation. -/
def StepThreeWindowsAndBudget (M : ABKModel d) (delta : ℝ) (n m : ℤ)
    (omega : Cutoff.CutoffSample d) : Prop :=
  ∀ v : Fin d → ℤ, v ∈ Support.latticeCubeSet d n m →
    IterationWindowFamily (stepThreeWindow (Support.triadicLatticePoint n v) m) m ∧
      stepThreeBadSet M delta n m (Support.triadicLatticePoint n v) omega ⊆
        Finset.Icc n m ∧
      ((stepThreeBadSet M delta n m (Support.triadicLatticePoint n v) omega).card : ℝ) ≤
        delta * (((m - n).toNat : ℝ) + 1) ∧
      StepOneBadSetSeparation
        (stepThreeBadSet M delta n m (Support.triadicLatticePoint n v) omega).card n m

/-- The per-window conclusion, from the producer's good-scales clause alone. -/
theorem stepThreeWindowsAndBudget_of_goodScaleWindows {M : ABKModel d} {delta : ℝ}
    {n m : ℤ} {omega : Cutoff.CutoffSample d} (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / 2) (hwin : (14 : ℤ) ≤ m - n)
    (hgood : GoodScaleWindows M stepOneSEighth delta stepOneSEighth_pos n m omega) :
    StepThreeWindowsAndBudget M delta n m omega := by
  intro v hv
  refine ⟨iterationWindowFamily_stepThreeWindow _ m
      (mem_openCubeSet_of_mem_latticeCubeSet hv),
    stepThreeBadSet_subset_Icc M delta n m _ omega,
    stepThreeBadSet_card_le_of_goodScaleWindows hdelta0 hgood hv, ?_⟩
  exact stepOneBadSetSeparation_of_goodScaleWindows hdelta0 hdelta hwin hgood hv

end Algsuperdiff.Section4.Provider.Regularity
