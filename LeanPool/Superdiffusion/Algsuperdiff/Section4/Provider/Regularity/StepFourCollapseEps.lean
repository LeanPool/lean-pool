/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFiveBudgetSums

/-!
# StepFourCollapseEps

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 4: the `ε_j` leg of the collapse

## The target

```text
   𝓔_{s/8,∞,2}(z + □_{n+1}; 𝐚_L − (κ_L − κ_{n+1})_{…}, σ_{n+1})
      =  Support.fluxCorrectedErrorRepresentative M L (n+1) ⟨s/8⟩ (τ_z ω) ,
```

while the Step-5 slot `ε_j` (`StepFiveBudgetSums.stepFiveEps`) is the `sup_{L ≥
j}` observable, restricted to the good event and pushed through `ENNReal.toReal`.

## Two exact alignments, and one shift

* **The gate is literally the same set.**  The excess-decay supply event is
  `goodEventAt M (cgEllipLowerConstant d) (n-2+3) z ⟨s/8⟩ (s/8 · √δ)` and
  `ε_j`'s indicator is
  `goodEventAt M (cgEllipLowerConstant d) j z ⟨s_8⟩ (stepOneEp δ)` with
  `stepOneEp δ = s_8 · √δ` and `s_8 = 1/32`.  At the Step-1 pin `s = 1/4` the
  two are the SAME term, constant for constant.
* **The observable is the same carrier**, and the per-level representative is
  dominated by the `sup_{L ≥ j}` observable
  (`Support.le_fluxCorrectedErrorObservableSup`) for every `L ≥ j`.
* **The scale shifts by one.**  The excess-decay display contracts the excess
  between scales `n` and `n-k`, but reads its error observable at `n-2+3 =
  n+1`.  Identifying the Step-5 index `j:= n` (which is what the excess indices
  force) therefore pins the Step-5 `ε`-slot at the shifted family `ε_{j+1}`.
  The shift is carried explicitly, not absorbed: `e.sum.eps.j.bound` is
  re-derived for it, at the same constant, from `GoodScaleWindows` on the
  shifted window `[n+1, m+1]`.

## The `toReal` corner, closed

`stepFiveEps` is a `toReal`, so a `⊤` observable would silently collapse the
slot to `0` and make the conversion.

## References

* ABK26, `t.regularity` Step 1; Step 4.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-! ## 1. The per-level representative under the Step-5 slot -/

/-- **The `ε_j` leg producer.**  On the good event, and with the observable
finite (the real cap `hcap`), the excess-decay lane's per-level flux-corrected
error at any truncation level `L ≥ j` is at most the Step-5 slot `ε_j`.

This is the exact conversion the Step-4 collapse needs: it turns the  leg datum
into the  `ε_j` at constant `1`. -/
theorem fluxCorrectedErrorRepresentative_le_stepFiveEps {M : ABKModel d} {j L : ℤ}
    {z : Vec d} {delta B : ℝ} {omega : Cutoff.CutoffSample d} (hjL : j ≤ L)
    (hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
      (Support.cgEllipLowerConstant d) j z ⟨stepOneSEighth, stepOneSEighth_pos⟩
      (stepOneEp delta))
    (hcap : stepOneEpsJ M j z delta omega ≤ ENNReal.ofReal B) :
    Support.fluxCorrectedErrorRepresentative M L j
        ⟨stepOneSEighth, stepOneSEighth_pos⟩ (Cutoff.translateCutoffSample z omega) ≤
      stepFiveEps M j z delta omega := by
  have hval : stepOneEpsJ M j z delta omega =
      Support.fluxCorrectedErrorObservableSup M j
        ⟨stepOneSEighth, stepOneSEighth_pos⟩ (Cutoff.translateCutoffSample z omega) := by
    rw [stepOneEpsJ, Set.indicator_of_mem hmem]
  have hle := Support.le_fluxCorrectedErrorObservableSup M j
    ⟨stepOneSEighth, stepOneSEighth_pos⟩ (Cutoff.translateCutoffSample z omega) hjL
  have hne : stepOneEpsJ M j z delta omega ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcap
  have hstep : ENNReal.ofReal
      (Support.fluxCorrectedErrorRepresentative M L j
        ⟨stepOneSEighth, stepOneSEighth_pos⟩ (Cutoff.translateCutoffSample z omega)) ≤
      stepOneEpsJ M j z delta omega := by
    rw [hval]
    exact hle
  have htoReal := ENNReal.toReal_mono hne hstep
  rwa [ENNReal.toReal_ofReal
    (Support.fluxCorrectedErrorRepresentative_nonneg M L j
      ⟨stepOneSEighth, stepOneSEighth_pos⟩ (Cutoff.translateCutoffSample z omega))]
    at htoReal

/-- The real-valued form of the `ε_j` cap: a `ℝ≥0∞` cap at a nonnegative real
transfers through `toReal`. -/
theorem stepFiveEps_le_of_cap {M : ABKModel d} {j : ℤ} {z : Vec d} {delta B : ℝ}
    {omega : Cutoff.CutoffSample d} (hB : 0 ≤ B)
    (hcap : stepOneEpsJ M j z delta omega ≤ ENNReal.ofReal B) :
    stepFiveEps M j z delta omega ≤ B :=
  ENNReal.toReal_le_of_le_ofReal hB hcap

end Algsuperdiff.Section4.Provider.Regularity
