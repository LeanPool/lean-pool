/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenWireBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenWireEmbedding
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenEndAssembly

/-!
# StepSevenWireChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7d: the narrowed chain

## What this module does

The Step-7d end chain is the entry point for Step 7d.  It takes four named
conditional inputs across its three displays: `hcg`, `hlambda`, `hembed`,
`hbridge`.  Three of them are discharged here:

* `hcg` — `StepSevenWireCgMatching.exists_stepSevenCgPoincareInput_pinned`
  (CoarseGraining's `coarsePoincareRHSTheory`, at the pin `s₀ = 1/4`);
* `hembed` — `StepSevenWireEmbedding.stepSevenEmbedding` (the Section-3
  mean-zero multiscale Poincaré, with the coordinate aggregation and the
  off-grid recovery);
* `hbridge` — `StepSevenWireBridge.stepSevenBesovBridge` (the summability
  conversion).

The narrowed entry point keeps `hlambda` alone.  Its
remaining conditional inputs are exactly

```text
  { hlambda ,  the Step-7c hgrad display (which carries hcacc / hlambda / hosc) } ,
```

plus the caller's own geometry (`hmean`, `hcomp`, the three transports and the
two `Ktr` dominations) and the printed nonnegativity/window data.  Nothing else.

## The carriers of the composition

Everything is stated at the scale normalization of the cube `Q`, which under the
translate-the-sample convention is `originCube d (m'-1)` carrying the sample
translated by `z'`:

```text
  oscLoc  = 3^{-Q.scale}‖u - (u)_Q‖_{L²(Q)}                     (the embedding LHS)
  besovP1 = cubeBesovNegativeVectorSeminorm Q 1 (∇u)             (B^{-1}_{2,1})
  besov   = scaleNormalizedNegativeBesovVectorNorm Q s₀ (.finite 2) (∇u)
  gradLoc = forcedSolutionEnergyNorm Q a u ,  dataLoc = [𝐠]_{B^{s₀}_{2,2}(Q)}
```

with `s₀ = stepSevenCgS = 1/4`.  Neither Besov membership is a hypothesis: the
`B^{-s₀}_{2,2}` side is CoarseGraining's proved
`forcedSolutionGradientField_negativeBesovPartialSeminormTwo_bddAbove`
(automatic for every `ForcedCubeSolution`), and the `B^{-1}_{2,1}` side is
derived from it through the conversion (`bddAbove_partialOne_of_partialTwo`).

## References

* ABK26, Step 7d; `e.energy.density.estimate`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The `B^{-1}_{2,1}` side's boundedness, derived from the `B^{-s}_{2,2}` one -/

/-- The conversion propagates boundedness: the `q = 1` partial seminorms are
bounded above whenever the `q = 2` ones at index `t < 1` are. -/
theorem bddAbove_partialOne_of_partialTwo (Q : TriadicCube d) {t : ℝ} (ht1 : t < 1)
    (F : Vec d → Vec d)
    (hbdd : BddAbove
      (Set.range fun N : ℕ => cubeBesovNegativeVectorPartialSeminormTwo Q t N F)) :
    BddAbove
      (Set.range fun N : ℕ => cubeBesovNegativeVectorPartialSeminorm Q 1 N F) := by
  refine ⟨stepSevenBridgeConst t * cubeBesovNegativeVectorSeminormTwo Q t F, ?_⟩
  rintro x ⟨N, rfl⟩
  refine le_trans (cubeBesovNegativeVectorPartialSeminorm_le_bridgeConst_mul Q ht1 F N) ?_
  exact mul_le_mul_of_nonneg_left (le_csSup hbdd (Set.mem_range_self N))
    (stepSevenBridgeConst_nonneg t)

/-- `hbridge` with the right-hand side in CoarseGraining's `q = 2` carrier — the
object `coarsePoincareRHSTheory` produces. -/
theorem stepSevenBridge_to_scaleNormalized (Q : TriadicCube d) {t : ℝ} (ht1 : t < 1)
    (F : Vec d → Vec d)
    (hbdd : BddAbove
      (Set.range fun N : ℕ => cubeBesovNegativeVectorPartialSeminormTwo Q t N F)) :
    cubeBesovNegativeVectorSeminorm Q 1 F ≤
      stepSevenBridgeConst t *
        scaleNormalizedNegativeBesovVectorNorm Q t (Ch02.MultiscaleExponent.finite 2) F := by
  rw [scaleNegativeBesovVectorNorm_finiteTwo_eq_cubeNegativeSeminorm]
  exact stepSevenBesovBridge Q ht1 F hbdd

end

end Algsuperdiff.Section4.Provider.Regularity
