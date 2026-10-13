/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfaces.Definitions

/-!
# CoarseGrainingSeminormScaling

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Positive homogeneity of the `q = 2` negative Besov seminorm

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## Why this is needed

ABK26's coarse-graining display `e.homogenization.L2.interior` has the **scalar
comparator on the left**:

```text
  3^{-sn/2} σ_n ‖∇u − ∇v‖_{H_hat^{-s/2}(x+□_n)}  ≤  … ,
```

and CoarseGraining's `homogenizationComparisonNegativeBesovLHS` likewise
measures the *field* `a₀(∇u − ∇v) = σ₀ (∇u − ∇v)`, not the bare gradient
defect.  The negative-norm-to-`L²` leg, on the other hand, consumes the bare
gradient of an `H¹₀` function.  Moving the scalar across is exactly the
positive homogeneity proved here — an identity, with no constant and no side
condition.

Every step is elementary and local to CoarseGraining's definition chain
`cubeAverageVec → vecNormSq → descendantsAverage → depth seminorm → partial
seminorm → sSup`; the last step uses Mathlib's `Real.smul_iSup_of_nonneg`,
which is unconditional because `Real.sSup` of an unbounded set is `0`.

## References

* ABK26, `e.homogenization.L2.interior`.
* `Homogenization/Deterministic/WeakNormInterfaces/Definitions.lean` (the
  definition chain).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-! ## 1. Averages -/

/-- Cube averages of vector fields are homogeneous. -/
theorem cubeAverageVec_smul (Q : TriadicCube d) (c : ℝ) (F : Vec d → Vec d) :
    cubeAverageVec Q (fun x => c • F x) = c • cubeAverageVec Q F := by
  funext i
  have hint : ∫ x in cubeSet Q, c * F x i ∂MeasureTheory.volume =
      c * ∫ x in cubeSet Q, F x i ∂MeasureTheory.volume :=
    MeasureTheory.integral_const_mul c fun x => F x i
  show (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, c * F x i ∂MeasureTheory.volume =
    c * ((cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, F x i ∂MeasureTheory.volume)
  rw [hint]
  ring

/-- Descendant averages are linear in a scalar factor. -/
theorem descendantsAverage_const_mul (Q : TriadicCube d) (j : ℕ) (c : ℝ)
    (G : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => c * G R) = c * descendantsAverage Q j G := by
  classical
  show ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      (descendantsAtDepth Q j).sum (fun R => c * G R) =
    c * (((descendantsAtDepth Q j).card : ℝ)⁻¹ * (descendantsAtDepth Q j).sum G)
  rw [← Finset.mul_sum]
  ring

/-! ## 2. The depth pieces -/

/-- The depth-`j` block average scales by `c²`. -/
theorem cubeBesovNegativeVectorDepthAverage_smul (Q : TriadicCube d) (c : ℝ)
    (F : Vec d → Vec d) (j : ℕ) :
    cubeBesovNegativeVectorDepthAverage Q (fun x => c • F x) j =
      c ^ 2 * cubeBesovNegativeVectorDepthAverage Q F j := by
  rw [cubeBesovNegativeVectorDepthAverage, cubeBesovNegativeVectorDepthAverage]
  have hpt : (fun R : TriadicCube d => vecNormSq (cubeAverageVec R (fun x => c • F x))) =
      fun R : TriadicCube d => c ^ 2 * vecNormSq (cubeAverageVec R F) := by
    funext R
    rw [cubeAverageVec_smul, vecNormSq_smul]
  rw [hpt, descendantsAverage_const_mul]

/-- The depth-`j` negative seminorm scales by `c` for `c ≥ 0`. -/
theorem cubeBesovNegativeVectorDepthSeminorm_smul (Q : TriadicCube d) (s : ℝ)
    {c : ℝ} (hc : 0 ≤ c) (F : Vec d → Vec d) (j : ℕ) :
    cubeBesovNegativeVectorDepthSeminorm Q s (fun x => c • F x) j =
      c * cubeBesovNegativeVectorDepthSeminorm Q s F j := by
  rw [cubeBesovNegativeVectorDepthSeminorm, cubeBesovNegativeVectorDepthSeminorm,
    cubeBesovNegativeVectorDepthAverage_smul, Real.sqrt_mul (sq_nonneg c),
    Real.sqrt_sq hc]
  ring

/-- The finite-depth `q = 2` negative seminorm scales by `c` for `c ≥ 0`. -/
theorem cubeBesovNegativeVectorPartialSeminormTwo_smul (Q : TriadicCube d) (s : ℝ)
    {c : ℝ} (hc : 0 ≤ c) (F : Vec d → Vec d) (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => c • F x) =
      c * cubeBesovNegativeVectorPartialSeminormTwo Q s N F := by
  rw [cubeBesovNegativeVectorPartialSeminormTwo,
    cubeBesovNegativeVectorPartialSeminormTwo]
  have hsum : (Finset.range (N + 1)).sum
        (fun j => cubeBesovNegativeVectorDepthSeminorm Q s (fun x => c • F x) j ^ 2) =
      c ^ 2 * (Finset.range (N + 1)).sum
        (fun j => cubeBesovNegativeVectorDepthSeminorm Q s F j ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [cubeBesovNegativeVectorDepthSeminorm_smul Q s hc F j]
    ring
  rw [hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-! ## 3. The seminorm -/

/-- **Positive homogeneity of the `q = 2` negative Besov seminorm.**

```text
  [c F]_{B^{-s}_{2,2}(Q)} = c [F]_{B^{-s}_{2,2}(Q)}      (c ≥ 0) .
```

No boundedness hypothesis is needed: `Real.sSup` of an unbounded set is `0`, so
`Real.smul_iSup_of_nonneg` is unconditional. -/
theorem cubeBesovNegativeVectorSeminormTwo_smul (Q : TriadicCube d) (s : ℝ)
    {c : ℝ} (hc : 0 ≤ c) (F : Vec d → Vec d) :
    cubeBesovNegativeVectorSeminormTwo Q s (fun x => c • F x) =
      c * cubeBesovNegativeVectorSeminormTwo Q s F := by
  rw [cubeBesovNegativeVectorSeminormTwo, cubeBesovNegativeVectorSeminormTwo]
  have hfun : (fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => c • F x)) =
      fun N : ℕ => c • cubeBesovNegativeVectorPartialSeminormTwo Q s N F := by
    funext N
    rw [cubeBesovNegativeVectorPartialSeminormTwo_smul Q s hc F N, smul_eq_mul]
  rw [hfun]
  have hsup := (Real.smul_iSup_of_nonneg hc
    fun N : ℕ => cubeBesovNegativeVectorPartialSeminormTwo Q s N F).symm
  rw [iSup, iSup] at hsup
  rw [hsup, smul_eq_mul]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
