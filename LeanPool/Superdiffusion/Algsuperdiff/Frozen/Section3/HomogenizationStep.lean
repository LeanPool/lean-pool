/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.CommonEventOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.TwoTermOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffResponseJ
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Disorder.Cstar
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.IterateAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.UnionCompletion

/-!
# HomogenizationStep

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3.Provider.Homogenization
  (exists_isCommonEventTwoTermBigOWith_cutoffResponseJ_of_iterateMeanBound)

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory



/-!
# The homogenization step — [ABK] `p.homogenization.step`

Two-term Orlicz control of the cutoff homogenization error at every scale
below `m` upgrades, on one common event, to two-term Orlicz control of the
whole family of cutoff response observables indexed by scale and direction:
the fluctuation term improves to `epsilon E^2 gamma` and the rare term to
`epsilon exp(-2 E^{-3} gamma^{-1})`.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.homogenization_step
    (d : ℕ) :
    ∃ Chom : ℝ, 1 ≤ Chom ∧
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        (∀ k : ℤ, k ≤ m - 1 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            Probability.IsTwoTermBigOWith
              (Cutoff.cutoffSampleLaw M).toMeasure
              (HCPolySupport.IndependentSums.gammaSigma 2)
              (HCPolySupport.IndependentSums.gammaSigma (1 / 2))
              (Observable.cutoffHomogenizationError M k
                ⟨s,
                  (mul_pos (by norm_num : (0 : ℝ) < 8)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
              ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
              ((s⁻¹) ^ 2 *
                Real.exp
                  (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) →
        ∀ epsilon : ℝ, epsilon ∈ Set.Ioc 0 (1 / 2) →
          M.gamma ≤ Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon →
          Probability.IsCommonEventTwoTermBigOWith
            (Cutoff.cutoffSampleLaw M).toMeasure
            (HCPolySupport.IndependentSums.gammaSigma 1)
            (HCPolySupport.IndependentSums.gammaSigma (1 / 4))
            (fun i :
                {p : ℤ ×
                    {e : Vec d // HCPolySupport.Book.Ch02.vecNorm e = 1} //
                  (p.1 : ℝ) ≤ (m : ℝ) - Chom * |Real.log epsilon|} =>
              Observable.cutoffResponseJ M m i.1.1 i.1.2.1)
            (epsilon * (E : ℝ) ^ 2 * M.gamma)
            (epsilon *
              Real.exp
                (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))
-- FROZEN-STATEMENT-END
    := by
  exact
    exists_isCommonEventTwoTermBigOWith_cutoffResponseJ_of_iterateMeanBound _
    (Provider.Homogenization.exists_iterateMeanBound_integral_cutoffResponseJ _)
