/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenSigmaBar
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenWireChain

/-!
# StepSevenSigmaBarChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7d: the narrowed chain, generic in the `σ` comparison

## What this module does

The fifth and last of the sites where the proved chain hard-codes the printed
`σ_{n'} ≤ 2 σ_m` is the narrowed Step-7d chain.

Making the comparison constant a parameter closes the `hcomp` gap: the `σ`
comparison can then be discharged from the frozen Section-3 `inductionState` by
`sigmaBar_le_four_mul_sigmaBar`, so the chain no longer asks its caller for a
comparison it cannot supply.  The output constant picks up `√4 = 2` where print
writes `√2`.

## References

* ABK26, Step 7d; `e.energy.density.estimate`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open scoped ENNReal

noncomputable section

/-- **Step 7d, end to end, with `hcg`/`hembed`/`hbridge` discharged and the `σ`
comparison generic.**

The narrowed Step-7d chain with the printed constant `2` replaced
by a parameter `Ccmp`; the remaining conditional inputs are still exactly
`hlambda` (`e.lambda.stability.applied`) and the Step-7c gradient display
`hgrad`. -/
theorem exists_stepSevenEnd_chain_of_lambda_gen (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {alpha : ℝ} {n m : ℤ} {Q : TriadicCube d} {a : CoeffFamily d}
        {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
        {Cg Cmean Clam Ccmp Kg Kd Ks Ctr shomNp shomMp shomM
          gradLoc oscTrunc gradM dataG dataM W G H : ℝ},
        0 ≤ Cg → 0 ≤ Cmean → 0 ≤ Clam → 0 ≤ Ks → 0 ≤ Ccmp → 0 ≤ shomMp → 0 < shomM →
        0 ≤ oscTrunc → 0 ≤ gradM → 0 ≤ dataG → 0 ≤ W → 0 ≤ G → 0 ≤ H →
        ForceBesovRegularity Q stepSevenCgS g →
        stepSevenCgLamInv Q a stepSevenCgS ≤ Clam * shomMp →
        forcedSolutionEnergyNorm Q a u ≤ Kg * gradM →
        scaleNormalizedPositiveBesovVectorSeminormTwo Q stepSevenCgS g ≤ Kd * dataG →
        shomMp ≤ Ks * shomM⁻¹ →
        Real.sqrt Ks * Kg ≤ Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) →
        Ks * Kd ≤ Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) →
        oscTrunc ≤ Cmean * ((cubeScaleFactor Q)⁻¹ *
          cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.toH1.toFun x)) →
        shomNp ≤ Ccmp * shomM →
        gradLoc ≤ Cg * Real.sqrt shomNp *
            Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) * oscTrunc +
          Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
            (Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) + dataM) →
          gradLoc ≤
            Cg * Real.sqrt Ccmp *
                (Cmean * stepSevenEmbeddingConst d * stepSevenBridgeConst stepSevenCgS *
                  (C * 64 * (Real.sqrt Clam + Clam)) * Ctr) *
                Real.rpow (3 : ℝ) (stepSixExponent alpha n m) *
                (gradM + Real.sqrt shomM⁻¹ * dataG) +
              Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
                (Real.sqrt Ccmp *
                  (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
  obtain ⟨C, hCpos, hC⟩ := exists_stepSevenCgPoincareInput_pinned d
  refine ⟨C, hCpos, ?_⟩
  intro alpha n m Q a g u Cg Cmean Clam Ccmp Kg Kd Ks Ctr shomNp shomMp shomM
    gradLoc oscTrunc gradM dataG dataM W G H
    hCg hCmean hClam hKs hCcmp hshomMp hshomM hoscTrunc hgradM hdataG hW hG hH
    hforce hlambda htrGrad htrData htrShom hKgb hKdb hmean hcomp hgrad
  -- the data leg's nonnegativity: a field of the printed `𝐠 ∈ H^s` binder
  have hdataNN : (0 : ℝ) ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q stepSevenCgS g :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q stepSevenCgS g
      hforce.partialSeminorms_bddAbove
  -- the `B^{-s₀}_{2,2}` membership: proved upstream, not a hypothesis
  have hbdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q stepSevenCgS N
          (forcedSolutionGradientField u)) :=
    forcedSolutionGradientField_negativeBesovPartialSeminormTwo_bddAbove u
      stepSevenCgS_pos
  -- the coarse-graining Poincaré, `hcg` discharged
  have hcg := hC (a := a) u hforce
  have hCcg : (0 : ℝ) ≤ C * 64 := by linarith only [hCpos]
  have hshomMinv : (0 : ℝ) ≤ shomM⁻¹ := (inv_pos.mpr hshomM).le
  have hE : (0 : ℝ) ≤ forcedSolutionEnergyNorm Q a u := by
    rw [forcedSolutionEnergyNorm, h1EnergyNormOnCube]
    exact Real.sqrt_nonneg _
  have hpoincare := stepSevenCgPoincareApplied hCcg hClam hKs hshomMp hshomMinv hE hdataNN
    hgradM hdataG hcg hlambda htrGrad htrData htrShom hKgb hKdb
  -- the embedding, `hembed` discharged
  have hembed := stepSevenEmbedding Q u.toH1
    (bddAbove_partialOne_of_partialTwo Q stepSevenCgS_lt_one
      (forcedSolutionGradientField u) hbdd)
  -- the summability conversion, `hbridge` discharged
  have hbridge := stepSevenBridge_to_scaleNormalized Q stepSevenCgS_lt_one
    (forcedSolutionGradientField u) hbdd
  -- the chain, generic in the `σ` comparison
  exact stepSevenEnd_chain_gen hCg hCmean (stepSevenEmbeddingConst_nonneg d)
    (stepSevenBridgeConst_nonneg stepSevenCgS) hCcmp hshomM hoscTrunc hW hG hH hcomp
    hgrad hmean hembed hbridge hpoincare

end

end Algsuperdiff.Section4.Provider.Regularity
