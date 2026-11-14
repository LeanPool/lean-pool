/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenLambdaSlots
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenMean

/-!
# StepSevenLambdaChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7b: the Step-7 chain with `hlambda` discharged

## What this file does

`StepSevenMean.exists_stepSevenEnd_chain_of_lambda_hmeanFree` is the
Step-7 end chain with `hmean` and `hoscTrunc` discharged inside; its remaining
conditional inputs are exactly two — `hlambda` and the Step-7c gradient display
`hgrad`.

`exists_stepSevenEnd_chain_of_caps` below replaces `hlambda` by the
clause-(B) record `StepSevenLambdaCaps` on the parent cube `□_{k+1}`, at
`Clam := (32/7)·CB` and `shomMp := σ^{-1}` — the row-1 entry of the
derived-slot table (`StepSevenLambdaSlots.stepSevenCgLamInv_le_of_caps`).  The
chain's conditional set is thereby narrowed to

```text
   clause (B)  +  the Step-7c hgrad
```

and clause (B) is itself produced unconditionally, a.e. on the §4.4 good event,
by `StepSevenLambdaGoodEvent.ae_stepSevenLambdaCaps`.

Every other binder of the parent chain is carried verbatim; only `Clam` and
`shomMp` are substituted, and the two positivity binders that referred to them
(`0 ≤ Clam`, `0 ≤ shomMp`) are replaced by `0 ≤ CB` and `0 < sigma`, from which
they are derived here.

## References

* ABK26, `t.regularity` Step 7.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. Row 1 at the chain's own indexing -/

/-- **Row 1 of the derived-slot table at the chain's indexing.**  Clause (B) on
the parent cube `□_{k+1}` caps the chain's `hlambda` slot on `□_k`:

```text
  λ_{1/8,2}^{-1}(□_k; a) ≤ (32/7)·CB · σ^{-1} .
``` -/
theorem stepSevenCgLamInv_le_of_caps_succ [NeZero d] {k : ℤ} (a : CoeffFamily d)
    {sigma CB : ℝ}
    (hcaps : StepSevenLambdaCaps (originCube d (k + 1)) a sigma CB) :
    stepSevenCgLamInv (originCube d k) a stepSevenCgS ≤ (32 / 7 * CB) * sigma⁻¹ := by
  have h := stepSevenCgLamInv_le_of_caps (k := k + 1) a hcaps
  rwa [show k + 1 - 1 = k by ring] at h

/-! ## 2. The Step-7 chain with `hlambda` discharged -/

/-- **The Step-7 end chain, conditional only on clause (B)'s `hgrad`.**

This is `StepSevenMean.exists_stepSevenEnd_chain_of_lambda_hmeanFree`
verbatim, with the `hlambda` hypothesis `stepSevenCgLamInv (□_k) a stepSevenCgS
≤ Clam * shomMp` replaced by the clause-(B) record on the parent cube and
the two constants substituted: `Clam := (32/7)·CB`, `shomMp := σ^{-1}`. -/
theorem exists_stepSevenEnd_chain_of_caps (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {alpha : ℝ} {n m k : ℤ} {a : CoeffFamily d} {g : Vec d → Vec d}
        {z c : Vec d} {w : Vec d → ℝ}
        (u : ForcedCubeSolution (originCube d k) a g)
        {Cg Ccmp Kg Kd Ks Ctr CB sigma shomNp shomM
          gradLoc gradM dataG dataM W G H : ℝ},
        (∀ y, u.toH1.toFun y = w (y + c)) →
        z ∈ openCubeSet (originCube d m) → k ≤ m →
        truncatedWindow z m k ⊆ (fun y => c + y) '' openCubeSet (originCube d k) →
        IntegrableOn w (truncatedWindow z m k) →
        IntegrableOn (fun x => w x ^ 2) (truncatedWindow z m k) →
        IntegrableOn w ((fun y => c + y) '' openCubeSet (originCube d k)) →
        IntegrableOn (fun x => w x ^ 2)
          ((fun y => c + y) '' openCubeSet (originCube d k)) →
        IntegrableOn
          (fun x => (w x - volumeAverage ((fun y => c + y) ''
            openCubeSet (originCube d k)) w) ^ 2)
          ((fun y => c + y) '' openCubeSet (originCube d k)) →
        0 ≤ Cg → 0 ≤ CB → 0 ≤ Ks → 0 ≤ Ccmp → 0 < sigma → 0 < shomM →
        0 ≤ gradM → 0 ≤ dataG → 0 ≤ W → 0 ≤ G → 0 ≤ H →
        ForceBesovRegularity (originCube d k) stepSevenCgS g →
        StepSevenLambdaCaps (originCube d (k + 1)) a sigma CB →
        forcedSolutionEnergyNorm (originCube d k) a u ≤ Kg * gradM →
        scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k) stepSevenCgS g ≤
          Kd * dataG →
        sigma⁻¹ ≤ Ks * shomM⁻¹ →
        Real.sqrt Ks * Kg ≤ Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) →
        Ks * Kd ≤ Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) →
        shomNp ≤ Ccmp * shomM →
        gradLoc ≤ Cg * Real.sqrt shomNp *
            Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
            ((cubeScaleFactor (originCube d k))⁻¹ *
              normalizedL2On (truncatedWindow z m k)
                (fun x => w x - volumeAverage (truncatedWindow z m k) w)) +
          Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
            (Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) + dataM) →
          gradLoc ≤
            Cg * Real.sqrt Ccmp *
                (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
                  stepSevenBridgeConst stepSevenCgS *
                  (C * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) * Ctr) *
                Real.rpow (3 : ℝ) (stepSixExponent alpha n m) *
                (gradM + Real.sqrt shomM⁻¹ * dataG) +
              Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
                (Real.sqrt Ccmp *
                  (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
  obtain ⟨C, hCpos, hC⟩ := exists_stepSevenEnd_chain_of_lambda_hmeanFree d
  refine ⟨C, hCpos, ?_⟩
  intro alpha n m k a g z c w u Cg Ccmp Kg Kd Ks Ctr CB sigma shomNp shomM
    gradLoc gradM dataG dataM W G H
    hv hz hkm hST hwS hwS2 hwT hwT2 hint
    hCg hCB hKs hCcmp hsigma hshomM hgradM hdataG hW hG hH
    hforce hcaps hgradE hdataB htrShom hKgb hKdb hcomp hgrad
  have hClam : (0 : ℝ) ≤ 32 / 7 * CB := by linarith only [hCB]
  have hshomMp : (0 : ℝ) ≤ sigma⁻¹ := inv_nonneg.mpr hsigma.le
  exact hC u hv hz hkm hST hwS hwS2 hwT hwT2 hint hCg hClam hKs hCcmp hshomMp hshomM
    hgradM hdataG hW hG hH hforce (stepSevenCgLamInv_le_of_caps_succ a hcaps) hgradE
    hdataB htrShom hKgb hKdb hcomp hgrad

end

end Algsuperdiff.Section4.Provider.Regularity
