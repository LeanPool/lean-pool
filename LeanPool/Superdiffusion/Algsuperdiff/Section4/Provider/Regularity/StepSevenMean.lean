/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenSigmaBarChain

/-!
# StepSevenMean

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7d: the `hmean` producer, and the chain without `hmean`

## The gap this module closes

```text
  oscTrunc ≤ Cmean · ( (3^{Q.scale})^{-1} · osc_{L²}(Q; u) )
```

as a hypothesis of the narrowed Step-7d chain.
Producers do exist, in two steps, at `Cmean = √(3^d)`:

* `normalizedL2On_image_add_sub_average_le_cubeBesovOscillation` (the off-grid
  recovery at constant `1`) — the translated cube's mass against the
  origin-cube oscillation of the translated sample.

This module composes them (`stepSevenHmean_of_sandwich`) and proves the
narrowed chain with `hmean` gone
(`exists_stepSevenEnd_chain_of_lambda_hmeanFree`).

## The carriers, and where the two constants come from

At the scale normalization `Q = originCube d k` (`k = m'-1` at the consumption
site) with the sample translated by `c`:

```text
  oscTrunc = 3^{-k}‖u - (u)_{(z+□_k)∩□_m}‖_{L²((z+□_k)∩□_m)}     (the tex's LHS)
           ≤ 3^{d/2} · 3^{-k}‖u - (u)_{c+□_k}‖_{L²(c+□_k)}        (sandwich)
           ≤ 3^{d/2} · 3^{-k}·osc_{L²}(□_k; u(·+c)) .              (cost 1)
```

So `Cmean = √(3^d)` and nothing else enters.

## What is still the caller's

The five integrability binders of the two proved atoms (`w` and `w²` on both
windows, and the mean-subtracted square on the sandwich cube) and the sandwich
inclusion `hST` — the latter is `StepSevenSelectionData.upper_sandwich_in` at
`k = m'-1`, so it is free at the selection.  The three measure-theoretic side
conditions of the sandwich cube (measurability, positive volume, finite volume)
are discharged here
rather than carried: a translate of the open cube is open and has volume
`3^{dk}`.

## References

* ABK26, Step 7d.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The sandwich cube's measure-theoretic data, discharged -/

/-- The translated open cube is measurable. -/
theorem measurableSet_image_add_openCubeSet (c : Vec d) (k : ℤ) :
    MeasurableSet ((fun y => c + y) '' openCubeSet (originCube d k)) := by
  rw [image_add_eq_preimage]
  exact ((isOpenBoundedConvexDomain_openCubeSet
    (originCube d k)).isOpen.measurableSet).preimage (measurable_const_add (-c))

/-- The translated open cube has finite volume. -/
theorem volume_image_add_openCubeSet_ne_top (c : Vec d) (k : ℤ) :
    volume ((fun y => c + y) '' openCubeSet (originCube d k)) ≠ ⊤ := by
  rw [volume_image_add]
  exact volume_openCubeSet_originCube_ne_top d k

/-- The translated open cube has positive volume `3^{dk}`. -/
theorem volume_toReal_image_add_openCubeSet_pos (c : Vec d) (k : ℤ) :
    0 < (volume ((fun y => c + y) '' openCubeSet (originCube d k))).toReal := by
  have h : (volume ((fun y => c + y) '' openCubeSet (originCube d k))).toReal =
      ((3 : ℝ) ^ k) ^ d := by
    rw [volume_image_add, volume_toReal_openCubeSet_originCube]
  rw [h]
  exact pow_pos (zpow_pos (by norm_num : (0 : ℝ) < 3) k) d

/-! ## 2. The `hmean` producer -/

/-- ```text
  3^{-k}‖u - (u)_{(z+□_k)∩□_m}‖_{L²((z+□_k)∩□_m)}
      ≤ √(3^d) · ( 3^{-k} · osc_{L²}(□_k; u(·+c)) ) ,
```

which is the `hmean` slot of the Step-7d chain at `Cmean = √(3^d)` and `Q =
originCube d k`.  Two proved atoms composed, nothing else. -/
theorem stepSevenHmean_of_sandwich {m k : ℤ} {z c : Vec d} {w : Vec d → ℝ}
    (v : H1Function (openCubeSet (originCube d k))) (hv : ∀ y, v.toFun y = w (y + c))
    (hz : z ∈ openCubeSet (originCube d m)) (hkm : k ≤ m)
    (hST : truncatedWindow z m k ⊆ (fun y => c + y) '' openCubeSet (originCube d k))
    (hwS : IntegrableOn w (truncatedWindow z m k))
    (hwS2 : IntegrableOn (fun x => w x ^ 2) (truncatedWindow z m k))
    (hwT : IntegrableOn w ((fun y => c + y) '' openCubeSet (originCube d k)))
    (hwT2 : IntegrableOn (fun x => w x ^ 2)
      ((fun y => c + y) '' openCubeSet (originCube d k)))
    (hint : IntegrableOn
      (fun x => (w x - volumeAverage ((fun y => c + y) ''
        openCubeSet (originCube d k)) w) ^ 2)
      ((fun y => c + y) '' openCubeSet (originCube d k))) :
    (cubeScaleFactor (originCube d k))⁻¹ *
        normalizedL2On (truncatedWindow z m k)
          (fun x => w x - volumeAverage (truncatedWindow z m k) w) ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        ((cubeScaleFactor (originCube d k))⁻¹ *
          cubeBesovOscillation (originCube d k) (2 : ℝ≥0∞) (fun x => v.toFun x)) := by
  have hinv : (0 : ℝ) ≤ (cubeScaleFactor (originCube d k))⁻¹ :=
    (inv_pos.mpr (cubeScaleFactor_pos' (originCube d k))).le
  have hstep1 := stepSevenEndpointMeanComparison (k := k) (c := c) (u := w) hz hkm hST
    hwS hwS2 hint
  have hstep2 := normalizedL2On_image_add_sub_average_le_cubeBesovOscillation
    (Q := originCube d k) (c := c) (w := w) v hv
    (measurableSet_image_add_openCubeSet c k)
    (volume_toReal_image_add_openCubeSet_pos c k)
    (volume_image_add_openCubeSet_ne_top c k) hwT hwT2
  have hchain : normalizedL2On (truncatedWindow z m k)
      (fun x => w x - volumeAverage (truncatedWindow z m k) w) ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        cubeBesovOscillation (originCube d k) (2 : ℝ≥0∞) (fun x => v.toFun x) :=
    le_trans hstep1 (mul_le_mul_of_nonneg_left hstep2 (Real.sqrt_nonneg _))
  have hmul := mul_le_mul_of_nonneg_left hchain hinv
  have hassoc : (cubeScaleFactor (originCube d k))⁻¹ *
      (Real.sqrt ((3 : ℝ) ^ d) *
        cubeBesovOscillation (originCube d k) (2 : ℝ≥0∞) (fun x => v.toFun x)) =
      Real.sqrt ((3 : ℝ) ^ d) *
        ((cubeScaleFactor (originCube d k))⁻¹ *
          cubeBesovOscillation (originCube d k) (2 : ℝ≥0∞) (fun x => v.toFun x)) := by
    ring
  linarith only [hmul, hassoc.ge, hassoc.le]

/-- The Step-7d transported oscillation is nonnegative — the chain's `hoscTrunc` at
the concrete carrier, so the caller need not supply it. -/
theorem stepSevenOscTrunc_nonneg (z : Vec d) (m k : ℤ) (w : Vec d → ℝ) :
    (0 : ℝ) ≤ (cubeScaleFactor (originCube d k))⁻¹ *
      normalizedL2On (truncatedWindow z m k)
        (fun x => w x - volumeAverage (truncatedWindow z m k) w) :=
  mul_nonneg (inv_pos.mpr (cubeScaleFactor_pos' (originCube d k))).le
    (normalizedL2On_nonneg _ _)

/-! ## 3. The narrowed chain, with `hmean` gone -/

/-- **Step 7d end to end with `hcg`, `hembed`, `hbridge` AND `hmean` discharged.**

`exists_stepSevenEnd_chain_of_lambda_gen` fed by `stepSevenHmean_of_sandwich`, at
`Cmean = √(3^d)` and the concrete transported oscillation

```text
  oscTrunc = 3^{-k}‖u - (u)_{(z+□_k)∩□_m}‖_{L²((z+□_k)∩□_m)} .
```

`hoscTrunc` is discharged too (it is a product of nonnegatives at the concrete
carrier).  The remaining conditional inputs are `hlambda`
(`e.lambda.stability.applied`) and the Step-7c gradient display `hgrad`;
everything else is the caller's geometry, integrability, or the printed
nonnegativity data. -/
theorem exists_stepSevenEnd_chain_of_lambda_hmeanFree (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {alpha : ℝ} {n m k : ℤ} {a : CoeffFamily d} {g : Vec d → Vec d}
        {z c : Vec d} {w : Vec d → ℝ}
        (u : ForcedCubeSolution (originCube d k) a g)
        {Cg Clam Ccmp Kg Kd Ks Ctr shomNp shomMp shomM
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
        0 ≤ Cg → 0 ≤ Clam → 0 ≤ Ks → 0 ≤ Ccmp → 0 ≤ shomMp → 0 < shomM →
        0 ≤ gradM → 0 ≤ dataG → 0 ≤ W → 0 ≤ G → 0 ≤ H →
        ForceBesovRegularity (originCube d k) stepSevenCgS g →
        stepSevenCgLamInv (originCube d k) a stepSevenCgS ≤ Clam * shomMp →
        forcedSolutionEnergyNorm (originCube d k) a u ≤ Kg * gradM →
        scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k) stepSevenCgS g ≤
          Kd * dataG →
        shomMp ≤ Ks * shomM⁻¹ →
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
                  (C * 64 * (Real.sqrt Clam + Clam)) * Ctr) *
                Real.rpow (3 : ℝ) (stepSixExponent alpha n m) *
                (gradM + Real.sqrt shomM⁻¹ * dataG) +
              Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
                (Real.sqrt Ccmp *
                  (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
  obtain ⟨C, hCpos, hC⟩ := exists_stepSevenEnd_chain_of_lambda_gen d
  refine ⟨C, hCpos, ?_⟩
  intro alpha n m k a g z c w u Cg Clam Ccmp Kg Kd Ks Ctr shomNp shomMp shomM
    gradLoc gradM dataG dataM W G H
    hv hz hkm hST hwS hwS2 hwT hwT2 hint
    hCg hClam hKs hCcmp hshomMp hshomM hgradM hdataG hW hG hH
    hforce hlambda htrGrad htrData htrShom hKgb hKdb hcomp hgrad
  have hmean := stepSevenHmean_of_sandwich (m := m) (k := k) (z := z) (c := c) (w := w)
    u.toH1 hv hz hkm hST hwS hwS2 hwT hwT2 hint
  exact hC u hCg (Real.sqrt_nonneg _) hClam hKs hCcmp hshomMp hshomM
    (stepSevenOscTrunc_nonneg z m k w) hgradM hdataG hW hG hH hforce hlambda htrGrad
    htrData htrShom hKgb hKdb hmean hcomp hgrad

end

end Algsuperdiff.Section4.Provider.Regularity
