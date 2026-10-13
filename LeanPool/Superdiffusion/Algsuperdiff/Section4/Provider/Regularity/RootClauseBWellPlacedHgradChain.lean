/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBRebasedWellPlaced
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBGateGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenLambdaChain

/-!
# RootClauseBWellPlacedHgradChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# fine-scale dichotomy geometry

Nothing here imports any of them, nothing here claims an anchor, and nothing
here is a frozen statement.

## The two items

2. The dichotomy geometry, proved's machine-verified probe: the negation of the
   flush overhang at scale `k` IS the gate at scale `k`
   (`no_overhang_iff_gate`), and on the gated side the clamp is inactive
   (`wellPlacedCentre_eq_self_of_gate`).  These make the split `GATE(n')` /
   `flush(n')` at the selected fine scale —'s corrected reading of option (i).

## References

* ABK26, `t.regularity` Step 7.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The dichotomy geometry -/

/-- **The negation of the flush overhang at scale `k` is exactly the gate at scale
`k`** — the fine-scale dichotomy is exhaustive ('s probe, proved). -/
theorem no_overhang_iff_gate {m k : ℤ} {z : Vec d} :
    (∀ (i : Fin d) (sigma : ℝ), (sigma = 1 ∨ sigma = -1) →
        ¬ (wellPlacedHalfGap m k < sigma * z i)) ↔
      ((fun y => z + y) '' openCubeSet (originCube d k) ⊆
        openCubeSet (originCube d m)) := by
  rw [image_add_subset_openCubeSet_iff]
  constructor
  · intro h i
    have h1 := not_lt.mp (h i 1 (Or.inl rfl))
    have h2 := not_lt.mp (h i (-1) (Or.inr rfl))
    rw [wellPlacedHalfGap] at h1 h2
    rcases abs_cases (z i) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
      [linarith only [h1]; linarith only [h2]]
  · intro h i sigma hsigma
    have hi := h i
    have habs : |z i| ≤ wellPlacedHalfGap m k := by
      rw [wellPlacedHalfGap]; linarith only [hi]
    have hle := (abs_le.mp habs)
    rcases hsigma with hσ | hσ <;> subst hσ <;> intro hcon <;>
      [linarith only [hle.2, hcon]; linarith only [hle.1, hcon]]

/-! ## 2. The well-placed coarse chain from an abstract `hgrad` -/

/-- **The Step-7 coarse chain at the well-placed re-based frame, from `hgrad`.**

`StepSevenMean.exists_stepSevenEnd_chain_of_lambda_hmeanFree` with every
coarse slot discharged at `c := wellPlacedCentre z m k` on `parentRebasedFamily
M L (k+1) c z ω`, and the fine side abstracted into the parent's own `hgrad`
slot. -/
theorem exists_stepSevenEnd_chain_wellPlaced_of_hgrad (d : ℕ) [NeZero d] :
    ∃ Cch : ℝ, 0 < Cch ∧
      ∀ (M : ABKModel d) (L : ℤ) {alpha : ℝ} {n m k : ℤ}
        {gsrc : Vec d → Vec d} {z : Vec d}
        (uglob hdat : H1Function (openCubeSet (originCube d m)))
        (omega : Cutoff.CutoffSample d)
        {Cg Ccmp Kd Ks Ctr CB sigma shomNp shomM
          gradLoc dataG dataM W G H : ℝ},
        z ∈ openCubeSet (originCube d m) → k ≤ m →
        0 ≤ Cg → 0 ≤ CB → 0 ≤ Ks → 0 ≤ Ccmp → 0 < sigma → 0 < shomM →
        0 ≤ dataG → 0 ≤ W → 0 ≤ G → 0 ≤ H →
        Support.IsDirichletSolutionOn
          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
          (originCube d m) uglob hdat gsrc →
        MemLp gsrc 2
          (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
        MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
          (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
        stepSevenCgLamInv (originCube d k)
            (parentRebasedFamily M L (k + 1) (wellPlacedCentre z m k) z omega)
            stepSevenCgS ≤ CB * sigma⁻¹ →
        scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k) stepSevenCgS
            (fun x => -gsrc (x + wellPlacedCentre z m k)) ≤ Kd * dataG →
        sigma⁻¹ ≤ Ks * shomM⁻¹ →
        Real.sqrt Ks * rootClauseBTopKg d m k ≤
          Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) →
        Ks * Kd ≤ Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) →
        shomNp ≤ Ccmp * shomM →
        (gradLoc ≤
          Cg * Real.sqrt shomNp *
              Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
              ((cubeScaleFactor (originCube d k))⁻¹ *
                normalizedL2On (truncatedWindow z m k)
                  (fun x => uglob.toFun x -
                    volumeAverage (truncatedWindow z m k) uglob.toFun)) +
            Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
              (Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) + dataM)) →
          gradLoc ≤
            Cg * Real.sqrt Ccmp *
                (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
                  stepSevenBridgeConst stepSevenCgS *
                  (Cch * 64 * (Real.sqrt CB + CB)) * Ctr) *
                Real.rpow (3 : ℝ) (stepSixExponent alpha n m) *
                (stepSevenNuGradNorm (M.nu : ℝ) (openCubeSet (originCube d m))
                    uglob.grad +
                  Real.sqrt shomM⁻¹ * dataG) +
              Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
                (Real.sqrt Ccmp *
                  (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
  obtain ⟨Cchain, hCchainPos, hchain⟩ := exists_stepSevenEnd_chain_of_lambda_hmeanFree d
  refine ⟨Cchain, hCchainPos, ?_⟩
  intro M L alpha n m k gsrc z uglob hdat omega Cg Ccmp Kd Ks Ctr CB sigma shomNp
    shomM gradLoc dataG dataM W G H
    hz hkm hCg hCB hKs hCcmp hsigma hshomM hdataG hW hG hH
    hsol hgL2 hgW hlam hdataB htrShom hKgb hKdb hcomp hgrad
  obtain ⟨v0, hval0, hgrad0, heq0⟩ :=
    exists_coarseFrameSolutionRebased (z := z) M L (k + 1) z omega hkm hsol
  have hgradE := forcedSolutionEnergyNorm_coarseFrameRebased_le M L (k + 1) k m
    (z := z) z omega
    (⟨v0, heq0⟩ : ForcedCubeSolution (originCube d k)
      (parentRebasedFamily M L (k + 1) (wellPlacedCentre z m k) z omega)
      (fun x => -gsrc (x + wellPlacedCentre z m k)))
    uglob hgrad0 hkm
  obtain ⟨hwT, hwT2⟩ := integrableOn_truncatedWindow_pack (m := m) (k := k) z uglob
  obtain ⟨hwS, hwS2, hint⟩ := integrableOn_coarseFrame_pack z hkm uglob
    (volumeAverage ((fun y => wellPlacedCentre z m k + y) ''
      openCubeSet (originCube d k)) uglob.toFun)
  exact hchain
    (⟨v0, heq0⟩ : ForcedCubeSolution (originCube d k)
      (parentRebasedFamily M L (k + 1) (wellPlacedCentre z m k) z omega)
      (fun x => -gsrc (x + wellPlacedCentre z m k)))
    hval0 hz hkm (truncatedWindow_subset_coarseFrame z hkm) hwT hwT2 hwS hwS2 hint
    hCg hCB hKs hCcmp (inv_nonneg.mpr hsigma.le) hshomM
    (stepSevenNuGradNorm_nonneg _ _ _) hdataG hW hG hH
    (forceBesovRegularity_coarseFrame hkm hgL2 hgW)
    hlam hgradE hdataB htrShom hKgb hKdb hcomp hgrad

end

end Algsuperdiff.Section4.Provider.Regularity
