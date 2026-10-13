/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBWellPlacedHgradChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBGateBoundaryC1

/-!
# RootClauseBDichotomyDisplay

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# an abstract fine-side `hgrad` — NO coarse gate

Nothing here imports any of them, nothing here claims an anchor, and nothing
here is a frozen statement.

## The item

* the coarse side at the print's own well-placed re-based frame (units A--C, F):
  the ONLY geometric inputs are `z ∈ □_m` and the scale ladder;
* the fine side abstracted into the chain's `hgrad` slot, so the fine-scale
  dichotomy (`GATE(n')` / `flush(n')`, both branches proved) can feed it;
* the `dataM` slot abstract, priced by the caller on the printed carrier
  `√σ_m^{-1}·3^{m/2}K_g` — so BOTH branches (the gated Caccioppoli's `dataM`
  and the flush branch's priced `𝐠`-legs) enter one display.

The conclusion is the boundary three-leg display V (the printed
`√σ_m·3^{m/2}K_h` leg included), at every centre `z ∈ □_m`.

## References

* ABK26, `t.regularity`; Step 7.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The well-placed prefactor -/

/-- **The well-placed boundary prefactor**: the collapse constant of the display
below. -/
def rootClauseBWellPlacedPrefactor (d : ℕ) [NeZero d]
    (Cch Cg CB Ctr CWG CWH CdM : ℝ) : ℝ :=
  Cg * Real.sqrt 4 *
      (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt CB + CB)) * Ctr) +
    Cg * (Real.sqrt 4 * CWG + Real.sqrt 4 * CWH + CdM)

/-- The well-placed prefactor at nonnegative data. -/
theorem rootClauseBWellPlacedPrefactor_nonneg (d : ℕ) [NeZero d]
    {Cch Cg CB Ctr CWG CWH CdM : ℝ} (hCch : 0 ≤ Cch) (hCg : 0 ≤ Cg)
    (hCB : 0 ≤ CB) (hCtr : 0 ≤ Ctr) (hCWG : 0 ≤ CWG) (hCWH : 0 ≤ CWH)
    (hCdM : 0 ≤ CdM) :
    0 ≤ rootClauseBWellPlacedPrefactor d Cch Cg CB Ctr CWG CWH CdM := by
  have hbr : (0 : ℝ) ≤ Real.sqrt CB + CB := by
    have h5 := Real.sqrt_nonneg CB
    linarith only [h5, hCB]
  have hX : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
      stepSevenBridgeConst stepSevenCgS * (Cch * 64 * (Real.sqrt CB + CB)) * Ctr := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (stepSevenEmbeddingConst_nonneg d)) (stepSevenBridgeConst_nonneg _)) ?_) hCtr
    exact mul_nonneg (by linarith only [hCch]) hbr
  have hY : (0 : ℝ) ≤ Real.sqrt 4 * CWG + Real.sqrt 4 * CWH + CdM := by
    have h1 := mul_nonneg (Real.sqrt_nonneg (4 : ℝ)) hCWG
    have h2 := mul_nonneg (Real.sqrt_nonneg (4 : ℝ)) hCWH
    linarith only [h1, h2, hCdM]
  have hleft : (0 : ℝ) ≤ Cg * Real.sqrt 4 *
      (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt CB + CB)) * Ctr) :=
    mul_nonneg (mul_nonneg hCg (Real.sqrt_nonneg 4)) hX
  have hright : (0 : ℝ) ≤ Cg * (Real.sqrt 4 * CWG + Real.sqrt 4 * CWH + CdM) :=
    mul_nonneg hCg hY
  rw [rootClauseBWellPlacedPrefactor]
  linarith only [hleft, hright]

/-! ## 2. The display -/

/-- **Clause (A) of the a.e. lattice display at the W frame, from the fine-side
`hgrad` — no coarse gate, every centre `z ∈ □_m`.**  See the module docstring. -/
theorem rootClauseB_display_wellPlaced_of_hgrad (d : ℕ) [NeZero d] :
    ∃ Cch : ℝ, 0 < Cch ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
        M.gamma < 1 / 2 →
        ∀ (L : ℤ) {alpha : ℝ} {n m kc np : ℤ} {z : Vec d}
          (omega : Cutoff.CutoffSample d)
          (uglob hdat : H1Function (openCubeSet (originCube d m)))
          {gsrc : Vec d → Vec d}
          {Khol Kh Kd CB Cg Cdel CdM CWH C1 delta Cest dataH dataM : ℝ} {B : ℕ},
          z ∈ openCubeSet (originCube d m) → m ≤ m0 →
          n ≤ m → kc ≤ m - 1 → np + 1 ≤ m → m - (kc + 1) ≤ (B : ℤ) + 1 →
          Support.IsDirichletSolutionOn
              (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
              (originCube d m) uglob hdat gsrc →
          MemLp gsrc 2
              (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
          MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
              (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
          0 ≤ Khol → 0 ≤ Kh → 0 ≤ Kd → 0 ≤ CB → 0 ≤ Cg → 0 ≤ Cdel →
          0 ≤ CdM → 0 ≤ CWH → 0 ≤ dataH → 0 ≤ dataM →
          2 * (d : ℝ) + 2 ≤ C1 → 0 ≤ alpha → alpha ≤ 1 →
          delta ≤ C1⁻¹ * (1 - alpha) →
          (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1) →
          stepSevenCgLamInv (originCube d kc)
              (parentRebasedFamily M L (kc + 1) (wellPlacedCentre z m kc) z omega)
              stepSevenCgS ≤ CB * ((Annealed.sigmaBar M (kc + 1) : ℝ))⁻¹ →
          scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d kc)
              stepSevenCgS (fun x => -gsrc (x + wellPlacedCentre z m kc)) ≤
            Kd * edFinalDataOscG Khol m →
          dataM ≤ CdM * (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
            edFinalDataOscG Khol m) →
          dataH ≤ CWH * edFinalDataOscG Kh m →
          (stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (n + 1))
              uglob.grad ≤
            Cg * Real.sqrt ((Annealed.sigmaBar M (np + 1) : ℝ)) *
                Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
                ((cubeScaleFactor (originCube d kc))⁻¹ *
                  normalizedL2On (truncatedWindow z m kc)
                    (fun x => uglob.toFun x -
                      volumeAverage (truncatedWindow z m kc) uglob.toFun)) +
              Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
                (Real.sqrt ((Annealed.sigmaBar M (np + 1) : ℝ)) *
                  (1 * (((Annealed.sigmaBar M m : ℝ))⁻¹ *
                    ((Annealed.sigmaBar M m : ℝ) *
                      edFinalDataG M Cdel
                        (Khol * stepFourGagliardoConst d stepOneS) m) + dataH)) +
                  dataM)) →
          rootClauseBWellPlacedPrefactor d Cch Cg CB (rootClauseBTopCtr d Kd)
              (edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS) CWH
              CdM ≤ Cest →
          Real.sqrt M.nu *
              normalizedL2On (truncatedWindow z m (n + 1))
                (fun y => Real.sqrt (vecNormSq (uglob.grad y)))
            ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
              (Real.sqrt M.nu *
                  normalizedL2On (openCubeSet (originCube d m))
                    (fun y => Real.sqrt (vecNormSq (uglob.grad y))) +
                Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol +
                Real.sqrt ((Annealed.sigmaBar M m : ℝ)) *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
  obtain ⟨Cch, hCch, hchain⟩ := exists_stepSevenEnd_chain_wellPlaced_of_hgrad d
  refine ⟨Cch, hCch, ?_⟩
  intro M m0 Ecap hS hgamma L alpha n m kc np z omega uglob hdat gsrc Khol Kh Kd CB
    Cg Cdel CdM CWH C1 delta Cest dataH dataM B hz hmm0 hnm hkc hnpm hgapTop
    hsol hgL2 hgW hKhol hKh hKd hCB hCg hCdel hCdM hCWH hdataH0 hdataM0 hC1
    halpha0 halpha1 hdelta hbudget hlam hdataB hdataM hWH hgrad hCest
  -- the σ facts
  have hsigmaPos : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hsigmaCoarse : (0 : ℝ) < (Annealed.sigmaBar M (kc + 1) : ℝ) :=
    (Annealed.sigmaBar M (kc + 1)).2
  have htrShom : ((Annealed.sigmaBar M (kc + 1) : ℝ))⁻¹ ≤
      rootClauseBTopKs M.gamma m (kc + 1) * ((Annealed.sigmaBar M m : ℝ))⁻¹ :=
    rootClauseBTop_htrShom hS (by omega) hmm0
  have hcomp : (Annealed.sigmaBar M (np + 1) : ℝ) ≤ 4 * (Annealed.sigmaBar M m : ℝ) :=
    sigmaBar_le_four_mul_sigmaBar M hS (by omega) hmm0
  -- the budget dominations
  have hE : (0 : ℝ) ≤ stepSixExponent alpha n m := by
    have hc : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    rw [stepSixExponent]
    exact mul_nonneg (by linarith only [halpha1]) (by linarith only [hc])
  have hKgb := rootClauseBTop_hKgb (d := d) (Kd := Kd) (n := n) (m := m) (k := kc)
    (Bb := B) hgamma hC1 halpha0 halpha1 hnm hdelta hbudget (by omega) hgapTop
  have hKdb := rootClauseBTop_hKdb (d := d) (Kd := Kd) (n := n) (m := m) (k := kc)
    (Bb := B) hgamma hKd hC1 halpha0 halpha1 hnm hdelta hbudget (by omega) hgapTop
  have hCtr0 : (0 : ℝ) ≤ rootClauseBTopCtr d Kd := rootClauseBTopCtr_nonneg d Kd
  -- the data-leg nonnegativity
  have hW0 : (0 : ℝ) ≤ edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS :=
    mul_nonneg (edFinalDataOscW_nonneg hgamma hCdel) (stepFourGagliardoConst_nonneg d _)
  have hG0 : (0 : ℝ) ≤ edFinalDataOscG Khol m := edFinalDataOscG_nonneg hKhol m
  have hGpres : (0 : ℝ) ≤
      (Annealed.sigmaBar M m : ℝ) *
        edFinalDataG M Cdel (Khol * stepFourGagliardoConst d stepOneS) m := by
    rw [sigmaBar_mul_edFinalDataG_eq]
    exact mul_nonneg hW0 hG0
  -- the chain
  have hmain := hchain M L (alpha := alpha) (n := n) (m := m) (k := kc)
    (gsrc := gsrc) (z := z) uglob hdat omega
    (Cg := Cg) (Ccmp := 4) (Kd := Kd)
    (Ks := rootClauseBTopKs M.gamma m (kc + 1))
    (Ctr := rootClauseBTopCtr d Kd) (CB := CB)
    (sigma := (Annealed.sigmaBar M (kc + 1) : ℝ))
    (shomNp := (Annealed.sigmaBar M (np + 1) : ℝ))
    (shomM := (Annealed.sigmaBar M m : ℝ))
    (gradLoc := stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (n + 1))
      uglob.grad)
    (dataG := edFinalDataOscG Khol m) (dataM := dataM) (W := 1)
    (G := (Annealed.sigmaBar M m : ℝ) *
      edFinalDataG M Cdel (Khol * stepFourGagliardoConst d stepOneS) m)
    (H := dataH)
    hz (by omega) hCg hCB (rootClauseBTopKs_nonneg _ _ _) (by norm_num)
    hsigmaCoarse hsigmaPos hG0 zero_le_one hGpres hdataH0
    hsol hgL2 hgW hlam hdataB htrShom hKgb hKdb hcomp hgrad
  -- the outer collapse, with the `H` leg kept
  have hXnn : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
      stepSevenBridgeConst stepSevenCgS *
      (Cch * 64 * (Real.sqrt CB + CB)) * rootClauseBTopCtr d Kd := by
    have hb : (0 : ℝ) ≤ Cch * 64 * (Real.sqrt CB + CB) := by
      have h1 : (0 : ℝ) ≤ Cch * 64 := by linarith only [hCch]
      have h2 : (0 : ℝ) ≤ Real.sqrt CB + CB := by
        have := Real.sqrt_nonneg CB
        linarith only [this, hCB]
      exact mul_nonneg h1 h2
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (stepSevenEmbeddingConst_nonneg d)) (stepSevenBridgeConst_nonneg _)) hb) hCtr0
  have hKmain : (0 : ℝ) ≤ Cg * Real.sqrt 4 *
      (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt CB + CB)) * rootClauseBTopCtr d Kd) :=
    mul_nonneg (mul_nonneg hCg (Real.sqrt_nonneg 4)) hXnn
  have hWGid : (1 : ℝ) * ((Annealed.sigmaBar M m : ℝ) *
        edFinalDataG M Cdel (Khol * stepFourGagliardoConst d stepOneS) m) ≤
      (edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS) *
        edFinalDataOscG Khol m := by
    rw [one_mul, sigmaBar_mul_edFinalDataG_eq]
  have hcoll := rootClauseB_collapse_boundary (CdG := 1)
    (Lg := edFinalDataOscG Khol m) (Lh := edFinalDataOscG Kh m)
    hKmain hCg (Real.sqrt_nonneg 4) hW0 hCWH hCdM hE
    (stepSevenNuGradNorm_nonneg _ _ _) hG0 (edFinalDataOscG_nonneg hKh m)
    (by rw [one_mul]; exact hGpres) (by rw [one_mul]; exact hdataH0)
    hdataM0
    (by rw [one_mul])
    hWGid (by rw [one_mul]; exact hWH) hdataM hmain
  rw [max_self, mul_one] at hcoll
  -- into the root's own carrier and constant
  rw [stepSevenNuGradNorm_eq_sqrt_mul_normalizedL2On (le_of_lt M.nu_pos),
    stepSevenNuGradNorm_eq_sqrt_mul_normalizedL2On (le_of_lt M.nu_pos),
    stepSixExponent, edFinalDataOscG, edFinalDataOscG,
    ← mul_assoc (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹)
      (Real.rpow (3 : ℝ) ((m : ℝ) / 2)) Khol,
    ← mul_assoc (Real.sqrt ((Annealed.sigmaBar M m : ℝ)))
      (Real.rpow (3 : ℝ) ((m : ℝ) / 2)) Kh] at hcoll
  rw [rootClauseBWellPlacedPrefactor] at hCest
  refine clauseB_const_mono (Real.rpow_pos_of_pos (by norm_num) _).le ?_ hCest hcoll
  have h1 : (0 : ℝ) ≤ Real.sqrt M.nu *
      normalizedL2On (openCubeSet (originCube d m))
        (fun y => Real.sqrt (vecNormSq (uglob.grad y))) :=
    mul_nonneg (Real.sqrt_nonneg _) (normalizedL2On_nonneg _ _)
  have h2 : (0 : ℝ) ≤ Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_pos_of_pos (by norm_num) _).le) hKhol
  have h3 : (0 : ℝ) ≤ Real.sqrt ((Annealed.sigmaBar M m : ℝ)) *
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_pos_of_pos (by norm_num) _).le) hKh
  linarith only [h1, h2, h3]

end

end Algsuperdiff.Section4.Provider.Regularity
