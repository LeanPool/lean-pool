/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBCloseArith

/-!
# RootClauseBCloseChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-- The interior clause-(B) display with `k = m-1` replaced by a
free `k_c ≤ m-1`; the coarse clause-(B) record accordingly sits at `□_{k_c+1}`
against its own `σ_{k_c+1}`, which is what lets the record come from the
Step-3 good event instead of the uncontrolled top scale. -/
theorem rootClauseB_display_interior_freeCoarse (d : ℕ) [NeZero d] :
    ∃ Cch Cc : ℝ, 0 < Cch ∧ 0 < Cc ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
        M.gamma < 1 / 2 →
        ∀ (L : ℤ) {alpha : ℝ} {n m kc n' : ℤ} {z : Vec d}
          (omega : Cutoff.CutoffSample d)
          (uglob hdat : H1Function (openCubeSet (originCube d m)))
          {gsrc : Vec d → Vec d}
          {Khol Kd CB CBc Cdel Cosc CdM C1 delta Cest : ℝ} {B : ℕ},
          z ∈ openCubeSet (originCube d (m - 1)) → m ≤ m0 →
          n' ≤ m - 1 → n + 1 ≤ n' - 2 → n ≤ m →
          n' ≤ kc → kc ≤ m - 1 → m - (kc + 1) ≤ (B : ℤ) + 1 →
          Support.IsDirichletSolutionOn
              (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
              (originCube d m) uglob hdat gsrc →
          MemLp gsrc 2
              (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
          MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
              (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
          0 ≤ Khol → 0 ≤ Kd → 0 ≤ CB → 0 ≤ CBc → 0 ≤ Cdel → 0 ≤ Cosc → 0 ≤ CdM →
          2 * (d : ℝ) + 2 ≤ C1 → 0 ≤ alpha → alpha ≤ 1 →
          delta ≤ C1⁻¹ * (1 - alpha) → n' - n ≤ (B : ℤ) + 6 →
          (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1) →
          StepSevenLambdaCaps (originCube d (kc + 1))
              (Support.fluxCorrectedCoeffFamily M L (kc + 1) (originCube d (kc + 1))
                (Cutoff.translateCutoffSample z omega))
              ((Annealed.sigmaBar M (kc + 1) : ℝ)) CB →
          StepSevenLambdaCaps (originCube d (n' + 1))
              (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
                (Cutoff.translateCutoffSample z omega))
              ((Annealed.sigmaBar M (n' + 1) : ℝ)) CBc →
          scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d kc)
              stepSevenCgS (fun x => -gsrc (x + z)) ≤
            Kd * edFinalDataOscG Khol m →
          stepSevenCaccDataM (originCube d n')
              (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
                (Cutoff.translateCutoffSample z omega))
              (fun x => -gsrc (x + z)) ≤
            CdM * (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
              edFinalDataOscG Khol m) →
          ((3 : ℝ) ^ (-n') *
              normalizedL2On (truncatedWindow z m n')
                (fun x => uglob.toFun x -
                  volumeAverage (truncatedWindow z m n') uglob.toFun) ≤
            Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                ((3 : ℝ) ^ (-kc) *
                  normalizedL2On (truncatedWindow z m kc)
                    (fun x => uglob.toFun x -
                      volumeAverage (truncatedWindow z m kc) uglob.toFun)) +
              Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                (edFinalDataG M Cdel
                  (Khol * stepFourGagliardoConst d stepOneS) m + 0)) →
          rootClauseBPrefactor d Cch
              (stepSevenCaccConst Cc (originCube d n')
                (Support.fluxCorrectedCoeffFamily M L (n' + 1)
                  (originCube d (n' + 1)) (Cutoff.translateCutoffSample z omega)))
              Cosc CBc CB (rootClauseBTopCtr d Kd)
              (edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS) CdM ≤
            Cest →
          Real.sqrt M.nu *
              normalizedL2On (truncatedWindow z m (n + 1))
                (fun y => Real.sqrt (vecNormSq (uglob.grad y)))
            ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
              (Real.sqrt M.nu *
                  normalizedL2On (openCubeSet (originCube d m))
                    (fun y => Real.sqrt (vecNormSq (uglob.grad y))) +
                Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol) := by
  obtain ⟨Cch, Cc, hCch, hCc, hchain⟩ := exists_stepSevenEnd_chain_interior_of_dirichlet d
  refine ⟨Cch, Cc, hCch, hCc, ?_⟩
  intro M m0 Ecap hS hgamma L alpha n m kc n' z omega uglob hdat gsrc Khol Kd CB CBc Cdel
    Cosc CdM C1 delta Cest B hzin hmm0 hn' hcore hnm hn'kc hkc hgapTop hsol hgL2 hgW
    hKhol hKd hCB hCBc hCdel hCosc hCdM hC1 halpha0 halpha1 hdelta hgap hbudget hcaps
    hcapsc hdataB hdataM hosc hCest
  -- geometry at the re-cut coarse scale
  have hzm : z ∈ openCubeSet (originCube d m) :=
    openCubeSet_originCube_subset_of_le (by omega) hzin
  have hsub : translateSet z (openCubeSet (originCube d kc)) ⊆
      openCubeSet (originCube d m) := by
    rw [← image_add_eq_translateSet]
    exact image_add_subset_openCubeSet_of_mem_inner hzin hkc
  have hWeq : truncatedWindow z m kc =
      (fun y => z + y) '' openCubeSet (originCube d kc) := by
    rw [truncatedWindow_eq_translateSet_of_mem_inner hzin hkc, image_add_eq_translateSet]
  have hTsub : (fun y => z + y) '' openCubeSet (originCube d kc) ⊆
      openCubeSet (originCube d m) := by
    rw [image_add_eq_translateSet]; exact hsub
  have hTtop : volume ((fun y => z + y) '' openCubeSet (originCube d kc)) ≠ ⊤ :=
    volume_image_add_openCubeSet_ne_top z kc
  have hStop : volume (truncatedWindow z m kc) ≠ ⊤ :=
    (volume_truncatedWindow_lt_top z m kc).ne
  -- the solution object at the lattice centre, at the free flux pair `(k_c+1, □_{k_c+1})`
  obtain ⟨v, hval, hgradid, heqv⟩ :=
    exists_stepSevenCaccInteriorSolution (n' := kc) (mf := kc + 1) M L
      (originCube d (kc + 1)) omega hzin hkc hsol
  have hgradE : forcedSolutionEnergyNorm (originCube d kc)
        (Support.fluxCorrectedCoeffFamily M L (kc + 1) (originCube d (kc + 1))
          (Cutoff.translateCutoffSample z omega))
        (⟨v, heqv⟩ : ForcedCubeSolution (originCube d kc)
          (Support.fluxCorrectedCoeffFamily M L (kc + 1) (originCube d (kc + 1))
            (Cutoff.translateCutoffSample z omega)) (fun x => -gsrc (x + z))) ≤
      rootClauseBTopKg d m kc *
        stepSevenNuGradNorm (M.nu : ℝ) (openCubeSet (originCube d m)) uglob.grad := by
    rw [forcedSolutionEnergyNorm_fluxCorrected_eq_nuGradNorm M L (kc + 1) m kc
      (originCube d (kc + 1)) omega _ uglob.grad hgradid hzin hkc]
    exact stepSevenNuGradNorm_window_le_cube d (le_of_lt M.nu_pos) hzin hkc uglob
  -- the two `σ` slots
  have hsigmaPos : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hsigmaCoarse : (0 : ℝ) < (Annealed.sigmaBar M (kc + 1) : ℝ) :=
    (Annealed.sigmaBar M (kc + 1)).2
  have htrShom : ((Annealed.sigmaBar M (kc + 1) : ℝ))⁻¹ ≤
      rootClauseBTopKs M.gamma m (kc + 1) * ((Annealed.sigmaBar M m : ℝ))⁻¹ :=
    rootClauseBTop_htrShom hS (by omega) hmm0
  have hcomp : (Annealed.sigmaBar M (n' + 1) : ℝ) ≤ 4 * (Annealed.sigmaBar M m : ℝ) :=
    sigmaBar_le_four_mul_sigmaBar M hS (by omega) hmm0
  -- the two `K_tr` dominations at the re-cut
  have hE : (0 : ℝ) ≤ stepSixExponent alpha n m := by
    have hc : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    rw [stepSixExponent]
    exact mul_nonneg (by linarith only [halpha1]) (by linarith only [hc])
  have hKgb := rootClauseBTop_hKgb (d := d) (Kd := Kd) (n := n) (m := m) (k := kc)
    (Bb := B) hgamma hC1 halpha0 halpha1 hnm hdelta hbudget (by omega) hgapTop
  have hKdb := rootClauseBTop_hKdb (d := d) (Kd := Kd) (n := n) (m := m) (k := kc)
    (Bb := B) hgamma hKd hC1 halpha0 halpha1 hnm hdelta hbudget (by omega) hgapTop
  have hCtr0 : (0 : ℝ) ≤ rootClauseBTopCtr d Kd := rootClauseBTopCtr_nonneg d Kd
  -- the `dataOsc` slot (items (i) and (ii))
  have hW0 : (0 : ℝ) ≤ edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS :=
    mul_nonneg (edFinalDataOscW_nonneg hgamma hCdel) (stepFourGagliardoConst_nonneg d _)
  have hG0 : (0 : ℝ) ≤ edFinalDataOscG Khol m := edFinalDataOscG_nonneg hKhol m
  have hoscChain := hosc
  rw [edFinalDataG_eq_dataOsc_scaled M Cdel Khol (stepFourGagliardoConst d stepOneS) m,
    ← cubeScaleFactor_originCube_inv d kc] at hoscChain
  -- the chain
  have hmain := hchain M L (originCube d (n' + 1)) uglob hdat omega ⟨v, heqv⟩
    (Ccmp := 4) (Kg := rootClauseBTopKg d m kc) (Kd := Kd)
    (Ks := rootClauseBTopKs M.gamma m (kc + 1))
    (Ctr := rootClauseBTopCtr d Kd) (CB := CB) (CBc := CBc)
    (sigma := (Annealed.sigmaBar M (kc + 1) : ℝ))
    (sigmac := (Annealed.sigmaBar M (n' + 1) : ℝ))
    (shomM := (Annealed.sigmaBar M m : ℝ))
    (gradM := stepSevenNuGradNorm (M.nu : ℝ) (openCubeSet (originCube d m)) uglob.grad)
    (dataG := edFinalDataOscG Khol m)
    (W := edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS)
    (G := edFinalDataOscG Khol m) (H := 0) (C1 := C1) (delta := delta) (Cosc := Cosc)
    (B := B) hval hzm (by omega) (hWeq ▸ Set.Subset.refl _)
    (integrableOn_toFun_subset uglob (truncatedWindow_subset_domain z m kc) hStop)
    (integrableOn_sq_toFun_subset uglob (truncatedWindow_subset_domain z m kc) hStop)
    (integrableOn_toFun_subset uglob hTsub hTtop)
    (integrableOn_sq_toFun_subset uglob hTsub hTtop)
    (integrableOn_sub_sq_toFun_subset uglob hTsub hTtop _)
    hCB (rootClauseBTopKs_nonneg _ _ _) (by norm_num) hsigmaCoarse hsigmaPos
    (stepSevenNuGradNorm_nonneg _ _ _) hG0 hW0 hG0 (le_refl 0)
    (forceBesovRegularity_stepSevenCacc_interior (n' := kc) hzin hkc hgL2 hgW)
    hcaps hgradE hdataB htrShom hKgb hKdb hcomp hzin hn' hcore hsol hgL2 hgW hC1
    halpha0 halpha1 hnm hdelta hgap hbudget hCosc hCBc hcapsc hoscChain
  -- the outer collapse (item (iv))
  have hCgnn : (0 : ℝ) ≤ rootClauseBCg d
      (stepSevenCaccConst Cc (originCube d n')
        (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
          (Cutoff.translateCutoffSample z omega))) Cosc CBc := by
    have h1 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have h3 : (0 : ℝ) ≤ Cosc * Real.sqrt (256 / 63 * CBc) + 1 := by
      have h4 := mul_nonneg hCosc (Real.sqrt_nonneg (256 / 63 * CBc))
      linarith only [h4]
    rw [rootClauseBCg]
    exact mul_nonneg (mul_nonneg h1 (stepSevenCaccConst_nonneg _ _ _)) h3
  have hXnn : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
      stepSevenBridgeConst stepSevenCgS *
      (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) *
      rootClauseBTopCtr d Kd := by
    have hb : (0 : ℝ) ≤ Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB) := by
      have h1 : (0 : ℝ) ≤ Cch * 64 := by linarith only [hCch]
      have h2 : (0 : ℝ) ≤ Real.sqrt (32 / 7 * CB) + 32 / 7 * CB := by
        have := Real.sqrt_nonneg (32 / 7 * CB)
        linarith only [this, hCB]
      exact mul_nonneg h1 h2
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (stepSevenEmbeddingConst_nonneg d)) (stepSevenBridgeConst_nonneg _)) hb) hCtr0
  have hKmain : (0 : ℝ) ≤ rootClauseBCg d
        (stepSevenCaccConst Cc (originCube d n')
          (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
            (Cutoff.translateCutoffSample z omega))) Cosc CBc * Real.sqrt 4 *
      (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) *
        rootClauseBTopCtr d Kd) :=
    mul_nonneg (mul_nonneg hCgnn (Real.sqrt_nonneg 4)) hXnn
  have hcoll := rootClauseB_collapse (CdG := 1) (Lg := edFinalDataOscG Khol m)
    hKmain hCgnn (Real.sqrt_nonneg 4) hW0 hCdM hE
    (stepSevenNuGradNorm_nonneg _ _ _) hG0 (mul_nonneg hW0 hG0)
    (stepSevenCaccDataM_nonneg _ _
      (forceBesovRegularity_stepSevenCacc_interior (n' := n') hzin hn' hgL2 hgW))
    (by rw [one_mul]) (le_refl _) hdataM hmain
  rw [max_self, mul_one] at hcoll
  -- into the root's own carrier and constant
  rw [stepSevenNuGradNorm_eq_sqrt_mul_normalizedL2On (le_of_lt M.nu_pos),
    stepSevenNuGradNorm_eq_sqrt_mul_normalizedL2On (le_of_lt M.nu_pos),
    stepSixExponent, edFinalDataOscG,
    ← mul_assoc (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹)
      (Real.rpow (3 : ℝ) ((m : ℝ) / 2)) Khol] at hcoll
  rw [rootClauseBPrefactor] at hCest
  refine clauseB_const_mono (Real.rpow_pos_of_pos (by norm_num) _).le ?_ hCest hcoll
  have h1 : (0 : ℝ) ≤ Real.sqrt M.nu *
      normalizedL2On (openCubeSet (originCube d m))
        (fun y => Real.sqrt (vecNormSq (uglob.grad y))) :=
    mul_nonneg (Real.sqrt_nonneg _) (normalizedL2On_nonneg _ _)
  have h2 : (0 : ℝ) ≤ Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_pos_of_pos (by norm_num) _).le) hKhol
  linarith only [h1, h2]

end

end Algsuperdiff.Section4.Provider.Regularity
