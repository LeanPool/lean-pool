/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBCloseChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootPayloadCest
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepNineOffGridGeometry

/-!
# RootClauseBClosePayload

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

/-! ## 1. The re-cut payload -/

/-- **The Step-7 payload of the clause-(B) display at a free coarse scale**, at the
lattice centre `z = offGridCentre n x` the root's display is stated at. -/
structure RootClauseBTopPayload [NeZero d] (M : ABKModel d) (L : ℤ)
    (Khol Kd CB CBc Cdel Cosc CdM alpha : ℝ) (n m kc n' : ℤ) (x : Vec d)
    (omega : Cutoff.CutoffSample d)
    (uglob : H1Function (openCubeSet (originCube d m)))
    (gsrc : Vec d → Vec d) : Prop where
  /-- The `A6` clause-(B) record on the re-cut coarse cube `□_{k_c+1}`. -/
  caps : StepSevenLambdaCaps (originCube d (kc + 1))
    (Support.fluxCorrectedCoeffFamily M L (kc + 1) (originCube d (kc + 1))
      (Cutoff.translateCutoffSample (offGridCentre n x) omega))
    ((Annealed.sigmaBar M (kc + 1) : ℝ)) CB
  /-- The `A6` clause-(B) record on the Caccioppoli's cube `□_{n'+1}`. -/
  capsCacc : StepSevenLambdaCaps (originCube d (n' + 1))
    (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
      (Cutoff.translateCutoffSample (offGridCentre n x) omega))
    ((Annealed.sigmaBar M (n' + 1) : ℝ)) CBc
  /-- The Step-7d data transport at the re-cut coarse cube. -/
  dataB : scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d kc)
      stepSevenCgS (fun y => -gsrc (y + offGridCentre n x)) ≤
    Kd * edFinalDataOscG Khol m
  /-- The Caccioppoli's data leg against the printed `K_g`-leg. -/
  dataM : stepSevenCaccDataM (originCube d n')
      (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
        (Cutoff.translateCutoffSample (offGridCentre n x) omega))
      (fun y => -gsrc (y + offGridCentre n x)) ≤
    CdM * (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ * edFinalDataOscG Khol m)
  /-- `e.oscillation.Holder.bound` at `(n', k_c)`. -/
  osc : (3 : ℝ) ^ (-n') *
      normalizedL2On (truncatedWindow (offGridCentre n x) m n')
        (fun y => uglob.toFun y -
          volumeAverage (truncatedWindow (offGridCentre n x) m n') uglob.toFun) ≤
    Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
        ((3 : ℝ) ^ (-kc) *
          normalizedL2On (truncatedWindow (offGridCentre n x) m kc)
            (fun y => uglob.toFun y -
              volumeAverage (truncatedWindow (offGridCentre n x) m kc)
                uglob.toFun)) +
      Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
        (edFinalDataG M Cdel (Khol * stepFourGagliardoConst d stepOneS) m + 0)

/-! ## 2. The endpoint: clause (B) of `RootLatticeDisplay` -/

/-- **Clause (B) of `RootAssemblyConditional.RootLatticeDisplay`, at the re-cut
coarse scale.**

The S conjunct of the root's lattice-centre display — the interior-guarded,
boundary-leg-free half — produced for every datum satisfying
`RootClauseBTopPayload`, with the funding line stated at the `ω`- Caccioppoli
constant unit 1. -/
theorem rootClauseB_display_offGrid_freeUniform (d : ℕ) [NeZero d] :
    ∃ Cch Cc : ℝ, 0 < Cch ∧ 0 < Cc ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
        M.gamma < 1 / 2 →
        ∀ (L : ℤ) {alpha : ℝ} {n m kc n' : ℤ} {x : Vec d}
          (omega : Cutoff.CutoffSample d)
          (uglob hdat : H1Function (openCubeSet (originCube d m)))
          {gsrc : Vec d → Vec d}
          {Khol Kd CB CBc Cdel Cosc CdM C1 delta Cest : ℝ} {B : ℕ},
          m ≤ m0 → n' ≤ m - 1 → n + 1 ≤ n' - 2 → n ≤ m →
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
          RootClauseBTopPayload M L Khol Kd CB CBc Cdel Cosc CdM alpha n m kc n' x
            omega uglob gsrc →
          rootClauseBPrefactor d Cch (rootClauseBCaccUniform Cc CBc)
              Cosc CBc CB (rootClauseBTopCtr d Kd)
              (edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS) CdM ≤
            Cest →
          (offGridCentre n x ∈ openCubeSet (originCube d (m - 1)) →
            Real.sqrt M.nu *
                Support.normalizedL2On
                  (truncatedWindow (offGridCentre n x) m (n + 1))
                  (fun y => Real.sqrt (vecNormSq (uglob.grad y)))
              ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
                (Real.sqrt M.nu *
                    Support.normalizedL2On (openCubeSet (originCube d m))
                      (fun y => Real.sqrt (vecNormSq (uglob.grad y))) +
                  Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                    Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol)) := by
  obtain ⟨Cch, Cc, hCch, hCc, hmain⟩ := rootClauseB_display_interior_freeCoarse d
  refine ⟨Cch, Cc, hCch, hCc, ?_⟩
  intro M m0 Ecap hS hgamma L alpha n m kc n' x omega uglob hdat gsrc Khol Kd CB CBc Cdel
    Cosc CdM C1 delta Cest B hmm0 hn' hcore hnm hn'kc hkc hgapTop hsol hgL2 hgW hKhol hKd
    hCB hCBc hCdel hCosc hCdM hC1 halpha0 halpha1 hdelta hgap hbudget hpay hCest hzin
  refine hmain M m0 Ecap hS hgamma L omega uglob hdat hzin hmm0 hn' hcore hnm hn'kc hkc
    hgapTop hsol hgL2 hgW hKhol hKd hCB hCBc hCdel hCosc hCdM hC1 halpha0 halpha1 hdelta
    hgap hbudget hpay.caps hpay.capsCacc hpay.dataB hpay.dataM hpay.osc ?_
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M (n' + 1) : ℝ) :=
    (Annealed.sigmaBar M (n' + 1)).2
  have hcacc := stepSevenCaccConst_le_uniform (k := n') hCc hsigma hpay.capsCacc
  have hCtr : (0 : ℝ) ≤ rootClauseBTopCtr d Kd := rootClauseBTopCtr_nonneg d Kd
  have hCWG : (0 : ℝ) ≤ edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS :=
    mul_nonneg (edFinalDataOscW_nonneg hgamma hCdel) (stepFourGagliardoConst_nonneg d _)
  exact le_trans (rootClauseBPrefactor_mono_ccacc d hCch.le hCosc hCB hCtr hCWG hCdM
    hcacc) hCest

/-! ## 3. The three produced fields -/

/-- **`dataB` at the re-cut coarse cube, produced.**

`RootPayloadDataB.besovTranslated_neg_le_holder` at `j = k_c` followed by
`3^{k_c/2} ≤ 3^{m/2}` — the same single inequality used at `j = m-1`. -/
theorem rootClauseB_dataB_free [NeZero d] {m kc : ℤ} {z : Vec d}
    {gsrc : Vec d → Vec d} {Khol : ℝ}
    (hz : z ∈ openCubeSet (originCube d (m - 1))) (hkc : kc ≤ m - 1)
    (hKhol : 0 ≤ Khol)
    (hgHol : Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
      (1 / 2) Khol gsrc)
    (hgL2 : MemLp gsrc 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
    (hgW : MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m)))) :
    scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d kc)
        stepSevenCgS (fun y => -gsrc (y + z)) ≤
      rootClauseBDataBConst d * edFinalDataOscG Khol m := by
  have hmain := besovTranslated_neg_le_holder (m := m) (j := kc) hz hkc hKhol hgHol
    hgL2 hgW
  refine le_trans hmain ?_
  rw [edFinalDataOscG]
  have hcast : (kc : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : kc ≤ m)
  have hmono : Real.rpow (3 : ℝ) ((kc : ℝ) / 2) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hcast])
  have hstep : Real.rpow (3 : ℝ) ((kc : ℝ) / 2) * Khol ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol :=
    mul_le_mul_of_nonneg_right hmono hKhol
  exact mul_le_mul_of_nonneg_left hstep (rootClauseBDataBConst_nonneg d)

end

end Algsuperdiff.Section4.Provider.Regularity
