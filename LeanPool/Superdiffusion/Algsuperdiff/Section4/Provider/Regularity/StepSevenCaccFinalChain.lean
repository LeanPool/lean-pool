/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccFinalDisplay
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenLambdaChain

/-!
# StepSevenCaccFinalChain

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

/-! ## 1. The Step-7 end chain with `hgrad` discharged -/

/-- ** gap 2, closed on the interior branch: the Step-7 end chain with `hgrad`
GONE.**

`StepSevenLambdaChain.exists_stepSevenEnd_chain_of_caps` with its one surviving
conditional input replaced by the produced display
`StepSevenCaccFinalDisplay.exists_stepSevenGradientWithShom_interior_of_caps`.
Every other binder of the parent chain is carried verbatim; the new binders are
the pinned Caccioppoli's own (equation, forcing regularity, the clause-(B)
record at the good scale), the printed interior gate, the Step-7c scalar
budget, and `hosc`. -/
theorem exists_stepSevenEnd_chain_interior (d : ℕ) [NeZero d] :
    ∃ Cch Cc : ℝ, 0 < Cch ∧ 0 < Cc ∧
      ∀ (M : ABKModel d) (L : ℤ) {alpha : ℝ} {n m k n' mf : ℤ} (Qf : TriadicCube d)
        {a : CoeffFamily d} {g gcacc : Vec d → Vec d} {z c : Vec d}
        (uglob : H1Function (openCubeSet (originCube d m)))
        (v : H1Function (Ch02.cubeDomain (originCube d n') : Set (Vec d)))
        (omega : Cutoff.CutoffSample d)
        (u : ForcedCubeSolution (originCube d k) a g)
        {Ccmp Kg Kd Ks Ctr CB CBc sigma sigmac shomM
          gradM dataG W G H C1 delta Cosc : ℝ} {B : ℕ},
        (∀ y, u.toH1.toFun y = uglob.toFun (y + c)) →
        z ∈ openCubeSet (originCube d m) → k ≤ m →
        truncatedWindow z m k ⊆ (fun y => c + y) '' openCubeSet (originCube d k) →
        IntegrableOn uglob.toFun (truncatedWindow z m k) →
        IntegrableOn (fun x => uglob.toFun x ^ 2) (truncatedWindow z m k) →
        IntegrableOn uglob.toFun ((fun y => c + y) '' openCubeSet (originCube d k)) →
        IntegrableOn (fun x => uglob.toFun x ^ 2)
          ((fun y => c + y) '' openCubeSet (originCube d k)) →
        IntegrableOn
          (fun x => (uglob.toFun x - volumeAverage ((fun y => c + y) ''
            openCubeSet (originCube d k)) uglob.toFun) ^ 2)
          ((fun y => c + y) '' openCubeSet (originCube d k)) →
        0 ≤ CB → 0 ≤ Ks → 0 ≤ Ccmp → 0 < sigma → 0 < shomM →
        0 ≤ gradM → 0 ≤ dataG → 0 ≤ W → 0 ≤ G → 0 ≤ H →
        ForceBesovRegularity (originCube d k) stepSevenCgS g →
        StepSevenLambdaCaps (originCube d (k + 1)) a sigma CB →
        forcedSolutionEnergyNorm (originCube d k) a u ≤ Kg * gradM →
        scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k) stepSevenCgS g ≤
          Kd * dataG →
        sigma⁻¹ ≤ Ks * shomM⁻¹ →
        Real.sqrt Ks * Kg ≤ Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) →
        Ks * Kd ≤ Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) →
        sigmac ≤ Ccmp * shomM →
        (∀ y, v.toFun y = uglob.toFun (y + z)) →
        (∀ y, v.grad y = uglob.grad (y + z)) →
        z ∈ openCubeSet (originCube d (m - 1)) → n' ≤ m - 1 → n + 1 ≤ n' - 2 →
        IsForcedEquation (originCube d n')
          (Support.fluxCorrectedCoeffFamily M L mf Qf
            (Cutoff.translateCutoffSample z omega)) v gcacc →
        ForceBesovRegularity (originCube d n') stepOneS gcacc →
        2 * (d : ℝ) + 2 ≤ C1 → 0 ≤ alpha → alpha ≤ 1 → n ≤ m →
        delta ≤ C1⁻¹ * (1 - alpha) → n' - n ≤ (B : ℤ) + 6 →
        (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1) →
        0 ≤ Cosc → 0 ≤ CBc →
        StepSevenLambdaCaps (originCube d (n' + 1))
          (Support.fluxCorrectedCoeffFamily M L mf Qf
            (Cutoff.translateCutoffSample z omega)) sigmac CBc →
        ((3 : ℝ) ^ (-n') *
            normalizedL2On (truncatedWindow z m n')
              (fun x => uglob.toFun x -
                volumeAverage (truncatedWindow z m n') uglob.toFun) ≤
          Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
              ((cubeScaleFactor (originCube d k))⁻¹ *
                normalizedL2On (truncatedWindow z m k)
                  (fun x => uglob.toFun x -
                    volumeAverage (truncatedWindow z m k) uglob.toFun)) +
            Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
              (W * (shomM⁻¹ * G + H))) →
          stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (n + 1)) uglob.grad ≤
            (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
                  stepSevenCaccConst Cc (originCube d n')
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega)) *
                  (Cosc * Real.sqrt (256 / 63 * CBc) + 1)) * Real.sqrt Ccmp *
                (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
                  stepSevenBridgeConst stepSevenCgS *
                  (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) * Ctr) *
                Real.rpow (3 : ℝ) (stepSixExponent alpha n m) *
                (gradM + Real.sqrt shomM⁻¹ * dataG) +
              (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
                  stepSevenCaccConst Cc (originCube d n')
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega)) *
                  (Cosc * Real.sqrt (256 / 63 * CBc) + 1)) *
                Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
                (Real.sqrt Ccmp *
                  (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) +
                  stepSevenCaccDataM (originCube d n')
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega)) gcacc) := by
  obtain ⟨Cchain, hCchainPos, hchain⟩ := exists_stepSevenEnd_chain_of_caps d
  obtain ⟨Cd, hCdPos, hdisp⟩ := exists_stepSevenGradientWithShom_interior_of_caps d
  refine ⟨Cchain, Cd, hCchainPos, hCdPos, ?_⟩
  intro M L alpha n m k n' mf Qf a g gcacc z c uglob v omega u Ccmp Kg Kd Ks Ctr CB CBc
    sigma sigmac shomM gradM dataG W G H C1 delta Cosc B
    hv hz hkm hST hwS hwS2 hwT hwT2 hint hCB hKs hCcmp hsigma hshomM hgradM hdataG
    hW hG hH hforce hcaps hgradE hdataB htrShom hKgb hKdb hcomp
    hval hgradv hzin hn' hcore heq hforcec hC1 halpha0 halpha1 hnm hdelta hgap
    hbudget hCosc hCBc hcapsc hosc
  have hoscHi : (0 : ℝ) ≤ (cubeScaleFactor (originCube d k))⁻¹ *
      normalizedL2On (truncatedWindow z m k)
        (fun x => uglob.toFun x - volumeAverage (truncatedWindow z m k) uglob.toFun) := by
    have hsc : (0 : ℝ) ≤ (cubeScaleFactor (originCube d k))⁻¹ := by
      rw [cubeScaleFactor]
      exact inv_nonneg.mpr (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    exact mul_nonneg hsc (normalizedL2On_nonneg _ _)
  have hdataOsc : (0 : ℝ) ≤ W * (shomM⁻¹ * G + H) :=
    mul_nonneg hW (add_nonneg (mul_nonneg (inv_nonneg.mpr hshomM.le) hG) hH)
  have hgrad := hdisp M L mf m n n' Qf omega uglob v hval hgradv hzin hn' hcore heq
    hforcec hC1 halpha0 halpha1 hnm hdelta hgap hbudget hCosc hCBc hoscHi hdataOsc
    hcapsc hosc
  have hCg : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
      stepSevenCaccConst Cd (originCube d n')
        (Support.fluxCorrectedCoeffFamily M L mf Qf
          (Cutoff.translateCutoffSample z omega)) *
      (Cosc * Real.sqrt (256 / 63 * CBc) + 1) := by
    have h1 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have h2 : (0 : ℝ) ≤ stepSevenCaccConst Cd (originCube d n')
        (Support.fluxCorrectedCoeffFamily M L mf Qf
          (Cutoff.translateCutoffSample z omega)) := stepSevenCaccConst_nonneg _ _ _
    have h3 : (0 : ℝ) ≤ Cosc * Real.sqrt (256 / 63 * CBc) + 1 := by
      have h4 := mul_nonneg hCosc (Real.sqrt_nonneg (256 / 63 * CBc))
      linarith only [h4]
    exact mul_nonneg (mul_nonneg h1 h2) h3
  exact hchain u hv hz hkm hST hwS hwS2 hwT hwT2 hint hCg hCB hKs hCcmp hsigma hshomM
    hgradM hdataG hW hG hH hforce hcaps hgradE hdataB htrShom hKgb hKdb hcomp hgrad

/-! ## 2. The same, entered at `t.regularity`'s own Dirichlet datum -/

/-- **The interior Step-7 end chain from the Dirichlet datum alone.**

`exists_stepSevenEnd_chain_interior` with the Caccioppoli side entered at
`t.regularity` Step 3's own datum: the transported solution `v`, its two frame
identities and its forced equation are BUILT
(`StepSevenCaccFinalInterior.exists_stepSevenCaccInteriorSolution`), and the
forcing binder at the good-scale cube is produced from the §4.4 `H^{1/4}` datum
on `□_m` through the Gagliardo ↔ Besov bridge (residue,
`StepSevenCaccFinalInterior.forceBesovRegularity_stepSevenCacc_interior`) — the
two `MemLp` hypotheses below are literally the two forcing binders's Step-6
interior endpoint. -/
theorem exists_stepSevenEnd_chain_interior_of_dirichlet (d : ℕ) [NeZero d] :
    ∃ Cch Cc : ℝ, 0 < Cch ∧ 0 < Cc ∧
      ∀ (M : ABKModel d) (L : ℤ) {alpha : ℝ} {n m k n' mf : ℤ} (Qf : TriadicCube d)
        {a : CoeffFamily d} {g gsrc : Vec d → Vec d} {z c : Vec d}
        (uglob hdat : H1Function (openCubeSet (originCube d m)))
        (omega : Cutoff.CutoffSample d)
        (u : ForcedCubeSolution (originCube d k) a g)
        {Ccmp Kg Kd Ks Ctr CB CBc sigma sigmac shomM
          gradM dataG W G H C1 delta Cosc : ℝ} {B : ℕ},
        (∀ y, u.toH1.toFun y = uglob.toFun (y + c)) →
        z ∈ openCubeSet (originCube d m) → k ≤ m →
        truncatedWindow z m k ⊆ (fun y => c + y) '' openCubeSet (originCube d k) →
        IntegrableOn uglob.toFun (truncatedWindow z m k) →
        IntegrableOn (fun x => uglob.toFun x ^ 2) (truncatedWindow z m k) →
        IntegrableOn uglob.toFun ((fun y => c + y) '' openCubeSet (originCube d k)) →
        IntegrableOn (fun x => uglob.toFun x ^ 2)
          ((fun y => c + y) '' openCubeSet (originCube d k)) →
        IntegrableOn
          (fun x => (uglob.toFun x - volumeAverage ((fun y => c + y) ''
            openCubeSet (originCube d k)) uglob.toFun) ^ 2)
          ((fun y => c + y) '' openCubeSet (originCube d k)) →
        0 ≤ CB → 0 ≤ Ks → 0 ≤ Ccmp → 0 < sigma → 0 < shomM →
        0 ≤ gradM → 0 ≤ dataG → 0 ≤ W → 0 ≤ G → 0 ≤ H →
        ForceBesovRegularity (originCube d k) stepSevenCgS g →
        StepSevenLambdaCaps (originCube d (k + 1)) a sigma CB →
        forcedSolutionEnergyNorm (originCube d k) a u ≤ Kg * gradM →
        scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k) stepSevenCgS g ≤
          Kd * dataG →
        sigma⁻¹ ≤ Ks * shomM⁻¹ →
        Real.sqrt Ks * Kg ≤ Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) →
        Ks * Kd ≤ Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) →
        sigmac ≤ Ccmp * shomM →
        z ∈ openCubeSet (originCube d (m - 1)) → n' ≤ m - 1 → n + 1 ≤ n' - 2 →
        Support.IsDirichletSolutionOn
          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
          (originCube d m) uglob hdat gsrc →
        MemLp gsrc 2
          (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
        MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
          (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
        2 * (d : ℝ) + 2 ≤ C1 → 0 ≤ alpha → alpha ≤ 1 → n ≤ m →
        delta ≤ C1⁻¹ * (1 - alpha) → n' - n ≤ (B : ℤ) + 6 →
        (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1) →
        0 ≤ Cosc → 0 ≤ CBc →
        StepSevenLambdaCaps (originCube d (n' + 1))
          (Support.fluxCorrectedCoeffFamily M L mf Qf
            (Cutoff.translateCutoffSample z omega)) sigmac CBc →
        ((3 : ℝ) ^ (-n') *
            normalizedL2On (truncatedWindow z m n')
              (fun x => uglob.toFun x -
                volumeAverage (truncatedWindow z m n') uglob.toFun) ≤
          Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
              ((cubeScaleFactor (originCube d k))⁻¹ *
                normalizedL2On (truncatedWindow z m k)
                  (fun x => uglob.toFun x -
                    volumeAverage (truncatedWindow z m k) uglob.toFun)) +
            Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
              (W * (shomM⁻¹ * G + H))) →
          stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (n + 1)) uglob.grad ≤
            (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
                  stepSevenCaccConst Cc (originCube d n')
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega)) *
                  (Cosc * Real.sqrt (256 / 63 * CBc) + 1)) * Real.sqrt Ccmp *
                (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
                  stepSevenBridgeConst stepSevenCgS *
                  (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) * Ctr) *
                Real.rpow (3 : ℝ) (stepSixExponent alpha n m) *
                (gradM + Real.sqrt shomM⁻¹ * dataG) +
              (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
                  stepSevenCaccConst Cc (originCube d n')
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega)) *
                  (Cosc * Real.sqrt (256 / 63 * CBc) + 1)) *
                Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
                (Real.sqrt Ccmp *
                  (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) +
                  stepSevenCaccDataM (originCube d n')
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega))
                    (fun x => -gsrc (x + z))) := by
  obtain ⟨Cch, Cc, hCch, hCc, hmain⟩ := exists_stepSevenEnd_chain_interior d
  refine ⟨Cch, Cc, hCch, hCc, ?_⟩
  intro M L alpha n m k n' mf Qf a g gsrc z c uglob hdat omega u Ccmp Kg Kd Ks Ctr CB CBc
    sigma sigmac shomM gradM dataG W G H C1 delta Cosc B
    hv hz hkm hST hwS hwS2 hwT hwT2 hint hCB hKs hCcmp hsigma hshomM hgradM hdataG
    hW hG hH hforce hcaps hgradE hdataB htrShom hKgb hKdb hcomp
    hzin hn' hcore hsol hgL2 hgW hC1 halpha0 halpha1 hnm hdelta hgap
    hbudget hCosc hCBc hcapsc hosc
  obtain ⟨v, hval, hgradv, heq⟩ :=
    exists_stepSevenCaccInteriorSolution (n' := n') (mf := mf) M L Qf omega hzin hn' hsol
  have hforcec := forceBesovRegularity_stepSevenCacc_interior (n' := n') hzin hn' hgL2 hgW
  exact hmain M L Qf uglob v omega u hv hz hkm hST hwS hwS2 hwT hwT2 hint hCB hKs hCcmp
    hsigma hshomM hgradM hdataG hW hG hH hforce hcaps hgradE hdataB htrShom hKgb hKdb
    hcomp hval hgradv hzin hn' hcore heq hforcec hC1 halpha0 halpha1 hnm hdelta hgap
    hbudget hCosc hCBc hcapsc hosc

end

end Algsuperdiff.Section4.Provider.Regularity
