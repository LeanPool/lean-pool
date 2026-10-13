/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBDichotomyDisplay
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenFlushMerged
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenFlushHgradSlot
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenClampLambdaAtCentre
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBBoundaryOscFloor
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBCloseAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBCloseChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBFinalArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBGateBoundaryC1
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBGateGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenLambdaChain

/-!
# RootClauseBWellPlacedFloor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# fine-scale dichotomy executed

Nothing here imports any of them, nothing here claims an anchor, and nothing
here is a frozen statement.

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

/-! ## 1. Prefactor monotonicity -/

private abbrev rootClauseBWellPlacedFloor_comparisonBounds3_statement : Prop :=
    ∀ (d : ℕ) (cstar Crg : ℝ) (hCrg : (0 : ℝ) < Crg) (C Ccap Cann Citer : ℝ) (kb : ℕ) (hC : (0 : ℝ) < C)
      (hCcap : (0 : ℝ) < Ccap) (Ccaps : ℝ) (hCcaps : (0 : ℝ) < Ccaps) (Clam : ℝ) (hClam : (0 : ℝ) < Clam) (Cflu : ℝ)
      (hCflu : (0 : ℝ) < Cflu) (CannP : ℝ) (hCannP : (0 : ℝ) < CannP) (Cind : ℝ),
      let Cmax : ℝ := max (max (max C Ccap) (max Ccaps Clam)) (max (max Cflu CannP) (1 : ℝ));
      ∀ (Cedos : ℝ),
        let C1 : ℝ := stepOneC1 d Cedos (1 : ℝ) Citer (kb + (1 : ℕ));
        ∀ (gamma0 : ℝ)
          (hfacts :
            ∀ (M : ABKModel d), Disorder.cstar M = cstar → M.gamma ≤ gamma0 → RootClauseBGammaFacts M Cmax Cann Cind C1 Crg)
          (M : ABKModel d) (hcs : Disorder.cstar M = cstar) (hgammale : M.gamma ≤ min gamma0 ((Crg / (2 : ℝ)) ^ (2 : ℕ)))
          (alpha : ℝ) (halpha0 : (0 : ℝ) < alpha) (halpha : alpha ≤ (1 : ℝ) - Crg * √M.gamma),
          M.gamma ≤ (Crg / (2 : ℝ)) ^ (2 : ℕ) ∧
            RootClauseBGammaFacts M Cmax Cann Cind C1 Crg ∧
              (0 : ℝ) < M.gamma ∧
                alpha < (1 : ℝ) ∧
                  M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) ∧
                    M.gamma ≤ Ccap⁻¹ * Disorder.cstar M ^ (10 : ℕ) ∧
                      M.gamma ≤ Ccaps⁻¹ * Disorder.cstar M ^ (10 : ℕ) ∧
                        M.gamma ≤ Clam⁻¹ * Disorder.cstar M ^ (10 : ℕ) ∧
                          M.gamma ≤ Cflu⁻¹ * Disorder.cstar M ^ (10 : ℕ) ∧
                            M.gamma ≤ CannP⁻¹ * Disorder.cstar M ^ (10 : ℕ) ∧
                              M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                                stepOneSEighth.rpow (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                                  stepOneEp (stepOneDelta C1 alpha)

private abbrev rootClauseB_energyWindowBound_statement : Prop :=
    ∀ (d : ℕ) [inst : NeZero d] (Crg C Ccap Cann Cb Citer Cosc : ℝ) (kb : ℕ)
      (hCosc : (0 : ℝ) ≤ Cosc) (Ccaps Clam Klam : ℝ) (hKlam : (0 : ℝ) < Klam) (Cflu Afl K1 K2 : ℝ) (hK1 : (0 : ℝ) < K1)
      (hK2 : (0 : ℝ) ≤ K2) (CannP Cind Cch : ℝ) (hCch : (0 : ℝ) < Cch)
      (hend :
        ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : { E : ℝ // (1 : ℝ) ≤ E }),
          Frozen.Section3.inductionState M m0 Ecap →
            M.gamma < (1 / 2 : ℝ) →
              ∀ (L : ℤ) {alpha : ℝ} {n m kc np : ℤ} {z : Vec d} (omega : Cutoff.CutoffSample d)
                (uglob hdat : H1Function (openCubeSet (originCube d m))) {gsrc : Vec d → Vec d}
                {Khol Kh Kd CB Cg Cdel CdM CWH C1 delta Cest dataH dataM : ℝ} {B : ℕ},
                z ∈ openCubeSet (originCube d m) →
                  m ≤ m0 →
                    n ≤ m →
                      kc ≤ m - (1 : ℤ) →
                        np + (1 : ℤ) ≤ m →
                          m - (kc + (1 : ℤ)) ≤ (↑B : ℤ) + (1 : ℤ) →
                            IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m)
                                uglob hdat gsrc →
                              MemLp gsrc (2 : ENNReal) (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
                                MemLp (Gagliardo.gagliardoKernel stepOneS (2 : ENNReal) gsrc) (2 : ENNReal)
                                    (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                                  (0 : ℝ) ≤ Khol →
                                    (0 : ℝ) ≤ Kh →
                                      (0 : ℝ) ≤ Kd →
                                        (0 : ℝ) ≤ CB →
                                          (0 : ℝ) ≤ Cg →
                                            (0 : ℝ) ≤ Cdel →
                                              (0 : ℝ) ≤ CdM →
                                                (0 : ℝ) ≤ CWH →
                                                  (0 : ℝ) ≤ dataH →
                                                    (0 : ℝ) ≤ dataM →
                                                      (2 : ℝ) * (↑d : ℝ) + (2 : ℝ) ≤ C1 →
                                                        (0 : ℝ) ≤ alpha →
                                                          alpha ≤ (1 : ℝ) →
                                                            delta ≤ C1⁻¹ * ((1 : ℝ) - alpha) →
                                                              (↑B : ℝ) ≤ delta * ((↑(m - n).toNat : ℝ) + (1 : ℝ)) →
                                                                stepSevenCgLamInv (originCube d kc)
                                                                      (parentRebasedFamily M L (kc + (1 : ℤ))
                                                                        (wellPlacedCentre z m kc) z omega)
                                                                      stepSevenCgS ≤
                                                                    CB * (↑(Annealed.sigmaBar M (kc + (1 : ℤ))) : ℝ)⁻¹ →
                                                                  (scaleNormalizedPositiveBesovVectorSeminormTwo
                                                                        (originCube d kc) stepSevenCgS fun (x : Vec d) =>
                                                                        -gsrc (x + wellPlacedCentre z m kc)) ≤
                                                                      Kd * edFinalDataOscG Khol m →
                                                                    dataM ≤
                                                                        CdM *
                                                                          (√(↑(Annealed.sigmaBar M m) : ℝ)⁻¹ *
                                                                            edFinalDataOscG Khol m) →
                                                                      dataH ≤ CWH * edFinalDataOscG Kh m →
                                                                        stepSevenNuGradNorm M.nu
                                                                              (truncatedWindow z m (n + (1 : ℤ)))
                                                                              uglob.grad ≤
                                                                            Cg *
                                                                                    √(↑(Annealed.sigmaBar M
                                                                                            (np + (1 : ℤ))) :
                                                                                        ℝ) *
                                                                                  Real.rpow (3 : ℝ)
                                                                                    ((3 / 4 : ℝ) *
                                                                                      stepSixExponent alpha n m) *
                                                                                ((cubeScaleFactor (originCube d kc))⁻¹ *
                                                                                  normalizedL2On (truncatedWindow z m kc)
                                                                                    fun (x : Vec d) =>
                                                                                    uglob.toFun x -
                                                                                      volumeAverage (truncatedWindow z m kc)
                                                                                        uglob.toFun) +
                                                                              Cg *
                                                                                  Real.rpow (3 : ℝ)
                                                                                    ((3 / 4 : ℝ) *
                                                                                      stepSixExponent alpha n m) *
                                                                                (√(↑(Annealed.sigmaBar M (np + (1 : ℤ))) :
                                                                                        ℝ) *
                                                                                    ((1 : ℝ) *
                                                                                      ((↑(Annealed.sigmaBar M m) : ℝ)⁻¹ *
                                                                                          ((↑(Annealed.sigmaBar M m) : ℝ) *
                                                                                            edFinalDataG M Cdel
                                                                                              (Khol *
                                                                                                stepFourGagliardoConst d
                                                                                                  stepOneS)
                                                                                              m) +
                                                                                        dataH)) +
                                                                                  dataM) →
                                                                          rootClauseBWellPlacedPrefactor d Cch Cg CB
                                                                                (rootClauseBTopCtr d Kd)
                                                                                (edFinalDataOscW M Cdel *
                                                                                  stepFourGagliardoConst d stepOneS)
                                                                                CWH CdM ≤
                                                                              Cest →
                                                                            (√M.nu *
                                                                                normalizedL2On
                                                                                  (truncatedWindow z m (n + (1 : ℤ)))
                                                                                  fun (y : Vec d) =>
                                                                                  √(vecNormSq (uglob.grad y))) ≤
                                                                              Cest *
                                                                                  Real.rpow (3 : ℝ)
                                                                                    (((1 : ℝ) - alpha) *
                                                                                      ((↑m : ℝ) - (↑n : ℝ))) *
                                                                                ((√M.nu *
                                                                                      normalizedL2On
                                                                                        (openCubeSet (originCube d m))
                                                                                        fun (y : Vec d) =>
                                                                                        √(vecNormSq (uglob.grad y))) +
                                                                                    √(↑(Annealed.sigmaBar M m) : ℝ)⁻¹ *
                                                                                        Real.rpow (3 : ℝ)
                                                                                          ((↑m : ℝ) / (2 : ℝ)) *
                                                                                      Khol +
                                                                                  √(↑(Annealed.sigmaBar M m) : ℝ) *
                                                                                      Real.rpow (3 : ℝ)
                                                                                        ((↑m : ℝ) / (2 : ℝ)) *
                                                                                    Kh))
      (CdispC : ℝ) (hCbd : (0 : ℝ) ≤ edBoundaryCbd d Cb C kb) (hCWH : (0 : ℝ) ≤ boundaryCWH d Cb C kb) (hd1 : (1 : ℕ) ≤ d),
      let CBu : ℝ := rootClauseBCapsUniform d Ccaps;
      let CWGu : ℝ := rootClauseBOscWUniform (edBoundaryCbd d Cb C kb) * stepFourGagliardoConst d stepOneS;
      let Ctru : ℝ := rootClauseBTopCtr d (rootClauseBDataBConst d);
      ∀ (hCtru0 : (0 : ℝ) ≤ Ctru),
        let PG : ℝ :=
          rootClauseBWellPlacedPrefactor d Cch (rootClauseBCg d (rootClauseBCaccUniform CdispC CBu) Cosc CBu) Klam Ctru CWGu
            (boundaryCWH d Cb C kb) (rootClauseBDataMConst d CBu);
        let PF : ℝ :=
          rootClauseBWellPlacedPrefactor d Cch (stepSevenFlushCg d K1 K2 Cosc) Klam Ctru CWGu
            (boundaryCWH d Cb C kb + (1 : ℝ)) (1 : ℝ);
        ∀ (Cedos : ℝ),
          let C1 : ℝ := stepOneC1 d Cedos (1 : ℝ) Citer (kb + (1 : ℕ));
          ∀ (M : ABKModel d) (alpha : ℝ) (halpha0 : (0 : ℝ) < alpha) (m : ℤ)
            (hfact :
              RootClauseBGammaFacts M (max (max (max C Ccap) (max Ccaps Clam)) (max (max Cflu CannP) (1 : ℝ))) Cann Cind
                (stepOneC1 d Cedos (1 : ℝ) Citer (kb + (1 : ℕ))) Crg)
            (halpha1 : alpha < (1 : ℝ)) (Ecap : { E : ℝ // (1 : ℝ) ≤ E })
            (hstate : ∀ (m : ℤ), Frozen.Section3.inductionState M m Ecap) (h2gamma : (2 : ℝ) * M.gamma ≤ (1 : ℝ) - alpha)
            (omega : Cutoff.CutoffSample d)
            (hFlush :
              ∀ (L m n nl : ℤ) (v : Fin d → ℤ) (i : Fin d) (sigma : ℝ),
                sigma = (1 : ℝ) ∨ sigma = (-1 : ℝ) →
                  m ≤ L →
                    n + (3 : ℤ) ≤ m →
                      triadicLatticePoint nl v ∈ openCubeSet (originCube d m) →
                        wellPlacedHalfGap m (n + (2 : ℤ)) < sigma * triadicLatticePoint nl v i →
                          omega ∈
                              Frozen.Section4.goodEventAt M (cgEllipLowerConstant d) (n + (3 : ℤ))
                                (triadicLatticePoint nl v)
                                ⟨stepOneS / (8 : ℝ),
                                  (by
                                    solve
                                    | norm_num [Algsuperdiff.Section4.Provider.Regularity.stepOneS]
                                    | positivity
                                    | assumption
                                    | omega
                                    | linarith)⟩
                                (1 / 2 : ℝ) →
                            Afl *
                                  fluxCorrectedErrorRepresentative M L (n + (3 : ℤ))
                                    ⟨stepOneS / (8 : ℝ),
                                      (by
                                        solve
                                        | norm_num [Algsuperdiff.Section4.Provider.Regularity.stepOneS]
                                        | positivity
                                        | assumption
                                        | omega
                                        | linarith)⟩
                                    (Cutoff.translateCutoffSample (triadicLatticePoint nl v) omega) ≤
                                stepOneS ^ (4 : ℕ) →
                              StepSevenFlushBound M K1 K2 L m n (triadicLatticePoint nl v) omega)
            (hPin :
              ∀ (j nl : ℤ) (v : Fin d → ℤ),
                omega ∈
                    stepThreeGoodEvent M (stepOneDelta (stepOneC1 d Cedos (1 : ℝ) Citer (kb + (1 : ℕ))) alpha) j
                      (triadicLatticePoint nl v) →
                  ∀ (L : ℤ),
                    j ≤ L →
                      Afl *
                          fluxCorrectedErrorRepresentative M L j
                            ⟨stepOneS / (8 : ℝ),
                              (by
                                solve
                                | norm_num [Algsuperdiff.Section4.Provider.Regularity.stepOneS]
                                | positivity
                                | assumption
                                | omega
                                | linarith)⟩
                            (Cutoff.translateCutoffSample (triadicLatticePoint nl v) omega) ≤
                        stepOneS ^ (4 : ℕ))
            (n L : ℤ) (hnm : n ≤ m) (hmL : m ≤ L) (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
            (Kg Kh : ℝ)
            (hsol : IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m) u h g)
            (hgHol : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2 : ℝ) Kg g)
            (hhHol : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2 : ℝ) Kh h.grad)
            (hsup : ∀ y ∈ openCubeSet (originCube d m), ‖h.grad y‖ ≤ Real.rpow (3 : ℝ) ((↑m : ℝ) / (2 : ℝ)) * Kh)
            (x : Vec d) (hKg : (0 : ℝ) ≤ Kg) (hKh : (0 : ℝ) ≤ Kh)
            (hzm : triadicLatticePoint n (offGridLatticeIndex n x) ∈ openCubeSet (originCube d m))
            (hgL2 : MemLp g (2 : ENNReal) (normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
            (hgW :
              MemLp (Gagliardo.gagliardoKernel stepOneS (2 : ENNReal) g) (2 : ENNReal)
                (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))))
            (hhW :
              MemLp (Gagliardo.gagliardoKernel stepOneS (2 : ENNReal) h.grad) (2 : ENNReal)
                (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))))
            (hoscfun :
              ∀ (n' kc : ℤ),
                n ≤ n' →
                  n' ≤ kc →
                    kc ≤ m →
                      ((3 : ℝ) ^ (-n') *
                          normalizedL2On (truncatedWindow (triadicLatticePoint n (offGridLatticeIndex n x)) m n')
                            fun (y : Vec d) =>
                            u.toFun y -
                              volumeAverage (truncatedWindow (triadicLatticePoint n (offGridLatticeIndex n x)) m n')
                                u.toFun) ≤
                        Cosc * Real.rpow (3 : ℝ) ((1 / 2 : ℝ) * stepSixExponent alpha n m) *
                            ((3 : ℝ) ^ (-kc) *
                              normalizedL2On (truncatedWindow (triadicLatticePoint n (offGridLatticeIndex n x)) m kc)
                                fun (y : Vec d) =>
                                u.toFun y -
                                  volumeAverage (truncatedWindow (triadicLatticePoint n (offGridLatticeIndex n x)) m kc)
                                    u.toFun) +
                          Cosc * Real.rpow (3 : ℝ) ((1 / 2 : ℝ) * stepSixExponent alpha n m) *
                            (edFinalDataG M (edBoundaryCbd d Cb C kb) (Kg * stepFourGagliardoConst d stepOneS) m +
                              edBoundaryDataHPrinted d Cb C kb Kh m))
            (kc : ℤ) (hkhi : kc + (1 : ℤ) ≤ m - (1 : ℤ)) (np : ℤ) (hjlo : n + (4 : ℤ) ≤ np + (1 : ℤ))
            (hgoodj :
              omega ∈
                stepThreeGoodEvent M (stepOneDelta C1 alpha) (np + (1 : ℤ))
                  (triadicLatticePoint n (offGridLatticeIndex n x))),
            let B : ℕ :=
              (stepThreeBadSet M (stepOneDelta C1 alpha) n m (triadicLatticePoint n (offGridLatticeIndex n x)) omega).card;
            ∀ (hcard : (↑B : ℝ) ≤ stepOneDelta C1 alpha * ((↑(m - n).toNat : ℝ) + (1 : ℝ)))
              (hgapHi : m - (kc + (1 : ℤ)) ≤ (↑B : ℤ) + (1 : ℤ)) (hgapLo : np + (1 : ℤ) - n ≤ (↑B : ℤ) + (4 : ℤ))
              (hgapStrict : np + (2 : ℤ) ≤ kc) (hδIoc : stepOneDelta C1 alpha ∈ Set.Ioc (0 : ℝ) (1 / 2 : ℝ))
              (hlamkc :
                stepSevenCgLamInv (originCube d kc)
                    (parentRebasedFamily M L (kc + (1 : ℤ))
                      (wellPlacedCentre (triadicLatticePoint n (offGridLatticeIndex n x)) m kc)
                      (triadicLatticePoint n (offGridLatticeIndex n x)) omega)
                    stepSevenCgS ≤
                  Klam * (↑(Annealed.sigmaBar M (kc + (1 : ℤ))) : ℝ)⁻¹)
              (hCWGle : edFinalDataOscW M (edBoundaryCbd d Cb C kb) * stepFourGagliardoConst d stepOneS ≤ CWGu)
              (hCWG0 : (0 : ℝ) ≤ edFinalDataOscW M (edBoundaryCbd d Cb C kb) * stepFourGagliardoConst d stepOneS)
              (hdataHP0 : (0 : ℝ) ≤ edBoundaryDataHPrinted d Cb C kb Kh m) (hC1dim : (2 : ℝ) * (↑d : ℝ) + (2 : ℝ) ≤ C1)
              (hdeltaEq : stepOneDelta C1 alpha ≤ C1⁻¹ * ((1 : ℝ) - alpha))
              (hoscHi0 :
                (0 : ℝ) ≤
                  (cubeScaleFactor (originCube d kc))⁻¹ *
                    normalizedL2On (truncatedWindow (triadicLatticePoint n (offGridLatticeIndex n x)) m kc)
                      fun (y : Vec d) =>
                      u.toFun y -
                        volumeAverage (truncatedWindow (triadicLatticePoint n (offGridLatticeIndex n x)) m kc) u.toFun)
              (hedG0 : (0 : ℝ) ≤ edFinalDataG M (edBoundaryCbd d Cb C kb) (Kg * stepFourGagliardoConst d stepOneS) m)
              (hgate :
                ¬(fun (y : Vec d) => triadicLatticePoint n (offGridLatticeIndex n x) + y) '' openCubeSet (originCube d np) ⊆
                    openCubeSet (originCube d m)),
              (√M.nu *
                  normalizedL2On (truncatedWindow (offGridCentre n x) m (n + (1 : ℤ))) fun (y : Vec d) =>
                    √(vecNormSq (u.grad y))) ≤
                max PG PF * Real.rpow (3 : ℝ) (((1 : ℝ) - alpha) * ((↑m : ℝ) - (↑n : ℝ))) *
                  ((√M.nu * normalizedL2On (openCubeSet (originCube d m)) fun (y : Vec d) => √(vecNormSq (u.grad y))) +
                      √(↑(Annealed.sigmaBar M m) : ℝ)⁻¹ * Real.rpow (3 : ℝ) ((↑m : ℝ) / (2 : ℝ)) * Kg +
                    √(↑(Annealed.sigmaBar M m) : ℝ) * Real.rpow (3 : ℝ) ((↑m : ℝ) / (2 : ℝ)) * Kh)

/-- The well-placed prefactor is monotone in its four data slots. -/
theorem rootClauseBWellPlacedPrefactor_mono (d : ℕ) [NeZero d]
    {Cch Cg Cg' CB Ctr CWG CWG' CWH CWH' CdM CdM' : ℝ}
    (hCch : 0 ≤ Cch) (hCg : 0 ≤ Cg) (hCB : 0 ≤ CB) (hCtr : 0 ≤ Ctr)
    (hCWG : 0 ≤ CWG) (hCWH : 0 ≤ CWH) (hCdM : 0 ≤ CdM)
    (hg : Cg ≤ Cg') (hwg : CWG ≤ CWG') (hwh : CWH ≤ CWH') (hdm : CdM ≤ CdM') :
    rootClauseBWellPlacedPrefactor d Cch Cg CB Ctr CWG CWH CdM ≤
      rootClauseBWellPlacedPrefactor d Cch Cg' CB Ctr CWG' CWH' CdM' := by
  have hX : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
      stepSevenBridgeConst stepSevenCgS * (Cch * 64 * (Real.sqrt CB + CB)) * Ctr := by
    have hbr : (0 : ℝ) ≤ Real.sqrt CB + CB := by
      have h5 := Real.sqrt_nonneg CB
      linarith only [h5, hCB]
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (stepSevenEmbeddingConst_nonneg d)) (stepSevenBridgeConst_nonneg _)) ?_) hCtr
    exact mul_nonneg (by linarith only [hCch]) hbr
  have hs4 : (0 : ℝ) ≤ Real.sqrt 4 := Real.sqrt_nonneg _
  have hCg' : 0 ≤ Cg' := le_trans hCg hg
  have h1 : Cg * Real.sqrt 4 *
      (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt CB + CB)) * Ctr) ≤
      Cg' * Real.sqrt 4 *
      (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt CB + CB)) * Ctr) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg hs4) hX
  have hY : Real.sqrt 4 * CWG + Real.sqrt 4 * CWH + CdM ≤
      Real.sqrt 4 * CWG' + Real.sqrt 4 * CWH' + CdM' := by
    have a1 := mul_le_mul_of_nonneg_left hwg hs4
    have a2 := mul_le_mul_of_nonneg_left hwh hs4
    linarith only [a1, a2, hdm]
  have hY0 : (0 : ℝ) ≤ Real.sqrt 4 * CWG + Real.sqrt 4 * CWH + CdM := by
    have a1 := mul_nonneg hs4 hCWG
    have a2 := mul_nonneg hs4 hCWH
    linarith only [a1, a2, hCdM]
  have h2 : Cg * (Real.sqrt 4 * CWG + Real.sqrt 4 * CWH + CdM) ≤
      Cg' * (Real.sqrt 4 * CWG' + Real.sqrt 4 * CWH' + CdM') :=
    mul_le_mul hg hY hY0 hCg'
  rw [rootClauseBWellPlacedPrefactor, rootClauseBWellPlacedPrefactor]
  linarith only [h1, h2]

/-- The gate branch's chain constant against its `ω`-free cap. -/
theorem gateBranchCg_le_uniform (d : ℕ) [NeZero d] {Cc sigma CBraw CBu Cosc : ℝ}
    {np : ℤ} {a : CoeffFamily d} (hCc : 0 < Cc) (hsigma : 0 < sigma)
    (hCosc : 0 ≤ Cosc) (hCBraw : 0 ≤ CBraw) (hle : CBraw ≤ CBu)
    (hcaps : StepSevenLambdaCaps (originCube d (np + 1)) a sigma CBraw) :
    Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
        stepSevenCaccConst Cc (originCube d np) a *
        (Cosc * Real.sqrt (256 / 63 * CBraw) + 1) ≤
      rootClauseBCg d (rootClauseBCaccUniform Cc CBu) Cosc CBu := by
  have hr0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) :=
    Real.rpow_nonneg (by norm_num) _
  have hcc := stepSevenCaccConst_le_uniform (k := np) hCc hsigma hcaps
  have hccU := rootClauseBCaccUniform_nonneg Cc CBraw
  have hbr : Cosc * Real.sqrt (256 / 63 * CBraw) + 1 ≤
      Cosc * Real.sqrt (256 / 63 * CBu) + 1 := by
    have hs := Real.sqrt_le_sqrt (by linarith only [hle] :
      256 / 63 * CBraw ≤ 256 / 63 * CBu)
    have := mul_le_mul_of_nonneg_left hs hCosc
    linarith only [this]
  have hbr0 : (0 : ℝ) ≤ Cosc * Real.sqrt (256 / 63 * CBraw) + 1 := by
    have := mul_nonneg hCosc (Real.sqrt_nonneg (256 / 63 * CBraw))
    linarith only [this]
  have hccm := rootClauseBCaccUniform_mono Cc hCBraw hle
  rw [rootClauseBCg]
  have h1 : Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
      stepSevenCaccConst Cc (originCube d np) a ≤
      Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
        rootClauseBCaccUniform Cc CBu :=
    mul_le_mul_of_nonneg_left (le_trans hcc hccm) hr0
  exact mul_le_mul h1 hbr hbr0
    (mul_nonneg hr0 (rootClauseBCaccUniform_nonneg Cc CBu))

/-! ## 2. The floor -/

private theorem rootClauseBWellPlacedFloor_comparisonBounds1 :
    ∀ (d : ℕ) [inst : NeZero d] (cstar Crg : ℝ) (hCrg : (0 : ℝ) < Crg) (C Ccap Cann Cb Cflo Citer Cosc : ℝ)
      (kb : ℕ)
      (hoscprod :
        ∀ (Cedos : ℝ),
          Cflo ≤ Cedos →
            ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : { E : ℝ // (1 : ℝ) ≤ E }),
              Frozen.Section3.inductionState M m0 Ecap →
                M.gamma < (1 / 2 : ℝ) →
                  M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
                    M.gamma ≤ Ccap⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
                      M.gamma ≤ Cann⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
                        M.gamma ≤ (1 / 256 : ℝ) →
                          ∀ (alpha : ℝ),
                            (0 : ℝ) < alpha →
                              alpha < (1 : ℝ) →
                                M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                                    stepOneSEighth.rpow (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                                      stepOneEp (stepOneDelta (stepOneC1 d Cedos (1 : ℝ) Citer (kb + (1 : ℕ))) alpha) →
                                  ∀ m ≤ m0,
                                    ∀ᵐ (omega :
                                      Cutoff.CutoffSample
                                        d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)),
                                      ∀ (L n : ℤ) (v : Fin d → ℤ),
                                        m ≤ L →
                                          (14 : ℤ) ≤ m - n →
                                            v ∈ latticeCubeSet d n m →
                                              RootWindowPayload M (stepOneC1 d Cedos (1 : ℝ) Citer (kb + (1 : ℕ))) alpha n m
                                                  omega →
                                                ∀ (uglob hdat : H1Function (openCubeSet (originCube d m)))
                                                  (gsrc : Vec d → Vec d) (Khol Kh : ℝ),
                                                  (0 : ℝ) ≤ Khol →
                                                    (0 : ℝ) ≤ Kh →
                                                      IsDirichletSolutionOn
                                                          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                                                          (originCube d m) uglob hdat gsrc →
                                                        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2 : ℝ)
                                                            Khol gsrc →
                                                          HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2 : ℝ)
                                                              Kh hdat.grad →
                                                            (∀ y ∈ openCubeSet (originCube d m),
                                                                ‖hdat.grad y‖ ≤
                                                                  Real.rpow (3 : ℝ) ((↑m : ℝ) / (2 : ℝ)) * Kh) →
                                                              HasGradientOn (openCubeSet (originCube d m)) hdat.toFun
                                                                  hdat.grad →
                                                                ∀ (n' kc : ℤ),
                                                                  n ≤ n' →
                                                                    n' ≤ kc →
                                                                      kc ≤ m →
                                                                        ((3 : ℝ) ^ (-n') *
                                                                            normalizedL2On
                                                                              (truncatedWindow (triadicLatticePoint n v) m
                                                                                n')
                                                                              fun (y : Vec d) =>
                                                                              uglob.toFun y -
                                                                                volumeAverage
                                                                                  (truncatedWindow (triadicLatticePoint n v)
                                                                                    m n')
                                                                                  uglob.toFun) ≤
                                                                          Cosc *
                                                                                Real.rpow (3 : ℝ)
                                                                                  ((1 / 2 : ℝ) *
                                                                                    stepSixExponent alpha n m) *
                                                                              ((3 : ℝ) ^ (-kc) *
                                                                                normalizedL2On
                                                                                  (truncatedWindow (triadicLatticePoint n v)
                                                                                    m kc)
                                                                                  fun (y : Vec d) =>
                                                                                  uglob.toFun y -
                                                                                    volumeAverage
                                                                                      (truncatedWindow
                                                                                        (triadicLatticePoint n v) m kc)
                                                                                      uglob.toFun) +
                                                                            Cosc *
                                                                                Real.rpow (3 : ℝ)
                                                                                  ((1 / 2 : ℝ) *
                                                                                    stepSixExponent alpha n m) *
                                                                              (edFinalDataG M (edBoundaryCbd d Cb C kb)
                                                                                  (Khol * stepFourGagliardoConst d stepOneS)
                                                                                  m +
                                                                                edBoundaryDataHPrinted d Cb C kb Kh m))
      (Ccaps : ℝ)
      (hcapsprod :
        ∀ (M : ABKModel d),
          M.gamma ≤ Ccaps⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
            ∀ delta ∈ Set.Ioc (0 : ℝ) (1 / 2 : ℝ),
              (8 : ℝ) * M.gamma ≤ stepOneSEighth →
                M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                    stepOneSEighth.rpow (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * stepOneEp delta →
                  ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)),
                    ∀ (k n : ℤ) (v : Fin d → ℤ),
                      omega ∈ stepThreeGoodEvent M delta k (triadicLatticePoint n v) →
                        ∀ (L : ℤ),
                          k ≤ L →
                            StepSevenLambdaCaps (originCube d k)
                              (fluxCorrectedCoeffFamily M L k (originCube d k)
                                (Cutoff.translateCutoffSample (triadicLatticePoint n v) omega))
                              (↑(Annealed.sigmaBar M k) : ℝ)
                              ((2 : ℝ) * (↑d : ℝ) * ((Ccaps * stepOneEp delta) ^ (2 : ℕ) + (1 : ℝ))))
      (Clam Klam : ℝ)
      (hlamprod :
        ∀ (M : ABKModel d),
          M.gamma ≤ Clam⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
            ∀ delta ∈ Set.Ioc (0 : ℝ) (1 / 2 : ℝ),
              (8 : ℝ) * M.gamma ≤ stepOneSEighth →
                M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                    stepOneSEighth.rpow (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * stepOneEp delta →
                  ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)),
                    ∀ (j nl : ℤ) (v : Fin d → ℤ),
                      omega ∈ stepThreeGoodEvent M delta j (triadicLatticePoint nl v) →
                        ∀ (L m : ℤ),
                          j ≤ L →
                            j - (1 : ℤ) ≤ m →
                              triadicLatticePoint nl v ∈ openCubeSet (originCube d m) →
                                stepSevenCgLamInv (originCube d (j - (1 : ℤ)))
                                    (parentRebasedFamily M L j (wellPlacedCentre (triadicLatticePoint nl v) m (j - (1 : ℤ)))
                                      (triadicLatticePoint nl v) omega)
                                    stepSevenCgS ≤
                                  Klam * (↑(Annealed.sigmaBar M j) : ℝ)⁻¹)
      (Cflu CannP Cind : ℝ),
      let Cmax : ℝ := max (max (max C Ccap) (max Ccaps Clam)) (max (max Cflu CannP) (1 : ℝ));
      ∀ (Cedos : ℝ) (hfloorO : Cflo ≤ Cedos),
        let C1 : ℝ := stepOneC1 d Cedos (1 : ℝ) Citer (kb + (1 : ℕ));
        ∀ (hC1two : (2 : ℝ) ≤ C1) (M : ABKModel d) (alpha : ℝ) (halpha0 : (0 : ℝ) < alpha)
          (halpha : alpha ≤ (1 : ℝ) - Crg * √M.gamma) (m : ℤ) (hgammaCrg : M.gamma ≤ (Crg / (2 : ℝ)) ^ (2 : ℕ))
          (hfact : RootClauseBGammaFacts M Cmax Cann Cind C1 Crg) (hg0 : (0 : ℝ) < M.gamma) (halpha1 : alpha < (1 : ℝ))
          (hregC : M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ)) (hregCap : M.gamma ≤ Ccap⁻¹ * Disorder.cstar M ^ (10 : ℕ))
          (hregCaps : M.gamma ≤ Ccaps⁻¹ * Disorder.cstar M ^ (10 : ℕ))
          (hregLam : M.gamma ≤ Clam⁻¹ * Disorder.cstar M ^ (10 : ℕ))
          (hsmall :
            M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
              stepOneSEighth.rpow (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * stepOneEp (stepOneDelta C1 alpha))
          (Ecap : { E : ℝ // (1 : ℝ) ≤ E }) (hstate : ∀ (m : ℤ), Frozen.Section3.inductionState M m Ecap),
          stepOneDelta C1 alpha ∈ Set.Ioc (0 : ℝ) (1 / 2 : ℝ) ∧
            (2 : ℝ) * M.gamma ≤ (1 : ℝ) - alpha ∧
              stepOneS ∈ Set.Icc ((64 : ℝ) * M.gamma) (1 : ℝ) ∧
                M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                    (stepOneS / (8 : ℝ)).rpow (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2 : ℝ) ∧
                  (∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)),
                      ∀ (L n : ℤ) (v : Fin d → ℤ),
                        m ≤ L →
                          (14 : ℤ) ≤ m - n →
                            v ∈ latticeCubeSet d n m →
                              RootWindowPayload M (stepOneC1 d Cedos (1 : ℝ) Citer (kb + (1 : ℕ))) alpha n m omega →
                                ∀ (uglob hdat : H1Function (openCubeSet (originCube d m))) (gsrc : Vec d → Vec d)
                                  (Khol Kh : ℝ),
                                  (0 : ℝ) ≤ Khol →
                                    (0 : ℝ) ≤ Kh →
                                      IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                                          (originCube d m) uglob hdat gsrc →
                                        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2 : ℝ) Khol gsrc →
                                          HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2 : ℝ) Kh hdat.grad →
                                            (∀ y ∈ openCubeSet (originCube d m),
                                                ‖hdat.grad y‖ ≤ Real.rpow (3 : ℝ) ((↑m : ℝ) / (2 : ℝ)) * Kh) →
                                              HasGradientOn (openCubeSet (originCube d m)) hdat.toFun hdat.grad →
                                                ∀ (n' kc : ℤ),
                                                  n ≤ n' →
                                                    n' ≤ kc →
                                                      kc ≤ m →
                                                        ((3 : ℝ) ^ (-n') *
                                                            normalizedL2On (truncatedWindow (triadicLatticePoint n v) m n')
                                                              fun (y : Vec d) =>
                                                              uglob.toFun y -
                                                                volumeAverage
                                                                  (truncatedWindow (triadicLatticePoint n v) m n')
                                                                  uglob.toFun) ≤
                                                          Cosc *
                                                                Real.rpow (3 : ℝ)
                                                                  ((1 / 2 : ℝ) * stepSixExponent alpha n m) *
                                                              ((3 : ℝ) ^ (-kc) *
                                                                normalizedL2On
                                                                  (truncatedWindow (triadicLatticePoint n v) m kc)
                                                                  fun (y : Vec d) =>
                                                                  uglob.toFun y -
                                                                    volumeAverage
                                                                      (truncatedWindow (triadicLatticePoint n v) m kc)
                                                                      uglob.toFun) +
                                                            Cosc *
                                                                Real.rpow (3 : ℝ)
                                                                  ((1 / 2 : ℝ) * stepSixExponent alpha n m) *
                                                              (edFinalDataG M (edBoundaryCbd d Cb C kb)
                                                                  (Khol * stepFourGagliardoConst d stepOneS) m +
                                                                edBoundaryDataHPrinted d Cb C kb Kh m)) ∧
                    (∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)),
                        ∀ (k n : ℤ) (v : Fin d → ℤ),
                          omega ∈ stepThreeGoodEvent M (stepOneDelta C1 alpha) k (triadicLatticePoint n v) →
                            ∀ (L : ℤ),
                              k ≤ L →
                                StepSevenLambdaCaps (originCube d k)
                                  (fluxCorrectedCoeffFamily M L k (originCube d k)
                                    (Cutoff.translateCutoffSample (triadicLatticePoint n v) omega))
                                  (↑(Annealed.sigmaBar M k) : ℝ)
                                  ((2 : ℝ) * (↑d : ℝ) *
                                    ((Ccaps * stepOneEp (stepOneDelta C1 alpha)) ^ (2 : ℕ) + (1 : ℝ)))) ∧
                      ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)),
                        ∀ (j nl : ℤ) (v : Fin d → ℤ),
                          omega ∈ stepThreeGoodEvent M (stepOneDelta C1 alpha) j (triadicLatticePoint nl v) →
                            ∀ (L m : ℤ),
                              j ≤ L →
                                j - (1 : ℤ) ≤ m →
                                  triadicLatticePoint nl v ∈ openCubeSet (originCube d m) →
                                    stepSevenCgLamInv (originCube d (j - (1 : ℤ)))
                                        (parentRebasedFamily M L j
                                          (wellPlacedCentre (triadicLatticePoint nl v) m (j - (1 : ℤ)))
                                          (triadicLatticePoint nl v) omega)
                                        stepSevenCgS ≤
                                      Klam * (↑(Annealed.sigmaBar M j) : ℝ)⁻¹ := by
  intro d instance1 cstar Crg hCrg C Ccap Cann Cb Cflo Citer Cosc kb hoscprod Ccaps hcapsprod Clam Klam hlamprod Cflu CannP Cind Cmax Cedos hfloorO C1 hC1two M alpha halpha0 halpha m hgammaCrg hfact hg0 halpha1 hregC hregCap hregCaps hregLam hsmall Ecap hstate
  have hdeltamem := stepOneDelta_mem hC1two halpha0 halpha1
  -- the `2γ ≤ 1-α` regime
  have h2gamma : 2 * M.gamma ≤ 1 - alpha := by
    have hCrg2 : (0 : ℝ) ≤ Crg / 2 := by linarith only [hCrg]
    have hsg : Real.sqrt M.gamma ≤ Crg / 2 := by
      have hstep := Real.sqrt_le_sqrt hgammaCrg
      rwa [Real.sqrt_sq hCrg2] at hstep
    have h1 : 2 * M.gamma = 2 * (Real.sqrt M.gamma * Real.sqrt M.gamma) := by
      rw [Real.mul_self_sqrt hg0.le]
    have h2 : Real.sqrt M.gamma * Real.sqrt M.gamma ≤
        (Crg / 2) * Real.sqrt M.gamma :=
      mul_le_mul_of_nonneg_right hsg (Real.sqrt_nonneg _)
    have h3 : Crg * Real.sqrt M.gamma ≤ 1 - alpha := by linarith only [halpha]
    linarith only [h1.le, h1.ge, h2, h3]
  -- the flush producer's `s`-range and smallness
  have hsrange : stepOneS ∈ Set.Icc (64 * M.gamma) 1 := by
    constructor
    · have h256 := hfact.le256
      rw [show stepOneS = (1 / 4 : ℝ) from rfl]
      linarith only [h256]
    · rw [show stepOneS = (1 / 4 : ℝ) from rfl]; norm_num
  have hsmallFlu : M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
      Real.rpow (stepOneS / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
        (1 / 2) := by
    have hb : (0 : ℝ) ≤ Real.rpow (stepOneS / 8) (3 / 2 : ℝ) *
        Disorder.cstar M ^ (2 : ℕ) := by
      have h1 : (0 : ℝ) ≤ Real.rpow (stepOneS / 8) (3 / 2 : ℝ) :=
        Real.rpow_nonneg (by rw [show stepOneS = (1 / 4 : ℝ) from rfl]; norm_num) _
      exact mul_nonneg h1 (pow_nonneg ((Disorder.cstar_characterization M).1).le 2)
    refine le_trans hfact.smallFree (mul_le_mul_of_nonneg_left ?_ hb)
    have hCmax1 : (1 : ℝ) ≤ Cmax :=
      le_trans (le_max_right (max Cflu CannP) 1) (le_max_right _ _)
    have hCmaxinv : Cmax⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact hCmax1
    have hS40 : (0 : ℝ) ≤ stepOneS ^ (4 : ℕ) :=
      pow_nonneg (by rw [show stepOneS = (1 / 4 : ℝ) from rfl]; norm_num) 4
    have hS4half : stepOneS ^ (4 : ℕ) ≤ 1 / 2 := by
      rw [show stepOneS = (1 / 4 : ℝ) from rfl]
      norm_num
    calc Cmax⁻¹ * stepOneS ^ (4 : ℕ) ≤ 1 * stepOneS ^ (4 : ℕ) :=
          mul_le_mul_of_nonneg_right hCmaxinv hS40
      _ = stepOneS ^ (4 : ℕ) := one_mul _
      _ ≤ 1 / 2 := hS4half
  -- the a.e. facts
  have haeOsc := hoscprod Cedos hfloorO M m Ecap (hstate m) hfact.ltHalf hregC
    hregCap hfact.regimeAnn hfact.le256 alpha halpha0 halpha1 hsmall m le_rfl
  have haeCaps := hcapsprod M hregCaps (stepOneDelta C1 alpha) hdeltamem
    hfact.floorEight hsmall
  have haeLam := hlamprod M hregLam (stepOneDelta C1 alpha) hdeltamem
    hfact.floorEight hsmall
  exact ⟨hdeltamem, h2gamma, hsrange, hsmallFlu, haeOsc, haeCaps, haeLam⟩

private theorem rootClauseBWellPlacedFloor_comparisonBounds2 :
    ∀ (d : ℕ) [inst : NeZero d] (Crg C Ccap Cann Cb Citer : ℝ) (kb : ℕ) (Ccaps : ℝ) (hCcaps : (0 : ℝ) < Ccaps)
      (Clam Cflu CannP Cind : ℝ) (hCbd : (0 : ℝ) ≤ edBoundaryCbd d Cb C kb) (hCWH : (0 : ℝ) ≤ boundaryCWH d Cb C kb),
      let Cmax : ℝ := max (max (max C Ccap) (max Ccaps Clam)) (max (max Cflu CannP) (1 : ℝ));
      let CBu : ℝ := rootClauseBCapsUniform d Ccaps;
      ∀ (hCBuDef : CBu = rootClauseBCapsUniform d Ccaps),
        let CWGu : ℝ := rootClauseBOscWUniform (edBoundaryCbd d Cb C kb) * stepFourGagliardoConst d stepOneS;
        ∀ (hCWGuDef : CWGu = rootClauseBOscWUniform (edBoundaryCbd d Cb C kb) * stepFourGagliardoConst d stepOneS)
          (Cedos : ℝ),
          let C1 : ℝ := stepOneC1 d Cedos (1 : ℝ) Citer (kb + (1 : ℕ));
          ∀ (M : ABKModel d) (alpha : ℝ) (m : ℤ) (hfact : RootClauseBGammaFacts M Cmax Cann Cind C1 Crg) (n : ℤ)
            (u : H1Function (openCubeSet (originCube d m))) (Kg Kh : ℝ) (x : Vec d) (hKg : (0 : ℝ) ≤ Kg)
            (hKh : (0 : ℝ) ≤ Kh) (kc np : ℤ) (hδIoc : stepOneDelta C1 alpha ∈ Set.Ioc (0 : ℝ) (1 / 2 : ℝ)),
            let CBraw : ℝ := (2 : ℝ) * (↑d : ℝ) * ((Ccaps * stepOneEp (stepOneDelta C1 alpha)) ^ (2 : ℕ) + (1 : ℝ));
            ∀ (hCBrawDef : CBraw = (2 : ℝ) * (↑d : ℝ) * ((Ccaps * stepOneEp (stepOneDelta C1 alpha)) ^ (2 : ℕ) + (1 : ℝ))),
              (0 : ℝ) ≤ CBraw ∧
                CBraw ≤ CBu ∧
                  edFinalDataOscW M (edBoundaryCbd d Cb C kb) * stepFourGagliardoConst d stepOneS ≤ CWGu ∧
                    (0 : ℝ) ≤ edFinalDataOscW M (edBoundaryCbd d Cb C kb) * stepFourGagliardoConst d stepOneS ∧
                      (0 : ℝ) < (↑(Annealed.sigmaBar M (np + (1 : ℤ))) : ℝ) ∧
                        (0 : ℝ) ≤ edBoundaryDataHPrinted d Cb C kb Kh m ∧
                          (2 : ℝ) * (↑d : ℝ) + (2 : ℝ) ≤ C1 ∧
                            stepOneDelta C1 alpha ≤ C1⁻¹ * ((1 : ℝ) - alpha) ∧
                              ((0 : ℝ) ≤
                                  (cubeScaleFactor (originCube d kc))⁻¹ *
                                    normalizedL2On (truncatedWindow (triadicLatticePoint n (offGridLatticeIndex n x)) m kc)
                                      fun (y : Vec d) =>
                                      u.toFun y -
                                        volumeAverage
                                          (truncatedWindow (triadicLatticePoint n (offGridLatticeIndex n x)) m kc)
                                          u.toFun) ∧
                                (0 : ℝ) < (↑(Annealed.sigmaBar M m) : ℝ) ∧
                                  (0 : ℝ) ≤
                                      (↑(Annealed.sigmaBar M m) : ℝ) *
                                        edFinalDataG M (edBoundaryCbd d Cb C kb) (Kg * stepFourGagliardoConst d stepOneS)
                                          m ∧
                                    (0 : ℝ) ≤
                                      edFinalDataG M (edBoundaryCbd d Cb C kb) (Kg * stepFourGagliardoConst d stepOneS) m := by
  intro d instance1 Crg C Ccap Cann Cb Citer kb Ccaps hCcaps Clam Cflu CannP Cind hCbd hCWH Cmax CBu hCBuDef CWGu hCWGuDef Cedos C1 M alpha m hfact n u Kg Kh x hKg hKh kc np hδIoc CBraw hCBrawDef
  have hCBraw0 : (0 : ℝ) ≤ CBraw := by
    have hsq : (0 : ℝ) ≤ (Ccaps * stepOneEp (stepOneDelta C1 alpha)) ^ 2 := sq_nonneg _
    have hdd : (0 : ℝ) ≤ 2 * (d : ℝ) := by
      have hcd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith only [hcd]
    rw [hCBrawDef]
    exact mul_nonneg hdd (by linarith only [hsq])
  have hCBle : CBraw ≤ CBu := by
    rw [hCBrawDef, hCBuDef]
    exact capsConst_le_rootClauseBCapsUniform d hCcaps.le hδIoc.2
  have hCWGle : edFinalDataOscW M (edBoundaryCbd d Cb C kb) *
      stepFourGagliardoConst d stepOneS ≤ CWGu := by
    rw [hCWGuDef]
    exact mul_le_mul_of_nonneg_right
      (edFinalDataOscW_le_uniform hfact.ltHalf hfact.leQuarter hCbd)
      (stepFourGagliardoConst_nonneg d _)
  have hCWG0 : (0 : ℝ) ≤ edFinalDataOscW M (edBoundaryCbd d Cb C kb) *
      stepFourGagliardoConst d stepOneS :=
    mul_nonneg (edFinalDataOscW_nonneg hfact.ltHalf hCbd)
      (stepFourGagliardoConst_nonneg d _)
  have hsigmaJ : (0 : ℝ) < (Annealed.sigmaBar M (np + 1) : ℝ) :=
    (Annealed.sigmaBar M (np + 1)).2
  have hdataHP0 : (0 : ℝ) ≤ edBoundaryDataHPrinted d Cb C kb Kh m := by
    rw [edBoundaryDataHPrinted_eq_boundaryCWH_mul]
    exact mul_nonneg hCWH (edFinalDataOscG_nonneg hKh m)
  have hC1dim : 2 * (d : ℝ) + 2 ≤ C1 := two_mul_dim_le_stepOneC1 d Cedos 1 Citer (kb + 1)
  have hdeltaEq : stepOneDelta C1 alpha ≤ C1⁻¹ * (1 - alpha) := le_of_eq rfl
  -- the two-branch dichotomy at the selected fine scale
  have hoscHi0 : (0 : ℝ) ≤ (cubeScaleFactor (originCube d kc))⁻¹ *
      normalizedL2On
        (truncatedWindow (Support.triadicLatticePoint n (offGridLatticeIndex n x))
          m kc)
        (fun y => u.toFun y -
          volumeAverage
            (truncatedWindow
              (Support.triadicLatticePoint n (offGridLatticeIndex n x)) m kc)
            u.toFun) := by
    have hsc : (0 : ℝ) ≤ (cubeScaleFactor (originCube d kc))⁻¹ := by
      rw [cubeScaleFactor]
      exact inv_nonneg.mpr (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    exact mul_nonneg hsc (normalizedL2On_nonneg _ _)
  have hsigmaPos : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hGpres : (0 : ℝ) ≤ (Annealed.sigmaBar M m : ℝ) *
      edFinalDataG M (edBoundaryCbd d Cb C kb)
        (Kg * stepFourGagliardoConst d stepOneS) m := by
    rw [sigmaBar_mul_edFinalDataG_eq]
    exact mul_nonneg hCWG0 (edFinalDataOscG_nonneg hKg m)
  have hedG0 : (0 : ℝ) ≤ edFinalDataG M (edBoundaryCbd d Cb C kb)
      (Kg * stepFourGagliardoConst d stepOneS) m :=
    (mul_nonneg_iff_of_pos_left hsigmaPos).mp hGpres
  exact ⟨hCBraw0, hCBle, hCWGle, hCWG0, hsigmaJ, hdataHP0, hC1dim, hdeltaEq, hoscHi0, hsigmaPos, hGpres, hedG0⟩

private theorem rootClauseBWellPlacedFloor_comparisonBounds3 : rootClauseBWellPlacedFloor_comparisonBounds3_statement := by
  intro d cstar Crg hCrg C Ccap Cann Citer kb hC hCcap Ccaps hCcaps Clam hClam Cflu hCflu CannP hCannP Cind Cmax Cedos C1 gamma0 hfacts M hcs hgammale alpha halpha0 halpha
  have hgammag0 : M.gamma ≤ gamma0 := le_trans hgammale (min_le_left _ _)
  have hgammaCrg : M.gamma ≤ (Crg / 2) ^ (2 : ℕ) :=
    le_trans hgammale (min_le_right _ _)
  have hfact := hfacts M hcs hgammag0
  have hg0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hsqrtpos : (0 : ℝ) < Crg * Real.sqrt M.gamma :=
    mul_pos hCrg (Real.sqrt_pos.mpr hg0)
  have halpha1 : alpha < 1 := by linarith only [halpha, hsqrtpos]
  have hcs10 : (0 : ℝ) ≤ Disorder.cstar M ^ (10 : ℕ) :=
    pow_nonneg ((Disorder.cstar_characterization M).1).le 10
  -- the regime facts for each producer
  have hregC : M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hfact.regimeC (mul_le_mul_of_nonneg_right
      (inv_anti₀ hC (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))) hcs10)
  have hregCap : M.gamma ≤ Ccap⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hfact.regimeC (mul_le_mul_of_nonneg_right
      (inv_anti₀ hCcap (le_trans (le_max_right _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))) hcs10)
  have hregCaps : M.gamma ≤ Ccaps⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hfact.regimeC (mul_le_mul_of_nonneg_right
      (inv_anti₀ hCcaps (le_trans (le_max_left _ _)
        (le_trans (le_max_right _ _) (le_max_left _ _)))) hcs10)
  have hregLam : M.gamma ≤ Clam⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hfact.regimeC (mul_le_mul_of_nonneg_right
      (inv_anti₀ hClam (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_left _ _)))) hcs10)
  have hregFlu : M.gamma ≤ Cflu⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hfact.regimeC (mul_le_mul_of_nonneg_right
      (inv_anti₀ hCflu (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_right _ _)))) hcs10)
  have hregAnnP : M.gamma ≤ CannP⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hfact.regimeC (mul_le_mul_of_nonneg_right
      (inv_anti₀ hCannP (le_trans (le_max_right _ _)
        (le_trans (le_max_left _ _) (le_max_right _ _)))) hcs10)
  have hsmall := hfact.smallEp alpha halpha0 halpha
  exact ⟨hgammaCrg, hfact, hg0, halpha1, hregC, hregCap, hregCaps, hregLam, hregFlu, hregAnnP, hsmall⟩

private theorem rootClauseB_energyWindowBound : rootClauseB_energyWindowBound_statement := by
  intro d instance1 Crg C Ccap Cann Cb Citer Cosc kb hCosc Ccaps Clam Klam hKlam Cflu Afl K1 K2 hK1 hK2 CannP Cind Cch hCch hend CdispC hCbd hCWH hd1 CBu CWGu Ctru hCtru0 PG PF Cedos C1 M alpha halpha0 m hfact halpha1 Ecap hstate h2gamma omega hFlush hPin n L hnm hmL u h g Kg Kh hsol hgHol hhHol hsup x hKg hKh hzm hgL2 hgW hhW hoscfun kc hkhi np hjlo hgoodj B hcard hgapHi hgapLo hgapStrict hδIoc hlamkc hCWGle hCWG0 hdataHP0 hC1dim hdeltaEq hoscHi0 hedG0 hgate
  -- branch: the `S`-killed window energy under the `ε`-pin
  have hnogate : ¬ (∀ (i : Fin d) (sigma : ℝ), (sigma = 1 ∨ sigma = -1) →
      ¬ (wellPlacedHalfGap m np <
        sigma * Support.triadicLatticePoint n (offGridLatticeIndex n x) i)) :=
    fun hall => hgate (no_overhang_iff_gate.mp hall)
  push Not at hnogate
  obtain ⟨i, sigma, hsig, hover⟩ := hnogate
  have hover' : wellPlacedHalfGap m (np - 2 + 2) <
      sigma * Support.triadicLatticePoint n (offGridLatticeIndex n x) i := by
    rw [show (np - 2 + 2 : ℤ) = np by ring]
    exact hover
  have hmemHalf : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
      (Support.cgEllipLowerConstant d) (np - 2 + 3)
      (Support.triadicLatticePoint n (offGridLatticeIndex n x))
      ⟨stepOneS / 8, by have := stepOneS_pos; linarith only [this]⟩ (1 / 2) := by
    rw [show (np - 2 + 3 : ℤ) = np + 1 by ring]
    exact mem_goodEventAtHalf_of_stepThree hδIoc hgoodj
  have hpinInst : Afl * Support.fluxCorrectedErrorRepresentative M L (np - 2 + 3)
      ⟨stepOneS / 8, by have := stepOneS_pos; linarith only [this]⟩
      (Cutoff.translateCutoffSample
        (Support.triadicLatticePoint n (offGridLatticeIndex n x)) omega) ≤
      stepOneS ^ (4 : ℕ) := by
    rw [show (np - 2 + 3 : ℤ) = np + 1 by ring]
    exact hPin (np + 1) n (offGridLatticeIndex n x) hgoodj L (by omega)
  have hFB := hFlush L m (np - 2) n (offGridLatticeIndex n x) i sigma hsig hmL
    (by omega) hzm hover' hmemHalf hpinInst
  have hDDraw := hFB u h g hsol hgL2 hgW hhW
  rw [show (((fun y' =>
        Support.triadicLatticePoint n (offGridLatticeIndex n x) + y') ''
          openCubeSet (originCube d (np - 2 + 3))) ∩
        openCubeSet (originCube d m)) =
      truncatedWindow (Support.triadicLatticePoint n (offGridLatticeIndex n x))
        m (np - 2 + 3) from rfl] at hDDraw
  have hsigmaF : (0 : ℝ) < (Annealed.sigmaBar M (np - 2 + 3) : ℝ) :=
    (Annealed.sigmaBar M (np - 2 + 3)).2
  have hbr := flushBracket_le (n := np - 2) (m := m)
    (z := Support.triadicLatticePoint n (offGridLatticeIndex n x))
    (sigma := (Annealed.sigmaBar M (np - 2 + 3) : ℝ)) (K2 := K2) (Khol := Kg)
    (Kh := Kh) u h (gsrc := g) hd1 hzm (by omega) hsigmaF hK2 hKg hKh hgHol
    hhHol hsup
  have hDD' := le_trans hDDraw (mul_le_mul_of_nonneg_left hbr hK1.le)
  have hbrG : ((Annealed.sigmaBar M (np - 2 + 3) : ℝ))⁻¹ ≤
      rootClauseBTopKs M.gamma m (np - 2 + 3) *
        ((Annealed.sigmaBar M m : ℝ))⁻¹ := by
    rw [show (np - 2 + 3 : ℤ) = np + 1 by ring]
    exact rootClauseBTop_htrShom (hstate m) (by omega) le_rfl
  have hoscF := hoscfun (np + 1) kc (by omega) (by omega) (by omega)
  rw [← cubeScaleFactor_originCube_inv d kc] at hoscF
  rw [show (np + 1 : ℤ) = np - 2 + 3 by ring] at hoscF
  have hoscData0f : (0 : ℝ) ≤ edFinalDataG M (edBoundaryCbd d Cb C kb)
      (Kg * stepFourGagliardoConst d stepOneS) m +
      edBoundaryDataHPrinted d Cb C kb Kh m := by
    linarith only [hedG0, hdataHP0]
  have hgradF := stepSevenFlushHgrad d (M := M) (nroot := n) (n := np - 2)
    (m := m) (z := Support.triadicLatticePoint n (offGridLatticeIndex n x)) u
    hzm hnm (by omega) (by omega) hC1dim halpha0.le halpha1.le hdeltaEq
    (by omega) hcard h2gamma hK1.le hK2 hKg hKh hCosc hoscHi0 hoscData0f
    hbrG hDD' hoscF
  rw [show (np - 2 + 3 : ℤ) = np + 1 by ring] at hgradF
  rw [show edFinalDataG M (edBoundaryCbd d Cb C kb)
        (Kg * stepFourGagliardoConst d stepOneS) m +
        edBoundaryDataHPrinted d Cb C kb Kh m +
        Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh =
      edFinalDataG M (edBoundaryCbd d Cb C kb)
        (Kg * stepFourGagliardoConst d stepOneS) m +
        (edBoundaryDataHPrinted d Cb C kb Kh m +
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) from by ring,
    edFinalDataG_add_boundary_eq_dataOsc (M := M) (edBoundaryCbd d Cb C kb) Kg
      (stepFourGagliardoConst d stepOneS) m
      (edBoundaryDataHPrinted d Cb C kb Kh m +
        Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)] at hgradF
  have hCgF0 : (0 : ℝ) ≤ stepSevenFlushCg d K1 K2 Cosc :=
    stepSevenFlushCg_nonneg d hK1.le hK2 hCosc
  have hdataHf0 : (0 : ℝ) ≤ edBoundaryDataHPrinted d Cb C kb Kh m +
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh := by
    have h1 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKh
    linarith only [hdataHP0, h1]
  have hdataMf0 : (0 : ℝ) ≤ Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
      (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg) :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKg)
  have hCestF : rootClauseBWellPlacedPrefactor d Cch
      (stepSevenFlushCg d K1 K2 Cosc) Klam Ctru
      (edFinalDataOscW M (edBoundaryCbd d Cb C kb) *
        stepFourGagliardoConst d stepOneS)
      (boundaryCWH d Cb C kb + 1) 1 ≤ max PG PF := by
    have hpre := rootClauseBWellPlacedPrefactor_mono d
      (CWH := boundaryCWH d Cb C kb + 1) (CWH' := boundaryCWH d Cb C kb + 1)
      (CdM := (1 : ℝ)) (CdM' := (1 : ℝ)) hCch.le hCgF0 hKlam.le
      hCtru0 hCWG0 (by linarith only [hCWH]) (by norm_num : (0 : ℝ) ≤ 1)
      le_rfl hCWGle le_rfl le_rfl
    exact le_trans hpre (le_max_right PG PF)
  exact hend M m Ecap (hstate m) hfact.ltHalf L omega u h hzm le_rfl hnm
    (by omega) (by omega) (by omega) hsol hgL2 hgW hKg hKh
    (rootClauseBDataBConst_nonneg d) hKlam.le hCgF0 hCbd
    (by norm_num : (0 : ℝ) ≤ 1) (by linarith only [hCWH]) hdataHf0 hdataMf0
    hC1dim halpha0.le halpha1.le hdeltaEq hcard hlamkc
    (rootClauseB_dataB_coarseFrame (by omega) hKg hgHol hgL2 hgW)
    (le_of_eq (by rw [edFinalDataOscG, one_mul]))
    (le_of_eq (by
      rw [edBoundaryDataHPrinted_eq_boundaryCWH_mul, edFinalDataOscG]
      ring))
    hgradF hCestF



private theorem rootClauseB_gatedCaccioppoliBound :
    ∀ (d : ℕ) [inst : NeZero d] (Crg C Ccap Cann Cb Citer Cosc : ℝ)
      (kb : ℕ) (hCosc : (0 : ℝ) ≤ Cosc) (Ccaps Clam Klam : ℝ) (hKlam : (0 : ℝ) < Klam) (Cflu K1 K2 CannP Cind Cch : ℝ)
      (hCch : (0 : ℝ) < Cch)
      (hend :
        ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : { E : ℝ // (1 : ℝ) ≤ E }),
          Frozen.Section3.inductionState M m0 Ecap →
            M.gamma < (1 / 2 : ℝ) →
              ∀ (L : ℤ) {alpha : ℝ} {n m kc np : ℤ} {z : Vec d} (omega : Cutoff.CutoffSample d)
                (uglob hdat : H1Function (openCubeSet (originCube d m))) {gsrc : Vec d → Vec d}
                {Khol Kh Kd CB Cg Cdel CdM CWH C1 delta Cest dataH dataM : ℝ} {B : ℕ},
                z ∈ openCubeSet (originCube d m) →
                  m ≤ m0 →
                    n ≤ m →
                      kc ≤ m - (1 : ℤ) →
                        np + (1 : ℤ) ≤ m →
                          m - (kc + (1 : ℤ)) ≤ (↑B : ℤ) + (1 : ℤ) →
                            IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m)
                                uglob hdat gsrc →
                              MemLp gsrc (2 : ENNReal) (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
                                MemLp (Gagliardo.gagliardoKernel stepOneS (2 : ENNReal) gsrc) (2 : ENNReal)
                                    (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                                  (0 : ℝ) ≤ Khol →
                                    (0 : ℝ) ≤ Kh →
                                      (0 : ℝ) ≤ Kd →
                                        (0 : ℝ) ≤ CB →
                                          (0 : ℝ) ≤ Cg →
                                            (0 : ℝ) ≤ Cdel →
                                              (0 : ℝ) ≤ CdM →
                                                (0 : ℝ) ≤ CWH →
                                                  (0 : ℝ) ≤ dataH →
                                                    (0 : ℝ) ≤ dataM →
                                                      (2 : ℝ) * (↑d : ℝ) + (2 : ℝ) ≤ C1 →
                                                        (0 : ℝ) ≤ alpha →
                                                          alpha ≤ (1 : ℝ) →
                                                            delta ≤ C1⁻¹ * ((1 : ℝ) - alpha) →
                                                              (↑B : ℝ) ≤ delta * ((↑(m - n).toNat : ℝ) + (1 : ℝ)) →
                                                                stepSevenCgLamInv (originCube d kc)
                                                                      (parentRebasedFamily M L (kc + (1 : ℤ))
                                                                        (wellPlacedCentre z m kc) z omega)
                                                                      stepSevenCgS ≤
                                                                    CB * (↑(Annealed.sigmaBar M (kc + (1 : ℤ))) : ℝ)⁻¹ →
                                                                  (scaleNormalizedPositiveBesovVectorSeminormTwo
                                                                        (originCube d kc) stepSevenCgS fun (x : Vec d) =>
                                                                        -gsrc (x + wellPlacedCentre z m kc)) ≤
                                                                      Kd * edFinalDataOscG Khol m →
                                                                    dataM ≤
                                                                        CdM *
                                                                          (√(↑(Annealed.sigmaBar M m) : ℝ)⁻¹ *
                                                                            edFinalDataOscG Khol m) →
                                                                      dataH ≤ CWH * edFinalDataOscG Kh m →
                                                                        stepSevenNuGradNorm M.nu
                                                                              (truncatedWindow z m (n + (1 : ℤ)))
                                                                              uglob.grad ≤
                                                                            Cg *
                                                                                    √(↑(Annealed.sigmaBar M
                                                                                            (np + (1 : ℤ))) :
                                                                                        ℝ) *
                                                                                  Real.rpow (3 : ℝ)
                                                                                    ((3 / 4 : ℝ) *
                                                                                      stepSixExponent alpha n m) *
                                                                                ((cubeScaleFactor (originCube d kc))⁻¹ *
                                                                                  normalizedL2On (truncatedWindow z m kc)
                                                                                    fun (x : Vec d) =>
                                                                                    uglob.toFun x -
                                                                                      volumeAverage (truncatedWindow z m kc)
                                                                                        uglob.toFun) +
                                                                              Cg *
                                                                                  Real.rpow (3 : ℝ)
                                                                                    ((3 / 4 : ℝ) *
                                                                                      stepSixExponent alpha n m) *
                                                                                (√(↑(Annealed.sigmaBar M (np + (1 : ℤ))) :
                                                                                        ℝ) *
                                                                                    ((1 : ℝ) *
                                                                                      ((↑(Annealed.sigmaBar M m) : ℝ)⁻¹ *
                                                                                          ((↑(Annealed.sigmaBar M m) : ℝ) *
                                                                                            edFinalDataG M Cdel
                                                                                              (Khol *
                                                                                                stepFourGagliardoConst d
                                                                                                  stepOneS)
                                                                                              m) +
                                                                                        dataH)) +
                                                                                  dataM) →
                                                                          rootClauseBWellPlacedPrefactor d Cch Cg CB
                                                                                (rootClauseBTopCtr d Kd)
                                                                                (edFinalDataOscW M Cdel *
                                                                                  stepFourGagliardoConst d stepOneS)
                                                                                CWH CdM ≤
                                                                              Cest →
                                                                            (√M.nu *
                                                                                normalizedL2On
                                                                                  (truncatedWindow z m (n + (1 : ℤ)))
                                                                                  fun (y : Vec d) =>
                                                                                  √(vecNormSq (uglob.grad y))) ≤
                                                                              Cest *
                                                                                  Real.rpow (3 : ℝ)
                                                                                    (((1 : ℝ) - alpha) *
                                                                                      ((↑m : ℝ) - (↑n : ℝ))) *
                                                                                ((√M.nu *
                                                                                      normalizedL2On
                                                                                        (openCubeSet (originCube d m))
                                                                                        fun (y : Vec d) =>
                                                                                        √(vecNormSq (uglob.grad y))) +
                                                                                    √(↑(Annealed.sigmaBar M m) : ℝ)⁻¹ *
                                                                                        Real.rpow (3 : ℝ)
                                                                                          ((↑m : ℝ) / (2 : ℝ)) *
                                                                                      Khol +
                                                                                  √(↑(Annealed.sigmaBar M m) : ℝ) *
                                                                                      Real.rpow (3 : ℝ)
                                                                                        ((↑m : ℝ) / (2 : ℝ)) *
                                                                                    Kh))
      (CdispC : ℝ) (hCdispC : (0 : ℝ) < CdispC)
      (hdisp :
        ∀ (M : ABKModel d) (L mf m n n' : ℤ) (Qf : TriadicCube d) {z : Vec d} (omega : Cutoff.CutoffSample d)
          (u : H1Function (openCubeSet (originCube d m))) (v : H1Function (Ch02.cubeDomain (originCube d n')).carrier)
          {g : Vec d → Vec d} {C1 alpha delta : ℝ} {B : ℕ} {Cosc CB sigma oscHi dataOsc : ℝ},
          (∀ (y : Vec d), v.toFun y = u.toFun (y + z)) →
            (∀ (y : Vec d), v.grad y = u.grad (y + z)) →
              (fun (y : Vec d) => z + y) '' openCubeSet (originCube d n') ⊆ openCubeSet (originCube d m) →
                n + (1 : ℤ) ≤ n' - (2 : ℤ) →
                  IsForcedEquation (originCube d n')
                      (fluxCorrectedCoeffFamily M L mf Qf (Cutoff.translateCutoffSample z omega)) v g →
                    ForceBesovRegularity (originCube d n') stepOneS g →
                      (2 : ℝ) * (↑d : ℝ) + (2 : ℝ) ≤ C1 →
                        (0 : ℝ) ≤ alpha →
                          alpha ≤ (1 : ℝ) →
                            n ≤ m →
                              delta ≤ C1⁻¹ * ((1 : ℝ) - alpha) →
                                n' - n ≤ (↑B : ℤ) + (6 : ℤ) →
                                  (↑B : ℝ) ≤ delta * ((↑(m - n).toNat : ℝ) + (1 : ℝ)) →
                                    (0 : ℝ) ≤ Cosc →
                                      (0 : ℝ) ≤ CB →
                                        (0 : ℝ) ≤ oscHi →
                                          (0 : ℝ) ≤ dataOsc →
                                            StepSevenLambdaCaps (originCube d (n' + (1 : ℤ)))
                                                (fluxCorrectedCoeffFamily M L mf Qf (Cutoff.translateCutoffSample z omega))
                                                sigma CB →
                                              ((3 : ℝ) ^ (-n') *
                                                    normalizedL2On (truncatedWindow z m n') fun (x : Vec d) =>
                                                      u.toFun x - volumeAverage (truncatedWindow z m n') u.toFun) ≤
                                                  Cosc * Real.rpow (3 : ℝ) ((1 / 2 : ℝ) * stepSixExponent alpha n m) *
                                                      oscHi +
                                                    Cosc * Real.rpow (3 : ℝ) ((1 / 2 : ℝ) * stepSixExponent alpha n m) *
                                                      dataOsc →
                                                stepSevenNuGradNorm M.nu (truncatedWindow z m (n + (1 : ℤ))) u.grad ≤
                                                  Real.rpow (3 : ℝ) ((3 : ℝ) * (↑d : ℝ) + (1 / 4 : ℝ)) *
                                                              stepSevenCaccConst CdispC (originCube d n')
                                                                (fluxCorrectedCoeffFamily M L mf Qf
                                                                  (Cutoff.translateCutoffSample z omega)) *
                                                            (Cosc * √((256 / 63 : ℝ) * CB) + (1 : ℝ)) *
                                                          √sigma *
                                                        Real.rpow (3 : ℝ) ((3 / 4 : ℝ) * stepSixExponent alpha n m) *
                                                      oscHi +
                                                    Real.rpow (3 : ℝ) ((3 : ℝ) * (↑d : ℝ) + (1 / 4 : ℝ)) *
                                                            stepSevenCaccConst CdispC (originCube d n')
                                                              (fluxCorrectedCoeffFamily M L mf Qf
                                                                (Cutoff.translateCutoffSample z omega)) *
                                                          (Cosc * √((256 / 63 : ℝ) * CB) + (1 : ℝ)) *
                                                        Real.rpow (3 : ℝ) ((3 / 4 : ℝ) * stepSixExponent alpha n m) *
                                                      (√sigma * dataOsc +
                                                        stepSevenCaccDataM (originCube d n')
                                                          (fluxCorrectedCoeffFamily M L mf Qf
                                                            (Cutoff.translateCutoffSample z omega))
                                                          g))
      (hCbd : (0 : ℝ) ≤ edBoundaryCbd d Cb C kb) (hCWH : (0 : ℝ) ≤ boundaryCWH d Cb C kb),
      let CBu : ℝ := rootClauseBCapsUniform d Ccaps;
      let CWGu : ℝ := rootClauseBOscWUniform (edBoundaryCbd d Cb C kb) * stepFourGagliardoConst d stepOneS;
      let Ctru : ℝ := rootClauseBTopCtr d (rootClauseBDataBConst d);
      ∀ (hCtru0 : (0 : ℝ) ≤ Ctru),
        let PG : ℝ :=
          rootClauseBWellPlacedPrefactor d Cch (rootClauseBCg d (rootClauseBCaccUniform CdispC CBu) Cosc CBu) Klam Ctru CWGu
            (boundaryCWH d Cb C kb) (rootClauseBDataMConst d CBu);
        let PF : ℝ :=
          rootClauseBWellPlacedPrefactor d Cch (stepSevenFlushCg d K1 K2 Cosc) Klam Ctru CWGu
            (boundaryCWH d Cb C kb + (1 : ℝ)) (1 : ℝ);
        ∀ (Cedos : ℝ),
          let C1 : ℝ := stepOneC1 d Cedos (1 : ℝ) Citer (kb + (1 : ℕ));
          ∀ (M : ABKModel d) (alpha : ℝ) (halpha0 : (0 : ℝ) < alpha) (m : ℤ)
            (hfact :
              RootClauseBGammaFacts M (max (max (max C Ccap) (max Ccaps Clam)) (max (max Cflu CannP) (1 : ℝ))) Cann Cind
                (stepOneC1 d Cedos (1 : ℝ) Citer (kb + (1 : ℕ))) Crg)
            (halpha1 : alpha < (1 : ℝ)) (Ecap : { E : ℝ // (1 : ℝ) ≤ E })
            (hstate : ∀ (m : ℤ), Frozen.Section3.inductionState M m Ecap) (omega : Cutoff.CutoffSample d) (n L : ℤ)
            (hnm : n ≤ m) (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d) (Kg Kh : ℝ)
            (hsol : IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m) u h g)
            (hgHol : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2 : ℝ) Kg g) (x : Vec d) (hKg : (0 : ℝ) ≤ Kg)
            (hKh : (0 : ℝ) ≤ Kh) (hzm : triadicLatticePoint n (offGridLatticeIndex n x) ∈ openCubeSet (originCube d m))
            (hgL2 : MemLp g (2 : ENNReal) (normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
            (hgW :
              MemLp (Gagliardo.gagliardoKernel stepOneS (2 : ENNReal) g) (2 : ENNReal)
                (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))))
            (hoscfun :
              ∀ (n' kc : ℤ),
                n ≤ n' →
                  n' ≤ kc →
                    kc ≤ m →
                      ((3 : ℝ) ^ (-n') *
                          normalizedL2On (truncatedWindow (triadicLatticePoint n (offGridLatticeIndex n x)) m n')
                            fun (y : Vec d) =>
                            u.toFun y -
                              volumeAverage (truncatedWindow (triadicLatticePoint n (offGridLatticeIndex n x)) m n')
                                u.toFun) ≤
                        Cosc * Real.rpow (3 : ℝ) ((1 / 2 : ℝ) * stepSixExponent alpha n m) *
                            ((3 : ℝ) ^ (-kc) *
                              normalizedL2On (truncatedWindow (triadicLatticePoint n (offGridLatticeIndex n x)) m kc)
                                fun (y : Vec d) =>
                                u.toFun y -
                                  volumeAverage (truncatedWindow (triadicLatticePoint n (offGridLatticeIndex n x)) m kc)
                                    u.toFun) +
                          Cosc * Real.rpow (3 : ℝ) ((1 / 2 : ℝ) * stepSixExponent alpha n m) *
                            (edFinalDataG M (edBoundaryCbd d Cb C kb) (Kg * stepFourGagliardoConst d stepOneS) m +
                              edBoundaryDataHPrinted d Cb C kb Kh m))
            (kc : ℤ) (hkhi : kc + (1 : ℤ) ≤ m - (1 : ℤ)) (np : ℤ) (hjlo : n + (4 : ℤ) ≤ np + (1 : ℤ)),
            let B : ℕ :=
              (stepThreeBadSet M (stepOneDelta C1 alpha) n m (triadicLatticePoint n (offGridLatticeIndex n x)) omega).card;
            ∀ (hcard : (↑B : ℝ) ≤ stepOneDelta C1 alpha * ((↑(m - n).toNat : ℝ) + (1 : ℝ)))
              (hgapHi : m - (kc + (1 : ℤ)) ≤ (↑B : ℤ) + (1 : ℤ)) (hgapLo : np + (1 : ℤ) - n ≤ (↑B : ℤ) + (4 : ℤ))
              (hgapStrict : np + (2 : ℤ) ≤ kc)
              (hlamkc :
                stepSevenCgLamInv (originCube d kc)
                    (parentRebasedFamily M L (kc + (1 : ℤ))
                      (wellPlacedCentre (triadicLatticePoint n (offGridLatticeIndex n x)) m kc)
                      (triadicLatticePoint n (offGridLatticeIndex n x)) omega)
                    stepSevenCgS ≤
                  Klam * (↑(Annealed.sigmaBar M (kc + (1 : ℤ))) : ℝ)⁻¹),
              let CBraw : ℝ := (2 : ℝ) * (↑d : ℝ) * ((Ccaps * stepOneEp (stepOneDelta C1 alpha)) ^ (2 : ℕ) + (1 : ℝ));
              ∀
                (hcapsj :
                  StepSevenLambdaCaps (originCube d (np + (1 : ℤ)))
                    (fluxCorrectedCoeffFamily M L (np + (1 : ℤ)) (originCube d (np + (1 : ℤ)))
                      (Cutoff.translateCutoffSample (triadicLatticePoint n (offGridLatticeIndex n x)) omega))
                    (↑(Annealed.sigmaBar M (np + (1 : ℤ))) : ℝ) CBraw)
                (hCBraw0 : (0 : ℝ) ≤ CBraw) (hCBle : CBraw ≤ CBu)
                (hCWGle : edFinalDataOscW M (edBoundaryCbd d Cb C kb) * stepFourGagliardoConst d stepOneS ≤ CWGu)
                (hCWG0 : (0 : ℝ) ≤ edFinalDataOscW M (edBoundaryCbd d Cb C kb) * stepFourGagliardoConst d stepOneS)
                (hsigmaJ : (0 : ℝ) < (↑(Annealed.sigmaBar M (np + (1 : ℤ))) : ℝ))
                (hdataHP0 : (0 : ℝ) ≤ edBoundaryDataHPrinted d Cb C kb Kh m) (hC1dim : (2 : ℝ) * (↑d : ℝ) + (2 : ℝ) ≤ C1)
                (hdeltaEq : stepOneDelta C1 alpha ≤ C1⁻¹ * ((1 : ℝ) - alpha))
                (hoscHi0 :
                  (0 : ℝ) ≤
                    (cubeScaleFactor (originCube d kc))⁻¹ *
                      normalizedL2On (truncatedWindow (triadicLatticePoint n (offGridLatticeIndex n x)) m kc)
                        fun (y : Vec d) =>
                        u.toFun y -
                          volumeAverage (truncatedWindow (triadicLatticePoint n (offGridLatticeIndex n x)) m kc) u.toFun)
                (hsigmaPos : (0 : ℝ) < (↑(Annealed.sigmaBar M m) : ℝ))
                (hGpres :
                  (0 : ℝ) ≤
                    (↑(Annealed.sigmaBar M m) : ℝ) *
                      edFinalDataG M (edBoundaryCbd d Cb C kb) (Kg * stepFourGagliardoConst d stepOneS) m)
                (hgate :
                  (fun (y : Vec d) => triadicLatticePoint n (offGridLatticeIndex n x) + y) ''
                      openCubeSet (originCube d np) ⊆
                    openCubeSet (originCube d m)),
                (√M.nu *
                    normalizedL2On (truncatedWindow (offGridCentre n x) m (n + (1 : ℤ))) fun (y : Vec d) =>
                      √(vecNormSq (u.grad y))) ≤
                  max PG PF * Real.rpow (3 : ℝ) (((1 : ℝ) - alpha) * ((↑m : ℝ) - (↑n : ℝ))) *
                    ((√M.nu * normalizedL2On (openCubeSet (originCube d m)) fun (y : Vec d) => √(vecNormSq (u.grad y))) +
                        √(↑(Annealed.sigmaBar M m) : ℝ)⁻¹ * Real.rpow (3 : ℝ) ((↑m : ℝ) / (2 : ℝ)) * Kg +
                      √(↑(Annealed.sigmaBar M m) : ℝ) * Real.rpow (3 : ℝ) ((↑m : ℝ) / (2 : ℝ)) * Kh) := by
  intro d instance1 Crg C Ccap Cann Cb Citer Cosc kb hCosc Ccaps Clam Klam hKlam Cflu K1 K2 CannP Cind Cch hCch hend CdispC hCdispC hdisp hCbd hCWH CBu CWGu Ctru hCtru0 PG PF Cedos C1 M alpha halpha0 m hfact halpha1 Ecap hstate omega n L hnm u h g Kg Kh hsol hgHol x hKg hKh hzm hgL2 hgW hoscfun kc hkhi np hjlo B hcard hgapHi hgapLo hgapStrict hlamkc CBraw hcapsj hCBraw0 hCBle hCWGle hCWG0 hsigmaJ hdataHP0 hC1dim hdeltaEq hoscHi0 hsigmaPos hGpres hgate
  -- GATE branch: the gated Caccioppoli, no `S`
  obtain ⟨v, hval, hgradv, heqv⟩ :=
    exists_stepSevenCaccGateSolution (n' := np) (mf := np + 1) M L
      (originCube d (np + 1)) omega hgate hsol
  have hforcec := forceBesovRegularity_stepSevenCacc_gate (n' := np) hgate hgL2 hgW
  have hoscG := hoscfun np kc (by omega) (by omega) (by omega)
  rw [edFinalDataG_add_boundary_eq_dataOsc (M := M) (edBoundaryCbd d Cb C kb) Kg
      (stepFourGagliardoConst d stepOneS) m
      (edBoundaryDataHPrinted d Cb C kb Kh m),
    ← cubeScaleFactor_originCube_inv d kc] at hoscG
  have hdataOsc0 : (0 : ℝ) ≤ 1 * (((Annealed.sigmaBar M m : ℝ))⁻¹ *
      ((Annealed.sigmaBar M m : ℝ) *
        edFinalDataG M (edBoundaryCbd d Cb C kb)
          (Kg * stepFourGagliardoConst d stepOneS) m) +
      edBoundaryDataHPrinted d Cb C kb Kh m) := by
    rw [one_mul]
    have h1 : (0 : ℝ) ≤ ((Annealed.sigmaBar M m : ℝ))⁻¹ *
        ((Annealed.sigmaBar M m : ℝ) *
          edFinalDataG M (edBoundaryCbd d Cb C kb)
            (Kg * stepFourGagliardoConst d stepOneS) m) :=
      mul_nonneg (inv_nonneg.mpr hsigmaPos.le) hGpres
    linarith only [h1, hdataHP0]
  have hgradG := hdisp M L (np + 1) m n np (originCube d (np + 1)) omega u v
    hval hgradv hgate (by omega) heqv hforcec hC1dim halpha0.le halpha1.le hnm
    hdeltaEq (by omega) hcard hCosc hCBraw0 hoscHi0 hdataOsc0 hcapsj hoscG
  have hCgRaw0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
      stepSevenCaccConst CdispC (originCube d np)
        (Support.fluxCorrectedCoeffFamily M L (np + 1) (originCube d (np + 1))
          (Cutoff.translateCutoffSample
            (Support.triadicLatticePoint n (offGridLatticeIndex n x)) omega)) *
      (Cosc * Real.sqrt (256 / 63 * CBraw) + 1) := by
    have h1 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have h2 : (0 : ℝ) ≤ stepSevenCaccConst CdispC (originCube d np)
        (Support.fluxCorrectedCoeffFamily M L (np + 1) (originCube d (np + 1))
          (Cutoff.translateCutoffSample
            (Support.triadicLatticePoint n (offGridLatticeIndex n x)) omega)) :=
      stepSevenCaccConst_nonneg _ _ _
    have h3 : (0 : ℝ) ≤ Cosc * Real.sqrt (256 / 63 * CBraw) + 1 := by
      have h4 := mul_nonneg hCosc (Real.sqrt_nonneg (256 / 63 * CBraw))
      linarith only [h4]
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hCestG : rootClauseBWellPlacedPrefactor d Cch
      (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
        stepSevenCaccConst CdispC (originCube d np)
          (Support.fluxCorrectedCoeffFamily M L (np + 1) (originCube d (np + 1))
            (Cutoff.translateCutoffSample
              (Support.triadicLatticePoint n (offGridLatticeIndex n x)) omega)) *
        (Cosc * Real.sqrt (256 / 63 * CBraw) + 1)) Klam Ctru
      (edFinalDataOscW M (edBoundaryCbd d Cb C kb) *
        stepFourGagliardoConst d stepOneS)
      (boundaryCWH d Cb C kb) (rootClauseBDataMConst d CBraw) ≤ max PG PF := by
    have hCgle := gateBranchCg_le_uniform d (np := np) hCdispC hsigmaJ hCosc
      hCBraw0 hCBle hcapsj
    have hpre := rootClauseBWellPlacedPrefactor_mono d hCch.le hCgRaw0 hKlam.le
      hCtru0 hCWG0 hCWH (rootClauseBDataMConst_nonneg d CBraw)
      hCgle hCWGle le_rfl (rootClauseBDataMConst_mono d hCBle)
    exact le_trans hpre (le_max_left PG PF)
  exact hend M m Ecap (hstate m) hfact.ltHalf L omega u h hzm le_rfl hnm
    (by omega) (by omega) (by omega) hsol hgL2 hgW hKg hKh
    (rootClauseBDataBConst_nonneg d) hKlam.le hCgRaw0 hCbd
    (rootClauseBDataMConst_nonneg d CBraw) hCWH hdataHP0
    (stepSevenCaccDataM_nonneg _ _ hforcec) hC1dim halpha0.le halpha1.le
    hdeltaEq hcard hlamkc
    (rootClauseB_dataB_coarseFrame (by omega) hKg hgHol hgL2 hgW)
    (rootClauseB_dataM_gate (hstate m) hfact.ltHalf le_rfl (by omega) hgate hKg
      hCBraw0 hgHol hgL2 hgW hcapsj)
    (le_of_eq (edBoundaryDataHPrinted_eq_boundaryCWH_mul d Cb C kb Kh m))
    hgradG hCestG


/-- **The boundary three-leg display centre, almost surely** — the fine-scale
dichotomy executed; no gate, no shell, no region hypothesis.  See the module
docstring. -/
theorem rootClauseB_display_wellPlaced_final_floor (d : ℕ) [NeZero d] (hd : d ≠ 0)
    (cstar Crg : ℝ) (hcstar : 0 < cstar) (hCrg : 0 < Crg) :
    ∃ (Cfl Citer Cest : ℝ) (k : ℕ),
      1 ≤ Cfl ∧ 0 ≤ Cest ∧ 11 ≤ k ∧
      ∀ Cedos : ℝ, Cfl ≤ Cedos →
        ∃ gamma0 : ℝ, 0 < gamma0 ∧
          ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
            ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - Crg * Real.sqrt M.gamma →
              ∀ m : ℤ,
                ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                  ∀ n L : ℤ, n ≤ m → m ≤ L →
                    RootWindowPayload M (stepOneC1 d Cedos 1 Citer k) alpha n m omega →
                      ∀ (u h : H1Function (openCubeSet (originCube d m)))
                        (g : Vec d → Vec d) (Kg Kh : ℝ),
                        Support.IsDirichletSolutionOn
                            (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                            (originCube d m) u h g →
                        Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
                            (1 / 2) Kg g →
                        Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
                            (1 / 2) Kh h.grad →
                        (∀ y ∈ openCubeSet (originCube d m),
                          ‖h.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) →
                        Support.HasGradientOn (openCubeSet (originCube d m))
                          h.toFun h.grad →
                        ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                          Real.sqrt M.nu *
                              Support.normalizedL2On
                                (truncatedWindow (offGridCentre n x) m (n + 1))
                                (fun y => Real.sqrt (vecNormSq (u.grad y)))
                            ≤ Cest *
                                Real.rpow (3 : ℝ)
                                  ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
                              (Real.sqrt M.nu *
                                  Support.normalizedL2On
                                    (openCubeSet (originCube d m))
                                    (fun y => Real.sqrt (vecNormSq (u.grad y))) +
                                Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                                Real.sqrt (Annealed.sigmaBar M m : ℝ) *
                                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
  classical
  obtain ⟨C, Ccap, Cann, Cb, Cflo, Citer, Cosc, kb, hC, hCcap, hCann, hCb, hCflo,
    hCosc, hk10, hoscprod⟩ := exists_rootClauseBOsc_boundary_floor d hd
  obtain ⟨Ccaps, hCcaps, hcapsprod⟩ := ae_stepSevenLambdaCaps_merged d
  obtain ⟨Clam, Klam, hClam, hKlam, hlamprod⟩ := ae_stepSevenClampLambdaSlot_merged d
  obtain ⟨Cflu, Afl, K1, K2, hCflu, hAfl, hK1, hK2, hflushprod⟩ :=
    ae_stepSevenFlushBound_merged d
  obtain ⟨CannP, hCannP, hpinmain⟩ := ae_shellEpsPin_merged d
  obtain ⟨CflP, hCflP, hpinprod⟩ := hpinmain Afl hAfl
  obtain ⟨Cind, hCind6, -, hind⟩ :=
    Algsuperdiff.Section4.Provider.GoodEvents.exists_allScalesInductionState_ge d 0
  obtain ⟨Cch, hCch, hend⟩ := rootClauseB_display_wellPlaced_of_hgrad d
  obtain ⟨CdispC, hCdispC, hdisp⟩ := exists_stepSevenGradientWithShom_gate_of_caps d
  have hCindpos : (0 : ℝ) < Cind := by linarith only [hCind6]
  have hCbd : (0 : ℝ) ≤ edBoundaryCbd d Cb C kb := edBoundaryCbd_nonneg d Cb hC.le kb
  have hCWH : (0 : ℝ) ≤ boundaryCWH d Cb C kb := boundaryCWH_nonneg d Cb hC.le kb
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  set Cmax : ℝ := max (max (max C Ccap) (max Ccaps Clam)) (max (max Cflu CannP) 1)
    with hCmaxDef
  have hCmaxpos : (0 : ℝ) < Cmax :=
    lt_of_lt_of_le hC (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_left _ _)))
  set CBu : ℝ := rootClauseBCapsUniform d Ccaps with hCBuDef
  have hCBu : (0 : ℝ) ≤ CBu := rootClauseBCapsUniform_nonneg d Ccaps
  set CWGu : ℝ := rootClauseBOscWUniform (edBoundaryCbd d Cb C kb) *
    stepFourGagliardoConst d stepOneS with hCWGuDef
  have hCWGu0 : (0 : ℝ) ≤ CWGu := by
    rw [hCWGuDef]
    exact mul_nonneg (rootClauseBOscWUniform_nonneg hCbd)
      (stepFourGagliardoConst_nonneg d _)
  set Ctru : ℝ := rootClauseBTopCtr d (rootClauseBDataBConst d) with hCtruDef
  have hCtru0 : (0 : ℝ) ≤ Ctru := rootClauseBTopCtr_nonneg d _
  -- the two branch prefactor caps
  set PG : ℝ := rootClauseBWellPlacedPrefactor d Cch
    (rootClauseBCg d (rootClauseBCaccUniform CdispC CBu) Cosc CBu) Klam Ctru
    CWGu (boundaryCWH d Cb C kb) (rootClauseBDataMConst d CBu) with hPGdef
  set PF : ℝ := rootClauseBWellPlacedPrefactor d Cch
    (stepSevenFlushCg d K1 K2 Cosc) Klam Ctru
    CWGu (boundaryCWH d Cb C kb + 1) 1 with hPFdef
  have hCgU0 : (0 : ℝ) ≤ rootClauseBCg d (rootClauseBCaccUniform CdispC CBu) Cosc CBu :=
    rootClauseBCg_nonneg d (rootClauseBCaccUniform_nonneg _ _) hCosc
  have hPG0 : (0 : ℝ) ≤ PG := by
    rw [hPGdef]
    exact rootClauseBWellPlacedPrefactor_nonneg d hCch.le hCgU0 hKlam.le hCtru0
      hCWGu0 hCWH (rootClauseBDataMConst_nonneg d CBu)
  refine ⟨max Cflo CflP, Citer, max PG PF, kb + 1,
    le_trans hCflo (le_max_left _ _), le_trans hPG0 (le_max_left _ _),
    by omega, ?_⟩
  intro Cedos hfloor
  have hfloorO : Cflo ≤ Cedos := le_trans (le_max_left _ _) hfloor
  have hfloorP : CflP ≤ Cedos := le_trans (le_max_right _ _) hfloor
  set C1 : ℝ := stepOneC1 d Cedos 1 Citer (kb + 1) with hC1Def
  have hC1two : (2 : ℝ) ≤ C1 := two_le_stepOneC1 d Cedos 1 Citer (kb + 1)
  have hC1pos : (0 : ℝ) < C1 := by linarith only [hC1two]
  obtain ⟨gamma0, hgamma0, hfacts⟩ :=
    exists_rootClauseBGammaFacts d (C := Cmax) (Cann := Cann) (Cind := Cind)
      (C1 := C1) (Crg := Crg) hcstar hCmaxpos hCann hCindpos hC1pos hCrg
  refine ⟨min gamma0 ((Crg / 2) ^ (2 : ℕ)), lt_min hgamma0 (by positivity), ?_⟩
  intro M hcs hgammale alpha halpha0 halpha m
  obtain ⟨stage_hgammaCrg, stage_hfact, stage_hg0, stage_halpha1, stage_hregC, stage_hregCap, stage_hregCaps, stage_hregLam, stage_hregFlu, stage_hregAnnP, stage_hsmall⟩ :=
    @rootClauseBWellPlacedFloor_comparisonBounds3 (d) (cstar) (Crg) (hCrg) (C) (Ccap) (Cann) (Citer) (kb) (hC) (hCcap) (Ccaps) (hCcaps) (Clam) (hClam) (Cflu) (hCflu) (CannP) (hCannP) (Cind) (Cedos) (gamma0) (hfacts) (M) (hcs) (hgammale) (alpha) (halpha0) (halpha)
  have hgammaCrg : M.gamma ≤ (Crg / 2) ^ (2 : ℕ) := stage_hgammaCrg
  have hfact := stage_hfact
  have hg0 : 0 < M.gamma := stage_hg0
  have halpha1 : alpha < 1 := stage_halpha1
  have hregC : M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) := stage_hregC
  have hregCap : M.gamma ≤ Ccap⁻¹ * Disorder.cstar M ^ (10 : ℕ) := stage_hregCap
  have hregCaps : M.gamma ≤ Ccaps⁻¹ * Disorder.cstar M ^ (10 : ℕ) := stage_hregCaps
  have hregLam : M.gamma ≤ Clam⁻¹ * Disorder.cstar M ^ (10 : ℕ) := stage_hregLam
  have hregFlu : M.gamma ≤ Cflu⁻¹ * Disorder.cstar M ^ (10 : ℕ) := stage_hregFlu
  have hregAnnP : M.gamma ≤ CannP⁻¹ * Disorder.cstar M ^ (10 : ℕ) := stage_hregAnnP
  have hsmall := stage_hsmall
  obtain ⟨Ecap, -, -, hstate⟩ := hind M hfact.regimeInd
  obtain ⟨stage_hdeltamem, stage_h2gamma, stage_hsrange, stage_hsmallFlu, stage_haeOsc, stage_haeCaps, stage_haeLam⟩ :=
    @rootClauseBWellPlacedFloor_comparisonBounds1 (d) (by infer_instance) (cstar) (Crg) (hCrg) (C) (Ccap) (Cann) (Cb) (Cflo) (Citer) (Cosc) (kb) (hoscprod) (Ccaps) (hcapsprod) (Clam) (Klam) (hlamprod) (Cflu) (CannP) (Cind) (Cedos) (hfloorO) (hC1two) (M) (alpha) (halpha0) (halpha) (m) (hgammaCrg) (hfact) (hg0) (halpha1) (hregC) (hregCap) (hregCaps) (hregLam) (hsmall) (Ecap) (hstate)
  have hdeltamem := stage_hdeltamem
  have h2gamma : 2 * M.gamma ≤ 1 - alpha := stage_h2gamma
  have hsrange : stepOneS ∈ Set.Icc (64 * M.gamma) 1 := stage_hsrange
  have hsmallFlu : M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
      Real.rpow (stepOneS / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
        (1 / 2) := stage_hsmallFlu
  have haeOsc := stage_haeOsc
  have haeCaps := stage_haeCaps
  have haeLam := stage_haeLam
  have haeFlush := hflushprod M hsrange hregFlu hsmallFlu
  have haePin := hpinprod M hregAnnP hfact.le256 Cedos Citer (kb + 1) hfloorP
    alpha halpha0 halpha1 hsmall
  filter_upwards [haeOsc, haeCaps, haeLam, haeFlush, haePin]
    with omega hOsc hCap hLam hFlush hPin
  intro n L hnm hmL hpay u h g Kg Kh hsol hgHol hhHol hsup hgradh x hx
  have hKg : (0 : ℝ) ≤ Kg := holderHalf_const_nonneg hgHol
  have hKh : (0 : ℝ) ≤ Kh := holderHalf_const_nonneg hhHol
  have hv : offGridLatticeIndex n x ∈ Support.latticeCubeSet d n m :=
    offGridLatticeIndex_mem_of_mem_cube n hx
  have hzm : Support.triadicLatticePoint n (offGridLatticeIndex n x) ∈
      openCubeSet (originCube d m) := offGridCentre_mem_openCubeSet n hx
  obtain ⟨hgL2, hgW⟩ := memLp_pair_of_holderHalf hd1 hKg hgHol
  obtain ⟨-, hhW⟩ := memLp_pair_of_holderHalf hd1 hKh hhHol
  have hbudgetW := hpay.2.2.1
  have hwin : (14 : ℤ) ≤ m - n := hpay.2.1
  have hcard := (hbudgetW _ hv).2.2.1
  have hoscfun := hOsc L n (offGridLatticeIndex n x) hmL hwin hv hpay u h g Kg Kh
    hKg hKh hsol hgHol hhHol hsup hgradh
  -- the scale selection
  obtain ⟨j, kk, hjlo, hjk, hkhi, hgapLo, hgapHi, hgoodj, hgoodk⟩ :=
    exists_rootClauseBCapScales hbudgetW hv
  obtain ⟨kc, rfl⟩ : ∃ kc : ℤ, kk = kc + 1 := ⟨kk - 1, by ring⟩
  obtain ⟨np, rfl⟩ : ∃ np : ℤ, j = np + 1 := ⟨j - 1, by ring⟩
  set B : ℕ := (stepThreeBadSet M (stepOneDelta C1 alpha) n m
    (Support.triadicLatticePoint n (offGridLatticeIndex n x)) omega).card
    with hBdef
  -- the strict gap `np + 2 ≤ kc`
  have hdelta4 : stepOneDelta C1 alpha ≤ 1 / 4 := by
    have hC1four : (4 : ℝ) ≤ C1 := by
      have h2d := two_mul_dim_le_stepOneC1 d Cedos 1 Citer (kb + 1)
      have hdr : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
      rw [hC1Def]
      linarith only [h2d, hdr]
    have hval : stepOneDelta C1 alpha = C1⁻¹ * (1 - alpha) := rfl
    have hinv : C1⁻¹ ≤ 1 / 4 := by
      rw [inv_le_comm₀ hC1pos (by norm_num)]
      linarith only [hC1four]
    have hinv0 : (0 : ℝ) ≤ C1⁻¹ := inv_nonneg.mpr hC1pos.le
    rw [hval]
    calc C1⁻¹ * (1 - alpha) ≤ C1⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (by linarith only [halpha0]) hinv0
      _ = C1⁻¹ := mul_one _
      _ ≤ 1 / 4 := hinv
  have hgapStrict : np + 2 ≤ kc := by
    have hTn : (((m - n).toNat : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) :=
      toNat_sub_cast_real hnm
    have hcardR : (B : ℝ) ≤ (1 / 4) * (((m : ℝ) - (n : ℝ)) + 1) := by
      have h1 := hcard
      rw [hTn] at h1
      have hmn0 : (0 : ℝ) ≤ ((m : ℝ) - (n : ℝ)) + 1 := by
        have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
        linarith only [this]
      calc (B : ℝ) ≤ stepOneDelta C1 alpha * (((m : ℝ) - (n : ℝ)) + 1) := h1
        _ ≤ (1 / 4) * (((m : ℝ) - (n : ℝ)) + 1) :=
            mul_le_mul_of_nonneg_right hdelta4 hmn0
    have hlo : ((np + 1 - n : ℤ) : ℝ) ≤ (B : ℝ) + 4 := by exact_mod_cast hgapLo
    have hhi : ((m - (kc + 1) : ℤ) : ℝ) ≤ (B : ℝ) + 1 := by exact_mod_cast hgapHi
    have hwinR : (14 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by exact_mod_cast hwin
    have hgapR : (1 : ℝ) < ((kc - np : ℤ) : ℝ) := by
      push_cast at hlo hhi ⊢
      linarith only [hlo, hhi, hwinR, hcardR]
    have : (1 : ℤ) < kc - np := by exact_mod_cast hgapR
    omega
  -- shared per-branch data
  have hδIoc : stepOneDelta C1 alpha ∈ Set.Ioc (0 : ℝ) (1 / 2) := hdeltamem
  have hcapsj := hCap (np + 1) n (offGridLatticeIndex n x) hgoodj L (by omega)
  have hlamkc := hLam (kc + 1) n (offGridLatticeIndex n x) hgoodk L m (by omega)
    (by omega) hzm
  rw [show (kc + 1 - 1 : ℤ) = kc by ring] at hlamkc
  set CBraw : ℝ :=
    2 * (d : ℝ) * ((Ccaps * stepOneEp (stepOneDelta C1 alpha)) ^ 2 + 1) with hCBrawDef
  obtain ⟨hCBraw0, hCBle, hCWGle, hCWG0, hsigmaJ, hdataHP0, hC1dim, hdeltaEq, hoscHi0, hsigmaPos, hGpres, hedG0⟩ :=
    (show ((0 : ℝ) ≤ CBraw) ∧ (CBraw ≤ CBu) ∧ (edFinalDataOscW M (edBoundaryCbd d Cb C kb) *
      stepFourGagliardoConst d stepOneS ≤ CWGu) ∧ ((0 : ℝ) ≤ edFinalDataOscW M (edBoundaryCbd d Cb C kb) *
      stepFourGagliardoConst d stepOneS) ∧ ((0 : ℝ) < (Annealed.sigmaBar M (np + 1) : ℝ)) ∧ ((0 : ℝ) ≤ edBoundaryDataHPrinted d Cb C kb Kh m) ∧ (2 * (d : ℝ) + 2 ≤ C1) ∧ (stepOneDelta C1 alpha ≤ C1⁻¹ * (1 - alpha)) ∧ ((0 : ℝ) ≤ (cubeScaleFactor (originCube d kc))⁻¹ *
      normalizedL2On
        (truncatedWindow (Support.triadicLatticePoint n (offGridLatticeIndex n x))
          m kc)
        (fun y => u.toFun y -
          volumeAverage
            (truncatedWindow
              (Support.triadicLatticePoint n (offGridLatticeIndex n x)) m kc)
            u.toFun)) ∧ ((0 : ℝ) < (Annealed.sigmaBar M m : ℝ)) ∧ ((0 : ℝ) ≤ (Annealed.sigmaBar M m : ℝ) *
      edFinalDataG M (edBoundaryCbd d Cb C kb)
        (Kg * stepFourGagliardoConst d stepOneS) m) ∧ ((0 : ℝ) ≤ edFinalDataG M (edBoundaryCbd d Cb C kb)
      (Kg * stepFourGagliardoConst d stepOneS) m) from
      @rootClauseBWellPlacedFloor_comparisonBounds2 (d) (by infer_instance) (Crg) (C) (Ccap) (Cann) (Cb) (Citer) (kb) (Ccaps) (hCcaps) (Clam) (Cflu) (CannP) (Cind) (hCbd) (hCWH) (hCBuDef) (hCWGuDef) (Cedos) (M) (alpha) (m) (hfact) (n) (u) (Kg) (Kh) (x) (hKg) (hKh) (kc) (np) (hδIoc) (hCBrawDef))
  by_cases hgate : (fun y => Support.triadicLatticePoint n (offGridLatticeIndex n x) +
      y) '' openCubeSet (originCube d np) ⊆ openCubeSet (originCube d m)
  · exact @rootClauseB_gatedCaccioppoliBound (d) (by infer_instance) (Crg) (C) (Ccap) (Cann) (Cb) (Citer) (Cosc) (kb) (hCosc) (Ccaps) (Clam) (Klam) (hKlam) (Cflu) (K1) (K2) (CannP) (Cind) (Cch) (hCch) (hend) (CdispC) (hCdispC) (hdisp) (hCbd) (hCWH) (hCtru0) (Cedos) (M) (alpha) (halpha0) (m) (hfact) (halpha1) (Ecap) (hstate) (omega) (n) (L) (hnm) (u) (h) (g) (Kg) (Kh) (hsol) (hgHol) (x) (hKg) (hKh) (hzm) (hgL2) (hgW) (hoscfun) (kc) (hkhi) (np) (hjlo) (hcard) (hgapHi) (hgapLo) (hgapStrict) (hlamkc) (hcapsj) (hCBraw0) (hCBle) (hCWGle) (hCWG0) (hsigmaJ) (hdataHP0) (hC1dim) (hdeltaEq) (hoscHi0) (hsigmaPos) (hGpres) (hgate)
  · exact @rootClauseB_energyWindowBound (d) (by infer_instance) (Crg) (C) (Ccap) (Cann) (Cb) (Citer) (Cosc) (kb) (hCosc) (Ccaps) (Clam) (Klam) (hKlam) (Cflu) (Afl) (K1) (K2) (hK1) (hK2) (CannP) (Cind) (Cch) (hCch) (hend) (CdispC) (hCbd) (hCWH) (hd1) (hCtru0) (Cedos) (M) (alpha) (halpha0) (m) (hfact) (halpha1) (Ecap) (hstate) (h2gamma) (omega) (hFlush) (hPin) (n) (L) (hnm) (hmL) (u) (h) (g) (Kg) (Kh) (hsol) (hgHol) (hhHol) (hsup) (x) (hKg) (hKh) (hzm) (hgL2) (hgW) (hhW) (hoscfun) (kc) (hkhi) (np) (hjlo) (hgoodj) (hcard) (hgapHi) (hgapLo) (hgapStrict) (hδIoc) (hlamkc) (hCWGle) (hCWG0) (hdataHP0) (hC1dim) (hdeltaEq) (hoscHi0) (hedG0) (hgate)
end

end Algsuperdiff.Section4.Provider.Regularity
