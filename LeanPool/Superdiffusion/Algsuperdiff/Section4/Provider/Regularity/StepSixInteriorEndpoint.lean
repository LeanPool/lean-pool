/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourFinalEndpoint

/-!
# StepSixInteriorEndpoint

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

/-- For `z = 3^n v ∈ □_{m-1}` and every `n ≤ n' ≤ m' ≤ m`,

```text
   3^{-n'} ‖u - (u)_{U_{n'}}‖_{L²(U_{n'})}
     ≤ (C_out + C_out²) 3^{(1/2)(1-α)(m-n)} 3^{-m'} ‖u - (u)_{U_{m'}}‖_{L²(U_{m'})}
       + (C_out + C_out²) 3^{(1/2)(1-α)(m-n)} ( dataG + 0 ) .
```

No Step-4 decay hypothesis and no Step-5 conditional: the whole chain runs off
the harmonic-approximation anchor and the Step-3 supply events. -/
theorem edFinal_oscillationHolderBound_interior (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C Cann : ℝ, 0 < C ∧ 0 < Cann ∧ ∃ k₀ : ℕ, 3 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k → 2 ≤ k →
        ∃ Cout Citer : ℝ, 0 < Cout ∧ 0 ≤ Citer ∧
          ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
            Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
            M.gamma < 1 / 2 →
            M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
            M.gamma ≤ Cann⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
            M.gamma ≤ 1 / 256 →
            M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                Real.rpow (stepOneS / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                  (C⁻¹ * stepOneS ^ (4 : ℕ)) →
            ∀ (Cedos Cannp alpha : ℝ), alpha ≤ 1 →
              stepOneDelta (stepOneC1 d Cedos Cannp Citer k) alpha ∈
                  Set.Ioc (0 : ℝ) (1 / 2) →
              M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                  Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                    stepOneEp (stepOneDelta (stepOneC1 d Cedos Cannp Citer k) alpha) →
              edFinalEpsCoeff d C k stepOneS *
                    (Cann *
                      stepOneEp (stepOneDelta (stepOneC1 d Cedos Cannp Citer k) alpha)) ≤
                  (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * (k : ℝ)) →
              ∀ L m n : ℤ, m ≤ L → m ≤ m0 → (14 : ℤ) ≤ m - n →
                ∀ v : Fin d → ℤ, v ∈ Support.latticeCubeSet d n m →
                  Support.triadicLatticePoint n v ∈
                      openCubeSet (originCube d (m - 1)) →
                    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                      GoodScaleWindows M stepOneSEighth
                          (stepOneDelta (stepOneC1 d Cedos Cannp Citer k) alpha)
                          stepOneSEighth_pos n m omega →
                      (((stepThreeBadSet M
                            (stepOneDelta (stepOneC1 d Cedos Cannp Citer k) alpha) n m
                            (Support.triadicLatticePoint n v) omega).card : ℝ)) ≤
                          stepOneDelta (stepOneC1 d Cedos Cannp Citer k) alpha *
                            (((m : ℝ) - (n : ℝ)) + 1) →
                      ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                        (g : Vec d → Vec d) (Kg : ℝ), 0 ≤ Kg →
                        IsDirichletSolutionOn
                            (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                            (originCube d m) u hdat g →
                        MemLp g 2
                            (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
                        MemLp (Gagliardo.gagliardoKernel stepOneS 2 g) 2
                            (normalizedGagliardoMeasureOn
                              (openCubeSet (originCube d m))) →
                        MemLp (Gagliardo.gagliardoKernel stepOneS 2 hdat.grad) 2
                            (normalizedGagliardoMeasureOn
                              (openCubeSet (originCube d m))) →
                        HolderSeminormBoundOn (openCubeSet (originCube d m))
                            (1 / 2) Kg g →
                        ∀ (c : ℤ → ℝ) (slope : ℤ → Vec d),
                          (∀ j : ℤ, j ≤ m →
                            IsAffineMinimizer
                              (stepThreeWindow (Support.triadicLatticePoint n v) m j)
                              u.toFun (c j) (slope j)) →
                          ∀ n' m' : ℤ, n ≤ n' → n' ≤ m' → m' ≤ m →
                            (3 : ℝ) ^ (-n') *
                                normalizedL2On
                                  (stepThreeWindow
                                    (Support.triadicLatticePoint n v) m n')
                                  (fun x => u.toFun x -
                                    volumeAverage
                                      (stepThreeWindow
                                        (Support.triadicLatticePoint n v) m n')
                                      u.toFun) ≤
                              (Cout + Cout * Cout) *
                                  Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                                  ((3 : ℝ) ^ (-m') *
                                    normalizedL2On
                                      (stepThreeWindow
                                        (Support.triadicLatticePoint n v) m m')
                                      (fun x => u.toFun x -
                                        volumeAverage
                                          (stepThreeWindow
                                            (Support.triadicLatticePoint n v) m m')
                                          u.toFun)) +
                                (Cout + Cout * Cout) *
                                  Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                                  (edFinalDataG M (edFinalDeltaConst d C k stepOneS)
                                      (Kg * stepFourGagliardoConst d stepOneS) m + 0) := by
  classical
  obtain ⟨C, Cann, hC, hCann, k₀, hk₀, hres⟩ :=
    edFinal_oscillationIterationResult_interior d hd
  refine ⟨C, Cann, hC, hCann, k₀, hk₀, ?_⟩
  intro k hk hk2
  obtain ⟨Cout, Citer, hCout, hCiter, hres'⟩ := hres k hk hk2
  refine ⟨Cout, Citer, hCout, hCiter, ?_⟩
  intro M m0 Ecap hS hgamma hregime hregimeAnn hgamma256 hfund Cedos Cannp alpha halpha
    hdelta hsmall hgate L m n hmL hmm0 hwin v hv hzin
  filter_upwards [hres' M m0 Ecap hS hgamma hregime hregimeAnn hgamma256 hfund Cedos
    Cannp alpha halpha hdelta hsmall hgate L m n hmL hmm0 hwin v hv hzin] with omega hom
  intro hgood hBz u hdat g Kg hKg0 hsol hgL2 hgW hhW hhol c slope hmin n' m' hn' hn'm' hm'm
  have hbase := hom hgood hBz u hdat g Kg hKg0 hsol hgL2 hgW hhW hhol c slope hmin n' m'
    hn' hn'm' hm'm
  have hoscHi : (0 : ℝ) ≤ (3 : ℝ) ^ (-m') *
      normalizedL2On (stepThreeWindow (Support.triadicLatticePoint n v) m m')
        (fun x => u.toFun x -
          volumeAverage (stepThreeWindow (Support.triadicLatticePoint n v) m m')
            u.toFun) :=
    mul_nonneg (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) (normalizedL2On_nonneg _ _)
  have hdataG : (0 : ℝ) ≤ edFinalDataG M (edFinalDeltaConst d C k stepOneS)
      (Kg * stepFourGagliardoConst d stepOneS) m :=
    edFinalDataG_nonneg hgamma
      (edFinalDeltaConst_nonneg d hC.le k (by rw [stepOneS]; norm_num))
      (mul_nonneg hKg0 (stepFourGagliardoConst_nonneg d stepOneS)) m
  exact oscillationHolderBound_of_iterationResult d hCout.le hCiter halpha
    (by omega : n ≤ m) hoscHi hdataG le_rfl hbase

end

end Algsuperdiff.Section4.Provider.Regularity
