/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourFinalBudget

/-!
# StepFourFinalEndpoint

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `e.oscillation.iteration.result` with `hstep4` GONE

## What this module is

`StepFiveConcreteEndpoint.stepFiveConcreteOscillationResult_of_stepFourDecay`
is the Step-5 endpoint with `hstep4` as **the one conditional input**.  This
module is its interior-branch sibling with **`hstep4` gone**: the Step-4 decay
is supplied by `StepFourFinalIteration.stepFourDecay_interior_pinned` off the
frozen statements and the supply events, and the two budgets by
`StepFourFinalBudget`.

* the `ε`-slot carries the collapse's coefficient `C_ε`,
  absorbed by the generic re-run at `C_iter = 2C₀(k+1+C_ε)`;
* the `δ`-family is the interior `g`-leg alone, at the root's own Hölder datum
  `K_g` rather than the `W^{1/2,∞}` seminorm it dominates;
* `dataH = 0` — the interior clause carries no `∇h` leg and no boundary
  indicator, so the whole `1_{z ∉ □_{m-1}}` half of the printed `dataH` slot is
  absent.
  This is the pay-off of gating at `z ∈ □_{m-1}`: on that half of the lattice
  the printed indicator is `0` and the interior route reproduces it exactly.

## What is NOT in this module

The boundary branch (`z ∉ □_{m-1}`), where's general-clause route with its `∇h`
legs's `excessDecay_oneStep_anchored` join are needed, and where's mismatch (3)
(the flat ungated `‖∇h‖_∞` leg with no decay in `n`) is still open.

## References

* ABK26, `t.regularity` Steps 4--5.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

/-- **`e.oscillation.iteration.result` on the interior branch, `hstep4` GONE.**

For `z = 3^n v ∈ □_{m-1}` and every `n ≤ n' ≤ m' ≤ m`,

```text
   3^{-n'} ‖u - (u)_{U_{n'}}‖_{L²(U_{n'})}
     ≤ C exp( C₁^{-1} C_iter (1-α)(m-n) ) ( 3^{-m'} ‖u - (u)_{U_{m'}}‖ + C·dataG )
       + C exp( C₁^{-1} C_iter (1-α)(m-n) ) · 0 ,
   dataG = 4 C_δ 3^{m/2} σ_m^{-1} ( K_g C_{S4.4}(d,1/4) ) / (1 - 3^{-(1/2-γ)}) ,
```

with `U = stepThreeWindow z m`, `C_iter = 2C₀(k+1+C_ε)`, and NO Step-4 decay
hypothesis: the excess decay is produced from the harmonic-approximation anchor
and the Step-3 supply events. -/
theorem edFinal_oscillationIterationResult_interior (d : ℕ) [NeZero d] (hd : d ≠ 0) :
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
                              Cout *
                                  Real.exp
                                    ((stepOneC1 d Cedos Cannp Citer k)⁻¹ * Citer *
                                      stepSixExponent alpha n m) *
                                  ((3 : ℝ) ^ (-m') *
                                      normalizedL2On
                                        (stepThreeWindow
                                          (Support.triadicLatticePoint n v) m m')
                                        (fun x => u.toFun x -
                                          volumeAverage
                                            (stepThreeWindow
                                              (Support.triadicLatticePoint n v) m m')
                                            u.toFun) +
                                    Cout *
                                      edFinalDataG M (edFinalDeltaConst d C k stepOneS)
                                        (Kg * stepFourGagliardoConst d stepOneS) m) +
                                Cout *
                                  Real.exp
                                    ((stepOneC1 d Cedos Cannp Citer k)⁻¹ * Citer *
                                      stepSixExponent alpha n m) * 0 := by
  classical
  obtain ⟨C, Cann, hC, hCann, k₀, hk₀, hpin⟩ := stepFourDecay_interior_pinned d hd
  refine ⟨C, Cann, hC, hCann, k₀, hk₀, ?_⟩
  intro k hk hk2
  obtain ⟨Cout, Citer, hCout, hCiter, hiter⟩ :=
    oscillationIterationResult_of_stepFourDecay_generic d hd k hk2
      (edFinalEpsCoeff_nonneg d hC.le k (s := stepOneS) (by rw [stepOneS]; norm_num))
  refine ⟨Cout, Citer, hCout, hCiter, ?_⟩
  intro M m0 Ecap hS hgamma hregime hregimeAnn hgamma256 hfund Cedos Cannp alpha halpha
    hdelta hsmall hgate L m n hmL hmm0 hwin v hv hzin
  set delta := stepOneDelta (stepOneC1 d Cedos Cannp Citer k) alpha with hdeltadef
  set z := Support.triadicLatticePoint n v with hzdef
  have hnm : n ≤ m := by omega
  have hCdel : (0 : ℝ) ≤ edFinalDeltaConst d C k stepOneS :=
    edFinalDeltaConst_nonneg d hC.le k (by rw [stepOneS]; norm_num)
  have hCeps : (0 : ℝ) ≤ edFinalEpsCoeff d C k stepOneS :=
    edFinalEpsCoeff_nonneg d hC.le k (by rw [stepOneS]; norm_num)
  filter_upwards [hpin k hk M m0 Ecap hS hregime hregimeAnn hgamma256 hfund delta hdelta
    hsmall hgate L m hmL hmm0 z hzin n] with omega hstep
  intro hgood hBz u hdat g Kg hKg0 hsol hgL2 hgW hhW hhol c slope hmin n' m' hn' hn'm' hm'm
  have hKgT : (0 : ℝ) ≤ Kg * stepFourGagliardoConst d stepOneS :=
    mul_nonneg hKg0 (stepFourGagliardoConst_nonneg d stepOneS)
  have hzm : z ∈ openCubeSet (originCube d m) :=
    Algsuperdiff.Section4.Provider.ExcessDecay.openCubeSet_originCube_subset_of_le
      (by omega : m - 1 ≤ m) hzin
  have hu : MemLp u.toFun 2 (volume.restrict (stepThreeWindow z m m)) :=
    u.memL2.mono_measure
      (Measure.restrict_mono (truncatedWindow_subset_domain z m m) le_rfl)
  exact hiter Cedos Cannp alpha halpha n m (by omega) (stepThreeWindow z m)
    (iterationWindowFamily_stepThreeWindow z m hzm) u.toFun hu c slope hmin
    (stepThreeBadSet M delta n m z omega) hBz
    (fun j => edFinalEpsCoeff d C k stepOneS * stepFiveEps M j z delta omega)
    (fun j => edFinalDelta M (edFinalDeltaConst d C k stepOneS)
      (Kg * stepFourGagliardoConst d stepOneS) j)
    (fun j _ _ => mul_nonneg hCeps (stepFiveEps_nonneg M j z delta omega))
    (fun j _ _ => edFinalDelta_nonneg hCdel hKgT j)
    (sum_Icc_edFinalEps_le hCeps hdelta.1.le hwin hgood hv)
    (edFinalDataG M (edFinalDeltaConst d C k stepOneS)
      (Kg * stepFourGagliardoConst d stepOneS) m) 0
    (edFinalDataG_nonneg hgamma hCdel hKgT m) le_rfl
    (by
      have h := sum_Icc_top_edFinalDelta_le hS hgamma hCdel hKgT hnm hmm0
      linarith only [h])
    (fun j hj1 hj2 hj3 => hstep u hdat g Kg hKg0 hsol hgL2 hgW hhW hhol c slope hmin j
      hj1 hj2 hj3)
    n' m' hn' hn'm' hm'm

end

end Algsuperdiff.Section4.Provider.Regularity
