/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AssemblyComposedErrorWeighted

/-!
# AssemblyComposed

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

/-- The unweighted boundary clause follows by capping the representative error. -/
theorem exists_boundaryClauseComposed_honest (d : ℕ) [NeZero d] :
    ∃ C Cfin : ℝ, 0 < C ∧ 0 < Cfin ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ x z : Vec d,
          x ∈ openCubeSet (originCube d m) →
          (fun y => x + y) '' openCubeSet (originCube d n) ⊆
              ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
                openCubeSet (originCube d m) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (Support.cgEllipLowerConstant d) (n + 3) z
                  ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
                ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d) (S : ℝ),
                  Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (originCube d m) u hdat g →
                  MemLp g 2 (Support.normalizedVolumeMeasureOn
                    (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 g) 2
                    (Support.normalizedGagliardoMeasureOn
                      (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
                    (Support.normalizedGagliardoMeasureOn
                      (openCubeSet (originCube d m))) →
                  |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
                      openCubeSet (originCube d (n + 2)))
                      (fun y => u.toFun y - hdat.toFun y)| ≤ S →
                  ∀ (v : H1Function
                      ((fun y => x + y) '' openCubeSet (originCube d n)))
                    (w : H10Function
                      ((fun y => x + y) '' openCubeSet (originCube d n))),
                    Support.IsWeaklyHarmonicOn
                        ((fun y => x + y) '' openCubeSet (originCube d n)) v →
                    (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                    (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                      (eLpNorm (fun y => u.toFun y - v.toFun y) 2
                        (Support.normalizedVolumeMeasureOn
                          ((fun y => x + y) ''
                            openCubeSet (originCube d n)))).toReal ≤
                        Cfin *
                          (Real.rpow s (-(4 : ℝ)) *
                              Support.fluxCorrectedErrorRepresentative M L (n + 3)
                                ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega) *
                              (eLpNorm (fun y => u.toFun y -
                                  volumeAverage ((((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m))) u.toFun) 2
                                (Support.normalizedVolumeMeasureOn
                                  ((((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m))))).toReal +
                            Real.rpow s (-(7 : ℝ)) *
                              ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
                              Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                              (Support.normalizedGagliardoESeminormOn
                                ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))) s g).toReal +
                            Real.rpow s (-(6 : ℝ)) *
                              Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                              (Support.normalizedGagliardoESeminormOn
                                ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))) s hdat.grad).toReal +
                            Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                              (eLpNorm hdat.grad 2
                                (Support.normalizedVolumeMeasureOn
                                  ((((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m))))).toReal +
                            Real.rpow s (-(4 : ℝ)) *
                              Support.fluxCorrectedErrorRepresentative M L (n + 3)
                                ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega) * S) := by
  obtain ⟨Cweighted, K, hCweighted, hK, hweighted⟩ :=
    exists_boundaryClauseComposed_honest_errorWeighted d
  obtain ⟨CE, hCE, hcap, _⟩ := assemblyBoundaryConstants d
  refine ⟨max Cweighted CE, K * max 1 (CE * (1 / 2 : ℝ)),
    lt_of_lt_of_le hCweighted (le_max_left _ _),
    mul_pos hK (lt_of_lt_of_le zero_lt_one (le_max_left _ _)), ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm x z hx hgeom
  have hregimeWeighted : M.gamma ≤ Cweighted⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    hregime.trans (mul_le_mul_of_nonneg_right
      (inv_anti₀ hCweighted (le_max_left _ _)) (by positivity))
  have hregimeCap : M.gamma ≤ CE⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    hregime.trans (mul_le_mul_of_nonneg_right
      (inv_anti₀ hCE (le_max_right _ _)) (by positivity))
  filter_upwards [hweighted M s hsrange hregimeWeighted hsmall hs L m n hmL hnm x z hx hgeom,
    hcap M s hsrange hregimeCap hsmall hs n z] with omega hweighted hcap
  intro hmem u hdat g S hsol hgL2 hgW hhW hmean v w hharm hval hgrad
  have hbound := hweighted hmem u hdat g S hsol hgL2 hgW hhW hmean v w hharm hval hgrad
  have herrorCap := hcap hmem L (le_trans hnm hmL)
  let representativeError := fluxCorrectedErrorRepresentative M L (n + 3)
    ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega)
  have herror0 : 0 ≤ representativeError := fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hS0 : 0 ≤ S := (abs_nonneg _).trans hmean
  have hsigma : 0 < (Annealed.sigmaBar M (n + 3) : ℝ) :=
    (Annealed.sigmaBar M (n + 3)).2
  let parentWindow := ((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
    openCubeSet (originCube d m)
  let oscillationLeg := Real.rpow s (-(4 : ℝ)) * representativeError *
    (eLpNorm (fun y => u.toFun y - volumeAverage parentWindow u.toFun) 2
      (Support.normalizedVolumeMeasureOn parentWindow)).toReal
  let forcingLeg := Real.rpow s (-(7 : ℝ)) * (Annealed.sigmaBar M (n + 3) : ℝ)⁻¹ *
    Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
    (Support.normalizedGagliardoESeminormOn parentWindow s g).toReal
  let gradientLeg := Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
    (Support.normalizedGagliardoESeminormOn parentWindow s hdat.grad).toReal
  let flatLeg := Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
    (eLpNorm hdat.grad 2 (Support.normalizedVolumeMeasureOn parentWindow)).toReal
  let meanLeg := Real.rpow s (-(4 : ℝ)) * representativeError * S
  have hbase : (eLpNorm (fun y => u.toFun y - v.toFun y) 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => x + y) '' openCubeSet (originCube d n)))).toReal ≤
      K * (oscillationLeg + forcingLeg + gradientLeg +
      representativeError * flatLeg + meanLeg) := by
    convert hbound using 1
    dsimp only [oscillationLeg, forcingLeg, gradientLeg, flatLeg, meanLeg,
      representativeError, parentWindow]
    ring
  have hresult := five_leg_bound_errorWeighted hK.le herrorCap
    (show 0 ≤ oscillationLeg by dsimp [oscillationLeg]; positivity)
    (show 0 ≤ forcingLeg by dsimp [forcingLeg]; positivity)
    (show 0 ≤ gradientLeg by dsimp [gradientLeg]; positivity)
    (show 0 ≤ flatLeg by dsimp [flatLeg]; positivity)
    (show 0 ≤ meanLeg by dsimp [meanLeg]; positivity) hbase
  simpa only [oscillationLeg, forcingLeg, gradientLeg, flatLeg, meanLeg,
    representativeError, parentWindow] using hresult

end

end Algsuperdiff.Section4.Provider.ExcessDecay
