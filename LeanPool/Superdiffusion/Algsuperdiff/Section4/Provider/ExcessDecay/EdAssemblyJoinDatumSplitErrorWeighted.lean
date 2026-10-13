/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EdAssemblyAnchorErrorWeighted
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EdAssemblyOneStep
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryCompose
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryHonestRegated
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepEvenBoundFinal
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepInterior
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddClassCornerProducer
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddCompose
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RebaseEpsilon

/-!
# EdAssemblyJoinDatumSplitErrorWeighted

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

/-! ## 1. The join at the honest boundary binders, at the error-weighted anchor -/

/-- **The anchored one-step at every scale-`n` window, with the printed
datum leg, at the error-weighted anchor.**

The anchored one-step with the printed datum leg, with the
anchor re-pointed at the error-weighted statement: the remainder's `B.toReal`
expansion is the error-weighted five-leg block (the fifth leg the
`𝓔`-multiplied flat `∇h` average), and everything else — the window
disjunction, the contraction, the remainder weight and the datum leg — is that
theorem's, character for character. -/
theorem excessDecay_oneStep_anchored_datumSplit_errorWeighted (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C Cb : ℝ, 0 < C ∧ 0 ≤ Cb ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
              (C⁻¹ * s ^ (4 : ℕ)) →
        ∀ hs : 0 < s,
        ∀ delta : ℝ, delta ≤ 1 → delta ≤ 64 * (C ^ (2 : ℕ))⁻¹ * s ^ (6 : ℕ) →
        ∀ L m n : ℤ, m ≤ L → n - 2 + 3 ≤ m →
          ∀ x z : Vec d,
            x ∈ truncatedWindow z m (n - 3) →
            z ∈ openCubeSet (originCube d m) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (cgEllipLowerConstant d) (n - 2 + 3) z
                  ⟨s / 8, by linarith only [hs]⟩ (s / 8 * Real.sqrt delta) →
                ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                  IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (originCube d m) u hdat g →
                  MemLp g 2
                      (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 g) 2
                      (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
                      (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                  ∀ (v : H1Function ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                          openCubeSet (originCube d (n - 2))))
                    (w : H10Function ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                          openCubeSet (originCube d (n - 2)))),
                    IsWeaklyHarmonicOn ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                      openCubeSet (originCube d (n - 2))) v →
                    (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                    (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                    ∀ Kh : ℝ, 0 ≤ Kh →
                    ((fun y => x + y) '' openCubeSet (originCube d (n - 2)) ⊆
                        openCubeSet (originCube d m) ∨
                      (∃ (i : Fin d) (V v₁ : Vec d → ℝ) (cl : ℝ) (Al : Vec d),
                        (MeetsUpperFace x m (n - 2) i ∨
                          MeetsLowerFace x m (n - 2) i) ∧
                        MemLp v.toFun 2 (volume.restrict (truncatedWindow x m n)) ∧
                        MemLp V 2
                          (volume.restrict (reflectedWindow x m (n - 2))) ∧
                        V =ᵐ[volume.restrict (truncatedWindow x m (n - 2))]
                          (fun y => v.toFun y - affineLift x cl Al y - v₁ y) ∧
                        (∀ᵐ y ∂(volume.restrict (truncatedWindow x m (n - 2))),
                          |v₁ y| ≤ datumResidualBound d n Kh) ∧
                        (∀ l : Fin d, MeetsUpperFace x m (n - 2) l →
                          ∀ y ∈ reflectedWindow x m (n - 2),
                            V (coordFaceReflection
                              ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) ∧
                        (∀ l : Fin d, MeetsLowerFace x m (n - 2) l →
                          ∀ y ∈ reflectedWindow x m (n - 2),
                            V (coordFaceReflection
                              (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) ∧
                        HarmonicOnNhd
                          (V ∘
                            (Schauder.toEuc.symm :
                              EuclideanSpace ℝ (Fin d) → Vec d))
                          ((Schauder.toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
                            reflectedWindow x m (n - 2)))) →
                    ∀ k : ℕ, 3 ≤ k →
                      affineExcess (truncatedWindow x m (n - (k : ℤ))) u.toFun ≤
                        taylorContractionConst d * max (schauderWindowConst d) Cb
                            * windowRatioConst d 2
                            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
                            * affineExcess (truncatedWindow x m n) u.toFun
                          + triangleRemainderConst d
                              (max (schauderWindowConst d) Cb) k
                            * ((3 : ℝ) ^ (-n) *
                              (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
                                (C * Real.rpow s (-(4 : ℝ)) *
                                    fluxCorrectedErrorRepresentative M L (n - 2 + 3)
                                      ⟨s / 8, by linarith only [hs]⟩
                                      (Cutoff.translateCutoffSample z omega) *
                                    ((MeasureTheory.eLpNorm
                                        (fun y => u.toFun y -
                                          HCPolySupport.volumeAverage
                                            (((fun y' => z + y') ''
                                                openCubeSet
                                                  (originCube d (n - 2 + 3))) ∩
                                              openCubeSet (originCube d m))
                                            u.toFun) 2
                                        (normalizedVolumeMeasureOn
                                          (((fun y' => z + y') ''
                                              openCubeSet
                                                (originCube d (n - 2 + 3))) ∩
                                            openCubeSet
                                              (originCube d m)))).toReal +
                                      Real.rpow s (-(3 / 2 : ℝ)) *
                                          Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                                        ‖HCPolySupport.volumeAverageVec
                                            (((fun y' => z + y') ''
                                                openCubeSet
                                                  (originCube d (n - 2 + 2))) ∩
                                              openCubeSet (originCube d m))
                                            hdat.grad‖) +
                                  C * Real.rpow s (-(7 : ℝ)) *
                                      (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ *
                                      Real.rpow (3 : ℝ)
                                        ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
                                    (normalizedGagliardoESeminormOn
                                      (((fun y' => z + y') ''
                                          openCubeSet
                                            (originCube d (n - 2 + 3))) ∩
                                        openCubeSet (originCube d m)) s g).toReal +
                                  C * Real.rpow s (-(6 : ℝ)) *
                                      Real.rpow (3 : ℝ)
                                        ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
                                    (normalizedGagliardoESeminormOn
                                      (((fun y' => z + y') ''
                                          openCubeSet
                                            (originCube d (n - 2 + 3))) ∩
                                        openCubeSet (originCube d m)) s
                                      hdat.grad).toReal +
                                  C * Real.rpow s (-(6 : ℝ)) *
                                      fluxCorrectedErrorRepresentative M L (n - 2 + 3)
                                        ⟨s / 8, by linarith only [hs]⟩
                                        (Cutoff.translateCutoffSample z omega) *
                                      Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                                    ‖HCPolySupport.volumeAverageVec
                                        (((fun y' => z + y') ''
                                            openCubeSet
                                              (originCube d (n - 2 + 2))) ∩
                                          openCubeSet (originCube d m))
                                        hdat.grad‖)))
                          + taylorContractionConst d
                              * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
                              * (boundaryDatumLegConst d
                                  (max (schauderWindowConst d) Cb) k * Kh) := by
  classical
  obtain ⟨Cb, hCb, hbd⟩ := excessDecay_oneStep_boundary_metSet_datumSplit_regated d hd
  obtain ⟨C, hC, hanchor⟩ := exists_oneStepAnchorBound_errorWeighted d
  refine ⟨C, Cb, hC, hCb, ?_⟩
  intro M s hsrange hregime hfund hs delta hdelta1 hprice L m n hmL hnm x z hxz hz
  have hs1 : s ≤ 1 := hsrange.2
  have hxm : x ∈ openCubeSet (originCube d m) :=
    truncatedWindow_subset_domain z m (n - 3) hxz
  have hnm1 : n - 1 ≤ m := by omega
  have hnm2 : n - 2 ≤ m := by omega
  have hmn : n - 2 < m := by omega
  have hrep : s / 8 * Real.sqrt delta ≤ C⁻¹ * s ^ (4 : ℕ) :=
    excessDecayDelta_repriced hC hs.le hprice
  have hmovsub : (fun y => wellPlacedCentre x m (n - 2) + y) ''
      openCubeSet (originCube d (n - 2)) ⊆ openCubeSet (originCube d m) :=
    image_add_wellPlacedCentre_subset_openCubeSet x hnm2
  filter_upwards [hanchor M s hsrange hregime hfund hs L m n hmL hnm x z hxz hz]
    with omega ha
  intro hmem u hdat g hsol hgL2 hgW hhW v w hharmv hval hgradv Kh hKh hwin k hk
  have hE0 : (0 : ℝ) ≤ affineExcess (truncatedWindow x m n) u.toFun :=
    affineExcess_nonneg _ _
  obtain ⟨B, hB, hharm, hexp⟩ := ha u hdat g hsol hgL2 hgW hhW v w hharmv hval hgradv
  have hR := ENNReal.toReal_nonneg.trans hexp
  have hu : MemLp u.toFun 2 (volume.restrict (truncatedWindow x m n)) :=
    u.memL2.mono_measure
      (Measure.restrict_mono (truncatedWindow_subset_domain x m n) le_rfl)
  have hTnn : (0 : ℝ) ≤ taylorContractionConst d
      * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) :=
    mul_nonneg (taylorContractionConst_nonneg d)
      (Real.rpow_nonneg (zpow_pos (by norm_num) _).le _)
  rcases hwin with hcube |
    ⟨i, V, v₁, cl, Al, hmet, hv, hvR, hVae, hv₁, hupv, hlowv, hharmclass⟩
  · have hmain := excessDecay_oneStep_interior_of_weaklyHarmonic_regated hd hk hs hs1 hdelta1 hxm hnm1
      hcube hu hharmv hmem hB hrep hharm
    refine oneStepConclusionKh_mono d (le_max_left _ _) hE0 hR hKh ?_
    have hpad : (0 : ℝ) ≤ taylorContractionConst d
        * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
        * (boundaryDatumLegConst d (schauderWindowConst d) k * Kh) :=
      mul_nonneg hTnn (mul_nonneg
        (boundaryDatumLegConst_nonneg d (schauderWindowConst_nonneg d) k) hKh)
    have hrem := oneStepRemainder_mono d (schauderWindowConst_nonneg d) k n hexp
    simp only [mul_zero] at hmain
    linarith only [hmain, hrem, hpad]
  · have huv : MemLp (fun y => u.toFun y - v.toFun y) 2
        (volume.restrict (movedReplacementCube x m n)) := by
      rw [movedReplacementCube]
      exact (u.memL2.mono_measure
        (Measure.restrict_mono hmovsub le_rfl)).sub v.memL2
    have hmain := hbd hk hs hs1 hdelta1 hxm hnm1 hmn hmet hKh hu hv hvR huv hVae hv₁
      hupv hlowv hharmclass hmem hB hrep hharm
    refine oneStepConclusionKh_mono d (le_max_right _ _) hE0 hR hKh ?_
    have hrem := oneStepRemainder_mono d hCb k n hexp
    linarith only [hmain, hrem]
end

end Algsuperdiff.Section4.Provider.ExcessDecay
