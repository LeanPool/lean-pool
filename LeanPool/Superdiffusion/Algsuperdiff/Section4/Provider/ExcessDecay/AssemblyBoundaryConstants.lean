/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AssemblyEnergyLeg
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ReindexComposed
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RecutAtoms

/-!
# Shared boundary assembly constants

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

/-- Shared constant package for the boundary assembly and its error-weighted variant. -/
theorem assemblyBoundaryConstants :
    ∀ (d : ℕ) [inst : NeZero d],
      ∃ (CE : ℝ) (_ : (0 : ℝ) < CE) (_ :
        ∀ (M : ABKModel d),
          ∀ s ∈ Set.Icc ((64 : ℝ) * M.gamma) (1 : ℝ),
            M.gamma ≤ CE⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
              M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                  (s / (8 : ℝ)).rpow (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2 : ℝ) →
                ∀ (hs : (0 : ℝ) < s) (n : ℤ) (z : Vec d),
                  ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                    (Cutoff.CutoffSample d)),
                    omega ∈
                        Frozen.Section4.goodEventAt M (cgEllipLowerConstant d) (n + (3 : ℤ)) z
                          ⟨s / (8 : ℝ),
                            (by positivity)⟩
                          (1 / 2 : ℝ) →
                      ∀ (L : ℤ),
                        n + (3 : ℤ) ≤ L →
                          fluxCorrectedErrorRepresentative M L (n + (3 : ℤ))
                              ⟨s / (8 : ℝ),
                                (by positivity)⟩
                              (Cutoff.translateCutoffSample z omega) ≤
                            CE * (1 / 2 : ℝ))
        (CB : ℝ) (KE : ℝ) (_ : (0 : ℝ) < CB) (_ :
        ∀ (M : ABKModel d),
          ∀ s ∈ Set.Icc ((64 : ℝ) * M.gamma) (1 : ℝ),
            M.gamma ≤ CB⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
              M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                  (s / (8 : ℝ)).rpow (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2 : ℝ) →
                ∀ (hs : (0 : ℝ) < s) (L m n : ℤ),
                  m ≤ L →
                    n + (3 : ℤ) ≤ m →
                      ∀ (x z : Vec d),
                        x ∈ openCubeSet (originCube d m) →
                          (fun (y : Vec d) => x + y) '' openCubeSet (originCube d n) ⊆
                              (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (1 :
                                ℤ))) ∩
                                openCubeSet (originCube d m) →
                            ∀ᵐ (omega :
                              Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                                (Cutoff.CutoffSample d)),
                              omega ∈
                                  Frozen.Section4.goodEventAt M (cgEllipLowerConstant d) (n + (3 :
                                    ℤ)) z
                                    ⟨s / (8 : ℝ),
                                      (by positivity)⟩
                                    (1 / 2 : ℝ) →
                                ∀ (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d
                                  → Vec d) (S : ℝ),
                                  IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L
                                    omega).toCoeffField
                                      (originCube d m) u hdat g →
                                    MemLp g (2 : ENNReal) (normalizedVolumeMeasureOn (openCubeSet
                                      (originCube d m))) →
                                      MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal) g) (2 :
                                        ENNReal)
                                          (normalizedGagliardoMeasureOn (openCubeSet (originCube d
                                            m))) →
                                        MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal)
                                          hdat.grad) (2 : ENNReal)
                                            (normalizedGagliardoMeasureOn (openCubeSet (originCube
                                              d m))) →
                                          |volumeAverage
                                                  ((fun (y : Vec d) => wellPlacedCentre x m (n +
                                                    (2 : ℤ)) + y) ''
                                                    openCubeSet (originCube d (n + (2 : ℤ))))
                                                  fun (y : Vec d) => u.toFun y - hdat.toFun y| ≤
                                              S →
                                            ∀
                                              (hsubx :
                                                translateSet x (openCubeSet (originCube d n)) ⊆
                                                  openCubeSet (originCube d m)),
                                              Ch03.h1EnergyNormOnCube (originCube d n)
                                                  (parentRebasedFamily M L (n + (3 : ℤ)) x z omega)
                                                  (H1Function.untranslate x
                                                    (u.restrict (isOpen_translateSet_openCubeSet x
                                                      n) hsubx)) ≤
                                                KE *
                                                  (√(↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) *
                                                              Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ))
                                                                : ℝ)) *
                                                            (eLpNorm
                                                                (fun (y : Vec d) =>
                                                                  u.toFun y -
                                                                    volumeAverage
                                                                      ((fun (y' : Vec d) => z +
                                                                        y') ''
                                                                          openCubeSet (originCube
                                                                            d (n + (3 : ℤ))) ∩
                                                                        openCubeSet (originCube d
                                                                          m))
                                                                      u.toFun)
                                                                (2 : ENNReal)
                                                                (normalizedVolumeMeasureOn
                                                                  ((fun (y' : Vec d) => z + y') ''
                                                                      openCubeSet (originCube d (n
                                                                        + (3 : ℤ))) ∩
                                                                    openCubeSet (originCube d
                                                                      m)))).toReal +
                                                          √(↑(Annealed.sigmaBar M (n + (3 : ℤ))) :
                                                            ℝ) *
                                                              Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ))
                                                                : ℝ)) *
                                                            S +
                                                        s.rpow (-3 : ℝ) * √(↑(Annealed.sigmaBar M
                                                          (n + (3 : ℤ))) : ℝ)⁻¹ *
                                                            Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ))
                                                              : ℝ)) *
                                                          (normalizedGagliardoESeminormOn
                                                              ((fun (y' : Vec d) => z + y') ''
                                                                  openCubeSet (originCube d (n +
                                                                    (3 : ℤ))) ∩
                                                                openCubeSet (originCube d m))
                                                              s g).toReal +
                                                      s.rpow (-2 : ℝ) * √(↑(Annealed.sigmaBar M (n
                                                        + (3 : ℤ))) : ℝ) *
                                                          Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) :
                                                            ℝ)) *
                                                        (normalizedGagliardoESeminormOn
                                                            ((fun (y' : Vec d) => z + y') ''
                                                                openCubeSet (originCube d (n + (3
                                                                  : ℤ))) ∩
                                                              openCubeSet (originCube d m))
                                                            s hdat.grad).toReal +
                                                    s.rpow (-2 : ℝ) * √(↑(Annealed.sigmaBar M (n +
                                                      (3 : ℤ))) : ℝ) *
                                                      (eLpNorm hdat.grad (2 : ENNReal)
                                                          (normalizedVolumeMeasureOn
                                                            ((fun (y' : Vec d) => z + y') ''
                                                                openCubeSet (originCube d (n + (3
                                                                  : ℤ))) ∩
                                                              openCubeSet (originCube d
                                                                m)))).toReal))
         (_ :
        (0 : ℝ) ≤ √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ))
        (_ :
        (0 : ℝ) ≤
          √((2 : ℝ) * (↑d : ℝ) * ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) ^ (2 :
            ℕ) + (1 : ℝ))) *
              (√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) +
            (2 : ℝ) * ((2 : ℝ) * (↑d : ℝ) * ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 :
              ℝ))) ^ (2 : ℕ) + (1 : ℝ))))
        (_ : (0 : ℝ) ≤ (3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d)
        (_ :
        (0 : ℝ) ≤
          (3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d * (216 : ℝ) * (√((192 : ℝ) * (↑d
            : ℝ)) * (3 : ℝ) * KE))
        (_ :
        (0 : ℝ) ≤
          (3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d * (1944 : ℝ) *
            ((√((2 : ℝ) * (↑d : ℝ) * ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) ^
              (2 : ℕ) + (1 : ℝ))) *
                  (√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) +
                (2 : ℝ) *
                  ((2 : ℝ) * (↑d : ℝ) * ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ)))
                    ^ (2 : ℕ) + (1 : ℝ)))) *
              (besovGagliardoConstant d * (gagliardoWindowConst d * windowMoveConst d))))
        (_ : (0 : ℝ) ≤ interiorCorrectionConst d * (gagliardoWindowConst d * windowMoveConst d))
          (_ :
        (0 : ℝ) ≤
          (9 : ℝ) * (CE * (1 / 2 : ℝ)) *
            ((3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d * (216 : ℝ) * (√((192 : ℝ) *
              (↑d : ℝ)) * (3 : ℝ) * KE))),
        (0 : ℝ) ≤
          CE * (1 / 2 : ℝ) *
            ((3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d * (216 : ℝ) *
              (√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * KE)) := by
  classical
  intro d _
  obtain ⟨CE, hCEpos, hCE⟩ := ae_errorRepresentative_le_harmonicSlot_addThree d
  obtain ⟨CB, KE, hCBpos, hKEpos, hEnergyLeg⟩ :=
    ae_h1EnergyNormOnCube_boundary_le_anchorLegs d
  obtain ⟨hkappa, hb0, hcg, hA1, hA2, hA3, hCE2, hCE3⟩ :=
    comparison_constants_nonneg d CE KE
      (gagliardoWindowConst d * windowMoveConst d) hCEpos.le hKEpos.le
      (mul_nonneg (gagliardoWindowConst_pos d).le (windowMoveConst_pos d).le)
  exact ⟨CE, hCEpos, hCE, CB, KE, hCBpos, hEnergyLeg, hkappa, hb0, hcg, hA1, hA2, hA3,
    hCE2, hCE3⟩

end

end Algsuperdiff.Section4.Provider.ExcessDecay
