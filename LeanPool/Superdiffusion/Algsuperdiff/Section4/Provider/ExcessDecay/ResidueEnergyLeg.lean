/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AssemblyEnergyLeg
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueCapCovering
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueCapWindowLegs

/-!
# ResidueEnergyLeg

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary energy leg, re-cut at the two hinges

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## What is proved

`AssemblyEnergyLeg.ae_h1EnergyNormOnCube_boundary_le_anchorLegs` prices
CoarseGraining's coefficient-energy norm on the child cube against the five
canonical legs of the boundary chain, at the anchor's geometry binder.
measured that the binder enters that proof at exactly two places:

```text
  (W)  wellPlacedCentre x m (n+2) + □_{n+2} ⊆ (z+□_{n+3}) ∩ □_m
  (P)  translateSet (wellPlacedCentre x m (n+2) − z) (cubeSet □_{n+2})
         ⊆ cubeSet □_{n+3}
```

`ae_h1EnergyNormOnCube_boundary_le_anchorLegs_atHinges` is the same statement
with `(W)` and `(P)` as binders in place of `hgeom` — a strict generalization
(the proved statement is recovered by
`image_add_wellPlacedCentre_subset_anchorWindow` and
`translateSet_cubeSet_coveringCube_subset_anchorParent`), and the only form in
which the boundary energy leg is available at the flush scale-`n` sub-cube
`K'`, which provably fails `hgeom` (`ResidueAbsorption`).

Section 1 re-cuts the one auxiliary of `AssemblyEnergyLeg` that also carried
the binder (the Euclidean `L²` transport of the boundary gradient).

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`; the boundary application.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The Euclidean `L²` transport of the boundary gradient, at hinge (W) -/

/-- **The datum pricing's crude datum leg, transported onto the anchor window,
at hinge (W).** -/
theorem normalizedEuclideanL2_datumGrad_coveringCube_atWindow
    {n m : ℤ} {x z : Vec d} {F : Vec d → Vec d}
    (hcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    (hL2W : MemLp F 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))))
    (hFcube : MemVectorL2 (cubeSet (originCube d (n + 2)))
      (fun y => F (y + wellPlacedCentre x m (n + 2)))) :
    normalizedEuclideanL2 (originCube d (n + 2))
        (fun y => F (y + wellPlacedCentre x m (n + 2))) ≤
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
        (eLpNorm F 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal := by
  classical
  set c : Vec d := wellPlacedCentre x m (n + 2) with hc
  set cov : Set (Vec d) :=
    (fun y => c + y) '' openCubeSet (originCube d (n + 2)) with hcovSet
  set W : Set (Vec d) :=
    (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)) with hW
  have hbase := normalizedEuclideanL2_le_sqrt_card_mul hFcube
  have hframe : cubeLpNorm (originCube d (n + 2)) (2 : ℝ≥0∞) (fun y => F (y + c)) =
      (eLpNorm F 2 (Support.normalizedVolumeMeasureOn cov)).toReal := by
    change (eLpNorm (fun y => F (y + c)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d (n + 2)))).toReal = _
    rw [hcovSet, eLpNorm_normalizedVolumeMeasureOn_image_add c
      (openCubeSet (originCube d (n + 2))) (by norm_num) (by norm_num),
      normalizedVolumeMeasureOn_openCubeSet]
  have hmove : (eLpNorm F 2 (Support.normalizedVolumeMeasureOn cov)).toReal ≤
      (3 : ℝ) ^ d * (eLpNorm F 2 (Support.normalizedVolumeMeasureOn W)).toReal := by
    have hb := eLpNorm_coveringCube_atWindow hcov F
    have hRHSne : ENNReal.ofReal ((3 : ℝ) ^ d) *
        eLpNorm F 2 (Support.normalizedVolumeMeasureOn W) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL2W.eLpNorm_ne_top
    have hstep := ENNReal.toReal_mono hRHSne hb
    rwa [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ d)] at hstep
  have hcard : Real.sqrt ((Fintype.card (Fin d) : ℝ)) = Real.sqrt (d : ℝ) := by
    rw [Fintype.card_fin]
  rw [hcard] at hbase
  calc normalizedEuclideanL2 (originCube d (n + 2)) (fun y => F (y + c))
      ≤ Real.sqrt (d : ℝ) * cubeLpNorm (originCube d (n + 2)) (2 : ℝ≥0∞)
          (fun y => F (y + c)) := hbase
    _ = Real.sqrt (d : ℝ) *
          (eLpNorm F 2 (Support.normalizedVolumeMeasureOn cov)).toReal := by rw [hframe]
    _ ≤ Real.sqrt (d : ℝ) *
          ((3 : ℝ) ^ d * (eLpNorm F 2 (Support.normalizedVolumeMeasureOn W)).toReal) :=
        mul_le_mul_of_nonneg_left hmove (Real.sqrt_nonneg _)
    _ = Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
          (eLpNorm F 2 (Support.normalizedVolumeMeasureOn W)).toReal := by ring

/-! ## 2. The boundary energy leg, at the two hinges -/

private theorem residueEnergyLeg_comparisonBounds1 :
    ∀ (d : ℕ) [NeZero d] (CB1 CB2 CG1 CG2 KP : ℝ) (_ : (0 : ℝ) < KP) (KR : ℝ) (_ : (0 : ℝ) < KR)
      (Pcap : ℝ)
      (_ : (0 : ℝ) ≤ Pcap) (alpha : ℝ) (_ : alpha = √((2 : ℝ) * (3 : ℝ) ^ d * (Pcap * KP)))
      (_ : (0 : ℝ) ≤ alpha) (beta sK : ℝ) (_ : sK = √KR) (_ : (0 : ℝ) ≤ √(3 / 2 : ℝ)) (M :
        ABKModel d)
      (s : ℝ) (_ : (0 : ℝ) < s) (L m n : ℤ) (x z : Vec d)
      (_ :
        (fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) '' openCubeSet (originCube d
          (n + (2 : ℤ))) ⊆
          (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (3 : ℤ))) ∩ openCubeSet
            (originCube d m))
      (_ : s ≤ (1 : ℝ)) (_ : (0 : ℝ) < (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ)) (omega :
        Cutoff.CutoffSample d)
      (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d) (S : ℝ)
      (hsubx : translateSet x (openCubeSet (originCube d n)) ⊆ openCubeSet (originCube d m))
      (_ :
        caccioppoliWithRHSPrefactor CB1 (originCube d (n + (2 : ℤ)))
            (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 : ℤ))) z omega)
              (1 / 2 : ℝ) (s / (3 : ℝ)) ≤
          Pcap)
      (_ :
        Ch02.lambdaS (originCube d (n + (2 : ℤ))) (s / (3 : ℝ))
            (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 : ℤ))) z omega) ≤
          KP * (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ))
      (_ :
        (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) *
            (Ch02.lambdaSq (originCube d (n + (2 : ℤ))) (s / (4 : ℝ))
              (Ch02.MultiscaleExponent.finite (2 : ℝ))
                (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 : ℤ))) z
                  omega))⁻¹ ≤
          KR)
      (_ :
        MemLp hdat.grad (2 : ℝ≥0∞)
          (normalizedVolumeMeasureOn
            ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
              openCubeSet (originCube d m))))
      (_ :
        MemLp (Gagliardo.gagliardoKernel s (2 : ℝ≥0∞) g) (2 : ℝ≥0∞)
          (normalizedGagliardoMeasureOn
            ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
              openCubeSet (originCube d m))))
      (_ :
        MemLp g (2 : ℝ≥0∞)
          (normalizedVolumeMeasureOn
            ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) '' openCubeSet
              (originCube d (n + (2 : ℤ))))))
      (_ :
        MemLp (Gagliardo.gagliardoKernel s (2 : ℝ≥0∞) g) (2 : ℝ≥0∞)
          (normalizedGagliardoMeasureOn
            ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) '' openCubeSet
              (originCube d (n + (2 : ℤ))))))
      (_ :
        ForceBesovRegularity (originCube d (n + (2 : ℤ))) s fun (y : Vec d) => -g (y +
          wellPlacedCentre x m (n + (2 : ℤ))))
      (hsubc :
        translateSet (wellPlacedCentre x m (n + (2 : ℤ))) (openCubeSet (originCube d (n + (2 :
          ℤ)))) ⊆
          openCubeSet (originCube d m))
      (v :
        DirichletForcedCubeSolution (originCube d (n + (2 : ℤ)))
          (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 : ℤ))) z omega) fun
            (y : Vec d) =>
          -g (y + wellPlacedCentre x m (n + (2 : ℤ))))
      (_ : dirichletBoundaryGradientField v = fun (y : Vec d) => hdat.grad (y + wellPlacedCentre x
        m (n + (2 : ℤ))))
      (_ :
        (0 : ℝ) ≤
          Ch02.lambdaS (originCube d (n + (2 : ℤ))) (s / (3 : ℝ))
            (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 : ℤ))) z omega))
      (_ :
        √(localizedCoeffEnergyValue (openCubeSet (originCube d n))
              ((parentRebasedFamily M L (n + (3 : ℤ)) x z omega).coeffOn (originCube d n))
              (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx))) ≤
          √((2 : ℝ) * (3 : ℝ) ^ d *
                  (caccioppoliWithRHSPrefactor CB1 (originCube d (n + (2 : ℤ)))
                      (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 : ℤ)))
                        z omega) (1 / 2 : ℝ)
                      (s / (3 : ℝ)) *
                    Ch02.lambdaS (originCube d (n + (2 : ℤ))) (s / (3 : ℝ))
                      (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 : ℤ)))
                        z omega))) *
              (Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ)) *
                √(normalizedL2SqOnSet (openCubeSet (originCube d (n + (2 : ℤ)))) fun (y : Vec d) =>
                    u.toFun (y + wellPlacedCentre x m (n + (2 : ℤ))) - v.toH1.toFun y)) +
            beta *
              dirichletEnergyWithRHSRHS CB2 (originCube d (n + (2 : ℤ)))
                (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 : ℤ))) z
                  omega) (s / (2 : ℝ))
                (fun (y : Vec d) => -g (y + wellPlacedCentre x m (n + (2 : ℤ)))) v)
      (_ :
        Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ)) *
            √(normalizedL2SqOnSet (openCubeSet (originCube d (n + (2 : ℤ)))) fun (y : Vec d) =>
                (H1Function.untranslate (wellPlacedCentre x m (n + (2 : ℤ)))
                        (u.restrict (isOpen_translateSet_openCubeSet (wellPlacedCentre x m (n + (2
                          : ℤ))) (n + (2 : ℤ)))
                          hsubc)).toFun
                    y -
                  v.toH1.toFun y) ≤
          Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ)) *
                  ((3 : ℝ) ^ d *
                    (eLpNorm
                        (fun (y : Vec d) =>
                          u.toFun y -
                            volumeAverage
                              ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                                ℤ))) ∩
                                openCubeSet (originCube d m))
                              u.toFun)
                        (2 : ℝ≥0∞)
                        (normalizedVolumeMeasureOn
                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                            ℤ))) ∩
                            openCubeSet (originCube d m)))).toReal) +
                Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ)) * S +
              unitMeanZeroPoincareConst d *
                ((↑d : ℝ) *
                  ((3 : ℝ) ^ d *
                    (eLpNorm hdat.grad (2 : ℝ≥0∞)
                        (normalizedVolumeMeasureOn
                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                            ℤ))) ∩
                            openCubeSet (originCube d m)))).toReal)) +
            CG1 *
              (((s / (2 : ℝ)).rpow (-(3 / 2 : ℝ)) *
                      poincareLowerEllipticityFactor (originCube d (n + (2 : ℤ)))
                        (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 :
                          ℤ))) z omega) (s / (4 : ℝ))
                        (Ch02.MultiscaleExponent.finite (2 : ℝ)) *
                    dirichletEnergyWithRHSRHS CG2 (originCube d (n + (2 : ℤ)))
                      (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 : ℤ)))
                        z omega) (s / (2 : ℝ))
                      (fun (y : Vec d) => -g (y + wellPlacedCentre x m (n + (2 : ℤ)))) v +
                  (s / (2 : ℝ)).rpow (-3 : ℝ) *
                      (Ch02.lambdaSq (originCube d (n + (2 : ℤ))) (s / (4 : ℝ))
                        (Ch02.MultiscaleExponent.finite (2 : ℝ))
                            (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 :
                              ℤ))) z omega)).rpow
                        (-1 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + (2 : ℤ))) (s
                      / (2 : ℝ))
                      fun (y : Vec d) => -g (y + wellPlacedCentre x m (n + (2 : ℤ)))) +
                negativeToL2Factor s *
                  normalizedEuclideanL2 (originCube d (n + (2 : ℤ)))
                    (dirichletBoundaryGradientField v))),
      poincareLowerEllipticityFactor (originCube d (n + (2 : ℤ)))
            (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 : ℤ))) z omega)
              (s / (4 : ℝ))
            (Ch02.MultiscaleExponent.finite (2 : ℝ)) ≤
          sK * √(↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ)⁻¹ ∧
        (Ch02.lambdaSq (originCube d (n + (2 : ℤ))) (s / (4 : ℝ)) (Ch02.MultiscaleExponent.finite
          (2 : ℝ))
                  (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 : ℤ))) z
                    omega)).rpow
              (-1 : ℝ) ≤
            KR * (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ)⁻¹ ∧
          (scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + (2 : ℤ))) (s / (2 :
            ℝ)) fun (y : Vec d) =>
                -g (y + wellPlacedCentre x m (n + (2 : ℤ)))) ≤
              besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ)) *
                (gagliardoWindowConst d *
                  (normalizedGagliardoESeminormOn
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                        openCubeSet (originCube d m))
                      s g).toReal) ∧
            normalizedEuclideanL2 (originCube d (n + (2 : ℤ))) (dirichletBoundaryGradientField v) ≤
                √(↑d : ℝ) * (3 : ℝ) ^ d *
                  (eLpNorm hdat.grad (2 : ℝ≥0∞)
                      (normalizedVolumeMeasureOn
                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                          openCubeSet (originCube d m)))).toReal ∧
              negativeToL2Factor s ≤ √(3 / 2 : ℝ) * s.rpow (-2 : ℝ) ∧
                √(localizedCoeffEnergyValue (openCubeSet (originCube d n))
                      ((parentRebasedFamily M L (n + (3 : ℤ)) x z omega).coeffOn (originCube d n))
                      (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n)
                        hsubx))) ≤
                  alpha * √(↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) *
                      (Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ)) *
                              ((3 : ℝ) ^ d *
                                (eLpNorm
                                    (fun (y : Vec d) =>
                                      u.toFun y -
                                        volumeAverage
                                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube
                                            d (n + (3 : ℤ))) ∩
                                            openCubeSet (originCube d m))
                                          u.toFun)
                                    (2 : ℝ≥0∞)
                                    (normalizedVolumeMeasureOn
                                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d
                                        (n + (3 : ℤ))) ∩
                                        openCubeSet (originCube d m)))).toReal) +
                            Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ)) * S +
                          unitMeanZeroPoincareConst d *
                            ((↑d : ℝ) *
                              ((3 : ℝ) ^ d *
                                (eLpNorm hdat.grad (2 : ℝ≥0∞)
                                    (normalizedVolumeMeasureOn
                                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d
                                        (n + (3 : ℤ))) ∩
                                        openCubeSet (originCube d m)))).toReal)) +
                        CG1 *
                          (((s / (2 : ℝ)).rpow (-(3 / 2 : ℝ)) *
                                  poincareLowerEllipticityFactor (originCube d (n + (2 : ℤ)))
                                    (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m
                                      (n + (2 : ℤ))) z omega)
                                    (s / (4 : ℝ)) (Ch02.MultiscaleExponent.finite (2 : ℝ)) *
                                dirichletEnergyWithRHSRHS CG2 (originCube d (n + (2 : ℤ)))
                                  (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n
                                    + (2 : ℤ))) z omega)
                                  (s / (2 : ℝ)) (fun (y : Vec d) => -g (y + wellPlacedCentre x m
                                    (n + (2 : ℤ)))) v +
                              (s / (2 : ℝ)).rpow (-3 : ℝ) *
                                  (Ch02.lambdaSq (originCube d (n + (2 : ℤ))) (s / (4 : ℝ))
                                        (Ch02.MultiscaleExponent.finite (2 : ℝ))
                                        (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x
                                          m (n + (2 : ℤ))) z
                                          omega)).rpow
                                    (-1 : ℝ) *
                                scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n +
                                  (2 : ℤ))) (s / (2 : ℝ))
                                  fun (y : Vec d) => -g (y + wellPlacedCentre x m (n + (2 : ℤ)))) +
                            negativeToL2Factor s *
                              normalizedEuclideanL2 (originCube d (n + (2 : ℤ)))
                                (dirichletBoundaryGradientField v))) +
                    beta *
                      dirichletEnergyWithRHSRHS CB2 (originCube d (n + (2 : ℤ)))
                        (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 :
                          ℤ))) z omega) (s / (2 : ℝ))
                        (fun (y : Vec d) => -g (y + wellPlacedCentre x m (n + (2 : ℤ)))) v := by
  intro d _ CB1 _ _ _ KP hKP KR hKR Pcap hPcap0 alpha halphadef halpha0 _ sK hsKdef hnegC0 M s hs
    L m n x z hcov hs1 hsig omega _ hdat g _ _ hprefcap hlamScap hlam4 hhL2W hgWW hgL2cov hgWcov
      hgreg hsubc v hbg hLam0 hsqrt hB4
  have hA : Real.sqrt (2 * (3 : ℝ) ^ d *
      (caccioppoliWithRHSPrefactor CB1 (originCube d (n + 2))
          (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
          (1 / 2) (s / 3) *
        Ch02.lambdaS (originCube d (n + 2)) (s / 3)
          (parentRebasedFamily M L (n + 3)
            (wellPlacedCentre x m (n + 2)) z omega))) ≤
      alpha * Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) := by
    have hprod := mul_le_mul hprefcap hlamScap hLam0 hPcap0
    have hmul : 2 * (3 : ℝ) ^ d *
        (caccioppoliWithRHSPrefactor CB1 (originCube d (n + 2))
            (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
            (1 / 2) (s / 3) *
          Ch02.lambdaS (originCube d (n + 2)) (s / 3)
            (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)) ≤
        (2 * (3 : ℝ) ^ d * (Pcap * KP)) * (Annealed.sigmaBar M (n + 3) : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hprod
        (by positivity : (0 : ℝ) ≤ 2 * (3 : ℝ) ^ d)
      calc 2 * (3 : ℝ) ^ d * _ ≤ 2 * (3 : ℝ) ^ d * (Pcap * (KP * _)) := h1
        _ = (2 * (3 : ℝ) ^ d * (Pcap * KP)) * (Annealed.sigmaBar M (n + 3) : ℝ) := by
            ring
    rw [halphadef, ← Real.sqrt_mul
      (mul_nonneg (by positivity) (mul_nonneg hPcap0 hKP.le))]
    exact Real.sqrt_le_sqrt hmul
  have hlow : poincareLowerEllipticityFactor (originCube d (n + 2))
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (s / 4) (Ch02.MultiscaleExponent.finite 2) ≤
      sK * Real.sqrt (((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹) := by
    rw [poincareLowerEllipticityFactor, hsKdef]
    exact rpow_neg_half_le_of_lower_cap
      (Ch02.lambdaSq_nonneg (originCube d (n + 2)) _ (by linarith only [hs])
        (by norm_num)) hsig hKR.le hlam4
  have hlamInv : Real.rpow (Ch02.lambdaSq (originCube d (n + 2)) (s / 4)
      (Ch02.MultiscaleExponent.finite 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega))
      (-1 : ℝ) ≤ KR * ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ :=
    rpow_neg_one_lambdaSq_le_of_lower_cap
      (Ch02.lambdaSq_finite_pos (originCube d (n + 2)) _ (by linarith only [hs])
        (by norm_num)) hsig hlam4
  have hBg : scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2))
      (s / 2) (fun y => -g (y + wellPlacedCentre x m (n + 2))) ≤
      besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) *
        (gagliardoWindowConst d *
          (Support.normalizedGagliardoESeminormOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))) s g).toReal) :=
    (scaleNormalizedPositiveBesovVectorSeminormTwo_le_of_exponent_le
      (originCube d (n + 2)) _ (by linarith only [hs]) hgreg).trans
      (besovVectorSeminormTwo_coveringCube_atWindow hcov hs hs1
        hgL2cov hgWcov hgWW)
  have hgradcube : MemVectorL2 (cubeSet (originCube d (n + 2)))
      (fun y => hdat.grad (y + wellPlacedCentre x m (n + 2))) :=
    memVectorL2_cubeSet_of_openCubeSet
      (H1Function.untranslate (wellPlacedCentre x m (n + 2))
        (hdat.restrict
          (isOpen_translateSet_openCubeSet (wellPlacedCentre x m (n + 2)) (n + 2))
          hsubc)).grad_memVectorL2
  have hHn : normalizedEuclideanL2 (originCube d (n + 2))
      (dirichletBoundaryGradientField v) ≤
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
        (eLpNorm hdat.grad 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal := by
    rw [hbg]
    exact normalizedEuclideanL2_datumGrad_coveringCube_atWindow hcov hhL2W hgradcube
  have hnegf : negativeToL2Factor s ≤
      Real.sqrt (3 / 2 : ℝ) * Real.rpow s (-(2 : ℝ)) :=
    (negativeToL2Factor_le_rpow_neg_half hs hs1).trans
      (mul_le_mul_of_nonneg_left (rpow_neg_half_le_neg_two hs hs1) hnegC0)
  -- the composed real bound, then the arithmetic
  have hmain := hsqrt.trans (add_le_add (mul_le_mul hA hB4
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _))
    (mul_nonneg halpha0 (Real.sqrt_nonneg _))) le_rfl)
  exact ⟨hlow, hlamInv, hBg, hHn, hnegf, hmain⟩

private theorem residueEnergyLeg_comparisonBounds2 :
    ∀ (d : ℕ) [NeZero d] (s : ℝ) (_ : (0 : ℝ) < s) (m n : ℤ) (x z : Vec d) (_ : s ≤ (1 : ℝ))
      (_ : n + (2 : ℤ) ≤ m) (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
      (_ : MemLp g (2 : ℝ≥0∞) (normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
      (_ :
        MemLp (Gagliardo.gagliardoKernel s (2 : ℝ≥0∞) g) (2 : ℝ≥0∞)
          (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))))
      (_ :
        MemLp (Gagliardo.gagliardoKernel s (2 : ℝ≥0∞) hdat.grad) (2 : ℝ≥0∞)
          (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))))
      (_ : MemLp hdat.grad (2 : ℝ≥0∞) (normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
      (_ : MemLp u.toFun (2 : ℝ≥0∞) (normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
      (_ :
        (volume : Set (Vec d) → ENNReal)
            ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
              openCubeSet (originCube d m)) ≠
          (0 : ℝ≥0∞))
      (_ :
        IsProbabilityMeasure
          (normalizedVolumeMeasureOn
            ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
              openCubeSet (originCube d m)))),
      MemLp hdat.grad (2 : ℝ≥0∞)
          (normalizedVolumeMeasureOn
            ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
              openCubeSet (originCube d m))) ∧
        MemLp (Gagliardo.gagliardoKernel s (2 : ℝ≥0∞) g) (2 : ℝ≥0∞)
            (normalizedGagliardoMeasureOn
              ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                openCubeSet (originCube d m))) ∧
          MemLp (Gagliardo.gagliardoKernel s (2 : ℝ≥0∞) hdat.grad) (2 : ℝ≥0∞)
              (normalizedGagliardoMeasureOn
                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                  openCubeSet (originCube d m))) ∧
            eLpNorm
                  (fun (y : Vec d) =>
                    u.toFun y -
                      volumeAverage
                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                          openCubeSet (originCube d m))
                        u.toFun)
                  (2 : ℝ≥0∞)
                  (normalizedVolumeMeasureOn
                    ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                      openCubeSet (originCube d m))) ≠
                ∞ ∧
              eLpNorm hdat.grad (2 : ℝ≥0∞)
                    (normalizedVolumeMeasureOn
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                        openCubeSet (originCube d m))) ≠
                  ∞ ∧
                MemLp g (2 : ℝ≥0∞)
                    (normalizedVolumeMeasureOn
                      ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                        openCubeSet (originCube d (n + (2 : ℤ))))) ∧
                  MemLp (Gagliardo.gagliardoKernel s (2 : ℝ≥0∞) g) (2 : ℝ≥0∞)
                      (normalizedGagliardoMeasureOn
                        ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                          openCubeSet (originCube d (n + (2 : ℤ))))) ∧
                    MemLp hdat.grad (2 : ℝ≥0∞)
                        (normalizedVolumeMeasureOn
                          ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                            openCubeSet (originCube d (n + (2 : ℤ))))) ∧
                      MemLp (Gagliardo.gagliardoKernel s (2 : ℝ≥0∞) hdat.grad) (2 : ℝ≥0∞)
                          (normalizedGagliardoMeasureOn
                            ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                              openCubeSet (originCube d (n + (2 : ℤ))))) ∧
                        (ForceBesovRegularity (originCube d (n + (2 : ℤ))) s fun (y : Vec d) =>
                            -g (y + wellPlacedCentre x m (n + (2 : ℤ)))) ∧
                          (ForceBesovRegularity (originCube d (n + (2 : ℤ))) (s / (2 : ℝ)) fun (y
                            : Vec d) =>
                              -g (y + wellPlacedCentre x m (n + (2 : ℤ)))) ∧
                            (ForceBesovRegularity (originCube d (n + (2 : ℤ))) s fun (y : Vec d) =>
                                hdat.grad (y + wellPlacedCentre x m (n + (2 : ℤ)))) ∧
                              (ForceBesovRegularity (originCube d (n + (2 : ℤ))) (s / (2 : ℝ)) fun
                                (y : Vec d) =>
                                  hdat.grad (y + wellPlacedCentre x m (n + (2 : ℤ)))) ∧
                                translateSet (wellPlacedCentre x m (n + (2 : ℤ)))
                                    (openCubeSet (originCube d (n + (2 : ℤ)))) ⊆
                                  openCubeSet (originCube d m) := by
  intro d _ s hs m n x z hs1 hnm2 u hdat g hgL2 hgW hhW hhL2m huL2m hW30 _
  have huL2W : MemLp u.toFun 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedVolumeMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW30 huL2m
  have hhL2W : MemLp hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedVolumeMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW30 hhL2m
  have hgWW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedGagliardoMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW30 hgW
  have hhWW : MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedGagliardoMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW30 hhW
  have hXfin : eLpNorm (fun y => u.toFun y -
      volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤ :=
    (huL2W.sub (memLp_const _)).eLpNorm_ne_top
  have hHfin : eLpNorm hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤ := hhL2W.eLpNorm_ne_top
  have hgL2cov := memLp_two_coveringCube_of_clause_iv (x := x) hnm2 hgL2
  have hgWcov := memLp_two_gagliardo_coveringCube_of_clause_iv (x := x) (s := s) hnm2 hgW
  have hhL2cov := memLp_two_coveringCube_of_clause_iv (x := x) hnm2 hhL2m
  have hhWcov := memLp_two_gagliardo_coveringCube_of_clause_iv (x := x) (s := s) hnm2 hhW
  have hgreg : ForceBesovRegularity (originCube d (n + 2)) s
      (fun y => -g (y + wellPlacedCentre x m (n + 2))) :=
    forceBesovRegularity_coveringCube_neg_of_clause_iv hnm2 hs hs1 le_rfl hgL2 hgW
  have hgreg2 : ForceBesovRegularity (originCube d (n + 2)) (s / 2)
      (fun y => -g (y + wellPlacedCentre x m (n + 2))) :=
    forceBesovRegularity_coveringCube_neg_of_clause_iv hnm2 hs hs1
      (by linarith only [hs]) hgL2 hgW
  have hhreg : ForceBesovRegularity (originCube d (n + 2)) s
      (fun y => hdat.grad (y + wellPlacedCentre x m (n + 2))) :=
    forceBesovRegularity_coveringCube_datumGrad_of_clause_iv hnm2 hs hs1 le_rfl hhL2m hhW
  have hhreg2 : ForceBesovRegularity (originCube d (n + 2)) (s / 2)
      (fun y => hdat.grad (y + wellPlacedCentre x m (n + 2))) :=
    forceBesovRegularity_coveringCube_datumGrad_of_clause_iv hnm2 hs hs1
      (by linarith only [hs]) hhL2m hhW
  have hsubc : translateSet (wellPlacedCentre x m (n + 2))
      (openCubeSet (originCube d (n + 2))) ⊆ openCubeSet (originCube d m) :=
    translateSet_wellPlacedCentre_subset x hnm2
  exact ⟨hhL2W, hgWW, hhWW, hXfin, hHfin, hgL2cov, hgWcov, hhL2cov, hhWcov, hgreg, hgreg2, hhreg,
    hhreg2, hsubc⟩

private theorem residueEnergyLeg_comparisonBounds3 :
    ∀ (d : ℕ) [NeZero d] (CB1 CB2 : ℝ) (_ : (0 : ℝ) < CB1) (_ : (0 : ℝ) < CB2)
      (_ : (0 : ℝ) ≤ (3 : ℝ) ^ d) (M : ABKModel d) (s : ℝ) (_ : (0 : ℝ) < s) (L m n : ℤ) (x z :
        Vec d)
      (_ : s ≤ (1 : ℝ)) (omega : Cutoff.CutoffSample d) (u hdat : H1Function (openCubeSet
        (originCube d m)))
      (g : Vec d → Vec d) (hsubx : translateSet x (openCubeSet (originCube d n)) ⊆ openCubeSet
        (originCube d m))
      (_ :
        ForceBesovRegularity (originCube d (n + (2 : ℤ))) (s / (2 : ℝ)) fun (y : Vec d) =>
          -g (y + wellPlacedCentre x m (n + (2 : ℤ))))
      (_ :
        ForceBesovRegularity (originCube d (n + (2 : ℤ))) (s / (2 : ℝ)) fun (y : Vec d) =>
          hdat.grad (y + wellPlacedCentre x m (n + (2 : ℤ))))
      (v :
        DirichletForcedCubeSolution (originCube d (n + (2 : ℤ)))
          (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 : ℤ))) z omega) fun
            (y : Vec d) =>
          -g (y + wellPlacedCentre x m (n + (2 : ℤ))))
      (_ : ∀ (y : Vec d), v.boundaryData.grad y = hdat.grad (y + wellPlacedCentre x m (n + (2 :
        ℤ))))
      (_ :
        localizedCoeffEnergyValue (openCubeSet (originCube d n))
            ((parentRebasedFamily M L (n + (3 : ℤ)) x z omega).coeffOn (originCube d n))
            (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx)) ≤
          (3 : ℝ) ^ d *
            ((2 : ℝ) *
                (caccioppoliWithRHSPrefactor CB1 (originCube d (n + (2 : ℤ)))
                    (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 : ℤ))) z
                      omega) (1 / 2 : ℝ)
                    (s / (3 : ℝ)) *
                  (Ch02.lambdaS (originCube d (n + (2 : ℤ))) (s / (3 : ℝ))
                        (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 :
                          ℤ))) z omega) *
                      Real.rpow (3 : ℝ) ((-2 : ℝ) * (↑(n + (2 : ℤ)) : ℝ)) *
                    normalizedL2SqOnSet (openCubeSet (originCube d (n + (2 : ℤ)))) fun (y : Vec d)
                      =>
                      u.toFun (y + wellPlacedCentre x m (n + (2 : ℤ))) - v.toH1.toFun y)) +
              (2 : ℝ) *
                ((18 : ℝ) ^ d *
                  dirichletEnergyWithRHSRHS CB2 (originCube d (n + (2 : ℤ)))
                      (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 : ℤ)))
                        z omega) (s / (2 : ℝ))
                      (fun (y : Vec d) => -g (y + wellPlacedCentre x m (n + (2 : ℤ)))) v ^
                    (2 : ℕ)))),
      (dirichletBoundaryGradientField v = fun (y : Vec d) => hdat.grad (y + wellPlacedCentre x m
        (n + (2 : ℤ)))) ∧
        ForceBesovRegularity (originCube d (n + (2 : ℤ))) (s / (2 : ℝ))
          (dirichletBoundaryGradientField v) ∧
          h1EnergyNormOnCube (originCube d n) (parentRebasedFamily M L (n + (3 : ℤ)) x z omega)
                (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n)
                  hsubx)) =
              √(localizedCoeffEnergyValue (openCubeSet (originCube d n))
                  ((parentRebasedFamily M L (n + (3 : ℤ)) x z omega).coeffOn (originCube d n))
                  (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n)
                    hsubx))) ∧
            (0 : ℝ) ≤
                Ch02.lambdaS (originCube d (n + (2 : ℤ))) (s / (3 : ℝ))
                  (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 : ℤ))) z
                    omega) ∧
              √(localizedCoeffEnergyValue (openCubeSet (originCube d n))
                      ((parentRebasedFamily M L (n + (3 : ℤ)) x z omega).coeffOn (originCube d n))
                      (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n)
                        hsubx))) ≤
                  √((2 : ℝ) * (3 : ℝ) ^ d *
                          (caccioppoliWithRHSPrefactor CB1 (originCube d (n + (2 : ℤ)))
                              (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2
                                : ℤ))) z omega)
                              (1 / 2 : ℝ) (s / (3 : ℝ)) *
                            Ch02.lambdaS (originCube d (n + (2 : ℤ))) (s / (3 : ℝ))
                              (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2
                                : ℤ))) z omega))) *
                      (√(Real.rpow (3 : ℝ) ((-2 : ℝ) * (↑(n + (2 : ℤ)) : ℝ))) *
                        √(normalizedL2SqOnSet (openCubeSet (originCube d (n + (2 : ℤ)))) fun (y :
                          Vec d) =>
                            u.toFun (y + wellPlacedCentre x m (n + (2 : ℤ))) - v.toH1.toFun y)) +
                    √((2 : ℝ) * (3 : ℝ) ^ d * (18 : ℝ) ^ d) *
                      dirichletEnergyWithRHSRHS CB2 (originCube d (n + (2 : ℤ)))
                        (parentRebasedFamily M L (n + (3 : ℤ)) (wellPlacedCentre x m (n + (2 :
                          ℤ))) z omega) (s / (2 : ℝ))
                        (fun (y : Vec d) => -g (y + wellPlacedCentre x m (n + (2 : ℤ)))) v ∧
                √(Real.rpow (3 : ℝ) ((-2 : ℝ) * (↑(n + (2 : ℤ)) : ℝ))) = Real.rpow (3 : ℝ) (-(↑(n
                  + (2 : ℤ)) : ℝ)) := by
  intro d _ CB1 CB2 hCB1 hCB2 h3d0 M s hs L m n x z hs1 omega u hdat g hsubx hgreg2 hhreg2 v
    hvgrad hB2disp
  have hbg : dirichletBoundaryGradientField v =
      fun y => hdat.grad (y + wellPlacedCentre x m (n + 2)) := by
    funext y
    rw [dirichletBoundaryGradientField, hvgrad y]
  have hbgreg2 : ForceBesovRegularity (originCube d (n + 2)) (s / 2)
      (dirichletBoundaryGradientField v) := by rw [hbg]; exact hhreg2
  -- the left-hand side is the square root of the Caccioppoli left-hand side
  have hLHS : h1EnergyNormOnCube (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (H1Function.untranslate x
        (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx)) =
      Real.sqrt (localizedCoeffEnergyValue (openCubeSet (originCube d n))
        ((parentRebasedFamily M L (n + 3) x z omega).coeffOn (originCube d n))
        (H1Function.untranslate x
          (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx))) := by
    rw [h1EnergyNormOnCube_parentRebasedFamily_eq M L (n + 3) n x z omega,
      localizedCoeffEnergyValue_parentRebasedFamily_eq M L (n + 3) x z omega
        (originCube d n)]
  -- the square root of the display
  have hDirB0 : (0 : ℝ) ≤ dirichletEnergyWithRHSRHS CB2 (originCube d (n + 2))
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega) (s / 2)
      (fun y => -g (y + wellPlacedCentre x m (n + 2))) v :=
    dirichletEnergyWithRHSRHS_nonneg v hCB2.le (by linarith only [hs]) hgreg2 hbgreg2
  have hP0 : (0 : ℝ) ≤ caccioppoliWithRHSPrefactor CB1 (originCube d (n + 2))
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (1 / 2) (s / 3) :=
    caccioppoliWithRHSPrefactor_nonneg hCB1.le (by norm_num) (by linarith only [hs])
      (by linarith only [hs1])
  have hLam0 : (0 : ℝ) ≤ Ch02.lambdaS (originCube d (n + 2)) (s / 3)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega) :=
    Ch02.lambdaSq_nonneg (originCube d (n + 2)) _ (by linarith only [hs]) (by norm_num)
  have hsqrt := sqrt_le_of_boundaryCaccioppoliDisplay h3d0 hP0 hLam0
    (show (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ)) from
      Real.rpow_nonneg (by norm_num) _)
    (normalizedL2SqOnSet_nonneg _ _
      (isOpen_openCubeSet (originCube d (n + 2))).measurableSet)
    (by positivity : (0 : ℝ) ≤ (18 : ℝ) ^ d) hDirB0 hB2disp
  have hT2sqrt : Real.sqrt (Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ))) =
      Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) := by
    rw [show (-2 : ℝ) * (((n + 2 : ℤ)) : ℝ) = 2 * (-(((n + 2 : ℤ)) : ℝ)) by ring]
    exact sqrt_rpow_two_mul (by norm_num) _
  exact ⟨hbg, hbgreg2, hLHS, hLam0, hsqrt, hT2sqrt⟩

/-- **The boundary lane's energy leg, at hinges (W) and (P).**

`AssemblyEnergyLeg.ae_h1EnergyNormOnCube_boundary_le_anchorLegs` with the
anchor's geometry binder replaced by the two containments its proof derives from
it.  Every constant, index and right-hand side is unchanged. -/
theorem ae_h1EnergyNormOnCube_boundary_le_anchorLegs_atHinges (d : ℕ) [NeZero d] :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ x z : Vec d,
          x ∈ openCubeSet (originCube d m) →
          ((fun y => wellPlacedCentre x m (n + 2) + y) ''
              openCubeSet (originCube d (n + 2)) ⊆
            (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))) →
          (translateSet (wellPlacedCentre x m (n + 2) - z)
              (cubeSet (originCube d (n + 2))) ⊆
            cubeSet (originCube d (n + 3))) →
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
                ∀ hsubx : translateSet x (openCubeSet (originCube d n)) ⊆
                    openCubeSet (originCube d m),
                  h1EnergyNormOnCube (originCube d n)
                      (parentRebasedFamily M L (n + 3) x z omega)
                      (H1Function.untranslate x
                        (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx)) ≤
                    K * (Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
                            Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
                            (eLpNorm (fun y => u.toFun y -
                                volumeAverage ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))) u.toFun) 2
                              (Support.normalizedVolumeMeasureOn
                                ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))))).toReal +
                          Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
                              Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) * S +
                          Real.rpow s (-(3 : ℝ)) *
                              Real.sqrt (((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹) *
                              Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) *
                              (Support.normalizedGagliardoESeminormOn
                                ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))) s g).toReal +
                          Real.rpow s (-(2 : ℝ)) *
                              Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
                              Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) *
                              (Support.normalizedGagliardoESeminormOn
                                ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))) s hdat.grad).toReal +
                          Real.rpow s (-(2 : ℝ)) *
                              Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ)) *
                              (eLpNorm hdat.grad 2
                                (Support.normalizedVolumeMeasureOn
                                  ((((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m))))).toReal) := by
  classical
  obtain ⟨CB1, CB2, hCB1, hCB2, hB2⟩ :=
    exists_boundaryWindowEnergy_rebased_le_dirichletDatumRHS_full d
  obtain ⟨CG1, CG2, hCG1, hCG2, hGA⟩ :=
    exists_cubeLpNorm_datumDifference_le_dirichletEnergyRHS d
  obtain ⟨CP, KP, hCP, hKP, hpref⟩ := ae_coveringCubePrefactor_le_gapThree d
  obtain ⟨CR, KR, hCR, hKR, hratio⟩ := ae_coveringCubeRatioCap_le_gapThree d
  obtain ⟨Pcap, hPcapdef, hPcap0⟩ :
      ∃ t : ℝ, t = (6 * max 1 CB1) ^ (14 : ℕ) * 64 * (KP * KP) ^ (6 : ℕ) ∧ 0 ≤ t :=
    ⟨_, rfl, by positivity⟩
  obtain ⟨alpha, halphadef, halpha0⟩ :
      ∃ t : ℝ, t = Real.sqrt (2 * (3 : ℝ) ^ d * (Pcap * KP)) ∧ 0 ≤ t :=
    ⟨_, rfl, Real.sqrt_nonneg _⟩
  obtain ⟨beta, hbetadef, hbeta0⟩ :
      ∃ t : ℝ, t = Real.sqrt (2 * (3 : ℝ) ^ d * (18 : ℝ) ^ d) ∧ 0 ≤ t :=
    ⟨_, rfl, Real.sqrt_nonneg _⟩
  obtain ⟨sK, hsKdef, hsK0⟩ : ∃ t : ℝ, t = Real.sqrt KR ∧ 0 ≤ t :=
    ⟨_, rfl, Real.sqrt_nonneg _⟩
  have hCbg0 : (0 : ℝ) ≤ besovGagliardoConstant d := besovGagliardoConstant_nonneg d
  have hCgw0 : (0 : ℝ) ≤ gagliardoWindowConst d := (gagliardoWindowConst_pos d).le
  have hgP0 : (0 : ℝ) ≤ unitMeanZeroPoincareConst d := unitMeanZeroPoincareConst_nonneg d
  have h3d0 : (0 : ℝ) ≤ (3 : ℝ) ^ d := by positivity
  have hsd0 : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hnegC0 : (0 : ℝ) ≤ Real.sqrt (3 / 2 : ℝ) := Real.sqrt_nonneg _
  have hn1 : (0 : ℝ) ≤ alpha * (3 : ℝ) ^ d := mul_nonneg halpha0 h3d0
  have hn3 : (0 : ℝ) ≤ alpha * CG1 * CG2 * KR * besovGagliardoConstant d *
      gagliardoWindowConst d :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg halpha0 hCG1.le)
      hCG2.le) hKR.le) hCbg0) hCgw0
  have hn4 : (0 : ℝ) ≤ alpha * CG1 * KR * besovGagliardoConstant d *
      gagliardoWindowConst d :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg halpha0 hCG1.le) hKR.le) hCbg0) hCgw0
  have hn5 : (0 : ℝ) ≤ beta * CB2 * sK * besovGagliardoConstant d *
      gagliardoWindowConst d :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbeta0 hCB2.le) hsK0) hCbg0) hCgw0
  have hn6 : (0 : ℝ) ≤ alpha * unitMeanZeroPoincareConst d * (d : ℝ) * (3 : ℝ) ^ d :=
    mul_nonneg (mul_nonneg (mul_nonneg halpha0 hgP0) (Nat.cast_nonneg d)) h3d0
  have hn7 : (0 : ℝ) ≤ alpha * CG1 * CG2 * KR * Real.sqrt (d : ℝ) * (3 : ℝ) ^ d :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg halpha0 hCG1.le)
      hCG2.le) hKR.le) hsd0) h3d0
  have hn8 : (0 : ℝ) ≤ Real.sqrt (3 / 2 : ℝ) * alpha * CG1 * Real.sqrt (d : ℝ) *
      (3 : ℝ) ^ d :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hnegC0 halpha0) hCG1.le) hsd0) h3d0
  have hn9 : (0 : ℝ) ≤ beta * CB2 * sK * Real.sqrt (d : ℝ) * (3 : ℝ) ^ d :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbeta0 hCB2.le) hsK0) hsd0) h3d0
  refine ⟨max CP CR,
    alpha * (3 : ℝ) ^ d + alpha +
      (8 * alpha * CG1 * CG2 * KR * besovGagliardoConstant d * gagliardoWindowConst d +
        8 * alpha * CG1 * KR * besovGagliardoConstant d * gagliardoWindowConst d +
        3 * beta * CB2 * sK * besovGagliardoConstant d * gagliardoWindowConst d) +
      (4 * alpha * CG1 * CG2 * KR * besovGagliardoConstant d * gagliardoWindowConst d +
        2 * beta * CB2 * sK * besovGagliardoConstant d * gagliardoWindowConst d) +
      (alpha * unitMeanZeroPoincareConst d * (d : ℝ) * (3 : ℝ) ^ d +
        4 * alpha * CG1 * CG2 * KR * Real.sqrt (d : ℝ) * (3 : ℝ) ^ d +
        Real.sqrt (3 / 2 : ℝ) * alpha * CG1 * Real.sqrt (d : ℝ) * (3 : ℝ) ^ d +
        2 * beta * CB2 * sK * Real.sqrt (d : ℝ) * (3 : ℝ) ^ d) + 1,
    lt_of_lt_of_le hCP (le_max_left _ _),
    by linarith only [hn1, halpha0, hn3, hn4, hn5, hn6, hn7, hn8, hn9], ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm x z hx hcov hP
  have hs1 : s ≤ 1 := hsrange.2
  have hnm2 : n + 2 ≤ m := by omega
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 3) : ℝ) :=
    (Annealed.sigmaBar M (n + 3)).2
  have hregimeP : M.gamma ≤ CP⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 := one_div_le_one_div_of_le hCP (le_max_left CP CR)
    rw [one_div, one_div] at h1
    exact h1
  have hregimeR : M.gamma ≤ CR⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 := one_div_le_one_div_of_le hCR (le_max_right CP CR)
    rw [one_div, one_div] at h1
    exact h1
  filter_upwards [hpref M s hsrange hregimeP hsmall hs L m n hmL hnm z,
    hratio M s hsrange hregimeR hsmall hs L m n hmL hnm z (s / 2)
      (by linarith only [hs]) (by linarith only [hs1])
      (offGridStabilityConst_pinHalf_le hs hs1),
    hratio M s hsrange hregimeR hsmall hs L m n hmL hnm z (s / 4)
      (by linarith only [hs]) (by linarith only [hs1])
      (offGridStabilityConst_pinQuarter_le hs hs1)] with omega hpre hr2 hr4
  intro hmem u hdat g S hsol hgL2 hgW hhW hmean hsubx
  obtain ⟨hprefcap, hlamScap⟩ := hpre hmem x hP CB1 hCB1
  obtain ⟨hLam2, -⟩ := hr2 hmem x hP
  obtain ⟨-, hlam4⟩ := hr4 hmem x hP
  rw [← hPcapdef] at hprefcap
  -- the anchor's data on the two windows and on the covering cube
  have hhL2m : MemLp hdat.grad 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))) :=
    memLp_normalizedVolumeMeasureOn_of_restrict
      (volume_openCubeSet_ne_zero (originCube d m)) hdat.grad_memVectorL2
  have huL2m : MemLp u.toFun 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))) :=
    memLp_normalizedVolumeMeasureOn_of_restrict
      (volume_openCubeSet_ne_zero (originCube d m)) u.memL2
  have hW3top := volume_anchorWindow_ne_top (n + 3) m z
  have hW30 : volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m))) ≠ 0 := by
    intro hzero
    have hle := measure_mono (μ := (volume : Measure (Vec d))) hcov
    rw [hzero] at hle
    exact volume_image_add_openCubeSet_ne_zero (wellPlacedCentre x m (n + 2))
      (originCube d (n + 2)) (le_antisymm hle zero_le)
  have := isProbabilityMeasure_normalizedVolumeMeasureOn hW30 hW3top
  obtain ⟨hhL2W, hgWW, hhWW, hXfin, hHfin, hgL2cov, hgWcov, hhL2cov, hhWcov, hgreg, hgreg2, hhreg,
    hhreg2, hsubc⟩ :=
    @residueEnergyLeg_comparisonBounds2 (d) (by infer_instance) (s) (hs) (m) (n) (x) (z) (hs1)
      (hnm2) (u) (hdat) (g) (hgL2) (hgW) (hhW) (hhL2m) (huL2m) (hW30) (this)
  -- the boundary Caccioppoli at `(1/2, s/3)` and the pin `r = s/2`
  obtain ⟨v, hvval, hvgrad, hB2disp⟩ :=
    hB2 M L omega m n x z (1 / 2) (s / 3) (s / 2) u hdat g hx hnm2 hsubx hsol
      (by norm_num) (by norm_num) (by linarith only [hs]) (by linarith only [hs1])
      (by linarith only [hs1]) (by linarith only [hs]) (by linarith only [hs1])
      hgreg2 hhreg2
  obtain ⟨hbg, hbgreg2, hLHS, hLam0, hsqrt, hT2sqrt⟩ :=
    @residueEnergyLeg_comparisonBounds3 (d) (by infer_instance) (CB1) (CB2) (hCB1) (hCB2) (h3d0)
      (M) (s) (hs) (L) (m) (n) (x) (z) (hs1) (omega) (u) (hdat) (g) (hsubx) (hgreg2) (hhreg2) (v)
        (hvgrad) (hB2disp)
  rw [hT2sqrt, ← hbetadef] at hsqrt
  -- the datum pricing, and the parent-`L²` pricing scaled by the frame factor
  have hGA1 := hGA (originCube d (n + 2))
    (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega) s
    (fun y => -g (y + wellPlacedCentre x m (n + 2))) v hs hs1 hgreg2 hbgreg2
  have hB4 := rpow_three_neg_mul_sqrt_coveringDifference_le_atWindow (x := x) (z := z)
    (S := S) hnm2 hcov u hdat v
    (H1Function.untranslate (wellPlacedCentre x m (n + 2))
      (u.restrict
        (isOpen_translateSet_openCubeSet (wellPlacedCentre x m (n + 2)) (n + 2)) hsubc))
    (fun _ => rfl) hvval hXfin hHfin hmean hGA1
  -- the energy legs, at the two Dirichlet-energy constants
  have hDirBle := dirichletEnergyWithRHSRHS_coveringCube_le_anchorLegs_atWindow
    (c := wellPlacedCentre x m (n + 2)) (C₂ := CB2) (K := KR)
    (sigma := (Annealed.sigmaBar M (n + 3) : ℝ)) rfl hcov hs hs1 hCB2.le hsig
    hKR.le hdat v hvgrad hlam4 hLam2 hgreg hhreg hgL2cov hgWcov hgWW hhL2cov hhWcov
    hhWW hhL2W
  have hDirGle := dirichletEnergyWithRHSRHS_coveringCube_le_anchorLegs_atWindow
    (c := wellPlacedCentre x m (n + 2)) (C₂ := CG2) (K := KR)
    (sigma := (Annealed.sigmaBar M (n + 3) : ℝ)) rfl hcov hs hs1 hCG2.le hsig
    hKR.le hdat v hvgrad hlam4 hLam2 hgreg hhreg hgL2cov hgWcov hgWW hhL2cov hhWcov
    hhWW hhL2W
  rw [← hsKdef] at hDirBle hDirGle
  -- the coarse caps of the prefactor and of the datum pricing's two factors
  obtain ⟨hlow, hlamInv, hBg, hHn, hnegf, hmain⟩ :=
    @residueEnergyLeg_comparisonBounds1 (d) (by infer_instance) (CB1) (CB2) (CG1) (CG2) (KP) (hKP)
      (KR) (hKR) (Pcap) (hPcap0) (alpha) (halphadef) (halpha0) (beta) (sK) (hsKdef) (hnegC0) (M)
        (s) (hs) (L) (m) (n) (x) (z) (hcov) (hs1) (hsig) (omega) (u) (hdat) (g) (S) (hsubx)
          (hprefcap) (hlamScap) (hlam4) (hhL2W) (hgWW) (hgL2cov) (hgWcov) (hgreg) (hsubc) (v)
            (hbg) (hLam0) (hsqrt) (hB4)
  rw [hLHS]
  refine five_leg_bound (boundary_energy_arith halpha0 hbeta0 (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) hsK0 hKR.le hCG1.le hCB2.le hgP0 (Nat.cast_nonneg d) h3d0
    hsd0 hCbg0 hCgw0 (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg hs.le _) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg (Real.rpow_nonneg (by linarith only [hs]) _)
    (Real.rpow_nonneg (by linarith only [hs]) _)
    (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      hgreg2)
    (normalizedEuclideanL2_nonneg _ _)
    (dirichletEnergyWithRHSRHS_nonneg v hCG2.le (by linarith only [hs]) hgreg2 hbgreg2)
    hsig (sqrt_mul_sqrt_inv hsig) (sqrt_mul_inv_eq_sqrt_inv hsig)
    (by rw [hsKdef]; exact Real.mul_self_sqrt hKR.le)
    (pin_force_sq hs) (pin_gradh_prod hs) (pin_force_cube hs)
    (pin_force_half_le hs hs1) (pin_gradh_half_le hs hs1) (one_le_rpow_neg_two hs hs1)
    hlow hlamInv hBg hHn hnegf hnegC0 hDirGle hDirBle hmain) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_
  · linarith only [hn1, halpha0, hn3, hn4, hn5, hn6, hn7, hn8, hn9]
  · linarith only [hn1, halpha0, hn3, hn4, hn5, hn6, hn7, hn8, hn9]
  · linarith only [hn1, halpha0, hn3, hn4, hn5, hn6, hn7, hn8, hn9]
  · linarith only [hn1, halpha0, hn3, hn4, hn5, hn6, hn7, hn8, hn9]
  · linarith only [hn1, halpha0, hn3, hn4, hn5, hn6, hn7, hn8, hn9]
  · exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg
  · exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg (by norm_num) _)) (le_trans (abs_nonneg _) hmean)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _)
      (Real.sqrt_nonneg _)) (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _)
      (Real.sqrt_nonneg _)) (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg
  · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.sqrt_nonneg _))
      ENNReal.toReal_nonneg

end

end Algsuperdiff.Section4.Provider.ExcessDecay
