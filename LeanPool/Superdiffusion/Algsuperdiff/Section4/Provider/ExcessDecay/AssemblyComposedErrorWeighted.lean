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
# AssemblyComposedErrorWeighted

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary branch of the error-weighted general clause, composed

This module is `AssemblyComposed`'s script with ONE row of the regrouping
changed.  It does not import `AssemblyComposed`, which is untouched and still
consumed by the frontier-empty chains, and it claims no anchor.

## What is proved

`ReindexComposed` composes the deterministic `x`-frame envelope with the
**interior** Caccioppoli and proves the general clause at frontier-empty
windows.  This module runs the *same* composition with the **boundary** energy
leg (`AssemblyEnergyLeg`) in place of the interior one, and therefore needs
no gate at all: the boundary display is proved for **every** `z`, the frontier
condition entering nowhere.

## The `s`-powers, as consumed

```text
  row 1  direct DirE ∇h    s^{-4}·(s/2)^{-1/2}                → ≤ 2 s^{-6}   (legs 4,5)
  row 2  direct DirE [g]   s^{-4}·(s/2)^{-3/2}                → ≤ 3 s^{-7}   (force leg)
  row 3  datum, crude leg  s^{-4}·s^{-1/2}                    → ≤   s^{-6}   (flat leg)
  row 4  datum, force leg  s^{-4}·(s/2)^{-3}                  =   8 s^{-7}   (force leg)
  row 5  datum → DirE [g]  s^{-4}·(s/2)^{-3/2}·(s/2)^{-3/2}   =   8 s^{-7}   (force leg)
  row 6  datum → DirE ∇h   s^{-4}·(s/2)^{-3/2}·(s/2)^{-1/2}   =   4 s^{-6}   (legs 4,5)
```

Row 6 proves **at equality**: `AssemblyArith.pin_gradh_prod` supplies the exact
identity `(s/2)^{-3/2}·(s/2)^{-1/2} = 4 s^{-2}`, so no slack remains on that
row.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the boundary application.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

private abbrev assemblyComposedErrorWeighted_comparisonBounds2_statement : Prop :=
    ∀ (d : ℕ) [NeZero d] (CE KE : ℝ),
      let kappa : ℝ := √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ);
      ∀ (_ : (0 : ℝ) ≤ kappa),
        let e0 : ℝ := kappa * (CE * (1 / 2 : ℝ));
        let k0 : ℝ := (2 : ℝ) * (↑d : ℝ) * (e0 ^ (2 : ℕ) + (1 : ℝ));
        let b0 : ℝ := √k0 * e0 + (2 : ℝ) * k0;
        ∀ (_ : b0 = √k0 * e0 + (2 : ℝ) * k0) (M : ABKModel d) (s : ℝ) (_ : (0 : ℝ) < s) (L m n :
          ℤ) (x z : Vec d)
          (_ :
            (fun (y : Vec d) => x + y) '' openCubeSet (originCube d n) ⊆
              (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (1 : ℤ))) ∩ openCubeSet
                (originCube d m))
          (_ : s ≤ (1 : ℝ)) (omega : Cutoff.CutoffSample d) (u hdat : H1Function (openCubeSet
            (originCube d m)))
          (g : Vec d → Vec d) (S : ℝ) (hsubx : translateSet x (openCubeSet (originCube d n)) ⊆
            openCubeSet (originCube d m))
          (_ :
            MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal) g) (2 : ENNReal)
              (normalizedGagliardoMeasureOn
                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2 : ℤ))) ∩
                  openCubeSet (originCube d m))))
          (_ :
            MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal) g) (2 : ENNReal)
              (normalizedGagliardoMeasureOn
                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                  openCubeSet (originCube d m))))
          (_ :
            MemLp g (2 : ENNReal) (normalizedVolumeMeasureOn ((fun (y : Vec d) => x + y) ''
              openCubeSet (originCube d n))))
          (_ :
            MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal) g) (2 : ENNReal)
              (normalizedGagliardoMeasureOn ((fun (y : Vec d) => x + y) '' openCubeSet (originCube
                d n)))),
          let Erep : ℝ :=
            fluxCorrectedErrorRepresentative M L (n + (3 : ℤ)) ⟨s / (8 : ℝ), (by positivity)⟩
              (Cutoff.translateCutoffSample z omega);
          ∀ (_ : (0 : ℝ) ≤ Erep),
            let Eb : ℝ :=
              √(offGridStabilityConst d (s / (6 : ℝ)) (s / (8 : ℝ))) * ((3 : ℝ) ^ ((3 : ℝ) * (s /
                (8 : ℝ))) * Erep);
            ∀
              (_ :
                ∀ (x : Vec d) (m : ℤ),
                  (fun (y : Vec d) => x + y) '' openCubeSet (originCube d n) ⊆
                      (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (1 : ℤ))) ∩
                        openCubeSet (originCube d m) →
                    Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
                        (parentRebasedFamily M L (n + (3 : ℤ)) x z omega)
                        (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s / (3 :
                          ℝ)) (0 : ℕ) ≤
                      Eb)
              (_ :
                ∀ (x : Vec d) (m : ℤ),
                  (fun (y : Vec d) => x + y) '' openCubeSet (originCube d n) ⊆
                      (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (1 : ℤ))) ∩
                        openCubeSet (originCube d m) →
                    coarseGrainingForceBracket (originCube d n) (parentRebasedFamily M L (n + (3 :
                      ℤ)) x z omega)
                        (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s / (3 :
                          ℝ)) ≤
                      √((2 : ℝ) * (↑d : ℝ) * (Eb ^ (2 : ℕ) + (1 : ℝ))) * Eb +
                        (2 : ℝ) * ((2 : ℝ) * (↑d : ℝ) * (Eb ^ (2 : ℕ) + (1 : ℝ)))),
              let sig : ℝ := (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ);
              ∀ (_ : (0 : ℝ) < sig),
                let X : ℝ :=
                  (eLpNorm
                      (fun (y : Vec d) =>
                        u.toFun y -
                          volumeAverage
                            ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                              ℤ))) ∩
                              openCubeSet (originCube d m))
                            u.toFun)
                      (2 : ENNReal)
                      (normalizedVolumeMeasureOn
                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                          openCubeSet (originCube d m)))).toReal;
                let Gs : ℝ :=
                  (normalizedGagliardoESeminormOn
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                        openCubeSet (originCube d m))
                      s g).toReal;
                let Hs : ℝ :=
                  (normalizedGagliardoESeminormOn
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                        openCubeSet (originCube d m))
                      s hdat.grad).toReal;
                let Hn : ℝ :=
                  (eLpNorm hdat.grad (2 : ENNReal)
                      (normalizedVolumeMeasureOn
                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                          openCubeSet (originCube d m)))).toReal;
                let Y2 : ℝ :=
                  (normalizedGagliardoESeminormOn
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2 : ℤ))) ∩
                        openCubeSet (originCube d m))
                      s g).toReal;
                let Ychild : ℝ :=
                  (normalizedGagliardoESeminormOn ((fun (y : Vec d) => x + y) '' openCubeSet
                    (originCube d n)) s g).toReal;
                let P2 : ℝ := Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ));
                let Q3s : ℝ := Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ));
                let Q3sn : ℝ := Real.rpow (3 : ℝ) (s * (↑n : ℝ));
                let Sm3 : ℝ := s.rpow (-3 : ℝ);
                let Sm2 : ℝ := s.rpow (-2 : ℝ);
                ∀
                  (_ :
                    Ch03.h1EnergyNormOnCube (originCube d n) (parentRebasedFamily M L (n + (3 :
                      ℤ)) x z omega)
                        (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x
                          n) hsubx)) ≤
                      KE *
                        (√sig * P2 * X + √sig * P2 * S + Sm3 * √sig⁻¹ * Q3s * Gs + Sm2 * √sig *
                          Q3s * Hs + Sm2 * √sig * Hn))
                  (_ : (0 : ℝ) ≤ Eb) (_ : Eb ≤ kappa * Erep) (_ : Eb ≤ e0)
                  (_ : (2 : ℝ) * (↑d : ℝ) * (Eb ^ (2 : ℕ) + (1 : ℝ)) ≤ k0),
                  coarseGrainingForceBracket (originCube d n) (parentRebasedFamily M L (n + (3 :
                    ℤ)) x z omega)
                        (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s / (3 :
                          ℝ)) ≤
                      b0 ∧
                    coarseGrainingEnergyTerm (originCube d n) (parentRebasedFamily M L (n + (3 :
                      ℤ)) x z omega)
                          (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s / (3
                            : ℝ))
                          (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x
                            n) hsubx)) ≤
                        kappa * KE * Erep *
                          (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) + Sm2 * (sig * (Q3s
                            * Hs)) +
                            Sm2 * (sig * Hn)) ∧
                      (Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s fun
                        (y : Vec d) =>
                            -g (y + x)) ≤
                          besovGagliardoConstant d * Q3sn * Ychild ∧
                        ((0 : ℝ) ≤
                            Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s
                              fun (y : Vec d) =>
                              -g (y + x)) ∧
                          Ychild ≤ gagliardoWindowConst d * windowMoveConst d * Gs

private abbrev assemblyComposedErrorWeighted_comparisonBounds5_statement : Prop :=
    ∀ (d : ℕ) [NeZero d] (CE KE : ℝ),
      let kappa : ℝ := √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ);
      ∀ (_ : kappa = √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ)) (_ : (0 : ℝ) ≤ kappa),
        let e0 : ℝ := kappa * (CE * (1 / 2 : ℝ));
        ∀ (_ : e0 = kappa * (CE * (1 / 2 : ℝ))),
          let k0 : ℝ := (2 : ℝ) * (↑d : ℝ) * (e0 ^ (2 : ℕ) + (1 : ℝ));
          ∀ (_ : k0 = (2 : ℝ) * (↑d : ℝ) * (e0 ^ (2 : ℕ) + (1 : ℝ))),
            let b0 : ℝ := √k0 * e0 + (2 : ℝ) * k0;
            ∀ (_ : b0 = √k0 * e0 + (2 : ℝ) * k0) (_ : (0 : ℝ) ≤ b0) (M : ABKModel d) (s : ℝ) (_ :
              (0 : ℝ) < s)
              (L m n : ℤ) (_ : m ≤ L) (_ : n + (3 : ℤ) ≤ m) (x z : Vec d)
              (_ :
                (fun (y : Vec d) => x + y) '' openCubeSet (originCube d n) ⊆
                  (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (1 : ℤ))) ∩
                    openCubeSet (originCube d m))
              (_ : s ≤ (1 : ℝ)) (omega : Cutoff.CutoffSample d)
              (_ :
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
              (_ :
                omega ∈
                    Frozen.Section4.goodEventAt M (cgEllipLowerConstant d) (n + (3 : ℤ)) z
                      ⟨s / (8 : ℝ),
                        (by positivity)⟩
                      (1 / 2 : ℝ) →
                  ∀ (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d) (S :
                    ℝ),
                    IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (originCube d m) u hdat g →
                      MemLp g (2 : ENNReal) (normalizedVolumeMeasureOn (openCubeSet (originCube d
                        m))) →
                        MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal) g) (2 : ENNReal)
                            (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                          MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal) hdat.grad) (2 : ENNReal)
                              (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                            |volumeAverage
                                    ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                                      openCubeSet (originCube d (n + (2 : ℤ))))
                                    fun (y : Vec d) => u.toFun y - hdat.toFun y| ≤
                                S →
                              ∀ (hsubx : translateSet x (openCubeSet (originCube d n)) ⊆
                                openCubeSet (originCube d m)),
                                Ch03.h1EnergyNormOnCube (originCube d n) (parentRebasedFamily M L
                                  (n + (3 : ℤ)) x z omega)
                                    (H1Function.untranslate x (u.restrict
                                      (isOpen_translateSet_openCubeSet x n) hsubx)) ≤
                                  KE *
                                    (√(↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) *
                                                Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ)) *
                                              (eLpNorm
                                                  (fun (y : Vec d) =>
                                                    u.toFun y -
                                                      volumeAverage
                                                        ((fun (y' : Vec d) => z + y') ''
                                                            openCubeSet (originCube d (n + (3 :
                                                              ℤ))) ∩
                                                          openCubeSet (originCube d m))
                                                        u.toFun)
                                                  (2 : ENNReal)
                                                  (normalizedVolumeMeasureOn
                                                    ((fun (y' : Vec d) => z + y') ''
                                                        openCubeSet (originCube d (n + (3 : ℤ))) ∩
                                                      openCubeSet (originCube d m)))).toReal +
                                            √(↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) *
                                                Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ)) *
                                              S +
                                          s.rpow (-3 : ℝ) * √(↑(Annealed.sigmaBar M (n + (3 : ℤ)))
                                            : ℝ)⁻¹ *
                                              Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ)) *
                                            (normalizedGagliardoESeminormOn
                                                ((fun (y' : Vec d) => z + y') '' openCubeSet
                                                  (originCube d (n + (3 : ℤ))) ∩
                                                  openCubeSet (originCube d m))
                                                s g).toReal +
                                        s.rpow (-2 : ℝ) * √(↑(Annealed.sigmaBar M (n + (3 : ℤ))) :
                                          ℝ) *
                                            Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ)) *
                                          (normalizedGagliardoESeminormOn
                                              ((fun (y' : Vec d) => z + y') '' openCubeSet
                                                (originCube d (n + (3 : ℤ))) ∩
                                                openCubeSet (originCube d m))
                                              s hdat.grad).toReal +
                                      s.rpow (-2 : ℝ) * √(↑(Annealed.sigmaBar M (n + (3 : ℤ))) :
                                        ℝ) *
                                        (eLpNorm hdat.grad (2 : ENNReal)
                                            (normalizedVolumeMeasureOn
                                              ((fun (y' : Vec d) => z + y') '' openCubeSet
                                                (originCube d (n + (3 : ℤ))) ∩
                                                openCubeSet (originCube d m)))).toReal))
              (_ :
                ∀ (x : Vec d) (m : ℤ),
                  (fun (y : Vec d) => x + y) '' openCubeSet (originCube d n) ⊆
                      (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (1 : ℤ))) ∩
                        openCubeSet (originCube d m) →
                    Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
                        (parentRebasedFamily M L (n + (3 : ℤ)) x z omega)
                        (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s / (3 :
                          ℝ)) (0 : ℕ) ≤
                      √(offGridStabilityConst d (s / (6 : ℝ)) (s / (8 : ℝ))) *
                        ((3 : ℝ) ^ ((3 : ℝ) * (s / (8 : ℝ))) *
                          fluxCorrectedErrorRepresentative M L (n + (3 : ℤ))
                            ⟨s / (8 : ℝ),
                              (by positivity)⟩
                            (Cutoff.translateCutoffSample z omega)))
              (_ :
                ∀ (x : Vec d) (m : ℤ),
                  (fun (y : Vec d) => x + y) '' openCubeSet (originCube d n) ⊆
                      (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (1 : ℤ))) ∩
                        openCubeSet (originCube d m) →
                    coarseGrainingForceBracket (originCube d n) (parentRebasedFamily M L (n + (3 :
                      ℤ)) x z omega)
                        (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s / (3 :
                          ℝ)) ≤
                      √((2 : ℝ) * (↑d : ℝ) *
                              ((√(offGridStabilityConst d (s / (6 : ℝ)) (s / (8 : ℝ))) *
                                    ((3 : ℝ) ^ ((3 : ℝ) * (s / (8 : ℝ))) *
                                      fluxCorrectedErrorRepresentative M L (n + (3 : ℤ))
                                        ⟨s / (8 : ℝ),
                                          (by positivity)⟩
                                        (Cutoff.translateCutoffSample z omega))) ^
                                  (2 : ℕ) +
                                (1 : ℝ))) *
                          (√(offGridStabilityConst d (s / (6 : ℝ)) (s / (8 : ℝ))) *
                            ((3 : ℝ) ^ ((3 : ℝ) * (s / (8 : ℝ))) *
                              fluxCorrectedErrorRepresentative M L (n + (3 : ℤ))
                                ⟨s / (8 : ℝ),
                                  (by positivity)⟩
                                (Cutoff.translateCutoffSample z omega))) +
                        (2 : ℝ) *
                          ((2 : ℝ) * (↑d : ℝ) *
                            ((√(offGridStabilityConst d (s / (6 : ℝ)) (s / (8 : ℝ))) *
                                  ((3 : ℝ) ^ ((3 : ℝ) * (s / (8 : ℝ))) *
                                    fluxCorrectedErrorRepresentative M L (n + (3 : ℤ))
                                      ⟨s / (8 : ℝ),
                                        (by positivity)⟩
                                      (Cutoff.translateCutoffSample z omega))) ^
                                (2 : ℕ) +
                              (1 : ℝ))))
              (_ :
                omega ∈
                  Frozen.Section4.goodEventAt M (cgEllipLowerConstant d) (n + (3 : ℤ)) z
                    ⟨s / (8 : ℝ),
                      (by positivity)⟩
                    (1 / 2 : ℝ))
              (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d) (S : ℝ)
              (_ : IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                (originCube d m) u hdat g)
              (_ : MemLp g (2 : ENNReal) (normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
              (_ :
                MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal) g) (2 : ENNReal)
                  (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))))
              (_ :
                MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal) hdat.grad) (2 : ENNReal)
                  (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))))
              (_ :
                |volumeAverage
                      ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                        openCubeSet (originCube d (n + (2 : ℤ))))
                      fun (y : Vec d) => u.toFun y - hdat.toFun y| ≤
                  S)
              (v : H1Function ((fun (y : Vec d) => x + y) '' openCubeSet (originCube d n)))
              (w : H10Function ((fun (y : Vec d) => x + y) '' openCubeSet (originCube d n)))
              (_ : IsWeaklyHarmonicOn ((fun (y : Vec d) => x + y) '' openCubeSet (originCube d n))
                v)
              (_ : ∀ (y : Vec d), v.toFun y = u.toFun y - w.toFun y)
              (_ : ∀ (y : Vec d), v.grad y = u.grad y - w.grad y),
              ∃ (hsubx : translateSet x (openCubeSet (originCube d n)) ⊆ openCubeSet (originCube d
                m)) (_ :
                fluxCorrectedErrorRepresentative M L (n + (3 : ℤ)) ⟨s / (8 : ℝ), (by positivity)⟩
                    (Cutoff.translateCutoffSample z omega) ≤
                  CE * (1 / 2 : ℝ))
                (_ :
                (0 : ℝ) ≤
                  fluxCorrectedErrorRepresentative M L (n + (3 : ℤ)) ⟨s / (8 : ℝ), (by positivity)⟩
                    (Cutoff.translateCutoffSample z omega))
                (_ : (0 : ℝ) < (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ)) (_ :
                Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ)) = Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) :
                  ℝ))) (_ :
                Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ)) = Real.rpow (3 : ℝ) (s * (↑(n + (2 :
                  ℤ)) : ℝ))) (_ :
                (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) *
                    (cubeBesovScaleWeight (1 : ℝ) (originCube d n) *
                      (eLpNorm (fun (y : Vec d) => u.toFun y - v.toFun y) (2 : ENNReal)
                          (normalizedVolumeMeasureOn
                            ((fun (y : Vec d) => x + y) '' openCubeSet (originCube d n)))).toReal) ≤
                  (3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d *
                      ((216 : ℝ) * s⁻¹ ^ (4 : ℕ) *
                          coarseGrainingEnergyTerm (originCube d n) (parentRebasedFamily M L (n +
                            (3 : ℤ)) x z omega)
                            (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s /
                              (3 : ℝ))
                            (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet
                              x n) hsubx)) +
                        (1944 : ℝ) * s⁻¹ ^ (6 : ℕ) *
                          coarseGrainingForceTerm (originCube d n) (parentRebasedFamily M L (n +
                            (3 : ℤ)) x z omega)
                            (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s /
                              (3 : ℝ)) s
                            fun (y : Vec d) => -g (y + x)) +
                    interiorCorrectionConst d * s.rpow (-(1 / 2 : ℝ)) * Real.rpow (3 : ℝ) (s * (↑n
                      : ℝ)) *
                      (normalizedGagliardoESeminormOn ((fun (y : Vec d) => x + y) '' openCubeSet
                        (originCube d n)) s
                          g).toReal)
                (_ : Real.rpow (3 : ℝ) (s * (↑n : ℝ)) = Real.rpow (3 : ℝ) (s * (↑n : ℝ))) (_ :
                Real.rpow (3 : ℝ) (((1 : ℝ) + s) * (↑n : ℝ)) = Real.rpow (3 : ℝ) (((1 : ℝ) + s) *
                  (↑n : ℝ))) (_ :
                Real.rpow (3 : ℝ) (↑n : ℝ) = Real.rpow (3 : ℝ) (↑n : ℝ)) (_ : s.rpow (-4 : ℝ) =
                  s.rpow (-4 : ℝ)) (_ :
                s.rpow (-7 : ℝ) = s.rpow (-7 : ℝ)) (_ : s.rpow (-6 : ℝ) = s.rpow (-6 : ℝ)) (_ :
                s.rpow (-3 : ℝ) = s.rpow (-3 : ℝ)) (_ : s.rpow (-2 : ℝ) = s.rpow (-2 : ℝ)) (_ :
                (0 : ℝ) ≤
                  (eLpNorm
                      (fun (y : Vec d) =>
                        u.toFun y -
                          volumeAverage
                            ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                              ℤ))) ∩
                              openCubeSet (originCube d m))
                            u.toFun)
                      (2 : ENNReal)
                      (normalizedVolumeMeasureOn
                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                          openCubeSet (originCube d m)))).toReal)
                (_ :
                (0 : ℝ) ≤
                  (normalizedGagliardoESeminormOn
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                        openCubeSet (originCube d m))
                      s g).toReal)
                (_ :
                (0 : ℝ) ≤
                  (normalizedGagliardoESeminormOn
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                        openCubeSet (originCube d m))
                      s hdat.grad).toReal)
                (_ :
                (0 : ℝ) ≤
                  (eLpNorm hdat.grad (2 : ENNReal)
                      (normalizedVolumeMeasureOn
                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                          openCubeSet (originCube d m)))).toReal)
                (_ : (0 : ℝ) ≤ S) (_ : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ))) (_ :
                (0 : ℝ) ≤ Real.rpow (3 : ℝ) (s * (↑n : ℝ))) (_ : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (((1
                  : ℝ) + s) * (↑n : ℝ))) (_
                : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (↑n : ℝ)) (_ : (0 : ℝ) ≤ s.rpow (-4 : ℝ)) (_ : (0 :
                  ℝ) ≤ s.rpow (-7 : ℝ)) (_ :
                (0 : ℝ) ≤ s.rpow (-6 : ℝ)) (_ : (0 : ℝ) ≤ s.rpow (-3 : ℝ)) (_ : (0 : ℝ) ≤ s.rpow
                  (-2 : ℝ)) (_ :
                (0 : ℝ) ≤ (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ)⁻¹) (_ :
                coarseGrainingEnergyTerm (originCube d n) (parentRebasedFamily M L (n + (3 : ℤ)) x
                  z omega)
                    (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s / (3 : ℝ))
                    (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n)
                      hsubx)) ≤
                  kappa * KE *
                      fluxCorrectedErrorRepresentative M L (n + (3 : ℤ)) ⟨s / (8 : ℝ), (by
                        positivity)⟩
                        (Cutoff.translateCutoffSample z omega) *
                    ((↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) *
                              (Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ)) *
                                (eLpNorm
                                    (fun (y : Vec d) =>
                                      u.toFun y -
                                        volumeAverage
                                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube
                                            d (n + (3 : ℤ))) ∩
                                            openCubeSet (originCube d m))
                                          u.toFun)
                                    (2 : ENNReal)
                                    (normalizedVolumeMeasureOn
                                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d
                                        (n + (3 : ℤ))) ∩
                                        openCubeSet (originCube d m)))).toReal) +
                            (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) * (Real.rpow (3 : ℝ) (-(↑(n
                              + (2 : ℤ)) : ℝ)) * S) +
                          s.rpow (-3 : ℝ) *
                            (Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ)) *
                              (normalizedGagliardoESeminormOn
                                  ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n +
                                    (3 : ℤ))) ∩
                                    openCubeSet (originCube d m))
                                  s g).toReal) +
                        s.rpow (-2 : ℝ) *
                          ((↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) *
                            (Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ)) *
                              (normalizedGagliardoESeminormOn
                                  ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n +
                                    (3 : ℤ))) ∩
                                    openCubeSet (originCube d m))
                                  s hdat.grad).toReal)) +
                      s.rpow (-2 : ℝ) *
                        ((↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) *
                          (eLpNorm hdat.grad (2 : ENNReal)
                              (normalizedVolumeMeasureOn
                                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3
                                  : ℤ))) ∩
                                  openCubeSet (originCube d m)))).toReal)))
                (_ :
                (normalizedGagliardoESeminormOn ((fun (y : Vec d) => x + y) '' openCubeSet
                  (originCube d n)) s g).toReal ≤
                  gagliardoWindowConst d * windowMoveConst d *
                    (normalizedGagliardoESeminormOn
                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                          openCubeSet (originCube d m))
                        s g).toReal)
                (_ :
                (coarseGrainingForceTerm (originCube d n) (parentRebasedFamily M L (n + (3 : ℤ)) x
                  z omega)
                    (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s / (3 : ℝ))
                      s fun (y : Vec d) =>
                    -g (y + x)) ≤
                  b0 *
                    (besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * (↑n : ℝ)) *
                      (gagliardoWindowConst d * windowMoveConst d *
                        (normalizedGagliardoESeminormOn
                            ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                              ℤ))) ∩
                              openCubeSet (originCube d m))
                            s g).toReal))),
                True

private theorem assemblyComposedErrorWeighted_estimate1 :
    ∀ (CE KE kappa cg A1 : ℝ)
      (_ : A1 = cg * (216 : ℝ) * (kappa * KE)) (_ : (0 : ℝ) ≤ A1) (s : ℝ) (_ : (0 : ℝ) < s) (S
        Erep : ℝ)
      (_ : Erep ≤ CE * (1 / 2 : ℝ)) (_ : (0 : ℝ) ≤ Erep) (sig X Gs Hs Hn P2 Q3s Q1s R3n S4 S7 S6
        Sm3 Sm2 : ℝ)
      (_ : (0 : ℝ) ≤ X) (_ : (0 : ℝ) ≤ Gs) (_ : (0 : ℝ) ≤ Hs) (_ : (0 : ℝ) ≤ S) (_ : (0 : ℝ) ≤ Q3s)
      (_ : (0 : ℝ) ≤ R3n) (_ : (0 : ℝ) ≤ Sm3) (_ : (0 : ℝ) ≤ Sm2) (_ : (0 : ℝ) ≤ sig⁻¹)
      (_ : sig⁻¹ * sig = (1 : ℝ)) (_ : s⁻¹ ^ (4 : ℕ) = S4) (_ : S4 * Sm3 = S7) (_ : S4 * Sm2 = S6)
      (_ : R3n * P2 ≤ (1 : ℝ)) (_ : R3n * Q3s ≤ (9 : ℝ) * Q1s),
      sig⁻¹ * R3n *
          (cg *
            ((216 : ℝ) * s⁻¹ ^ (4 : ℕ) *
              (kappa * KE * Erep *
                (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) + Sm2 * (sig * (Q3s * Hs)) +
                  Sm2 * (sig * Hn))))) ≤
        A1 * (S4 * Erep * X) + (9 : ℝ) * (CE * (1 / 2 : ℝ)) * A1 * (S7 * sig⁻¹ * Q1s * Gs) +
              (9 : ℝ) * (CE * (1 / 2 : ℝ)) * A1 * (S6 * Q1s * Hs) +
            A1 * (S6 * Erep * R3n * Hn) +
          A1 * (S4 * Erep * S) := by
  intro CE KE kappa cg A1 hA1def hA1 s hs S Erep hErepCap hErep0 sig X Gs Hs Hn P2 Q3s Q1s R3n S4
    S7 S6 Sm3 Sm2 hX0 hGs0 hHs0 hS0 hQ3s0 hR3n0 hSm30 hSm20 hsiginv0 hsinv hS4eq hS4Sm3 hS4Sm2
      hRP2 hRQ3s
  have hsplit : (sig⁻¹ * R3n) * (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
        (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
          Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))))) =
      A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((sig⁻¹ * sig) * ((R3n * P2) * X)))) +
        A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((sig⁻¹ * sig) * ((R3n * P2) * S)))) +
        A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs))))) +
        A1 * ((s⁻¹) ^ (4 : ℕ) *
          (Erep * ((sig⁻¹ * sig) * (Sm2 * ((R3n * Q3s) * Hs))))) +
        A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((sig⁻¹ * sig) * (Sm2 * (R3n * Hn))))) := by
    rw [hA1def]; ring
  rw [hsplit, hsinv]
  have hsinv4 : (0 : ℝ) ≤ (s⁻¹) ^ (4 : ℕ) := pow_nonneg (inv_nonneg.mpr hs.le) 4
  have hi : A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * X)))) ≤
      A1 * (S4 * Erep * X) := by
    have h1 : (R3n * P2) * X ≤ X := by
      have h := mul_le_mul_of_nonneg_right hRP2 hX0
      linarith only [h]
    calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * X))))
        = A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((R3n * P2) * X))) := by ring
      _ ≤ A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * X)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h1 hErep0) hsinv4) hA1
      _ = A1 * (S4 * Erep * X) := by rw [hS4eq]; ring
  have hii : A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * S)))) ≤
      A1 * (S4 * Erep * S) := by
    have h1 : (R3n * P2) * S ≤ S := by
      have h := mul_le_mul_of_nonneg_right hRP2 hS0
      linarith only [h]
    calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * S))))
        = A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((R3n * P2) * S))) := by ring
      _ ≤ A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * S)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h1 hErep0) hsinv4) hA1
      _ = A1 * (S4 * Erep * S) := by rw [hS4eq]; ring
  have hiii : A1 * ((s⁻¹) ^ (4 : ℕ) *
      (Erep * (sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs))))) ≤
      (9 * (CE * (1 / 2)) * A1) * (S7 * sig⁻¹ * Q1s * Gs) := by
    have h2 : (R3n * Q3s) * (Sm3 * Gs) ≤ (9 * Q1s) * (Sm3 * Gs) :=
      mul_le_mul_of_nonneg_right hRQ3s (mul_nonneg hSm30 hGs0)
    have h2nn : (0 : ℝ) ≤ sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs)) :=
      mul_nonneg hsiginv0 (mul_nonneg (mul_nonneg hR3n0 hQ3s0)
        (mul_nonneg hSm30 hGs0))
    have hinner : Erep * (sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs))) ≤
        (CE * (1 / 2)) * (sig⁻¹ * ((9 * Q1s) * (Sm3 * Gs))) :=
      mul_le_mul hErepCap (mul_le_mul_of_nonneg_left h2 hsiginv0) h2nn
        (le_trans hErep0 hErepCap)
    calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs)))))
        ≤ A1 * ((s⁻¹) ^ (4 : ℕ) *
            ((CE * (1 / 2)) * (sig⁻¹ * ((9 * Q1s) * (Sm3 * Gs))))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinner hsinv4) hA1
      _ = (9 * (CE * (1 / 2)) * A1) * (((s⁻¹) ^ (4 : ℕ) * Sm3) * sig⁻¹ * Q1s * Gs) := by
          ring
      _ = (9 * (CE * (1 / 2)) * A1) * (S7 * sig⁻¹ * Q1s * Gs) := by
          rw [hS4eq, hS4Sm3]
  have hiv : A1 * ((s⁻¹) ^ (4 : ℕ) *
      (Erep * (1 * (Sm2 * ((R3n * Q3s) * Hs))))) ≤
      (9 * (CE * (1 / 2)) * A1) * (S6 * Q1s * Hs) := by
    have h2 : Sm2 * ((R3n * Q3s) * Hs) ≤ Sm2 * ((9 * Q1s) * Hs) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hRQ3s hHs0) hSm20
    have h2nn : (0 : ℝ) ≤ Sm2 * ((R3n * Q3s) * Hs) :=
      mul_nonneg hSm20 (mul_nonneg (mul_nonneg hR3n0 hQ3s0) hHs0)
    have hinner : Erep * (Sm2 * ((R3n * Q3s) * Hs)) ≤
        (CE * (1 / 2)) * (Sm2 * ((9 * Q1s) * Hs)) :=
      mul_le_mul hErepCap h2 h2nn (le_trans hErep0 hErepCap)
    calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * (Sm2 * ((R3n * Q3s) * Hs)))))
        = A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (Sm2 * ((R3n * Q3s) * Hs)))) := by ring
      _ ≤ A1 * ((s⁻¹) ^ (4 : ℕ) * ((CE * (1 / 2)) * (Sm2 * ((9 * Q1s) * Hs)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinner hsinv4) hA1
      _ = (9 * (CE * (1 / 2)) * A1) * (((s⁻¹) ^ (4 : ℕ) * Sm2) * Q1s * Hs) := by ring
      _ = (9 * (CE * (1 / 2)) * A1) * (S6 * Q1s * Hs) := by rw [hS4eq, hS4Sm2]
  -- The error-weighted delta: the flat leg keeps `𝓔`.
  have hv : A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * (Sm2 * (R3n * Hn))))) ≤
      A1 * (S6 * Erep * R3n * Hn) := by
    have hprod : (s⁻¹) ^ (4 : ℕ) * Sm2 = S6 := by rw [hS4eq]; exact hS4Sm2
    refine le_of_eq ?_
    rw [← hprod]; ring
  linarith only [hi, hii, hiii, hiv, hv]

private theorem assemblyComposedErrorWeighted_comparisonBounds1 :
    ∀ (CE KE kappa cg A1 : ℝ) (_ : A1 = cg * (216 : ℝ) * (kappa * KE)) (_ : (0 : ℝ) ≤ A1) (s : ℝ)
      (_ : (0 : ℝ) < s) (n : ℤ) (_ : s ≤ (1 : ℝ)) (S Erep : ℝ) (_ : Erep ≤ CE * (1 / 2 : ℝ))
      (_ : (0 : ℝ) ≤ Erep) (sig X Gs Hs Hn P2 : ℝ) (_ : P2 = Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) :
        ℝ))) (Q3s : ℝ)
      (_ : Q3s = Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ))) (Q3sn : ℝ)
      (_ : Q3sn = Real.rpow (3 : ℝ) (s * (↑n : ℝ))) (Q1s : ℝ)
      (_ : Q1s = Real.rpow (3 : ℝ) (((1 : ℝ) + s) * (↑n : ℝ))) (R3n : ℝ) (_ : R3n = Real.rpow (3 :
        ℝ) (↑n : ℝ))
      (S4 S7 S6 Sm3 Sm2 : ℝ) (_ : (0 : ℝ) ≤ X) (_ : (0 : ℝ) ≤ Gs) (_ : (0 : ℝ) ≤ Hs) (_ : (0 : ℝ)
        ≤ S)
      (_ : (0 : ℝ) ≤ Q3s) (_ : (0 : ℝ) ≤ R3n) (_ : (0 : ℝ) ≤ Sm3) (_ : (0 : ℝ) ≤ Sm2)
      (_ : (0 : ℝ) ≤ sig⁻¹) (_ : sig⁻¹ * sig = (1 : ℝ)) (_ : s⁻¹ ^ (4 : ℕ) = S4) (_ : S4 * Sm3 = S7)
      (_ : S4 * Sm2 = S6),
      R3n * Q3sn = Q1s ∧
        sig⁻¹ * R3n *
            (cg *
              ((216 : ℝ) * s⁻¹ ^ (4 : ℕ) *
                (kappa * KE * Erep *
                  (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) + Sm2 * (sig * (Q3s * Hs)) +
                    Sm2 * (sig * Hn))))) ≤
          A1 * (S4 * Erep * X) + (9 : ℝ) * (CE * (1 / 2 : ℝ)) * A1 * (S7 * sig⁻¹ * Q1s * Gs) +
                (9 : ℝ) * (CE * (1 / 2 : ℝ)) * A1 * (S6 * Q1s * Hs) +
              A1 * (S6 * Erep * R3n * Hn) +
            A1 * (S4 * Erep * S) := by
  intro CE KE kappa cg A1 hA1def hA1 s hs n hs1 S Erep hErepCap hErep0 sig X Gs Hs Hn P2 hP2def
    Q3s hQ3sdef Q3sn hQ3sndef Q1s hQ1sdef R3n hR3ndef S4 S7 S6 Sm3 Sm2 hX0 hGs0 hHs0 hS0 hQ3s0
      hR3n0 hSm30 hSm20 hsiginv0 hsinv hS4eq hS4Sm3 hS4Sm2
  have hRP2 : R3n * P2 ≤ 1 := by
    rw [hR3ndef, hP2def]
    exact rpow_three_frame_l2_le_one n
  have hRQ3s : R3n * Q3s ≤ 9 * Q1s := by
    rw [hR3ndef, hQ3sdef, hQ1sdef]
    exact rpow_three_frame_force_le n hs1
  have hRQ3sn : R3n * Q3sn = Q1s := by
    rw [hR3ndef, hQ3sndef, hQ1sdef]
    exact rpow_three_mul_eq_one_add s n
  have hT1 : (sig⁻¹ * R3n) * (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
        (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
          Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))))) ≤
      A1 * (S4 * Erep * X) + (9 * (CE * (1 / 2)) * A1) * (S7 * sig⁻¹ * Q1s * Gs) +
        (9 * (CE * (1 / 2)) * A1) * (S6 * Q1s * Hs) +
        A1 * (S6 * Erep * R3n * Hn) + A1 * (S4 * Erep * S)  :=
          @assemblyComposedErrorWeighted_estimate1 (CE) (KE) (kappa) (cg) (A1) (hA1def) (hA1) (s)
            (hs) (S) (Erep) (hErepCap) (hErep0) (sig) (X) (Gs) (Hs) (Hn) (P2) (Q3s) (Q1s) (R3n)
              (S4) (S7) (S6) (Sm3) (Sm2) (hX0) (hGs0) (hHs0) (hS0) (hQ3s0) (hR3n0) (hSm30) (hSm20)
                (hsiginv0) (hsinv) (hS4eq) (hS4Sm3) (hS4Sm2) (hRP2) (hRQ3s)
  exact ⟨hRQ3sn, hT1⟩

private theorem assemblyComposedErrorWeighted_comparisonBounds2 :
  assemblyComposedErrorWeighted_comparisonBounds2_statement := by
  intro d _ _ KE kappa hkappa e0 k0 b0 hb0def M s hs L m n x z hgeom hs1 omega u _ g S hsubx hgWW2
    hgWW3 hgL2child hgWchild Erep hErep0 Eb herrD hbrk sig hsig X Gs Hs Hn Y2 Ychild P2 Q3s Q3sn
      Sm3 Sm2 hEn hEb0 hEbkappa hEbe0 hKble
  have hbrkCap : coarseGrainingForceBracket (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) ≤ b0 := by
    refine (hbrk x m hgeom).trans ?_
    rw [hb0def]
    have h1 : Real.sqrt (2 * (d : ℝ) * (Eb ^ 2 + 1)) * Eb ≤ Real.sqrt k0 * e0 :=
      mul_le_mul (Real.sqrt_le_sqrt hKble) hEbe0 hEb0 (Real.sqrt_nonneg _)
    have h2 : 2 * (2 * (d : ℝ) * (Eb ^ 2 + 1)) ≤ 2 * k0 := by linarith only [hKble]
    linarith only [h1, h2]
  -- (c) the energy term, with the boundary energy leg substituted
  have hEnergy0 : 0 ≤ Ch03.h1EnergyNormOnCube (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (H1Function.untranslate x
        (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx)) :=
    h1EnergyNormOnCube_nonneg _ _ _
  have hET : coarseGrainingEnergyTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3)
      (H1Function.untranslate x
        (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx)) ≤
      kappa * KE * Erep *
        (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
          Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn)) := by
    have hEcap : Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
        (parentRebasedFamily M L (n + 3) x z omega)
        (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) 0 ≤ kappa * Erep :=
      (herrD x m hgeom).trans hEbkappa
    rw [coarseGrainingEnergyTerm, constantCoeffMatrixNormHalf_scalarComparator_sqrt]
    have hstep : Real.sqrt sig *
        Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
          (parentRebasedFamily M L (n + 3) x z omega)
          (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) 0 *
        Ch03.h1EnergyNormOnCube (originCube d n)
          (parentRebasedFamily M L (n + 3) x z omega)
          (H1Function.untranslate x
            (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx)) ≤
        Real.sqrt sig * (kappa * Erep) *
          (KE * (Real.sqrt sig * P2 * X + Real.sqrt sig * P2 * S +
            Sm3 * Real.sqrt sig⁻¹ * Q3s * Gs + Sm2 * Real.sqrt sig * Q3s * Hs +
            Sm2 * Real.sqrt sig * Hn)) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hEcap (Real.sqrt_nonneg _)) hEn
        hEnergy0 ?_
      exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hkappa hErep0)
    refine hstep.trans (le_of_eq ?_)
    have h1 : Real.sqrt sig * Real.sqrt sig = sig := Real.mul_self_sqrt hsig.le
    have h2 : Real.sqrt sig * Real.sqrt sig⁻¹ = 1 := sqrt_mul_sqrt_inv hsig
    calc Real.sqrt sig * (kappa * Erep) *
          (KE * (Real.sqrt sig * P2 * X + Real.sqrt sig * P2 * S +
            Sm3 * Real.sqrt sig⁻¹ * Q3s * Gs + Sm2 * Real.sqrt sig * Q3s * Hs +
            Sm2 * Real.sqrt sig * Hn))
        = kappa * KE * Erep *
            ((Real.sqrt sig * Real.sqrt sig) * (P2 * X) +
              (Real.sqrt sig * Real.sqrt sig) * (P2 * S) +
              (Real.sqrt sig * Real.sqrt sig⁻¹) * (Sm3 * (Q3s * Gs)) +
              (Real.sqrt sig * Real.sqrt sig) * (Sm2 * (Q3s * Hs)) +
              (Real.sqrt sig * Real.sqrt sig) * (Sm2 * Hn)) := by ring
      _ = kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) +
            1 * (Sm3 * (Q3s * Gs)) + sig * (Sm2 * (Q3s * Hs)) + sig * (Sm2 * Hn)) := by
          rw [h1, h2]
      _ = kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
            Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn)) := by ring
  -- (d) the forcing leg, through the two window moves
  have hGbes : Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s
      (fun y => -g (y + x)) ≤ besovGagliardoConstant d * Q3sn * Ychild := by
    have h := besovVectorSeminormTwo_translated_neg_le_gagliardo_window
      (originCube d n) hs hs1 hgL2child hgWchild
    rwa [cubeBesovScaleWeight_neg_originCube (d := d) n s] at h
  have hGbes0 : 0 ≤ Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo
      (originCube d n) s (fun y => -g (y + x)) :=
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (forceBesovRegularity_translated_neg (originCube d n) hs hs1 hgL2child hgWchild)
  have hYchild2 : Ychild ≤ gagliardoWindowConst d * Y2 :=
    normalizedGagliardoESeminormOn_child_toReal_le hgeom g hgWW2
  have hY23 : Y2 ≤ windowMoveConst d * Gs := by
    have hbase := normalizedGagliardoESeminormOn_anchorWindow_le hgeom s g
    have hRHSne : ENNReal.ofReal (windowMoveConst d) *
        Support.normalizedGagliardoESeminormOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))) s g ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgWW3.eLpNorm_ne_top
    have hstep := ENNReal.toReal_mono hRHSne hbase
    rwa [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (windowMoveConst_pos d).le] at hstep
  have hYchild3 : Ychild ≤ gagliardoWindowConst d * windowMoveConst d * Gs := by
    refine hYchild2.trans ?_
    have h := mul_le_mul_of_nonneg_left hY23 (gagliardoWindowConst_pos d).le
    calc gagliardoWindowConst d * Y2 ≤ gagliardoWindowConst d * (windowMoveConst d * Gs) := h
      _ = gagliardoWindowConst d * windowMoveConst d * Gs := by ring
  exact ⟨hbrkCap, hET, hGbes, hGbes0, hYchild3⟩

private theorem assemblyComposedErrorWeighted_comparisonBounds3 :
    ∀ (d : ℕ) (CE : ℝ),
      let kappa : ℝ := √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ);
      ∀ (_ : kappa = √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ)) (_ : (0 : ℝ) ≤ kappa),
        let e0 : ℝ := kappa * (CE * (1 / 2 : ℝ));
        ∀ (_ : e0 = kappa * (CE * (1 / 2 : ℝ))),
          let k0 : ℝ := (2 : ℝ) * (↑d : ℝ) * (e0 ^ (2 : ℕ) + (1 : ℝ));
          ∀ (_ : k0 = (2 : ℝ) * (↑d : ℝ) * (e0 ^ (2 : ℕ) + (1 : ℝ))) (M : ABKModel d) (s : ℝ) (_ :
            (0 : ℝ) < s)
            (L m n : ℤ) (x z : Vec d) (_ : s ≤ (1 : ℝ)) (omega : Cutoff.CutoffSample d)
            (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d) (S : ℝ)
            (_ :
              |volumeAverage
                    ((fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                      openCubeSet (originCube d (n + (2 : ℤ))))
                    fun (y : Vec d) => u.toFun y - hdat.toFun y| ≤
                S),
            let Erep : ℝ :=
              fluxCorrectedErrorRepresentative M L (n + (3 : ℤ)) ⟨s / (8 : ℝ), (by positivity)⟩
                (Cutoff.translateCutoffSample z omega);
            ∀ (_ : Erep ≤ CE * (1 / 2 : ℝ)) (_ : (0 : ℝ) ≤ Erep),
              let Eb : ℝ :=
                √(offGridStabilityConst d (s / (6 : ℝ)) (s / (8 : ℝ))) * ((3 : ℝ) ^ ((3 : ℝ) * (s
                  / (8 : ℝ))) * Erep);
              ∀
                (_ :
                  Eb =
                    √(offGridStabilityConst d (s / (6 : ℝ)) (s / (8 : ℝ))) * ((3 : ℝ) ^ ((3 : ℝ) *
                      (s / (8 : ℝ))) * Erep)),
                let sig : ℝ := (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ);
                ∀ (_ : (0 : ℝ) < sig),
                  let X : ℝ :=
                    (eLpNorm
                        (fun (y : Vec d) =>
                          u.toFun y -
                            volumeAverage
                              ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                                ℤ))) ∩
                                openCubeSet (originCube d m))
                              u.toFun)
                        (2 : ENNReal)
                        (normalizedVolumeMeasureOn
                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                            ℤ))) ∩
                            openCubeSet (originCube d m)))).toReal;
                  let Gs : ℝ :=
                    (normalizedGagliardoESeminormOn
                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                          openCubeSet (originCube d m))
                        s g).toReal;
                  let Hs : ℝ :=
                    (normalizedGagliardoESeminormOn
                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                          openCubeSet (originCube d m))
                        s hdat.grad).toReal;
                  let Hn : ℝ :=
                    (eLpNorm hdat.grad (2 : ENNReal)
                        (normalizedVolumeMeasureOn
                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                            ℤ))) ∩
                            openCubeSet (originCube d m)))).toReal;
                  let _ : ℝ :=
                    (normalizedGagliardoESeminormOn
                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2 : ℤ))) ∩
                          openCubeSet (originCube d m))
                        s g).toReal;
                  let _ : ℝ :=
                    (normalizedGagliardoESeminormOn ((fun (y : Vec d) => x + y) '' openCubeSet
                      (originCube d n)) s
                        g).toReal;
                  let _ : ℝ := Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ));
                  let Q3s : ℝ := Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ));
                  let Q3sn : ℝ := Real.rpow (3 : ℝ) (s * (↑n : ℝ));
                  let Q1s : ℝ := Real.rpow (3 : ℝ) (((1 : ℝ) + s) * (↑n : ℝ));
                  let R3n : ℝ := Real.rpow (3 : ℝ) (↑n : ℝ);
                  let S4 : ℝ := s.rpow (-4 : ℝ);
                  let S7 : ℝ := s.rpow (-7 : ℝ);
                  let S6 : ℝ := s.rpow (-6 : ℝ);
                  let Sm3 : ℝ := s.rpow (-3 : ℝ);
                  let Sm2 : ℝ := s.rpow (-2 : ℝ);
                  (0 : ℝ) ≤ X ∧
                    (0 : ℝ) ≤ Gs ∧
                      (0 : ℝ) ≤ Hs ∧
                        (0 : ℝ) ≤ Hn ∧
                          (0 : ℝ) ≤ S ∧
                            (0 : ℝ) ≤ Q3s ∧
                              (0 : ℝ) ≤ Q3sn ∧
                                (0 : ℝ) ≤ Q1s ∧
                                  (0 : ℝ) ≤ R3n ∧
                                    (0 : ℝ) ≤ S4 ∧
                                      (0 : ℝ) ≤ S7 ∧
                                        (0 : ℝ) ≤ S6 ∧
                                          (0 : ℝ) ≤ Sm3 ∧
                                            (0 : ℝ) ≤ Sm2 ∧
                                              (0 : ℝ) ≤ sig⁻¹ ∧
                                                (0 : ℝ) ≤ Eb ∧
                                                  Eb ≤ kappa * Erep ∧
                                                    Eb ≤ e0 ∧ (2 : ℝ) * (↑d : ℝ) * (Eb ^ (2 : ℕ) +
                                                      (1 : ℝ)) ≤ k0 := by
  intro d _ kappa hkappadef hkappa e0 he0def k0 hk0def _ s hs _ _ _ _ _ hs1 _ _ _ _ S hmean Erep
    hErepCap hErep0 Eb hEbdef sig hsig X Gs Hs Hn Y2 Ychild P2 Q3s Q3sn Q1s R3n S4 S7 S6 Sm3 Sm2
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hGs0 : 0 ≤ Gs := ENNReal.toReal_nonneg
  have hHs0 : 0 ≤ Hs := ENNReal.toReal_nonneg
  have hHn0 : 0 ≤ Hn := ENNReal.toReal_nonneg
  have hY20 : 0 ≤ Y2 := ENNReal.toReal_nonneg
  have hYchild0 : 0 ≤ Ychild := ENNReal.toReal_nonneg
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) hmean
  have hP20 : 0 ≤ P2 := Real.rpow_nonneg (by norm_num) _
  have hQ3s0 : 0 ≤ Q3s := Real.rpow_nonneg (by norm_num) _
  have hQ3sn0 : 0 ≤ Q3sn := Real.rpow_nonneg (by norm_num) _
  have hQ1s0 : 0 ≤ Q1s := Real.rpow_nonneg (by norm_num) _
  have hR3n0 : 0 ≤ R3n := Real.rpow_nonneg (by norm_num) _
  have hS40 : 0 ≤ S4 := Real.rpow_nonneg hs.le _
  have hS70 : 0 ≤ S7 := Real.rpow_nonneg hs.le _
  have hS60 : 0 ≤ S6 := Real.rpow_nonneg hs.le _
  have hSm30 : 0 ≤ Sm3 := Real.rpow_nonneg hs.le _
  have hSm20 : 0 ≤ Sm2 := Real.rpow_nonneg hs.le _
  have hsiginv0 : (0 : ℝ) ≤ sig⁻¹ := inv_nonneg.mpr hsig.le
  -- the off-grid error factor
  have hEb0 : 0 ≤ Eb := by
    rw [hEbdef]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hErep0)
  have hEbkappa : Eb ≤ kappa * Erep := by
    have h1 : Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) ≤
        Real.sqrt (192 * (d : ℝ)) :=
      Real.sqrt_le_sqrt (offGridStabilityConst_slot_le hs hs1)
    have h2 : ((3 : ℝ) ^ (3 * (s / 8))) ≤ 3 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (by linarith only [hs1] : 3 * (s / 8) ≤ (1 : ℝ))
      rwa [Real.rpow_one] at h
    have h3 : (3 : ℝ) ^ (3 * (s / 8)) * Erep ≤ 3 * Erep :=
      mul_le_mul_of_nonneg_right h2 hErep0
    have h4 : (0 : ℝ) ≤ (3 : ℝ) ^ (3 * (s / 8)) * Erep :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hErep0
    rw [hEbdef]
    calc Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
          ((3 : ℝ) ^ (3 * (s / 8)) * Erep)
        ≤ Real.sqrt (192 * (d : ℝ)) * (3 * Erep) :=
          mul_le_mul h1 h3 h4 (Real.sqrt_nonneg _)
      _ = kappa * Erep := by rw [hkappadef]; ring
  have hEbe0 : Eb ≤ e0 := by
    refine hEbkappa.trans ?_
    rw [he0def]
    exact mul_le_mul_of_nonneg_left hErepCap hkappa
  -- (b) the bracket cap
  have hKble : 2 * (d : ℝ) * (Eb ^ 2 + 1) ≤ k0 := by
    rw [hk0def]
    have hsq : Eb ^ 2 ≤ e0 ^ 2 := pow_le_pow_left₀ hEb0 hEbe0 2
    exact mul_le_mul_of_nonneg_left (by linarith only [hsq])
      (mul_nonneg zero_le_two (Nat.cast_nonneg d))
  exact ⟨hX0, hGs0, hHs0, hHn0, hS0, hQ3s0, hQ3sn0, hQ1s0, hR3n0, hS40, hS70, hS60, hSm30, hSm20,
    hsiginv0, hEb0, hEbkappa, hEbe0, hKble⟩

private theorem assemblyComposedErrorWeighted_comparisonBounds4 : ∀ (d : ℕ) (b0 cg A2 : ℝ)
      (_ : A2 = cg * (1944 : ℝ) * (b0 * (besovGagliardoConstant d * (gagliardoWindowConst d *
        windowMoveConst d))))
      (_ : (0 : ℝ) ≤ A2) (A3 : ℝ) (_ : A3 = interiorCorrectionConst d * (gagliardoWindowConst d *
        windowMoveConst d))
      (_ : (0 : ℝ) ≤ A3) (s S Erep : ℝ) (_ : (0 : ℝ) ≤ Erep) (sig X Gs Hs Hn Q3sn Q1s R3n S4 S7 S6
        : ℝ)
      (_ : (0 : ℝ) ≤ X) (_ : (0 : ℝ) ≤ Gs) (_ : (0 : ℝ) ≤ Hs) (_ : (0 : ℝ) ≤ Hn) (_ : (0 : ℝ) ≤ S)
      (_ : (0 : ℝ) ≤ Q1s) (_ : (0 : ℝ) ≤ R3n) (_ : (0 : ℝ) ≤ S4) (_ : (0 : ℝ) ≤ S7) (_ : (0 : ℝ) ≤
        S6)
      (_ : (0 : ℝ) ≤ sig⁻¹) (_ : s⁻¹ ^ (6 : ℕ) = S6) (_ : S6 ≤ S7) (_ : s.rpow (-(1 / 2 : ℝ)) ≤ S7)
      (_ : R3n * Q3sn = Q1s),
      sig⁻¹ * R3n *
            (cg *
              ((1944 : ℝ) * s⁻¹ ^ (6 : ℕ) *
                (b0 * (besovGagliardoConstant d * Q3sn * (gagliardoWindowConst d * windowMoveConst
                  d * Gs))))) ≤
          A2 * (S7 * sig⁻¹ * Q1s * Gs) ∧
        sig⁻¹ * R3n *
              (interiorCorrectionConst d * s.rpow (-(1 / 2 : ℝ)) * Q3sn *
                (gagliardoWindowConst d * windowMoveConst d * Gs)) ≤
            A3 * (S7 * sig⁻¹ * Q1s * Gs) ∧
          (0 : ℝ) ≤ S4 * Erep * X ∧
            (0 : ℝ) ≤ S4 * Erep * S ∧
              (0 : ℝ) ≤ S7 * sig⁻¹ * Q1s * Gs ∧ (0 : ℝ) ≤ S6 * Q1s * Hs ∧ (0 : ℝ) ≤ S6 * Erep *
                R3n * Hn := by
  intro d _ b0 cg A2 hA2def hA2 A3 hA3def hA3 s S Erep hErep0 sig X Gs Hs Hn Q3sn Q1s R3n S4 S7 S6
    hX0 hGs0 hHs0 hHn0 hS0 hQ1s0 hR3n0 hS40 hS70 hS60 hsiginv0 hS6eq hS6le hQScle hRQ3sn
  have hT2 : (sig⁻¹ * R3n) * (cg * (1944 * (s⁻¹) ^ (6 : ℕ) *
        (b0 * (besovGagliardoConstant d * Q3sn *
          (gagliardoWindowConst d * windowMoveConst d * Gs))))) ≤
      A2 * (S7 * sig⁻¹ * Q1s * Gs) := by
    have hrw : (sig⁻¹ * R3n) * (cg * (1944 * (s⁻¹) ^ (6 : ℕ) *
          (b0 * (besovGagliardoConstant d * Q3sn *
            (gagliardoWindowConst d * windowMoveConst d * Gs))))) =
        A2 * ((s⁻¹) ^ (6 : ℕ) * (sig⁻¹ * ((R3n * Q3sn) * Gs))) := by
      rw [hA2def]; ring
    rw [hrw, hRQ3sn, hS6eq]
    have hnn : (0 : ℝ) ≤ sig⁻¹ * (Q1s * Gs) :=
      mul_nonneg hsiginv0 (mul_nonneg hQ1s0 hGs0)
    calc A2 * (S6 * (sig⁻¹ * (Q1s * Gs)))
        ≤ A2 * (S7 * (sig⁻¹ * (Q1s * Gs))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS6le hnn) hA2
      _ = A2 * (S7 * sig⁻¹ * Q1s * Gs) := by ring
  have hT3 : (sig⁻¹ * R3n) * (interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) *
        Q3sn * (gagliardoWindowConst d * windowMoveConst d * Gs)) ≤
      A3 * (S7 * sig⁻¹ * Q1s * Gs) := by
    have hrw : (sig⁻¹ * R3n) * (interiorCorrectionConst d *
          Real.rpow s (-(1 / 2 : ℝ)) * Q3sn *
          (gagliardoWindowConst d * windowMoveConst d * Gs)) =
        A3 * (Real.rpow s (-(1 / 2 : ℝ)) * (sig⁻¹ * ((R3n * Q3sn) * Gs))) := by
      rw [hA3def]; ring
    rw [hrw, hRQ3sn]
    have hnn : (0 : ℝ) ≤ sig⁻¹ * (Q1s * Gs) :=
      mul_nonneg hsiginv0 (mul_nonneg hQ1s0 hGs0)
    calc A3 * (Real.rpow s (-(1 / 2 : ℝ)) * (sig⁻¹ * (Q1s * Gs)))
        ≤ A3 * (S7 * (sig⁻¹ * (Q1s * Gs))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQScle hnn) hA3
      _ = A3 * (S7 * sig⁻¹ * Q1s * Gs) := by ring
  -- (h) the conclusion
  have hXterm : (0 : ℝ) ≤ S4 * Erep * X := mul_nonneg (mul_nonneg hS40 hErep0) hX0
  have hSterm : (0 : ℝ) ≤ S4 * Erep * S := mul_nonneg (mul_nonneg hS40 hErep0) hS0
  have hGterm : (0 : ℝ) ≤ S7 * sig⁻¹ * Q1s * Gs :=
    mul_nonneg (mul_nonneg (mul_nonneg hS70 hsiginv0) hQ1s0) hGs0
  have hHsterm : (0 : ℝ) ≤ S6 * Q1s * Hs :=
    mul_nonneg (mul_nonneg hS60 hQ1s0) hHs0
  have hHnterm : (0 : ℝ) ≤ S6 * Erep * R3n * Hn :=
    mul_nonneg (mul_nonneg (mul_nonneg hS60 hErep0) hR3n0) hHn0
  exact ⟨hT2, hT3, hXterm, hSterm, hGterm, hHsterm, hHnterm⟩

private theorem assemblyComposedErrorWeighted_comparisonBounds5 :
  assemblyComposedErrorWeighted_comparisonBounds5_statement := by
  classical
  intro d _ CE KE kappa hkappadef hkappa e0 he0def k0 hk0def b0 hb0def hb0 M s hs L m n hmL hnm x
    z hgeom hs1 omega hcapE hEnLeg herrD hbrk hmem u hdat g S hsol hgL2 hgW hhW hmean v w hharm
      hval hgrad
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 3) : ℝ) :=
    (Annealed.sigmaBar M (n + 3)).2
  have hsubx : translateSet x (openCubeSet (originCube d n)) ⊆
      openCubeSet (originCube d m) :=
    translateSet_openCubeSet_subset_of_anchorGeometry hgeom
  have hsubimg : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      openCubeSet (originCube d m) := fun p hp => (hgeom hp).2
  have hW20 : volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
      openCubeSet (originCube d m))) ≠ 0 := volume_anchorWindowInner_ne_zero hgeom
  have hW3top := volume_anchorWindow_ne_top (n + 3) m z
  have hW30 : volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m))) ≠ 0 := by
    intro hzero
    have hmono := measure_mono (μ := (volume : Measure (Vec d)))
      (anchorWindowInner_subset_anchorWindow (d := d) n m z)
    rw [hzero, le_zero_iff] at hmono
    exact hW20 hmono
  have hgL2W2 := memLp_normalizedVolumeMeasureOn_subset
    (Set.inter_subset_right
      (s := (fun y' => z + y') '' openCubeSet (originCube d (n + 2))))
    (volume_openCubeSet_ne_zero (originCube d m))
    (volume_openCubeSet_ne_top (originCube d m)) hW20 hgL2
  have hgWW2 := memLp_normalizedGagliardoMeasureOn_subset
    (Set.inter_subset_right
      (s := (fun y' => z + y') '' openCubeSet (originCube d (n + 2))))
    (volume_openCubeSet_ne_zero (originCube d m))
    (volume_openCubeSet_ne_top (originCube d m)) hW20 hgW
  have hgWW3 := memLp_normalizedGagliardoMeasureOn_subset
    (Set.inter_subset_right
      (s := (fun y' => z + y') '' openCubeSet (originCube d (n + 3))))
    (volume_openCubeSet_ne_zero (originCube d m))
    (volume_openCubeSet_ne_top (originCube d m)) hW30 hgW
  have hgL2child := memLp_two_child_of_clause_iv hsubimg hgL2
  have hgWchild := memLp_two_gagliardo_child_of_clause_iv hsubimg hgW
  -- the deterministic `x`-frame composition
  have hxf := eLpNorm_sub_weaklyHarmonic_le_coarseGraining_rebased_addThree (z := z) M L omega
    hs hs1 hsubx u hdat g hsol hgL2 hgW v w hharm hval hgrad
    (Annealed.sigmaBar M (n + 3)).2
  -- the energy leg
  have hEn := hEnLeg hmem u hdat g S hsol hgL2 hgW hhW hmean hsubx
  set Erep : ℝ := Support.fluxCorrectedErrorRepresentative M L (n + 3)
    ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) with hErepdef
  have hErepCap : Erep ≤ CE * (1 / 2) := hcapE hmem L (le_trans hnm hmL)
  have hErep0 : 0 ≤ Erep := Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  set Eb : ℝ := Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
    ((3 : ℝ) ^ (3 * (s / 8)) * Erep) with hEbdef
  set sig : ℝ := (Annealed.sigmaBar M (n + 3) : ℝ) with hsigdef
  set X : ℝ := (eLpNorm (fun y => u.toFun y -
      volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal with hXdef
  set Gs : ℝ := (Support.normalizedGagliardoESeminormOn
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) s g).toReal with hGsdef
  set Hs : ℝ := (Support.normalizedGagliardoESeminormOn
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) s hdat.grad).toReal with hHsdef
  set Hn : ℝ := (eLpNorm hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal with hHndef
  set Y2 : ℝ := (Support.normalizedGagliardoESeminormOn
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
        openCubeSet (originCube d m))) s g).toReal with hY2def
  set Ychild : ℝ := (Support.normalizedGagliardoESeminormOn
      ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal with hYchilddef
  set Lhs : ℝ := (eLpNorm (fun y => u.toFun y - v.toFun y) 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => x + y) '' openCubeSet (originCube d n)))).toReal with hLhsdef
  set P2 : ℝ := Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) with hP2def
  set Q3s : ℝ := Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) with hQ3sdef
  set Q3sn : ℝ := Real.rpow (3 : ℝ) (s * (n : ℝ)) with hQ3sndef
  set Q1s : ℝ := Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) with hQ1sdef
  set R3n : ℝ := Real.rpow (3 : ℝ) ((n : ℝ)) with hR3ndef
  set S4 : ℝ := Real.rpow s (-(4 : ℝ)) with hS4def
  set S7 : ℝ := Real.rpow s (-(7 : ℝ)) with hS7def
  set S6 : ℝ := Real.rpow s (-(6 : ℝ)) with hS6def
  set Sm3 : ℝ := Real.rpow s (-(3 : ℝ)) with hSm3def
  set Sm2 : ℝ := Real.rpow s (-(2 : ℝ)) with hSm2def
  obtain ⟨hX0, hGs0, hHs0, hHn0, hS0, hQ3s0, hQ3sn0, hQ1s0, hR3n0, hS40, hS70, hS60, hSm30, hSm20,
    hsiginv0, hEb0, hEbkappa, hEbe0, hKble⟩ :=
    (show (0 ≤ X) ∧ (0 ≤ Gs) ∧ (0 ≤ Hs) ∧ (0 ≤ Hn) ∧ (0 ≤ S) ∧ (0 ≤ Q3s) ∧ (0 ≤ Q3sn) ∧ (0 ≤ Q1s)
      ∧ (0 ≤ R3n) ∧ (0 ≤ S4) ∧ (0 ≤ S7) ∧ (0 ≤ S6) ∧ (0 ≤ Sm3) ∧ (0 ≤ Sm2) ∧ ((0 : ℝ) ≤ sig⁻¹) ∧
        (0 ≤ Eb) ∧ (Eb ≤ kappa * Erep) ∧ (Eb ≤ e0) ∧ (2 * (d : ℝ) * (Eb ^ 2 + 1) ≤ k0) from
      @assemblyComposedErrorWeighted_comparisonBounds3 (d) (CE) (hkappadef) (hkappa) (he0def)
        (hk0def) (M) (s) (hs) (L) (m) (n) (x) (z) (hs1) (omega) (u) (hdat) (g) (S) (hmean)
          (hErepCap) (hErep0) (hEbdef) (hsig))
  obtain ⟨hbrkCap, hET, hGbes, hGbes0, hYchild3⟩ :=
    (show (coarseGrainingForceBracket (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) ≤ b0) ∧ (coarseGrainingEnergyTerm
        (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3)
      (H1Function.untranslate x
        (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx)) ≤
      kappa * KE * Erep *
        (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
          Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))) ∧
            (Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s
      (fun y => -g (y + x)) ≤ besovGagliardoConstant d * Q3sn * Ychild) ∧ (0 ≤
        Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo
      (originCube d n) s (fun y => -g (y + x))) ∧ (Ychild ≤ gagliardoWindowConst d *
        windowMoveConst d * Gs) from
      @assemblyComposedErrorWeighted_comparisonBounds2 (d) (by infer_instance) (CE) (KE) (hkappa)
        (hb0def) (M) (s) (hs) (L) (m) (n) (x) (z) (hgeom) (hs1) (omega) (u) (hdat) (g) (S) (hsubx)
          (hgWW2) (hgWW3) (hgL2child) (hgWchild) (hErep0) (herrD) (hbrk) (hsig) (hEn) (hEb0)
            (hEbkappa) (hEbe0) (hKble))
  have hFT : coarseGrainingForceTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) s
      (fun y => -g (y + x)) ≤
      b0 * (besovGagliardoConstant d * Q3sn *
        (gagliardoWindowConst d * windowMoveConst d * Gs)) := by
    rw [coarseGrainingForceTerm]
    refine mul_le_mul hbrkCap ?_ hGbes0 hb0
    refine hGbes.trans ?_
    exact mul_le_mul_of_nonneg_left hYchild3
      (mul_nonneg (besovGagliardoConstant_nonneg d) hQ3sn0)
  exact ⟨hsubx, hErepCap, hErep0, hsig, hP2def, hQ3sdef, hxf, hQ3sndef, hQ1sdef, hR3ndef, hS4def,
    hS7def, hS6def, hSm3def, hSm2def, hX0, hGs0, hHs0, hHn0, hS0, hQ3s0, hQ3sn0, hQ1s0, hR3n0,
      hS40, hS70, hS60, hSm30, hSm20, hsiginv0, hET, hYchild3, hFT, True.intro⟩

private theorem assemblyComposedErrorWeighted_comparisonBounds6 :
    ∀ (d : ℕ) [NeZero d] (CE KE : ℝ),
      let kappa : ℝ := √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ);
      let e0 : ℝ := kappa * (CE * (1 / 2 : ℝ));
      let k0 : ℝ := (2 : ℝ) * (↑d : ℝ) * (e0 ^ (2 : ℕ) + (1 : ℝ));
      let b0 : ℝ := √k0 * e0 + (2 : ℝ) * k0;
      let cg : ℝ := (3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d;
      ∀ (M : ABKModel d) (s : ℝ) (_ : (0 : ℝ) < s) (L m n : ℤ) (x z : Vec d) (omega :
        Cutoff.CutoffSample d)
        (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d) (S : ℝ)
        (v : H1Function ((fun (y : Vec d) => x + y) '' openCubeSet (originCube d n)))
        (hsubx : translateSet x (openCubeSet (originCube d n)) ⊆ openCubeSet (originCube d m)),
        let Erep : ℝ :=
          fluxCorrectedErrorRepresentative M L (n + (3 : ℤ)) ⟨s / (8 : ℝ), (by positivity)⟩
            (Cutoff.translateCutoffSample z omega);
        let sig : ℝ := (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ);
        ∀ (_ : (0 : ℝ) < sig) (_ : (0 : ℝ) ≤ sig⁻¹),
          let X : ℝ :=
            (eLpNorm
                (fun (y : Vec d) =>
                  u.toFun y -
                    volumeAverage
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                        openCubeSet (originCube d m))
                      u.toFun)
                (2 : ENNReal)
                (normalizedVolumeMeasureOn
                  ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                    openCubeSet (originCube d m)))).toReal;
          let Gs : ℝ :=
            (normalizedGagliardoESeminormOn
                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                  openCubeSet (originCube d m)) s
                g).toReal;
          let Hs : ℝ :=
            (normalizedGagliardoESeminormOn
                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                  openCubeSet (originCube d m)) s
                hdat.grad).toReal;
          let Hn : ℝ :=
            (eLpNorm hdat.grad (2 : ENNReal)
                (normalizedVolumeMeasureOn
                  ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                    openCubeSet (originCube d m)))).toReal;
          let Ychild : ℝ :=
            (normalizedGagliardoESeminormOn ((fun (y : Vec d) => x + y) '' openCubeSet (originCube
              d n)) s g).toReal;
          ∀ (_ : Ychild ≤ gagliardoWindowConst d * windowMoveConst d * Gs),
            let Lhs : ℝ :=
              (eLpNorm (fun (y : Vec d) => u.toFun y - v.toFun y) (2 : ENNReal)
                  (normalizedVolumeMeasureOn ((fun (y : Vec d) => x + y) '' openCubeSet
                    (originCube d n)))).toReal;
            let P2 : ℝ := Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ));
            let Q3s : ℝ := Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ));
            let Q3sn : ℝ := Real.rpow (3 : ℝ) (s * (↑n : ℝ));
            ∀ (_ : (0 : ℝ) ≤ Q3sn),
              let R3n : ℝ := Real.rpow (3 : ℝ) (↑n : ℝ);
              ∀ (_ : (0 : ℝ) ≤ R3n),
                let Sm3 : ℝ := s.rpow (-3 : ℝ);
                let Sm2 : ℝ := s.rpow (-2 : ℝ);
                let ET : ℝ :=
                  coarseGrainingEnergyTerm (originCube d n) (parentRebasedFamily M L (n + (3 : ℤ))
                    x z omega)
                    (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s / (3 : ℝ))
                    (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n)
                      hsubx));
                ∀
                  (_ :
                    ET ≤
                      √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * KE * Erep *
                        ((↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) * (P2 * X) +
                                (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) * (P2 * S) +
                              Sm3 * (Q3s * Gs) +
                            Sm2 * ((↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) * (Q3s * Hs)) +
                          Sm2 * ((↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) * Hn))),
                  let FT : ℝ :=
                    coarseGrainingForceTerm (originCube d n) (parentRebasedFamily M L (n + (3 :
                      ℤ)) x z omega)
                      (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s / (3 :
                        ℝ)) s fun (y : Vec d) =>
                      -g (y + x);
                  ∀
                    (_ :
                      FT ≤
                        (√((2 : ℝ) * (↑d : ℝ) *
                                  ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) ^ (2 :
                                    ℕ) + (1 : ℝ))) *
                              (√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) +
                            (2 : ℝ) *
                              ((2 : ℝ) * (↑d : ℝ) *
                                ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) ^ (2 :
                                  ℕ) + (1 : ℝ)))) *
                          (besovGagliardoConstant d * Q3sn * (gagliardoWindowConst d *
                            windowMoveConst d * Gs)))
                    (_ :
                      (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) * (Real.rpow (3 : ℝ) (-(↑n : ℝ))
                        * Lhs) ≤
                        (3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d *
                            ((216 : ℝ) * s⁻¹ ^ (4 : ℕ) * ET + (1944 : ℝ) * s⁻¹ ^ (6 : ℕ) * FT) +
                          interiorCorrectionConst d * s.rpow (-(1 / 2 : ℝ)) * Q3sn * Ychild),
                    (0 : ℝ) ≤ sig⁻¹ * R3n ∧
                      sig⁻¹ * sig = (1 : ℝ) ∧
                        Lhs ≤
                            sig⁻¹ * R3n *
                              (cg * ((216 : ℝ) * s⁻¹ ^ (4 : ℕ) * ET + (1944 : ℝ) * s⁻¹ ^ (6 : ℕ) *
                                FT) +
                                interiorCorrectionConst d * s.rpow (-(1 / 2 : ℝ)) * Q3sn * Ychild) ∧
                          (216 : ℝ) * s⁻¹ ^ (4 : ℕ) * ET ≤
                              (216 : ℝ) * s⁻¹ ^ (4 : ℕ) *
                                (kappa * KE * Erep *
                                  (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) + Sm2 * (sig
                                    * (Q3s * Hs)) +
                                    Sm2 * (sig * Hn))) ∧
                            (1944 : ℝ) * s⁻¹ ^ (6 : ℕ) * FT ≤
                                (1944 : ℝ) * s⁻¹ ^ (6 : ℕ) *
                                  (b0 *
                                    (besovGagliardoConstant d * Q3sn * (gagliardoWindowConst d *
                                      windowMoveConst d * Gs))) ∧
                              interiorCorrectionConst d * s.rpow (-(1 / 2 : ℝ)) * Q3sn * Ychild ≤
                                interiorCorrectionConst d * s.rpow (-(1 / 2 : ℝ)) * Q3sn *
                                  (gagliardoWindowConst d * windowMoveConst d * Gs) := by
  classical
  intro d _ _ KE kappa _ _ b0 cg _ s hs _ _ n _ _ _ _ _ _ S _ _ Erep sig hsig hsiginv0 X Gs Hs Hn
    Ychild hYchild3 Lhs P2 Q3s Q3sn hQ3sn0 R3n hR3n0 Sm3 Sm2 ET hET FT hFT hxf
  have hxfr : sig * (Real.rpow (3 : ℝ) (-(n : ℝ)) * Lhs) ≤
      cg * (216 * (s⁻¹) ^ (4 : ℕ) * ET + 1944 * (s⁻¹) ^ (6 : ℕ) * FT) +
        interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn * Ychild := hxf
  have hfac0 : (0 : ℝ) ≤ sig⁻¹ * R3n := mul_nonneg hsiginv0 hR3n0
  have hsinv : sig⁻¹ * sig = 1 := inv_mul_cancel₀ hsig.ne'
  have hid : sig⁻¹ * R3n * (sig * (Real.rpow (3 : ℝ) (-(n : ℝ)) * Lhs)) = Lhs := by
    have h2 : Real.rpow (3 : ℝ) (-(n : ℝ)) * R3n = 1 := rpow_three_neg_mul_self n
    calc sig⁻¹ * R3n * (sig * (Real.rpow (3 : ℝ) (-(n : ℝ)) * Lhs))
        = (sig⁻¹ * sig) * ((Real.rpow (3 : ℝ) (-(n : ℝ)) * R3n) * Lhs) := by ring
      _ = 1 * (1 * Lhs) := by rw [hsinv, h2]
      _ = Lhs := by ring
  have hstep : Lhs ≤ (sig⁻¹ * R3n) *
      (cg * (216 * (s⁻¹) ^ (4 : ℕ) * ET + 1944 * (s⁻¹) ^ (6 : ℕ) * FT) +
        interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn * Ychild) := by
    rw [← hid]
    exact mul_le_mul_of_nonneg_left hxfr hfac0
  -- (f) the monotone replacement of the three legs
  have hccorr0 : (0 : ℝ) ≤ interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn :=
    mul_nonneg (mul_nonneg (interiorCorrectionConst_pos d).le
      (Real.rpow_nonneg hs.le _)) hQ3sn0
  have hleg1 : 216 * (s⁻¹) ^ (4 : ℕ) * ET ≤
      216 * (s⁻¹) ^ (4 : ℕ) *
        (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
          Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))) :=
    mul_le_mul_of_nonneg_left hET
      (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr hs.le) 4))
  have hleg2 : 1944 * (s⁻¹) ^ (6 : ℕ) * FT ≤
      1944 * (s⁻¹) ^ (6 : ℕ) *
        (b0 * (besovGagliardoConstant d * Q3sn *
          (gagliardoWindowConst d * windowMoveConst d * Gs))) :=
    mul_le_mul_of_nonneg_left hFT
      (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr hs.le) 6))
  have hleg3 : interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn * Ychild ≤
      interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn *
        (gagliardoWindowConst d * windowMoveConst d * Gs) :=
    mul_le_mul_of_nonneg_left hYchild3 hccorr0
  exact ⟨hfac0, hsinv, hstep, hleg1, hleg2, hleg3⟩

private theorem assemblyComposedErrorWeighted_comparisonBounds7 :
    ∀ (d : ℕ) [NeZero d],
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
        (_ : √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) = √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ)) (_ :
        (0 : ℝ) ≤ √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ)) (_ :
        √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ)) = √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ)
          * (CE * (1 / 2 : ℝ))) (_
        :
        (2 : ℝ) * (↑d : ℝ) * ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) ^ (2 : ℕ) +
          (1 : ℝ)) =
          (2 : ℝ) * (↑d : ℝ) * ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) ^ (2 : ℕ)
            + (1 : ℝ)))
        (_ :
        √((2 : ℝ) * (↑d : ℝ) * ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) ^ (2 : ℕ)
          + (1 : ℝ))) *
              (√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) +
            (2 : ℝ) *
              ((2 : ℝ) * (↑d : ℝ) * ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) ^ (2
                : ℕ) + (1 : ℝ))) =
          √((2 : ℝ) * (↑d : ℝ) * ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) ^ (2 :
            ℕ) + (1 : ℝ))) *
              (√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) +
            (2 : ℝ) * ((2 : ℝ) * (↑d : ℝ) * ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 :
              ℝ))) ^ (2 : ℕ) + (1 : ℝ))))
        (_ :
        (0 : ℝ) ≤
          √((2 : ℝ) * (↑d : ℝ) * ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) ^ (2 :
            ℕ) + (1 : ℝ))) *
              (√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) +
            (2 : ℝ) * ((2 : ℝ) * (↑d : ℝ) * ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 :
              ℝ))) ^ (2 : ℕ) + (1 : ℝ))))
        (_ : (0 : ℝ) ≤ (3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d) (_ :
        (3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d * (216 : ℝ) * (√((192 : ℝ) * (↑d :
          ℝ)) * (3 : ℝ) * KE) =
          (3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d * (216 : ℝ) * (√((192 : ℝ) * (↑d
            : ℝ)) * (3 : ℝ) * KE))
        (_ :
        (0 : ℝ) ≤
          (3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d * (216 : ℝ) * (√((192 : ℝ) * (↑d
            : ℝ)) * (3 : ℝ) * KE))
        (_ :
        (3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d * (1944 : ℝ) *
            ((√((2 : ℝ) * (↑d : ℝ) * ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) ^
              (2 : ℕ) + (1 : ℝ))) *
                  (√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) +
                (2 : ℝ) *
                  ((2 : ℝ) * (↑d : ℝ) * ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ)))
                    ^ (2 : ℕ) + (1 : ℝ)))) *
              (besovGagliardoConstant d * (gagliardoWindowConst d * windowMoveConst d))) =
          (3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d * (1944 : ℝ) *
            ((√((2 : ℝ) * (↑d : ℝ) * ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) ^
              (2 : ℕ) + (1 : ℝ))) *
                  (√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ))) +
                (2 : ℝ) *
                  ((2 : ℝ) * (↑d : ℝ) * ((√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * (CE * (1 / 2 : ℝ)))
                    ^ (2 : ℕ) + (1 : ℝ)))) *
              (besovGagliardoConstant d * (gagliardoWindowConst d * windowMoveConst d))))
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
        (_ :
        interiorCorrectionConst d * (gagliardoWindowConst d * windowMoveConst d) =
          interiorCorrectionConst d * (gagliardoWindowConst d * windowMoveConst d))
        (_ : (0 : ℝ) ≤ interiorCorrectionConst d * (gagliardoWindowConst d * windowMoveConst d))
          (_ :
        (0 : ℝ) ≤
          (9 : ℝ) * (CE * (1 / 2 : ℝ)) *
            ((3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d * (216 : ℝ) * (√((192 : ℝ) *
              (↑d : ℝ)) * (3 : ℝ) * KE)))
        (_ :
        (0 : ℝ) ≤
          CE * (1 / 2 : ℝ) *
            ((3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d * (216 : ℝ) *
              (√((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) * KE))),
        True := by
  classical
  intro d _
  obtain ⟨CE, hCEpos, hCE⟩ := ae_errorRepresentative_le_harmonicSlot_addThree d
  obtain ⟨CB, KE, hCBpos, hKEpos, hEnergyLeg⟩ :=
    ae_h1EnergyNormOnCube_boundary_le_anchorLegs d
  -- the explicit constants, exactly as in the interior composition
  set kappa : ℝ := Real.sqrt (192 * (d : ℝ)) * 3 with hkappadef
  have hkappa : 0 ≤ kappa := mul_nonneg (Real.sqrt_nonneg _) (by norm_num)
  set e0 : ℝ := kappa * (CE * (1 / 2)) with he0def
  have he0 : 0 ≤ e0 := mul_nonneg hkappa (mul_nonneg hCEpos.le (by norm_num))
  set k0 : ℝ := 2 * (d : ℝ) * (e0 ^ 2 + 1) with hk0def
  have hk0 : 0 ≤ k0 :=
    mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg d))
      (add_nonneg (sq_nonneg e0) zero_le_one)
  set b0 : ℝ := Real.sqrt k0 * e0 + 2 * k0 with hb0def
  have hb0 : 0 ≤ b0 :=
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) he0) (mul_nonneg zero_le_two hk0)
  set cg : ℝ := 3 * negNormBaseConst d * coarseGrainingP2Const d with hcgdef
  have hcg : 0 ≤ cg :=
    mul_nonneg (mul_nonneg (by norm_num) (negNormBaseConst_pos d).le)
      (coarseGrainingP2Const_pos d).le
  set A1 : ℝ := cg * 216 * (kappa * KE) with hA1def
  have hA1 : 0 ≤ A1 := by
    rw [hA1def]
    exact mul_nonneg (mul_nonneg hcg (by norm_num)) (mul_nonneg hkappa hKEpos.le)
  set A2 : ℝ := cg * 1944 *
    (b0 * (besovGagliardoConstant d * (gagliardoWindowConst d * windowMoveConst d)))
    with hA2def
  have hA2 : 0 ≤ A2 := by
    have h1 : 0 ≤ besovGagliardoConstant d := besovGagliardoConstant_nonneg d
    have h2 : 0 < gagliardoWindowConst d := gagliardoWindowConst_pos d
    have h3 : 0 < windowMoveConst d := windowMoveConst_pos d
    rw [hA2def]
    exact mul_nonneg (mul_nonneg hcg (by norm_num))
      (mul_nonneg hb0 (mul_nonneg h1 (mul_nonneg h2.le h3.le)))
  set A3 : ℝ := interiorCorrectionConst d * (gagliardoWindowConst d * windowMoveConst d)
    with hA3def
  have hA3 : 0 ≤ A3 := by
    have h1 : 0 < interiorCorrectionConst d := interiorCorrectionConst_pos d
    have h2 : 0 < gagliardoWindowConst d := gagliardoWindowConst_pos d
    have h3 : 0 < windowMoveConst d := windowMoveConst_pos d
    rw [hA3def]
    exact mul_nonneg h1.le (mul_nonneg h2.le h3.le)
  have hCE2 : (0 : ℝ) ≤ 9 * (CE * (1 / 2)) * A1 :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCEpos.le (by norm_num))) hA1
  have hCE3 : (0 : ℝ) ≤ CE * (1 / 2) * A1 :=
    mul_nonneg (mul_nonneg hCEpos.le (by norm_num)) hA1
  exact ⟨CE, hCEpos, hCE, CB, KE, hCBpos, hEnergyLeg, hkappadef, hkappa, he0def, hk0def, hb0def,
    hb0, hcg, hA1def, hA1, hA2def, hA2, hA3def, hA3, hCE2, hCE3, True.intro⟩

private theorem assemblyComposedErrorWeighted_comparisonBounds8 :
    ∀ (d : ℕ) (CE KE kappa b0 cg A1 : ℝ) (_ : A1 = A1) (_ : (0 : ℝ) ≤ A1)
      (_ : A1 = cg * (216 : ℝ) * (kappa * KE)) (A2 : ℝ) (_ : A2 = A2) (_ : (0 : ℝ) ≤ A2)
      (_ : A2 = cg * (1944 : ℝ) * (b0 * (besovGagliardoConstant d * (gagliardoWindowConst d *
        windowMoveConst d))))
      (A3 : ℝ) (_ : A3 = A3) (_ : (0 : ℝ) ≤ A3)
      (_ : A3 = interiorCorrectionConst d * (gagliardoWindowConst d * windowMoveConst d)) (s
        : ℝ) (_ : (0 : ℝ) < s)
      (n : ℤ) (_ : s ≤ (1 : ℝ)) (S : ℝ) (_ : (0 : ℝ) ≤ S) (Erep : ℝ) (_ : Erep ≤ CE *
        (1 / 2 : ℝ))
      (_ : (0 : ℝ) ≤ Erep) (sig : ℝ) (_ : (0 : ℝ) ≤ sig⁻¹) (X : ℝ) (_ : (0 : ℝ) ≤ X)
        (Gs : ℝ)
      (_ : (0 : ℝ) ≤ Gs) (Hs : ℝ) (_ : (0 : ℝ) ≤ Hs) (Hn : ℝ) (_ : (0 : ℝ) ≤ Hn) (P2 : ℝ)
        (_ : P2 = P2)
      (_ : P2 = Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ))) (Q3s : ℝ) (_ : Q3s = Q3s)
        (_ : (0 : ℝ) ≤ Q3s)
      (_ : Q3s = Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ))) (Q3sn : ℝ) (_ : Q3sn =
        Q3sn)
      (_ : Q3sn = Real.rpow (3 : ℝ) (s * (↑n : ℝ))) (Q1s : ℝ) (_ : Q1s = Q1s) (_
        : (0 : ℝ) ≤ Q1s)
      (_ : Q1s = Real.rpow (3 : ℝ) (((1 : ℝ) + s) * (↑n : ℝ))) (R3n : ℝ) (_ : R3n =
        R3n) (_ : (0 : ℝ) ≤ R3n)
      (_ : R3n = Real.rpow (3 : ℝ) (↑n : ℝ)) (S4 : ℝ) (_ : S4 = S4) (_ : (0 : ℝ) ≤ S4)
      (_ : S4 = s.rpow (-4 : ℝ)) (S7 : ℝ) (_ : S7 = S7) (_ : (0 : ℝ) ≤ S7) (_ :
        S7 = s.rpow (-7 : ℝ))
      (S6 : ℝ) (_ : S6 = S6) (_ : (0 : ℝ) ≤ S6) (_ : S6 = s.rpow (-6 : ℝ)) (Sm3 : ℝ)
        (_ : Sm3 = Sm3)
      (_ : (0 : ℝ) ≤ Sm3) (_ : Sm3 = s.rpow (-3 : ℝ)) (Sm2 : ℝ) (_ : Sm2 = Sm2)
        (_ : (0 : ℝ) ≤ Sm2)
      (_ : Sm2 = s.rpow (-2 : ℝ)) (_ : sig⁻¹ * sig = (1 : ℝ)),
      sig⁻¹ * R3n *
            (cg *
              ((216 : ℝ) * s⁻¹ ^ (4 : ℕ) *
                (kappa * KE * Erep *
                  (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) + Sm2 * (sig * (Q3s * Hs)) +
                    Sm2 * (sig * Hn))))) ≤
          A1 * (S4 * Erep * X) + (9 : ℝ) * (CE * (1 / 2 : ℝ)) * A1 * (S7 * sig⁻¹ * Q1s * Gs) +
                (9 : ℝ) * (CE * (1 / 2 : ℝ)) * A1 * (S6 * Q1s * Hs) +
              A1 * (S6 * Erep * R3n * Hn) +
            A1 * (S4 * Erep * S) ∧
        sig⁻¹ * R3n *
              (cg *
                ((1944 : ℝ) * s⁻¹ ^ (6 : ℕ) *
                  (b0 * (besovGagliardoConstant d * Q3sn * (gagliardoWindowConst d *
                    windowMoveConst d * Gs))))) ≤
            A2 * (S7 * sig⁻¹ * Q1s * Gs) ∧
          sig⁻¹ * R3n *
                (interiorCorrectionConst d * s.rpow (-(1 / 2 : ℝ)) * Q3sn *
                  (gagliardoWindowConst d * windowMoveConst d * Gs)) ≤
              A3 * (S7 * sig⁻¹ * Q1s * Gs) ∧
            (0 : ℝ) ≤ S4 * Erep * X ∧
              (0 : ℝ) ≤ S4 * Erep * S ∧
                (0 : ℝ) ≤ S7 * sig⁻¹ * Q1s * Gs ∧ (0 : ℝ) ≤ S6 * Q1s * Hs ∧ (0 : ℝ) ≤ S6 * Erep *
                  R3n * Hn := by
  classical
  intro d _ CE KE kappa b0 cg A1 hA1def hA1 hA1def A2 hA2def hA2 hA2def A3 hA3def hA3 hA3def s hs
    n hs1 S hS0 Erep hErepCap hErep0 sig hsiginv0 X hX0 Gs hGs0 Hs hHs0 Hn hHn0 P2 hP2def hP2def
      Q3s hQ3sdef hQ3s0 hQ3sdef Q3sn hQ3sndef hQ3sndef Q1s hQ1sdef hQ1s0 hQ1sdef R3n hR3ndef hR3n0
        hR3ndef S4 hS4def hS40 hS4def S7 hS7def hS70 hS7def S6 hS6def hS60 hS6def Sm3 hSm3def
          hSm30 hSm3def Sm2 hSm2def hSm20 hSm2def hsinv
  have hS4eq : (s⁻¹) ^ (4 : ℕ) = S4 := by
    rw [hS4def, inv_pow_eq_rpow_neg hs 4]
    congr 1
  have hS6eq : (s⁻¹) ^ (6 : ℕ) = S6 := by
    rw [hS6def, inv_pow_eq_rpow_neg hs 6]
    congr 1
  have hS4Sm3 : S4 * Sm3 = S7 := by
    rw [hS4def, hSm3def, hS7def]
    exact rpow_s_four_mul_three hs
  have hS4Sm2 : S4 * Sm2 = S6 := by
    rw [hS4def, hSm2def, hS6def]
    exact rpow_neg_four_mul_neg_two hs
  have hS6le : S6 ≤ S7 := by
    rw [hS6def, hS7def]
    exact rpow_le_rpow_neg_seven hs hs1 (by norm_num)
  have hQScle : Real.rpow s (-(1 / 2 : ℝ)) ≤ S7 := by
    rw [hS7def]
    exact rpow_le_rpow_neg_seven hs hs1 (by norm_num)
  obtain ⟨hRQ3sn, hT1⟩ :=
    (show (R3n * Q3sn = Q1s) ∧ ((sig⁻¹ * R3n) * (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
        (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
          Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))))) ≤
      A1 * (S4 * Erep * X) + (9 * (CE * (1 / 2)) * A1) * (S7 * sig⁻¹ * Q1s * Gs) +
        (9 * (CE * (1 / 2)) * A1) * (S6 * Q1s * Hs) +
        A1 * (S6 * Erep * R3n * Hn) + A1 * (S4 * Erep * S)) from
      @assemblyComposedErrorWeighted_comparisonBounds1 (CE) (KE) (kappa) (cg) (A1) (hA1def) (hA1)
        (s) (hs) (n) (hs1) (S) (Erep) (hErepCap) (hErep0) (sig) (X) (Gs) (Hs) (Hn) (P2) (hP2def)
          (Q3s) (hQ3sdef) (Q3sn) (hQ3sndef) (Q1s) (hQ1sdef) (R3n) (hR3ndef) (S4) (S7) (S6) (Sm3)
            (Sm2) (hX0) (hGs0) (hHs0) (hS0) (hQ3s0) (hR3n0) (hSm30) (hSm20) (hsiginv0) (hsinv)
              (hS4eq) (hS4Sm3) (hS4Sm2))
  obtain ⟨hT2, hT3, hXterm, hSterm, hGterm, hHsterm, hHnterm⟩ :=
    (show ((sig⁻¹ * R3n) * (cg * (1944 * (s⁻¹) ^ (6 : ℕ) *
        (b0 * (besovGagliardoConstant d * Q3sn *
          (gagliardoWindowConst d * windowMoveConst d * Gs))))) ≤
      A2 * (S7 * sig⁻¹ * Q1s * Gs)) ∧ ((sig⁻¹ * R3n) * (interiorCorrectionConst d * Real.rpow s
        (-(1 / 2 : ℝ)) *
        Q3sn * (gagliardoWindowConst d * windowMoveConst d * Gs)) ≤
      A3 * (S7 * sig⁻¹ * Q1s * Gs)) ∧ ((0 : ℝ) ≤ S4 * Erep * X) ∧ ((0 : ℝ) ≤ S4 * Erep * S) ∧ ((0
        : ℝ) ≤ S7 * sig⁻¹ * Q1s * Gs) ∧ ((0 : ℝ) ≤ S6 * Q1s * Hs) ∧ ((0 : ℝ) ≤ S6 * Erep * R3n *
          Hn) from
      @assemblyComposedErrorWeighted_comparisonBounds4 (d) (b0) (cg) (A2)
        (hA2def) (hA2) (A3) (hA3def) (hA3) (s) (S) (Erep) (hErep0) (sig) (X) (Gs) (Hs) (Hn) (Q3sn)
          (Q1s) (R3n) (S4) (S7) (S6) (hX0) (hGs0) (hHs0) (hHn0) (hS0) (hQ1s0) (hR3n0) (hS40)
            (hS70) (hS60) (hsiginv0) (hS6eq) (hS6le) (hQScle) (hRQ3sn))
  exact ⟨hT1, hT2, hT3, hXterm, hSterm, hGterm, hHsterm, hHnterm⟩

/-- **The boundary branch of the error-weighted general clause, composed.**

The deterministic `x`-frame envelope with the boundary energy leg substituted:
no frontier condition is used, so the display holds at every `z`. -/
theorem exists_boundaryClauseComposed_honest_errorWeighted (d : ℕ) [NeZero d] :
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
                            Real.rpow s (-(6 : ℝ)) *
                              Support.fluxCorrectedErrorRepresentative M L (n + 3)
                                ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega) *
                              Real.rpow (3 : ℝ) (n : ℝ) *
                              (eLpNorm hdat.grad 2
                                (Support.normalizedVolumeMeasureOn
                                  ((((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m))))).toReal +
                            Real.rpow s (-(4 : ℝ)) *
                              Support.fluxCorrectedErrorRepresentative M L (n + 3)
                                ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega) * S) := by
  classical
  obtain ⟨CE, hCEpos, hCE, CB, KE, hCBpos, hEnergyLeg, hkappadef, hkappa, he0def, hk0def, hb0def,
    hb0, hcg, hA1def, hA1, hA2def, hA2, hA3def, hA3, hCE2, hCE3, _⟩ :=
    @assemblyComposedErrorWeighted_comparisonBounds7 (d) (by infer_instance)
  set kappa : ℝ := Real.sqrt (192 * (d : ℝ)) * 3 with hkappadef
  set e0 : ℝ := kappa * (CE * (1 / 2)) with he0def
  set k0 : ℝ := 2 * (d : ℝ) * (e0 ^ 2 + 1) with hk0def
  set b0 : ℝ := Real.sqrt k0 * e0 + 2 * k0 with hb0def
  set cg : ℝ := 3 * negNormBaseConst d * coarseGrainingP2Const d with hcgdef
  set A1 : ℝ := cg * 216 * (kappa * KE) with hA1def
  set A2 : ℝ := cg * 1944 *
    (b0 * (besovGagliardoConstant d * (gagliardoWindowConst d * windowMoveConst d)))
    with hA2def
  set A3 : ℝ := interiorCorrectionConst d * (gagliardoWindowConst d * windowMoveConst d)
    with hA3def
  refine ⟨max CE CB,
    A1 + 9 * (CE * (1 / 2)) * A1 + CE * (1 / 2) * A1 + A2 + A3 + 1,
    lt_of_lt_of_le hCEpos (le_max_left _ _),
    add_pos_of_nonneg_of_pos
      (add_nonneg (add_nonneg (add_nonneg (add_nonneg hA1 hCE2) hCE3) hA2) hA3)
      zero_lt_one, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm x z hx hgeom
  have hs1 : s ≤ 1 := hsrange.2
  have hregimeCE : M.gamma ≤ CE⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans
      (mul_le_mul_of_nonneg_right ?_ (Even.pow_nonneg (by exact ⟨5, rfl⟩) _))
    have h1 := one_div_le_one_div_of_le hCEpos (le_max_left CE CB)
    rw [one_div, one_div] at h1
    exact h1
  have hregimeCB : M.gamma ≤ CB⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans
      (mul_le_mul_of_nonneg_right ?_ (Even.pow_nonneg (by exact ⟨5, rfl⟩) _))
    have h1 := one_div_le_one_div_of_le hCBpos (le_max_right CE CB)
    rw [one_div, one_div] at h1
    exact h1
  filter_upwards [hCE M s hsrange hregimeCE hsmall hs n z,
    hEnergyLeg M s hsrange hregimeCB hsmall hs L m n hmL hnm x z hx hgeom,
    ae_coarseGrainingErrorAtDepth_rebased_le_representative_addThree M L n z hs hs1,
    ae_forceBracket_rebased_le_addThree M L n z hs hs1] with omega hcapE hEnLeg herrD hbrk
  intro hmem u hdat g S hsol hgL2 hgW hhW hmean v w hharm hval hgrad
  obtain ⟨hsubx, hErepCap, hErep0, hsig, hP2def, hQ3sdef, hxf, hQ3sndef, hQ1sdef, hR3ndef, hS4def,
    hS7def, hS6def, hSm3def, hSm2def, hX0, hGs0, hHs0, hHn0, hS0, hQ3s0, hQ3sn0, hQ1s0, hR3n0,
      hS40, hS70, hS60, hSm30, hSm20, hsiginv0, hET, hYchild3, hFT, _⟩ :=
    @assemblyComposedErrorWeighted_comparisonBounds5 (d) (by infer_instance) (CE) (KE) (hkappadef)
      (hkappa) (he0def) (hk0def) (hb0def) (hb0) (M) (s) (hs) (L) (m) (n) (hmL) (hnm) (x) (z)
        (hgeom) (hs1) (omega) (hcapE) (hEnLeg) (herrD) (hbrk) (hmem) (u) (hdat) (g) (S) (hsol)
          (hgL2) (hgW) (hhW) (hmean) (v) (w) (hharm) (hval) (hgrad)
  set Erep : ℝ := Support.fluxCorrectedErrorRepresentative M L (n + 3)
    ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) with hErepdef
  set Eb : ℝ := Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
    ((3 : ℝ) ^ (3 * (s / 8)) * Erep) with hEbdef
  set sig : ℝ := (Annealed.sigmaBar M (n + 3) : ℝ) with hsigdef
  set X : ℝ := (eLpNorm (fun y => u.toFun y -
      volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal with hXdef
  set Gs : ℝ := (Support.normalizedGagliardoESeminormOn
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) s g).toReal with hGsdef
  set Hs : ℝ := (Support.normalizedGagliardoESeminormOn
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) s hdat.grad).toReal with hHsdef
  set Hn : ℝ := (eLpNorm hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal with hHndef
  set Y2 : ℝ := (Support.normalizedGagliardoESeminormOn
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
        openCubeSet (originCube d m))) s g).toReal with hY2def
  set Ychild : ℝ := (Support.normalizedGagliardoESeminormOn
      ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal with hYchilddef
  set Lhs : ℝ := (eLpNorm (fun y => u.toFun y - v.toFun y) 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => x + y) '' openCubeSet (originCube d n)))).toReal with hLhsdef
  set P2 : ℝ := Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) with hP2def
  set Q3s : ℝ := Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) with hQ3sdef
  set Q3sn : ℝ := Real.rpow (3 : ℝ) (s * (n : ℝ)) with hQ3sndef
  set Q1s : ℝ := Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) with hQ1sdef
  set R3n : ℝ := Real.rpow (3 : ℝ) ((n : ℝ)) with hR3ndef
  set S4 : ℝ := Real.rpow s (-(4 : ℝ)) with hS4def
  set S7 : ℝ := Real.rpow s (-(7 : ℝ)) with hS7def
  set S6 : ℝ := Real.rpow s (-(6 : ℝ)) with hS6def
  set Sm3 : ℝ := Real.rpow s (-(3 : ℝ)) with hSm3def
  set Sm2 : ℝ := Real.rpow s (-(2 : ℝ)) with hSm2def
  -- (e) the frame division
  set ET : ℝ := coarseGrainingEnergyTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3)
      (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx))
    with hETdef
  set FT : ℝ := coarseGrainingForceTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) s (fun y => -g (y + x))
    with hFTdef
  have hW1 : cubeBesovScaleWeight (1 : ℝ) (originCube d n) =
      Real.rpow (3 : ℝ) (-(n : ℝ)) := by
    have h := cubeBesovScaleWeight_neg_originCube (d := d) n (-1)
    rw [neg_neg] at h
    rw [h]
    congr 1
    ring
  rw [hW1] at hxf
  obtain ⟨hfac0, hsinv, hstep, hleg1, hleg2, hleg3⟩ :=
    (show ((0 : ℝ) ≤ sig⁻¹ * R3n) ∧ (sig⁻¹ * sig = 1) ∧ (Lhs ≤ (sig⁻¹ * R3n) *
      (cg * (216 * (s⁻¹) ^ (4 : ℕ) * ET + 1944 * (s⁻¹) ^ (6 : ℕ) * FT) +
        interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn * Ychild)) ∧ (216 * (s⁻¹) ^
          (4 : ℕ) * ET ≤
      216 * (s⁻¹) ^ (4 : ℕ) *
        (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
          Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn)))) ∧ (1944 * (s⁻¹) ^ (6 : ℕ) * FT ≤
      1944 * (s⁻¹) ^ (6 : ℕ) *
        (b0 * (besovGagliardoConstant d * Q3sn *
          (gagliardoWindowConst d * windowMoveConst d * Gs)))) ∧ (interiorCorrectionConst d *
            Real.rpow s (-(1 / 2 : ℝ)) * Q3sn * Ychild ≤
      interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn *
        (gagliardoWindowConst d * windowMoveConst d * Gs)) from
      @assemblyComposedErrorWeighted_comparisonBounds6 (d) (by infer_instance) (CE) (KE) (M) (s)
        (hs) (L) (m) (n) (x) (z) (omega) (u) (hdat) (g) (S) (v) (hsubx) (hsig) (hsiginv0)
          (hYchild3) (hQ3sn0) (hR3n0) (hET) (hFT) (hxf))
  have hmono := add_le_add (mul_le_mul_of_nonneg_left (add_le_add hleg1 hleg2) hcg) hleg3
  clear_value Lhs X Gs Hs Hn Y2 Ychild ET FT Erep Eb sig P2 Q3s Q3sn Q1s R3n S4 S7 S6
    Sm3 Sm2 A3 A2 A1 cg b0 k0 e0 kappa
  -- (g) the regrouping
  obtain ⟨hT1, hT2, hT3, hXterm, hSterm, hGterm, hHsterm, hHnterm⟩ :=
    @assemblyComposedErrorWeighted_comparisonBounds8 (d) (CE) (KE) (kappa)
      (b0) (cg) (A1) (by assumption) (hA1) (hA1def) (A2) (by assumption) (hA2) (hA2def) (A3) (by
        assumption) (hA3) (hA3def) (s) (hs) (n) (hs1) (S) (hS0) (Erep) (hErepCap) (hErep0) (sig)
          (hsiginv0) (X) (hX0) (Gs) (hGs0) (Hs) (hHs0) (Hn) (hHn0) (P2) (by assumption) (hP2def)
            (Q3s) (by assumption) (hQ3s0) (hQ3sdef) (Q3sn) (by assumption) (hQ3sndef) (Q1s) (by
              assumption) (hQ1s0) (hQ1sdef) (R3n) (by assumption) (hR3n0) (hR3ndef) (S4) (by
                assumption) (hS40) (hS4def) (S7) (by assumption) (hS70) (hS7def) (S6) (by
                  assumption) (hS60) (hS6def) (Sm3) (by assumption) (hSm30) (hSm3def) (Sm2) (by
                    assumption) (hSm20) (hSm2def) (hsinv)
  refine hstep.trans (le_trans (mul_le_mul_of_nonneg_left hmono hfac0) ?_)
  have hdistrib : (sig⁻¹ * R3n) *
      (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
            (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
              Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))) +
          1944 * (s⁻¹) ^ (6 : ℕ) *
            (b0 * (besovGagliardoConstant d * Q3sn *
              (gagliardoWindowConst d * windowMoveConst d * Gs)))) +
        interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn *
          (gagliardoWindowConst d * windowMoveConst d * Gs)) =
      (sig⁻¹ * R3n) * (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
          (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
            Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))))) +
        (sig⁻¹ * R3n) * (cg * (1944 * (s⁻¹) ^ (6 : ℕ) *
          (b0 * (besovGagliardoConstant d * Q3sn *
            (gagliardoWindowConst d * windowMoveConst d * Gs))))) +
        (sig⁻¹ * R3n) * (interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) *
          Q3sn * (gagliardoWindowConst d * windowMoveConst d * Gs)) := by ring
  rw [hdistrib]
  have habs : A1 * (S4 * Erep * X) +
        (9 * (CE * (1 / 2)) * A1 + A2 + A3) * (S7 * sig⁻¹ * Q1s * Gs) +
        (9 * (CE * (1 / 2)) * A1) * (S6 * Q1s * Hs) +
        A1 * (S6 * Erep * R3n * Hn) + A1 * (S4 * Erep * S) ≤
      (A1 + 9 * (CE * (1 / 2)) * A1 + CE * (1 / 2) * A1 + A2 + A3 + 1) *
        (S4 * Erep * X + S7 * sig⁻¹ * Q1s * Gs + S6 * Q1s * Hs +
          S6 * Erep * R3n * Hn + S4 * Erep * S) :=
    five_leg_bound le_rfl (by linarith only [hCE2, hCE3, hA2, hA3])
      (by linarith only [hA1, hCE3]) (by linarith only [hA1, hCE3, hA2, hA3])
      (by linarith only [hCE2, hCE3, hA2, hA3])
      (by linarith only [hCE2, hCE3, hA2, hA3]) hXterm hGterm hHsterm hHnterm hSterm
  linarith only [hT1, hT2, hT3, habs]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
