/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorComposedArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorAssemblyAnchorShape
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.GoodEventCaps

/-!
# InteriorComposed

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior clause, composed at the honest exponents

The payoff of the-- residue: **one** almost-sure statement, entered at the
frozen theorem's own binders and concluded in the frozen theorem's own
carriers,

```text
  1_𝒢 ‖u − v‖_{L²(x+□_n)}
      ≤ C ( s^{-4}    𝓔_{s/8}(z+□_{n+2}; ã_{L,n+2}, σ_{n+2}) ‖u − (u)_W‖_{L²(W)}
          + s^{-19/2} σ_{n+2}^{-1} 3^{(1+s)n} [g]_{H^s(W)} ) ,
      W = (z + □_{n+2}) ∩ □_m .
```

This is the frozen interior clause **at the honest `s`-powers**: the
printed display carries `s^{-3/2}` and `s^{-7}` where the proved chain gives
`s^{-4}` and `s^{-19/2}`.  Every other carrier is the anchor's, byte for byte:
the same left-hand `eLpNorm`, the same `fluxCorrectedErrorRepresentative` at
the printed index `s/8` and at the translated sample, the same mean-subtracted
parent norm, the same `normalizedGagliardo` on the parent-intersected window.

## What goes into it

* `InteriorEllipticitySlot`: the coarse-graining slot re-cut at `r = s/3` (so
  that the child's coarse-graining index is `s/6 > s/8`), and the `x`-frame
  composition at the re-based family;
* `InteriorEllipticity`: the child-frame `𝓔` against the anchor's own
  representative, and CoarseGraining's forcing bracket collapsed on the good
  event;
* `InteriorWindowMove`: the Gagliardo seminorm from the child window to the
  anchor's parent-intersected window;
* `GoodEventCaps`: the representative's cap, used **only** in the second
  summand (the first keeps it, as the frozen statement does).

## Deviations from the printed statement

* the `σ` index: the second summand carries `σ_{n+2}^{-1}`; the printed one
  carries `σ_n^{-1}`, and `SigmaBarIndex.exists_inv_sigmaBar_add_two_le`
  converts at the factor `4` inside the anchor's own regime.
* no `γ`-move is made anywhere.

## References

* ABK26, `l.harmonic.approximation.good.scales`;
  `e.homogenization.L2.interior`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The composed interior estimate -/

private abbrev interiorComposed_comparisonBounds2_statement : Prop :=
    ∀ (d : ℕ) [NeZero d] (CE Cout : ℝ) (_ : (0 : ℝ) < Cout),
      let kappa : ℝ := √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ);
      ∀ (_ : (0 : ℝ) ≤ kappa),
        let e0 : ℝ := kappa * (CE * (1 / 2 : ℝ));
          let k0 : ℝ := (2 : ℝ) * (↑d : ℝ) * (e0 ^ (2 : ℕ) + (1 : ℝ));
            let b0 : ℝ := √k0 * e0 + (2 : ℝ) * k0;
            ∀ (M : ABKModel d) (s : ℝ) (_ : (0 : ℝ) < s) (L m n
              : ℤ) (x z : Vec d)
              (hz : z ∈ openCubeSet (originCube d m))
              (_ :
                (fun (y : Vec d) => x + y) '' openCubeSet (originCube d n) ⊆
                  (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (1 : ℤ))) ∩
                    openCubeSet (originCube d m))
              (hfr :
                (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (2 : ℤ))) ∩
                    frontier (openCubeSet (originCube d m)) =
                  ∅)
              (_ : s ≤ (1 : ℝ)) (omega : Cutoff.CutoffSample d) (u : H1Function (openCubeSet
                (originCube d m)))
              (g : Vec d → Vec d) (hsubx : translateSet x (openCubeSet (originCube d n)) ⊆
                openCubeSet (originCube d m))
              (hsubz : translateSet z (openCubeSet (originCube d (n + (2 : ℤ)))) ⊆ openCubeSet
                (originCube d m))
              (_ :
                Ch03.localizedCoeffEnergyValue ((fun (y : Vec d) => x - z + y) '' openCubeSet
                  (originCube d n))
                    ((fluxCorrectedCoeffFamily M L (n + (2 : ℤ)) (originCube d (n + (2 : ℤ)))
                          (Cutoff.translateCutoffSample z omega)).coeffOn
                      (originCube d (n + (2 : ℤ))))
                    (H1Function.untranslate z
                      (u.restrict (isOpen_translateSet_openCubeSet z (n + (2 : ℤ)))
                        (translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr))) ≤
                  Cout *
                    interiorAnchorEnergyRHSOn M n s
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2 : ℤ))) ∩
                        openCubeSet (originCube d m))
                      u.toFun g)
              (_ :
                MemLp g (2 : ENNReal)
                  (normalizedVolumeMeasureOn ((fun (y : Vec d) => x + y) '' openCubeSet
                    (originCube d n))))
              (_ :
                MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal) g) (2 : ENNReal)
                  (normalizedGagliardoMeasureOn ((fun (y : Vec d) => x + y) '' openCubeSet
                    (originCube d n))))
              (_ :
                Ch03.h1EnergyNormOnCube (originCube d n) (parentRebasedFamily M L (n + (2 : ℤ)) x
                  z omega)
                    (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n)
                      hsubx)) =
                  √(Ch03.localizedCoeffEnergyValue ((fun (y : Vec d) => x - z + y) '' openCubeSet
                    (originCube d n))
                      ((fluxCorrectedCoeffFamily M L (n + (2 : ℤ)) (originCube d (n + (2 : ℤ)))
                            (Cutoff.translateCutoffSample z omega)).coeffOn
                        (originCube d (n + (2 : ℤ))))
                      (H1Function.untranslate z (u.restrict (isOpen_translateSet_openCubeSet z (n
                        + (2 : ℤ))) hsubz)))),
              let Erep : ℝ :=
                fluxCorrectedErrorRepresentative M L (n + (2 : ℤ)) ⟨s / (8 : ℝ), (by positivity)⟩
                  (Cutoff.translateCutoffSample z omega);
              ∀ (_ : Erep ≤ CE * (1 / 2 : ℝ)) (_ : (0 : ℝ) ≤ Erep),
                let Eb : ℝ :=
                  √(offGridStabilityConst d (s / (6 : ℝ)) (s / (8 : ℝ))) * ((3 : ℝ) ^ ((2 : ℝ) *
                    (s / (8 : ℝ))) * Erep);
                ∀
                  (_ :
                    ∀ (x : Vec d) (m : ℤ),
                      (fun (y : Vec d) => x + y) '' openCubeSet (originCube d n) ⊆
                          (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (1 : ℤ))) ∩
                            openCubeSet (originCube d m) →
                        Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
                            (parentRebasedFamily M L (n + (2 : ℤ)) x z omega)
                            (scalarComparator (Annealed.sigmaBar M (n + (2 : ℤ))).property) (s /
                              (3 : ℝ)) (0 : ℕ) ≤
                          Eb)
                  (_ :
                    ∀ (x : Vec d) (m : ℤ),
                      (fun (y : Vec d) => x + y) '' openCubeSet (originCube d n) ⊆
                          (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (1 : ℤ))) ∩
                            openCubeSet (originCube d m) →
                        coarseGrainingForceBracket (originCube d n) (parentRebasedFamily M L (n +
                          (2 : ℤ)) x z omega)
                            (scalarComparator (Annealed.sigmaBar M (n + (2 : ℤ))).property) (s /
                              (3 : ℝ)) ≤
                          √((2 : ℝ) * (↑d : ℝ) * (Eb ^ (2 : ℕ) + (1 : ℝ))) * Eb +
                            (2 : ℝ) * ((2 : ℝ) * (↑d : ℝ) * (Eb ^ (2 : ℕ) + (1 : ℝ))))
                  ,
                  let sig : ℝ := (↑(Annealed.sigmaBar M (n + (2 : ℤ))) : ℝ);
                  ∀ (_ : (0 : ℝ) < sig),
                    let X : ℝ :=
                      (eLpNorm
                          (fun (y : Vec d) =>
                            u.toFun y -
                              volumeAverage
                                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2
                                  : ℤ))) ∩
                                  openCubeSet (originCube d m))
                                u.toFun)
                          (2 : ENNReal)
                          (normalizedVolumeMeasureOn
                            ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2 :
                              ℤ))) ∩
                              openCubeSet (originCube d m)))).toReal;
                    let Y : ℝ :=
                      (normalizedGagliardoESeminormOn
                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2 :
                            ℤ))) ∩
                            openCubeSet (originCube d m))
                          s g).toReal;
                    let Ychild : ℝ :=
                      (normalizedGagliardoESeminormOn ((fun (y : Vec d) => x + y) '' openCubeSet
                        (originCube d n)) s
                          g).toReal;
                    let P2 : ℝ := Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ));
                    let QS : ℝ := s.rpow (-(11 / 2 : ℝ));
                    let Q3s : ℝ := Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ));
                    let Q3sn : ℝ := Real.rpow (3 : ℝ) (s * (↑n : ℝ));
                    let S4 : ℝ := s.rpow (-4 : ℝ);
                    let S192 : ℝ := s.rpow (-(19 / 2 : ℝ));
                    (0 : ℝ) ≤ S4 ∧
                      (0 : ℝ) ≤ S192 ∧
                        (0 : ℝ) ≤ sig⁻¹ ∧
                          coarseGrainingForceBracket (originCube d n) (parentRebasedFamily M L (n
                            + (2 : ℤ)) x z omega)
                                (scalarComparator (Annealed.sigmaBar M (n + (2 : ℤ))).property) (s
                                  / (3 : ℝ)) ≤
                              b0 ∧
                            coarseGrainingEnergyTerm (originCube d n) (parentRebasedFamily M L (n
                              + (2 : ℤ)) x z omega)
                                  (scalarComparator (Annealed.sigmaBar M (n + (2 : ℤ))).property)
                                    (s / (3 : ℝ))
                                  (H1Function.untranslate x (u.restrict
                                    (isOpen_translateSet_openCubeSet x n) hsubx)) ≤
                                kappa * √Cout * Erep * (sig * (P2 * X) + QS * (Q3s * Y)) ∧
                              (Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n)
                                s fun (y : Vec d) =>
                                  -g (y + x)) ≤
                                besovGagliardoConstant d * Q3sn * Ychild

private abbrev interiorComposed_comparisonBounds3_statement : Prop :=
    ∀ (d : ℕ) [NeZero d] (CE Cout : ℝ) (_ : (0 : ℝ) < Cout),
      let kappa : ℝ := √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ);
      ∀ (_ : (0 : ℝ) ≤ kappa),
        let e0 : ℝ := kappa * (CE * (1 / 2 : ℝ));
          let k0 : ℝ := (2 : ℝ) * (↑d : ℝ) * (e0 ^ (2 : ℕ) + (1 : ℝ));
            let b0 : ℝ := √k0 * e0 + (2 : ℝ) * k0;
            ∀ (_ : (0 : ℝ) ≤ b0) (M : ABKModel d) (s : ℝ) (_ :
              (0 : ℝ) < s)
              (L m n : ℤ) (_ : m ≤ L) (_ : n + (2 : ℤ) ≤ m) (x z : Vec d) (hz : z ∈ openCubeSet
                (originCube d m))
              (_ :
                (fun (y : Vec d) => x + y) '' openCubeSet (originCube d n) ⊆
                  (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (1 : ℤ))) ∩
                    openCubeSet (originCube d m))
              (hfr :
                (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (2 : ℤ))) ∩
                    frontier (openCubeSet (originCube d m)) =
                  ∅)
              (_ : s ≤ (1 : ℝ)) (omega : Cutoff.CutoffSample d)
              (_ :
                omega ∈
                    Frozen.Section4.goodEventAt M (cgEllipLowerConstant d) (n + (2 : ℤ)) z
                      ⟨s / (8 : ℝ),
                        (by positivity)⟩
                      (1 / 2 : ℝ) →
                  ∀ (L : ℤ),
                    n + (2 : ℤ) ≤ L →
                      fluxCorrectedErrorRepresentative M L (n + (2 : ℤ))
                          ⟨s / (8 : ℝ),
                            (by positivity)⟩
                          (Cutoff.translateCutoffSample z omega) ≤
                        CE * (1 / 2 : ℝ))
              (_ :
                omega ∈
                    Frozen.Section4.goodEventAt M (cgEllipLowerConstant d) (n + (2 : ℤ)) z
                      ⟨s / (8 : ℝ),
                        (by positivity)⟩
                      (1 / 2 : ℝ) →
                  ∀ (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
                    IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (originCube d m) u hdat g →
                      MemLp g (2 : ENNReal)
                          (normalizedVolumeMeasureOn
                            ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2 :
                              ℤ))) ∩
                              openCubeSet (originCube d m))) →
                        MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal) g) (2 : ENNReal)
                            (normalizedGagliardoMeasureOn
                              ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2 :
                                ℤ))) ∩
                                openCubeSet (originCube d m))) →
                          Ch03.localizedCoeffEnergyValue ((fun (y : Vec d) => x - z + y) ''
                            openCubeSet (originCube d n))
                              ((fluxCorrectedCoeffFamily M L (n + (2 : ℤ)) (originCube d (n + (2 :
                                ℤ)))
                                    (Cutoff.translateCutoffSample z omega)).coeffOn
                                (originCube d (n + (2 : ℤ))))
                              (H1Function.untranslate z
                                (u.restrict (isOpen_translateSet_openCubeSet z (n + (2 : ℤ)))
                                  (translateSet_openCubeSet_subset_of_frontier_inter_empty hz
                                    hfr))) ≤
                            Cout *
                              interiorAnchorEnergyRHSOn M n s
                                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2
                                  : ℤ))) ∩
                                  openCubeSet (originCube d m))
                                u.toFun g)
              (_ :
                ∀ (x : Vec d) (m : ℤ),
                  (fun (y : Vec d) => x + y) '' openCubeSet (originCube d n) ⊆
                      (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (1 : ℤ))) ∩
                        openCubeSet (originCube d m) →
                    Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
                        (parentRebasedFamily M L (n + (2 : ℤ)) x z omega)
                        (scalarComparator (Annealed.sigmaBar M (n + (2 : ℤ))).property) (s / (3 :
                          ℝ)) (0 : ℕ) ≤
                      √(offGridStabilityConst d (s / (6 : ℝ)) (s / (8 : ℝ))) *
                        ((3 : ℝ) ^ ((2 : ℝ) * (s / (8 : ℝ))) *
                          fluxCorrectedErrorRepresentative M L (n + (2 : ℤ))
                            ⟨s / (8 : ℝ),
                              (by positivity)⟩
                            (Cutoff.translateCutoffSample z omega)))
              (_ :
                ∀ (x : Vec d) (m : ℤ),
                  (fun (y : Vec d) => x + y) '' openCubeSet (originCube d n) ⊆
                      (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (1 : ℤ))) ∩
                        openCubeSet (originCube d m) →
                    coarseGrainingForceBracket (originCube d n) (parentRebasedFamily M L (n + (2 :
                      ℤ)) x z omega)
                        (scalarComparator (Annealed.sigmaBar M (n + (2 : ℤ))).property) (s / (3 :
                          ℝ)) ≤
                      √((2 : ℝ) * (↑d : ℝ) *
                              ((√(offGridStabilityConst d (s / (6 : ℝ)) (s / (8 : ℝ))) *
                                    ((3 : ℝ) ^ ((2 : ℝ) * (s / (8 : ℝ))) *
                                      fluxCorrectedErrorRepresentative M L (n + (2 : ℤ))
                                        ⟨s / (8 : ℝ),
                                          (by positivity)⟩
                                        (Cutoff.translateCutoffSample z omega))) ^
                                  (2 : ℕ) +
                                (1 : ℝ))) *
                          (√(offGridStabilityConst d (s / (6 : ℝ)) (s / (8 : ℝ))) *
                            ((3 : ℝ) ^ ((2 : ℝ) * (s / (8 : ℝ))) *
                              fluxCorrectedErrorRepresentative M L (n + (2 : ℤ))
                                ⟨s / (8 : ℝ),
                                  (by positivity)⟩
                                (Cutoff.translateCutoffSample z omega))) +
                        (2 : ℝ) *
                          ((2 : ℝ) * (↑d : ℝ) *
                            ((√(offGridStabilityConst d (s / (6 : ℝ)) (s / (8 : ℝ))) *
                                  ((3 : ℝ) ^ ((2 : ℝ) * (s / (8 : ℝ))) *
                                    fluxCorrectedErrorRepresentative M L (n + (2 : ℤ))
                                      ⟨s / (8 : ℝ),
                                        (by positivity)⟩
                                      (Cutoff.translateCutoffSample z omega))) ^
                                (2 : ℕ) +
                              (1 : ℝ))))
              (_ :
                omega ∈
                  Frozen.Section4.goodEventAt M (cgEllipLowerConstant d) (n + (2 : ℤ)) z
                    ⟨s / (8 : ℝ),
                      (by positivity)⟩
                    (1 / 2 : ℝ))
              (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
              (_ : IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                (originCube d m) u hdat g)
              (_ : MemLp g (2 : ENNReal) (normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
              (_ :
                MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal) g) (2 : ENNReal)
                  (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))))
              (v : H1Function ((fun (y : Vec d) => x + y) '' openCubeSet (originCube d n)))
              (w : H10Function ((fun (y : Vec d) => x + y) '' openCubeSet (originCube d n)))
              (_ : IsWeaklyHarmonicOn ((fun (y : Vec d) => x + y) '' openCubeSet (originCube d n))
                v)
              (_ : ∀ (y : Vec d), v.toFun y = u.toFun y - w.toFun y)
              (_ : ∀ (y : Vec d), v.grad y = u.grad y - w.grad y),
              ∃ (hsubx : translateSet x (openCubeSet (originCube d n)) ⊆ openCubeSet (originCube d
                m)) (_ :
                fluxCorrectedErrorRepresentative M L (n + (2 : ℤ)) ⟨s / (8 : ℝ), (by positivity)⟩
                    (Cutoff.translateCutoffSample z omega) ≤
                  CE * (1 / 2 : ℝ))
                (_ :
                (0 : ℝ) ≤
                  fluxCorrectedErrorRepresentative M L (n + (2 : ℤ)) ⟨s / (8 : ℝ), (by positivity)⟩
                    (Cutoff.translateCutoffSample z omega))
                (_ : (0 : ℝ) < (↑(Annealed.sigmaBar M (n + (2 : ℤ))) : ℝ)) (_ :
                Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ)) = Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) :
                  ℝ))) (_ :
                s.rpow (-(11 / 2 : ℝ)) = s.rpow (-(11 / 2 : ℝ))) (_ :
                Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ)) = Real.rpow (3 : ℝ) (s * (↑(n + (2 :
                  ℤ)) : ℝ))) (_ :
                Real.rpow (3 : ℝ) (s * (↑n : ℝ)) = Real.rpow (3 : ℝ) (s * (↑n : ℝ))) (_ :
                Real.rpow (3 : ℝ) (((1 : ℝ) + s) * (↑n : ℝ)) = Real.rpow (3 : ℝ) (((1 : ℝ) + s) *
                  (↑n : ℝ))) (_ :
                Real.rpow (3 : ℝ) (↑n : ℝ) = Real.rpow (3 : ℝ) (↑n : ℝ)) (_ : s.rpow (-4 : ℝ) =
                  s.rpow (-4 : ℝ)) (_ :
                s.rpow (-(19 / 2 : ℝ)) = s.rpow (-(19 / 2 : ℝ))) (_ :
                (0 : ℝ) ≤
                  (eLpNorm
                      (fun (y : Vec d) =>
                        u.toFun y -
                          volumeAverage
                            ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2 :
                              ℤ))) ∩
                              openCubeSet (originCube d m))
                            u.toFun)
                      (2 : ENNReal)
                      (normalizedVolumeMeasureOn
                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2 : ℤ))) ∩
                          openCubeSet (originCube d m)))).toReal)
                (_ :
                (0 : ℝ) ≤
                  (normalizedGagliardoESeminormOn
                      ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2 : ℤ))) ∩
                        openCubeSet (originCube d m))
                      s g).toReal)
                (_ : (0 : ℝ) ≤ s.rpow (-(11 / 2 : ℝ))) (_ : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (s * (↑(n
                  + (2 : ℤ)) : ℝ))) (_ :
                (0 : ℝ) ≤ Real.rpow (3 : ℝ) (s * (↑n : ℝ))) (_ : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (((1
                  : ℝ) + s) * (↑n : ℝ))) (_
                : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (↑n : ℝ)) (_ : (0 : ℝ) ≤ s.rpow (-4 : ℝ)) (_ :
                (0 : ℝ) ≤ s.rpow (-(19 / 2 : ℝ))) (_ : (0 : ℝ) ≤ (↑(Annealed.sigmaBar M (n + (2 :
                  ℤ))) : ℝ)⁻¹) (_ :
                (normalizedGagliardoESeminormOn ((fun (y : Vec d) => x + y) '' openCubeSet
                  (originCube d n)) s g).toReal ≤
                  gagliardoWindowConst d *
                    (normalizedGagliardoESeminormOn
                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2 : ℤ))) ∩
                          openCubeSet (originCube d m))
                        s g).toReal)
                (_ :
                coarseGrainingEnergyTerm (originCube d n) (parentRebasedFamily M L (n + (2 : ℤ)) x
                  z omega)
                    (scalarComparator (Annealed.sigmaBar M (n + (2 : ℤ))).property) (s / (3 : ℝ))
                    (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n)
                      hsubx)) ≤
                  kappa * √Cout *
                      fluxCorrectedErrorRepresentative M L (n + (2 : ℤ)) ⟨s / (8 : ℝ), (by
                        positivity)⟩
                        (Cutoff.translateCutoffSample z omega) *
                    ((↑(Annealed.sigmaBar M (n + (2 : ℤ))) : ℝ) *
                        (Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ)) *
                          (eLpNorm
                              (fun (y : Vec d) =>
                                u.toFun y -
                                  volumeAverage
                                    ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n
                                      + (2 : ℤ))) ∩
                                      openCubeSet (originCube d m))
                                    u.toFun)
                              (2 : ENNReal)
                              (normalizedVolumeMeasureOn
                                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2
                                  : ℤ))) ∩
                                  openCubeSet (originCube d m)))).toReal) +
                      s.rpow (-(11 / 2 : ℝ)) *
                        (Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ)) *
                          (normalizedGagliardoESeminormOn
                              ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2 :
                                ℤ))) ∩
                                openCubeSet (originCube d m))
                              s g).toReal)))
                (_ :
                (coarseGrainingForceTerm (originCube d n) (parentRebasedFamily M L (n + (2 : ℤ)) x
                  z omega)
                    (scalarComparator (Annealed.sigmaBar M (n + (2 : ℤ))).property) (s / (3 : ℝ))
                      s fun (y : Vec d) =>
                    -g (y + x)) ≤
                  b0 *
                    (besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * (↑n : ℝ)) *
                      (gagliardoWindowConst d *
                        (normalizedGagliardoESeminormOn
                            ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2 :
                              ℤ))) ∩
                              openCubeSet (originCube d m))
                            s g).toReal)))
                (_ :
                (↑(Annealed.sigmaBar M (n + (2 : ℤ))) : ℝ) *
                    (cubeBesovScaleWeight (1 : ℝ) (originCube d n) *
                      (eLpNorm (fun (y : Vec d) => u.toFun y - v.toFun y) (2 : ENNReal)
                          (normalizedVolumeMeasureOn
                            ((fun (y : Vec d) => x + y) '' openCubeSet (originCube d n)))).toReal) ≤
                  (3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d *
                      ((216 : ℝ) * s⁻¹ ^ (4 : ℕ) *
                          coarseGrainingEnergyTerm (originCube d n) (parentRebasedFamily M L (n +
                            (2 : ℤ)) x z omega)
                            (scalarComparator (Annealed.sigmaBar M (n + (2 : ℤ))).property) (s /
                              (3 : ℝ))
                            (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet
                              x n) hsubx)) +
                        (1944 : ℝ) * s⁻¹ ^ (6 : ℕ) *
                          coarseGrainingForceTerm (originCube d n) (parentRebasedFamily M L (n +
                            (2 : ℤ)) x z omega)
                            (scalarComparator (Annealed.sigmaBar M (n + (2 : ℤ))).property) (s /
                              (3 : ℝ)) s
                            fun (y : Vec d) => -g (y + x)) +
                    interiorCorrectionConst d * s.rpow (-(1 / 2 : ℝ)) * Real.rpow (3 : ℝ) (s * (↑n
                      : ℝ)) *
                      (normalizedGagliardoESeminormOn ((fun (y : Vec d) => x + y) '' openCubeSet
                        (originCube d n)) s
                          g).toReal),
                cubeBesovScaleWeight (1 : ℝ) (originCube d n) = Real.rpow (3 : ℝ) (-(↑n :
                  ℝ))

private theorem interiorComposed_comparisonBounds1 :
    ∀ (d : ℕ) [NeZero d] (CE : ℝ) (_ : (0 : ℝ) < CE) (Cout : ℝ) (_ : (0 : ℝ) < Cout),
      let kappa : ℝ := √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ);
      let e0 : ℝ := kappa * (CE * (1 / 2 : ℝ));
      let k0 : ℝ := (2 : ℝ) * (↑d : ℝ) * (e0 ^ (2 : ℕ) + (1 : ℝ));
      let b0 : ℝ := √k0 * e0 + (2 : ℝ) * k0;
      let cg : ℝ := (3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d;
      ∀ (_ : (0 : ℝ) ≤ cg),
        let A1 : ℝ := cg * (216 : ℝ) * (kappa * √Cout);
        ∀  (_ : (0 : ℝ) ≤ A1),
          let A2 : ℝ := cg * (1944 : ℝ) * (b0 * (besovGagliardoConstant d * gagliardoWindowConst
            d));
          ∀
            (_ : (0 : ℝ) ≤ A2),
            let A3 : ℝ := interiorCorrectionConst d * gagliardoWindowConst d;
            ∀  (_ : (0 : ℝ) ≤ A3) (s
              : ℝ)
              (_ : (0 : ℝ) < s) (n : ℤ) (_ : s ≤ (1 : ℝ)) (Erep : ℝ) (_ : Erep ≤ CE * (1 / 2 : ℝ))
              (_ : (0 : ℝ) ≤ Erep) (sig X Y P2 : ℝ) (_ : P2 = Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ))
                : ℝ))) (QS : ℝ)
              (_ : QS = s.rpow (-(11 / 2 : ℝ))) (Q3s : ℝ)
              (_ : Q3s = Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ))) (Q3sn : ℝ)
              (_ : Q3sn = Real.rpow (3 : ℝ) (s * (↑n : ℝ))) (Q1s : ℝ)
              (_ : Q1s = Real.rpow (3 : ℝ) (((1 : ℝ) + s) * (↑n : ℝ))) (R3n : ℝ)
              (_ : R3n = Real.rpow (3 : ℝ) (↑n : ℝ)) (S4 : ℝ) (_ : S4 = s.rpow (-4 : ℝ)) (S192 : ℝ)
              (_ : S192 = s.rpow (-(19 / 2 : ℝ))) (_ : (0 : ℝ) ≤ X) (_ : (0 : ℝ) ≤ Y) (_ : (0 : ℝ)
                ≤ QS)
              (_ : (0 : ℝ) ≤ Q3s) (_ : (0 : ℝ) ≤ Q1s) (_ : (0 : ℝ) ≤ R3n) (_ : (0 : ℝ) ≤ S4)
              (_ : (0 : ℝ) ≤ S192) (_ : (0 : ℝ) ≤ sig⁻¹) (_ : sig⁻¹ * sig = (1 : ℝ)),
              sig⁻¹ * R3n *
                    (cg * ((216 : ℝ) * s⁻¹ ^ (4 : ℕ) * (kappa * √Cout * Erep * (sig * (P2 * X) +
                      QS * (Q3s * Y))))) ≤
                  A1 * (S4 * Erep * X) + (9 : ℝ) * (CE * (1 / 2 : ℝ)) * A1 * (S192 * sig⁻¹ * Q1s *
                    Y) ∧
                sig⁻¹ * R3n *
                      (cg *
                        ((1944 : ℝ) * s⁻¹ ^ (6 : ℕ) *
                          (b0 * (besovGagliardoConstant d * Q3sn * (gagliardoWindowConst d *
                            Y))))) ≤
                    A2 * (S192 * sig⁻¹ * Q1s * Y) ∧
                  sig⁻¹ * R3n * (interiorCorrectionConst d * s.rpow (-(1 / 2 : ℝ)) * Q3sn *
                    (gagliardoWindowConst d * Y)) ≤
                      A3 * (S192 * sig⁻¹ * Q1s * Y) ∧
                    (0 : ℝ) ≤ S4 * Erep * X ∧ (0 : ℝ) ≤ S192 * sig⁻¹ * Q1s * Y ∧ (0 : ℝ) ≤ (9 : ℝ)
                      * (CE * (1 / 2 : ℝ)) * A1 := by
  intro d _ CE _ Cout _ kappa _ _ b0 cg _ A1 hA1 A2 hA2 A3 hA3 s hs n hs1 Erep hErepCap hErep0
    sig X Y P2 hP2def QS hQSdef Q3s hQ3sdef Q3sn hQ3sndef Q1s hQ1sdef R3n hR3ndef S4 hS4def S192
    hS192def hX0 hY0 hQS0 hQ3s0 hQ1s0 hR3n0 hS40 hS1920 hsiginv0 hsinv
  have hA1def : A1 = cg * (216 : ℝ) * (kappa * √Cout) := rfl
  have hA2def : A2 = cg * (1944 : ℝ) * (b0 * (besovGagliardoConstant d * gagliardoWindowConst
    d)) := rfl
  have hA3def : A3 = interiorCorrectionConst d * gagliardoWindowConst d := rfl
  have hS4eq : (s⁻¹) ^ (4 : ℕ) = S4 := by
    rw [hS4def, inv_pow_eq_rpow_neg hs 4]
    congr 1
  have hS6eq : (s⁻¹) ^ (6 : ℕ) = Real.rpow s (-(6 : ℝ)) := by
    rw [inv_pow_eq_rpow_neg hs 6]
    congr 1
  have hS4QS : S4 * QS = S192 := by
    rw [hS4def, hQSdef, hS192def]
    exact rpow_s_four_mul_eleven_halves hs
  have hS6le : Real.rpow s (-(6 : ℝ)) ≤ S192 := by
    rw [hS192def]
    exact rpow_le_rpow_neg_nineteen_halves hs hs1 (by norm_num)
  have hQScle : Real.rpow s (-(1 / 2 : ℝ)) ≤ S192 := by
    rw [hS192def]
    exact rpow_le_rpow_neg_nineteen_halves hs hs1 (by norm_num)
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
        (kappa * Real.sqrt Cout * Erep * (sig * (P2 * X) + QS * (Q3s * Y))))) ≤
      A1 * (S4 * Erep * X) + (9 * (CE * (1 / 2)) * A1) * (S192 * sig⁻¹ * Q1s * Y) := by
    have hsplit : (sig⁻¹ * R3n) * (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
          (kappa * Real.sqrt Cout * Erep * (sig * (P2 * X) + QS * (Q3s * Y))))) =
        A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((sig⁻¹ * sig) * ((R3n * P2) * X)))) +
          A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (sig⁻¹ * ((R3n * Q3s) * (QS * Y))))) := by
      rw [hA1def]; ring
    rw [hsplit, hsinv]
    refine add_le_add ?_ ?_
    · have h1 : (R3n * P2) * X ≤ X := by
        have := mul_le_mul_of_nonneg_right hRP2 hX0
        linarith only [this]
      calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * X))))
          = A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((R3n * P2) * X))) := by ring
        _ ≤ A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * X)) := by
            refine mul_le_mul_of_nonneg_left ?_ hA1
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left h1 hErep0
        _ = A1 * (S4 * Erep * X) := by rw [hS4eq]; ring
    · have h2 : (R3n * Q3s) * (QS * Y) ≤ (9 * Q1s) * (QS * Y) :=
        mul_le_mul_of_nonneg_right hRQ3s (mul_nonneg hQS0 hY0)
      have h2nn : (0 : ℝ) ≤ sig⁻¹ * ((R3n * Q3s) * (QS * Y)) :=
        mul_nonneg hsiginv0 (mul_nonneg (mul_nonneg hR3n0 hQ3s0) (mul_nonneg hQS0 hY0))
      have hinner : Erep * (sig⁻¹ * ((R3n * Q3s) * (QS * Y))) ≤
          (CE * (1 / 2)) * (sig⁻¹ * ((9 * Q1s) * (QS * Y))) :=
        mul_le_mul hErepCap (mul_le_mul_of_nonneg_left h2 hsiginv0) h2nn
          (le_trans hErep0 hErepCap)
      calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (sig⁻¹ * ((R3n * Q3s) * (QS * Y)))))
          ≤ A1 * ((s⁻¹) ^ (4 : ℕ) * ((CE * (1 / 2)) * (sig⁻¹ * ((9 * Q1s) * (QS * Y))))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hinner (by positivity)) hA1
        _ = (9 * (CE * (1 / 2)) * A1) * (((s⁻¹) ^ (4 : ℕ) * QS) * sig⁻¹ * Q1s * Y) := by ring
        _ = (9 * (CE * (1 / 2)) * A1) * (S192 * sig⁻¹ * Q1s * Y) := by
            rw [hS4eq, hS4QS]
  have hT2 : (sig⁻¹ * R3n) * (cg * (1944 * (s⁻¹) ^ (6 : ℕ) *
        (b0 * (besovGagliardoConstant d * Q3sn * (gagliardoWindowConst d * Y))))) ≤
      A2 * (S192 * sig⁻¹ * Q1s * Y) := by
    have hrw : (sig⁻¹ * R3n) * (cg * (1944 * (s⁻¹) ^ (6 : ℕ) *
          (b0 * (besovGagliardoConstant d * Q3sn * (gagliardoWindowConst d * Y))))) =
        A2 * ((s⁻¹) ^ (6 : ℕ) * (sig⁻¹ * ((R3n * Q3sn) * Y))) := by
      rw [hA2def]; ring
    rw [hrw, hRQ3sn, hS6eq]
    have hnn : (0 : ℝ) ≤ sig⁻¹ * (Q1s * Y) := mul_nonneg hsiginv0 (mul_nonneg hQ1s0 hY0)
    calc A2 * (Real.rpow s (-(6 : ℝ)) * (sig⁻¹ * (Q1s * Y)))
        ≤ A2 * (S192 * (sig⁻¹ * (Q1s * Y))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS6le hnn) hA2
      _ = A2 * (S192 * sig⁻¹ * Q1s * Y) := by ring
  have hT3 : (sig⁻¹ * R3n) * (interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn *
        (gagliardoWindowConst d * Y)) ≤ A3 * (S192 * sig⁻¹ * Q1s * Y) := by
    have hrw : (sig⁻¹ * R3n) * (interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn *
          (gagliardoWindowConst d * Y)) =
        A3 * (Real.rpow s (-(1 / 2 : ℝ)) * (sig⁻¹ * ((R3n * Q3sn) * Y))) := by
      rw [hA3def]; ring
    rw [hrw, hRQ3sn]
    have hnn : (0 : ℝ) ≤ sig⁻¹ * (Q1s * Y) := mul_nonneg hsiginv0 (mul_nonneg hQ1s0 hY0)
    calc A3 * (Real.rpow s (-(1 / 2 : ℝ)) * (sig⁻¹ * (Q1s * Y)))
        ≤ A3 * (S192 * (sig⁻¹ * (Q1s * Y))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQScle hnn) hA3
      _ = A3 * (S192 * sig⁻¹ * Q1s * Y) := by ring
  -- (h) the conclusion
  have hXterm : (0 : ℝ) ≤ S4 * Erep * X := mul_nonneg (mul_nonneg hS40 hErep0) hX0
  have hYterm : (0 : ℝ) ≤ S192 * sig⁻¹ * Q1s * Y :=
    mul_nonneg (mul_nonneg (mul_nonneg hS1920 hsiginv0) hQ1s0) hY0
  have hCE2 : (0 : ℝ) ≤ 9 * (CE * (1 / 2)) * A1 := by positivity
  exact ⟨hT1, hT2, hT3, hXterm, hYterm, hCE2⟩

private theorem interiorComposed_comparisonBounds2 :
  interiorComposed_comparisonBounds2_statement := by
  intro d _ _CE Cout hCoutpos kappa hkappa e0 k0 b0 M s hs L m n x z _ hgeom _ hs1 omega u g hsubx
    _ hcaccW hgL2child hgWchild hR3 Erep hErepCap hErep0 Eb herrD hbrk sig hsig X Y Ychild P2 QS
    Q3s Q3sn S4 S192
  have hkappadef :
    kappa = √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ)
    := rfl
  have he0def :
    e0 = kappa * (_CE * (1 / 2 : ℝ))
    := rfl
  have hk0def :
    k0 = (2 : ℝ) * (↑d : ℝ) * (e0 ^ (2 : ℕ) + (1 : ℝ))
    := rfl
  have hb0def :
    b0 = √k0 * e0 + (2 : ℝ) * k0
    := rfl
  have hEbdef :
    Eb =
                      √(offGridStabilityConst d (s / (6 : ℝ)) (s / (8 : ℝ))) *
                        ((3 : ℝ) ^ ((2 : ℝ) * (s / (8 : ℝ))) * Erep)
    := rfl
  have hS40 : 0 ≤ S4 := Real.rpow_nonneg hs.le _
  have hS1920 : 0 ≤ S192 := Real.rpow_nonneg hs.le _
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
    have h2 : ((3 : ℝ) ^ (2 * (s / 8))) ≤ 3 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (by linarith only [hs1] : 2 * (s / 8) ≤ (1 : ℝ))
      rwa [Real.rpow_one] at h
    have h3 : (3 : ℝ) ^ (2 * (s / 8)) * Erep ≤ 3 * Erep :=
      mul_le_mul_of_nonneg_right h2 hErep0
    have h4 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * (s / 8)) * Erep :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hErep0
    rw [hEbdef]
    calc Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
          ((3 : ℝ) ^ (2 * (s / 8)) * Erep)
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
    have h2d : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith only [hsq]) h2d
  have hbrkCap : coarseGrainingForceBracket (originCube d n)
      (parentRebasedFamily M L (n + 2) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 2)).2) (s / 3) ≤ b0 := by
    refine (hbrk x m hgeom).trans ?_
    rw [hb0def]
    have h1 : Real.sqrt (2 * (d : ℝ) * (Eb ^ 2 + 1)) * Eb ≤ Real.sqrt k0 * e0 :=
      mul_le_mul (Real.sqrt_le_sqrt hKble) hEbe0 hEb0 (Real.sqrt_nonneg _)
    have h2 : 2 * (2 * (d : ℝ) * (Eb ^ 2 + 1)) ≤ 2 * k0 := by linarith only [hKble]
    linarith only [h1, h2]
  -- (c) the energy leg
  have hEnergy : Ch03.h1EnergyNormOnCube (originCube d n)
      (parentRebasedFamily M L (n + 2) x z omega)
      (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx)) ≤
      Real.sqrt Cout * (Real.sqrt sig * P2 * X + QS * Real.sqrt sig⁻¹ * Q3s * Y) := by
    rw [hR3]
    refine le_trans (Real.sqrt_le_sqrt hcaccW) ?_
    rw [Real.sqrt_mul hCoutpos.le]
    exact mul_le_mul_of_nonneg_left
      (sqrt_interiorAnchorEnergyRHSOn_le M n hs _ u.toFun g) (Real.sqrt_nonneg _)
  have hEnergy0 : 0 ≤ Ch03.h1EnergyNormOnCube (originCube d n)
      (parentRebasedFamily M L (n + 2) x z omega)
      (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx)) :=
    h1EnergyNormOnCube_nonneg _ _ _
  have hET : coarseGrainingEnergyTerm (originCube d n)
      (parentRebasedFamily M L (n + 2) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 2)).2) (s / 3)
      (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx)) ≤
      kappa * Real.sqrt Cout * Erep * (sig * (P2 * X) + QS * (Q3s * Y)) := by
    have hEcap : Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
        (parentRebasedFamily M L (n + 2) x z omega)
        (scalarComparator (Annealed.sigmaBar M (n + 2)).2) (s / 3) 0 ≤ kappa * Erep :=
      (herrD x m hgeom).trans hEbkappa
    rw [coarseGrainingEnergyTerm, constantCoeffMatrixNormHalf_scalarComparator_sqrt]
    have hstep : Real.sqrt sig *
        Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
          (parentRebasedFamily M L (n + 2) x z omega)
          (scalarComparator (Annealed.sigmaBar M (n + 2)).2) (s / 3) 0 *
        Ch03.h1EnergyNormOnCube (originCube d n)
          (parentRebasedFamily M L (n + 2) x z omega)
          (H1Function.untranslate x
            (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx)) ≤
        Real.sqrt sig * (kappa * Erep) *
          (Real.sqrt Cout * (Real.sqrt sig * P2 * X + QS * Real.sqrt sig⁻¹ * Q3s * Y)) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hEcap (Real.sqrt_nonneg _)) hEnergy
        hEnergy0 ?_
      exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hkappa hErep0)
    refine hstep.trans (le_of_eq ?_)
    have h1 : Real.sqrt sig * Real.sqrt sig = sig := Real.mul_self_sqrt hsig.le
    have h2 : Real.sqrt sig * Real.sqrt sig⁻¹ = 1 := sqrt_mul_sqrt_inv hsig
    calc Real.sqrt sig * (kappa * Erep) *
          (Real.sqrt Cout * (Real.sqrt sig * P2 * X + QS * Real.sqrt sig⁻¹ * Q3s * Y))
        = kappa * Real.sqrt Cout * Erep *
            ((Real.sqrt sig * Real.sqrt sig) * (P2 * X) +
              (Real.sqrt sig * Real.sqrt sig⁻¹) * (QS * (Q3s * Y))) := by ring
      _ = kappa * Real.sqrt Cout * Erep * (sig * (P2 * X) + 1 * (QS * (Q3s * Y))) := by
            rw [h1, h2]
      _ = kappa * Real.sqrt Cout * Erep * (sig * (P2 * X) + QS * (Q3s * Y)) := by ring
  -- (d) the forcing leg
  have hGbes : Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s
      (fun y => -g (y + x)) ≤ besovGagliardoConstant d * Q3sn * Ychild := by
    have h := besovVectorSeminormTwo_translated_neg_le_gagliardo_window (originCube d n) hs hs1
      hgL2child hgWchild
    rwa [cubeBesovScaleWeight_neg_originCube (d := d) n s] at h
  exact ⟨hS40, hS1920, hsiginv0, hbrkCap, hET, hGbes⟩

private theorem interiorComposed_comparisonBounds3 :
  interiorComposed_comparisonBounds3_statement := by
  classical
  intro d _ CE Cout hCoutpos kappa hkappa _e0 _k0 b0 hb0 M s hs L m n hmL hnm x z hz hgeom hfr hs1
    omega hcapE hcacc herrD hbrk hmem u hdat g hsol hgL2 hgW v w hharm hval hgrad
  have hkappadef :
    kappa = √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ)
    := rfl
  have he0def :
    _e0 = kappa * (CE * (1 / 2 : ℝ))
    := rfl
  have hk0def :
    _k0 = (2 : ℝ) * (↑d : ℝ) * (_e0 ^ (2 : ℕ) + (1 : ℝ))
    := rfl
  have hb0def :
    b0 = √_k0 * _e0 + (2 : ℝ) * _k0
    := rfl
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 2) : ℝ) := (Annealed.sigmaBar M (n + 2)).2
  have hsubx : translateSet x (openCubeSet (originCube d n)) ⊆
      openCubeSet (originCube d m) :=
    translateSet_openCubeSet_subset_of_anchorGeometry hgeom
  have hsubz : translateSet z (openCubeSet (originCube d (n + 2))) ⊆
      openCubeSet (originCube d m) :=
    translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr
  have hsubimg : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      openCubeSet (originCube d m) := fun p hp => (hgeom hp).2
  have hwin : (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
      openCubeSet (originCube d m)) =
      (fun y' => z + y') '' openCubeSet (originCube d (n + 2)) :=
    inter_eq_of_frontier_inter_empty hz hfr
  have hWvol : volume (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
      openCubeSet (originCube d m)) ≠ 0 := by
    rw [hwin]
    exact volume_image_add_openCubeSet_ne_zero z (originCube d (n + 2))
  have hgL2W := memLp_normalizedVolumeMeasureOn_subset
    (Set.inter_subset_right (s := (fun y' => z + y') '' openCubeSet (originCube d (n + 2))))
    (volume_openCubeSet_ne_zero (originCube d m))
    (volume_openCubeSet_ne_top (originCube d m)) hWvol hgL2
  have hgWW := memLp_normalizedGagliardoMeasureOn_subset
    (Set.inter_subset_right (s := (fun y' => z + y') '' openCubeSet (originCube d (n + 2))))
    (volume_openCubeSet_ne_zero (originCube d m))
    (volume_openCubeSet_ne_top (originCube d m)) hWvol hgW
  have hcaccW := hcacc hmem u hdat g hsol hgL2W hgWW
  have hgL2child := memLp_two_child_of_clause_iv hsubimg hgL2
  have hgWchild := memLp_two_gagliardo_child_of_clause_iv hsubimg hgW
  -- the deterministic `x`-frame composition
  have hxf := eLpNorm_sub_weaklyHarmonic_le_coarseGraining_rebased (z := z) M L omega hs hs1
    hsubx u hdat g hsol hgL2 hgW v w hharm hval hgrad (Annealed.sigmaBar M (n + 2)).2
  -- the energy leg
  have hR3 := h1EnergyNormOnCube_parentRebasedFamily_eq_sqrt_localizedCoeffEnergyValue
    (n := n) (m := m) (k := n + 2) M L x z omega u hsubx hsubz
  set Erep : ℝ := Support.fluxCorrectedErrorRepresentative M L (n + 2)
    ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) with hErepdef
  have hErepCap : Erep ≤ CE * (1 / 2) := hcapE hmem L (le_trans hnm hmL)
  have hErep0 : 0 ≤ Erep := Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  -- names for the atoms
  set Eb : ℝ := Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
    ((3 : ℝ) ^ (2 * (s / 8)) * Erep) with hEbdef
  set sig : ℝ := (Annealed.sigmaBar M (n + 2) : ℝ) with hsigdef
  set X : ℝ := (eLpNorm (fun y => u.toFun y -
      volumeAverage (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
        openCubeSet (originCube d m)) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
          openCubeSet (originCube d m)))).toReal with hXdef
  set Y : ℝ := (Support.normalizedGagliardoESeminormOn
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
        openCubeSet (originCube d m)) s g).toReal with hYdef
  set Ychild : ℝ := (Support.normalizedGagliardoESeminormOn
      ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal with hYchilddef
  set Lhs : ℝ := (eLpNorm (fun y => u.toFun y - v.toFun y) 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => x + y) '' openCubeSet (originCube d n)))).toReal with hLhsdef
  set P2 : ℝ := Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) with hP2def
  set QS : ℝ := Real.rpow s (-(11 / 2 : ℝ)) with hQSdef
  set Q3s : ℝ := Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) with hQ3sdef
  set Q3sn : ℝ := Real.rpow (3 : ℝ) (s * (n : ℝ)) with hQ3sndef
  set Q1s : ℝ := Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) with hQ1sdef
  set R3n : ℝ := Real.rpow (3 : ℝ) ((n : ℝ)) with hR3ndef
  set S4 : ℝ := Real.rpow s (-(4 : ℝ)) with hS4def
  set S192 : ℝ := Real.rpow s (-(19 / 2 : ℝ)) with hS192def
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hY0 : 0 ≤ Y := ENNReal.toReal_nonneg
  have hYchild0 : 0 ≤ Ychild := ENNReal.toReal_nonneg
  have hP20 : 0 ≤ P2 := Real.rpow_nonneg (by norm_num) _
  have hQS0 : 0 ≤ QS := Real.rpow_nonneg hs.le _
  have hQ3s0 : 0 ≤ Q3s := Real.rpow_nonneg (by norm_num) _
  have hQ3sn0 : 0 ≤ Q3sn := Real.rpow_nonneg (by norm_num) _
  have hQ1s0 : 0 ≤ Q1s := Real.rpow_nonneg (by norm_num) _
  have hR3n0 : 0 ≤ R3n := Real.rpow_nonneg (by norm_num) _
  obtain ⟨hS40, hS1920, hsiginv0, hbrkCap, hET, hGbes⟩ :=
    (show (0 ≤ S4) ∧ (0 ≤ S192) ∧ ((0 : ℝ) ≤ sig⁻¹) ∧ (coarseGrainingForceBracket (originCube d n)
      (parentRebasedFamily M L (n + 2) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 2)).2) (s / 3) ≤ b0) ∧ (coarseGrainingEnergyTerm
        (originCube d n)
      (parentRebasedFamily M L (n + 2) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 2)).2) (s / 3)
      (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx)) ≤
      kappa * Real.sqrt Cout * Erep * (sig * (P2 * X) + QS * (Q3s * Y))) ∧
        (Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s
      (fun y => -g (y + x)) ≤ besovGagliardoConstant d * Q3sn * Ychild) from
      @interiorComposed_comparisonBounds2 (d) (by infer_instance) (CE) (Cout) (hCoutpos)
         (hkappa)    (M) (s) (hs) (L) (m) (n) (x) (z) (hz)
          (hgeom) (hfr) (hs1) (omega) (u) (g) (hsubx) (hsubz) (hcaccW) (hgL2child) (hgWchild)
            (hR3) (hErepCap) (hErep0) (herrD) (hbrk)  (hsig))
  have hGbes0 : 0 ≤ Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s
      (fun y => -g (y + x)) :=
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (forceBesovRegularity_translated_neg (originCube d n) hs hs1 hgL2child hgWchild)
  have hYchildle : Ychild ≤ gagliardoWindowConst d * Y :=
    normalizedGagliardoESeminormOn_child_toReal_le hgeom g hgWW
  have hFT : coarseGrainingForceTerm (originCube d n)
      (parentRebasedFamily M L (n + 2) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 2)).2) (s / 3) s (fun y => -g (y + x)) ≤
      b0 * (besovGagliardoConstant d * Q3sn * (gagliardoWindowConst d * Y)) := by
    rw [coarseGrainingForceTerm]
    refine mul_le_mul hbrkCap ?_ hGbes0 hb0
    refine hGbes.trans ?_
    exact mul_le_mul_of_nonneg_left hYchildle
      (mul_nonneg (besovGagliardoConstant_nonneg d) hQ3sn0)
  -- (e) the frame division
  set ET : ℝ := coarseGrainingEnergyTerm (originCube d n)
      (parentRebasedFamily M L (n + 2) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 2)).2) (s / 3)
      (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx))
    with hETdef
  set FT : ℝ := coarseGrainingForceTerm (originCube d n)
      (parentRebasedFamily M L (n + 2) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 2)).2) (s / 3) s (fun y => -g (y + x))
    with hFTdef
  have hW1 : cubeBesovScaleWeight (1 : ℝ) (originCube d n) = Real.rpow (3 : ℝ) (-(n : ℝ)) := by
    have h := cubeBesovScaleWeight_neg_originCube (d := d) n (-1)
    rw [neg_neg] at h
    rw [h]
    congr 1
    ring
  exact ⟨hsubx, hErepCap, hErep0, hsig, hP2def, hQSdef, hQ3sdef, hQ3sndef, hQ1sdef, hR3ndef,
    hS4def, hS192def, hX0, hY0, hQS0, hQ3s0, hQ3sn0, hQ1s0, hR3n0, hS40, hS1920, hsiginv0,
      hYchildle, hET, hFT, hxf, hW1⟩

/-- **The interior clause at the honest exponents.**

See the module docstring for the deviation list; the two `s`-powers are the
proved chain's own, not the printed ones. -/
theorem exists_interiorClause_honest (d : ℕ) [NeZero d] :
    ∃ C Cfin : ℝ, 0 < C ∧ 0 < Cfin ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 2 ≤ m → ∀ x z : Vec d,
          z ∈ openCubeSet (originCube d m) →
            (fun y => x + y) '' openCubeSet (originCube d n) ⊆
                ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
                  openCubeSet (originCube d m) →
            ((fun y => z + y) '' openCubeSet (originCube d (n + 2))) ∩
                frontier (openCubeSet (originCube d m)) = ∅ →
              ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                    (Support.cgEllipLowerConstant d) (n + 2) z
                    ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
                  ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d),
                    Support.IsDirichletSolutionOn
                        (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                        (originCube d m) u hdat g →
                    MemLp g 2 (Support.normalizedVolumeMeasureOn
                      (openCubeSet (originCube d m))) →
                    MemLp (Gagliardo.gagliardoKernel s 2 g) 2
                      (Support.normalizedGagliardoMeasureOn
                        (openCubeSet (originCube d m))) →
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
                                Support.fluxCorrectedErrorRepresentative M L (n + 2)
                                  ⟨s / 8, by linarith only [hs]⟩
                                  (Cutoff.translateCutoffSample z omega) *
                                (eLpNorm (fun y => u.toFun y -
                                    volumeAverage
                                      (((fun y' => z + y') ''
                                          openCubeSet (originCube d (n + 2))) ∩
                                        openCubeSet (originCube d m)) u.toFun) 2
                                  (Support.normalizedVolumeMeasureOn
                                    (((fun y' => z + y') ''
                                        openCubeSet (originCube d (n + 2))) ∩
                                      openCubeSet (originCube d m)))).toReal +
                              Real.rpow s (-(19 / 2 : ℝ)) *
                                ((Annealed.sigmaBar M (n + 2) : ℝ))⁻¹ *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                (Support.normalizedGagliardoESeminormOn
                                  (((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 2))) ∩
                                    openCubeSet (originCube d m)) s g).toReal) := by
  classical
  obtain ⟨CE, hCEpos, hCE⟩ := ae_errorRepresentative_le_harmonicSlot d
  obtain ⟨CC, Cout, hCCpos, hCoutpos, hCC⟩ := ae_interiorCaccioppoliEnergy_anchorWindow d
  -- the explicit constants
  set kappa : ℝ := Real.sqrt (192 * (d : ℝ)) * 3 with hkappadef
  have hkappa : 0 ≤ kappa := by positivity
  set e0 : ℝ := kappa * (CE * (1 / 2)) with he0def
  have he0 : 0 ≤ e0 := mul_nonneg hkappa (by positivity)
  set k0 : ℝ := 2 * (d : ℝ) * (e0 ^ 2 + 1) with hk0def
  have hk0 : 0 ≤ k0 := by positivity
  set b0 : ℝ := Real.sqrt k0 * e0 + 2 * k0 with hb0def
  have hb0 : 0 ≤ b0 := by positivity
  set cg : ℝ := 3 * negNormBaseConst d * coarseGrainingP2Const d with hcgdef
  have hcg : 0 ≤ cg := by
    have h1 : 0 < negNormBaseConst d := negNormBaseConst_pos d
    have h2 : 0 < coarseGrainingP2Const d := coarseGrainingP2Const_pos d
    positivity
  set A1 : ℝ := cg * 216 * (kappa * Real.sqrt Cout) with hA1def
  have hA1 : 0 ≤ A1 := by positivity
  set A2 : ℝ := cg * 1944 * (b0 * (besovGagliardoConstant d * gagliardoWindowConst d))
    with hA2def
  have hA2 : 0 ≤ A2 := by
    have h1 : 0 ≤ besovGagliardoConstant d := besovGagliardoConstant_nonneg d
    have h2 : 0 < gagliardoWindowConst d := gagliardoWindowConst_pos d
    positivity
  set A3 : ℝ := interiorCorrectionConst d * gagliardoWindowConst d with hA3def
  have hA3 : 0 ≤ A3 := by
    have h1 : 0 < interiorCorrectionConst d := interiorCorrectionConst_pos d
    have h2 : 0 < gagliardoWindowConst d := gagliardoWindowConst_pos d
    positivity
  refine ⟨max CE CC, A1 + 9 * (CE * (1 / 2)) * A1 + A2 + A3 + 1, ?_, by positivity, ?_⟩
  · exact lt_of_lt_of_le hCEpos (le_max_left _ _)
  intro M s hsrange hregime hsmall hs L m n hmL hnm x z hz hgeom hfr
  have hs1 : s ≤ 1 := hsrange.2
  have hregimeCE : M.gamma ≤ CE⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 := one_div_le_one_div_of_le hCEpos (le_max_left CE CC)
    rw [one_div, one_div] at h1
    exact h1
  have hregimeCC : M.gamma ≤ CC⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 := one_div_le_one_div_of_le hCCpos (le_max_right CE CC)
    rw [one_div, one_div] at h1
    exact h1
  filter_upwards [hCE M s hsrange hregimeCE hsmall hs n z,
    hCC M s hsrange hregimeCC hsmall hs L m n hmL hnm x z hz hgeom hfr,
    ae_coarseGrainingErrorAtDepth_rebased_le_representative M L n z hs hs1,
    ae_forceBracket_rebased_le M L n z hs hs1] with omega hcapE hcacc herrD hbrk
  intro hmem u hdat g hsol hgL2 hgW v w hharm hval hgrad
  obtain ⟨hsubx, hErepCap, hErep0, hsig, hP2def, hQSdef, hQ3sdef, hQ3sndef, hQ1sdef, hR3ndef,
    hS4def, hS192def, hX0, hY0, hQS0, hQ3s0, hQ3sn0, hQ1s0, hR3n0, hS40, hS1920, hsiginv0,
      hYchildle, hET, hFT, hxf, hW1⟩ :=
    @interiorComposed_comparisonBounds3 (d) (by infer_instance) (CE) (Cout) (hCoutpos)
      (hkappa)    (hb0) (M) (s) (hs) (L) (m) (n) (hmL) (hnm) (x) (z) (hz)
        (hgeom) (hfr) (hs1) (omega) (hcapE) (hcacc) (herrD) (hbrk) (hmem) (u) (hdat) (g) (hsol)
          (hgL2) (hgW) (v) (w) (hharm) (hval) (hgrad)
  set Erep : ℝ := Support.fluxCorrectedErrorRepresentative M L (n + 2)
    ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) with hErepdef
  set Eb : ℝ := Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
    ((3 : ℝ) ^ (2 * (s / 8)) * Erep) with hEbdef
  set sig : ℝ := (Annealed.sigmaBar M (n + 2) : ℝ) with hsigdef
  set X : ℝ := (eLpNorm (fun y => u.toFun y -
      volumeAverage (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
        openCubeSet (originCube d m)) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
          openCubeSet (originCube d m)))).toReal with hXdef
  set Y : ℝ := (Support.normalizedGagliardoESeminormOn
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
        openCubeSet (originCube d m)) s g).toReal with hYdef
  set Ychild : ℝ := (Support.normalizedGagliardoESeminormOn
      ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal with hYchilddef
  set Lhs : ℝ := (eLpNorm (fun y => u.toFun y - v.toFun y) 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => x + y) '' openCubeSet (originCube d n)))).toReal with hLhsdef
  set P2 : ℝ := Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) with hP2def
  set QS : ℝ := Real.rpow s (-(11 / 2 : ℝ)) with hQSdef
  set Q3s : ℝ := Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) with hQ3sdef
  set Q3sn : ℝ := Real.rpow (3 : ℝ) (s * (n : ℝ)) with hQ3sndef
  set Q1s : ℝ := Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) with hQ1sdef
  set R3n : ℝ := Real.rpow (3 : ℝ) ((n : ℝ)) with hR3ndef
  set S4 : ℝ := Real.rpow s (-(4 : ℝ)) with hS4def
  set S192 : ℝ := Real.rpow s (-(19 / 2 : ℝ)) with hS192def
  set ET : ℝ := coarseGrainingEnergyTerm (originCube d n)
      (parentRebasedFamily M L (n + 2) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 2)).2) (s / 3)
      (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx))
    with hETdef
  set FT : ℝ := coarseGrainingForceTerm (originCube d n)
      (parentRebasedFamily M L (n + 2) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 2)).2) (s / 3) s (fun y => -g (y + x))
    with hFTdef
  rw [hW1] at hxf
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
    mul_nonneg (mul_nonneg (interiorCorrectionConst_pos d).le (Real.rpow_nonneg hs.le _)) hQ3sn0
  have hleg1 : 216 * (s⁻¹) ^ (4 : ℕ) * ET ≤
      216 * (s⁻¹) ^ (4 : ℕ) *
        (kappa * Real.sqrt Cout * Erep * (sig * (P2 * X) + QS * (Q3s * Y))) :=
    mul_le_mul_of_nonneg_left hET (by positivity)
  have hleg2 : 1944 * (s⁻¹) ^ (6 : ℕ) * FT ≤
      1944 * (s⁻¹) ^ (6 : ℕ) *
        (b0 * (besovGagliardoConstant d * Q3sn * (gagliardoWindowConst d * Y))) :=
    mul_le_mul_of_nonneg_left hFT (by positivity)
  have hleg3 : interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn * Ychild ≤
      interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn *
        (gagliardoWindowConst d * Y) :=
    mul_le_mul_of_nonneg_left hYchildle hccorr0
  have hmono := add_le_add (mul_le_mul_of_nonneg_left (add_le_add hleg1 hleg2) hcg) hleg3
  clear_value Lhs X Y Ychild ET FT Erep Eb sig P2 QS Q3s Q3sn Q1s R3n S4 S192
  -- (g) the regrouping
  obtain ⟨hT1, hT2, hT3, hXterm, hYterm, hCE2⟩ :=
    (show ((sig⁻¹ * R3n) * (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
        (kappa * Real.sqrt Cout * Erep * (sig * (P2 * X) + QS * (Q3s * Y))))) ≤
      A1 * (S4 * Erep * X) + (9 * (CE * (1 / 2)) * A1) * (S192 * sig⁻¹ * Q1s * Y)) ∧ ((sig⁻¹ *
        R3n) * (cg * (1944 * (s⁻¹) ^ (6 : ℕ) *
        (b0 * (besovGagliardoConstant d * Q3sn * (gagliardoWindowConst d * Y))))) ≤
      A2 * (S192 * sig⁻¹ * Q1s * Y)) ∧ ((sig⁻¹ * R3n) * (interiorCorrectionConst d * Real.rpow s
        (-(1 / 2 : ℝ)) * Q3sn *
        (gagliardoWindowConst d * Y)) ≤ A3 * (S192 * sig⁻¹ * Q1s * Y)) ∧ ((0 : ℝ) ≤ S4 * Erep * X)
          ∧ ((0 : ℝ) ≤ S192 * sig⁻¹ * Q1s * Y) ∧ ((0 : ℝ) ≤ 9 * (CE * (1 / 2)) * A1) from
      @interiorComposed_comparisonBounds1 (d) (by infer_instance) (CE) (hCEpos) (Cout) (hCoutpos)
        (hcg)  (hA1)  (hA2)  (hA3) (s) (hs) (n) (hs1) (Erep) (hErepCap)
          (hErep0) (sig) (X) (Y) (P2) (hP2def) (QS) (hQSdef) (Q3s) (hQ3sdef) (Q3sn) (hQ3sndef)
            (Q1s) (hQ1sdef) (R3n) (hR3ndef) (S4) (hS4def) (S192) (hS192def) (hX0) (hY0) (hQS0)
              (hQ3s0) (hQ1s0) (hR3n0) (hS40) (hS1920) (hsiginv0) (hsinv))
  refine hstep.trans ?_
  refine le_trans (mul_le_mul_of_nonneg_left hmono hfac0) ?_
  have hdistrib : (sig⁻¹ * R3n) *
      (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
              (kappa * Real.sqrt Cout * Erep * (sig * (P2 * X) + QS * (Q3s * Y))) +
            1944 * (s⁻¹) ^ (6 : ℕ) *
              (b0 * (besovGagliardoConstant d * Q3sn * (gagliardoWindowConst d * Y)))) +
        interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn *
          (gagliardoWindowConst d * Y)) =
      (sig⁻¹ * R3n) * (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
            (kappa * Real.sqrt Cout * Erep * (sig * (P2 * X) + QS * (Q3s * Y))))) +
        (sig⁻¹ * R3n) * (cg * (1944 * (s⁻¹) ^ (6 : ℕ) *
            (b0 * (besovGagliardoConstant d * Q3sn * (gagliardoWindowConst d * Y))))) +
        (sig⁻¹ * R3n) * (interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn *
          (gagliardoWindowConst d * Y)) := by ring
  rw [hdistrib]
  have hsum : A1 * (S4 * Erep * X) + (9 * (CE * (1 / 2)) * A1) * (S192 * sig⁻¹ * Q1s * Y) +
      A2 * (S192 * sig⁻¹ * Q1s * Y) + A3 * (S192 * sig⁻¹ * Q1s * Y) ≤
      (A1 + 9 * (CE * (1 / 2)) * A1 + A2 + A3 + 1) * (S4 * Erep * X + S192 * sig⁻¹ * Q1s * Y) := by
    have hC1 : A1 ≤ A1 + 9 * (CE * (1 / 2)) * A1 + A2 + A3 + 1 := by
      linarith only [hCE2, hA2, hA3]
    have hC2 : 9 * (CE * (1 / 2)) * A1 + A2 + A3 ≤
        A1 + 9 * (CE * (1 / 2)) * A1 + A2 + A3 + 1 := by linarith only [hA1]
    calc A1 * (S4 * Erep * X) + (9 * (CE * (1 / 2)) * A1) * (S192 * sig⁻¹ * Q1s * Y) +
          A2 * (S192 * sig⁻¹ * Q1s * Y) + A3 * (S192 * sig⁻¹ * Q1s * Y)
        = A1 * (S4 * Erep * X) +
            (9 * (CE * (1 / 2)) * A1 + A2 + A3) * (S192 * sig⁻¹ * Q1s * Y) := by ring
      _ ≤ (A1 + 9 * (CE * (1 / 2)) * A1 + A2 + A3 + 1) * (S4 * Erep * X) +
            (A1 + 9 * (CE * (1 / 2)) * A1 + A2 + A3 + 1) * (S192 * sig⁻¹ * Q1s * Y) :=
          add_le_add (mul_le_mul_of_nonneg_right hC1 hXterm)
            (mul_le_mul_of_nonneg_right hC2 hYterm)
      _ = (A1 + 9 * (CE * (1 / 2)) * A1 + A2 + A3 + 1) *
            (S4 * Erep * X + S192 * sig⁻¹ * Q1s * Y) := by ring
  linarith only [hT1, hT2, hT3, hsum]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
