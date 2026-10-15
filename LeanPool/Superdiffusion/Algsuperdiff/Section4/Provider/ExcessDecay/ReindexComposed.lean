/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.GeneralClauseInteriorComposed
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ReindexEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ReindexEnergy

/-!
# ReindexComposed

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The general clause at frontier-empty windows, composed at the slot `n+3`

`GeneralClauseInteriorComposed` composes the proved chain at the slot `n+2`;
this module re-runs the **same** composition at the frozen slot `n+3`:

```text
  1_𝒢 ‖u − v‖_{L²(x+□_n)}
      ≤ C ( s^{-4} 𝓔_{s/8}(z+□_{n+3}; ã_{L,n+3}, σ_{n+3}) ‖u − (u)_W‖_{L²(W)}
          + s^{-7} σ_{n+3}^{-1} 3^{(1+s)n} [g]_{H^s(W)} ) ,
      W = (z + □_{n+2}) ∩ □_m ,
```

on the good event `𝒢(n+3, z; s/8, 1/2)` and under the frozen binder
`n + 3 ≤ m`.  Three inputs move, nothing else:

* the **energy leg** — `ReindexEnergy.ae_constantDatumEnergy_anchorWindow_addThree`;
* the **child-frame objects** — `ReindexEllipticity`'s two caps, at the
  depth-`3` off-grid factor `3^{3s/8}` in place of `3^{s/4}`;
* the **caps** — `ReindexSlot.ae_errorRepresentative_le_harmonicSlot_addThree`, read
  at `L ≥ n+3`, which is exactly what the frozen binder `n + 3 ≤ m ≤ L`
  supplies.

**The energy leg's identity is slot-free.**  The bridge
`InteriorEnergyBridge.h1EnergyNormOnCube_parentRebasedFamily_eq` and the
`ν`-identification `NuIdentification.localizedCoeffEnergyValue_fluxCorrectedCoeffFamily_eq`
both evaluate to `ν ⨍|∇u|²`, with **no** dependence on the flux slot or on the
cube carrying the correction; so the bridge below is proved on the
anchor's own `(n+2)`-containment `z + □_{n+2} ⊆ □_m` — the frozen gate's
own consequence — and never needs `z + □_{n+3} ⊆ □_m`, which the anchor does
not supply.

The constant `kappa = √(192 d)·3` is **unchanged**: the depth factor
`3^{3(s/8)}` still satisfies `3^{3(s/8)} ≤ 3` on `s ≤ 1` (indeed `3s/8 ≤ 3/8`),
so the one extra depth is absorbed with no constant move at all.

## Deviations from the printed statement

* the off-grid depth factor is `3^{3s/8}` (proved: `3^{s/4}`) — one extra
  `3^{s/8} ≤ 3^{1/8}`, absorbed inside the unchanged `kappa`;
* the centre-child cap costs `3^{s/8} ≤ 3^{1/8}`, absorbed in
  `ReindexSlot`'s own constant;
* the `σ` index: the force leg carries `σ_{n+3}^{-1}`; the frozen statement
  carries `σ_n^{-1}`, and `ReindexSlot.exists_inv_sigmaBar_add_three_le`
  converts at the factor `4` — the *same* constant as the proved two-scale
  conversion, the gap being free;
* no `γ`-move and no `s`-exponent move is made anywhere.

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

/-! ## 1. The sharpened arithmetic, at the `n+3` comparator -/

private abbrev reindexComposed_comparisonBounds1_statement : Prop :=
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
                    ((fluxCorrectedCoeffFamily M L (n + (3 : ℤ)) (originCube d (n + (3 : ℤ)))
                          (Cutoff.translateCutoffSample z omega)).coeffOn
                      (originCube d (n + (2 : ℤ))))
                    (H1Function.untranslate z
                      (u.restrict (isOpen_translateSet_openCubeSet z (n + (2 : ℤ)))
                        (translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr))) ≤
                  Cout *
                    constantDatumAnchorEnergyRHSOnAddThree M n s
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
                Ch03.h1EnergyNormOnCube (originCube d n) (parentRebasedFamily M L (n + (3 : ℤ)) x
                  z omega)
                    (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n)
                      hsubx)) =
                  √(Ch03.localizedCoeffEnergyValue ((fun (y : Vec d) => x - z + y) '' openCubeSet
                    (originCube d n))
                      ((fluxCorrectedCoeffFamily M L (n + (3 : ℤ)) (originCube d (n + (3 : ℤ)))
                            (Cutoff.translateCutoffSample z omega)).coeffOn
                        (originCube d (n + (2 : ℤ))))
                      (H1Function.untranslate z (u.restrict (isOpen_translateSet_openCubeSet z (n
                        + (2 : ℤ))) hsubz)))),
              let Erep : ℝ :=
                fluxCorrectedErrorRepresentative M L (n + (3 : ℤ)) ⟨s / (8 : ℝ), (by positivity)⟩
                  (Cutoff.translateCutoffSample z omega);
              ∀ (_ : Erep ≤ CE * (1 / 2 : ℝ)) (_ : (0 : ℝ) ≤ Erep),
                let Eb : ℝ :=
                  √(offGridStabilityConst d (s / (6 : ℝ)) (s / (8 : ℝ))) * ((3 : ℝ) ^ ((3 : ℝ) *
                    (s / (8 : ℝ))) * Erep);
                ∀
                  (_ :
                    ∀ (x : Vec d) (m : ℤ),
                      (fun (y : Vec d) => x + y) '' openCubeSet (originCube d n) ⊆
                          (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (1 : ℤ))) ∩
                            openCubeSet (originCube d m) →
                        Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
                            (parentRebasedFamily M L (n + (3 : ℤ)) x z omega)
                            (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s /
                              (3 : ℝ)) (0 : ℕ) ≤
                          Eb)
                  (_ :
                    ∀ (x : Vec d) (m : ℤ),
                      (fun (y : Vec d) => x + y) '' openCubeSet (originCube d n) ⊆
                          (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (1 : ℤ))) ∩
                            openCubeSet (originCube d m) →
                        coarseGrainingForceBracket (originCube d n) (parentRebasedFamily M L (n +
                          (3 : ℤ)) x z omega)
                            (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s /
                              (3 : ℝ)) ≤
                          √((2 : ℝ) * (↑d : ℝ) * (Eb ^ (2 : ℕ) + (1 : ℝ))) * Eb +
                            (2 : ℝ) * ((2 : ℝ) * (↑d : ℝ) * (Eb ^ (2 : ℕ) + (1 : ℝ))))
                  ,
                  let sig : ℝ := (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ);
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
                    let QS : ℝ := s.rpow (-3 : ℝ);
                    let Q3s : ℝ := Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ));
                    let Q3sn : ℝ := Real.rpow (3 : ℝ) (s * (↑n : ℝ));
                    let S4 : ℝ := s.rpow (-4 : ℝ);
                    let S7 : ℝ := s.rpow (-7 : ℝ);
                    (0 : ℝ) ≤ S4 ∧
                      (0 : ℝ) ≤ S7 ∧
                        (0 : ℝ) ≤ sig⁻¹ ∧
                          coarseGrainingForceBracket (originCube d n) (parentRebasedFamily M L (n
                            + (3 : ℤ)) x z omega)
                                (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s
                                  / (3 : ℝ)) ≤
                              b0 ∧
                            coarseGrainingEnergyTerm (originCube d n) (parentRebasedFamily M L (n
                              + (3 : ℤ)) x z omega)
                                  (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property)
                                    (s / (3 : ℝ))
                                  (H1Function.untranslate x (u.restrict
                                    (isOpen_translateSet_openCubeSet x n) hsubx)) ≤
                                kappa * √Cout * Erep * (sig * (P2 * X) + QS * (Q3s * Y)) ∧
                              (Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n)
                                s fun (y : Vec d) =>
                                  -g (y + x)) ≤
                                besovGagliardoConstant d * Q3sn * Ychild

private abbrev reindexComposed_comparisonBounds3_statement : Prop :=
    ∀ (d : ℕ) [NeZero d] (CE Cout : ℝ) (_ : (0 : ℝ) < Cout),
      let kappa : ℝ := √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ);
      ∀ (_ : (0 : ℝ) ≤ kappa),
        let e0 : ℝ := kappa * (CE * (1 / 2 : ℝ));
          let k0 : ℝ := (2 : ℝ) * (↑d : ℝ) * (e0 ^ (2 : ℕ) + (1 : ℝ));
            let b0 : ℝ := √k0 * e0 + (2 : ℝ) * k0;
            ∀ (_ : (0 : ℝ) ≤ b0) (M : ABKModel d) (s : ℝ) (_ :
              (0 : ℝ) < s)
              (L m n : ℤ) (_ : m ≤ L) (_ : n + (3 : ℤ) ≤ m) (x z : Vec d) (hz : z ∈ openCubeSet
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
                              ((fluxCorrectedCoeffFamily M L (n + (3 : ℤ)) (originCube d (n + (3 :
                                ℤ)))
                                    (Cutoff.translateCutoffSample z omega)).coeffOn
                                (originCube d (n + (2 : ℤ))))
                              (H1Function.untranslate z
                                (u.restrict (isOpen_translateSet_openCubeSet z (n + (2 : ℤ)))
                                  (translateSet_openCubeSet_subset_of_frontier_inter_empty hz
                                    hfr))) ≤
                            Cout *
                              constantDatumAnchorEnergyRHSOnAddThree M n s
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
              (_ : ∀ (y : Vec d), v.grad y = u.grad y - w.grad y)
              (_ : (0 : ℝ) < (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ)),
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
                s.rpow (-3 : ℝ) = s.rpow (-3 : ℝ)) (_ :
                Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ)) = Real.rpow (3 : ℝ) (s * (↑(n + (2 :
                  ℤ)) : ℝ))) (_ :
                Real.rpow (3 : ℝ) (s * (↑n : ℝ)) = Real.rpow (3 : ℝ) (s * (↑n : ℝ))) (_ :
                Real.rpow (3 : ℝ) (((1 : ℝ) + s) * (↑n : ℝ)) = Real.rpow (3 : ℝ) (((1 : ℝ) + s) *
                  (↑n : ℝ))) (_ :
                Real.rpow (3 : ℝ) (↑n : ℝ) = Real.rpow (3 : ℝ) (↑n : ℝ)) (_ : s.rpow (-4 : ℝ) =
                  s.rpow (-4 : ℝ)) (_ :
                s.rpow (-7 : ℝ) = s.rpow (-7 : ℝ)) (_ :
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
                (_ : (0 : ℝ) ≤ s.rpow (-3 : ℝ)) (_ : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (s * (↑(n + (2 :
                  ℤ)) : ℝ))) (_ :
                (0 : ℝ) ≤ Real.rpow (3 : ℝ) (s * (↑n : ℝ))) (_ : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (((1
                  : ℝ) + s) * (↑n : ℝ))) (_
                : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (↑n : ℝ)) (_ : (0 : ℝ) ≤ s.rpow (-4 : ℝ)) (_ : (0 :
                  ℝ) ≤ s.rpow (-7 : ℝ)) (_ :
                (0 : ℝ) ≤ (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ)⁻¹) (_ :
                (normalizedGagliardoESeminormOn ((fun (y : Vec d) => x + y) '' openCubeSet
                  (originCube d n)) s g).toReal ≤
                  gagliardoWindowConst d *
                    (normalizedGagliardoESeminormOn
                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2 : ℤ))) ∩
                          openCubeSet (originCube d m))
                        s g).toReal)
                (_ :
                coarseGrainingEnergyTerm (originCube d n) (parentRebasedFamily M L (n + (3 : ℤ)) x
                  z omega)
                    (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s / (3 : ℝ))
                    (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n)
                      hsubx)) ≤
                  kappa * √Cout *
                      fluxCorrectedErrorRepresentative M L (n + (3 : ℤ)) ⟨s / (8 : ℝ), (by
                        positivity)⟩
                        (Cutoff.translateCutoffSample z omega) *
                    ((↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) *
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
                      s.rpow (-3 : ℝ) *
                        (Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ)) *
                          (normalizedGagliardoESeminormOn
                              ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (2 :
                                ℤ))) ∩
                                openCubeSet (originCube d m))
                              s g).toReal)))
                (_ :
                (coarseGrainingForceTerm (originCube d n) (parentRebasedFamily M L (n + (3 : ℤ)) x
                  z omega)
                    (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s / (3 : ℝ))
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
                          g).toReal),
                cubeBesovScaleWeight (1 : ℝ) (originCube d n) = Real.rpow (3 : ℝ) (-(↑n :
                  ℝ))

/-- **The two legs of the `n+3` Caccioppoli right-hand side.**

```text
  ( σ_{n+3} 3^{-2(n+2)} X² + s^{-6} σ_{n+3}^{-1} 3^{2s(n+2)} Y² )^{1/2}
      ≤ σ_{n+3}^{1/2} 3^{-(n+2)} X  +  s^{-3} σ_{n+3}^{-1/2} 3^{s(n+2)} Y .
```
-/
theorem sqrt_constantDatumAnchorEnergyRHSOn_addThree_le (M : ABKModel d) (n : ℤ)
    {s : ℝ} (hs : 0 < s) (W : Set (Vec d)) (f : Vec d → ℝ) (g : Vec d → Vec d) :
    Real.sqrt (constantDatumAnchorEnergyRHSOnAddThree M n s W f g) ≤
      Real.sqrt (Annealed.sigmaBar M (n + 3) : ℝ) *
          Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
          (eLpNorm (fun y => f y - volumeAverage W f) 2
            (Support.normalizedVolumeMeasureOn W)).toReal +
        Real.rpow s (-(3 : ℝ)) *
          Real.sqrt ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
          Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) *
          (Support.normalizedGagliardoESeminormOn W s g).toReal := by
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 3) : ℝ) := (Annealed.sigmaBar M (n + 3)).2
  set X : ℝ := (eLpNorm (fun y => f y - volumeAverage W f) 2
    (Support.normalizedVolumeMeasureOn W)).toReal with hXdef
  set Y : ℝ := (Support.normalizedGagliardoESeminormOn W s g).toReal with hYdef
  have hX : 0 ≤ X := ENNReal.toReal_nonneg
  have hY : 0 ≤ Y := ENNReal.toReal_nonneg
  set P3 : ℝ := Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ)) with hP3def
  set Q3 : ℝ := Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) with hQ3def
  set PS : ℝ := Real.rpow s (-6 : ℝ) with hPSdef
  set QS : ℝ := Real.rpow s (-(3 : ℝ)) with hQSdef
  set P3s : ℝ := Real.rpow (3 : ℝ) (2 * s * (((n + 2 : ℤ)) : ℝ)) with hP3sdef
  set Q3s : ℝ := Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) with hQ3sdef
  set SIG : ℝ := (Annealed.sigmaBar M (n + 3) : ℝ) with hSIGdef
  have hP3nn : (0 : ℝ) ≤ P3 := Real.rpow_nonneg (by norm_num) _
  have hPSnn : (0 : ℝ) ≤ PS := Real.rpow_nonneg hs.le _
  have hP3snn : (0 : ℝ) ≤ P3s := Real.rpow_nonneg (by norm_num) _
  have hP3sqrt : Real.sqrt P3 = Q3 := by
    rw [hP3def, hQ3def,
      show (-2 : ℝ) * (((n + 2 : ℤ)) : ℝ) = 2 * (-(((n + 2 : ℤ)) : ℝ)) by ring]
    exact sqrt_rpow_two_mul (by norm_num) _
  have hPSsqrt : Real.sqrt PS = QS := by
    rw [hPSdef, hQSdef, show (-6 : ℝ) = 2 * (-(3 : ℝ)) by norm_num]
    exact sqrt_rpow_two_mul hs _
  have hP3ssqrt : Real.sqrt P3s = Q3s := by
    rw [hP3sdef, hQ3sdef,
      show (2 : ℝ) * s * (((n + 2 : ℤ)) : ℝ) = 2 * (s * (((n + 2 : ℤ)) : ℝ)) by ring]
    exact sqrt_rpow_two_mul (by norm_num) _
  have hAnn : (0 : ℝ) ≤ SIG * P3 * X ^ (2 : ℕ) :=
    mul_nonneg (mul_nonneg hsig.le hP3nn) (pow_nonneg hX 2)
  have hBnn : (0 : ℝ) ≤ PS * SIG⁻¹ * P3s * Y ^ (2 : ℕ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hPSnn (inv_nonneg.mpr hsig.le)) hP3snn)
      (pow_nonneg hY 2)
  have hA : Real.sqrt (SIG * P3 * X ^ (2 : ℕ)) = Real.sqrt SIG * Q3 * X := by
    rw [Real.sqrt_mul (mul_nonneg hsig.le hP3nn) (X ^ (2 : ℕ)), Real.sqrt_sq hX,
      Real.sqrt_mul hsig.le P3, hP3sqrt]
  have hB : Real.sqrt (PS * SIG⁻¹ * P3s * Y ^ (2 : ℕ)) =
      QS * Real.sqrt SIG⁻¹ * Q3s * Y := by
    have h1 : (0 : ℝ) ≤ PS * SIG⁻¹ := mul_nonneg hPSnn (inv_nonneg.mpr hsig.le)
    rw [Real.sqrt_mul (mul_nonneg h1 hP3snn) (Y ^ (2 : ℕ)), Real.sqrt_sq hY,
      Real.sqrt_mul h1 P3s, Real.sqrt_mul hPSnn SIG⁻¹, hPSsqrt, hP3ssqrt]
  rw [constantDatumAnchorEnergyRHSOnAddThree]
  exact le_trans (sqrt_add_le_sqrt_add_sqrt hAnn hBnn)
    (le_of_eq (by rw [hA, hB]))

/-! ## 2. The slot-free energy bridge -/

/-- **The energy leg at the `(n+3)` re-based family.**

The coefficient-energy norm carried by the child-frame coarse-graining energy
term at the `(n+3)` re-based family is exactly the square root of the localized
coefficient energy that `ReindexEnergy` bounds — same solution, same window,
two frames.  Both sides are `ν ⨍|∇u|²`, so the flux slot never enters and the
containment needed is the anchor's own `z + □_{n+2} ⊆ □_m`. -/
theorem h1EnergyNormOnCube_parentRebasedFamily_addThree_eq_sqrt_localizedCoeffEnergyValue
    {n m : ℤ} (M : ABKModel d) (L : ℤ) (x z : Vec d)
    (omega : Cutoff.CutoffSample d) (u : H1Function (openCubeSet (originCube d m)))
    (hx : translateSet x (openCubeSet (originCube d n)) ⊆
      openCubeSet (originCube d m))
    (hz : translateSet z (openCubeSet (originCube d (n + 2))) ⊆
      openCubeSet (originCube d m)) :
    Ch03.h1EnergyNormOnCube (originCube d n) (parentRebasedFamily M L (n + 3) x z omega)
        (H1Function.untranslate x
          (u.restrict (isOpen_translateSet_openCubeSet x n) hx)) =
      Real.sqrt (Ch03.localizedCoeffEnergyValue
        ((fun y => (x - z) + y) '' openCubeSet (originCube d n))
        ((Support.fluxCorrectedCoeffFamily M L (n + 3) (originCube d (n + 3))
          (Cutoff.translateCutoffSample z omega)).coeffOn (originCube d (n + 2)))
        (H1Function.untranslate z
          (u.restrict (isOpen_translateSet_openCubeSet z (n + 2)) hz))) := by
  rw [h1EnergyNormOnCube_parentRebasedFamily_eq M L (n + 3) n x z omega,
    localizedCoeffEnergyValue_fluxCorrectedCoeffFamily_eq M L (n + 3)
      (originCube d (n + 3)) (originCube d (n + 2))
      (Cutoff.translateCutoffSample z omega)]
  refine congrArg Real.sqrt (congrArg (fun t => (M.nu : ℝ) * t) ?_)
  exact (normalizedSetAverage_vecNormSq_grad_frame n x z u.grad).symm

/-! ## 3. The composed general clause at the slot `n+3` -/

private theorem reindexComposed_comparisonBounds1 : reindexComposed_comparisonBounds1_statement :=
  by
  intro d _ _CE Cout hCoutpos kappa hkappa e0 k0 b0 M s hs L m n x z _ hgeom _ hs1 omega u g hsubx
    _ hcaccW hgL2child hgWchild hR3 Erep hErepCap hErep0 Eb herrD hbrk sig hsig X Y Ychild P2 QS
    Q3s Q3sn S4 S7
  have he0def :
    e0 = kappa * (_CE * (1 / 2 : ℝ)) := rfl
  have hS40 : 0 ≤ S4 := Real.rpow_nonneg hs.le _
  have hS70 : 0 ≤ S7 := Real.rpow_nonneg hs.le _
  have hsiginv0 : (0 : ℝ) ≤ sig⁻¹ := inv_nonneg.mpr hsig.le
  have herror := offGridStabilityError_bound (d := d) hs hs1
    (by linarith only [hs1] : (3 : ℝ) * (s / 8) ≤ 1) hErep0
  have hEb0 : 0 ≤ Eb := herror.1
  have hEbkappa : Eb ≤ kappa * Erep := herror.2
  have hEbe0 : Eb ≤ e0 := by
    refine hEbkappa.trans ?_
    rw [he0def]
    exact mul_le_mul_of_nonneg_left hErepCap hkappa
  -- (c) the energy leg
  have hEnergy : Ch03.h1EnergyNormOnCube (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx)) ≤
      Real.sqrt Cout * (Real.sqrt sig * P2 * X + QS * Real.sqrt sig⁻¹ * Q3s * Y) := by
    rw [hR3]
    refine le_trans (Real.sqrt_le_sqrt hcaccW) ?_
    rw [Real.sqrt_mul hCoutpos.le]
    exact mul_le_mul_of_nonneg_left
      (sqrt_constantDatumAnchorEnergyRHSOn_addThree_le M n hs _ u.toFun g) (Real.sqrt_nonneg _)
  have hcomparison := coarseGraining_comparisonBounds (originCube d n)
    (parentRebasedFamily M L (n + 3) x z omega) hsig (s / 3)
    kappa Erep Eb e0 Cout P2 QS Q3s X Y
    (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx))
    hkappa hErep0 hEb0 hEbe0 ((herrD x m hgeom).trans hEbkappa) (hbrk x m hgeom) hEnergy
  have hbrkCap : coarseGrainingForceBracket (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) ≤ b0 := hcomparison.1
  have hET := hcomparison.2
  -- (d) the forcing leg
  have hGbes : Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s
      (fun y => -g (y + x)) ≤ besovGagliardoConstant d * Q3sn * Ychild :=
    besovVectorSeminormTwo_originCube_translated_neg_le n hs hs1 hgL2child hgWchild
  exact ⟨hS40, hS70, hsiginv0, hbrkCap, hET, hGbes⟩

private theorem reindexComposed_comparisonBounds2 :
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
              (_ : QS = s.rpow (-3 : ℝ)) (Q3s : ℝ) (_ : Q3s = Real.rpow (3 : ℝ) (s * (↑(n + (2 :
                ℤ)) : ℝ)))
              (Q3sn : ℝ) (_ : Q3sn = Real.rpow (3 : ℝ) (s * (↑n : ℝ))) (Q1s : ℝ)
              (_ : Q1s = Real.rpow (3 : ℝ) (((1 : ℝ) + s) * (↑n : ℝ))) (R3n : ℝ)
              (_ : R3n = Real.rpow (3 : ℝ) (↑n : ℝ)) (S4 : ℝ) (_ : S4 = s.rpow (-4 : ℝ)) (S7 : ℝ)
              (_ : S7 = s.rpow (-7 : ℝ)) (_ : (0 : ℝ) ≤ X) (_ : (0 : ℝ) ≤ Y) (_ : (0 : ℝ) ≤ QS)
              (_ : (0 : ℝ) ≤ Q3s) (_ : (0 : ℝ) ≤ Q1s) (_ : (0 : ℝ) ≤ R3n) (_ : (0 : ℝ) ≤ S4)
              (_ : (0 : ℝ) ≤ S7) (_ : (0 : ℝ) ≤ sig⁻¹) (_ : sig⁻¹ * sig = (1 : ℝ)),
              sig⁻¹ * R3n *
                    (cg * ((216 : ℝ) * s⁻¹ ^ (4 : ℕ) * (kappa * √Cout * Erep * (sig * (P2 * X) +
                      QS * (Q3s * Y))))) ≤
                  A1 * (S4 * Erep * X) + (9 : ℝ) * (CE * (1 / 2 : ℝ)) * A1 * (S7 * sig⁻¹ * Q1s *
                    Y) ∧
                sig⁻¹ * R3n *
                      (cg *
                        ((1944 : ℝ) * s⁻¹ ^ (6 : ℕ) *
                          (b0 * (besovGagliardoConstant d * Q3sn * (gagliardoWindowConst d *
                            Y))))) ≤
                    A2 * (S7 * sig⁻¹ * Q1s * Y) ∧
                  sig⁻¹ * R3n * (interiorCorrectionConst d * s.rpow (-(1 / 2 : ℝ)) * Q3sn *
                    (gagliardoWindowConst d * Y)) ≤
                      A3 * (S7 * sig⁻¹ * Q1s * Y) ∧
                    (0 : ℝ) ≤ S4 * Erep * X ∧ (0 : ℝ) ≤ S7 * sig⁻¹ * Q1s * Y ∧ (0 : ℝ) ≤ (9 : ℝ) *
                      (CE * (1 / 2 : ℝ)) * A1 := by
  intro d _ CE _ Cout _ kappa _ _ b0 cg _ A1 hA1 A2 hA2 A3 hA3 s hs n hs1 Erep hErepCap hErep0
    sig X Y P2 hP2def QS hQSdef Q3s hQ3sdef Q3sn hQ3sndef Q1s hQ1sdef R3n hR3ndef S4 hS4def S7
    hS7def hX0 hY0 hQS0 hQ3s0 hQ1s0 hR3n0 hS40 hS70 hsiginv0 hsinv
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
  have hS4QS : S4 * QS = S7 := by
    rw [hS4def, hQSdef, hS7def]
    exact rpow_s_four_mul_three hs
  have hS6le : Real.rpow s (-(6 : ℝ)) ≤ S7 := by
    rw [hS7def]
    exact rpow_le_rpow_neg_seven hs hs1 (by norm_num)
  have hQScle : Real.rpow s (-(1 / 2 : ℝ)) ≤ S7 := by
    rw [hS7def]
    exact rpow_le_rpow_neg_seven hs hs1 (by norm_num)
  have hRP2 : R3n * P2 ≤ 1 := by
    rw [hR3ndef, hP2def]
    exact rpow_three_frame_l2_le_one n
  have hRQ3s : R3n * Q3s ≤ 9 * Q1s := by
    rw [hR3ndef, hQ3sdef, hQ1sdef]
    exact rpow_three_frame_force_le n hs1
  have hRQ3sn : R3n * Q3sn = Q1s := by
    rw [hR3ndef, hQ3sndef, hQ1sdef]
    exact rpow_three_mul_eq_one_add s n
  have hshared := scalar_frame_three_term_bounds A1 A2 A3 (CE * (1 / 2)) Erep sig
    R3n P2 QS Q3s Q3sn Q1s S4 S7 (Real.rpow s (-6)) (Real.rpow s (-(1 / 2)))
    9 X Y hA1 hA2 hA3 hErep0 hErepCap hX0 hY0 hQS0 hQ3s0 hQ1s0 hR3n0 hS40
    hS70 hsiginv0 hsinv hRP2 hRQ3s hRQ3sn hS4QS hS6le hQScle (by norm_num)
  refine ⟨?_, ?_, ?_, hshared.2.2.2.1, hshared.2.2.2.2.1, hshared.2.2.2.2.2⟩
  · convert hshared.1 using 1
    simp only [hA1def, hS4eq]
    ring
  · convert hshared.2.1 using 1
    simp only [hA2def, hS6eq]
    ring
  · convert hshared.2.2.1 using 1
    simp only [hA3def]
    ring

private theorem reindexComposed_comparisonBounds3 : reindexComposed_comparisonBounds3_statement :=
  by
  classical
  intro d _ CE Cout hCoutpos kappa hkappa _e0 _k0 b0 hb0 M s hs L m n hmL hnm x z hz hgeom hfr hs1
    omega hcapE hcacc herrD hbrk hmem u hdat g hsol hgL2 hgW v w hharm hval hgrad hsig
  have hkappadef :
    kappa = √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ) := rfl
  have he0def :
    _e0 = kappa * (CE * (1 / 2 : ℝ)) := rfl
  have hk0def :
    _k0 = (2 : ℝ) * (↑d : ℝ) * (_e0 ^ (2 : ℕ) + (1 : ℝ)) := rfl
  have hb0def :
    b0 = √_k0 * _e0 + (2 : ℝ) * _k0 := rfl
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
  have hxf := eLpNorm_sub_weaklyHarmonic_le_coarseGraining_rebased_addThree (z := z) M L omega
    hs hs1 hsubx u hdat g hsol hgL2 hgW v w hharm hval hgrad
    (Annealed.sigmaBar M (n + 3)).2
  -- the energy leg
  have hR3 := h1EnergyNormOnCube_parentRebasedFamily_addThree_eq_sqrt_localizedCoeffEnergyValue
    (n := n) (m := m) M L x z omega u hsubx hsubz
  set Erep : ℝ := Support.fluxCorrectedErrorRepresentative M L (n + 3)
    ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) with hErepdef
  have hErepCap : Erep ≤ CE * (1 / 2) := hcapE hmem L (le_trans hnm hmL)
  have hErep0 : 0 ≤ Erep := Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  -- names for the atoms
  set Eb : ℝ := Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
    ((3 : ℝ) ^ (3 * (s / 8)) * Erep) with hEbdef
  set sig : ℝ := (Annealed.sigmaBar M (n + 3) : ℝ) with hsigdef
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
  set QS : ℝ := Real.rpow s (-(3 : ℝ)) with hQSdef
  set Q3s : ℝ := Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) with hQ3sdef
  set Q3sn : ℝ := Real.rpow (3 : ℝ) (s * (n : ℝ)) with hQ3sndef
  set Q1s : ℝ := Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) with hQ1sdef
  set R3n : ℝ := Real.rpow (3 : ℝ) ((n : ℝ)) with hR3ndef
  set S4 : ℝ := Real.rpow s (-(4 : ℝ)) with hS4def
  set S7 : ℝ := Real.rpow s (-(7 : ℝ)) with hS7def
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hY0 : 0 ≤ Y := ENNReal.toReal_nonneg
  have hYchild0 : 0 ≤ Ychild := ENNReal.toReal_nonneg
  have hP20 : 0 ≤ P2 := Real.rpow_nonneg (by norm_num) _
  have hQS0 : 0 ≤ QS := Real.rpow_nonneg hs.le _
  have hQ3s0 : 0 ≤ Q3s := Real.rpow_nonneg (by norm_num) _
  have hQ3sn0 : 0 ≤ Q3sn := Real.rpow_nonneg (by norm_num) _
  have hQ1s0 : 0 ≤ Q1s := Real.rpow_nonneg (by norm_num) _
  have hR3n0 : 0 ≤ R3n := Real.rpow_nonneg (by norm_num) _
  obtain ⟨hS40, hS70, hsiginv0, hbrkCap, hET, hGbes⟩ :=
    (show (0 ≤ S4) ∧ (0 ≤ S7) ∧ ((0 : ℝ) ≤ sig⁻¹) ∧ (coarseGrainingForceBracket (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) ≤ b0) ∧ (coarseGrainingEnergyTerm
        (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3)
      (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx)) ≤
      kappa * Real.sqrt Cout * Erep * (sig * (P2 * X) + QS * (Q3s * Y))) ∧
        (Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s
      (fun y => -g (y + x)) ≤ besovGagliardoConstant d * Q3sn * Ychild) from
      @reindexComposed_comparisonBounds1 (d) (by infer_instance) (CE) (Cout) (hCoutpos) (hkappa)
        (M) (s) (hs) (L) (m) (n) (x) (z) (hz) (hgeom) (hfr) (hs1) (omega) (u) (g) (hsubx) (hsubz)
        (hcaccW) (hgL2child) (hgWchild) (hR3) (hErepCap) (hErep0) (herrD) (hbrk) (hsig))
  have hGbes0 : 0 ≤ Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s
      (fun y => -g (y + x)) :=
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (forceBesovRegularity_translated_neg (originCube d n) hs hs1 hgL2child hgWchild)
  have hYchildle : Ychild ≤ gagliardoWindowConst d * Y :=
    normalizedGagliardoESeminormOn_child_toReal_le hgeom g hgWW
  have hFT : coarseGrainingForceTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) s (fun y => -g (y + x)) ≤
      b0 * (besovGagliardoConstant d * Q3sn * (gagliardoWindowConst d * Y)) := by
    rw [coarseGrainingForceTerm]
    refine mul_le_mul hbrkCap ?_ hGbes0 hb0
    refine hGbes.trans ?_
    exact mul_le_mul_of_nonneg_left hYchildle
      (mul_nonneg (besovGagliardoConstant_nonneg d) hQ3sn0)
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
  have hW1 : cubeBesovScaleWeight (1 : ℝ) (originCube d n) = Real.rpow (3 : ℝ) (-(n : ℝ)) := by
    have h := cubeBesovScaleWeight_neg_originCube (d := d) n (-1)
    rw [neg_neg] at h
    rw [h]
    congr 1
    ring
  exact ⟨hsubx, hErepCap, hErep0, hsig, hP2def, hQSdef, hQ3sdef, hQ3sndef, hQ1sdef, hR3ndef,
    hS4def, hS7def, hX0, hY0, hQS0, hQ3s0, hQ3sn0, hQ1s0, hR3n0, hS40, hS70, hsiginv0, hYchildle,
      hET, hFT, hxf, hW1⟩

/-- **The general clause at frontier-empty windows, in real form.**

`GeneralClauseInteriorComposed.exists_generalClauseInterior_honest` at the
frozen slot: the good event, the flux-corrected error index and the `σ`
index all read `n+3`, and the binder is the frozen binder `n + 3 ≤ m`.
Every `s`-power, every `3`-power and every window is the proved one. -/
theorem exists_generalClauseInterior_honest_addThree (d : ℕ) [NeZero d] :
    ∃ C Cfin : ℝ, 0 < C ∧ 0 < Cfin ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ x z : Vec d,
          z ∈ openCubeSet (originCube d m) →
            (fun y => x + y) '' openCubeSet (originCube d n) ⊆
                ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
                  openCubeSet (originCube d m) →
            ((fun y => z + y) '' openCubeSet (originCube d (n + 2))) ∩
                frontier (openCubeSet (originCube d m)) = ∅ →
              ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                    (Support.cgEllipLowerConstant d) (n + 3) z
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
                                Support.fluxCorrectedErrorRepresentative M L (n + 3)
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
                              Real.rpow s (-(7 : ℝ)) *
                                ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                (Support.normalizedGagliardoESeminormOn
                                  (((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 2))) ∩
                                    openCubeSet (originCube d m)) s g).toReal) := by
  classical
  obtain ⟨CE, hCEpos, hCE⟩ := ae_errorRepresentative_le_harmonicSlot_addThree d
  obtain ⟨CC, Cout, hCCpos, hCoutpos, hCC⟩ := ae_constantDatumEnergy_anchorWindow_addThree d
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
    ae_coarseGrainingErrorAtDepth_rebased_le_representative_addThree M L n z hs hs1,
    ae_forceBracket_rebased_le_addThree M L n z hs hs1] with omega hcapE hcacc herrD hbrk
  intro hmem u hdat g hsol hgL2 hgW v w hharm hval hgrad
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 3) : ℝ) := (Annealed.sigmaBar M (n + 3)).2
  obtain ⟨hsubx, hErepCap, hErep0, hsig, hP2def, hQSdef, hQ3sdef, hQ3sndef, hQ1sdef, hR3ndef,
    hS4def, hS7def, hX0, hY0, hQS0, hQ3s0, hQ3sn0, hQ1s0, hR3n0, hS40, hS70, hsiginv0, hYchildle,
      hET, hFT, hxf, hW1⟩ :=
    @reindexComposed_comparisonBounds3 (d) (by infer_instance) (CE) (Cout) (hCoutpos) (hkappa)
      (hb0) (M) (s) (hs) (L) (m) (n) (hmL) (hnm) (x) (z) (hz) (hgeom) (hfr) (hs1) (omega) (hcapE)
      (hcacc) (herrD) (hbrk) (hmem) (u) (hdat) (g) (hsol) (hgL2) (hgW) (v) (w) (hharm) (hval)
      (hgrad) (hsig)
  set Erep : ℝ := Support.fluxCorrectedErrorRepresentative M L (n + 3)
    ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) with hErepdef
  set Eb : ℝ := Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
    ((3 : ℝ) ^ (3 * (s / 8)) * Erep) with hEbdef
  set sig : ℝ := (Annealed.sigmaBar M (n + 3) : ℝ) with hsigdef
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
  set QS : ℝ := Real.rpow s (-(3 : ℝ)) with hQSdef
  set Q3s : ℝ := Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) with hQ3sdef
  set Q3sn : ℝ := Real.rpow (3 : ℝ) (s * (n : ℝ)) with hQ3sndef
  set Q1s : ℝ := Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) with hQ1sdef
  set R3n : ℝ := Real.rpow (3 : ℝ) ((n : ℝ)) with hR3ndef
  set S4 : ℝ := Real.rpow s (-(4 : ℝ)) with hS4def
  set S7 : ℝ := Real.rpow s (-(7 : ℝ)) with hS7def
  set ET : ℝ := coarseGrainingEnergyTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3)
      (H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n) hsubx))
    with hETdef
  set FT : ℝ := coarseGrainingForceTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) s (fun y => -g (y + x))
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
  clear_value Lhs X Y Ychild ET FT Erep Eb sig P2 QS Q3s Q3sn Q1s R3n S4 S7
  -- (g) the regrouping
  obtain ⟨hT1, hT2, hT3, hXterm, hYterm, hCE2⟩ :=
    (show ((sig⁻¹ * R3n) * (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
        (kappa * Real.sqrt Cout * Erep * (sig * (P2 * X) + QS * (Q3s * Y))))) ≤
      A1 * (S4 * Erep * X) + (9 * (CE * (1 / 2)) * A1) * (S7 * sig⁻¹ * Q1s * Y)) ∧ ((sig⁻¹ * R3n)
        * (cg * (1944 * (s⁻¹) ^ (6 : ℕ) *
        (b0 * (besovGagliardoConstant d * Q3sn * (gagliardoWindowConst d * Y))))) ≤
      A2 * (S7 * sig⁻¹ * Q1s * Y)) ∧ ((sig⁻¹ * R3n) * (interiorCorrectionConst d * Real.rpow s
        (-(1 / 2 : ℝ)) * Q3sn *
        (gagliardoWindowConst d * Y)) ≤ A3 * (S7 * sig⁻¹ * Q1s * Y)) ∧ ((0 : ℝ) ≤ S4 * Erep * X) ∧
          ((0 : ℝ) ≤ S7 * sig⁻¹ * Q1s * Y) ∧ ((0 : ℝ) ≤ 9 * (CE * (1 / 2)) * A1) from
      @reindexComposed_comparisonBounds2 (d) (by infer_instance) (CE) (hCEpos) (Cout) (hCoutpos)
        (hcg)  (hA1)  (hA2)  (hA3) (s) (hs) (n) (hs1) (Erep) (hErepCap)
          (hErep0) (sig) (X) (Y) (P2) (hP2def) (QS) (hQSdef) (Q3s) (hQ3sdef) (Q3sn) (hQ3sndef)
            (Q1s) (hQ1sdef) (R3n) (hR3ndef) (S4) (hS4def) (S7) (hS7def) (hX0) (hY0) (hQS0) (hQ3s0)
              (hQ1s0) (hR3n0) (hS40) (hS70) (hsiginv0) (hsinv))
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
  have hsum : A1 * (S4 * Erep * X) + (9 * (CE * (1 / 2)) * A1) * (S7 * sig⁻¹ * Q1s * Y) +
      A2 * (S7 * sig⁻¹ * Q1s * Y) + A3 * (S7 * sig⁻¹ * Q1s * Y) ≤
      (A1 + 9 * (CE * (1 / 2)) * A1 + A2 + A3 + 1) * (S4 * Erep * X + S7 * sig⁻¹ * Q1s * Y) := by
    have hC1 : A1 ≤ A1 + 9 * (CE * (1 / 2)) * A1 + A2 + A3 + 1 := by
      linarith only [hCE2, hA2, hA3]
    have hC2 : 9 * (CE * (1 / 2)) * A1 + A2 + A3 ≤
        A1 + 9 * (CE * (1 / 2)) * A1 + A2 + A3 + 1 := by linarith only [hA1]
    calc A1 * (S4 * Erep * X) + (9 * (CE * (1 / 2)) * A1) * (S7 * sig⁻¹ * Q1s * Y) +
          A2 * (S7 * sig⁻¹ * Q1s * Y) + A3 * (S7 * sig⁻¹ * Q1s * Y)
        = A1 * (S4 * Erep * X) +
            (9 * (CE * (1 / 2)) * A1 + A2 + A3) * (S7 * sig⁻¹ * Q1s * Y) := by ring
      _ ≤ (A1 + 9 * (CE * (1 / 2)) * A1 + A2 + A3 + 1) * (S4 * Erep * X) +
            (A1 + 9 * (CE * (1 / 2)) * A1 + A2 + A3 + 1) * (S7 * sig⁻¹ * Q1s * Y) :=
          add_le_add (mul_le_mul_of_nonneg_right hC1 hXterm)
            (mul_le_mul_of_nonneg_right hC2 hYterm)
      _ = (A1 + 9 * (CE * (1 / 2)) * A1 + A2 + A3 + 1) *
            (S4 * Erep * X + S7 * sig⁻¹ * Q1s * Y) := by ring
  linarith only [hT1, hT2, hT3, hsum]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
