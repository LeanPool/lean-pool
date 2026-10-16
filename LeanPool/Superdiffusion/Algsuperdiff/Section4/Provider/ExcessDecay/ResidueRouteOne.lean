/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueEnergyLeg
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueCapChild
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueFlushTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ReindexComposed
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RecutAtoms

/-!
# ResidueRouteOne

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Route 1, machine-assembled at the flush sub-cube `K'`

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## What is proved

derived, from the *shapes* of the proved theorems, that the `p = 2`
coarse-graining comparison read at the flush scale-`n` sub-cube `K' =
flushSubCentre z m n i σ + □_n` prices the harmonic-approximation residue `‖u −
w‖_{L²(K')}` on the five canonical legs, but could not assemble it, because
the proved caps carry the anchor's geometry binder and `K'` provably fails it.
This module *is* that assembly:

```text
  ‖u − w‖_{L²(K')} ≤ Cfin ·
      ( s^{-4}·𝓔·‖u − (u)_{W'}‖_{L²(W')}
      + s^{-7}·σ_{n+3}^{-1}·3^{(1+s)n}·[g]_{H^s(W')}
      + s^{-6}·3^{(1+s)n}·[∇h]_{H^s(W')}
      + s^{-6}·3^{n}·‖∇h‖_{L²(W')}
      + s^{-4}·𝓔·S )
```

with `𝓔 = fluxCorrectedErrorRepresentative M L (n+3) ⟨s/8⟩ (translate z ω)`
carried **explicitly** (not substituted by the frozen good event's `ε = 1/2`),
and `S` the boundary scalar at the flush cube `K = wellPlacedCentre z m (n+2) +
□_{n+2}` — which is the covering cube of `K'`
(`ResidueCapGeometry.wellPlacedCentre_flushSubCentre`).

* the deterministic `x`-frame envelope
  `ReindexEllipticity.eLpNorm_sub_weaklyHarmonic_le_coarseGraining_rebased_addThree`
  (binder-free: it needs only `translateSet x □_n ⊆ □_m`);
* the boundary energy leg at the two hinges (`ResidueEnergyLeg`);
* the child cube's `𝓔`-cap and forcing bracket at hinge (C)
  (`ResidueCapChild`);
* the **one-hop** Gagliardo transport `K' → W'` (`ResidueFlushTransport`) in
  place of the proved two-hop route through the `(n+2)` window, which `K'` does
  not meet.

## The `σ`-cancellation, machine-verified

The envelope is divided by `σ₀ = σ_{n+3}` and the energy term carries
`‖a₀‖^{1/2} = √σ_{n+3}` (`constantCoeffMatrixNormHalf_scalarComparator_sqrt`).
The two identities `√σ·√σ = σ` and `√σ·√(σ^{-1}) = 1` are consumed at `h1` and `h2`
below: they cancel `σ` exactly on the four `√σ` legs and leave exactly one
`σ^{-1}` on the force leg.  **No `ν` is divided anywhere**: CoarseGraining's
`h1EnergyNormOnCube` at the re-based family equals `√(ν·⨍|∇u|²)`, and that
quantity is consumed *whole* by the boundary energy leg — it is never converted
to a Euclidean gradient.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the boundary application;
  `e.homogenization.L2.interior`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

/-- Child-cube geometry and transport facts shared by the two boundary routes. -/
abbrev boundaryRouteGeometryComparison : Prop :=
    ∀ (d : ℕ) [NeZero d] (CE KE : ℝ),
      let kappa : ℝ := √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ);
      ∀ (_ : (0 : ℝ) ≤ kappa),
        let e0 : ℝ := kappa * (CE * (1 / 2 : ℝ));
          let k0 : ℝ := (2 : ℝ) * (↑d : ℝ) * (e0 ^ (2 : ℕ) + (1 : ℝ));
            let b0 : ℝ := √k0 * e0 + (2 : ℝ) * k0;
            ∀ (M : ABKModel d) (s : ℝ) (_ : (0 : ℝ) < s) (L m n
              : ℤ) (_ : m ≤ L)
              (_ : n + (3 : ℤ) ≤ m) (z : Vec d) (_ : z ∈ openCubeSet (originCube d m)) (i : Fin d)
                (sigma : ℝ)
              (_ : sigma = (1 : ℝ) ∨ sigma = (-1 : ℝ)) (_ : wellPlacedHalfGap m (n + (2 : ℤ)) <
                sigma * z i)
              (_ : s ≤ (1 : ℝ)) (_ : n + (2 : ℤ) ≤ m)
              (_ :
                translateSet (flushSubCentre z m n i sigma - z) (cubeSet (originCube d n)) ⊆
                  cubeSet (originCube d (n + (3 : ℤ))))
              (omega : Cutoff.CutoffSample d)
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
                                    ((fun (y : Vec d) =>
                                        wellPlacedCentre (flushSubCentre z m n i sigma) m (n + (2
                                          : ℤ)) + y) ''
                                      openCubeSet (originCube d (n + (2 : ℤ))))
                                    fun (y : Vec d) => u.toFun y - hdat.toFun y| ≤
                                S →
                              ∀
                                (hsubx :
                                  translateSet (flushSubCentre z m n i sigma) (openCubeSet
                                    (originCube d n)) ⊆
                                    openCubeSet (originCube d m)),
                                Ch03.h1EnergyNormOnCube (originCube d n)
                                    (parentRebasedFamily M L (n + (3 : ℤ)) (flushSubCentre z m n i
                                      sigma) z omega)
                                    (H1Function.untranslate (flushSubCentre z m n i sigma)
                                      (u.restrict (isOpen_translateSet_openCubeSet (flushSubCentre
                                        z m n i sigma) n)
                                        hsubx)) ≤
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
                ∀ (x : Vec d),
                  translateSet (x - z) (cubeSet (originCube d n)) ⊆ cubeSet (originCube d (n + (3
                    : ℤ))) →
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
                ∀ (x : Vec d),
                  translateSet (x - z) (cubeSet (originCube d n)) ⊆ cubeSet (originCube d (n + (3
                    : ℤ))) →
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
                      ((fun (y : Vec d) => wellPlacedCentre z m (n + (2 : ℤ)) + y) ''
                        openCubeSet (originCube d (n + (2 : ℤ))))
                      fun (y : Vec d) => u.toFun y - hdat.toFun y| ≤
                  S)
              (v : H1Function ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) ''
                openCubeSet (originCube d n)))
              (w : H10Function ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) ''
                openCubeSet (originCube d n)))
              (_ :
                IsWeaklyHarmonicOn ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) ''
                  openCubeSet (originCube d n))
                  v)
              (_ : ∀ (y : Vec d), v.toFun y = u.toFun y - w.toFun y)
              (_ : ∀ (y : Vec d), v.grad y = u.grad y - w.grad y),
              ∃ (hsubx :
                translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n)) ⊆
                  openCubeSet (originCube d m))
                (_ :
                fluxCorrectedErrorRepresentative M L (n + (3 : ℤ)) ⟨s / (8 : ℝ), (by positivity)⟩
                    (Cutoff.translateCutoffSample z omega) ≤
                  CE * (1 / 2 : ℝ))
                (_ :
                (0 : ℝ) ≤
                  fluxCorrectedErrorRepresentative M L (n + (3 : ℤ)) ⟨s / (8 : ℝ), (by positivity)⟩
                    (Cutoff.translateCutoffSample z omega))
                (_ : (0 : ℝ) < (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ)) (_ :
                (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) *
                    (cubeBesovScaleWeight (1 : ℝ) (originCube d n) *
                      (eLpNorm (fun (y : Vec d) => u.toFun y - v.toFun y) (2 : ENNReal)
                          (normalizedVolumeMeasureOn
                            ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) ''
                              openCubeSet (originCube d n)))).toReal) ≤
                  (3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d *
                      ((216 : ℝ) * s⁻¹ ^ (4 : ℕ) *
                          coarseGrainingEnergyTerm (originCube d n)
                            (parentRebasedFamily M L (n + (3 : ℤ)) (flushSubCentre z m n i sigma)
                              z omega)
                            (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s /
                              (3 : ℝ))
                            (H1Function.untranslate (flushSubCentre z m n i sigma)
                              (u.restrict (isOpen_translateSet_openCubeSet (flushSubCentre z m n i
                                sigma) n) hsubx)) +
                        (1944 : ℝ) * s⁻¹ ^ (6 : ℕ) *
                          coarseGrainingForceTerm (originCube d n)
                            (parentRebasedFamily M L (n + (3 : ℤ)) (flushSubCentre z m n i sigma)
                              z omega)
                            (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s /
                              (3 : ℝ)) s
                            fun (y : Vec d) => -g (y + flushSubCentre z m n i sigma)) +
                    interiorCorrectionConst d * s.rpow (-(1 / 2 : ℝ)) * Real.rpow (3 : ℝ) (s * (↑n
                      : ℝ)) *
                      (normalizedGagliardoESeminormOn
                          ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet
                            (originCube d n)) s
                          g).toReal)
                        (_ :
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
                coarseGrainingForceBracket (originCube d n)
                    (parentRebasedFamily M L (n + (3 : ℤ)) (flushSubCentre z m n i sigma) z omega)
                    (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s / (3 : ℝ)) ≤
                  b0)
                (_ :
                coarseGrainingEnergyTerm (originCube d n)
                    (parentRebasedFamily M L (n + (3 : ℤ)) (flushSubCentre z m n i sigma) z omega)
                    (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s / (3 : ℝ))
                    (H1Function.untranslate (flushSubCentre z m n i sigma)
                      (u.restrict (isOpen_translateSet_openCubeSet (flushSubCentre z m n i sigma)
                        n) hsubx)) ≤
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
                (Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s fun (y :
                  Vec d) =>
                    -g (y + flushSubCentre z m n i sigma)) ≤
                  besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * (↑n : ℝ)) *
                    (normalizedGagliardoESeminormOn
                        ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet
                          (originCube d n)) s g).toReal)
                (_ :
                (0 : ℝ) ≤
                  Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s fun (y :
                    Vec d) =>
                    -g (y + flushSubCentre z m n i sigma)),
                (normalizedGagliardoESeminormOn
                      ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet
                        (originCube d n)) s g).toReal ≤
                  flushWindowConst d *
                    (normalizedGagliardoESeminormOn
                        ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                          openCubeSet (originCube d m))
                        s g).toReal

/-- The energy comparison contract shared by the two boundary routes. -/
abbrev boundaryRouteEnergyComparison : Prop :=
    ∀ (d : ℕ) [NeZero d] (CE KE : ℝ),
      let kappa : ℝ := √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ);
      ∀ (_ : (0 : ℝ) ≤ kappa),
        let e0 : ℝ := kappa * (CE * (1 / 2 : ℝ));
          let k0 : ℝ := (2 : ℝ) * (↑d : ℝ) * (e0 ^ (2 : ℕ) + (1 : ℝ));
            let b0 : ℝ := √k0 * e0 + (2 : ℝ) * k0;
            ∀ (M : ABKModel d) (s : ℝ) (_ : (0 : ℝ) < s) (L m n
              : ℤ) (z : Vec d)
              (i : Fin d) (sigma : ℝ) (_ : s ≤ (1 : ℝ))
              (_ :
                translateSet (flushSubCentre z m n i sigma - z) (cubeSet (originCube d n)) ⊆
                  cubeSet (originCube d (n + (3 : ℤ))))
              (omega : Cutoff.CutoffSample d) (u hdat : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d)
              (S : ℝ)
              (hsubx :
                translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n)) ⊆
                  openCubeSet (originCube d m)),
              let Erep : ℝ :=
                fluxCorrectedErrorRepresentative M L (n + (3 : ℤ)) ⟨s / (8 : ℝ), (by positivity)⟩
                  (Cutoff.translateCutoffSample z omega);
              ∀ (_ : Erep ≤ CE * (1 / 2 : ℝ)) (_ : (0 : ℝ) ≤ Erep),
                let Eb : ℝ :=
                  √(offGridStabilityConst d (s / (6 : ℝ)) (s / (8 : ℝ))) * ((3 : ℝ) ^ ((3 : ℝ) *
                    (s / (8 : ℝ))) * Erep);
                ∀
                  (_ :
                    ∀ (x : Vec d),
                      translateSet (x - z) (cubeSet (originCube d n)) ⊆ cubeSet (originCube d (n +
                        (3 : ℤ))) →
                        Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
                            (parentRebasedFamily M L (n + (3 : ℤ)) x z omega)
                            (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s /
                              (3 : ℝ)) (0 : ℕ) ≤
                          Eb)
                  (_ :
                    ∀ (x : Vec d),
                      translateSet (x - z) (cubeSet (originCube d n)) ⊆ cubeSet (originCube d (n +
                        (3 : ℤ))) →
                        coarseGrainingForceBracket (originCube d n) (parentRebasedFamily M L (n +
                          (3 : ℤ)) x z omega)
                            (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s /
                              (3 : ℝ)) ≤
                          √((2 : ℝ) * (↑d : ℝ) * (Eb ^ (2 : ℕ) + (1 : ℝ))) * Eb +
                            (2 : ℝ) * ((2 : ℝ) * (↑d : ℝ) * (Eb ^ (2 : ℕ) + (1 : ℝ)))),
                  let sig : ℝ := (↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ);
                  ∀ (_ : (0 : ℝ) < sig),
                    let X : ℝ :=
                      (eLpNorm
                          (fun (y : Vec d) =>
                            u.toFun y -
                              volumeAverage
                                ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3
                                  : ℤ))) ∩
                                  openCubeSet (originCube d m))
                                u.toFun)
                          (2 : ENNReal)
                          (normalizedVolumeMeasureOn
                            ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                              ℤ))) ∩
                              openCubeSet (originCube d m)))).toReal;
                    let Gs : ℝ :=
                      (normalizedGagliardoESeminormOn
                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                            ℤ))) ∩
                            openCubeSet (originCube d m))
                          s g).toReal;
                    let Hs : ℝ :=
                      (normalizedGagliardoESeminormOn
                          ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                            ℤ))) ∩
                            openCubeSet (originCube d m))
                          s hdat.grad).toReal;
                    let Hn : ℝ :=
                      (eLpNorm hdat.grad (2 : ENNReal)
                          (normalizedVolumeMeasureOn
                            ((fun (y' : Vec d) => z + y') '' openCubeSet (originCube d (n + (3 :
                              ℤ))) ∩
                              openCubeSet (originCube d m)))).toReal;
                    let P2 : ℝ := Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ));
                    let Q3s : ℝ := Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ));
                    let Sm3 : ℝ := s.rpow (-3 : ℝ);
                    let Sm2 : ℝ := s.rpow (-2 : ℝ);
                    ∀
                      (_ :
                        Ch03.h1EnergyNormOnCube (originCube d n)
                            (parentRebasedFamily M L (n + (3 : ℤ)) (flushSubCentre z m n i sigma)
                              z omega)
                            (H1Function.untranslate (flushSubCentre z m n i sigma)
                              (u.restrict (isOpen_translateSet_openCubeSet (flushSubCentre z m n i
                                sigma) n) hsubx)) ≤
                          KE *
                            (√sig * P2 * X + √sig * P2 * S + Sm3 * √sig⁻¹ * Q3s * Gs + Sm2 * √sig
                              * Q3s * Hs +
                              Sm2 * √sig * Hn)),
                      (0 : ℝ) ≤ sig⁻¹ ∧
                        coarseGrainingForceBracket (originCube d n)
                              (parentRebasedFamily M L (n + (3 : ℤ)) (flushSubCentre z m n i
                                sigma) z omega)
                              (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s /
                                (3 : ℝ)) ≤
                            b0 ∧
                          coarseGrainingEnergyTerm (originCube d n)
                              (parentRebasedFamily M L (n + (3 : ℤ)) (flushSubCentre z m n i
                                sigma) z omega)
                              (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s /
                                (3 : ℝ))
                              (H1Function.untranslate (flushSubCentre z m n i sigma)
                                (u.restrict (isOpen_translateSet_openCubeSet (flushSubCentre z m n
                                  i sigma) n) hsubx)) ≤
                            kappa * KE * Erep *
                              (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) + Sm2 * (sig *
                                (Q3s * Hs)) +
                                Sm2 * (sig * Hn))

theorem residueRouteOne_comparisonBounds1 : boundaryRouteEnergyComparison :=
  by
  intro d _ CE KE kappa hkappa e0 k0 b0 M s hs L m n z i sigma hs1
    hChinge omega u _ _ S hsubx Erep hErepCap hErep0 Eb herrD hbrk sig hsig X Gs Hs Hn P2
      Q3s Sm3 Sm2 hEn
  have he0def : e0 = kappa * (CE * (1 / 2 : ℝ)) := rfl
  have hk0def : k0 = (2 : ℝ) * (↑d : ℝ) * (e0 ^ (2 : ℕ) + (1 : ℝ)) := rfl
  have hb0def : b0 = √k0 * e0 + (2 : ℝ) * k0 := rfl
  have hsiginv0 : (0 : ℝ) ≤ sig⁻¹ := inv_nonneg.mpr hsig.le
  have herror := offGridStabilityError_bound (d := d) hs hs1
    (by linarith only [hs1] : (3 : ℝ) * (s / 8) ≤ 1) hErep0
  have hEb0 : 0 ≤ Eb := herror.1
  have hEbkappa : Eb ≤ kappa * Erep := herror.2
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
  have hbrkCap : coarseGrainingForceBracket (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) ≤ b0 := by
    refine (hbrk (flushSubCentre z m n i sigma) hChinge).trans ?_
    rw [hb0def]
    have h1 : Real.sqrt (2 * (d : ℝ) * (Eb ^ 2 + 1)) * Eb ≤ Real.sqrt k0 * e0 :=
      mul_le_mul (Real.sqrt_le_sqrt hKble) hEbe0 hEb0 (Real.sqrt_nonneg _)
    have h2 : 2 * (2 * (d : ℝ) * (Eb ^ 2 + 1)) ≤ 2 * k0 := by linarith only [hKble]
    linarith only [h1, h2]
  -- (c) the energy term, with the boundary energy leg substituted
  have hEnergy0 : 0 ≤ Ch03.h1EnergyNormOnCube (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (H1Function.untranslate (flushSubCentre z m n i sigma)
        (u.restrict (isOpen_translateSet_openCubeSet
          (flushSubCentre z m n i sigma) n) hsubx)) :=
    h1EnergyNormOnCube_nonneg _ _ _
  have hET : coarseGrainingEnergyTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3)
      (H1Function.untranslate (flushSubCentre z m n i sigma)
        (u.restrict (isOpen_translateSet_openCubeSet
          (flushSubCentre z m n i sigma) n) hsubx)) ≤
      kappa * KE * Erep *
        (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
          Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn)) := by
    have hEcap : Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
        (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
        (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) 0 ≤ kappa * Erep :=
      (herrD (flushSubCentre z m n i sigma) hChinge).trans hEbkappa
    rw [coarseGrainingEnergyTerm, constantCoeffMatrixNormHalf_scalarComparator_sqrt]
    have hstep : Real.sqrt sig *
        Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
          (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
          (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) 0 *
        Ch03.h1EnergyNormOnCube (originCube d n)
          (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
          (H1Function.untranslate (flushSubCentre z m n i sigma)
            (u.restrict (isOpen_translateSet_openCubeSet
              (flushSubCentre z m n i sigma) n) hsubx)) ≤
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
  exact ⟨hsiginv0, hbrkCap, hET⟩

theorem residueRouteOne_comparisonBounds4 : boundaryRouteGeometryComparison :=
  by
  classical
  intro d _ CE KE kappa hkappa _ _ b0 M s hs L m n hmL hnm z hz i
    sigma hsigma hover hs1 hnm2 hChinge omega hcapE hEnLeg herrD hbrk hmem u hdat g S hsol hgL2
      hgW hhW hmean v w hharm hval hgrad
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 3) : ℝ) :=
    (Annealed.sigmaBar M (n + 3)).2
  have hsubx : translateSet (flushSubCentre z m n i sigma)
      (openCubeSet (originCube d n)) ⊆ openCubeSet (originCube d m) :=
    translateSet_flushSubCube_subset_openCubeSet hnm2 z i hsigma
  have hsubimg : (fun y => flushSubCentre z m n i sigma + y) ''
      openCubeSet (originCube d n) ⊆ openCubeSet (originCube d m) :=
    flushSubCube_subset_openCubeSet hnm2 z i hsigma
  have hW30 : volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m))) ≠ 0 :=
    volume_anchorWindow_ne_zero_of_flushSubCube hnm2 hz i hsigma
  have hgWW3 := memLp_normalizedGagliardoMeasureOn_subset
    (Set.inter_subset_right
      (s := (fun y' => z + y') '' openCubeSet (originCube d (n + 3))))
    (volume_openCubeSet_ne_zero (originCube d m))
    (volume_openCubeSet_ne_top (originCube d m)) hW30 hgW
  have hgL2child := memLp_two_child_of_clause_iv hsubimg hgL2
  have hgWchild := memLp_two_gagliardo_child_of_clause_iv hsubimg hgW
  -- the deterministic `x`-frame composition at `K'`
  have hxf := eLpNorm_sub_weaklyHarmonic_le_coarseGraining_rebased_addThree (z := z) M L omega
    hs hs1 hsubx u hdat g hsol hgL2 hgW v w hharm hval hgrad
    (Annealed.sigmaBar M (n + 3)).2
  -- the energy leg, at the covering cube of `K'`
  have hmeanFlush : |volumeAverage
      ((fun y => wellPlacedCentre (flushSubCentre z m n i sigma) m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)))
      (fun y => u.toFun y - hdat.toFun y)| ≤ S := by
    rw [wellPlacedCentre_flushSubCentre hnm2 hsigma hover]
    exact hmean
  have hEn := hEnLeg hmem u hdat g S hsol hgL2 hgW hhW hmeanFlush hsubx
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
  set Ychild : ℝ := (Support.normalizedGagliardoESeminormOn
      ((fun y => flushSubCentre z m n i sigma + y) ''
        openCubeSet (originCube d n)) s g).toReal with hYchilddef
  set Lhs : ℝ := (eLpNorm (fun y => u.toFun y - v.toFun y) 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => flushSubCentre z m n i sigma + y) ''
          openCubeSet (originCube d n)))).toReal with hLhsdef
  set P2 : ℝ := Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ))
  set Q3s : ℝ := Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ))
  set Q3sn : ℝ := Real.rpow (3 : ℝ) (s * (n : ℝ))
  set Q1s : ℝ := Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))
  set R3n : ℝ := Real.rpow (3 : ℝ) ((n : ℝ))
  set S4 : ℝ := Real.rpow s (-(4 : ℝ))
  set S7 : ℝ := Real.rpow s (-(7 : ℝ))
  set S6 : ℝ := Real.rpow s (-(6 : ℝ))
  set Sm3 : ℝ := Real.rpow s (-(3 : ℝ))
  set Sm2 : ℝ := Real.rpow s (-(2 : ℝ))
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hGs0 : 0 ≤ Gs := ENNReal.toReal_nonneg
  have hHs0 : 0 ≤ Hs := ENNReal.toReal_nonneg
  have hHn0 : 0 ≤ Hn := ENNReal.toReal_nonneg
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
  obtain ⟨hsiginv0, hbrkCap, hET⟩ :=
    (show ((0 : ℝ) ≤ sig⁻¹) ∧ (coarseGrainingForceBracket (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) ≤ b0) ∧ (coarseGrainingEnergyTerm
        (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3)
      (H1Function.untranslate (flushSubCentre z m n i sigma)
        (u.restrict (isOpen_translateSet_openCubeSet
          (flushSubCentre z m n i sigma) n) hsubx)) ≤
      kappa * KE * Erep *
        (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
          Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))) from
      @residueRouteOne_comparisonBounds1 (d) (by infer_instance) (CE) (KE) (hkappa)
        (M) (s) (hs) (L) (m) (n) (z) (i) (sigma) (hs1) (hChinge)
          (omega) (u) (hdat) (g) (S) (hsubx) (hErepCap) (hErep0) (herrD) (hbrk) (hsig)
            (hEn))
  -- (d) the forcing leg, through the one-hop window move
  have hGbes : Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s
      (fun y => -g (y + flushSubCentre z m n i sigma)) ≤
      besovGagliardoConstant d * Q3sn * Ychild := by
    have h := besovVectorSeminormTwo_translated_neg_le_gagliardo_window
      (originCube d n) hs hs1 hgL2child hgWchild
    rwa [cubeBesovScaleWeight_neg_originCube (d := d) n s] at h
  have hGbes0 : 0 ≤ Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo
      (originCube d n) s (fun y => -g (y + flushSubCentre z m n i sigma)) :=
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (forceBesovRegularity_translated_neg (originCube d n) hs hs1 hgL2child hgWchild)
  have hYchild3 : Ychild ≤ flushWindowConst d * Gs := by
    rw [hYchilddef, hGsdef]
    exact normalizedGagliardoESeminormOn_flushSubCube_toReal_le hnm2 hz i hsigma g hgWW3
  exact ⟨hsubx, hErepCap, hErep0, hsig, hxf, hX0, hGs0, hHs0, hHn0, hS0, hQ3s0, hQ3sn0,
    hQ1s0, hR3n0, hS40, hS70, hS60, hSm30, hSm20, hsiginv0, hbrkCap, hET, hGbes,
    hGbes0, hYchild3⟩

theorem residueRouteOne_comparisonBounds5 :
    ∀ (d : ℕ) [NeZero d] (CE KE : ℝ),
      let kappa : ℝ := √((192 : ℝ) * (↑d : ℝ)) * (3 : ℝ);
      let e0 : ℝ := kappa * (CE * (1 / 2 : ℝ));
      let k0 : ℝ := (2 : ℝ) * (↑d : ℝ) * (e0 ^ (2 : ℕ) + (1 : ℝ));
      let b0 : ℝ := √k0 * e0 + (2 : ℝ) * k0;
      let cg : ℝ := (3 : ℝ) * negNormBaseConst d * coarseGrainingP2Const d;
      ∀ (M : ABKModel d) (s : ℝ) (_ : (0 : ℝ) < s) (L m n : ℤ) (z : Vec d) (i : Fin d) (sigma : ℝ)
        (omega : Cutoff.CutoffSample d) (u hdat : H1Function (openCubeSet (originCube d m))) (g :
          Vec d → Vec d) (S : ℝ)
        (v : H1Function ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet
          (originCube d n)))
        (hsubx : translateSet (flushSubCentre z m n i sigma) (openCubeSet (originCube d n)) ⊆
          openCubeSet (originCube d m)),
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
            (normalizedGagliardoESeminormOn
                ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet (originCube
                  d n)) s g).toReal;
          ∀ (_ : Ychild ≤ flushWindowConst d * Gs),
            let Lhs : ℝ :=
              (eLpNorm (fun (y : Vec d) => u.toFun y - v.toFun y) (2 : ENNReal)
                  (normalizedVolumeMeasureOn
                    ((fun (y : Vec d) => flushSubCentre z m n i sigma + y) '' openCubeSet
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
                  coarseGrainingEnergyTerm (originCube d n)
                    (parentRebasedFamily M L (n + (3 : ℤ)) (flushSubCentre z m n i sigma) z omega)
                    (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s / (3 : ℝ))
                    (H1Function.untranslate (flushSubCentre z m n i sigma)
                      (u.restrict (isOpen_translateSet_openCubeSet (flushSubCentre z m n i sigma)
                        n) hsubx));
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
                    coarseGrainingForceTerm (originCube d n)
                      (parentRebasedFamily M L (n + (3 : ℤ)) (flushSubCentre z m n i sigma) z omega)
                      (scalarComparator (Annealed.sigmaBar M (n + (3 : ℤ))).property) (s / (3 :
                        ℝ)) s fun (y : Vec d) =>
                      -g (y + flushSubCentre z m n i sigma);
                  ∀ (_ : FT ≤ b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs)))
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
                                  (b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d *
                                    Gs))) ∧
                              interiorCorrectionConst d * s.rpow (-(1 / 2 : ℝ)) * Q3sn * Ychild ≤
                                interiorCorrectionConst d * s.rpow (-(1 / 2 : ℝ)) * Q3sn *
                                  (flushWindowConst d * Gs) := by
  classical
  intro d _ _ KE kappa _ _ b0 cg _ s hs _ _ n _ _ _ _ _ _ _ S _ _ Erep sig hsig hsiginv0 X Gs Hs
    Hn Ychild hYchild3 Lhs P2 Q3s Q3sn hQ3sn0 R3n hR3n0 Sm3 Sm2 ET hET FT hFT hxf
  have hxfr : sig * (Real.rpow (3 : ℝ) (-(n : ℝ)) * Lhs) ≤
      cg * (216 * (s⁻¹) ^ (4 : ℕ) * ET + 1944 * (s⁻¹) ^ (6 : ℕ) * FT) +
        interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn * Ychild := hxf
  have hfac0 : (0 : ℝ) ≤ sig⁻¹ * R3n := mul_nonneg hsiginv0 hR3n0
  have hsinv : sig⁻¹ * sig = 1 := inv_mul_cancel₀ hsig.ne'
  have hstep := scalar_frame_cancel_le hsig hR3n0 (rpow_three_neg_mul_self n) hxfr
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
        (b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs))) :=
    mul_le_mul_of_nonneg_left hFT
      (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr hs.le) 6))
  have hleg3 : interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn * Ychild ≤
      interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn *
        (flushWindowConst d * Gs) :=
    mul_le_mul_of_nonneg_left hYchild3 hccorr0
  exact ⟨hfac0, hsinv, hstep, hleg1, hleg2, hleg3⟩

theorem residueRouteOne_comparisonBounds6 :
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
                          (fun (y : Vec d) => wellPlacedCentre x m (n + (2 : ℤ)) + y) ''
                                openCubeSet (originCube d (n + (2 : ℤ))) ⊆
                              (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (3 :
                                ℤ))) ∩
                                openCubeSet (originCube d m) →
                            translateSet (wellPlacedCentre x m (n + (2 : ℤ)) - z) (cubeSet
                              (originCube d (n + (2 : ℤ)))) ⊆
                                cubeSet (originCube d (n + (3 : ℤ))) →
                              ∀ᵐ (omega :
                                Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                                  (Cutoff.CutoffSample d)),
                                omega ∈
                                    Frozen.Section4.goodEventAt M (cgEllipLowerConstant d) (n + (3
                                      : ℤ)) z
                                      ⟨s / (8 : ℝ),
                                        (by positivity)⟩
                                      (1 / 2 : ℝ) →
                                  ∀ (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec
                                    d → Vec d) (S : ℝ),
                                    IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L
                                      omega).toCoeffField
                                        (originCube d m) u hdat g →
                                      MemLp g (2 : ENNReal) (normalizedVolumeMeasureOn
                                        (openCubeSet (originCube d m))) →
                                        MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal) g) (2 :
                                          ENNReal)
                                            (normalizedGagliardoMeasureOn (openCubeSet (originCube
                                              d m))) →
                                          MemLp (Gagliardo.gagliardoKernel s (2 : ENNReal)
                                            hdat.grad) (2 : ENNReal)
                                              (normalizedGagliardoMeasureOn (openCubeSet
                                                (originCube d m))) →
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
                                                    (parentRebasedFamily M L (n + (3 : ℤ)) x z
                                                      omega)
                                                    (H1Function.untranslate x
                                                      (u.restrict (isOpen_translateSet_openCubeSet
                                                        x n) hsubx)) ≤
                                                  KE *
                                                    (√(↑(Annealed.sigmaBar M (n + (3 : ℤ))) : ℝ) *
                                                                Real.rpow (3 : ℝ) (-(↑(n + (2 :
                                                                  ℤ)) : ℝ)) *
                                                              (eLpNorm
                                                                  (fun (y : Vec d) =>
                                                                    u.toFun y -
                                                                      volumeAverage
                                                                        ((fun (y' : Vec d) => z +
                                                                          y') ''
                                                                            openCubeSet
                                                                              (originCube d (n +
                                                                                (3 : ℤ))) ∩
                                                                          openCubeSet (originCube
                                                                            d m))
                                                                        u.toFun)
                                                                  (2 : ENNReal)
                                                                  (normalizedVolumeMeasureOn
                                                                    ((fun (y' : Vec d) => z + y') ''
                                                                        openCubeSet (originCube d
                                                                          (n + (3 : ℤ))) ∩
                                                                      openCubeSet (originCube d
                                                                        m)))).toReal +
                                                            √(↑(Annealed.sigmaBar M (n + (3 : ℤ)))
                                                              : ℝ) *
                                                                Real.rpow (3 : ℝ) (-(↑(n + (2 :
                                                                  ℤ)) : ℝ)) *
                                                              S +
                                                          s.rpow (-3 : ℝ) * √(↑(Annealed.sigmaBar
                                                            M (n + (3 : ℤ))) : ℝ)⁻¹ *
                                                              Real.rpow (3 : ℝ) (s * (↑(n + (2 :
                                                                ℤ)) : ℝ)) *
                                                            (normalizedGagliardoESeminormOn
                                                                ((fun (y' : Vec d) => z + y') ''
                                                                    openCubeSet (originCube d (n +
                                                                      (3 : ℤ))) ∩
                                                                  openCubeSet (originCube d m))
                                                                s g).toReal +
                                                        s.rpow (-2 : ℝ) * √(↑(Annealed.sigmaBar M
                                                          (n + (3 : ℤ))) : ℝ) *
                                                            Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ))
                                                              : ℝ)) *
                                                          (normalizedGagliardoESeminormOn
                                                              ((fun (y' : Vec d) => z + y') ''
                                                                  openCubeSet (originCube d (n +
                                                                    (3 : ℤ))) ∩
                                                                openCubeSet (originCube d m))
                                                              s hdat.grad).toReal +
                                                      s.rpow (-2 : ℝ) * √(↑(Annealed.sigmaBar M (n
                                                        + (3 : ℤ))) : ℝ) *
                                                        (eLpNorm hdat.grad (2 : ENNReal)
                                                            (normalizedVolumeMeasureOn
                                                              ((fun (y' : Vec d) => z + y') ''
                                                                  openCubeSet (originCube d (n +
                                                                    (3 : ℤ))) ∩
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
              (besovGagliardoConstant d * flushWindowConst d)))
         (_ :
        (0 : ℝ) ≤ interiorCorrectionConst d * flushWindowConst d) (_ :
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
    ae_h1EnergyNormOnCube_boundary_le_anchorLegs_atHinges d
  obtain ⟨hkappa, hb0, hcg, hA1, hA2, hA3, hCE2, hCE3⟩ :=
    comparison_constants_nonneg d CE KE
      (flushWindowConst d) hCEpos.le hKEpos.le
      (flushWindowConst_pos d).le
  exact ⟨CE, hCEpos, hCE, CB, KE, hCBpos, hEnergyLeg, hkappa, hb0, hcg, hA1, hA2, hA3,
    hCE2, hCE3⟩

/-- **Route 1, composed at the flush sub-cube.**

The harmonic-approximation residue at `K'`, priced on the five canonical legs
with the good-event error `𝓔` carried explicitly. -/
private theorem residueRouteOneErrorWeighted_comparisonBounds7 :
    ∀ (d : ℕ) (CE : ℝ) (_ : (0 : ℝ) < CE) (CB : ℝ) (_ : (0 : ℝ) < CB) (M : ABKModel d) (s : ℝ)
      (_ : s ∈ Set.Icc ((64 : ℝ) * M.gamma) (1 : ℝ)) (_ : M.gamma ≤ (max CE CB)⁻¹ * Disorder.cstar
        M ^ (10 : ℕ))
      (_ m n : ℤ) (_ : n + (3 : ℤ) ≤ m) (z : Vec d) (_ : z ∈ openCubeSet (originCube d m)) (i :
        Fin d) (sigma : ℝ)
      (_ : sigma = (1 : ℝ) ∨ sigma = (-1 : ℝ)),
      s ≤ (1 : ℝ) ∧
        n + (2 : ℤ) ≤ m ∧
          M.gamma ≤ CE⁻¹ * Disorder.cstar M ^ (10 : ℕ) ∧
            M.gamma ≤ CB⁻¹ * Disorder.cstar M ^ (10 : ℕ) ∧
              flushSubCentre z m n i sigma ∈ openCubeSet (originCube d m) ∧
                (fun (y : Vec d) => wellPlacedCentre (flushSubCentre z m n i sigma) m (n + (2 :
                  ℤ)) + y) ''
                      openCubeSet (originCube d (n + (2 : ℤ))) ⊆
                    (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                      openCubeSet (originCube d m) ∧
                  translateSet (wellPlacedCentre (flushSubCentre z m n i sigma) m (n + (2 : ℤ)) - z)
                        (cubeSet (originCube d (n + (2 : ℤ)))) ⊆
                      cubeSet (originCube d (n + (3 : ℤ))) ∧
                    translateSet (flushSubCentre z m n i sigma - z) (cubeSet (originCube d n)) ⊆
                      cubeSet (originCube d (n + (3 : ℤ))) := by
  classical
  intro d CE hCEpos CB hCBpos M s hsrange hregime _ m n _ z hz i sigma hsigma
  have hs1 : s ≤ 1 := hsrange.2
  have hnm2 : n + 2 ≤ m := by omega
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
  have hxc : flushSubCentre z m n i sigma ∈ openCubeSet (originCube d m) :=
    flushSubCentre_mem_openCubeSet hnm2 z i hsigma
  have hcov : (fun y => wellPlacedCentre (flushSubCentre z m n i sigma) m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)) :=
    image_add_flushCoveringCube_subset_anchorWindow hnm2 hz i hsigma
  have hPhinge : translateSet
      (wellPlacedCentre (flushSubCentre z m n i sigma) m (n + 2) - z)
      (cubeSet (originCube d (n + 2))) ⊆ cubeSet (originCube d (n + 3)) :=
    translateSet_cubeSet_flushCoveringCube_subset_anchorParent hnm2 hz i hsigma
  have hChinge : translateSet (flushSubCentre z m n i sigma - z)
      (cubeSet (originCube d n)) ⊆ cubeSet (originCube d (n + 3)) :=
    translateSet_cubeSet_flushSubCube_subset_anchorParent hnm2 hz i hsigma
  exact ⟨hs1, hnm2, hregimeCE, hregimeCB, hxc, hcov, hPhinge, hChinge⟩

/-- **Route 1, composed at the flush sub-cube — the error-weighted legs.**

The harmonic-approximation residue at `K'`, priced on the five canonical legs
with the good-event error `𝓔` carried explicitly.  As in `AssemblyComposedErrorWeighted`,
the monotone discard is declined on the flat `∇h` row, so that leg reads
`s^{-6}·𝓔·3^n·‖∇h‖_{L²(W')}`. -/
theorem exists_flushResidue_route1_composed_errorWeighted (d : ℕ) [NeZero d] :
    ∃ C Cfin : ℝ, 0 < C ∧ 0 < Cfin ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ z : Vec d,
          z ∈ openCubeSet (originCube d m) →
          ∀ (i : Fin d) (σ : ℝ), (σ = 1 ∨ σ = -1) →
            wellPlacedHalfGap m (n + 2) < σ * z i →
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
                  |volumeAverage ((fun y => wellPlacedCentre z m (n + 2) + y) ''
                      openCubeSet (originCube d (n + 2)))
                      (fun y => u.toFun y - hdat.toFun y)| ≤ S →
                  ∀ (v : H1Function ((fun y => flushSubCentre z m n i σ + y) ''
                      openCubeSet (originCube d n)))
                    (w : H10Function ((fun y => flushSubCentre z m n i σ + y) ''
                      openCubeSet (originCube d n))),
                    Support.IsWeaklyHarmonicOn
                        ((fun y => flushSubCentre z m n i σ + y) ''
                          openCubeSet (originCube d n)) v →
                    (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                    (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                      (eLpNorm (fun y => u.toFun y - v.toFun y) 2
                        (Support.normalizedVolumeMeasureOn
                          ((fun y => flushSubCentre z m n i σ + y) ''
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
  obtain ⟨CE, hCEpos, hCE, CB, KE, hCBpos, hEnergyLeg, hkappa, hb0, hcg, hA1, hA2, hA3, hCE2,
    hCE3⟩ :=
    @residueRouteOne_comparisonBounds6 (d) (by infer_instance)
  set kappa : ℝ := Real.sqrt (192 * (d : ℝ)) * 3 with hkappadef
  set e0 : ℝ := kappa * (CE * (1 / 2)) with he0def
  set k0 : ℝ := 2 * (d : ℝ) * (e0 ^ 2 + 1) with hk0def
  set b0 : ℝ := Real.sqrt k0 * e0 + 2 * k0 with hb0def
  set cg : ℝ := 3 * negNormBaseConst d * coarseGrainingP2Const d with hcgdef
  set A1 : ℝ := cg * 216 * (kappa * KE) with hA1def
  set A2 : ℝ := cg * 1944 * (b0 * (besovGagliardoConstant d * flushWindowConst d))
    with hA2def
  set A3 : ℝ := interiorCorrectionConst d * flushWindowConst d with hA3def
  refine ⟨max CE CB,
    A1 + 9 * (CE * (1 / 2)) * A1 + CE * (1 / 2) * A1 + A2 + A3 + 1,
    lt_of_lt_of_le hCEpos (le_max_left _ _),
    add_pos_of_nonneg_of_pos
      (add_nonneg (add_nonneg (add_nonneg (add_nonneg hA1 hCE2) hCE3) hA2) hA3)
      zero_lt_one, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm z hz i sigma hsigma hover
  obtain ⟨hs1, hnm2, hregimeCE, hregimeCB, hxc, hcov, hPhinge, hChinge⟩ :=
    (show (s ≤ 1) ∧ (n + 2 ≤ m) ∧ (M.gamma ≤ CE⁻¹ * Disorder.cstar M ^ (10 : ℕ)) ∧ (M.gamma ≤ CB⁻¹
      * Disorder.cstar M ^ (10 : ℕ)) ∧ (flushSubCentre z m n i sigma ∈ openCubeSet (originCube d
        m)) ∧ ((fun y => wellPlacedCentre (flushSubCentre z m n i sigma) m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) ∧ (translateSet
      (wellPlacedCentre (flushSubCentre z m n i sigma) m (n + 2) - z)
      (cubeSet (originCube d (n + 2))) ⊆ cubeSet (originCube d (n + 3))) ∧ (translateSet
        (flushSubCentre z m n i sigma - z)
      (cubeSet (originCube d n)) ⊆ cubeSet (originCube d (n + 3))) from
      @residueRouteOneErrorWeighted_comparisonBounds7 (d) (CE) (hCEpos) (CB) (hCBpos) (M) (s)
        (hsrange) (hregime) (L) (m) (n) (hnm) (z) (hz) (i) (sigma) (hsigma))
  filter_upwards [hCE M s hsrange hregimeCE hsmall hs n z,
    hEnergyLeg M s hsrange hregimeCB hsmall hs L m n hmL hnm
      (flushSubCentre z m n i sigma) z hxc hcov hPhinge,
    ae_coarseGrainingErrorAtDepth_rebased_le_representative_gapThree M L n z hs hs1,
    ae_forceBracket_rebased_le_gapThree M L n z hs hs1] with omega hcapE hEnLeg herrD hbrk
  intro hmem u hdat g S hsol hgL2 hgW hhW hmean v w hharm hval hgrad
  obtain ⟨hsubx, hErepCap, hErep0, hsig, hxf, hX0, hGs0, hHs0, hHn0, hS0, hQ3s0, hQ3sn0,
    hQ1s0, hR3n0, hS40, hS70, hS60, hSm30, hSm20, hsiginv0, hbrkCap, hET, hGbes,
    hGbes0, hYchild3⟩ :=
    @residueRouteOne_comparisonBounds4 (d) (by infer_instance) (CE) (KE) (hkappa)
      (M) (s) (hs) (L) (m) (n) (hmL) (hnm) (z) (hz) (i)
        (sigma) (hsigma) (hover) (hs1) (hnm2) (hChinge) (omega) (hcapE) (hEnLeg) (herrD) (hbrk)
          (hmem) (u) (hdat) (g) (S) (hsol) (hgL2) (hgW) (hhW) (hmean) (v) (w) (hharm) (hval) (hgrad)
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
  set Ychild : ℝ := (Support.normalizedGagliardoESeminormOn
      ((fun y => flushSubCentre z m n i sigma + y) ''
        openCubeSet (originCube d n)) s g).toReal with hYchilddef
  set Lhs : ℝ := (eLpNorm (fun y => u.toFun y - v.toFun y) 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => flushSubCentre z m n i sigma + y) ''
          openCubeSet (originCube d n)))).toReal with hLhsdef
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
  have hFT : coarseGrainingForceTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) s
      (fun y => -g (y + flushSubCentre z m n i sigma)) ≤
      b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs)) := by
    rw [coarseGrainingForceTerm]
    refine mul_le_mul hbrkCap ?_ hGbes0 hb0
    refine hGbes.trans ?_
    exact mul_le_mul_of_nonneg_left hYchild3
      (mul_nonneg (besovGagliardoConstant_nonneg d) hQ3sn0)
  -- (e) the frame division
  set ET : ℝ := coarseGrainingEnergyTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3)
      (H1Function.untranslate (flushSubCentre z m n i sigma)
        (u.restrict (isOpen_translateSet_openCubeSet
          (flushSubCentre z m n i sigma) n) hsubx))
    with hETdef
  set FT : ℝ := coarseGrainingForceTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) s
      (fun y => -g (y + flushSubCentre z m n i sigma))
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
        (b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs)))) ∧
          (interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn * Ychild ≤
      interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn *
        (flushWindowConst d * Gs)) from
      @residueRouteOne_comparisonBounds5 (d) (by infer_instance) (CE) (KE) (M) (s)
        (hs) (L) (m) (n) (z) (i) (sigma) (omega) (u) (hdat) (g) (S) (v) (hsubx) (hsig) (hsiginv0)
          (hYchild3) (hQ3sn0) (hR3n0) (hET) (hFT) (hxf))
  have hmono := add_le_add (mul_le_mul_of_nonneg_left (add_le_add hleg1 hleg2) hcg) hleg3
  clear_value Lhs X Gs Hs Hn Ychild ET FT Erep Eb sig P2 Q3s Q3sn Q1s R3n S4 S7 S6
    Sm3 Sm2 A3 A2 A1 cg b0 k0 e0 kappa
  -- (g) the regrouping
  obtain ⟨hT1, hT2, hT3, hXterm, hSterm, hGterm, hHsterm, hHnterm⟩ :=
    @boundary_composed_comparison_bounds_errorWeighted
      (besovGagliardoConstant d) (interiorCorrectionConst d) (flushWindowConst d)
      (CE) (KE) (kappa) (b0)
      (cg) (A1) (hA1) (hA1def) (A2) (hA2) (hA2def) (A3) (hA3) (hA3def) (s) (hs) (n) (hs1) (S)
        (hS0) (Erep) (hErepCap) (hErep0) (sig)
          (hsiginv0) (X) (hX0) (Gs) (hGs0) (Hs) (hHs0) (Hn) (hHn0) (P2) (hP2def)
            (Q3s) (hQ3s0) (hQ3sdef) (Q3sn) (hQ3sndef) (Q1s) (hQ1s0) (hQ1sdef) (R3n) (hR3n0)
              (hR3ndef) (S4) (hS40) (hS4def) (S7) (hS70) (hS7def) (S6) (hS60) (hS6def) (Sm3)
                (hSm30) (hSm3def) (Sm2) (hSm20) (hSm2def) (hsinv)
  refine hstep.trans (le_trans (mul_le_mul_of_nonneg_left hmono hfac0) ?_)
  exact boundary_composed_absorption_errorWeighted
    hA1 hA2 hA3 hCE2 hCE3 hXterm hGterm hHsterm hHnterm hSterm hT1 hT2 hT3


theorem exists_flushResidue_route1_composed (d : ℕ) [NeZero d] :
    ∃ C Cfin : ℝ, 0 < C ∧ 0 < Cfin ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ z : Vec d,
          z ∈ openCubeSet (originCube d m) →
          ∀ (i : Fin d) (σ : ℝ), (σ = 1 ∨ σ = -1) →
            wellPlacedHalfGap m (n + 2) < σ * z i →
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
                  |volumeAverage ((fun y => wellPlacedCentre z m (n + 2) + y) ''
                      openCubeSet (originCube d (n + 2)))
                      (fun y => u.toFun y - hdat.toFun y)| ≤ S →
                  ∀ (v : H1Function ((fun y => flushSubCentre z m n i σ + y) ''
                      openCubeSet (originCube d n)))
                    (w : H10Function ((fun y => flushSubCentre z m n i σ + y) ''
                      openCubeSet (originCube d n))),
                    Support.IsWeaklyHarmonicOn
                        ((fun y => flushSubCentre z m n i σ + y) ''
                          openCubeSet (originCube d n)) v →
                    (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                    (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                      (eLpNorm (fun y => u.toFun y - v.toFun y) 2
                        (Support.normalizedVolumeMeasureOn
                          ((fun y => flushSubCentre z m n i σ + y) ''
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
    exists_flushResidue_route1_composed_errorWeighted d
  obtain ⟨CE, hCE, hcap, _⟩ := residueRouteOne_comparisonBounds6 d
  refine ⟨max Cweighted CE, K * max 1 (CE * (1 / 2 : ℝ)),
    lt_of_lt_of_le hCweighted (le_max_left _ _),
    mul_pos hK (lt_of_lt_of_le zero_lt_one (le_max_left _ _)), ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm z hz i sigma hsigma hover
  have hregimeWeighted : M.gamma ≤ Cweighted⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    hregime.trans (mul_le_mul_of_nonneg_right
      (inv_anti₀ hCweighted (le_max_left _ _)) (by positivity))
  have hregimeCap : M.gamma ≤ CE⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    hregime.trans (mul_le_mul_of_nonneg_right
      (inv_anti₀ hCE (le_max_right _ _)) (by positivity))
  filter_upwards [hweighted M s hsrange hregimeWeighted hsmall hs L m n hmL hnm z hz i sigma
      hsigma hover,
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
        ((fun y => flushSubCentre z m n i sigma + y) '' openCubeSet (originCube d n)))).toReal ≤
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
