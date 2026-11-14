/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ProviderBoundary
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RebaseSealDistance

/-!
# ProviderEpsFree

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `ε`-free provider, **unconditional**

## What is proved

One public theorem, `harmonic_approximation_provider_epsFree`, whose statement is
the frozen block verbatim (up to the single
`(fun omega' =>` ↦ `(fun _omega' =>` rename that the zero-warning gate forces,
the same rename the proved siblings carry), and whose proof has
**no hypothesis**: no `hres`, no `hepsPin`, no `hmean`, no `hgen`, no `hbdry`.

## The composition, slot by slot

```text
  RebaseGeneralClauseRegated.exists_generalClauseReal_frontierEmpty_regated   (the interior/
                                                                      general side)
        │
        ├─ RebaseJoinRegated  ──────────────────────────── the two clauses, one constant
        │
  ProviderBoundary.exists_boundaryClauseReal   (the boundary side)
        │      ├─ AssemblyBoundaryClause.hbdryOfScalarCoarse
        │      ├─ StitchDisplayLegs.exists_scalarLeg_le_displayLegs_of_epsPin
        │      │       └─ ResiduePlugin.exists_flushResidue_le_displayLegs_of_epsPin
        │      │       └─ ResidueBudget.exists_scalarControl_of_boundaryBranch_…
        │      ├─ GoodEventCaps.ae_errorRepresentative_le_of_mem_goodEventAt  (the pin)
        │      ├─ ReindexSlot.exists_inv_sigmaBar_add_three_le      (σ_{n+3} → σ_n)
        │      └─ MeanControlWindowCube.overhang_of_boundaryBranch  (the gate)
        │
  RebaseSealDistance.exists_harmonicApproximation_provider_of_boundaryClauseReal
        │
        ▼
  the frozen block
```

`C` is chosen **last**, after every `d`-only constant of the chain, so the
closing fit is sound.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the frozen block of
  `Algsuperdiff/Section4/Provider/ExcessDecay/ProviderEpsFree.lean` (read for
  the byte-verification, never imported).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

/-- **`l.harmonic.approximation.good.scales`, the provider —
unconditional.**

The frozen block, proved from the proved chain with no caller obligation.
The boundary instance of the general clause is
`ProviderBoundary.exists_boundaryClauseReal`; the frontier-empty
instance, the `ℝ≥0∞` shell, the interior clause and the outer join are
`RebaseSealDistance`'s. -/
theorem harmonic_approximation_provider_epsFree (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (C⁻¹ * s ^ (4 : ℕ)) →
        ∀ hs : 0 < s,
        ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m →
          ∀ x z : HCPolySupport.Vec d,
            x ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m) →
            z ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m) →
            (fun y => x + y) '' HCPolySupport.openCubeSet (HCPolySupport.originCube d n) ⊆
              ((fun y => z + y) ''
                  HCPolySupport.openCubeSet (HCPolySupport.originCube d (n + 1))) ∩
                HCPolySupport.openCubeSet (HCPolySupport.originCube d m) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ (u h : HCPolySupport.H1Function
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)))
                (g : HCPolySupport.Vec d → HCPolySupport.Vec d),
                Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                    (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                    (HCPolySupport.originCube d m) u h g →
                MeasureTheory.MemLp g 2
                    (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) →
                MeasureTheory.MemLp (HCPolySupport.Gagliardo.gagliardoKernel s 2 g) 2
                    (Algsuperdiff.Section4.Support.normalizedGagliardoMeasureOn
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) →
                MeasureTheory.MemLp (HCPolySupport.Gagliardo.gagliardoKernel s 2 h.grad) 2
                    (Algsuperdiff.Section4.Support.normalizedGagliardoMeasureOn
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) →
                ∀ (v : HCPolySupport.H1Function
                      ((fun y => x + y) ''
                        HCPolySupport.openCubeSet (HCPolySupport.originCube d n)))
                  (w : HCPolySupport.H10Function
                      ((fun y => x + y) ''
                        HCPolySupport.openCubeSet (HCPolySupport.originCube d n))),
                  Algsuperdiff.Section4.Support.IsWeaklyHarmonicOn
                      ((fun y => x + y) ''
                        HCPolySupport.openCubeSet (HCPolySupport.originCube d n)) v →
                  (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                  (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                  (Set.indicator
                        (Algsuperdiff.Frozen.Section4.goodEventAt M
                          (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) (n + 3) z
                          ⟨s / 8, by linarith only [hs]⟩ (C⁻¹ * s ^ (4 : ℕ)))
                        (fun _omega' =>
                          MeasureTheory.eLpNorm (fun y => u.toFun y - v.toFun y) 2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              ((fun y => x + y) ''
                                HCPolySupport.openCubeSet (HCPolySupport.originCube d n))))
                        omega ≤
                      ENNReal.ofReal
                          (C * Real.rpow s (-(4 : ℝ)) *
                            Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative M L
                              (n + 3) ⟨s / 8, by linarith only [hs]⟩
                              (Cutoff.translateCutoffSample z omega)) *
                        (MeasureTheory.eLpNorm
                            (fun y =>
                              u.toFun y -
                                HCPolySupport.volumeAverage
                                  (((fun y' => z + y') ''
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d (n + 3))) ∩
                                    HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                                  u.toFun)
                            2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              (((fun y' => z + y') ''
                                  HCPolySupport.openCubeSet
                                    (HCPolySupport.originCube d (n + 3))) ∩
                                HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) +
                          ENNReal.ofReal
                            (Real.rpow s (-(3 / 2 : ℝ)) *
                              Real.rpow (3 : ℝ) (n : ℝ) *
                              ‖HCPolySupport.volumeAverageVec
                                  (((fun y' => z + y') ''
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d (n + 2))) ∩
                                    HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                                  h.grad‖)) +
                        ENNReal.ofReal
                            (C * Real.rpow s (-(7 : ℝ)) *
                              (Annealed.sigmaBar M n : ℝ)⁻¹ *
                              Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))) *
                          Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                            (((fun y' => z + y') ''
                                HCPolySupport.openCubeSet
                                  (HCPolySupport.originCube d (n + 3))) ∩
                              HCPolySupport.openCubeSet (HCPolySupport.originCube d m)) s g +
                        ENNReal.ofReal
                            (C * Real.rpow s (-(6 : ℝ)) *
                              Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))) *
                          Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                            (((fun y' => z + y') ''
                                HCPolySupport.openCubeSet
                                  (HCPolySupport.originCube d (n + 3))) ∩
                              HCPolySupport.openCubeSet (HCPolySupport.originCube d m)) s
                            h.grad +
                        ENNReal.ofReal
                            (C * Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ)) *
                          MeasureTheory.eLpNorm h.grad 2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              (((fun y' => z + y') ''
                                  HCPolySupport.openCubeSet
                                    (HCPolySupport.originCube d (n + 3))) ∩
                                HCPolySupport.openCubeSet (HCPolySupport.originCube d m)))) ∧
                    ((((fun y' => z + y') ''
                            HCPolySupport.openCubeSet
                              (HCPolySupport.originCube d (n + 2))) ∩
                          frontier
                            (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)) =
                        ∅) →
                      Set.indicator
                          (Algsuperdiff.Frozen.Section4.goodEventAt M
                            (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) (n + 2) z
                            ⟨s / 8, by linarith only [hs]⟩ (1 / 2))
                          (fun _omega' =>
                            MeasureTheory.eLpNorm (fun y => u.toFun y - v.toFun y) 2
                              (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                ((fun y => x + y) ''
                                  HCPolySupport.openCubeSet (HCPolySupport.originCube d n))))
                          omega ≤
                        ENNReal.ofReal
                            (C * Real.rpow s (-(4 : ℝ)) *
                              Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative M L
                                (n + 2) ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega)) *
                          MeasureTheory.eLpNorm
                            (fun y =>
                              u.toFun y -
                                HCPolySupport.volumeAverage
                                  (((fun y' => z + y') ''
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d (n + 2))) ∩
                                    HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                                  u.toFun)
                            2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              (((fun y' => z + y') ''
                                  HCPolySupport.openCubeSet
                                    (HCPolySupport.originCube d (n + 2))) ∩
                                HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) +
                          ENNReal.ofReal
                              (C * Real.rpow s (-(19 / 2 : ℝ)) *
                                (Annealed.sigmaBar M n : ℝ)⁻¹ *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))) *
                            Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                              (((fun y' => z + y') ''
                                  HCPolySupport.openCubeSet
                                    (HCPolySupport.originCube d (n + 2))) ∩
                                HCPolySupport.openCubeSet (HCPolySupport.originCube d m)) s g) :=
  exists_harmonicApproximation_provider_of_boundaryClauseReal d
    (exists_boundaryClauseReal d)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
