/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RebaseJoinErrorWeighted
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RebaseGeneralClauseErrorWeighted

/-!
# RebaseSealDistanceErrorWeighted

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The error-weighted seal distance — the boundary instance, and nothing
# else

`RebaseJoinErrorWeighted` returns the frozen block from the whole general clause at
the re-gated funding line and the clause event; `RebaseGeneralClauseRegated` discharges
that clause **at frontier-empty windows** — the anchor's own interior gate.
Composing them, the remaining caller obligation is exactly the *boundary*
instance: the same real-valued statement with the gate **negated**,

```text
  (z + □_{n+2}) ∩ ∂□_m ≠ ∅ .
```

This module performs the composition and the two `ε` back-ports: the case split
is on the gate, which depends only on `d, z, n, m` — data bound before the
almost-sure quantifier — so it happens outside the `∀ᵐ` and no measurability
question arises.  The gate is still the `n+2` one: the two re-gated literals are
the funding line and the general clause's threshold, not the interior clause's
trigger.

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

/-- **The frozen block from the boundary instance alone.**

The hypothesis `hbdry` is the general clause in real form, restricted to
the *boundary* regime `(z+□_{n+2}) ∩ ∂□_m ≠ ∅`; the frontier-empty regime is
supplied by `exists_generalClauseReal_frontierEmpty_regated`, and the `ℝ≥0∞` shell,
the join and the interior clause by
`exists_harmonicApproximation_provider_of_generalClauseReal_regated`. -/
theorem exists_harmonicApproximation_provider_of_boundaryClauseReal_errorWeighted (d : ℕ)
    (hbdry : ∃ C : ℝ, 0 < C ∧
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
            (((fun y' => z + y') ''
                    HCPolySupport.openCubeSet (HCPolySupport.originCube d (n + 2))) ∩
                  frontier (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)) ≠
                ∅) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) (n + 3) z
                  ⟨s / 8, by linarith only [hs]⟩ (C⁻¹ * s ^ (4 : ℕ)) →
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
                      (MeasureTheory.eLpNorm (fun y => u.toFun y - v.toFun y) 2
                          (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                            ((fun y => x + y) ''
                              HCPolySupport.openCubeSet
                                (HCPolySupport.originCube d n)))).toReal ≤
                        C *
                          (Real.rpow s (-(4 : ℝ)) *
                                Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative
                                  M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
                                  (Cutoff.translateCutoffSample z omega) *
                                ((MeasureTheory.eLpNorm
                                    (fun y =>
                                      u.toFun y -
                                        HCPolySupport.volumeAverage
                                          (((fun y' => z + y') ''
                                              HCPolySupport.openCubeSet
                                                (HCPolySupport.originCube d (n + 3))) ∩
                                            HCPolySupport.openCubeSet
                                              (HCPolySupport.originCube d m))
                                          u.toFun)
                                    2
                                    (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                      (((fun y' => z + y') ''
                                          HCPolySupport.openCubeSet
                                            (HCPolySupport.originCube d (n + 3))) ∩
                                        HCPolySupport.openCubeSet
                                          (HCPolySupport.originCube d m)))).toReal +
                                  Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                                    ‖HCPolySupport.volumeAverageVec
                                        (((fun y' => z + y') ''
                                            HCPolySupport.openCubeSet
                                              (HCPolySupport.originCube d (n + 2))) ∩
                                          HCPolySupport.openCubeSet
                                            (HCPolySupport.originCube d m))
                                        h.grad‖) +
                            Real.rpow s (-(7 : ℝ)) * (Annealed.sigmaBar M n : ℝ)⁻¹ *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                (Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                                  (((fun y' => z + y') ''
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d (n + 3))) ∩
                                    HCPolySupport.openCubeSet
                                      (HCPolySupport.originCube d m)) s g).toReal +
                            Real.rpow s (-(6 : ℝ)) *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                (Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                                  (((fun y' => z + y') ''
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d (n + 3))) ∩
                                    HCPolySupport.openCubeSet
                                      (HCPolySupport.originCube d m)) s h.grad).toReal +
                            Real.rpow s (-(6 : ℝ)) *
                                Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative
                                  M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
                                  (Cutoff.translateCutoffSample z omega) *
                                Real.rpow (3 : ℝ) (n : ℝ) *
                                (MeasureTheory.eLpNorm h.grad 2
                                  (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                    (((fun y' => z + y') ''
                                        HCPolySupport.openCubeSet
                                          (HCPolySupport.originCube d (n + 3))) ∩
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d m)))).toReal)) :
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
                            (C * Real.rpow s (-(6 : ℝ)) *
                              Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative M L
                                (n + 3) ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega) *
                              Real.rpow (3 : ℝ) (n : ℝ)) *
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
                                HCPolySupport.openCubeSet (HCPolySupport.originCube d m)) s g)
    := by
  classical
  refine exists_harmonicApproximation_provider_of_generalClauseReal_errorWeighted d ?_
  obtain ⟨CB, hCB, hB⟩ := hbdry
  obtain ⟨CG, hCG, hG⟩ := exists_generalClauseReal_frontierEmpty_half_errorWeighted d
  have hleB : CB ≤ max (max CB CG) 2 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hleG : CG ≤ max (max CB CG) 2 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hle2 : (2 : ℝ) ≤ max (max CB CG) 2 := le_max_right _ _
  have hCpos : (0 : ℝ) < max (max CB CG) 2 := lt_of_lt_of_le (by norm_num) hle2
  refine ⟨max (max CB CG) 2, hCpos, ?_⟩
  intro M s hsrange hregime hfund hs L m n hmL hnm x z hx hz hgeom
  have hs1 : s ≤ 1 := hsrange.2
  have hep0 : (0 : ℝ) ≤ (max (max CB CG) 2)⁻¹ * s ^ (4 : ℕ) :=
    clauseEpsilon_nonneg hCpos hs.le
  have hepB : (max (max CB CG) 2)⁻¹ * s ^ (4 : ℕ) ≤ CB⁻¹ * s ^ (4 : ℕ) :=
    clauseEpsilon_anti hCB hleB hs.le
  have hepG : (max (max CB CG) 2)⁻¹ * s ^ (4 : ℕ) ≤ 1 / 2 :=
    clauseEpsilon_le_half hle2 hs.le hs1
  have hS4 : (0 : ℝ) ≤ Real.rpow s (-(4 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS7 : (0 : ℝ) ≤ Real.rpow s (-(7 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS6 : (0 : ℝ) ≤ Real.rpow s (-(6 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS32 : (0 : ℝ) ≤ Real.rpow s (-(3 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  have h3n : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (n : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h3sn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsgn : (0 : ℝ) ≤ ((Annealed.sigmaBar M n : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M n).2.le
  by_cases hfr : (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
      frontier (openCubeSet (originCube d m))) = ∅
  · filter_upwards [hG M s hsrange (regime_le_of_const_le hCG hleG hregime)
      (funding_le_of_epsilon_le hs hepG hfund) hs L m n hmL hnm x z hx hz hgeom hfr]
      with omega hom
    intro hmem u h g hsol hgL2 hgW hhW v w hharm hval hgrad
    have hmemG := Algsuperdiff.Section4.Provider.GoodEvents.goodEventAt_mono_ep M
      (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) (n + 3) z
      ⟨s / 8, by linarith only [hs]⟩ hep0 hepG hmem
    refine (hom hmemG u h g hsol hgL2 hgW hhW v w hharm hval hgrad).trans
      (mul_le_mul_of_nonneg_right hleG (fourSummandBracket_nonneg
        (mul_nonneg hS4 (Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _))
        (mul_nonneg (mul_nonneg hS7 hsgn) h3sn) (mul_nonneg hS6 h3sn)
        (mul_nonneg (mul_nonneg hS6
          (Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _)) h3n)
        ENNReal.toReal_nonneg
        (mul_nonneg (mul_nonneg hS32 h3n) (norm_nonneg _)) ENNReal.toReal_nonneg
        ENNReal.toReal_nonneg ENNReal.toReal_nonneg))
  · filter_upwards [hB M s hsrange (regime_le_of_const_le hCB hleB hregime)
      (funding_le_of_epsilon_le hs hepB hfund) hs L m n hmL hnm x z hx hz hgeom hfr]
      with omega hom
    intro hmem u h g hsol hgL2 hgW hhW v w hharm hval hgrad
    have hmemB := Algsuperdiff.Section4.Provider.GoodEvents.goodEventAt_mono_ep M
      (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) (n + 3) z
      ⟨s / 8, by linarith only [hs]⟩ hep0 hepB hmem
    refine (hom hmemB u h g hsol hgL2 hgW hhW v w hharm hval hgrad).trans
      (mul_le_mul_of_nonneg_right hleB (fourSummandBracket_nonneg
        (mul_nonneg hS4 (Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _))
        (mul_nonneg (mul_nonneg hS7 hsgn) h3sn) (mul_nonneg hS6 h3sn)
        (mul_nonneg (mul_nonneg hS6
          (Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _)) h3n)
        ENNReal.toReal_nonneg
        (mul_nonneg (mul_nonneg hS32 h3n) (norm_nonneg _)) ENNReal.toReal_nonneg
        ENNReal.toReal_nonneg ENNReal.toReal_nonneg))

end

end Algsuperdiff.Section4.Provider.ExcessDecay
