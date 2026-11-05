/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.HarmonicProviderFinalInterior
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RebaseEpsilon
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RebaseWeakening
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RebaseJoinRegated

/-!
# RebaseJoinErrorWeighted

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The error-weighted provider assembly, the outer join

`RebaseJoinRegated`'s script with the general clause's fifth leg read
`𝓔`-multiplied on both sides (hypothesis and conclusion).
The shell lemma `le_ofReal_mul_bracket_add_three` is blind to the coefficients'
shape, so the only change is one more nonnegativity factor at two sites.  The
proved `RebaseJoinRegated` is untouched.

The output is the `ε`-free block with that one leg replaced; the print's own
average form is then produced by `HarmonicApproximationProvider`'s
fractional-Poincaré split.

## Orientation

**This module is a conditional A, not a source-node closure.**  It is
The outer join re-cut at the frozen statement (realized in
`ProviderEpsFree`, read for comparison, never imported).  Against the
`(1/2)`-gated display the frozen statement moves **exactly two** literals, both
at the statement's own existential `C`: the hoisted funding line's
`(1/2) ↦ C⁻¹ s⁴` and the **general** clause's good-event threshold
`(1/2) ↦ C⁻¹ s⁴`.  The **interior** clause's event stays at `(1/2)`.

## Why this is a re-cut and not a composition

`hgen` is a *hypothesis*, and both edits touch its own hypotheses: at the frozen
text `hgen` is funded less and gated on a smaller event, i.e. it is a
**weaker** caller obligation than the `(1/2)`-gated join's.  A weaker hypothesis
cannot be fed to the `(1/2)`-gated theorem, so that script is re-run, and the
two back-ports appear where the constants are chosen:

* the interior clause (`exists_interiorClause_anchorShape`, untouched) is funded
  from the `C⁻¹ s⁴` line through `clauseEpsilon_le_half`;
* the caller's `hgen` is funded through `clauseEpsilon_anti` at its own constant;
* the conclusion's `C⁻¹ s⁴` event is pushed into `hgen`'s (larger) one by the
  proved `GoodEvents.goodEventAt_mono_ep`.

The joint constant is `max (max C_gen C_int) 2`: the `2` is exactly what makes
`C⁻¹ s⁴ ≤ 1/2` on the anchor's own range `s ≤ 1`.

## What the module discharges, unconditionally

* the **outer join**: the two clauses under one existential constant;
* the **a.e. layer**: the two almost-sure statements intersected;
* the **`ℝ≥0∞` shell** of both clauses;
* the **binder weakening** `n + 3 ≤ m ⟹ n + 2 ≤ m` at the interior-instance
  call;
* the **`ε`-back-ports** of both threshold moves.

## The caller obligation `hgen`, in words

On the anchor's own binders, funded at `γ|log γ|² ≤ (s/8)^{3/2} c⋆² · C⁻¹ s⁴`,
and on the good event `𝒢(n+3, z; s/8, C⁻¹ s⁴)`, almost surely,

```text
  ‖u − v‖_{L²(x+□_n)}
      ≤ C ( s^{-4} 𝓔_{s/8}(z+□_{n+3}) ( ‖u − (u)_{W'}‖_{L²(W')}
                                        + s^{-3/2} 3^n |(∇h)_W| )
          + s^{-7}  σ_n^{-1} 3^{(1+s)n} [g]_{H^s(W')}
          + s^{-6}          3^{(1+s)n} [∇h]_{H^s(W')}
          + s^{-6}          3^n        ‖∇h‖_{L²(W')} ) ,
      W = (z + □_{n+2}) ∩ □_m ,   W' = (z + □_{n+3}) ∩ □_m ,
```

with every carrier the anchor's own — the two deliberate asymmetries are
unchanged: the in-bracket `∇h` average stays at `W`, and the interior clause's
slot, gate, flux index and `(1/2)` event all stay at `n+2`.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the frozen block as realized
  in `ProviderEpsFree`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

/-- **The frozen block, from the proved interior chain and one real-valued
caller obligation.**

The conclusion is the frozen statement byte-for-byte (only the two
indicator binders `omega'` carry a leading underscore, forced by the
repository's zero-warning gate: the frozen file escapes the `unusedVariables`
linter only through its `sorry`).  The hypothesis `hgen` is a conditional A
obligation, not a premise of the pinned source statement. -/
theorem exists_harmonicApproximation_provider_of_generalClauseReal_errorWeighted (d : ℕ)
    (hgen : ∃ C : ℝ, 0 < C ∧
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
  exact exists_harmonicApproximation_provider_of_generalClauseReal_with_gradientWeight d
    (fun M L j t z omega => Support.fluxCorrectedErrorRepresentative M L j t
      (Cutoff.translateCutoffSample z omega))
    (fun _ _ _ _ _ _ => Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _) hgen

end

end Algsuperdiff.Section4.Provider.ExcessDecay
