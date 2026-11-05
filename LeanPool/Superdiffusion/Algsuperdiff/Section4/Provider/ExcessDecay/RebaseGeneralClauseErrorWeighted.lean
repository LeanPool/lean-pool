/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ReindexGeneralClause
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RecutAtoms
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ReindexComposed

/-!
# RebaseGeneralClauseErrorWeighted

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The error-weighted general clause in real form, at frontier-empty
# windows

This is `ReindexGeneralClause.exists_generalClauseReal_frontierEmpty`'s
interface with the two slack `∇h` legs re-typed at the error-weighted shapes — the
Gagliardo one at `s^{-6}` and the flat one at `s^{-6}·𝓔·3^n·‖∇h‖_{L²}`.  Both
are **pure nonnegative slack** on this branch, so the change is statement-only;
the frontier-empty modules at the unweighted shapes are untouched.  The
composed chain of
`ReindexComposed` (good event, flux index and `σ` index all at `n+3`, binder
`n + 3 ≤ m`) is carried onto that right-hand side by the **three** proved
moves, in one absorption:

* the **`σ` gap-3 conversion** `σ_{n+3}^{-1} ≤ 4 σ_n^{-1}`
  (`ReindexSlot.exists_inv_sigmaBar_add_three_le`; the same constant `4` the
  proved two-scale conversion pays — the gap is free);
* the **two window moves** to `W' = (z + □_{n+3}) ∩ □_m`, at the volume ratio
  `81^d`, i.e. `K = 2·9^d` on the `L²` leg and `9^d` on the force leg
  (`RecutAtoms`, unchanged);
* the **three `∇h` legs**, which are nonnegative summands of the frozen
  right-hand side and are simply added (the comparison solution carries a
  constant boundary datum, so no `∇h` term is produced anywhere in the chain).

Every `s`-power, every `3`-power, the in-bracket `3^n |(∇h)_W|` companion at the
**`n+2`** window (the frozen statement's deliberate asymmetry), and the interior
gate are byte-untouched.

## The `MemLp` side conditions

Exactly the re-cut general clause's: `u.toFun` almost-everywhere strongly
measurable on the normalized `W`, and the two window quantities finite so
that the `ℝ≥0∞` bounds descend to `ℝ`.  Both come from the anchor's own binders.
No new hypothesis is introduced.

## References

* ABK26, `l.harmonic.approximation.good.scales`;
  `Algsuperdiff.Frozen.Section4.harmonic_approximation_good_scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory

noncomputable section

/-! The three window-absorption helpers are shared with `ReindexGeneralClause`. -/

/-! ## 2. The error-weighted general clause in real form, gated at the interior
regime -/

/-- **The Join's `hgen`, at frontier-empty windows, at the `(1/2)` event.**

`ReindexComposed.exists_generalClauseInterior_honest_addThree` carried onto the
error-weighted right-hand side: the `σ` gap-3 conversion, the two `81^d` window
moves and the three nonnegative `∇h` legs, in one absorption.

On this branch the three `∇h` legs are **pure slack** — `general_absorb_window`
consumes nothing about them but their sign — so re-typing the flat one at
`s^{-6}·𝓔·3^n·‖∇h‖_{L²}` (and the Gagliardo one at the power `s^{-6}` rather
than `s^{-9/2}`) uses the shared `exists_generalClauseReal_frontierEmpty_with_slack` estimate
and discharges its two nonnegativity obligations.  The
`ε`-re-gating to the threshold `C⁻¹s⁴` is performed by the consumer
`RebaseSealDistanceErrorWeighted`, exactly as `RebaseGeneralClauseRegated` does
it at the unweighted shapes. -/
theorem exists_generalClauseReal_frontierEmpty_half_errorWeighted (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
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
                  frontier (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)) =
                ∅) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) (n + 3) z
                  ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
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
                                        (HCPolySupport.originCube d m)))).toReal) := by
  obtain ⟨C, hC, hcore⟩ := exists_generalClauseReal_frontierEmpty_with_slack d
  refine ⟨C, hC, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm x z hx hz hgeom hfr
  filter_upwards [hcore M s hsrange hregime hsmall hs L m n hmL hnm x z hx hz hgeom hfr]
    with omega hom
  intro hmem u h g hsol hgL2 hgW hhW v w hharm hval hgrad
  refine hom hmem u h g hsol hgL2 hgW hhW _ _ ?_ ?_ v w hharm hval hgrad
  · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _)
      (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _)
      (Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _))
      (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg

end

end Algsuperdiff.Section4.Provider.ExcessDecay
