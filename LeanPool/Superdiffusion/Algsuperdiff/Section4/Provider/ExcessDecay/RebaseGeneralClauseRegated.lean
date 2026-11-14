/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RebaseGeneralClause
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RebaseEpsilon

/-!
# RebaseGeneralClauseRegated

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior chain's re-gated instance

**Conditional-free provider helper, not a node realization.**  The re-gated
sibling of `RebaseGeneralClause`'s
`exists_generalClauseReal_frontierEmpty_legMoved`, at the frozen text: the
hoisted funding line and the good-event threshold of the general clause both
read `C⁻¹ s⁴` instead of `(1/2)`, at the statement's own existential constant.

Both edits are **hypothesis-side** here — the funding line is a hypothesis, and
so is the event membership `hmem` in the real-valued clause — so the re-gated
instance is a pure a-fortiori composition of the `(1/2)` one at the constant
re-choice `C ↦ max C 2`:

* `regime_le_of_const_le` back-ports the standing regime;
* `funding_le_of_epsilon_le` back-ports the funding line (`C⁻¹ s⁴ ≤ 1/2` funds
  less);
* the proved `GoodEvents.goodEventAt_mono_ep` back-ports the event membership
  (the re-gated event is the smaller set, so `hmem` at `C⁻¹ s⁴` gives `hmem` at
  `(1/2)`);
* `fourSummandBracket_nonneg` pays the constant bump on the conclusion.

Nothing else moves.  The flux index `n+3`, the binder `n+3 ≤ m`, the
frontier-empty gate at `n+2`, the windows `W = (z+□_{n+2}) ∩ □_m` and
`W' = (z+□_{n+3}) ∩ □_m`, the flux prefactor `s^{-4}`, the in-bracket companion
`s^{-3/2}`, the force leg `s^{-7}` and the two `∇h` legs `s^{-6}` are the frozen
block's own: only the two literals `(1/2) ↦ C⁻¹ s⁴` move.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the frozen block as realized
  in `ProviderEpsFree` (read for comparison, never imported).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

/-- **The Join's `hgen`, at frontier-empty windows, re-gated.**

`exists_generalClauseReal_frontierEmpty_legMoved` read a fortiori at the
`C⁻¹ s⁴` funding line and the `C⁻¹ s⁴` good-event threshold.  Same carriers,
same legs; only the two literals move, and both move the safe way. -/
theorem exists_generalClauseReal_frontierEmpty_regated (d : ℕ) :
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
            (((fun y' => z + y') ''
                    HCPolySupport.openCubeSet (HCPolySupport.originCube d (n + 2))) ∩
                  frontier (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)) =
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
                            Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                                (MeasureTheory.eLpNorm h.grad 2
                                  (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                    (((fun y' => z + y') ''
                                        HCPolySupport.openCubeSet
                                          (HCPolySupport.originCube d (n + 3))) ∩
                                      HCPolySupport.openCubeSet
                                        (HCPolySupport.originCube d m)))).toReal)
    := by
  classical
  obtain ⟨C, hC, hclause⟩ := exists_generalClauseReal_frontierEmpty_legMoved d
  have hCle : C ≤ max C 2 := le_max_left C 2
  have hC2 : (2 : ℝ) ≤ max C 2 := le_max_right C 2
  have hCpos : (0 : ℝ) < max C 2 := lt_of_lt_of_le (by norm_num) hC2
  refine ⟨max C 2, hCpos, ?_⟩
  intro M s hsrange hregime hfund hs L m n hmL hnm x z hx hz hgeom hfr
  have hs1 : s ≤ 1 := hsrange.2
  have hep0 : (0 : ℝ) ≤ (max C 2)⁻¹ * s ^ (4 : ℕ) := clauseEpsilon_nonneg hCpos hs.le
  have hephalf : (max C 2)⁻¹ * s ^ (4 : ℕ) ≤ 1 / 2 := clauseEpsilon_le_half hC2 hs.le hs1
  have hS4 : (0 : ℝ) ≤ Real.rpow s (-(4 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS7 : (0 : ℝ) ≤ Real.rpow s (-(7 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS6 : (0 : ℝ) ≤ Real.rpow s (-(6 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS32 : (0 : ℝ) ≤ Real.rpow s (-(3 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  have h3n : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (n : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h3sn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsgn : (0 : ℝ) ≤ ((Annealed.sigmaBar M n : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M n).2.le
  filter_upwards [hclause M s hsrange (regime_le_of_const_le hC hCle hregime)
    (funding_le_of_epsilon_le hs hephalf hfund) hs L m n hmL hnm x z hx hz hgeom hfr]
    with omega hom
  intro hmem u h g hsol hgL2 hgW hhW v w hharm hval hgrad
  have hmem' := Algsuperdiff.Section4.Provider.GoodEvents.goodEventAt_mono_ep M
    (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) (n + 3) z
    ⟨s / 8, by linarith only [hs]⟩ hep0 hephalf hmem
  refine (hom hmem' u h g hsol hgL2 hgW hhW v w hharm hval hgrad).trans ?_
  exact mul_le_mul_of_nonneg_right hCle (fourSummandBracket_nonneg
    (mul_nonneg hS4 (Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _))
    (mul_nonneg (mul_nonneg hS7 hsgn) h3sn) (mul_nonneg hS6 h3sn)
    (mul_nonneg hS6 h3n) ENNReal.toReal_nonneg
    (mul_nonneg (mul_nonneg hS32 h3n) (norm_nonneg _)) ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
