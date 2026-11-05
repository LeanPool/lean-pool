/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.OneSidedOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.PlateauLandmarks
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.ObservableScaleAntitone
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Induction.BaseWindowDiffusivity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TwoTermPromotion
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Scales.BaseLoss

/-!
# InductionStart

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The induction state at the base landmark `m**`

ABK26 packages the base case from the `m <= m**` consequences of the plateau
estimate as the induction state `d.mathcalS.def` at `m0 = m**`.  This file
supplies the diffusivity half of that packaging, and the scale-transport
glue the base-case assembly consumes.

## Main results

* `inductionState_diffusivity`: the diffusivity conjunct of
  `Algsuperdiff.Frozen.Section3.inductionState M (mStarStar M) E` — proved
  unconditionally, with no residual input and no dependence on `E`.

Supporting glue:

* `isOneSidedOrlicz_cutoffHomogenizationError_of_le`: the non-strict scale
  transport of the Appendix-literal one-sided relation, obtained from the
  proved `Provider.ErrorComparison.isBigOWith_cutoffHomogenizationError_of_lt`.
* `sqrt_cstar_le_sqrt_cstarPlus`: the numeric comparison the base-case assembly
  needs.

The model-free two-term promotion `isTwoTermBigOWith_of_isOneSidedOrlicz` — a
one-sided `Gamma_sigma` bound promotes for free to the two-term shape, with the
second witness identically zero and the second amplitude an arbitrary positive
number — lives in `Provider/Orlicz/TwoTermPromotion.lean`, and the base-loss
square-root comparison in `Provider/Scales/BaseLoss.lean`.

## The diffusivity conjunct

Since `m** <= m*`, the conjunct is the proved
`Provider.Induction.inductionState_diffusivity_le_mStar` composed with
transitivity: for `m <= m*` the landmark threshold forces `cstar gamma^{-1}
3^{2 gamma m} <= nu^2`, so the `max` in the induction state collapses to
`nu^2`, and the plateau specialization gives `nu <= sigmaBar_m <= 2 nu`, which
is inside the printed window `[nu^2 / 4, 4 nu^2]`.

## The scale endpoint

`inductionState` quantifies its error clause over the closed window `s in [8
gamma, 1]`, while every recorded base estimate carries the literal open
interval `0 < s < 1`.  The endpoint `s = 1` is reached by the consumer without
ever evaluating `baseLoss` at `1`: the interior scale `min s (1/2)` is used,
and the error at the larger scale `s` is dominated a.e. by the error at the
smaller scale via `e.mathcalE.monotone.ordered`, proved as
`Provider.ErrorComparison.cutoffHomogenizationError_ae_antitone` and exposed
here as `isOneSidedOrlicz_cutoffHomogenizationError_of_le`.  That costs only
the factor `(min s (1/2))^{-1} <= 2 s^{-1}`.

## References

* ABK26, `p.base.case`.
* ABK26, `d.mathcalS.def`, the induction state.
* ABK26, `e.mstarstar`.
* ABK26, `e.mathcalE.monotone.ordered`.
-/

namespace Algsuperdiff.Section3.Provider.Base

open HCPolySupport MeasureTheory

/-! ## The diffusivity conjunct of the induction state -/

/-- **The diffusivity conjunct of `Algsuperdiff.Frozen.Section3.inductionState`
at `m0 = m**`, unconditionally.**

This statement is the first conjunct of
`Algsuperdiff.Frozen.Section3.inductionState M (mStarStar M) E`, which does not
mention `E`.  No residual input is used.

`m** <= m*` (`Provider.Scales.mStarStar_le_mStar`), so this is the proved
`Provider.Induction.inductionState_diffusivity_le_mStar`, which proves the same
window on the whole base range `m <= m*`, composed with transitivity.  There
the landmark characterization collapses the `max` to `nu^2` and the plateau
specialization gives `nu <= sigmaBar_m <= 2 nu`, hence `nu^2 / 4 <= nu^2 <=
sigmaBar_m^2 <= 4 nu^2`. -/
theorem inductionState_diffusivity {d : ℕ} (M : ABKModel d) :
    ∀ m : ℤ, m ≤ mStarStar M →
      (1 / 4 : ℝ) *
          max
            (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))
            (M.nu ^ 2)
        ≤ (Annealed.sigmaBar M m : ℝ) ^ 2 ∧
      (Annealed.sigmaBar M m : ℝ) ^ 2
        ≤ 4 *
          max
            (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))
            (M.nu ^ 2) :=
  fun m hm => Provider.Induction.inductionState_diffusivity_le_mStar M m
    (hm.trans (Provider.Scales.mStarStar_le_mStar M))

/-! ## Scale transport of the one-sided relation -/

/-- **The non-strict scale transport of `X <= O_Psi(A)` for the Section 3 error
observable.**

The proved
`Provider.ErrorComparison.isBigOWith_cutoffHomogenizationError_of_lt` covers `t
< s`; the base case also needs `t = s`, where the two observables are literally
the same function.  Neither `Psi` nor `A` changes. -/
theorem isOneSidedOrlicz_cutoffHomogenizationError_of_le {d : ℕ} (M : ABKModel d)
    (m : ℤ) {Psi : ℝ → ℝ} {t s A : ℝ} (ht : 0 < t) (hts : t ≤ s)
    (h : Probability.IsOneSidedOrlicz (Cutoff.cutoffSampleLaw M).toMeasure Psi
      (Observable.cutoffHomogenizationError M m ⟨t, ht⟩) A) :
    Probability.IsOneSidedOrlicz (Cutoff.cutoffSampleLaw M).toMeasure Psi
      (Observable.cutoffHomogenizationError M m ⟨s, lt_of_lt_of_le ht hts⟩) A := by
  refine ⟨h.1, h.2.1,
    Observable.measurable_cutoffHomogenizationError M m ⟨s, lt_of_lt_of_le ht hts⟩, ?_⟩
  rcases eq_or_lt_of_le hts with heq | hlt
  · have hsub : (⟨s, lt_of_lt_of_le ht hts⟩ : {s : ℝ // 0 < s}) = ⟨t, ht⟩ :=
      Subtype.ext heq.symm
    rw [hsub]
    exact h.2.2.2
  · exact Provider.ErrorComparison.isBigOWith_cutoffHomogenizationError_of_lt
      M m ht hlt h.2.2.2

/-! ## The two numeric comparisons -/

/-- The directional constant never exceeds the Frobenius one: `cstar <= c+`
because `d cstar <= c+` and `d >= 2`. -/
theorem sqrt_cstar_le_sqrt_cstarPlus {d : ℕ} (M : ABKModel d) :
    Real.sqrt (Disorder.cstar M) ≤ Real.sqrt (Disorder.cstarPlus M) := by
  refine Real.sqrt_le_sqrt ?_
  have hd : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast M.shellPrefix.dimension
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hdc := Disorder.dim_mul_cstar_le_cstarPlus M
  have h1 : 1 * Disorder.cstar M ≤ (d : ℝ) * Disorder.cstar M :=
    mul_le_mul_of_nonneg_right (by linarith) hcs.le
  linarith

end Algsuperdiff.Section3.Provider.Base
