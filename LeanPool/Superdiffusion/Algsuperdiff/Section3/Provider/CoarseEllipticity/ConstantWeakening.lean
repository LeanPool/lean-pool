/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Exponent
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.LowerFamily

/-!
# ConstantWeakening

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Constant weakening for the coarse-ellipticity tail carriers

Proposition `p.cg.ellipticity.bounds` (ABK26) is stated as `∃ C(d) < ∞` such
that two weak-Orlicz displays hold.  Its frozen Lean surface
`Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds` therefore only records
`0 < Ccg`, while several consumers need a *normalized* constant (concretely `1
≤ Ccg`; see `Provider/BadEvents/BadEventLemmaCases.lean`, whose `hCcg` binder
is exactly that gate).  Nothing but monotonicity is needed: the source
statement is *weaker* for a larger constant, in every one of its slots.

This module supplies the three monotonicity facts that make that precise, all
of them model-free.

* `isLowerIntegerFamilyOrlicz_mono` --- the lower-family carrier
  `Probability.IsLowerIntegerFamilyOrlicz` is monotone in the deterministic
  shift `b` and in the tail scale `A`.  The witness is unchanged; the
  domination `X L ω ≤ b + Y ω` only weakens, and the tail weakens by
  CoarseGraining's `IsBigOWith.mono_scale`.
* `isDeterministicShiftTwoTermOneSidedOrlicz_mono` --- the two-term carrier
  `Probability.IsDeterministicShiftTwoTermOneSidedOrlicz` is monotone in the
  deterministic shift `b` and in both tail scales `A₁`, `A₂`, by the same two
  ingredients.
* `lowerEllipticityProfile_mono_const` --- the source-corrected deterministic
  lower profile of `Section3/Exponent.lean` is monotone in its constant, in all
  three branches of `CoarseEllipticityExponent` (finite `q < 2` at pole order
  `2 / q`, finite `q ≥ 2` at pole order one, and the infinity endpoint).  Its
  two hypotheses `0 ≤ s` and `0 ≤ 2 * s - gamma` are consequences of the source
  window `s ∈ [gamma/2 + exp(...), 1]`, not extra premises.

## References

* ABK26, `p.cg.ellipticity.bounds`.
* ABK26, Appendix, (the weak-Orlicz notation).
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open Algsuperdiff.Section3

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The lower-indexed source supremum bound weakens when the deterministic
shift and the tail scale both increase.  The common measurable witness is
unchanged. -/
theorem isLowerIntegerFamilyOrlicz_mono
    {μ : Measure Ω} [IsFiniteMeasure μ] {Ψ : ℝ → ℝ} {X : ℤ → Ω → ℝ}
    {L0 : ℤ} {b b' A A' : ℝ}
    (hX : Probability.IsLowerIntegerFamilyOrlicz μ Ψ X L0 b A)
    (hb : b ≤ b') (hA : A ≤ A') :
    Probability.IsLowerIntegerFamilyOrlicz μ Ψ X L0 b' A' := by
  obtain ⟨Y, hY⟩ := hX
  refine ⟨Y, hY.admissible, lt_of_lt_of_le hY.scale_pos hA, hY.measurable_observable,
    hY.measurable_witness, ?_, hY.tail.mono_scale hA⟩
  intro ω L hL
  have := hY.dominates ω L hL
  linarith

/-- The one-sided two-term weak-Orlicz relation with a deterministic shift
weakens when the shift and both tail scales increase.  Both witnesses are
unchanged. -/
theorem isDeterministicShiftTwoTermOneSidedOrlicz_mono
    {μ : Measure Ω} [IsFiniteMeasure μ] {Ψ₁ Ψ₂ : ℝ → ℝ} {X : Ω → ℝ}
    {b b' A₁ A₁' A₂ A₂' : ℝ}
    (hX : Probability.IsDeterministicShiftTwoTermOneSidedOrlicz μ Ψ₁ Ψ₂ X b A₁ A₂)
    (hb : b ≤ b') (hA₁ : A₁ ≤ A₁') (hA₂ : A₂ ≤ A₂') :
    Probability.IsDeterministicShiftTwoTermOneSidedOrlicz μ Ψ₁ Ψ₂ X b' A₁' A₂' := by
  rw [Probability.deterministicShiftTwoTermOneSidedOrlicz_iff_exists] at hX ⊢
  obtain ⟨Y, Z, hΨ₁, hΨ₂, hA₁pos, hA₂pos, hXmeas, hYmeas, hZmeas, hdom, hYtail,
    hZtail⟩ := hX
  refine ⟨Y, Z, hΨ₁, hΨ₂, lt_of_lt_of_le hA₁pos hA₁, lt_of_lt_of_le hA₂pos hA₂,
    hXmeas, hYmeas, hZmeas, ?_, hYtail.mono_scale hA₁, hZtail.mono_scale hA₂⟩
  intro ω
  have := hdom ω
  linarith

/-- The source-corrected deterministic lower-ellipticity profile is monotone in
its constant, on the whole admissible exponent carrier.

The two hypotheses are exactly what the source window
`s ∈ [gamma/2 + exp(-C⁻¹E⁻²gamma⁻¹), 1]` supplies; they are needed only so
that the finite `q < 2` branch's real power has a nonnegative base. -/
theorem lowerEllipticityProfile_mono_const {C C' gamma s : ℝ}
    (hs : 0 ≤ s) (hgap : 0 ≤ 2 * s - gamma) (hC : C ≤ C')
    (q : CoarseEllipticityExponent) :
    lowerEllipticityProfile C gamma s q ≤ lowerEllipticityProfile C' gamma s q := by
  obtain ⟨q, -⟩ := q
  have hratio : (0 : ℝ) ≤ s / (2 * s - gamma) := div_nonneg hs hgap
  cases q with
  | finite r =>
      simp only [lowerEllipticityProfile]
      by_cases hr : r < 2
      · rw [ite_eq_left hr, ite_eq_left hr]
        exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hratio _)
      · rw [ite_eq_right hr, ite_eq_right hr, mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right hC
          (mul_nonneg hs (inv_nonneg.2 hgap))
  | infinity => exact hC

end Algsuperdiff.Section3.Provider.CoarseEllipticity
