/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger

/-!
# High-contrast homogenization: Provider.Quenched.RestoredSource

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Restoration of the microscopic source scale

This file isolates the rescaled source scale of the dilated law and its tail, as
they are used in `ss.algebraic.convergence`.  The tail event
is strict, exactly as in `CoarseEllipticityDagger.source_tail` and in the
reference text.
-/

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory
open IndependentSums

variable {d : ℕ}

/-- The restored source has the native tail at the dilated gauge argument.

The floor at one cannot contribute because the tail threshold is at least
one and the upper-tail event is strict. -/
theorem measureReal_restored_source_upperTail_le
    {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdagger : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (Nann : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    P.real (upperTailEvent
        (fun a => max 1 (S a / (3 : ℝ) ^ Nann)) t) ≤
      (Ψ ((3 : ℝ) ^ Nann * t))⁻¹ := by
  have hscale : 0 < (3 : ℝ) ^ Nann := by positivity
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hevent :
      upperTailEvent (fun a => max 1 (S a / (3 : ℝ) ^ Nann)) t =
        upperTailEvent S ((3 : ℝ) ^ Nann * t) := by
    ext a
    change (t < max 1 (S a / (3 : ℝ) ^ Nann)) ↔
      ((3 : ℝ) ^ Nann * t < S a)
    constructor
    · intro ha
      rcases lt_max_iff.mp ha with hone | hscaled
      · exact False.elim ((not_lt_of_ge ht) hone)
      · have hmul := (lt_div_iff₀ hscale).mp hscaled
        simpa only [mul_comm] using hmul
    · intro ha
      apply lt_max_of_lt_right
      apply (lt_div_iff₀ hscale).2
      simpa only [mul_comm] using ha
  rw [hevent]
  exact hdagger.source_tail _ (mul_pos hscale ht0)

/-- The restored microscopic source scale is measurable, at least one, and
has the source-gauge upper tail after discarding the dilation factor by
monotonicity. -/
theorem exists_restored_source_scale
    {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdagger : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (Nann : ℕ) :
    ∃ Ssrc : CoeffSpace d → ℝ,
      Measurable Ssrc ∧
      (∀ a, 1 ≤ Ssrc a) ∧
      (∀ a, Ssrc a = max 1 (S a / (3 : ℝ) ^ Nann)) ∧
      ∀ t : ℝ, 1 ≤ t →
        P.real (upperTailEvent Ssrc t) ≤ (Ψ t)⁻¹ := by
  let Ssrc : CoeffSpace d → ℝ :=
    fun a => max 1 (S a / (3 : ℝ) ^ Nann)
  refine ⟨Ssrc, ?_, ?_, fun _ => rfl, ?_⟩
  · exact measurable_const.max (hdagger.source_measurable.div_const _)
  · exact fun a => le_max_left _ _
  · intro t ht
    have htail := measureReal_restored_source_upperTail_le hdagger Nann ht
    have ht0 : 0 ≤ t := zero_le_one.trans ht
    have hscale1 : (1 : ℝ) ≤ (3 : ℝ) ^ Nann := one_le_pow₀ (by norm_num)
    have htle : t ≤ (3 : ℝ) ^ Nann * t := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hscale1 ht0
    have hΨle : Ψ t ≤ Ψ ((3 : ℝ) ^ Nann * t) :=
      hdagger.gauge_admissible.1 ht0
        (le_trans ht0 htle) htle
    have hΨt : 0 < Ψ t :=
      lt_of_lt_of_le zero_lt_one (hdagger.gauge_admissible.2 ht0)
    have hΨscale : 0 < Ψ ((3 : ℝ) ^ Nann * t) :=
      lt_of_lt_of_le zero_lt_one
        (hdagger.gauge_admissible.2 (le_trans ht0 htle))
    exact htail.trans ((inv_le_inv₀ hΨscale hΨt).2 hΨle)

end HCPolySupport.HighContrast.Quenched
