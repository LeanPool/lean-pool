/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.Basic
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Integrable potentials and their truncation

Finite-domain witnesses of `PotentialIntegrable`, integrability of the lower truncation for every
real cutoff and of
its actual biconjugate, and the integral comparison used in the convexification step of CEK
Proposition 12.

Supporting infrastructure for Cordero-Erausquin–Klartag, Proposition 12.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis

section
-- Potential integrability and lower truncation.

open MeasureTheory
open scoped ENNReal
section Truncation
variable {E : Type*} [MeasurableSpace E] {μ : Measure E}
/-- A nonzero measure and the source a.e. finiteness give a real finite-domain
witness; probability normalization and centering are unnecessary. -/
theorem potentialIntegrable_exists_finite (f : E → EReal) (hμ : μ ≠ 0)
    (hf : PotentialIntegrable f μ) : ∃ x, f x ≠ ⊤ := by
  let : NeZero μ := ⟨hμ⟩
  exact hf.2.1.exists
omit [MeasurableSpace E] in
/-- The actual extended truncation has the expected real value at every finite
input point. Infinite values are not silently converted to zero in this identity. -/
theorem lowerTruncate_toReal_of_finite (f : E → EReal) (M : ℝ) (x : E)
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    (lowerTruncate f M x).toReal = max (f x).toReal (-M) := by
  change (max (f x) ((-M : ℝ) : EReal)).toReal = max (f x).toReal (-M)
  lift f x to ℝ using ⟨ht, hb⟩ with r hr
  rcases le_total r (-M) with h | h
  · simp only [EReal.toReal_coe,
      max_eq_right (EReal.coe_le_coe_iff.mpr h), max_eq_right h]
  · simp only [EReal.toReal_coe,
      max_eq_left (EReal.coe_le_coe_iff.mpr h), max_eq_left h]
/-- Lower truncation preserves the source admissibility for every real cutoff,
with no global finiteness, convexity or measurability assumption on the input. -/
theorem lowerTruncate_potentialIntegrable [IsFiniteMeasure μ]
    (f : E → EReal) (M : ℝ) (hf : PotentialIntegrable f μ) :
    PotentialIntegrable (lowerTruncate f M) μ := by
  have hae : (fun x => (lowerTruncate f M x).toReal) =ᵐ[μ]
      (fun x => max (f x).toReal (-M)) := by
    filter_upwards [hf.2.1] with x hx
    exact lowerTruncate_toReal_of_finite f M x hx (hf.1 x)
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ne_of_gt ((EReal.bot_lt_coe (-M)).trans_le (le_max_right _ _))
  · filter_upwards [hf.2.1] with x hx
    exact ne_of_lt (max_lt (Ne.lt_top hx) (EReal.coe_lt_top (-M)))
  · exact (hf.2.2.sup (integrable_const (-M))).congr hae.symm
end Truncation
section Convexification
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
/-- The actual biconjugate of the truncation is admissible. Its Borel real
restriction and domination are derived from lsc and the proved bounds, rather
than provided as additional integrability assumptions. -/
theorem biconjugate_lowerTruncate_potentialIntegrable [IsFiniteMeasure μ]
    (f : E → EReal) (M : ℝ) (hμ : μ ≠ 0) (hf : PotentialIntegrable f μ) :
    PotentialIntegrable (legendre (legendre (lowerTruncate f M))) μ := by
  have hfinite := potentialIntegrable_exists_finite f hμ hf
  have hg := lowerTruncate_potentialIntegrable f M hf
  obtain ⟨hc, hls, _, hbounds, _⟩ := lowerTruncate_convexification f M hfinite
  have hfin : ∀ᵐ x ∂μ, legendre (legendre (lowerTruncate f M)) x ≠ ⊤ := by
    filter_upwards [hg.2.1] with x hx
    exact ne_of_lt ((hbounds x).2.trans_lt (Ne.lt_top hx))
  have hmeas : Measurable (fun x => (legendre (legendre (lowerTruncate f M)) x).toReal) :=
    hls.measurable.ereal_toReal
  have hbnd : ∀ᵐ x ∂μ,
      ‖(legendre (legendre (lowerTruncate f M)) x).toReal‖ ≤
        ‖(lowerTruncate f M x).toReal‖ + |M| := by
    filter_upwards [hfin, hg.2.1] with x hx hgt
    have hlo : -M ≤ (legendre (legendre (lowerTruncate f M)) x).toReal := by
      simpa only [EReal.toReal_coe] using
        (EReal.toReal_le_toReal (hbounds x).1 (EReal.coe_ne_bot (-M)) hx)
    have hup := EReal.toReal_le_toReal (hbounds x).2 (hc.1 x) hgt
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · have hM := le_abs_self M
      have hng := norm_nonneg ((lowerTruncate f M x).toReal)
      linarith
    · have hgabs := le_abs_self ((lowerTruncate f M x).toReal)
      rw [← Real.norm_eq_abs] at hgabs
      have hM := abs_nonneg M
      linarith
  exact ⟨hc.1, hfin, (hg.2.2.norm.add (integrable_const |M|)).mono'
    hmeas.aestronglyMeasurable hbnd⟩
/-- The integral comparison needed for the source convexification step follows
from the admissibility just proved and the actual pointwise biconjugate bound. -/
theorem integral_biconjugate_lowerTruncate_le [IsFiniteMeasure μ]
    (f : E → EReal) (M : ℝ) (hμ : μ ≠ 0) (hf : PotentialIntegrable f μ) :
    (∫ x, (legendre (legendre (lowerTruncate f M)) x).toReal ∂μ) ≤
      ∫ x, (lowerTruncate f M x).toReal ∂μ := by
  have hg := lowerTruncate_potentialIntegrable f M hf
  have hc := biconjugate_lowerTruncate_potentialIntegrable f M hμ hf
  have hproper := lowerTruncate_proper f M (potentialIntegrable_exists_finite f hμ hf)
  apply integral_mono_ae hc.2.2 hg.2.2
  filter_upwards [hg.2.1] with x hx
  exact EReal.toReal_le_toReal (biconjugate_le _ hproper x) (hc.1 x) hx
end Convexification

end

end FunctionalInequalities.Probability.MomentMeasure
