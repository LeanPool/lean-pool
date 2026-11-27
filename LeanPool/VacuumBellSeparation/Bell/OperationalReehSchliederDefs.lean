/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.BicommutantOrbit

/-!
# The explicitly corrected operational Reeh–Schlieder property

VW05 Lemma 6.1 prints a strict estimate for every ambient R. At R=0
this asks for 0<0. We record that literal predicate separately, use a
strict bound only for nonzero R and require the exact equality at zero.
The quantified non-strict all-R version is proved equivalent separately.
The selected expectation is the original numerator divided by its actual
positive selection weight; its nonzero denominator is explicit.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The literal vector-state numerator and success denominator in VW05 (6.1). -/
def operationalSelectedValue (Ω : H) (a R : H →L[ℂ] H) : ℂ :=
  ⟪Ω, (star a * R * a) Ω⟫_ℂ / ⟪Ω, (star a * a) Ω⟫_ℂ

/-- Approximation of every unit-vector state by a normalized selection from the given algebra. -/
def HasOperationalReehSchlieder (A : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) : Prop :=
  ∀ χ : H, ‖χ‖ = 1 → ∀ ε : ℝ, 0 < ε → ∃ a : A,
    ⟪Ω, (star (a : H →L[ℂ] H) * (a : H →L[ℂ] H)) Ω⟫_ℂ ≠ 0 ∧
    ⟪χ, (0 : H →L[ℂ] H) χ⟫_ℂ = operationalSelectedValue Ω a 0 ∧
    ∀ R : H →L[ℂ] H, R ≠ 0 →
      ‖⟪χ, R χ⟫_ℂ - operationalSelectedValue Ω a R‖ < ε * ‖R‖

/-- Operational Reeh–Schlieder condition with a non-strict bound for all test operators. -/
def HasOperationalReehSchliederLe (A : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) : Prop :=
  ∀ χ : H, ‖χ‖ = 1 → ∀ ε : ℝ, 0 < ε → ∃ a : A,
    ⟪Ω, (star (a : H →L[ℂ] H) * (a : H →L[ℂ] H)) Ω⟫_ℂ ≠ 0 ∧
    ∀ R : H →L[ℂ] H,
      ‖⟪χ, R χ⟫_ℂ - operationalSelectedValue Ω a R‖ ≤ ε * ‖R‖

/-- The uncorrected printed all-R strict formula; it is false for a unit Ω. -/
def PrintedStrictOperationalReehSchlieder
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) : Prop :=
  ∀ χ : H, ‖χ‖ = 1 → ∀ ε : ℝ, 0 < ε → ∃ a : A,
    ∀ R : H →L[ℂ] H,
      ‖⟪χ, R χ⟫_ℂ - operationalSelectedValue Ω a R‖ < ε * ‖R‖

@[simp] theorem operationalSelectedValue_zero (Ω : H) (a : H →L[ℂ] H) :
    operationalSelectedValue Ω a 0 = 0 := by
  simp only [operationalSelectedValue, mul_zero, zero_mul,
    zero_apply, inner_zero_right, zero_div]

theorem operationalSelectedValue_eq_pairing (Ω : H) (a R : H →L[ℂ] H) :
    operationalSelectedValue Ω a R = ⟪a Ω, R (a Ω)⟫_ℂ / ⟪a Ω, a Ω⟫_ℂ := by
  simp only [operationalSelectedValue, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

theorem operationalSelectionWeight_eq_norm_sq (Ω : H) (a : H →L[ℂ] H) :
    ⟪Ω, (star a * a) Ω⟫_ℂ = (‖a Ω‖ : ℂ) ^ 2 := by
  simp only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K,
    RCLike.ofReal_eq_complex_ofReal]

theorem operationalSelectionWeight_ne_zero_iff (Ω : H) (a : H →L[ℂ] H) :
    ⟪Ω, (star a * a) Ω⟫_ℂ ≠ 0 ↔ a Ω ≠ 0 := by
  rw [operationalSelectionWeight_eq_norm_sq]
  simp only [ne_eq, pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0),
    Complex.ofReal_eq_zero, norm_eq_zero]

theorem operationalSelectionWeight_re_pos (Ω : H) (a : H →L[ℂ] H)
    (ha : a Ω ≠ 0) : 0 < (⟪Ω, (star a * a) Ω⟫_ℂ).re := by
  rw [operationalSelectionWeight_eq_norm_sq, ← Complex.ofReal_pow, Complex.ofReal_re]
  exact sq_pos_of_pos (norm_pos_iff.mpr ha)

theorem operationalSelectedValue_of_unit (Ω : H) (a R : H →L[ℂ] H)
    (ha : ‖a Ω‖ = 1) : operationalSelectedValue Ω a R = ⟪a Ω, R (a Ω)⟫_ℂ := by
  rw [operationalSelectedValue_eq_pairing, inner_self_eq_norm_sq_to_K,
    ha, RCLike.ofReal_one, one_pow, div_one]

theorem not_printedStrictOperationalReehSchlieder
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (hΩ : ‖Ω‖ = 1) :
    ¬ PrintedStrictOperationalReehSchlieder A Ω := by
  intro h
  obtain ⟨a, ha⟩ := h Ω hΩ 1 zero_lt_one
  have hzero := ha 0
  simp only [zero_apply, inner_zero_right, operationalSelectedValue_zero, sub_self,
    norm_zero, mul_zero, lt_self_iff_false] at hzero

theorem operationalReehSchlieder_iff_le
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) :
    HasOperationalReehSchlieder A Ω ↔ HasOperationalReehSchliederLe A Ω := by
  constructor
  · intro h χ hχ ε hε
    obtain ⟨a, ha, hz, hb⟩ := h χ hχ ε hε
    refine ⟨a, ha, fun R => ?_⟩
    by_cases hR : R = 0
    · subst R
      simp only [zero_apply, inner_zero_right,
        operationalSelectedValue_zero, sub_self, norm_zero, mul_zero, le_refl]
    · exact (hb R hR).le
  · intro h χ hχ ε hε
    obtain ⟨a, ha, hb⟩ := h χ hχ (ε / 2) (by positivity)
    refine ⟨a, ha, ?_, fun R hR => ?_⟩
    · simp only [zero_apply, inner_zero_right, operationalSelectedValue_zero]
    · exact (hb R).trans_lt (mul_lt_mul_of_pos_right (by linarith) (norm_pos_iff.mpr hR))

end VacuumBellSeparation.Bipartite
