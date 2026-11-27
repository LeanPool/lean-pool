/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.ReflectionReduction
public import LeanPool.VacuumBellSeparation.Bell.EventConstantDefs

/-!
# The event comparison constants `K_{r,±}` and Theorem 3.1 in the manuscript's form

Equation (3.1) (`eq:K`) of the manuscript defines, for `r > 1`,

`K_{r,+} = sup_{E,P} ω(EP)^r / (ω(E)ω(P))^{r-1}`,
`K_{r,-} = sup_{E,P} (ω(E)ω(P))^r / ω(EP)^{r-1}`,

the suprema ranging over local projections with positive product of marginals, a positive
numerator with zero denominator giving `+∞`.  They are defined in
`VacuumBellSeparation.Bell.EventConstantDefs` as `eventConstPlus` and `eventConstMinus`.

`eventPlus_bound` and `eventMinus_bound` convert finiteness of the constants into the
denominator-free inequalities used by `chshValue_le_one_of_projection_bounds`.

`bellCorrelation_eq_one_of_event_constants_of_approx` is Theorem 3.1 of the manuscript with
one extra explicit hypothesis per algebra, the reflection-approximation property
`saContractions M ⊆ closure (convexHull ℝ (reflections M))`; that property is proved for
every von Neumann algebra in `VacuumBellSeparation.Bell.Theorem31`
(`saContractions_subset_closure_convexHull_reflections`), which also states the theorem
without the extra hypotheses (`probability_criterion`).
-/

@[expose] public section

open scoped ENNReal

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem le_eventConstPlus (ω : State H) {𝔄 𝔅 : VonNeumannAlgebra H} (r : ℝ)
    {E P : H →L[ℂ] H} (hE : E ∈ projections 𝔄) (hP : P ∈ projections 𝔅)
    (hpos : 0 < (ω E).re * (ω P).re) :
    ENNReal.ofReal ((ω (E * P)).re ^ r / ((ω E).re * (ω P).re) ^ (r - 1))
      ≤ eventConstPlus ω 𝔄 𝔅 r :=
  le_iSup₂_of_le E hE (le_iSup₂_of_le P hP (le_iSup_of_le hpos le_rfl))

theorem le_eventConstMinus (ω : State H) {𝔄 𝔅 : VonNeumannAlgebra H} (r : ℝ)
    {E P : H →L[ℂ] H} (hE : E ∈ projections 𝔄) (hP : P ∈ projections 𝔅)
    (hpos : 0 < (ω E).re * (ω P).re) :
    ENNReal.ofReal (((ω E).re * (ω P).re) ^ r) / ENNReal.ofReal ((ω (E * P)).re ^ (r - 1))
      ≤ eventConstMinus ω 𝔄 𝔅 r :=
  le_iSup₂_of_le E hE (le_iSup₂_of_le P hP (le_iSup_of_le hpos le_rfl))

/-- A projection is a positive operator. -/
theorem isPositive_of_mem_projections {M : VonNeumannAlgebra H} {E : H →L[ℂ] H}
    (hE : E ∈ projections M) : E.IsPositive := by
  have h : (0 : H →L[ℂ] H) ≤ star E * E := star_mul_self_nonneg E
  rw [hE.2.1.star_eq, hE.2.2] at h
  exact ContinuousLinearMap.nonneg_iff_isPositive.mp h

/-- The complement of a projection is a projection. -/
theorem one_sub_mem_projections {M : VonNeumannAlgebra H} {E : H →L[ℂ] H}
    (hE : E ∈ projections M) : 1 - E ∈ projections M := by
  refine ⟨sub_mem (one_mem M) hE.1, IsSelfAdjoint.sub (by simp) hE.2.1, ?_⟩
  simp only [sub_mul, mul_sub, one_mul, mul_one, hE.2.2, sub_self, sub_zero]

/-- Probabilities of a pair of commuting local projections: `0 ≤ ω(EP) ≤ min(ω(E), ω(P))`. -/
theorem projection_cell_facts (ω : State H) {𝔄 𝔅 : VonNeumannAlgebra H}
    (hcomm : Commuting 𝔄 𝔅) {E P : H →L[ℂ] H}
    (hE : E ∈ projections 𝔄) (hP : P ∈ projections 𝔅) :
    0 ≤ (ω (E * P)).re ∧ (ω (E * P)).re ≤ (ω E).re ∧ (ω (E * P)).re ≤ (ω P).re ∧
      0 ≤ (ω E).re ∧ 0 ≤ (ω P).re := by
  have hEp := isPositive_of_mem_projections hE
  have hPp := isPositive_of_mem_projections hP
  have hc : E * P = P * E := hcomm E hE.1 P hP.1
  have hE' := isPositive_of_mem_projections (one_sub_mem_projections hE)
  have hP' := isPositive_of_mem_projections (one_sub_mem_projections hP)
  have h1 : (E * (1 - P)).IsPositive := isPositive_mul_of_commute hEp hP' (by
    rw [mul_sub, sub_mul, mul_one, one_mul, hc])
  have h2 : ((1 - E) * P).IsPositive := isPositive_mul_of_commute hE' hPp (by
    rw [mul_sub, sub_mul, mul_one, one_mul, hc])
  have e1 : ω (E * (1 - P)) = ω E - ω (E * P) := by rw [mul_sub, mul_one, map_sub]
  have e2 : ω ((1 - E) * P) = ω P - ω (E * P) := by rw [sub_mul, one_mul, map_sub]
  have n1 := (ω.map_nonneg' _ h1).2
  have n2 := (ω.map_nonneg' _ h2).2
  rw [e1, Complex.sub_re] at n1
  rw [e2, Complex.sub_re] at n2
  exact ⟨(ω.map_nonneg' _ (isPositive_mul_of_commute hEp hPp hc)).2, by linarith, by linarith,
    (ω.map_nonneg' _ hEp).2, (ω.map_nonneg' _ hPp).2⟩

/-- Finiteness of `K_{r,+}` gives the denominator-free upper event bound for all pairs of
local projections. -/
theorem eventPlus_bound (ω : State H) {𝔄 𝔅 : VonNeumannAlgebra H} (hcomm : Commuting 𝔄 𝔅)
    {r : ℝ} (hr : 1 < r) (hfin : eventConstPlus ω 𝔄 𝔅 r ≠ ⊤) :
    ∀ E ∈ projections 𝔄, ∀ P ∈ projections 𝔅,
      (ω (E * P)).re ^ r
        ≤ (eventConstPlus ω 𝔄 𝔅 r).toReal * ((ω E).re * (ω P).re) ^ (r - 1) := by
  intro E hE P hP
  obtain ⟨hw0, hwE, hwP, hE0, hP0⟩ := projection_cell_facts ω hcomm hE hP
  have hr0 : r ≠ 0 := (lt_trans zero_lt_one hr).ne'
  have hr1 : r - 1 ≠ 0 := (sub_pos.mpr hr).ne'
  by_cases hpos : 0 < (ω E).re * (ω P).re
  · have h1 := le_eventConstPlus ω r hE hP hpos
    rw [ENNReal.ofReal_le_iff_le_toReal hfin] at h1
    have hden : 0 < ((ω E).re * (ω P).re) ^ (r - 1) := Real.rpow_pos_of_pos hpos _
    exact (div_le_iff₀ hden).mp h1
  · have hm : (ω E).re * (ω P).re = 0 := le_antisymm (not_lt.mp hpos) (mul_nonneg hE0 hP0)
    have hw : (ω (E * P)).re = 0 := by
      rcases mul_eq_zero.mp hm with h | h
      · exact le_antisymm (hwE.trans h.le) hw0
      · exact le_antisymm (hwP.trans h.le) hw0
    rw [hw, hm, Real.zero_rpow hr0, Real.zero_rpow hr1]
    simp

/-- Finiteness of `K_{r,-}` gives the denominator-free lower event bound for all pairs of
local projections. -/
theorem eventMinus_bound (ω : State H) {𝔄 𝔅 : VonNeumannAlgebra H} (hcomm : Commuting 𝔄 𝔅)
    {r : ℝ} (hr : 1 < r) (hfin : eventConstMinus ω 𝔄 𝔅 r ≠ ⊤) :
    ∀ E ∈ projections 𝔄, ∀ P ∈ projections 𝔅,
      ((ω E).re * (ω P).re) ^ r
        ≤ (eventConstMinus ω 𝔄 𝔅 r).toReal * (ω (E * P)).re ^ (r - 1) := by
  intro E hE P hP
  obtain ⟨hw0, -, -, hE0, hP0⟩ := projection_cell_facts ω hcomm hE hP
  have hr0 : r ≠ 0 := (lt_trans zero_lt_one hr).ne'
  have hr1 : 0 < r - 1 := sub_pos.mpr hr
  by_cases hpos : 0 < (ω E).re * (ω P).re
  · have h1 := le_eventConstMinus ω r hE hP hpos
    have hnum : 0 < ((ω E).re * (ω P).re) ^ r := Real.rpow_pos_of_pos hpos _
    by_cases hw : (ω (E * P)).re = 0
    · exfalso
      rw [hw, Real.zero_rpow hr1.ne', ENNReal.ofReal_zero,
        ENNReal.div_zero (ENNReal.ofReal_pos.mpr hnum).ne'] at h1
      exact hfin (top_le_iff.mp h1)
    · have hwpos : 0 < (ω (E * P)).re := lt_of_le_of_ne hw0 (Ne.symm hw)
      have hden : 0 < (ω (E * P)).re ^ (r - 1) := Real.rpow_pos_of_pos hwpos _
      rw [← ENNReal.ofReal_div_of_pos hden, ENNReal.ofReal_le_iff_le_toReal hfin] at h1
      exact (div_le_iff₀ hden).mp h1
  · have hm : (ω E).re * (ω P).re = 0 := le_antisymm (not_lt.mp hpos) (mul_nonneg hE0 hP0)
    rw [hm, Real.zero_rpow hr0]
    exact mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg hw0 _)

/-- Identities attain the value `1` (manuscript, after (2.4)). -/
theorem one_mem_chshValues (ω : State H) (𝔄 𝔅 : VonNeumannAlgebra H) :
    (1 : ℝ) ∈ chshValues ω 𝔄 𝔅 := by
  refine ⟨1, one_mem_saContractions 𝔄, 1, one_mem_saContractions 𝔄,
    1, one_mem_saContractions 𝔅, 1, one_mem_saContractions 𝔅, ?_⟩
  have h2 : chshOp (1 : H →L[ℂ] H) 1 1 1 = (2 : ℂ) • (1 : H →L[ℂ] H) := by
    unfold chshOp
    rw [sub_self, mul_zero, add_zero, one_mul, two_smul]
  have h3 : ω (chshOp (1 : H →L[ℂ] H) 1 1 1) = ((2 : ℝ) : ℂ) := by
    rw [h2, map_smul, ω.map_one']
    simp
  rw [h3, Complex.norm_real, Real.norm_eq_abs, abs_two]
  norm_num

/-- The Bell correlation is at least `1`. -/
theorem one_le_bellCorrelation (ω : State H) (𝔄 𝔅 : VonNeumannAlgebra H) :
    1 ≤ bellCorrelation ω 𝔄 𝔅 :=
  le_csSup (bddAbove_chshValues ω 𝔄 𝔅) (one_mem_chshValues ω 𝔄 𝔅)

/-- If all CHSH expectations have modulus at most `2`, the Bell correlation equals `1`. -/
theorem bellCorrelation_eq_one_of_chsh_le (ω : State H) (𝔄 𝔅 : VonNeumannAlgebra H)
    (h : ∀ A₀ ∈ saContractions 𝔄, ∀ A₁ ∈ saContractions 𝔄, ∀ B₀ ∈ saContractions 𝔅,
      ∀ B₁ ∈ saContractions 𝔅, ‖ω (chshOp A₀ A₁ B₀ B₁)‖ ≤ 2) :
    bellCorrelation ω 𝔄 𝔅 = 1 := by
  have hle : ∀ x ∈ chshValues ω 𝔄 𝔅, x ≤ 1 := by
    rintro x ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, rfl⟩
    have h' := h A₀ hA₀ A₁ hA₁ B₀ hB₀ B₁ hB₁
    linarith
  exact le_antisymm (csSup_le ⟨1, one_mem_chshValues ω 𝔄 𝔅⟩ hle) (one_le_bellCorrelation ω 𝔄 𝔅)

/-- Theorem 3.1 of the manuscript, with the reflection-approximation property of the two
algebras as explicit hypotheses `hapA`, `hapB` (intermediate statement). -/
theorem bellCorrelation_eq_one_of_event_constants_of_approx
    (ω : State H) {𝔄 𝔅 : VonNeumannAlgebra H} (hcomm : Commuting 𝔄 𝔅)
    (hapA : saContractions 𝔄 ⊆ closure (convexHull ℝ (reflections 𝔄)))
    (hapB : saContractions 𝔅 ⊆ closure (convexHull ℝ (reflections 𝔅)))
    {rp rm q : ℝ} (hrp : 2 < rp) (hrm : 1 < rm) (hrm2 : rm < 2)
    (hη : 0 < expEta rp rm)
    (hKp : eventConstPlus ω 𝔄 𝔅 rp ≠ ⊤) (hKm : eventConstMinus ω 𝔄 𝔅 rm ≠ ⊤)
    (hcl : ∀ A ∈ saContractions 𝔄, ∀ B ∈ saContractions 𝔅,
      ‖ω (A * B) - ω A * ω B‖ ≤ q)
    (hcut : q ^ expEta rp rm * (eventConstPlus ω 𝔄 𝔅 rp).toReal ^ nuPlus rp rm
        * (eventConstMinus ω 𝔄 𝔅 rm).toReal ^ nuMinus rm
        ≤ (2 : ℝ) ^ (-(2 / (expA rm * expB rp)))) :
    bellCorrelation ω 𝔄 𝔅 = 1 := by
  apply bellCorrelation_eq_one_of_chsh_le
  apply chsh_bound_of_reflections ω hapA hapB
  intro A₀ hA₀ A₁ hA₁ B₀ hB₀ B₁ hB₁
  have h := chshValue_le_one_of_projection_bounds ω hcomm hrp hrm hrm2 hη
    (eventPlus_bound ω hcomm (by linarith) hKp) (eventMinus_bound ω hcomm hrm hKm)
    hcl hcut hA₀ hA₁ hB₀ hB₁
  linarith

end VacuumBellSeparation
