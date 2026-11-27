/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FaithfulPowerDomain
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianRenyiParameters

/-!
# The actual sandwiched Rényi power-trace quantity

For r>1 and a faithful positive reference, the inverse-range form has at
most one bounded extension. Its extended positive r-th power trace is the
sandwiched Rényi quantity. If no bounded positive extension exists the
value is infinity. A positive extension is not required to be trace class:
its r-th power may be trace class even when the extension is not.

The infimum definition below is total; its interpretation and uniqueness
theorems have the stated faithful-reference and r>1 hypotheses. The range
form theorem identifies the factorization with actual inverse powers on
their dense range, never with a total bounded inverse of the density.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Sandwiched Rényi quantity. -/
def sandwichedRenyiQuantity (ρ σ : E →L[ℂ] E) (r : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ Θ : E →L[ℂ] E, 0 ≤ Θ ∧
    σ ^ (gaussianRenyiTau r / 2) * Θ * σ ^ (gaussianRenyiTau r / 2) = ρ ∧
    positiveTrace (Θ ^ r) = t}

theorem sandwichedRenyiQuantity_eq_power_trace
    {ρ σ Θ : E →L[ℂ] E} (hσ : IsFaithfulDensity σ) {r : ℝ} (hr : 1 < r)
    (hΘ : 0 ≤ Θ)
    (hf : σ ^ (gaussianRenyiTau r / 2) * Θ * σ ^ (gaussianRenyiTau r / 2) = ρ) :
    sandwichedRenyiQuantity ρ σ r = positiveTrace (Θ ^ r) := by
  have hset : {t | ∃ Ξ : E →L[ℂ] E, 0 ≤ Ξ ∧
      σ ^ (gaussianRenyiTau r / 2) * Ξ * σ ^ (gaussianRenyiTau r / 2) = ρ ∧
      positiveTrace (Ξ ^ r) = t} = {positiveTrace (Θ ^ r)} := by
    ext t
    constructor
    · rintro ⟨Ξ, hΞ, hΞf, ht⟩
      have heq : Ξ = Θ := faithful_power_sandwich_unique hσ
        (half_pos (gaussianRenyiTau_pos hr)) (hΞf.trans hf.symm)
      simpa only [Set.mem_singleton_iff, ← heq] using ht.symm
    · intro ht
      exact ⟨Θ, hΘ, hf, (Set.mem_singleton_iff.mp ht).symm⟩
  unfold sandwichedRenyiQuantity
  rw [hset, sInf_singleton]

theorem sandwichedRenyiQuantity_eq_top_of_no_extension
    {ρ σ : E →L[ℂ] E} {r : ℝ}
    (h : ¬ ∃ Θ : E →L[ℂ] E, 0 ≤ Θ ∧
      σ ^ (gaussianRenyiTau r / 2) * Θ * σ ^ (gaussianRenyiTau r / 2) = ρ) :
    sandwichedRenyiQuantity ρ σ r = ⊤ := by
  unfold sandwichedRenyiQuantity
  have he : {t | ∃ Θ : E →L[ℂ] E, 0 ≤ Θ ∧
      σ ^ (gaussianRenyiTau r / 2) * Θ * σ ^ (gaussianRenyiTau r / 2) = ρ ∧
      positiveTrace (Θ ^ r) = t} = (∅ : Set ℝ≥0∞) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro t ⟨Θ, hΘ, hf, _⟩
    exact h ⟨Θ, hΘ, hf⟩
  rw [he, sInf_empty]

theorem faithful_sandwich_factorization_iff_inverse_form
    {ρ σ : E →L[ℂ] E} (hσ : IsFaithfulDensity σ) {r : ℝ} (hr : 1 < r)
    (Θ : E →L[ℂ] E) :
    σ ^ (gaussianRenyiTau r / 2) * Θ * σ ^ (gaussianRenyiTau r / 2) = ρ ↔
      ∀ x y : operatorInverseRange (σ ^ (gaussianRenyiTau r / 2)),
        inner ℂ (x : E) (Θ (y : E)) =
          inverseSandwichRangeForm (σ ^ (gaussianRenyiTau r / 2))
            (positive_rpow_injective hσ.1 hσ.2.2 (half_pos (gaussianRenyiTau_pos hr))) ρ x y :=
  sandwich_factorization_iff_range_form _ _ (CFC.rpow_nonneg (a := σ)
    (y := gaussianRenyiTau r / 2)).isSelfAdjoint _ _

end VacuumBellSeparation.Gaussian
