/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.ProbabilityCriterion

/-!
# Reflection quartets and the projection form of the probability criterion

The manuscript's Theorem 3.1 assumes the event bounds only for local *projections*.  For a
quartet of *reflections* (self-adjoint unitaries) the outcome effects `(1 ± A)/2` are
projections, so the criterion applies with projection hypotheses:
`chshValue_le_one_of_projection_bounds`.

The reduction step of the manuscript's proof ("every self-adjoint contraction is a spectral
average of reflections"), which passes from reflection quartets to arbitrary quartets of
self-adjoint contractions, is proved in `VacuumBellSeparation.Bell.ReflectionReduction`,
`VacuumBellSeparation.Bell.SpectralThreshold`, `VacuumBellSeparation.Bell.ReflectionApprox`
and assembled in `VacuumBellSeparation.Bell.Theorem31`.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The reflections (self-adjoint unitaries) of a von Neumann algebra `M`. -/
def reflections (M : VonNeumannAlgebra H) : Set (H →L[ℂ] H) :=
  {A | A ∈ M ∧ IsSelfAdjoint A ∧ A * A = 1}

/-- A self-adjoint operator with `A * A = 1` is a contraction. -/
theorem norm_le_one_of_reflection {A : H →L[ℂ] H} (hsa : IsSelfAdjoint A)
    (hsq : A * A = 1) : ‖A‖ ≤ 1 := by
  have h1 : ‖star A * A‖ = ‖A‖ * ‖A‖ := CStarRing.norm_star_mul_self
  rw [hsa.star_eq, hsq] at h1
  have h2 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)
  by_contra hlt
  have hlt' : 1 < ‖A‖ := lt_of_not_ge hlt
  nlinarith

theorem reflections_subset_saContractions (M : VonNeumannAlgebra H) :
    reflections M ⊆ saContractions M :=
  fun _ hA => ⟨hA.1, hA.2.1, norm_le_one_of_reflection hA.2.1 hA.2.2⟩

theorem neg_mem_reflections {M : VonNeumannAlgebra H} {A : H →L[ℂ] H}
    (hA : A ∈ reflections M) : -A ∈ reflections M :=
  ⟨neg_mem hA.1, hA.2.1.neg, by rw [neg_mul_neg]; exact hA.2.2⟩

theorem one_mem_projections (M : VonNeumannAlgebra H) :
    (1 : H →L[ℂ] H) ∈ projections M :=
  ⟨one_mem M, by simp, mul_one 1⟩

/-- The outcome effects `(1 ± A)/2` of a reflection are projections. -/
theorem outcomeEffect_mem_projections {M : VonNeumannAlgebra H} {A : H →L[ℂ] H}
    (hA : A ∈ reflections M) (α : Bool) : outcomeEffect A α ∈ projections M := by
  have hsa := hA.2.1
  have hsq := hA.2.2
  have hn := norm_le_one_of_reflection hsa hsq
  refine ⟨(outcomeEffect_mem_effects (reflections_subset_saContractions M hA) α).1,
    (outcomeEffect_isPositive hsa hn α).isSelfAdjoint, ?_⟩
  cases α
  · rw [outcomeEffect_false]
    have h : (1 - A) * (1 - A) = (2 : ℂ) • (1 - A) := by
      simp only [two_smul, mul_sub, sub_mul, one_mul, mul_one, hsq]
      abel
    rw [smul_mul_smul_comm, h, smul_smul]
    norm_num
  · rw [outcomeEffect_true]
    have h : (1 + A) * (1 + A) = (2 : ℂ) • (1 + A) := by
      simp only [two_smul, mul_add, add_mul, one_mul, mul_one, hsq]
      abel
    rw [smul_mul_smul_comm, h, smul_smul]
    norm_num

/-- **Theorem 3.1 for reflection quartets (projection form).**  With the event bounds
assumed only for local projections, as in the manuscript, every quartet of local
*reflections* has CHSH value at most `1`. -/
theorem chshValue_le_one_of_projection_bounds
    (ω : State H) {𝔄 𝔅 : VonNeumannAlgebra H} (hcomm : Commuting 𝔄 𝔅)
    {rp rm Kp Km q : ℝ} (hrp : 2 < rp) (hrm : 1 < rm) (_hrm2 : rm < 2)
    (hη : 0 < expEta rp rm)
    (hup : ∀ E ∈ projections 𝔄, ∀ P ∈ projections 𝔅,
      (ω (E * P)).re ^ rp ≤ Kp * ((ω E).re * (ω P).re) ^ (rp - 1))
    (hlow : ∀ E ∈ projections 𝔄, ∀ P ∈ projections 𝔅,
      ((ω E).re * (ω P).re) ^ rm ≤ Km * (ω (E * P)).re ^ (rm - 1))
    (hcl : ∀ A ∈ saContractions 𝔄, ∀ B ∈ saContractions 𝔅,
      ‖ω (A * B) - ω A * ω B‖ ≤ q)
    (hcut : q ^ expEta rp rm * Kp ^ nuPlus rp rm * Km ^ nuMinus rm
        ≤ (2 : ℝ) ^ (-(2 / (expA rm * expB rp))))
    {A₀ A₁ B₀ B₁ : H →L[ℂ] H}
    (hA₀ : A₀ ∈ reflections 𝔄) (hA₁ : A₁ ∈ reflections 𝔄)
    (hB₀ : B₀ ∈ reflections 𝔅) (hB₁ : B₁ ∈ reflections 𝔅) :
    (1 / 2 : ℝ) * ‖ω (chshOp A₀ A₁ B₀ B₁)‖ ≤ 1 := by
  have hKp : (1 : ℝ) ≤ Kp := by
    simpa [ω.map_one'] using hup 1 (one_mem_projections 𝔄) 1 (one_mem_projections 𝔅)
  have hKm : (1 : ℝ) ≤ Km := by
    simpa [ω.map_one'] using hlow 1 (one_mem_projections 𝔄) 1 (one_mem_projections 𝔅)
  exact chshValue_le_one_of_event_bounds ω hcomm (by linarith) hrm hη (by linarith)
    (by linarith) (projections 𝔄) (projections 𝔅) hup hlow hcl hcut
    (reflections_subset_saContractions 𝔄 hA₀) (reflections_subset_saContractions 𝔄 hA₁)
    (reflections_subset_saContractions 𝔅 hB₀) (reflections_subset_saContractions 𝔅 hB₁)
    (fun α => ⟨outcomeEffect_mem_projections hA₀ α, outcomeEffect_mem_projections hA₁ α,
      outcomeEffect_mem_projections (neg_mem_reflections hA₀) α,
      outcomeEffect_mem_projections (neg_mem_reflections hA₁) α⟩)
    (fun β => ⟨outcomeEffect_mem_projections hB₀ β, outcomeEffect_mem_projections hB₁ β⟩)

end VacuumBellSeparation
