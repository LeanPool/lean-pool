/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTrace

/-!
# Unitary transport of the actual positive trace

Mathlib's conjugation star-algebra equivalence transports actual bounded
operators between Hilbert spaces. Basis transport proves invariance of the
extended positive trace; faithfulness and genuine CFC powers also transport.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

variable {E F ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Transported Hilbert basis obtained from `HilbertBasis.ofRepr`. -/
noncomputable def transportedHilbertBasis (b : HilbertBasis ι ℂ E) (e : E ≃ₗᵢ[ℂ] F) :
    HilbertBasis ι ℂ F := HilbertBasis.ofRepr (e.symm.trans b.repr)

omit [CompleteSpace E] [CompleteSpace F] in
@[simp]
theorem transportedHilbertBasis_apply (b : HilbertBasis ι ℂ E) (e : E ≃ₗᵢ[ℂ] F) (i : ι) :
    transportedHilbertBasis b e i = e (b i) := rfl

theorem positiveTrace_conjStarAlgEquiv (e : E ≃ₗᵢ[ℂ] F) {A : E →L[ℂ] E}
    (hA : 0 ≤ A) : positiveTrace (e.conjStarAlgEquiv A) = positiveTrace A := by
  obtain ⟨s, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := E)
  rw [positiveTrace_eq_tsum_diagonal (transportedHilbertBasis b e)
    (map_nonneg e.conjStarAlgEquiv hA), positiveTrace_eq_tsum_diagonal b hA]
  apply tsum_congr
  intro i
  simp only [transportedHilbertBasis_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    e.symm_apply_apply, e.inner_map_map]

theorem IsPositiveTraceClass.conjStarAlgEquiv (e : E ≃ₗᵢ[ℂ] F) {A : E →L[ℂ] E}
    (hA : IsPositiveTraceClass A) : IsPositiveTraceClass (e.conjStarAlgEquiv A) := by
  refine ⟨map_nonneg e.conjStarAlgEquiv hA.1, ?_⟩
  rw [positiveTrace_conjStarAlgEquiv e hA.1]
  exact hA.2

theorem IsFaithfulDensity.conjStarAlgEquiv (e : E ≃ₗᵢ[ℂ] F) {A : E →L[ℂ] E}
    (hA : IsFaithfulDensity A) : IsFaithfulDensity (e.conjStarAlgEquiv A) := by
  refine ⟨map_nonneg e.conjStarAlgEquiv hA.1, ?_, ?_⟩
  · rw [positiveTrace_conjStarAlgEquiv e hA.1, hA.2.1]
  · intro x y hxy
    apply e.symm.injective
    apply hA.2.2
    apply e.injective
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] using hxy

theorem conjStarAlgEquiv_rpow (e : E ≃ₗᵢ[ℂ] F) {A : E →L[ℂ] E}
    (hA : 0 ≤ A) {τ : ℝ} (hτ : 0 ≤ τ) :
    e.conjStarAlgEquiv (A ^ τ) = (e.conjStarAlgEquiv A) ^ τ := by
  have hmap : 0 ≤ e.conjStarAlgEquiv A := map_nonneg e.conjStarAlgEquiv hA
  rw [CFC.rpow_eq_cfc_real hA, CFC.rpow_eq_cfc_real hmap]
  exact StarAlgHomClass.map_cfc e.conjStarAlgEquiv (fun x : ℝ => x ^ τ) A
    (Real.continuous_rpow_const hτ).continuousOn (by
      change Continuous (fun T : E →L[ℂ] E =>
        e.toContinuousLinearEquiv.toContinuousLinearMap ∘L T ∘L
          e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
      fun_prop)
    hA.isSelfAdjoint hmap.isSelfAdjoint

theorem positiveTrace_conjStarAlgEquiv_rpow (e : E ≃ₗᵢ[ℂ] F)
    {A : E →L[ℂ] E} (hA : 0 ≤ A) {τ : ℝ} (hτ : 0 ≤ τ) :
    positiveTrace ((e.conjStarAlgEquiv A) ^ τ) = positiveTrace (A ^ τ) := by
  rw [← conjStarAlgEquiv_rpow e hA hτ]
  exact positiveTrace_conjStarAlgEquiv e CFC.rpow_nonneg

end VacuumBellSeparation.Gaussian
