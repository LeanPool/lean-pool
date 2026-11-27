/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Uniqueness

/-!
# Unitary equivalence from actual cyclic Gram data

The linear map on finite combinations is extended by the proved norm
identity. Density of both actual families proves surjectivity. The generic
lemma keeps both density obligations explicit; it does not give cyclicity
or representation equivalence to a physical subsystem by assumption.
-/

@[expose] public section

open scoped InnerProductSpace

namespace VacuumBellSeparation

variable {ι H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
theorem denseRange_linearCombination_of_dense_span (v : ι → H)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    DenseRange (Finsupp.linearCombination ℂ v) := by
  have hd : Dense ((Submodule.span ℂ (Set.range v) : Submodule ℂ H) : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hv
  apply Dense.mono ?_ hd
  intro x hx
  have hm : x ∈ LinearMap.range (Finsupp.linearCombination ℂ v) := by
    rw [Finsupp.range_linearCombination]
    exact hx
  exact LinearMap.mem_range.mp hm

theorem exists_unitary_equiv_of_dense_gram (v : ι → H) (w : ι → K)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (hw : (Submodule.span ℂ (Set.range w)).topologicalClosure = ⊤)
    (hgram : ∀ i j, ⟪v i, v j⟫_ℂ = ⟪w i, w j⟫_ℂ) :
    ∃ U : H ≃ₗᵢ[ℂ] K, ∀ i, U (v i) = w i := by
  have hdv := denseRange_linearCombination_of_dense_span v hv
  have hdw := denseRange_linearCombination_of_dense_span w hw
  have hn (c : ι →₀ ℂ) :
      ‖Finsupp.linearCombination ℂ w c‖ = ‖Finsupp.linearCombination ℂ v c‖ := by
    have he := inner_linearCombination_eq_of_inner_eq v w hgram c c
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), he]
  let U : H →ₗᵢ[ℂ] K := (Finsupp.linearCombination ℂ w).extendOfIsometry hdv hn
  have he (c : ι →₀ ℂ) : U (Finsupp.linearCombination ℂ v c) =
      Finsupp.linearCombination ℂ w c :=
    LinearMap.extendOfIsometry_eq _ hdv hn c
  have hsurj : Function.Surjective U := by
    have hc := U.isometry.isClosedEmbedding.isClosed_range
    have hs : Set.range (Finsupp.linearCombination ℂ w) ⊆ Set.range U := by
      rintro _ ⟨c, rfl⟩
      exact ⟨Finsupp.linearCombination ℂ v c, he c⟩
    have hcl := closure_minimal hs hc
    rw [hdw.closure_range] at hcl
    intro y
    exact hcl (Set.mem_univ y)
  refine ⟨LinearIsometryEquiv.ofSurjective U hsurj, fun i => ?_⟩
  simpa only [LinearIsometryEquiv.coe_ofSurjective,
    Finsupp.linearCombination_single, one_smul] using he (Finsupp.single i 1)

omit [CompleteSpace H] [CompleteSpace K] in
/-- Equality on the actual cyclic family determines the intertwining relation. -/
theorem cyclic_unitary_intertwines (v : ι → H)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (U : H ≃ₗᵢ[ℂ] K) (A : H →L[ℂ] H) (B : K →L[ℂ] K)
    (h : ∀ i, U (A (v i)) = B (U (v i))) :
    U.toContinuousLinearEquiv.toContinuousLinearMap.comp A =
      B.comp U.toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr hv)
  rintro _ ⟨i, rfl⟩
  exact h i

end VacuumBellSeparation
