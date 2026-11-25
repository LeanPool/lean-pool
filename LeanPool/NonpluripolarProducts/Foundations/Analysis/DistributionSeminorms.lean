/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Distribution.Distribution

/-! # Seminorm bounds for distributions on a fixed compact support -/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped Distributions NNReal

namespace SGPT.Foundations.Analysis.Pending

/-- On a fixed compact set, a distribution is controlled by finitely many of the
standard derivative seminorms on smooth functions supported in that compact set. -/
theorem exists_finite_seminorm_bound_on_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (K : Compacts E)
    (hKΩ : (K : Set E) ⊆ Ω) :
    ∃ (s : Finset ℕ) (C : ℝ≥0), C ≠ 0 ∧
      ∀ φ : ContDiffMapSupportedIn E ℝ ⊤ K,
        |T (TestFunction.ofSupportedIn hKΩ φ)| ≤
          (C : ℝ) *
            (s.sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ := by
  let TK := T.comp (TestFunction.ofSupportedInCLM ℝ hKΩ)
  let q : Seminorm ℝ (ContDiffMapSupportedIn E ℝ ⊤ K) :=
    (normSeminorm ℝ ℝ).comp TK.toLinearMap
  have hq : Continuous q := continuous_norm.comp TK.continuous
  obtain ⟨s, C, hC, hbound⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K) q hq
  refine ⟨s, C, hC, fun φ ↦ ?_⟩
  have h := hbound φ
  change |T ((TestFunction.ofSupportedInCLM ℝ hKΩ) φ)| ≤
    (C : ℝ) * (s.sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ
  change |T ((TestFunction.ofSupportedInCLM ℝ hKΩ) φ)| ≤
    (C : ℝ) * (s.sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ at h
  exact h

/-- A distribution has finite order on every fixed compact subset of its domain:
one common derivative order controls its value on all smooth functions supported
in that compact set. -/
theorem exists_finite_order_seminorm_bound_on_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (K : Compacts E)
    (hKΩ : (K : Set E) ⊆ Ω) :
    ∃ (m : ℕ) (C : ℝ≥0), C ≠ 0 ∧
      ∀ φ : ContDiffMapSupportedIn E ℝ ⊤ K,
        |T (TestFunction.ofSupportedIn hKΩ φ)| ≤
          (C : ℝ) *
            ((Finset.Iic m).sup
              (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ := by
  obtain ⟨s, C, hC, hbound⟩ := exists_finite_seminorm_bound_on_compact T K hKΩ
  refine ⟨s.sup id, C, hC, fun φ ↦ (hbound φ).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  have hseminorm :
      s.sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K) ≤
        (Finset.Iic (s.sup id)).sup
          (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K) :=
    Finset.sup_mono s.subset_Iic_sup_id
  exact hseminorm φ

end SGPT.Foundations.Analysis.Pending
