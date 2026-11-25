/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Compactly supported smooth test cutoffs -/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Distributions Manifold Topology

namespace SGPT.Foundations.Analysis.Pending

/-- A compact subset of an open finite-dimensional real vector space admits a
smooth test-function cutoff which equals one on a neighborhood of the compact
set and takes values in `[0, 1]`. -/
theorem exists_testFunction_eq_one_nhds_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Ω : Opens E} {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ χ : 𝓓(Ω, ℝ),
      (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  have hKintV : K ⊆ interior V := by simpa [hVo.interior_eq] using hKV
  obtain ⟨f, hfK, hfV, hfrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (n := (⊤ : ℕ∞)) (𝓘(ℝ, E)) hK.isClosed hKintV
  have hsupp : Function.support f ⊆ V := by
    intro x hx
    by_contra hxV
    exact hx (hfV x hxV)
  let χ : 𝓓(Ω, ℝ) :=
    ⟨f, f.contMDiff.contDiff,
      HasCompactSupport.of_support_subset_isCompact hVc
        (hsupp.trans subset_closure),
      (closure_mono hsupp).trans hVΩ⟩
  exact ⟨χ, hfK, hfrange⟩

end SGPT.Foundations.Analysis.Pending
