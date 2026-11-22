/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Genuine C¹ local extension for coordinate vector fields
A Euclidean bump in finite-dimensional coordinates makes the actual local C¹
field globally C¹ while retaining equality on a neighborhood of its center.
-/

@[expose] public section
open Set Filter Metric Module Function
open scoped Topology

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- An actual C¹ germ has an actual global C¹ extension agreeing near the point. -/
theorem exists_contDiff_one_eventuallyEq_of_contDiffAt
    {F : E → E} {x₀ : E} (hF : ContDiffAt ℝ 1 F x₀) :
    ∃ G : E → E, ContDiff ℝ 1 G ∧ G =ᶠ[𝓝 x₀] F := by
  have hnear : {x | ContDiffAt ℝ 1 F x} ∈ 𝓝 x₀ := hF.eventually (by norm_num)
  obtain ⟨d, hd, hds⟩ := Euclidean.nhds_basis_closedBall.mem_iff.mp hnear
  let χ : ContDiffBump (toEuclidean x₀) :=
    ⟨d / 2, d, half_pos hd, half_lt_self hd⟩
  let φ : E → ℝ := χ ∘ toEuclidean
  have hφ : ContDiff ℝ 1 φ := χ.contDiff.comp (ContinuousLinearEquiv.contDiff _)
  have hsupp : tsupport φ ⊆ Euclidean.closedBall x₀ d := by
    rw [tsupport, ← Euclidean.closure_ball _ hd.ne']
    apply closure_mono
    intro x hx
    have hχ : toEuclidean x ∈ support χ := hx
    rwa [χ.support_eq] at hχ
  let G : E → E := fun x ↦ φ x • F x
  refine ⟨G, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport φ
    · exact (hφ.contDiffAt.smul (hds (hsupp hx)))
    · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [G, hy]
  · have hball : ∀ᶠ x in 𝓝 x₀, x ∈ Euclidean.closedBall x₀ (d / 2) :=
      Euclidean.nhds_basis_closedBall.mem_iff.mpr ⟨d / 2, half_pos hd, Subset.rfl⟩
    filter_upwards [hball] with x hx
    have hχ : χ (toEuclidean x) = 1 := χ.one_of_mem_closedBall hx
    simp [G, φ, Function.comp_apply, hχ]

end CutoffRigidity
