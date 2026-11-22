/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
public import Mathlib.Tactic.Linarith

/-! # Gluing actual integral curves on a union of centered intervals
Actual manifold ODE uniqueness supplies every overlap identification.
-/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [T2Space M] [BoundarylessManifold I M]

/-- Arbitrarily indexed local solutions with one initial point glue to an
actual solution on the union of their centered open intervals. -/
theorem exists_isMIntegralCurveOn_iUnion
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    {ι : Type*} [Nonempty ι] (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (γ : ι → ℝ → M) {x : M} (hzero : ∀ i, γ i 0 = x)
    (hγ : ∀ i, IsMIntegralCurveOn (γ i) X (Ioo (-r i) (r i))) :
    ∃ Γ : ℝ → M, Γ 0 = x ∧
      IsMIntegralCurveOn Γ X (⋃ i, Ioo (-r i) (r i)) ∧
      ∀ i, EqOn Γ (γ i) (Ioo (-r i) (r i)) := by
  classical
  let U := ⋃ i, Ioo (-r i) (r i)
  have hchoose (t : ℝ) (ht : t ∈ U) : ∃ i, t ∈ Ioo (-r i) (r i) := mem_iUnion.mp ht
  let Γ : ℝ → M := fun t ↦ if ht : t ∈ U then γ (hchoose t ht).choose t else x
  have heq (i : ι) : EqOn Γ (γ i) (Ioo (-r i) (r i)) := by
    intro t ht
    have hU : t ∈ U := mem_iUnion.mpr ⟨i, ht⟩
    rw [show Γ t = γ (hchoose t hU).choose t by simp [Γ, hU]]
    let j := (hchoose t hU).choose
    have hj : t ∈ Ioo (-r j) (r j) := (hchoose t hU).choose_spec
    rcases le_total (r i) (r j) with hij | hji
    · exact (isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        (t₀ := 0) ⟨by linarith [hr i], hr i⟩ hX
        ((hγ j).mono (Ioo_subset_Ioo (neg_le_neg hij) hij)) (hγ i)
        ((hzero j).trans (hzero i).symm)) ht
    · exact (isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        (t₀ := 0) ⟨by linarith [hr j], hr j⟩ hX
        (hγ j) ((hγ i).mono (Ioo_subset_Ioo (neg_le_neg hji) hji))
        ((hzero j).trans (hzero i).symm)) hj
  refine ⟨Γ, ?_, ?_, heq⟩
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact (heq i ⟨by linarith [hr i], hr i⟩).trans (hzero i)
  · intro t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    apply HasMFDerivAt.hasMFDerivWithinAt
    apply HasMFDerivAt.congr_of_eventuallyEq_abuse (f := γ i)
    · rw [heq i hi]
      exact ((hγ i) t hi).hasMFDerivAt (Ioo_mem_nhds hi.1 hi.2)
    · exact Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Ioo (-r i) (r i), Ioo_mem_nhds hi.1 hi.2, heq i⟩

end CutoffRigidity
