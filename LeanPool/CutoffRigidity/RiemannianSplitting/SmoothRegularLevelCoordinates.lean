/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.SmoothImplicitChart
public import LeanPool.CutoffRigidity.RiemannianSplitting.BoundarylessChart

/-! # Smooth scalar product coordinates inside an actual manifold chart -/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ E]
  [IsManifold I 2 M]
  [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The scalar chart representative has the same finite regularity at the chart center. -/
theorem contDiffAt_chartScalar_finite {n : ℕ} (x : M) {f : M → ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) n f x) :
    ContDiffAt ℝ n (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  have hRange : range I ∈ 𝓝 (extChartAt I x x) := range_mem_nhds_isInteriorPoint
    (BoundarylessManifold.isInteriorPoint (I := I) (x := x))
  have hi := (contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := n) x).contMDiffAt hRange
  have hf' : ContMDiffAt I 𝓘(ℝ, ℝ) n f ((extChartAt I x).symm (extChartAt I x x)) := by
    simpa only [extChartAt_to_inv] using hf
  exact (hf'.comp _ hi).contDiffAt

omit [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The actual scalar IFT coordinates may be chosen smooth in both directions
and entirely inside the actual manifold chart target. -/
theorem exists_finiteSmooth_regularScalar_coordinates {n : ℕ} (x : M) {f : M → ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) n f x) (hn0 : n ≠ 0)
    (X : (y : M) → TangentSpace I y) (hne : mvfderiv I f x (X x) ≠ 0) :
    ∃ e : OpenPartialHomeomorph E (ℝ ×
        (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)).ker),
      (extChartAt I x x) ∈ e.source ∧
      e.source ⊆ (extChartAt I x).target ∧
      e (extChartAt I x x) = (f x, 0) ∧
      (∀ z, (e z).1 = f ((extChartAt I x).symm z)) ∧
      ContDiffOn ℝ n e e.source ∧ ContDiffOn ℝ n e.symm e.target := by
  obtain ⟨e, he, he0, heFirst, hforward, hbackward⟩ :=
    exists_contDiff_regularScalar_coordinates (contDiffAt_chartScalar_finite x hf) hn0
      (surjective_fderiv_chartScalar x (hf.mdifferentiableAt (by exact_mod_cast hn0)) X hne)
  have ht := isOpen_extChartAt_target_of_boundarylessManifold (I := I) x
  let c := e.restrOpen (extChartAt I x).target ht
  have hsrc : c.source = e.source ∩ (extChartAt I x).target :=
    e.restrOpen_source _ ht
  have hraw : (c : E → _) = e := e.coe_restrOpen ht
  have hinv : (c.symm : _ → E) = e.symm := e.coe_restrOpen_symm ht
  refine ⟨c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsrc]
    exact ⟨he, mem_extChartAt_target x⟩
  · rw [hsrc]
    exact inter_subset_right
  · rw [hraw]
    simpa only [Function.comp_apply, extChartAt_to_inv] using he0
  · intro z
    rw [hraw]
    exact heFirst z
  · rw [hraw]
    apply hforward.mono
    rw [hsrc]
    exact inter_subset_left
  · rw [hinv]
    apply hbackward.mono
    intro y hy
    have hxy := c.map_target hy
    rw [hsrc] at hxy
    have hpoint : e (c.symm y) = y := by rw [← hraw]; exact c.right_inv hy
    rw [← hpoint]
    have hxy' : c.symm y ∈ e.source := hxy.1
    exact e.map_source hxy'

omit [FiniteDimensional ℝ E]
  [IsManifold I 2 M]
  [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The `C¹` specialization of the actual scalar chart regularity theorem. -/
theorem contDiffAt_chartScalar (x : M) {f : M → ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f x) :
    ContDiffAt ℝ 1 (f ∘ (extChartAt I x).symm) (extChartAt I x x) :=
  contDiffAt_chartScalar_finite x hf

omit [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The `C¹` specialization of the constructed smooth scalar coordinates. -/
theorem exists_smooth_regularScalar_coordinates (x : M) {f : M → ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f x)
    (X : (y : M) → TangentSpace I y) (hne : mvfderiv I f x (X x) ≠ 0) :
    ∃ e : OpenPartialHomeomorph E (ℝ ×
        (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)).ker),
      (extChartAt I x x) ∈ e.source ∧
      e.source ⊆ (extChartAt I x).target ∧
      e (extChartAt I x x) = (f x, 0) ∧
      (∀ z, (e z).1 = f ((extChartAt I x).symm z)) ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target := by
  exact exists_finiteSmooth_regularScalar_coordinates x hf one_ne_zero X hne

end CutoffRigidity
