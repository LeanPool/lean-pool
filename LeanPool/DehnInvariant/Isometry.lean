/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.PlaneCut
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Tactic.Linarith

/-!
Lean study 2 of the shape-language canon (DICTO, 19 Nov 2026), part E: rigid motions.

`dehnSet_image`: the Dehn invariant of a set is unchanged by every isometry of the space
(rotations, translations, reflections). `IsPoly.image`: the image of a convex polytope is a convex
polytope.
No `sorry`.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma motion_add (g : E ≃ᵃⁱ[ℝ] E) (x w : E) : g (x + w) = g x + g.linearIsometryEquiv w := by
  rw [add_comm x w, add_comm (g x)]
  exact g.map_vadd x w

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tcone_image (g : E ≃ᵃⁱ[ℝ] E) (P : Set E) (x : E) :
    tcone (g '' P) (g x) = g.linearIsometryEquiv '' tcone P x := by
  ext v; constructor
  · rintro ⟨⟨x', hx', hgx⟩, t, ht, ⟨y, hy, hgy⟩⟩
    have hxx : x' = x := g.injective hgx
    subst hxx
    refine ⟨g.linearIsometryEquiv.symm v, ⟨hx', t, ht, ?_⟩,
      g.linearIsometryEquiv.apply_symm_apply v⟩
    have h1 : g (x' + t • g.linearIsometryEquiv.symm v) = g y := by
      rw [motion_add, map_smul, LinearIsometryEquiv.apply_symm_apply, hgy]
    rw [g.injective h1]; exact hy
  · rintro ⟨w, ⟨hx, t, ht, hmem⟩, rfl⟩
    refine ⟨mem_image_of_mem g hx, t, ht, ?_⟩
    have h1 : g x + t • g.linearIsometryEquiv w = g (x + t • w) := by
      rw [motion_add, map_smul]
    rw [h1]; exact mem_image_of_mem g hmem

lemma wedgeAngleIn_image (L : E ≃ₗᵢ[ℝ] E) (T : Set E) (V : Submodule ℝ E) :
    wedgeAngleIn (L '' T) (V.map (L.toLinearEquiv : E →ₗ[ℝ] E)) = wedgeAngleIn T V := by
  let e := LinearIsometryEquiv.submoduleMap V L
  let me : V ≃ᵐ ↥(V.map (L.toLinearEquiv : E →ₗ[ℝ] E)) := e.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving me volume volume := e.measurePreserving
  have hcoe : ∀ w : V, ((me w : ↥(V.map (L.toLinearEquiv : E →ₗ[ℝ] E))) : E) = L (w : E) :=
    fun w => rfl
  have hnorm : ∀ w : V, ‖me w‖ = ‖w‖ := fun w => e.norm_map w
  have h1 : me ⁻¹' {w : ↥(V.map (L.toLinearEquiv : E →ₗ[ℝ] E)) | (w : E) ∈ L '' T ∧ ‖w‖ < 1} =
      {w : V | (w : E) ∈ T ∧ ‖w‖ < 1} := by
    ext w
    change ((me w : ↥(V.map (L.toLinearEquiv : E →ₗ[ℝ] E))) : E) ∈ L '' T ∧ ‖me w‖ < 1 ↔
      (w : E) ∈ T ∧ ‖w‖ < 1
    rw [hcoe, hnorm, L.injective.mem_set_image]
  have h2 : me ⁻¹' Metric.ball (0 : ↥(V.map (L.toLinearEquiv : E →ₗ[ℝ] E))) 1 =
      Metric.ball (0 : V) 1 := by
    ext w
    change me w ∈ Metric.ball (0 : ↥(V.map (L.toLinearEquiv : E →ₗ[ℝ] E)))
        1 ↔ w ∈ Metric.ball (0 : V) 1
    rw [Metric.mem_ball, Metric.mem_ball, dist_zero_right, dist_zero_right, hnorm]
  unfold wedgeAngleIn
  rw [← hmp.measure_preimage_equiv, ← hmp.measure_preimage_equiv (Metric.ball _ _), h1, h2]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma linSpace_image (L : E ≃ₗᵢ[ℝ] E) (T : Set E) :
    linSpace (L '' T) = (linSpace T).map (L.toLinearEquiv : E →ₗ[ℝ] E) := by
  unfold linSpace
  rw [Submodule.map_span]
  congr 1
  ext v; constructor
  · rintro ⟨⟨w, hw, rfl⟩, ⟨w', hw', h⟩⟩
    have h1 : w' = -w := L.injective (by rw [h, map_neg])
    subst h1
    exact ⟨w, ⟨hw, hw'⟩, rfl⟩
  · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨w, h1, rfl⟩, ⟨-w, h2, map_neg _ _⟩⟩

lemma theta_image (L : E ≃ₗᵢ[ℝ] E) (T : Set E) : theta (L '' T) = theta T := by
  unfold theta
  rw [linSpace_image, LinearEquiv.finrank_map_eq]
  by_cases h : finrank ℝ (linSpace T) = 1
  · rw [ite_eq_left h, ite_eq_left h, wedgeAngle_eq_in, wedgeAngle_eq_in,
      ← Submodule.map_orthogonal_equiv, wedgeAngleIn_image]
  · rw [ite_eq_right h, ite_eq_right h]

lemma edgeAngle_image (g : E ≃ᵃⁱ[ℝ] E) (P : Set E) (x : E) :
    edgeAngle (g '' P) (g x) = edgeAngle P x := by
  unfold edgeAngle
  rw [tcone_image, theta_image]

/-- **Rigid motions keep the Dehn invariant.** -/
theorem dehnSet_image (g : E ≃ᵃⁱ[ℝ] E) (P : Set E) : dehnSet (g '' P) = dehnSet P := by
  unfold dehnSet tsum1
  apply finsum_congr; intro θ
  have h : {y | edgeAngle (g '' P) y = θ} = g '' {x | edgeAngle P x = θ} := by
    ext y; constructor
    · intro hy
      refine ⟨g.symm y, ?_, g.apply_symm_apply y⟩
      change edgeAngle P (g.symm y) = θ
      rw [← edgeAngle_image g P (g.symm y), g.apply_symm_apply]; exact hy
    · rintro ⟨x, hx, rfl⟩
      change edgeAngle (g '' P) (g x) = θ
      rw [edgeAngle_image]; exact hx
  rw [h, g.isometry.hausdorffMeasure_image (Or.inl zero_le_one)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The image of a convex polytope under a rigid motion is a convex polytope. -/
lemma IsPoly.image {P : Set E} (hP : IsPoly P) (g : E ≃ᵃⁱ[ℝ] E) : IsPoly (g '' P) := by
  obtain ⟨hb, ι, inst, a, b, rfl⟩ := hP
  refine ⟨?_, ι, inst, fun i => g.linearIsometryEquiv (a i),
    fun i => b i + ⟪g.linearIsometryEquiv (a i), g 0⟫, ?_⟩
  · exact (g.isometry.lipschitzWith.isBounded_image hb)
  · have hkey : ∀ (i : ι) (x : E), ⟪g.linearIsometryEquiv (a i), g x⟫ =
        ⟪a i, x⟫ + ⟪g.linearIsometryEquiv (a i), g 0⟫ := by
      intro i x
      have h1 : g x = g 0 + g.linearIsometryEquiv x := by
        rw [← motion_add, zero_add]
      rw [h1, inner_add_right, LinearIsometryEquiv.inner_map_map, add_comm]
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩ i
      change ⟪g.linearIsometryEquiv (a i), g x⟫ ≤ b i + ⟪g.linearIsometryEquiv (a i), g 0⟫
      rw [hkey]; have := hx i; linarith
    · intro hy
      refine ⟨g.symm y, fun i => ?_, g.apply_symm_apply y⟩
      have h1 : ⟪g.linearIsometryEquiv (a i), g (g.symm y)⟫ ≤
          b i + ⟪g.linearIsometryEquiv (a i), g 0⟫ := by
        rw [g.apply_symm_apply]; exact hy i
      rw [hkey] at h1; linarith

end DehnCanon.Library
