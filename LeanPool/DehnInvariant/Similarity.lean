/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.CubeAndTetrahedron
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Positivity

/-!
Lean study 4 of the shape-language canon (DICTO, 19 Nov 2026), part K: size and position.

`dehnSet_smul_set`: scaling a set by a factor `a > 0` multiplies its Dehn invariant by `a` (every
edge length
is multiplied by `a`, every angle is unchanged). With `dehnSet_image` of study 2 (rigid motions)
this gives the
Dehn invariant of every similar copy of a set (`dehnSet_similarCopy`), and Dehn's theorem of study
3 for the
regular tetrahedron and the cube in any size and any position
(`similarTetra_not_scissorsCongruent_similarCube`).

Credits: Mathlib `MeasureTheory.Measure.hausdorffMeasure_smul₀` (Hausdorff measure under scaling),
`smul_finsum`, `TensorProduct.smul_tmul'`.
No `sorry`.
-/

@[expose] public section

open scoped RealInnerProductSpace Pointwise
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Scaling about the origin does not change the cone of directions at a point. -/
lemma tcone_smul_set {a : ℝ} (ha : 0 < a) (P : Set E) (x : E) :
    tcone (a • P) (a • x) = tcone P x := by
  ext v
  have h1 : a • x ∈ a • P ↔ x ∈ P := Set.smul_mem_smul_set_iff₀ ha.ne' _ _
  constructor
  · rintro ⟨hx, t, ht, hmem⟩
    refine ⟨h1.1 hx, t / a, div_pos ht ha, ?_⟩
    have h2 : a • x + t • v = a • (x + (t / a) • v) := by
      rw [smul_add, smul_smul, mul_div_cancel₀ _ ha.ne']
    rw [h2] at hmem
    exact (Set.smul_mem_smul_set_iff₀ ha.ne' _ _).1 hmem
  · rintro ⟨hx, t, ht, hmem⟩
    refine ⟨h1.2 hx, a * t, mul_pos ha ht, ?_⟩
    have h2 : a • x + (a * t) • v = a • (x + t • v) := by
      rw [smul_add, smul_smul]
    rw [h2]; exact Set.smul_mem_smul_set hmem

/-- Scaling does not change the angle class at a point. -/
lemma edgeAngle_smul_set {a : ℝ} (ha : 0 < a) (P : Set E) (x : E) :
    edgeAngle (a • P) (a • x) = edgeAngle P x := by
  unfold edgeAngle; rw [tcone_smul_set ha]

/-- **Scaling.** The Dehn invariant of the set `P` scaled by `a > 0` is `a` times the Dehn
invariant of `P`:
lengths are multiplied by `a`, angles are unchanged. (`a` acts on the length factor of ℝ ⊗[ℚ]
(ℝ/ℚπ).) -/
theorem dehnSet_smul_set {a : ℝ} (ha : 0 < a) (P : Set E) : dehnSet (a • P) = a • dehnSet P := by
  unfold dehnSet
  rw [smul_finsum]
  apply finsum_congr; intro θ
  have h : {y | edgeAngle (a • P) y = θ} = a • {x | edgeAngle P x = θ} := by
    ext y; constructor
    · intro hy
      refine ⟨a⁻¹ • y, ?_, smul_inv_smul₀ ha.ne' y⟩
      change edgeAngle P (a⁻¹ • y) = θ
      rw [← edgeAngle_smul_set ha P, smul_inv_smul₀ ha.ne']; exact hy
    · rintro ⟨x, hx, rfl⟩
      change edgeAngle (a • P) (a • x) = θ
      rw [edgeAngle_smul_set ha]; exact hx
  rw [h, Measure.hausdorffMeasure_smul₀ zero_le_one ha.ne', TensorProduct.smul_tmul']
  congr 1
  rw [NNReal.rpow_one, ENNReal.toReal_smul, NNReal.smul_def, coe_nnNorm, Real.norm_eq_abs,
    abs_of_pos ha]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A scaled convex polytope is a convex polytope. -/
lemma IsPoly.smul_set {P : Set E} (hP : IsPoly P) {a : ℝ} (ha : 0 < a) : IsPoly (a • P) := by
  obtain ⟨hb, ι, inst, n, b, rfl⟩ := hP
  refine ⟨hb.smul₀ a, ι, inst, n, fun i => a * b i, ?_⟩
  ext y; constructor
  · rintro ⟨x, hx, rfl⟩ i
    change ⟪n i, a • x⟫ ≤ a * b i
    rw [inner_smul_right]; exact mul_le_mul_of_nonneg_left (hx i) ha.le
  · intro hy
    refine ⟨a⁻¹ • y, fun i => ?_, smul_inv_smul₀ ha.ne' y⟩
    have h1 : ⟪n i, y⟫ ≤ a * b i := hy i
    rw [inner_smul_right, inv_mul_le_iff₀ ha]; exact h1

/-- `Q` is a similar copy of `P`: `P` scaled by a factor `a > 0` and then moved by an isometry of
the space
(rotation, translation, reflection). Any size, any position. -/
def IsSimilarCopy (P Q : Set E) : Prop := ∃ a : ℝ, 0 < a ∧ ∃ g : E ≃ᵃⁱ[ℝ] E, Q = g '' (a • P)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma isSimilarCopy_refl (P : Set E) : IsSimilarCopy P P :=
  ⟨1, one_pos, AffineIsometryEquiv.refl ℝ E, by simp⟩

/-- The Dehn invariant of a similar copy: that of the original times the scale factor. -/
theorem dehnSet_similarCopy {P Q : Set E} (h : IsSimilarCopy P Q) :
    ∃ a : ℝ, 0 < a ∧ dehnSet Q = a • dehnSet P := by
  obtain ⟨a, ha, g, rfl⟩ := h
  exact ⟨a, ha, by rw [dehnSet_image, dehnSet_smul_set ha]⟩

/-- A similar copy has Dehn invariant zero exactly when the original has. -/
theorem dehnSet_similarCopy_eq_zero_iff {P Q : Set E} (h : IsSimilarCopy P Q) :
    dehnSet Q = 0 ↔ dehnSet P = 0 := by
  obtain ⟨a, ha, hQ⟩ := dehnSet_similarCopy h
  rw [hQ]
  constructor
  · intro h0
    have h1 := congrArg (fun D => a⁻¹ • D) h0
    simpa [inv_smul_smul₀ ha.ne'] using h1
  · intro h0; rw [h0, smul_zero]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma IsPoly.similarCopy {P Q : Set E} (hP : IsPoly P) (h : IsSimilarCopy P Q) : IsPoly Q := by
  obtain ⟨a, ha, g, rfl⟩ := h
  exact (hP.smul_set ha).image g

/-- Convex polytopes one of which has Dehn invariant zero and the other not are not scissors
congruent,
and the same holds for all their similar copies. -/
theorem not_scissorsCongruent_similarCopies [Fact (finrank ℝ E = 3)] {P Q P' Q' : Set E}
    (hP : IsPoly P) (hQ : IsPoly Q) (hPne : dehnSet P ≠ 0) (hQ0 : dehnSet Q = 0)
    (hP' : IsSimilarCopy P P') (hQ' : IsSimilarCopy Q Q') : ¬ ScissorsCongruent P' Q' := by
  apply not_scissorsCongruent_of_dehnSet_ne (hP.similarCopy hP') (hQ.similarCopy hQ')
  rw [(dehnSet_similarCopy_eq_zero_iff hQ').2 hQ0]
  exact fun h => hPne ((dehnSet_similarCopy_eq_zero_iff hP').1 h)

/-- The Dehn invariant of the model tetrahedron of study 3 is not zero. -/
theorem dehnSet_tetra_ne_zero : dehnSet tetraSet ≠ 0 := by
  rw [dehnSet_tetra]; exact dehn_tetrahedron_ne_zero (by positivity)

/-- **Dehn's theorem, any size and any position.** No similar copy of the regular tetrahedron
`tetraSet`
(corners (−1,−1,−1), (1,1,−1), (1,−1,1), (−1,1,1)) is scissors congruent to a similar copy of the
cube
`[-1, 1]³`. Here "a regular tetrahedron" and "a cube" mean: a similar copy of these two models. -/
theorem similarTetra_not_scissorsCongruent_similarCube {T Q : Set R3}
    (hT : IsSimilarCopy tetraSet T) (hQ : IsSimilarCopy (cubeSet 1) Q) : ¬ ScissorsCongruent T Q :=
  not_scissorsCongruent_similarCopies isPoly_tetra (isPoly_cube 1) dehnSet_tetra_ne_zero
    (dehnSet_cube 1 one_pos) hT hQ

end DehnCanon.Library
