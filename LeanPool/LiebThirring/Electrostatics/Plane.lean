/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.Configuration

/-!
# Affine planar surface measure

Orthonormal affine frames define plane surface measures as pushforwards of planar volume.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace LiebThirring

/-- Euclidean parameter space for an orthonormal plane frame. -/
abbrev Planar := EuclideanSpace ℝ (Fin 2)

/-- The affine plane through `b` with normal `n`, given by its orthogonal direction. -/
noncomputable def affinePlane (n b : Position) : AffineSubspace ℝ Position :=
  AffineSubspace.mk' b (ℝ ∙ n)ᗮ

@[simp] theorem mem_affinePlane (n b x : Position) :
    x ∈ affinePlane n b ↔ inner ℝ n (x - b) = 0 := by
  exact Submodule.mem_orthogonal_singleton_iff_inner_right

instance (n b : Position) : Nonempty (affinePlane n b) :=
  ⟨⟨b, AffineSubspace.self_mem_mk' b (ℝ ∙ n)ᗮ⟩⟩

/-- An orthonormal affine frame onto the indicated affine subspace. -/
abbrev PlaneFrame (H : AffineSubspace ℝ Position) [Nonempty H] :=
  Planar ≃ᵃⁱ[ℝ] H

/-- Build a named affine frame from an orthonormal basis and a point on the plane. -/
noncomputable def planeFrameOfBasis {H : AffineSubspace ℝ Position} [Nonempty H]
    (B : OrthonormalBasis (Fin 2) ℝ H.direction) (p : H) : PlaneFrame H :=
  B.repr.symm.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ p)

/-- A nonzero normal gives a two-dimensional affine plane. -/
theorem finrank_affinePlane_direction (n b : Position) (hn : n ≠ 0) :
    Module.finrank ℝ (affinePlane n b).direction = 2 := by
  change Module.finrank ℝ (AffineSubspace.mk' b (ℝ ∙ n)ᗮ).direction = 2
  rw [AffineSubspace.direction_mk']
  let : Fact (Module.finrank ℝ Position = 2 + 1) := ⟨finrank_euclideanSpace⟩
  exact Submodule.finrank_orthogonal_span_singleton hn

/-- An orthonormal affine frame exists for every plane with nonzero normal. -/
theorem nonempty_planeFrame (n b : Position) (hn : n ≠ 0) :
    Nonempty (PlaneFrame (affinePlane n b)) := by
  let B := (stdOrthonormalBasis ℝ (affinePlane n b).direction).reindex
    (Fin.castOrderIso (finrank_affinePlane_direction n b hn)).toEquiv
  exact ⟨planeFrameOfBasis B ⟨b, AffineSubspace.self_mem_mk' b (ℝ ∙ n)ᗮ⟩⟩

/-- Surface measure in a named orthonormal affine frame. -/
noncomputable def planeMeasure {H : AffineSubspace ℝ Position} [Nonempty H]
    (F : PlaneFrame H) : Measure Position :=
  Measure.map (Subtype.val ∘ F) volume

/-- Affine Euclidean isometries preserve planar Lebesgue measure, including translations. -/
theorem measurePreserving_planar_affineIsometry (e : Planar ≃ᵃⁱ[ℝ] Planar) :
    MeasurePreserving e volume volume := by
  have h := (measurePreserving_add_right (volume : Measure Planar) (e 0)).comp
    e.linearIsometryEquiv.measurePreserving
  convert h using 1
  funext x
  change e x = e.linearIsometryEquiv x + e 0
  simpa only [vadd_eq_add, add_zero] using (e.map_vadd (0 : Planar) x)

/-- Changing the orthonormal frame and its origin does not change surface measure. -/
theorem planeMeasure_eq {H : AffineSubspace ℝ Position} [Nonempty H]
    (F G : PlaneFrame H) : planeMeasure F = planeMeasure G := by
  let e := F.trans G.symm
  have he := (measurePreserving_planar_affineIsometry e).map_eq
  have hG : Measurable (Subtype.val ∘ G) :=
    continuous_subtype_val.measurable.comp G.continuous.measurable
  have hcomp : (Subtype.val ∘ G) ∘ e = Subtype.val ∘ F := by
    funext q
    exact congrArg Subtype.val (G.apply_symm_apply (F q))
  unfold planeMeasure
  rw [← hcomp, ← Measure.map_map hG e.continuous.measurable, he]

/-- Integration against the planar surface measure is integration in its frame. -/
theorem lintegral_planeMeasure {H : AffineSubspace ℝ Position} [Nonempty H]
    (F : PlaneFrame H) (h : Position → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ x, h x ∂planeMeasure F = ∫⁻ q, h (F q : Position) := by
  exact lintegral_map hh (continuous_subtype_val.measurable.comp F.continuous.measurable)

end LiebThirring

end
