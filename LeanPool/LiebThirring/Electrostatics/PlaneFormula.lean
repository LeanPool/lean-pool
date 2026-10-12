/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import LeanPool.LiebThirring.Electrostatics.PlaneCofactor

/-!
# Plane projection integration formula

Coordinate formulas for nonnegative extended integration on affine planes.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace LiebThirring

/-- The inverse coordinate projection chart is a closed embedding into ambient space. -/
theorem isClosedEmbedding_planeGraph (n b : Position) (a : Fin 3) (ha : n a ≠ 0) :
    Topology.IsClosedEmbedding (planeGraph n b a ha) := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    exact ha rfl
  obtain ⟨F⟩ := nonempty_planeFrame n b hn
  let e := planeProjectionChart n b a ha F
  have hfun : planeGraph n b a ha = Subtype.val ∘ (F ∘ e.symm) := by
    funext q
    exact (planeProjectionChart_symm_frame n b a ha F q).symm
  rw [hfun]
  exact (affinePlane n b).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.comp
    (F.toHomeomorph.isClosedEmbedding.comp
      (AffineEquiv.toContinuousAffineEquiv e.symm).toHomeomorph.isClosedEmbedding)

/-- The plane surface measure equals the explicit graph pushforward times the inverse
absolute normal coordinate. -/
theorem planeMeasure_eq_projection_map (n b : Position) (hn : ‖n‖ = 1)
    (a : Fin 3) (ha : n a ≠ 0) (F : PlaneFrame (affinePlane n b)) :
    planeMeasure F = ENNReal.ofReal (|n a|⁻¹) • Measure.map (planeGraph n b a ha) volume := by
  let e := planeProjectionChart n b a ha F
  have he : Measure.map (e : Planar → Planar) volume =
      ENNReal.ofReal (|n a|⁻¹) • volume := by
    rw [map_planar_affineEquiv_volume, abs_inv]
    rw [abs_det_planeProjectionChart n b hn a ha F]
  have hcomp : planeGraph n b a ha ∘ (e : Planar → Planar) = Subtype.val ∘ F := by
    funext q
    exact planeGraph_planeProjection n b a ha (F q) (F q).property
  have hg := (isClosedEmbedding_planeGraph n b a ha).continuous.measurable
  have hem : Measurable (e : Planar → Planar) := e.continuous_of_finiteDimensional.measurable
  rw [planeMeasure, ← hcomp, ← Measure.map_map hg hem, he, Measure.map_smul _ hg.aemeasurable]

/-- Real integrability on the plane is exactly integrability in the coordinate projection chart. -/
theorem integrable_planeMeasure_projection_iff (n b : Position) (hn : ‖n‖ = 1)
    (a : Fin 3) (ha : n a ≠ 0) (F : PlaneFrame (affinePlane n b)) (h : Position → ℝ) :
    Integrable h (planeMeasure F) ↔ Integrable (h ∘ planeGraph n b a ha) volume := by
  rw [planeMeasure_eq_projection_map n b hn a ha F,
    integrable_smul_measure
      (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (abs_pos.mpr ha))) ENNReal.ofReal_ne_top]
  exact (isClosedEmbedding_planeGraph n b a ha).measurableEmbedding.integrable_map_iff

/-- Real coordinate projection formula (3.2).
The closed embedding also makes this valid for the total Bochner integral convention;
`integrable_planeMeasure_projection_iff` identifies the integrable locus. -/
theorem integral_planeMeasure_projection (n b : Position) (hn : ‖n‖ = 1)
    (a : Fin 3) (ha : n a ≠ 0) (F : PlaneFrame (affinePlane n b)) (h : Position → ℝ) :
    ∫ x, h x ∂planeMeasure F = |n a|⁻¹ * ∫ q, h (planeGraph n b a ha q) := by
  rw [planeMeasure_eq_projection_map n b hn a ha F, integral_smul_measure,
    (isClosedEmbedding_planeGraph n b a ha).integral_map h,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _)), smul_eq_mul]

end LiebThirring

end
