/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import LeanPool.LiebThirring.Electrostatics.SlicingLines
import LeanPool.LiebThirring.Electrostatics.SphereCap
import all Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Volume and derivative coordinates for slicing

Coordinate insertion is an isometric embedding on each line; coordinate
deletion and insertion preserve Lebesgue volume as a product decomposition.
-/

public section

open MeasureTheory

namespace LiebThirring

theorem coordinateLine_zero_one_eq_basis (a : Fin 3) :
    coordinateLine a 0 1 = EuclideanSpace.basisFun (Fin 3) ℝ a := by
  ext i
  revert i
  rw [a.forall_iff_succAbove]
  constructor
  · simp [EuclideanSpace.basisFun_apply]
  · intro j
    simp [EuclideanSpace.basisFun_apply, a.succAbove_ne j]

theorem isometry_coordinateLine (a : Fin 3) (q : Planar) :
    Isometry (coordinateLine a q) := by
  apply isometry_iff_dist_eq.mpr
  intro s t
  rw [dist_eq_norm, coordinateLine_eq_affine a q s, coordinateLine_eq_affine a q t]
  rw [add_sub_add_left_eq_sub, ← sub_smul, coordinateLine_zero_one_eq_basis,
    norm_smul]
  simp [EuclideanSpace.basisFun_apply, Real.dist_eq]

theorem isClosedEmbedding_coordinateLine (a : Fin 3) (q : Planar) :
    Topology.IsClosedEmbedding (coordinateLine a q) :=
  (isometry_coordinateLine a q).isClosedEmbedding

/-- Measure-preserving separation of a selected spatial coordinate from its plane. -/
@[expose] noncomputable def coordinateSplit (a : Fin 3) : Position ≃ᵐ Planar × ℝ :=
  ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) a).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))).trans (MeasurableEquiv.prodComm : ℝ × Planar ≃ᵐ
          Planar × ℝ)

theorem coordinateSplit_preserving (a : Fin 3) : MeasurePreserving (coordinateSplit a) := by
  have hs : MeasurePreserving (MeasurableEquiv.prodComm : ℝ × Planar ≃ᵐ Planar × ℝ)
      volume volume := by
    change MeasurePreserving Prod.swap volume volume
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
        (ν := (volume : Measure Planar)))
  exact ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).trans
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) a).trans
      ((MeasurePreserving.id volume).prod
        (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).symm))).trans hs

theorem integral_coordinateLines (a : Fin 3) (f : Position → ℝ) (hf : Integrable f) :
    (∫ x, f x) = ∫ q : Planar, ∫ t : ℝ, f (coordinateLine a q t) := by
  have hmp := (coordinateSplit_preserving a).symm
  have hi : Integrable (fun p : Planar × ℝ => f ((coordinateSplit a).symm p)) :=
    (hmp.integrable_comp_emb (coordinateSplit a).symm.measurableEmbedding).mpr hf
  rw [← hmp.integral_comp (coordinateSplit a).symm.measurableEmbedding,
    Measure.volume_eq_prod, integral_prod _ hi]
  rfl

theorem hasDerivAt_coordinateLine (a : Fin 3) (q : Planar) (t : ℝ) :
    HasDerivAt (coordinateLine a q) (EuclideanSpace.basisFun (Fin 3) ℝ a) t := by
  have he : coordinateLine a q =
      (fun t : ℝ => coordinateLine a q 0 + t • coordinateLine a 0 1) :=
    funext (coordinateLine_eq_affine a q)
  rw [he, ← coordinateLine_zero_one_eq_basis]
  simpa only [id_eq, one_smul] using
    ((hasDerivAt_id t).smul_const (coordinateLine a 0 1)).const_add (coordinateLine a q 0)

end LiebThirring

end
