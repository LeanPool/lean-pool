/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.Plane

/-!
# Coordinate projection charts on affine planes

Delete coordinate `a`, retaining the Euclidean norm on the remaining coordinates.

The graph formula solving the omitted coordinate of a plane.
-/

@[expose] public section

open MeasureTheory WithLp
open scoped ENNReal

namespace LiebThirring

/-- Delete coordinate `a`, retaining the Euclidean norm on the remaining coordinates. -/
noncomputable def planeProjection (a : Fin 3) (x : Position) : Planar :=
  toLp 2 (fun i => x (a.succAbove i))

/-- The graph formula solving the omitted coordinate of a plane. -/
noncomputable def planeGraph (n b : Position) (a : Fin 3) (_ha : n a ≠ 0) (q : Planar) : Position :=
  toLp 2 (a.insertNth
    (b a - (∑ i : Fin 2, n (a.succAbove i) * (q i - b (a.succAbove i))) / n a)
    (fun i => q i))

@[simp] theorem planeProjection_apply (a : Fin 3) (x : Position) (i : Fin 2) :
    planeProjection a x i = x (a.succAbove i) := rfl

@[simp] theorem planeGraph_apply_same (n b : Position) (a : Fin 3) (ha : n a ≠ 0) (q : Planar) :
    planeGraph n b a ha q a =
      b a - (∑ i : Fin 2, n (a.succAbove i) * (q i - b (a.succAbove i))) / n a := by
  dsimp only [planeGraph]
  exact Fin.insertNth_apply_same (α := fun _ => ℝ) a _ _

@[simp] theorem planeGraph_apply_succAbove (n b : Position) (a : Fin 3) (ha : n a ≠ 0) (q : Planar)
    (i : Fin 2) : planeGraph n b a ha q (a.succAbove i) = q i := by
  dsimp only [planeGraph]
  exact Fin.insertNth_apply_succAbove (α := fun _ => ℝ) a _ _ i

/-- The Euclidean plane equation expanded in its three coordinates. -/
theorem inner_sub_eq_coordinate_sum (n x b : Position) :
    inner ℝ n (x - b) = ∑ i : Fin 3, n i * (x i - b i) := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The graph formula takes values on the plane when the deleted normal coordinate is nonzero. -/
theorem planeGraph_mem (n b : Position) (a : Fin 3) (ha : n a ≠ 0) (q : Planar) :
    planeGraph n b a ha q ∈ affinePlane n b := by
  rw [mem_affinePlane, inner_sub_eq_coordinate_sum, Fin.sum_univ_succAbove _ a]
  simp only [planeGraph_apply_same, planeGraph_apply_succAbove]
  field_simp
  ring

/-- Projecting the graph returns its two parameters. -/
@[simp] theorem planeProjection_planeGraph (n b : Position) (a : Fin 3) (ha : n a ≠ 0) (q : Planar)
  :
    planeProjection a (planeGraph n b a ha q) = q := by
  ext i
  exact planeGraph_apply_succAbove n b a ha q i

/-- Solving the normal equation reconstructs each point on the plane. -/
theorem planeGraph_planeProjection (n b : Position) (a : Fin 3) (ha : n a ≠ 0)
    (x : Position) (hx : x ∈ affinePlane n b) :
    planeGraph n b a ha (planeProjection a x) = x := by
  rw [mem_affinePlane, inner_sub_eq_coordinate_sum, Fin.sum_univ_succAbove _ a] at hx
  ext i
  revert i
  rw [a.forall_iff_succAbove]
  constructor
  · rw [planeGraph_apply_same]
    simp only [planeProjection_apply]
    have hs : (∑ j : Fin 2, n (a.succAbove j) * (x (a.succAbove j) - b (a.succAbove j))) / n a = b
      a - x a := by
      apply (div_eq_iff ha).mpr
      linarith only [hx]
    rw [hs]
    ring
  · intro j
    rw [planeGraph_apply_succAbove, planeProjection_apply]

/-- Coordinate deletion is bijective on a plane with nonzero corresponding normal component. -/
theorem planeProjection_bijective (n b : Position) (a : Fin 3) (ha : n a ≠ 0) :
    Function.Bijective (fun x : affinePlane n b => planeProjection a (x : Position)) := by
  constructor
  · intro x y hxy
    change planeProjection a (x : Position) = planeProjection a (y : Position) at hxy
    apply Subtype.ext
    rw [← planeGraph_planeProjection n b a ha x x.property,
      ← planeGraph_planeProjection n b a ha y y.property, hxy]
  · intro q
    exact ⟨⟨planeGraph n b a ha q, planeGraph_mem n b a ha q⟩,
      planeProjection_planeGraph n b a ha q⟩

/-- Coordinate deletion as a linear map on Euclidean carriers. -/
noncomputable def planeProjectionLinear (a : Fin 3) : Position →ₗ[ℝ] Planar where
  toFun := planeProjection a
  map_add' x y := by
    ext i
    rfl
  map_smul' c x := by
    ext i
    rfl

/-- Coordinate deletion after an orthonormal frame, as a bijective affine chart. -/
noncomputable def planeProjectionChart (n b : Position) (a : Fin 3) (ha : n a ≠ 0)
    (F : PlaneFrame (affinePlane n b)) : Planar ≃ᵃ[ℝ] Planar :=
  AffineEquiv.ofBijective (φ := (planeProjectionLinear a).toAffineMap.comp
    ((affinePlane n b).subtype.comp F.toAffineEquiv.toAffineMap))
    ((planeProjection_bijective n b a ha).comp F.toAffineEquiv.bijective)

/-- The inverse of the projection chart, followed by the frame, is the explicit plane graph. -/
theorem planeProjectionChart_symm_frame (n b : Position) (a : Fin 3) (ha : n a ≠ 0)
    (F : PlaneFrame (affinePlane n b)) (q : Planar) :
    (F ((planeProjectionChart n b a ha F).symm q) : Position) = planeGraph n b a ha q := by
  have hp : planeProjection a (F ((planeProjectionChart n b a ha F).symm q) : Position) = q :=
    (planeProjectionChart n b a ha F).apply_symm_apply q
  calc
    _ = planeGraph n b a ha
        (planeProjection a (F ((planeProjectionChart n b a ha F).symm q) : Position)) :=
      (planeGraph_planeProjection n b a ha _
        (F ((planeProjectionChart n b a ha F).symm q)).property).symm
    _ = _ := congrArg (planeGraph n b a ha) hp

/-- A planar affine coordinate change rescales volume by its inverse absolute determinant. -/
theorem map_planar_affineEquiv_volume (e : Planar ≃ᵃ[ℝ] Planar) :
    Measure.map e volume =
      ENNReal.ofReal |(LinearMap.det (e.linear : Planar →ₗ[ℝ] Planar))⁻¹| • volume := by
  have hfun : (fun x : Planar => x + e 0) ∘ e.linear = e := by
    funext x
    symm
    change e x = e.linear x + e 0
    simpa only [vadd_eq_add, add_zero] using e.map_vadd (0 : Planar) x
  have hl : Measurable (e.linear : Planar → Planar) :=
    e.linear.toLinearMap.continuous_of_finiteDimensional.measurable
  have ht : Measurable (fun x : Planar => x + e 0) :=
    continuous_id.add continuous_const |>.measurable
  have hlin : Measure.map (e.linear : Planar → Planar) volume =
      ENNReal.ofReal |(LinearMap.det (e.linear : Planar →ₗ[ℝ] Planar))⁻¹| • volume := by
    simpa only [LinearEquiv.coe_coe] using
      (Measure.map_linearMap_addHaar_eq_smul_addHaar volume e.linear.isUnit_det'.ne_zero)
  rw [← hfun, ← Measure.map_map ht hl, hlin,
    Measure.map_smul _ ht.aemeasurable,
    (measurePreserving_add_right volume (e 0)).map_eq]

end LiebThirring

end
