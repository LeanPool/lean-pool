/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.VoronoiStrata
public import LeanPool.LiebThirring.Electrostatics.PlaneProjection
import LeanPool.LiebThirring.Electrostatics.FaceMeasureGeometry

/-!
# Null projected triple ties

Coordinate projections of triple-tie strata form a null exceptional set for line slicing.
-/

public section

open MeasureTheory Set

namespace LiebThirring

theorem volume_planeProjection_affineSubspace_eq_zero (a : Fin 3)
    (S : AffineSubspace ℝ Position) (hS : Module.finrank ℝ S.direction ≤ 1) :
    volume (planeProjection a '' (S : Set Position)) = 0 := by
  let f := (planeProjectionLinear a).toAffineMap
  have he : planeProjection a '' (S : Set Position) = (S.map f : Set Planar) :=
    (AffineSubspace.coe_map f S).symm
  rw [he]
  apply Measure.addHaar_affineSubspace
  intro ht
  have hd : Module.finrank ℝ (S.map f).direction ≤ 1 := by
    rw [AffineSubspace.map_direction]
    exact (Submodule.finrank_map_le f.linear S.direction).trans hS
  rw [ht, AffineSubspace.direction_top, finrank_top] at hd
  have hdim : Module.finrank ℝ Planar = 2 := by
    simp only [Planar, finrank_euclideanSpace_fin]
  rw [hdim] at hd
  omega

theorem volume_planeProjection_voronoiTripleStratum {M : ℕ}
    (R : Fin M → Position) (hR : Function.Injective R) (a : Fin 3) :
    volume (planeProjection a '' voronoiTripleStratum R) = 0 := by
  rw [voronoiTripleStratum_eq_iUnion]
  simp only [image_iUnion]
  exact measure_iUnion_null fun k => measure_iUnion_null fun l => measure_iUnion_null fun p =>
    volume_planeProjection_affineSubspace_eq_zero a _
      (finrank_bisectorPlane_inf_le_one R hR l.property p.property.1 p.property.2)

/-- A nontransverse plane projects into an affine line in the base plane. -/
theorem volume_planeProjection_affinePlane_of_coordinate_zero
    (n b : Position) (hn : n ≠ 0) (a : Fin 3) (ha : n a = 0) :
    volume (planeProjection a '' (affinePlane n b : Set Position)) = 0 := by
  have hnp : planeProjection a n ≠ 0 := by
    intro he
    apply hn
    ext i
    revert i
    rw [a.forall_iff_succAbove]
    constructor
    · simpa only [PiLp.zero_apply] using ha
    · intro j
      have hc := congrArg (fun q : Planar => q j) he
      simpa only [planeProjection_apply, PiLp.zero_apply] using hc
  let H : AffineSubspace ℝ Planar :=
    AffineSubspace.mk' (planeProjection a b) (ℝ ∙ planeProjection a n)ᗮ
  have hnull : volume (H : Set Planar) = 0 := by
    apply Measure.addHaar_affineSubspace
    intro ht
    have hm : planeProjection a n + planeProjection a b ∈ H := by rw [ht]; trivial
    change planeProjection a n + planeProjection a b ∈
      AffineSubspace.mk' (planeProjection a b) (ℝ ∙ planeProjection a n)ᗮ at hm
    rw [AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_right,
      Submodule.mem_orthogonal_singleton_iff_inner_right] at hm
    exact hnp (inner_self_eq_zero.mp hm)
  apply measure_mono_null _ hnull
  rintro q ⟨x, hx, rfl⟩
  change planeProjection a x ∈ AffineSubspace.mk' (planeProjection a b)
    (ℝ ∙ planeProjection a n)ᗮ
  rw [AffineSubspace.mem_mk', vsub_eq_sub,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  have he : inner ℝ (planeProjection a n) (planeProjection a x - planeProjection a b) =
      ∑ j : Fin 2, n (a.succAbove j) * (x (a.succAbove j) - b (a.succAbove j)) := by
    simp [PiLp.inner_apply, RCLike.inner_apply, planeProjection_apply, mul_comm]
  rw [he]
  have hx' : x ∈ affinePlane n b := hx
  rw [mem_affinePlane, inner_sub_eq_coordinate_sum, Fin.sum_univ_succAbove _ a,
    ha, zero_mul, zero_add] at hx'
  exact hx'

theorem volume_planeProjection_bisector_of_coordinate_zero {M : ℕ}
    (R : Fin M → Position) (hR : Function.Injective R) (k l : Fin M)
    (hkl : k ≠ l) (a : Fin 3) (ha : bisectorNormal R k l a = 0) :
    volume (planeProjection a '' (bisectorPlane R k l : Set Position)) = 0 := by
  rw [bisectorPlane_eq_affinePlane R hR hkl]
  apply volume_planeProjection_affinePlane_of_coordinate_zero _ _ _ a ha
  intro he
  have hh := norm_bisectorNormal R hR hkl
  rw [he, norm_zero] at hh
  exact zero_ne_one hh

/-- Bases excluded in the slicing proof: triple ties and nontransverse planes. -/
@[expose] def slicingExceptionalSet {M : ℕ} (R : Fin M → Position) (a : Fin 3) : Set Planar :=
  (planeProjection a '' voronoiTripleStratum R) ∪
    ⋃ k : Fin M, ⋃ l : {l : Fin M // k ≠ l},
      ⋃ (_ : bisectorNormal R k l.val a = 0),
        planeProjection a '' (bisectorPlane R k l.val : Set Position)

theorem volume_slicingExceptionalSet {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (a : Fin 3) :
    volume (slicingExceptionalSet R a) = 0 := by
  apply measure_union_null (volume_planeProjection_voronoiTripleStratum R hR a)
  exact measure_iUnion_null fun k => measure_iUnion_null fun l => measure_iUnion_null fun ha =>
    volume_planeProjection_bisector_of_coordinate_zero R hR k l.val l.property a ha

theorem ae_notMem_slicingExceptionalSet {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (a : Fin 3) :
    ∀ᵐ q : Planar, q ∉ slicingExceptionalSet R a := by
  apply ae_iff.mpr
  simpa only [not_not, Set.ofPred_mem_eq] using volume_slicingExceptionalSet R hR a

end LiebThirring

end
