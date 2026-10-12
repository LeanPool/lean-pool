/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.SlicingCoordinates
public import LeanPool.LiebThirring.Electrostatics.SlicingScalar
public import LeanPool.LiebThirring.Electrostatics.FaceMeasureGeometry

/-!
# Voronoi cells as finite halfspace slices

The affine constraints and genuine-facet values needed to instantiate the
scalar fundamental theorem on almost every coordinate line.
-/

public section

open Set
open scoped RealInnerProductSpace

namespace LiebThirring

/-- The affine offset of a Voronoi halfspace along a selected coordinate line. -/
@[expose] noncomputable def voronoiSliceOffset {M : ℕ} (R : Fin M → Position)
    (k l : Fin M) (a : Fin 3) (q : Planar) : ℝ :=
  ‖R l - R k‖ / 2 - inner ℝ (bisectorNormal R k l) (coordinateLine a q 0 - R k)

theorem inner_bisectorNormal_coordinateLine {M : ℕ} (R : Fin M → Position)
    (k l : Fin M) (a : Fin 3) (q : Planar) (t : ℝ) :
    inner ℝ (bisectorNormal R k l) (coordinateLine a q t - R k) =
      t * bisectorNormal R k l a +
        inner ℝ (bisectorNormal R k l) (coordinateLine a q 0 - R k) := by
  rw [coordinateLine_eq_affine a q t, coordinateLine_zero_one_eq_basis,
    add_sub_right_comm, inner_add_right, inner_smul_right,
    EuclideanSpace.inner_basisFun_real]
  ring

theorem dist_lt_dist_iff_bisectorNormal {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (k l : Fin M) (hkl : k ≠ l) (x : Position) :
    dist x (R k) < dist x (R l) ↔
      inner ℝ (bisectorNormal R k l) (x - R k) < ‖R l - R k‖ / 2 := by
  have hp : 0 < ‖R l - R k‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hR.ne hkl.symm))
  rw [dist_lt_dist_iff_inner_lt]
  simp only [bisectorNormal, real_inner_smul_left, ← div_eq_inv_mul]
  rw [div_lt_iff₀ hp]
  constructor <;> intro h <;> nlinarith only [h]

theorem dist_lt_dist_coordinateLine_iff {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (k l : Fin M) (hkl : k ≠ l)
    (a : Fin 3) (q : Planar) (t : ℝ) :
    dist (coordinateLine a q t) (R k) < dist (coordinateLine a q t) (R l) ↔
      t * bisectorNormal R k l a < voronoiSliceOffset R k l a q := by
  rw [dist_lt_dist_iff_bisectorNormal R hR k l hkl,
    inner_bisectorNormal_coordinateLine]
  unfold voronoiSliceOffset
  constructor <;> intro h <;> linarith only [h]

theorem mem_voronoiCell_coordinateLine_iff {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (k : Fin M) (a : Fin 3) (q : Planar) (t : ℝ) :
    coordinateLine a q t ∈ voronoiCell R k ↔
      ∀ l : {l : Fin M // l ≠ k},
        t * bisectorNormal R k l.val a < voronoiSliceOffset R k l.val a q := by
  rw [mem_voronoiCell_iff_normal R hR]
  simp only [Subtype.forall]
  apply forall_congr'
  intro l
  apply imp_congr_right
  intro hl
  rw [inner_bisectorNormal_coordinateLine]
  unfold voronoiSliceOffset
  constructor <;> intro ht <;> linarith only [ht]

theorem coordinateLine_slice_root_mem_bisector {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (k l : Fin M) (hkl : k ≠ l) (a : Fin 3) (q : Planar)
    (ha : bisectorNormal R k l a ≠ 0) :
    coordinateLine a q (voronoiSliceOffset R k l a q / bisectorNormal R k l a) ∈
      bisectorPlane R k l := by
  rw [mem_bisectorPlane_iff_normal R hR hkl, inner_bisectorNormal_coordinateLine,
    div_mul_cancel₀ _ ha, voronoiSliceOffset]
  exact sub_add_cancel _ _

theorem voronoi_slice_constraints_regular {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (k : Fin M) (a : Fin 3) (q : Planar)
    (hq : q ∉ slicingExceptionalSet R a) (t : ℝ)
    (l p : {l : Fin M // l ≠ k}) (hlp : l ≠ p)
    (hl : t * bisectorNormal R k l.val a = voronoiSliceOffset R k l.val a q)
    (hp : t * bisectorNormal R k p.val a = voronoiSliceOffset R k p.val a q) : False := by
  have hlplane : coordinateLine a q t ∈ bisectorPlane R k l.val := by
    rw [mem_bisectorPlane_iff_normal R hR l.property.symm,
      inner_bisectorNormal_coordinateLine, hl, voronoiSliceOffset]
    exact sub_add_cancel _ _
  have hpplane : coordinateLine a q t ∈ bisectorPlane R k p.val := by
    rw [mem_bisectorPlane_iff_normal R hR p.property.symm,
      inner_bisectorNormal_coordinateLine, hp, voronoiSliceOffset]
    exact sub_add_cancel _ _
  apply hq
  apply Or.inl
  refine ⟨coordinateLine a q t, ?_, planeProjection_coordinateLine a q t⟩
  exact ⟨k, l.val, p.val, l.property.symm, p.property.symm,
    (fun he => hlp (Subtype.ext he)), hlplane, hpplane⟩

theorem coordinateLine_slice_root_eq_planeGraph {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (k l : Fin M) (hkl : k ≠ l) (a : Fin 3) (q : Planar)
    (ha : bisectorNormal R k l a ≠ 0) :
    coordinateLine a q (voronoiSliceOffset R k l a q / bisectorNormal R k l a) =
      planeGraph (bisectorNormal R k l) (midpoint ℝ (R k) (R l)) a ha q := by
  have hm := coordinateLine_slice_root_mem_bisector R hR k l hkl a q ha
  rw [bisectorPlane_eq_affinePlane R hR hkl] at hm
  exact (planeGraph_planeProjection _ _ a ha _ hm).symm.trans
    (by rw [planeProjection_coordinateLine])

theorem halfspaceFaceValue_voronoi {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (k : Fin M) (l : {l : Fin M // l ≠ k})
    (a : Fin 3) (q : Planar) (ha : bisectorNormal R k l.val a ≠ 0)
    (g : Position → ℝ) :
    halfspaceFaceValue (fun p : {p : Fin M // p ≠ k} => bisectorNormal R k p.val a)
      (fun p => voronoiSliceOffset R k p.val a q) (fun t => g (coordinateLine a q t)) l =
      (voronoiFace R k l.val).indicator g
        (coordinateLine a q (voronoiSliceOffset R k l.val a q / bisectorNormal R k l.val a)) := by
  classical
  let t := voronoiSliceOffset R k l.val a q / bisectorNormal R k l.val a
  have he : (∀ p : {p : Fin M // p ≠ k}, p ≠ l →
      t * bisectorNormal R k p.val a < voronoiSliceOffset R k p.val a q) ↔
      coordinateLine a q t ∈ voronoiFace R k l.val := by
    constructor
    · intro hp
      refine ⟨l.property.symm, coordinateLine_slice_root_mem_bisector R hR k l.val
        l.property.symm a q ha, ?_⟩
      intro p hpk hpl
      exact (dist_lt_dist_coordinateLine_iff R hR k p hpk.symm a q t).mpr
        (hp ⟨p, hpk⟩ (fun he => hpl (congrArg Subtype.val he)))
    · intro hx p hpl
      exact (dist_lt_dist_coordinateLine_iff R hR k p.val p.property.symm a q t).mp
        (hx.2.2 p.val p.property (fun he => hpl (Subtype.ext he)))
  unfold halfspaceFaceValue
  dsimp only
  by_cases hf : ∀ p : {p : Fin M // p ≠ k}, p ≠ l →
      t * bisectorNormal R k p.val a < voronoiSliceOffset R k p.val a q
  · rw [ite_eq_left hf, indicator_of_mem (he.mp hf)]
  · rw [ite_eq_right hf, indicator_of_notMem (fun hm => hf (he.mpr hm))]

end LiebThirring

end
