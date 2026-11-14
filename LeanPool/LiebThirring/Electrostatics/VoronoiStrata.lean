/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.VoronoiDistance
public import LeanPool.LiebThirring.Electrostatics.Plane

/-!
# Voronoi faces and surface-null triple strata

Intersections of distinct bisectors give the lower-dimensional triple-tie strata.
-/

public section

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal

namespace LiebThirring

variable {M : ℕ}

/-- Distinct bisectors with a common nucleus cannot contain one another. -/
theorem bisectorPlane_not_le (R : Fin M → Position) (hR : Function.Injective R)
    {k l p : Fin M} (hkl : k ≠ l) (hkp : k ≠ p) (hlp : l ≠ p) :
    ¬ bisectorPlane R k l ≤ bisectorPlane R k p := by
  intro hH
  have hd := AffineSubspace.direction_le hH
  change (AffineSubspace.perpBisector (R k) (R l)).direction ≤
    (AffineSubspace.perpBisector (R k) (R p)).direction at hd
  rw [AffineSubspace.direction_perpBisector, AffineSubspace.direction_perpBisector] at hd
  have hspan := Submodule.orthogonal_le hd
  simp only [Submodule.orthogonal_orthogonal, vsub_eq_sub] at hspan
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (hspan (Submodule.mem_span_singleton_self (R p - R k)))
  have hm := hH (AffineSubspace.midpoint_mem_perpBisector (R k) (R l))
  change midpoint ℝ (R k) (R l) ∈ AffineSubspace.perpBisector (R k) (R p) at hm
  rw [AffineSubspace.mem_perpBisector_iff_inner_eq, midpoint_vsub_left,
    invOf_eq_inv, real_inner_smul_left, vsub_eq_sub, dist_eq_norm,
    norm_sub_rev (R k) (R p)] at hm
  simp only [vsub_eq_sub] at hm
  norm_num only at hm
  have hi : inner ℝ (R l - R k) (R p - R k) = ‖R p - R k‖ ^ 2 := by
    linarith only [hm]
  have he : t * ‖R l - R k‖ ^ 2 = t * t * ‖R l - R k‖ ^ 2 := by
    calc
      t * ‖R l - R k‖ ^ 2 = inner ℝ (R l - R k) (R p - R k) := by
        rw [← ht, real_inner_smul_right, real_inner_self_eq_norm_sq]
      _ = inner ℝ (R p - R k) (R p - R k) := hi.trans (real_inner_self_eq_norm_sq _).symm
      _ = t * t * ‖R l - R k‖ ^ 2 := by
        rw [← ht, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
        ring
  have hd0 : ‖R l - R k‖ ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hR.ne hkl.symm))))
  have ht0 : t ≠ 0 := by
    intro ht0
    rw [ht0, zero_smul] at ht
    exact hR.ne hkp.symm (sub_eq_zero.mp ht.symm)
  have ht1 : t = 1 := by
    have hf : (t * (t - 1)) * ‖R l - R k‖ ^ 2 = 0 := by
      nlinarith only [he]
    have hh := (mul_eq_zero.mp hf).resolve_right hd0
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left ht0)
  rw [ht1, one_smul] at ht
  exact hR.ne hlp (sub_left_inj.mp ht)

theorem finrank_bisectorPlane_direction (R : Fin M → Position)
    (hR : Function.Injective R) {k l : Fin M} (hkl : k ≠ l) :
    Module.finrank ℝ (bisectorPlane R k l).direction = 2 := by
  change Module.finrank ℝ (AffineSubspace.perpBisector (R k) (R l)).direction = 2
  rw [AffineSubspace.direction_perpBisector, vsub_eq_sub]
  have : Fact (Module.finrank ℝ Position = 2 + 1) := ⟨finrank_euclideanSpace⟩
  exact Submodule.finrank_orthogonal_span_singleton (sub_ne_zero.mpr (hR.ne hkl.symm))

/-- Each constituent of the triple stratum is an affine line, a point, or empty,
as expressed by direction dimension at most one. -/
theorem finrank_bisectorPlane_inf_le_one (R : Fin M → Position)
    (hR : Function.Injective R) {k l p : Fin M}
    (hkl : k ≠ l) (hkp : k ≠ p) (hlp : l ≠ p) :
    Module.finrank ℝ (bisectorPlane R k l ⊓ bisectorPlane R k p).direction ≤ 1 := by
  let S := bisectorPlane R k l ⊓ bisectorPlane R k p
  change Module.finrank ℝ S.direction ≤ 1
  rcases S.eq_bot_or_nonempty with he | ⟨x, hx⟩
  · rw [he, AffineSubspace.direction_bot, finrank_bot]
    omega
  · have hle : S.direction ≤ (bisectorPlane R k l).direction :=
      AffineSubspace.direction_le inf_le_left
    have hne : S.direction ≠ (bisectorPlane R k l).direction := by
      intro heq
      have heqS : S = bisectorPlane R k l :=
        AffineSubspace.ext_of_direction_eq heq ⟨x, hx, hx.1⟩
      have hbad : bisectorPlane R k l ≤ bisectorPlane R k p := heqS ▸ inf_le_right
      exact bisectorPlane_not_le R hR hkl hkp hlp hbad
    have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
    rw [finrank_bisectorPlane_direction R hR hkl] at hlt
    omega

/-- The triple stratum is a finite union of affine subspaces with direction dimension ≤ 1. -/
theorem voronoiTripleStratum_eq_iUnion (R : Fin M → Position) :
    voronoiTripleStratum R = ⋃ k : Fin M, ⋃ l : {l : Fin M // k ≠ l},
      ⋃ p : {p : Fin M // k ≠ p ∧ l.val ≠ p},
        (bisectorPlane R k l ⊓ bisectorPlane R k p : Set Position) := by
  ext x
  simp only [voronoiTripleStratum, mem_ofPred_eq, mem_iUnion, Subtype.exists]
  constructor
  · rintro ⟨k, l, p, hkl, hkp, hlp, hx₁, hx₂⟩
    exact ⟨k, l, hkl, p, ⟨hkp, hlp⟩, hx₁, hx₂⟩
  · rintro ⟨k, l, hkl, p, ⟨hkp, hlp⟩, hx₁, hx₂⟩
    exact ⟨k, l, p, hkl, hkp, hlp, hx₁, hx₂⟩

end LiebThirring

end
