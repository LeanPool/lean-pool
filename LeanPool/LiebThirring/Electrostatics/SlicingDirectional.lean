/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import LeanPool.LiebThirring.Electrostatics.SlicingCellGeometry

/-!
# The directional cell identity on almost every line

The compact scalar fundamental theorem, applied to each transverse line in a
Voronoi cell. The resulting terms are oriented genuine-face values.
-/

public section

open Set MeasureTheory

namespace LiebThirring

/-- Boundary value selected by a coordinate slice of a genuine Voronoi face. -/
@[expose] noncomputable def coordinateFaceTerm {M : ℕ} (R : Fin M → Position)
    (k l : Fin M) (a : Fin 3) (g : Position → ℝ) (q : Planar) : ℝ := by
  classical
  exact if ha : bisectorNormal R k l a ≠ 0 then
    (bisectorNormal R k l a / |bisectorNormal R k l a|) *
      (voronoiFace R k l).indicator g
        (planeGraph (bisectorNormal R k l) (midpoint ℝ (R k) (R l)) a ha q)
  else 0

theorem hasDerivAt_comp_coordinateLine (g : Position → ℝ) (hg : ContDiff ℝ 1 g)
    (a : Fin 3) (q : Planar) (t : ℝ) :
    HasDerivAt (fun s => g (coordinateLine a q s))
      (fderiv ℝ g (coordinateLine a q t) (EuclideanSpace.basisFun (Fin 3) ℝ a)) t :=
  ((hg.differentiable (by decide)).differentiableAt.hasFDerivAt).comp_hasDerivAt t
    (hasDerivAt_coordinateLine a q t)

theorem integral_coordinateLine_voronoiCell {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (k : Fin M) (a : Fin 3) (q : Planar)
    (hq : q ∉ slicingExceptionalSet R a) (g : Position → ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    (∫ t in {t | coordinateLine a q t ∈ voronoiCell R k},
      fderiv ℝ g (coordinateLine a q t) (EuclideanSpace.basisFun (Fin 3) ℝ a)) =
      ∑ l : {l : Fin M // l ≠ k}, coordinateFaceTerm R k l.val a g q := by
  classical
  let α := fun l : {l : Fin M // l ≠ k} => bisectorNormal R k l.val a
  let β := fun l : {l : Fin M // l ≠ k} => voronoiSliceOffset R k l.val a q
  let G := fun t => g (coordinateLine a q t)
  have hG : ContDiff ℝ 1 G := hg.comp (contDiff_coordinateLine a q 1)
  have hGc : HasCompactSupport G := hgc.comp_isClosedEmbedding
    (isClosedEmbedding_coordinateLine a q)
  have hd (t : ℝ) : deriv G t =
      fderiv ℝ g (coordinateLine a q t) (EuclideanSpace.basisFun (Fin 3) ℝ a) :=
    (hasDerivAt_comp_coordinateLine g hg a q t).deriv
  have hs : {t | coordinateLine a q t ∈ voronoiCell R k} =
      {t | ∀ l, t * α l < β l} := by
    ext t
    exact mem_voronoiCell_coordinateLine_iff R hR k a q t
  rw [hs]
  have hi := integral_derivative_finite_halfspaces α β
    (fun t l p hlp _ hl hp => voronoi_slice_constraints_regular R hR k a q hq
      t l p hlp hl hp) G (deriv G)
    (fun t => (hG.differentiable (by decide) t).hasDerivAt)
    hG.continuous_deriv_one hGc hGc.deriv
  simp only [hd] at hi
  rw [hi, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  by_cases ha : α l = 0
  · simp only [ha, lt_self_iff_false, ite_false, sub_self]
    symm
    unfold coordinateFaceTerm
    exact dite_eq_right (not_ne_iff.mpr ha)
  · rw [halfspaceFaceValue_voronoi R hR k l a q ha g,
      coordinateLine_slice_root_eq_planeGraph R hR k l.val l.property.symm a q ha]
    unfold coordinateFaceTerm
    rw [dite_eq_left ha]
    change ((if 0 < α l then _ else 0) - (if α l < 0 then _ else 0)) =
      (α l / |α l|) * _
    rcases lt_or_gt_of_ne ha with hn | hp
    · rw [ite_eq_right (not_lt_of_ge hn.le), ite_eq_left hn, abs_of_neg hn]
      simp only [div_neg, div_self ha, neg_one_mul, zero_sub]
    · rw [ite_eq_left hp, ite_eq_right (not_lt_of_ge hp.le), abs_of_pos hp,
        div_self ha, one_mul, sub_zero]

end LiebThirring

end
