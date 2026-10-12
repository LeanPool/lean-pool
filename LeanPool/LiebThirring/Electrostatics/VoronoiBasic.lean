/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.Coulomb
public import Mathlib.Geometry.Euclidean.PerpBisector

/-!
# Voronoi cells and strict faces

The perpendicular bisector affine subspace of two nuclei.

Points having nucleus `k` as their unique closest nucleus.
-/

public section

open Set Metric
open scoped InnerProductSpace ENNReal

namespace LiebThirring

variable {M : ℕ}

/-- The perpendicular bisector affine subspace of two nuclei. -/
@[expose] noncomputable def bisectorPlane (R : Fin M → Position) (k l : Fin M) :
    AffineSubspace ℝ Position :=
  AffineSubspace.perpBisector (R k) (R l)

/-- Points having nucleus `k` as their unique closest nucleus. -/
@[expose] def voronoiCell (R : Fin M → Position) (k : Fin M) : Set Position :=
  {x | ∀ l, l ≠ k → dist x (R k) < dist x (R l)}

/-- Points having nucleus `k` among their closest nuclei. -/
@[expose] def closedVoronoiCell (R : Fin M → Position) (k : Fin M) : Set Position :=
  {x | ∀ l, dist x (R k) ≤ dist x (R l)}

/-- The genuine face: exactly `k` and `l` are closest, with no third tie. -/
@[expose] def voronoiFace (R : Fin M → Position) (k l : Fin M) : Set Position :=
  {x | k ≠ l ∧ x ∈ bisectorPlane R k l ∧
    ∀ p, p ≠ k → p ≠ l → dist x (R k) < dist x (R p)}

/-- The finite union of intersections of bisectors with a common nucleus.
It contains every point with at least three nearest nuclei. -/
@[expose] def voronoiTripleStratum (R : Fin M → Position) : Set Position :=
  {x | ∃ k l p, k ≠ l ∧ k ≠ p ∧ l ≠ p ∧
    x ∈ bisectorPlane R k l ∧ x ∈ bisectorPlane R k p}

/-- The directed unit bisector normal for distinct nuclei. -/
@[expose] noncomputable def bisectorNormal (R : Fin M → Position) (k l : Fin M) :
    Position :=
  ‖R l - R k‖⁻¹ • (R l - R k)

@[simp] theorem mem_bisectorPlane (R : Fin M → Position) (k l : Fin M) (x : Position) :
    x ∈ bisectorPlane R k l ↔ dist x (R k) = dist x (R l) :=
  AffineSubspace.mem_perpBisector_iff_dist_eq

theorem bisectorPlane_comm (R : Fin M → Position) (k l : Fin M) :
    bisectorPlane R k l = bisectorPlane R l k :=
  AffineSubspace.perpBisector_comm _ _

/-- Squared-distance comparison, in affine-linear form. -/
theorem dist_lt_dist_iff_inner_lt (x a b : Position) :
    dist x a < dist x b ↔ 2 * inner ℝ (b - a) (x - a) < ‖b - a‖ ^ 2 := by
  have hexp := norm_sub_sq_real (x - a) (b - a)
  rw [sub_sub_sub_cancel_right, real_inner_comm] at hexp
  rw [dist_eq_norm, dist_eq_norm]
  constructor
  · intro h
    have hsq := (sq_lt_sq₀ (norm_nonneg (x - a)) (norm_nonneg (x - b))).2 h
    linarith only [hexp, hsq]
  · intro h
    apply (sq_lt_sq₀ (norm_nonneg (x - a)) (norm_nonneg (x - b))).1
    linarith only [hexp, h]

theorem dist_le_dist_iff_inner_le (x a b : Position) :
    dist x a ≤ dist x b ↔ 2 * inner ℝ (b - a) (x - a) ≤ ‖b - a‖ ^ 2 := by
  have hexp := norm_sub_sq_real (x - a) (b - a)
  rw [sub_sub_sub_cancel_right, real_inner_comm] at hexp
  rw [dist_eq_norm, dist_eq_norm]
  constructor
  · intro h
    have hsq := (sq_le_sq₀ (norm_nonneg (x - a)) (norm_nonneg (x - b))).2 h
    linarith only [hexp, hsq]
  · intro h
    apply (sq_le_sq₀ (norm_nonneg (x - a)) (norm_nonneg (x - b))).1
    linarith only [hexp, h]

theorem mem_voronoiCell_iff_inner (R : Fin M → Position) (k : Fin M) (x : Position) :
    x ∈ voronoiCell R k ↔
      ∀ l, l ≠ k → 2 * inner ℝ (R l - R k) (x - R k) < ‖R l - R k‖ ^ 2 := by
  simp only [voronoiCell, mem_ofPred_eq, dist_lt_dist_iff_inner_lt]

theorem voronoiCell_subset_closed (R : Fin M → Position) (k : Fin M) :
    voronoiCell R k ⊆ closedVoronoiCell R k := by
  intro x hx l
  by_cases hl : l = k
  · rw [hl]
  · exact (hx l hl).le

theorem isOpen_voronoiCell (R : Fin M → Position) (k : Fin M) :
    IsOpen (voronoiCell R k) := by
  have heq : voronoiCell R k = ⋂ l : {l : Fin M // l ≠ k},
      {x | dist x (R k) < dist x (R l)} := by
    ext x
    simp only [voronoiCell, mem_ofPred_eq, mem_iInter, Subtype.forall]
  rw [heq]
  exact isOpen_iInter_of_finite fun l => isOpen_lt
    (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)

theorem disjoint_voronoiCell (R : Fin M → Position) {k l : Fin M} (hkl : k ≠ l) :
    Disjoint (voronoiCell R k) (voronoiCell R l) := by
  rw [disjoint_left]
  intro x hx hy
  exact (hx l hkl.symm).not_gt (hy k hkl)

theorem voronoiFace_comm (R : Fin M → Position) (k l : Fin M) :
    voronoiFace R k l = voronoiFace R l k := by
  ext x
  simp only [voronoiFace, mem_ofPred_eq, mem_bisectorPlane]
  constructor <;> rintro ⟨hkl, heq, hx⟩
  · refine ⟨hkl.symm, heq.symm, ?_⟩
    intro p hpl hpk
    rw [← heq]
    exact hx p hpk hpl
  · refine ⟨hkl.symm, heq.symm, ?_⟩
    intro p hpl hpk
    rw [← heq]
    exact hx p hpk hpl

theorem voronoiFace_subset_closed (R : Fin M → Position) (k l : Fin M) :
    voronoiFace R k l ⊆ closedVoronoiCell R k := by
  rintro x ⟨hkl, heq, hx⟩ p
  by_cases hpk : p = k
  · rw [hpk]
  by_cases hpl : p = l
  · rw [hpl, (mem_bisectorPlane R k l x).mp heq]
  · exact (hx p hpk hpl).le

theorem nearestNucleusDistance_eq_of_mem_closedVoronoiCell
    (R : Fin M → Position) (k : Fin M) {x : Position}
    (hx : x ∈ closedVoronoiCell R k) :
    nearestNucleusDistance R x = ENNReal.ofReal ‖x - R k‖ := by
  apply le_antisymm
  · exact iInf_le _ k
  · apply le_iInf
    intro l
    exact ENNReal.ofReal_le_ofReal (by simpa only [dist_eq_norm] using hx l)

@[simp] theorem nearestOtherNucleusDistance_one (R : Fin 1 → Position) (k : Fin 1) :
    nearestOtherNucleusDistance R k = ⊤ := by
  apply iInf_eq_top.mpr
  intro l
  exact (l.property (Subsingleton.elim l.val k)).elim

end LiebThirring

end
