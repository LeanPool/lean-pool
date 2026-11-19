/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.AnnularClosePairCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# A pair is determined by two of its equidistant points

Formalizes the injectivity of the κ ledger used by Lemma J of
`docs/results/explicit-constant-gain-1-40-2026-10-21.md` (§1): in a set with no three
collinear and no four concyclic points, two pairs `{a, b}` and `{a', b'}` that have the same
two distinct equidistant points `z ≠ z'` are the same pair. The points `z, z'` need not belong
to the set.

Write `e = z' - z`. Both pairs are symmetric about the line through `z` and `z'`.

* If the pairs share a point, the third point lies on the two circles about `z` and `z'`
  through the shared point; two circles with distinct centers in the plane meet in at most two
  points, so the pairs agree.
* If the four points are distinct and `⟨e, a' - a⟩ = 0`, then `a, b, a'` lie on the line through
  `a` orthogonal to `e`, against no three collinear.
* Otherwise the point `x = z + t e` of the line `zz'` with `|xa| = |xa'|` exists, and it is at
  equal distance from all four points, against no four concyclic.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry

/-- Two circles with distinct centers `z ≠ z'` through the two points `a ≠ b` meet in no third
point: a point `x` with `|zx| = |za|` and `|z'x| = |z'a|` is `a` or `b`. -/
private lemma eq_or_eq_of_dist_eq_of_dist_eq {a b z z' x : Point} (hzz : z ≠ z') (hab : a ≠ b)
    (h1 : dist z a = dist z b) (h2 : dist z' a = dist z' b)
    (hx1 : dist z x = dist z a) (hx2 : dist z' x = dist z' a) : x = a ∨ x = b := by
  have hd : Module.finrank ℝ Point = 2 := finrank_euclideanSpace_fin
  refine eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hd hzz hab (r₁ := dist a z)
    (r₂ := dist a z') rfl ?_ ?_ rfl ?_ ?_
  · rw [dist_comm b z, ← h1, dist_comm]
  · rw [dist_comm x z, hx1, dist_comm]
  · rw [dist_comm b z', ← h2, dist_comm]
  · rw [dist_comm x z', hx2, dist_comm]

/-- Equal distances from squared distances. -/
private lemma dist_eq_of_sq_eq {x y w v : Point} (h : dist x y ^ 2 = dist w v ^ 2) :
    dist x y = dist w v :=
  (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).mp h

/-- Squared form of `|za| = |zb|` in coordinates. -/
private lemma coord_eq_of_dist_eq {z a b : Point} (h : dist z a = dist z b) :
    (z 0 - a 0) ^ 2 + (z 1 - a 1) ^ 2 = (z 0 - b 0) ^ 2 + (z 1 - b 1) ^ 2 := by
  have h2 : dist z a ^ 2 = dist z b ^ 2 := by rw [h]
  simpa only [point_dist_sq_coordinates] using h2

/-- κ injectivity. In a set with no three collinear and no four concyclic points, if the two
distinct points `z ≠ z'` are each equidistant from `a` and `b` and from `a'` and `b'`, where
`a ≠ b` and `a' ≠ b'` lie in the set, then `{a, b} = {a', b'}`, in one of the two orders. -/
theorem eq_or_swap_of_common_bisector_points {P : Finset Point} (hgp : InGeneralPosition P)
    {a b a' b' z z' : Point} (ha : a ∈ P) (hb : b ∈ P) (ha' : a' ∈ P) (hb' : b' ∈ P)
    (hab : a ≠ b) (hab' : a' ≠ b') (hzz : z ≠ z')
    (h1 : dist z a = dist z b) (h2 : dist z' a = dist z' b)
    (h3 : dist z a' = dist z b') (h4 : dist z' a' = dist z' b') :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  -- The four cases with a shared point.
  by_cases haa' : a = a'
  · subst haa'
    rcases eq_or_eq_of_dist_eq_of_dist_eq hzz hab h1 h2 h3.symm h4.symm with h | h
    · exact absurd h.symm hab'
    · exact Or.inl ⟨rfl, h.symm⟩
  by_cases hab'' : a = b'
  · subst hab''
    rcases eq_or_eq_of_dist_eq_of_dist_eq hzz hab h1 h2 h3 h4 with h | h
    · exact absurd h hab'
    · exact Or.inr ⟨rfl, h.symm⟩
  by_cases hba' : b = a'
  · subst hba'
    rcases eq_or_eq_of_dist_eq_of_dist_eq hzz hab h1 h2 (h3.symm.trans h1.symm)
        (h4.symm.trans h2.symm) with h | h
    · exact Or.inr ⟨h.symm, rfl⟩
    · exact absurd h.symm hab'
  by_cases hbb' : b = b'
  · subst hbb'
    rcases eq_or_eq_of_dist_eq_of_dist_eq hzz hab h1 h2 (h3.trans h1.symm)
        (h4.trans h2.symm) with h | h
    · exact Or.inl ⟨h.symm, rfl⟩
    · exact absurd h hab'
  -- Four distinct points.
  exfalso
  have h1c := coord_eq_of_dist_eq h1
  have h2c := coord_eq_of_dist_eq h2
  have h3c := coord_eq_of_dist_eq h3
  have h4c := coord_eq_of_dist_eq h4
  by_cases hδ : (z' 0 - z 0) * (a' 0 - a 0) + (z' 1 - z 1) * (a' 1 - a 1) = 0
  · -- `a, b, a'` lie on the line through `a` orthogonal to `e = z' - z`.
    have hq : a - (z' - z) ≠ a + (z' - z) := by
      intro h
      apply hzz
      have h0 := congrArg (fun v : Point ↦ v 0) h
      have h1' := congrArg (fun v : Point ↦ v 1) h
      simp at h0 h1'
      ext i; fin_cases i <;> simp <;> linarith
    have hmem : ∀ y : Point,
        (z' 0 - z 0) * (y 0 - a 0) + (z' 1 - z 1) * (y 1 - a 1) = 0 →
          y ∈ (AffineSubspace.perpBisector (a - (z' - z)) (a + (z' - z)) : Set Point) := by
      intro y hy
      rw [SetLike.mem_coe, AffineSubspace.mem_perpBisector_iff_dist_eq]
      apply dist_eq_of_sq_eq
      simp only [point_dist_sq_coordinates, PiLp.add_apply, PiLp.sub_apply]
      linear_combination 4 * hy
    have hcol : Collinear ℝ ({a, b, a'} : Set Point) := by
      apply collinear_subset_perpBisector hq
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact hmem _ (by ring)
      · exact hmem _ (by linear_combination (h2c - h1c) / 2)
      · exact hmem _ hδ
    exact hgp.1 ha hb ha' hab hba' haa' hcol
  · -- The point `x = z + t e` with `|xa| = |xa'|` is equidistant from all four points.
    obtain ⟨t, ht⟩ : ∃ t : ℝ,
        2 * t * ((z' 0 - z 0) * (a' 0 - a 0) + (z' 1 - z 1) * (a' 1 - a 1)) =
          ((z 0 - a' 0) ^ 2 + (z 1 - a' 1) ^ 2) - ((z 0 - a 0) ^ 2 + (z 1 - a 1) ^ 2) :=
      ⟨(((z 0 - a' 0) ^ 2 + (z 1 - a' 1) ^ 2) - ((z 0 - a 0) ^ 2 + (z 1 - a 1) ^ 2)) /
        (2 * ((z' 0 - z 0) * (a' 0 - a 0) + (z' 1 - z 1) * (a' 1 - a 1))), by field_simp⟩
    obtain ⟨x, hx⟩ : ∃ x : Point, x = z + t • (z' - z) := ⟨_, rfl⟩
    have hcoord : ∀ y : Point, dist y x ^ 2 =
        (y 0 - (z 0 + t * (z' 0 - z 0))) ^ 2 + (y 1 - (z 1 + t * (z' 1 - z 1))) ^ 2 := by
      intro y
      simp only [hx, point_dist_sq_coordinates, PiLp.add_apply, PiLp.smul_apply,
        PiLp.sub_apply, smul_eq_mul]
    have hb_x : dist b x = dist a x := by
      apply dist_eq_of_sq_eq
      rw [hcoord, hcoord]
      linear_combination (t - 1) * h1c - t * h2c
    have ha'_x : dist a' x = dist a x := by
      apply dist_eq_of_sq_eq
      rw [hcoord, hcoord]
      linear_combination (-1 : ℝ) * ht
    have hb'_x : dist b' x = dist a x := by
      rw [← ha'_x]
      apply dist_eq_of_sq_eq
      rw [hcoord, hcoord]
      linear_combination (t - 1) * h3c - t * h4c
    have hT : ({a, b, a', b'} : Finset Point) ⊆ P := by
      simp [Finset.insert_subset_iff, ha, hb, ha', hb']
    have hcard : ({a, b, a', b'} : Finset Point).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, haa', hab'']),
        Finset.card_insert_of_notMem (by simp [hba', hbb']), Finset.card_pair hab']
    refine hgp.2 _ hT hcard ⟨x, dist a x, fun y hy ↦ ?_⟩
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · rfl
    · exact hb_x
    · exact ha'_x
    · exact hb'_x

end Esgk
