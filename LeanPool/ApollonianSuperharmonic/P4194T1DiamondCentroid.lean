/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCellRows
public import LeanPool.ApollonianSuperharmonic.DiamondTile
public import LeanPool.ApollonianSuperharmonic.TileCentroid
public meta import Lean.Meta.Tactic.NormCast

-- [TABLET NODE: P4194T1DiamondCentroid]

/-!
# P4194T1DiamondCentroid

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4194T1DiamondCentroid (n : Nat) (hn : 0 < n) :
    TileCentroid (DiamondTile n) = (0, (n : Real)) := by
-- BODY
  let domain := DiamondCellDomain n
  have hne : domain.Nonempty := by
    refine ⟨0, (P4194T1DiamondCellRows n 0).1.mpr ?_⟩
    norm_num
    omega
  let reflectX : GaussianInt → GaussianInt := fun z => ⟨-z.re - 1, z.im⟩
  let reflectY : GaussianInt → GaussianInt := fun z => ⟨z.re, 2 * (n : Int) - 1 - z.im⟩
  have reflectX_mem (z : GaussianInt) (hz : z ∈ domain) : reflectX z ∈ domain := by
    apply (P4194T1DiamondCellRows n (reflectX z)).1.mpr
    have h := (P4194T1DiamondCellRows n z).1.mp hz
    dsimp [reflectX]
    omega
  have reflectY_mem (z : GaussianInt) (hz : z ∈ domain) : reflectY z ∈ domain := by
    apply (P4194T1DiamondCellRows n (reflectY z)).1.mpr
    have h := (P4194T1DiamondCellRows n z).1.mp hz
    dsimp [reflectY]
    omega
  have sum_re_reflect : domain.sum (fun z => z.re) =
      domain.sum (fun z => (reflectX z).re) := by
    apply Finset.sum_bij (fun z _ => reflectX z)
    · exact fun z hz => reflectX_mem z hz
    · intro z hz w hw heq
      apply Zsqrtd.ext
      · simp [reflectX] at heq ⊢
        omega
      · simp only [Int.reduceNeg, Zsqrtd.mk.injEq, sub_left_inj, neg_inj, reflectX] at heq ⊢
        exact heq.2
    · intro z hz
      refine ⟨reflectX z, reflectX_mem z hz, ?_⟩
      apply Zsqrtd.ext <;> simp [reflectX]
    · intro z hz
      simp [reflectX]
  have sum_re_formula : domain.sum (fun z => z.re) * 2 = -(domain.card : Int) := by
    have hsum := sum_re_reflect
    simp only [reflectX] at hsum
    rw [Finset.sum_sub_distrib, Finset.sum_const] at hsum
    simp at hsum
    linarith
  have sum_im_reflect : domain.sum (fun z => z.im) =
      domain.sum (fun z => (reflectY z).im) := by
    apply Finset.sum_bij (fun z _ => reflectY z)
    · exact fun z hz => reflectY_mem z hz
    · intro z hz w hw heq
      apply Zsqrtd.ext
      · simp only [Int.reduceNeg, Zsqrtd.mk.injEq, sub_right_inj, reflectY] at heq ⊢
        exact heq.1
      · simp [reflectY] at heq ⊢
        omega
    · intro z hz
      refine ⟨reflectY z, reflectY_mem z hz, ?_⟩
      apply Zsqrtd.ext <;> simp [reflectY]
    · intro z hz
      simp [reflectY]
  have sum_im_formula : domain.sum (fun z => z.im) * 2 =
      (2 * (n : Int) - 1) * domain.card := by
    have hsum := sum_im_reflect
    simp only [reflectY] at hsum
    rw [Finset.sum_sub_distrib, Finset.sum_const] at hsum
    simp at hsum
    linarith
  change (if domain.Nonempty then
    (((domain.sum (fun z => z.re) : Int) : Real) / domain.card + (1 / 2 : Real),
     ((domain.sum (fun z => z.im) : Int) : Real) / domain.card + (1 / 2 : Real))
    else _) = _
  rw [ite_eq_left hne]
  apply Prod.ext <;> dsimp
  · have hc : (0 : Real) < domain.card := by exact_mod_cast hne.card_pos
    have hs : ((domain.sum (fun z => z.re) : Int) : Real) * 2 =
        -(domain.card : Real) := by exact_mod_cast sum_re_formula
    field_simp
    linarith
  · have hc : (0 : Real) < domain.card := by exact_mod_cast hne.card_pos
    have hs : ((domain.sum (fun z => z.im) : Int) : Real) * 2 =
        (2 * (n : Real) - 1) * domain.card := by exact_mod_cast sum_im_formula
    field_simp
    linarith

end ApollonianSuperharmonic

end
