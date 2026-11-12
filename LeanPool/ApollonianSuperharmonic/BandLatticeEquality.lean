/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.IntegralityLatticeIndex

-- [TABLET NODE: BandLatticeEquality]

/-!
# BandLatticeEquality

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandLatticeEquality : ∀ C : BandCircle,
    IntegralityLattice C = TilingLattice C := by
-- BODY
  intro C
  classical
  obtain ⟨R, hR, hRcard⟩ := IntegralityLatticeIndex C
  obtain ⟨S, hS, hScard⟩ := TilingLatticeIndex C
  have contain : TilingLattice C ≤ IntegralityLattice C := TilingLatticeInclusion C
  let representative : GaussianInt → GaussianInt := fun x =>
    Classical.choose (hS x)
  have representative_spec (x : GaussianInt) :
      representative x ∈ S ∧ x - representative x ∈ TilingLattice C := by
    exact (Classical.choose_spec (hS x)).1
  have representative_injective : Set.InjOn representative (↑R : Set GaussianInt) := by
    intro x hx y hy hxy
    have hxS := representative_spec x
    have hyS := representative_spec y
    have hxi : x - representative x ∈ IntegralityLattice C := contain hxS.2
    have hyi : y - representative y ∈ IntegralityLattice C := contain hyS.2
    have hxyI : x - y ∈ IntegralityLattice C := by
      simpa [sub_eq_add_neg, hxy, add_assoc, add_left_comm, add_comm] using
        (IntegralityLattice C).sub_mem hxi hyi
    apply (hR x).unique
    · exact ⟨hx, (by simp)⟩
    · exact ⟨hy, hxyI⟩
  have image_eq : Finset.image representative R = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨a, ha, haz⟩ := Finset.mem_image.mp hz
      rw [← haz]
      exact (representative_spec a).1
    · rw [Finset.card_image_of_injOn representative_injective, hRcard, hScard]
  have representative_congruent (x y : GaussianInt)
      (hxy : x - y ∈ IntegralityLattice C) : representative x = representative y := by
    have hxmem : representative x ∈ Finset.image representative R := by
      rw [image_eq]
      exact (representative_spec x).1
    have hymem : representative y ∈ Finset.image representative R := by
      rw [image_eq]
      exact (representative_spec y).1
    obtain ⟨r, hr, hrf⟩ := Finset.mem_image.mp hxmem
    obtain ⟨q, hq, hqf⟩ := Finset.mem_image.mp hymem
    have hxr : x - r ∈ TilingLattice C := by
      have hsum := (TilingLattice C).add_mem (representative_spec x).2
        ((TilingLattice C).neg_mem (representative_spec r).2)
      simpa [sub_eq_add_neg, ← hrf] using hsum
    have hyq : y - q ∈ TilingLattice C := by
      have hsum := (TilingLattice C).add_mem (representative_spec y).2
        ((TilingLattice C).neg_mem (representative_spec q).2)
      simpa [sub_eq_add_neg, ← hqf] using hsum
    have hyr : y - r ∈ IntegralityLattice C := by
      have hsum := (IntegralityLattice C).add_mem
        ((IntegralityLattice C).neg_mem hxy) (contain hxr)
      convert hsum using 1; abel
    have hqr : q = r := by
      apply (hR y).unique
      · exact ⟨hq, contain hyq⟩
      · exact ⟨hr, hyr⟩
    rw [← hqf, hqr, hrf]
  apply le_antisymm
  · intro x hx
    have hrep : representative x = representative 0 :=
      representative_congruent x 0 (by simpa using hx)
    have hxf := (representative_spec x).2
    have hzero := (representative_spec 0).2
    have hdiff : x - representative 0 ∈ TilingLattice C := by
      simpa [hrep] using hxf
    have hsum := (TilingLattice C).add_mem hdiff
      ((TilingLattice C).neg_mem hzero)
    convert hsum using 1; abel
  · exact contain

end ApollonianSuperharmonic

end
