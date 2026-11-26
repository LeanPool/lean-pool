/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.RadialCorners
import LeanPool.GraphMinor.Surface.ArcTools

/-!
# A subline joining two points of a line

Pull two distinct points back to the unit interval and take the
closed interval between their parameters. Its image is the
required subline. This supplies the common boundary line for
any two points on a wall face's outer boundary arc.
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface GM11

/-- Any two distinct points of a line are joined by a subline. -/
theorem exists_subline_between {S : Type*} [TopologicalSpace S] [T2Space S]
    {L : Set S} {a b x y : S} (hL : IsLineWithEnds L a b)
    (hx : x ∈ L) (hy : y ∈ L) (hxy : x ≠ y) :
    ∃ K, IsLineWithEnds K x y ∧ K ⊆ L := by
  obtain ⟨e,_,_⟩ := hL
  let p : unitInterval → S := fun t => (e t).val
  let s := e.symm ⟨x,hx⟩
  let t := e.symm ⟨y,hy⟩
  have hpc : Continuous p := continuous_subtype_val.comp e.continuous
  have hpi : Function.Injective p := fun _ _ he => e.injective (Subtype.ext he)
  have hs : p s = x := congrArg Subtype.val (e.apply_symm_apply _)
  have ht : p t = y := congrArg Subtype.val (e.apply_symm_apply _)
  have hst : s ≠ t := fun he => hxy (hs.symm.trans ((congrArg p he).trans ht))
  rcases lt_or_gt_of_ne hst with h | h
  · refine ⟨p '' Icc s t,?_,?_⟩
    · simpa only [hs,ht] using isLine_piece hpc hpi h
    · rintro z ⟨u,_,rfl⟩
      exact (e u).property
  · refine ⟨p '' Icc t s,?_,?_⟩
    · have hLine := isLine_piece hpc hpi h
      rw [hs,ht] at hLine
      exact hLine.symm
    · rintro z ⟨u,_,rfl⟩
      exact (e u).property

end GraphMinor.GM16
