/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3TwoCircleCuffs
public import LeanPool.GraphMinor.GM12.Section3BarbellCircles
public import LeanPool.GraphMinor.GM12.Section3MeetingLoopSchismatic
import LeanPool.GraphMinor.GM12.Section3SchismaticCandidate
import LeanPool.GraphMinor.GM11.PaintingFacts

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Surrounding cuffs for the two-loop schismatic shapes

VII Section 8, page 241, used by XII (3.1), page 245, asserts that
the two circles in its first two schismatic shapes surround distinct
cuffs. For disjoint loops the other loop proves each is proper. For
loops meeting once, each loop has a point other than their common
vertex, so each is again proper. The proved circle classifications
then reduce both shapes to the common two-circle cuff argument.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

universe u

/-- The two loops of a schismatic barbell surround distinct cuffs,
as asserted in VII Section 8, page 241. -/
theorem surrounding_cuffs_of_schismatic_x1
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsSurface S) (hcuffs : (cuffs S).Nonempty)
    {F A P : Set S} {a b : S}
    (hF : IsOArc F) (hA : IsOArc A) (hdis : Disjoint F A)
    (hP : IsLineWithEnds P a b) (ha : a ∈ F) (hb : b ∈ A)
    (hPF : P ∩ F = {a}) (hPA : P ∩ A = {b})
    (hX : GM07.IsSchismatic (F ∪ A ∪ P)) :
    ∃ C D : Set S, GM07.SurroundsCuff F C ∧ GM07.SurroundsCuff A D ∧ C ≠ D := by
  let := hS.1
  have hFX : F ⊂ F ∪ A ∪ P := by
    refine ⟨subset_union_left.trans subset_union_left, ?_⟩
    intro hsub
    exact Set.disjoint_left.mp hdis (hsub (Or.inl (Or.inr hb))) hb
  have hAX : A ⊂ F ∪ A ∪ P := by
    refine ⟨subset_union_right.trans subset_union_left, ?_⟩
    intro hsub
    exact Set.disjoint_left.mp hdis ha (hsub (Or.inl (Or.inl ha)))
  exact surrounding_cuffs_of_two_circle_cover hS hcuffs
    (solid_connected_of_schismatic hX).1 hF hA hFX hAX
    (fun Z hZ hZX => oArc_subset_disjoint_circle_or hF hA hdis hP ha hb hPF hPA hZ hZX) hX

/-- The two loops of a schismatic one-vertex two-loop shape surround
distinct cuffs, as asserted in VII Section 8, page 241. -/
theorem surrounding_cuffs_of_schismatic_x2
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsSurface S) (hcuffs : (cuffs S).Nonempty)
    {F A : Set S} {a : S} (hF : IsOArc F) (hA : IsOArc A) (hcap : F ∩ A = {a})
    (hX : GM07.IsSchismatic (F ∪ A)) :
    ∃ C D : Set S, GM07.SurroundsCuff F C ∧ GM07.SurroundsCuff A D ∧ C ≠ D := by
  let := hS.1
  obtain ⟨x, hxA, hxa⟩ := (infinite_of_isOArc hA).exists_notMem_finite (finite_singleton a)
  obtain ⟨y, hyF, hya⟩ := (infinite_of_isOArc hF).exists_notMem_finite (finite_singleton a)
  have hFX : F ⊂ F ∪ A := by
    refine ⟨subset_union_left, ?_⟩
    intro hsub
    exact hxa (hcap ▸ (show x ∈ F ∩ A from ⟨hsub (Or.inr hxA), hxA⟩))
  have hAX : A ⊂ F ∪ A := by
    refine ⟨subset_union_right, ?_⟩
    intro hsub
    exact hya (hcap ▸ (show y ∈ F ∩ A from ⟨hyF, hsub (Or.inl hyF)⟩))
  exact surrounding_cuffs_of_two_circle_cover hS hcuffs
    (solid_connected_of_schismatic hX).1 hF hA hFX hAX
    (fun Z hZ hZX => oArc_subset_meeting_circle_or hF hA hcap hZ hZX) hX

end GraphMinor.GM12
