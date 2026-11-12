/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3544T1DiagonalSplit

-- [TABLET NODE: P3652T1ChildFillSeparation]

/-!
# P3652T1ChildFillSeparation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3652T1ChildFillSeparation {n : Nat} {p : P3381T1PolygonBoundary n}
    (S : P3544T1DiagonalSplit p) {XL XR : Set (Real × Real)}
    (hL : XL = P3544T1RayParity S.left ∪ P3544T1BoundaryCarrier S.left)
    (hR : XR = P3544T1RayParity S.right ∪ P3544T1BoundaryCarrier S.right)
    (hcL : IsPathConnected (P3544T1RayParity S.left))
    (hcR : IsPathConnected (P3544T1RayParity S.right)) :
    XL ∩ XR = segment Real (p.vertex S.a) (p.vertex S.b) := by
-- BODY
  let OL := P3544T1RayParity S.left
  let OR := P3544T1RayParity S.right
  let CL := P3544T1BoundaryCarrier S.left
  let CR := P3544T1BoundaryCarrier S.right
  let e := segment Real (p.vertex S.a) (p.vertex S.b)
  have heL : e ⊆ CL := by
    rw [show e = CL ∩ CR from S.carrier_intersection.symm]
    exact Set.inter_subset_left
  have heR : e ⊆ CR := by
    rw [show e = CL ∩ CR from S.carrier_intersection.symm]
    exact Set.inter_subset_right
  have hOLCR : Disjoint OL CR := by
    apply Set.disjoint_left.mpr
    intro x hx hC
    by_cases he : x ∈ e
    · exact hx.1 (heL he)
    · exact Set.disjoint_left.mp S.right_arc_even ⟨hC, he⟩ hx
  have hORCL : Disjoint OR CL := by
    apply Set.disjoint_left.mpr
    intro x hx hC
    by_cases he : x ∈ e
    · exact hx.1 (heR he)
    · exact Set.disjoint_left.mp S.left_arc_even ⟨hC, he⟩ hx
  let m := midpoint Real (p.vertex S.a) (p.vertex S.b)
  have hm : m ∈ openSegment Real (p.vertex S.a) (p.vertex S.b) :=
    midpoint_mem_openSegment _ _
  have hme : m ∈ e := openSegment_subset_segment Real _ _ hm
  obtain ⟨r, hr, s, hs⟩ := S.diagonal_sides m hm
  have hlocal : Disjoint (Metric.ball m r ∩ OL) OR := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hleft := (hs x hx.1).1.mp hx.2
    have hright := (hs x hx.1).2.mp hy
    cases s <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hleft hright <;>
      linarith
  have hclosureL : closure OL = OL ∪ CL := (P3544T1LocalParity S.left).1
  have hclosureR : closure OR = OR ∪ CR := (P3544T1LocalParity S.right).1
  have hmL : m ∈ closure OL := hclosureL.symm ▸ Or.inr (heL hme)
  have hmR : m ∈ closure OR := hclosureR.symm ▸ Or.inr (heR hme)
  obtain ⟨xL, hxL, hdL⟩ := Metric.mem_closure_iff.mp hmL r hr
  obtain ⟨xR, hxR, hdR⟩ := Metric.mem_closure_iff.mp hmR r hr
  have hbL : xL ∈ Metric.ball m r := by simpa only [Metric.mem_ball, dist_comm] using hdL
  have hbR : xR ∈ Metric.ball m r := by simpa only [Metric.mem_ball, dist_comm] using hdR
  have hxLout : xL ∈ (closure OR)ᶜ := by
    rw [hclosureR]
    rintro (ho | hc)
    · exact Set.disjoint_left.mp hlocal ⟨hbL, hxL⟩ ho
    · exact Set.disjoint_left.mp hOLCR hxL hc
  have hxRout : xR ∈ (closure OL)ᶜ := by
    rw [hclosureL]
    rintro (ho | hc)
    · exact Set.disjoint_left.mp hlocal ⟨hbR, ho⟩ hxR
    · exact Set.disjoint_left.mp hORCL hxR hc
  have hLout : OL ⊆ (closure OR)ᶜ := by
    apply hcL.isConnected.isPreconnected.subset_right_of_subset_union
      (P3544T1LocalParity S.right).2.1 isClosed_closure.isOpen_compl
      (Set.disjoint_left.mpr (fun _ hx hy => hy (subset_closure hx)))
    · intro x hx
      by_cases ho : x ∈ OR
      · exact Or.inl ho
      · apply Or.inr
        rw [hclosureR]
        exact fun h => h.elim ho (Set.disjoint_left.mp hOLCR hx)
    · exact ⟨xL, hxL, hxLout⟩
  have hRout : OR ⊆ (closure OL)ᶜ := by
    apply hcR.isConnected.isPreconnected.subset_right_of_subset_union
      (P3544T1LocalParity S.left).2.1 isClosed_closure.isOpen_compl
      (Set.disjoint_left.mpr (fun _ hx hy => hy (subset_closure hx)))
    · intro x hx
      by_cases ho : x ∈ OL
      · exact Or.inl ho
      · apply Or.inr
        rw [hclosureL]
        exact fun h => h.elim ho (Set.disjoint_left.mp hORCL hx)
    · exact ⟨xR, hxR, hxRout⟩
  rw [hL, hR]
  ext x
  constructor
  · rintro ⟨hx, hy⟩
    rcases hx with hx | hx
    · exact False.elim (hLout hx (hclosureR.symm ▸ hy))
    · rcases hy with hy | hy
      · exact False.elim (hRout hy (hclosureL.symm ▸ Or.inr hx))
      · exact S.carrier_intersection ▸ ⟨hx, hy⟩
  · intro hx
    exact ⟨Or.inr (heL hx), Or.inr (heR hx)⟩

end ApollonianSuperharmonic

end
