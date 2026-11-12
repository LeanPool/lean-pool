/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3544T1DiagonalSplit
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Convex

-- [TABLET NODE: P3652T1ParentOddGluing]

/-!
# P3652T1ParentOddGluing

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3652T1ParentOddGluing {n : Nat} {p : P3381T1PolygonBoundary n}
    (S : P3544T1DiagonalSplit p) {XL XR : Set (Real × Real)}
    (hL : XL = P3544T1RayParity S.left ∪ P3544T1BoundaryCarrier S.left)
    (hR : XR = P3544T1RayParity S.right ∪ P3544T1BoundaryCarrier S.right)
    (hcL : IsPathConnected (P3544T1RayParity S.left))
    (hcR : IsPathConnected (P3544T1RayParity S.right))
    (hsep : XL ∩ XR = segment Real (p.vertex S.a) (p.vertex S.b)) :
    P3544T1RayParity p = P3544T1RayParity S.left ∪
      P3544T1RayParity S.right ∪ openSegment Real (p.vertex S.a) (p.vertex S.b) ∧
    XL ∪ XR = P3544T1RayParity p ∪ P3544T1BoundaryCarrier p ∧
    IsPathConnected (P3544T1RayParity p) := by
-- BODY
  let OL := P3544T1RayParity S.left
  let OR := P3544T1RayParity S.right
  let CL := P3544T1BoundaryCarrier S.left
  let CR := P3544T1BoundaryCarrier S.right
  let e := segment Real (p.vertex S.a) (p.vertex S.b)
  let d := openSegment Real (p.vertex S.a) (p.vertex S.b)
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
  have hdis : Disjoint OL OR := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hxy : x ∈ XL ∩ XR := ⟨hL.symm ▸ Or.inl hx, hR.symm ▸ Or.inl hy⟩
    have he : x ∈ e := by rwa [hsep] at hxy
    exact hx.1 (heL he)
  have hCp : P3544T1BoundaryCarrier p ⊆ CL ∪ CR := by
    intro x hx
    exact S.carrier_union.symm ▸ Or.inl hx
  have hv (i : Fin (n + 3)) : p.vertex i ∈ P3544T1BoundaryCarrier p :=
    Set.mem_iUnion.mpr ⟨i, left_mem_segment Real _ _⟩
  have hodd : P3544T1RayParity p = OL ∪ OR ∪ d := by
    ext x
    constructor
    · intro hx
      by_cases hC : x ∈ CL ∪ CR
      · have he : x ∈ e := (S.carrier_union ▸ hC).resolve_left hx.1
        exact Or.inr (mem_openSegment_of_ne_left_right
          (fun h => hx.1 (h ▸ hv S.a)) (fun h => hx.1 (h ▸ hv S.b)) he)
      · have hnL : x ∉ CL := fun h => hC (Or.inl h)
        have hnR : x ∉ CR := fun h => hC (Or.inr h)
        exact Or.inl ((S.parity_sum x hnL hnR).mp hx |>.elim
          (fun h => Or.inl h.1) (fun h => Or.inr h.2))
    · rintro ((hx | hx) | hx)
      · apply (S.parity_sum x hx.1 (Set.disjoint_left.mp hOLCR hx)).mpr
        exact Or.inl ⟨hx, Set.disjoint_left.mp hdis hx⟩
      · apply (S.parity_sum x (Set.disjoint_left.mp hORCL hx) hx.1).mpr
        exact Or.inr ⟨fun h => Set.disjoint_left.mp hdis h hx, hx⟩
      · exact S.diagonal_odd hx
  have heCp : e ⊆ d ∪ P3544T1BoundaryCarrier p := by
    intro x hx
    by_cases ha : p.vertex S.a = x
    · exact Or.inr (ha ▸ hv S.a)
    by_cases hb : p.vertex S.b = x
    · exact Or.inr (hb ▸ hv S.b)
    exact Or.inl (mem_openSegment_of_ne_left_right ha hb hx)
  have hfill : XL ∪ XR = P3544T1RayParity p ∪ P3544T1BoundaryCarrier p := by
    rw [hL, hR, hodd]
    change (OL ∪ CL) ∪ (OR ∪ CR) = (OL ∪ OR ∪ d) ∪ P3544T1BoundaryCarrier p
    apply Set.Subset.antisymm
    · intro x hx
      rcases hx with (hx | hx) | (hx | hx)
      · exact Or.inl (Or.inl (Or.inl hx))
      · have hC : x ∈ CL ∪ CR := Or.inl hx
        rw [show CL ∪ CR = P3544T1BoundaryCarrier p ∪ e from S.carrier_union] at hC
        rcases hC with hc | he
        · exact Or.inr hc
        · exact (heCp he).elim (fun h => Or.inl (Or.inr h)) Or.inr
      · exact Or.inl (Or.inl (Or.inr hx))
      · have hC : x ∈ CL ∪ CR := Or.inr hx
        rw [show CL ∪ CR = P3544T1BoundaryCarrier p ∪ e from S.carrier_union] at hC
        rcases hC with hc | he
        · exact Or.inr hc
        · exact (heCp he).elim (fun h => Or.inl (Or.inr h)) Or.inr
    · intro x
      rintro (((hx | hx) | hx) | hx)
      · exact Or.inl (Or.inl hx)
      · exact Or.inr (Or.inl hx)
      · exact Or.inl (Or.inr (heL (openSegment_subset_segment Real _ _ hx)))
      · exact (hCp hx).elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h))
  let m := midpoint Real (p.vertex S.a) (p.vertex S.b)
  have hm : m ∈ d := midpoint_mem_openSegment _ _
  have hme : m ∈ e := openSegment_subset_segment Real _ _ hm
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (P3544T1LocalParity p).2.1 m
    (S.diagonal_odd hm)
  have hmL : m ∈ closure OL := (P3544T1LocalParity S.left).1.symm ▸ Or.inr (heL hme)
  have hmR : m ∈ closure OR := (P3544T1LocalParity S.right).1.symm ▸ Or.inr (heR hme)
  obtain ⟨xL, hxL, hdL⟩ := Metric.mem_closure_iff.mp hmL r hr
  obtain ⟨xR, hxR, hdR⟩ := Metric.mem_closure_iff.mp hmR r hr
  have hbL : xL ∈ Metric.ball m r := by simpa only [Metric.mem_ball, dist_comm] using hdL
  have hbR : xR ∈ Metric.ball m r := by simpa only [Metric.mem_ball, dist_comm] using hdR
  have hb : m ∈ Metric.ball m r := Metric.mem_ball_self hr
  have hballc := (convex_ball m r).isPathConnected ⟨m, hb⟩
  have hdc := (convex_openSegment (p.vertex S.a) (p.vertex S.b)).isPathConnected ⟨m, hm⟩
  have hconn := ((hcL.union hballc ⟨xL, hxL, hbL⟩).union hcR
    ⟨xR, Or.inr hbR, hxR⟩).union hdc ⟨m, Or.inl (Or.inr hb), hm⟩
  have heq : ((OL ∪ Metric.ball m r) ∪ OR) ∪ d = P3544T1RayParity p := by
    rw [hodd]
    have hsub : Metric.ball m r ⊆ OL ∪ OR ∪ d := hodd ▸ hball
    ext x
    constructor
    · rintro (((hx | hx) | hx) | hx)
      · exact Or.inl (Or.inl hx)
      · exact hsub hx
      · exact Or.inl (Or.inr hx)
      · exact Or.inr hx
    · rintro ((hx | hx) | hx)
      · exact Or.inl (Or.inl (Or.inl hx))
      · exact Or.inl (Or.inr hx)
      · exact Or.inr hx
  exact ⟨hodd, hfill, heq ▸ hconn⟩

end ApollonianSuperharmonic

end
