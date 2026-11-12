/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3019T1ChamberSegmentOrder
public import LeanPool.ApollonianSuperharmonic.P3019T1UnimodularStripWindow

-- [TABLET NODE: OrientedUnimodularStripConcatenation]

/-!
# OrientedUnimodularStripConcatenation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem OrientedUnimodularStripConcatenation
    (x : Int × Int) (a b c d : Int)
    (hab : 0 ≤ b ∧ b ≤ a) (hcd : 0 ≤ d ∧ d ≤ c)
    (horient : a * d - b * c = -1)
    (left right : List (Int × Int))
    (hleft : TriangularStripSegment x (x + (a, b)) left)
    (hright : TriangularStripSegment (x + (a, b))
      (x + (a, b) + (c, d)) right) :
    TriangularStripSegment x (x + (a, b) + (c, d))
      (left.dropLast ++ right) := by
-- BODY
  obtain ⟨ha, hc, hwindowLeft, hwindowRight⟩ :=
    P3019T1UnimodularStripWindow x a b c d hab hcd horient
  have hleftNe : x ≠ x + (a, b) := by
    intro he
    have hh := congrArg Prod.fst he
    simp only [Prod.fst_add] at hh
    omega
  have hrightNe : x + (a, b) ≠ x + (a, b) + (c, d) := by
    intro he
    have hh := congrArg Prod.fst he
    simp only [Prod.fst_add] at hh
    omega
  have htotalNe : x ≠ x + (a, b) + (c, d) := by
    intro he
    have hh := congrArg Prod.fst he
    simp only [Prod.fst_add] at hh
    omega
  have hl : left.head? = some x ∧ left.getLast? = some (x + (a, b)) ∧
      left.Nodup ∧ (∀ z ∈ left, TriangularBoundaryStrip x (x + (a, b)) z) ∧
      left.IsChain TriangularLatticeAdjacent := by
    simpa [TriangularStripSegment, hleftNe, List.IsChain] using hleft
  have hr : right.head? = some (x + (a, b)) ∧
      right.getLast? = some (x + (a, b) + (c, d)) ∧
      right.Nodup ∧ (∀ z ∈ right,
        TriangularBoundaryStrip (x + (a, b)) (x + (a, b) + (c, d)) z) ∧
      right.IsChain TriangularLatticeAdjacent := by
    simpa [TriangularStripSegment, hrightNe, List.IsChain] using hright
  have horderLeft := P3019T1ChamberSegmentOrder x a b ha hab left hleft
  have horderRight := P3019T1ChamberSegmentOrder (x + (a, b)) c d hc hcd right hright
  have hgeomLeft := P3019T1ChamberStripGeometry x a b ha hab
  have hgeomRight := P3019T1ChamberStripGeometry (x + (a, b)) c d hc hcd
  have hstrip : ∀ z ∈ left.dropLast ++ right,
      TriangularBoundaryStrip x (x + (a, b) + (c, d)) z := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · have hzLeft := List.mem_of_mem_dropLast hz
      have hbounds := horderLeft.2.2.1 z hzLeft
      have hheight := (hgeomLeft.2.1 z).mp (hl.2.2.2.1 z hzLeft)
      have hrep : x + (z.1 - x.1, z.2 - x.2) = z := by
        ext <;> simp
      have hh := hwindowLeft (z.1 - x.1) (z.2 - x.2) (by constructor <;> omega) hheight
      simpa only [hrep] using hh
    · have hbounds := horderRight.2.2.1 z hz
      have hheight := (hgeomRight.2.1 z).mp (hr.2.2.2.1 z hz)
      simp only [Prod.fst_add, Prod.snd_add] at hbounds hheight
      have hrep : x + (a, b) + (z.1 - (x.1 + a), z.2 - (x.2 + b)) = z := by
        ext <;> simp
      have hh := hwindowRight (z.1 - (x.1 + a)) (z.2 - (x.2 + b))
        (by constructor <;> omega) hheight
      simpa only [hrep] using hh
  have hleftConcat : left.dropLast ++ [x + (a, b)] = left :=
    List.dropLast_append_getLast? _ (by simp only [hl.2.1, Option.mem_def])
  have hrightCons : (x + (a, b)) :: right.tail = right :=
    List.cons_head?_tail (by simp only [hr.1, Option.mem_def])
  have hxmem : x ∈ left := List.mem_of_mem_head? (by simp [hl.1])
  have hxdrop : x ∈ left.dropLast :=
    List.mem_dropLast_of_mem_of_ne_getLast? hxmem (by
      rw [hl.2.1]
      simpa using hleftNe)
  have hdropNe : left.dropLast ≠ [] := List.ne_nil_of_mem hxdrop
  have hdropHead : left.dropLast.head? = some x := by
    have hh := congrArg List.head? hleftConcat
    rw [List.head?_append_of_ne_nil _ hdropNe] at hh
    exact hh.trans hl.1
  have hrightNonempty : right ≠ [] := by
    intro he
    simp [he] at hr
  have hnodup : (left.dropLast ++ right).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hl.2.2.1.sublist (List.dropLast_sublist left), hr.2.2.1, ?_⟩
    intro z hz y hy he
    have hzbound := horderLeft.2.2.2 z hz
    have hybound := (horderRight.2.2.1 y hy).1
    simp only [Prod.fst_add] at hybound
    have hh := congrArg Prod.fst he
    omega
  have hchain : (left.dropLast ++ right).IsChain TriangularLatticeAdjacent := by
    have hchainLeft : (left.dropLast ++ [x + (a, b)]).IsChain
        TriangularLatticeAdjacent := by
      rw [hleftConcat]
      exact hl.2.2.2.2
    have hchainRight : ([x + (a, b)] ++ right.tail).IsChain
        TriangularLatticeAdjacent := by
      simpa only [List.singleton_append, hrightCons] using hr.2.2.2.2
    have hh := hchainLeft.append_overlap hchainRight (by simp)
    simpa only [List.append_assoc, List.singleton_append, hrightCons] using hh
  rw [TriangularStripSegment, ite_eq_right htotalNe]
  refine ⟨?_, ?_, hnodup, hstrip, hchain⟩
  · rw [List.head?_append_of_ne_nil _ hdropNe]
    exact hdropHead
  · rw [List.getLast?_append_of_ne_nil _ hrightNonempty]
    exact hr.2.1

end ApollonianSuperharmonic

end
