/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3019T1ChamberStripGeometry
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Pairwise

-- [TABLET NODE: P3019T1ChamberSegmentOrder]

/-!
# P3019T1ChamberSegmentOrder

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3019T1ChamberSegmentOrder
    (x : Int × Int) (r s : Int) (hr : 0 < r) (hs : 0 ≤ s ∧ s ≤ r)
    (path : List (Int × Int))
    (hpath : TriangularStripSegment x (x + (r, s)) path) :
    path.IsChain (fun z y => y.1 = z.1 + 1) ∧
    path.Pairwise (fun z y => z.1 < y.1) ∧
    (∀ z ∈ path, x.1 ≤ z.1 ∧ z.1 ≤ x.1 + r) ∧
    (∀ z ∈ path.dropLast, z.1 < x.1 + r) := by
-- BODY
  have hxy : x ≠ x + (r, s) := by
    intro he
    have := congrArg Prod.fst he
    simp only [Prod.fst_add] at this
    omega
  have hdata : path.head? = some x ∧ path.getLast? = some (x + (r, s)) ∧
      path.Nodup ∧ (∀ z ∈ path, TriangularBoundaryStrip x (x + (r, s)) z) ∧
      path.IsChain TriangularLatticeAdjacent := by
    simpa [TriangularStripSegment, hxy, List.IsChain] using hpath
  have hgeom := P3019T1ChamberStripGeometry x r s hr hs
  have hinj : ∀ z ∈ path, ∀ y ∈ path, z.1 = y.1 → z = y := by
    intro z hz y hy he
    exact hgeom.2.2.1 z y (hdata.2.2.2.1 z hz) (hdata.2.2.2.1 y hy) he
  have hsteps : path.IsChain (fun z y => y.1 = z.1 + 1 ∨ z.1 = y.1 + 1) := by
    apply hdata.2.2.2.2.imp_of_mem_imp
    intro z y hz hy hadj
    have hn := (hgeom.2.2.2 z (hdata.2.2.2.1 z hz) y).mp
      ⟨hadj, hdata.2.2.2.1 y hy⟩
    rcases hn with ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
    all_goals simp [he, add_assoc]
  have walk : ∀ p : List Int, p.Nodup →
      p.IsChain (fun u v => v = u + 1 ∨ u = v + 1) →
      p.IsChain (fun u v => v = u + 1) ∨
        p.IsChain (fun u v => u = v + 1) := by
    intro p
    induction p with
    | nil => intro _ _; exact Or.inl List.IsChain.nil
    | cons a l ih =>
      intro hn hc
      cases l with
      | nil => exact Or.inl (List.IsChain.singleton a)
      | cons b t =>
        have hnot := (List.nodup_cons.mp hn).1
        have hstep := hc.rel
        rcases ih (List.nodup_cons.mp hn).2 hc.tail with hi | hd
        · rcases hstep with hp | hm
          · exact Or.inl (hi.cons_cons hp)
          · cases t with
            | nil => exact Or.inr ((List.IsChain.singleton b).cons_cons hm)
            | cons c rest =>
              have hbc := hi.rel
              have he : a = c := by omega
              exact False.elim (hnot (by simp [he]))
        · rcases hstep with hp | hm
          · cases t with
            | nil => exact Or.inl ((List.IsChain.singleton b).cons_cons hp)
            | cons c rest =>
              have hbc := hd.rel
              have he : a = c := by omega
              exact False.elim (hnot (by simp [he]))
          · exact Or.inr (hd.cons_cons hm)
  have hindnodup : (path.map Prod.fst).Nodup := hdata.2.2.1.map_on hinj
  have hindchain : (path.map Prod.fst).IsChain
      (fun u v : Int => v = u + 1 ∨ u = v + 1) :=
    (List.isChain_map _).mpr hsteps
  have hxmem : x ∈ path := List.mem_of_mem_head? (by simp [hdata.1])
  have hymem : x + (r, s) ∈ path := List.mem_of_getLast? hdata.2.1
  have hne : path ≠ [] := List.ne_nil_of_mem hxmem
  have hhead : path.head hne = x :=
    Option.some.inj ((List.head?_eq_some_head hne).symm.trans hdata.1)
  have hlast : path.getLast hne = x + (r, s) :=
    Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hdata.2.1)
  have hforward : path.IsChain (fun z y => y.1 = z.1 + 1) := by
    rcases walk _ hindnodup hindchain with hi | hd
    · exact (List.isChain_map _).mp hi
    · have hback : path.IsChain (fun z y => y.1 ≤ z.1) :=
        ((List.isChain_map _).mp hd).imp (by intro z y he; omega)
      have : Trans (fun z y : Int × Int => y.1 ≤ z.1)
          (fun z y : Int × Int => y.1 ≤ z.1)
          (fun z y : Int × Int => y.1 ≤ z.1) :=
        ⟨fun h₁ h₂ => le_trans h₂ h₁⟩
      have hh := hback.pairwise.rel_head_of_rel_head_head hymem (le_refl _)
      rw [hhead] at hh
      simp only [Prod.fst_add] at hh
      omega
  have : Trans (fun z y : Int × Int => z.1 < y.1)
      (fun z y : Int × Int => z.1 < y.1)
      (fun z y : Int × Int => z.1 < y.1) :=
    ⟨fun h₁ h₂ => lt_trans h₁ h₂⟩
  have horder : path.Pairwise (fun z y => z.1 < y.1) :=
    (hforward.imp (by intro z y he; omega)).pairwise
  have hweak : path.Pairwise (fun z y => z.1 ≤ y.1) :=
    horder.imp (by intro z y hh; exact le_of_lt hh)
  refine ⟨hforward, horder, ?_, ?_⟩
  · intro z hz
    have hlo := hweak.rel_head_of_rel_head_head hz (le_refl _)
    have hhi := hweak.rel_getLast_of_rel_getLast_getLast hz (le_refl _)
    rw [hhead] at hlo
    rw [hlast] at hhi
    exact ⟨hlo, by simpa only [Prod.fst_add] using hhi⟩
  · intro z hz
    have hh := horder.rel_dropLast_getLast hz
    rw [hlast] at hh
    simpa only [Prod.fst_add] using hh

end ApollonianSuperharmonic

end
