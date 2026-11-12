/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4062T1InteriorGeometry
public import LeanPool.ApollonianSuperharmonic.P4062T1ZeroIncoming
public import LeanPool.ApollonianSuperharmonic.ParentalOrientationGluing

-- [TABLET NODE: P4062T1ParentGluing]

/-!
# P4062T1ParentGluing

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4062T1ParentGluing (P : FordFareyParameter) (hP : 2 < P.q)
    (σ : GaussianInt → Int)
    (o : ∀ i, AcyclicIndegreeOrientation (P4062T1RecursiveInteriors P i) σ)
    (t₀ : AcyclicIndegreeOrientation
      (P4062T1RecursiveInteriors P 0 ∩ P4062T1RecursiveInteriors P 1) σ)
    (t₂ : AcyclicIndegreeOrientation
      (P4062T1RecursiveInteriors P 2 ∩ P4062T1RecursiveInteriors P 3) σ) :
    ∃ t : AcyclicIndegreeOrientation
      ((P4062T1RecursiveInteriors P 0 ∪ P4062T1RecursiveInteriors P 1) ∪
        (P4062T1RecursiveInteriors P 2 ∪ P4062T1RecursiveInteriors P 3)) σ,
      ∀ i, ∀ x ∈ P4062T1RecursiveInteriors P i,
        ∀ y ∈ P4062T1RecursiveInteriors P i,
          t.edge x y ↔ (o i).edge x y := by
-- BODY
  classical
  let A := P4062T1RecursiveInteriors P
  obtain ⟨hsub, hcross, hdis, hsep, hempty₂, hempty₀⟩ :=
    P4062T1InteriorGeometry P hP
  have closed (i j : Fin 4)
      (t : AcyclicIndegreeOrientation (A i ∩ A j) σ) :
      ∀ x ∈ A i ∩ A j, ∀ y ∈ A i, (o i).edge y x → y ∈ A j := by
    intro x hx y hy he
    have hc := P4062T1ZeroIncoming (A i) (A i ∩ A j) σ
      Finset.inter_subset_left (o i) t x hx y hy he
    exact (Finset.mem_inter.mp hc).2
  obtain ⟨a, ha₀, ha₁⟩ := ParentalOrientationGluing (A 0) (A 1) σ
    (o 0) (o 1) (hcross 0 1) (closed 0 1 t₀)
    (by simpa only [Finset.inter_comm] using
      (closed 1 0 (by simpa only [Finset.inter_comm] using t₀)))
  obtain ⟨b, hb₂, hb₃⟩ := ParentalOrientationGluing (A 2) (A 3) σ
    (o 2) (o 3) (hcross 2 3) (closed 2 3 t₂)
    (by simpa only [Finset.inter_comm] using
      (closed 3 2 (by simpa only [Finset.inter_comm] using t₂)))
  have hi : (A 0 ∪ A 1) ∩ (A 2 ∪ A 3) = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp hdis
  obtain ⟨t, ht₀, ht₂⟩ := ParentalOrientationGluing _ _ σ a b
    (by intro x hx _ y hy _; exact hsep x hx y hy)
    (by intro x hx; rw [hi] at hx; simp at hx)
    (by intro x hx; rw [hi] at hx; simp at hx)
  refine ⟨t, ?_⟩
  intro i x hx y hy
  fin_cases i
  · exact (ht₀ x (Finset.mem_union_left _ hx) y (Finset.mem_union_left _ hy)).trans
      (ha₀ x hx y hy)
  · exact (ht₀ x (Finset.mem_union_right _ hx) y (Finset.mem_union_right _ hy)).trans
      (ha₁ x hx y hy)
  · exact (ht₂ x (Finset.mem_union_left _ hx) y (Finset.mem_union_left _ hy)).trans
      (hb₂ x hx y hy)
  · exact (ht₂ x (Finset.mem_union_right _ hx) y (Finset.mem_union_right _ hy)).trans
      (hb₃ x hx y hy)

end ApollonianSuperharmonic

end
