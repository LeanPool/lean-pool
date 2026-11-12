/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ParentalOrientationGluing

-- [TABLET NODE: P5532T1FiniteOrientationGluing]

/-!
# P5532T1FiniteOrientationGluing

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5532T1FiniteOrientationGluing {ι : Type*} [Fintype ι]
    (A : ι → Finset GaussianInt) (σ : GaussianInt → ℤ)
    (o : ∀ i, AcyclicIndegreeOrientation (A i) σ)
    (hcross : ∀ i j, ∀ x ∈ A i, x ∉ A j → ∀ y ∈ A j, y ∉ A i →
      ¬ FourNeighborAdjacent x y)
    (hclosed : ∀ i j, ∀ x ∈ A i ∩ A j, ∀ y ∈ A i,
      (o i).edge y x → y ∈ A j) :
    ∃ t : AcyclicIndegreeOrientation (Finset.univ.biUnion A) σ,
      ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, t.edge x y ↔ (o i).edge x y := by
-- BODY
  classical
  have run : ∀ J : Finset ι,
      ∃ t : AcyclicIndegreeOrientation (J.biUnion A) σ,
        ∀ i ∈ J, ∀ x ∈ A i, ∀ y ∈ A i, t.edge x y ↔ (o i).edge x y := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      refine ⟨{
        edge := fun _ _ => False
        edge_decidable := fun _ _ => Classical.propDecidable _
        rank := fun _ => 0
        supported := by intro x y he; cases he
        oriented := by simp
        increasing := by intro x y he; cases he
        indegree := by simp }, by simp⟩
    | @insert i J hi ih =>
      obtain ⟨a, ha⟩ := ih
      let U := J.biUnion A
      have common : ∀ x ∈ U, ∀ y ∈ U, FourNeighborAdjacent x y →
          ∃ j ∈ J, x ∈ A j ∧ y ∈ A j := by
        intro x hx y hy hxy
        obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
        obtain ⟨k, hk, hyk⟩ := Finset.mem_biUnion.mp hy
        by_cases hyj : y ∈ A j
        · exact ⟨j, hj, hxj, hyj⟩
        by_cases hxk : x ∈ A k
        · exact ⟨k, hk, hxk, hyk⟩
        exact (hcross j k x hxj hxk y hyk hyj hxy).elim
      have cross : ∀ x ∈ U, x ∉ A i → ∀ y ∈ A i, y ∉ U →
          ¬ FourNeighborAdjacent x y := by
        intro x hx hxi y hy hyU
        obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
        exact hcross j i x hxj hxi y hy (fun hyj =>
          hyU (Finset.mem_biUnion.mpr ⟨j, hj, hyj⟩))
      have closedU : ∀ x ∈ U ∩ A i, ∀ y ∈ U, a.edge y x → y ∈ A i := by
        intro x hx y hy he
        obtain ⟨j, hj, hyj, hxj⟩ := common y hy x (Finset.mem_inter.mp hx).1
          (a.supported y x he).2.2
        exact hclosed j i x (Finset.mem_inter.mpr ⟨hxj, (Finset.mem_inter.mp hx).2⟩)
          y hyj ((ha j hj y hyj x hxj).mp he)
      have closedI : ∀ x ∈ U ∩ A i, ∀ y ∈ A i, (o i).edge y x → y ∈ U := by
        intro x hx y hy he
        obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hx).1
        exact Finset.mem_biUnion.mpr ⟨j, hj, hclosed i j x
          (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).2, hxj⟩) y hy he⟩
      obtain ⟨t, htU, htI⟩ := ParentalOrientationGluing U (A i) σ a (o i)
        cross closedU closedI
      have hset : (insert i J).biUnion A = U ∪ A i := by
        simp [U, Finset.union_comm]
      rw [hset]
      refine ⟨t, ?_⟩
      intro j hj x hx y hy
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact htI x hx y hy
      · have hxU : x ∈ U := Finset.mem_biUnion.mpr ⟨j, hj, hx⟩
        have hyU : y ∈ U := Finset.mem_biUnion.mpr ⟨j, hj, hy⟩
        exact (htU x hxU y hyU).trans (ha j hj x hx y hy)
  obtain ⟨t, ht⟩ := run Finset.univ
  exact ⟨t, fun i => ht i (Finset.mem_univ i)⟩

end ApollonianSuperharmonic

end
