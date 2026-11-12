/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AcyclicIndegreeOrientation

-- [TABLET NODE: FiniteAcyclicOrientationObstruction]

/-!
# FiniteAcyclicOrientationObstruction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FiniteAcyclicOrientationObstruction
    (D : Finset GaussianInt) (g : IntegerLatticeFunction)
    (o : AcyclicIndegreeOrientation D
      (fun x => 2 + FourNeighborLaplacian g x))
    (Y : Finset GaussianInt) (hY : Y.Nonempty) (hsub : Y ⊆ D) :
    ∃ x ∈ Y, 2 ≤ FourNeighborLaplacian
      (fun z => g z - if z ∈ Y then 1 else 0) x := by
-- BODY
  classical
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image Y o.rank hY
  have hxD : x ∈ D := hsub hx
  have hsubset : Y.filter (fun y => o.edge y x) ⊆
      D.filter (fun y => @decide (o.edge y x) (o.edge_decidable y x)) := by
    intro y hy
    have hyY := (Finset.mem_filter.mp hy).1
    have hye := (Finset.mem_filter.mp hy).2
    exact Finset.mem_filter.mpr ⟨hsub hyY, by simp [hye]⟩
  have hcard : ((Y.filter (fun y => o.edge y x)).card : ℤ) ≤
      ((D.filter (fun y => @decide (o.edge y x) (o.edge_decidable y x))).card : ℤ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hneighbor : ∀ y ∈ Y, FourNeighborAdjacent x y → o.edge y x := by
    intro y hy hxy
    rcases o.oriented x hxD y (hsub hy) hxy with h | h
    · exfalso
      exact (Nat.not_lt_of_ge (hmax y hy)) (o.increasing x y h.1)
    · exact h.1
  obtain ⟨hyedge, hyedge_mem⟩ := hY
  have hcount : (Y.filter (fun y => FourNeighborAdjacent x y)).card ≤
      (Y.filter (fun y => o.edge y x)).card := by
    apply Finset.card_le_card
    intro y hy
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,
      hneighbor y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2⟩
  have hcount' : ((Y.filter (fun y => FourNeighborAdjacent x y)).card : ℤ) ≤
      ((D.filter (fun y => @decide (o.edge y x) (o.edge_decidable y x))).card : ℤ) := by
    have hcountInt : ((Y.filter (fun y => FourNeighborAdjacent x y)).card : ℤ) ≤
        ((Y.filter (fun y => o.edge y x)).card : ℤ) := by
      exact_mod_cast hcount
    exact hcountInt.trans hcard
  have hindeg := o.indegree x hxD
  rw [hindeg] at hcount'
  have hset : Y.filter (fun y => FourNeighborAdjacent x y) =
      ({x + 1, x - 1, x + ⟨0, 1⟩, x - ⟨0, 1⟩} : Finset GaussianInt).filter
        (fun y => y ∈ Y) := by
    ext y
    rw [Finset.mem_filter, Finset.mem_filter]
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    unfold FourNeighborAdjacent
    tauto
  rw [hset] at hcount'
  rw [Finset.card_filter] at hcount'
  have h12 : x + 1 ≠ x - 1 := by
    intro h
    have q := congrArg (fun z : GaussianInt => z.re) h
    simp at q
    omega
  have h13 : x + 1 ≠ x + ⟨0, 1⟩ := by
    intro h
    have q := congrArg (fun z : GaussianInt => z.im) h
    simp at q
  have h14 : x + 1 ≠ x - ⟨0, 1⟩ := by
    intro h
    have q := congrArg (fun z : GaussianInt => z.re) h
    simp at q
  have h23 : x - 1 ≠ x + ⟨0, 1⟩ := by
    intro h
    have q := congrArg (fun z : GaussianInt => z.re) h
    simp at q
  have h24 : x - 1 ≠ x - ⟨0, 1⟩ := by
    intro h
    have q := congrArg (fun z : GaussianInt => z.re) h
    simp at q
  have h34 : x + ⟨0, 1⟩ ≠ x - ⟨0, 1⟩ := by
    intro h
    have q := congrArg (fun z : GaussianInt => z.im) h
    simp at q
    omega
  have hsum : (∑ i ∈ ({x + 1, x - 1, x + ⟨0, 1⟩, x - ⟨0, 1⟩} : Finset GaussianInt),
      if i ∈ Y then 1 else 0) =
      (if x + 1 ∈ Y then 1 else 0) + (if x - 1 ∈ Y then 1 else 0) +
        (if x + ⟨0, 1⟩ ∈ Y then 1 else 0) +
          (if x - ⟨0, 1⟩ ∈ Y then 1 else 0) := by
    by_cases q1 : x + 1 ∈ Y <;> by_cases q2 : x - 1 ∈ Y <;>
      by_cases q3 : x + ⟨0, 1⟩ ∈ Y <;> by_cases q4 : x - ⟨0, 1⟩ ∈ Y <;>
      simp_all []
  rw [hsum] at hcount'
  have hineq :
      (if x + 1 ∈ Y then (1 : ℤ) else 0) +
          (if x - 1 ∈ Y then 1 else 0) +
          (if x + ⟨0, 1⟩ ∈ Y then 1 else 0) +
          (if x - ⟨0, 1⟩ ∈ Y then 1 else 0) ≤
        2 + FourNeighborLaplacian g x := by
    exact_mod_cast hcount'
  refine ⟨x, hx, ?_⟩
  unfold FourNeighborLaplacian
  simp only []
  unfold FourNeighborLaplacian at hineq
  simp? [hx] at hineq ⊢
  clear hcount'
  linarith [hineq]

end ApollonianSuperharmonic

end
