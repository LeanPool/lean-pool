/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AcyclicIndegreeOrientation

-- [TABLET NODE: P4250T2IndegreeSubtraction]

/-!
# P4250T2IndegreeSubtraction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4250T2IndegreeSubtraction
    (D P : Finset GaussianInt) (σ : GaussianInt → ℤ)
    (hPD : P ⊆ D) (hP : Nonempty (AcyclicIndegreeOrientation P σ))
    (htotal : (∑ x ∈ D, σ x) =
      ((((D.product D).filter fun e => @decide (FourNeighborAdjacent e.1 e.2)
        (Classical.propDecidable _)).card / 2 : ℕ) : ℤ)) :
    let W := D \ P
    (∑ x ∈ W, (σ x -
      ((P.filter fun y => @decide (FourNeighborAdjacent y x)
        (Classical.propDecidable _)).card : ℤ))) =
      ((((W.product W).filter fun e => @decide (FourNeighborAdjacent e.1 e.2)
        (Classical.propDecidable _)).card / 2 : ℕ) : ℤ) := by
-- BODY
  classical
  let W := D \ P
  let count (S T : Finset GaussianInt) (r : GaussianInt → GaussianInt → Prop) : ℤ :=
    ∑ x ∈ S, ∑ y ∈ T, if r x y then 1 else 0
  have hcard (S T : Finset GaussianInt) (r : GaussianInt → GaussianInt → Prop) :
      (((S.product T).filter fun e => r e.1 e.2).card : ℤ) = count S T r := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, count]
    exact Finset.sum_product' S T (fun x y => if r x y then (1 : ℤ) else 0)
  have hswap (S T : Finset GaussianInt) (r : GaussianInt → GaussianInt → Prop) :
      count S T (fun x y => r y x) = count T S r := by
    exact Finset.sum_comm
  have adjacent_symm {x y : GaussianInt} (h : FourNeighborAdjacent x y) :
      FourNeighborAdjacent y x := by
    rcases h with h | h | h | h <;> subst y
    all_goals simp [FourNeighborAdjacent, Zsqrtd.ext_iff]
  have adjacent_comm (x y : GaussianInt) :
      FourNeighborAdjacent y x ↔ FourNeighborAdjacent x y :=
    ⟨adjacent_symm, adjacent_symm⟩
  have hcount_symm (S T : Finset GaussianInt) :
      count S T FourNeighborAdjacent = count T S FourNeighborAdjacent := by
    simpa only [adjacent_comm] using hswap S T FourNeighborAdjacent
  -- East and north select exactly one order of each lattice edge.
  let positive (x y : GaussianInt) : Prop :=
    y = x + 1 ∨ y = x + (⟨0, 1⟩ : GaussianInt)
  have hpoint (x y : GaussianInt) :
      (if FourNeighborAdjacent x y then (1 : ℤ) else 0) =
        (if positive x y then 1 else 0) + (if positive y x then 1 else 0) := by
    by_cases h : FourNeighborAdjacent x y
    · rcases h with h | h | h | h <;> subst y
      all_goals simp [positive, FourNeighborAdjacent, Zsqrtd.ext_iff]; omega
    · have hpos : ¬ positive x y := by
        rintro (hxy | hxy)
        · exact h (Or.inl hxy)
        · exact h (Or.inr (Or.inr (Or.inl hxy)))
      have hrev : ¬ positive y x := by
        rintro (hyx | hyx)
        · exact h (adjacent_symm (Or.inl hyx))
        · exact h (adjacent_symm (Or.inr (Or.inr (Or.inl hyx))))
      simp only [ite_eq_right h, ite_eq_right hpos, ite_eq_right hrev, add_zero]
  have hhalf (S : Finset GaussianInt) :
      count S S FourNeighborAdjacent =
        2 * ((((S.product S).filter fun e => FourNeighborAdjacent e.1 e.2).card /
          2 : ℕ) : ℤ) := by
    have hsum : count S S FourNeighborAdjacent =
        count S S positive + count S S (fun x y => positive y x) := by
      dsimp only [count]
      simp_rw [hpoint]
      rw [Finset.sum_congr rfl (fun x _ => Finset.sum_add_distrib),
        Finset.sum_add_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;>
        apply Finset.sum_congr rfl <;> intro y _
      all_goals split_ifs <;> rfl
    rw [hswap S S positive] at hsum
    rw [← hcard S S FourNeighborAdjacent, ← hcard S S positive] at hsum
    rw [← hcard S S FourNeighborAdjacent]
    omega
  have hdisjoint : Disjoint P W := by
    exact Finset.disjoint_left.mpr (fun x hx hw => (Finset.mem_sdiff.mp hw).2 hx)
  have hunion : D = P ∪ W := by
    symm
    exact Finset.union_sdiff_of_subset hPD
  have hsplit (f : GaussianInt → ℤ) :
      (∑ x ∈ D, f x) = (∑ x ∈ P, f x) + ∑ x ∈ W, f x := by
    rw [hunion, Finset.sum_union hdisjoint]
  have hpartition : count D D FourNeighborAdjacent =
      count P P FourNeighborAdjacent + count W W FourNeighborAdjacent +
        2 * count P W FourNeighborAdjacent := by
    calc
      _ = (count P P FourNeighborAdjacent + count P W FourNeighborAdjacent) +
          (count W P FourNeighborAdjacent + count W W FourNeighborAdjacent) := by
        dsimp only [count]
        rw [hsplit]
        simp_rw [hsplit, Finset.sum_add_distrib]
      _ = _ := by rw [hcount_symm W P]; ring
  obtain ⟨o⟩ := hP
  have hindegree : (∑ x ∈ P, σ x) = count P P o.edge := by
    calc
      _ = ∑ x ∈ P, ∑ y ∈ P, if o.edge y x then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hi := o.indegree x hx
        simpa only [Finset.card_filter, decide_eq_true_eq, Nat.cast_sum,
          Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hi.symm
      _ = _ := hswap P P o.edge
  have horient : count P P FourNeighborAdjacent = 2 * count P P o.edge := by
    have hlocal (x : GaussianInt) (hx : x ∈ P) (y : GaussianInt) (hy : y ∈ P) :
        (if FourNeighborAdjacent x y then (1 : ℤ) else 0) =
          (if o.edge x y then 1 else 0) + (if o.edge y x then 1 else 0) := by
      by_cases hxy : FourNeighborAdjacent x y
      · rcases o.oriented x hx y hy hxy with h | h
        · simp only [ite_eq_left hxy, ite_eq_left h.1, ite_eq_right h.2, add_zero]
        · simp only [ite_eq_left hxy, ite_eq_left h.1, ite_eq_right h.2, zero_add]
      · have hnot : ¬ o.edge x y := fun h => hxy (o.supported x y h).2.2
        have hnotrev : ¬ o.edge y x :=
          fun h => hxy (adjacent_symm (o.supported y x h).2.2)
        simp only [ite_eq_right hxy, ite_eq_right hnot, ite_eq_right hnotrev, add_zero]
    calc
      _ = count P P o.edge + count P P (fun x y => o.edge y x) := by
        dsimp only [count]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun y hy => hlocal x hx y hy)
      _ = _ := by rw [hswap]; ring
  have hcross :
      (∑ x ∈ W, ((P.filter fun y => @decide (FourNeighborAdjacent y x)
        (Classical.propDecidable _)).card : ℤ)) = count P W FourNeighborAdjacent := by
    rw [← hswap W P FourNeighborAdjacent]
    simp only [count, Finset.card_filter, decide_eq_true_eq, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  change (∑ x ∈ W, _) = _
  rw [Finset.sum_sub_distrib, hcross]
  have hd := hhalf D
  have hw := hhalf W
  have ht : (∑ x ∈ P, σ x) + (∑ x ∈ W, σ x) =
      ((((D.product D).filter fun e => FourNeighborAdjacent e.1 e.2).card /
        2 : ℕ) : ℤ) := by
    simpa only [hsplit, decide_eq_true_eq] using htotal
  have hfinal : (∑ x ∈ W, σ x) - count P W FourNeighborAdjacent =
      ((((W.product W).filter fun e => FourNeighborAdjacent e.1 e.2).card /
        2 : ℕ) : ℤ) := by
    linarith
  simpa only [decide_eq_true_eq] using hfinal

end ApollonianSuperharmonic

end
