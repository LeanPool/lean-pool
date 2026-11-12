/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AcyclicIndegreeOrientation
public import Mathlib.Order.Interval.Finset.Nat

/-!
# P4062T1RankedAttachment

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic


-- [TABLET NODE: P4062T1RankedAttachment]
theorem P4062T1RankedAttachment (D E : Finset GaussianInt)
    (σ : GaussianInt → Int) (d : GaussianInt → Nat)
    (hE : E ⊆ D) (o : AcyclicIndegreeOrientation E σ)
    (hres : ∀ x ∈ D \ E,
      ((@Finset.filter GaussianInt (fun y => FourNeighborAdjacent y x)
          (fun _ => Classical.propDecidable _) E).card : Int) +
        ((@Finset.filter GaussianInt (fun y => FourNeighborAdjacent y x ∧ d y < d x)
          (fun _ => Classical.propDecidable _) (D \ E)).card : Int)
          = σ x)
    (hstrict : ∀ x ∈ D \ E, ∀ y ∈ D \ E,
      FourNeighborAdjacent x y → d x ≠ d y) :
    ∃ t : AcyclicIndegreeOrientation D σ,
      (∀ x ∈ E, ∀ y ∈ E, t.edge x y ↔ o.edge x y) ∧
      (∀ x ∈ E, ∀ y ∈ D \ E, FourNeighborAdjacent x y → t.edge x y) ∧
      (∀ x ∈ D \ E, ∀ y ∈ D \ E,
        t.edge x y ↔ FourNeighborAdjacent x y ∧ d x < d y) ∧
      (∀ x ∈ E, t.rank x = o.rank x) ∧
      ∀ x ∈ D \ E, t.rank x = E.sup o.rank + 1 + d x := by
-- BODY
  classical
  let W := D \ E
  let M := E.sup o.rank
  let edge : GaussianInt → GaussianInt → Prop := fun x y =>
    o.edge x y ∨ (x ∈ E ∧ y ∈ W ∧ FourNeighborAdjacent x y) ∨
      (x ∈ W ∧ y ∈ W ∧ FourNeighborAdjacent x y ∧ d x < d y)
  let rank : GaussianInt → Nat := fun x => if x ∈ E then o.rank x else M+1+d x
  have symm (x y : GaussianInt) (h : FourNeighborAdjacent x y) :
      FourNeighborAdjacent y x := by
    rcases h with h | h | h | h <;> subst y <;> simp [FourNeighborAdjacent]
  have notW (x : GaussianInt) (hx : x ∈ E) : x ∉ W := by
    intro h
    exact (Finset.mem_sdiff.mp h).2 hx
  have support : ∀ x y, edge x y → x ∈ D ∧ y ∈ D ∧ FourNeighborAdjacent x y := by
    intro x y he
    rcases he with he | ⟨hx, hy, ha⟩ | ⟨hx, hy, ha, hd⟩
    · have hs := o.supported x y he
      exact ⟨hE hs.1, hE hs.2.1, hs.2.2⟩
    · exact ⟨hE hx, (Finset.mem_sdiff.mp hy).1, ha⟩
    · exact ⟨(Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hy).1, ha⟩
  have oriented : ∀ x ∈ D, ∀ y ∈ D, FourNeighborAdjacent x y →
      (edge x y ∧ ¬ edge y x) ∨ (edge y x ∧ ¬ edge x y) := by
    intro x hx y hy ha
    by_cases hxE : x ∈ E <;> by_cases hyE : y ∈ E
    · simpa [edge, notW x hxE, notW y hyE] using o.oriented x hxE y hyE ha
    · have hyW : y ∈ W := Finset.mem_sdiff.mpr ⟨hy, hyE⟩
      have ho : ¬ o.edge x y := fun h => hyE (o.supported x y h).2.1
      have hr : ¬ o.edge y x := fun h => hyE (o.supported y x h).1
      simp [edge, hxE, hyE, notW x hxE, hyW, ha, ho, hr]
    · have hxW : x ∈ W := Finset.mem_sdiff.mpr ⟨hx, hxE⟩
      have ho : ¬ o.edge x y := fun h => hxE (o.supported x y h).1
      have hr : ¬ o.edge y x := fun h => hxE (o.supported y x h).2.1
      simp [edge, hxE, hyE, hxW, notW y hyE, symm x y ha, ho, hr]
    · have hxW : x ∈ W := Finset.mem_sdiff.mpr ⟨hx, hxE⟩
      have hyW : y ∈ W := Finset.mem_sdiff.mpr ⟨hy, hyE⟩
      have ho : ¬ o.edge x y := fun h => hxE (o.supported x y h).1
      have hr : ¬ o.edge y x := fun h => hyE (o.supported y x h).1
      rcases lt_or_gt_of_ne (hstrict x hxW y hyW ha) with hd | hd
      · simp [edge, hxE, hyE, hxW, hyW, ho, hr, ha, hd, Nat.not_lt_of_ge hd.le]
      · simp [edge, hxE, hyE, hxW, hyW, ho, hr, symm x y ha, hd,
          Nat.not_lt_of_ge hd.le]
  have increasing : ∀ x y, edge x y → rank x < rank y := by
    intro x y he
    rcases he with he | ⟨hx, hy, ha⟩ | ⟨hx, hy, ha, hd⟩
    · have hs := o.supported x y he
      simpa only [rank, ite_eq_left hs.1, ite_eq_left hs.2.1] using o.increasing x y he
    · have hyE := (Finset.mem_sdiff.mp hy).2
      have hb : o.rank x ≤ M := Finset.le_sup hx
      simp only [rank, ite_eq_left hx, ite_eq_right hyE]
      omega
    · have hxE := (Finset.mem_sdiff.mp hx).2
      have hyE := (Finset.mem_sdiff.mp hy).2
      simp only [rank, ite_eq_right hxE, ite_eq_right hyE]
      omega
  let t : AcyclicIndegreeOrientation D σ := {
    edge := edge
    edge_decidable := fun _ _ => Classical.propDecidable _
    rank := rank
    supported := support
    oriented := oriented
    increasing := increasing
    indegree := by
      intro x hx
      simp only [decide_eq_true_eq]
      by_cases hxE : x ∈ E
      · have hf : D.filter (fun y => edge y x) = E.filter (fun y => o.edge y x) := by
          ext y
          constructor
          · intro hy
            have he := (Finset.mem_filter.mp hy).2
            rcases he with he | ⟨hyE, hxW, ha⟩ | ⟨hyW, hxW, ha, hd⟩
            · exact Finset.mem_filter.mpr ⟨(o.supported y x he).1, he⟩
            · exact (notW x hxE hxW).elim
            · exact (notW x hxE hxW).elim
          · intro hy
            have hp := Finset.mem_filter.mp hy
            exact Finset.mem_filter.mpr ⟨hE hp.1, Or.inl hp.2⟩
        rw [hf]
        simpa only [decide_eq_true_eq] using o.indegree x hxE
      · have hxW : x ∈ W := Finset.mem_sdiff.mpr ⟨hx, hxE⟩
        let N := E.filter (fun y => FourNeighborAdjacent y x)
        let L := W.filter (fun y => FourNeighborAdjacent y x ∧ d y < d x)
        have hd : Disjoint N L := by
          apply Finset.disjoint_left.mpr
          intro y hy hz
          exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).2
            (Finset.mem_filter.mp hy).1
        have hf : D.filter (fun y => edge y x) = N ∪ L := by
          ext y
          constructor
          · intro hy
            have he := (Finset.mem_filter.mp hy).2
            rcases he with he | ⟨hyE, hxW, ha⟩ | ⟨hyW, hxW, ha, hdy⟩
            · exact (hxE (o.supported y x he).2.1).elim
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyE, ha⟩)
            · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hyW, ha, hdy⟩)
          · intro hy
            rcases Finset.mem_union.mp hy with hy | hy
            · have hp := Finset.mem_filter.mp hy
              exact Finset.mem_filter.mpr
                ⟨hE hp.1, Or.inr (Or.inl ⟨hp.1, hxW, hp.2⟩)⟩
            · have hp := Finset.mem_filter.mp hy
              exact Finset.mem_filter.mpr
                ⟨(Finset.mem_sdiff.mp hp.1).1, Or.inr (Or.inr ⟨hp.1, hxW, hp.2⟩)⟩
        rw [hf, Finset.card_union_of_disjoint hd, Nat.cast_add]
        have hN : N = @Finset.filter GaussianInt (fun y => FourNeighborAdjacent y x)
            (fun _ => Classical.propDecidable _) E := by
          ext y
          simp only [N, Finset.mem_filter]
        have hL : L = @Finset.filter GaussianInt
            (fun y => FourNeighborAdjacent y x ∧ d y < d x)
            (fun _ => Classical.propDecidable _) (D \ E) := by
          ext y
          simp only [L, W, Finset.mem_filter]
        rw [hN, hL]
        exact hres x hxW }
  refine ⟨t, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    simp [t, edge, notW x hx, notW y hy]
  · intro x hx y hy ha
    exact Or.inr (Or.inl ⟨hx, hy, ha⟩)
  · intro x hx y hy
    have hxE := (Finset.mem_sdiff.mp hx).2
    have hyE := (Finset.mem_sdiff.mp hy).2
    have ho : ¬ o.edge x y := fun h => hxE (o.supported x y h).1
    have hxW : x ∈ W := hx
    have hyW : y ∈ W := hy
    simp [t, edge, hxE, ho, hxW, hyW]
  · intro x hx
    simp [t, rank, hx]
  · intro x hx
    simp [t, rank, M, (Finset.mem_sdiff.mp hx).2]

end ApollonianSuperharmonic

end
