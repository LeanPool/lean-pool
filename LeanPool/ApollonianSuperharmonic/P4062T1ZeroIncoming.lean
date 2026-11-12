/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AcyclicIndegreeOrientation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- [TABLET NODE: P4062T1ZeroIncoming]

/-!
# P4062T1ZeroIncoming

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4062T1ZeroIncoming (D I : Finset GaussianInt)
    (σ : GaussianInt → Int) (hI : I ⊆ D)
    (o : AcyclicIndegreeOrientation D σ)
    (t : AcyclicIndegreeOrientation I σ) :
    ∀ x ∈ I, ∀ y ∈ D, o.edge y x → y ∈ I := by
-- BODY
  classical
  have symm (x y : GaussianInt) (h : FourNeighborAdjacent x y) :
      FourNeighborAdjacent y x := by
    rcases h with h | h | h | h <;> subst y <;>
      simp [FourNeighborAdjacent]
  have directed_count (S : Finset GaussianInt) (hS : I ⊆ S)
      (a : AcyclicIndegreeOrientation S σ) :
      2 * ((I.product I).filter (fun e => a.edge e.1 e.2)).card =
        ((I.product I).filter (fun e => FourNeighborAdjacent e.1 e.2)).card := by
    let C := (I.product I).filter (fun e => a.edge e.1 e.2)
    let R := (I.product I).filter (fun e => a.edge e.2 e.1)
    have hcard : C.card = R.card := by
      apply Finset.card_bij (fun e _ => e.swap)
      · intro e he
        simp only [C, R, Finset.product_eq_sprod, Finset.mem_filter,
          Finset.mem_product, Prod.fst_swap, Prod.snd_swap] at he ⊢
        exact ⟨⟨he.1.2, he.1.1⟩, he.2⟩
      · intro e he f hf h
        exact Prod.swap_injective h
      · intro e he
        refine ⟨e.swap, ?_, by simp⟩
        simp only [C, R, Finset.product_eq_sprod, Finset.mem_filter,
          Finset.mem_product, Prod.fst_swap, Prod.snd_swap] at he ⊢
        exact ⟨⟨he.1.2, he.1.1⟩, he.2⟩
    have hdis : Disjoint C R := by
      apply Finset.disjoint_left.mpr
      intro e he hr
      have h := (Finset.mem_filter.mp he).2
      have k := (Finset.mem_filter.mp hr).2
      exact Nat.lt_asymm (a.increasing _ _ h) (a.increasing _ _ k)
    have hun : C ∪ R =
        (I.product I).filter (fun e => FourNeighborAdjacent e.1 e.2) := by
      ext e
      simp only [C, R, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨he, h⟩ | ⟨he, h⟩)
        · exact ⟨he, (a.supported _ _ h).2.2⟩
        · exact ⟨he, symm _ _ (a.supported _ _ h).2.2⟩
      · rintro ⟨he, hadj⟩
        have hp := Finset.mem_product.mp he
        rcases a.oriented _ (hS hp.1) _ (hS hp.2) hadj with h | h
        · exact Or.inl ⟨he, h.1⟩
        · exact Or.inr ⟨he, h.1⟩
    have hc := Finset.card_union_of_disjoint hdis
    rw [hun, ← hcard] at hc
    dsimp only [C] at hc
    omega
  have totals (S T : Finset GaussianInt) (r : GaussianInt → GaussianInt → Prop) :
      ((S.product T).filter (fun e => r e.1 e.2)).card =
        ∑ x ∈ T, (S.filter (fun y => r y x)).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.product_eq_sprod, Finset.sum_product, Finset.sum_comm]
  let B := (D.product I).filter (fun e => o.edge e.1 e.2)
  let C := (I.product I).filter (fun e => o.edge e.1 e.2)
  let F := (I.product I).filter (fun e => t.edge e.1 e.2)
  have hBC : C ⊆ B := by
    intro e he
    have h := Finset.mem_filter.mp he
    have hp := Finset.mem_product.mp h.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hI hp.1, hp.2⟩, h.2⟩
  have hBF : B.card = F.card := by
    rw [show B.card = _ from totals D I o.edge,
      show F.card = _ from totals I I t.edge]
    apply Finset.sum_congr rfl
    intro x hx
    have ho := o.indegree x (hI hx)
    have ht := t.indegree x hx
    have he : ((D.filter (fun y => o.edge y x)).card : Int) =
        ((I.filter (fun y => t.edge y x)).card : Int) := by
      simpa only [decide_eq_true_eq] using ho.trans ht.symm
    exact_mod_cast he
  have hCF : C.card = F.card := by
    have hc := directed_count D hI o
    have hf := directed_count I (fun _ h => h) t
    dsimp only [C, F]
    omega
  have hEq : C = B := Finset.eq_of_subset_of_card_le hBC (by omega)
  intro x hx y hy he
  have hm : (y,x) ∈ B := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hy, hx⟩, he⟩
  rw [← hEq] at hm
  exact (Finset.mem_product.mp (Finset.mem_filter.mp hm).1).1

end ApollonianSuperharmonic

end
