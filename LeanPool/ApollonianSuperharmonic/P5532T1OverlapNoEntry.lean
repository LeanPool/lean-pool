/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AcyclicIndegreeOrientation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- [TABLET NODE: P5532T1OverlapNoEntry]

/-!
# P5532T1OverlapNoEntry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5532T1OverlapNoEntry (D I : Finset GaussianInt)
    (σ : GaussianInt → ℤ) (hI : I ⊆ D)
    (o : AcyclicIndegreeOrientation D σ)
    (hmass : (∑ x ∈ I, σ x) =
      ((((I.product I).filter fun e => @decide (FourNeighborAdjacent e.1 e.2)
        (Classical.propDecidable _)).card / 2 : ℕ) : ℤ)) :
    ∀ x ∈ I, ∀ y ∈ D, o.edge y x → y ∈ I := by
-- BODY
  classical
  have symm (x y : GaussianInt) (h : FourNeighborAdjacent x y) :
      FourNeighborAdjacent y x := by
    rcases h with h | h | h | h <;> subst y <;> simp [FourNeighborAdjacent]
  let B := (D.product I).filter (fun e => o.edge e.1 e.2)
  let K := (I.product I).filter (fun e => o.edge e.1 e.2)
  let K' := (I.product I).filter (fun e => o.edge e.2 e.1)
  let A := (I.product I).filter (fun e => FourNeighborAdjacent e.1 e.2)
  have hswap : K.card = K'.card := by
    apply Finset.card_bij (fun e _ => e.swap)
    · intro e he
      simpa only [K, K', Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
        Prod.fst_swap, Prod.snd_swap, and_comm] using he
    · intro e he f hf h
      exact Prod.swap_injective h
    · intro e he
      refine ⟨e.swap, ?_, by simp⟩
      simpa only [K, K', Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
        Prod.fst_swap, Prod.snd_swap, and_comm] using he
  have hdis : Disjoint K K' := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact Nat.lt_asymm (o.increasing _ _ (Finset.mem_filter.mp he).2)
      (o.increasing _ _ (Finset.mem_filter.mp hf).2)
  have hun : K ∪ K' = A := by
    ext e
    simp only [K, K', A, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨he, h⟩ | ⟨he, h⟩)
      · exact ⟨he, (o.supported _ _ h).2.2⟩
      · exact ⟨he, symm _ _ (o.supported _ _ h).2.2⟩
    · rintro ⟨he, ha⟩
      have hp := Finset.mem_product.mp he
      rcases o.oriented _ (hI hp.1) _ (hI hp.2) ha with h | h
      · exact Or.inl ⟨he, h.1⟩
      · exact Or.inr ⟨he, h.1⟩
  have hhalf : A.card / 2 = K.card := by
    have hc := Finset.card_union_of_disjoint hdis
    rw [hun, ← hswap] at hc
    omega
  have hsum : (B.card : ℤ) = ∑ x ∈ I, σ x := by
    have totals : B.card = ∑ x ∈ I, (D.filter fun y => o.edge y x).card := by
      dsimp [B]
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_product, Finset.sum_comm]
    rw [totals, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro x hx
    simpa only [decide_eq_true_eq] using o.indegree x (hI hx)
  have hBK : B.card = K.card := by
    have hm : (∑ x ∈ I, σ x) = (A.card / 2 : ℕ) := by
      simpa only [A, decide_eq_true_eq] using hmass
    rw [hm, hhalf] at hsum
    exact_mod_cast hsum
  have hsub : K ⊆ B := by
    intro e he
    obtain ⟨hp, hh⟩ := Finset.mem_filter.mp he
    have hpi := Finset.mem_product.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hI hpi.1, hpi.2⟩, hh⟩
  have heq : K = B := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro x hx y hy he
  have hm : (y, x) ∈ B :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy, hx⟩, he⟩
  rw [← heq] at hm
  exact (Finset.mem_product.mp (Finset.mem_filter.mp hm).1).1

end ApollonianSuperharmonic

end
