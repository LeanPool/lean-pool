/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section5
import Mathlib.Data.Fintype.EquivFin
import LeanPool.GraphMinor.GM09.Basic

/-!
# Selecting the spokes in XVI (5.5)

At most `μ - 1` spokes meet another horn vertex. For each old path end,
at most one spoke end is too close, by the triangle inequality. Removing
both kinds of spokes leaves the `5 * μ` spokes used in (5.4).
-/

public section
namespace GraphMinor.GM16
open Set Function Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w

/-- Graph Minors XVI, proof of (5.5), Claim (1), page 57: select
`5 * μ` spokes avoiding the other horn vertices and staying far from
all the old path ends. -/
theorem theorem_5_5_select_spokes
    {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {d : Set S → Set S → ℕ} {x : α} {r μ m : ℕ}
    {P : Fin (8 * μ) → Graph α β} {ends : Fin (8 * μ) → S}
    (h : IsHorn G H η d x (2 * r) (8 * μ) P ends)
    {X : Set α} (hX : X.Finite) (hxX : x ∈ X) (hXcard : X.ncard = μ)
    {W : Set S} (hW : W.Finite) (hWH : W ⊆ H.V) (hWcard : W.ncard ≤ 2 * m)
    (hm : m < μ)
    (hsymm : ∀ a ∈ H.V, ∀ b ∈ H.V, d {a} {b} = d {b} {a})
    (htri : ∀ a ∈ H.V, ∀ b ∈ H.V, ∀ c ∈ H.V,
      d {a} {c} ≤ d {a} {b} + d {b} {c}) :
    ∃ f : Fin (5 * μ) ↪ Fin (8 * μ), ∀ i,
      V(P (f i)) ∩ X = {x} ∧ ∀ z ∈ W, r ≤ d {ends (f i)} {z} := by
  classical
  let bad : Set (Fin (8 * μ)) := {i | ∃ y ∈ X, y ∈ V(P i) ∧ y ≠ x}
  let near : Set (Fin (8 * μ)) := {i | ∃ z ∈ W, d {ends i} {z} < r}
  have hbad : bad.ncard ≤ μ - 1 := by
    let witness : Fin (8 * μ) → α := fun i =>
      if hi : i ∈ bad then (show ∃ y ∈ X, y ∈ V(P i) ∧ y ≠ x from hi).choose else x
    have hw : ∀ i ∈ bad, witness i ∈ X ∧ witness i ∈ V(P i) ∧ witness i ≠ x := by
      intro i hi
      dsimp only [witness]
      rw [dite_eq_left hi]
      exact (show ∃ y ∈ X, y ∈ V(P i) ∧ y ≠ x from hi).choose_spec
    have hinj : InjOn witness bad := by
      intro i hi j hj heq
      by_contra hij
      have hy : witness i ∈ V(P i) ∩ V(P j) :=
        ⟨(hw i hi).2.1, heq ▸ (hw j hj).2.1⟩
      rw [(h.2.2.2.2.1 i j hij).1] at hy
      exact (hw i hi).2.2 (mem_singleton_iff.mp hy)
    have hbound := ncard_le_ncard_of_injOn witness
      (fun i hi => show witness i ∈ X \ {x} from ⟨(hw i hi).1, (hw i hi).2.2⟩)
      hinj hX.sdiff
    have hcount := ncard_sdiff' (singleton_subset_iff.mpr hxX) hX
    rw [ncard_singleton, hXcard] at hcount
    omega
  have hnear : near.ncard ≤ W.ncard := by
    let witness : Fin (8 * μ) → S := fun i =>
      if hi : i ∈ near then (show ∃ z ∈ W, d {ends i} {z} < r from hi).choose else ends i
    have hw : ∀ i ∈ near, witness i ∈ W ∧ d {ends i} {witness i} < r := by
      intro i hi
      dsimp only [witness]
      rw [dite_eq_left hi]
      exact (show ∃ z ∈ W, d {ends i} {z} < r from hi).choose_spec
    have hinj : InjOn witness near := by
      intro i hi j hj heq
      by_contra hij
      have hbound := htri (ends i) (h.2.1 i) (witness i) (hWH (hw i hi).1)
        (ends j) (h.2.1 j)
      rw [hsymm (witness i) (hWH (hw i hi).1) (ends j) (h.2.1 j)] at hbound
      have hd := h.2.2.2.2.2 i j hij
      have hdi := (hw i hi).2
      have hdj := (hw j hj).2
      rw [← heq] at hdj
      omega
    exact ncard_le_ncard_of_injOn witness (fun i hi => (hw i hi).1) hinj hW
  let good : Set (Fin (8 * μ)) := univ \ (bad ∪ near)
  have hgood : 5 * μ ≤ good.ncard := by
    have hu := ncard_union_le bad near
    have hc := ncard_sdiff' (subset_univ (bad ∪ near)) (toFinite univ)
    have hall : (univ : Set (Fin (8 * μ))).ncard = 8 * μ := by simp
    change 5 * μ ≤ (univ \ (bad ∪ near)).ncard
    omega
  let : Fintype good := Fintype.ofFinite good
  have hcard : Fintype.card (Fin (5 * μ)) ≤ Fintype.card good := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hgood
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨f.trans ⟨Subtype.val, Subtype.val_injective⟩, ?_⟩
  intro i
  have hi : (f i).val ∉ bad ∧ (f i).val ∉ near := by
    simpa only [good, mem_sdiff, mem_univ, true_and, mem_union, not_or] using (f i).property
  constructor
  · apply Set.Subset.antisymm
    · rintro y ⟨hyP, hyX⟩
      apply mem_singleton_iff.mpr
      by_contra hne
      exact hi.1 ⟨y, hyX, hyP, hne⟩
    · rintro y rfl
      exact ⟨(h.2.2.1 (f i).val).left_mem, hxX⟩
  · intro z hz
    exact Nat.le_of_not_gt (fun hd => hi.2 ⟨z, hz, hd⟩)

end GraphMinor.GM16
