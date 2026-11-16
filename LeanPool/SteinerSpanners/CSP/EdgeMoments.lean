/-
Copyright (c) 2026 Goran Zuzic et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Goran Zuzic, David P. Woodruff, Vahab Mirrokni
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Analysis.Complex.ExponentialBounds

public import LeanPool.SteinerSpanners.CSP.CherryMoments

/-! # Edge Moments for spanner CSP codes

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib.
-/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners.Proofs.CSP

noncomputable section Helpers

private lemma homQueries_membership : ∀ {N0 q0 : ℕ} (z : Fin N0 → Fin q0)
      (t : Fin N0 × Fin N0 × Fin q0 × Fin q0),
      t ∈ homQueries z ↔ t.1 < t.2.1 ∧ t.2.2.1 = z t.1 ∧ t.2.2.2 = z t.2.1 := by
  intro N0 q0 z ⟨u, v, c₁, c₂⟩
  simp only [homQueries, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨u', v'⟩, huv, rfl, rfl, h1, h2⟩
    exact ⟨huv, h1.symm, h2.symm⟩
  · rintro ⟨huv, rfl, rfl⟩
    exact ⟨(u, v), huv, rfl, rfl, rfl, rfl⟩

private lemma edgeMoments_hbound1 :
    ∀ (N0 q0 r0 : ℕ) (x y : Fin N0 → Fin q0),
      dHam x y = r0 →
        (∀ (z : Fin N0 → Fin q0), {v ∈ disagreeSet x y | z v = y v} ⊆ disagreeSet x z) →
          ∀ b ≤ r0,
            let B_of : (Fin N0 → Fin q0) → Finset (Fin N0) := fun (z : Fin N0 → Fin q0) => {v ∈
                disagreeSet x y | z v = y v};
            let F_b : Finset (Fin N0 → Fin q0) := {z : Fin N0 → Fin q0 | dHam x z = r0 ∧ (B_of
                z).card = b};
            let S₁ : Finset (Finset (Fin N0)) := Finset.powersetCard b (disagreeSet x y);
            ∀ B ∈ S₁, {z ∈ F_b | B_of z = B}.card ≤ (N0 - b).choose (r0 - b) * (q0 - (1 : ℕ)) ^
                (r0 - b) := by
  classical
  intro N0 q0 r0 x y hdxy hB_sub_xz b hb B_of F_b S₁ B hB
  let T_of : (Fin N0 → Fin q0) → Finset (Fin N0) := fun (z : Fin N0 → Fin q0) => disagreeSet x z
      \ B_of z
  have hB_card : B.card = b := (Finset.mem_powersetCard.mp hB).2
  let S₂ := (Finset.univ \ B).powersetCard (r0 - b)
  have hS₂_card : S₂.card = (N0 - b).choose (r0 - b) := by
    rw [Finset.card_powersetCard]
    have hadd := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
    rw [Finset.card_univ, Fintype.card_fin, hB_card] at hadd
    have hcard_u : (Finset.univ \ B).card = N0 - b := by omega
    rw [hcard_u]
  have hmaps2 : ∀ z ∈ F_b.filter (fun z => B_of z = B), T_of z ∈ S₂ := by
    intro z hz
    simp only [F_b, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro v hv
      simp only [T_of, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv ⊢
      rw [← hz.2]
      exact hv.2
    · have hsub : B_of z ⊆ disagreeSet x z := hB_sub_xz z
      have hadd := Finset.card_sdiff_add_card_eq_card hsub
      change (T_of z).card + (B_of z).card = dHam x z at hadd
      omega
  have hfib2 : (F_b.filter (fun z => B_of z = B)).card =
      ∑ T ∈ S₂, ((F_b.filter (fun z => B_of z = B)).filter (fun z => T_of z = T)).card := by
    simp_rw [Finset.card_eq_sum_ones]
    exact (Finset.sum_fiberwise_of_maps_to hmaps2 _).symm
  have hbound2 : ∀ T ∈ S₂,
      ((F_b.filter (fun z => B_of z = B)).filter (fun z => T_of z = T)).card ≤
        (q0 - 1) ^ (r0 - b) := by
    intro T hT
    have hT_card : T.card = r0 - b := (Finset.mem_powersetCard.mp hT).2
    let P_target := Fintype.piFinset (fun v : ↥T => Finset.univ.erase (x v.1))
    have hP_card : P_target.card = (q0 - 1) ^ (r0 - b) := by
      rw [Fintype.card_piFinset]
      have h1 : ∀ v : ↥T, (Finset.univ.erase (x v.1)).card = q0 - 1 := by
        intro v
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      simp_rw [h1]
      simp [Finset.prod_const, hT_card]
    rw [← hP_card]
    apply Finset.card_le_card_of_injOn (fun z (v : ↥T) => z v.1)
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter] at hz
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro v
      have hvT : v.1 ∈ T_of z := by rw [hz.2]; exact v.2
      simp only [T_of, disagreeSet, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
        true_and] at hvT
      exact Finset.mem_erase.mpr ⟨hvT.1.symm, Finset.mem_univ _⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hz₁ hz₂
      funext w
      by_cases hwB : w ∈ B
      · have h1 : w ∈ B_of z₁ := by rwa [hz₁.1.2]
        have h2 : w ∈ B_of z₂ := by rwa [hz₂.1.2]
        simp only [B_of, Finset.mem_filter] at h1 h2
        rw [h1.2, h2.2]
      · by_cases hwT : w ∈ T
        · exact congr_fun heq ⟨w, hwT⟩
        · have hn1 : w ∉ disagreeSet x z₁ := by
            intro hd
            have hTw : w ∈ T_of z₁ := Finset.mem_sdiff.mpr ⟨hd, by rwa [hz₁.1.2]⟩
            rw [hz₁.2] at hTw
            exact hwT hTw
          have hn2 : w ∉ disagreeSet x z₂ := by
            intro hd
            have hTw : w ∈ T_of z₂ := Finset.mem_sdiff.mpr ⟨hd, by rwa [hz₂.1.2]⟩
            rw [hz₂.2] at hTw
            exact hwT hTw
          simp only [disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
              at hn1 hn2
          rw [← hn1, ← hn2]
  rw [hfib2]
  calc
    ∑ T ∈ S₂, ((F_b.filter (fun z => B_of z = B)).filter (fun z => T_of z = T)).card
      ≤ S₂.card • ((q0 - 1) ^ (r0 - b)) := Finset.sum_le_card_nsmul _ _ _ hbound2
    _ = (N0 - b).choose (r0 - b) * (q0 - 1) ^ (r0 - b) := by rw [hS₂_card, smul_eq_mul]

private lemma queryTripleCardinalityAndFibers : ∀ (N0 q0 r0 : ℕ) (x y : Fin N0 → Fin q0),
    dHam x y = r0 →
        (∀ z : Fin N0 → Fin q0, dHam x z = r0 →
          ((disagreeSet x y).filter (fun v => z v = y v)).card ≤ r0 ∧
          (homQueries x ∪ homQueries y).card +
            ((r0 - ((disagreeSet x y).filter (fun v => z v = y v)).card) * (N0 - 1) -
             (r0 - ((disagreeSet x y).filter (fun v => z v = y v)).card).choose 2) ≤
            (homQueries x ∪ homQueries y ∪ homQueries z).card) ∧
        (∀ b : ℕ, b ≤ r0 →
          (Finset.univ.filter (fun z : Fin N0 → Fin q0 =>
            dHam x z = r0 ∧
            ((disagreeSet x y).filter (fun v => z v = y v)).card = b)).card ≤
            r0.choose b * (N0 - b).choose (r0 - b) * (q0 - 1) ^ (r0 - b)) := by
  intro N0 q0 r0 x y hdxy
  have hB_sub_xz : ∀ z : Fin N0 → Fin q0,
      (disagreeSet x y).filter (fun v => z v = y v) ⊆ disagreeSet x z := by
    intro z v hv
    simp only [disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rw [hv.2]
    exact hv.1
  constructor
  · intro z hdxz
    let B := (disagreeSet x y).filter (fun v => z v = y v)
    let b := B.card
    have hb_le : b ≤ r0 := by
      rw [← hdxy]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    refine ⟨hb_le, ?_⟩
    let T := disagreeSet x z \ B
    have hT_card : T.card = r0 - b := by
      have hadd := Finset.card_sdiff_add_card_eq_card (hB_sub_xz z)
      change T.card + b = dHam x z at hadd
      omega
    have hT_ne : ∀ w ∈ T, z w ≠ x w ∧ z w ≠ y w := by
      intro w hw
      simp only [T, B, disagreeSet, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
        true_and, not_and] at hw
      refine ⟨hw.1.symm, fun hzy => ?_⟩
      apply hw.2
      · rw [← hzy]
        exact hw.1
      · exact hzy
    have hfresh := freshHomQueryCardinality z ({x, y} : Finset (Fin N0 → Fin q0)) T (by
      intro v hv a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact (hT_ne v hv).1
      · have : a = y := Finset.mem_singleton.mp ha
        subst a
        exact (hT_ne v hv).2)
    simp only [Finset.biUnion_insert, Finset.singleton_biUnion] at hfresh
    have hunion3 : (homQueries x ∪ homQueries y ∪ homQueries z).card =
        (homQueries x ∪ homQueries y).card +
        (homQueries z \ (homQueries x ∪ homQueries y)).card := by
      rw [← Finset.union_sdiff_self_eq_union (s := homQueries x ∪ homQueries y) (t := homQueries z),
        Finset.card_union_of_disjoint disjoint_sdiff_self_right]
    change (homQueries x ∪ homQueries y).card +
      ((r0 - b) * (N0 - 1) - (r0 - b).choose 2) ≤ _
    rw [hunion3]
    exact Nat.add_le_add_left (by simpa only [hT_card] using hfresh) _
  · intro b hb
    let B_of : (Fin N0 → Fin q0) → Finset (Fin N0) :=
      fun z => (disagreeSet x y).filter (fun v => z v = y v)
    let T_of : (Fin N0 → Fin q0) → Finset (Fin N0) :=
      fun z => disagreeSet x z \ B_of z
    let F_b := Finset.univ.filter (fun z : Fin N0 → Fin q0 => dHam x z = r0 ∧ (B_of z).card = b)
    let S₁ := (disagreeSet x y).powersetCard b
    have hS₁_card : S₁.card = r0.choose b := by
      rw [Finset.card_powersetCard, ← hdxy]
    have hmaps1 : ∀ z ∈ F_b, B_of z ∈ S₁ := by
      intro z hz
      simp only [F_b, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.filter_subset _ _, hz.2⟩
    have hfib1 : F_b.card = ∑ B ∈ S₁, (F_b.filter (fun z => B_of z = B)).card := by
      simp_rw [Finset.card_eq_sum_ones]
      exact (Finset.sum_fiberwise_of_maps_to hmaps1 _).symm
    have hbound1 :=
      @edgeMoments_hbound1 N0 q0 r0 x y hdxy hB_sub_xz b hb
    change F_b.card ≤ _
    rw [hfib1, mul_assoc]
    calc
      ∑ B ∈ S₁, (F_b.filter (fun z => B_of z = B)).card
        ≤ S₁.card • ((N0 - b).choose (r0 - b) * (q0 - 1) ^ (r0 - b)) :=
          Finset.sum_le_card_nsmul _ _ _ hbound1
      _ = r0.choose b * ((N0 - b).choose (r0 - b) * (q0 - 1) ^ (r0 - b)) := by
          rw [hS₁_card, smul_eq_mul]

private lemma edgeMoments_h_props :
    ∀ (N0 q0 : ℕ) (x y x' y' : Fin N0 → Fin q0),
      let K₁ : Finset (Fin N0) := {v : Fin N0 | x' v = x v ∨ x' v = y v};
      let K₂ : Finset (Fin N0) := {v ∈ disagreeSet x' y' | y' v = x v ∨ y' v = y v};
      let S : Finset (Fin N0 ⊕ Fin N0) := K₁.disjSum K₂;
      let I : Finset (Fin N0 × Fin N0 × Fin q0 × Fin q0) := (homQueries x ∪ homQueries y) ∩
          (homQueries x' ∪ homQueries y');
      let τ : Fin N0 → Fin N0 ⊕ Fin N0 := fun (w : Fin N0) => if x' w = y' w then Sum.inl w else
          Sum.inr w;
      let π : Fin N0 ⊕ Fin N0 → Fin N0 := Sum.elim id id;
      let γ_col : Fin N0 ⊕ Fin N0 → Fin q0 := Sum.elim x' y';
      (∀ (w : Fin N0), γ_col (τ w) = y' w) →
        (∀ (w : Fin N0), y' w = x w ∨ y' w = y w → τ w ∈ S) →
          let α_map : Fin N0 × Fin N0 × Fin q0 × Fin q0 → Fin N0 ⊕ Fin N0 := fun (t : Fin N0 ×
              Fin N0 × Fin q0 × Fin q0) =>
            if t.2.2.1 = x' t.1 ∧ t.2.2.2 = x' t.2.1 then Sum.inl t.1 else τ t.1;
          let β_map : Fin N0 × Fin N0 × Fin q0 × Fin q0 → Fin N0 ⊕ Fin N0 := fun (t : Fin N0 ×
              Fin N0 × Fin q0 × Fin q0) =>
            if t.2.2.1 = x' t.1 ∧ t.2.2.2 = x' t.2.1 then Sum.inl t.2.1 else τ t.2.1;
          (∀ (t : Fin N0 × Fin N0 × Fin q0 × Fin q0), π (α_map t) = t.1) →
            (∀ (t : Fin N0 × Fin N0 × Fin q0 × Fin q0), π (β_map t) = t.2.1) →
              ∀ t ∈ I,
                t.1 < t.2.1 ∧
                  α_map t ≠ β_map t ∧ α_map t ∈ S ∧ β_map t ∈ S ∧ γ_col (α_map t) = t.2.2.1 ∧
                      γ_col (β_map t) = t.2.2.2 := by
  classical
  intro N0 q0 x y x' y' K₁ K₂ S I τ π γ_col hγ_τ hτ_mem α_map β_map hπ_α hπ_β t ht
  simp only [I, Finset.mem_inter, Finset.mem_union, homQueries_membership] at ht
  have hlt : t.1 < t.2.1 := by
    rcases ht.1 with h | h <;> exact h.1
  have hc1_xy : t.2.2.1 = x t.1 ∨ t.2.2.1 = y t.1 := by
    rcases ht.1 with h | h
    · exact Or.inl h.2.1
    · exact Or.inr h.2.1
  have hc2_xy : t.2.2.2 = x t.2.1 ∨ t.2.2.2 = y t.2.1 := by
    rcases ht.1 with h | h
    · exact Or.inl h.2.2
    · exact Or.inr h.2.2
  have hne_αβ : α_map t ≠ β_map t := by
    intro heq
    have hp := congr_arg π heq
    rw [hπ_α, hπ_β] at hp
    exact (ne_of_lt hlt) hp
  refine ⟨hlt, hne_αβ, ?_⟩
  by_cases hx' : t.2.2.1 = x' t.1 ∧ t.2.2.2 = x' t.2.1
  · have hα_eq : α_map t = Sum.inl t.1 := ite_eq_left hx'
    have hβ_eq : β_map t = Sum.inl t.2.1 := ite_eq_left hx'
    rw [hα_eq, hβ_eq]
    refine ⟨?_, ?_, hx'.1.symm, hx'.2.symm⟩
    · rw [Finset.inl_mem_disjSum]
      simp only [K₁, Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [← hx'.1]
    · rw [Finset.inl_mem_disjSum]
      simp only [K₁, Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [← hx'.2]
  · have hy' : t.2.2.1 = y' t.1 ∧ t.2.2.2 = y' t.2.1 := by
      rcases ht.2 with h | h
      · exact absurd ⟨h.2.1, h.2.2⟩ hx'
      · exact ⟨h.2.1, h.2.2⟩
    have hα_eq : α_map t = τ t.1 := ite_eq_right hx'
    have hβ_eq : β_map t = τ t.2.1 := ite_eq_right hx'
    rw [hα_eq, hβ_eq]
    refine ⟨hτ_mem t.1 (by rwa [← hy'.1]), hτ_mem t.2.1 (by rwa [← hy'.2]), ?_, ?_⟩
    · rw [hγ_τ, hy'.1]
    · rw [hγ_τ, hy'.2]

private lemma edgeMoments_hX_bound :
    ∀ (N0 q0 : ℕ) (x y : Fin N0 → Fin q0),
      ∀ k₁ : ℕ,
        let K₁_of : (Fin N0 → Fin q0) → Finset (Fin N0) := fun (x' : Fin N0 → Fin q0) =>
          {v : Fin N0 | x' v = x v ∨ x' v = y v};
        let X_fib : Finset (Fin N0 → Fin q0) := {x' : Fin N0 → Fin q0 | (K₁_of x').card = k₁};
        X_fib.card ≤ N0.choose k₁ * (2 : ℕ) ^ k₁ * q0 ^ (N0 - k₁) := by
  classical
  intro N0 q0 x y k₁ K₁_of X_fib
  let S_K₁ := (Finset.univ : Finset (Fin N0)).powersetCard k₁
  have hSK₁_card : S_K₁.card = N0.choose k₁ := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hmaps_x : ∀ x' ∈ X_fib, K₁_of x' ∈ S_K₁ := by
    intro x' hx'
    simp only [X_fib, Finset.mem_filter, Finset.mem_univ, true_and] at hx'
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hx'⟩
  have hfib_x : X_fib.card = ∑ K₁ ∈ S_K₁, (X_fib.filter (fun x' => K₁_of x' = K₁)).card := by
    simp_rw [Finset.card_eq_sum_ones]
    exact (Finset.sum_fiberwise_of_maps_to hmaps_x _).symm
  have hbx : ∀ K₁ ∈ S_K₁,
      (X_fib.filter (fun x' => K₁_of x' = K₁)).card ≤ 2 ^ k₁ * q0 ^ (N0 - k₁) := by
    intro K₁ hK₁
    have hK₁_card : K₁.card = k₁ := (Finset.mem_powersetCard.mp hK₁).2
    let U_target : Finset ((↥K₁ → Bool) × (↥(Finset.univ \ K₁) → Fin q0)) := Finset.univ
    have hU_card : U_target.card = 2 ^ k₁ * q0 ^ (N0 - k₁) := by
      simp [U_target, Fintype.card_bool, hK₁_card]
    rw [← hU_card]
    apply Finset.card_le_card_of_injOn
      (fun x' => ((fun v : ↥K₁ => decide (x' v.1 = x v.1)),
                  (fun w : ↥(Finset.univ \ K₁) => x' w.1)))
    · intro x' _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro x'₁ hx₁ x'₂ hx₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hx₁ hx₂
      simp only [Prod.mk.injEq] at heq
      funext u
      by_cases hu : u ∈ K₁
      · have hdec := congr_fun heq.1 ⟨u, hu⟩
        have hu1 : u ∈ K₁_of x'₁ := by rwa [hx₁.2]
        have hu2 : u ∈ K₁_of x'₂ := by rwa [hx₂.2]
        simp only [K₁_of, Finset.mem_filter, Finset.mem_univ, true_and] at hu1 hu2
        by_cases hxu1 : x'₁ u = x u
        · simp only [hxu1, decide_true, true_eq_decide_iff] at hdec
          rw [hxu1, hdec]
        · simp only [hxu1, decide_false, false_eq_decide_iff] at hdec
          have hy1 : x'₁ u = y u := hu1.resolve_left hxu1
          have hy2 : x'₂ u = y u := hu2.resolve_left hdec
          rw [hy1, hy2]
      · exact congr_fun heq.2 ⟨u, Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, hu⟩⟩
  rw [hfib_x, mul_assoc]
  calc
    ∑ K₁ ∈ S_K₁, (X_fib.filter (fun x' => K₁_of x' = K₁)).card
      ≤ S_K₁.card • (2 ^ k₁ * q0 ^ (N0 - k₁)) := Finset.sum_le_card_nsmul _ _ _ hbx
    _ = N0.choose k₁ * (2 ^ k₁ * q0 ^ (N0 - k₁)) := by rw [hSK₁_card, smul_eq_mul]

private lemma edgeMoments_hY_bound :
    ∀ (N0 q0 r0 : ℕ) (x y : Fin N0 → Fin q0) (k₂ : ℕ),
        let K₂_of : (Fin N0 → Fin q0) → (Fin N0 → Fin q0) → Finset (Fin N0) := fun (x' y' : Fin
            N0 → Fin q0) =>
          {v ∈ disagreeSet x' y' | y' v = x v ∨ y' v = y v};
        let Y_fib : (Fin N0 → Fin q0) → Finset (Fin N0 → Fin q0) := fun (x' : Fin N0 → Fin q0) =>
          {y' : Fin N0 → Fin q0 | dHam x' y' = r0 ∧ (K₂_of x' y').card = k₂};
        ∀ (x' : Fin N0 → Fin q0), (Y_fib x').card ≤ N0.choose r0 * r0.choose k₂ * (2 : ℕ) ^ k₂ *
            (q0 - (1 : ℕ)) ^ (r0 - k₂) := by
  classical
  intro N0 q0 r0 x y k₂ K₂_of Y_fib x'
  let S_D := (Finset.univ : Finset (Fin N0)).powersetCard r0
  have hSD_card : S_D.card = N0.choose r0 := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hmaps_D : ∀ y' ∈ Y_fib x', disagreeSet x' y' ∈ S_D := by
    intro y' hy'
    simp only [Y_fib, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hy'.1⟩
  have hfib_D : (Y_fib x').card =
      ∑ D ∈ S_D, ((Y_fib x').filter (fun y' => disagreeSet x' y' = D)).card := by
    simp_rw [Finset.card_eq_sum_ones]
    exact (Finset.sum_fiberwise_of_maps_to hmaps_D _).symm
  have hbD : ∀ D ∈ S_D,
      ((Y_fib x').filter (fun y' => disagreeSet x' y' = D)).card ≤
        r0.choose k₂ * (2 ^ k₂ * (q0 - 1) ^ (r0 - k₂)) := by
    intro D hD
    have hD_card : D.card = r0 := (Finset.mem_powersetCard.mp hD).2
    let S_K₂ := D.powersetCard k₂
    have hSK₂_card : S_K₂.card = r0.choose k₂ := by
      rw [Finset.card_powersetCard, hD_card]
    have hmaps_K₂ : ∀ y' ∈ (Y_fib x').filter (fun y' => disagreeSet x' y' = D),
        K₂_of x' y' ∈ S_K₂ := by
      intro y' hy'
      simp only [Y_fib, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
      rw [Finset.mem_powersetCard]
      refine ⟨?_, hy'.1.2⟩
      rw [← hy'.2]
      exact Finset.filter_subset _ _
    have hfib_K₂ : ((Y_fib x').filter (fun y' => disagreeSet x' y' = D)).card =
        ∑ K₂ ∈ S_K₂, (((Y_fib x').filter (fun y' => disagreeSet x' y' = D)).filter
          (fun y' => K₂_of x' y' = K₂)).card := by
      simp_rw [Finset.card_eq_sum_ones]
      exact (Finset.sum_fiberwise_of_maps_to hmaps_K₂ _).symm
    have hbK₂ : ∀ K₂ ∈ S_K₂,
        (((Y_fib x').filter (fun y' => disagreeSet x' y' = D)).filter
          (fun y' => K₂_of x' y' = K₂)).card ≤ 2 ^ k₂ * (q0 - 1) ^ (r0 - k₂) := by
      intro K₂ hK₂
      obtain ⟨hK₂_sub, hK₂_card⟩ := Finset.mem_powersetCard.mp hK₂
      have hsdiff_card : (D \ K₂).card = r0 - k₂ := by
        have hadd := Finset.card_sdiff_add_card_eq_card hK₂_sub
        rw [hD_card, hK₂_card] at hadd
        omega
      let B_univ : Finset (↥K₂ → Bool) := Finset.univ
      let P_rem := Fintype.piFinset (fun w : ↥(D \ K₂) => Finset.univ.erase (x' w.1))
      have hBP_card : (B_univ ×ˢ P_rem).card = 2 ^ k₂ * (q0 - 1) ^ (r0 - k₂) := by
        rw [Finset.card_product]
        have hB : B_univ.card = 2 ^ k₂ := by simp [B_univ, Fintype.card_bool, hK₂_card]
        have hP : P_rem.card = (q0 - 1) ^ (r0 - k₂) := by
          rw [Fintype.card_piFinset]
          have h1 : ∀ w : ↥(D \ K₂), (Finset.univ.erase (x' w.1)).card = q0 - 1 := by
            intro w
            rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
          simp_rw [h1]
          simp [Finset.prod_const, hsdiff_card]
        rw [hB, hP]
      rw [← hBP_card]
      apply Finset.card_le_card_of_injOn
        (fun y' => ((fun v : ↥K₂ => decide (y' v.1 = x v.1)),
                    (fun w : ↥(D \ K₂) => y' w.1)))
      · intro y' hy'
        simp only [Finset.mem_coe, Finset.mem_filter] at hy'
        rw [Finset.mem_coe, Finset.mem_product]
        refine ⟨Finset.mem_univ _, Fintype.mem_piFinset.mpr (fun w => ?_)⟩
        have hwD : w.1 ∈ disagreeSet x' y' := by
          rw [hy'.1.2]
          exact (Finset.mem_sdiff.mp w.2).1
        simp only [disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hwD
        exact Finset.mem_erase.mpr ⟨hwD.symm, Finset.mem_univ _⟩
      · intro y'₁ hy₁ y'₂ hy₂ heq
        simp only [Finset.mem_coe, Finset.mem_filter] at hy₁ hy₂
        simp only [Prod.mk.injEq] at heq
        funext u
        by_cases huK₂ : u ∈ K₂
        · have hdec := congr_fun heq.1 ⟨u, huK₂⟩
          have hu1 : u ∈ K₂_of x' y'₁ := by rwa [hy₁.2]
          have hu2 : u ∈ K₂_of x' y'₂ := by rwa [hy₂.2]
          simp only [K₂_of, Finset.mem_filter] at hu1 hu2
          by_cases hxu1 : y'₁ u = x u
          · simp only [hxu1, decide_true, true_eq_decide_iff] at hdec
            rw [hxu1, hdec]
          · simp only [hxu1, decide_false, false_eq_decide_iff] at hdec
            have hyu1 : y'₁ u = y u := hu1.2.resolve_left hxu1
            have hyu2 : y'₂ u = y u := hu2.2.resolve_left hdec
            rw [hyu1, hyu2]
        · by_cases huD : u ∈ D
          · exact congr_fun heq.2 ⟨u, Finset.mem_sdiff.mpr ⟨huD, huK₂⟩⟩
          · have hn1 : u ∉ disagreeSet x' y'₁ := by rwa [hy₁.1.2]
            have hn2 : u ∉ disagreeSet x' y'₂ := by rwa [hy₂.1.2]
            simp only [disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
              at hn1 hn2
            rw [← hn1, ← hn2]
    rw [hfib_K₂]
    calc
      ∑ K₂ ∈ S_K₂, (((Y_fib x').filter (fun y' => disagreeSet x' y' = D)).filter
          (fun y' => K₂_of x' y' = K₂)).card
        ≤ S_K₂.card • (2 ^ k₂ * (q0 - 1) ^ (r0 - k₂)) := Finset.sum_le_card_nsmul _ _ _ hbK₂
      _ = r0.choose k₂ * (2 ^ k₂ * (q0 - 1) ^ (r0 - k₂)) := by
          rw [hSK₂_card, smul_eq_mul]
  calc
    (Y_fib x').card
      = ∑ D ∈ S_D, ((Y_fib x').filter (fun y' => disagreeSet x' y' = D)).card := hfib_D
    _ ≤ S_D.card • (r0.choose k₂ * (2 ^ k₂ * (q0 - 1) ^ (r0 - k₂))) :=
        Finset.sum_le_card_nsmul _ _ _ hbD
    _ = N0.choose r0 * r0.choose k₂ * 2 ^ k₂ * (q0 - 1) ^ (r0 - k₂) := by
        rw [hSD_card, smul_eq_mul]
        ring

private lemma queryPairIntersectionAndFibers : ∀ (N0 q0 r0 : ℕ),
      ∀ (x y : Fin N0 → Fin q0),
        (∀ x' y' : Fin N0 → Fin q0,
          ((homQueries x ∪ homQueries y) ∩ (homQueries x' ∪ homQueries y')).card ≤
            ((Finset.univ.filter (fun v : Fin N0 => x' v = x v ∨ x' v = y v)).card +
             ((disagreeSet x' y').filter (fun v : Fin N0 => y' v = x v ∨ y' v = y
                 v)).card).choose 2) ∧
        (∀ k₁ k₂ : ℕ,
          (Finset.univ.filter (fun xy' : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) =>
            dHam xy'.1 xy'.2 = r0 ∧
            (Finset.univ.filter (fun v : Fin N0 => xy'.1 v = x v ∨ xy'.1 v = y v)).card = k₁ ∧
            ((disagreeSet xy'.1 xy'.2).filter (fun v : Fin N0 => xy'.2 v = x v ∨ xy'.2 v = y
                v)).card = k₂)).card ≤
            N0.choose k₁ * 2 ^ k₁ * q0 ^ (N0 - k₁) *
              (N0.choose r0 * r0.choose k₂ * 2 ^ k₂ * (q0 - 1) ^ (r0 - k₂))) := by
  intro N0 q0 r0 x y
  constructor
  · intro x' y'
    let K₁ := Finset.univ.filter (fun v : Fin N0 => x' v = x v ∨ x' v = y v)
    let K₂ := (disagreeSet x' y').filter (fun v : Fin N0 => y' v = x v ∨ y' v = y v)
    let S : Finset (Fin N0 ⊕ Fin N0) := K₁.disjSum K₂
    let I := (homQueries x ∪ homQueries y) ∩ (homQueries x' ∪ homQueries y')
    have hS_pow_card : (S.powersetCard 2).card = (K₁.card + K₂.card).choose 2 := by
      rw [Finset.card_powersetCard, Finset.card_disjSum]
    change I.card ≤ _
    rw [← hS_pow_card]
    let τ : Fin N0 → Fin N0 ⊕ Fin N0 := fun w => if x' w = y' w then Sum.inl w else Sum.inr w
    let π : Fin N0 ⊕ Fin N0 → Fin N0 := Sum.elim id id
    let γ_col : Fin N0 ⊕ Fin N0 → Fin q0 := Sum.elim x' y'
    have hπ_τ : ∀ w : Fin N0, π (τ w) = w := by
      intro w
      dsimp [π, τ]
      split_ifs <;> rfl
    have hγ_τ : ∀ w : Fin N0, γ_col (τ w) = y' w := by
      intro w
      dsimp [γ_col, τ]
      split_ifs with h
      · exact h
      · rfl
    have hτ_mem : ∀ w : Fin N0, (y' w = x w ∨ y' w = y w) → τ w ∈ S := by
      intro w hw
      dsimp [τ, S]
      split_ifs with heq_xy
      · rw [Finset.inl_mem_disjSum]
        simp only [K₁, Finset.mem_filter, Finset.mem_univ, true_and]
        rwa [heq_xy]
      · rw [Finset.inr_mem_disjSum]
        simp only [K₂, disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨heq_xy, hw⟩
    let α_map : Fin N0 × Fin N0 × Fin q0 × Fin q0 → Fin N0 ⊕ Fin N0 :=
      fun t => if t.2.2.1 = x' t.1 ∧ t.2.2.2 = x' t.2.1 then Sum.inl t.1 else τ t.1
    let β_map : Fin N0 × Fin N0 × Fin q0 × Fin q0 → Fin N0 ⊕ Fin N0 :=
      fun t => if t.2.2.1 = x' t.1 ∧ t.2.2.2 = x' t.2.1 then Sum.inl t.2.1 else τ t.2.1
    let Ψ : Fin N0 × Fin N0 × Fin q0 × Fin q0 → Finset (Fin N0 ⊕ Fin N0) :=
      fun t => {α_map t, β_map t}
    have hπ_α : ∀ t, π (α_map t) = t.1 := by
      intro t
      dsimp [α_map]
      split_ifs
      · rfl
      · exact hπ_τ t.1
    have hπ_β : ∀ t, π (β_map t) = t.2.1 := by
      intro t
      dsimp [β_map]
      split_ifs
      · rfl
      · exact hπ_τ t.2.1
    have h_props : ∀ t ∈ I,
        t.1 < t.2.1 ∧ α_map t ≠ β_map t ∧ α_map t ∈ S ∧ β_map t ∈ S ∧
        γ_col (α_map t) = t.2.2.1 ∧ γ_col (β_map t) = t.2.2.2 :=
      @edgeMoments_h_props N0 q0 x y x' y' hγ_τ hτ_mem hπ_α hπ_β
    apply Finset.card_le_card_of_injOn Ψ
    · intro t ht
      rw [Finset.mem_coe] at ht ⊢
      obtain ⟨_, hne, hαS, hβS, _, _⟩ := h_props t ht
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair hne⟩
      intro z hz
      simp only [Ψ, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hαS
      · exact hβS
    · intro t₁ ht₁ t₂ ht₂ heq
      rw [Finset.mem_coe] at ht₁ ht₂
      obtain ⟨hlt₁, hne₁, _, _, hγα₁, hγβ₁⟩ := h_props t₁ ht₁
      obtain ⟨hlt₂, _, _, _, hγα₂, hγβ₂⟩ := h_props t₂ ht₂
      have hα_mem : α_map t₁ ∈ ({α_map t₂, β_map t₂} : Finset _) := by
        change α_map t₁ ∈ Ψ t₂
        rw [← heq]
        exact Finset.mem_insert_self _ _
      have hβ_mem : β_map t₁ ∈ ({α_map t₂, β_map t₂} : Finset _) := by
        change β_map t₁ ∈ Ψ t₂
        rw [← heq]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hα_mem hβ_mem
      have hα_eq : α_map t₁ = α_map t₂ := by
        rcases hα_mem with h1 | h1
        · exact h1
        · exfalso
          have hβ_eq : β_map t₁ = α_map t₂ := by
            rcases hβ_mem with h2 | h2
            · exact h2
            · exfalso; apply hne₁; rw [h1, h2]
          have hp1 := congr_arg π h1
          have hp2 := congr_arg π hβ_eq
          rw [hπ_α, hπ_β] at hp1
          rw [hπ_β, hπ_α] at hp2
          have : t₂.2.1 < t₂.2.1 := by
            calc
              t₂.2.1 = t₁.1 := hp1.symm
              _ < t₁.2.1 := hlt₁
              _ = t₂.1 := hp2
              _ < t₂.2.1 := hlt₂
          exact lt_irrefl _ this
      have hβ_eq : β_map t₁ = β_map t₂ := by
        rcases hβ_mem with h2 | h2
        · exfalso; apply hne₁; rw [hα_eq, h2]
        · exact h2
      have hu_eq : t₁.1 = t₂.1 := by
        have hp := congr_arg π hα_eq
        rwa [hπ_α, hπ_α] at hp
      have hv_eq : t₁.2.1 = t₂.2.1 := by
        have hp := congr_arg π hβ_eq
        rwa [hπ_β, hπ_β] at hp
      have hc1_eq : t₁.2.2.1 = t₂.2.2.1 := by
        rw [← hγα₁, ← hγα₂, hα_eq]
      have hc2_eq : t₁.2.2.2 = t₂.2.2.2 := by
        rw [← hγβ₁, ← hγβ₂, hβ_eq]
      rcases t₁ with ⟨u₁, v₁, c₁₁, c₁₂⟩
      rcases t₂ with ⟨u₂, v₂, c₂₁, c₂₂⟩
      simp only [Prod.mk.injEq] at hu_eq hv_eq hc1_eq hc2_eq ⊢
      exact ⟨hu_eq, hv_eq, hc1_eq, hc2_eq⟩
  · intro k₁ k₂
    let K₁_of : (Fin N0 → Fin q0) → Finset (Fin N0) :=
      fun x' => Finset.univ.filter (fun v : Fin N0 => x' v = x v ∨ x' v = y v)
    let K₂_of : (Fin N0 → Fin q0) → (Fin N0 → Fin q0) → Finset (Fin N0) :=
      fun x' y' => (disagreeSet x' y').filter (fun v : Fin N0 => y' v = x v ∨ y' v = y v)
    let F_pair := Finset.univ.filter (fun xy' : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) =>
      dHam xy'.1 xy'.2 = r0 ∧ (K₁_of xy'.1).card = k₁ ∧ (K₂_of xy'.1 xy'.2).card = k₂)
    let X_fib := Finset.univ.filter (fun x' : Fin N0 → Fin q0 => (K₁_of x').card = k₁)
    let Y_fib : (Fin N0 → Fin q0) → Finset (Fin N0 → Fin q0) :=
      fun x' => Finset.univ.filter (fun y' : Fin N0 → Fin q0 =>
        dHam x' y' = r0 ∧ (K₂_of x' y').card = k₂)
    have hX_bound :=
      @edgeMoments_hX_bound N0 q0 x y k₁
    have hY_bound :=
      @edgeMoments_hY_bound N0 q0 r0 x y k₂
    have hmaps_pair : ∀ xy' ∈ F_pair, xy'.1 ∈ X_fib := by
      intro xy' hxy'
      simp only [F_pair, X_fib, Finset.mem_filter, Finset.mem_univ, true_and] at hxy' ⊢
      exact hxy'.2.1
    have hfib_pair : F_pair.card = ∑ x' ∈ X_fib, (F_pair.filter (fun xy' => xy'.1 = x')).card := by
      simp_rw [Finset.card_eq_sum_ones]
      exact (Finset.sum_fiberwise_of_maps_to hmaps_pair _).symm
    have hpair_snd : ∀ x' ∈ X_fib, (F_pair.filter (fun xy' => xy'.1 = x')).card ≤ (Y_fib
        x').card := by
      intro x' _
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro xy' hxy'
        simp only [F_pair, Y_fib, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_univ, true_and] at hxy' ⊢
        rw [← hxy'.2]
        exact ⟨hxy'.1.1, hxy'.1.2.2⟩
      · intro a ha b hb heq
        simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
        exact Prod.ext (ha.2.trans hb.2.symm) heq
    change F_pair.card ≤ _
    rw [hfib_pair]
    calc
      ∑ x' ∈ X_fib, (F_pair.filter (fun xy' => xy'.1 = x')).card
        ≤ X_fib.card • (N0.choose r0 * r0.choose k₂ * 2 ^ k₂ * (q0 - 1) ^ (r0 - k₂)) := by
          refine Finset.sum_le_card_nsmul _ _ _ (fun x' hx' => ?_)
          exact le_trans (hpair_snd x' hx') (hY_bound x')
      _ = X_fib.card * (N0.choose r0 * r0.choose k₂ * 2 ^ k₂ * (q0 - 1) ^ (r0 - k₂)) :=
          smul_eq_mul _ _
      _ ≤ (N0.choose k₁ * 2 ^ k₁ * q0 ^ (N0 - k₁)) *
            (N0.choose r0 * r0.choose k₂ * 2 ^ k₂ * (q0 - 1) ^ (r0 - k₂)) :=
          Nat.mul_le_mul_right _ hX_bound

private lemma exponentialGammaBound : ∀ r0 : ℕ,
      Real.exp ((r0 : ℝ) * ((2 : ℝ) ^ (- (999 : ℝ)))) ≤ cspGamma r0 := by
  intro r0
  unfold cspGamma
  conv_rhs => rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have h999 : (2 : ℝ) ^ (- (999 : ℝ)) = (1 / 2 : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) := by
    have h1 : (- (999 : ℝ)) = (- (1 : ℝ)) - ((998 : ℕ) : ℝ) := by push_cast; norm_num
    rw [h1, Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
      show (2 : ℝ) ^ (- (1 : ℝ)) = 1 / 2 by norm_num, Real.rpow_natCast]
  rw [h999]
  have hrew : (r0 : ℝ) * ((1 / 2 : ℝ) / ((2 : ℝ) ^ (998 : ℕ))) =
      (1 / 2 : ℝ) * ((r0 : ℝ) / ((2 : ℝ) ^ (998 : ℕ))) := by
    generalize ((2 : ℝ) ^ (998 : ℕ)) = d998
    ring
  rw [hrew]
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hden_pos : (0 : ℝ) < (2 : ℝ) ^ (998 : ℕ) := pow_pos (by norm_num) 998
  have hfrac_nn : (0 : ℝ) ≤ (r0 : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) :=
    div_nonneg (Nat.cast_nonneg r0) (le_of_lt hden_pos)
  exact mul_le_mul_of_nonneg_right hlog hfrac_nn

private lemma edgeMoments_h_term :
    ∀ (L r0 q1 lam0 gamma0 : ℕ) (σ D_star : ℝ),
      (3001 : ℕ) ≤ r0 →
        (3000 : ℕ) ≤ lam0 →
          gamma0 = (5 : ℕ) * lam0 →
            (0 : ℝ) < σ →
              (0 : ℝ) ≤ D_star →
                (6 : ℝ) * (↑lam0 : ℝ) ≤ σ * (↑r0 : ℝ) / (2 : ℝ) →
                  let N0 : ℕ := (2 : ℕ) ^ L * r0;
                  let p_e : ℝ := (2 : ℝ) ^ (-σ);
                  let D_om : ℝ := (↑(N0.choose r0) : ℝ) * (↑q1 : ℝ) ^ r0 * p_e ^ (r0 * (N0 - (1
                      : ℕ)) - r0.choose (2 : ℕ));
                  r0 ≤ N0 →
                    (0 : ℝ) < (↑q1 : ℝ) →
                      (0 : ℝ) < p_e →
                        let G : ℝ := (2 : ℝ) ^ (↑gamma0 : ℝ);
                        (0 : ℝ) < G →
                          (4 : ℝ) * G * (2 : ℝ) ^ L * (↑q1 : ℝ) * p_e ^ (N0 - (1 : ℕ)) = (1 : ℝ) →
                            (∀ b ≤ r0, (N0 - b).choose (r0 - b) * ((2 : ℕ) ^ L) ^ b ≤ N0.choose
                                r0) →
                              (0 : ℝ) < D_om →
                                let ε : ℝ := (2 : ℝ) ^ (-999 : ℝ);
                                ∀ b ∈ Finset.range (r0 + (1 : ℕ)),
                                  D_star / D_om *
                                      ((↑(r0.choose b) : ℝ) * (↑((N0 - b).choose (r0 - b)) : ℝ)
                                          * (↑q1 : ℝ) ^ (r0 - b) *
                                        p_e ^ ((r0 - b) * (N0 - (1 : ℕ)) - (r0 - b).choose (2 :
                                            ℕ))) ≤
                                    D_star * ((↑(r0.choose b) : ℝ) * ε ^ b) := by
  classical
  intro L r0 q1 lam0 gamma0 σ D_star hr_ge hlam0_ge hgam_eq hσ_pos0 hD_nn hσ_low0 N0 p_e D_om
      hrN hq1_pos hpe_pos G hG_pos h_cal1 h_binom_ratio hDOm_pos ε b hb_mem
  have hb : b ≤ r0 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb_mem)
  let E_r := r0 * (N0 - 1) - r0.choose 2
  let E_s := (r0 - b) * (N0 - 1) - (r0 - b).choose 2
  let Δ_b := r0.choose 2 - (r0 - b).choose 2
  have hch_mono : (r0 - b).choose 2 ≤ r0.choose 2 :=
    Nat.choose_le_choose 2 (Nat.sub_le r0 b)
  have hch_r : r0.choose 2 ≤ r0 * (N0 - 1) := choose_two_le_product r0 hrN
  have hch_s : (r0 - b).choose 2 ≤ (r0 - b) * (N0 - 1) :=
    choose_two_le_product (r0 - b) (le_trans (Nat.sub_le _ _) hrN)
  have hmul_split : (r0 - b) * (N0 - 1) + b * (N0 - 1) = r0 * (N0 - 1) := by
    rw [← add_mul, Nat.sub_add_cancel hb]
  have hexp_id : E_s + b * (N0 - 1) = E_r + Δ_b := by omega
  have hcal_b : (4 : ℝ) ^ b * G ^ b * ((2 : ℝ) ^ L) ^ b * (q1 : ℝ) ^ b * p_e ^ (b * (N0 - 1)) =
      1 := by
    have hp := congr_arg (· ^ b) h_cal1
    change ((4 : ℝ) * G * (2 : ℝ) ^ L * (q1 : ℝ) * p_e ^ (N0 - 1)) ^ b = 1 ^ b at hp
    rw [one_pow, mul_pow, mul_pow, mul_pow, mul_pow,
      ← pow_mul p_e (N0 - 1) b, mul_comm (N0 - 1) b] at hp
    exact hp
  have hq_pow : (q1 : ℝ) ^ (r0 - b) * (q1 : ℝ) ^ b = (q1 : ℝ) ^ r0 := by
    rw [← pow_add, Nat.sub_add_cancel hb]
  have hpe_pow : p_e ^ E_s * p_e ^ (b * (N0 - 1)) = p_e ^ E_r * p_e ^ Δ_b := by
    rw [← pow_add, hexp_id, pow_add]
  have hbin_real : (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * ((2 : ℝ) ^ L) ^ b ≤
      (N0.choose r0 : ℝ) := by
    have hcast : (((N0 - b).choose (r0 - b) * (2 ^ L) ^ b : ℕ) : ℝ) ≤ (N0.choose r0 : ℝ) := by
      exact_mod_cast h_binom_ratio b hb
    push_cast at hcast
    exact hcast
  have hT_le : (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * (q1 : ℝ) ^ (r0 - b)) *
      p_e ^ E_s) ≤
      D_om * ((r0.choose b : ℝ) * ((4 : ℝ) ^ b * G ^ b * p_e ^ Δ_b)) := by
    have h1 : (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * (q1 : ℝ) ^ (r0 - b)) *
        p_e ^ E_s) =
        ((((N0 - b).choose (r0 - b) : ℕ) : ℝ) * ((2 : ℝ) ^ L) ^ b) *
        ((r0.choose b : ℝ) * (4 : ℝ) ^ b * G ^ b * (q1 : ℝ) ^ r0 * p_e ^ E_r * p_e ^ Δ_b) := by
      calc
        (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * (q1 : ℝ) ^ (r0 - b)) * p_e
            ^ E_s)
          = (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * (q1 : ℝ) ^ (r0 - b)) *
              p_e ^ E_s) *
            ((4 : ℝ) ^ b * G ^ b * ((2 : ℝ) ^ L) ^ b * (q1 : ℝ) ^ b * p_e ^ (b * (N0 - 1))) := by
              rw [hcal_b, mul_one]
        _ = ((((N0 - b).choose (r0 - b) : ℕ) : ℝ) * ((2 : ℝ) ^ L) ^ b) *
            ((r0.choose b : ℝ) * (4 : ℝ) ^ b * G ^ b * ((q1 : ℝ) ^ (r0 - b) * (q1 : ℝ) ^ b) *
             (p_e ^ E_s * p_e ^ (b * (N0 - 1)))) := by ring
        _ = ((((N0 - b).choose (r0 - b) : ℕ) : ℝ) * ((2 : ℝ) ^ L) ^ b) *
            ((r0.choose b : ℝ) * (4 : ℝ) ^ b * G ^ b * (q1 : ℝ) ^ r0 * p_e ^ E_r * p_e ^ Δ_b) := by
              rw [hq_pow, hpe_pow]
              ring
    rw [h1]
    have hnn : 0 ≤ (r0.choose b : ℝ) * (4 : ℝ) ^ b * G ^ b * (q1 : ℝ) ^ r0 * p_e ^ E_r * p_e ^
        Δ_b :=
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) b))
              (pow_nonneg (le_of_lt hG_pos) b))
            (pow_nonneg (le_of_lt hq1_pos) r0))
          (pow_nonneg (le_of_lt hpe_pos) E_r))
        (pow_nonneg (le_of_lt hpe_pos) Δ_b)
    calc
      ((((N0 - b).choose (r0 - b) : ℕ) : ℝ) * ((2 : ℝ) ^ L) ^ b) *
          ((r0.choose b : ℝ) * (4 : ℝ) ^ b * G ^ b * (q1 : ℝ) ^ r0 * p_e ^ E_r * p_e ^ Δ_b)
        ≤ (N0.choose r0 : ℝ) *
          ((r0.choose b : ℝ) * (4 : ℝ) ^ b * G ^ b * (q1 : ℝ) ^ r0 * p_e ^ E_r * p_e ^ Δ_b) :=
            mul_le_mul_of_nonneg_right hbin_real hnn
      _ = D_om * ((r0.choose b : ℝ) * ((4 : ℝ) ^ b * G ^ b * p_e ^ Δ_b)) := by
            dsimp [D_om]
            ring
  have hΔ_quad_nat : b * (r0 - 1) ≤ 2 * Δ_b := by
    have hc1 := twice_choose_two (r0 - b)
    have hc2 := twice_choose_two r0
    have hle1 : (r0 - b) * (r0 - b - 1) ≤ (r0 - b) * (r0 - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hadd1 : (r0 - b) * (r0 - 1) + b * (r0 - 1) = r0 * (r0 - 1) := by
      rw [← add_mul, Nat.sub_add_cancel hb]
    omega
  have hΔ_quad_real : (b : ℝ) * ((r0 : ℝ) - 1) ≤ 2 * (Δ_b : ℝ) := by
    have hcast : ((b * (r0 - 1) : ℕ) : ℝ) ≤ ((2 * Δ_b : ℕ) : ℝ) := by exact_mod_cast hΔ_quad_nat
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ r0), Nat.cast_one, Nat.cast_mul,
      Nat.cast_ofNat] at hcast
    exact hcast
  have hdecay : (4 : ℝ) ^ b * G ^ b * p_e ^ Δ_b ≤ ε ^ b := by
    have h4_eq : (4 : ℝ) ^ b = (2 : ℝ) ^ (2 * (b : ℝ)) := by
      have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [h4, ← Real.rpow_natCast ((2 : ℝ) ^ (2 : ℝ)) b,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hG_eq : G ^ b = (2 : ℝ) ^ ((gamma0 : ℝ) * (b : ℝ)) := by
      dsimp [G]
      rw [← Real.rpow_natCast _ b, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hpe_eq : p_e ^ Δ_b = (2 : ℝ) ^ (- σ * (Δ_b : ℝ)) := by
      dsimp [p_e]
      rw [← Real.rpow_natCast _ Δ_b, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hε_eq : ε ^ b = (2 : ℝ) ^ (- (999 : ℝ) * (b : ℝ)) := by
      dsimp [ε]
      rw [← Real.rpow_natCast _ b, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h4_eq, hG_eq, hpe_eq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hε_eq]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hr_real : (3001 : ℝ) ≤ (r0 : ℝ) := by exact_mod_cast hr_ge
    have hlam0_real : (3000 : ℝ) ≤ (lam0 : ℝ) := by exact_mod_cast hlam0_ge
    have hgam_real : (gamma0 : ℝ) = 5 * (lam0 : ℝ) := by
      rw [hgam_eq]
      push_cast
      ring
    have hb_nn : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    have hlam0_nn : (0 : ℝ) ≤ (lam0 : ℝ) := Nat.cast_nonneg lam0
    have hr0_pos : (0 : ℝ) < 2 * (r0 : ℝ) := by linarith only [hr_real]
    have hbr1_nn : (0 : ℝ) ≤ (b : ℝ) * ((r0 : ℝ) - 1) :=
      mul_nonneg hb_nn (by linarith only [hr_real])
    have hm1 : (12 * (lam0 : ℝ)) * ((b : ℝ) * ((r0 : ℝ) - 1)) ≤
        (σ * (r0 : ℝ)) * ((b : ℝ) * ((r0 : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hσ_low0]) hbr1_nn
    have hm2 : (σ * (r0 : ℝ)) * ((b : ℝ) * ((r0 : ℝ) - 1)) ≤
        (σ * (r0 : ℝ)) * (2 * (Δ_b : ℝ)) :=
      mul_le_mul_of_nonneg_left hΔ_quad_real
        (mul_nonneg (le_of_lt hσ_pos0) (by linarith only [hr_real]))
    have hm3 : 12 * ((lam0 : ℝ) * (b : ℝ)) ≤ (r0 : ℝ) * ((lam0 : ℝ) * (b : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hr_real]) (mul_nonneg hlam0_nn hb_nn)
    have hm4 : 3000 * ((b : ℝ) * (r0 : ℝ)) ≤ (lam0 : ℝ) * ((b : ℝ) * (r0 : ℝ)) :=
      mul_le_mul_of_nonneg_right hlam0_real (mul_nonneg hb_nn (by linarith only [hr_real]))
    have hscaled : (2 * (r0 : ℝ)) * (2 * (b : ℝ) + (gamma0 : ℝ) * (b : ℝ) + - σ * (Δ_b : ℝ)) ≤
        (2 * (r0 : ℝ)) * (- (999 : ℝ) * (b : ℝ)) := by
      rw [hgam_real]
      linarith [hm1, hm2, hm3, hm4,
        show (12 * (lam0 : ℝ)) * ((b : ℝ) * ((r0 : ℝ) - 1)) =
          12 * ((lam0 : ℝ) * ((b : ℝ) * (r0 : ℝ))) - 12 * ((lam0 : ℝ) * (b : ℝ)) by ring,
        show (σ * (r0 : ℝ)) * (2 * (Δ_b : ℝ)) = 2 * (r0 : ℝ) * (σ * (Δ_b : ℝ)) by ring,
        show (r0 : ℝ) * ((lam0 : ℝ) * (b : ℝ)) = (lam0 : ℝ) * ((b : ℝ) * (r0 : ℝ)) by ring,
        show (2 * (r0 : ℝ)) * (2 * (b : ℝ) + 5 * (lam0 : ℝ) * (b : ℝ) + - σ * (Δ_b : ℝ)) =
          4 * ((b : ℝ) * (r0 : ℝ)) + 10 * ((lam0 : ℝ) * ((b : ℝ) * (r0 : ℝ))) -
            2 * (r0 : ℝ) * (σ * (Δ_b : ℝ)) by ring,
        show (2 * (r0 : ℝ)) * (- (999 : ℝ) * (b : ℝ)) = - 1998 * ((b : ℝ) * (r0 : ℝ)) by ring]
    exact le_of_mul_le_mul_left hscaled hr0_pos
  calc
    (D_star / D_om) *
        (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * (q1 : ℝ) ^ (r0 - b)) *
         p_e ^ E_s)
      ≤ (D_star / D_om) * (D_om * ((r0.choose b : ℝ) * ((4 : ℝ) ^ b * G ^ b * p_e ^ Δ_b))) :=
        mul_le_mul_of_nonneg_left hT_le (div_nonneg hD_nn (le_of_lt hDOm_pos))
    _ = D_star * ((r0.choose b : ℝ) * ((4 : ℝ) ^ b * G ^ b * p_e ^ Δ_b)) := by
        have hne : D_om ≠ 0 := ne_of_gt hDOm_pos
        field_simp [hne]
    _ ≤ D_star * ((r0.choose b : ℝ) * ε ^ b) := by
        refine mul_le_mul_of_nonneg_left ?_ hD_nn
        exact mul_le_mul_of_nonneg_left hdecay (Nat.cast_nonneg _)

private lemma hypergeometricMoment_bound : ∀ (L r0 q1 lam0 gamma0 : ℕ) (σ D_star : ℝ),
      3001 ≤ r0 → 1 ≤ q1 → 3000 ≤ lam0 → gamma0 = 5 * lam0 → 0 < σ → 0 ≤ D_star →
      (4 : ℝ) * (2 : ℝ) ^ L * (q1 : ℝ) * ((2 : ℝ) ^ (- σ)) ^ (2 ^ L * r0 - 1) =
        (2 : ℝ) ^ (- (gamma0 : ℝ)) →
      6 * (lam0 : ℝ) ≤ σ * (r0 : ℝ) / 2 →
      let N0 := 2 ^ L * r0
      let p_e := (2 : ℝ) ^ (- σ)
      let D_om := (N0.choose r0 : ℝ) * (q1 : ℝ) ^ r0 * p_e ^ (r0 * (N0 - 1) - r0.choose 2)
      ∑ b ∈ Finset.range (r0 + 1),
        (D_star / D_om) *
          (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * (q1 : ℝ) ^ (r0 - b)) *
           p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2)) ≤
        (3 / 2 : ℝ) * cspGamma r0 * D_star := by
  intro L r0 q1 lam0 gamma0 σ D_star hr_ge hq1_pos_nat hlam0_ge hgam_eq hσ_pos0 hD_nn h_cal0
      hσ_low0 N0 p_e D_om
  have h1_le_2L : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have hrN : r0 ≤ N0 := Nat.le_mul_of_pos_left r0 h1_le_2L
  have hq1_pos : (0 : ℝ) < (q1 : ℝ) := by exact_mod_cast (show 0 < q1 by omega)
  have hpe_pos : 0 < p_e := Real.rpow_pos_of_pos (by norm_num) (- σ)
  let G : ℝ := (2 : ℝ) ^ (gamma0 : ℝ)
  have hG_pos : 0 < G := Real.rpow_pos_of_pos (by norm_num) (gamma0 : ℝ)
  have h_cal1 : (4 : ℝ) * G * (2 : ℝ) ^ L * (q1 : ℝ) * p_e ^ (N0 - 1) = 1 := by
    have hmul : G * ((4 : ℝ) * (2 : ℝ) ^ L * (q1 : ℝ) * p_e ^ (N0 - 1)) = 1 := by
      change G * ((4 : ℝ) * (2 : ℝ) ^ L * (q1 : ℝ) * ((2 : ℝ) ^ (- σ)) ^ (2 ^ L * r0 - 1)) = 1
      rw [h_cal0]
      dsimp [G]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero]
    linarith
  have h_binom_ratio : ∀ b : ℕ, b ≤ r0 →
      (N0 - b).choose (r0 - b) * (2 ^ L) ^ b ≤ N0.choose r0 := by
    intro b
    induction b with
    | zero =>
      intro _
      simp
    | succ b ih =>
      intro hb1
      have hr'_pos : 1 ≤ r0 - b := by omega
      have hb_le_2Lb : b ≤ 2 ^ L * b := Nat.le_mul_of_pos_left b h1_le_2L
      have h2Lr_sum : 2 ^ L * (r0 - b) + 2 ^ L * b = N0 := by
        dsimp [N0]
        rw [← mul_add, show r0 - b + b = r0 by omega]
      have h2Lr_le : 2 ^ L * (r0 - b) ≤ N0 - b := by omega
      have habs : (N0 - b) * (N0 - b - 1).choose (r0 - b - 1) =
          (N0 - b).choose (r0 - b) * (r0 - b) := by
        have h := Nat.add_one_mul_choose_eq (N0 - b - 1) (r0 - b - 1)
        rwa [show N0 - b - 1 + 1 = N0 - b by omega, show r0 - b - 1 + 1 = r0 - b by omega] at h
      have hmul_step : ((N0 - b - 1).choose (r0 - b - 1) * 2 ^ L) * (r0 - b) ≤
          (N0 - b).choose (r0 - b) * (r0 - b) := by
        calc
          ((N0 - b - 1).choose (r0 - b - 1) * 2 ^ L) * (r0 - b)
            = (N0 - b - 1).choose (r0 - b - 1) * (2 ^ L * (r0 - b)) := mul_assoc _ _ _
          _ ≤ (N0 - b - 1).choose (r0 - b - 1) * (N0 - b) := Nat.mul_le_mul_left _ h2Lr_le
          _ = (N0 - b) * (N0 - b - 1).choose (r0 - b - 1) := mul_comm _ _
          _ = (N0 - b).choose (r0 - b) * (r0 - b) := habs
      have hstep : (N0 - b - 1).choose (r0 - b - 1) * 2 ^ L ≤ (N0 - b).choose (r0 - b) :=
        Nat.le_of_mul_le_mul_right hmul_step (by omega)
      rw [show N0 - (b + 1) = N0 - b - 1 by omega, show r0 - (b + 1) = r0 - b - 1 by omega,
        pow_succ']
      calc
        (N0 - b - 1).choose (r0 - b - 1) * (2 ^ L * (2 ^ L) ^ b)
          = ((N0 - b - 1).choose (r0 - b - 1) * 2 ^ L) * (2 ^ L) ^ b := (mul_assoc _ _ _).symm
        _ ≤ (N0 - b).choose (r0 - b) * (2 ^ L) ^ b := Nat.mul_le_mul_right _ hstep
        _ ≤ N0.choose r0 := ih (by omega)
  have hDOm_pos : 0 < D_om := by
    dsimp [D_om]
    have hch_pos : (0 : ℝ) < (N0.choose r0 : ℝ) := by exact_mod_cast (Nat.choose_pos hrN)
    exact mul_pos (mul_pos hch_pos (pow_pos hq1_pos r0)) (pow_pos hpe_pos _)
  let ε : ℝ := (2 : ℝ) ^ (- (999 : ℝ))
  have h_term :=
    @edgeMoments_h_term L r0 q1 lam0 gamma0 σ D_star hr_ge hlam0_ge hgam_eq hσ_pos0 hD_nn
        hσ_low0 hrN hq1_pos hpe_pos hG_pos h_cal1 h_binom_ratio hDOm_pos
  have hsum_bin : ∑ b ∈ Finset.range (r0 + 1), (r0.choose b : ℝ) * ε ^ b = (ε + 1) ^ r0 := by
    rw [add_pow]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp [mul_comm]
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos (by norm_num) _
  have hexp_bound : (ε + 1) ^ r0 ≤ (3 / 2 : ℝ) * cspGamma r0 := by
    have h1 : (ε + 1) ^ r0 ≤ Real.exp ((r0 : ℝ) * ε) := by
      calc
        (ε + 1) ^ r0 ≤ (Real.exp ε) ^ r0 :=
          pow_le_pow_left₀ (by linarith) (Real.add_one_le_exp ε) r0
        _ = Real.exp ((r0 : ℝ) * ε) := (Real.exp_nat_mul ε r0).symm
    have h2 : Real.exp ((r0 : ℝ) * ε) ≤ cspGamma r0 := exponentialGammaBound r0
    have hγ_nn : 0 ≤ cspGamma r0 := by
      unfold cspGamma
      exact Real.rpow_nonneg (by norm_num) _
    linarith only [h1, h2, hγ_nn]
  calc
    ∑ b ∈ Finset.range (r0 + 1),
        (D_star / D_om) *
          (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * (q1 : ℝ) ^ (r0 - b)) *
           p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2))
      ≤ ∑ b ∈ Finset.range (r0 + 1), D_star * ((r0.choose b : ℝ) * ε ^ b) :=
        Finset.sum_le_sum h_term
    _ = D_star * (∑ b ∈ Finset.range (r0 + 1), (r0.choose b : ℝ) * ε ^ b) :=
        (Finset.mul_sum _ _ _).symm
    _ = D_star * (ε + 1) ^ r0 := by rw [hsum_bin]
    _ ≤ D_star * ((3 / 2 : ℝ) * cspGamma r0) :=
        mul_le_mul_of_nonneg_left hexp_bound hD_nn
    _ = (3 / 2 : ℝ) * cspGamma r0 * D_star := by ring

private lemma vandermondeMoment_bound : ∀ (L beta0 gamma0 r0 : ℕ),
      20 ≤ L → 1000 ≤ beta0 → gamma0 ≤ L → 3001 ≤ r0 →
      let N0 := 2 ^ L * r0
      let E_q := 2 * beta0 * 2 ^ L
      let σ := ((E_q + L + gamma0 + 2 : ℕ) : ℝ) / ((N0 - 1 : ℕ) : ℝ)
      let p_e := (2 : ℝ) ^ (- σ)
      ∑ k₁ ∈ Finset.range (N0 + 1),
        ∑ k₂ ∈ Finset.range (r0 + 1),
          ((N0.choose k₁ : ℕ) : ℝ) *
          ((r0.choose k₂ : ℕ) : ℝ) *
          ((2 : ℝ) / ((2 ^ E_q : ℕ) : ℝ)) ^ (k₁ + k₂) *
          (p_e⁻¹) ^ ((k₁ + k₂).choose 2) ≤
        2 * cspGamma r0 := by
  intro L beta0 gamma0 r0 hL_ge20 hbeta0_ge hgam_le_L hr_ge N0 E_q σ p_e
  let M := N0 + r0
  let w : ℕ → ℝ := fun k => ((2 : ℝ) / ((2 ^ E_q : ℕ) : ℝ)) ^ k * (p_e⁻¹) ^ (k.choose 2)
  have h2L_gt_L : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self
  have h2L_ge21 : 21 ≤ 2 ^ L := by omega
  have hN_ge2 : 2 ≤ N0 := by
    dsimp [N0]
    have : 21 * 3001 ≤ 2 ^ L * r0 := Nat.mul_le_mul h2L_ge21 hr_ge
    omega
  have hpe_pos : 0 < p_e := Real.rpow_pos_of_pos (by norm_num) (- σ)
  have hw_nn : ∀ k : ℕ, 0 ≤ w k := by
    intro k
    dsimp [w]
    exact mul_nonneg
      (pow_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _)) k)
      (pow_nonneg (inv_nonneg.mpr (le_of_lt hpe_pos)) _)
  have h_vand :
      ∑ k₁ ∈ Finset.range (N0 + 1),
        ∑ k₂ ∈ Finset.range (r0 + 1),
          ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) * w (k₁ + k₂) ≤
      ∑ k ∈ Finset.range (M + 1), (M.choose k : ℝ) * w k := by
    let S_prod := Finset.range (N0 + 1) ×ˢ Finset.range (r0 + 1)
    rw [← Finset.sum_product']
    have hmaps : ∀ p ∈ S_prod, p.1 + p.2 ∈ Finset.range (M + 1) := by
      intro p hp
      simp only [S_prod, M, Finset.mem_product, Finset.mem_range] at hp ⊢
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_le_sum (fun k _ => ?_)
    have hcongr : ∑ p ∈ S_prod.filter (fun p => p.1 + p.2 = k),
        ((N0.choose p.1 : ℕ) : ℝ) * ((r0.choose p.2 : ℕ) : ℝ) * w (p.1 + p.2) =
      (∑ p ∈ S_prod.filter (fun p => p.1 + p.2 = k),
        ((N0.choose p.1 : ℕ) : ℝ) * ((r0.choose p.2 : ℕ) : ℝ)) * w k := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      rw [(Finset.mem_filter.mp hp).2]
    rw [hcongr]
    refine mul_le_mul_of_nonneg_right ?_ (hw_nn k)
    have hsub : S_prod.filter (fun p => p.1 + p.2 = k) ⊆ Finset.HasAntidiagonal.antidiagonal k := by
      intro p hp
      exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (Finset.mem_filter.mp hp).2
    calc
      ∑ p ∈ S_prod.filter (fun p => p.1 + p.2 = k),
          ((N0.choose p.1 : ℕ) : ℝ) * ((r0.choose p.2 : ℕ) : ℝ)
        ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
            ((N0.choose p.1 : ℕ) : ℝ) * ((r0.choose p.2 : ℕ) : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      _ = ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, N0.choose p.1 * r0.choose p.2 : ℕ) : ℝ)
          := by
          push_cast
          rfl
      _ = (M.choose k : ℝ) := by
          dsimp [M]
          rw [Nat.add_choose_eq]
  let μ : ℝ := (1 / 2 : ℝ) * (beta0 : ℝ) * (2 : ℝ) ^ L
  let η : ℝ := (2 : ℝ) ^ (- μ)
  have hbeta0_real : (1000 : ℝ) ≤ (beta0 : ℝ) := by exact_mod_cast hbeta0_ge
  have hL_real : (20 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge20
  have hgam_real : (gamma0 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hgam_le_L
  have h2L_real : (L : ℝ) + 1 ≤ (2 : ℝ) ^ L := by
    have hcast : ((L + 1 : ℕ) : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by exact_mod_cast h2L_gt_L
    simpa using hcast
  have hprod_ge : 1000 * ((L : ℝ) + 1) ≤ (beta0 : ℝ) * (2 : ℝ) ^ L := by
    calc
      1000 * ((L : ℝ) + 1) ≤ (beta0 : ℝ) * ((L : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hbeta0_real (by linarith only [hL_real])
      _ ≤ (beta0 : ℝ) * (2 : ℝ) ^ L :=
        mul_le_mul_of_nonneg_left h2L_real (Nat.cast_nonneg beta0)
  have hw_le_η : ∀ k ∈ Finset.range (M + 1), w k ≤ η ^ k := by
    intro k hk_mem
    have hk_le : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_mem)
    have hdiv_eq : (2 : ℝ) / ((2 ^ E_q : ℕ) : ℝ) = (2 : ℝ) ^ ((1 : ℝ) - (E_q : ℝ)) := by
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one, Real.rpow_natCast]
      push_cast
      rfl
    have hinv_eq : p_e⁻¹ = (2 : ℝ) ^ σ := by
      dsimp [p_e]
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), neg_neg]
    have hwk_eq : w k = (2 : ℝ) ^ (((1 : ℝ) - (E_q : ℝ)) * (k : ℝ) + σ * (k.choose 2 : ℝ)) := by
      dsimp [w]
      rw [hdiv_eq, hinv_eq, ← Real.rpow_natCast _ k, ← Real.rpow_natCast _ (k.choose 2),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hηk_eq : η ^ k = (2 : ℝ) ^ (- μ * (k : ℝ)) := by
      dsimp [η]
      rw [← Real.rpow_natCast _ k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hwk_eq, hηk_eq]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    by_cases hk0 : k = 0
    · subst hk0
      simp
    · have hk_pos : 1 ≤ k := by omega
      have hch_real : (k.choose 2 : ℝ) = (k : ℝ) * (((k : ℝ) - 1) / 2) := by
        have hc := twice_choose_two k
        have hcast : ((2 * k.choose 2 : ℕ) : ℝ) = ((k * (k - 1) : ℕ) : ℝ) := by exact_mod_cast hc
        rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_sub hk_pos, Nat.cast_one] at hcast
        linarith only [hcast]
      have h4k_nat : 4 * (k - 1) ≤ 5 * (N0 - 1) := by
        have h4r : 4 * r0 + 1 ≤ N0 := by
          dsimp [N0]
          have : 21 * r0 ≤ 2 ^ L * r0 := Nat.mul_le_mul_right r0 h2L_ge21
          omega
        dsimp [M] at hk_le
        omega
      have h4k_real : 4 * ((k : ℝ) - 1) ≤ 5 * ((N0 - 1 : ℕ) : ℝ) := by
        have hcast : ((4 * (k - 1) : ℕ) : ℝ) ≤ ((5 * (N0 - 1) : ℕ) : ℝ) := by exact_mod_cast h4k_nat
        rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hk_pos, Nat.cast_one,
          Nat.cast_mul, Nat.cast_ofNat] at hcast
        exact hcast
      have hN1_pos : (0 : ℝ) < ((N0 - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < N0 - 1 by omega)
      have hrat_le : ((k : ℝ) - 1) / ((N0 - 1 : ℕ) : ℝ) ≤ 5 / 4 := by
        rw [div_le_iff₀ hN1_pos]
        linarith only [h4k_real]
      have hσ_term : σ * (((k : ℝ) - 1) / 2) ≤
          (5 / 8 : ℝ) * ((E_q : ℝ) + (L : ℝ) + (gamma0 : ℝ) + 2) := by
        dsimp [σ]
        have hrew : (((E_q + L + gamma0 + 2 : ℕ) : ℝ) / ((N0 - 1 : ℕ) : ℝ)) * (((k : ℝ) - 1) / 2) =
            (((E_q + L + gamma0 + 2 : ℕ) : ℝ) / 2) * (((k : ℝ) - 1) / ((N0 - 1 : ℕ) : ℝ)) := by ring
        rw [hrew]
        have hnum_nn : (0 : ℝ) ≤ ((E_q + L + gamma0 + 2 : ℕ) : ℝ) / 2 :=
          div_nonneg (Nat.cast_nonneg _) (by norm_num)
        have hm := mul_le_mul_of_nonneg_left hrat_le hnum_nn
        push_cast at hm ⊢
        linarith only [hm]
      have hEq_real : (E_q : ℝ) = 2 * (beta0 : ℝ) * (2 : ℝ) ^ L := by
        dsimp [E_q]
        push_cast
        ring
      have hdrift_1 : (1 : ℝ) - (E_q : ℝ) + σ * (((k : ℝ) - 1) / 2) ≤ - μ := by
        dsimp [μ]
        linarith only [hσ_term, hEq_real, hprod_ge, hL_real, hgam_real]
      have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hm := mul_le_mul_of_nonneg_right hdrift_1 hk_nn
      rw [hch_real]
      linarith [hm,
        show ((1 : ℝ) - (E_q : ℝ) + σ * (((k : ℝ) - 1) / 2)) * (k : ℝ) =
          ((1 : ℝ) - (E_q : ℝ)) * (k : ℝ) + σ * ((k : ℝ) * (((k : ℝ) - 1) / 2)) by ring]
  have hsum_bin : ∑ k ∈ Finset.range (M + 1), (M.choose k : ℝ) * η ^ k = (η + 1) ^ M := by
    rw [add_pow]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [mul_comm]
  have hexp_bound : (η + 1) ^ M ≤ 2 * cspGamma r0 := by
    have hη_pos : 0 < η := Real.rpow_pos_of_pos (by norm_num) (- μ)
    have h1 : (η + 1) ^ M ≤ Real.exp ((M : ℝ) * η) := by
      calc
        (η + 1) ^ M ≤ (Real.exp η) ^ M :=
          pow_le_pow_left₀ (by linarith) (Real.add_one_le_exp η) M
        _ = Real.exp ((M : ℝ) * η) := (Real.exp_nat_mul η M).symm
    have hM_le : (M : ℝ) ≤ (r0 : ℝ) * (2 : ℝ) ^ ((L : ℝ) + 1) := by
      have hM_nat : M ≤ r0 * 2 ^ (L + 1) := by
        dsimp [M, N0]
        have h1_2L : 1 ≤ 2 ^ L := Nat.one_le_two_pow
        have hr_le_N : r0 ≤ 2 ^ L * r0 := Nat.le_mul_of_pos_left r0 h1_2L
        rw [pow_succ, show r0 * (2 ^ L * 2) = 2 ^ L * r0 + 2 ^ L * r0 by ring]
        omega
      have hcast : (M : ℝ) ≤ ((r0 * 2 ^ (L + 1) : ℕ) : ℝ) := by exact_mod_cast hM_nat
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        ← Real.rpow_natCast (2 : ℝ) (L + 1), Nat.cast_add L 1, Nat.cast_one] at hcast
      exact hcast
    have hexp_le : (2 : ℝ) ^ ((L : ℝ) + 1) * η ≤ (2 : ℝ) ^ (- (999 : ℝ)) := by
      dsimp [η, μ]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith only [hprod_ge, hL_real]
    have hMη_le : (M : ℝ) * η ≤ (r0 : ℝ) * (2 : ℝ) ^ (- (999 : ℝ)) := by
      have hm1 := mul_le_mul_of_nonneg_right hM_le (le_of_lt hη_pos)
      have hm2 := mul_le_mul_of_nonneg_left hexp_le (Nat.cast_nonneg r0)
      linarith [hm1, hm2, mul_assoc (r0 : ℝ) ((2 : ℝ) ^ ((L : ℝ) + 1)) η]
    have h2 : Real.exp ((M : ℝ) * η) ≤ cspGamma r0 :=
      le_trans (Real.exp_le_exp.mpr hMη_le) (exponentialGammaBound r0)
    have hγ_nn : 0 ≤ cspGamma r0 := by
      unfold cspGamma
      exact Real.rpow_nonneg (by norm_num) _
    linarith only [h1, h2, hγ_nn]
  calc
    ∑ k₁ ∈ Finset.range (N0 + 1),
      ∑ k₂ ∈ Finset.range (r0 + 1),
        ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
        ((2 : ℝ) / ((2 ^ E_q : ℕ) : ℝ)) ^ (k₁ + k₂) *
        (p_e⁻¹) ^ ((k₁ + k₂).choose 2)
      = ∑ k₁ ∈ Finset.range (N0 + 1),
          ∑ k₂ ∈ Finset.range (r0 + 1),
            ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) * w (k₁ + k₂) := by
          refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun k₂ _ => ?_))
          dsimp [w]
          ring
    _ ≤ ∑ k ∈ Finset.range (M + 1), (M.choose k : ℝ) * w k := h_vand
    _ ≤ ∑ k ∈ Finset.range (M + 1), (M.choose k : ℝ) * η ^ k :=
        Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hw_le_η k hk) (Nat.cast_nonneg _))
    _ = (η + 1) ^ M := hsum_bin
    _ ≤ 2 * cspGamma r0 := hexp_bound

private lemma edgeMoments_hM0_const :
    ∀ (N0 q0 r0 : ℕ) (p_k p_e n_0 D_star : ℝ),
      (∀ (a b : Fin N0 → Fin q0),
          (homQueries a ∪ homQueries b).card = N0.choose (2 : ℕ) + dHam a b * (N0 - (1 : ℕ)) -
              (dHam a b).choose (2 : ℕ)) →
        ∑ xy : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) with dHam xy.1 xy.2 = r0,
              p_k ^ (2 : ℕ) * p_e ^ (homQueries xy.1 ∪ homQueries xy.2).card =
            n_0 * D_star →
          let U_r : ℕ := N0.choose (2 : ℕ) + r0 * (N0 - (1 : ℕ)) - r0.choose (2 : ℕ);
          let E_all : Finset ((Fin N0 → Fin q0) × (Fin N0 → Fin q0)) :=
            {xy : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) | dHam xy.1 xy.2 = r0};
          (↑E_all.card : ℝ) * (p_k ^ (2 : ℕ) * p_e ^ U_r) = n_0 * D_star := by
  classical
  intro N0 q0 r0 p_k p_e n_0 D_star h_union h_M0_gen U_r E_all
  rw [← h_M0_gen]
  have hcongr : ∑ xy ∈ E_all, p_k ^ 2 * p_e ^ (homQueries xy.1 ∪ homQueries xy.2).card =
      ∑ _xy ∈ E_all, (p_k ^ 2 * p_e ^ U_r) := by
    refine Finset.sum_congr rfl (fun xy hxy => ?_)
    have hd : dHam xy.1 xy.2 = r0 := (Finset.mem_filter.mp hxy).2
    rw [h_union xy.1 xy.2, hd]
  rw [hcongr, Finset.sum_const, nsmul_eq_mul]

private lemma edgeMoments_hinner_bound :
    ∀ (N0 q0 r0 : ℕ) (p_k p_e γ : ℝ),
          (0 : ℝ) < p_k →
            (0 : ℝ) < p_e →
              (∀ (a b : Fin N0 → Fin q0),
                  (homQueries a ∪ homQueries b).card =
                    N0.choose (2 : ℕ) + dHam a b * (N0 - (1 : ℕ)) - (dHam a b).choose (2 : ℕ)) →
                ∑ k₁ ∈ Finset.range (N0 + (1 : ℕ)),
                      ∑ k₂ ∈ Finset.range (r0 + (1 : ℕ)),
                        (↑(N0.choose k₁) : ℝ) * (↑(r0.choose k₂) : ℝ) * ((2 : ℝ) / (↑(q0 - (1 :
                            ℕ)) : ℝ)) ^ (k₁ + k₂) *
                          p_e⁻¹ ^ (k₁ + k₂).choose (2 : ℕ) ≤
                    (2 : ℝ) * γ →
                  let U_r : ℕ := N0.choose (2 : ℕ) + r0 * (N0 - (1 : ℕ)) - r0.choose (2 : ℕ);
                  let E_all : Finset ((Fin N0 → Fin q0) × (Fin N0 → Fin q0)) :=
                    {xy : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) | dHam xy.1 xy.2 = r0};
                  E_all.card = q0 ^ N0 * (N0.choose r0 * (q0 - (1 : ℕ)) ^ r0) →
                    (0 : ℝ) < (↑(q0 - (1 : ℕ)) : ℝ) →
                      (↑(q0 - (1 : ℕ)) : ℝ) ≤ (↑q0 : ℝ) →
                        (1 : ℝ) ≤ p_e⁻¹ →
                          ∀ xy ∈ E_all,
                            ∑ xy' ∈ E_all,
                                p_k ^ (4 : ℕ) *
                                  p_e ^ (homQueries xy.1 ∪ homQueries xy.2 ∪ homQueries xy'.1 ∪
                                      homQueries xy'.2).card ≤
                              (↑E_all.card : ℝ) * (p_k ^ (2 : ℕ) * p_e ^ U_r) ^ (2 : ℕ) * ((2 :
                                  ℝ) * γ) := by
  classical
  intro N0 q0 r0 p_k p_e γ hpk_pos hpe_pos h_union h_s4_gen U_r E_all hE_card hq1_pos
      hq1_le_qr h1_le_inv_pe ⟨x, y⟩ hxy
  have hdxy : dHam x y = r0 := (Finset.mem_filter.mp hxy).2
  obtain ⟨hs2_a, hs2_b⟩ := queryPairIntersectionAndFibers N0 q0 r0 x y
  let k1_fn : (Fin N0 → Fin q0) → ℕ :=
    fun x' => (Finset.univ.filter (fun v : Fin N0 => x' v = x v ∨ x' v = y v)).card
  let k2_fn : (Fin N0 → Fin q0) → (Fin N0 → Fin q0) → ℕ :=
    fun x' y' => ((disagreeSet x' y').filter (fun v : Fin N0 => y' v = x v ∨ y' v = y v)).card
  let S_kr := Finset.range (N0 + 1) ×ˢ Finset.range (r0 + 1)
  have hmaps_kr : ∀ xy' ∈ E_all, (k1_fn xy'.1, k2_fn xy'.1 xy'.2) ∈ S_kr := by
    intro xy' hxy'
    have hdxy' : dHam xy'.1 xy'.2 = r0 := (Finset.mem_filter.mp hxy').2
    have hk1 : k1_fn xy'.1 ≤ N0 := by
      simpa using Finset.card_le_univ
        (Finset.univ.filter (fun v : Fin N0 => xy'.1 v = x v ∨ xy'.1 v = y v))
    have hk2 : k2_fn xy'.1 xy'.2 ≤ r0 := by
      rw [← hdxy']
      exact Finset.card_le_card (Finset.filter_subset _ _)
    simp only [S_kr, Finset.mem_product, Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps_kr]
  have hkk_bound : ∀ kk ∈ S_kr,
      ∑ xy' ∈ E_all.filter (fun xy' => (k1_fn xy'.1, k2_fn xy'.1 xy'.2) = kk),
        p_k ^ 4 * p_e ^ (homQueries x ∪ homQueries y ∪
                         homQueries xy'.1 ∪ homQueries xy'.2).card ≤
      ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2) *
        (((N0.choose kk.1 : ℕ) : ℝ) * ((r0.choose kk.2 : ℕ) : ℝ) *
         ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (kk.1 + kk.2) *
         (p_e⁻¹) ^ ((kk.1 + kk.2).choose 2)) := by
    rintro ⟨k₁, k₂⟩ hkk
    simp only [S_kr, Finset.mem_product, Finset.mem_range] at hkk
    have hk₁ : k₁ ≤ N0 := Nat.lt_succ_iff.mp hkk.1
    have hk₂ : k₂ ≤ r0 := Nat.lt_succ_iff.mp hkk.2
    have hpt : ∀ xy' ∈ E_all.filter (fun xy' => (k1_fn xy'.1, k2_fn xy'.1 xy'.2) = (k₁, k₂)),
        p_k ^ 4 * p_e ^ (homQueries x ∪ homQueries y ∪
                         homQueries xy'.1 ∪ homQueries xy'.2).card ≤
        (p_k ^ 2 * p_e ^ U_r) ^ 2 * (p_e⁻¹) ^ ((k₁ + k₂).choose 2) := by
      intro xy' hxy'_f
      obtain ⟨hxy'E, hpair_eq⟩ := Finset.mem_filter.mp hxy'_f
      have hdxy' : dHam xy'.1 xy'.2 = r0 := (Finset.mem_filter.mp hxy'E).2
      obtain ⟨hk1_eq, hk2_eq⟩ := Prod.mk.inj hpair_eq
      let Q₁ := homQueries x ∪ homQueries y
      let Q₂ := homQueries xy'.1 ∪ homQueries xy'.2
      have hu_assoc : homQueries x ∪ homQueries y ∪ homQueries xy'.1 ∪ homQueries xy'.2 =
          Q₁ ∪ Q₂ := Finset.union_assoc _ _ _
      have hQ₁_card : Q₁.card = U_r := by dsimp [Q₁]; rw [h_union x y, hdxy]
      have hQ₂_card : Q₂.card = U_r := by dsimp [Q₂]; rw [h_union xy'.1 xy'.2, hdxy']
      have hcard_ui : (Q₁ ∪ Q₂).card + (Q₁ ∩ Q₂).card = U_r + U_r := by
        rw [Finset.card_union_add_card_inter, hQ₁_card, hQ₂_card]
      have hpe_split : p_e ^ (Q₁ ∪ Q₂).card =
          p_e ^ U_r * p_e ^ U_r * (p_e⁻¹) ^ (Q₁ ∩ Q₂).card := by
        have hne : p_e ≠ 0 := ne_of_gt hpe_pos
        have h1 : p_e ^ (Q₁ ∪ Q₂).card * p_e ^ (Q₁ ∩ Q₂).card = p_e ^ U_r * p_e ^ U_r := by
          rw [← pow_add, hcard_ui, pow_add]
        calc
          p_e ^ (Q₁ ∪ Q₂).card
            = p_e ^ (Q₁ ∪ Q₂).card * (p_e ^ (Q₁ ∩ Q₂).card * (p_e⁻¹) ^ (Q₁ ∩ Q₂).card) := by
                rw [← mul_pow, mul_inv_cancel₀ hne, one_pow, mul_one]
          _ = (p_e ^ (Q₁ ∪ Q₂).card * p_e ^ (Q₁ ∩ Q₂).card) * (p_e⁻¹) ^ (Q₁ ∩ Q₂).card := by
                ring
          _ = p_e ^ U_r * p_e ^ U_r * (p_e⁻¹) ^ (Q₁ ∩ Q₂).card := by rw [h1]
      have hinter_le : (Q₁ ∩ Q₂).card ≤ (k₁ + k₂).choose 2 := by
        rw [← hk1_eq, ← hk2_eq]
        exact hs2_a xy'.1 xy'.2
      have hinv_pow := pow_le_pow_right₀ h1_le_inv_pe hinter_le
      rw [hu_assoc, hpe_split]
      calc
        p_k ^ 4 * (p_e ^ U_r * p_e ^ U_r * (p_e⁻¹) ^ (Q₁ ∩ Q₂).card)
          = (p_k ^ 2 * p_e ^ U_r) ^ 2 * (p_e⁻¹) ^ (Q₁ ∩ Q₂).card := by ring
        _ ≤ (p_k ^ 2 * p_e ^ U_r) ^ 2 * (p_e⁻¹) ^ ((k₁ + k₂).choose 2) :=
            mul_le_mul_of_nonneg_left hinv_pow (by positivity)
    have hcard_fib :
        ((E_all.filter (fun xy' => (k1_fn xy'.1, k2_fn xy'.1 xy'.2) = (k₁, k₂))).card : ℝ) ≤
        (E_all.card : ℝ) * ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
          ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (k₁ + k₂) := by
      have hfeq : E_all.filter (fun xy' => (k1_fn xy'.1, k2_fn xy'.1 xy'.2) = (k₁, k₂)) =
          Finset.univ.filter (fun xy' =>
            dHam xy'.1 xy'.2 = r0 ∧ k1_fn xy'.1 = k₁ ∧ k2_fn xy'.1 xy'.2 = k₂) := by
        ext xy'
        simp [E_all, Prod.mk.injEq]
      rw [hfeq]
      have hnat := hs2_b k₁ k₂
      let q_r : ℝ := (q0 : ℝ)
      let q_1 : ℝ := ((q0 - 1 : ℕ) : ℝ)
      have hcast : ((Finset.univ.filter
          (fun (xy' : (Fin N0 → Fin q0) × (Fin N0 → Fin q0)) =>
            dHam xy'.1 xy'.2 = r0 ∧ k1_fn xy'.1 = k₁ ∧ k2_fn xy'.1 xy'.2 = k₂)).card : ℝ) ≤
          ((N0.choose k₁ : ℕ) : ℝ) * (2 : ℝ) ^ k₁ * q_r ^ (N0 - k₁) *
            ((N0.choose r0 : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) * (2 : ℝ) ^ k₂ * q_1 ^ (r0 - k₂)) := by
        dsimp [q_r, q_1]
        exact_mod_cast hnat
      have hpow1 : (2 : ℝ) ^ k₁ * q_r ^ (N0 - k₁) ≤ ((2 : ℝ) / q_1) ^ k₁ * q_r ^ N0 := by
        have hdiv_ge1 : (1 : ℝ) ≤ q_r / q_1 := (one_le_div hq1_pos).mpr hq1_le_qr
        have h2_le : (2 : ℝ) ≤ ((2 : ℝ) / q_1) * q_r := by
          have hm := mul_le_mul_of_nonneg_left hdiv_ge1 (by norm_num : (0 : ℝ) ≤ 2)
          linarith [hm, show (2 : ℝ) * (q_r / q_1) = ((2 : ℝ) / q_1) * q_r by ring]
        have hp1 : (2 : ℝ) ^ k₁ ≤ ((2 : ℝ) / q_1) ^ k₁ * q_r ^ k₁ := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by norm_num) h2_le k₁
        calc
          (2 : ℝ) ^ k₁ * q_r ^ (N0 - k₁)
            ≤ (((2 : ℝ) / q_1) ^ k₁ * q_r ^ k₁) * q_r ^ (N0 - k₁) :=
              mul_le_mul_of_nonneg_right hp1 (pow_nonneg (Nat.cast_nonneg q0) _)
          _ = ((2 : ℝ) / q_1) ^ k₁ * (q_r ^ k₁ * q_r ^ (N0 - k₁)) := by ring
          _ = ((2 : ℝ) / q_1) ^ k₁ * q_r ^ N0 := by
              rw [← pow_add, Nat.add_sub_of_le hk₁]
      have hpow2 : (2 : ℝ) ^ k₂ * q_1 ^ (r0 - k₂) = ((2 : ℝ) / q_1) ^ k₂ * q_1 ^ r0 := by
        have hq1_ne : q_1 ^ k₂ ≠ 0 := pow_ne_zero k₂ (ne_of_gt hq1_pos)
        have hr_split : q_1 ^ r0 = q_1 ^ k₂ * q_1 ^ (r0 - k₂) := by
          rw [← pow_add, Nat.add_sub_of_le hk₂]
        rw [div_pow, hr_split]
        field_simp [hq1_ne]
      have hE_real : (E_all.card : ℝ) = q_r ^ N0 * ((N0.choose r0 : ℝ) * q_1 ^ r0) := by
        have hc : (E_all.card : ℝ) = ((q0 ^ N0 * (N0.choose r0 * (q0 - 1) ^ r0) : ℕ) : ℝ) := by
          exact_mod_cast hE_card
        push_cast at hc
        exact hc
      have hprod_le :
          ((N0.choose k₁ : ℕ) : ℝ) * (2 : ℝ) ^ k₁ * q_r ^ (N0 - k₁) *
            ((N0.choose r0 : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) * (2 : ℝ) ^ k₂ * q_1 ^ (r0 - k₂)) ≤
          (E_all.card : ℝ) * ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
            ((2 : ℝ) / q_1) ^ (k₁ + k₂) := by
        have hnn2 : 0 ≤ ((N0.choose k₁ : ℕ) : ℝ) * ((N0.choose r0 : ℝ) *
            ((r0.choose k₂ : ℕ) : ℝ) * (((2 : ℝ) / q_1) ^ k₂ * q_1 ^ r0)) := by
          dsimp [q_1]
          positivity
        calc
          ((N0.choose k₁ : ℕ) : ℝ) * (2 : ℝ) ^ k₁ * q_r ^ (N0 - k₁) *
              ((N0.choose r0 : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) * (2 : ℝ) ^ k₂ * q_1 ^ (r0 - k₂))
            = ((2 : ℝ) ^ k₁ * q_r ^ (N0 - k₁)) *
                (((N0.choose k₁ : ℕ) : ℝ) * ((N0.choose r0 : ℝ) *
                  ((r0.choose k₂ : ℕ) : ℝ) * ((2 : ℝ) ^ k₂ * q_1 ^ (r0 - k₂)))) := by ring
          _ = ((2 : ℝ) ^ k₁ * q_r ^ (N0 - k₁)) *
                (((N0.choose k₁ : ℕ) : ℝ) * ((N0.choose r0 : ℝ) *
                  ((r0.choose k₂ : ℕ) : ℝ) * (((2 : ℝ) / q_1) ^ k₂ * q_1 ^ r0))) := by
                rw [hpow2]
          _ ≤ (((2 : ℝ) / q_1) ^ k₁ * q_r ^ N0) *
                (((N0.choose k₁ : ℕ) : ℝ) * ((N0.choose r0 : ℝ) *
                  ((r0.choose k₂ : ℕ) : ℝ) * (((2 : ℝ) / q_1) ^ k₂ * q_1 ^ r0))) :=
                mul_le_mul_of_nonneg_right hpow1 hnn2
          _ = (q_r ^ N0 * ((N0.choose r0 : ℝ) * q_1 ^ r0)) *
                ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
                (((2 : ℝ) / q_1) ^ k₁ * ((2 : ℝ) / q_1) ^ k₂) := by ring
          _ = (E_all.card : ℝ) * ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
                ((2 : ℝ) / q_1) ^ (k₁ + k₂) := by
                rw [← hE_real, ← pow_add]
      exact le_trans hcast hprod_le
    calc
      ∑ xy' ∈ E_all.filter (fun xy' => (k1_fn xy'.1, k2_fn xy'.1 xy'.2) = (k₁, k₂)),
          p_k ^ 4 * p_e ^ (homQueries x ∪ homQueries y ∪
                           homQueries xy'.1 ∪ homQueries xy'.2).card
        ≤ ((E_all.filter (fun xy' => (k1_fn xy'.1, k2_fn xy'.1 xy'.2) = (k₁, k₂))).card : ℝ) *
            ((p_k ^ 2 * p_e ^ U_r) ^ 2 * (p_e⁻¹) ^ ((k₁ + k₂).choose 2)) := by
          simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hpt
      _ ≤ ((E_all.card : ℝ) * ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
            ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (k₁ + k₂)) *
            ((p_k ^ 2 * p_e ^ U_r) ^ 2 * (p_e⁻¹) ^ ((k₁ + k₂).choose 2)) :=
          mul_le_mul_of_nonneg_right hcard_fib (by positivity)
      _ = ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2) *
            (((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
             ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (k₁ + k₂) *
             (p_e⁻¹) ^ ((k₁ + k₂).choose 2)) := by ring
  calc
    ∑ kk ∈ S_kr,
        ∑ xy' ∈ E_all.filter (fun xy' => (k1_fn xy'.1, k2_fn xy'.1 xy'.2) = kk),
          p_k ^ 4 * p_e ^ (homQueries x ∪ homQueries y ∪
                           homQueries xy'.1 ∪ homQueries xy'.2).card
      ≤ ∑ kk ∈ S_kr,
          ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2) *
            (((N0.choose kk.1 : ℕ) : ℝ) * ((r0.choose kk.2 : ℕ) : ℝ) *
             ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (kk.1 + kk.2) *
             (p_e⁻¹) ^ ((kk.1 + kk.2).choose 2)) :=
        Finset.sum_le_sum hkk_bound
    _ = ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2) *
          ∑ kk ∈ S_kr,
            (((N0.choose kk.1 : ℕ) : ℝ) * ((r0.choose kk.2 : ℕ) : ℝ) *
             ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (kk.1 + kk.2) *
             (p_e⁻¹) ^ ((kk.1 + kk.2).choose 2)) :=
        (Finset.mul_sum _ _ _).symm
    _ = ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2) *
          ∑ k₁ ∈ Finset.range (N0 + 1),
            ∑ k₂ ∈ Finset.range (r0 + 1),
              (((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
               ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (k₁ + k₂) *
               (p_e⁻¹) ^ ((k₁ + k₂).choose 2)) :=
        congrArg (((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2) * ·)
          (Finset.sum_product' (Finset.range (N0 + 1)) (Finset.range (r0 + 1))
            (fun k₁ k₂ => ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
              ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (k₁ + k₂) *
              (p_e⁻¹) ^ ((k₁ + k₂).choose 2)))
    _ ≤ ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2) * (2 * γ) :=
        mul_le_mul_of_nonneg_left h_s4_gen (by positivity)
    _ = (E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2 * (2 * γ) := by ring

private lemma rawMoments_assembly : ∀ (N0 q0 r0 : ℕ) (p_k p_e n_0 D_star γ : ℝ),
      2 ≤ q0 →
      0 < p_k → 0 < p_e → p_e < 1 →
      (∀ a b : Fin N0 → Fin q0,
        (homQueries a ∪ homQueries b).card =
          N0.choose 2 + dHam a b * (N0 - 1) - (dHam a b).choose 2) →
      (∑ xy ∈ Finset.univ.filter
          (fun xy : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) => dHam xy.1 xy.2 = r0),
        p_k ^ 2 * p_e ^ (homQueries xy.1 ∪ homQueries xy.2).card = n_0 * D_star) →
      (∑ b ∈ Finset.range (r0 + 1),
        p_k *
          (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) *
            ((q0 - 1 : ℕ) : ℝ) ^ (r0 - b)) *
           p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2)) ≤
        (3 / 2 : ℝ) * γ * D_star) →
      (∑ k₁ ∈ Finset.range (N0 + 1),
        ∑ k₂ ∈ Finset.range (r0 + 1),
          ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
          ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (k₁ + k₂) *
          (p_e⁻¹) ^ ((k₁ + k₂).choose 2) ≤ 2 * γ) →
      (∑ xyz ∈ Finset.univ.filter
          (fun xyz : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) × (Fin N0 → Fin q0) =>
            dHam xyz.1 xyz.2.1 = r0 ∧ dHam xyz.1 xyz.2.2 = r0 ∧ xyz.2.1 ≠ xyz.2.2),
        p_k ^ 3 * p_e ^ (homQueries xyz.1 ∪ homQueries xyz.2.1 ∪ homQueries xyz.2.2).card ≤
          (3 / 2 : ℝ) * γ * n_0 * D_star ^ 2) ∧
      (∑ e₁₂ ∈ Finset.univ.filter
          (fun e₁₂ : ((Fin N0 → Fin q0) × (Fin N0 → Fin q0)) ×
                     ((Fin N0 → Fin q0) × (Fin N0 → Fin q0)) =>
            dHam e₁₂.1.1 e₁₂.1.2 = r0 ∧ dHam e₁₂.2.1 e₁₂.2.2 = r0 ∧
            e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
            e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2),
        p_k ^ 4 * p_e ^ (homQueries e₁₂.1.1 ∪ homQueries e₁₂.1.2 ∪
                         homQueries e₁₂.2.1 ∪ homQueries e₁₂.2.2).card ≤
          2 * γ * (n_0 * D_star) ^ 2) := by
  intro N0 q0 r0 p_k p_e n_0 D_star γ hq hpk_pos hpe_pos hpe_lt1
    h_union h_M0_gen h_s3_gen h_s4_gen
  let U_r := N0.choose 2 + r0 * (N0 - 1) - r0.choose 2
  let E_all := Finset.univ.filter
    (fun xy : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) => dHam xy.1 xy.2 = r0)
  have hM0_const :=
    @edgeMoments_hM0_const N0 q0 r0 p_k p_e n_0 D_star h_union h_M0_gen
  have hE_card :=
    orderedHammingSphere_card (N := N0) (q := q0) r0
  constructor
  · let T3_off := Finset.univ.filter
      (fun xyz : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) × (Fin N0 → Fin q0) =>
        dHam xyz.1 xyz.2.1 = r0 ∧ dHam xyz.1 xyz.2.2 = r0 ∧ xyz.2.1 ≠ xyz.2.2)
    let T3_all := Finset.univ.filter
      (fun xyz : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) × (Fin N0 → Fin q0) =>
        dHam xyz.1 xyz.2.1 = r0 ∧ dHam xyz.1 xyz.2.2 = r0)
    have hT3_sub : T3_off ⊆ T3_all := by
      intro xyz hxyz
      simp only [T3_off, T3_all, Finset.mem_filter, Finset.mem_univ, true_and] at hxyz ⊢
      exact ⟨hxyz.1, hxyz.2.1⟩
    have hmaps3 : ∀ xyz ∈ T3_all, (xyz.1, xyz.2.1) ∈ E_all := by
      intro xyz hxyz
      simp only [T3_all, E_all, Finset.mem_filter, Finset.mem_univ, true_and] at hxyz ⊢
      exact hxyz.1
    have hxy_bound : ∀ xy ∈ E_all,
        ∑ xyz ∈ T3_all.filter (fun xyz => (xyz.1, xyz.2.1) = xy),
          p_k ^ 3 * p_e ^ (homQueries xyz.1 ∪ homQueries xyz.2.1 ∪ homQueries xyz.2.2).card ≤
        (p_k ^ 2 * p_e ^ U_r) * ((3 / 2 : ℝ) * γ * D_star) := by
      intro ⟨x, y⟩ hxy
      have hdxy : dHam x y = r0 := (Finset.mem_filter.mp hxy).2
      let S_x := Finset.univ.filter (fun z : Fin N0 → Fin q0 => dHam x z = r0)
      have hfib_img : T3_all.filter (fun xyz => (xyz.1, xyz.2.1) = (x, y)) =
          S_x.image (fun z => (x, (y, z))) := by
        ext ⟨x', y', z'⟩
        simp only [T3_all, S_x, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
          Prod.mk.injEq]
        constructor
        · rintro ⟨⟨_, hdz⟩, rfl, rfl⟩
          exact ⟨z', hdz, rfl, rfl, rfl⟩
        · rintro ⟨z, hdz, rfl, rfl, rfl⟩
          exact ⟨⟨hdxy, hdz⟩, rfl, rfl⟩
      rw [hfib_img, Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj (Prod.mk.inj h).2).2)]
      obtain ⟨hs1_a, hs1_b⟩ := queryTripleCardinalityAndFibers N0 q0 r0 x y hdxy
      let b_fn : (Fin N0 → Fin q0) → ℕ :=
        fun z => ((disagreeSet x y).filter (fun v => z v = y v)).card
      have hmaps_b : ∀ z ∈ S_x, b_fn z ∈ Finset.range (r0 + 1) := by
        intro z hz
        have hdz : dHam x z = r0 := (Finset.mem_filter.mp hz).2
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hs1_a z hdz).1)
      rw [← Finset.sum_fiberwise_of_maps_to hmaps_b]
      have hb_bound : ∀ b ∈ Finset.range (r0 + 1),
          ∑ z ∈ S_x.filter (fun z => b_fn z = b),
            p_k ^ 3 * p_e ^ (homQueries x ∪ homQueries y ∪ homQueries z).card ≤
          (p_k ^ 2 * p_e ^ U_r) *
            (p_k *
              (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) *
                ((q0 - 1 : ℕ) : ℝ) ^ (r0 - b)) *
               p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2))) := by
        intro b hb_mem
        have hb : b ≤ r0 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb_mem)
        have hpt : ∀ z ∈ S_x.filter (fun z => b_fn z = b),
            p_k ^ 3 * p_e ^ (homQueries x ∪ homQueries y ∪ homQueries z).card ≤
            (p_k ^ 2 * p_e ^ U_r) *
              (p_k * p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2)) := by
          intro z hz
          obtain ⟨hzS, hbz⟩ := Finset.mem_filter.mp hz
          have hdz : dHam x z = r0 := (Finset.mem_filter.mp hzS).2
          have hcard_le := (hs1_a z hdz).2
          change (homQueries x ∪ homQueries y).card +
            ((r0 - b_fn z) * (N0 - 1) - (r0 - b_fn z).choose 2) ≤ _ at hcard_le
          rw [h_union x y, hdxy, hbz] at hcard_le
          have hpe_le := pow_le_pow_of_le_one (le_of_lt hpe_pos) (le_of_lt hpe_lt1) hcard_le
          rw [pow_add] at hpe_le
          have hpk_nn : 0 ≤ p_k ^ 3 := by positivity
          calc
            p_k ^ 3 * p_e ^ (homQueries x ∪ homQueries y ∪ homQueries z).card
              ≤ p_k ^ 3 * (p_e ^ U_r * p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2)) :=
                mul_le_mul_of_nonneg_left hpe_le hpk_nn
            _ = (p_k ^ 2 * p_e ^ U_r) *
                  (p_k * p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2)) := by ring
        have hcard_fib : ((S_x.filter (fun z => b_fn z = b)).card : ℝ) ≤
            (r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) *
              ((q0 - 1 : ℕ) : ℝ) ^ (r0 - b) := by
          have hfeq : S_x.filter (fun z => b_fn z = b) =
              Finset.univ.filter (fun z => dHam x z = r0 ∧ b_fn z = b) := by
            ext z
            simp [S_x]
          rw [hfeq]
          have hnat := hs1_b b hb
          have hcast : (((Finset.univ.filter (fun z => dHam x z = r0 ∧ b_fn z = b)).card : ℕ) : ℝ) ≤
              ((r0.choose b * (N0 - b).choose (r0 - b) * (q0 - 1) ^ (r0 - b) : ℕ) : ℝ) := by
            exact_mod_cast hnat
          push_cast at hcast
          exact hcast
        calc
          ∑ z ∈ S_x.filter (fun z => b_fn z = b),
              p_k ^ 3 * p_e ^ (homQueries x ∪ homQueries y ∪ homQueries z).card
            ≤ ((S_x.filter (fun z => b_fn z = b)).card : ℝ) *
                ((p_k ^ 2 * p_e ^ U_r) *
                  (p_k * p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2))) := by
              simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hpt
          _ ≤ ((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) *
                ((q0 - 1 : ℕ) : ℝ) ^ (r0 - b)) *
                ((p_k ^ 2 * p_e ^ U_r) *
                  (p_k * p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2))) :=
              mul_le_mul_of_nonneg_right hcard_fib (by positivity)
          _ = (p_k ^ 2 * p_e ^ U_r) *
                (p_k *
                  (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) *
                    ((q0 - 1 : ℕ) : ℝ) ^ (r0 - b)) *
                   p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2))) := by ring
      calc
        ∑ b ∈ Finset.range (r0 + 1),
            ∑ z ∈ S_x.filter (fun z => b_fn z = b),
              p_k ^ 3 * p_e ^ (homQueries x ∪ homQueries y ∪ homQueries z).card
          ≤ ∑ b ∈ Finset.range (r0 + 1),
              (p_k ^ 2 * p_e ^ U_r) *
                (p_k *
                  (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) *
                    ((q0 - 1 : ℕ) : ℝ) ^ (r0 - b)) *
                   p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2))) :=
            Finset.sum_le_sum hb_bound
        _ = (p_k ^ 2 * p_e ^ U_r) *
              ∑ b ∈ Finset.range (r0 + 1),
                p_k *
                  (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) *
                    ((q0 - 1 : ℕ) : ℝ) ^ (r0 - b)) *
                   p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2)) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ (p_k ^ 2 * p_e ^ U_r) * ((3 / 2 : ℝ) * γ * D_star) :=
            mul_le_mul_of_nonneg_left h_s3_gen (by positivity)
    calc
      ∑ xyz ∈ T3_off,
          p_k ^ 3 * p_e ^ (homQueries xyz.1 ∪ homQueries xyz.2.1 ∪ homQueries xyz.2.2).card
        ≤ ∑ xyz ∈ T3_all,
            p_k ^ 3 * p_e ^ (homQueries xyz.1 ∪ homQueries xyz.2.1 ∪ homQueries xyz.2.2).card :=
          Finset.sum_le_sum_of_subset_of_nonneg hT3_sub (fun _ _ _ => by positivity)
      _ = ∑ xy ∈ E_all,
            ∑ xyz ∈ T3_all.filter (fun xyz => (xyz.1, xyz.2.1) = xy),
              p_k ^ 3 * p_e ^ (homQueries xyz.1 ∪ homQueries xyz.2.1 ∪ homQueries xyz.2.2).card :=
          (Finset.sum_fiberwise_of_maps_to hmaps3 _).symm
      _ ≤ (E_all.card : ℝ) * ((p_k ^ 2 * p_e ^ U_r) * ((3 / 2 : ℝ) * γ * D_star)) := by
          simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hxy_bound
      _ = ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r)) * ((3 / 2 : ℝ) * γ * D_star) := by ring
      _ = (3 / 2 : ℝ) * γ * n_0 * D_star ^ 2 := by
          rw [hM0_const]
          ring
  · let E4_disj := Finset.univ.filter
      (fun e₁₂ : ((Fin N0 → Fin q0) × (Fin N0 → Fin q0)) ×
                 ((Fin N0 → Fin q0) × (Fin N0 → Fin q0)) =>
        dHam e₁₂.1.1 e₁₂.1.2 = r0 ∧ dHam e₁₂.2.1 e₁₂.2.2 = r0 ∧
        e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
        e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2)
    have hE4_sub : E4_disj ⊆ E_all ×ˢ E_all := by
      intro e₁₂ he
      simp only [E4_disj, E_all, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
        true_and] at he ⊢
      exact ⟨he.1, he.2.1⟩
    have hq1_pos : (0 : ℝ) < ((q0 - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < q0 - 1 by omega)
    have hq1_le_qr : ((q0 - 1 : ℕ) : ℝ) ≤ (q0 : ℝ) := by
      exact_mod_cast (Nat.sub_le q0 1)
    have h1_le_inv_pe : 1 ≤ p_e⁻¹ := (one_le_inv₀ hpe_pos).mpr (le_of_lt hpe_lt1)
    have hinner_bound :=
      @edgeMoments_hinner_bound N0 q0 r0 p_k p_e γ hpk_pos hpe_pos h_union h_s4_gen
          hE_card hq1_pos hq1_le_qr h1_le_inv_pe
    calc
      ∑ e₁₂ ∈ E4_disj,
          p_k ^ 4 * p_e ^ (homQueries e₁₂.1.1 ∪ homQueries e₁₂.1.2 ∪
                           homQueries e₁₂.2.1 ∪ homQueries e₁₂.2.2).card
        ≤ ∑ e₁₂ ∈ E_all ×ˢ E_all,
            p_k ^ 4 * p_e ^ (homQueries e₁₂.1.1 ∪ homQueries e₁₂.1.2 ∪
                             homQueries e₁₂.2.1 ∪ homQueries e₁₂.2.2).card :=
          Finset.sum_le_sum_of_subset_of_nonneg hE4_sub (fun _ _ _ => by positivity)
      _ = ∑ xy ∈ E_all,
            ∑ xy' ∈ E_all,
              p_k ^ 4 * p_e ^ (homQueries xy.1 ∪ homQueries xy.2 ∪
                               homQueries xy'.1 ∪ homQueries xy'.2).card :=
          Finset.sum_product' E_all E_all (fun xy xy' =>
            p_k ^ 4 * p_e ^ (homQueries xy.1 ∪ homQueries xy.2 ∪
                             homQueries xy'.1 ∪ homQueries xy'.2).card)
      _ ≤ (E_all.card : ℝ) * ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2 * (2 * γ)) := by
          simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hinner_bound
      _ = 2 * γ * ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r)) ^ 2 := by ring
      _ = 2 * γ * (n_0 * D_star) ^ 2 := by rw [hM0_const]

theorem raw_degree_and_edge_second_moment_sums (C₁ : ℕ) (hC₁ : 3 ≤ C₁) (r_star : ℕ) (hr : 1000 *
    C₁ < r_star)
    (hσ_pos : 0 < cspSigmaEdge C₁ r_star)
    (hp_edge_pos : 0 < cspPEdge C₁ r_star)
    (hp_edge_lt1 : cspPEdge C₁ r_star < 1)
    (h_cal : (4 : ℝ) * (2 : ℝ) ^ cspL C₁ * ((cspQ C₁ - 1 : ℕ) : ℝ) *
      (cspPEdge C₁ r_star) ^ (2 ^ cspL C₁ * r_star - 1) = (2 : ℝ) ^ (-(cspGamma0 C₁ : ℝ)))
    (hσ_low : (cspBeta0 C₁ : ℝ) ≤ cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2)
    (hp_keep_pos : 0 < cspPKeep C₁ r_star)
    (h_union_card : ∀ x y : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      (homQueries x ∪ homQueries y).card =
        (2 ^ cspL C₁ * r_star).choose 2 +
          dHam x y * (2 ^ cspL C₁ * r_star - 1) - (dHam x y).choose 2)
    (h_M0 : ∑ xy ∈ Finset.univ.filter
        (fun xy : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                  (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
          dHam xy.1 xy.2 = r_star),
      (cspPKeep C₁ r_star) ^ 2 *
        (cspPEdge C₁ r_star) ^ (homQueries xy.1 ∪ homQueries xy.2).card =
      cspN0 C₁ r_star * cspDStar C₁ r_star) :
    (∑ xyz ∈ Finset.univ.filter
        (fun xyz : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                   (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                   (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
          dHam xyz.1 xyz.2.1 = r_star ∧ dHam xyz.1 xyz.2.2 = r_star ∧ xyz.2.1 ≠ xyz.2.2),
      (cspPKeep C₁ r_star) ^ 3 *
        (cspPEdge C₁ r_star) ^ (homQueries xyz.1 ∪ homQueries xyz.2.1 ∪ homQueries xyz.2.2).card ≤
        (3 / 2 : ℝ) * cspGamma r_star *
          cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2) ∧
    (∑ e₁₂ ∈ Finset.univ.filter
        (fun e₁₂ : ((Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                    (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) ×
                   ((Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                    (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) =>
          dHam e₁₂.1.1 e₁₂.1.2 = r_star ∧ dHam e₁₂.2.1 e₁₂.2.2 = r_star ∧
          e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
          e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2),
      (cspPKeep C₁ r_star) ^ 4 *
        (cspPEdge C₁ r_star) ^ (homQueries e₁₂.1.1 ∪ homQueries e₁₂.1.2 ∪
                                homQueries e₁₂.2.1 ∪ homQueries e₁₂.2.2).card ≤
        2 * cspGamma r_star *
          (cspN0 C₁ r_star * cspDStar C₁ r_star) ^ 2) :=
by
  have hr_ge : 3001 ≤ r_star := by omega
  have hq_ge2 : 2 ≤ cspQ C₁ := by
    unfold cspQ
    have := @Nat.one_le_two_pow (cspEq C₁)
    omega
  have hq1_pos_nat : 1 ≤ cspQ C₁ - 1 := by omega
  have hL_ge20 : 20 ≤ cspL C₁ := by unfold cspL; omega
  have hlam0_1000 := (lam0_ge_1000_C1 C₁ hC₁).2.1
  have hlam0_ge3000 : 3000 ≤ cspLam0 C₁ := by omega
  have hbeta0_ge1000 : 1000 ≤ cspBeta0 C₁ := by unfold cspBeta0; omega
  have hgam_le_L : cspGamma0 C₁ ≤ cspL C₁ := by
    unfold cspGamma0 cspL cspInvEta0
    have hsq : 9 ≤ C₁ ^ 2 := Nat.pow_le_pow_left hC₁ 2
    have hmul : 5 * cspLam0 C₁ ≤ 20 * C₁ ^ 2 * 80 * cspLam0 C₁ :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hσ_low6 : 6 * (cspLam0 C₁ : ℝ) ≤ cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 := by
    have hbeq : (cspBeta0 C₁ : ℝ) = 6 * (cspLam0 C₁ : ℝ) := by unfold cspBeta0; push_cast; ring
    linarith only [hbeq, hσ_low]
  have hD_nn : 0 ≤ cspDStar C₁ r_star := by
    unfold cspDStar
    exact Real.rpow_nonneg (by norm_num) _
  have h_s3 := hypergeometricMoment_bound (cspL C₁) r_star (cspQ C₁ - 1) (cspLam0 C₁) (cspGamma0 C₁)
    (cspSigmaEdge C₁ r_star) (cspDStar C₁ r_star)
    hr_ge hq1_pos_nat hlam0_ge3000 rfl hσ_pos hD_nn h_cal hσ_low6
  have h_s4 : ∑ k₁ ∈ Finset.range (2 ^ cspL C₁ * r_star + 1),
      ∑ k₂ ∈ Finset.range (r_star + 1),
        (((2 ^ cspL C₁ * r_star).choose k₁ : ℕ) : ℝ) *
        ((r_star.choose k₂ : ℕ) : ℝ) *
        ((2 : ℝ) / ((cspQ C₁ - 1 : ℕ) : ℝ)) ^ (k₁ + k₂) *
        ((cspPEdge C₁ r_star)⁻¹) ^ ((k₁ + k₂).choose 2) ≤
      2 * cspGamma r_star := by
    have hq1_eq : cspQ C₁ - 1 = 2 ^ (2 * cspBeta0 C₁ * 2 ^ cspL C₁) := Nat.add_sub_cancel _ 1
    rw [hq1_eq]
    exact vandermondeMoment_bound (cspL C₁) (cspBeta0 C₁) (cspGamma0 C₁) r_star
      hL_ge20 hbeta0_ge1000 hgam_le_L hr_ge
  exact rawMoments_assembly (2 ^ cspL C₁ * r_star) (cspQ C₁) r_star
    (cspPKeep C₁ r_star) (cspPEdge C₁ r_star)
    (cspN0 C₁ r_star) (cspDStar C₁ r_star) (cspGamma r_star)
    hq_ge2 hp_keep_pos hp_edge_pos hp_edge_lt1
    h_union_card h_M0 h_s3 h_s4

end Helpers

end HighDimSteinerSpanners.Proofs.CSP
