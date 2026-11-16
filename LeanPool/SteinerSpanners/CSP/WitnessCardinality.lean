/-
Copyright (c) 2026 Goran Zuzic et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Goran Zuzic, David P. Woodruff, Vahab Mirrokni
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

public import LeanPool.SteinerSpanners.CSP.CalibrationBounds

/-! # Witness Cardinality for spanner CSP codes

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib.
-/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners.Proofs.CSP

noncomputable section Helpers

lemma candMFresh_subset_union {N q : ℕ} (a b : Fin N → Fin q)
    (m : ℕ) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q) :
    candMFresh a b m z_prev x ⊆ diffCoords x a ∪ diffCoords x b := by
  intro v hv
  simp only [candMFresh, cspRvc, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image] at hv
  simp only [diffCoords, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inl (fun hxa => hv (Or.inl (Or.inl ⟨v, hxa.symm ▸ rfl⟩)))

lemma candMWit_card_le {N q : ℕ} (C₁ r_star m : ℕ)
    (hC₁ : 3 ≤ C₁) (hr : 1000 * C₁ < r_star)
    (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q)
    (hd_xa : dHam x a ≤ C₁ * r_star) (hd_xb : dHam x b ≤ C₁ * r_star) :
    let M := candMFresh a b m z_prev x
    ((candMWit C₁ r_star a b m z_prev x).card : ℝ) ≤
      (2 : ℝ) ^ (3 * (r_star : ℝ) + (1 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (M.card : ℝ)) := by
  intro M
  let K_max := cspKMax C₁
  let W_ab := diffCoords x a ∪ diffCoords x b
  have hW_card : W_ab.card ≤ 2 * C₁ * r_star := by
    have h1 := Finset.card_union_le (diffCoords x a) (diffCoords x b)
    have h2 : (diffCoords x a).card ≤ C₁ * r_star := hd_xa
    have h3 : (diffCoords x b).card ≤ C₁ * r_star := hd_xb
    calc
      W_ab.card ≤ C₁ * r_star + C₁ * r_star := le_trans h1 (Nat.add_le_add h2 h3)
      _ = 2 * C₁ * r_star := by ring
  let base := (Finset.univ : Finset (Fin (K_max + 1))) ×ˢ
    (Fintype.piFinset (fun u : Fin N =>
      if u ∈ M then Finset.univ else ({0} : Finset (Fin (K_max + 1)))) ×ˢ
      Fintype.piFinset (fun _ : Fin K_max => M.powerset))
  let s_hat := fun (k : Fin (K_max + 1)) (τ : Fin N → Fin (K_max + 1)) (r : Fin K_max) =>
    if r.1 < k.1 then (M.filter (fun u => τ u = r.succ)).card - (11 * r_star) / 40 else 0
  have hcard_le1 : (candMWit C₁ r_star a b m z_prev x).card ≤
      ∑ ktB ∈ base, (((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).card).choose
        (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r) := by
    have h1 : (candMWit C₁ r_star a b m z_prev x).card ≤
        (base.biUnion (fun ktB =>
          (((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).powersetCard
            (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r)).image
            (fun U_out => (ktB.1, ktB.2.1, ktB.2.2, U_out)))).card :=
      Finset.card_filter_le _ _
    refine le_trans h1 (le_trans Finset.card_biUnion_le (Finset.sum_le_sum (fun ktB _ => ?_)))
    exact le_trans Finset.card_image_le (le_of_eq (Finset.card_powersetCard _ _))
  have hU_card : ((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).card ≤ 16 * C₁ ^ 2 * r_star := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    calc
      K_max * W_ab.card ≤ (8 * C₁) * (2 * C₁ * r_star) :=
        Nat.mul_le_mul_left K_max hW_card
      _ = 16 * C₁ ^ 2 * r_star := by ring
  have hS_le : ∀ ktB : Fin (K_max + 1) × (Fin N → Fin (K_max + 1)) × (Fin K_max → Finset (Fin N)),
      ∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r ≤ M.card := by
    intro ktB
    have hle1 : ∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r ≤
        ∑ r : Fin K_max, (M.filter (fun u => ktB.2.1 u = r.succ)).card := by
      refine Finset.sum_le_sum (fun r _ => ?_)
      dsimp [s_hat]
      split_ifs
      · exact Nat.sub_le _ _
      · exact Nat.zero_le _
    have hdisj : ((Finset.univ : Finset (Fin K_max)) : Set (Fin K_max)).PairwiseDisjoint
        (fun r => M.filter (fun u => ktB.2.1 u = r.succ)) := by
      intro r₁ _ r₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro u hu₁ hu₂
      simp only [Finset.mem_filter] at hu₁ hu₂
      exact hne (Fin.succ_injective _ (hu₁.2.symm.trans hu₂.2))
    have hsub : (Finset.univ : Finset (Fin K_max)).biUnion
        (fun r => M.filter (fun u => ktB.2.1 u = r.succ)) ⊆ M := by
      intro u hu
      rcases Finset.mem_biUnion.mp hu with ⟨_, _, huM⟩
      exact (Finset.mem_filter.mp huM).1
    rw [← Finset.card_biUnion hdisj] at hle1
    exact le_trans hle1 (Finset.card_le_card hsub)
  have hbase_card : base.card =
      (K_max + 1) * ((K_max + 1) ^ M.card * (2 ^ M.card) ^ K_max) := by
    dsimp [base]
    rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin,
      Fintype.card_piFinset, Fintype.card_piFinset]
    have htau : ∀ u : Fin N,
        (if u ∈ M then Finset.univ else ({0} : Finset (Fin (K_max + 1)))).card =
          if u ∈ M then K_max + 1 else 1 := by
      intro u
      split_ifs
      · rw [Finset.card_univ, Fintype.card_fin]
      · exact Finset.card_singleton 0
    simp_rw [htau, Finset.card_powerset]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsum_r : ((candMWit C₁ r_star a b m z_prev x).card : ℝ) ≤
      (base.card : ℝ) * ((16 * (C₁ : ℝ) ^ 2) ^ M.card * (4 : ℝ) ^ r_star) := by
    have hc : ((candMWit C₁ r_star a b m z_prev x).card : ℝ) ≤
        ∑ ktB ∈ base, ((((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).card).choose
          (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r) : ℝ) := by
      exact_mod_cast hcard_le1
    calc
      ((candMWit C₁ r_star a b m z_prev x).card : ℝ)
        ≤ ∑ ktB ∈ base, ((((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).card).choose
            (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r) : ℝ) := hc
      _ ≤ ∑ _ktB ∈ base, ((16 * (C₁ : ℝ) ^ 2) ^ M.card * (4 : ℝ) ^ r_star) := by
          refine Finset.sum_le_sum (fun ktB _ => ?_)
          have hch := choose_bound_exp4 (((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).card)
            (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r) M.card r_star (16 * C₁ ^ 2)
            (by nlinarith) hU_card (hS_le ktB)
          simpa using hch
      _ = (base.card : ℝ) * ((16 * (C₁ : ℝ) ^ 2) ^ M.card * (4 : ℝ) ^ r_star) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hconst_r : ((K_max + 1 : ℕ) : ℝ) * (4 : ℝ) ^ r_star ≤ (2 : ℝ) ^ (3 * (r_star : ℝ)) := by
    have hk_r : K_max + 1 ≤ 2 ^ r_star := by
      have hk1 : K_max + 1 ≤ r_star := by dsimp [K_max, cspKMax]; omega
      exact le_trans hk1 (le_of_lt Nat.lt_two_pow_self)
    have hk_real : ((K_max + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (r_star : ℝ) := by
      have hc : ((K_max + 1 : ℕ) : ℝ) ≤ ((2 ^ r_star : ℕ) : ℝ) := by exact_mod_cast hk_r
      rwa [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast] at hc
    have h4_eq : (4 : ℝ) ^ r_star = (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← pow_mul, ← Real.rpow_natCast]
      push_cast; rfl
    calc
      ((K_max + 1 : ℕ) : ℝ) * (4 : ℝ) ^ r_star
        ≤ (2 : ℝ) ^ (r_star : ℝ) * (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
          rw [h4_eq]; exact mul_le_mul_of_nonneg_right hk_real (by positivity)
      _ = (2 : ℝ) ^ (3 * (r_star : ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
  have hper_s : ((K_max + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K_max * (16 * (C₁ : ℝ) ^ 2) ≤
      (2 : ℝ) ^ ((1 / 10 : ℝ) * (cspLam0 C₁ : ℝ)) := by
    have hk_pow : K_max + 1 ≤ 2 ^ K_max := Nat.lt_two_pow_self
    have hC_pow : C₁ ≤ 2 ^ Nat.clog 2 C₁ := Nat.le_pow_clog (by decide : 1 < 2) C₁
    have hnat : (K_max + 1) * 2 ^ K_max * (16 * C₁ ^ 2) ≤
        2 ^ (10 * C₁ * (2 * Nat.clog 2 C₁ + 6)) := by
      have h1 : (K_max + 1) * 2 ^ K_max * (16 * C₁ ^ 2) ≤
          2 ^ K_max * 2 ^ K_max * (2 ^ 4 * (2 ^ Nat.clog 2 C₁) ^ 2) := by
        have hC2 : C₁ ^ 2 ≤ (2 ^ Nat.clog 2 C₁) ^ 2 := Nat.pow_le_pow_left hC_pow 2
        have h16 : 16 * C₁ ^ 2 ≤ 2 ^ 4 * (2 ^ Nat.clog 2 C₁) ^ 2 := by
          simpa using Nat.mul_le_mul_left 16 hC2
        exact Nat.mul_le_mul (Nat.mul_le_mul_right _ hk_pow) h16
      have h2 : 2 ^ K_max * 2 ^ K_max * (2 ^ 4 * (2 ^ Nat.clog 2 C₁) ^ 2) =
          2 ^ (2 * K_max + 4 + 2 * Nat.clog 2 C₁) := by
        rw [← pow_mul (2 : ℕ) (Nat.clog 2 C₁) 2,
          show Nat.clog 2 C₁ * 2 = 2 * Nat.clog 2 C₁ by ring,
          ← pow_add, ← pow_add, ← pow_add]
        congr 1; omega
      have hclog_ge2 := (lam0_ge_1000_C1 C₁ hC₁).1
      have hexp : 2 * K_max + 4 + 2 * Nat.clog 2 C₁ ≤ 10 * C₁ * (2 * Nat.clog 2 C₁ + 6) := by
        dsimp [K_max, cspKMax]
        have h10 : 10 ≤ 2 * Nat.clog 2 C₁ + 6 := by omega
        nlinarith
      rw [h2] at h1
      exact le_trans h1 (Nat.pow_le_pow_right (by norm_num) hexp)
    have hcast : ((K_max + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K_max * (16 * (C₁ : ℝ) ^ 2) ≤
        ((2 ^ (10 * C₁ * (2 * Nat.clog 2 C₁ + 6)) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    refine le_trans hcast (le_of_eq ?_)
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    congr 1
    dsimp [cspLam0]
    push_cast
    ring
  have hrew_base : (base.card : ℝ) * ((16 * (C₁ : ℝ) ^ 2) ^ M.card * (4 : ℝ) ^ r_star) =
      (((K_max + 1 : ℕ) : ℝ) * (4 : ℝ) ^ r_star) *
        (((K_max + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K_max * (16 * (C₁ : ℝ) ^ 2)) ^ M.card := by
    rw [hbase_card]
    push_cast
    rw [pow_right_comm (2 : ℝ) M.card K_max]
    repeat rw [mul_pow]
    ring
  calc
    ((candMWit C₁ r_star a b m z_prev x).card : ℝ)
      ≤ (((K_max + 1 : ℕ) : ℝ) * (4 : ℝ) ^ r_star) *
          (((K_max + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K_max * (16 * (C₁ : ℝ) ^ 2)) ^ M.card := by
        rwa [hrew_base] at hsum_r
    _ ≤ (2 : ℝ) ^ (3 * (r_star : ℝ)) *
          ((2 : ℝ) ^ ((1 / 10 : ℝ) * (cspLam0 C₁ : ℝ))) ^ M.card :=
        mul_le_mul hconst_r (pow_le_pow_left₀ (by positivity) hper_s M.card)
          (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (3 * (r_star : ℝ) + (1 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (M.card : ℝ)) := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ _) M.card,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

lemma candMWit_quad {N q : ℕ} (C₁ r_star m : ℕ)
    (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q) :
    let M := candMFresh a b m z_prev x
    ∀ w ∈ candMWit C₁ r_star a b m z_prev x,
      (∀ uv ∈ candA2 C₁ a b x M w, uv.1 ≠ uv.2) ∧
      40 * ((M.card : ℤ) ^ 2 - 2 * ((candA2 C₁ a b x M w).card : ℤ)) ≤
        23 * (r_star : ℤ) * (M.card : ℤ) := by
  intro M
  let K_max := cspKMax C₁
  let W_ab := diffCoords x a ∪ diffCoords x b
  have hM_sub_W : M ⊆ W_ab := candMFresh_subset_union a b m z_prev x
  intro w hw
  have hw_filt := (Finset.mem_filter.mp hw).2
  let k := w.1
  let τ := w.2.1
  let B_fut := w.2.2.1
  let U_out := w.2.2.2
  rcases hw_filt with ⟨hτ_le, htail_le, hr_props⟩
  let M_piece := fun r : Fin K_max => M.filter (fun u => τ u = r.succ)
  let I_tilde := fun r : Fin K_max => M.filter (fun u => τ u = 0 ∨ r.1 + 1 < (τ u).1)
  let B_out := fun r : Fin K_max => W_ab.filter (fun v => (r, v) ∈ U_out)
  refine ⟨?_, ?_⟩
  · rintro ⟨u, v⟩ huv
    simp only [candA2, Finset.mem_filter, Finset.mem_product] at huv
    rcases huv with ⟨⟨huM, hvW⟩, r, hrk, hτu, hvB⟩
    obtain ⟨hBf_sub, _, hBo_disj, _⟩ := hr_props r hrk
    dsimp only
    intro heq
    subst heq
    rcases hvB with hvf | hvo
    · have huI := (Finset.mem_filter.mp (hBf_sub hvf)).2
      rw [hτu] at huI
      rcases huI with h0 | hlt
      · exact Fin.succ_ne_zero r h0
      · simp at hlt
    · have huBo : u ∈ B_out r := Finset.mem_filter.mpr ⟨hvW, hvo⟩
      have huMr : u ∈ M_piece r := Finset.mem_filter.mpr ⟨huM, hτu⟩
      exact Finset.disjoint_left.mp hBo_disj huBo (Finset.mem_union_left _ huMr)
  · -- Exact card of candA2
    let R_lt := (Finset.univ : Finset (Fin K_max)).filter (fun r => r.1 < k.1)
    have hA2_eq : candA2 C₁ a b x M w =
        R_lt.biUnion (fun r => M_piece r ×ˢ (B_fut r ∪ B_out r)) := by
      ext ⟨u, v⟩
      simp only [candA2, R_lt, M_piece, B_out, Finset.mem_filter, Finset.mem_product,
        Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨huM, hvW⟩, r, hrk, hτu, hvf | hvo⟩
        · exact ⟨r, hrk, ⟨huM, hτu⟩, Finset.mem_union_left _ hvf⟩
        · exact ⟨r, hrk, ⟨huM, hτu⟩, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvW, hvo⟩)⟩
      · rintro ⟨r, hrk, ⟨huM, hτu⟩, hv⟩
        rcases Finset.mem_union.mp hv with hvf | hvo
        · have hvfM : v ∈ M := (Finset.mem_filter.mp ((hr_props r hrk).1 hvf)).1
          exact ⟨⟨huM, hM_sub_W hvfM⟩, r, hrk, hτu, Or.inl hvf⟩
        · rcases Finset.mem_filter.mp hvo with ⟨hvW, hvoU⟩
          exact ⟨⟨huM, hvW⟩, r, hrk, hτu, Or.inr hvoU⟩
    have hA2_disj : (R_lt : Set (Fin K_max)).PairwiseDisjoint
        (fun r => M_piece r ×ˢ (B_fut r ∪ B_out r)) := by
      intro r₁ _ r₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      rintro ⟨u, v⟩ h₁ h₂
      simp only [M_piece, Finset.mem_product, Finset.mem_filter] at h₁ h₂
      exact hne (Fin.succ_injective _ (h₁.1.2.symm.trans h₂.1.2))
    have hA2_card : (candA2 C₁ a b x M w).card =
        ∑ r ∈ R_lt, (M_piece r).card * ((B_fut r).card + (B_out r).card) := by
      rw [hA2_eq, Finset.card_biUnion hA2_disj]
      refine Finset.sum_congr rfl (fun r hr => ?_)
      have hrk : r.1 < k.1 := (Finset.mem_filter.mp hr).2
      obtain ⟨hBf_sub, _, hBo_disj, _⟩ := hr_props r hrk
      have hdisj_f_o : Disjoint (B_fut r) (B_out r) := by
        rw [Finset.disjoint_left]
        intro z hzf hzo
        exact Finset.disjoint_left.mp hBo_disj hzo (Finset.mem_union_right _ (hBf_sub hzf))
      rw [Finset.card_product, Finset.card_union_of_disjoint hdisj_f_o]
    -- Backward induction on suffix j = k.1 - d
    let Suf := fun j : ℕ => M.filter (fun u => τ u = 0 ∨ j < (τ u).1)
    let A2_suf := fun j : ℕ =>
      ∑ r ∈ R_lt.filter (fun r => j ≤ r.1),
        (M_piece r).card * ((B_fut r).card + (B_out r).card)
    have h_ind : ∀ d : ℕ, d ≤ k.1 →
        40 * (((Suf (k.1 - d)).card : ℤ) ^ 2 - 2 * (A2_suf (k.1 - d) : ℤ)) ≤
          23 * (r_star : ℤ) * ((Suf (k.1 - d)).card : ℤ) := by
      intro d
      induction d with
      | zero =>
        intro _
        simp only [Nat.sub_zero]
        have hSuf_k : Suf k.1 = M.filter (fun u => τ u = 0) := by
          ext u
          simp only [Suf, Finset.mem_filter]
          constructor
          · rintro ⟨huM, h0 | hgt⟩
            · exact ⟨huM, h0⟩
            · exact absurd (hτ_le u huM) (not_le_of_gt hgt)
          · rintro ⟨huM, h0⟩
            exact ⟨huM, Or.inl h0⟩
        have hA2_k : A2_suf k.1 = 0 := by
          apply Finset.sum_eq_zero
          intro r hr
          simp only [R_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hr
          omega
        rw [hSuf_k, hA2_k]
        have ht_int : 2 * (((M.filter (fun u => τ u = 0)).card : ℤ)) ≤ (r_star : ℤ) := by
          exact_mod_cast htail_le
        have ht_nn : (0 : ℤ) ≤ ((M.filter (fun u => τ u = 0)).card : ℤ) := Nat.cast_nonneg _
        nlinarith
      | succ d ih =>
        intro hd1
        let j := k.1 - (d + 1)
        have hjk : j < k.1 := by omega
        have hkd_eq : k.1 - d = j + 1 := by omega
        have hih := ih (by omega)
        rw [hkd_eq] at hih
        have hjK : j < K_max := lt_of_lt_of_le hjk (Nat.le_of_lt_succ k.2)
        let r0 : Fin K_max := ⟨j, hjK⟩
        have hr0_val : r0.1 = j := rfl
        have hr0_lt : r0.1 < k.1 := hjk
        obtain ⟨hBf_sub, hmiss_le, _, hBo_card⟩ := hr_props r0 hr0_lt
        have hSuf_split : Suf j = M_piece r0 ∪ Suf (j + 1) := by
          ext u
          simp only [Suf, M_piece, Finset.mem_union, Finset.mem_filter, Fin.ext_iff,
            Fin.val_succ, Fin.val_zero]
          rw [hr0_val]
          by_cases hu : u ∈ M
          · simp only [hu, true_and]
            omega
          · simp [hu]
        have hSuf_disj : Disjoint (M_piece r0) (Suf (j + 1)) := by
          rw [Finset.disjoint_left]
          intro u hu1 hu2
          simp only [M_piece, Suf, Finset.mem_filter, Fin.ext_iff,
            Fin.val_succ, Fin.val_zero] at hu1 hu2
          rw [hr0_val] at hu1
          omega
        have hSuf_card : (Suf j).card = (M_piece r0).card + (Suf (j + 1)).card := by
          rw [hSuf_split, Finset.card_union_of_disjoint hSuf_disj]
        have hA2_split : A2_suf j =
            (M_piece r0).card * ((B_fut r0).card + (B_out r0).card) + A2_suf (j + 1) := by
          have hset : R_lt.filter (fun r => j ≤ r.1) =
              insert r0 (R_lt.filter (fun r => j + 1 ≤ r.1)) := by
            ext r
            simp only [R_lt, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
              true_and, Fin.ext_iff]
            rw [hr0_val]
            omega
          have hnot : r0 ∉ R_lt.filter (fun r => j + 1 ≤ r.1) := by
            simp [r0]
          dsimp [A2_suf]
          rw [hset, Finset.sum_insert hnot]
        have hIt_eq : I_tilde r0 = Suf (j + 1) := rfl
        have hsdiff_card : (Suf (j + 1)).card =
            (I_tilde r0 \ B_fut r0).card + (B_fut r0).card := by
          rw [← hIt_eq, Finset.card_sdiff_add_card_eq_card hBf_sub]
        have hBo_card' : (B_out r0).card = (M_piece r0).card - (11 * r_star) / 40 := hBo_card
        have hBo_ineq : 40 * (M_piece r0).card ≤ 40 * (B_out r0).card + 11 * r_star := by
          rw [hBo_card']
          omega
        -- Finish step in ℤ
        set a_c : ℤ := ((M_piece r0).card : ℤ)
        set b_c : ℤ := ((Suf (j + 1)).card : ℤ)
        set f_c : ℤ := ((B_fut r0).card : ℤ)
        set m_c : ℤ := ((I_tilde r0 \ B_fut r0).card : ℤ)
        set o_c : ℤ := ((B_out r0).card : ℤ)
        have ha_nn : 0 ≤ a_c := Nat.cast_nonneg _
        have hbmf : b_c = m_c + f_c := by
          dsimp only [b_c, m_c, f_c]
          exact_mod_cast hsdiff_card
        have hmiss_le' : 80 * (I_tilde r0 \ B_fut r0).card ≤ r_star := hmiss_le
        have hm80 : 80 * m_c ≤ (r_star : ℤ) := by
          dsimp only [m_c]
          exact_mod_cast hmiss_le'
        have ho40 : 40 * a_c ≤ 40 * o_c + 11 * (r_star : ℤ) := by
          have hc : ((40 * (M_piece r0).card : ℕ) : ℤ) ≤
              ((40 * (B_out r0).card + 11 * r_star : ℕ) : ℤ) := by exact_mod_cast hBo_ineq
          push_cast at hc
          exact hc
        change 40 * (((Suf j).card : ℤ) ^ 2 - 2 * (A2_suf j : ℤ)) ≤
          23 * (r_star : ℤ) * ((Suf j).card : ℤ)
        rw [hSuf_card, hA2_split]
        push_cast
        change 40 * ((a_c + b_c) ^ 2 - 2 * (a_c * (f_c + o_c) + (A2_suf (j + 1) : ℤ))) ≤
          23 * (r_star : ℤ) * (a_c + b_c)
        have hterm_miss : 80 * a_c * (b_c - f_c) ≤ (r_star : ℤ) * a_c := by
          have hbf : b_c - f_c = m_c := by linarith only [hbmf]
          rw [hbf]
          nlinarith only [mul_le_mul_of_nonneg_right hm80 ha_nn]
        have hterm_out : 40 * (a_c ^ 2 - 2 * a_c * o_c) ≤ 22 * (r_star : ℤ) * a_c := by
          have hsq_nn : 0 ≤ 40 * a_c ^ 2 := by positivity
          nlinarith only [mul_le_mul_of_nonneg_right ho40 ha_nn, hsq_nn]
        change 40 * (b_c ^ 2 - 2 * (A2_suf (j + 1) : ℤ)) ≤ 23 * (r_star : ℤ) * b_c at hih
        nlinarith only [hih, hterm_miss, hterm_out]
    have h0 := h_ind k.1 (le_refl k.1)
    simp only [Nat.sub_self] at h0
    have hSuf0 : Suf 0 = M := by
      ext u
      simp only [Suf, Finset.mem_filter, Fin.ext_iff, Fin.val_zero]
      constructor
      · exact fun h => h.1
      · intro hu; exact ⟨hu, by omega⟩
    have hA2_0 : A2_suf 0 = (candA2 C₁ a b x M w).card := by
      rw [hA2_card]
      dsimp [A2_suf]
      congr 1
      ext r
      simp
    rwa [hSuf0, hA2_0] at h0

lemma candMWit_card_and_quad {N q : ℕ} (C₁ r_star m : ℕ)
    (hC₁ : 3 ≤ C₁) (hr : 1000 * C₁ < r_star)
    (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q)
    (hd_xa : dHam x a ≤ C₁ * r_star) (hd_xb : dHam x b ≤ C₁ * r_star) :
    let M := candMFresh a b m z_prev x
    ((candMWit C₁ r_star a b m z_prev x).card : ℝ) ≤
      (2 : ℝ) ^ (3 * (r_star : ℝ) + (1 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (M.card : ℝ)) ∧
    ∀ w ∈ candMWit C₁ r_star a b m z_prev x,
      (∀ uv ∈ candA2 C₁ a b x M w, uv.1 ≠ uv.2) ∧
      40 * ((M.card : ℤ) ^ 2 - 2 * ((candA2 C₁ a b x M w).card : ℤ)) ≤
        23 * (r_star : ℤ) * (M.card : ℤ) := by
  exact ⟨candMWit_card_le C₁ r_star m hC₁ hr a b z_prev x hd_xa hd_xb,
    candMWit_quad C₁ r_star m a b z_prev x⟩

end Helpers

end HighDimSteinerSpanners.Proofs.CSP
