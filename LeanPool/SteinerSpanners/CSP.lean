/-
Copyright (c) 2026 Goran Zuzic et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Goran Zuzic, David P. Woodruff, Vahab Mirrokni
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

public import Mathlib.Analysis.SpecialFunctions.Log.Base

public import LeanPool.SteinerSpanners.CSP.Existence

/-! # Locally list-bounded CSP codes

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib.
-/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners.Proofs.CSP

/-- **Theorem 2.3 (Existence of Locally List-Bounded `2`-CSP Codes, Module 3)** Takes Lemma
6.3 (`h_6_3`) as an explicit hypothesis so this module compiles independently. -/
theorem thm_2_3_from_6_3
    (h_6_3 : ∀ (N q C₁ rStar : ℕ), 2 ≤ N → 2 ≤ q → 3 ≤ C₁ → 1 ≤ rStar →
      ∀ (R : Fin N → Fin N → Fin q → Fin q → Prop),
        Symmetric2CSP R →
        ∀ (X : Finset (Fin N → Fin q)),
          X ⊆ satisfyingSet R →
          let η₀ : ℝ := 1 / 80
          (∀ x ∈ X, ∀ u ∈ X, ∀ z ∈ satisfyingSet R,
            hammingDist x u ≤ C₁ * rStar →
            hammingDist x z ≤ C₁ * rStar →
            ((threeWayDisagree x u z).card : ℝ) ≤ η₀ * (rStar : ℝ)) →
          let L_X : ↥X → ↥X → Finset ↥X := fun a b =>
            if 0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar then
              Finset.univ.filter (fun x : ↥X => x.val ∈ bicliqueWitnessList R C₁ rStar a.val b.val)
            else ∅
          ListHitCond C₁ rStar X L_X) :
    ∃ M_L : ℝ, 0 < M_L ∧
      ∀ C₁ : ℕ, 3 ≤ C₁ →
        ∃ (L q K R₀ : ℕ) (μ₀ : ℝ),
          2 ≤ L ∧ (L : ℝ) ≤ M_L * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) ∧
          2 ≤ q ∧ K = 20 * C₁ ^ 2 ∧ 160 * C₁ < R₀ ∧ 0 < μ₀ ∧
          let c : ℝ := (2 : ℝ) ^ (-((2 * L + 5 : ℕ) : ℝ))
          ∀ rStar : ℕ, R₀ ≤ rStar →
            let N : ℕ := 2 ^ L * rStar
            ∃ (X : Finset (Fin N → Fin q)) (L_X : ↥X → ↥X → Finset ↥X),
              2 ≤ X.card ∧
              (2 : ℝ) / 5 * μ₀ * (rStar : ℝ) ≤ Real.logb 2 (X.card : ℝ) ∧
              Real.logb 2 (X.card : ℝ) ≤ (3 : ℝ) / 2 * μ₀ * (rStar : ℝ) ∧
              (1 : ℝ) / 192 * (X.card : ℝ) ^ (1 + c) ≤ ((exactDistPairs X rStar).card : ℝ) ∧
              (∀ x ∈ X, ∀ y ∈ X, x ≠ y → (rStar : ℝ) / 2 ≤ (hammingDist x y : ℝ)) ∧
              ListSizeCond C₁ rStar K X L_X ∧
              OverlapCond C₁ rStar K X ∧
              ListHitCond C₁ rStar X L_X := by
  refine ⟨(2000000 : ℝ), by norm_num, ?_⟩
  intro C₁ hC₁
  have hL_ge2 : 2 ≤ cspL C₁ :=
    Nat.le_trans (by decide : 2 ≤ 20) (Nat.le_add_right 20 _)
  have hlam_info := lam0_ge_1000_C1 C₁ hC₁
  have hL_le : (cspL C₁ : ℝ) ≤ (2000000 : ℝ) * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) :=
    hlam_info.2.2
  have hq_ge2 : 2 ≤ cspQ C₁ := by
    unfold cspQ
    exact Nat.succ_le_succ Nat.one_le_two_pow
  have hlam0_1000 : 1000 * C₁ ≤ cspLam0 C₁ := hlam_info.2.1
  have hlam0_ge : 1000 ≤ cspLam0 C₁ := by omega
  have hbeta0_ge : 6000 ≤ cspBeta0 C₁ := by unfold cspBeta0; omega
  have hbeta0_pos_real : (0 : ℝ) < (cspBeta0 C₁ : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < 6000) hbeta0_ge)
  have hμ₀_pos : 0 < (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) :=
    mul_pos hbeta0_pos_real (pow_pos (by norm_num) _)
  have hR0 : 160 * C₁ < 1000 * C₁ + 1 := by omega
  have hdHam_eq : ∀ {M p : ℕ} (x y : Fin M → Fin p), dHam x y = hammingDist x y := fun _ _ => rfl
  have hexact_eq : ∀ {M p : ℕ} (S : Finset (Fin M → Fin p)) (r : ℕ),
      (S ×ˢ S).filter (fun xy => dHam xy.1 xy.2 = r) = exactDistPairs S r := fun _ _ => rfl
  refine ⟨cspL C₁, cspQ C₁, cspKMom C₁, 1000 * C₁ + 1,
    (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁),
    hL_ge2, hL_le, hq_ge2, rfl, hR0, hμ₀_pos, ?_⟩
  intro c rStar hrStar
  have hr : 1000 * C₁ < rStar := Nat.lt_of_lt_of_le (Nat.lt_succ_self (1000 * C₁)) hrStar
  have hr_ge1 : 1 ≤ rStar := Nat.le_trans (Nat.le_add_left 1 (1000 * C₁)) hrStar
  have hN_ge2_val : 2 ≤ 2 ^ cspL C₁ * rStar := by
    have h2L : 4 ≤ 2 ^ cspL C₁ := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ cspL C₁ := Nat.pow_le_pow_right (by norm_num) hL_ge2
    nlinarith only [h2L, hr_ge1]
  intro N
  obtain ⟨R, X, hSym, hSub, ⟨hCard_low, hCard_up⟩, hDense, hD3, hCh, hCand, hDist⟩ :=
    complete_graph_2csp_expurgated_existence C₁ hC₁ rStar hr
  let L_X : ↥X → ↥X → Finset ↥X := fun a b =>
    if 0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar then
      Finset.univ.filter (fun x : ↥X => x.val ∈ bicliqueWitnessList R C₁ rStar a.val b.val)
    else ∅
  have h22L_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * cspL C₁) := by
    exact_mod_cast (Nat.one_le_two_pow (n := 2 * cspL C₁))
  have hμ₀_ge : (6000 : ℝ) ≤ (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) := by
    have hbeta_r : (6000 : ℝ) ≤ (cspBeta0 C₁ : ℝ) := by exact_mod_cast hbeta0_ge
    nlinarith only [hbeta_r, h22L_ge1]
  have hr_real_ge1 : (1 : ℝ) ≤ (rStar : ℝ) := by exact_mod_cast hr_ge1
  have hX_ge2 : 2 ≤ X.card := by
    have hexp : (1 : ℝ) ≤ (98 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (rStar
      : ℝ) := by
      have hμr : (6000 : ℝ) ≤ ((cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁)) * (rStar : ℝ) := by
        nlinarith only [hμ₀_ge, hr_real_ge1]
      linarith
    have h2 : (2 : ℝ) ≤ (X.card : ℝ) := by
      calc
        (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
        _ ≤ (2 : ℝ) ^ ((98 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (rStar :
          ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ ≤ (X.card : ℝ) := hCard_low
    exact_mod_cast h2
  have hX_pos : (0 : ℝ) < (X.card : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_two hX_ge2)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogb_pow : ∀ z : ℝ, Real.logb 2 ((2 : ℝ) ^ z) = z := by
    intro z
    unfold Real.logb
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2), mul_div_cancel_right₀ _ (ne_of_gt hlog2_pos)]
  have hlogb_mono : ∀ x y : ℝ, 0 < x → x ≤ y → Real.logb 2 x ≤ Real.logb 2 y := by
    intro x y hx hxy
    unfold Real.logb
    exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy) (le_of_lt hlog2_pos)
  refine ⟨X, L_X, hX_ge2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := hlogb_mono _ (X.card : ℝ) (Real.rpow_pos_of_pos (by norm_num) _) hCard_low
    rw [hlogb_pow] at h1
    have hμr_nn : 0 ≤ (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (rStar : ℝ) :=
      mul_nonneg (le_of_lt hμ₀_pos) (Nat.cast_nonneg _)
    linarith
  · have h1 := hlogb_mono (X.card : ℝ) _ hX_pos hCard_up
    rw [hlogb_pow] at h1
    have hμr_nn : 0 ≤ (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (rStar : ℝ) :=
      mul_nonneg (le_of_lt hμ₀_pos) (Nat.cast_nonneg _)
    linarith
  · have hc_nn : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
    have hpow_c : (X.card : ℝ) ^ c ≤ (2 : ℝ) ^ ((1 / 5 : ℝ) * (cspLam0 C₁ : ℝ) * (rStar : ℝ)) := by
      have h1 : (X.card : ℝ) ^ c ≤
          ((2 : ℝ) ^ ((102 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (rStar :
            ℝ))) ^ c :=
        Real.rpow_le_rpow (le_of_lt hX_pos) hCard_up hc_nn
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at h1
      have h2Lc : (2 : ℝ) ^ (2 * cspL C₁) * c = 1 / 32 := by
        dsimp [c]
        rw [← Real.rpow_natCast (2 : ℝ) (2 * cspL C₁), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        have hexp : ((2 * cspL C₁ : ℕ) : ℝ) + (-((2 * cspL C₁ + 5 : ℕ) : ℝ)) = - (5 : ℝ) := by
          push_cast
          ring
        rw [hexp]
        norm_num
      have hbeta_eq : (cspBeta0 C₁ : ℝ) = 6 * (cspLam0 C₁ : ℝ) := by
        unfold cspBeta0; push_cast; ring
      have hexp_le : ((102 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (rStar :
        ℝ)) * c ≤
          (1 / 5 : ℝ) * (cspLam0 C₁ : ℝ) * (rStar : ℝ) := by
        have hrew : ((102 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (rStar :
          ℝ)) * c =
            (102 / 100 : ℝ) * 6 * ((2 : ℝ) ^ (2 * cspL C₁) * c) * ((cspLam0 C₁ : ℝ) * (rStar :
              ℝ)) := by
          rw [hbeta_eq]; ring
        rw [hrew, h2Lc]
        have hlr_nn : 0 ≤ (cspLam0 C₁ : ℝ) * (rStar : ℝ) :=
          mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        linarith
      exact le_trans h1 (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le)
    have h1c : (X.card : ℝ) ^ (1 + c) = (X.card : ℝ) ^ c * (X.card : ℝ) := by
      rw [Real.rpow_add hX_pos, Real.rpow_one, mul_comm]
    have hm := mul_le_mul_of_nonneg_right hpow_c (le_of_lt hX_pos)
    rw [hexact_eq X rStar] at hDense
    have htot : (X.card : ℝ) ^ (1 + c) ≤ 192 * ((exactDistPairs X rStar).card : ℝ) := by
      rw [h1c]
      exact le_trans hm hDense
    linarith
  · intro x hx y hy hne
    have hd := hDist x hx y hy hne
    rw [hdHam_eq] at hd
    have hd_r : (rStar : ℝ) ≤ 2 * (hammingDist x y : ℝ) := by exact_mod_cast hd
    linarith
  · intro a b hpos hle
    dsimp [L_X]
    rw [ite_eq_left ⟨hpos, hle⟩]
    have hne : a.val ≠ b.val := by
      intro heq
      rw [heq, hammingDist_self] at hpos
      exact (lt_irrefl 0 hpos).elim
    have hcard_le : (Finset.univ.filter (fun x : ↥X =>
        x.val ∈ bicliqueWitnessList R C₁ rStar a.val b.val)).card ≤
        (X.filter (fun x => x ∈ bicliqueWitnessList R C₁ rStar a.val b.val)).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact ⟨x.prop, hx⟩
      · intro x₁ _ x₂ _ heq
        exact Subtype.ext heq
    exact lt_of_le_of_lt hcard_le (hCand a.val a.prop b.val b.prop hne hle)
  · intro x w₀ hpos hle
    have hne : x.val ≠ w₀.val := by
      intro heq
      rw [heq, hammingDist_self] at hpos
      exact (lt_irrefl 0 hpos).elim
    have hcard_le : (Finset.univ.filter (fun y : ↥X =>
        y ≠ x ∧ y ≠ w₀ ∧
        hammingDist x.val y.val = rStar ∧
        (rStar : ℝ) / 4 < ((disagreeSet x.val w₀.val ∩ disagreeSet x.val y.val).card : ℝ))).card ≤
      (X.filter (fun y =>
        y ≠ x.val ∧ y ≠ w₀.val ∧ dHam x.val y = rStar ∧
        rStar < 4 * (disagreeSet x.val w₀.val ∩ disagreeSet x.val y).card)).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro y hy
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        have hlt_r : (rStar : ℝ) < 4 * ((disagreeSet x.val w₀.val ∩ disagreeSet x.val
          y.val).card : ℝ) := by
          linarith [hy.2.2.2]
        have hlt_nat : rStar < 4 * (disagreeSet x.val w₀.val ∩ disagreeSet x.val y.val).card := by
          exact_mod_cast hlt_r
        exact ⟨y.prop, fun h => hy.1 (Subtype.ext h), fun h => hy.2.1 (Subtype.ext h),
          hy.2.2.1, hlt_nat⟩
      · intro y₁ _ y₂ _ heq
        exact Subtype.ext heq
    exact lt_of_le_of_lt hcard_le (hCh x.val x.prop w₀.val w₀.prop hne hle)
  · apply h_6_3 N (cspQ C₁) C₁ rStar hN_ge2_val hq_ge2 hC₁ hr_ge1 R hSym X hSub
    intro x hx u hu z hz hdu hdz
    have hd3 := hD3 x hx u hu z hz hdu hdz
    have hd3_r : ((cspInvEta0 C₁ : ℝ)) * ((threeWayDisagree x u z).card : ℝ) ≤ (rStar : ℝ) := by
      exact_mod_cast hd3
    have hinv_eq : (cspInvEta0 C₁ : ℝ) = 80 := by
      unfold cspInvEta0
      norm_num
    rw [hinv_eq] at hd3_r
    change ((threeWayDisagree x u z).card : ℝ) ≤ (1 / 80 : ℝ) * (rStar : ℝ)
    linarith only [hd3_r]

end HighDimSteinerSpanners.Proofs.CSP
