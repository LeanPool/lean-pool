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

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

public import LeanPool.SteinerSpanners.CSP.Definitions

/-! # Calibration Bounds for spanner CSP codes

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib.
-/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners.Proofs.CSP

noncomputable section Helpers

lemma lam0_ge_1000_C1 (C₁ : ℕ) (hC₁ : 3 ≤ C₁) :
    2 ≤ Nat.clog 2 C₁ ∧ 1000 * C₁ ≤ cspLam0 C₁ ∧
    (cspL C₁ : ℝ) ≤ (2000000 : ℝ) * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) := by
  have hclog_ge2 : 2 ≤ Nat.clog 2 C₁ := by
    by_contra hlt
    have hle1 : Nat.clog 2 C₁ ≤ 1 := by omega
    have hC_le : C₁ ≤ 2 ^ 1 := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp hle1
    omega
  have hlam_ge : 1000 * C₁ ≤ cspLam0 C₁ := by
    unfold cspLam0
    have h10 : 10 ≤ 2 * Nat.clog 2 C₁ + 6 := by omega
    nlinarith
  refine ⟨hclog_ge2, hlam_ge, ?_⟩
  set t := Nat.clog 2 C₁
  have ht_pos : 1 ≤ t := by omega
  have hpow_lt : 2 ^ (t - 1) < C₁ := by
    by_contra hge
    push Not at hge
    have hle : Nat.clog 2 C₁ ≤ t - 1 :=
      (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr hge
    omega
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogb_mono : ∀ x y : ℝ, 0 < x → x ≤ y → Real.logb 2 x ≤ Real.logb 2 y := by
    intro x y hx hxy
    unfold Real.logb
    exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy) (le_of_lt hlog2_pos)
  have hlogb_pow : ∀ k : ℕ, Real.logb 2 ((2 : ℝ) ^ k) = (k : ℝ) := by
    intro k
    unfold Real.logb
    rw [Real.log_pow, mul_div_cancel_right₀ _ (ne_of_gt hlog2_pos)]
  have hC1_real_ge3 : (3 : ℝ) ≤ (C₁ : ℝ) := by exact_mod_cast hC₁
  have hlog_ge1 : 1 ≤ Real.logb 2 (C₁ : ℝ) := by
    have h := hlogb_mono 2 (C₁ : ℝ) (by norm_num) (by linarith)
    simpa [hlogb_pow 1] using h
  have ht1_le : ((t - 1 : ℕ) : ℝ) ≤ Real.logb 2 (C₁ : ℝ) := by
    have hle_real : ((2 : ℝ) ^ (t - 1)) ≤ (C₁ : ℝ) := by
      exact_mod_cast (le_of_lt hpow_lt)
    have h := hlogb_mono ((2 : ℝ) ^ (t - 1)) (C₁ : ℝ) (by positivity) hle_real
    rwa [hlogb_pow (t - 1)] at h
  have ht_le : (t : ℝ) ≤ 2 * Real.logb 2 (C₁ : ℝ) := by
    rw [Nat.cast_sub ht_pos, Nat.cast_one] at ht1_le
    linarith
  have h2t6_le : 2 * (t : ℝ) + 6 ≤ 10 * Real.logb 2 (C₁ : ℝ) := by linarith
  have hlam_real : (cspLam0 C₁ : ℝ) ≤ 1000 * (C₁ : ℝ) * Real.logb 2 (C₁ : ℝ) := by
    have heq : (cspLam0 C₁ : ℝ) = 100 * (C₁ : ℝ) * (2 * (t : ℝ) + 6) := by
      dsimp [cspLam0, t]
      push_cast
      ring
    rw [heq]
    have h100C : 0 ≤ 100 * (C₁ : ℝ) := by positivity
    have hm := mul_le_mul_of_nonneg_left h2t6_le h100C
    linarith
  have hL_eq : (cspL C₁ : ℝ) = 1600 * (C₁ : ℝ) ^ 2 * (cspLam0 C₁ : ℝ) + 20 := by
    unfold cspL cspInvEta0
    push_cast
    ring
  have hC3_ge27 : (27 : ℝ) ≤ (C₁ : ℝ) ^ 3 := by nlinarith
  have hC3log_ge27 : (27 : ℝ) ≤ (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) := by
    nlinarith
  have hm_L : 1600 * (C₁ : ℝ) ^ 2 * (cspLam0 C₁ : ℝ) ≤
      1600000 * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hlam_real (by positivity : (0 : ℝ) ≤ 1600 * (C₁ : ℝ) ^ 2)
    linarith [hm,
      show 1600 * (C₁ : ℝ) ^ 2 * (1000 * (C₁ : ℝ) * Real.logb 2 (C₁ : ℝ)) =
        1600000 * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) by ring]
  linarith

lemma choose_bound_exp4 (U S m_sz r B : ℕ) (hB : 1 ≤ B) (hU : U ≤ B * r) (hS : S ≤ m_sz) :
    (U.choose S : ℝ) ≤ (B : ℝ) ^ m_sz * (4 : ℝ) ^ r := by
  have hexp4 : Real.exp (r : ℝ) ≤ (4 : ℝ) ^ r := by
    have h1 : Real.exp (r : ℝ) = (Real.exp 1) ^ r := by simp
    have he4 : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
    rw [h1]
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he4 r
  have h1 : (U.choose S : ℝ) ≤ (U : ℝ) ^ S / (S.factorial : ℝ) := Nat.choose_le_pow_div S U
  have hU_r : (U : ℝ) ≤ (B : ℝ) * (r : ℝ) := by exact_mod_cast hU
  have h2 : (U : ℝ) ^ S / (S.factorial : ℝ) ≤
      ((B : ℝ) * (r : ℝ)) ^ S / (S.factorial : ℝ) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg U) hU_r S) (Nat.cast_nonneg _)
  have h3 : ((B : ℝ) * (r : ℝ)) ^ S / (S.factorial : ℝ) =
      (B : ℝ) ^ S * ((r : ℝ) ^ S / (S.factorial : ℝ)) := by
    rw [mul_pow, mul_div_assoc]
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBs : (B : ℝ) ^ S ≤ (B : ℝ) ^ m_sz := pow_le_pow_right₀ hB1 hS
  have hrs : (r : ℝ) ^ S / (S.factorial : ℝ) ≤ (4 : ℝ) ^ r :=
    le_trans (Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg r) S) hexp4
  have h4 : (B : ℝ) ^ S * ((r : ℝ) ^ S / (S.factorial : ℝ)) ≤ (B : ℝ) ^ m_sz * (4 : ℝ) ^ r :=
    mul_le_mul hBs hrs (by positivity) (by positivity)
  linarith

lemma powerset_card_le_bound {α : Type*} (R_set : Finset α)
    (C₁ A b : ℕ) (hC₁ : 3 ≤ C₁) (hA : A ≤ 21) (hcard : R_set.card ≤ A * C₁ ^ 2 * b) :
    ((R_set.powerset.filter (fun G => G.card ≤ b)).card : ℝ) ≤
      ((b + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * b : ℕ) : ℝ) := by
  classical
  let M : ℕ := 21 * C₁ ^ 2 * b
  have hR_le_M : R_set.card ≤ M := by
    have hAC : A * C₁ ^ 2 ≤ 21 * C₁ ^ 2 := Nat.mul_le_mul_right _ hA
    exact le_trans hcard (Nat.mul_le_mul_right b hAC)
  have h2b_le_M : 2 * b ≤ M := by
    dsimp [M]
    have hC2 : 9 ≤ C₁ ^ 2 := by nlinarith
    nlinarith
  have hchoose_mono : ∀ (N0 t0 b0 : ℕ), 2 * b0 ≤ N0 → t0 ≤ b0 → N0.choose t0 ≤ N0.choose b0 := by
    intro N0 t0 b0 h2b htb
    have hstep : ∀ k : ℕ, 2 * (k + 1) ≤ N0 → N0.choose k ≤ N0.choose (k + 1) := by
      intro k hk
      have hid := (Nat.choose_succ_right_eq N0 k).symm
      have hkle : k + 1 ≤ N0 - k := by omega
      have hmul : N0.choose k * (k + 1) ≤ N0.choose (k + 1) * (k + 1) := by
        calc
          N0.choose k * (k + 1) ≤ N0.choose k * (N0 - k) := Nat.mul_le_mul_left _ hkle
          _ = N0.choose (k + 1) * (k + 1) := hid
      exact Nat.le_of_mul_le_mul_right hmul (by omega)
    have hm : ∀ x : ℕ, t0 ≤ x → 2 * x ≤ N0 → N0.choose t0 ≤ N0.choose x :=
      Nat.le_induction (fun _ => le_refl _) (fun k _ ih hk1 =>
        le_trans (ih (by omega)) (hstep k hk1))
    exact hm b0 htb h2b
  have hMb_le : (M.choose b : ℝ) ≤ (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * b : ℕ) : ℝ) := by
    have h1 : (M.choose b : ℝ) ≤ (M : ℝ) ^ b / (b.factorial : ℝ) := Nat.choose_le_pow_div b M
    have hM_cast : (M : ℝ) = (21 * (C₁ : ℝ) ^ 2) * (b : ℝ) := by dsimp [M]; push_cast; ring
    have h2 : (M : ℝ) ^ b / (b.factorial : ℝ) =
        (21 * (C₁ : ℝ) ^ 2) ^ b * ((b : ℝ) ^ b / (b.factorial : ℝ)) := by
      rw [hM_cast, mul_pow, mul_div_assoc]
    have hexp3 : (b : ℝ) ^ b / (b.factorial : ℝ) ≤ (3 : ℝ) ^ b := by
      have he : Real.exp (b : ℝ) ≤ (3 : ℝ) ^ b := by
        have heb : Real.exp (b : ℝ) = (Real.exp 1) ^ b := by simp
        have he3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
        rw [heb]
        exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he3 b
      exact le_trans (Real.pow_div_factorial_le_exp (b : ℝ) (Nat.cast_nonneg b) b) he
    have hC_pow : C₁ ≤ 2 ^ Nat.clog 2 C₁ := Nat.le_pow_clog (by decide : 1 < 2) C₁
    have hC_r : (C₁ : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 C₁ := by exact_mod_cast hC_pow
    have hbase : 63 * (C₁ : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * Nat.clog 2 C₁ + 6) := by
      calc
        63 * (C₁ : ℝ) ^ 2 ≤ 64 * ((2 : ℝ) ^ Nat.clog 2 C₁) ^ 2 := by
          have hsq : (C₁ : ℝ) ^ 2 ≤ ((2 : ℝ) ^ Nat.clog 2 C₁) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg C₁) hC_r 2
          nlinarith [show (0 : ℝ) ≤ ((2 : ℝ) ^ Nat.clog 2 C₁) ^ 2 by positivity]
        _ = (2 : ℝ) ^ (2 * Nat.clog 2 C₁ + 6) := by
          rw [show (64 : ℝ) = (2 : ℝ) ^ 6 by norm_num, ← pow_mul, ← pow_add]
          congr 1; omega
    have h12 : (M.choose b : ℝ) ≤ (21 * (C₁ : ℝ) ^ 2) ^ b * (3 : ℝ) ^ b := by
      calc
        (M.choose b : ℝ) ≤ (M : ℝ) ^ b / (b.factorial : ℝ) := h1
        _ = (21 * (C₁ : ℝ) ^ 2) ^ b * ((b : ℝ) ^ b / (b.factorial : ℝ)) := h2
        _ ≤ (21 * (C₁ : ℝ) ^ 2) ^ b * (3 : ℝ) ^ b :=
            mul_le_mul_of_nonneg_left hexp3 (by positivity)
    calc
      (M.choose b : ℝ) ≤ (21 * (C₁ : ℝ) ^ 2) ^ b * (3 : ℝ) ^ b := h12
      _ = (63 * (C₁ : ℝ) ^ 2) ^ b := by rw [← mul_pow]; congr 1; ring
      _ ≤ ((2 : ℝ) ^ (2 * Nat.clog 2 C₁ + 6)) ^ b := pow_le_pow_left₀ (by positivity) hbase b
      _ = (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * b : ℕ) : ℝ) := by
        rw [← pow_mul, ← Real.rpow_natCast]
  have hsub : R_set.powerset.filter (fun G => G.card ≤ b) ⊆
      (Finset.range (b + 1)).biUnion (fun t => R_set.powersetCard t) := by
    intro G hG
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard] at hG ⊢
    exact ⟨G.card, Nat.lt_succ_of_le hG.2, hG.1, rfl⟩
  have hcard_nat : (R_set.powerset.filter (fun G => G.card ≤ b)).card ≤ (b + 1) * M.choose b := by
    calc
      (R_set.powerset.filter (fun G => G.card ≤ b)).card
        ≤ ((Finset.range (b + 1)).biUnion (fun t => R_set.powersetCard t)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ t ∈ Finset.range (b + 1), (R_set.powersetCard t).card := Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ Finset.range (b + 1), M.choose b := by
          refine Finset.sum_le_sum (fun t ht => ?_)
          rw [Finset.card_powersetCard]
          exact le_trans (Nat.choose_le_choose t hR_le_M)
            (hchoose_mono M t b h2b_le_M (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)))
      _ = (b + 1) * M.choose b := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  calc
    ((R_set.powerset.filter (fun G => G.card ≤ b)).card : ℝ)
      ≤ ((b + 1 : ℕ) : ℝ) * (M.choose b : ℝ) := by exact_mod_cast hcard_nat
    _ ≤ ((b + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * b : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hMb_le (Nat.cast_nonneg _)

end Helpers

end HighDimSteinerSpanners.Proofs.CSP
