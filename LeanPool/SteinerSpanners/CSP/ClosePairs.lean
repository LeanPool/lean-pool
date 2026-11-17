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

public import LeanPool.SteinerSpanners.CSP.EdgeMoments

/-! # Close Pairs for spanner CSP codes

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib.
-/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners.Proofs.CSP

noncomputable section Helpers

open Classical in
private lemma closePairs_h_sphere_sum :
    ∀ (r_star N q : ℕ) (p_edge p_keep n_0 : ℝ) (d_omega : ℕ → ℝ),
      (∀ (s : ℕ),
          d_omega s = (↑(N.choose s) : ℝ) * (↑(q - (1 : ℕ)) : ℝ) ^ s * p_edge ^ (s * (N - (1 :
              ℕ)) - s.choose (2 : ℕ))) →
        n_0 = p_keep * (↑q : ℝ) ^ N * p_edge ^ N.choose (2 : ℕ) →
          (∀ (x y : Fin N → Fin q),
              (homQueries x ∪ homQueries y).card =
                N.choose (2 : ℕ) + dHam x y * (N - (1 : ℕ)) - (dHam x y).choose (2 : ℕ)) →
            (∀ s ≤ r_star / (2 : ℕ), s.choose (2 : ℕ) ≤ s * (N - (1 : ℕ))) →
                let PairSphere : ℕ → Finset ((Fin N → Fin q) × (Fin N → Fin q)) := fun (s : ℕ) =>
                  {xy : (Fin N → Fin q) × (Fin N → Fin q) | dHam xy.1 xy.2 = s};
                ∀ s ≤ r_star / (2 : ℕ),
                  ∑ xy ∈ PairSphere s, p_keep ^ (2 : ℕ) * p_edge ^ (homQueries xy.1 ∪ homQueries
                      xy.2).card =
                    n_0 * p_keep * d_omega s := by
  classical
  intro r_star N q p_edge p_keep n_0 d_omega hdomega_def hn0_def h_uc
      hs_choose_le PairSphere s hs
  exact weightedHammingSphere_sum s (hs_choose_le s hs) p_edge p_keep n_0
    (d_omega s) (hdomega_def s) hn0_def h_uc

open Classical in
private lemma closePairs_hterm_le :
    ∀ (r_star : ℕ),
      (3001 : ℕ) ≤ r_star →
        ∀ (N q lam0 beta0 gamma0 : ℕ) (sigma_edge p_edge p_keep n_0 : ℝ) (d_omega : ℕ → ℝ),
          (1000 : ℕ) ≤ lam0 →
            r_star < N →
              (0 : ℝ) < sigma_edge →
                (0 : ℝ) < p_edge →
                  sigma_edge * (↑r_star : ℝ) / (2 : ℝ) ≤ (10001 / 10000 : ℝ) * (↑beta0 : ℝ) →
                    (∀ (s : ℕ),
                        d_omega s =
                          (↑(N.choose s) : ℝ) * (↑(q - (1 : ℕ)) : ℝ) ^ s *
                            p_edge ^ (s * (N - (1 : ℕ)) - s.choose (2 : ℕ))) →
                      (∀ s ≤ N,
                          d_omega s ≤
                            (2 : ℝ) ^
                              ((2 : ℝ) * (↑r_star : ℝ) - (↑gamma0 : ℝ) * (↑s : ℝ) +
                                sigma_edge * (↑(s.choose (2 : ℕ)) : ℝ))) →
                        p_keep ≤ (2 : ℝ) ^ (-(747 / 1000 : ℝ) * (↑lam0 : ℝ) * (↑r_star : ℝ)) →
                          (0 : ℝ) < n_0 →
                              (1000 : ℝ) ≤ (↑lam0 : ℝ) →
                                (↑beta0 : ℝ) = (6 : ℝ) * (↑lam0 : ℝ) →
                                  (↑gamma0 : ℝ) = (5 : ℝ) * (↑lam0 : ℝ) →
                                    (∀ (s : ℕ), (2 : ℕ) * s.choose (2 : ℕ) = s * (s - (1 : ℕ))) →
                                      let PairSphere : ℕ → Finset ((Fin N → Fin q) × (Fin N →
                                          Fin q)) := fun (s : ℕ) =>
                                        {xy : (Fin N → Fin q) × (Fin N → Fin q) | dHam xy.1 xy.2
                                            = s};
                                      (∀ s ≤ r_star / (2 : ℕ),
                                          ∑ xy ∈ PairSphere s,
                                              p_keep ^ (2 : ℕ) * p_edge ^ (homQueries xy.1 ∪
                                                  homQueries xy.2).card =
                                            n_0 * p_keep * d_omega s) →
                                        let B_close : ℝ := n_0 * (2 : ℝ) ^ (-(74 / 100 : ℝ) *
                                            (↑lam0 : ℝ) * (↑r_star : ℝ));
                                        ∀ s ∈ Finset.Icc (1 : ℕ) (r_star / (2 : ℕ)),
                                          ∑ xy ∈ PairSphere s,
                                              p_keep ^ (2 : ℕ) * p_edge ^ (homQueries xy.1 ∪
                                                  homQueries xy.2).card ≤
                                            B_close := by
  classical
  intro r_star hr_ge N q lam0 beta0 gamma0 sigma_edge p_edge p_keep n_0 d_omega hlam0_ge hN_gt_r
      hσ0 hp_edge0 hσ_up0 hdomega_def hDOm_s0 hp_keep_up0 hn0_pos0 hlam0_real hbeta_real
          hgam_real h_choose2_nat PairSphere h_sphere_sum B_close s hs
  rw [Finset.mem_Icc] at hs
  rw [h_sphere_sum s hs.2]
  have hsN : s ≤ N := by omega
  have hDOm_nn : 0 ≤ d_omega s := by
    rw [hdomega_def s]
    positivity
  have hsc2_le : (s.choose 2 : ℝ) ≤ (r_star : ℝ) * (s : ℝ) / 4 := by
    have hnat : 4 * s.choose 2 ≤ r_star * s := by
      have h2s : 2 * s ≤ r_star := by omega
      calc 4 * s.choose 2 = 2 * (2 * s.choose 2) := by ring
        _ = 2 * (s * (s - 1)) := by rw [h_choose2_nat s]
        _ ≤ 2 * (s * s) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left s (Nat.sub_le s 1))
        _ = (2 * s) * s := by ring
        _ ≤ r_star * s := Nat.mul_le_mul_right s h2s
    have hreal : (4 : ℝ) * (s.choose 2 : ℝ) ≤ (r_star : ℝ) * (s : ℝ) := by exact_mod_cast hnat
    linarith
  have hsig_sc2 : sigma_edge * (s.choose 2 : ℝ) ≤ (gamma0 : ℝ) * (s : ℝ) := by
    have hm1 : sigma_edge * (s.choose 2 : ℝ) ≤ sigma_edge * ((r_star : ℝ) * (s : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left hsc2_le (le_of_lt hσ0)
    have hm2 : (sigma_edge * (r_star : ℝ) / 2) * ((s : ℝ) / 2) ≤
        ((10001 / 10000 : ℝ) * (beta0 : ℝ)) * ((s : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hσ_up0 (by positivity)
    have hprod_nn : (0 : ℝ) ≤ (lam0 : ℝ) * (s : ℝ) := by positivity
    rw [hbeta_real] at hm2
    rw [hgam_real]
    linarith
  have hpDOm : p_keep * d_omega s ≤
      (2 : ℝ) ^ (- (74 / 100 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) := by
    have hm := mul_le_mul hp_keep_up0 (hDOm_s0 s hsN) hDOm_nn (by positivity)
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at hm
    have hexp : - (747 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) +
        (2 * (r_star : ℝ) - (gamma0 : ℝ) * (s : ℝ) + sigma_edge * (s.choose 2 : ℝ)) ≤
        - (74 / 100 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by
      have h2r_le : 2 * (r_star : ℝ) ≤ (2 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by
        have hscaled := mul_le_mul_of_nonneg_right hlam0_real (Nat.cast_nonneg r_star)
        nlinarith only [hscaled]
      have hprod_nn : (0 : ℝ) ≤ (lam0 : ℝ) * (r_star : ℝ) := by positivity
      linarith only [hsig_sc2, h2r_le, hprod_nn]
    exact le_trans hm (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
  dsimp [B_close]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hpDOm (le_of_lt hn0_pos0)

private lemma closePair_core (r_star : ℕ) (hr_ge : 3001 ≤ r_star) : ∀ (N q lam0 beta0 gamma0 : ℕ)
      (sigma_edge p_edge p_keep n_0 delta_bad : ℝ) (d_omega : ℕ → ℝ),
      1000 ≤ lam0 →
      beta0 = 6 * lam0 →
      gamma0 = 5 * lam0 →
      r_star < N →
      0 < sigma_edge →
      0 < p_edge →
      sigma_edge * (r_star : ℝ) / 2 ≤ (10001 / 10000 : ℝ) * (beta0 : ℝ) →
      (∀ s : ℕ, d_omega s = (N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s *
        p_edge ^ (s * (N - 1) - s.choose 2)) →
      (∀ s : ℕ, s ≤ N →
        d_omega s ≤ (2 : ℝ) ^ (2 * (r_star : ℝ) - (gamma0 : ℝ) * (s : ℝ) +
          sigma_edge * (s.choose 2 : ℝ))) →
      0 < p_keep →
      p_keep ≤ (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) →
      n_0 = p_keep * ((q : ℝ) ^ N) * p_edge ^ (N.choose 2) →
      0 < n_0 →
      delta_bad = (2 : ℝ) ^ (- (6 / 10 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) →
      (∀ x y : Fin N → Fin q,
        (homQueries x ∪ homQueries y).card =
          N.choose 2 + dHam x y * (N - 1) - (dHam x y).choose 2) →
      ∑ ab ∈ Finset.univ.filter
          (fun ab : (Fin N → Fin q) × (Fin N → Fin q) =>
            ab.1 ≠ ab.2 ∧ 2 * dHam ab.1 ab.2 < r_star),
        p_keep ^ 2 * p_edge ^ (homQueries ab.1 ∪ homQueries ab.2).card ≤
        (1 / 4 : ℝ) * delta_bad * n_0 := by
  intro N q lam0 beta0 gamma0 sigma_edge p_edge p_keep n_0 delta_bad d_omega
    hlam0_ge hbeta_eq hgam_eq hN_gt_r hσ0 hp_edge0 hσ_up0 hdomega_def hDOm_s0
    hp_keep0 hp_keep_up0 hn0_def hn0_pos0 hdelta_def h_uc
  have hr_real : (3001 : ℝ) ≤ (r_star : ℝ) := by exact_mod_cast hr_ge
  have hr_pos : (0 : ℝ) < (r_star : ℝ) := by linarith
  have hlam0_real : (1000 : ℝ) ≤ (lam0 : ℝ) := by exact_mod_cast hlam0_ge
  have hbeta_real : (beta0 : ℝ) = 6 * (lam0 : ℝ) := by rw [hbeta_eq]; push_cast; ring
  have hgam_real : (gamma0 : ℝ) = 5 * (lam0 : ℝ) := by rw [hgam_eq]; push_cast; ring
  have h_choose2_nat : ∀ s : ℕ, 2 * s.choose 2 = s * (s - 1) := by
    intro s
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self s).two_dvd]
  have hs_choose_le : ∀ s : ℕ, s ≤ r_star / 2 → s.choose 2 ≤ s * (N - 1) := by
    intro s hs
    have hs1 : s - 1 ≤ 2 * (N - 1) := by omega
    have h2 : 2 * s.choose 2 ≤ 2 * (s * (N - 1)) := by
      rw [h_choose2_nat s]
      calc s * (s - 1) ≤ s * (2 * (N - 1)) := Nat.mul_le_mul_left s hs1
        _ = 2 * (s * (N - 1)) := by ring
    omega
  let PairSphere : ℕ → Finset ((Fin N → Fin q) × (Fin N → Fin q)) :=
    fun s => Finset.univ.filter (fun xy => dHam xy.1 xy.2 = s)
  have h_sphere_sum : ∀ s : ℕ, s ≤ r_star / 2 →
      ∑ xy ∈ PairSphere s,
        p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card =
        n_0 * p_keep * d_omega s :=
    @closePairs_h_sphere_sum r_star N q p_edge p_keep n_0 d_omega hdomega_def hn0_def h_uc
      hs_choose_le
  have hne_iff : ∀ a b : Fin N → Fin q, a ≠ b ↔ 1 ≤ dHam a b := by
    intro a b
    constructor
    · intro hne
      obtain ⟨v, hv⟩ := Function.ne_iff.mp hne
      exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩
    · intro h1 heq
      subst heq
      have h0 : dHam a a = 0 := by simp [dHam, disagreeSet]
      omega
  have hsub_close : Finset.univ.filter
      (fun ab : (Fin N → Fin q) × (Fin N → Fin q) =>
        ab.1 ≠ ab.2 ∧ 2 * dHam ab.1 ab.2 < r_star) ⊆
      (Finset.Icc 1 (r_star / 2)).biUnion PairSphere := by
    intro ab hab
    simp only [PairSphere, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_Icc, hne_iff] at hab ⊢
    exact ⟨dHam ab.1 ab.2, ⟨hab.1, by omega⟩, rfl⟩
  have hdisj : ((Finset.Icc 1 (r_star / 2) : Finset ℕ) : Set ℕ).PairwiseDisjoint PairSphere := by
    intro s₁ _ s₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro ab h₁ h₂
    simp only [PairSphere, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact hne (h₁.symm.trans h₂)
  have hle_bi : ∑ ab ∈ Finset.univ.filter
      (fun ab : (Fin N → Fin q) × (Fin N → Fin q) =>
        ab.1 ≠ ab.2 ∧ 2 * dHam ab.1 ab.2 < r_star),
      p_keep ^ 2 * p_edge ^ (homQueries ab.1 ∪ homQueries ab.2).card ≤
    ∑ s ∈ Finset.Icc 1 (r_star / 2), ∑ xy ∈ PairSphere s,
      p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card := by
    rw [← Finset.sum_biUnion hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub_close (fun _ _ _ => by positivity)
  let B_close : ℝ := n_0 * (2 : ℝ) ^ (- (74 / 100 : ℝ) * (lam0 : ℝ) * (r_star : ℝ))
  have hterm_le : ∀ s ∈ Finset.Icc 1 (r_star / 2),
      ∑ xy ∈ PairSphere s,
        p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card ≤ B_close :=
    @closePairs_hterm_le r_star hr_ge N q lam0 beta0 gamma0 sigma_edge p_edge p_keep n_0 d_omega
        hlam0_ge hN_gt_r hσ0 hp_edge0 hσ_up0 hdomega_def hDOm_s0 hp_keep_up0 hn0_pos0
            hlam0_real hbeta_real hgam_real h_choose2_nat h_sphere_sum
  have hsum_le1 : ∑ s ∈ Finset.Icc 1 (r_star / 2), ∑ xy ∈ PairSphere s,
      p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card ≤
      ((Finset.Icc 1 (r_star / 2)).card : ℝ) * B_close := by
    calc
      ∑ s ∈ Finset.Icc 1 (r_star / 2), _
        ≤ ∑ _s ∈ Finset.Icc 1 (r_star / 2), B_close := Finset.sum_le_sum hterm_le
      _ = ((Finset.Icc 1 (r_star / 2)).card : ℝ) * B_close := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_le : ((Finset.Icc 1 (r_star / 2)).card : ℝ) ≤ (2 : ℝ) ^ (r_star : ℝ) := by
    have hc_nat : (Finset.Icc 1 (r_star / 2)).card ≤ 2 ^ r_star := by
      have hc1 : (Finset.Icc 1 (r_star / 2)).card ≤ r_star := by
        rw [Nat.card_Icc]; omega
      exact le_trans hc1 (le_of_lt Nat.lt_two_pow_self)
    have hcast : ((Finset.Icc 1 (r_star / 2)).card : ℝ) ≤ ((2 ^ r_star : ℕ) : ℝ) := by
      exact_mod_cast hc_nat
    rwa [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast] at hcast
  have hB_nn : 0 ≤ B_close := by dsimp [B_close]; positivity
  have hsum_le2 : ((Finset.Icc 1 (r_star / 2)).card : ℝ) * B_close ≤
      (1 / 4 : ℝ) * delta_bad * n_0 := by
    have hm := mul_le_mul_of_nonneg_right hcard_le hB_nn
    dsimp [B_close] at hm
    have hrew : (2 : ℝ) ^ (r_star : ℝ) *
        (n_0 * (2 : ℝ) ^ (- (74 / 100 : ℝ) * (lam0 : ℝ) * (r_star : ℝ))) =
        n_0 * (2 : ℝ) ^ ((r_star : ℝ) + (- (74 / 100 : ℝ) * (lam0 : ℝ) * (r_star : ℝ))) := by
      rw [mul_left_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [hrew] at hm
    have htarget : (2 : ℝ) ^ ((r_star : ℝ) + (- (74 / 100 : ℝ) * (lam0 : ℝ) * (r_star : ℝ))) ≤
        (1 / 4 : ℝ) * delta_bad := by
      rw [hdelta_def]
      have hquarter : (1 / 4 : ℝ) = (2 : ℝ) ^ (- (2 : ℝ)) := by norm_num
      rw [hquarter, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h1r : (r_star : ℝ) ≤ (1 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by
        nlinarith only [hlam0_real, hr_pos]
      have hlam_r : (1000 : ℝ) ≤ (lam0 : ℝ) * (r_star : ℝ) := by
        nlinarith only [hlam0_real, hr_real]
      linarith only [h1r, hlam_r]
    have hm2 := mul_le_mul_of_nonneg_left htarget (le_of_lt hn0_pos0)
    have hrhs_eq : n_0 * ((1 / 4 : ℝ) * delta_bad) = (1 / 4 : ℝ) * delta_bad * n_0 := by ring
    rw [hrhs_eq] at hm2
    dsimp [B_close]
    exact le_trans hm hm2
  exact le_trans hle_bi (le_trans hsum_le1 hsum_le2)

theorem close_pair_query_sum_bound (C₁ : ℕ) (hC₁ : 3 ≤ C₁) (r_star : ℕ) (hr : 1000 * C₁ < r_star)
    (hσ_pos : 0 < cspSigmaEdge C₁ r_star)
    (hp_edge_pos : 0 < cspPEdge C₁ r_star)
    (hσ_up : cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 ≤ (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ))
    (hDOm_s : ∀ s : ℕ, s ≤ 2 ^ cspL C₁ * r_star →
      cspDOmega C₁ r_star s ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ) +
          cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ)))
    (hp_keep_pos : 0 < cspPKeep C₁ r_star)
    (hp_keep_up : cspPKeep C₁ r_star ≤
      (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))
    (hn0_pos : 0 < cspN0 C₁ r_star)
    (h_union_card : ∀ x y : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      (homQueries x ∪ homQueries y).card =
        (2 ^ cspL C₁ * r_star).choose 2 +
          dHam x y * (2 ^ cspL C₁ * r_star - 1) - (dHam x y).choose 2)
     :
    ∑ ab ∈ Finset.univ.filter
        (fun ab : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                  (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
          ab.1 ≠ ab.2 ∧ 2 * dHam ab.1 ab.2 < r_star),
      (cspPKeep C₁ r_star) ^ 2 *
        (cspPEdge C₁ r_star) ^ (homQueries ab.1 ∪ homQueries ab.2).card ≤
      (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
  have h_core := closePair_core r_star (by omega)
  have hlam0_1000 := (lam0_ge_1000_C1 C₁ hC₁).2.1
  have hlam0_ge : 1000 ≤ cspLam0 C₁ := by omega
  have hN_gt_r : r_star < 2 ^ cspL C₁ * r_star := by
    have hr_pos : 0 < r_star := by omega
    have hL_ge1 : 1 ≤ cspL C₁ := Nat.le_trans (by decide : 1 ≤ 20) (Nat.le_add_right 20 _)
    have h2L : 2 ≤ 2 ^ cspL C₁ := by
      simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hL_ge1
    calc
      r_star = 1 * r_star := (one_mul r_star).symm
      _ < 2 * r_star := Nat.mul_lt_mul_of_pos_right (by decide : 1 < 2) hr_pos
      _ ≤ 2 ^ cspL C₁ * r_star := Nat.mul_le_mul_right r_star h2L
  exact h_core
    (2 ^ cspL C₁ * r_star) (cspQ C₁) (cspLam0 C₁) (cspBeta0 C₁) (cspGamma0 C₁)
    (cspSigmaEdge C₁ r_star) (cspPEdge C₁ r_star) (cspPKeep C₁ r_star)
    (cspN0 C₁ r_star) (cspDeltaBad C₁ r_star) (cspDOmega C₁ r_star)
    hlam0_ge rfl rfl hN_gt_r hσ_pos hp_edge_pos hσ_up (fun _ => rfl) hDOm_s
    hp_keep_pos hp_keep_up rfl hn0_pos rfl h_union_card

end Helpers

end HighDimSteinerSpanners.Proofs.CSP
