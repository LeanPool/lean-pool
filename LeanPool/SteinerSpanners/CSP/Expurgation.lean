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
import Mathlib.Algebra.BigOperators.Field

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Prod

public import LeanPool.SteinerSpanners.CSP.Bernoulli

/-! # Expurgation for spanner CSP codes

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib.
-/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners.Proofs.CSP

noncomputable section Helpers

open Classical in
private lemma expurgation_hGc_bound :
    ∀ {Ω V : Type} [Fintype Ω] (W : Ω → ℝ),
      (∀ (ω : Ω), 0 ≤ W ω) →
        ∑ ω : Ω, W ω = 1 →
          ∀ (Rel : V → V → Prop) [DecidableRel Rel] (P_raw : Ω → Finset V) (n_0 D_star : ℝ),
            0 < n_0 →
              0 < D_star →
                let E_set : Finset V → Finset (V × V) := fun (S : Finset V) => {xy ∈ S ×ˢ S |
                    Rel xy.1 xy.2};
                let Z : Ω → ℝ := fun (ω : Ω) => ↑(E_set (P_raw ω)).card;
                let M_0 : ℝ := n_0 * D_star;
                let p_good : Ω → Prop := fun (ω : Ω) => 1 / 2 * M_0 ≤ Z ω;
                let instDecNotGood : ∀ ω : Ω, Decidable (¬p_good ω) := fun _ => Classical.dec _;
                let Gc : Finset Ω := @Finset.filter Ω (fun ω => ¬p_good ω)
                  instDecNotGood Finset.univ;
                ∑ ω ∈ Gc, W ω * Z ω ≤ 1 / 2 * M_0 := by
  classical
  intro Ω V _ W hW_nn hW_sum Rel _ P_raw n_0 D_star hn0 hD E_set Z M_0 p_good instDecNotGood Gc
  have hpt : ∀ ω ∈ Gc, W ω * Z ω ≤ ((1 / 2 : ℝ) * M_0) * W ω := by
    intro ω hω
    have hnot : ¬ ((1 / 2 : ℝ) * M_0 ≤ Z ω) := (Finset.mem_filter.mp hω).2
    have hle : Z ω ≤ (1 / 2 : ℝ) * M_0 := le_of_not_ge hnot
    calc
      W ω * Z ω ≤ W ω * ((1 / 2 : ℝ) * M_0) := mul_le_mul_of_nonneg_left hle (hW_nn ω)
      _ = ((1 / 2 : ℝ) * M_0) * W ω := mul_comm _ _
  have hsum1 : ∑ ω ∈ Gc, W ω * Z ω ≤ ((1 / 2 : ℝ) * M_0) * ∑ ω ∈ Gc, W ω := by
    calc
      ∑ ω ∈ Gc, W ω * Z ω ≤ ∑ ω ∈ Gc, ((1 / 2 : ℝ) * M_0) * W ω := Finset.sum_le_sum hpt
      _ = ((1 / 2 : ℝ) * M_0) * ∑ ω ∈ Gc, W ω := (Finset.mul_sum Gc W ((1 / 2 : ℝ) * M_0)).symm
  have hsumW : ∑ ω ∈ Gc, W ω ≤ 1 := by
    calc
      ∑ ω ∈ Gc, W ω ≤ ∑ ω : Ω, W ω := Finset.sum_le_univ_sum_of_nonneg hW_nn
      _ = 1 := hW_sum
  have hhalf_nn : 0 ≤ (1 / 2 : ℝ) * M_0 := by positivity
  calc
    ∑ ω ∈ Gc, W ω * Z ω ≤ ((1 / 2 : ℝ) * M_0) * ∑ ω ∈ Gc, W ω := hsum1
    _ ≤ ((1 / 2 : ℝ) * M_0) * 1 := mul_le_mul_of_nonneg_left hsumW hhalf_nn
    _ = (1 / 2 : ℝ) * M_0 := mul_one _

open Classical in
private lemma expurgation_hCS_G :
    ∀ {Ω V : Type} [Fintype Ω] (W : Ω → ℝ),
      (∀ (ω : Ω), 0 ≤ W ω) →
        ∀ (Rel : V → V → Prop) [DecidableRel Rel] (P_raw : Ω → Finset V) (n_0 D_star : ℝ),
          let E_set : Finset V → Finset (V × V) := fun (S : Finset V) => {xy ∈ S ×ˢ S | Rel xy.1
              xy.2};
          let Z : Ω → ℝ := fun (ω : Ω) => ↑(E_set (P_raw ω)).card;
          let M_0 : ℝ := n_0 * D_star;
          let p_good : Ω → Prop := fun (ω : Ω) => 1 / 2 * M_0 ≤ Z ω;
          let instDecGood : DecidablePred p_good := Classical.decPred p_good;
          let G : Finset Ω := @Finset.filter Ω p_good instDecGood Finset.univ;
          (∑ ω ∈ G, W ω * Z ω) ^ 2 ≤ (∑ ω ∈ G, W ω) * ∑ ω ∈ G, W ω * Z ω ^ 2 := by
  classical
  intro Ω V _ W hW_nn Rel _ P_raw n_0 D_star E_set Z M_0 p_good instDecGood G
  have hraw := Finset.sum_mul_sq_le_sq_mul_sq G
    (fun ω => Real.sqrt (W ω)) (fun ω => Real.sqrt (W ω) * Z ω)
  have h1 : ∑ ω ∈ G, Real.sqrt (W ω) * (Real.sqrt (W ω) * Z ω) = ∑ ω ∈ G, W ω * Z ω := by
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [← mul_assoc, Real.mul_self_sqrt (hW_nn ω)]
  have h2 : ∑ ω ∈ G, (Real.sqrt (W ω)) ^ 2 = ∑ ω ∈ G, W ω := by
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    exact Real.sq_sqrt (hW_nn ω)
  have h3 : ∑ ω ∈ G, (Real.sqrt (W ω) * Z ω) ^ 2 = ∑ ω ∈ G, W ω * Z ω ^ 2 := by
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [mul_pow, Real.sq_sqrt (hW_nn ω)]
  rwa [h1, h2, h3] at hraw

open Classical in
private lemma expurgation_hPZ :
    ∀ {Ω V : Type} [Fintype Ω] (W : Ω → ℝ),
      (∀ (ω : Ω), 0 ≤ W ω) →
        ∀ (Rel : V → V → Prop) [DecidableRel Rel] (P_raw : Ω → Finset V) (n_0 D_star γ : ℝ),
          ∑ ω : Ω, W ω * ↑{xy ∈ P_raw ω ×ˢ P_raw ω | Rel xy.1 xy.2}.card ^ 2 ≤ 3 * γ * (n_0 *
              D_star) ^ 2 →
            let E_set : Finset V → Finset (V × V) := fun (S : Finset V) => {xy ∈ S ×ˢ S | Rel
                xy.1 xy.2};
            let Z : Ω → ℝ := fun (ω : Ω) => ↑(E_set (P_raw ω)).card;
            let M_0 : ℝ := n_0 * D_star;
            0 < M_0 →
              0 < M_0 ^ 2 →
                let p_good : Ω → Prop := fun (ω : Ω) => 1 / 2 * M_0 ≤ Z ω;
                let instDecGood : DecidablePred p_good := Classical.decPred p_good;
          let G : Finset Ω := @Finset.filter Ω p_good instDecGood Finset.univ;
                1 / 2 * M_0 ≤ ∑ ω ∈ G, W ω * Z ω →
                  (∑ ω ∈ G, W ω * Z ω) ^ 2 ≤ (∑ ω ∈ G, W ω) * ∑ ω ∈ G, W ω * Z ω ^ 2 → 1 ≤ ∑ ω ∈
                      G, W ω * (12 * γ) := by
  classical
  intro Ω V _ W hW_nn Rel _ P_raw n_0 D_star γ hE2 E_set Z M_0 hM0_pos hM0_sq_pos p_good
      instDecGood G hG_E1 hCS_G
  have hsq_low : (1 / 4 : ℝ) * M_0 ^ 2 ≤ (∑ ω ∈ G, W ω * Z ω) ^ 2 := by
    have hsq : ((1 / 2 : ℝ) * M_0) ^ 2 ≤ (∑ ω ∈ G, W ω * Z ω) ^ 2 := by
      nlinarith only [hG_E1, hM0_pos]
    linarith [hsq, show ((1 / 2 : ℝ) * M_0) ^ 2 = (1 / 4 : ℝ) * M_0 ^ 2 by ring]
  have hG_E2 : ∑ ω ∈ G, W ω * Z ω ^ 2 ≤ 3 * γ * M_0 ^ 2 := by
    calc
      ∑ ω ∈ G, W ω * Z ω ^ 2 ≤ ∑ ω : Ω, W ω * Z ω ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg (fun ω => mul_nonneg (hW_nn ω) (sq_nonneg (Z ω)))
      _ ≤ 3 * γ * M_0 ^ 2 := hE2
  have hGW_nn : 0 ≤ ∑ ω ∈ G, W ω := Finset.sum_nonneg (fun ω _ => hW_nn ω)
  have hcomb : (1 / 4 : ℝ) * M_0 ^ 2 ≤ (∑ ω ∈ G, W ω) * (3 * γ * M_0 ^ 2) :=
    le_trans hsq_low (le_trans hCS_G (mul_le_mul_of_nonneg_left hG_E2 hGW_nn))
  have hmul4 : 1 * M_0 ^ 2 ≤ ((∑ ω ∈ G, W ω) * (12 * γ)) * M_0 ^ 2 := by
    linarith [hcomb,
      show (∑ ω ∈ G, W ω) * (3 * γ * M_0 ^ 2) =
        (1 / 4 : ℝ) * (((∑ ω ∈ G, W ω) * (12 * γ)) * M_0 ^ 2) by ring]
  have h1 : 1 ≤ (∑ ω ∈ G, W ω) * (12 * γ) := le_of_mul_le_mul_right hmul4 hM0_sq_pos
  rwa [Finset.sum_mul] at h1

open Classical in
private lemma expurgation_hPhi_sum1 :
    ∀ {Ω V : Type} [Fintype Ω] (W : Ω → ℝ) (P_raw : Ω → Finset V) (n_0 : ℝ),
      0 < n_0 → ∑ ω : Ω, W ω * ↑(P_raw ω).card ≤ n_0 → ∑ ω : Ω, W ω * (↑(P_raw ω).card / (6 *
          n_0)) ≤ 1 / 6 := by
  classical
  intro Ω V _ W P_raw n_0 hn0 hM1
  have heq : ∑ ω : Ω, W ω * (((P_raw ω).card : ℝ) / (6 * n_0)) =
      (∑ ω : Ω, W ω * ((P_raw ω).card : ℝ)) / (6 * n_0) := by
    simp_rw [← mul_div_assoc]
    exact (Finset.sum_div Finset.univ (fun ω => W ω * ((P_raw ω).card : ℝ)) (6 * n_0)).symm
  rw [heq]
  have hden : 0 < 6 * n_0 := by positivity
  rw [div_le_iff₀ hden]
  linarith only [hM1]

open Classical in
private lemma expurgation_hPhi_sum2 :
    ∀ {Ω V : Type} [Fintype Ω] (W : Ω → ℝ) (Rel : V → V → Prop) [DecidableRel Rel] (P_raw : Ω →
        Finset V)
      (n_0 D_star γ : ℝ),
      0 < n_0 →
        0 < D_star →
          1 ≤ γ →
            ∑ ω : Ω, W ω *
              ∑ x ∈ P_raw ω, (({y ∈ P_raw ω | Rel x y} : Finset V).card : ℝ) ^ 2 ≤ 2 * γ * n_0 *
                D_star ^ 2 →
              let deg_set : Finset V → V → ℕ := fun (S : Finset V) (x : V) => {y ∈ S | Rel x
                  y}.card;
              let W_2 : Ω → ℝ := fun (ω : Ω) => ∑ x ∈ P_raw ω, ↑(deg_set (P_raw ω) x) ^ 2;
              ∑ ω : Ω, W ω * (W_2 ω / (12 * γ * n_0 * D_star ^ 2)) ≤ 1 / 6 := by
  classical
  intro Ω V _ W Rel _ P_raw n_0 D_star γ hn0 hD hγ hW2 deg_set W_2
  have heq : ∑ ω : Ω, W ω * (W_2 ω / (12 * γ * n_0 * D_star ^ 2)) =
      (∑ ω : Ω, W ω * W_2 ω) / (12 * γ * n_0 * D_star ^ 2) := by
    simp_rw [← mul_div_assoc]
    exact (Finset.sum_div Finset.univ (fun ω => W ω * W_2 ω) (12 * γ * n_0 * D_star ^ 2)).symm
  rw [heq]
  have hden : 0 < 12 * γ * n_0 * D_star ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  have hW2' : ∑ ω : Ω, W ω * W_2 ω ≤ 2 * γ * n_0 * D_star ^ 2 := hW2
  linarith [hW2', show (1 / 6 : ℝ) * (12 * γ * n_0 * D_star ^ 2) = 2 * γ * n_0 * D_star ^ 2 by ring]

open Classical in
private lemma expurgation_hPhi_sum3 :
    ∀ {Ω V : Type} [Fintype Ω] (W : Ω → ℝ) (B_bad : Ω → Finset V) (n_0 δ_bad : ℝ),
      0 < n_0 →
        0 < δ_bad →
          ∑ ω : Ω, W ω * ↑(B_bad ω).card ≤ δ_bad * n_0 → ∑ ω : Ω, W ω * (↑(B_bad ω).card / (6 *
              δ_bad * n_0)) ≤ 1 / 6 := by
  classical
  intro Ω V _ W B_bad n_0 δ_bad hn0 hδ hBad
  have heq : ∑ ω : Ω, W ω * (((B_bad ω).card : ℝ) / (6 * δ_bad * n_0)) =
      (∑ ω : Ω, W ω * ((B_bad ω).card : ℝ)) / (6 * δ_bad * n_0) := by
    simp_rw [← mul_div_assoc]
    exact (Finset.sum_div Finset.univ (fun ω => W ω * ((B_bad ω).card : ℝ)) (6 * δ_bad * n_0)).symm
  rw [heq]
  have hden : 0 < 6 * δ_bad * n_0 := by positivity
  rw [div_le_iff₀ hden]
  linarith [hBad, show (1 / 6 : ℝ) * (6 * δ_bad * n_0) = δ_bad * n_0 by ring]

open Classical in
private lemma expurgation_hB0_deg_sum :
    ∀ {Ω V : Type} (Rel : V → V → Prop) [DecidableRel Rel] (P_raw B_bad : Ω → Finset V) (n_0
        D_star γ δ_bad : ℝ),
      0 < n_0 →
        0 < D_star →
          1 ≤ γ →
            0 < δ_bad →
              72 * 144 * γ ^ 3 * δ_bad ≤ 1 / 256 →
                let deg_set : Finset V → V → ℕ := fun (S : Finset V) (x : V) => {y ∈ S | Rel x
                    y}.card;
                let W_2 : Ω → ℝ := fun (ω : Ω) => ∑ x ∈ P_raw ω, ↑(deg_set (P_raw ω) x) ^ 2;
                ∀ (ω₀ : Ω),
                  W_2 ω₀ ≤ 144 * γ ^ 2 * n_0 * D_star ^ 2 →
                    ↑(B_bad ω₀).card ≤ 72 * γ * δ_bad * n_0 →
                      let P_0 : Finset V := P_raw ω₀;
                      let B_raw : Finset V := B_bad ω₀;
                      let B_0 : Finset V := P_0 ∩ B_raw;
                      ∑ x ∈ B_0, ↑(deg_set P_0 x) ≤ 1 / 16 * (n_0 * D_star) := by
  classical
  intro Ω V Rel _ P_raw B_bad n_0 D_star γ δ_bad hn0 hD hγ hδ h_margin deg_set W_2 ω₀ hW2_ω₀
      hBad_ω₀ P_0 B_raw B_0
  have hcs_raw := Finset.sum_mul_sq_le_sq_mul_sq B_0 (fun _ => (1 : ℝ)) (fun x => (deg_set P_0 x
      : ℝ))
  have hcs : (∑ x ∈ B_0, (deg_set P_0 x : ℝ)) ^ 2 ≤
      (B_0.card : ℝ) * ∑ x ∈ B_0, ((deg_set P_0 x : ℝ) ^ 2) := by
    have h1 : ∑ x ∈ B_0, (1 : ℝ) * (deg_set P_0 x : ℝ) = ∑ x ∈ B_0, (deg_set P_0 x : ℝ) := by
      simp only [one_mul]
    have h2 : ∑ _x ∈ B_0, (1 : ℝ) ^ 2 = (B_0.card : ℝ) := by
      simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
    rwa [h1, h2] at hcs_raw
  have hB0_card : (B_0.card : ℝ) ≤ 72 * γ * δ_bad * n_0 := by
    have hnat : B_0.card ≤ B_raw.card := Finset.card_le_card Finset.inter_subset_right
    have hreal : (B_0.card : ℝ) ≤ (B_raw.card : ℝ) := by exact_mod_cast hnat
    exact le_trans hreal hBad_ω₀
  have hB0_sq : ∑ x ∈ B_0, ((deg_set P_0 x : ℝ) ^ 2) ≤ 144 * γ ^ 2 * n_0 * D_star ^ 2 := by
    have hsub : ∑ x ∈ B_0, ((deg_set P_0 x : ℝ) ^ 2) ≤ W_2 ω₀ :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun _ _ _ => sq_nonneg _)
    exact le_trans hsub hW2_ω₀
  have hprod1 : (B_0.card : ℝ) * ∑ x ∈ B_0, ((deg_set P_0 x : ℝ) ^ 2) ≤
      (72 * γ * δ_bad * n_0) * (144 * γ ^ 2 * n_0 * D_star ^ 2) :=
    mul_le_mul hB0_card hB0_sq
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (by positivity)
  have hprod2 : (72 * γ * δ_bad * n_0) * (144 * γ ^ 2 * n_0 * D_star ^ 2) ≤
      ((1 / 16 : ℝ) * (n_0 * D_star)) ^ 2 := by
    have hmarg_mul : (72 * 144 * γ ^ 3 * δ_bad) * (n_0 * D_star) ^ 2 ≤
        (1 / 256 : ℝ) * (n_0 * D_star) ^ 2 :=
      mul_le_mul_of_nonneg_right h_margin (sq_nonneg _)
    linarith [hmarg_mul,
      show (72 * γ * δ_bad * n_0) * (144 * γ ^ 2 * n_0 * D_star ^ 2) =
        (72 * 144 * γ ^ 3 * δ_bad) * (n_0 * D_star) ^ 2 by ring,
      show (1 / 256 : ℝ) * (n_0 * D_star) ^ 2 =
        ((1 / 16 : ℝ) * (n_0 * D_star)) ^ 2 by ring]
  have hsq_le : (∑ x ∈ B_0, (deg_set P_0 x : ℝ)) ^ 2 ≤ ((1 / 16 : ℝ) * (n_0 * D_star)) ^ 2 :=
    le_trans hcs (le_trans hprod1 hprod2)
  have hrhs_pos : 0 < (1 / 16 : ℝ) * (n_0 * D_star) := by positivity
  nlinarith only [hsq_le, hrhs_pos]

open Classical in
private lemma expurgation_hX_low :
    ∀ {Ω V : Type} (Rel : V → V → Prop) [DecidableRel Rel] (P_raw B_bad : Ω → Finset V) (n_0
        D_star γ : ℝ),
      0 < n_0 →
        0 < D_star →
          1 ≤ γ →
            let E_set : Finset V → Finset (V × V) := fun (S : Finset V) => {xy ∈ S ×ˢ S | Rel
                xy.1 xy.2};
            let deg_set : Finset V → V → ℕ := fun (S : Finset V) (x : V) => {y ∈ S | Rel x y}.card;
            let W_2 : Ω → ℝ := fun (ω : Ω) => ∑ x ∈ P_raw ω, ↑(deg_set (P_raw ω) x) ^ 2;
            γ ≠ 0 →
              ∀ (ω₀ : Ω),
                W_2 ω₀ ≤ 144 * γ ^ 2 * n_0 * D_star ^ 2 →
                  (∀ (A B : Finset V), {xy ∈ A ×ˢ B | Rel xy.1 xy.2}.card = ∑ x ∈ A, deg_set B x) →
                    let P_0 : Finset V := P_raw ω₀;
                    let B_raw : Finset V := B_bad ω₀;
                    let X : Finset V := P_0 \ B_raw;
                    3 / 8 * (n_0 * D_star) ≤ ↑(E_set X).card → 1 / 1024 * γ⁻¹ ^ 2 * n_0 ≤
                        ↑X.card := by
  classical
  intro Ω V Rel _ P_raw B_bad n_0 D_star γ hn0 hD hγ E_set deg_set W_2 hγ_ne ω₀ hW2_ω₀
      h_fiber_left P_0 B_raw X hEX_low
  have hEX_deg_nat : (E_set X).card ≤ ∑ x ∈ X, deg_set P_0 x := by
    rw [h_fiber_left X X]
    refine Finset.sum_le_sum (fun x _ => ?_)
    exact Finset.card_le_card (Finset.filter_subset_filter (fun y => Rel x y) Finset.sdiff_subset)
  have hEX_deg : ((E_set X).card : ℝ) ≤ ∑ x ∈ X, (deg_set P_0 x : ℝ) := by
    have hcast : ((E_set X).card : ℝ) ≤ ((∑ x ∈ X, deg_set P_0 x : ℕ) : ℝ) := by
      exact_mod_cast hEX_deg_nat
    push_cast at hcast
    exact hcast
  have hsum_low : (3 / 8 : ℝ) * (n_0 * D_star) ≤ ∑ x ∈ X, (deg_set P_0 x : ℝ) :=
    le_trans hEX_low hEX_deg
  have hsq_low : (9 / 64 : ℝ) * n_0 ^ 2 * D_star ^ 2 ≤ (∑ x ∈ X, (deg_set P_0 x : ℝ)) ^ 2 := by
    have hpos : 0 < (3 / 8 : ℝ) * (n_0 * D_star) := by positivity
    have hsq : ((3 / 8 : ℝ) * (n_0 * D_star)) ^ 2 ≤ (∑ x ∈ X, (deg_set P_0 x : ℝ)) ^ 2 := by
      nlinarith only [hsum_low, hpos]
    linarith [hsq, show ((3 / 8 : ℝ) * (n_0 * D_star)) ^ 2 = (9 / 64 : ℝ) * n_0 ^ 2 * D_star ^ 2
        by ring]
  have hcs_raw := Finset.sum_mul_sq_le_sq_mul_sq X (fun _ => (1 : ℝ)) (fun x => (deg_set P_0 x : ℝ))
  have hcs : (∑ x ∈ X, (deg_set P_0 x : ℝ)) ^ 2 ≤
      (X.card : ℝ) * ∑ x ∈ X, ((deg_set P_0 x : ℝ) ^ 2) := by
    have h1 : ∑ x ∈ X, (1 : ℝ) * (deg_set P_0 x : ℝ) = ∑ x ∈ X, (deg_set P_0 x : ℝ) := by
      simp only [one_mul]
    have h2 : ∑ _x ∈ X, (1 : ℝ) ^ 2 = (X.card : ℝ) := by
      simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
    rwa [h1, h2] at hcs_raw
  have hX_sq : ∑ x ∈ X, ((deg_set P_0 x : ℝ) ^ 2) ≤ 144 * γ ^ 2 * n_0 * D_star ^ 2 := by
    have hsub : ∑ x ∈ X, ((deg_set P_0 x : ℝ) ^ 2) ≤ W_2 ω₀ :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => sq_nonneg _)
    exact le_trans hsub hW2_ω₀
  have hprod : (9 / 64 : ℝ) * n_0 ^ 2 * D_star ^ 2 ≤
      (X.card : ℝ) * (144 * γ ^ 2 * n_0 * D_star ^ 2) :=
    le_trans hsq_low (le_trans hcs (mul_le_mul_of_nonneg_left hX_sq (Nat.cast_nonneg _)))
  have halg : ((1 / 1024 : ℝ) * γ⁻¹ ^ 2 * n_0) * (144 * γ ^ 2 * n_0 * D_star ^ 2) =
      (9 / 64 : ℝ) * n_0 ^ 2 * D_star ^ 2 := by
    field_simp [hγ_ne]
    ring
  have hfactor_pos : 0 < 144 * γ ^ 2 * n_0 * D_star ^ 2 := by positivity
  apply le_of_mul_le_mul_right _ hfactor_pos
  rw [halg]
  exact hprod

open Classical in
theorem paley_zygmund_markov_expurgation {Ω V : Type} [Fintype Ω]
    (W : Ω → ℝ) (hW_nn : ∀ ω : Ω, 0 ≤ W ω) (hW_sum : ∑ ω : Ω, W ω = 1)
    (Rel : V → V → Prop) [DecidableRel Rel] (hRel_symm : Std.Symm Rel)
    (P_raw B_bad : Ω → Finset V)
    (n_0 D_star γ δ_bad : ℝ)
    (hn0 : 0 < n_0) (hD : 0 < D_star) (hγ : 1 ≤ γ) (hδ : 0 < δ_bad)
    (h_margin : 72 * 144 * γ ^ 3 * δ_bad ≤ 1 / 256)
    (hM1 : ∑ ω : Ω, W ω * ((P_raw ω).card : ℝ) ≤ n_0)
    (hE1 : n_0 * D_star ≤ ∑ ω : Ω, W ω *
      (((P_raw ω ×ˢ P_raw ω).filter (fun xy => Rel xy.1 xy.2)).card : ℝ))
    (hE2 : ∑ ω : Ω, W ω *
      ((((P_raw ω ×ˢ P_raw ω).filter (fun xy => Rel xy.1 xy.2)).card : ℝ) ^ 2) ≤
        3 * γ * (n_0 * D_star) ^ 2)
    (hW2 : ∑ ω : Ω, W ω *
      (∑ x ∈ P_raw ω, (((P_raw ω).filter (fun y => Rel x y)).card : ℝ) ^ 2) ≤
        2 * γ * n_0 * D_star ^ 2)
    (hBad : ∑ ω : Ω, W ω * ((B_bad ω).card : ℝ) ≤ δ_bad * n_0) :
    ∃ ω₀ : Ω,
      (1 / 1024 : ℝ) * γ⁻¹ ^ 2 * n_0 ≤ ((P_raw ω₀ \ B_bad ω₀).card : ℝ) ∧
      ((P_raw ω₀ \ B_bad ω₀).card : ℝ) ≤ 72 * γ * n_0 ∧
      (D_star / γ) * ((P_raw ω₀ \ B_bad ω₀).card : ℝ) ≤
        192 * ((((P_raw ω₀ \ B_bad ω₀) ×ˢ (P_raw ω₀ \ B_bad ω₀)).filter
          (fun xy => Rel xy.1 xy.2)).card : ℝ) :=
by
  classical
  let E_set : Finset V → Finset (V × V) :=
    fun S => (S ×ˢ S).filter (fun xy => Rel xy.1 xy.2)
  let deg_set : Finset V → V → ℕ :=
    fun S x => (S.filter (fun y => Rel x y)).card
  let Z : Ω → ℝ := fun ω => ((E_set (P_raw ω)).card : ℝ)
  let W_2 : Ω → ℝ := fun ω => ∑ x ∈ P_raw ω, ((deg_set (P_raw ω) x : ℝ) ^ 2)
  let M_0 : ℝ := n_0 * D_star
  have hγ_pos : 0 < γ := lt_of_lt_of_le zero_lt_one hγ
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hM0_pos : 0 < M_0 := mul_pos hn0 hD
  have hM0_sq_pos : 0 < M_0 ^ 2 := pow_pos hM0_pos 2
  have hW2_nn : ∀ ω : Ω, 0 ≤ W_2 ω := fun _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  let p_good : Ω → Prop := fun ω => (1 / 2 : ℝ) * M_0 ≤ Z ω
  let instDecGood : DecidablePred p_good := Classical.decPred p_good
  let instDecNotGood : ∀ ω : Ω, Decidable (¬ p_good ω) := fun ω => Classical.dec (¬ p_good ω)
  let G : Finset Ω := Finset.univ.filter p_good
  let Gc : Finset Ω := Finset.univ.filter (fun ω => ¬ p_good ω)
  have h_part : (∑ ω ∈ G, W ω * Z ω) + (∑ ω ∈ Gc, W ω * Z ω) = ∑ ω : Ω, W ω * Z ω :=
    Finset.sum_filter_add_sum_filter_not Finset.univ p_good (fun ω => W ω * Z ω)
  have hGc_bound : ∑ ω ∈ Gc, W ω * Z ω ≤ (1 / 2 : ℝ) * M_0 :=
    @expurgation_hGc_bound Ω V inferInstance W hW_nn hW_sum Rel inferInstance P_raw n_0 D_star
        hn0 hD
  have hE1' : M_0 ≤ ∑ ω : Ω, W ω * Z ω := hE1
  have hG_E1 : (1 / 2 : ℝ) * M_0 ≤ ∑ ω ∈ G, W ω * Z ω := by
    linarith only [h_part, hGc_bound, hE1']
  have hCS_G : (∑ ω ∈ G, W ω * Z ω) ^ 2 ≤ (∑ ω ∈ G, W ω) * (∑ ω ∈ G, W ω * Z ω ^ 2) :=
    @expurgation_hCS_G Ω V inferInstance W hW_nn Rel inferInstance P_raw n_0 D_star
  have hPZ : 1 ≤ ∑ ω ∈ G, W ω * (12 * γ) :=
    @expurgation_hPZ Ω V inferInstance W hW_nn Rel inferInstance P_raw n_0 D_star γ hE2 hM0_pos
        hM0_sq_pos hG_E1 hCS_G
  let Phi : Ω → ℝ := fun ω =>
    ((P_raw ω).card : ℝ) / (6 * n_0) +
    W_2 ω / (12 * γ * n_0 * D_star ^ 2) +
    ((B_bad ω).card : ℝ) / (6 * δ_bad * n_0)
  have hPhi_t1_nn : ∀ ω : Ω, 0 ≤ ((P_raw ω).card : ℝ) / (6 * n_0) :=
    fun _ => div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hPhi_t2_nn : ∀ ω : Ω, 0 ≤ W_2 ω / (12 * γ * n_0 * D_star ^ 2) :=
    fun ω => div_nonneg (hW2_nn ω) (by positivity)
  have hPhi_t3_nn : ∀ ω : Ω, 0 ≤ ((B_bad ω).card : ℝ) / (6 * δ_bad * n_0) :=
    fun _ => div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hPhi_nn : ∀ ω : Ω, 0 ≤ Phi ω := fun ω => by
    dsimp only [Phi]
    linarith only [hPhi_t1_nn ω, hPhi_t2_nn ω, hPhi_t3_nn ω]
  have hPhi_sum1 : ∑ ω : Ω, W ω * (((P_raw ω).card : ℝ) / (6 * n_0)) ≤ 1 / 6 :=
    @expurgation_hPhi_sum1 Ω V inferInstance W P_raw n_0 hn0 hM1
  have hPhi_sum2 : ∑ ω : Ω, W ω * (W_2 ω / (12 * γ * n_0 * D_star ^ 2)) ≤ 1 / 6 :=
    @expurgation_hPhi_sum2 Ω V inferInstance W Rel inferInstance P_raw n_0 D_star γ hn0 hD hγ hW2
  have hPhi_sum3 : ∑ ω : Ω, W ω * (((B_bad ω).card : ℝ) / (6 * δ_bad * n_0)) ≤ 1 / 6 :=
    @expurgation_hPhi_sum3 Ω V inferInstance W B_bad n_0 δ_bad hn0 hδ hBad
  have hPhi_G_le : ∑ ω ∈ G, W ω * Phi ω ≤ 1 / 2 := by
    have huniv : ∑ ω ∈ G, W ω * Phi ω ≤ ∑ ω : Ω, W ω * Phi ω :=
      Finset.sum_le_univ_sum_of_nonneg (fun ω => mul_nonneg (hW_nn ω) (hPhi_nn ω))
    have hexp : ∑ ω : Ω, W ω * Phi ω =
        (∑ ω : Ω, W ω * (((P_raw ω).card : ℝ) / (6 * n_0))) +
        (∑ ω : Ω, W ω * (W_2 ω / (12 * γ * n_0 * D_star ^ 2))) +
        (∑ ω : Ω, W ω * (((B_bad ω).card : ℝ) / (6 * δ_bad * n_0))) := by
      have hdist : ∀ ω : Ω, W ω * Phi ω =
          W ω * (((P_raw ω).card : ℝ) / (6 * n_0)) +
          W ω * (W_2 ω / (12 * γ * n_0 * D_star ^ 2)) +
          W ω * (((B_bad ω).card : ℝ) / (6 * δ_bad * n_0)) := by
        intro ω
        dsimp only [Phi]
        ring
      simp_rw [hdist, Finset.sum_add_distrib]
    linarith only [huniv, hexp, hPhi_sum1, hPhi_sum2, hPhi_sum3]
  have hPhi_lt_PZ : ∑ ω ∈ G, W ω * Phi ω < ∑ ω ∈ G, W ω * (12 * γ) := by
    linarith only [hPhi_G_le, hPZ]
  obtain ⟨ω₀, hω₀_G, hω₀_lt⟩ := Finset.exists_lt_of_sum_lt hPhi_lt_PZ
  have hPhi_ω₀_le : Phi ω₀ ≤ 12 * γ :=
    le_of_lt (lt_of_mul_lt_mul_left hω₀_lt (hW_nn ω₀))
  have hZ_ω₀ : (1 / 2 : ℝ) * (n_0 * D_star) ≤ Z ω₀ := (Finset.mem_filter.mp hω₀_G).2
  have hP0_card : ((P_raw ω₀).card : ℝ) ≤ 72 * γ * n_0 := by
    have h1 : ((P_raw ω₀).card : ℝ) / (6 * n_0) ≤ 12 * γ := by
      have ht2 := hPhi_t2_nn ω₀
      have ht3 := hPhi_t3_nn ω₀
      dsimp only [Phi] at hPhi_ω₀_le
      linarith only [hPhi_ω₀_le, ht2, ht3]
    have hden : 0 < 6 * n_0 := by positivity
    rw [div_le_iff₀ hden] at h1
    linarith [h1, show (12 * γ) * (6 * n_0) = 72 * γ * n_0 by ring]
  have hW2_ω₀ : W_2 ω₀ ≤ 144 * γ ^ 2 * n_0 * D_star ^ 2 := by
    have h1 : W_2 ω₀ / (12 * γ * n_0 * D_star ^ 2) ≤ 12 * γ := by
      have ht1 := hPhi_t1_nn ω₀
      have ht3 := hPhi_t3_nn ω₀
      dsimp only [Phi] at hPhi_ω₀_le
      linarith only [hPhi_ω₀_le, ht1, ht3]
    have hden : 0 < 12 * γ * n_0 * D_star ^ 2 := by positivity
    rw [div_le_iff₀ hden] at h1
    linarith [h1, show (12 * γ) * (12 * γ * n_0 * D_star ^ 2) = 144 * γ ^ 2 * n_0 * D_star ^ 2
        by ring]
  have hBad_ω₀ : ((B_bad ω₀).card : ℝ) ≤ 72 * γ * δ_bad * n_0 := by
    have h1 : ((B_bad ω₀).card : ℝ) / (6 * δ_bad * n_0) ≤ 12 * γ := by
      have ht1 := hPhi_t1_nn ω₀
      have ht2 := hPhi_t2_nn ω₀
      dsimp only [Phi] at hPhi_ω₀_le
      linarith only [hPhi_ω₀_le, ht1, ht2]
    have hden : 0 < 6 * δ_bad * n_0 := by positivity
    rw [div_le_iff₀ hden] at h1
    linarith [h1, show (12 * γ) * (6 * δ_bad * n_0) = 72 * γ * δ_bad * n_0 by ring]
  have h_fiber_left : ∀ A B : Finset V,
      ((A ×ˢ B).filter (fun xy => Rel xy.1 xy.2)).card = ∑ x ∈ A, deg_set B x := by
    intro A B
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact (Finset.card_filter (fun y => Rel x y) B).symm
  have h_fiber_right : ∀ A B : Finset V,
      ((A ×ˢ B).filter (fun xy => Rel xy.1 xy.2)).card = ∑ y ∈ B, deg_set A y := by
    intro A B
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have hsym : ∑ x ∈ A, (if Rel x y then 1 else 0) = ∑ x ∈ A, (if Rel y x then 1 else 0) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      exact ite_congr (propext ⟨fun h => hRel_symm.symm _ _ h, fun h => hRel_symm.symm _ _ h⟩)
        (fun _ => rfl) (fun _ => rfl)
    rw [hsym]
    exact (Finset.card_filter (fun x => Rel y x) A).symm
  let P_0 : Finset V := P_raw ω₀
  let B_raw : Finset V := B_bad ω₀
  let B_0 : Finset V := P_0 ∩ B_raw
  let X : Finset V := P_0 \ B_raw
  let L_1 : Finset (V × V) := (B_0 ×ˢ P_0).filter (fun xy => Rel xy.1 xy.2)
  let L_2 : Finset (V × V) := (P_0 ×ˢ B_0).filter (fun xy => Rel xy.1 xy.2)
  have hE_sub : E_set P_0 ⊆ E_set X ∪ (L_1 ∪ L_2) := by
    intro xy hxy
    simp only [E_set, L_1, L_2, B_0, X, Finset.mem_union, Finset.mem_filter,
      Finset.mem_product, Finset.mem_inter, Finset.mem_sdiff] at hxy ⊢
    rcases hxy with ⟨⟨hxP, hyP⟩, hrel⟩
    by_cases hxB : xy.1 ∈ B_raw
    · exact Or.inr (Or.inl ⟨⟨⟨hxP, hxB⟩, hyP⟩, hrel⟩)
    · by_cases hyB : xy.2 ∈ B_raw
      · exact Or.inr (Or.inr ⟨⟨hxP, ⟨hyP, hyB⟩⟩, hrel⟩)
      · exact Or.inl ⟨⟨⟨hxP, hxB⟩, ⟨hyP, hyB⟩⟩, hrel⟩
  have hZ_del_nat : (E_set P_0).card ≤ (E_set X).card + 2 * ∑ x ∈ B_0, deg_set P_0 x := by
    have hc0 := Finset.card_le_card hE_sub
    have hc1 := Finset.card_union_le (E_set X) (L_1 ∪ L_2)
    have hc2 := Finset.card_union_le L_1 L_2
    have hL1 : L_1.card = ∑ x ∈ B_0, deg_set P_0 x := h_fiber_left B_0 P_0
    have hL2 : L_2.card = ∑ x ∈ B_0, deg_set P_0 x := h_fiber_right P_0 B_0
    omega
  have hZ_del : Z ω₀ ≤ ((E_set X).card : ℝ) + 2 * ∑ x ∈ B_0, (deg_set P_0 x : ℝ) := by
    have hcast : ((E_set P_0).card : ℝ) ≤
        (((E_set X).card + 2 * ∑ x ∈ B_0, deg_set P_0 x : ℕ) : ℝ) := by
      exact_mod_cast hZ_del_nat
    push_cast at hcast
    exact hcast
  have hX_up : (X.card : ℝ) ≤ 72 * γ * n_0 := by
    have hle_nat : X.card ≤ P_0.card := Finset.card_le_card Finset.sdiff_subset
    have hle_real : (X.card : ℝ) ≤ (P_0.card : ℝ) := by exact_mod_cast hle_nat
    exact le_trans hle_real hP0_card
  have hB0_deg_sum : ∑ x ∈ B_0, (deg_set P_0 x : ℝ) ≤ (1 / 16 : ℝ) * (n_0 * D_star) :=
    @expurgation_hB0_deg_sum Ω V Rel inferInstance P_raw B_bad n_0 D_star γ δ_bad hn0 hD hγ hδ
        h_margin ω₀ hW2_ω₀ hBad_ω₀
  have hEX_low : (3 / 8 : ℝ) * (n_0 * D_star) ≤ ((E_set X).card : ℝ) := by
    linarith only [hZ_ω₀, hZ_del, hB0_deg_sum]
  have hDense : (D_star / γ) * (X.card : ℝ) ≤ 192 * ((E_set X).card : ℝ) := by
    have hDγ_nn : 0 ≤ D_star / γ := div_nonneg (le_of_lt hD) (le_of_lt hγ_pos)
    have h1 : (D_star / γ) * (X.card : ℝ) ≤ (D_star / γ) * (72 * γ * n_0) :=
      mul_le_mul_of_nonneg_left hX_up hDγ_nn
    have h2 : (D_star / γ) * (72 * γ * n_0) = 72 * (n_0 * D_star) := by
      field_simp [hγ_ne]
    linarith only [h1, h2, hEX_low]
  have hX_low : (1 / 1024 : ℝ) * γ⁻¹ ^ 2 * n_0 ≤ (X.card : ℝ) :=
    @expurgation_hX_low Ω V Rel inferInstance P_raw B_bad n_0 D_star γ hn0 hD hγ hγ_ne ω₀ hW2_ω₀
        h_fiber_left hEX_low
  exact ⟨ω₀, hX_low, hX_up, hDense⟩

end Helpers

end HighDimSteinerSpanners.Proofs.CSP
