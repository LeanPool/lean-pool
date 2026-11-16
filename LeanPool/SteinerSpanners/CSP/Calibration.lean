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

import Mathlib.Analysis.Complex.ExponentialBounds

public import LeanPool.SteinerSpanners.CSP.Expurgation

/-! # Calibration for spanner CSP codes

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib.
-/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners.Proofs.CSP

noncomputable section Helpers

lemma dyadic_linear_growth : ∀ m : ℕ, 20 ≤ m → 20000 * (m + 2) ≤ 2 ^ m := by
  classical
  intro m hm
  refine Nat.le_induction ?_ ?_ m hm
  · norm_num
  · intro k hk ih
    calc
      20000 * (k + 1 + 2) ≤ 2 * (20000 * (k + 2)) := by omega
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by ring

lemma twice_choose_two : ∀ m : ℕ, 2 * m.choose 2 = m * (m - 1) := by
  classical
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    cases m with
    | zero => rfl
    | succ k =>
      have hc : (k + 2).choose 2 = (k + 1) + (k + 1).choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      have ih' : 2 * (k + 1).choose 2 = (k + 1) * k := ih
      have hsub : k + 2 - 1 = k + 1 := rfl
      rw [hc, hsub]
      linarith only [ih']

lemma twice_choose_two_int : ∀ m : ℕ, 2 * (m.choose 2 : ℤ) = (m : ℤ) * ((m : ℤ) - 1) := by
  classical
  intro m
  cases m with
  | zero => norm_num
  | succ k =>
    have hnat := twice_choose_two (k + 1)
    have hcast : (2 : ℤ) * ((k + 1).choose 2 : ℤ) = ((k + 1 : ℕ) : ℤ) * (k : ℤ) := by
      exact_mod_cast hnat
    push_cast at hcast ⊢
    linarith only [hcast]

lemma twice_choose_two_real : ∀ m : ℕ, 2 * (m.choose 2 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
  classical
  intro m
  exact_mod_cast twice_choose_two_int m

lemma choose_two_le_product {N : ℕ} : ∀ s : ℕ, s ≤ N → s.choose 2 ≤ s * (N - 1) := by
  classical
  intro s hs
  rcases Nat.eq_zero_or_pos s with rfl | hs_pos
  · simp
  · have h1 : s.choose 2 ≤ 2 * s.choose 2 := Nat.le_mul_of_pos_left _ (by omega)
    have h2 := twice_choose_two s
    have h3 : s * (s - 1) ≤ s * (N - 1) := Nat.mul_le_mul_left s (by omega)
    omega





lemma ordered_pairs_card {N : ℕ} : ∀ A : Finset (Fin N),
    ((A ×ˢ A).filter (fun uv : Fin N × Fin N => uv.1 < uv.2)).card = A.card.choose 2 := by
  classical
  intro A
  rw [← Finset.card_powersetCard 2 A]
  refine Finset.card_bij (fun uv _ => ({uv.1, uv.2} : Finset (Fin N))) ?_ ?_ ?_
  · intro uv huv
    simp only [Finset.mem_filter, Finset.mem_product] at huv
    rw [Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_pair (ne_of_lt huv.2)⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact huv.1.1
    · exact huv.1.2
  · intro uv₁ h₁ uv₂ h₂ heq
    simp only [Finset.mem_filter, Finset.mem_product] at h₁ h₂
    have hm1 : uv₁.1 ∈ ({uv₂.1, uv₂.2} : Finset (Fin N)) := by
      rw [← heq]; simp
    have hm2 : uv₁.2 ∈ ({uv₂.1, uv₂.2} : Finset (Fin N)) := by
      rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
    rcases hm1 with h11 | h12 <;> rcases hm2 with h21 | h22
    · exfalso; exact (ne_of_lt h₁.2) (h11.trans h21.symm)
    · exact Prod.ext h11 h22
    · exfalso
      have hlt1 : uv₁.1 < uv₁.2 := h₁.2
      have hlt2 : uv₂.1 < uv₂.2 := h₂.2
      rw [h12, h21] at hlt1
      exact lt_asymm hlt1 hlt2
    · exfalso; exact (ne_of_lt h₁.2) (h12.trans h22.symm)
  · intro T hT
    rw [Finset.mem_powersetCard] at hT
    rcases Finset.card_eq_two.mp hT.2 with ⟨a, b, hab, rfl⟩
    have ha : a ∈ A := hT.1 (by simp)
    have hb : b ∈ A := hT.1 (by simp)
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · refine ⟨(a, b), ?_, rfl⟩
      simp [ha, hb, hlt]
    · exact absurd rfl hab
    · refine ⟨(b, a), ?_, Finset.pair_comm b a⟩
      simp [ha, hb, hgt]

lemma homQueryMap_injective {N q : ℕ} : ∀ z : Fin N → Fin q,
    Function.Injective (fun uv : Fin N × Fin N => (uv.1, uv.2, z uv.1, z uv.2)) := by
  classical
  intro z uv₁ uv₂ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1 h.2.1

lemma homQueries_card {N q : ℕ} : ∀ x : Fin N → Fin q, (homQueries x).card = N.choose 2 := by
  classical
  intro x
  unfold homQueries
  rw [Finset.card_image_of_injective _ (homQueryMap_injective x)]
  have huniv_eq : (Finset.univ.filter (fun uv : Fin N × Fin N => uv.1 < uv.2)) =
      ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
        (fun uv => uv.1 < uv.2) := by
    ext uv
    simp
  rw [huniv_eq, ordered_pairs_card, Finset.card_univ, Fintype.card_fin]

lemma homQueries_union_card {N q : ℕ} (hN_ge1 : 1 ≤ N) : ∀ x y : Fin N → Fin q,
    (homQueries x ∪ homQueries y).card =
      N.choose 2 + dHam x y * (N - 1) - (dHam x y).choose 2 := by
  classical
  intro x y
  let S := diffCoords x y
  let s := dHam x y
  let A : Finset (Fin N) := Finset.univ \ S
  have hs_eq : S.card = s := rfl
  have hs_le_N : s ≤ N := by
    simpa [hs_eq, Fintype.card_fin] using Finset.card_le_univ S
  have hA_card : A.card = N - s := by
    dsimp [A]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hs_eq]
  have hinter_eq : homQueries x ∩ homQueries y =
      ((A ×ˢ A).filter (fun uv : Fin N × Fin N => uv.1 < uv.2)).image
        (fun uv => (uv.1, uv.2, x uv.1, x uv.2)) := by
    ext t
    simp only [Finset.mem_inter, homQueries, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_product, A, Finset.mem_sdiff, S, diffCoords,
      not_not]
    constructor
    · rintro ⟨⟨uv₁, h₁, rfl⟩, ⟨uv₂, h₂, heq⟩⟩
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨heq1, heq2, heq3, heq4⟩
      refine ⟨uv₁, ⟨⟨?_, ?_⟩, h₁⟩, rfl⟩
      · rw [← heq3, heq1]
      · rw [← heq4, heq2]
    · rintro ⟨uv, ⟨⟨hx1, hx2⟩, huv⟩, rfl⟩
      refine ⟨⟨uv, huv, rfl⟩, ⟨uv, huv, ?_⟩⟩
      rw [hx1, hx2]
  have hinter_card : (homQueries x ∩ homQueries y).card = (N - s).choose 2 := by
    rw [hinter_eq, Finset.card_image_of_injective _ (homQueryMap_injective x),
        ordered_pairs_card, hA_card]
  have hunion_ie := Finset.card_union_add_card_inter (homQueries x) (homQueries y)
  rw [hinter_card, homQueries_card x, homQueries_card y] at hunion_ie
  have hs_choose_le : s.choose 2 ≤ s * (N - 1) := choose_two_le_product s hs_le_N
  have hs_choose_le_tot : s.choose 2 ≤ N.choose 2 + s * (N - 1) :=
    le_trans hs_choose_le (Nat.le_add_left _ _)
  suffices h_int : ((homQueries x ∪ homQueries y).card : ℤ) =
      ((N.choose 2 + s * (N - 1) - s.choose 2 : ℕ) : ℤ) from Int.ofNat.inj h_int
  have hie_int : ((homQueries x ∪ homQueries y).card : ℤ) + ((N - s).choose 2 : ℤ) =
      (N.choose 2 : ℤ) + (N.choose 2 : ℤ) := by exact_mod_cast hunion_ie
  have h2N := twice_choose_two_int N
  have h2s := twice_choose_two_int s
  have h2Ns := twice_choose_two_int (N - s)
  rw [Nat.cast_sub hs_le_N] at h2Ns
  rw [Nat.cast_sub hs_choose_le_tot, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hN_ge1]
  push_cast
  have hpoly : ((N : ℤ) - (s : ℤ)) * ((N : ℤ) - (s : ℤ) - 1) +
      ((N : ℤ) * ((N : ℤ) - 1) + 2 * (s : ℤ) * ((N : ℤ) - 1) - (s : ℤ) * ((s : ℤ) - 1)) =
      2 * ((N : ℤ) * ((N : ℤ) - 1)) := by ring
  linarith only [hie_int, h2N, h2s, h2Ns, hpoly]

lemma hammingSphere_card {N q : ℕ} : ∀ (x : Fin N → Fin q) (s : ℕ),
    (Finset.univ.filter (fun y => dHam x y = s)).card = N.choose s * (q - 1) ^ s := by
  classical
  intro x s
  let Fib : Finset (Fin N) → Finset (Fin N → Fin q) := fun S =>
    Fintype.piFinset (fun v : Fin N =>
      if v ∈ S then Finset.univ.erase (x v) else ({x v} : Finset (Fin q)))
  have hFib_mem : ∀ (S : Finset (Fin N)) (y : Fin N → Fin q),
      y ∈ Fib S ↔ diffCoords x y = S := by
    intro S y
    simp only [Fib, Fintype.mem_piFinset, Finset.ext_iff, diffCoords, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hy v
      specialize hy v
      by_cases hv : v ∈ S
      · simp only [ite_eq_left hv, Finset.mem_erase, Finset.mem_univ, and_true] at hy
        exact ⟨fun _ => hv, fun _ => Ne.symm hy⟩
      · simp only [ite_eq_right hv, Finset.mem_singleton] at hy
        exact ⟨fun hne => absurd hy.symm hne, fun h => absurd h hv⟩
    · intro hS v
      by_cases hv : v ∈ S
      · simp only [ite_eq_left hv, Finset.mem_erase, Finset.mem_univ, and_true]
        exact Ne.symm ((hS v).mpr hv)
      · simp only [ite_eq_right hv, Finset.mem_singleton]
        by_contra hne
        exact hv ((hS v).mp (Ne.symm hne))
  have h_bi : Finset.univ.filter (fun y : Fin N → Fin q => dHam x y = s) =
      ((Finset.univ : Finset (Fin N)).powersetCard s).biUnion Fib := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_powersetCard, hFib_mem, dHam]
    constructor
    · intro hs
      exact ⟨diffCoords x y, ⟨Finset.subset_univ _, hs⟩, rfl⟩
    · rintro ⟨S, ⟨_, hScard⟩, rfl⟩
      exact hScard
  have h_disj : (((Finset.univ : Finset (Fin N)).powersetCard s : Finset (Finset (Fin N))) :
      Set (Finset (Fin N))).PairwiseDisjoint Fib := by
    intro S₁ _ S₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy₁ hy₂
    rw [hFib_mem] at hy₁ hy₂
    exact hne (hy₁.symm.trans hy₂)
  rw [h_bi, Finset.card_biUnion h_disj]
  have hFib_card : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard s,
      (Fib S).card = (q - 1) ^ s := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    dsimp [Fib]
    rw [Fintype.card_piFinset]
    have hterm : ∀ v : Fin N,
        (if v ∈ S then Finset.univ.erase (x v) else ({x v} : Finset (Fin q))).card =
          if v ∈ S then q - 1 else 1 := by
      intro v
      split_ifs
      · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      · exact Finset.card_singleton _
    simp_rw [hterm]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, hS.2]
  rw [Finset.sum_congr rfl hFib_card, Finset.sum_const, smul_eq_mul,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

lemma orderedHammingSphere_card {N q : ℕ} : ∀ s : ℕ,
    (Finset.univ.filter
      (fun xy : (Fin N → Fin q) × (Fin N → Fin q) => dHam xy.1 xy.2 = s)).card =
      q ^ N * (N.choose s * (q - 1) ^ s) := by
  classical
  intro s
  let G : (Fin N → Fin q) → Finset ((Fin N → Fin q) × (Fin N → Fin q)) :=
    fun x => (Finset.univ.filter (fun y => dHam x y = s)).image (fun y => (x, y))
  have h_eq : Finset.univ.filter
      (fun xy : (Fin N → Fin q) × (Fin N → Fin q) => dHam xy.1 xy.2 = s) =
      (Finset.univ : Finset (Fin N → Fin q)).biUnion G := by
    ext xy
    simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_image]
    constructor
    · intro h
      exact ⟨xy.1, xy.2, h, Prod.eta xy⟩
    · rintro ⟨x, y, h, rfl⟩
      exact h
  have h_disj : ((Finset.univ : Finset (Fin N → Fin q)) : Set (Fin N → Fin q)).PairwiseDisjoint
      G := by
    intro x₁ _ x₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp₁ hp₂
    rcases Finset.mem_image.mp hp₁ with ⟨_, _, rfl⟩
    rcases Finset.mem_image.mp hp₂ with ⟨_, _, hp⟩
    exact hne (Prod.mk.inj hp).1.symm
  rw [h_eq, Finset.card_biUnion h_disj]
  have hG_card : ∀ x ∈ (Finset.univ : Finset (Fin N → Fin q)),
      (G x).card = N.choose s * (q - 1) ^ s := by
    intro x _
    dsimp [G]
    rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), hammingSphere_card x s]
  rw [Finset.sum_congr rfl hG_card, Finset.sum_const, smul_eq_mul,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]





open Classical in
private lemma calibration_h_upper_s :
    ∀ (r_star L : ℕ),
      (3001 : ℕ) ≤ r_star →
        (0 : ℝ) ≤ (↑r_star : ℝ) →
          let N : ℕ := (2 : ℕ) ^ L * r_star;
          (0 : ℝ) < (↑N : ℝ) →
            ∀ (s : ℕ), (↑(N.choose s) : ℝ) * ((↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ))) ^ s ≤ (4 :
                ℝ) ^ r_star / (4 : ℝ) ^ s := by
  classical
  intro r_star L hr_3001 hr_real_nn N hN_pos s
  have h_exp_4 : Real.exp (r_star : ℝ) ≤ (4 : ℝ) ^ r_star := by
    have h1 : Real.exp (r_star : ℝ) = (Real.exp 1) ^ r_star := by
      simp
    have h2 : Real.exp 1 ≤ 4 := by
      have hlt := Real.exp_one_lt_d9
      linarith only [hlt]
    rw [h1]
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) h2 r_star
  have hchoose : (N.choose s : ℝ) ≤ (N : ℝ) ^ s / (s.factorial : ℝ) :=
    Nat.choose_le_pow_div s N
  have hpow_div : ((r_star : ℝ) / (4 * (N : ℝ))) ^ s =
      (r_star : ℝ) ^ s / ((4 : ℝ) ^ s * (N : ℝ) ^ s) := by
    rw [div_pow, mul_pow]
  have hstep1 : (N.choose s : ℝ) * ((r_star : ℝ) / (4 * (N : ℝ))) ^ s ≤
      ((N : ℝ) ^ s / (s.factorial : ℝ)) *
        ((r_star : ℝ) ^ s / ((4 : ℝ) ^ s * (N : ℝ) ^ s)) := by
    rw [hpow_div]
    exact mul_le_mul_of_nonneg_right hchoose (by positivity)
  have hNs_ne : (N : ℝ) ^ s ≠ 0 := ne_of_gt (pow_pos hN_pos s)
  have hsimp : ((N : ℝ) ^ s / (s.factorial : ℝ)) *
      ((r_star : ℝ) ^ s / ((4 : ℝ) ^ s * (N : ℝ) ^ s)) =
      ((r_star : ℝ) ^ s / (s.factorial : ℝ)) / (4 : ℝ) ^ s := by
    field_simp [hNs_ne]
  have hexp_s : (r_star : ℝ) ^ s / (s.factorial : ℝ) ≤ (4 : ℝ) ^ r_star :=
    le_trans (Real.pow_div_factorial_le_exp (r_star : ℝ) hr_real_nn s) h_exp_4
  have hstep2 : ((r_star : ℝ) ^ s / (s.factorial : ℝ)) / (4 : ℝ) ^ s ≤
      (4 : ℝ) ^ r_star / (4 : ℝ) ^ s :=
    div_le_div_of_nonneg_right hexp_s (by positivity)
  linarith only [hstep1, hsimp, hstep2]

open Classical in
private lemma calibration_h_env_all :
    ∀ (r_star L : ℕ),
      let N : ℕ := (2 : ℕ) ^ L * r_star;
      (4 : ℝ) ^ r_star = (2 : ℝ) ^ ((2 : ℝ) * (↑r_star : ℝ)) →
        (∀ (s : ℕ), (↑(N.choose s) : ℝ) * ((↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ))) ^ s ≤ (4 : ℝ) ^
            r_star / (4 : ℝ) ^ s) →
          ∀ (s : ℕ), (↑(N.choose s) : ℝ) * ((↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ))) ^ s ≤ (2 : ℝ)
              ^ ((2 : ℝ) * (↑r_star : ℝ)) := by
  classical
  intro r_star L N h4_eq_rpow h_upper_s s
  rw [← h4_eq_rpow]
  have h4s_ge1 : (1 : ℝ) ≤ (4 : ℝ) ^ s := one_le_pow₀ (by norm_num)
  have hdiv : (4 : ℝ) ^ r_star / (4 : ℝ) ^ s ≤ (4 : ℝ) ^ r_star / 1 :=
    div_le_div_of_nonneg_left (by positivity) zero_lt_one h4s_ge1
  rw [div_one] at hdiv
  exact le_trans (h_upper_s s) hdiv

open Classical in
private lemma calibration_h_env_diag_low :
    ∀ (r_star L : ℕ),
      (3001 : ℕ) ≤ r_star →
        let N : ℕ := (2 : ℕ) ^ L * r_star;
        r_star ≤ N →
          (0 : ℝ) < (↑N : ℝ) →
            (4 : ℝ) ^ r_star = (2 : ℝ) ^ ((2 : ℝ) * (↑r_star : ℝ)) →
              (2 : ℝ) ^ (-((2 : ℝ) * (↑r_star : ℝ))) ≤
                (↑(N.choose r_star) : ℝ) * ((↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ))) ^ r_star := by
  classical
  intro r_star L hr_3001 N hr_le_N hN_pos h4_eq_rpow
  have h_fall : ∀ k M : ℕ, k ≤ M → M ^ k ≤ M.choose k * k ^ k := by
    intro k
    induction k with
    | zero =>
      intro M _
      simp
    | succ k ih =>
      intro M hM
      cases M with
      | zero => omega
      | succ M' =>
        have hM' : k ≤ M' := by omega
        cases k with
        | zero =>
          simp [Nat.choose_one_right]
        | succ k' =>
          let km := k' + 1
          have hkm_pos : 0 < km := by omega
          have hkm_le : km ≤ M' := hM'
          have hcross : (M' + 1) * km ≤ M' * (km + 1) := by nlinarith only [hkm_le]
          have hpow_cross : (M' + 1) ^ km * km ^ km ≤ M' ^ km * (km + 1) ^ km := by
            simpa [mul_pow] using Nat.pow_le_pow_left hcross km
          have h_ih := Nat.mul_le_mul_right ((km + 1) ^ km) (ih M' hkm_le)
          have hchain : (M' + 1) ^ km * km ^ km ≤ (M'.choose km * (km + 1) ^ km) * km ^ km := by
            calc
              (M' + 1) ^ km * km ^ km ≤ M' ^ km * (km + 1) ^ km := hpow_cross
              _ ≤ (M'.choose km * km ^ km) * (km + 1) ^ km := h_ih
              _ = (M'.choose km * (km + 1) ^ km) * km ^ km := by ring
          have hstep : (M' + 1) ^ km ≤ M'.choose km * (km + 1) ^ km :=
            Nat.le_of_mul_le_mul_right hchain (Nat.pow_pos hkm_pos)
          have hmul := Nat.mul_le_mul_left (M' + 1) hstep
          have hid := Nat.add_one_mul_choose_eq M' km
          calc
            (M' + 1) ^ (km + 1) = (M' + 1) * (M' + 1) ^ km := by ring
            _ ≤ (M' + 1) * (M'.choose km * (km + 1) ^ km) := hmul
            _ = ((M' + 1) * M'.choose km) * (km + 1) ^ km := by ring
            _ = ((M' + 1).choose (km + 1) * (km + 1)) * (km + 1) ^ km := by rw [hid]
            _ = (M' + 1).choose (km + 1) * (km + 1) ^ (km + 1) := by ring
  have hNr_real : (N : ℝ) ^ r_star ≤ (N.choose r_star : ℝ) * (r_star : ℝ) ^ r_star := by
    exact_mod_cast h_fall r_star N hr_le_N
  have hdiv := div_le_div_of_nonneg_right hNr_real
    (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ r_star * (N : ℝ) ^ r_star)
  have hNr_ne : (N : ℝ) ^ r_star ≠ 0 := ne_of_gt (pow_pos hN_pos r_star)
  have hlhs : (N : ℝ) ^ r_star / ((4 : ℝ) ^ r_star * (N : ℝ) ^ r_star) =
      (2 : ℝ) ^ (- (2 * (r_star : ℝ))) := by
    have h1 : (N : ℝ) ^ r_star / ((4 : ℝ) ^ r_star * (N : ℝ) ^ r_star) =
        ((4 : ℝ) ^ r_star)⁻¹ := by
      field_simp [hNr_ne]
    rw [h1, h4_eq_rpow, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hrhs : (N.choose r_star : ℝ) * (r_star : ℝ) ^ r_star /
      ((4 : ℝ) ^ r_star * (N : ℝ) ^ r_star) =
      (N.choose r_star : ℝ) * ((r_star : ℝ) / (4 * (N : ℝ))) ^ r_star := by
    rw [div_pow, mul_pow, mul_div_assoc]
  rwa [hlhs, hrhs] at hdiv

open Classical in
private lemma calibration_h_cal :
    ∀ (r_star gamma0 L eq q : ℕ) (sigma_edge p_edge : ℝ),
      (20 : ℕ) ≤ L →
        sigma_edge = (↑(eq + L + gamma0 + (2 : ℕ)) : ℝ) / (↑((2 : ℕ) ^ L * r_star - (1 : ℕ)) : ℝ) →
          q - (1 : ℕ) = (2 : ℕ) ^ eq →
            let N : ℕ := (2 : ℕ) ^ L * r_star;
            N = (2 : ℕ) ^ L * r_star →
              (0 : ℕ) < N - (1 : ℕ) →
                (0 : ℝ) < (↑(N - (1 : ℕ)) : ℝ) →
                  (∀ (k : ℕ), p_edge ^ k = (2 : ℝ) ^ (-sigma_edge * (↑k : ℝ))) →
                    (4 : ℝ) * (2 : ℝ) ^ L * (↑(q - (1 : ℕ)) : ℝ) * p_edge ^ (N - (1 : ℕ)) = (2 :
                        ℝ) ^ (-(↑gamma0 : ℝ)) := by
  classical
  intro r_star gamma0 L eq q sigma_edge p_edge hL_ge20 hsigma_def hq_sub1 N hN_def hN1_pos_nat
      hN1_pos hp_edge_pow
  have hq1_real : ((q - 1 : ℕ) : ℝ) = (2 : ℝ) ^ eq := by
    rw [hq_sub1, Nat.cast_pow, Nat.cast_ofNat]
  have hlhs1 : (4 : ℝ) * (2 : ℝ) ^ L * ((q - 1 : ℕ) : ℝ) =
      (2 : ℝ) ^ ((eq + L + 2 : ℕ) : ℝ) := by
    rw [hq1_real, show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num]
    have hp : (2 : ℝ) ^ (2 : ℕ) * (2 : ℝ) ^ L * (2 : ℝ) ^ eq = (2 : ℝ) ^ (eq + L + 2) := by
      rw [pow_add, pow_add]
      ring
    rw [hp, ← Real.rpow_natCast]
  have hlhs2 : p_edge ^ (N - 1) = (2 : ℝ) ^ (- ((eq + L + gamma0 + 2 : ℕ) : ℝ)) := by
    rw [hp_edge_pow (N - 1), hsigma_def, ← hN_def]
    congr 1
    field_simp [ne_of_gt hN1_pos]
  rw [hlhs1, hlhs2, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  push_cast
  ring

open Classical in
private lemma calibration_hσ_low :
    ∀ (r_star lam0 beta0 gamma0 L eq : ℕ) (sigma_edge : ℝ),
      beta0 = (6 : ℕ) * lam0 →
        gamma0 = (5 : ℕ) * lam0 →
          (20 : ℕ) ≤ L →
            eq = (2 : ℕ) * beta0 * (2 : ℕ) ^ L →
              sigma_edge = (↑(eq + L + gamma0 + (2 : ℕ)) : ℝ) / (↑((2 : ℕ) ^ L * r_star - (1 :
                  ℕ)) : ℝ) →
                (0 : ℕ) < r_star →
                  (18000 : ℕ) ≤ beta0 →
                    let N : ℕ := (2 : ℕ) ^ L * r_star;
                    N = (2 : ℕ) ^ L * r_star →
                      (0 : ℝ) < (↑(N - (1 : ℕ)) : ℝ) → (↑beta0 : ℝ) < sigma_edge * (↑r_star : ℝ)
                          / (2 : ℝ) := by
  classical
  intro r_star lam0 beta0 gamma0 L eq sigma_edge hbeta0_def hgamma0_def hL_ge20 heq_def
      hsigma_def hr_pos hbeta0_ge N hN_def hN1_pos
  have hnat : 2 * beta0 * (N - 1) < (eq + L + gamma0 + 2) * r_star := by
    have h1 : 2 * beta0 * (N - 1) ≤ 2 * beta0 * N :=
      Nat.mul_le_mul_left _ (Nat.sub_le N 1)
    have h2 : 2 * beta0 * N = eq * r_star := by
      rw [hN_def, heq_def]; ring
    have h3 : eq * r_star < (eq + L + gamma0 + 2) * r_star :=
      Nat.mul_lt_mul_of_pos_right (by omega) hr_pos
    omega
  have hreal : (2 : ℝ) * (beta0 : ℝ) * ((N - 1 : ℕ) : ℝ) <
      ((eq + L + gamma0 + 2 : ℕ) : ℝ) * (r_star : ℝ) := by exact_mod_cast hnat
  rw [hsigma_def, ← hN_def, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2),
    div_mul_eq_mul_div, lt_div_iff₀ hN1_pos]
  linarith only [hreal]

open Classical in
private lemma calibration_hσ_up :
    ∀ (r_star lam0 beta0 gamma0 L eq : ℕ) (sigma_edge : ℝ),
      beta0 = (6 : ℕ) * lam0 →
        eq = (2 : ℕ) * beta0 * (2 : ℕ) ^ L →
          sigma_edge = (↑(eq + L + gamma0 + (2 : ℕ)) : ℝ) / (↑((2 : ℕ) ^ L * r_star - (1 : ℕ)) :
              ℝ) →
            (3001 : ℕ) ≤ r_star →
              (18000 : ℕ) ≤ beta0 →
                (10000 : ℕ) * (L + gamma0 + (2 : ℕ)) ≤ (2 : ℕ) ^ L →
                  (1048576 : ℕ) ≤ (2 : ℕ) ^ L →
                    let N : ℕ := (2 : ℕ) ^ L * r_star;
                    N = (2 : ℕ) ^ L * r_star →
                      (1 : ℕ) ≤ N →
                        (0 : ℝ) < (↑(N - (1 : ℕ)) : ℝ) →
                          sigma_edge * (↑r_star : ℝ) / (2 : ℝ) < (10001 / 10000 : ℝ) * (↑beta0 :
                              ℝ) := by
  classical
  intro r_star lam0 beta0 gamma0 L eq sigma_edge hbeta0_def heq_def hsigma_def hr_3001 hbeta0_ge
      h2L_lg h2L_mil N hN_def hN_ge1 hN1_pos
  have hnat : 10000 * (eq + L + gamma0 + 2) * r_star < 20002 * beta0 * (N - 1) := by
    have hA : 10000 * (L + gamma0 + 2) * r_star ≤ beta0 * N := by
      have hA1 : 10000 * (L + gamma0 + 2) * r_star ≤ N := Nat.mul_le_mul_right r_star h2L_lg
      have hA2 : 1 * N ≤ beta0 * N := Nat.mul_le_mul_right N (by omega)
      omega
    have hB : 20002 * beta0 < beta0 * N := by
      have hB1 : 20002 < N := by
        rw [hN_def]
        nlinarith only [h2L_mil, hr_3001]
      nlinarith only [hbeta0_ge, hB1]
    have hN_split : N = (N - 1) + 1 := (Nat.sub_add_cancel hN_ge1).symm
    have heq_r : eq * r_star = 2 * beta0 * N := by
      rw [hN_def, heq_def]; ring
    have hexp : 10000 * (eq + L + gamma0 + 2) * r_star =
        10000 * (eq * r_star) + 10000 * (L + gamma0 + 2) * r_star := by ring
    rw [hexp, heq_r]
    nlinarith only [hA, hB, hN_split]
  have hreal : (10000 : ℝ) * ((eq + L + gamma0 + 2 : ℕ) : ℝ) * (r_star : ℝ) <
      (20002 : ℝ) * (beta0 : ℝ) * ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
  rw [hsigma_def, ← hN_def, div_lt_iff₀ (by norm_num : (0 : ℝ) < 2),
    div_mul_eq_mul_div, div_lt_iff₀ hN1_pos]
  linarith only [hreal]

open Classical in
private lemma calibration_h_qp_eq :
    ∀ (r_star gamma0 L q : ℕ) (p_edge : ℝ),
      (3001 : ℕ) ≤ r_star →
        (0 : ℝ) < (↑r_star : ℝ) →
          let N : ℕ := (2 : ℕ) ^ L * r_star;
          N = (2 : ℕ) ^ L * r_star →
            (4 : ℝ) * (2 : ℝ) ^ L * (↑(q - (1 : ℕ)) : ℝ) * p_edge ^ (N - (1 : ℕ)) = (2 : ℝ) ^
                (-(↑gamma0 : ℝ)) →
              (↑(q - (1 : ℕ)) : ℝ) * p_edge ^ (N - (1 : ℕ)) =
                (↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ)) * (2 : ℝ) ^ (-(↑gamma0 : ℝ)) := by
  classical
  intro r_star gamma0 L q p_edge hr_3001 hr_real_pos N hN_def h_cal
  have h42L_pos : (0 : ℝ) < (4 : ℝ) * (2 : ℝ) ^ L := by positivity
  have hN_cast : (N : ℝ) = (2 : ℝ) ^ L * (r_star : ℝ) := by
    rw [hN_def]; push_cast; rfl
  have hrhs1 : ((4 : ℝ) * (2 : ℝ) ^ L) * ((r_star : ℝ) / (4 * (N : ℝ))) = 1 := by
    rw [hN_cast]
    field_simp [ne_of_gt hr_real_pos, ne_of_gt h42L_pos]
  have hrhs : ((4 : ℝ) * (2 : ℝ) ^ L) *
      (((r_star : ℝ) / (4 * (N : ℝ))) * (2 : ℝ) ^ (- (gamma0 : ℝ))) =
      (2 : ℝ) ^ (- (gamma0 : ℝ)) := by
    rw [← mul_assoc, hrhs1, one_mul]
  have hlhs : ((4 : ℝ) * (2 : ℝ) ^ L) * (((q - 1 : ℕ) : ℝ) * p_edge ^ (N - 1)) =
      (2 : ℝ) ^ (- (gamma0 : ℝ)) := by
    have hmul : ((4 : ℝ) * (2 : ℝ) ^ L) * (((q - 1 : ℕ) : ℝ) * p_edge ^ (N - 1)) =
        (4 : ℝ) * (2 : ℝ) ^ L * ((q - 1 : ℕ) : ℝ) * p_edge ^ (N - 1) := by ring
    rw [hmul, h_cal]
  exact mul_left_cancel₀ (ne_of_gt h42L_pos) (hlhs.trans hrhs.symm)

open Classical in
private lemma calibration_h_base_s :
    ∀ (r_star gamma0 L q : ℕ) (p_edge : ℝ),
      let N : ℕ := (2 : ℕ) ^ L * r_star;
      (↑(q - (1 : ℕ)) : ℝ) * p_edge ^ (N - (1 : ℕ)) = (↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ)) * (2
          : ℝ) ^ (-(↑gamma0 : ℝ)) →
        ∀ (s : ℕ),
          (↑(N.choose s) : ℝ) * (↑(q - (1 : ℕ)) : ℝ) ^ s * p_edge ^ (s * (N - (1 : ℕ))) =
            (↑(N.choose s) : ℝ) * ((↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ))) ^ s * (2 : ℝ) ^
                (-(↑gamma0 : ℝ) * (↑s : ℝ)) := by
  classical
  intro r_star gamma0 L q p_edge N h_qp_eq s
  rw [mul_assoc, mul_comm s (N - 1), pow_mul, ← mul_pow, h_qp_eq, mul_pow, ← mul_assoc,
    ← Real.rpow_natCast ((2 : ℝ) ^ (- (gamma0 : ℝ))) s,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

open Classical in
private lemma calibration_h_binom_edge :
    ∀ (r_star gamma0 L q : ℕ) (p_edge : ℝ),
      let N : ℕ := (2 : ℕ) ^ L * r_star;
      (∀ (s : ℕ), (↑(N.choose s) : ℝ) * ((↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ))) ^ s ≤ (2 : ℝ) ^
          ((2 : ℝ) * (↑r_star : ℝ))) →
        (∀ (s : ℕ),
            (↑(N.choose s) : ℝ) * (↑(q - (1 : ℕ)) : ℝ) ^ s * p_edge ^ (s * (N - (1 : ℕ))) =
              (↑(N.choose s) : ℝ) * ((↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ))) ^ s * (2 : ℝ) ^
                  (-(↑gamma0 : ℝ) * (↑s : ℝ))) →
          ∀ (s : ℕ),
            (↑(N.choose s) : ℝ) * (↑(q - (1 : ℕ)) : ℝ) ^ s * p_edge ^ (s * (N - (1 : ℕ))) ≤
              (2 : ℝ) ^ ((2 : ℝ) * (↑r_star : ℝ) - (↑gamma0 : ℝ) * (↑s : ℝ)) := by
  classical
  intro r_star gamma0 L q p_edge N h_env_all h_base_s s
  rw [h_base_s s,
    show 2 * (r_star : ℝ) - (gamma0 : ℝ) * (s : ℝ) =
      2 * (r_star : ℝ) + (- (gamma0 : ℝ) * (s : ℝ)) by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_right (h_env_all s) (by positivity)

open Classical in
private lemma calibration_h_DOm_eq :
    ∀ (r_star gamma0 L q : ℕ) (sigma_edge p_edge : ℝ) (d_omega : ℕ → ℝ),
      (∀ (s : ℕ),
          d_omega s =
            (↑(((2 : ℕ) ^ L * r_star).choose s) : ℝ) * (↑(q - (1 : ℕ)) : ℝ) ^ s *
              p_edge ^ (s * ((2 : ℕ) ^ L * r_star - (1 : ℕ)) - s.choose (2 : ℕ))) →
        let N : ℕ := (2 : ℕ) ^ L * r_star;
        N = (2 : ℕ) ^ L * r_star →
          (∀ (k : ℕ), p_edge ^ k = (2 : ℝ) ^ (-sigma_edge * (↑k : ℝ))) →
            (∀ (s : ℕ),
                (↑(N.choose s) : ℝ) * (↑(q - (1 : ℕ)) : ℝ) ^ s * p_edge ^ (s * (N - (1 : ℕ))) =
                  (↑(N.choose s) : ℝ) * ((↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ))) ^ s *
                    (2 : ℝ) ^ (-(↑gamma0 : ℝ) * (↑s : ℝ))) →
              ∀ s ≤ N,
                d_omega s =
                  (↑(N.choose s) : ℝ) * ((↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ))) ^ s *
                    (2 : ℝ) ^ (-(↑gamma0 : ℝ) * (↑s : ℝ) + sigma_edge * (↑(s.choose (2 : ℕ)) :
                        ℝ)) := by
  classical
  intro r_star gamma0 L q sigma_edge p_edge d_omega hdomega_def N hN_def hp_edge_pow h_base_s s hs
  have hsub := choose_two_le_product s hs
  have hp_split : p_edge ^ (s * (N - 1) - s.choose 2) =
      p_edge ^ (s * (N - 1)) * (2 : ℝ) ^ (sigma_edge * (s.choose 2 : ℝ)) := by
    have hp1 : p_edge ^ (s * (N - 1) - s.choose 2) * p_edge ^ (s.choose 2) =
        p_edge ^ (s * (N - 1)) := by
      rw [← pow_add, Nat.sub_add_cancel hsub]
    have hp2 : p_edge ^ (s.choose 2) * (2 : ℝ) ^ (sigma_edge * (s.choose 2 : ℝ)) = 1 := by
      rw [hp_edge_pow (s.choose 2), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      have hexp0 : - sigma_edge * (s.choose 2 : ℝ) + sigma_edge * (s.choose 2 : ℝ) = 0 := by
        ring
      rw [hexp0, Real.rpow_zero]
    calc
      p_edge ^ (s * (N - 1) - s.choose 2)
        = p_edge ^ (s * (N - 1) - s.choose 2) *
            (p_edge ^ (s.choose 2) * (2 : ℝ) ^ (sigma_edge * (s.choose 2 : ℝ))) := by
              rw [hp2, mul_one]
      _ = (p_edge ^ (s * (N - 1) - s.choose 2) * p_edge ^ (s.choose 2)) *
            (2 : ℝ) ^ (sigma_edge * (s.choose 2 : ℝ)) := by ring
      _ = p_edge ^ (s * (N - 1)) * (2 : ℝ) ^ (sigma_edge * (s.choose 2 : ℝ)) := by rw [hp1]
  rw [hdomega_def s, ← hN_def, hp_split, ← mul_assoc, h_base_s s, mul_assoc,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

open Classical in
private lemma calibration_h_DOm_s :
    ∀ (r_star gamma0 L : ℕ) (sigma_edge : ℝ) (d_omega : ℕ → ℝ),
      let N : ℕ := (2 : ℕ) ^ L * r_star;
      (∀ (s : ℕ), (↑(N.choose s) : ℝ) * ((↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ))) ^ s ≤ (2 : ℝ) ^
          ((2 : ℝ) * (↑r_star : ℝ))) →
        (∀ s ≤ N,
            d_omega s =
              (↑(N.choose s) : ℝ) * ((↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ))) ^ s *
                (2 : ℝ) ^ (-(↑gamma0 : ℝ) * (↑s : ℝ) + sigma_edge * (↑(s.choose (2 : ℕ)) : ℝ))) →
          ∀ s ≤ N,
            d_omega s ≤
              (2 : ℝ) ^ ((2 : ℝ) * (↑r_star : ℝ) - (↑gamma0 : ℝ) * (↑s : ℝ) + sigma_edge *
                  (↑(s.choose (2 : ℕ)) : ℝ)) := by
  classical
  intro r_star gamma0 L sigma_edge d_omega N h_env_all h_DOm_eq s hs
  rw [h_DOm_eq s hs,
    show (2 : ℝ) ^ (2 * (r_star : ℝ) - (gamma0 : ℝ) * (s : ℝ) + sigma_edge * (s.choose 2 : ℝ)) =
      (2 : ℝ) ^ (2 * (r_star : ℝ)) *
        (2 : ℝ) ^ (- (gamma0 : ℝ) * (s : ℝ) + sigma_edge * (s.choose 2 : ℝ)) by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring]
  exact mul_le_mul_of_nonneg_right (h_env_all s) (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)

open Classical in
private lemma calibration_h_DOm_low :
    ∀ (r_star lam0 beta0 gamma0 L : ℕ) (sigma_edge : ℝ) (d_omega : ℕ → ℝ),
      (3001 : ℝ) ≤ (↑r_star : ℝ) →
        (3000 : ℝ) ≤ (↑lam0 : ℝ) →
          (↑beta0 : ℝ) = (6 : ℝ) * (↑lam0 : ℝ) →
            (↑gamma0 : ℝ) = (5 : ℝ) * (↑lam0 : ℝ) →
              let N : ℕ := (2 : ℕ) ^ L * r_star;
              r_star ≤ N →
                (2 : ℝ) ^ (-((2 : ℝ) * (↑r_star : ℝ))) ≤
                    (↑(N.choose r_star) : ℝ) * ((↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ))) ^ r_star →
                  (↑beta0 : ℝ) < sigma_edge * (↑r_star : ℝ) / (2 : ℝ) →
                    (∀ s ≤ N,
                        d_omega s =
                          (↑(N.choose s) : ℝ) * ((↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ))) ^ s *
                            (2 : ℝ) ^ (-(↑gamma0 : ℝ) * (↑s : ℝ) + sigma_edge * (↑(s.choose (2 :
                                ℕ)) : ℝ))) →
                      (2 : ℝ) ^ ((997 / 1000 : ℝ) * (↑lam0 : ℝ) * (↑r_star : ℝ)) ≤ d_omega
                          r_star := by
  classical
  intro r_star lam0 beta0 gamma0 L sigma_edge d_omega hr_real_3001 hlam0_real_ge hbeta0_real
      hgamma0_real N hr_le_N h_env_diag_low hσ_low h_DOm_eq
  rw [h_DOm_eq r_star hr_le_N]
  have hstep1 : (2 : ℝ) ^ (- (2 * (r_star : ℝ)) +
      (- (gamma0 : ℝ) * (r_star : ℝ) + sigma_edge * (r_star.choose 2 : ℝ))) ≤
      ((N.choose r_star : ℝ) * ((r_star : ℝ) / (4 * (N : ℝ))) ^ r_star) *
        (2 : ℝ) ^ (- (gamma0 : ℝ) * (r_star : ℝ) + sigma_edge * (r_star.choose 2 : ℝ)) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_right h_env_diag_low (by positivity)
  have hexp : (997 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) ≤
      - (2 * (r_star : ℝ)) +
        (- (gamma0 : ℝ) * (r_star : ℝ) + sigma_edge * (r_star.choose 2 : ℝ)) := by
    have hc2 := twice_choose_two_real r_star
    have hcr : (r_star.choose 2 : ℝ) = (r_star : ℝ) * ((r_star : ℝ) - 1) / 2 := by
      linarith only [hc2]
    rw [hcr, hgamma0_real]
    have hmul_eq : sigma_edge * ((r_star : ℝ) * ((r_star : ℝ) - 1) / 2) =
        (sigma_edge * (r_star : ℝ) / 2) * ((r_star : ℝ) - 1) := by ring
    rw [hmul_eq]
    have hlow_mul : (6 * (lam0 : ℝ)) * ((r_star : ℝ) - 1) ≤
        (sigma_edge * (r_star : ℝ) / 2) * ((r_star : ℝ) - 1) :=
      mul_le_mul_of_nonneg_right (by linarith only [hσ_low, hbeta0_real])
        (by linarith only [hr_real_3001])
    have hmargin : 6000 * (lam0 : ℝ) + 2000 * (r_star : ℝ) ≤
        3 * (lam0 : ℝ) * (r_star : ℝ) := by
      nlinarith only [hlam0_real_ge, hr_real_3001]
    linarith only [hlow_mul, hmargin]
  exact le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) hstep1

open Classical in
private lemma calibration_h_DOm_up :
    ∀ (r_star lam0 beta0 gamma0 L : ℕ) (sigma_edge : ℝ) (d_omega : ℕ → ℝ),
      (3000 : ℕ) ≤ lam0 →
        (3001 : ℕ) ≤ r_star →
          (0 : ℝ) < (↑r_star : ℝ) →
            (0 : ℝ) ≤ (↑r_star : ℝ) →
              (↑beta0 : ℝ) = (6 : ℝ) * (↑lam0 : ℝ) →
                (↑gamma0 : ℝ) = (5 : ℝ) * (↑lam0 : ℝ) →
                  let N : ℕ := (2 : ℕ) ^ L * r_star;
                  r_star ≤ N →
                    (↑(N.choose r_star) : ℝ) * ((↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ))) ^ r_star ≤
                        (1 : ℝ) →
                      (0 : ℝ) < sigma_edge →
                        sigma_edge * (↑r_star : ℝ) / (2 : ℝ) < (10001 / 10000 : ℝ) * (↑beta0 : ℝ) →
                          (∀ s ≤ N,
                              d_omega s =
                                (↑(N.choose s) : ℝ) * ((↑r_star : ℝ) / ((4 : ℝ) * (↑N : ℝ))) ^ s *
                                  (2 : ℝ) ^ (-(↑gamma0 : ℝ) * (↑s : ℝ) + sigma_edge *
                                      (↑(s.choose (2 : ℕ)) : ℝ))) →
                            d_omega r_star ≤ (2 : ℝ) ^ ((1001 / 1000 : ℝ) * (↑lam0 : ℝ) *
                                (↑r_star : ℝ)) := by
  classical
  intro r_star lam0 beta0 gamma0 L sigma_edge d_omega hlam0_ge hr_3001 hr_real_pos hr_real_nn
      hbeta0_real hgamma0_real N hr_le_N h_env_diag_up hσ_pos hσ_up h_DOm_eq
  rw [h_DOm_eq r_star hr_le_N]
  have hstep1 : ((N.choose r_star : ℝ) * ((r_star : ℝ) / (4 * (N : ℝ))) ^ r_star) *
      (2 : ℝ) ^ (- (gamma0 : ℝ) * (r_star : ℝ) + sigma_edge * (r_star.choose 2 : ℝ)) ≤
      (2 : ℝ) ^ (- (gamma0 : ℝ) * (r_star : ℝ) + sigma_edge * (r_star.choose 2 : ℝ)) := by
    simpa using mul_le_mul_of_nonneg_right h_env_diag_up
      (by positivity : (0 : ℝ) ≤
        (2 : ℝ) ^ (- (gamma0 : ℝ) * (r_star : ℝ) + sigma_edge * (r_star.choose 2 : ℝ)))
  have hexp : - (gamma0 : ℝ) * (r_star : ℝ) + sigma_edge * (r_star.choose 2 : ℝ) ≤
      (1001 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by
    have hc2 := twice_choose_two_real r_star
    have hcr_le : (r_star.choose 2 : ℝ) ≤ (r_star : ℝ) * (r_star : ℝ) / 2 := by
      linarith only [hr_real_pos, hc2]
    have hm1 : sigma_edge * (r_star.choose 2 : ℝ) ≤
        sigma_edge * ((r_star : ℝ) * (r_star : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hcr_le (le_of_lt hσ_pos)
    have hm2 : (sigma_edge * (r_star : ℝ) / 2) * (r_star : ℝ) ≤
        ((10001 / 10000 : ℝ) * (6 * (lam0 : ℝ))) * (r_star : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith only [hσ_up, hbeta0_real]) hr_real_nn
    have hring : sigma_edge * ((r_star : ℝ) * (r_star : ℝ) / 2) =
        (sigma_edge * (r_star : ℝ) / 2) * (r_star : ℝ) := by ring
    have hlr_nn : 0 ≤ (lam0 : ℝ) * (r_star : ℝ) := by positivity
    rw [hgamma0_real]
    linarith [hm1, hm2, hring, hlr_nn]
  exact le_trans hstep1 (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)

open Classical in
private lemma calibration_hp_keep_up :
    ∀ (r_star lam0 : ℕ) (d_star p_keep : ℝ) (d_omega : ℕ → ℝ),
      d_star = (2 : ℝ) ^ ((1 / 4 : ℝ) * (↑lam0 : ℝ) * (↑r_star : ℝ)) →
        p_keep = d_star / d_omega r_star →
          (2 : ℝ) ^ ((997 / 1000 : ℝ) * (↑lam0 : ℝ) * (↑r_star : ℝ)) ≤ d_omega r_star →
            p_keep ≤ (2 : ℝ) ^ (-(747 / 1000 : ℝ) * (↑lam0 : ℝ) * (↑r_star : ℝ)) := by
  classical
  intro r_star lam0 d_star p_keep d_omega hdstar_def hpkeep_def h_DOm_low
  rw [hpkeep_def, hdstar_def]
  have hdiv : (2 : ℝ) ^ ((1 / 4 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) / d_omega r_star ≤
      (2 : ℝ) ^ ((1 / 4 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) /
      (2 : ℝ) ^ ((997 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) h_DOm_low
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)] at hdiv
  refine le_trans hdiv (le_of_eq ?_)
  congr 1
  ring

open Classical in
private lemma calibration_hp_keep_lt1 :
    ∀ (r_star lam0 : ℕ) (p_keep : ℝ),
      (0 : ℝ) < (↑r_star : ℝ) →
        (0 : ℝ) < (↑lam0 : ℝ) → p_keep ≤ (2 : ℝ) ^ (-(747 / 1000 : ℝ) * (↑lam0 : ℝ) * (↑r_star :
            ℝ)) → p_keep < (1 : ℝ) := by
  classical
  intro r_star lam0 p_keep hr_real_pos hlam0_real_pos hp_keep_up
  have hlt1 : (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) < 1 := by
    rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) by norm_num]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    nlinarith only [hlam0_real_pos, hr_real_pos]
  exact lt_of_le_of_lt hp_keep_up hlt1

open Classical in
private lemma calibration_hp_keep_low :
    ∀ (r_star lam0 : ℕ) (d_star p_keep : ℝ) (d_omega : ℕ → ℝ),
      d_star = (2 : ℝ) ^ ((1 / 4 : ℝ) * (↑lam0 : ℝ) * (↑r_star : ℝ)) →
        p_keep = d_star / d_omega r_star →
          d_omega r_star ≤ (2 : ℝ) ^ ((1001 / 1000 : ℝ) * (↑lam0 : ℝ) * (↑r_star : ℝ)) →
            (0 : ℝ) < d_omega r_star → (2 : ℝ) ^ (-(751 / 1000 : ℝ) * (↑lam0 : ℝ) * (↑r_star :
                ℝ)) ≤ p_keep := by
  classical
  intro r_star lam0 d_star p_keep d_omega hdstar_def hpkeep_def h_DOm_up hDOm_r_pos
  rw [hpkeep_def, hdstar_def]
  have hdiv : (2 : ℝ) ^ ((1 / 4 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) /
      (2 : ℝ) ^ ((1001 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) ≤
      (2 : ℝ) ^ ((1 / 4 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) / d_omega r_star :=
    div_le_div_of_nonneg_left (by positivity) hDOm_r_pos h_DOm_up
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)] at hdiv
  refine le_trans (le_of_eq ?_) hdiv
  congr 1
  ring

open Classical in
private lemma calibration_hp_edge_Nchoose2 :
    ∀ (r_star gamma0 L eq : ℕ) (sigma_edge p_edge : ℝ),
      (20 : ℕ) ≤ L →
        sigma_edge = (↑(eq + L + gamma0 + (2 : ℕ)) : ℝ) / (↑((2 : ℕ) ^ L * r_star - (1 : ℕ)) : ℝ) →
          let N : ℕ := (2 : ℕ) ^ L * r_star;
          N = (2 : ℕ) ^ L * r_star →
            (3001 : ℕ) ≤ N →
              (0 : ℕ) < N - (1 : ℕ) →
                (0 : ℝ) < (↑(N - (1 : ℕ)) : ℝ) →
                  (∀ (k : ℕ), p_edge ^ k = (2 : ℝ) ^ (-sigma_edge * (↑k : ℝ))) →
                    p_edge ^ N.choose (2 : ℕ) = (2 : ℝ) ^ (-((↑N : ℝ) * (↑(eq + L + gamma0 + (2
                        : ℕ)) : ℝ) / (2 : ℝ))) := by
  classical
  intro r_star gamma0 L eq sigma_edge p_edge hL_ge20 hsigma_def N hN_def hN_ge3001 hN1_pos_nat
      hN1_pos hp_edge_pow
  rw [hp_edge_pow (N.choose 2), hsigma_def, ← hN_def]
  congr 1
  have h2N : (2 : ℝ) * (N.choose 2 : ℝ) = (N : ℝ) * ((N - 1 : ℕ) : ℝ) := by
    exact_mod_cast twice_choose_two N
  have hNc2 : (N.choose 2 : ℝ) = (N : ℝ) * ((N - 1 : ℕ) : ℝ) / 2 := by linarith only [h2N]
  rw [hNc2]
  field_simp [ne_of_gt hN1_pos]

open Classical in
private lemma calibration_hNeq_half :
    ∀ (r_star beta0 L eq : ℕ),
      eq = (2 : ℕ) * beta0 * (2 : ℕ) ^ L →
        let N : ℕ := (2 : ℕ) ^ L * r_star;
        N = (2 : ℕ) ^ L * r_star → (↑N : ℝ) * (↑eq : ℝ) / (2 : ℝ) = (↑beta0 : ℝ) * (2 : ℝ) ^ ((2
            : ℕ) * L) * (↑r_star : ℝ) := by
  classical
  intro r_star beta0 L eq heq_def N hN_def
  have hN_cast : (N : ℝ) = (2 : ℝ) ^ L * (r_star : ℝ) := by
    rw [hN_def]; push_cast; rfl
  have heq_cast : (eq : ℝ) = 2 * (beta0 : ℝ) * (2 : ℝ) ^ L := by
    rw [heq_def]; push_cast; ring
  have hpow2L : (2 : ℝ) ^ (2 * L) = (2 : ℝ) ^ L * (2 : ℝ) ^ L := by
    rw [two_mul, pow_add]
  rw [hN_cast, heq_cast, hpow2L]
  ring

open Classical in
private lemma calibration_hn0_low :
    ∀ (r_star lam0 beta0 gamma0 L eq q : ℕ) (p_edge p_keep n_0 : ℝ),
      (3000 : ℕ) ≤ lam0 →
        q = (2 : ℕ) ^ eq + (1 : ℕ) →
          n_0 = p_keep * (↑q : ℝ) ^ ((2 : ℕ) ^ L * r_star) * p_edge ^ ((2 : ℕ) ^ L *
              r_star).choose (2 : ℕ) →
            (3001 : ℕ) ≤ r_star →
              (0 : ℝ) ≤ (↑r_star : ℝ) →
                (18000 : ℕ) ≤ beta0 →
                  (18000 : ℝ) ≤ (↑beta0 : ℝ) →
                    (↑beta0 : ℝ) = (6 : ℝ) * (↑lam0 : ℝ) →
                      (10000 : ℕ) * (L + gamma0 + (2 : ℕ)) ≤ (2 : ℕ) ^ L →
                        (1048576 : ℕ) ≤ (2 : ℕ) ^ L →
                          let N : ℕ := (2 : ℕ) ^ L * r_star;
                          N = (2 : ℕ) ^ L * r_star →
                            (0 : ℝ) < p_keep →
                              (2 : ℝ) ^ (-(751 / 1000 : ℝ) * (↑lam0 : ℝ) * (↑r_star : ℝ)) ≤ p_keep →
                                p_edge ^ N.choose (2 : ℕ) =
                                    (2 : ℝ) ^ (-((↑N : ℝ) * (↑(eq + L + gamma0 + (2 : ℕ)) : ℝ) /
                                        (2 : ℝ))) →
                                  (↑N : ℝ) * (↑eq : ℝ) / (2 : ℝ) = (↑beta0 : ℝ) * (2 : ℝ) ^ ((2
                                      : ℕ) * L) * (↑r_star : ℝ) →
                                    (2 : ℝ) ^ ((99 / 100 : ℝ) * (↑beta0 : ℝ) * (2 : ℝ) ^ ((2 :
                                        ℕ) * L) * (↑r_star : ℝ)) ≤
                                      n_0 := by
  classical
  intro r_star lam0 beta0 gamma0 L eq q p_edge p_keep n_0 hlam0_ge hq_def hn0_def hr_3001
      hr_real_nn hbeta0_ge hbeta0_real_ge hbeta0_real h2L_lg h2L_mil N hN_def hp_keep_pos
      hp_keep_low hp_edge_Nchoose2 hNeq_half
  have hq_low : (2 : ℝ) ^ ((N : ℝ) * (eq : ℝ)) ≤ (q : ℝ) ^ N := by
    have hq1 : (2 : ℝ) ^ eq ≤ (q : ℝ) := by
      rw [hq_def]
      have hnat : 2 ^ eq ≤ 2 ^ eq + 1 := Nat.le_succ _
      exact_mod_cast hnat
    have hpow := pow_le_pow_left₀ (by positivity) hq1 N
    have hlhs : ((2 : ℝ) ^ eq) ^ N = (2 : ℝ) ^ ((N : ℝ) * (eq : ℝ)) := by
      rw [← pow_mul, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    rwa [hlhs] at hpow
  have hprod_low :
      (2 : ℝ) ^ (- (751 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) +
        (N : ℝ) * (eq : ℝ) +
        (- ((N : ℝ) * ((eq + L + gamma0 + 2 : ℕ) : ℝ) / 2))) ≤ n_0 := by
    rw [hn0_def, ← hN_def, hp_edge_Nchoose2, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hm1 : (2 : ℝ) ^ (- (751 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) *
        (2 : ℝ) ^ ((N : ℝ) * (eq : ℝ)) ≤ p_keep * (q : ℝ) ^ N :=
      mul_le_mul hp_keep_low hq_low (by positivity) (le_of_lt hp_keep_pos)
    exact mul_le_mul_of_nonneg_right hm1 (by positivity)
  have hexp :
      (99 / 100 : ℝ) * (beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ) ≤
        - (751 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) +
        (N : ℝ) * (eq : ℝ) +
        (- ((N : ℝ) * ((eq + L + gamma0 + 2 : ℕ) : ℝ) / 2)) := by
    have hN_cast : (N : ℝ) = (2 : ℝ) ^ L * (r_star : ℝ) := by
      rw [hN_def]; push_cast; rfl
    have hpow2L : (2 : ℝ) ^ (2 * L) = (2 : ℝ) ^ L * (2 : ℝ) ^ L := by
      rw [two_mul, pow_add]
    have hlin_real : (10000 : ℝ) * ((L : ℝ) + (gamma0 : ℝ) + 2) ≤ (2 : ℝ) ^ L := by
      exact_mod_cast h2L_lg
    have hmil_real : (1048576 : ℝ) ≤ (2 : ℝ) ^ L := by
      exact_mod_cast h2L_mil
    have h22L_ge : (1048576 : ℝ) ≤ (2 : ℝ) ^ (2 * L) := by
      rw [hpow2L]
      nlinarith only [hmil_real]
    have hterm1 : ((L : ℝ) + (gamma0 : ℝ) + 2) * (2 : ℝ) ^ L * (r_star : ℝ) / 2 ≤
        (1 / 20000 : ℝ) * (beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ) := by
      have h1 : ((L : ℝ) + (gamma0 : ℝ) + 2) * (2 : ℝ) ^ L / 2 ≤
          (1 / 20000 : ℝ) * (2 : ℝ) ^ (2 * L) := by
        rw [hpow2L]
        have h2L_nn : (0 : ℝ) ≤ (2 : ℝ) ^ L := by positivity
        nlinarith only [hlin_real, h2L_nn]
      have h2 : (1 / 20000 : ℝ) * (2 : ℝ) ^ (2 * L) ≤
          (1 / 20000 : ℝ) * (beta0 : ℝ) * (2 : ℝ) ^ (2 * L) := by
        have h22L_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * L) := by positivity
        nlinarith only [hbeta0_real_ge, h22L_nn]
      have hm := mul_le_mul_of_nonneg_right (le_trans h1 h2) hr_real_nn
      have hdiv_eq : ((L : ℝ) + (gamma0 : ℝ) + 2) * (2 : ℝ) ^ L * (r_star : ℝ) / 2 =
          ((L : ℝ) + (gamma0 : ℝ) + 2) * (2 : ℝ) ^ L / 2 * (r_star : ℝ) := by ring
      linarith only [hm, hdiv_eq]
    have hterm2 : (751 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) ≤
        (1 / 200 : ℝ) * (beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ) := by
      have hlr_nn : (0 : ℝ) ≤ (lam0 : ℝ) * (r_star : ℝ) := by positivity
      rw [hbeta0_real]
      nlinarith only [h22L_ge, hlr_nn]
    have hcast_sum : ((eq + L + gamma0 + 2 : ℕ) : ℝ) =
        (eq : ℝ) + (L : ℝ) + (gamma0 : ℝ) + 2 := by push_cast; ring
    rw [hcast_sum]
    have halg : (N : ℝ) * (eq : ℝ) +
        (- ((N : ℝ) * ((eq : ℝ) + (L : ℝ) + (gamma0 : ℝ) + 2) / 2)) =
        (N : ℝ) * (eq : ℝ) / 2 -
          ((L : ℝ) + (gamma0 : ℝ) + 2) * (2 : ℝ) ^ L * (r_star : ℝ) / 2 := by
      rw [hN_cast]
      ring
    have hX_nn : (0 : ℝ) ≤ (beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ) := by positivity
    linarith only [halg, hNeq_half, hterm1, hterm2, hX_nn]
  exact le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) hprod_low

open Classical in
private lemma calibration_hn0_up :
    ∀ (r_star beta0 gamma0 L eq q : ℕ) (p_edge p_keep n_0 : ℝ),
      (20 : ℕ) ≤ L →
        q = (2 : ℕ) ^ eq + (1 : ℕ) →
          n_0 = p_keep * (↑q : ℝ) ^ ((2 : ℕ) ^ L * r_star) * p_edge ^ ((2 : ℕ) ^ L *
              r_star).choose (2 : ℕ) →
            (3001 : ℕ) ≤ r_star →
              q - (1 : ℕ) = (2 : ℕ) ^ eq →
                let N : ℕ := (2 : ℕ) ^ L * r_star;
                N = (2 : ℕ) ^ L * r_star →
                  p_keep < (1 : ℝ) →
                    p_edge ^ N.choose (2 : ℕ) = (2 : ℝ) ^ (-((↑N : ℝ) * (↑(eq + L + gamma0 + (2
                        : ℕ)) : ℝ) / (2 : ℝ))) →
                      (↑N : ℝ) * (↑eq : ℝ) / (2 : ℝ) = (↑beta0 : ℝ) * (2 : ℝ) ^ ((2 : ℕ) * L) *
                          (↑r_star : ℝ) →
                        n_0 ≤ (2 : ℝ) ^ ((↑beta0 : ℝ) * (2 : ℝ) ^ ((2 : ℕ) * L) * (↑r_star : ℝ))
                            := by
  classical
  intro r_star beta0 gamma0 L eq q p_edge p_keep n_0 hL_ge20 hq_def hn0_def hr_3001 hq_sub1 N
      hN_def hp_keep_lt1 hp_edge_Nchoose2 hNeq_half
  have hq_up : (q : ℝ) ^ N ≤ (2 : ℝ) ^ ((N : ℝ) * ((eq : ℝ) + 1)) := by
    have hq1 : (q : ℝ) ≤ (2 : ℝ) ^ (eq + 1) := by
      rw [hq_def]
      have h1 : 1 ≤ 2 ^ eq := Nat.one_le_two_pow
      have hnat : 2 ^ eq + 1 ≤ 2 ^ (eq + 1) := by
        rw [pow_succ]
        omega
      exact_mod_cast hnat
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg q) hq1 N
    have hrhs : ((2 : ℝ) ^ (eq + 1)) ^ N = (2 : ℝ) ^ ((N : ℝ) * ((eq : ℝ) + 1)) := by
      rw [← pow_mul, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    rwa [hrhs] at hpow
  have hprod_up :
      n_0 ≤ (2 : ℝ) ^ ((N : ℝ) * ((eq : ℝ) + 1) +
        (- ((N : ℝ) * ((eq + L + gamma0 + 2 : ℕ) : ℝ) / 2))) := by
    rw [hn0_def, ← hN_def, hp_edge_Nchoose2, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hm1 : p_keep * (q : ℝ) ^ N ≤ 1 * (2 : ℝ) ^ ((N : ℝ) * ((eq : ℝ) + 1)) :=
      mul_le_mul (le_of_lt hp_keep_lt1) hq_up (by positivity) zero_le_one
    rw [one_mul] at hm1
    exact mul_le_mul_of_nonneg_right hm1 (by positivity)
  have hexp :
      (N : ℝ) * ((eq : ℝ) + 1) + (- ((N : ℝ) * ((eq + L + gamma0 + 2 : ℕ) : ℝ) / 2)) ≤
        (beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ) := by
    have hcast_sum : ((eq + L + gamma0 + 2 : ℕ) : ℝ) =
        (eq : ℝ) + (L : ℝ) + (gamma0 : ℝ) + 2 := by push_cast; ring
    rw [hcast_sum]
    have hNL_nn : (0 : ℝ) ≤ (N : ℝ) * ((L : ℝ) + (gamma0 : ℝ)) := by positivity
    linarith only [hNeq_half, hNL_nn]
  exact le_trans hprod_up (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)

open Classical in
private lemma calibration_h_M1 :
    ∀ (r_star L q : ℕ) (p_edge p_keep n_0 : ℝ),
      n_0 = p_keep * (↑q : ℝ) ^ ((2 : ℕ) ^ L * r_star) * p_edge ^ ((2 : ℕ) ^ L * r_star).choose
          (2 : ℕ) →
        let N : ℕ := (2 : ℕ) ^ L * r_star;
        N = (2 : ℕ) ^ L * r_star → ∑ x : Fin N → Fin q, p_keep * p_edge ^ (homQueries x).card =
            n_0 := by
  classical
  intro r_star L q p_edge p_keep n_0 hn0_def N hN_def
  have hcongr : ∀ x ∈ (Finset.univ : Finset (Fin N → Fin q)),
      p_keep * p_edge ^ (homQueries x).card = p_keep * p_edge ^ (N.choose 2) := by
    intro x _
    rw [homQueries_card x]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    hn0_def, ← hN_def]
  push_cast
  ring

open Classical in
private lemma calibration_h_sphere_sum :
    ∀ (r_star L q : ℕ) (p_edge p_keep n_0 : ℝ) (d_omega : ℕ → ℝ),
      (∀ (s : ℕ),
          d_omega s =
            (↑(((2 : ℕ) ^ L * r_star).choose s) : ℝ) * (↑(q - (1 : ℕ)) : ℝ) ^ s *
              p_edge ^ (s * ((2 : ℕ) ^ L * r_star - (1 : ℕ)) - s.choose (2 : ℕ))) →
        n_0 = p_keep * (↑q : ℝ) ^ ((2 : ℕ) ^ L * r_star) * p_edge ^ ((2 : ℕ) ^ L *
            r_star).choose (2 : ℕ) →
          let N : ℕ := (2 : ℕ) ^ L * r_star;
          N = (2 : ℕ) ^ L * r_star →
            (∀ (x y : Fin N → Fin q),
                (homQueries x ∪ homQueries y).card =
                  N.choose (2 : ℕ) + dHam x y * (N - (1 : ℕ)) - (dHam x y).choose (2 : ℕ)) →
              let PairSphere : ℕ → Finset ((Fin N → Fin q) × (Fin N → Fin q)) := fun (s : ℕ) =>
                {xy : (Fin N → Fin q) × (Fin N → Fin q) | dHam xy.1 xy.2 = s};
              ∀ s ≤ N,
                ∑ xy ∈ PairSphere s, p_keep ^ (2 : ℕ) * p_edge ^ (homQueries xy.1 ∪ homQueries
                    xy.2).card =
                  n_0 * p_keep * d_omega s := by
  classical
  intro r_star L q p_edge p_keep n_0 d_omega hdomega_def hn0_def N hN_def h_union_card
      PairSphere s hs
  have hsub := choose_two_le_product s hs
  have hcongr : ∀ xy ∈ PairSphere s,
      p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card =
        p_keep ^ 2 * (p_edge ^ (N.choose 2) * p_edge ^ (s * (N - 1) - s.choose 2)) := by
    intro xy hxy
    simp only [PairSphere, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
    rw [h_union_card xy.1 xy.2, hxy, Nat.add_sub_assoc hsub, pow_add]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
  have hcard : (PairSphere s).card = q ^ N * (N.choose s * (q - 1) ^ s) :=
      orderedHammingSphere_card s
  rw [hcard, hn0_def, hdomega_def s, ← hN_def]
  push_cast
  ring

open Classical in
private lemma calibration_h_M0 :
    ∀ (r_star L q : ℕ) (p_edge d_star p_keep n_0 : ℝ) (d_omega : ℕ → ℝ),
      p_keep = d_star / d_omega r_star →
        let N : ℕ := (2 : ℕ) ^ L * r_star;
        r_star ≤ N →
          (0 : ℝ) < d_omega r_star →
            (0 : ℝ) < d_star →
              (0 : ℝ) < n_0 →
                let PairSphere : ℕ → Finset ((Fin N → Fin q) × (Fin N → Fin q)) := fun (s : ℕ) =>
                  {xy : (Fin N → Fin q) × (Fin N → Fin q) | dHam xy.1 xy.2 = s};
                (∀ s ≤ N,
                    ∑ xy ∈ PairSphere s, p_keep ^ (2 : ℕ) * p_edge ^ (homQueries xy.1 ∪
                        homQueries xy.2).card =
                      n_0 * p_keep * d_omega s) →
                  ∑ xy ∈ PairSphere r_star, p_keep ^ (2 : ℕ) * p_edge ^ (homQueries xy.1 ∪
                      homQueries xy.2).card =
                    n_0 * d_star := by
  classical
  intro r_star L q p_edge d_star p_keep n_0 d_omega hpkeep_def N hr_le_N hDOm_r_pos hDStar_pos
      hn0_pos PairSphere h_sphere_sum
  rw [h_sphere_sum r_star hr_le_N, hpkeep_def]
  field_simp [ne_of_gt hDOm_r_pos]

open Classical in
private lemma calibration_h_ball_sum :
    ∀ (C₁ : ℕ),
      (3 : ℕ) ≤ C₁ →
        ∀ (r_star : ℕ),
          (1000 : ℕ) * C₁ < r_star →
            ∀ (lam0 beta0 gamma0 L q : ℕ) (sigma_edge p_edge p_keep n_0 : ℝ) (d_omega : ℕ → ℝ),
              (∀ (s : ℕ),
                  d_omega s =
                    (↑(((2 : ℕ) ^ L * r_star).choose s) : ℝ) * (↑(q - (1 : ℕ)) : ℝ) ^ s *
                      p_edge ^ (s * ((2 : ℕ) ^ L * r_star - (1 : ℕ)) - s.choose (2 : ℕ))) →
                (3001 : ℕ) ≤ r_star →
                  (0 : ℝ) ≤ (↑r_star : ℝ) →
                    (9 : ℝ) ≤ (↑(C₁ ^ (2 : ℕ)) : ℝ) →
                      (3000 : ℝ) ≤ (↑lam0 : ℝ) →
                        (↑beta0 : ℝ) = (6 : ℝ) * (↑lam0 : ℝ) →
                          let N : ℕ := (2 : ℕ) ^ L * r_star;
                          C₁ * r_star ≤ N →
                            (0 : ℝ) < sigma_edge →
                              (0 : ℝ) < p_edge →
                                sigma_edge * (↑r_star : ℝ) / (2 : ℝ) < (10001 / 10000 : ℝ) *
                                    (↑beta0 : ℝ) →
                                  (∀ s ≤ N,
                                      d_omega s ≤
                                        (2 : ℝ) ^
                                          ((2 : ℝ) * (↑r_star : ℝ) - (↑gamma0 : ℝ) * (↑s : ℝ) +
                                            sigma_edge * (↑(s.choose (2 : ℕ)) : ℝ))) →
                                    p_keep < (1 : ℝ) →
                                      (0 : ℝ) < n_0 →
                                        let PairSphere : ℕ → Finset ((Fin N → Fin q) × (Fin N →
                                            Fin q)) := fun (s : ℕ) =>
                                          {xy : (Fin N → Fin q) × (Fin N → Fin q) | dHam xy.1
                                              xy.2 = s};
                                        (∀ s ≤ N,
                                            ∑ xy ∈ PairSphere s,
                                                p_keep ^ (2 : ℕ) * p_edge ^ (homQueries xy.1 ∪
                                                    homQueries xy.2).card =
                                              n_0 * p_keep * d_omega s) →
                                          ∑ ab : (Fin N → Fin q) × (Fin N → Fin q) with
                                              ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star,
                                              p_keep ^ (2 : ℕ) * p_edge ^ (homQueries ab.1 ∪
                                                  homQueries ab.2).card ≤
                                            n_0 * (2 : ℝ) ^ ((7 : ℝ) * (↑(C₁ ^ (2 : ℕ)) : ℝ) *
                                                (↑lam0 : ℝ) * (↑r_star : ℝ)) := by
  classical
  intro C₁ hC₁ r_star hr lam0 beta0 gamma0 L q sigma_edge p_edge p_keep n_0 d_omega hdomega_def
      hr_3001 hr_real_nn hC2_real hlam0_real_ge hbeta0_real N hCr_le_N hσ_pos hp_edge_pos hσ_up
          h_DOm_s hp_keep_lt1 hn0_pos PairSphere h_sphere_sum
  have hne_iff : ∀ a b : Fin N → Fin q, a ≠ b ↔ 1 ≤ dHam a b := by
    intro a b
    constructor
    · intro hne
      have hex : ∃ v : Fin N, a v ≠ b v := by
        by_contra hall
        push Not at hall
        exact hne (funext hall)
      rcases hex with ⟨v, hv⟩
      exact Finset.card_pos.mpr ⟨v, by simp [diffCoords, hv]⟩
    · intro h1 heq
      subst heq
      have h0 : dHam a a = 0 := by simp [dHam, diffCoords]
      omega
  have hball_eq : Finset.univ.filter
      (fun ab : (Fin N → Fin q) × (Fin N → Fin q) =>
        ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star) =
      (Finset.Icc 1 (C₁ * r_star)).biUnion PairSphere := by
    ext ab
    simp only [PairSphere, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_Icc, hne_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨dHam ab.1 ab.2, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, h2⟩
  have hdisj : ((Finset.Icc 1 (C₁ * r_star) : Finset ℕ) : Set ℕ).PairwiseDisjoint PairSphere := by
    intro s₁ _ s₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro ab h₁ h₂
    simp only [PairSphere, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact hne (h₁.symm.trans h₂)
  rw [hball_eq, Finset.sum_biUnion hdisj]
  let B_term : ℝ := n_0 *
    (2 : ℝ) ^ (2 * (r_star : ℝ) +
      (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ))
  have hterm_le : ∀ s ∈ Finset.Icc 1 (C₁ * r_star),
      ∑ xy ∈ PairSphere s,
        p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card ≤ B_term := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    have hsN : s ≤ N := le_trans hs.2 hCr_le_N
    rw [h_sphere_sum s hsN]
    have hDOm_nn : 0 ≤ d_omega s := by
      rw [hdomega_def s]
      positivity
    have hgs_nn : 0 ≤ (gamma0 : ℝ) * (s : ℝ) := by positivity
    have hpDOm : p_keep * d_omega s ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) + sigma_edge * (s.choose 2 : ℝ)) := by
      calc
        p_keep * d_omega s
          ≤ 1 * d_omega s := mul_le_mul_of_nonneg_right (le_of_lt hp_keep_lt1) hDOm_nn
        _ = d_omega s := one_mul _
        _ ≤ (2 : ℝ) ^ (2 * (r_star : ℝ) - (gamma0 : ℝ) * (s : ℝ) +
              sigma_edge * (s.choose 2 : ℝ)) := h_DOm_s s hsN
        _ ≤ (2 : ℝ) ^ (2 * (r_star : ℝ) + sigma_edge * (s.choose 2 : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hgs_nn])
    have hsc2_le : (s.choose 2 : ℝ) ≤ ((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ) ^ 2 / 2 := by
      have hnat : 2 * s.choose 2 ≤ C₁ ^ 2 * r_star ^ 2 := by
        calc
          2 * s.choose 2 = s * (s - 1) := twice_choose_two s
          _ ≤ s * s := Nat.mul_le_mul_left s (Nat.sub_le s 1)
          _ ≤ (C₁ * r_star) * (C₁ * r_star) := Nat.mul_le_mul hs.2 hs.2
          _ = C₁ ^ 2 * r_star ^ 2 := by ring
      have hreal : (2 : ℝ) * (s.choose 2 : ℝ) ≤ ((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ) ^ 2 := by
        exact_mod_cast hnat
      linarith only [hreal]
    have hexp_s : 2 * (r_star : ℝ) + sigma_edge * (s.choose 2 : ℝ) ≤
        2 * (r_star : ℝ) +
          (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by
      have hm1 : sigma_edge * (s.choose 2 : ℝ) ≤
          sigma_edge * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hsc2_le (le_of_lt hσ_pos)
      have hm2 : (sigma_edge * (r_star : ℝ) / 2) * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)) ≤
          ((10001 / 10000 : ℝ) * (6 * (lam0 : ℝ))) * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith only [hσ_up, hbeta0_real]) (by positivity)
      have hr1 : sigma_edge * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ) ^ 2 / 2) =
          (sigma_edge * (r_star : ℝ) / 2) * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)) := by ring
      have hr2 : ((10001 / 10000 : ℝ) * (6 * (lam0 : ℝ))) *
          (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)) =
          (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by ring
      linarith only [hm1, hm2, hr1, hr2]
    have hrpow_s := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) hexp_s
    dsimp [B_term]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_trans hpDOm hrpow_s) (le_of_lt hn0_pos)
  have hsum_le1 : ∑ s ∈ Finset.Icc 1 (C₁ * r_star),
      (∑ xy ∈ PairSphere s,
        p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card) ≤
      ((Finset.Icc 1 (C₁ * r_star)).card : ℝ) * B_term := by
    calc
      ∑ s ∈ Finset.Icc 1 (C₁ * r_star), _
        ≤ ∑ _s ∈ Finset.Icc 1 (C₁ * r_star), B_term := Finset.sum_le_sum hterm_le
      _ = ((Finset.Icc 1 (C₁ * r_star)).card : ℝ) * B_term := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_Icc : ((Finset.Icc 1 (C₁ * r_star)).card : ℝ) ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
    have hc_eq : (Finset.Icc 1 (C₁ * r_star)).card = C₁ * r_star := by
      rw [Nat.card_Icc]
      omega
    have hr_pow : r_star ≤ 2 ^ r_star := le_of_lt Nat.lt_two_pow_self
    have hCr_le_pow : C₁ * r_star ≤ 2 ^ (2 * r_star) := by
      calc
        C₁ * r_star ≤ r_star * r_star := Nat.mul_le_mul_right r_star (by omega)
        _ ≤ 2 ^ r_star * 2 ^ r_star := Nat.mul_le_mul hr_pow hr_pow
        _ = 2 ^ (r_star + r_star) := (pow_add 2 r_star r_star).symm
        _ = 2 ^ (2 * r_star) := by rw [two_mul]
    rw [hc_eq]
    have hcast : ((C₁ * r_star : ℕ) : ℝ) ≤ ((2 ^ (2 * r_star) : ℕ) : ℝ) := by
      exact_mod_cast hCr_le_pow
    have hpow_eq : ((2 ^ (2 * r_star) : ℕ) : ℝ) = (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hcast, hpow_eq]
  have hB_nn : 0 ≤ B_term := by dsimp [B_term]; positivity
  have hsum_le2 : ((Finset.Icc 1 (C₁ * r_star)).card : ℝ) * B_term ≤
      n_0 * (2 : ℝ) ^ (4 * (r_star : ℝ) +
        (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_right hcard_Icc hB_nn
    have hrew : (2 : ℝ) ^ (2 * (r_star : ℝ)) * B_term =
        n_0 * (2 : ℝ) ^ (4 * (r_star : ℝ) +
          (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) := by
      dsimp [B_term]
      have hcomm : (2 : ℝ) ^ (2 * (r_star : ℝ)) *
          (n_0 * (2 : ℝ) ^ (2 * (r_star : ℝ) +
            (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ))) =
          n_0 * ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
            (2 : ℝ) ^ (2 * (r_star : ℝ) +
              (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ))) := by ring
      rw [hcomm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring
    rwa [hrew] at hm
  have hexp_final :
      4 * (r_star : ℝ) +
        (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ) ≤
        (7 * (C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by
    have hcast7 : (7 * (C₁ ^ 2 : ℕ) : ℝ) = 7 * ((C₁ ^ 2 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast7]
    have hprod : (27000 : ℝ) ≤ ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) := by
      nlinarith only [hC2_real, hlam0_real_ge]
    have h4_le : 4 * (r_star : ℝ) ≤
        (9994 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by
      have hc : (4 : ℝ) ≤ (9994 / 10000 : ℝ) * (((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ)) := by
        linarith only [hprod]
      have hm := mul_le_mul_of_nonneg_right hc hr_real_nn
      have hr1 : (9994 / 10000 : ℝ) * (((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ)) * (r_star : ℝ) =
          (9994 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by ring
      linarith only [hm, hr1]
    linarith only [h4_le]
  have hsum_le3 : n_0 *
      (2 : ℝ) ^ (4 * (r_star : ℝ) +
        (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) ≤
      n_0 * (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_final) (le_of_lt hn0_pos)
  exact le_trans hsum_le1 (le_trans hsum_le2 hsum_le3)

private lemma dyadicCalibration_core (C₁ : ℕ) (hC₁ : 3 ≤ C₁)
    (r_star : ℕ) (hr : 1000 * C₁ < r_star) : ∀ (lam0 beta0 gamma0 L eq q : ℕ)
    (sigma_edge p_edge d_star p_keep n_0 : ℝ) (d_omega : ℕ → ℝ),
    3000 ≤ lam0 →
    beta0 = 6 * lam0 →
    gamma0 = 5 * lam0 →
    20 ≤ L →
    C₁ ≤ L →
    gamma0 ≤ L →
    eq = 2 * beta0 * 2 ^ L →
    q = 2 ^ eq + 1 →
    sigma_edge = ((eq + L + gamma0 + 2 : ℕ) : ℝ) / ((2 ^ L * r_star - 1 : ℕ) : ℝ) →
    p_edge = (2 : ℝ) ^ (- sigma_edge) →
    (∀ s : ℕ, d_omega s = ((2 ^ L * r_star).choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s *
      p_edge ^ (s * (2 ^ L * r_star - 1) - s.choose 2)) →
    d_star = (2 : ℝ) ^ ((1 / 4 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) →
    p_keep = d_star / d_omega r_star →
    n_0 = p_keep * ((q : ℝ) ^ (2 ^ L * r_star)) * p_edge ^ ((2 ^ L * r_star).choose 2) →
    0 < sigma_edge ∧
    0 < p_edge ∧ p_edge < 1 ∧
    (4 : ℝ) * (2 : ℝ) ^ L * ((q - 1 : ℕ) : ℝ) *
      p_edge ^ (2 ^ L * r_star - 1) = (2 : ℝ) ^ (- (gamma0 : ℝ)) ∧
    (beta0 : ℝ) < sigma_edge * (r_star : ℝ) / 2 ∧
    sigma_edge * (r_star : ℝ) / 2 < (10001 / 10000 : ℝ) * (beta0 : ℝ) ∧
    (∀ s : ℕ, ((2 ^ L * r_star).choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s *
      p_edge ^ (s * (2 ^ L * r_star - 1)) ≤
      (2 : ℝ) ^ (2 * (r_star : ℝ) - (gamma0 : ℝ) * (s : ℝ))) ∧
    (∀ s : ℕ, s ≤ 2 ^ L * r_star →
      d_omega s ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) - (gamma0 : ℝ) * (s : ℝ) + sigma_edge * (s.choose 2 : ℝ))) ∧
    (2 : ℝ) ^ ((997 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) ≤ d_omega r_star ∧
    d_omega r_star ≤
      (2 : ℝ) ^ ((1001 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) ∧
    0 < p_keep ∧ p_keep < 1 ∧
    p_keep ≤ (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) ∧
    (2 : ℝ) ^ ((99 / 100 : ℝ) * (beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ)) ≤ n_0 ∧
    n_0 ≤ (2 : ℝ) ^ ((beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ)) ∧
    (∀ x : Fin (2 ^ L * r_star) → Fin q,
      (homQueries x).card = (2 ^ L * r_star).choose 2) ∧
    (∀ x y : Fin (2 ^ L * r_star) → Fin q,
      (homQueries x ∪ homQueries y).card =
        (2 ^ L * r_star).choose 2 +
          dHam x y * (2 ^ L * r_star - 1) - (dHam x y).choose 2) ∧
    (∀ (x : Fin (2 ^ L * r_star) → Fin q) (s : ℕ),
      (Finset.univ.filter (fun y => dHam x y = s)).card =
        (2 ^ L * r_star).choose s * (q - 1) ^ s) ∧
    (∑ x : Fin (2 ^ L * r_star) → Fin q,
      p_keep * p_edge ^ (homQueries x).card = n_0) ∧
    (∑ xy ∈ Finset.univ.filter
        (fun xy : (Fin (2 ^ L * r_star) → Fin q) ×
                  (Fin (2 ^ L * r_star) → Fin q) => dHam xy.1 xy.2 = r_star),
      p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card =
        n_0 * d_star) ∧
    (∑ ab ∈ Finset.univ.filter
        (fun ab : (Fin (2 ^ L * r_star) → Fin q) ×
                  (Fin (2 ^ L * r_star) → Fin q) =>
          ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star),
      p_keep ^ 2 * p_edge ^ (homQueries ab.1 ∪ homQueries ab.2).card ≤
        n_0 * (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ))) := by
  intro lam0 beta0 gamma0 L eq q sigma_edge p_edge d_star p_keep n_0 d_omega
    hlam0_ge hbeta0_def hgamma0_def hL_ge20 hC1_le_L hgamma0_le_L
    heq_def hq_def hsigma_def hpedge_def hdomega_def
    hdstar_def hpkeep_def hn0_def
  have hr_3001 : 3001 ≤ r_star := by omega
  have hr_pos : 0 < r_star := by omega
  have hr_real_pos : (0 : ℝ) < (r_star : ℝ) := by exact_mod_cast hr_pos
  have hr_real_nn : (0 : ℝ) ≤ (r_star : ℝ) := le_of_lt hr_real_pos
  have hr_real_3001 : (3001 : ℝ) ≤ (r_star : ℝ) := by exact_mod_cast hr_3001
  have hC2 : 9 ≤ C₁ ^ 2 := by nlinarith only [hC₁]
  have hC2_real : (9 : ℝ) ≤ ((C₁ ^ 2 : ℕ) : ℝ) := by exact_mod_cast hC2
  have hlam0_real_ge : (3000 : ℝ) ≤ (lam0 : ℝ) := by exact_mod_cast hlam0_ge
  have hlam0_real_pos : (0 : ℝ) < (lam0 : ℝ) := by linarith only [hlam0_real_ge]
  have hbeta0_ge : 18000 ≤ beta0 := by omega
  have hbeta0_real_ge : (18000 : ℝ) ≤ (beta0 : ℝ) := by exact_mod_cast hbeta0_ge
  have hbeta0_real : (beta0 : ℝ) = 6 * (lam0 : ℝ) := by rw [hbeta0_def]; push_cast; ring
  have hgamma0_real : (gamma0 : ℝ) = 5 * (lam0 : ℝ) := by rw [hgamma0_def]; push_cast; ring
  have h2L_lin : 20000 * (L + 2) ≤ 2 ^ L := dyadic_linear_growth L hL_ge20
  have h2L_lg : 10000 * (L + gamma0 + 2) ≤ 2 ^ L := by omega
  have h2L_mil : 1048576 ≤ 2 ^ L := by
    calc
      1048576 = 2 ^ 20 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL_ge20
  have hC1_le_2L : C₁ ≤ 2 ^ L := le_trans hC1_le_L (le_of_lt Nat.lt_two_pow_self)
  have hq_sub1 : q - 1 = 2 ^ eq := by
    rw [hq_def]
    exact Nat.add_sub_cancel _ _
  let N : ℕ := 2 ^ L * r_star
  have hN_def : N = 2 ^ L * r_star := rfl
  have hN_ge3001 : 3001 ≤ N := by
    rw [hN_def]
    nlinarith only [h2L_mil, hr_3001]
  have hN_ge1 : 1 ≤ N := by omega
  have hr_le_N : r_star ≤ N := by
    rw [hN_def]
    nlinarith only [h2L_mil, hr_3001]
  have hCr_le_N : C₁ * r_star ≤ N := Nat.mul_le_mul_right r_star hC1_le_2L
  have hN1_pos_nat : 0 < N - 1 := by omega
  have hN1_pos : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hN1_pos_nat
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have h_union_card := @homQueries_union_card N q hN_ge1
  have h4_eq_rpow : (4 : ℝ) ^ r_star = (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
    have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h4, ← pow_mul, ← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat]
  have h_upper_s : ∀ s : ℕ,
      (N.choose s : ℝ) * ((r_star : ℝ) / (4 * (N : ℝ))) ^ s ≤ (4 : ℝ) ^ r_star / (4 : ℝ) ^ s :=
    @calibration_h_upper_s r_star L hr_3001 hr_real_nn hN_pos
  have h_env_all :=
    @calibration_h_env_all r_star L h4_eq_rpow h_upper_s
  have h_env_diag_up : (N.choose r_star : ℝ) * ((r_star : ℝ) / (4 * (N : ℝ))) ^ r_star ≤ 1 := by
    have hdiv1 : (4 : ℝ) ^ r_star / (4 : ℝ) ^ r_star = 1 :=
      div_self (ne_of_gt (by positivity : (0 : ℝ) < (4 : ℝ) ^ r_star))
    simpa [hdiv1] using h_upper_s r_star
  have h_env_diag_low :=
    @calibration_h_env_diag_low r_star L hr_3001 hr_le_N hN_pos h4_eq_rpow
  have hσ_pos : 0 < sigma_edge := by
    rw [hsigma_def, ← hN_def]
    have hnum : (0 : ℝ) < ((eq + L + gamma0 + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < eq + L + gamma0 + 2 by omega)
    exact div_pos hnum hN1_pos
  have hp_edge_pos : 0 < p_edge := by
    rw [hpedge_def]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hp_edge_lt1 : p_edge < 1 := by
    rw [hpedge_def, show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) by norm_num]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith only [hσ_pos])
  have hp_edge_pow : ∀ k : ℕ, p_edge ^ k = (2 : ℝ) ^ (- sigma_edge * (k : ℝ)) := by
    intro k
    rw [hpedge_def, ← Real.rpow_natCast _ k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h_cal :=
    @calibration_h_cal r_star gamma0 L eq q sigma_edge p_edge hL_ge20 hsigma_def hq_sub1
        hN_def hN1_pos_nat hN1_pos hp_edge_pow
  have hσ_low :=
    @calibration_hσ_low r_star lam0 beta0 gamma0 L eq sigma_edge hbeta0_def hgamma0_def
        hL_ge20 heq_def hsigma_def hr_pos hbeta0_ge hN_def hN1_pos
  have hσ_up :=
    @calibration_hσ_up r_star lam0 beta0 gamma0 L eq sigma_edge hbeta0_def heq_def hsigma_def
        hr_3001 hbeta0_ge h2L_lg h2L_mil hN_def hN_ge1 hN1_pos
  have h_qp_eq :=
    @calibration_h_qp_eq r_star gamma0 L q p_edge hr_3001 hr_real_pos hN_def h_cal
  have h_base_s :=
    @calibration_h_base_s r_star gamma0 L q p_edge h_qp_eq
  have h_binom_edge :=
    @calibration_h_binom_edge r_star gamma0 L q p_edge h_env_all h_base_s
  have h_DOm_eq :=
    @calibration_h_DOm_eq r_star gamma0 L q sigma_edge p_edge d_omega hdomega_def hN_def
        hp_edge_pow h_base_s
  have h_DOm_s :=
    @calibration_h_DOm_s r_star gamma0 L sigma_edge d_omega h_env_all h_DOm_eq
  have h_DOm_low :=
    @calibration_h_DOm_low r_star lam0 beta0 gamma0 L sigma_edge d_omega hr_real_3001
        hlam0_real_ge hbeta0_real hgamma0_real hr_le_N h_env_diag_low hσ_low h_DOm_eq
  have h_DOm_up :=
    @calibration_h_DOm_up r_star lam0 beta0 gamma0 L sigma_edge d_omega hlam0_ge hr_3001
        hr_real_pos hr_real_nn hbeta0_real hgamma0_real hr_le_N h_env_diag_up hσ_pos hσ_up
        h_DOm_eq
  have hDOm_r_pos : 0 < d_omega r_star := lt_of_lt_of_le (by positivity) h_DOm_low
  have hDStar_pos : 0 < d_star := by
    rw [hdstar_def]; positivity
  have hp_keep_pos : 0 < p_keep := by
    rw [hpkeep_def]; exact div_pos hDStar_pos hDOm_r_pos
  have hp_keep_up :=
    @calibration_hp_keep_up r_star lam0 d_star p_keep d_omega hdstar_def hpkeep_def h_DOm_low
  have hp_keep_lt1 :=
    @calibration_hp_keep_lt1 r_star lam0 p_keep hr_real_pos hlam0_real_pos hp_keep_up
  have hp_keep_low :=
    @calibration_hp_keep_low r_star lam0 d_star p_keep d_omega hdstar_def hpkeep_def h_DOm_up
        hDOm_r_pos
  have hp_edge_Nchoose2 :=
    @calibration_hp_edge_Nchoose2 r_star gamma0 L eq sigma_edge p_edge hL_ge20 hsigma_def
        hN_def hN_ge3001 hN1_pos_nat hN1_pos hp_edge_pow
  have hNeq_half :=
    @calibration_hNeq_half r_star beta0 L eq heq_def hN_def
  have hn0_low :=
    @calibration_hn0_low r_star lam0 beta0 gamma0 L eq q p_edge p_keep n_0 hlam0_ge hq_def
        hn0_def hr_3001 hr_real_nn hbeta0_ge hbeta0_real_ge hbeta0_real h2L_lg h2L_mil hN_def
        hp_keep_pos hp_keep_low hp_edge_Nchoose2 hNeq_half
  have hn0_up :=
    @calibration_hn0_up r_star beta0 gamma0 L eq q p_edge p_keep n_0 hL_ge20 hq_def hn0_def
        hr_3001 hq_sub1 hN_def hp_keep_lt1 hp_edge_Nchoose2 hNeq_half
  have hn0_pos : 0 < n_0 := lt_of_lt_of_le (by positivity) hn0_low
  have h_M1 :=
    @calibration_h_M1 r_star L q p_edge p_keep n_0 hn0_def hN_def
  let PairSphere : ℕ → Finset ((Fin N → Fin q) × (Fin N → Fin q)) :=
    fun s => Finset.univ.filter (fun xy => dHam xy.1 xy.2 = s)
  have h_sphere_sum :=
    @calibration_h_sphere_sum r_star L q p_edge p_keep n_0 d_omega hdomega_def hn0_def hN_def
        h_union_card
  have h_M0 :=
    @calibration_h_M0 r_star L q p_edge d_star p_keep n_0 d_omega hpkeep_def hr_le_N
        hDOm_r_pos hDStar_pos hn0_pos h_sphere_sum
  have h_ball_sum :=
    @calibration_h_ball_sum C₁ hC₁ r_star hr lam0 beta0 gamma0 L q sigma_edge p_edge p_keep
        n_0 d_omega hdomega_def hr_3001 hr_real_nn hC2_real hlam0_real_ge hbeta0_real hCr_le_N
            hσ_pos hp_edge_pos hσ_up h_DOm_s hp_keep_lt1 hn0_pos h_sphere_sum
  exact ⟨hσ_pos, hp_edge_pos, hp_edge_lt1, h_cal, hσ_low, hσ_up,
    h_binom_edge, h_DOm_s, h_DOm_low, h_DOm_up,
    hp_keep_pos, hp_keep_lt1, hp_keep_up,
    hn0_low, hn0_up,
    homQueries_card, h_union_card, hammingSphere_card,
    h_M1, h_M0, h_ball_sum⟩

theorem csp_dyadic_calibration_and_first_moments (C₁ : ℕ) (hC₁ : 3 ≤ C₁) (r_star : ℕ) (hr : 1000
    * C₁ < r_star) :
    0 < cspSigmaEdge C₁ r_star ∧
    0 < cspPEdge C₁ r_star ∧ cspPEdge C₁ r_star < 1 ∧
    (4 : ℝ) * (2 : ℝ) ^ cspL C₁ * ((cspQ C₁ - 1 : ℕ) : ℝ) *
      (cspPEdge C₁ r_star) ^ (2 ^ cspL C₁ * r_star - 1) = (2 : ℝ) ^ (- (cspGamma0 C₁ : ℝ)) ∧
    (cspBeta0 C₁ : ℝ) < cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 ∧
    cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 < (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ) ∧
    (∀ s : ℕ, ((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
      (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1)) ≤
      (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ))) ∧
    (∀ s : ℕ, s ≤ 2 ^ cspL C₁ * r_star →
      cspDOmega C₁ r_star s ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ) +
          cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ))) ∧
    (2 : ℝ) ^ ((997 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ≤ cspDOmega C₁ r_star r_star ∧
    cspDOmega C₁ r_star r_star ≤
      (2 : ℝ) ^ ((1001 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ∧
    0 < cspPKeep C₁ r_star ∧ cspPKeep C₁ r_star < 1 ∧
    cspPKeep C₁ r_star ≤ (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ∧
    (2 : ℝ) ^ ((99 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) ≤
      cspN0 C₁ r_star ∧
    cspN0 C₁ r_star ≤
      (2 : ℝ) ^ ((cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) ∧
    (∀ x : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      (homQueries x).card = (2 ^ cspL C₁ * r_star).choose 2) ∧
    (∀ x y : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      (homQueries x ∪ homQueries y).card =
        (2 ^ cspL C₁ * r_star).choose 2 +
          dHam x y * (2 ^ cspL C₁ * r_star - 1) - (dHam x y).choose 2) ∧
    (∀ (x : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) (s : ℕ),
      (Finset.univ.filter (fun y => dHam x y = s)).card =
        (2 ^ cspL C₁ * r_star).choose s * (cspQ C₁ - 1) ^ s) ∧
    (∑ x : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      cspPKeep C₁ r_star * (cspPEdge C₁ r_star) ^ (homQueries x).card = cspN0 C₁ r_star) ∧
    (∑ xy ∈ Finset.univ.filter
        (fun xy : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                  (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) => dHam xy.1 xy.2 = r_star),
      (cspPKeep C₁ r_star) ^ 2 * (cspPEdge C₁ r_star) ^ (homQueries xy.1 ∪ homQueries xy.2).card =
        cspN0 C₁ r_star * cspDStar C₁ r_star) ∧
    (∑ ab ∈ Finset.univ.filter
        (fun ab : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                  (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
          ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star),
      (cspPKeep C₁ r_star) ^ 2 * (cspPEdge C₁ r_star) ^ (homQueries ab.1 ∪ homQueries ab.2).card ≤
        cspN0 C₁ r_star *
          (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) :=
by
  have h_core := dyadicCalibration_core C₁ hC₁ r_star hr
  have hlam0_1000C1 : 1000 * C₁ ≤ cspLam0 C₁ := (lam0_ge_1000_C1 C₁ hC₁).2.1
  have hlam0_ge : 3000 ≤ cspLam0 C₁ := by omega
  have hL_ge20 : 20 ≤ cspL C₁ := Nat.le_add_right 20 _
  have hL_ge_lam : 1600 * cspLam0 C₁ ≤ cspL C₁ := by
    have hsq : 1 ≤ C₁ ^ 2 := Nat.one_le_pow 2 C₁ (by omega)
    unfold cspL cspInvEta0
    nlinarith only [hsq]
  have hC1_le_L : C₁ ≤ cspL C₁ := by omega
  have hgamma0_le_L : cspGamma0 C₁ ≤ cspL C₁ := by
    unfold cspGamma0
    omega
  exact h_core
    (cspLam0 C₁) (cspBeta0 C₁) (cspGamma0 C₁) (cspL C₁) (cspEq C₁) (cspQ C₁)
    (cspSigmaEdge C₁ r_star) (cspPEdge C₁ r_star) (cspDStar C₁ r_star)
    (cspPKeep C₁ r_star) (cspN0 C₁ r_star) (cspDOmega C₁ r_star)
    hlam0_ge rfl rfl hL_ge20 hC1_le_L hgamma0_le_L rfl rfl rfl rfl (fun _ => rfl) rfl rfl rfl

end Helpers

end HighDimSteinerSpanners.Proofs.CSP
