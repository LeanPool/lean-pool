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

public import LeanPool.SteinerSpanners.CSP.Calibration

/-! # Witness Moments for spanner CSP codes

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib.
-/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners.Proofs.CSP

noncomputable section Helpers

theorem incidentQueryCardinality : ∀ {N : ℕ} (S : Finset (Fin N)),
    2 * ((S.card : ℤ) * ((N - 1 : ℕ) : ℤ) - ((candA1 S).card : ℤ)) ≤ (S.card : ℤ) ^ 2 := by
  intro N S
  let Ord : Finset (Fin N × Fin N) :=
    S.biUnion (fun u => ((Finset.univ : Finset (Fin N)).erase u).image (fun v => (u, v)))
  have hOrd_card : Ord.card = S.card * (N - 1) := by
    rw [Finset.card_biUnion]
    · have h_inner : ∀ u ∈ S,
          (((Finset.univ : Finset (Fin N)).erase u).image (fun v => (u, v))).card = N - 1 := by
        intro u _
        rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
          Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_fin]
      rw [Finset.sum_congr rfl h_inner, Finset.sum_const, smul_eq_mul]
    · intro u₁ _ u₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hp2 with ⟨_, _, hp⟩
      exact hne (Prod.mk.inj hp).1.symm
  let B_lt : Finset (Fin N × Fin N) := (S ×ˢ S).filter (fun uv => uv.1 < uv.2)
  let B_gt : Finset (Fin N × Fin N) := (S ×ˢ S).filter (fun uv => uv.2 < uv.1)
  let g : Fin N × Fin N → (Fin N × Fin N) ⊕ (Fin N × Fin N) :=
    fun ab =>
      if ab.1 < ab.2 then Sum.inl ab
      else if ab.2 ∈ S then Sum.inr (ab.2, ab.1)
      else Sum.inl (ab.2, ab.1)
  have hOrd_le : Ord.card ≤ (candA1 S).card + B_lt.card := by
    rw [← Finset.card_disjSum]
    apply Finset.card_le_card_of_injOn g
    · intro ab hab_mem
      simp only [Ord, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_erase, Finset.mem_univ, and_true] at hab_mem
      rcases hab_mem with ⟨a₀, ha₀, b₀, hba, rfl⟩
      dsimp [g]
      split_ifs with hlt hbS
      · simp only [Finset.mem_coe, Finset.mem_disjSum]
        refine Or.inl ⟨(a₀, b₀), ?_, rfl⟩
        simp only [candA1, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hlt, Or.inl ha₀⟩
      · simp only [Finset.mem_coe, Finset.mem_disjSum]
        refine Or.inr ⟨(b₀, a₀), ?_, rfl⟩
        simp only [B_lt, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hbS, ha₀⟩, lt_of_le_of_ne (not_lt.mp hlt) hba⟩
      · simp only [Finset.mem_coe, Finset.mem_disjSum]
        refine Or.inl ⟨(b₀, a₀), ?_, rfl⟩
        simp only [candA1, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨lt_of_le_of_ne (not_lt.mp hlt) hba, Or.inr ha₀⟩
    · intro ab₁ h₁ ab₂ h₂ heq
      simp only [Ord, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_erase, Finset.mem_univ, and_true] at h₁ h₂
      rcases h₁ with ⟨a₁, ha₁, b₁, _, rfl⟩
      rcases h₂ with ⟨a₂, ha₂, b₂, _, rfl⟩
      dsimp [g] at heq
      by_cases hlt₁ : a₁ < b₁ <;> by_cases hlt₂ : a₂ < b₂
      · rw [ite_eq_left hlt₁, ite_eq_left hlt₂] at heq
        exact Sum.inl.inj heq
      · rw [ite_eq_left hlt₁, ite_eq_right hlt₂] at heq
        by_cases hb₂ : b₂ ∈ S
        · rw [ite_eq_left hb₂] at heq
          cases heq
        · rw [ite_eq_right hb₂] at heq
          rcases Prod.mk.inj (Sum.inl.inj heq) with ⟨rfl, _⟩
          exact absurd ha₁ hb₂
      · rw [ite_eq_right hlt₁, ite_eq_left hlt₂] at heq
        by_cases hb₁ : b₁ ∈ S
        · rw [ite_eq_left hb₁] at heq
          cases heq
        · rw [ite_eq_right hb₁] at heq
          rcases Prod.mk.inj (Sum.inl.inj heq) with ⟨rfl, _⟩
          exact absurd ha₂ hb₁
      · rw [ite_eq_right hlt₁, ite_eq_right hlt₂] at heq
        by_cases hb₁ : b₁ ∈ S <;> by_cases hb₂ : b₂ ∈ S
        · rw [ite_eq_left hb₁, ite_eq_left hb₂] at heq
          rcases Prod.mk.inj (Sum.inr.inj heq) with ⟨rfl, rfl⟩
          rfl
        · rw [ite_eq_left hb₁, ite_eq_right hb₂] at heq
          cases heq
        · rw [ite_eq_right hb₁, ite_eq_left hb₂] at heq
          cases heq
        · rw [ite_eq_right hb₁, ite_eq_right hb₂] at heq
          rcases Prod.mk.inj (Sum.inl.inj heq) with ⟨rfl, rfl⟩
          rfl
  have hB_swap : B_lt.card ≤ B_gt.card := by
    apply Finset.card_le_card_of_injOn Prod.swap
    · intro uv huv
      simp only [B_lt, B_gt, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Prod.swap]
          at huv ⊢
      exact ⟨⟨huv.1.2, huv.1.1⟩, huv.2⟩
    · intro uv₁ _ uv₂ _ heq
      exact Prod.swap_injective heq
  have hB_disj : Disjoint B_lt B_gt := by
    rw [Finset.disjoint_left]
    intro uv h₁ h₂
    simp only [B_lt, B_gt, Finset.mem_filter] at h₁ h₂
    exact lt_asymm h₁.2 h₂.2
  have hB_sub : B_lt ∪ B_gt ⊆ S ×ˢ S :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hB_two : 2 * B_lt.card ≤ S.card ^ 2 := by
    have hc := Finset.card_le_card hB_sub
    rw [Finset.card_union_of_disjoint hB_disj, Finset.card_product, ← sq] at hc
    omega
  have hnat : 2 * (S.card * (N - 1)) ≤ 2 * (candA1 S).card + S.card ^ 2 := by
    omega
  have hint : ((2 * (S.card * (N - 1)) : ℕ) : ℤ) ≤
      ((2 * (candA1 S).card + S.card ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast hnat
  push_cast at hint
  linarith

theorem candidateQueriesFreshAndSupported : ∀ {N q : ℕ} (C₁ r_star m : ℕ), 3 ≤ C₁ → 1000 * C₁ <
    r_star →
    ∀ (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q),
    x ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev →
    candMFresh a b m z_prev x ⊆ disagreeSet x a ∩ disagreeSet x b ∧
    (∀ w ∈ candMWit C₁ r_star a b m z_prev x, candQCand C₁ a b m z_prev x w ⊆
      cspUCand a b (m + 1) (Fin.snoc z_prev x) \ cspUCand a b m z_prev) ∧
    (∀ ω : cspIota N q → Bool, ω (Sum.inr x) = true →
      x ∈ bicliqueWitnessList (symROf ω) C₁ r_star a b →
      ∃ w ∈ candMWit C₁ r_star a b m z_prev x, ∀ i ∈ candQCand C₁ a b m z_prev x w, ω i = true) ∧
    (∀ w, ∀ (p_edge p_keep : ℝ),
      ∏ i ∈ candQCand C₁ a b m z_prev x w, Sum.elim (fun _ => p_edge) (fun _ => p_keep) i =
        p_keep * p_edge ^ ((candA1 (candMFresh a b m z_prev x)).card +
          (candA2 C₁ a b x (candMFresh a b m z_prev x) w).card)) := by
  intro N q C₁ r_star m hC₁_loc hr_loc a b z_prev x hx
  have hx_sdiff := Finset.mem_sdiff.mp hx
  have hx_pool := hx_sdiff.1
  simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at hx_pool
  rcases hx_pool with ⟨hx_ne_a, hx_ne_b, hd_xa, hd_xb⟩
  have hx_not_img : ∀ t : Fin m, z_prev t ≠ x :=
    fun t ht => hx_sdiff.2 (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, ht⟩)
  let R_old := cspRvc a b m z_prev
  let R_new := cspRvc a b (m + 1) (Fin.snoc z_prev x)
  let S := candMFresh a b m z_prev x
  let W_ab := disagreeSet x a ∪ disagreeSet x b
  have ha_old : ∀ v : Fin N, (v, a v) ∈ R_old := by
    intro v
    simp only [R_old, cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inl ⟨v, rfl⟩)
  have hb_old : ∀ v : Fin N, (v, b v) ∈ R_old := by
    intro v
    simp only [R_old, cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inr ⟨v, rfl⟩)
  have hcstar_old : ∀ v : Fin N, (v, activeColor x a b v) ∈ R_old := by
    intro v
    unfold activeColor
    split_ifs
    · exact ha_old v
    · exact hb_old v
  have hcstar_ne : ∀ v ∈ W_ab, activeColor x a b v ≠ x v := by
    intro v hv
    simp only [W_ab, disagreeSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        at hv
    unfold activeColor
    split_ifs with hax
    · exact hax
    · push Not at hax
      rcases hv with h1 | h2
      · exact absurd hax.symm h1
      · exact Ne.symm h2
  have hold_sub_new : R_old ⊆ R_new := by
    intro vc hvc
    simp only [R_old, R_new, cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_biUnion] at hvc ⊢
    rcases hvc with (h | h) | ⟨t, v, rfl⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨t.castSucc, v, by simp [Fin.snoc_castSucc]⟩
  have hx_new : ∀ v : Fin N, (v, x v) ∈ R_new := by
    intro v
    simp only [R_new, cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_biUnion]
    exact Or.inr ⟨Fin.last m, v, by simp [Fin.snoc_last]⟩
  have hPhi1_inj : Function.Injective (candPhi1 x) := by
    rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ heq
    simp only [candPhi1, Prod.mk.injEq] at heq
    exact Prod.ext heq.1 heq.2.1
  have hPhi2_injOn : ∀ w, Set.InjOn (candPhi2 a b x) (candA2 C₁ a b x S w) := by
    intro w ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ heq
    simp only [candA2, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at h₁ h₂
    have hu₁_not : (u₁, x u₁) ∉ R_old := by
      have hS₁ := h₁.1.1
      simpa [S, candMFresh, R_old] using hS₁
    have hu₂_not : (u₂, x u₂) ∉ R_old := by
      have hS₂ := h₂.1.1
      simpa [S, candMFresh, R_old] using hS₂
    have hv₁_in : (v₁, activeColor x a b v₁) ∈ R_old := hcstar_old v₁
    have hv₂_in : (v₂, activeColor x a b v₂) ∈ R_old := hcstar_old v₂
    dsimp [candPhi2] at heq
    split_ifs at heq with hlt₁ hlt₂ hlt₂
    · simp only [Prod.mk.injEq] at heq
      exact Prod.ext heq.1 heq.2.1
    · simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, _, hval, _⟩
      rw [hval] at hu₁_not
      exact absurd hv₂_in hu₁_not
    · simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, _, hval, _⟩
      rw [← hval] at hu₂_not
      exact absurd hv₁_in hu₂_not
    · simp only [Prod.mk.injEq] at heq
      exact Prod.ext heq.2.1 heq.1
  have hPhi_disj : ∀ w,
      Disjoint ((candA1 S).image (candPhi1 x)) ((candA2 C₁ a b x S w).image (candPhi2 a b x)) := by
    intro w
    rw [Finset.disjoint_left]
    intro t ht₁ ht₂
    rcases Finset.mem_image.mp ht₁ with ⟨⟨u₁, v₁⟩, _, rfl⟩
    rcases Finset.mem_image.mp ht₂ with ⟨⟨u₂, v₂⟩, h₂, heq⟩
    simp only [candA2, Finset.mem_filter, Finset.mem_product] at h₂
    have hv₂_ne : activeColor x a b v₂ ≠ x v₂ := hcstar_ne v₂ h₂.1.2
    dsimp [candPhi1, candPhi2] at heq
    split_ifs at heq with hlt₂
    · simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨_, rfl, _, hval⟩
      exact hv₂_ne hval
    · simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, _, hval, _⟩
      exact hv₂_ne hval
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    simp only [candMFresh, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [disagreeSet, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => hv (h ▸ ha_old v), fun h => hv (h ▸ hb_old v)⟩
  · intro w hw i hi
    simp only [candQCand, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hi
    rw [Finset.mem_sdiff]
    rcases hi with ⟨_, rfl, rfl⟩ | ⟨t, ht | ht, rfl⟩
    · refine ⟨?_, ?_⟩
      · simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
        exact Or.inl (Or.inr ⟨Fin.last m, by simp [Fin.snoc_last]⟩)
      · intro hmem
        simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_univ, true_and] at hmem
        rcases hmem with (⟨z, rfl | rfl, h⟩ | ⟨t₀, h⟩) | ⟨_, _, h⟩
        · exact hx_ne_a (Sum.inr.inj h).symm
        · exact hx_ne_b (Sum.inr.inj h).symm
        · exact hx_not_img t₀ (Sum.inr.inj h)
        · cases h
    · rcases ht with ⟨⟨u, v⟩, huv, rfl⟩
      simp only [candA1, Finset.mem_filter, Finset.mem_univ, true_and] at huv
      refine ⟨?_, ?_⟩
      · simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact Or.inr ⟨(u, v, x u, x v), ⟨huv.1, hx_new u, hx_new v⟩, rfl⟩
      · intro hmem
        simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and] at hmem
        rcases hmem with (⟨_, _, h⟩ | ⟨_, h⟩) | ⟨t₀, ht₀, h⟩
        · cases h
        · cases h
        · have heq := Sum.inl.inj h
          subst heq
          rcases huv.2 with huS | hvS
          · have hu_not : (u, x u) ∉ R_old := by simpa [candMFresh, R_old] using huS
            exact hu_not ht₀.2.1
          · have hv_not : (v, x v) ∉ R_old := by simpa [candMFresh, R_old] using hvS
            exact hv_not ht₀.2.2
    · rcases ht with ⟨⟨u, v⟩, huv, rfl⟩
      have hne_uv : u ≠ v :=
        ((candMWit_card_and_quad C₁ r_star m hC₁_loc hr_loc a b z_prev x hd_xa hd_xb).2 w hw).1
          (u, v) huv
      have hu_not : (u, x u) ∉ R_old := by
        have huS := (Finset.mem_product.mp (Finset.mem_filter.mp huv).1).1
        simpa [candMFresh, R_old] using huS
      dsimp [candPhi2]
      split_ifs with hlt
      · refine ⟨?_, ?_⟩
        · simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact Or.inr ⟨(u, v, x u, activeColor x a b v),
            ⟨hlt, hx_new u, hold_sub_new (hcstar_old v)⟩, rfl⟩
        · intro hmem
          simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and] at hmem
          rcases hmem with (⟨_, _, h⟩ | ⟨_, h⟩) | ⟨t₀, ht₀, h⟩
          · cases h
          · cases h
          · have heq := Sum.inl.inj h
            subst heq
            exact hu_not ht₀.2.1
      · have hgt : v < u := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne_uv)
        refine ⟨?_, ?_⟩
        · simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact Or.inr ⟨(v, u, activeColor x a b v, x u),
            ⟨hgt, hold_sub_new (hcstar_old v), hx_new u⟩, rfl⟩
        · intro hmem
          simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and] at hmem
          rcases hmem with (⟨_, _, h⟩ | ⟨_, h⟩) | ⟨t₀, ht₀, h⟩
          · cases h
          · cases h
          · have heq := Sum.inl.inj h
            subst heq
            exact hu_not ht₀.2.2
  · intro ω hω_keep hx_wit
    exact candMWit_proj C₁ r_star m a b z_prev x ω hω_keep hx_wit
  · intro w p_edge p_keep
    have hdisj_sum : Disjoint
        (({x} : Finset (Fin N → Fin q)).image (Sum.inr : _ → cspIota N q))
        (((candA1 S).image (candPhi1 x) ∪
          (candA2 C₁ a b x S w).image (candPhi2 a b x)).image (Sum.inl : _ → cspIota N q)) := by
      rw [Finset.disjoint_left]
      intro i hi₁ hi₂
      rcases Finset.mem_image.mp hi₁ with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hi₂ with ⟨_, _, h⟩
      cases h
    dsimp [candQCand]
    rw [Finset.prod_union hdisj_sum,
      Finset.prod_image (fun _ _ _ _ h => Sum.inr.inj h),
      Finset.prod_singleton,
      Finset.prod_image (fun _ _ _ _ h => Sum.inl.inj h),
      Finset.prod_union (hPhi_disj w),
      Finset.prod_image (fun _ _ _ _ h => hPhi1_inj h),
      Finset.prod_image (hPhi2_injOn w)]
    simp [S, pow_add]

theorem freshCoordinateFiberCardinality : ∀ {N q : ℕ} (C₁ r_star m : ℕ), 3 ≤ C₁ → m < cspKMom C₁ →
    ∀ (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)),
    dHam a b ≤ C₁ * r_star →
    (∀ t : Fin m, dHam (z_prev t) a ≤ C₁ * r_star) →
    ∀ s : ℕ,
    ((Finset.univ.filter (fun x : Fin N → Fin q =>
      (candMFresh a b m z_prev x).card = s ∧ dHam x a ≤ C₁ * r_star)).card : ℝ) ≤
      ((C₁ * r_star + 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
        ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s) := by
  intro N q C₁ r_star m hC₁_loc hm_loc a b z_prev hd_ab_loc hz_prev s
  let R_old := cspRvc a b m z_prev
  let R_neq := R_old.filter (fun vc : Fin N × Fin q => vc.2 ≠ a vc.1)
  have hR_neq_card : R_neq.card ≤ (1 + m) * (C₁ * r_star) := by
    have hsub : R_neq ⊆ (disagreeSet a b).image (fun v => (v, b v)) ∪
        Finset.univ.biUnion (fun t : Fin m =>
          (disagreeSet (z_prev t) a).image (fun v => (v, z_prev t v))) := by
      intro vc hvc
      simp only [R_neq, R_old, cspRvc, Finset.mem_filter, Finset.mem_union,
        Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_biUnion] at hvc
      rcases hvc with ⟨(⟨v, rfl⟩ | ⟨v, rfl⟩) | ⟨t, v, rfl⟩, hne⟩
      · exact absurd rfl hne
      · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
          Finset.mem_univ, true_and, disagreeSet, Finset.mem_filter]
        exact Or.inl ⟨v, Ne.symm hne, rfl⟩
      · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
          Finset.mem_univ, true_and, disagreeSet, Finset.mem_filter]
        exact Or.inr ⟨t, v, hne, rfl⟩
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.card_union_le
      ((disagreeSet a b).image (fun v => (v, b v)))
      (Finset.univ.biUnion (fun t : Fin m =>
        (disagreeSet (z_prev t) a).image (fun v => (v, z_prev t v))))
    have hc_ab : ((disagreeSet a b).image (fun v => (v, b v))).card ≤ C₁ * r_star :=
      le_trans Finset.card_image_le hd_ab_loc
    have hc_z : (Finset.univ.biUnion (fun t : Fin m =>
        (disagreeSet (z_prev t) a).image (fun v => (v, z_prev t v)))).card ≤
        m * (C₁ * r_star) := by
      calc
        (Finset.univ.biUnion (fun t : Fin m =>
            (disagreeSet (z_prev t) a).image (fun v => (v, z_prev t v)))).card
          ≤ ∑ t : Fin m, ((disagreeSet (z_prev t) a).image (fun v => (v, z_prev t v))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _ : Fin m, (C₁ * r_star) :=
            Finset.sum_le_sum (fun t _ => le_trans Finset.card_image_le (hz_prev t))
        _ = m * (C₁ * r_star) := by rw [Finset.sum_const, Finset.card_fin, smul_eq_mul]
    have h_add : C₁ * r_star + m * (C₁ * r_star) = (1 + m) * (C₁ * r_star) := by ring
    omega
  have hR_neq_20 : R_neq.card ≤ 20 * C₁ ^ 2 * (C₁ * r_star) := by
    have h1m : 1 + m ≤ 20 * C₁ ^ 2 := by
      unfold cspKMom at hm_loc
      omega
    exact le_trans hR_neq_card (Nat.mul_le_mul_right (C₁ * r_star) h1m)
  let Sphere_a : Finset (Fin N → Fin q) :=
    ((Finset.univ : Finset (Fin N)).powersetCard s).biUnion (fun S =>
      Fintype.piFinset (fun v : Fin N =>
        if v ∈ S then (Finset.univ : Finset (Fin q)).erase (a v) else {a v}))
  have hSphere_card : Sphere_a.card ≤ N.choose s * (q - 1) ^ s := by
    calc
      Sphere_a.card
        ≤ ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard s,
            (Fintype.piFinset (fun v : Fin N =>
              if v ∈ S then (Finset.univ : Finset (Fin q)).erase (a v) else {a v})).card :=
          Finset.card_biUnion_le
      _ = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard s, (q - 1) ^ s := by
          refine Finset.sum_congr rfl (fun S hS => ?_)
          have hS_card : S.card = s := (Finset.mem_powersetCard.mp hS).2
          rw [Fintype.card_piFinset]
          have hfac : ∀ v ∈ (Finset.univ : Finset (Fin N)),
              (if v ∈ S then (Finset.univ : Finset (Fin q)).erase (a v) else {a v}).card =
                if v ∈ S then q - 1 else 1 := by
            intro v _
            split_ifs
            · rw [Finset.card_erase_of_mem (Finset.mem_univ (a v)), Finset.card_fin]
            · exact Finset.card_singleton _
          rw [Finset.prod_congr rfl hfac, Finset.prod_ite]
          have hfilt : (Finset.univ : Finset (Fin N)).filter (fun v => v ∈ S) = S := by
            ext v; simp
          rw [hfilt, Finset.prod_const, hS_card, Finset.prod_const_one, mul_one]
      _ = N.choose s * (q - 1) ^ s := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_fin, smul_eq_mul]
  let G_of : (Fin N → Fin q) → Finset (Fin N × Fin q) :=
    fun x =>
      (Finset.univ.filter (fun v : Fin N => v ∉ candMFresh a b m z_prev x ∧ x v ≠ a v)).image
        (fun v => (v, x v))
  let y_of : (Fin N → Fin q) → (Fin N → Fin q) :=
    fun x v => if v ∈ candMFresh a b m z_prev x then x v else a v
  have hy_fresh : ∀ x : Fin N → Fin q,
      candMFresh a b m z_prev x = Finset.univ.filter (fun v : Fin N => y_of x v ≠ a v) := by
    intro x
    ext v
    simp only [candMFresh, y_of, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hv
      rw [ite_eq_left (by simpa [candMFresh] using hv)]
      intro heq
      apply hv
      rw [heq]
      simp only [cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inl (Or.inl ⟨v, rfl⟩)
    · intro hne
      by_contra hnot
      simp [hnot] at hne
  have hG_mem_iff : ∀ (x : Fin N → Fin q) (v : Fin N),
      v ∉ candMFresh a b m z_prev x →
      ∀ c : Fin q, (v, c) ∈ G_of x ↔ c = x v ∧ x v ≠ a v := by
    intro x v hv c
    simp only [G_of, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨v', ⟨_, hne⟩, rfl, rfl⟩
      exact ⟨rfl, hne⟩
    · rintro ⟨rfl, hne⟩
      exact ⟨v, ⟨hv, hne⟩, rfl, rfl⟩
  let P_old := R_neq.powerset.filter (fun G => G.card ≤ C₁ * r_star)
  have hFib_le : (Finset.univ.filter (fun x : Fin N → Fin q =>
      (candMFresh a b m z_prev x).card = s ∧ dHam x a ≤ C₁ * r_star)).card ≤
      (P_old ×ˢ Sphere_a).card := by
    apply Finset.card_le_card_of_injOn (fun x => (G_of x, y_of x))
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [P_old, Finset.mem_coe, Finset.mem_product, Finset.mem_filter,
        Finset.mem_powerset]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro vc hvc
        rcases Finset.mem_image.mp hvc with ⟨v, hv, rfl⟩
        simp only [candMFresh, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hv
        simp only [R_neq, R_old, Finset.mem_filter]
        exact ⟨hv.1, hv.2⟩
      · have hsub_da : Finset.univ.filter
            (fun v : Fin N => v ∉ candMFresh a b m z_prev x ∧ x v ≠ a v) ⊆ disagreeSet x a := by
          intro v hv
          simp only [disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          exact hv.2
        exact le_trans Finset.card_image_le (le_trans (Finset.card_le_card hsub_da) hx.2)
      · simp only [Sphere_a, Finset.mem_biUnion, Finset.mem_powersetCard,
          Fintype.mem_piFinset]
        refine ⟨candMFresh a b m z_prev x, ⟨Finset.subset_univ _, hx.1⟩, ?_⟩
        intro v
        dsimp [y_of]
        split_ifs with hv
        · rw [Finset.mem_erase]
          refine ⟨?_, Finset.mem_univ _⟩
          intro heq
          simp only [candMFresh, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          apply hv
          rw [heq]
          simp only [cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
          exact Or.inl (Or.inl ⟨v, rfl⟩)
        · exact Finset.mem_singleton_self _
    · intro x₁ _ x₂ _ heq
      rcases Prod.mk.inj heq with ⟨hG_eq, hy_eq⟩
      have hS_eq : candMFresh a b m z_prev x₁ = candMFresh a b m z_prev x₂ := by
        rw [hy_fresh x₁, hy_fresh x₂, hy_eq]
      funext v
      by_cases hv : v ∈ candMFresh a b m z_prev x₁
      · have hv₂ : v ∈ candMFresh a b m z_prev x₂ := hS_eq ▸ hv
        have hy_v := congr_fun hy_eq v
        simpa [y_of, ite_eq_left hv, ite_eq_left hv₂] using hy_v
      · have hv₂ : v ∉ candMFresh a b m z_prev x₂ := hS_eq ▸ hv
        by_cases hx₁_ne : x₁ v ≠ a v
        · have hmem₁ : (v, x₁ v) ∈ G_of x₁ := (hG_mem_iff x₁ v hv (x₁ v)).mpr ⟨rfl, hx₁_ne⟩
          rw [hG_eq] at hmem₁
          exact ((hG_mem_iff x₂ v hv₂ (x₁ v)).mp hmem₁).1
        · push Not at hx₁_ne
          by_contra hx₂_ne
          have hx₂_ne_a : x₂ v ≠ a v := fun h => hx₂_ne (hx₁_ne.trans h.symm)
          have hmem₂ : (v, x₂ v) ∈ G_of x₂ := (hG_mem_iff x₂ v hv₂ (x₂ v)).mpr ⟨rfl, hx₂_ne_a⟩
          rw [← hG_eq] at hmem₂
          have heq₁₂ := ((hG_mem_iff x₁ v hv (x₂ v)).mp hmem₂).1
          exact hx₂_ne heq₁₂.symm
  rw [Finset.card_product] at hFib_le
  have hFib_nat := le_trans hFib_le (Nat.mul_le_mul_left P_old.card hSphere_card)
  have hFib_r : ((Finset.univ.filter (fun x : Fin N → Fin q =>
      (candMFresh a b m z_prev x).card = s ∧ dHam x a ≤ C₁ * r_star)).card : ℝ) ≤
      (P_old.card : ℝ) * ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s) := by
    exact_mod_cast hFib_nat
  have hP_old_r : (P_old.card : ℝ) ≤
      ((C₁ * r_star + 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * (C₁ * r_star) : ℕ) : ℝ) :=
    powerset_card_le_bound R_neq C₁ 20 (C₁ * r_star) hC₁_loc (by omega) hR_neq_20
  have hexp_eq : (((2 * Nat.clog 2 C₁ + 6) * (C₁ * r_star) : ℕ) : ℝ) =
      (1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
    unfold cspLam0
    push_cast
    ring
  rw [hexp_eq] at hP_old_r
  exact le_trans hFib_r (mul_le_mul_of_nonneg_right hP_old_r (by positivity))

private lemma calibration_range_bound (C₁ r_star : ℕ) (hC₁ : 3 ≤ C₁)
    (hr : 1000 * C₁ < r_star) :
    ((C₁ * r_star + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
  have hcr_le : C₁ * r_star + 1 ≤ r_star * r_star := by
    have hC1_le : C₁ + 1 ≤ r_star := by omega
    calc
      C₁ * r_star + 1 ≤ C₁ * r_star + r_star := by omega
      _ = (C₁ + 1) * r_star := (Nat.succ_mul C₁ r_star).symm
      _ ≤ r_star * r_star := Nat.mul_le_mul_right r_star hC1_le
  have hr_pow : r_star ≤ 2 ^ r_star := Nat.le_of_lt Nat.lt_two_pow_self
  have hsq_pow : r_star * r_star ≤ 2 ^ (2 * r_star) := by
    calc
      r_star * r_star ≤ 2 ^ r_star * 2 ^ r_star := Nat.mul_le_mul hr_pow hr_pow
      _ = 2 ^ (r_star + r_star) := (pow_add 2 r_star r_star).symm
      _ = 2 ^ (2 * r_star) := by rw [two_mul]
  have hnat := le_trans hcr_le hsq_pow
  have hcast : ((C₁ * r_star + 1 : ℕ) : ℝ) ≤ ((2 ^ (2 * r_star) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rwa [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat] at hcast

open Classical in
private lemma witnessMoments_h_xw_bound :
    ∀ (C₁ : ℕ),
      (3 : ℕ) ≤ C₁ →
        ∀ (r_star : ℕ),
          (1000 : ℕ) * C₁ < r_star →
            ∀ (N q : ℕ) (σ p_keep : ℝ),
              (0 : ℝ) < σ →
                σ * (↑r_star : ℝ) / (2 : ℝ) ≤ (10001 / 10000 : ℝ) * (↑(cspBeta0 C₁) : ℝ) →
                  (0 : ℝ) < p_keep →
                    ∀ (a₀ b₀ : Fin N → Fin q),
                      ∀ (m : ℕ),
                        ∀ (z_prev : Fin m → Fin N → Fin q),
                          (3000 : ℕ) ≤ cspLam0 C₁ →
                            (↑(cspBeta0 C₁) : ℝ) = (6 : ℝ) * (↑(cspLam0 C₁) : ℝ) →
                              let p_edge : ℝ := (2 : ℝ) ^ (-σ);
                              let P_rem : Finset (Fin N → Fin q) :=
                                cspPoolCand C₁ r_star a₀ b₀ \ Finset.image z_prev Finset.univ;
                              ∀ x ∈ P_rem,
                                ∀ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x,
                                  ∏ i ∈ candQCand C₁ a₀ b₀ m z_prev x w,
                                      Sum.elim (fun (_ : Fin N × Fin N × Fin q × Fin q) => p_edge)
                                        (fun (_ : Fin N → Fin q) => p_keep) i ≤
                                    p_keep * p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N -
                                        (1 : ℕ))) *
                                      (2 : ℝ) ^
                                        ((346 / 100 : ℝ) * (↑(cspLam0 C₁) : ℝ) * (↑(candMFresh
                                            a₀ b₀ m z_prev x).card : ℝ)) := by
  classical
  intro C₁ hC₁ r_star hr N q σ p_keep hσ_pos_loc hσ_up_loc hp_keep_pos_loc a₀ b₀ m z_prev
      hlam_ge hbeta_eq p_edge P_rem x hx w hw
  have hx_pool := (Finset.mem_sdiff.mp hx).1
  simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at hx_pool
  rcases hx_pool with ⟨_, _, hd_xa, hd_xb⟩
  obtain ⟨_, _, _, h_prod_eq⟩ := candidateQueriesFreshAndSupported C₁ r_star m hC₁ hr a₀ b₀
      z_prev x hx
  rw [h_prod_eq w p_edge p_keep]
  let S := candMFresh a₀ b₀ m z_prev x
  let s := S.card
  let a1 := (candA1 S).card
  let a2 := (candA2 C₁ a₀ b₀ x S w).card
  let N1 := N - 1
  have hs1_z : 2 * ((s : ℤ) * (N1 : ℤ) - (a1 : ℤ)) ≤ (s : ℤ) ^ 2 := incidentQueryCardinality S
  have hs2_z : 40 * ((s : ℤ) ^ 2 - 2 * (a2 : ℤ)) ≤ 23 * (r_star : ℤ) * (s : ℤ) :=
    ((candMWit_card_and_quad C₁ r_star m hC₁ hr a₀ b₀ z_prev x hd_xa hd_xb).2 w hw).2
  have hdef_z : 80 * ((s : ℤ) * (N1 : ℤ) - ((a1 + a2 : ℕ) : ℤ)) ≤
      23 * (r_star : ℤ) * (s : ℤ) := by
    push_cast
    linarith only [hs1_z, hs2_z]
  have hdef_r : 80 * (((s * N1 : ℕ) : ℝ) - ((a1 + a2 : ℕ) : ℝ)) ≤
      23 * (r_star : ℝ) * (s : ℝ) := by
    have hcast : ((80 * ((s : ℤ) * (N1 : ℤ) - ((a1 + a2 : ℕ) : ℤ))) : ℝ) ≤
        ((23 * (r_star : ℤ) * (s : ℤ)) : ℝ) := by exact_mod_cast hdef_z
    push_cast at hcast ⊢
    linarith only [hcast]
  have hσ_def : σ * (((s * N1 : ℕ) : ℝ) - ((a1 + a2 : ℕ) : ℝ)) ≤
      (346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ) := by
    have h1 : σ * (((s * N1 : ℕ) : ℝ) - ((a1 + a2 : ℕ) : ℝ)) ≤
        (σ * (r_star : ℝ) / 2) * ((23 / 40 : ℝ) * (s : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_left hdef_r (le_of_lt hσ_pos_loc)
      linarith [hm,
        show σ * (23 * (r_star : ℝ) * (s : ℝ)) =
          80 * ((σ * (r_star : ℝ) / 2) * ((23 / 40 : ℝ) * (s : ℝ))) by ring,
        show σ * (80 * (((s * N1 : ℕ) : ℝ) - ((a1 + a2 : ℕ) : ℝ))) =
          80 * (σ * (((s * N1 : ℕ) : ℝ) - ((a1 + a2 : ℕ) : ℝ))) by ring]
    have h2 : (σ * (r_star : ℝ) / 2) * ((23 / 40 : ℝ) * (s : ℝ)) ≤
        ((10001 / 10000 : ℝ) * (6 * (cspLam0 C₁ : ℝ))) * ((23 / 40 : ℝ) * (s : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hσ_up_loc, hbeta_eq]) (by positivity)
    have hprod_nn : (0 : ℝ) ≤ (cspLam0 C₁ : ℝ) * (s : ℝ) := by positivity
    linarith [h1, h2, hprod_nn]
  have hp_pow : p_edge ^ (a1 + a2) ≤ p_edge ^ (s * N1) *
      (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) := by
    have h_eq1 : p_edge ^ (a1 + a2) = (2 : ℝ) ^ (- σ * ((a1 + a2 : ℕ) : ℝ)) := by
      dsimp [p_edge]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h_eq2 : p_edge ^ (s * N1) *
        (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) =
        (2 : ℝ) ^ (- σ * ((s * N1 : ℕ) : ℝ) +
          (346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) := by
      dsimp [p_edge]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [h_eq1, h_eq2]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith only [hσ_def]
  calc
    p_keep * p_edge ^ (a1 + a2)
      ≤ p_keep * (p_edge ^ (s * N1) *
          (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) :=
        mul_le_mul_of_nonneg_left hp_pow (le_of_lt hp_keep_pos_loc)
    _ = p_keep * p_edge ^ (s * N1) *
          (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) :=
        (mul_assoc _ _ _).symm

open Classical in
private lemma witnessMoments_h_s_term :
    ∀ (C₁ : ℕ),
      (3 : ℕ) ≤ C₁ →
        ∀ (r_star N q : ℕ) (σ p_keep : ℝ),
          (∀ (s : ℕ),
              (↑(N.choose s) : ℝ) * (↑(q - (1 : ℕ)) : ℝ) ^ s * ((2 : ℝ) ^ (-σ)) ^ (s * (N - (1 :
                  ℕ))) ≤
                (2 : ℝ) ^ ((2 : ℝ) * (↑r_star : ℝ) - (↑(cspGamma0 C₁) : ℝ) * (↑s : ℝ))) →
            (0 : ℝ) < p_keep →
              ∀ (a₀ b₀ : Fin N → Fin q),
                dHam a₀ b₀ ≤ C₁ * r_star →
                  ∀ m < cspKMom C₁,
                    ∀ (z_prev : Fin m → Fin N → Fin q),
                      (3000 : ℕ) ≤ cspLam0 C₁ →
                        (↑(cspGamma0 C₁) : ℝ) = (5 : ℝ) * (↑(cspLam0 C₁) : ℝ) →
                          let p_edge : ℝ := (2 : ℝ) ^ (-σ);
                          let P_rem : Finset (Fin N → Fin q) :=
                            cspPoolCand C₁ r_star a₀ b₀ \ Finset.image z_prev Finset.univ;
                          let C_fixed : ℝ := (2 : ℝ) ^ ((3 : ℝ) * (↑r_star : ℝ)) * p_keep;
                          (0 : ℝ) ≤ C_fixed →
                            let R_s : Finset ℕ := Finset.range (C₁ * r_star + (1 : ℕ));
                            (∀ (t : Fin m), dHam (z_prev t) a₀ ≤ C₁ * r_star) →
                              (↑(C₁ * r_star + (1 : ℕ)) : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) * (↑r_star : ℝ)) →
                                ∀ s ∈ R_s,
                                  ∑ x ∈ P_rem with (candMFresh a₀ b₀ m z_prev x).card = s,
                                      p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - (1 :
                                          ℕ))) *
                                          (2 : ℝ) ^
                                            ((356 / 100 : ℝ) * (↑(cspLam0 C₁) : ℝ) *
                                              (↑(candMFresh a₀ b₀ m z_prev x).card : ℝ)) *
                                        C_fixed ≤
                                    (2 : ℝ) ^ ((2 : ℝ) * (↑r_star : ℝ)) *
                                          (2 : ℝ) ^ ((1 / 100 : ℝ) * (↑(cspLam0 C₁) : ℝ) *
                                              (↑r_star : ℝ)) *
                                        (2 : ℝ) ^ ((2 : ℝ) * (↑r_star : ℝ)) *
                                      C_fixed := by
  classical
  intro C₁ hC₁ r_star N q σ p_keep h_bin_loc hp_keep_pos_loc a₀ b₀ hd_ab_loc m hm z_prev hlam_ge
      hgamma_eq p_edge P_rem C_fixed hC_nn R_s hz_da h_range_r s _
  have h_congr : ∑ x ∈ P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s),
      ((p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
        (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
          ((candMFresh a₀ b₀ m z_prev x).card : ℝ))) * C_fixed) =
    ((P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)).card : ℝ) *
      ((p_edge ^ (s * (N - 1)) *
        (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed) := by
    have h1 : ∀ x ∈ P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s),
        (p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
          (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
            ((candMFresh a₀ b₀ m z_prev x).card : ℝ))) * C_fixed =
          (p_edge ^ (s * (N - 1)) *
            (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed := by
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
  rw [h_congr]
  have hfib_sub : P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s) ⊆
      Finset.univ.filter (fun x =>
        (candMFresh a₀ b₀ m z_prev x).card = s ∧ dHam x a₀ ≤ C₁ * r_star) := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxP, hxs⟩
    have hx_pool := (Finset.mem_sdiff.mp hxP).1
    simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at hx_pool
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxs, hx_pool.2.2.1⟩
  have hfib_le1 : ((P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)).card : ℝ) ≤
      ((Finset.univ.filter (fun x =>
        (candMFresh a₀ b₀ m z_prev x).card = s ∧ dHam x a₀ ≤ C₁ * r_star)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hfib_sub
  have hfib_r : ((P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)).card : ℝ) ≤
      (2 : ℝ) ^ (2 * (r_star : ℝ)) *
        (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
        ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s) := by
    have hs4 := le_trans hfib_le1 (freshCoordinateFiberCardinality C₁ r_star m hC₁ hm a₀ b₀
        z_prev hd_ab_loc hz_da s)
    exact le_trans hs4 (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h_range_r (by positivity)) (by positivity))
  have hs_bin : ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s * p_edge ^ (s * (N - 1))) *
      (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) ≤
      (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
    calc
      ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s * p_edge ^ (s * (N - 1))) *
          (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))
        ≤ (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ)) *
            (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) :=
          mul_le_mul_of_nonneg_right (h_bin_loc s) (by positivity)
      _ = (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ) +
            (356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hls_nn : 0 ≤ (cspLam0 C₁ : ℝ) * (s : ℝ) := by positivity
          rw [hgamma_eq]
          linarith only [hls_nn]
  calc
    ((P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)).card : ℝ) *
        ((p_edge ^ (s * (N - 1)) *
          (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed)
      ≤ ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
          (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
          ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s)) *
          ((p_edge ^ (s * (N - 1)) *
            (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed) :=
        mul_le_mul_of_nonneg_right hfib_r (by positivity)
    _ = (2 : ℝ) ^ (2 * (r_star : ℝ)) *
          (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
          (((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s * p_edge ^ (s * (N - 1))) *
            (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed := by
        ring
    _ ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) *
          (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
          (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs_bin (by positivity)) hC_nn

theorem witness_list_step_query_sum_bound (C₁ : ℕ) (hC₁ : 3 ≤ C₁) (r_star : ℕ) (hr : 1000 * C₁ <
    r_star)
    (hσ_pos : 0 < cspSigmaEdge C₁ r_star)
    (hσ_up : cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 ≤
      (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ))
    (h_binom_edge : ∀ s : ℕ,
      ((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
        (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1)) ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ)))
    (hp_keep_pos : 0 < cspPKeep C₁ r_star)
    (hp_keep_up : cspPKeep C₁ r_star ≤
      (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))
    (a b : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))
    (hd_ab : dHam a b ≤ C₁ * r_star) :
    ∃ (M_wit : (m : ℕ) → (Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) →
        (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) →
        Finset (candWitType (2 ^ cspL C₁ * r_star) C₁))
      (Q_cand : (m : ℕ) → (Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) →
        (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) →
        candWitType (2 ^ cspL C₁ * r_star) C₁ →
        Finset (cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁))),
      (∀ m < cspKMom C₁, ∀ z_prev : Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
        (∀ t : Fin m, z_prev t ∈ cspPoolCand C₁ r_star a b) →
        ∀ x ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev,
        ∀ w ∈ M_wit m z_prev x,
          Q_cand m z_prev x w ⊆
            cspUCand a b (m + 1) (Fin.snoc z_prev x) \ cspUCand a b m z_prev) ∧
      (∀ (ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool) (m : ℕ), m < cspKMom C₁ →
        ∀ z_prev : Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
        (∀ t : Fin m, z_prev t ∈ cspPoolCand C₁ r_star a b) →
        ∀ x ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev,
          ω (Sum.inr x) = true →
          x ∈ bicliqueWitnessList (symROf ω) C₁ r_star a b →
          ∃ w ∈ M_wit m z_prev x, ∀ i ∈ Q_cand m z_prev x w, ω i = true) ∧
      (∀ m < cspKMom C₁, ∀ z_prev : Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
        (∀ t : Fin m, z_prev t ∈ cspPoolCand C₁ r_star a b) →
        ∑ x ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev,
          ∑ w ∈ M_wit m z_prev x, (∏ i ∈ Q_cand m z_prev x w, cspPIota C₁ r_star i) ≤
            (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) :=
by
  have h_s5_poly : ∀ (N q : ℕ) (σ p_keep : ℝ),
      0 < σ →
      σ * (r_star : ℝ) / 2 ≤ (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ) →
      (∀ s : ℕ,
        (N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s * ((2 : ℝ) ^ (- σ)) ^ (s * (N - 1)) ≤
          (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ))) →
      0 < p_keep →
      p_keep ≤ (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) →
      ∀ (a₀ b₀ : Fin N → Fin q), dHam a₀ b₀ ≤ C₁ * r_star →
      ∀ m < cspKMom C₁, ∀ z_prev : Fin m → (Fin N → Fin q),
        (∀ t : Fin m, z_prev t ∈ cspPoolCand C₁ r_star a₀ b₀) →
        ∑ x ∈ cspPoolCand C₁ r_star a₀ b₀ \ Finset.univ.image z_prev,
          ∑ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x,
            (∏ i ∈ candQCand C₁ a₀ b₀ m z_prev x w,
              Sum.elim (fun _ => (2 : ℝ) ^ (- σ)) (fun _ => p_keep) i) ≤
          (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by
    clear hσ_pos hσ_up h_binom_edge hp_keep_pos hp_keep_up hd_ab a b
    intro N q σ p_keep hσ_pos_loc hσ_up_loc h_bin_loc hp_keep_pos_loc hp_keep_up_loc
      a₀ b₀ hd_ab_loc m hm z_prev hz_pool
    have hlam_ge : 3000 ≤ cspLam0 C₁ := by
      have h := (lam0_ge_1000_C1 C₁ hC₁).2.1
      omega
    have hbeta_eq : (cspBeta0 C₁ : ℝ) = 6 * (cspLam0 C₁ : ℝ) := by
      unfold cspBeta0; push_cast; ring
    have hgamma_eq : (cspGamma0 C₁ : ℝ) = 5 * (cspLam0 C₁ : ℝ) := by
      unfold cspGamma0; push_cast; ring
    let p_edge : ℝ := (2 : ℝ) ^ (- σ)
    let P_rem := cspPoolCand C₁ r_star a₀ b₀ \ Finset.univ.image z_prev
    have h_xw_bound :=
      @witnessMoments_h_xw_bound C₁ hC₁ r_star hr N q σ p_keep hσ_pos_loc hσ_up_loc
          hp_keep_pos_loc a₀ b₀ m z_prev hlam_ge hbeta_eq
    let C_fixed : ℝ := (2 : ℝ) ^ (3 * (r_star : ℝ)) * p_keep
    have hC_nn : 0 ≤ C_fixed := by positivity
    have h_x_bound : ∀ x ∈ P_rem,
        ∑ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x,
          (∏ i ∈ candQCand C₁ a₀ b₀ m z_prev x w,
            Sum.elim (fun _ => p_edge) (fun _ => p_keep) i) ≤
        (p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
          (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
            ((candMFresh a₀ b₀ m z_prev x).card : ℝ))) * C_fixed := by
      intro x hx
      have hx_pool := (Finset.mem_sdiff.mp hx).1
      simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at hx_pool
      have h_wcard_r :=
        (candMWit_card_and_quad C₁ r_star m hC₁ hr a₀ b₀ z_prev x hx_pool.2.2.1 hx_pool.2.2.2).1
      let s := (candMFresh a₀ b₀ m z_prev x).card
      calc
        ∑ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x, _
          ≤ ∑ _w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x,
              (p_keep * p_edge ^ (s * (N - 1)) *
                (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) :=
            Finset.sum_le_sum (fun w hw => h_xw_bound x hx w hw)
        _ = ((candMWit C₁ r_star a₀ b₀ m z_prev x).card : ℝ) *
              (p_keep * p_edge ^ (s * (N - 1)) *
                (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 : ℝ) ^ (3 * (r_star : ℝ) + (1 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) *
              (p_keep * p_edge ^ (s * (N - 1)) *
                (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) :=
            mul_le_mul_of_nonneg_right h_wcard_r (by positivity)
        _ = (p_edge ^ (s * (N - 1)) *
              ((2 : ℝ) ^ ((1 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) *
                (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)))) * C_fixed := by
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            dsimp [C_fixed]
            ring
        _ = (p_edge ^ (s * (N - 1)) *
              (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            congr 3
            ring
    let R_s := Finset.range (C₁ * r_star + 1)
    have hP_bi : P_rem = R_s.biUnion
        (fun s => P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)) := by
      ext x
      simp only [R_s, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
      constructor
      · intro hx
        have hS_sub := (candidateQueriesFreshAndSupported C₁ r_star m hC₁ hr a₀ b₀ z_prev x hx).1
        have hx_pool := (Finset.mem_sdiff.mp hx).1
        simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at hx_pool
        have hs_le : (candMFresh a₀ b₀ m z_prev x).card ≤ C₁ * r_star :=
          le_trans (Finset.card_le_card (hS_sub.trans Finset.inter_subset_left)) hx_pool.2.2.1
        exact ⟨(candMFresh a₀ b₀ m z_prev x).card, Nat.lt_succ_of_le hs_le, hx, rfl⟩
      · rintro ⟨_, _, hx, _⟩
        exact hx
    have hP_disj : (R_s : Set ℕ).PairwiseDisjoint
        (fun s => P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)) := by
      intro s₁ _ s₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
      intro x hx₁ hx₂
      exact hne (hx₁.2.symm.trans hx₂.2)
    have hz_da : ∀ t : Fin m, dHam (z_prev t) a₀ ≤ C₁ * r_star := by
      intro t
      have ht := hz_pool t
      simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      exact ht.2.2.1
    have h_range_r := calibration_range_bound C₁ r_star hC₁ hr
    have h_s_term :=
      @witnessMoments_h_s_term C₁ hC₁ r_star N q σ p_keep h_bin_loc hp_keep_pos_loc a₀ b₀
          hd_ab_loc m hm z_prev hlam_ge hgamma_eq hC_nn hz_da h_range_r
    have hRs_card : (R_s.card : ℝ) ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
      simpa [R_s] using h_range_r
    have h_tot_1 : ∑ x ∈ P_rem, ∑ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x,
        (∏ i ∈ candQCand C₁ a₀ b₀ m z_prev x w,
          Sum.elim (fun _ => p_edge) (fun _ => p_keep) i) ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ)) *
          ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
            (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
            (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed) := by
      calc
        ∑ x ∈ P_rem, ∑ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x, _
          ≤ ∑ x ∈ P_rem,
              ((p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
                (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
                  ((candMFresh a₀ b₀ m z_prev x).card : ℝ))) * C_fixed) :=
            Finset.sum_le_sum h_x_bound
        _ = ∑ s ∈ R_s, ∑ x ∈ P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s),
              ((p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
                (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
                  ((candMFresh a₀ b₀ m z_prev x).card : ℝ))) * C_fixed) := by
            conv_lhs => rw [hP_bi]
            exact Finset.sum_biUnion hP_disj
        _ ≤ ∑ _s ∈ R_s,
              ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
                (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
                (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed) :=
            Finset.sum_le_sum h_s_term
        _ = (R_s.card : ℝ) *
              ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
                (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
                (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
                (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
                (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed) :=
            mul_le_mul_of_nonneg_right hRs_card (by positivity)
    have hC_up : C_fixed ≤
        (2 : ℝ) ^ (3 * (r_star : ℝ)) *
          (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by
      dsimp [C_fixed]
      exact mul_le_mul_of_nonneg_left hp_keep_up_loc (by positivity)
    have h_tot_2 : (2 : ℝ) ^ (2 * (r_star : ℝ)) *
          ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
            (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
            (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed) ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) + 2 * (r_star : ℝ) +
          (1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) + 2 * (r_star : ℝ) +
          3 * (r_star : ℝ) +
          (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) := by
      calc
        (2 : ℝ) ^ (2 * (r_star : ℝ)) *
            ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
              (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
              (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed)
          ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
                (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
                (2 : ℝ) ^ (2 * (r_star : ℝ)) *
                ((2 : ℝ) ^ (3 * (r_star : ℝ)) *
                  (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hC_up (by positivity)) (by positivity)
        _ = (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
              (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              (2 : ℝ) ^ (3 * (r_star : ℝ)) *
              (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by ring
        _ = _ := by
            repeat rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have h_exp_le : 2 * (r_star : ℝ) + 2 * (r_star : ℝ) +
        (1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) + 2 * (r_star : ℝ) +
        3 * (r_star : ℝ) +
        (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ≤
        - (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
      have hlam_r : (3000 : ℝ) ≤ (cspLam0 C₁ : ℝ) := by exact_mod_cast hlam_ge
      have hr_nn : (0 : ℝ) ≤ (r_star : ℝ) := Nat.cast_nonneg _
      nlinarith only [hlam_r, hr_nn]
    exact le_trans h_tot_1
      (le_trans h_tot_2 (Real.rpow_le_rpow_of_exponent_le (by norm_num) h_exp_le))
  refine ⟨fun m z_prev x => candMWit C₁ r_star a b m z_prev x,
    fun m z_prev x w => candQCand C₁ a b m z_prev x w, ?_, ?_, ?_⟩
  · intro m _ z_prev _ x hx w hw
    exact (candidateQueriesFreshAndSupported C₁ r_star m hC₁ hr a b z_prev x hx).2.1 w hw
  · intro ω m _ z_prev _ x hx hω hClean
    exact (candidateQueriesFreshAndSupported C₁ r_star m hC₁ hr a b z_prev x hx).2.2.1 ω hω hClean
  · unfold cspPEdge at h_binom_edge
    unfold cspPIota cspPEdge
    exact h_s5_poly (2 ^ cspL C₁ * r_star) (cspQ C₁)
      (cspSigmaEdge C₁ r_star) (cspPKeep C₁ r_star)
      hσ_pos hσ_up h_binom_edge hp_keep_pos hp_keep_up a b hd_ab

end Helpers

end HighDimSteinerSpanners.Proofs.CSP
