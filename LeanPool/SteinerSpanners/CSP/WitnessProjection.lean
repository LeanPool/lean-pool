/-
Copyright (c) 2026 Goran Zuzic et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Goran Zuzic, David P. Woodruff, Vahab Mirrokni
-/

module

import Mathlib.Tactic.Linarith

public import LeanPool.SteinerSpanners.CSP.WitnessCardinality

/-! # Witness Projection for spanner CSP codes

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib.
-/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners.Proofs.CSP

noncomputable section Helpers

/-- Encode a disjoint finite partition by labels, using zero for the residual part. -/
lemma encodePartition {N K k : ℕ} (hk : k ≤ K) (M : Finset (Fin N))
    (A : Fin k → Finset (Fin N)) (I_k : Finset (Fin N))
    (hMpart : M ⊆ Finset.univ.biUnion A ∪ I_k)
    (hAdisjoint : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hAIdisjoint : ∀ r, Disjoint (A r) I_k) :
    ∃ τ : Fin N → Fin (K + 1),
      (∀ u ∈ M, τ u = 0 ↔ u ∈ I_k) ∧
      (∀ (r : Fin K) (hr : r.1 < k), ∀ u ∈ M, τ u = r.succ ↔ u ∈ A ⟨r.1, hr⟩) ∧
      (∀ u ∈ M, (τ u).1 ≤ k) ∧
      (∀ (r : Fin K) (hr : r.1 < k),
        M.filter (fun u => τ u = 0 ∨ r.1 + 1 < (τ u).1) =
          M ∩ ((Finset.univ.filter (fun j : Fin k => (⟨r.1, hr⟩ : Fin k) < j)).biUnion A ∪ I_k)) ∧
      (∀ u, u ∉ M → τ u = 0) := by
  classical
  let τ : Fin N → Fin (K + 1) := fun u =>
    if u ∈ M then
      if h : ∃ r : Fin k, u ∈ A r then
        (⟨(Classical.choose h).1, lt_of_lt_of_le (Classical.choose h).2 hk⟩ : Fin K).succ
      else 0
    else 0
  have hτ_zero_iff : ∀ u ∈ M, τ u = 0 ↔ u ∈ I_k := by
    intro u huM
    dsimp [τ]
    rw [ite_eq_left huM]
    have huI : u ∈ Finset.univ.biUnion A ∪ I_k := hMpart huM
    by_cases hex : ∃ r : Fin k, u ∈ A r
    · rw [dite_eq_left hex]
      have hne0 :
          (⟨(Classical.choose hex).1,
            lt_of_lt_of_le (Classical.choose hex).2 hk⟩ : Fin K).succ ≠ 0 :=
        Fin.succ_ne_zero _
      obtain ⟨r, hur⟩ := hex
      have hnotIk : u ∉ I_k := Finset.disjoint_left.mp (hAIdisjoint r) hur
      exact iff_of_false hne0 hnotIk
    · rw [dite_eq_right hex]
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and] at huI
      rcases huI with ⟨r, hur⟩ | huIk
      · exact absurd ⟨r, hur⟩ hex
      · exact iff_of_true rfl huIk
  have hτ_succ_iff : ∀ (r : Fin K) (hr : r.1 < k), ∀ u ∈ M,
      τ u = r.succ ↔ u ∈ A ⟨r.1, hr⟩ := by
    intro r hr u huM
    dsimp only [τ]
    rw [ite_eq_left huM]
    constructor
    · intro hτ
      by_cases hex : ∃ j : Fin k, u ∈ A j
      · rw [dite_eq_left hex] at hτ
        have hval : (Classical.choose hex).1 + 1 = r.1 + 1 := by
          simpa [Fin.ext_iff, Fin.val_succ] using hτ
        have hj_eq : Classical.choose hex = ⟨r.1, hr⟩ :=
          Fin.ext (by change (Classical.choose hex).1 = r.1; omega)
        exact hj_eq ▸ Classical.choose_spec hex
      · rw [dite_eq_right hex] at hτ
        exact absurd hτ.symm (Fin.succ_ne_zero r)
    · intro huA
      have hex : ∃ j : Fin k, u ∈ A j := ⟨⟨r.1, hr⟩, huA⟩
      rw [dite_eq_left hex]
      have hch_eq : Classical.choose hex = ⟨r.1, hr⟩ := by
        by_contra hne
        exact Finset.disjoint_left.mp (hAdisjoint hne) (Classical.choose_spec hex) huA
      ext
      simp [hch_eq]
  have hτ_le_k : ∀ u ∈ M, (τ u).1 ≤ k := by
    intro u huM
    dsimp [τ]
    rw [ite_eq_left huM]
    split_ifs with hex
    · exact (Classical.choose hex).2
    · exact Nat.zero_le k
  have hIt_eq : ∀ (r : Fin K) (hr : r.1 < k),
      M.filter (fun u => τ u = 0 ∨ r.1 + 1 < (τ u).1) =
        M ∩ ((Finset.univ.filter (fun j : Fin k => (⟨r.1, hr⟩ : Fin k) < j)).biUnion A ∪ I_k) := by
    intro r hr
    ext u
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨huM, h0 | hgt⟩
      · exact ⟨huM, Or.inr ((hτ_zero_iff u huM).mp h0)⟩
      · have hne0 : τ u ≠ 0 := by intro h; simp [h] at hgt
        have hle : (τ u).1 ≤ k := hτ_le_k u huM
        let j0 : Fin K := ⟨(τ u).1 - 1, lt_of_lt_of_le (by omega) hk⟩
        have hj0_lt : j0.1 < k := by dsimp [j0]; omega
        have hτ_j0 : τ u = j0.succ := by ext; dsimp [j0]; omega
        have huAj0 : u ∈ A ⟨j0.1, hj0_lt⟩ := (hτ_succ_iff j0 hj0_lt u huM).mp hτ_j0
        refine ⟨huM, Or.inl ⟨⟨j0.1, hj0_lt⟩, ?_, huAj0⟩⟩
        simp only [Fin.lt_def, j0]; omega
    · rintro ⟨huM, ⟨j, hrj, huAj⟩ | huIk⟩
      · have hjK : j.1 < K := lt_of_lt_of_le j.2 hk
        have hτj : τ u = (⟨j.1, hjK⟩ : Fin K).succ :=
          (hτ_succ_iff ⟨j.1, hjK⟩ j.2 u huM).mpr huAj
        refine ⟨huM, Or.inr ?_⟩
        rw [hτj, Fin.val_succ]
        dsimp only
        simp only [Fin.lt_def] at hrj
        omega
      · exact ⟨huM, Or.inl ((hτ_zero_iff u huM).mpr huIk)⟩
  exact ⟨τ, hτ_zero_iff, hτ_succ_iff, hτ_le_k, hIt_eq,
    fun u hu => by simp only [τ, ite_eq_right hu]⟩

/-- Convert a real cardinality deficit into a rounded bound for an intersection. -/
lemma cardIntersection_sub_le {α : Type*} [DecidableEq α] (M A B : Finset α) (r : ℕ)
    (h : (A.card : ℝ) - 11 / 40 * r ≤ B.card) :
    (M ∩ A).card - (11 * r) / 40 ≤ B.card := by
  have h40 : (40 : ℝ) * A.card ≤ 40 * B.card + 11 * r := by linarith
  have h40_nat : 40 * A.card ≤ 40 * B.card + 11 * r := by exact_mod_cast h40
  have hMA : (M ∩ A).card ≤ A.card := Finset.card_le_card Finset.inter_subset_right
  omega

lemma candMWit_proj {N q : ℕ} (C₁ r_star m : ℕ)
    (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q)
    (ω : cspIota N q → Bool) (hω_keep : ω (Sum.inr x) = true)
    (hx_wit : x ∈ bicliqueWitnessList (symROf ω) C₁ r_star a b) :
    ∃ w ∈ candMWit C₁ r_star a b m z_prev x,
      ∀ i ∈ candQCand C₁ a b m z_prev x w, ω i = true := by
  let K_max := cspKMax C₁
  let M := candMFresh a b m z_prev x
  let W_ab := diffCoords x a ∪ diffCoords x b
  have hM_sub_I : M ⊆ disagreeSet x a ∩ disagreeSet x b := by
    intro v hv
    simp only [M, candMFresh, cspRvc, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_image] at hv
    simp only [disagreeSet, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => hv (Or.inl (Or.inl ⟨v, h ▸ rfl⟩)),
           fun h => hv (Or.inl (Or.inr ⟨v, h ▸ rfl⟩))⟩
  simp only [bicliqueWitnessList, satisfyingSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx_wit
  rcases hx_wit with ⟨hx_hom, _, _, _, _, k, hk_le, A, B_fut₀, B_out₀, I_k,
    hA_disj, hAIk_disj, hpart, hIk_card, hr_all⟩
  have hk_Kmax : k ≤ K_max := hk_le
  let k_fin : Fin (K_max + 1) := ⟨k, Nat.lt_succ_of_le hk_Kmax⟩
  obtain ⟨τ, hτ_zero_iff, hτ_succ_iff, hτ_le_k, hIt_eq, hτ_outside⟩ :=
    encodePartition hk_Kmax M A I_k (fun _ hu => hpart.symm ▸ hM_sub_I hu) hA_disj hAIk_disj
  let B_fut : Fin K_max → Finset (Fin N) := fun r =>
    if hr : r.1 < k then M ∩ B_fut₀ ⟨r.1, hr⟩ else ∅
  -- Choose exact-size subset B_sub r' ⊆ B_out₀ r' for each r' : Fin k
  let s_target : Fin k → ℕ := fun r' => (M ∩ A r').card - (11 * r_star) / 40
  have hs_le_Bo : ∀ r' : Fin k, s_target r' ≤ (B_out₀ r').card :=
    fun r' => cardIntersection_sub_le M (A r') (B_out₀ r') r_star (hr_all r').2.2.2.2
  let B_sub : Fin k → Finset (Fin N) := fun r' =>
    Classical.choose (Finset.exists_subset_card_eq (hs_le_Bo r'))
  have hB_sub_spec : ∀ r' : Fin k, B_sub r' ⊆ B_out₀ r' ∧ (B_sub r').card = s_target r' :=
    fun r' => Classical.choose_spec (Finset.exists_subset_card_eq (hs_le_Bo r'))
  let U_out : Finset (Fin K_max × Fin N) :=
    (Finset.univ : Finset (Fin K_max)).biUnion (fun r =>
      if hr : r.1 < k then (B_sub ⟨r.1, hr⟩).image (fun v => (r, v)) else ∅)
  have hMr_eq : ∀ (r : Fin K_max) (hr : r.1 < k),
      M.filter (fun u => τ u = r.succ) = M ∩ A ⟨r.1, hr⟩ := by
    intro r hr
    ext u
    simp only [Finset.mem_filter, Finset.mem_inter]
    exact ⟨fun ⟨huM, h⟩ => ⟨huM, (hτ_succ_iff r hr u huM).mp h⟩,
           fun ⟨huM, h⟩ => ⟨huM, (hτ_succ_iff r hr u huM).mpr h⟩⟩
  have hBo_slice : ∀ (r : Fin K_max) (hr : r.1 < k),
      W_ab.filter (fun v => (r, v) ∈ U_out) = B_sub ⟨r.1, hr⟩ := by
    intro r hr
    ext v
    simp only [U_out, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, r', hmem⟩
      split_ifs at hmem with hr'
      · rcases Finset.mem_image.mp hmem with ⟨v', hv', hp⟩
        rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
        exact hv'
      · simp at hmem
    · intro hv
      have hvW : v ∈ W_ab := by
        have hv0 : v ∈ B_out₀ ⟨r.1, hr⟩ := (hB_sub_spec ⟨r.1, hr⟩).1 hv
        have hv1 := (hr_all ⟨r.1, hr⟩).2.1 hv0
        exact (Finset.mem_sdiff.mp hv1).1
      refine ⟨hvW, r, ?_⟩
      rw [dite_eq_left hr]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  let w : candWitType N C₁ := (k_fin, τ, B_fut, U_out)
  refine ⟨w, ?_, ?_⟩
  · -- w ∈ candMWit
    simp only [candMWit, Finset.mem_filter]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- w ∈ ambient biUnion
      rw [Finset.mem_biUnion]
      refine ⟨(k_fin, τ, B_fut), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_univ, true_and,
          Fintype.mem_piFinset, Finset.mem_powerset]
        refine ⟨fun u => ?_, fun r => ?_⟩
        · split_ifs with huM
          · exact Finset.mem_univ _
          · exact Finset.mem_singleton.mpr (hτ_outside u huM)
        · dsimp [B_fut]
          split_ifs with hr
          · exact Finset.inter_subset_left
          · exact Finset.empty_subset _
      · rw [Finset.mem_image]
        refine ⟨U_out, ?_, rfl⟩
        rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro rv hrv
          rcases Finset.mem_biUnion.mp hrv with ⟨r, _, hm⟩
          split_ifs at hm with hr
          · rcases Finset.mem_image.mp hm with ⟨v, hv, rfl⟩
            rw [Finset.mem_product]
            refine ⟨Finset.mem_univ r, ?_⟩
            have hv0 := (hB_sub_spec ⟨r.1, hr⟩).1 hv
            exact (Finset.mem_sdiff.mp ((hr_all ⟨r.1, hr⟩).2.1 hv0)).1
          · simp at hm
        · have hdisj : ((Finset.univ : Finset (Fin K_max)) : Set (Fin K_max)).PairwiseDisjoint
              (fun r : Fin K_max =>
                if hr : r.1 < k then (B_sub ⟨r.1, hr⟩).image (fun v => (r, v)) else ∅) := by
            intro r₁ _ r₂ _ hne
            rw [Function.onFun, Finset.disjoint_left]
            intro p hp1 hp2
            split_ifs at hp1 hp2 with hr1 hr2 hr2
            · rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
              rcases Finset.mem_image.mp hp2 with ⟨_, _, hp⟩
              exact hne (Prod.mk.inj hp).1.symm
            · simp at hp2
            · simp at hp1
            · simp at hp1
          dsimp [U_out]
          rw [Finset.card_biUnion hdisj]
          refine Finset.sum_congr rfl (fun r _ => ?_)
          split_ifs with hr
          · rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
              (hB_sub_spec ⟨r.1, hr⟩).2, hMr_eq r hr]
          · simp
    · exact hτ_le_k
    · have htail_sub : M.filter (fun u => τ u = 0) ⊆ I_k := by
        intro u hu
        rcases Finset.mem_filter.mp hu with ⟨huM, h0⟩
        exact (hτ_zero_iff u huM).mp h0
      have h2Ik_r : (2 : ℝ) * (I_k.card : ℝ) ≤ (r_star : ℝ) := by linarith
      have h2Ik : 2 * I_k.card ≤ r_star := by exact_mod_cast h2Ik_r
      exact le_trans (Nat.mul_le_mul_left 2 (Finset.card_le_card htail_sub)) h2Ik
    · intro r hrk
      have hr : r.1 < k := hrk
      obtain ⟨hBf0_sub, hBo0_sub, _, hmiss0, _⟩ := hr_all ⟨r.1, hr⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- B_fut r ⊆ I_tilde r
        rw [hIt_eq r hr]
        dsimp [w, B_fut]
        rw [dite_eq_left hr]
        exact Finset.inter_subset_inter_left hBf0_sub
      · -- 80 * (I_tilde r \ B_fut r).card ≤ r_star
        have hsdiff_sub : M.filter (fun u => τ u = 0 ∨ r.1 + 1 < (τ u).1) \ B_fut r ⊆
            ((Finset.univ.filter (fun j : Fin k => (⟨r.1, hr⟩ : Fin k) < j)).biUnion A ∪ I_k) \
              B_fut₀ ⟨r.1, hr⟩ := by
          rw [hIt_eq r hr]
          dsimp [B_fut]
          rw [dite_eq_left hr]
          intro u hu
          simp only [Finset.mem_sdiff, Finset.mem_inter] at hu ⊢
          exact ⟨hu.1.2, fun h => hu.2 ⟨hu.1.1, h⟩⟩
        have h80_r : (80 : ℝ) *
            ((((Finset.univ.filter (fun j : Fin k => (⟨r.1, hr⟩ : Fin k) < j)).biUnion A ∪ I_k) \
              B_fut₀ ⟨r.1, hr⟩).card : ℝ) ≤ (r_star : ℝ) := by linarith
        have h80_nat : 80 *
            (((Finset.univ.filter (fun j : Fin k => (⟨r.1, hr⟩ : Fin k) < j)).biUnion A ∪ I_k) \
              B_fut₀ ⟨r.1, hr⟩).card ≤ r_star := by exact_mod_cast h80_r
        exact le_trans (Nat.mul_le_mul_left 80 (Finset.card_le_card hsdiff_sub)) h80_nat
      · -- Disjoint (B_out r) (M_r ∪ I_tilde r)
        change Disjoint (W_ab.filter (fun v => (r, v) ∈ U_out)) _
        rw [hBo_slice r hr, hMr_eq r hr, hIt_eq r hr, Finset.disjoint_left]
        intro v hv hmem
        have hv0 := hBo0_sub ((hB_sub_spec ⟨r.1, hr⟩).1 hv)
        rw [Finset.mem_sdiff] at hv0
        apply hv0.2
        rcases Finset.mem_union.mp hmem with h1 | h2
        · exact Finset.mem_union_left _ (Finset.mem_inter.mp h1).2
        · exact Finset.mem_union_right _ (Finset.mem_inter.mp h2).2
      · -- (B_out r).card = M_r.card - (11 * r_star) / 40
        change (W_ab.filter (fun v => (r, v) ∈ U_out)).card = _
        rw [hBo_slice r hr, hMr_eq r hr, (hB_sub_spec ⟨r.1, hr⟩).2]
  · -- ∀ i ∈ candQCand, ω i = true
    intro i hi
    simp only [candQCand, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hi
    rcases hi with ⟨_, rfl, rfl⟩ | ⟨t, ht | ht, rfl⟩
    · exact hω_keep
    · rcases ht with ⟨⟨u, v⟩, huv, rfl⟩
      simp only [candA1, Finset.mem_filter, Finset.mem_univ, true_and] at huv
      simpa only [candPhi1, symROf, ite_eq_left huv.1] using hx_hom u v huv.1
    · rcases ht with ⟨⟨u, v⟩, huv, rfl⟩
      simp only [candA2, w, k_fin, Finset.mem_filter, Finset.mem_product] at huv
      rcases huv with ⟨⟨huM, hvW⟩, r, hrk, hτu, hvf | hvo⟩
      · have huA : u ∈ A ⟨r.1, hrk⟩ := (hτ_succ_iff r hrk u huM).mp hτu
        dsimp [B_fut] at hvf
        rw [dite_eq_left hrk] at hvf
        have hvBf0 : v ∈ B_fut₀ ⟨r.1, hrk⟩ := (Finset.mem_inter.mp hvf).2
        have hne_uv : u ≠ v := by
          intro heq; subst heq
          have huI := (Finset.mem_filter.mp
            ((hIt_eq r hrk).symm ▸ Finset.mem_inter.mpr ⟨huM, (hr_all ⟨r.1, hrk⟩).1 hvBf0⟩)).2
          rw [hτu] at huI
          rcases huI with h0 | hlt
          · exact Fin.succ_ne_zero r h0
          · simp at hlt
        have hrel := (hr_all ⟨r.1, hrk⟩).2.2.1 u huA v (Finset.mem_union_left _ hvBf0)
        dsimp [candPhi2]
        split_ifs with hlt
        · simpa [symROf, ite_eq_left hlt, candCStar, activeColor] using hrel
        · have hgt : v < u := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne_uv)
          simpa [symROf, ite_eq_right hlt, ite_eq_left hgt, candCStar, activeColor] using hrel
      · have huA : u ∈ A ⟨r.1, hrk⟩ := (hτ_succ_iff r hrk u huM).mp hτu
        have hvBsub : v ∈ B_sub ⟨r.1, hrk⟩ := by
          rw [← hBo_slice r hrk]
          exact Finset.mem_filter.mpr ⟨hvW, hvo⟩
        have hvBo0 : v ∈ B_out₀ ⟨r.1, hrk⟩ := (hB_sub_spec ⟨r.1, hrk⟩).1 hvBsub
        have hne_uv : u ≠ v := by
          intro heq; subst heq
          have hv_sdiff := (hr_all ⟨r.1, hrk⟩).2.1 hvBo0
          exact (Finset.mem_sdiff.mp hv_sdiff).2 (Finset.mem_union_left _ huA)
        have hrel := (hr_all ⟨r.1, hrk⟩).2.2.1 u huA v (Finset.mem_union_right _ hvBo0)
        dsimp [candPhi2]
        split_ifs with hlt
        · simpa [symROf, ite_eq_left hlt, candCStar, activeColor] using hrel
        · have hgt : v < u := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne_uv)
          simpa [symROf, ite_eq_right hlt, ite_eq_left hgt, candCStar, activeColor] using hrel

end Helpers

end HighDimSteinerSpanners.Proofs.CSP
