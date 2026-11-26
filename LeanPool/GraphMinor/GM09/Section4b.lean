/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section2a
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section3c
import LeanPool.GraphMinor.GM09.Section4a
import Mathlib.Data.Set.Card

/-!
# Graph Minors IX, Section 4 (Part 2): Clockwise Orderings and (4.4)

This file proves clockwise sequence and ordering lemmas for `CyclicPerm` and `AreInOrder`,
and proves (4.4) from Section 4 of
N. Robertson and P. D. Seymour, *Graph Minors. IX. Disjoint crossed paths*,
J. Combin. Theory Ser. B **49** (1990) 40–77 (pages 50–51).
-/

public section

namespace GraphMinor.GM09

open Set Graph GraphMinor

universe u v

variable {α : Type u} {β : Type v}

/-! ## Clockwise sequences and intervals in cyclic permutations -/

namespace CyclicPerm

variable (Ω : CyclicPerm α)

/-- In a clockwise sequence `L`, stepping `d ≥ 1` positions along `L` from `L[i]` corresponds to
some `k ≥ 1` iterations of `Ω` such that any intermediate hit in `{v | v ∈ L}` is `L[(i + m) % n]`
for some `1 ≤ m < d`. -/
theorem exists_iterate_step {L : List α} (h : Ω.IsClockwiseSeq L)
    (i d : ℕ) (hi : i < L.length) (hd : 1 ≤ d) :
    ∃ k : ℕ, 1 ≤ k ∧
      (Ω.toFun^[k]) (L[i]) = L[(i + d) % L.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)) ∧
      ∀ j : ℕ, 1 ≤ j → j < k → (Ω.toFun^[j]) (L[i]) ∈ {v | v ∈ L} →
        ∃ m : ℕ, 1 ≤ m ∧ m < d ∧
          (Ω.toFun^[j]) (L[i]) = L[(i + m) % L.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)) := by
  have hn_pos : 0 < L.length := Nat.zero_lt_of_lt hi
  induction d with
  | zero => omega
  | succ d ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · obtain ⟨k, hk1, hk_eq, _, hmin⟩ := h.2.2 i hi
      refine ⟨k, hk1, hk_eq, fun j hj1 hjlt hjL => (hmin j hj1 hjlt hjL).elim⟩
    · obtain ⟨k₁, hk₁_pos, hk₁_eq, hk₁_min⟩ := ih hd_pos
      let i' := (i + d) % L.length
      have hi' : i' < L.length := Nat.mod_lt _ hn_pos
      obtain ⟨k₂, hk₂_pos, hk₂_eq, _, hk₂_min⟩ := h.2.2 i' hi'
      have hmod_eq : (i' + 1) % L.length = (i + (d + 1)) % L.length := by
        simp [i', Nat.add_assoc]
      refine ⟨k₁ + k₂, by omega, ?_, ?_⟩
      · rw [Nat.add_comm k₁ k₂, Function.iterate_add_apply, hk₁_eq, hk₂_eq]
        congr 1
      · intro j hj1 hjlt hjL
        rcases lt_trichotomy j k₁ with hj_lt | rfl | hj_gt
        · obtain ⟨m, hm1, hmd, hm_eq⟩ := hk₁_min j hj1 hj_lt hjL
          exact ⟨m, hm1, Nat.lt_succ_of_lt hmd, hm_eq⟩
        · exact ⟨d, hd_pos, Nat.lt_succ_self d, hk₁_eq⟩
        · exfalso
          have hiter : (Ω.toFun^[j]) (L[i]) = (Ω.toFun^[j - k₁]) (L[i']) := by
            have hj_eq : j = (j - k₁) + k₁ := (Nat.sub_add_cancel (le_of_lt hj_gt)).symm
            conv_lhs => rw [hj_eq, Function.iterate_add_apply, hk₁_eq]
          rw [hiter] at hjL
          exact hk₂_min (j - k₁) (by omega) (by omega) hjL

/-- If `L` is `Ω`-clockwise and `i₁ < i₂ < i₃ < L.length`, then `(L[i₁], L[i₂], L[i₃])` is
`Ω`-clockwise, so `L[i₂] ∈ Ω.interval L[i₁] L[i₃]`. -/
theorem mem_interval_of_lt {L : List α} (h : Ω.IsClockwiseSeq L)
    {i₁ i₂ i₃ : ℕ} (h12 : i₁ < i₂) (h23 : i₂ < i₃) (h3 : i₃ < L.length) :
    L[i₂]'(Nat.lt_trans h23 h3) ∈
      Ω.interval (L[i₁]'(Nat.lt_trans h12 (Nat.lt_trans h23 h3))) (L[i₃]'h3) := by
  have h1 : i₁ < L.length := Nat.lt_trans h12 (Nat.lt_trans h23 h3)
  have h2 : i₂ < L.length := Nat.lt_trans h23 h3
  have hn_pos : 0 < L.length := Nat.zero_lt_of_lt h1
  let v₁ := L[i₁]'h1
  let v₂ := L[i₂]'h2
  let v₃ := L[i₃]'h3
  have hv₁ : v₁ ∈ Ω.bar := h.2.1 v₁ (List.getElem_mem h1)
  have hv₂ : v₂ ∈ Ω.bar := h.2.1 v₂ (List.getElem_mem h2)
  have hv₃ : v₃ ∈ Ω.bar := h.2.1 v₃ (List.getElem_mem h3)
  have hne12 : v₁ ≠ v₂ := fun heq => Nat.ne_of_lt h12 (( List.Nodup.getElem_inj_iff h.1 ).mp heq)
  have hne23 : v₂ ≠ v₃ := fun heq => Nat.ne_of_lt h23 (( List.Nodup.getElem_inj_iff h.1 ).mp heq)
  have hne13 : v₁ ≠ v₃ := fun heq =>
    Nat.ne_of_lt (Nat.lt_trans h12 h23) (( List.Nodup.getElem_inj_iff h.1 ).mp heq)
  -- Show `FirstHitIn {v₁, v₂, v₃} v₁ v₂`.
  have hhit12 : Ω.FirstHitIn {v₁, v₂, v₃} v₁ v₂ := by
    obtain ⟨k, hk1, hk_eq, hk_min⟩ := Ω.exists_iterate_step h i₁ (i₂ - i₁) h1 (by omega)
    have hmod : (i₁ + (i₂ - i₁)) % L.length = i₂ := by
      rw [Nat.add_sub_of_le (le_of_lt h12), Nat.mod_eq_of_lt h2]
    have hk_v₂ : (Ω.toFun^[k]) v₁ = v₂ := by
      rw [hk_eq]; congr 1
    refine ⟨k, hk1, hk_v₂, by simp, fun j hj1 hjlt hj_in => ?_⟩
    have hjL : (Ω.toFun^[j]) v₁ ∈ {v | v ∈ L} := by
      rcases hj_in with heq | heq | heq
      · rw [heq]; exact List.getElem_mem h1
      · rw [heq]; exact List.getElem_mem h2
      · rw [heq]; exact List.getElem_mem h3
    obtain ⟨m, hm1, hmd, hm_eq⟩ := hk_min j hj1 hjlt hjL
    have hm_lt : i₁ + m < L.length := by omega
    have hm_mod : (i₁ + m) % L.length = i₁ + m := Nat.mod_eq_of_lt hm_lt
    have hm_elem : (Ω.toFun^[j]) v₁ = L[i₁ + m]'hm_lt := by
      rw [hm_eq]; congr 1
    rw [hm_elem] at hj_in
    rcases hj_in with heq | heq | heq
    · have := (List.Nodup.getElem_inj_iff h.1).mp heq; omega
    · have := (List.Nodup.getElem_inj_iff h.1).mp heq; omega
    · have := (List.Nodup.getElem_inj_iff h.1).mp heq; omega
  -- Show `FirstHitIn {v₁, v₂, v₃} v₂ v₃`.
  have hhit23 : Ω.FirstHitIn {v₁, v₂, v₃} v₂ v₃ := by
    obtain ⟨k, hk1, hk_eq, hk_min⟩ := Ω.exists_iterate_step h i₂ (i₃ - i₂) h2 (by omega)
    have hmod : (i₂ + (i₃ - i₂)) % L.length = i₃ := by
      rw [Nat.add_sub_of_le (le_of_lt h23), Nat.mod_eq_of_lt h3]
    have hk_v₃ : (Ω.toFun^[k]) v₂ = v₃ := by
      rw [hk_eq]; congr 1
    refine ⟨k, hk1, hk_v₃, by simp, fun j hj1 hjlt hj_in => ?_⟩
    have hjL : (Ω.toFun^[j]) v₂ ∈ {v | v ∈ L} := by
      rcases hj_in with heq | heq | heq
      · rw [heq]; exact List.getElem_mem h1
      · rw [heq]; exact List.getElem_mem h2
      · rw [heq]; exact List.getElem_mem h3
    obtain ⟨m, hm1, hmd, hm_eq⟩ := hk_min j hj1 hjlt hjL
    have hm_lt : i₂ + m < L.length := by omega
    have hm_mod : (i₂ + m) % L.length = i₂ + m := Nat.mod_eq_of_lt hm_lt
    have hm_elem : (Ω.toFun^[j]) v₂ = L[i₂ + m]'hm_lt := by
      rw [hm_eq]; congr 1
    rw [hm_elem] at hj_in
    rcases hj_in with heq | heq | heq
    · have := (List.Nodup.getElem_inj_iff h.1).mp heq; omega
    · have := (List.Nodup.getElem_inj_iff h.1).mp heq; omega
    · have := (List.Nodup.getElem_inj_iff h.1).mp heq; omega
  -- Show `FirstHitIn {v₁, v₂, v₃} v₃ v₁`.
  have hhit31 : Ω.FirstHitIn {v₁, v₂, v₃} v₃ v₁ := by
    obtain ⟨k, hk1, hk_eq, hk_min⟩ :=
      Ω.exists_iterate_step h i₃ (L.length + i₁ - i₃) h3 (by omega)
    have hmod : (i₃ + (L.length + i₁ - i₃)) % L.length = i₁ := by
      have h_add : i₃ + (L.length + i₁ - i₃) = L.length + i₁ := by omega
      rw [h_add, Nat.add_mod_left, Nat.mod_eq_of_lt h1]
    have hk_v₁ : (Ω.toFun^[k]) v₃ = v₁ := by
      rw [hk_eq]; congr 1
    refine ⟨k, hk1, hk_v₁, by simp, fun j hj1 hjlt hj_in => ?_⟩
    have hjL : (Ω.toFun^[j]) v₃ ∈ {v | v ∈ L} := by
      rcases hj_in with heq | heq | heq
      · rw [heq]; exact List.getElem_mem h1
      · rw [heq]; exact List.getElem_mem h2
      · rw [heq]; exact List.getElem_mem h3
    obtain ⟨m, hm1, hmd, hm_eq⟩ := hk_min j hj1 hjlt hjL
    rw [hm_eq] at hj_in
    have hmod_ne : (i₃ + m) % L.length ≠ i₁ ∧ (i₃ + m) % L.length ≠ i₂ ∧ (i₃ + m) % L.length ≠ i₃
      := by
      by_cases hlt_len : i₃ + m < L.length
      · rw [Nat.mod_eq_of_lt hlt_len]
        omega
      · have h_sub : (i₃ + m) % L.length = i₃ + m - L.length := by
          have h_eq : i₃ + m = L.length + (i₃ + m - L.length) := by omega
          conv_lhs => rw [h_eq]
          rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        rw [h_sub]
        omega
    rcases hj_in with heq | heq | heq
    · exact hmod_ne.1 ((List.Nodup.getElem_inj_iff h.1).mp heq)
    · exact hmod_ne.2.1 ((List.Nodup.getElem_inj_iff h.1).mp heq)
    · exact hmod_ne.2.2 ((List.Nodup.getElem_inj_iff h.1).mp heq)
  refine ⟨⟨hv₂, ?_⟩, Ω.isClockwise3_iff.mpr ⟨hne12, hne13, hne23, hv₁, hv₂, hv₃, hhit12, hhit23,
    hhit31⟩⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or]
  exact ⟨hne12.symm, hne23⟩

/-- Every nonempty subset `W ⊆ Ω.bar` has a clockwise enumeration `L` starting at any given
`w₀ ∈ W`. -/
theorem exists_isClockwiseSeq_of_subset_bar {W : Set α} (hW_bar : W ⊆ Ω.bar)
    {w₀ : α} (hw₀ : w₀ ∈ W) :
    ∃ L : List α,
      L.length = W.ncard ∧
      {v | v ∈ L} = W ∧
      (∀ (h0 : 0 < L.length), L[0]'h0 = w₀) ∧
      Ω.IsClockwiseSeq L := by
  classical
  have hW_fin : W.Finite := Ω.finite_bar.subset hW_bar
  have hne : (Ω.bar ∩ W).Nonempty := ⟨w₀, hW_bar hw₀, hw₀⟩
  let nextW (x : α) : α :=
    if hx : x ∈ Ω.bar then (Ω.exists_firstHitIn hx hne).choose else x
  have hnext_spec : ∀ {x : α}, x ∈ Ω.bar → Ω.FirstHitIn W x (nextW x) := by
    intro x hx
    simp only [nextW, hx, ↓reduceDIte]
    exact (Ω.exists_firstHitIn hx hne).choose_spec
  have hnext_mem : ∀ {x : α}, x ∈ W → nextW x ∈ W := fun hx =>
    (hnext_spec (hW_bar hx)).mem_set
  have hiter_mem : ∀ (m : ℕ) {x : α}, x ∈ W → (nextW^[m]) x ∈ W := by
    intro m
    induction m with
    | zero => intro x hx; exact hx
    | succ m ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      exact hnext_mem (ih hx)
  have hnext_inj : Set.InjOn nextW W := by
    intro x₁ hx₁ x₂ hx₂ heq
    have h₁ := hnext_spec (hW_bar hx₁)
    have h₂ := hnext_spec (hW_bar hx₂)
    rw [heq] at h₁
    exact h₁.inj_left (hW_bar hx₁) (hW_bar hx₂) hx₁ hx₂ h₂
  have hiter_inj : ∀ m : ℕ, Set.InjOn (nextW^[m]) W := by
    intro m
    induction m with
    | zero => exact Set.injOn_id W
    | succ m ih =>
      intro x₁ hx₁ x₂ hx₂ heq
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at heq
      exact ih hx₁ hx₂ (hnext_inj (hiter_mem m hx₁) (hiter_mem m hx₂) heq)
  -- Every `z ∈ W` is reachable from `w₀` by iterating `nextW`.
  have hreach_aux : ∀ (K : ℕ) {x z : α}, x ∈ W → z ∈ W → (Ω.toFun^[K]) x = z →
      ∃ m : ℕ, (nextW^[m]) x = z := by
    intro K
    induction K using Nat.strong_induction_on with
    | ind K ih =>
      intro x z hx hz hK
      rcases Nat.eq_zero_or_pos K with rfl | hK_pos
      · exact ⟨0, hK⟩
      · obtain ⟨k₁, hk₁_pos, hk₁_eq, _, hk₁_min⟩ := hnext_spec (hW_bar hx)
        have hk₁_le : k₁ ≤ K := by
          by_contra hgt
          exact hk₁_min K hK_pos (by omega) (hK ▸ hz)
        have hrem : (Ω.toFun^[K - k₁]) (nextW x) = z := by
          have hiter : (Ω.toFun^[k₁]) ((Ω.toFun^[K - k₁]) (nextW x)) = (Ω.toFun^[k₁]) z := by
            rw [← hk₁_eq]
            simp only [← Function.iterate_add_apply]
            rw [Nat.sub_add_cancel hk₁_le, Function.iterate_add_apply, hK]
          exact Ω.injOn_iterate k₁ (Ω.iterate_mem (K - k₁) (hW_bar (hnext_mem hx)))
            (hW_bar hz) hiter
        obtain ⟨m, hm⟩ := ih (K - k₁) (by omega) (hnext_mem hx) hz hrem
        refine ⟨m + 1, ?_⟩
        rw [Function.iterate_succ_apply, hm]
  have hreach : ∀ z ∈ W, ∃ m : ℕ, (nextW^[m]) w₀ = z := by
    intro z hz
    obtain ⟨K, hK⟩ := Ω.single_orbit w₀ (hW_bar hw₀) z (hW_bar hz)
    exact hreach_aux K hw₀ hz hK
  let n := W.ncard
  have hn_pos : 0 < n := Set.ncard_pos hW_fin |>.mpr ⟨w₀, hw₀⟩
  let L := (List.range n).map (fun i => (nextW^[i]) w₀)
  have hL_len : L.length = n := by simp [L]
  have hL_get : ∀ (i : ℕ) (hi : i < L.length), L[i]'hi = (nextW^[i]) w₀ := by
    intro i hi
    simp [L]
  have hL_sub_W : {v | v ∈ L} ⊆ W := by
    intro v hv
    simp only [L, mem_ofPred_eq, List.mem_map, List.mem_range] at hv
    rcases hv with ⟨i, _, rfl⟩
    exact hiter_mem i hw₀
  -- If `(nextW^[d]) w₀ = w₀` for `1 ≤ d`, then `n ≤ d`.
  have hperiod_ge : ∀ d : ℕ, 1 ≤ d → (nextW^[d]) w₀ = w₀ → n ≤ d := by
    intro d hd1 hd_eq
    have hmul : ∀ q : ℕ, (nextW^[d * q]) w₀ = w₀ := by
      intro q
      induction q with
      | zero => rfl
      | succ q ih =>
        rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih, hd_eq]
    let Ld := (List.range d).map (fun r => (nextW^[r]) w₀)
    have hW_sub_Ld : W ⊆ {v | v ∈ Ld} := by
      intro z hz
      obtain ⟨m, rfl⟩ := hreach z hz
      have hm_eq : (nextW^[m]) w₀ = (nextW^[m % d]) w₀ := by
        conv_lhs => rw [← Nat.div_add_mod m d, add_comm]
        rw [Function.iterate_add_apply, hmul]
      rw [hm_eq]
      simp only [Ld, mem_ofPred_eq, List.mem_map, List.mem_range]
      exact ⟨m % d, Nat.mod_lt m hd1, rfl⟩
    have hLd_fin : {v | v ∈ Ld}.Finite := Ld.toFinset.finite_toSet.subset (fun _ hx
      => List.mem_toFinset.mpr hx)
    have hcard_le : n ≤ {v | v ∈ Ld}.ncard := Set.ncard_le_ncard hW_sub_Ld hLd_fin
    have hLd_eq : {v | v ∈ Ld} = (Ld.toFinset : Set α) := by ext x; simp
    have hLd_card : {v | v ∈ Ld}.ncard ≤ d := by
      rw [hLd_eq, Set.ncard_coe_finset]
      exact (List.toFinset_card_le Ld).trans (by simp [Ld])
    exact hcard_le.trans hLd_card
  have hL_nodup : L.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [Fin.mk.injEq]
    dsimp only at hij
    rw [hL_get i hi, hL_get j hj] at hij
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exfalso
      have heq_d : (nextW^[j - i]) w₀ = w₀ := by
        have hiter : (nextW^[i]) ((nextW^[j - i]) w₀) = (nextW^[i]) w₀ := by
          rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hlt), hij]
        exact hiter_inj i (hiter_mem (j - i) hw₀) hw₀ hiter
      have hge := hperiod_ge (j - i) (by omega) heq_d
      omega
    · rfl
    · exfalso
      have heq_d : (nextW^[i - j]) w₀ = w₀ := by
        have hiter : (nextW^[j]) ((nextW^[i - j]) w₀) = (nextW^[j]) w₀ := by
          rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hgt), ← hij]
        exact hiter_inj j (hiter_mem (i - j) hw₀) hw₀ hiter
      have hge := hperiod_ge (i - j) (by omega) heq_d
      omega
  have hL_ncard : {v | v ∈ L}.ncard = n := by
    have h_eq : {v | v ∈ L} = (L.toFinset : Set α) := by ext x; simp
    rw [h_eq, Set.ncard_coe_finset, List.card_toFinset, List.dedup_eq_self.mpr hL_nodup, hL_len]
  have hL_eq_W : {v | v ∈ L} = W :=
    Set.eq_of_subset_of_ncard_le hL_sub_W (by rw [hL_ncard]) hW_fin
  have hn_eq_w₀ : (nextW^[n]) w₀ = w₀ := by
    have hn_in_L : (nextW^[n]) w₀ ∈ {v | v ∈ L} := by
      rw [hL_eq_W]
      exact hiter_mem n hw₀
    simp only [L, mem_ofPred_eq, List.mem_map, List.mem_range] at hn_in_L
    rcases hn_in_L with ⟨i, hi, hi_eq⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi_pos
    · exact hi_eq.symm
    · exfalso
      have heq_d : (nextW^[n - i]) w₀ = w₀ := by
        have hiter : (nextW^[i]) ((nextW^[n - i]) w₀) = (nextW^[i]) w₀ := by
          rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hi), ← hi_eq]
        exact hiter_inj i (hiter_mem (n - i) hw₀) hw₀ hiter
      have hge := hperiod_ge (n - i) (by omega) heq_d
      omega
  refine ⟨L, hL_len, hL_eq_W, fun h0 => by simp [L], hL_nodup, ?_, ?_⟩
  · intro v hv
    exact hW_bar (hL_sub_W hv)
  · intro i hi
    rw [hL_eq_W, hL_get i hi, hL_get ((i + 1) % L.length) (Nat.mod_lt _ (by omega))]
    rw [hL_len] at hi ⊢
    by_cases hlt : i + 1 < n
    · rw [Nat.mod_eq_of_lt hlt, Function.iterate_succ_apply']
      exact hnext_spec (hW_bar (hiter_mem i hw₀))
    · have hi_eq : i + 1 = n := by omega
      have h_rhs : (nextW^[(i + 1) % n]) w₀ = nextW ((nextW^[i]) w₀) := by
        conv_lhs => rw [hi_eq, Nat.mod_self, Function.iterate_zero_apply, ← hn_eq_w₀, ← hi_eq,
          Function.iterate_succ_apply']
      rw [h_rhs]
      exact hnext_spec (hW_bar (hiter_mem i hw₀))

end CyclicPerm

/-! ## Ordering non-crossing transactions and `AreInOrder` properties -/

namespace Society

variable (S : Society α β)

/-- If `[Q₁, Q₂, Q₃]` are in order with ends `a_i, b_i` (`i = 1, 2, 3`) such that
`[a₃, a₂, a₁, b₁, b₂, b₃]` is clockwise, then `a₁, b₁ ∈ S.Ω.interval a₂ b₂` and
`a₃, b₃ ∈ S.Ω.interval b₂ a₂`. -/
theorem mem_intervals_of_isClockwiseSeq_six {a₁ a₂ a₃ b₁ b₂ b₃ : α}
    (h : S.Ω.IsClockwiseSeq [a₃, a₂, a₁, b₁, b₂, b₃]) :
    a₁ ∈ S.Ω.interval a₂ b₂ ∧ b₁ ∈ S.Ω.interval a₂ b₂ ∧
    a₃ ∈ S.Ω.interval b₂ a₂ ∧ b₃ ∈ S.Ω.interval b₂ a₂ := by
  have hlen4 : 4 < [a₃, a₂, a₁, b₁, b₂, b₃].length := by simp
  have hlen5 : 5 < [a₃, a₂, a₁, b₁, b₂, b₃].length := by simp
  have ha₁ : a₁ ∈ S.Ω.interval a₂ b₂ :=
    S.Ω.mem_interval_of_lt h (i₁ := 1) (i₂ := 2) (i₃ := 4) (by decide) (by decide) hlen4
  have hb₁ : b₁ ∈ S.Ω.interval a₂ b₂ :=
    S.Ω.mem_interval_of_lt h (i₁ := 1) (i₂ := 3) (i₃ := 4) (by decide) (by decide) hlen4
  have ha₂_in : a₂ ∈ S.Ω.interval a₃ b₂ :=
    S.Ω.mem_interval_of_lt h (i₁ := 0) (i₂ := 1) (i₃ := 4) (by decide) (by decide) hlen4
  have hb₂_in : b₂ ∈ S.Ω.interval a₂ b₃ :=
    S.Ω.mem_interval_of_lt h (i₁ := 1) (i₂ := 4) (i₃ := 5) (by decide) (by decide) hlen5
  exact ⟨ha₁, hb₁, S.Ω.mem_interval_rotate_right ha₂_in, S.Ω.mem_interval_rotate_left hb₂_in⟩

/-- In a fence `(A, B)` for `P_set`, `(A ∩ S.transactionEnds P_set).ncard = P_set.ncard` and
`(B ∩ S.transactionEnds P_set).ncard = P_set.ncard` and
`(S.transactionEnds P_set).ncard = 2 * P_set.ncard`. -/
theorem IsFenceFor.ncard_transactionEnds {P_set : Set (Graph α β)} {A B : Set α}
    (hfence : S.IsFenceFor P_set A B) :
    (A ∩ S.transactionEnds P_set).ncard = P_set.ncard ∧
    (B ∩ S.transactionEnds P_set).ncard = P_set.ncard ∧
    (S.transactionEnds P_set).ncard = 2 * P_set.ncard := by
  classical
  by_cases hP_ne : P_set.Nonempty
  · obtain ⟨P₀, hP₀_in⟩ := hP_ne
    obtain ⟨a₀, _, b₀, _, _⟩ := hfence.2.2 P₀ hP₀_in
    let endA (P : Graph α β) : α :=
      if hP : P ∈ P_set then (hfence.2.2 P hP).choose else a₀
    let endB (P : Graph α β) : α :=
      if hP : P ∈ P_set then (hfence.2.2 P hP).choose_spec.2.choose else b₀
    have hend_spec : ∀ {P : Graph α β}, P ∈ P_set →
        endA P ∈ A ∧ endB P ∈ B ∧ S.IsOmegaPathWithEnds P (endA P) (endB P) := by
      intro P hP
      simp only [endA, endB, hP, ↓reduceDIte]
      exact ⟨(hfence.2.2 P hP).choose_spec.1,
        (hfence.2.2 P hP).choose_spec.2.choose_spec.1,
        (hfence.2.2 P hP).choose_spec.2.choose_spec.2⟩
    have hA_eq : A ∩ S.transactionEnds P_set = endA '' P_set := by
      ext x
      simp only [mem_inter_iff, mem_image]
      constructor
      · rintro ⟨hxA, P, hP_in, y, hxy⟩
        refine ⟨P, hP_in, ?_⟩
        obtain ⟨_, hbB, hP_ends⟩ := hend_spec hP_in
        rcases hP_ends.ends_eq S hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact (disjoint_left.mp hfence.2.1.2.2.1 hxA hbB).elim
      · rintro ⟨P, hP_in, rfl⟩
        obtain ⟨haA, _, hP_ends⟩ := hend_spec hP_in
        exact ⟨haA, hP_ends.mem_transactionEnds_left S hP_in⟩
    have hB_eq : B ∩ S.transactionEnds P_set = endB '' P_set := by
      ext x
      simp only [mem_inter_iff, mem_image]
      constructor
      · rintro ⟨hxB, P, hP_in, y, hxy⟩
        refine ⟨P, hP_in, ?_⟩
        obtain ⟨haA, _, hP_ends⟩ := hend_spec hP_in
        rcases hP_ends.ends_eq S hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (disjoint_left.mp hfence.2.1.2.2.1 haA hxB).elim
        · rfl
      · rintro ⟨P, hP_in, rfl⟩
        obtain ⟨_, hbB, hP_ends⟩ := hend_spec hP_in
        exact ⟨hbB, hP_ends.mem_transactionEnds_right S hP_in⟩
    have hinj_A : Set.InjOn endA P_set := by
      intro P₁ hP₁ P₂ hP₂ heq
      by_contra hne
      exact disjoint_left.mp (hfence.1.2 hP₁ hP₂ hne)
        (hend_spec hP₁).2.2.1.left_mem (heq ▸ (hend_spec hP₂).2.2.1.left_mem)
    have hinj_B : Set.InjOn endB P_set := by
      intro P₁ hP₁ P₂ hP₂ heq
      by_contra hne
      exact disjoint_left.mp (hfence.1.2 hP₁ hP₂ hne)
        (hend_spec hP₁).2.2.1.right_mem (heq ▸ (hend_spec hP₂).2.2.1.right_mem)
    have hncard_A : (A ∩ S.transactionEnds P_set).ncard = P_set.ncard := by
      rw [hA_eq, hinj_A.ncard_image]
    have hncard_B : (B ∩ S.transactionEnds P_set).ncard = P_set.ncard := by
      rw [hB_eq, hinj_B.ncard_image]
    have hW_union : (A ∩ S.transactionEnds P_set) ∪ (B ∩ S.transactionEnds P_set) =
        S.transactionEnds P_set := by
      rw [← union_inter_distrib_right, hfence.2.1.2.2.2.1,
        inter_eq_self_of_subset_right (S.transactionEnds_subset_bar P_set)]
    have hdisj_AB : Disjoint (A ∩ S.transactionEnds P_set) (B ∩ S.transactionEnds P_set) :=
      hfence.2.1.2.2.1.mono inter_subset_left inter_subset_left
    have hfin_W : (S.transactionEnds P_set).Finite :=
      S.Ω.finite_bar.subset (S.transactionEnds_subset_bar P_set)
    have hncard_W : (S.transactionEnds P_set).ncard = 2 * P_set.ncard := by
      rw [← hW_union, Set.ncard_union_eq hdisj_AB (hfin_W.subset inter_subset_right)
        (hfin_W.subset inter_subset_right), hncard_A, hncard_B, two_mul]
    exact ⟨hncard_A, hncard_B, hncard_W⟩
  · have hP_empty : P_set = ∅ := Set.not_nonempty_iff_eq_empty.mp hP_ne
    subst hP_empty
    have hW_empty : S.transactionEnds ∅ = ∅ := by
      ext x; simp [transactionEnds]
    simp [hW_empty]

/-- A clockwise list of transaction ends starts in the first fence side and ends in the second. -/
theorem transaction_end_list_partitions_fence {F : Set (Graph α β)} {A B : Set α}
    (hfence : S.IsFenceFor F A B) {b_k a_k : α} {L : List α}
    (hk_pos : 0 < F.ncard) (hL_len : L.length = 2 * F.ncard) (hL_cw : S.Ω.IsClockwiseSeq L)
    (hL_0 : ∀ h0 : 0 < L.length, L[0]'h0 = a_k) :
    let W := S.transactionEnds F
    {v | v ∈ L} = W →
    b_k ∈ B ∩ W → a_k ∈ A ∩ W → Disjoint (S.Ω.interval b_k a_k) W →
    L[2 * F.ncard - 1]'(by omega) = b_k ∧
    (∀ (i : ℕ) (hi : i < L.length), i < F.ncard → L[i]'hi ∈ A) ∧
    (∀ (i : ℕ) (hi : i < L.length), F.ncard ≤ i → L[i]'hi ∈ B) := by
  classical
  intro W hL_set hb_k ha_k hd_bk_ak
  let k := F.ncard
  have hW_bar : W ⊆ S.Ω.bar := S.transactionEnds_subset_bar F
  obtain ⟨hncard_A, hncard_B, _⟩ := hfence.ncard_transactionEnds S
  have h2k_pos : 0 < L.length := by omega
  -- Show `L[2 * k - 1] = b_k`.
  have hL_last : L[2 * k - 1]'(by omega) = b_k := by
    have hhit_last : S.Ω.FirstHitIn W (L[2 * k - 1]'(by omega)) a_k := by
      have h := hL_cw.2.2 (2 * k - 1) (by omega)
      have hmod : (2 * k - 1 + 1) % L.length = 0 := by
        rw [hL_len, Nat.sub_add_cancel (by omega), Nat.mod_self]
      rw [hL_set] at h
      simpa [hmod, hL_0 h2k_pos] using h
    have hbk_ne_ak : b_k ≠ a_k :=
      fun h => disjoint_left.mp hfence.2.1.2.2.1 ha_k.1 (h ▸ hb_k.1)
    have hhit_bk : S.Ω.FirstHitIn W b_k a_k :=
      (S.Ω.firstHitIn_iff_disjoint_interval hW_bar hb_k.2 ha_k.2 hbk_ne_ak).mpr
        hd_bk_ak
    have hlast_W : L[2 * k - 1]'(by omega) ∈ W := by
      rw [← hL_set]; exact List.getElem_mem (by omega)
    exact hhit_last.inj_left (hW_bar hlast_W) (hW_bar hb_k.2) hlast_W hb_k.2 hhit_bk
  -- No `B`-element can precede an `A`-element in `L`.
  have hno_BA : ∀ (i j : ℕ) (hi : i < L.length) (hj : j < L.length),
      i < j → L[i]'hi ∈ B → L[j]'hj ∈ A → False := by
    intro i j hi hj hij hLiB hLjA
    have hi_gt : 0 < i := by
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [hL_0 h2k_pos] at hLiB
        exact (disjoint_left.mp hfence.2.1.2.2.1 ha_k.1 hLiB).elim
      · exact hpos
    have hj_lt : j < 2 * k - 1 := by
      by_contra hge
      have hj_eq : j = 2 * k - 1 := by omega
      subst hj_eq
      rw [hL_last] at hLjA
      exact disjoint_left.mp hfence.2.1.2.2.1 hLjA hb_k.1
    have hLi_in : L[i]'hi ∈ S.Ω.interval a_k (L[j]'hj) := by
      have h := S.Ω.mem_interval_of_lt hL_cw hi_gt hij hj
      simpa [hL_0 h2k_pos] using h
    have hLj_in : L[j]'hj ∈ S.Ω.interval a_k b_k := by
      have h := S.Ω.mem_interval_of_lt hL_cw (Nat.lt_trans hi_gt hij) hj_lt (by omega)
      simpa [hL_0 h2k_pos, hL_last] using h
    have hbk_in : b_k ∈ S.Ω.interval (L[j]'hj) a_k := S.Ω.mem_interval_rotate_left hLj_in
    have hcr : S.Ω.Crosses a_k (L[j]'hj) (L[i]'hi) b_k :=
      S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hLi_in, hbk_in⟩)
    exact hfence.2.1.2.2.2.2 a_k ha_k.1 (L[j]'hj) hLjA
      (fun h => by
        have h0j : L[0]'h2k_pos = L[j]'hj := (hL_0 h2k_pos).trans h
        have := (List.Nodup.getElem_inj_iff hL_cw.1).mp h0j
        omega)
      (L[i]'hi) hLiB b_k hb_k.1
      (fun h => by
        have hij' : L[i]'hi = L[2 * k - 1]'(by omega) := h.trans hL_last.symm
        have := (List.Nodup.getElem_inj_iff hL_cw.1).mp hij'
        omega)
      hcr
  -- Deduce `L[i] ∈ A` for `i < k` and `L[i] ∈ B` for `k ≤ i < 2 * k`.
  have hL_A : ∀ (i : ℕ) (hi : i < L.length), i < k → L[i]'hi ∈ A := by
    intro i hi hik
    have hLi_W : L[i]'hi ∈ W := by rw [← hL_set]; exact List.getElem_mem hi
    have hLi_AB : L[i]'hi ∈ A ∪ B := by rw [hfence.2.1.2.2.2.1]; exact hW_bar hLi_W
    rcases hLi_AB with hA | hB
    · exact hA
    · exfalso
      have hsub : A ∩ W ⊆ {v | v ∈ L.take i} := by
        intro x ⟨hxA, hxW⟩
        rw [← hL_set] at hxW
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hxW
        have hji : j < i := by
          by_contra hge
          rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
          · exact disjoint_left.mp hfence.2.1.2.2.1 hxA hB
          · exact hno_BA i j hi hj hgt hB hxA
        rw [mem_ofPred_eq, List.mem_take_iff_getElem]
        exact ⟨j, by omega, rfl⟩
      have hfin_take : {v | v ∈ L.take i}.Finite :=
        (L.take i).toFinset.finite_toSet.subset (fun _ hx => List.mem_toFinset.mpr hx)
      have hle1 : k ≤ {v | v ∈ L.take i}.ncard := by
        change F.ncard ≤ _
        rw [← hncard_A]
        exact Set.ncard_le_ncard hsub hfin_take
      have h_eq : {v | v ∈ L.take i} = ((L.take i).toFinset : Set α) := by ext x; simp
      have hle2 : {v | v ∈ L.take i}.ncard ≤ i := by
        rw [h_eq, Set.ncard_coe_finset]
        exact (List.toFinset_card_le (L.take i)).trans (by simp [Nat.le_of_lt hi])
      omega
  have hL_B : ∀ (i : ℕ) (hi : i < L.length), k ≤ i → L[i]'hi ∈ B := by
    intro i hi hki
    have hLi_W : L[i]'hi ∈ W := by rw [← hL_set]; exact List.getElem_mem hi
    have hLi_AB : L[i]'hi ∈ A ∪ B := by rw [hfence.2.1.2.2.2.1]; exact hW_bar hLi_W
    rcases hLi_AB with hA | hB
    · exfalso
      have hsub : B ∩ W ⊆ {v | v ∈ L.drop (i + 1)} := by
        intro x ⟨hxB, hxW⟩
        rw [← hL_set] at hxW
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hxW
        have hij : i < j := by
          by_contra hle
          rcases eq_or_lt_of_le (Nat.le_of_not_lt hle) with rfl | hlt
          · exact disjoint_left.mp hfence.2.1.2.2.1 hA hxB
          · exact hno_BA j i hj hi hlt hxB hA
        rw [mem_ofPred_eq, List.mem_iff_getElem]
        refine ⟨j - (i + 1), by simp; omega, ?_⟩
        simp [Nat.add_sub_of_le (by omega : i + 1 ≤ j)]
      have hfin_drop : {v | v ∈ L.drop (i + 1)}.Finite :=
        (L.drop (i + 1)).toFinset.finite_toSet.subset (fun _ hx => List.mem_toFinset.mpr hx)
      have hle1 : k ≤ {v | v ∈ L.drop (i + 1)}.ncard := by
        change F.ncard ≤ _
        rw [← hncard_B]
        exact Set.ncard_le_ncard hsub hfin_drop
      have h_eq : {v | v ∈ L.drop (i + 1)} = ((L.drop (i + 1)).toFinset : Set α) := by ext x; simp
      have hle2 : {v | v ∈ L.drop (i + 1)}.ncard ≤ L.length - (i + 1) := by
        rw [h_eq, Set.ncard_coe_finset]
        exact (List.toFinset_card_le (L.drop (i + 1))).trans (by simp)
      omega
    · exact hB
  exact ⟨hL_last, hL_A, hL_B⟩

/-- Every transaction `F` in which no two members cross can be enumerated as a list `Q` of length
`F.ncard` with `{P | P ∈ Q} = F` and `S.AreInOrder Q`. -/
theorem IsTransaction.exists_areInOrder_of_not_cross {F : Set (Graph α β)}
    (htrans : S.IsTransaction F)
    (hno_cross : ∀ P₁ ∈ F, ∀ P₂ ∈ F, ¬ S.OmegaPathsCross P₁ P₂) :
    ∃ Q : List (Graph α β),
      Q.length = F.ncard ∧
      Q.Nodup ∧
      {P | P ∈ Q} = F ∧
      S.AreInOrder Q := by
  classical
  by_cases hF_ne : F.Nonempty
  · obtain ⟨A, B, hfence⟩ := htrans
    let W := S.transactionEnds F
    have hW_bar : W ⊆ S.Ω.bar := S.transactionEnds_subset_bar F
    obtain ⟨_, _, hncard_W⟩ := hfence.ncard_transactionEnds S
    let k := F.ncard
    have hfin_F : F.Finite := hfence.1.finite S
    have hk_pos : 0 < k := Set.ncard_pos hfin_F |>.mpr hF_ne
    obtain ⟨P₀, hP₀_in⟩ := hF_ne
    obtain ⟨a₀, ha₀A, b₀, hb₀B, hP₀_ends⟩ := hfence.2.2 P₀ hP₀_in
    have ha₀W : a₀ ∈ A ∩ W := ⟨ha₀A, hP₀_ends.mem_transactionEnds_left S hP₀_in⟩
    have hb₀W : b₀ ∈ B ∩ W := ⟨hb₀B, hP₀_ends.mem_transactionEnds_right S hP₀_in⟩
    have hW_sub_BA : W ⊆ B ∪ A := by
      rw [union_comm, hfence.2.1.2.2.2.1]; exact hW_bar
    obtain ⟨b_k, hb_k, a_k, ha_k, hd_bk_ak⟩ :=
      S.Ω.exists_empty_interval_AB_of_subset_union hW_bar hW_sub_BA ⟨b₀, hb₀W⟩ ⟨a₀, ha₀W⟩
    obtain ⟨L, hL_len_W, hL_set, hL_0, hL_cw⟩ :=
      S.Ω.exists_isClockwiseSeq_of_subset_bar hW_bar ha_k.2
    have hL_len : L.length = 2 * k := hL_len_W.trans hncard_W
    obtain ⟨-, hL_A, hL_B⟩ :=
      transaction_end_list_partitions_fence S hfence hk_pos hL_len hL_cw hL_0 hL_set
        hb_k ha_k hd_bk_ak
    -- Define `a_list` and `b_list` so `a_list.reverse ++ b_list = L`.
    let a_list := List.ofFn (fun i : Fin k => L[k - 1 - i.1]'(by omega))
    let b_list := List.ofFn (fun i : Fin k => L[k + i.1]'(by omega))
    have ha_len : a_list.length = k := by simp [a_list]
    have hb_len : b_list.length = k := by simp [b_list]
    have hrev_append : a_list.reverse ++ b_list = L := by
      apply List.ext_getElem
      · simp [a_list, b_list, hL_len, two_mul]
      · intro i hi₁ hi₂
        rw [List.getElem_append]
        split_ifs with hik
        · have hik' : i < k := by simpa [a_list] using hik
          rw [List.getElem_reverse]
          simp only [a_list, List.length_ofFn, List.getElem_ofFn]
          congr 1
          omega
        · have hik' : ¬ i < k := by simpa [a_list] using hik
          simp only [a_list, b_list, List.length_reverse, List.length_ofFn, List.getElem_ofFn]
          congr 1
          omega
    -- For each `i < k`, find `Q_i ∈ F` with end `a_list[i] ∈ A` and other end `b_list[φ i] ∈ B`.
    have hex_Q : ∀ i : ℕ, (hi : i < k) →
        ∃ P ∈ F, ∃ j : ℕ, ∃ hj : j < k,
          S.IsOmegaPathWithEnds P (L[k - 1 - i]'(by omega)) (L[k + j]'(by omega)) := by
      intro i hi
      have h_in_W : L[k - 1 - i]'(by omega) ∈ W := by
        rw [← hL_set]; exact List.getElem_mem (by omega)
      have h_in_A : L[k - 1 - i]'(by omega) ∈ A := hL_A (k - 1 - i) (by omega) (by omega)
      obtain ⟨P, hP_in, y, hPy⟩ := h_in_W
      obtain ⟨aP, haPA, bP, hbPB, hP_ends⟩ := hfence.2.2 P hP_in
      have haP_eq : aP = L[k - 1 - i]'(by omega) := by
        rcases hP_ends.ends_eq S hPy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact (disjoint_left.mp hfence.2.1.2.2.1 h_in_A hbPB).elim
      subst haP_eq
      have hbP_W : bP ∈ W := hP_ends.mem_transactionEnds_right S hP_in
      rw [← hL_set] at hbP_W
      obtain ⟨m, hm, hm_eq⟩ := List.getElem_of_mem hbP_W
      have hmk : k ≤ m := by
        by_contra hlt
        exact disjoint_left.mp hfence.2.1.2.2.1 (hL_A m hm (by omega)) (hm_eq ▸ hbPB)
      refine ⟨P, hP_in, m - k, by omega, ?_⟩
      have hm_add : k + (m - k) = m := Nat.add_sub_of_le hmk
      simpa [hm_add, hm_eq] using hP_ends
    let Q_fn (i : ℕ) : Graph α β :=
      if hi : i < k then (hex_Q i hi).choose else P₀
    let φ (i : ℕ) : ℕ :=
      if hi : i < k then (hex_Q i hi).choose_spec.2.choose else 0
    have hQ_spec : ∀ (i : ℕ) (hi : i < k),
        Q_fn i ∈ F ∧ φ i < k ∧
          S.IsOmegaPathWithEnds (Q_fn i) (L[k - 1 - i]'(by omega))
            (L[k + φ i]'(by
              have hlt : φ i < k := by
                simp only [φ, hi, ↓reduceDIte]
                exact (hex_Q i hi).choose_spec.2.choose_spec.1
              omega)) := by
      intro i hi
      simp only [Q_fn, φ, hi, ↓reduceDIte]
      exact ⟨(hex_Q i hi).choose_spec.1,
        (hex_Q i hi).choose_spec.2.choose_spec.1,
        (hex_Q i hi).choose_spec.2.choose_spec.2⟩
    have hQ_inj : ∀ i j : ℕ, i < k → j < k → Q_fn i = Q_fn j → i = j := by
      intro i j hi hj heq
      have h₁ := (hQ_spec i hi).2.2
      have h₂ := (hQ_spec j hj).2.2
      rw [heq] at h₁
      rcases h₁.ends_eq S h₂ with ⟨h_eq, _⟩ | ⟨h_eq, _⟩
      · have := (List.Nodup.getElem_inj_iff hL_cw.1).mp h_eq; omega
      · exfalso
        have hA_j : L[k - 1 - j]'(by omega) ∈ A := hL_A (k - 1 - j) (by omega) (by omega)
        have hB_i : L[k + φ i]'(by have := (hQ_spec i hi).2.1; omega) ∈ B :=
          hL_B (k + φ i) (by have := (hQ_spec i hi).2.1; omega) (by omega)
        exact disjoint_left.mp hfence.2.1.2.2.1 hA_j (h_eq ▸ hB_i)
    -- Show `φ` is strictly increasing on `0 ..< k`, hence `φ i = i`.
    have hφ_mono : ∀ i j : ℕ, i < j → j < k → φ i < φ j := by
      intro i j hij hj
      have hi : i < k := Nat.lt_trans hij hj
      obtain ⟨hQi_F, hφi, hQi_ends⟩ := hQ_spec i hi
      obtain ⟨hQj_F, hφj, hQj_ends⟩ := hQ_spec j hj
      have hne_Q : Q_fn i ≠ Q_fn j := fun h => Nat.ne_of_lt hij (hQ_inj i j hi hj h)
      have hdisj_Q : Disjoint V(Q_fn i) V(Q_fn j) := hfence.1.2 hQi_F hQj_F hne_Q
      rcases lt_trichotomy (φ i) (φ j) with hlt | heq | hgt
      · exact hlt
      · exfalso
        have h_same_b : L[k + φ i]'(by omega) = L[k + φ j]'(by omega) := by congr 1; omega
        exact disjoint_left.mp hdisj_Q hQi_ends.1.right_mem (h_same_b ▸ hQj_ends.1.right_mem)
      · exfalso
        have h1 : k - 1 - j < k - 1 - i := by omega
        have h2 : k - 1 - i < k + φ j := by omega
        have h3 : k + φ j < k + φ i := by omega
        have h4 : k + φ i < L.length := by omega
        have h_ai_in : L[k - 1 - i]'(by omega) ∈
            S.Ω.interval (L[k - 1 - j]'(by omega)) (L[k + φ j]'(by omega)) :=
          S.Ω.mem_interval_of_lt hL_cw h1 h2 (Nat.lt_trans h3 h4)
        have h_bj_in : L[k + φ j]'(by omega) ∈
            S.Ω.interval (L[k - 1 - j]'(by omega)) (L[k + φ i]'(by omega)) :=
          S.Ω.mem_interval_of_lt hL_cw (Nat.lt_trans h1 h2) h3 h4
        have h_bi_in : L[k + φ i]'(by omega) ∈
            S.Ω.interval (L[k + φ j]'(by omega)) (L[k - 1 - j]'(by omega)) :=
          S.Ω.mem_interval_rotate_left h_bj_in
        have hcr : S.Ω.Crosses (L[k - 1 - j]'(by omega)) (L[k + φ j]'(by omega))
            (L[k - 1 - i]'(by omega)) (L[k + φ i]'(by omega)) :=
          S.Ω.crosses_iff_interval.mpr (Or.inl ⟨h_ai_in, h_bi_in⟩)
        exact hno_cross (Q_fn j) hQj_F (Q_fn i) hQi_F
          ⟨hdisj_Q.symm, _, _, _, _, hQj_ends, hQi_ends, hcr⟩
    have hφ_ge : ∀ i : ℕ, i < k → i ≤ φ i := by
      intro i
      induction i with
      | zero => intro _; exact Nat.zero_le _
      | succ i ih =>
        intro hi
        have := ih (Nat.lt_of_succ_lt hi)
        have := hφ_mono i (i + 1) (Nat.lt_succ_self i) hi
        omega
    have hφ_le : ∀ d : ℕ, d < k → φ (k - 1 - d) ≤ k - 1 - d := by
      intro d
      induction d with
      | zero =>
        intro hd
        have hlt := (hQ_spec (k - 1) (by omega)).2.1
        simpa using Nat.le_sub_one_of_lt hlt
      | succ d ih =>
        intro hd
        have := ih (Nat.lt_of_succ_lt hd)
        have := hφ_mono (k - 1 - (d + 1)) (k - 1 - d) (by omega) (by omega)
        omega
    have hφ_eq : ∀ i : ℕ, i < k → φ i = i := by
      intro i hi
      have h1 := hφ_ge i hi
      have h2 := hφ_le (k - 1 - i) (by omega)
      have h_idx : k - 1 - (k - 1 - i) = i := by omega
      rw [h_idx] at h2
      omega
    let Q := (List.range k).map Q_fn
    have hQ_len : Q.length = k := by simp [Q]
    have hQ_nodup : Q.Nodup := by
      rw [List.nodup_iff_injective_getElem]
      intro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only [Fin.mk.injEq]
      simp only [Q, List.getElem_map, List.getElem_range] at hij
      simp only [Q, List.length_map, List.length_range] at hi hj
      exact hQ_inj i j hi hj hij
    have hQ_sub_F : {P | P ∈ Q} ⊆ F := by
      intro P hP
      simp only [Q, mem_ofPred_eq, List.mem_map, List.mem_range] at hP
      rcases hP with ⟨i, hi, rfl⟩
      exact (hQ_spec i hi).1
    have hQ_ncard : {P | P ∈ Q}.ncard = k := by
      have h_eq : {P | P ∈ Q} = (Q.toFinset : Set (Graph α β)) := by ext x; simp
      rw [h_eq, Set.ncard_coe_finset, List.card_toFinset, List.dedup_eq_self.mpr hQ_nodup, hQ_len]
    have hQ_eq_F : {P | P ∈ Q} = F :=
      Set.eq_of_subset_of_ncard_le hQ_sub_F (by rw [hQ_ncard]) hfin_F
    have hQ_pairwise : Q.Pairwise (fun P₁ P₂ => Disjoint V(P₁) V(P₂)) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      have hiF : Q[i]'hi ∈ F := hQ_sub_F (List.getElem_mem hi)
      have hjF : Q[j]'hj ∈ F := hQ_sub_F (List.getElem_mem hj)
      have hne : Q[i]'hi ≠ Q[j]'hj :=
        fun h => Nat.ne_of_lt hij ((List.Nodup.getElem_inj_iff hQ_nodup).mp h)
      exact hfence.1.2 hiF hjF hne
    refine ⟨Q, hQ_len, hQ_nodup, hQ_eq_F, hQ_pairwise, a_list, b_list,
      ha_len.trans hQ_len.symm, hb_len.trans hQ_len.symm, ?_, ?_⟩
    · intro i hi
      have hik : i < k := by omega
      obtain ⟨_, _, hends⟩ := hQ_spec i hik
      simp only [Q, a_list, b_list, List.getElem_map, List.getElem_range, List.getElem_ofFn]
      simpa [hφ_eq i hik] using hends
    · rwa [hrev_append]
  · have hF_empty : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hF_ne
    subst hF_empty
    refine ⟨[], by simp, List.nodup_nil, by simp, List.Pairwise.nil, [], [], rfl, rfl,
      fun i hi => by simp at hi, List.nodup_nil, fun v hv => by simp at hv,
      fun i hi => by simp at hi⟩

/-! ## Proof of (4.4) -/

/-- If `Q` is a separating `Ω`-path with ends `a_Q, b_Q` that is half-covered by `P_set`, then no
member `P ∈ P_set` can have one end in `S.Ω.interval a_Q b_Q` and the other end in
`S.Ω.interval b_Q a_Q`. -/
theorem not_ends_in_both_intervals_of_separating_halfCovered
    {P_set : Set (Graph α β)} {Q P : Graph α β} {a_Q b_Q s t : α}
    (hQ_ends : S.IsOmegaPathWithEnds Q a_Q b_Q)
    (hsep : S.IsSeparatingOmegaPath Q)
    (hcov : S.IsHalfCovered P_set Q)
    (hP_in : P ∈ P_set)
    (hP_ends : S.IsOmegaPathWithEnds P s t)
    (hs_ab : s ∈ S.Ω.interval a_Q b_Q)
    (ht_ba : t ∈ S.Ω.interval b_Q a_Q) : False := by
  have hcr : S.Ω.Crosses a_Q b_Q s t :=
    S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hs_ab, ht_ba⟩)
  have hmeet : (V(P) ∩ V(Q)).Nonempty := by
    by_contra hnot
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hnot
    exact hsep.2 ⟨P, hnot, s, t, a_Q, b_Q, hP_ends, hQ_ends, hcr.symm⟩
  rcases hcov with ⟨P₀, _, _, huniq, s₀, t₀, a₀, b₀, _, hP₀_ends, hQ₀_ends, rfl, _, _⟩
  have hPP₀ : P = P₀ := huniq P hP_in hmeet
  subst hPP₀
  have hs₀_st : s₀ = s ∨ s₀ = t := by
    rcases hP_ends.ends_eq S hP₀_ends with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hs₀_ab : s₀ = a_Q ∨ s₀ = b_Q := by
    rcases hQ_ends.ends_eq S hQ₀_ends with ⟨h2, _⟩ | ⟨h2, _⟩
    · exact Or.inl h2
    · exact Or.inr h2
  rcases hs₀_st with rfl | rfl <;> rcases hs₀_ab with h2 | h2
  · rw [h2] at hs_ab; exact S.Ω.not_mem_interval_left a_Q b_Q hs_ab
  · rw [h2] at hs_ab; exact S.Ω.not_mem_interval_right a_Q b_Q hs_ab
  · rw [h2] at ht_ba; exact S.Ω.not_mem_interval_right b_Q a_Q ht_ba
  · rw [h2] at ht_ba; exact S.Ω.not_mem_interval_left b_Q a_Q ht_ba

/-- In a fence `(A, B)`, if `a₂, b₂ ∈ A` with `a₂ ≠ b₂`, then either `B ⊆ Ω.interval a₂ b₂` or
`B ⊆ Ω.interval b₂ a₂`. -/
theorem subset_interval_or_swap {A B : Set α} (hfence : S.Ω.IsFence A B)
    {a₂ b₂ : α} (ha₂ : a₂ ∈ A) (hb₂ : b₂ ∈ A) (hne : a₂ ≠ b₂) :
    B ⊆ S.Ω.interval a₂ b₂ ∨ B ⊆ S.Ω.interval b₂ a₂ := by
  have ha₂_bar : a₂ ∈ S.Ω.bar := hfence.1 ha₂
  have hb₂_bar : b₂ ∈ S.Ω.bar := hfence.1 hb₂
  have hB_union : B ⊆ S.Ω.interval a₂ b₂ ∪ S.Ω.interval b₂ a₂ := by
    rw [S.Ω.interval_union_interval_swap ha₂_bar hb₂_bar hne]
    intro b hb
    refine ⟨hfence.2.1 hb, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun h => disjoint_left.mp hfence.2.2.1 ha₂ (h ▸ hb),
      fun h => disjoint_left.mp hfence.2.2.1 hb₂ (h ▸ hb)⟩
  by_cases hex : ∃ b ∈ B, b ∈ S.Ω.interval a₂ b₂
  · left
    rcases hex with ⟨b, hbB, hb_ab⟩
    intro b' hb'B
    rcases hB_union hb'B with h_ab | h_ba
    · exact h_ab
    · exfalso
      have hne_b : b ≠ b' :=
        fun h => disjoint_left.mp (S.Ω.disjoint_interval_swap a₂ b₂) hb_ab (h ▸ h_ba)
      have hcr : S.Ω.Crosses a₂ b₂ b b' :=
        S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hb_ab, h_ba⟩)
      exact hfence.2.2.2.2 a₂ ha₂ b₂ hb₂ hne b hbB b' hb'B hne_b hcr
  · right
    push Not at hex
    intro b hbB
    exact (hB_union hbB).resolve_left (hex b hbB)

/-- **Graph Minors IX, (4.4)** (pages 50–51):
"(4.4) *Let **S** be true, and let $Q_1, Q_2, Q_3 \in \mathscr{Q}$ be in order, where $Q_2$ is
... separating. Suppse that $Q_1, Q_2, Q_3$ are all half-covered. Then one end of $Q_2$ is in $A$
and
the other is in $B$.*" -/
theorem theorem_4_4_proof {p : ℕ} {P_set Q_set : Set (Graph α β)} {A B : Set α}
    (hS : S.StatementS p P_set Q_set A B)
    {Q₁ Q₂ Q₃ : Graph α β}
    (_hQ₁ : Q₁ ∈ Q_set) (_hQ₂ : Q₂ ∈ Q_set) (_hQ₃ : Q₃ ∈ Q_set)
    (hord : S.AreInOrder [Q₁, Q₂, Q₃])
    (hsep₂ : S.IsSeparatingOmegaPath Q₂)
    (hcov₁ : S.IsHalfCovered P_set Q₁)
    (hcov₂ : S.IsHalfCovered P_set Q₂)
    (hcov₃ : S.IsHalfCovered P_set Q₃) :
    ∃ a₂ ∈ A, ∃ b₂ ∈ B, S.IsOmegaPathWithEnds Q₂ a₂ b₂ := by
  rcases hord with ⟨_, a_l, b_l, ha_len, hb_len, hends, hcw⟩
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at ha_len hb_len
  rcases a_l with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, _ | _⟩⟩⟩ <;> simp at ha_len
  rcases b_l with _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | _⟩⟩⟩ <;> simp at hb_len
  have h0 : 0 < [Q₁, Q₂, Q₃].length := by simp
  have h1 : 1 < [Q₁, Q₂, Q₃].length := by simp
  have h2 : 2 < [Q₁, Q₂, Q₃].length := by simp
  have hQ₁_ends : S.IsOmegaPathWithEnds Q₁ a₁ b₁ := hends 0 h0
  have hQ₂_ends : S.IsOmegaPathWithEnds Q₂ a₂ b₂ := hends 1 h1
  have hQ₃_ends : S.IsOmegaPathWithEnds Q₃ a₃ b₃ := hends 2 h2
  have hcw6 : S.Ω.IsClockwiseSeq [a₃, a₂, a₁, b₁, b₂, b₃] := hcw
  obtain ⟨ha₁_ab, hb₁_ab, ha₃_ba, hb₃_ba⟩ := S.mem_intervals_of_isClockwiseSeq_six hcw6
  -- Helper: it is impossible that `a₂, b₂ ∈ U` when `(U, V)` is a fence for `P_set`.
  have hnot_both_in_side : ∀ {U V : Set α}, S.IsFenceFor P_set U V →
      a₂ ∈ U → b₂ ∈ U → False := by
    intro U V hfenceU ha₂U hb₂U
    rcases S.subset_interval_or_swap hfenceU.2.1 ha₂U hb₂U hQ₂_ends.2.1 with hV_ab | hV_ba
    · -- `V ⊆ S.Ω.interval a₂ b₂`: use `Q₃` whose ends `a₃, b₃` lie in `S.Ω.interval b₂ a₂`.
      rcases hcov₃ with ⟨P₃, hP₃_in, _, _, s₃, t₃, a₃', b₃', _, hP₃_ends, hQ₃_ends', rfl, _, _⟩
      have hs₃_ba : s₃ ∈ S.Ω.interval b₂ a₂ := by
        rcases hQ₃_ends.ends_eq S hQ₃_ends' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ha₃_ba
        · exact hb₃_ba
      have hs₃_not_V : s₃ ∉ V :=
        fun hsV => disjoint_left.mp (S.Ω.disjoint_interval_swap a₂ b₂) (hV_ab hsV) hs₃_ba
      obtain ⟨u₃, hu₃U, v₃, hv₃V, hP₃_uv⟩ := hfenceU.2.2 P₃ hP₃_in
      have ht₃_V : t₃ ∈ V := by
        rcases hP₃_ends.ends_eq S hP₃_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hv₃V
        · exact (hs₃_not_V hv₃V).elim
      exact S.not_ends_in_both_intervals_of_separating_halfCovered
        hQ₂_ends hsep₂ hcov₂ hP₃_in hP₃_ends.symm (hV_ab ht₃_V) hs₃_ba
    · -- `V ⊆ S.Ω.interval b₂ a₂`: use `Q₁` whose ends `a₁, b₁` lie in `S.Ω.interval a₂ b₂`.
      rcases hcov₁ with ⟨P₁, hP₁_in, _, _, s₁, t₁, a₁', b₁', _, hP₁_ends, hQ₁_ends', rfl, _, _⟩
      have hs₁_ab : s₁ ∈ S.Ω.interval a₂ b₂ := by
        rcases hQ₁_ends.ends_eq S hQ₁_ends' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ha₁_ab
        · exact hb₁_ab
      have hs₁_not_V : s₁ ∉ V :=
        fun hsV => disjoint_left.mp (S.Ω.disjoint_interval_swap a₂ b₂) hs₁_ab (hV_ba hsV)
      obtain ⟨u₁, hu₁U, v₁, hv₁V, hP₁_uv⟩ := hfenceU.2.2 P₁ hP₁_in
      have ht₁_V : t₁ ∈ V := by
        rcases hP₁_ends.ends_eq S hP₁_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hv₁V
        · exact (hs₁_not_V hv₁V).elim
      exact S.not_ends_in_both_intervals_of_separating_halfCovered
        hQ₂_ends hsep₂ hcov₂ hP₁_in hP₁_ends hs₁_ab (hV_ba ht₁_V)
  have hfence_BA : S.IsFenceFor P_set B A := by
    refine ⟨hS.isFenceFor_P.1, hS.isFenceFor_P.2.1.symm, fun P hP => ?_⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hS.isFenceFor_P.2.2 P hP
    exact ⟨b, hb, a, ha, hab.symm S⟩
  have ha₂_AB : a₂ ∈ A ∪ B := by
    rw [hS.isFenceFor_P.2.1.2.2.2.1]; exact hQ₂_ends.2.2.1
  have hb₂_AB : b₂ ∈ A ∪ B := by
    rw [hS.isFenceFor_P.2.1.2.2.2.1]; exact hQ₂_ends.2.2.2
  rcases ha₂_AB with ha₂A | ha₂B <;> rcases hb₂_AB with hb₂A | hb₂B
  · exact (hnot_both_in_side hS.isFenceFor_P ha₂A hb₂A).elim
  · exact ⟨a₂, ha₂A, b₂, hb₂B, hQ₂_ends⟩
  · exact ⟨b₂, hb₂A, a₂, ha₂B, hQ₂_ends.symm S⟩
  · exact (hnot_both_in_side hfence_BA ha₂B hb₂B).elim

end Society

end GraphMinor.GM09
