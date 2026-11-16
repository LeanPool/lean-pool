/-
Copyright (c) 2026 Goran Zuzic et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Goran Zuzic, David P. Woodruff, Vahab Mirrokni
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Paths

public import LeanPool.SteinerSpanners.Defs
public import LeanPool.SteinerSpanners.Glue

/-! # Combinatorics infrastructure for Steiner spanners

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib. -/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners.Proofs.Combinatorics

private lemma pinFiber_card_le {α β : Type*} [DecidableEq α]
    {a : α} {b : β} {L : Finset α} {K : ℕ} (h : L.card < K) :
    ((insert a L) ×ˢ ({b} : Finset β)).card ≤ K := by
  rw [Finset.card_product, Finset.card_singleton, mul_one]
  exact (Finset.card_insert_le _ _).trans (by omega)

private lemma finiteSet_cover_card {α : Type*} [DecidableEq α] (S X Y : Finset α) :
    S.card ≤ (X ∩ Y).card + (S \ X).card + (S \ Y).card := by
  have h_sub : S ⊆ (X ∩ Y) ∪ (S \ X) ∪ (S \ Y) := by
    intro x hxS
    by_cases hxX : x ∈ X
    · by_cases hxY : x ∈ Y
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxX,
          hxY⟩))
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxS, hxY⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxS, hxX⟩))
  calc
    S.card ≤ ((X ∩ Y) ∪ (S \ X) ∪ (S \ Y)).card := Finset.card_le_card h_sub
    _ ≤ ((X ∩ Y) ∪ (S \ X)).card + (S \ Y).card := Finset.card_union_le _ _
    _ ≤ (X ∩ Y).card + (S \ X).card + (S \ Y).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _

private lemma card_lt_of_two_small_differences {α : Type*} [DecidableEq α]
    (S T X Y : Finset α) (r : ℕ) (hX : 8 * (S \ X).card < r)
    (hY : 8 * (S \ Y).card < r) (hdrop : 4 * (X ∩ Y).card + r < 4 * T.card) :
    S.card < T.card := by
  have hcover := finiteSet_cover_card S X Y
  omega

private lemma card_lt_at_right_boundary {α : Type*} [DecidableEq α] {ℓ : ℕ}
    (F : Fin (ℓ + 1) → Finset α) (T : Fin ℓ → Finset α) (L R : ℕ → ℕ) (r : ℕ)
    (hgood : ∀ (i : ℕ) (hi : i < ℓ), ∀ j, L i ≤ j → j ≤ R i →
      ∀ hj : j < ℓ + 1, 8 * (T ⟨i, hi⟩ \ F ⟨j, hj⟩).card < r)
    (hbad : ∀ (i : ℕ) (hi : i < ℓ), R i < ℓ →
      ¬ ∀ hj : R i + 1 < ℓ + 1, 8 * (T ⟨i, hi⟩ \ F ⟨R i + 1, hj⟩).card < r)
    (hdrop : ∀ (i : Fin ℓ) (j : Fin (ℓ + 1)), r ≤ 8 * (T i \ F j).card →
      4 * (F j ∩ (F i.castSucc ∪ F i.succ)).card + r < 4 * (T i).card)
    (i k : Fin ℓ) (hR : R i + 1 ≤ R k) (hL : L k ≤ (i : ℕ) + 1)
    (hRi : (i : ℕ) + 1 ≤ R i) (hRk : R k ≤ ℓ) : (T k).card < (T i).card := by
  have hRi_lt : R i < ℓ := by omega
  let j : Fin (ℓ + 1) := ⟨R i + 1, by omega⟩
  have hbadj : r ≤ 8 * (T i \ F j).card := by
    by_contra h
    apply hbad i i.isLt hRi_lt
    intro _
    exact Nat.lt_of_not_le h
  have hdropj := hdrop i j hbadj
  have hX : 8 * (T k \ F j).card < r :=
    hgood k k.isLt j (by dsimp [j]; omega) hR j.isLt
  have hY : 8 * (T k \ F i.succ).card < r :=
    hgood k k.isLt i.succ hL (by change (i : ℕ) + 1 ≤ R k; omega) i.succ.isLt
  apply card_lt_of_two_small_differences (T k) (T i) (F j) (F i.succ) r hX hY
  have hcard : (F j ∩ F i.succ).card ≤ (F j ∩ (F i.castSucc ∪ F i.succ)).card :=
    Finset.card_le_card (Finset.inter_subset_inter_left Finset.subset_union_right)
  omega

private lemma card_lt_at_left_boundary {α : Type*} [DecidableEq α] {ℓ : ℕ}
    (F : Fin (ℓ + 1) → Finset α) (T : Fin ℓ → Finset α) (L R : ℕ → ℕ) (r : ℕ)
    (hgood : ∀ (i : ℕ) (hi : i < ℓ), ∀ j, L i ≤ j → j ≤ R i →
      ∀ hj : j < ℓ + 1, 8 * (T ⟨i, hi⟩ \ F ⟨j, hj⟩).card < r)
    (hbad : ∀ (i : ℕ) (hi : i < ℓ), 0 < L i →
      ¬ ∀ hj : L i - 1 < ℓ + 1, 8 * (T ⟨i, hi⟩ \ F ⟨L i - 1, hj⟩).card < r)
    (hdrop : ∀ (i : Fin ℓ) (j : Fin (ℓ + 1)), r ≤ 8 * (T i \ F j).card →
      4 * (F j ∩ (F i.castSucc ∪ F i.succ)).card + r < 4 * (T i).card)
    (i k : Fin ℓ) (hik : (i : ℕ) < k) (hL : L i < L k)
    (hLk : L k ≤ (i : ℕ) + 1) (hkR : (k : ℕ) ≤ R i) : (T i).card < (T k).card := by
  have hLk_pos : 0 < L k := by omega
  let j : Fin (ℓ + 1) := ⟨L k - 1, by omega⟩
  have hbadj : r ≤ 8 * (T k \ F j).card := by
    by_contra h
    apply hbad k k.isLt hLk_pos
    intro _
    exact Nat.lt_of_not_le h
  have hdropj := hdrop k j hbadj
  have hX : 8 * (T i \ F j).card < r :=
    hgood i i.isLt j (by dsimp [j]; omega) (by dsimp [j]; omega) j.isLt
  have hY : 8 * (T i \ F k.castSucc).card < r :=
    hgood i i.isLt k.castSucc (by change L i ≤ (k : ℕ); omega) hkR k.castSucc.isLt
  apply card_lt_of_two_small_differences (T i) (T k) (F j) (F k.castSucc) r hX hY
  have hcard : (F j ∩ F k.castSucc).card ≤ (F j ∩ (F k.castSucc ∪ F k.succ)).card :=
    Finset.card_le_card (Finset.inter_subset_inter_left Finset.subset_union_left)
  omega

/-- **Theorem 2.2(a) (Last-Hit Edge Charging, Module 2)** -/
theorem thm_2_2a_proof :
    ∀ (C₁ rStar N q K : ℕ), 2 ≤ C₁ → 1 ≤ rStar → 2 ≤ N → 2 ≤ q → 1 ≤ K →
      ∀ (X : Finset (Fin N → Fin q)) (G_hat : SimpleGraph ↥X)
        (L : ↥X → ↥X → Finset ↥X),
        (∀ a b : ↥X, G_hat.Adj a b →
          0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar) →
        (∀ x y : ↥X, hammingDist x.val y.val = rStar →
          ∃ q_walk : G_hat.Walk x y,
            q_walk.IsPath ∧ ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar) →
        ListSizeCond C₁ rStar K X L →
        OverlapCond C₁ rStar K X →
        ListHitCond C₁ rStar X L →
        (exactDistPairs X rStar).card ≤ 2 * K ^ 2 * Nat.card G_hat.edgeSet := by
  classical
  intro C₁ rStar N q K _ hrStar _ _ _ X G_hat L hG_adj hG_path hListSize hOverlap hListHit
  let : Fintype G_hat.Dart := Fintype.ofFinite _
  let : Fintype G_hat.edgeSet := Fintype.ofFinite _
  have h_dart_card : (Finset.univ : Finset G_hat.Dart).card = 2 * Nat.card G_hat.edgeSet := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    have h := G_hat.dart_card_eq_twice_card_edges
    simpa only [SimpleGraph.edgeFinset, Set.toFinset_card,
      ← Nat.card_eq_fintype_card] using h
  let dartPinFiber : G_hat.Dart → Finset (↥X × ↥X) :=
    fun d => (insert d.toProd.1 (L d.toProd.1 d.toProd.2)) ×ˢ ({d.toProd.2} : Finset ↥X)
  let P_pin : Finset (↥X × ↥X) :=
    ((Finset.univ : Finset G_hat.Dart).biUnion dartPinFiber).filter
      (fun p => 0 < hammingDist p.1.val p.2.val ∧ hammingDist p.1.val p.2.val ≤ C₁ * rStar)
  have h_dart_fiber_le : ∀ d : G_hat.Dart, (dartPinFiber d).card ≤ K := by
    intro d
    obtain ⟨hab_pos, hab_dist⟩ := hG_adj d.toProd.1 d.toProd.2 d.adj
    exact pinFiber_card_le (hListSize _ _ hab_pos hab_dist)
  have h_Ppin_card : P_pin.card ≤ 2 * K * Nat.card G_hat.edgeSet := by
    have h1 : P_pin.card ≤ ((Finset.univ : Finset G_hat.Dart).biUnion dartPinFiber).card :=
      Finset.card_filter_le _ _
    have h2 : ((Finset.univ : Finset G_hat.Dart).biUnion dartPinFiber).card ≤
        ∑ d ∈ (Finset.univ : Finset G_hat.Dart), (dartPinFiber d).card :=
      Finset.card_biUnion_le
    have h3 : ∑ d ∈ (Finset.univ : Finset G_hat.Dart), (dartPinFiber d).card ≤
        (Finset.univ : Finset G_hat.Dart).card * K := by
      simpa [smul_eq_mul] using
        Finset.sum_le_card_nsmul (Finset.univ : Finset G_hat.Dart)
          (fun d => (dartPinFiber d).card) K (fun d _ => h_dart_fiber_le d)
    calc
      P_pin.card ≤ (Finset.univ : Finset G_hat.Dart).card * K :=
        le_trans h1 (le_trans h2 h3)
      _ = (2 * Nat.card G_hat.edgeSet) * K := by rw [h_dart_card]
      _ = 2 * K * Nat.card G_hat.edgeSet := by ring
  let CherrySet : ↥X → ↥X → Finset ↥X :=
    fun x w₀ => Finset.univ.filter (fun y : ↥X =>
      y ≠ x ∧ y ≠ w₀ ∧
      hammingDist x.val y.val = rStar ∧
      (rStar : ℝ) / 4 < ((disagreeSet x.val w₀.val ∩ disagreeSet x.val y.val).card : ℝ))
  let CherryFiber : ↥X × ↥X → Finset (↥X × ↥X) :=
    fun p => ({p.1} : Finset ↥X) ×ˢ insert p.2 (CherrySet p.1 p.2)
  have h_cherry_fiber_le : ∀ p ∈ P_pin, (CherryFiber p).card ≤ K := by
    intro p hp
    simp only [P_pin, Finset.mem_filter] at hp
    have h_ch_lt : (CherrySet p.1 p.2).card < K :=
      hOverlap p.1 p.2 hp.2.1 hp.2.2
    have h := pinFiber_card_le (a := p.2) (b := p.1) h_ch_lt
    simpa only [CherryFiber, Finset.card_product, Finset.card_singleton, one_mul, mul_one]
      using h
  have h_cover_card :
      (P_pin.biUnion CherryFiber).card ≤ 2 * K ^ 2 * Nat.card G_hat.edgeSet := by
    have h1 : (P_pin.biUnion CherryFiber).card ≤ ∑ p ∈ P_pin, (CherryFiber p).card :=
      Finset.card_biUnion_le
    have h2 : ∑ p ∈ P_pin, (CherryFiber p).card ≤ P_pin.card * K := by
      simpa [smul_eq_mul] using
        Finset.sum_le_card_nsmul P_pin (fun p => (CherryFiber p).card) K h_cherry_fiber_le
    calc
      (P_pin.biUnion CherryFiber).card ≤ P_pin.card * K := le_trans h1 h2
      _ ≤ (2 * K * Nat.card G_hat.edgeSet) * K :=
        Nat.mul_le_mul_right K h_Ppin_card
      _ = 2 * K ^ 2 * Nat.card G_hat.edgeSet := by ring
  let E_sub : Finset (↥X × ↥X) :=
    Finset.univ.filter (fun xy : ↥X × ↥X => hammingDist xy.1.val xy.2.val = rStar)
  have h_sub : E_sub ⊆ P_pin.biUnion CherryFiber := by
    rintro ⟨x, y⟩ hxy
    simp only [E_sub, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
    have hxy_ne : x ≠ y := by
      intro h_eq
      subst h_eq
      rw [hammingDist_self] at hxy
      omega
    obtain ⟨q_walk, hq_path, hq_ball⟩ := hG_path x y hxy
    let m : ℕ := q_walk.length
    have hm_pos : 1 ≤ m := by
      by_contra hm0
      have hm_eq : q_walk.length = 0 := by omega
      exact hxy_ne (SimpleGraph.Walk.eq_of_length_eq_zero hm_eq)
    let u : ℕ → ↥X := fun k => q_walk.getVert k
    have hu0 : u 0 = x := q_walk.getVert_zero
    have hum : u m = y := q_walk.getVert_length
    have hu_inj : Set.InjOn u {k : ℕ | k ≤ m} := hq_path.getVert_injOn
    have hu_eq : ∀ a b : ℕ, a ≤ m → b ≤ m → u a = u b → a = b :=
      fun a b ha hb hab => hu_inj ha hb hab
    have hu_ball : ∀ k : ℕ, hammingDist x.val (u k).val ≤ C₁ * rStar :=
      fun k => hq_ball (u k) (q_walk.getVert_mem_support k)
    have hu_adj : ∀ k : ℕ, k < m → G_hat.Adj (u k) (u (k + 1)) :=
      fun k hk => q_walk.adj_getVert_succ hk
    let I : Finset ℕ :=
      (Finset.Icc 1 m).filter (fun s => x ∈ insert (u (s - 1)) (L (u (s - 1)) (u s)))
    have h1_mem : 1 ∈ I := by
      simp only [I, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨le_rfl, hm_pos⟩, ?_⟩
      change x ∈ insert (u 0) (L (u 0) (u 1))
      rw [hu0]
      exact Finset.mem_insert_self _ _
    have hI_ne : I.Nonempty := ⟨1, h1_mem⟩
    let s₀ : ℕ := I.max' hI_ne
    let w₀ : ↥X := u s₀
    have hs₀_mem : s₀ ∈ I := Finset.max'_mem I hI_ne
    simp only [I, Finset.mem_filter, Finset.mem_Icc] at hs₀_mem
    obtain ⟨⟨hs₀_ge, hs₀_le⟩, hs₀_pin⟩ := hs₀_mem
    have hadj₀ : G_hat.Adj (u (s₀ - 1)) w₀ := by
      have h_lt : s₀ - 1 < m := by omega
      have h_succ : s₀ - 1 + 1 = s₀ := by omega
      have h_a := hu_adj (s₀ - 1) h_lt
      rwa [h_succ] at h_a
    have hx_ne_w₀ : x ≠ w₀ := by
      intro h_eq
      have h0s : u 0 = u s₀ := by rw [hu0]; exact h_eq
      have : 0 = s₀ := hu_eq 0 s₀ (by omega) hs₀_le h0s
      omega
    have hxw₀_pos : 0 < hammingDist x.val w₀.val :=
      hammingDist_pos.mpr (fun h_eq => hx_ne_w₀ (Subtype.ext h_eq))
    have hp_mem : (x, w₀) ∈ P_pin := by
      simp only [P_pin, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
      refine ⟨⟨⟨(u (s₀ - 1), w₀), hadj₀⟩, ?_⟩, hxw₀_pos, hu_ball s₀⟩
      exact Finset.mem_product.mpr ⟨hs₀_pin, Finset.mem_singleton_self w₀⟩
    simp only [Finset.mem_biUnion]
    refine ⟨(x, w₀), hp_mem, ?_⟩
    simp only [CherryFiber, Finset.mem_product, Finset.mem_singleton, true_and]
    rcases eq_or_lt_of_le hs₀_le with hs₀_eq | hs₀_lt
    · have hw₀_eq_y : w₀ = y := by
        dsimp [w₀]
        rw [hs₀_eq, hum]
      rw [hw₀_eq_y]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      simp only [CherrySet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hy_ne_w₀ : y ≠ w₀ := by
        intro h_eq
        have hms : u m = u s₀ := by rw [hum]; exact h_eq
        have : m = s₀ := hu_eq m s₀ le_rfl hs₀_le hms
        omega
      refine ⟨hxy_ne.symm, hy_ne_w₀, hxy, ?_⟩
      by_contra h_not_lt
      have h_inter_le :
          ((disagreeSet x.val w₀.val ∩ disagreeSet x.val y.val).card : ℝ) ≤ (rStar : ℝ) / 4 :=
        not_lt.mp h_not_lt
      let ℓ : ℕ := m - s₀
      have hℓ : 1 ≤ ℓ := by omega
      let w : Fin (ℓ + 1) → ↥X := fun t => u (s₀ + t.1)
      have hw_ball : ∀ t : Fin (ℓ + 1), w t ≠ x ∧ hammingDist x.val (w t).val ≤ C₁ * rStar := by
        intro t
        refine ⟨?_, hu_ball (s₀ + t.1)⟩
        intro h_eq
        have h_u : u (s₀ + t.1) = u 0 := by rw [hu0]; exact h_eq
        have h_le : s₀ + t.1 ≤ m := by have := t.2; omega
        have : s₀ + t.1 = 0 := hu_eq (s₀ + t.1) 0 h_le (by omega) h_u
        omega
      have hw_step : ∀ s : Fin ℓ,
          0 < hammingDist (w s.castSucc).val (w s.succ).val ∧
          hammingDist (w s.castSucc).val (w s.succ).val ≤ C₁ * rStar := by
        intro s
        have hs_lt : s₀ + s.1 < m := by have := s.2; omega
        have h_adj_s : G_hat.Adj (w s.castSucc) (w s.succ) := by
          dsimp [w]
          rw [← Nat.add_assoc]
          exact hu_adj (s₀ + s.1) hs_lt
        exact hG_adj _ _ h_adj_s
      have hw_last_eq : w (Fin.last ℓ) = y := by
        dsimp [w]
        have h_add : s₀ + ℓ = m := by omega
        rw [h_add, hum]
      have hw_zero_eq : w 0 = w₀ := rfl
      have hw_last_dist : hammingDist x.val (w (Fin.last ℓ)).val = rStar := by
        rw [hw_last_eq]
        exact hxy
      have hw_inter :
          ((disagreeSet x.val (w 0).val ∩ disagreeSet x.val (w (Fin.last ℓ)).val).card : ℝ) ≤
            (rStar : ℝ) / 4 := by
        rw [hw_zero_eq, hw_last_eq]
        exact h_inter_le
      obtain ⟨s, hs_cand⟩ := hListHit x ℓ hℓ w hw_ball hw_step hw_last_dist hw_inter
      let s' : ℕ := s₀ + s.1 + 1
      have hs'_mem : s' ∈ I := by
        simp only [I, Finset.mem_filter, Finset.mem_Icc]
        have hs'_bounds : 1 ≤ s' ∧ s' ≤ m := by have := s.2; omega
        refine ⟨hs'_bounds, ?_⟩
        apply Finset.mem_insert_of_mem
        have h1 : u (s' - 1) = w s.castSucc := rfl
        have h2 : u s' = w s.succ := by
          dsimp [w, s']
          rw [Nat.add_assoc]
        rw [h1, h2]
        exact hs_cand
      have hs'_le : s' ≤ s₀ := Finset.le_max' I s' hs'_mem
      omega
  have h_img : exactDistPairs X rStar ⊆ E_sub.image (fun xy => (xy.1.val, xy.2.val)) := by
    rintro ⟨xv, yv⟩ hxy
    simp only [exactDistPairs, Finset.mem_filter, Finset.mem_product] at hxy
    obtain ⟨⟨hx, hy⟩, hdist⟩ := hxy
    exact Finset.mem_image.mpr
      ⟨(⟨xv, hx⟩, ⟨yv, hy⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩, rfl⟩
  calc
    (exactDistPairs X rStar).card
      ≤ (E_sub.image (fun xy => (xy.1.val, xy.2.val))).card := Finset.card_le_card h_img
    _ ≤ E_sub.card := Finset.card_image_le
    _ ≤ (P_pin.biUnion CherryFiber).card := Finset.card_le_card h_sub
    _ ≤ 2 * K ^ 2 * Nat.card G_hat.edgeSet := h_cover_card

private lemma peel_coordinates {N rStar ℓ : ℕ} (hrStar : 1 ≤ rStar)
    (F : Fin (ℓ + 1) → Finset (Fin N)) : ∀ (n : ℕ) (I₀ W : Finset (Fin N)), I₀.card ≤ n → I₀ ⊆ W →
    ∃ (k : ℕ) (t : Fin k → Fin (ℓ + 1)) (A : Fin k → Finset (Fin N)) (T_star : Finset (Fin N)),
      k * rStar + 8 * T_star.card ≤ 8 * I₀.card ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (∀ r : Fin k, Disjoint (A r) T_star) ∧
      Finset.univ.biUnion A ∪ T_star = I₀ ∧
      (∀ r : Fin k,
        let I_rem := (Finset.univ.filter (fun j : Fin k => r < j)).biUnion A ∪ T_star
        Disjoint (A r) (F (t r)) ∧
        I_rem ⊆ F (t r) ∧
        4 * ((A r).card : ℤ) - (rStar : ℤ) ≤ 4 * (((W ∩ F (t r)) \ (A r ∪ I_rem)).card : ℤ)) ∧
      (∀ j : Fin (ℓ + 1), rStar ≤ 8 * (T_star \ F j).card →
        4 * (F j ∩ W).card + rStar < 4 * T_star.card) := by
  intro n
  induction n with
  | zero =>
    intro I₀ W hI₀_le _hIW
    have hI₀_card0 : I₀.card = 0 := by omega
    refine ⟨0, Fin.elim0, Fin.elim0, I₀, by omega,
      fun i => Fin.elim0 i, fun r => Fin.elim0 r, by simp, fun r => Fin.elim0 r, ?_⟩
    intro j hj
    have hsdiff0 : (I₀ \ F j).card = 0 := by
      have hle : (I₀ \ F j).card ≤ I₀.card := Finset.card_le_card Finset.sdiff_subset
      omega
    omega
  | succ n' ih =>
    intro I₀ W hI₀_le hIW
    by_cases hex : ∃ j : Fin (ℓ + 1),
        rStar ≤ 8 * (I₀ \ F j).card ∧
        4 * ((I₀ \ F j).card : ℤ) - (rStar : ℤ) ≤ 4 * (((W ∩ F j) \ I₀).card : ℤ)
    · obtain ⟨j₀, hj₀_size, hj₀_out⟩ := hex
      let A₀ := I₀ \ F j₀
      let I₁ := I₀ ∩ F j₀
      have hsplit_card : A₀.card + I₁.card = I₀.card := Finset.card_sdiff_add_card_inter I₀ (F j₀)
      have hA₀_pos : 1 ≤ A₀.card := by change rStar ≤ 8 * A₀.card at hj₀_size; omega
      have hI₁_le : I₁.card ≤ n' := by omega
      have hI₁W : I₁ ⊆ W := Finset.inter_subset_left.trans hIW
      obtain ⟨k', t', A', T_star, hk'_card, hA'_pw, hA'_T, hA'_part, hA'_step, hT_stop⟩ :=
        ih I₁ W hI₁_le hI₁W
      let t : Fin (k' + 1) → Fin (ℓ + 1) := Fin.cons j₀ t'
      let A : Fin (k' + 1) → Finset (Fin N) := Fin.cons A₀ A'
      have hA'_sub_I₁ : ∀ i : Fin k', A' i ⊆ I₁ := by
        intro i x hx
        rw [← hA'_part]
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
      have hT_sub_I₁ : T_star ⊆ I₁ := by
        intro x hx
        rw [← hA'_part]
        exact Finset.mem_union_right _ hx
      have hdisj_A₀_I₁ : Disjoint A₀ I₁ := Finset.disjoint_sdiff_inter I₀ (F j₀)
      have hbi_eq : (Finset.univ : Finset (Fin (k' + 1))).biUnion A =
          A₀ ∪ Finset.univ.biUnion A' := by
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
        constructor
        · rintro ⟨r, hr⟩
          refine Fin.cases ?_ ?_ r hr
          · intro h0; exact Or.inl h0
          · intro i hi; exact Or.inr ⟨i, hi⟩
        · rintro (h0 | ⟨i, hi⟩)
          · exact ⟨0, h0⟩
          · exact ⟨i.succ, hi⟩
      refine ⟨k' + 1, t, A, T_star, ?_, ?_, ?_, ?_, ?_, hT_stop⟩
      · change rStar ≤ 8 * A₀.card at hj₀_size
        have : (k' + 1) * rStar = k' * rStar + rStar := by ring
        omega
      · intro r₁ r₂ hne
        refine Fin.cases ?_ ?_ r₁ hne
        · refine Fin.cases ?_ ?_ r₂
          · intro h00; exact absurd rfl h00
          · intro j _
            exact Disjoint.mono_right (hA'_sub_I₁ j) hdisj_A₀_I₁
        · intro i
          refine Fin.cases ?_ ?_ r₂
          · intro _
            exact (Disjoint.mono_right (hA'_sub_I₁ i) hdisj_A₀_I₁).symm
          · intro j hij
            exact hA'_pw (fun heq => hij (congrArg Fin.succ heq))
      · intro r
        refine Fin.cases ?_ ?_ r
        · exact Disjoint.mono_right hT_sub_I₁ hdisj_A₀_I₁
        · intro i; exact hA'_T i
      · rw [hbi_eq, Finset.union_assoc, hA'_part]
        exact Finset.sdiff_union_inter I₀ (F j₀)
      · intro r
        refine Fin.cases ?_ ?_ r
        · have hfilter0 :
              ((Finset.univ.filter (fun j : Fin (k' + 1) => (0 : Fin (k' + 1)) < j)).biUnion A) =
              Finset.univ.biUnion A' := by
            ext x
            simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨j, hj_pos, hjx⟩
              refine Fin.cases ?_ ?_ j hj_pos hjx
              · intro hlt; exact absurd hlt (lt_irrefl _)
              · intro i _ hix; exact ⟨i, hix⟩
            · rintro ⟨i, hix⟩
              exact ⟨i.succ, Fin.succ_pos i, hix⟩
          dsimp only
          rw [hfilter0, hA'_part]
          change Disjoint A₀ (F j₀) ∧ I₁ ⊆ F j₀ ∧
            4 * (A₀.card : ℤ) - (rStar : ℤ) ≤ 4 * (((W ∩ F j₀) \ (A₀ ∪ I₁)).card : ℤ)
          have hA₀I₁ : A₀ ∪ I₁ = I₀ := Finset.sdiff_union_inter I₀ (F j₀)
          rw [hA₀I₁]
          exact ⟨Finset.sdiff_disjoint, Finset.inter_subset_right, hj₀_out⟩
        · intro i
          have hfilter_succ :
              (Finset.univ.filter (fun j : Fin (k' + 1) => i.succ < j)).biUnion A =
                (Finset.univ.filter (fun j' : Fin k' => i < j')).biUnion A' := by
            ext x
            simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨j, hj_lt, hjx⟩
              refine Fin.cases ?_ ?_ j hj_lt hjx
              · intro hlt; exact absurd hlt (Nat.not_lt_zero _)
              · intro j' hj'_lt hj'x
                exact ⟨j', Fin.succ_lt_succ_iff.mp hj'_lt, hj'x⟩
            · rintro ⟨j', hj'_lt, hj'x⟩
              exact ⟨j'.succ, Fin.succ_lt_succ_iff.mpr hj'_lt, hj'x⟩
          dsimp only
          rw [hfilter_succ]
          exact hA'_step i
    · refine ⟨0, Fin.elim0, Fin.elim0, I₀, by omega,
        fun i => Fin.elim0 i, fun r => Fin.elim0 r, by simp, fun r => Fin.elim0 r, ?_⟩
      intro j hj_size
      push Not at hex
      have hlt_z : 4 * (((W ∩ F j) \ I₀).card : ℤ) < 4 * ((I₀ \ F j).card : ℤ) - (rStar : ℤ) :=
        hex j hj_size
      have hlt_nat : 4 * ((W ∩ F j) \ I₀).card + rStar < 4 * (I₀ \ F j).card := by omega
      have hinter_eq : (W ∩ F j) ∩ I₀ = I₀ ∩ F j := by
        ext x
        simp only [Finset.mem_inter]
        exact ⟨fun ⟨⟨_, hxF⟩, hxI⟩ => ⟨hxI, hxF⟩, fun ⟨hxI, hxF⟩ => ⟨⟨hIW hxI, hxF⟩, hxI⟩⟩
      have hW_split : ((W ∩ F j) \ I₀).card + (I₀ ∩ F j).card = (F j ∩ W).card := by
        rw [← hinter_eq, Finset.card_sdiff_add_card_inter, Finset.inter_comm]
      have hI_split : (I₀ \ F j).card + (I₀ ∩ F j).card = I₀.card :=
        Finset.card_sdiff_add_card_inter I₀ (F j)
      omega

/-- **Theorem 2.2(b) (Biclique Bottleneck Lemma, Module 2)**
Note: `HighDimSteinerSpanners.Proofs.Glue.lem_5_1_proof` provides Lemma 5.1
    (`lem_5_1_interval_crossing`) ready to use. -/
theorem thm_2_2b_proof :
    ∀ (C₁ rStar N ℓ : ℕ), 2 ≤ C₁ → 1 ≤ rStar → 1 ≤ N → 1 ≤ ℓ →
      ∀ (F : Fin (ℓ + 1) → Finset (Fin N)),
        (∀ i : Fin (ℓ + 1), (F i).card ≤ C₁ * rStar) →
        ((F 0 ∩ F (Fin.last ℓ)).card : ℝ) ≤ (rStar : ℝ) / 4 →
        ∃ (s : Fin ℓ) (k : ℕ), k ≤ 8 * C₁ ∧
          ∃ (t : Fin k → Fin (ℓ + 1)) (A : Fin k → Finset (Fin N)) (I_k : Finset (Fin N)),
            Pairwise (fun i j => Disjoint (A i) (A j)) ∧
            (∀ r : Fin k, Disjoint (A r) I_k) ∧
            Finset.univ.biUnion A ∪ I_k = F s.castSucc ∩ F s.succ ∧
            (I_k.card : ℝ) ≤ (rStar : ℝ) / 2 ∧
            ∀ r : Fin k,
              let I_rem := (Finset.univ.filter (fun j : Fin k => r < j)).biUnion A ∪ I_k
              Disjoint (A r) (F (t r)) ∧
              I_rem ⊆ F (t r) ∧
              ((A r).card : ℝ) - (rStar : ℝ) / 4 ≤
                ((((F s.castSucc ∪ F s.succ) ∩ F (t r)) \ (A r ∪ I_rem)).card : ℝ) := by
  intro C₁ rStar N ℓ _hC₁ hrStar _ hℓ F hF_card hF_end_real
  have hF_end : 4 * (F 0 ∩ F (Fin.last ℓ)).card ≤ rStar := by
    have h : ((4 * (F 0 ∩ F (Fin.last ℓ)).card : ℕ) : ℝ) ≤ (rStar : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h
  have h_peel := peel_coordinates hrStar F
  let A_fn : Fin ℓ → Finset (Fin N) := fun s => F s.castSucc ∩ F s.succ
  let W_fn : Fin ℓ → Finset (Fin N) := fun s => F s.castSucc ∪ F s.succ
  have hA_card : ∀ s : Fin ℓ, (A_fn s).card ≤ C₁ * rStar := by
    intro s
    exact (Finset.card_le_card Finset.inter_subset_left).trans (hF_card s.castSucc)
  have hAW_sub : ∀ s : Fin ℓ, A_fn s ⊆ W_fn s := by
    intro s
    exact Finset.inter_subset_left.trans Finset.subset_union_left
  choose k_fn t_fn A_seq T_fn h_spec using fun s : Fin ℓ =>
    h_peel (A_fn s).card (A_fn s) (W_fn s) le_rfl (hAW_sub s)
  by_cases h_ex_small : ∃ s : Fin ℓ, 2 * (T_fn s).card ≤ rStar
  · obtain ⟨s, hs⟩ := h_ex_small
    obtain ⟨hk_card, hA_pw, hA_T, hA_part, hA_step, _⟩ := h_spec s
    have hk_le : k_fn s ≤ 8 * C₁ := by
      have h1 : k_fn s * rStar ≤ 8 * (C₁ * rStar) := by
        have := Nat.mul_le_mul_left 8 (hA_card s)
        omega
      have h2 : rStar * k_fn s ≤ rStar * (8 * C₁) := by
        have hr1 : rStar * k_fn s = k_fn s * rStar := by ring
        have hr2 : rStar * (8 * C₁) = 8 * (C₁ * rStar) := by ring
        omega
      exact Nat.le_of_mul_le_mul_left h2 (by omega : 0 < rStar)
    have hT_half : ((T_fn s).card : ℝ) ≤ (rStar : ℝ) / 2 := by
      have hr : 2 * ((T_fn s).card : ℝ) ≤ (rStar : ℝ) := by exact_mod_cast hs
      linarith
    refine ⟨s, k_fn s, hk_le, t_fn s, A_seq s, T_fn s, hA_pw, hA_T, hA_part, hT_half, ?_⟩
    intro r
    obtain ⟨hdisj, hsub, hout_z⟩ := hA_step r
    refine ⟨hdisj, hsub, ?_⟩
    have hout_r : 4 * (((A_seq s r).card : ℝ)) - (rStar : ℝ) ≤
        4 * ((((W_fn s ∩ F (t_fn s r)) \ (A_seq s r ∪
          ((Finset.univ.filter (fun j : Fin (k_fn s) => r < j)).biUnion (A_seq s) ∪ T_fn
              s))).card : ℝ)) := by
      exact_mod_cast hout_z
    linarith
  · exfalso
    push Not at h_ex_small
    have hT_sub_A : ∀ s : Fin ℓ, T_fn s ⊆ A_fn s := by
      intro s x hx
      rw [← (h_spec s).2.2.2.1]
      exact Finset.mem_union_right _ hx
    have h_tri := @finiteSet_cover_card (Fin N) inferInstance
    let Good : ∀ (i : ℕ), i < ℓ → ℕ → Prop :=
      fun i hi j => ∀ hj : j < ℓ + 1, 8 * (T_fn ⟨i, hi⟩ \ F ⟨j, hj⟩).card < rStar
    have h_good_self : ∀ (i : ℕ) (hi : i < ℓ), Good i hi i := by
      intro i hi hj
      have h_eq : (⟨i, hj⟩ : Fin (ℓ + 1)) = (⟨i, hi⟩ : Fin ℓ).castSucc := by ext; rfl
      rw [h_eq]
      have h_sub : T_fn ⟨i, hi⟩ ⊆ F (⟨i, hi⟩ : Fin ℓ).castSucc :=
        (hT_sub_A ⟨i, hi⟩).trans Finset.inter_subset_left
      rw [Finset.sdiff_eq_empty_iff_subset.mpr h_sub, Finset.card_empty, mul_zero]
      omega
    have h_good_succ : ∀ (i : ℕ) (hi : i < ℓ), Good i hi (i + 1) := by
      intro i hi hj
      have h_eq : (⟨i + 1, hj⟩ : Fin (ℓ + 1)) = (⟨i, hi⟩ : Fin ℓ).succ := by ext; rfl
      rw [h_eq]
      have h_sub : T_fn ⟨i, hi⟩ ⊆ F (⟨i, hi⟩ : Fin ℓ).succ :=
        (hT_sub_A ⟨i, hi⟩).trans Finset.inter_subset_right
      rw [Finset.sdiff_eq_empty_iff_subset.mpr h_sub, Finset.card_empty, mul_zero]
      omega
    let SL : ∀ (i : ℕ), i < ℓ → Finset ℕ :=
      fun i hi => (Finset.Icc 0 i).filter (fun a => ∀ j, a ≤ j → j ≤ i → Good i hi j)
    let SR : ∀ (i : ℕ), i < ℓ → Finset ℕ :=
      fun i hi => (Finset.Icc (i + 1) ℓ).filter (fun b => ∀ j, i + 1 ≤ j → j ≤ b → Good i hi j)
    have hSL_ne : ∀ (i : ℕ) (hi : i < ℓ), (SL i hi).Nonempty := by
      intro i hi
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le i, le_rfl⟩, ?_⟩⟩
      intro j h1 h2
      have hji : j = i := by omega
      rw [hji]
      exact h_good_self i hi
    have hSR_ne : ∀ (i : ℕ) (hi : i < ℓ), (SR i hi).Nonempty := by
      intro i hi
      refine ⟨i + 1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_⟩⟩
      intro j h1 h2
      have hji1 : j = i + 1 := by omega
      rw [hji1]
      exact h_good_succ i hi
    let L : ℕ → ℕ := fun i => if hi : i < ℓ then (SL i hi).min' (hSL_ne i hi) else 0
    let R : ℕ → ℕ := fun i => if hi : i < ℓ then (SR i hi).max' (hSR_ne i hi) else 0
    have hL_mem : ∀ (i : ℕ) (hi : i < ℓ), L i ∈ SL i hi := by
      intro i hi; dsimp only [L]; rw [dite_eq_left hi]; exact Finset.min'_mem (SL i hi) (hSL_ne
          i hi)
    have hL_min : ∀ (i : ℕ) (hi : i < ℓ) (a : ℕ), a ∈ SL i hi → L i ≤ a := by
      intro i hi a ha; dsimp only [L]; rw [dite_eq_left hi]; exact Finset.min'_le (SL i hi) a ha
    have hR_mem : ∀ (i : ℕ) (hi : i < ℓ), R i ∈ SR i hi := by
      intro i hi; dsimp only [R]; rw [dite_eq_left hi]; exact Finset.max'_mem (SR i hi) (hSR_ne
          i hi)
    have hR_max : ∀ (i : ℕ) (hi : i < ℓ) (b : ℕ), b ∈ SR i hi → b ≤ R i := by
      intro i hi b hb; dsimp only [R]; rw [dite_eq_left hi]; exact Finset.le_max' (SR i hi) b hb
    have hL_le : ∀ i < ℓ, L i ≤ i :=
      fun i hi => (Finset.mem_Icc.mp (Finset.mem_filter.mp (hL_mem i hi)).1).2
    have hR_low : ∀ i < ℓ, i + 1 ≤ R i :=
      fun i hi => (Finset.mem_Icc.mp (Finset.mem_filter.mp (hR_mem i hi)).1).1
    have hR_high : ∀ i < ℓ, R i ≤ ℓ :=
      fun i hi => (Finset.mem_Icc.mp (Finset.mem_filter.mp (hR_mem i hi)).1).2
    have h_good_seg : ∀ (i : ℕ) (hi : i < ℓ) (j : ℕ), L i ≤ j → j ≤ R i → Good i hi j := by
      intro i hi j hjL hjR
      by_cases hji : j ≤ i
      · exact (Finset.mem_filter.mp (hL_mem i hi)).2 j hjL hji
      · exact (Finset.mem_filter.mp (hR_mem i hi)).2 j (by omega) hjR
    have h_bad_L : ∀ (i : ℕ) (hi : i < ℓ), 0 < L i → ¬ Good i hi (L i - 1) := by
      intro i hi hLi_pos h_g
      have hLi_le : L i ≤ i := hL_le i hi
      have h_mem : L i - 1 ∈ SL i hi := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩, ?_⟩
        intro j hj1 hj2
        by_cases h_eq : j = L i - 1
        · rw [h_eq]; exact h_g
        · exact (Finset.mem_filter.mp (hL_mem i hi)).2 j (by omega) hj2
      have h_min_le : L i ≤ L i - 1 := hL_min i hi (L i - 1) h_mem
      omega
    have h_bad_R : ∀ (i : ℕ) (hi : i < ℓ), R i < ℓ → ¬ Good i hi (R i + 1) := by
      intro i hi hRi_lt h_g
      have hRi_low : i + 1 ≤ R i := hR_low i hi
      have h_mem : R i + 1 ∈ SR i hi := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        intro j hj1 hj2
        by_cases h_eq : j = R i + 1
        · rw [h_eq]; exact h_g
        · exact (Finset.mem_filter.mp (hR_mem i hi)).2 j hj1 (by omega)
      have h_le_max : R i + 1 ≤ R i := hR_max i hi (R i + 1) h_mem
      omega
    have h_not_full : ∀ i < ℓ, L i ≠ 0 ∨ R i ≠ ℓ := by
      intro i hi
      by_contra h_both
      push Not at h_both
      have hg0 : Good i hi 0 := h_good_seg i hi 0 (by omega) (by omega)
      have hgℓ : Good i hi ℓ := h_good_seg i hi ℓ (by omega) (by omega)
      have h0_eq : (⟨0, Nat.succ_pos ℓ⟩ : Fin (ℓ + 1)) = 0 := by ext; rfl
      have hℓ_eq : (⟨ℓ, Nat.lt_succ_self ℓ⟩ : Fin (ℓ + 1)) = Fin.last ℓ := by ext; rfl
      have hb0 : 8 * (T_fn ⟨i, hi⟩ \ F 0).card < rStar := by
        simpa [h0_eq] using hg0 (Nat.succ_pos ℓ)
      have hbℓ : 8 * (T_fn ⟨i, hi⟩ \ F (Fin.last ℓ)).card < rStar := by
        simpa [hℓ_eq] using hgℓ (Nat.lt_succ_self ℓ)
      have h_cov := h_tri (T_fn ⟨i, hi⟩) (F 0) (F (Fin.last ℓ))
      have h_large_i : rStar < 2 * (T_fn ⟨i, hi⟩).card := h_ex_small ⟨i, hi⟩
      omega
    let Lz : ℤ → ℤ := fun s => if 1 ≤ s ∧ s ≤ (ℓ : ℤ) then (L (s - 1).toNat : ℤ) else 0
    let Rz : ℤ → ℤ := fun s => if 1 ≤ s ∧ s ≤ (ℓ : ℤ) then (R (s - 1).toNat : ℤ) else 0
    obtain ⟨sz, tz, h1s, hst, htℓ, hLz_lt, hLz_ub, hRz_lb, hRz_mono⟩ :=
      HighDimSteinerSpanners.Proofs.Glue.lem_5_1_proof 1 (ℓ : ℤ) le_rfl (by exact_mod_cast hℓ)
          Lz Rz (by
        intro s hs1 hsℓ
        have hi : (s - 1).toNat < ℓ := by omega
        have hLs : Lz s = (L (s - 1).toNat : ℤ) := ite_eq_left ⟨hs1, hsℓ⟩
        have hRs : Rz s = (R (s - 1).toNat : ℤ) := ite_eq_left ⟨hs1, hsℓ⟩
        have h1 := hL_le (s - 1).toNat hi
        have h2 := hR_low (s - 1).toNat hi
        have h3 := hR_high (s - 1).toNat hi
        have h4 := h_not_full (s - 1).toNat hi
        rw [hLs, hRs]
        refine ⟨by omega, by omega, by omega, by omega, ?_⟩
        intro heq
        have heq1 : (L (s - 1).toNat : ℤ) = 1 - 1 := congr_arg Prod.fst heq
        have heq2 : (R (s - 1).toNat : ℤ) = (ℓ : ℤ) := congr_arg Prod.snd heq
        rcases h4 with hL0 | hRℓ <;> omega)
    let i : ℕ := (sz - 1).toNat
    let k : ℕ := (tz - 1).toNat
    have hi_lt : i < ℓ := by dsimp [i]; omega
    have hk_lt : k < ℓ := by dsimp [k]; omega
    have hik : i < k := by dsimp [i, k]; omega
    have hLsz : Lz sz = (L i : ℤ) := ite_eq_left ⟨h1s, by omega⟩
    have hLtz : Lz tz = (L k : ℤ) := ite_eq_left ⟨by omega, htℓ⟩
    have hRsz : Rz sz = (R i : ℤ) := ite_eq_left ⟨h1s, by omega⟩
    have hRtz : Rz tz = (R k : ℤ) := ite_eq_left ⟨by omega, htℓ⟩
    rw [hLsz, hLtz] at hLz_lt
    rw [hLtz] at hLz_ub
    rw [hRsz] at hRz_lb
    rw [hRsz, hRtz] at hRz_mono
    have hLiLk : L i < L k := by omega
    have hLk_ub : L k ≤ i + 1 := by dsimp [i]; omega
    have hk_Ri : k ≤ R i := by dsimp [k]; omega
    have hRiRk : R i + 1 ≤ R k := by omega
    have hRk_high : R k ≤ ℓ := hR_high k hk_lt
    have hRi_low : i + 1 ≤ R i := hR_low i hi_lt
    have hdrop : ∀ (i : Fin ℓ) (j : Fin (ℓ + 1)),
        rStar ≤ 8 * (T_fn i \ F j).card →
          4 * (F j ∩ (F i.castSucc ∪ F i.succ)).card + rStar < 4 * (T_fn i).card :=
      fun i j => (h_spec i).2.2.2.2.2 j
    have h_tk_lt_ti := card_lt_at_right_boundary F T_fn L R rStar h_good_seg h_bad_R hdrop
      ⟨i, hi_lt⟩ ⟨k, hk_lt⟩ hRiRk hLk_ub hRi_low hRk_high
    have h_ti_lt_tk := card_lt_at_left_boundary F T_fn L R rStar h_good_seg h_bad_L hdrop
      ⟨i, hi_lt⟩ ⟨k, hk_lt⟩ hik hLiLk hLk_ub hk_Ri
    exact Nat.lt_irrefl _ (lt_trans h_tk_lt_ti h_ti_lt_tk)

end HighDimSteinerSpanners.Proofs.Combinatorics
