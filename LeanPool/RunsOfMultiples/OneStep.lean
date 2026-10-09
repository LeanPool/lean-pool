/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import LeanPool.RunsOfMultiples.Entropy

/-!
# The one-step entropy lemma

If `G ⊆ R` and multiplication by `q` maps `G` into `R`, raising a "level" function by one,
then the counting entropy of the level on `R` is at least `(|G|/2) log (2|R|/|G|)`.
-/

open Finset Real

@[expose] public section

namespace RunsOfMultiples

/-- `x ↦ x log (N/x)` is monotone on `(0, N/e]`. -/
lemma mul_log_div_mono {a b N : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbN : b * exp 1 ≤ N) :
    a * log (N / a) ≤ b * log (N / b) := by
  have hb : 0 < b := ha.trans_le hab
  have hN : 0 < N := lt_of_lt_of_le (mul_pos hb (exp_pos 1)) hbN
  have h1 : 1 ≤ log (N / b) := by
    rw [le_log_iff_exp_le (div_pos hN hb), le_div_iff₀ hb]
    linarith [mul_comm b (exp 1)]
  have h2 : log (b / a) ≤ b / a - 1 := log_le_sub_one_of_pos (div_pos hb ha)
  have h3 : log (N / a) = log (N / b) + log (b / a) := by
    rw [← log_mul (div_pos hN hb).ne' (div_pos hb ha).ne']
    congr 1
    field_simp
  have h4 : a * log (b / a) ≤ b - a := by
    have := mul_le_mul_of_nonneg_left h2 ha.le
    have e : a * (b / a - 1) = b - a := by field_simp
    linarith
  rw [h3]
  nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hab)]

/-- `x log (N/x) ≤ N/e`. -/
lemma mul_log_div_le {x N : ℝ} (hx : 0 < x) (hN : 0 < N) : x * log (N / x) ≤ N * exp (-1) := by
  have h := log_le_sub_one_of_pos (div_pos (div_pos hN hx) (exp_pos 1))
  rw [log_div (div_pos hN hx).ne' (exp_pos 1).ne', log_exp] at h
  have h' : log (N / x) ≤ N / x / exp 1 := by linarith
  calc x * log (N / x) ≤ x * (N / x / exp 1) := mul_le_mul_of_nonneg_left h' hx.le
    _ = N * exp (-1) := by rw [exp_neg]; field_simp

/-- `δ ≤ N log (N / (N - δ))` for `0 ≤ δ < N`. -/
lemma le_mul_log_div_sub {δ N : ℝ} (hδ : 0 ≤ δ) (hδN : δ < N) :
    δ ≤ N * log (N / (N - δ)) := by
  have hN : 0 < N := lt_of_le_of_lt hδ hδN
  have hNd : 0 < N - δ := by linarith
  have h := log_le_sub_one_of_pos (div_pos hNd hN)
  have e : log (N / (N - δ)) = - log ((N - δ) / N) := by
    rw [← log_inv, inv_div]
  rw [e]
  have : (N - δ) / N - 1 = -(δ / N) := by field_simp; ring
  rw [this] at h
  have h' : δ / N ≤ -log ((N - δ) / N) := by linarith
  calc δ = N * (δ / N) := by field_simp
    _ ≤ N * -log ((N - δ) / N) := mul_le_mul_of_nonneg_left h' hN.le

/-- **Lemma 3** (one-step entropy). -/
theorem ent_ge_of_shift (R G : Finset ℕ) (lev : ℕ → ℕ) (q : ℕ) (hq : 0 < q) (hGR : G ⊆ R)
    (hmap : ∀ m ∈ G, q * m ∈ R ∧ lev (q * m) = lev m + 1) (hG : G.Nonempty) :
    (G.card : ℝ) / 2 * log (2 * R.card / G.card) ≤ ent R lev := by
  have hR : R.Nonempty := hG.mono hGR
  obtain ⟨j0, hj0, hmax⟩ :=
    exists_max_image R (fun m => (R.filter (fun x => lev x = lev m)).card) hR
  set j := lev j0 with hj
  set N := R.card with hNdef
  set M := (R.filter (fun x => lev x = j)).card with hMdef
  set δ := (R.filter (fun x => ¬ lev x = j)).card with hδdef
  have hNMδ : M + δ = N := card_filter_add_card_filter_not _
  have hMpos : 0 < M := fibre_card_pos hj0
  -- (i) min-entropy bound
  have hi : (N : ℝ) * log (N / M) ≤ ent R lev := by
    unfold ent
    have : (N : ℝ) * log (N / M) = ∑ m ∈ R, log ((N : ℝ) / M) := by
      rw [sum_const, nsmul_eq_mul]
    rw [this]
    refine sum_le_sum fun m hm => ?_
    have hF : (0 : ℝ) < (R.filter (fun x => lev x = lev m)).card := by
      exact_mod_cast fibre_card_pos hm
    have hFM : ((R.filter (fun x => lev x = lev m)).card : ℝ) ≤ M := by
      exact_mod_cast hmax m hm
    have hMpos' : (0 : ℝ) < M := by exact_mod_cast hMpos
    have hNpos : (0 : ℝ) < N := by exact_mod_cast card_pos.2 hR
    exact log_le_log (div_pos hNpos hMpos') (div_le_div_of_nonneg_left hNpos.le hF hFM)
  -- (iii) |G| ≤ 2 δ
  have hiii : G.card ≤ 2 * δ := by
    have h1 : (G.filter (fun x => ¬ lev x = j)).card ≤ δ :=
      card_le_card (filter_subset_filter _ hGR)
    have h2 : (G.filter (fun x => lev x = j)).card ≤ δ := by
      have hsub : (G.filter (fun x => lev x = j)).image (q * ·) ⊆
          R.filter (fun x => ¬ lev x = j) := by
        intro y hy
        rw [mem_image] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        rw [mem_filter] at hx ⊢
        obtain ⟨hR', hlev⟩ := hmap x hx.1
        refine ⟨hR', ?_⟩
        rw [hlev, hx.2]
        omega
      have := card_le_card hsub
      rwa [card_image_of_injective _ (mul_right_injective₀ hq.ne')] at this
    have := card_filter_add_card_filter_not (s := G) (fun x => lev x = j)
    omega
  have hgpos : 0 < G.card := card_pos.2 hG
  have hδpos : 0 < δ := by omega
  -- (ii) bound from the off-`j` part
  have hii : (δ : ℝ) * log (N / δ) ≤ ent R lev := by
    unfold ent
    have hδpos' : (0 : ℝ) < δ := by exact_mod_cast hδpos
    have hNpos : (0 : ℝ) < N := by exact_mod_cast card_pos.2 hR
    calc (δ : ℝ) * log (N / δ)
        = ∑ m ∈ R.filter (fun x => ¬ lev x = j), log ((N : ℝ) / δ) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ R.filter (fun x => ¬ lev x = j),
            log ((N : ℝ) / (R.filter (fun x => lev x = lev m)).card) := by
          refine sum_le_sum fun m hm => ?_
          rw [mem_filter] at hm
          have hF : (0 : ℝ) < (R.filter (fun x => lev x = lev m)).card := by
            exact_mod_cast fibre_card_pos hm.1
          have hFδ : ((R.filter (fun x => lev x = lev m)).card : ℝ) ≤ δ := by
            have : R.filter (fun x => lev x = lev m) ⊆ R.filter (fun x => ¬ lev x = j) := by
              intro x hx
              rw [mem_filter] at hx ⊢
              exact ⟨hx.1, by rw [hx.2]; exact hm.2⟩
            exact_mod_cast card_le_card this
          exact log_le_log (div_pos hNpos hδpos') (div_le_div_of_nonneg_left hNpos.le hF hFδ)
      _ ≤ ∑ m ∈ R, log ((N : ℝ) / (R.filter (fun x => lev x = lev m)).card) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            fun m hm _ => log_card_div_fibre_nonneg hm
  -- conclude
  have hg : (0 : ℝ) < G.card := by exact_mod_cast hgpos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast card_pos.2 hR
  have hx : (0 : ℝ) < (G.card : ℝ) / 2 := by positivity
  have hxδ : (G.card : ℝ) / 2 ≤ δ := by
    have : (G.card : ℝ) ≤ 2 * δ := by exact_mod_cast hiii
    linarith
  have hrw : (G.card : ℝ) / 2 * log (2 * N / G.card) =
      (G.card : ℝ) / 2 * log (N / (G.card / 2)) := by
    congr 2
    field_simp
  rw [hrw]
  by_cases hcase : (δ : ℝ) * exp 1 ≤ N
  · exact (mul_log_div_mono hx hxδ hcase).trans hii
  · push Not at hcase
    have hδN : (δ : ℝ) < N := by
      have : (δ : ℕ) < N := by omega
      exact_mod_cast this
    have hMeq : (M : ℝ) = N - δ := by
      have : ((M + δ : ℕ) : ℝ) = N := by exact_mod_cast hNMδ
      push_cast at this
      linarith
    calc (G.card : ℝ) / 2 * log (N / (G.card / 2)) ≤ N * exp (-1) := mul_log_div_le hx hNpos
      _ ≤ δ := by
          rw [exp_neg]
          rw [mul_inv_le_iff₀ (exp_pos 1)]
          linarith
      _ ≤ N * log (N / (N - δ)) := le_mul_log_div_sub (by positivity) hδN
      _ = N * log (N / M) := by rw [hMeq]
      _ ≤ ent R lev := hi

/-- Weak form: every shifted element contributes `log 2 / 2`. -/
theorem ent_ge_log_two (R G : Finset ℕ) (lev : ℕ → ℕ) (q : ℕ) (hq : 0 < q) (hGR : G ⊆ R)
    (hmap : ∀ m ∈ G, q * m ∈ R ∧ lev (q * m) = lev m + 1) :
    log 2 / 2 * G.card ≤ ent R lev := by
  rcases G.eq_empty_or_nonempty with rfl | hG
  · simpa using ent_nonneg R lev
  have h := ent_ge_of_shift R G lev q hq hGR hmap hG
  have hg : (0 : ℝ) < G.card := by exact_mod_cast card_pos.2 hG
  have hGRc : (G.card : ℝ) ≤ R.card := by exact_mod_cast card_le_card hGR
  have h2 : log 2 ≤ log (2 * R.card / G.card) := by
    apply log_le_log two_pos
    rw [le_div_iff₀ hg]
    linarith
  nlinarith

/-- Sparse form: if `|G| √q ≤ |R|` then the entropy is at least `(|G|/4) log q`. -/
theorem ent_ge_sparse (R G : Finset ℕ) (lev : ℕ → ℕ) (q : ℕ) (hq : 0 < q) (hGR : G ⊆ R)
    (hmap : ∀ m ∈ G, q * m ∈ R ∧ lev (q * m) = lev m + 1)
    (hsparse : (G.card : ℝ) * √(q : ℝ) ≤ R.card) :
    (G.card : ℝ) / 4 * log q ≤ ent R lev := by
  rcases G.eq_empty_or_nonempty with rfl | hG
  · simpa using ent_nonneg R lev
  have h := ent_ge_of_shift R G lev q hq hGR hmap hG
  have hg : (0 : ℝ) < G.card := by exact_mod_cast card_pos.2 hG
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.2 hq'
  have h2 : log q / 2 ≤ log (2 * R.card / G.card) := by
    rw [show log (q : ℝ) / 2 = log √(q : ℝ) by rw [Real.log_sqrt hq'.le]]
    apply log_le_log hsq
    rw [le_div_iff₀ hg]
    nlinarith
  nlinarith

end RunsOfMultiples
