/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import LeanPool.RunsOfMultiples.Replication
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Transferring multiplicative blocks to every large cardinality

Positive-density blocks with controlled size produce the sharp lower asymptotic order.
-/

open Finset Real

@[expose] public section

namespace RunsOfMultiples

/-- A positive-density block with exponential size bounds yields the sharp lower order. -/
theorem lower_bound_of_block {δ C₂ : ℝ} (hδ : 0 < δ) (hC₂ : 0 < C₂)
    (hblock : ∀ y : ℕ, 2 ≤ y → ∃ B G : Finset ℕ,
      (∀ a ∈ B, 0 < a) ∧ G ⊆ B ∧
      (∀ a ∈ G, ∀ j, 1 ≤ j → j ≤ y → j * a ∈ B) ∧ 0 < B.card ∧
      δ * B.card ≤ G.card ∧ (B.card : ℝ) ≤ exp (C₂ * (y / log y))) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ S : Finset ℕ,
    (∀ a ∈ S, 0 < a) ∧ S.card = n ∧
      c * n * Real.log n * Real.log (Real.log n) ≤ ((∑ a ∈ S, kVal S a : ℕ) : ℝ) := by
  set ε := 1 / (2 * C₂) with hεdef
  have hε : 0 < ε := by positivity
  refine ⟨ε * δ / 2, by positivity, ?_⟩
  have hev : ∀ᶠ n : ℕ in Filter.atTop, 4 ≤ n ∧ 2 / ε ≤ log (log (n : ℝ)) :=
    (Filter.eventually_ge_atTop 4).and
      ((tendsto_log_atTop.comp
        (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop (2 / ε))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hn4, hLL⟩ := hN n hn
  set L := log (n : ℝ) with hLdef
  set LL := log L with hLLdef
  have hL0 : 0 ≤ L := Real.log_natCast_nonneg n
  have hLLpos : 0 < LL := lt_of_lt_of_le (by positivity) hLL
  have hL1 : 1 < L := (log_pos_iff hL0).1 hLLpos
  have hεLL : 2 ≤ ε * LL := by
    rw [div_le_iff₀ hε] at hLL; linarith
  set y := ⌊ε * L * LL⌋₊ with hydef
  have hyle : (y : ℝ) ≤ ε * L * LL := Nat.floor_le (by positivity)
  have hylt : ε * L * LL < y + 1 := Nat.lt_floor_add_one _
  have hεLLL : 2 * L ≤ ε * L * LL := by
    nlinarith only [mul_le_mul_of_nonneg_right hεLL hL0]
  have hLy : L ≤ y := by linarith only [hεLLL, hylt, hL1]
  have hy2 : 2 ≤ y := by
    have h1 : (1 : ℝ) < y := by linarith
    have h2 : 1 < y := by exact_mod_cast h1
    omega
  obtain ⟨B, G, hBpos, hGB, hG, hBcard, hGcard, hBle⟩ := hblock y hy2
  have hlogy : LL ≤ log y := log_le_log (by linarith) hLy
  have hQ : (y : ℝ) / log y ≤ ε * L := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ ε * L := by positivity
    nlinarith only [hyle, mul_le_mul_of_nonneg_left hlogy this]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hexp : exp (L / 2) ≤ n / 2 := by
    set e := exp (L / 2) with he
    have hepos : 0 < e := exp_pos _
    have hee : e * e = n := by rw [he, ← exp_add, add_halves, hLdef, exp_log hn0]
    have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    have he2 : 2 ≤ e := by
      by_contra h
      push Not at h
      nlinarith only [hepos, h, hee, hn4']
    nlinarith only [he2, hee, hepos]
  have hBn : (B.card : ℝ) ≤ n / 2 := by
    calc (B.card : ℝ) ≤ exp (C₂ * (y / log y)) := hBle
      _ ≤ exp (L / 2) := by
          refine exp_le_exp.2 ?_
          calc C₂ * (y / log y) ≤ C₂ * (ε * L) := mul_le_mul_of_nonneg_left hQ hC₂.le
            _ = L / 2 := by rw [hεdef]; field_simp
      _ ≤ n / 2 := hexp
  have hBn' : 2 * B.card ≤ n := by
    have : (2 * B.card : ℝ) ≤ n := by linarith
    exact_mod_cast this
  obtain ⟨S, hSpos, hScard, hSsum⟩ := replicate B G y n hBpos hGB hG
  refine ⟨S, hSpos, hScard, ?_⟩
  have htB : n ≤ 2 * (n / B.card * B.card) := by
    have := Nat.lt_div_mul_add (a := n) hBcard
    generalize n / B.card * B.card = q at *
    omega
  have htB' : (n : ℝ) / 2 ≤ ((n / B.card : ℕ) : ℝ) * B.card := by
    have : (n : ℝ) ≤ 2 * (((n / B.card : ℕ) : ℝ) * B.card) := by exact_mod_cast htB
    linarith
  have hsum : (((n / B.card * G.card * (y + 1) : ℕ)) : ℝ) ≤ ((∑ a ∈ S, kVal S a : ℕ) : ℝ) := by
    exact_mod_cast hSsum
  have ht0 : (0 : ℝ) ≤ ((n / B.card : ℕ) : ℝ) := Nat.cast_nonneg _
  have hLLL : 0 ≤ ε * L * LL := by positivity
  calc ε * δ / 2 * n * L * LL = δ * (n / 2) * (ε * L * LL) := by ring
    _ ≤ δ * (((n / B.card : ℕ) : ℝ) * B.card) * (y + 1) := by
        gcongr
    _ = ((n / B.card : ℕ) : ℝ) * (δ * B.card) * (y + 1) := by ring
    _ ≤ ((n / B.card : ℕ) : ℝ) * G.card * (y + 1) := by
        gcongr
    _ = (((n / B.card * G.card * (y + 1) : ℕ)) : ℝ) := by push_cast; ring
    _ ≤ _ := hsum

end RunsOfMultiples
