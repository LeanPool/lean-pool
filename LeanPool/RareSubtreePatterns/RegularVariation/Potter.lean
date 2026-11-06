/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.RegularVariation.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform ratio bounds and Potter bounds for regularly varying sequences

Source lines 846–853, equation `eq: potter_bound`. Fix a monotone sequence `a : ℕ → ℝ` with
`0 < a n` for `n ≥ 1`, regularly varying of index `ρ ≥ 0` in the sequential sense
`RegularlyVaryingSeq ρ a`.

* `RegularlyVaryingSeq.eventually_ratio_bounds`: uniformly for `n ≤ m ≤ 2n`,
  `a m / a n = (1 + o(1)) (m/n)^ρ` (uniform convergence on the compact `[1,2]`, obtained from
  monotonicity and a finite grid, as for the uniform convergence theorem).
* `RegularlyVaryingSeq.potter_aux`: the two-sided Potter bounds for `B ≤ x ≤ y`, proved by
  iterated doubling.
* `RegularlyVaryingSeq.potter`: the paper's form for `a` itself:
  `a y / a x ≤ A max ((y/x)^(ρ+δ), (y/x)^(ρ-δ))` for `x, y ≥ B`.
* `RegularlyVaryingSeq.potter_slowlyVarying`: the paper's `eq: potter_bound` for the slowly
  varying part `ℓ(n) = a n / n ^ ρ`.
* `RegularlyVaryingSeq.exists_potter_global`: a version valid for all `1 ≤ x ≤ y`, with a
  constant `C` in place of `A`.

The source cites Bingham–Goldie–Teugels, Theorem 1.5.6, for Potter bounds of slowly varying
functions; here they are proved directly for monotone sequences, without any measurability
or continuity assumption beyond monotonicity.
-/

@[expose] public section

open Filter
open scoped Topology

namespace PoissonDeclumping

namespace RegularlyVaryingSeq

variable {ρ : ℝ} {a : ℕ → ℝ}

/-- Eventual two-sided bound at a fixed `c > 0`. -/
theorem eventually_bounds (hrv : RegularlyVaryingSeq ρ a) {c ε : ℝ} (hc : 0 < c)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (1 - ε) * c ^ ρ < a ⌊c * n⌋₊ / a n ∧
      a ⌊c * n⌋₊ / a n < (1 + ε) * c ^ ρ := by
  have hcρ : 0 < c ^ ρ := Real.rpow_pos_of_pos hc ρ
  have h := hrv c hc
  refine (h.eventually (lt_mem_nhds ?_)).and (h.eventually (gt_mem_nhds ?_))
  · nlinarith
  · nlinarith

/-- Uniform convergence on `[1,2]`: for every `ε > 0`, eventually in `n`, for all `m` with
`n ≤ m ≤ 2n`, `(1-ε)(m/n)^ρ a n ≤ a m ≤ (1+ε)(m/n)^ρ a n`. -/
theorem eventually_ratio_bounds (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 ≤ ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ≤ m → m ≤ 2 * n →
      a m ≤ (1 + ε) * ((m : ℝ) / n) ^ ρ * a n ∧
        (1 - ε) * ((m : ℝ) / n) ^ ρ * a n ≤ a m := by
  set ε₁ : ℝ := min (ε / 3) (1 / 3) with hε₁
  have hε₁pos : 0 < ε₁ := lt_min (by linarith) (by norm_num)
  have hε₁le : ε₁ ≤ ε / 3 := min_le_left _ _
  have hε₁le' : ε₁ ≤ 1 / 3 := min_le_right _ _
  -- a mesh `1/K` such that `(1 + 1/K)^ρ < 1 + ε₁`
  obtain ⟨K, hKρ, hK1⟩ : ∃ K : ℕ, (1 + 1 / (K : ℝ)) ^ ρ < 1 + ε₁ ∧ 1 ≤ K := by
    have h1 : Tendsto (fun K : ℕ => 1 + 1 / (K : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    have ht : Tendsto (fun K : ℕ => (1 + 1 / (K : ℝ)) ^ ρ) atTop (𝓝 ((1 + 0) ^ ρ)) :=
      (Real.continuousAt_rpow_const _ ρ (Or.inr hρ)).tendsto.comp h1
    rw [add_zero, Real.one_rpow] at ht
    exact ((ht.eventually (gt_mem_nhds (by linarith))).and (eventually_ge_atTop 1)).exists
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK1
  set t : ℕ → ℝ := fun i => 1 + (i : ℝ) / K with ht
  have ht1 : ∀ i, 1 ≤ t i := fun i => by
    simp only [ht]
    have : 0 ≤ (i : ℝ) / K := by positivity
    linarith
  have hgrid : ∀ᶠ n : ℕ in atTop, ∀ i ∈ Finset.range (K + 2),
      (1 - ε₁) * t i ^ ρ < a ⌊t i * n⌋₊ / a n ∧ a ⌊t i * n⌋₊ / a n < (1 + ε₁) * t i ^ ρ := by
    rw [Filter.eventually_all_finset]
    intro i _
    exact hrv.eventually_bounds (by linarith [ht1 i]) hε₁pos
  filter_upwards [hgrid, eventually_ge_atTop 1] with n hn hn1 m hnm hm2n
  have han : 0 < a n := hpos n hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  set c : ℝ := (m : ℝ) / n with hc
  have hc1 : 1 ≤ c := by
    rw [hc, le_div_iff₀ hnR, one_mul]
    exact_mod_cast hnm
  have hcn : (m : ℝ) = c * n := by rw [hc]; field_simp
  set i : ℕ := ⌊(c - 1) * K⌋₊ with hi
  have hc1K : 0 ≤ (c - 1) * K := mul_nonneg (by linarith) hKR.le
  have hiK : i ≤ K := by
    apply Nat.floor_le_of_le
    have hc2 : c ≤ 2 := by
      rw [hc, div_le_iff₀ hnR]
      exact_mod_cast hm2n
    nlinarith
  have hti : t i ≤ c := by
    have h := Nat.floor_le hc1K
    rw [← hi] at h
    simp only [ht]
    have : (i : ℝ) / K ≤ c - 1 := by rw [div_le_iff₀ hKR]; exact h
    linarith
  have hti1 : c < t (i + 1) := by
    have h := Nat.lt_floor_add_one ((c - 1) * K)
    rw [← hi] at h
    simp only [ht]
    have : c - 1 < ((i + 1 : ℕ) : ℝ) / K := by
      rw [lt_div_iff₀ hKR]
      push_cast
      exact h
    linarith
  have htsucc : t (i + 1) = t i + 1 / K := by
    simp only [ht]
    push_cast
    ring
  have hup_t : t (i + 1) ≤ (1 + 1 / (K : ℝ)) * c := by
    have : 1 / (K : ℝ) ≤ c * (1 / K) := le_mul_of_one_le_left (by positivity) hc1
    rw [htsucc]
    nlinarith
  have hc_up : c ≤ (1 + 1 / (K : ℝ)) * t i := by
    have : 1 / (K : ℝ) ≤ t i * (1 / K) := le_mul_of_one_le_left (by positivity) (ht1 i)
    have := htsucc
    nlinarith
  have hpow_le : ∀ u v : ℝ, 0 ≤ u → u ≤ (1 + 1 / (K : ℝ)) * v → 0 ≤ v →
      u ^ ρ ≤ (1 + ε₁) * v ^ ρ := by
    intro u v hu huv hv
    calc u ^ ρ ≤ ((1 + 1 / (K : ℝ)) * v) ^ ρ := Real.rpow_le_rpow hu huv hρ
      _ = (1 + 1 / (K : ℝ)) ^ ρ * v ^ ρ := Real.mul_rpow (by positivity) hv
      _ ≤ (1 + ε₁) * v ^ ρ := by gcongr
  have hti_mem : i ∈ Finset.range (K + 2) := Finset.mem_range.2 (by omega)
  have hti1_mem : i + 1 ∈ Finset.range (K + 2) := Finset.mem_range.2 (by omega)
  have hcρ : 0 ≤ c ^ ρ := Real.rpow_nonneg (by linarith) ρ
  have htiρ : 0 ≤ t i ^ ρ := Real.rpow_nonneg (by linarith [ht1 i]) ρ
  constructor
  · -- upper bound through the grid point `t (i+1)`
    have hm_le : m ≤ ⌊t (i + 1) * n⌋₊ := by
      apply Nat.le_floor
      rw [hcn]
      exact mul_le_mul_of_nonneg_right hti1.le hnR.le
    have h1 := (hn (i + 1) hti1_mem).2
    rw [div_lt_iff₀ han] at h1
    have h2 := hpow_le (t (i + 1)) c (by linarith [ht1 (i + 1)]) hup_t (by linarith)
    calc a m ≤ a ⌊t (i + 1) * n⌋₊ := hmono hm_le
      _ ≤ (1 + ε₁) * t (i + 1) ^ ρ * a n := h1.le
      _ ≤ (1 + ε₁) * ((1 + ε₁) * c ^ ρ) * a n := by gcongr
      _ ≤ (1 + ε) * c ^ ρ * a n := by
          have : (1 + ε₁) * (1 + ε₁) ≤ 1 + ε := by nlinarith
          have := mul_le_mul_of_nonneg_right this (mul_nonneg hcρ han.le)
          nlinarith
  · -- lower bound through the grid point `t i`
    have hm_ge : ⌊t i * n⌋₊ ≤ m := by
      apply Nat.floor_le_of_le
      rw [hcn]
      exact mul_le_mul_of_nonneg_right hti hnR.le
    have h1 := (hn i hti_mem).1
    rw [lt_div_iff₀ han] at h1
    have h2 := hpow_le c (t i) (by linarith) hc_up (by linarith [ht1 i])
    have key : (1 - ε) * c ^ ρ ≤ (1 - ε₁) * t i ^ ρ := by
      rcases le_or_gt ε 1 with hε1 | hε1
      · calc (1 - ε) * c ^ ρ ≤ (1 - ε) * ((1 + ε₁) * t i ^ ρ) :=
              mul_le_mul_of_nonneg_left h2 (by linarith)
          _ = ((1 - ε) * (1 + ε₁)) * t i ^ ρ := by ring
          _ ≤ (1 - ε₁) * t i ^ ρ := by
              have : (1 - ε) * (1 + ε₁) ≤ 1 - ε₁ := by nlinarith
              exact mul_le_mul_of_nonneg_right this htiρ
      · have : (1 - ε) * c ^ ρ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hcρ
        have : 0 ≤ (1 - ε₁) * t i ^ ρ := mul_nonneg (by linarith) htiρ
        linarith
    calc (1 - ε) * c ^ ρ * a n ≤ (1 - ε₁) * t i ^ ρ * a n :=
          mul_le_mul_of_nonneg_right key han.le
      _ ≤ a ⌊t i * n⌋₊ := h1.le
      _ ≤ a m := hmono hm_ge

/-- Two-sided Potter bounds for `a` itself, for `B ≤ x ≤ y`:
`a y ≤ A (y/x)^(ρ+δ) a x` and `(y/x)^(ρ-δ) a x ≤ A a y`. -/
theorem potter_aux (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 ≤ ρ) {A δ : ℝ} (hA : 1 < A) (hδ : 0 < δ) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ x y : ℕ, B ≤ x → x ≤ y →
      a y ≤ A * ((y : ℝ) / x) ^ (ρ + δ) * a x ∧ ((y : ℝ) / x) ^ (ρ - δ) * a x ≤ A * a y := by
  set D : ℝ := (2 : ℝ) ^ δ with hD
  have hD1 : 1 < D := Real.one_lt_rpow (by norm_num) hδ
  have hA' : 0 < 1 - 1 / A := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact hA
  have hD' : 0 < 1 - 1 / D := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact hD1
  set ε : ℝ := min (min (A - 1) (D - 1)) (min (1 - 1 / A) (1 - 1 / D)) with hε
  have hεpos : 0 < ε := lt_min (lt_min (by linarith) (by linarith)) (lt_min hA' hD')
  have hεA : 1 + ε ≤ A := by
    have : ε ≤ A - 1 := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hεD : 1 + ε ≤ D := by
    have : ε ≤ D - 1 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hεA' : 1 ≤ A * (1 - ε) := by
    have h : ε ≤ 1 - 1 / A := (min_le_right _ _).trans (min_le_left _ _)
    have : A * (1 / A) = 1 := by field_simp
    nlinarith
  have hεD' : 1 ≤ D * (1 - ε) := by
    have h : ε ≤ 1 - 1 / D := (min_le_right _ _).trans (min_le_right _ _)
    have : D * (1 / D) = 1 := by field_simp
    nlinarith
  have hε1 : ε < 1 := by
    have h : ε ≤ 1 - 1 / A := (min_le_right _ _).trans (min_le_left _ _)
    have : 0 < 1 / A := by positivity
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hrv.eventually_ratio_bounds hmono hpos hρ hεpos)
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  have key : ∀ k : ℕ, ∀ x : ℕ, max N 1 ≤ x → ∀ y : ℕ, x ≤ y → y ≤ 2 ^ k * x →
      a y ≤ (1 + ε) * ((y : ℝ) / x) ^ (ρ + δ) * a x ∧
        (1 - ε) * ((y : ℝ) / x) ^ (ρ - δ) * a x ≤ a y := by
    intro k
    induction k with
    | zero =>
      intro x hx y hxy hy
      have hyx : y = x := le_antisymm (by simpa using hy) hxy
      subst hyx
      have hy1 : 1 ≤ y := le_trans (le_max_right _ _) hx
      have hay := hpos y hy1
      have hy0 : (y : ℝ) ≠ 0 := by positivity
      rw [div_self hy0, Real.one_rpow, Real.one_rpow]
      constructor <;> nlinarith
    | succ k ih =>
      intro x hx y hxy hy
      have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
      have hxN : N ≤ x := le_trans (le_max_left _ _) hx
      have hax := hpos x hx1
      have hxR : (0 : ℝ) < x := by exact_mod_cast hx1
      have hyx : (1 : ℝ) ≤ (y : ℝ) / x := by
        rw [le_div_iff₀ hxR, one_mul]
        exact_mod_cast hxy
      by_cases h2 : y ≤ 2 * x
      · obtain ⟨hu, hl⟩ := hN x hxN y hxy h2
        constructor
        · calc a y ≤ (1 + ε) * ((y : ℝ) / x) ^ ρ * a x := hu
            _ ≤ (1 + ε) * ((y : ℝ) / x) ^ (ρ + δ) * a x := by
                have : ((y : ℝ) / x) ^ ρ ≤ ((y : ℝ) / x) ^ (ρ + δ) :=
                  Real.rpow_le_rpow_of_exponent_le hyx (by linarith)
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left this (by linarith)) hax.le
        · calc (1 - ε) * ((y : ℝ) / x) ^ (ρ - δ) * a x
              ≤ (1 - ε) * ((y : ℝ) / x) ^ ρ * a x := by
                have : ((y : ℝ) / x) ^ (ρ - δ) ≤ ((y : ℝ) / x) ^ ρ :=
                  Real.rpow_le_rpow_of_exponent_le hyx (by linarith)
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left this (by linarith)) hax.le
            _ ≤ a y := hl
      · have h2 := not_le.1 h2
        have h2x : max N 1 ≤ 2 * x := le_trans hx (by omega)
        have hy' : y ≤ 2 ^ k * (2 * x) := by
          rw [pow_succ] at hy
          calc y ≤ 2 ^ k * 2 * x := hy
            _ = 2 ^ k * (2 * x) := by ring
        obtain ⟨hu, hl⟩ := ih (2 * x) h2x y h2.le hy'
        obtain ⟨hu2, hl2⟩ := hN x hxN (2 * x) (by omega) le_rfl
        have h2div : ((2 * x : ℕ) : ℝ) / x = 2 := by
          push_cast
          field_simp
        rw [h2div] at hu2 hl2
        have hsplit : ∀ r : ℝ, ((y : ℝ) / x) ^ r =
            ((y : ℝ) / ((2 * x : ℕ) : ℝ)) ^ r * (2 : ℝ) ^ r := by
          intro r
          rw [← Real.mul_rpow (by positivity) (by norm_num)]
          congr 1
          push_cast
          field_simp
        have hup2 : a (2 * x) ≤ (2 : ℝ) ^ (ρ + δ) * a x := by
          rw [Real.rpow_add (by norm_num)]
          calc a (2 * x) ≤ (1 + ε) * 2 ^ ρ * a x := hu2
            _ ≤ D * 2 ^ ρ * a x := by gcongr
            _ = 2 ^ ρ * 2 ^ δ * a x := by rw [hD]; ring
        have hlo2 : (2 : ℝ) ^ (ρ - δ) * a x ≤ a (2 * x) := by
          rw [Real.rpow_sub (by norm_num)]
          have h2ρ : 0 < (2 : ℝ) ^ ρ := by positivity
          have hDpos : 0 < D := by linarith
          calc 2 ^ ρ / 2 ^ δ * a x = 2 ^ ρ * a x * (1 / D) := by rw [hD]; ring
            _ ≤ 2 ^ ρ * a x * (1 - ε) := by
                gcongr
                rw [div_le_iff₀ hDpos]
                linarith
            _ = (1 - ε) * 2 ^ ρ * a x := by ring
            _ ≤ a (2 * x) := hl2
        have hpow0 : ∀ r : ℝ, 0 ≤ ((y : ℝ) / ((2 * x : ℕ) : ℝ)) ^ r := fun r => by positivity
        constructor
        · calc a y ≤ (1 + ε) * ((y : ℝ) / ((2 * x : ℕ) : ℝ)) ^ (ρ + δ) * a (2 * x) := hu
            _ ≤ (1 + ε) * ((y : ℝ) / ((2 * x : ℕ) : ℝ)) ^ (ρ + δ) * (2 ^ (ρ + δ) * a x) := by
                have := hpow0 (ρ + δ)
                gcongr
            _ = (1 + ε) * ((y : ℝ) / x) ^ (ρ + δ) * a x := by rw [hsplit]; ring
        · calc (1 - ε) * ((y : ℝ) / x) ^ (ρ - δ) * a x
              = (1 - ε) * ((y : ℝ) / ((2 * x : ℕ) : ℝ)) ^ (ρ - δ) * (2 ^ (ρ - δ) * a x) := by
                rw [hsplit]; ring
            _ ≤ (1 - ε) * ((y : ℝ) / ((2 * x : ℕ) : ℝ)) ^ (ρ - δ) * a (2 * x) := by
                exact mul_le_mul_of_nonneg_left hlo2 (mul_nonneg (by linarith) (hpow0 _))
            _ ≤ a y := hl
  intro x y hx hxy
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hax := hpos x hx1
  have hay := hpos y (hx1.trans hxy)
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx1
  have hyR : (0 : ℝ) < y := by exact_mod_cast (hx1.trans hxy)
  obtain ⟨hu, hl⟩ := key y x hx y hxy (by
    calc y ≤ 2 ^ y := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ y * x := Nat.le_mul_of_pos_right _ hx1)
  have hp : ∀ r : ℝ, 0 ≤ ((y : ℝ) / x) ^ r := fun r => by positivity
  constructor
  · calc a y ≤ (1 + ε) * ((y : ℝ) / x) ^ (ρ + δ) * a x := hu
      _ ≤ A * ((y : ℝ) / x) ^ (ρ + δ) * a x := by
          have := hp (ρ + δ)
          gcongr
  · have h0 : 0 ≤ ((y : ℝ) / x) ^ (ρ - δ) * a x := mul_nonneg (hp _) hax.le
    calc ((y : ℝ) / x) ^ (ρ - δ) * a x ≤ (A * (1 - ε)) * (((y : ℝ) / x) ^ (ρ - δ) * a x) :=
          le_mul_of_one_le_left h0 hεA'
      _ = A * ((1 - ε) * ((y : ℝ) / x) ^ (ρ - δ) * a x) := by ring
      _ ≤ A * a y := by gcongr

/-- **Potter bounds** for the regularly varying sequence `a` itself (source eq.
`eq: potter_bound`, transferred from the slowly varying part to `a`): for every `A > 1` and
`δ > 0` there is `B` such that for all `x, y ≥ B`,
`a y / a x ≤ A * max ((y/x)^(ρ+δ)) ((y/x)^(ρ-δ))`. -/
theorem potter (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 ≤ ρ) {A δ : ℝ} (hA : 1 < A) (hδ : 0 < δ) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ x y : ℕ, B ≤ x → B ≤ y →
      a y / a x ≤ A * max (((y : ℝ) / x) ^ (ρ + δ)) (((y : ℝ) / x) ^ (ρ - δ)) := by
  obtain ⟨B, hB1, hB⟩ := hrv.potter_aux hmono hpos hρ hA hδ
  refine ⟨B, hB1, fun x y hx hy => ?_⟩
  have hax : 0 < a x := hpos x (hB1.trans hx)
  have hay : 0 < a y := hpos y (hB1.trans hy)
  have hxR : (0 : ℝ) < x := by exact_mod_cast hB1.trans hx
  have hyR : (0 : ℝ) < y := by exact_mod_cast hB1.trans hy
  rw [div_le_iff₀ hax]
  rcases le_total x y with hxy | hyx
  · calc a y ≤ A * ((y : ℝ) / x) ^ (ρ + δ) * a x := (hB x y hx hxy).1
      _ ≤ A * max (((y : ℝ) / x) ^ (ρ + δ)) (((y : ℝ) / x) ^ (ρ - δ)) * a x := by
          gcongr
          exact le_max_left _ _
  · have h := (hB y x hy hyx).2
    have hinv : ((x : ℝ) / y) ^ (ρ - δ) = (((y : ℝ) / x) ^ (ρ - δ))⁻¹ := by
      rw [← Real.inv_rpow (by positivity), inv_div]
    rw [hinv] at h
    have hp : 0 < ((y : ℝ) / x) ^ (ρ - δ) := by positivity
    calc a y = ((y : ℝ) / x) ^ (ρ - δ) * ((((y : ℝ) / x) ^ (ρ - δ))⁻¹ * a y) := by
          field_simp
      _ ≤ ((y : ℝ) / x) ^ (ρ - δ) * (A * a x) := by gcongr
      _ = A * ((y : ℝ) / x) ^ (ρ - δ) * a x := by ring
      _ ≤ A * max (((y : ℝ) / x) ^ (ρ + δ)) (((y : ℝ) / x) ^ (ρ - δ)) * a x := by
          gcongr
          exact le_max_right _ _

/-- **Potter bounds** (source eq. `eq: potter_bound`) for the slowly varying part
`ℓ(n) = a n / n ^ ρ` of the sequence: for every `A > 1` and `δ > 0` there is `B` such that for
all `x, y ≥ B`, `ℓ(y) / ℓ(x) ≤ A * max ((y/x)^δ) ((y/x)^(-δ))`. -/
theorem potter_slowlyVarying (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 ≤ ρ) {A δ : ℝ} (hA : 1 < A) (hδ : 0 < δ) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ x y : ℕ, B ≤ x → B ≤ y →
      (a y / (y : ℝ) ^ ρ) / (a x / (x : ℝ) ^ ρ) ≤
        A * max (((y : ℝ) / x) ^ δ) (((y : ℝ) / x) ^ (-δ)) := by
  obtain ⟨B, hB1, hB⟩ := hrv.potter hmono hpos hρ hA hδ
  refine ⟨B, hB1, fun x y hx hy => ?_⟩
  have hax : 0 < a x := hpos x (hB1.trans hx)
  have hay : 0 < a y := hpos y (hB1.trans hy)
  have hxR : (0 : ℝ) < x := by exact_mod_cast hB1.trans hx
  have hyR : (0 : ℝ) < y := by exact_mod_cast hB1.trans hy
  have hq : 0 < (y : ℝ) / x := by positivity
  have hqρ : 0 < ((y : ℝ) / x) ^ ρ := by positivity
  have hlhs : (a y / (y : ℝ) ^ ρ) / (a x / (x : ℝ) ^ ρ) = (a y / a x) / ((y : ℝ) / x) ^ ρ := by
    rw [Real.div_rpow hyR.le hxR.le]
    have : (0 : ℝ) < (x : ℝ) ^ ρ := by positivity
    have : (0 : ℝ) < (y : ℝ) ^ ρ := by positivity
    field_simp
  have hmax : max (((y : ℝ) / x) ^ (ρ + δ)) (((y : ℝ) / x) ^ (ρ - δ)) =
      ((y : ℝ) / x) ^ ρ * max (((y : ℝ) / x) ^ δ) (((y : ℝ) / x) ^ (-δ)) := by
    rw [Real.rpow_add hq, sub_eq_add_neg, Real.rpow_add hq, mul_max_of_nonneg _ _ hqρ.le]
  rw [hlhs, div_le_iff₀ hqρ]
  calc a y / a x ≤ A * max (((y : ℝ) / x) ^ (ρ + δ)) (((y : ℝ) / x) ^ (ρ - δ)) :=
        hB x y hx hy
    _ = A * max (((y : ℝ) / x) ^ δ) (((y : ℝ) / x) ^ (-δ)) * ((y : ℝ) / x) ^ ρ := by
        rw [hmax]; ring

/-- **Global Potter bounds**: for every `δ > 0` there is `C > 0` such that for all
`1 ≤ x ≤ y`, `a y ≤ C (y/x)^(ρ+δ) a x` and `(y/x)^(ρ-δ) a x ≤ C a y`. -/
theorem exists_potter_global (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hρ : 0 ≤ ρ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℕ, 1 ≤ x → x ≤ y →
      a y ≤ C * ((y : ℝ) / x) ^ (ρ + δ) * a x ∧ ((y : ℝ) / x) ^ (ρ - δ) * a x ≤ C * a y := by
  obtain ⟨B, hB1, hB⟩ := hrv.potter_aux hmono hpos hρ (by norm_num : (1 : ℝ) < 2) hδ
  have ha1 : 0 < a 1 := hpos 1 le_rfl
  set K : ℝ := a B / a 1 with hKdef
  have hK : 1 ≤ K := by
    rw [hKdef, le_div_iff₀ ha1, one_mul]
    exact hmono hB1
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hBρ : 1 ≤ (B : ℝ) ^ ρ := Real.one_le_rpow hBR hρ
  have hC1 : 2 ≤ 2 * K * (B : ℝ) ^ ρ := by nlinarith
  have hC2 : K ≤ 2 * K * (B : ℝ) ^ ρ := by nlinarith
  have hC3 : (B : ℝ) ^ ρ ≤ 2 * K * (B : ℝ) ^ ρ := by nlinarith
  refine ⟨2 * K * (B : ℝ) ^ ρ, by positivity, fun x y hx hxy => ?_⟩
  have hax := hpos x hx
  have hay := hpos y (hx.trans hxy)
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hxy' : (x : ℝ) ≤ y := by exact_mod_cast hxy
  have hyx : (1 : ℝ) ≤ (y : ℝ) / x := by
    rw [le_div_iff₀ hxR, one_mul]
    exact hxy'
  have hKx : a B ≤ K * a x := by
    calc a B = K * a 1 := by rw [hKdef]; field_simp
      _ ≤ K * a x := by gcongr; exact hmono hx
  have hpp : 1 ≤ ((y : ℝ) / x) ^ (ρ + δ) := Real.one_le_rpow hyx (by linarith)
  constructor
  · rcases le_or_gt B x with hBx | hxB
    · calc a y ≤ 2 * ((y : ℝ) / x) ^ (ρ + δ) * a x := (hB x y hBx hxy).1
        _ ≤ 2 * K * (B : ℝ) ^ ρ * ((y : ℝ) / x) ^ (ρ + δ) * a x := by
            have : 0 ≤ ((y : ℝ) / x) ^ (ρ + δ) * a x := by positivity
            nlinarith
    rcases le_or_gt B y with hBy | hyB
    · have h1 := (hB B y le_rfl hBy).1
      have h2 : ((y : ℝ) / B) ^ (ρ + δ) ≤ ((y : ℝ) / x) ^ (ρ + δ) := by
        apply Real.rpow_le_rpow (by positivity) _ (by linarith)
        apply div_le_div_of_nonneg_left (by positivity) hxR
        exact_mod_cast hxB.le
      calc a y ≤ 2 * ((y : ℝ) / B) ^ (ρ + δ) * a B := h1
        _ ≤ 2 * ((y : ℝ) / x) ^ (ρ + δ) * (K * a x) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) hKx
              (hpos B hB1).le (by positivity)
        _ = K * (2 * ((y : ℝ) / x) ^ (ρ + δ) * a x) := by ring
        _ ≤ K * (2 * ((y : ℝ) / x) ^ (ρ + δ) * a x) * (B : ℝ) ^ ρ :=
            le_mul_of_one_le_right (by positivity) hBρ
        _ = 2 * K * (B : ℝ) ^ ρ * ((y : ℝ) / x) ^ (ρ + δ) * a x := by ring
    · calc a y ≤ a B := hmono hyB.le
        _ ≤ K * a x := hKx
        _ ≤ 2 * K * (B : ℝ) ^ ρ * ((y : ℝ) / x) ^ (ρ + δ) * a x := by
            have h0 : 0 ≤ K * a x := by positivity
            have : K * a x ≤ (2 * K * (B : ℝ) ^ ρ) * a x := by gcongr
            have : (2 * K * (B : ℝ) ^ ρ) * a x ≤
                (2 * K * (B : ℝ) ^ ρ) * a x * ((y : ℝ) / x) ^ (ρ + δ) :=
              le_mul_of_one_le_right (by positivity) hpp
            nlinarith
  · have hle : ((y : ℝ) / x) ^ (ρ - δ) ≤ ((y : ℝ) / x) ^ ρ :=
      Real.rpow_le_rpow_of_exponent_le hyx (by linarith)
    rcases le_or_gt B x with hBx | hxB
    · calc ((y : ℝ) / x) ^ (ρ - δ) * a x ≤ 2 * a y := (hB x y hBx hxy).2
        _ ≤ 2 * K * (B : ℝ) ^ ρ * a y := by gcongr
    rcases le_or_gt B y with hBy | hyB
    · have h1 := (hB B y le_rfl hBy).2
      have hBx1 : (1 : ℝ) ≤ (B : ℝ) / x := by
        rw [le_div_iff₀ hxR, one_mul]
        exact_mod_cast hxB.le
      have hsplit : ((y : ℝ) / x) ^ (ρ - δ) = ((y : ℝ) / B) ^ (ρ - δ) * ((B : ℝ) / x) ^ (ρ - δ) :=
        by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        have : (B : ℝ) ≠ 0 := by positivity
        field_simp
      have h3 : ((B : ℝ) / x) ^ (ρ - δ) ≤ (B : ℝ) ^ ρ :=
        calc ((B : ℝ) / x) ^ (ρ - δ) ≤ ((B : ℝ) / x) ^ ρ :=
              Real.rpow_le_rpow_of_exponent_le hBx1 (by linarith)
          _ ≤ (B : ℝ) ^ ρ := by
              apply Real.rpow_le_rpow (by positivity) _ hρ
              apply div_le_self (by positivity)
              exact_mod_cast hx
      have hp0 : 0 ≤ ((y : ℝ) / B) ^ (ρ - δ) := by positivity
      calc ((y : ℝ) / x) ^ (ρ - δ) * a x
          = ((y : ℝ) / B) ^ (ρ - δ) * ((B : ℝ) / x) ^ (ρ - δ) * a x := by rw [hsplit]
        _ ≤ ((y : ℝ) / B) ^ (ρ - δ) * (B : ℝ) ^ ρ * a B := by
            gcongr
            exact hmono hxB.le
        _ = (B : ℝ) ^ ρ * (((y : ℝ) / B) ^ (ρ - δ) * a B) := by ring
        _ ≤ (B : ℝ) ^ ρ * (2 * a y) := by gcongr
        _ ≤ K * ((B : ℝ) ^ ρ * (2 * a y)) := le_mul_of_one_le_left (by positivity) hK
        _ = 2 * K * (B : ℝ) ^ ρ * a y := by ring
    · have h3 : ((y : ℝ) / x) ^ ρ ≤ (B : ℝ) ^ ρ := by
        apply Real.rpow_le_rpow (by positivity) _ hρ
        calc (y : ℝ) / x ≤ y := div_le_self (by positivity) (by exact_mod_cast hx)
          _ ≤ B := by exact_mod_cast hyB.le
      calc ((y : ℝ) / x) ^ (ρ - δ) * a x ≤ (B : ℝ) ^ ρ * a y :=
            mul_le_mul (hle.trans h3) (hmono hxy) hax.le (by positivity)
        _ ≤ 2 * K * (B : ℝ) ^ ρ * a y := by gcongr

end RegularlyVaryingSeq

end PoissonDeclumping
