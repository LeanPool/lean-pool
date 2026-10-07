/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Kato Regularization

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

noncomputable section
namespace CIV

/-- The smooth positive part: `katoSmooth kap g x` is a smooth approximation of `max (g x) 0`
that equals `(g x + |g x|)/2` when `kap = 0`. -/
@[expose] def katoSmooth (kap : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  (g x + Real.sqrt ((g x) ^ 2 + kap ^ 2)) / 2 - kap / 2

/-- The identity `max a 0 = (a + |a|) / 2`. -/
lemma max_eq_add_abs_div_two (a : ℝ) : max a 0 = (a + |a|) / 2 := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, abs_of_nonpos h]
    ring
  · rw [max_eq_left h, abs_of_nonneg h]
    ring

/-- The radicand `g x ^ 2 + kap ^ 2` is strictly positive when `kap ≠ 0`. -/
lemma radicand_pos (kap : ℝ) (g : ℝ → ℝ) (x : ℝ) (hkap : kap ≠ 0) : 0 < (g x) ^ 2 + kap ^ 2 := by
  have hkap_sq_pos : 0 < kap ^ 2 := sq_pos_iff.mpr hkap
  positivity

/-- The radicand `g x ^ 2 + kap ^ 2` is nonzero when `kap > 0`. -/
lemma radicand_ne_zero (kap : ℝ) (g : ℝ → ℝ) (x : ℝ) (hkap : 0 < kap) : (g x) ^ 2 + kap ^ 2 ≠ 0
    := by
  have hpos := radicand_pos kap g x hkap.ne'
  linarith only [hpos]

theorem katoSmooth_le_posPart (kap : ℝ) (hkap : 0 < kap) (g : ℝ → ℝ) (x : ℝ) :
    katoSmooth kap g x ≤ max (g x) 0 := by
  dsimp [katoSmooth]
  have h_sqrt_le : Real.sqrt ((g x) ^ 2 + kap ^ 2) ≤ |g x| + kap := by
    have h_sq_bound : (g x) ^ 2 + kap ^ 2 ≤ (|g x| + kap) ^ 2 := by
      calc
        (g x) ^ 2 + kap ^ 2 = (|g x|) ^ 2 + kap ^ 2 := by rw [sq_abs (g x)]
        _ ≤ (|g x|) ^ 2 + 2 * |g x| * kap + kap ^ 2 := by
          have : 0 ≤ 2 * |g x| * kap := by positivity
          nlinarith only [this]
        _ = (|g x| + kap) ^ 2 := by ring
    have h_nonneg : 0 ≤ |g x| + kap := by
      have h_abs_nonneg : 0 ≤ |g x| := abs_nonneg _
      linarith only [h_abs_nonneg, hkap]
    calc
      Real.sqrt ((g x) ^ 2 + kap ^ 2) ≤ Real.sqrt ((|g x| + kap) ^ 2) :=
        Real.sqrt_le_sqrt h_sq_bound
      _ = |g x| + kap := Real.sqrt_sq h_nonneg
  rw [max_eq_add_abs_div_two (g x)]
  nlinarith only [h_sqrt_le]

theorem posPart_sub_katoSmooth_le (kap : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    max (g x) 0 - katoSmooth kap g x ≤ kap / 2 := by
  dsimp [katoSmooth]
  rw [max_eq_add_abs_div_two (g x)]
  have h_sqrt_ge_abs : |g x| ≤ Real.sqrt ((g x) ^ 2 + kap ^ 2) := by
    have h_sq_bound : (|g x|) ^ 2 ≤ (g x) ^ 2 + kap ^ 2 := by
      rw [sq_abs (g x)]
      nlinarith only [sq_nonneg kap]
    have h_nonneg_abs : 0 ≤ |g x| := abs_nonneg _
    calc
      |g x| = Real.sqrt ((|g x|) ^ 2) := by rw [Real.sqrt_sq h_nonneg_abs]
      _ ≤ Real.sqrt ((g x) ^ 2 + kap ^ 2) := Real.sqrt_le_sqrt h_sq_bound
  nlinarith only [h_sqrt_ge_abs]

theorem contDiff_katoSmooth {n : WithTop ℕ∞} (kap : ℝ) (hkap : 0 < kap) {g : ℝ → ℝ}
    (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (katoSmooth kap g) := by
  unfold katoSmooth
  have h_radicand_contDiff : ContDiff ℝ n (fun x : ℝ => (g x) ^ 2 + kap ^ 2) :=
    (hg.pow 2).add contDiff_const
  have h_radicand_ne_zero : ∀ x : ℝ, (g x) ^ 2 + kap ^ 2 ≠ 0 := by
    intro x
    exact radicand_ne_zero kap g x hkap
  have h_sqrt_contDiff : ContDiff ℝ n (fun x : ℝ => Real.sqrt ((g x) ^ 2 + kap ^ 2)) :=
    h_radicand_contDiff.sqrt h_radicand_ne_zero
  have h_add : ContDiff ℝ n (fun x : ℝ => g x + Real.sqrt ((g x) ^ 2 + kap ^ 2)) :=
    hg.add h_sqrt_contDiff
  have h_div_two : ContDiff ℝ n (fun x : ℝ => (g x + Real.sqrt ((g x) ^ 2 + kap ^ 2)) / 2) :=
    h_add.div_const 2
  have h_kap_div_two : ContDiff ℝ n (fun _ : ℝ => kap / 2) := contDiff_const
  exact h_div_two.sub h_kap_div_two

theorem tendsto_katoSmooth (g : ℝ → ℝ) (x : ℝ) :
    Filter.Tendsto (fun kap : ℝ => katoSmooth kap g x) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (max (g x) 0)) := by
  set f := fun kap : ℝ => max (g x) 0 - kap / 2 with hf_def
  set gk := fun kap : ℝ => katoSmooth kap g x with hgk_def
  set h := fun _ : ℝ => max (g x) 0 with hh_def
  have h_lower_tendsto : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds (max (g x) 0)) := by
    have h_tendsto_div : Filter.Tendsto (fun kap : ℝ => kap / 2) (nhds 0) (nhds 0) := by
      have h_tendsto_kap : Filter.Tendsto (fun kap : ℝ => kap) (nhds 0) (nhds 0) :=
        continuous_id.tendsto 0
      simpa [div_eq_mul_inv] using h_tendsto_kap.mul_const (1/2 : ℝ)
    have h_sub_tendsto : Filter.Tendsto (fun kap : ℝ => max (g x) 0 - kap / 2) (nhds 0) (nhds
      (max (g x) 0)) := by
      simpa [sub_zero] using Filter.Tendsto.sub (tendsto_const_nhds (x := max (g x) 0))
        h_tendsto_div
    exact h_sub_tendsto.mono_left nhdsWithin_le_nhds
  have h_upper_tendsto : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds (max (g x) 0)) :=
    tendsto_const_nhds.mono_left nhdsWithin_le_nhds
  have h_lower_eventually : f ≤ᶠ[nhdsWithin 0 (Set.Ioi 0)] gk := by
    filter_upwards [self_mem_nhdsWithin] with kap hkap
    have hpos : 0 < kap := Set.mem_Ioi.mp hkap
    dsimp [f, gk]
    have hle := posPart_sub_katoSmooth_le kap g x
    linarith only [hle]
  have h_upper_eventually : gk ≤ᶠ[nhdsWithin 0 (Set.Ioi 0)] h := by
    filter_upwards [self_mem_nhdsWithin] with kap hkap
    have hpos : 0 < kap := Set.mem_Ioi.mp hkap
    dsimp [gk, h]
    exact katoSmooth_le_posPart kap hpos g x
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower_tendsto h_upper_tendsto
    h_lower_eventually h_upper_eventually

end CIV
