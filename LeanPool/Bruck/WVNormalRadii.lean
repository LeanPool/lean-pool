/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.WVEntireGrowth
public import LeanPool.Bruck.WVThresholdGrowth

-- Adapted from QuanyuTang/three-im-one-cm-formalization (Apache-2.0).

/-! # Actual good logarithmic radii for a non-polynomial entire function -/

@[expose] public section

open Set Filter MeasureTheory Topology

namespace Bruck

theorem wv_exists_ge_outside_finite_volume {E : Set ℝ} (hE : volume E < ⊤) (R : ℝ) :
    ∃ x : ℝ, R ≤ x ∧ x ∉ E := by
  by_contra hh
  push Not at hh
  have hsub : Ici R ⊆ E := fun x hx => hh x hx
  have hbad := (measure_mono hsub).trans_lt hE
  rw [Real.volume_Ici] at hbad
  exact lt_irrefl _ hbad

theorem wvLogMaximum_tendsto_atTop {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (h : WVNonPolynomial H) : Tendsto (wvLogMaximum H) atTop atTop := by
  obtain ⟨C, hC⟩ := wvLogMaximum_superlinear hH h 1
  apply tendsto_atTop_mono' atTop _ (tendsto_atTop_add_const_right _ C tendsto_id)
  filter_upwards [eventually_ge_atTop 0] with x hx
  simpa only [one_mul, id_eq] using hC x hx

theorem wv_grid_slope_product_lower {η ν : ℝ} (hη : 0 < η) (k : ℕ)
    (hν : (η * ((k : ℝ) + 1)) ^ 3 ≤ ν) :
    η * ((k : ℝ) + 1) / 4 ≤ ν * wvGridWidth η (k + 1) := by
  let s : ℝ := (k : ℝ) + 1
  have hs : 1 ≤ s := by
    dsimp only [s]
    linarith [show (0 : ℝ) ≤ (k : ℝ) by exact_mod_cast (Nat.zero_le k)]
  have hp : s * (s + 1) ^ 2 ≤ 4 * s ^ 3 := by
    have hh := mul_nonneg (mul_nonneg (by linarith : 0 ≤ s) (by linarith : 0 ≤ s - 1))
      (by linarith : 0 ≤ 3 * s + 1)
    nlinarith
  rw [wvGridWidth, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two, mul_one_div,
    le_div_iff₀ (by positivity : 0 < η ^ 2 * ((k : ℝ) + 2) ^ 2)]
  change η * s / 4 * (η ^ 2 * ((k : ℝ) + 2) ^ 2) ≤ ν
  rw [show (k : ℝ) + 2 = s + 1 by dsimp only [s]; ring]
  calc
    _ = (η ^ 3 / 4) * (s * (s + 1) ^ 2) := by ring
    _ ≤ (η ^ 3 / 4) * (4 * s ^ 3) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (η * s) ^ 3 := by ring
    _ ≤ ν := hν

theorem wv_convex_slope_le_square_off_exception {A : ℝ → ℝ}
    (hA : ConvexOn ℝ univ A) (hmono : Monotone A) {x : ℝ}
    (hx : 2 ≤ x) (hlarge : 216 ≤ A x) (hout : x ∉ wvCubicException A 1) :
    wvRightSlope A x ≤ (A x) ^ 2 := by
  obtain ⟨k, hlo, hhi⟩ := wv_cubic_grid_exists (η := 1) (by norm_num)
    (by norm_num; linarith : (1 : ℝ) ^ 3 ≤ A x)
  simp only [one_mul] at hlo hhi
  let s : ℝ := (k : ℝ) + 1
  have hk : 5 ≤ k := by
    by_contra hh
    have hk4 : k ≤ 4 := by omega
    have hp : ((k : ℝ) + 2) ^ 3 ≤ (6 : ℝ) ^ 3 := by
      gcongr
      exact_mod_cast (show k + 2 ≤ 6 by omega)
    norm_num at hp
    linarith
  have hs : 6 ≤ s := by dsimp only [s]; exact_mod_cast (show 6 ≤ k + 1 by omega)
  let ρ := wvGridWidth 1 (k + 1)
  have hρ : 0 < ρ := wvGridWidth_pos (by norm_num) _
  have hρ1 : ρ ≤ 1 := by
    dsimp only [ρ, wvGridWidth]
    norm_num only [one_pow, one_mul, Nat.cast_add, Nat.cast_one]
    rw [div_le_iff₀ (by positivity : 0 < ((k : ℝ) + 1 + 1) ^ 2)]
    nlinarith [show (0 : ℝ) ≤ (k : ℝ) by exact_mod_cast (Nat.zero_le k)]
  have hdelta := wv_cubic_grid_slope_bound (hmono.monotoneOn (Ici 1)) (by norm_num) hout k
    (by simpa only [one_mul] using hlo) (by simpa only [one_mul] using hhi)
    (by linarith : 1 ≤ x - ρ) (t := ρ) (by rw [abs_of_pos hρ])
  have hder := hA.rightDeriv_le_slope_of_mem_interior (by simp : x ∈ interior (univ : Set ℝ))
    (mem_univ (x + ρ)) (by linarith : x < x + ρ)
  rw [slope_def_field, show x + ρ - x = ρ by ring, le_div_iff₀ hρ] at hder
  have hupp : wvRightSlope A x * ρ ≤ (s + 1) ^ 3 - s ^ 3 := by
    have hh := (abs_le.mp hdelta).2
    simp only [one_mul] at hh
    dsimp only [wvRightSlope]
    change derivWithin A (Ioi x) x * ρ ≤ _
    nlinarith
  have hbound : wvRightSlope A x ≤ ((s + 1) ^ 3 - s ^ 3) * (s + 1) ^ 2 := by
    apply (le_div_iff₀ hρ).mpr at hupp
    convert hupp using 1
    dsimp only [ρ, wvGridWidth]
    norm_num only [one_pow, one_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    dsimp only [s]
    ring
  have hdiff : (s + 1) ^ 3 - s ^ 3 ≤ 7 * s ^ 2 := by nlinarith
  have hsquare : (s + 1) ^ 2 ≤ 4 * s ^ 2 := by nlinarith
  calc
    wvRightSlope A x ≤ ((s + 1) ^ 3 - s ^ 3) * (s + 1) ^ 2 := hbound
    _ ≤ (7 * s ^ 2) * (4 * s ^ 2) :=
      mul_le_mul hdiff hsquare (sq_nonneg _) (by positivity)
    _ = 28 * s ^ 4 := by ring
    _ ≤ s ^ 2 * s ^ 4 := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = (s ^ 3) ^ 2 := by ring
    _ ≤ (A x) ^ 2 := pow_le_pow_left₀ (by positivity) hlo 2

theorem wv_good_log_radius {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (h : WVNonPolynomial H) {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B) (R : ℝ) :
    ∃ (x : ℝ) (k : ℕ), R ≤ x ∧ 2 ≤ x ∧ 216 ≤ wvLogMaximum H x ∧
      0 < wvGridWidth η (k + 1) ∧ wvGridWidth η (k + 1) ≤ 1 ∧
      B ≤ wvLogSlope H x ∧ B ≤ wvLogSlope H x * wvGridWidth η (k + 1) ∧
      wvLogSlope H x ≤ wvLogMaximum H x ^ 2 ∧
      ∀ t : ℝ, |t| ≤ wvGridWidth η (k + 1) →
        |wvLogMaximum H (x + t) - wvLogMaximum H x - wvLogSlope H x * t| ≤ 7 * η := by
  let A := wvLogMaximum H
  let L := wvLogSlope H
  have hconv : ConvexOn ℝ univ A := wvLogMaximum_convex hH h.exists_nonzero
  have hm : Monotone A := wvLogMaximum_monotone hH h.exists_nonzero
  obtain ⟨K, hK⟩ := exists_nat_gt (4 * B / η)
  have hKη : 4 * B < η * ((K : ℝ) + 1) := by
    have hh := (div_lt_iff₀ hη).mp hK
    nlinarith
  have hevent : ∀ᶠ x in atTop,
      216 ≤ A x ∧ (η * ((K : ℝ) + 2)) ^ 3 ≤ L x :=
    ((wvLogMaximum_tendsto_atTop hH h).eventually (eventually_ge_atTop 216)).and
      ((wvLogSlope_tendsto_atTop hH h).eventually (eventually_ge_atTop _))
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hevent
  let E := wvCubicException L η ∪ wvCubicException A 1
  have hE : volume E < ⊤ := (measure_union_le _ _).trans_lt
    (ENNReal.add_lt_top.mpr ⟨(wvCubicException_finite_volume L hη).2,
      (wvCubicException_finite_volume A (by norm_num)).2⟩)
  obtain ⟨x, hx, hxE⟩ := wv_exists_ge_outside_finite_volume hE (max R (max R₀ 2))
  have hxR : R ≤ x := (le_max_left _ _).trans hx
  have hxR₀ : R₀ ≤ x := (le_max_left R₀ 2).trans ((le_max_right _ _).trans hx)
  have hx2 : 2 ≤ x := (le_max_right R₀ 2).trans ((le_max_right _ _).trans hx)
  obtain ⟨hAx, hLx⟩ := hR₀ x hxR₀
  have hηcube : η ^ 3 ≤ L x := by
    apply le_trans _ hLx
    gcongr
    have hKn : 0 ≤ (K : ℝ) := Nat.cast_nonneg _
    nlinarith
  obtain ⟨k, hlo, hhi⟩ := wv_cubic_grid_exists hη hηcube
  have hKk : K < k := by
    by_contra hh
    have hkK : k ≤ K := le_of_not_gt hh
    have hupper : (η * ((k : ℝ) + 2)) ^ 3 ≤ (η * ((K : ℝ) + 2)) ^ 3 := by
      gcongr
    linarith
  have hbase : 4 * B ≤ η * ((k : ℝ) + 1) := hKη.le.trans (by
    apply mul_le_mul_of_nonneg_left _ hη.le
    exact_mod_cast (Nat.add_le_add_right hKk.le 1))
  let ρ := wvGridWidth η (k + 1)
  have hρ : 0 < ρ := wvGridWidth_pos hη _
  have hρ1 : ρ ≤ 1 := by
    dsimp only [ρ, wvGridWidth]
    have hh : 1 ≤ η * ((k : ℝ) + 2) := by linarith
    rw [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two,
      div_le_iff₀ (by positivity : 0 < η ^ 2 * ((k : ℝ) + 2) ^ 2)]
    nlinarith [sq_nonneg (η * ((k : ℝ) + 2) - 1)]
  have hprod : B ≤ L x * ρ := (by linarith : B ≤ η * ((k : ℝ) + 1) / 4).trans
    (wv_grid_slope_product_lower hη k hlo)
  have hL0 : 0 ≤ L x := by
    have hp : 0 ≤ (η * ((k : ℝ) + 1)) ^ 3 := by positivity
    exact hp.trans hlo
  have hLB : B ≤ L x := hprod.trans (mul_le_of_le_one_right hL0 hρ1)
  have houtL : x ∉ wvCubicException L η := fun hh => hxE (Or.inl hh)
  have houtA : x ∉ wvCubicException A 1 := fun hh => hxE (Or.inr hh)
  refine ⟨x, k, hxR, hx2, hAx, hρ, hρ1, hLB, hprod,
    wv_convex_slope_le_square_off_exception hconv hm hx2 hAx houtA, ?_⟩
  intro t ht
  exact wv_cubic_grid_affine_error hconv hη houtL k hlo hhi (by linarith) ht

end Bruck
