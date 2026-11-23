/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.WVConvexGrowth

-- Adapted from QuanyuTang/three-im-one-cm-formalization (Apache-2.0).

/-!
# Cubic grids for the logarithmic slope

The grid spacing is adjustable. Its exceptional neighborhoods have widths
proportional to `(n+1)⁻²`, so each fixed spacing has finite exceptional measure.
Only sequential good radii will be needed; no common exceptional set for all
error tolerances is assumed.
-/

@[expose] public section

open Set Filter MeasureTheory Topology

namespace Bruck

/-- The half-width of the exceptional interval around the `n`th grid crossing. -/
noncomputable def wvGridWidth (η : ℝ) (n : ℕ) : ℝ :=
  1 / (η ^ 2 * ((n : ℝ) + 1) ^ 2)

/-- The union of neighborhoods of the crossings of a cubic slope grid. -/
noncomputable def wvCubicException (L : ℝ → ℝ) (η : ℝ) : Set ℝ :=
  ⋃ n : ℕ,
    Icc (wvThreshold L ((η * ((n : ℝ) + 1)) ^ 3) - wvGridWidth η n)
      (wvThreshold L ((η * ((n : ℝ) + 1)) ^ 3) + wvGridWidth η n)

theorem wvGridWidth_pos {η : ℝ} (hη : 0 < η) (n : ℕ) : 0 < wvGridWidth η n := by
  unfold wvGridWidth
  positivity

theorem wvGridWidth_summable (η : ℝ) : Summable (wvGridWidth η) := by
  have hh := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  have heq : wvGridWidth η =
      fun n : ℕ => (η ^ 2)⁻¹ * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    funext n
    simp only [wvGridWidth, Nat.cast_add, Nat.cast_one, one_div, mul_inv_rev]
    ring
  rw [heq]
  exact hh.mul_left _

theorem wvCubicException_finite_volume (L : ℝ → ℝ) (η : ℝ) :
    MeasurableSet (wvCubicException L η) ∧ volume (wvCubicException L η) < ⊤ := by
  exact wv_threshold_intervals_finite_volume (wvGridWidth_summable η)

theorem wvGridWidth_antitone {η : ℝ} (hη : 0 < η) : Antitone (wvGridWidth η) := by
  intro m n hmn
  unfold wvGridWidth
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

theorem wv_cubic_grid_exists {η v : ℝ} (hη : 0 < η) (hv : η ^ 3 ≤ v) :
    ∃ k : ℕ, (η * ((k : ℝ) + 1)) ^ 3 ≤ v ∧ v < (η * ((k : ℝ) + 2)) ^ 3 := by
  have hex : ∃ n : ℕ, v < (η * ((n : ℝ) + 1)) ^ 3 := by
    obtain ⟨n, hn⟩ := exists_nat_gt (max 1 v / η)
    have hh : max 1 v < η * (n : ℝ) := by
      have ht := (div_lt_iff₀ hη).mp hn
      nlinarith
    have hlarge : 1 < η * ((n : ℝ) + 1) := by linarith [le_max_left 1 v]
    have hbound : v < η * ((n : ℝ) + 1) := by linarith [le_max_right 1 v]
    refine ⟨n, hbound.trans_le ?_⟩
    nlinarith [sq_nonneg (η * ((n : ℝ) + 1) - 1)]
  classical
  let n := Nat.find hex
  have hn : n ≠ 0 := by
    intro h0
    have hh := Nat.find_spec hex
    change v < (η * ((n : ℝ) + 1)) ^ 3 at hh
    rw [h0] at hh
    norm_num at hh
    linarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  refine ⟨k, ?_, ?_⟩
  · have hh := Nat.find_min hex (m := k) (by change k < n; omega)
    push Not at hh
    exact hh
  · have hh := Nat.find_spec hex
    change v < (η * ((n : ℝ) + 1)) ^ 3 at hh
    simpa only [hk, Nat.cast_succ, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using hh

theorem wv_cubic_grid_slope_bound {L : ℝ → ℝ} (hL : MonotoneOn L (Ici 1))
    {η x : ℝ} (hη : 0 < η) (hout : x ∉ wvCubicException L η)
    (k : ℕ) (hlo : (η * ((k : ℝ) + 1)) ^ 3 ≤ L x)
    (hhi : L x < (η * ((k : ℝ) + 2)) ^ 3)
    (hx : 1 ≤ x - wvGridWidth η (k + 1))
    {t : ℝ} (ht : |t| ≤ wvGridWidth η (k + 1)) :
    |L (x + t) - L x| ≤
      (η * ((k : ℝ) + 2)) ^ 3 - (η * ((k : ℝ) + 1)) ^ 3 := by
  let ρ := wvGridWidth η (k + 1)
  have hρ : 0 < ρ := wvGridWidth_pos hη _
  have houtk : x ∉ Icc
      (wvThreshold L ((η * ((k : ℝ) + 1)) ^ 3) - wvGridWidth η k)
      (wvThreshold L ((η * ((k : ℝ) + 1)) ^ 3) + wvGridWidth η k) := by
    intro hh
    exact hout (mem_iUnion.mpr ⟨k, hh⟩)
  have houtk1 : x ∉ Icc
      (wvThreshold L ((η * ((k : ℝ) + 2)) ^ 3) - ρ)
      (wvThreshold L ((η * ((k : ℝ) + 2)) ^ 3) + ρ) := by
    intro hh
    apply hout
    apply mem_iUnion.mpr
    refine ⟨k + 1, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hh
  have hleft := (wv_threshold_no_crossing hL hx hρ.le
    (wvGridWidth_antitone hη (Nat.le_succ k)) houtk).1 hlo
  have hright := (wv_threshold_no_crossing hL hx hρ.le le_rfl houtk1).2 hhi
  have hy : 1 ≤ x + t := by linarith [(abs_le.mp ht).1]
  have hmin : x - ρ ≤ x + t := by linarith [(abs_le.mp ht).1]
  have hmax : x + t ≤ x + ρ := by linarith [(abs_le.mp ht).2]
  have hlow := hleft.trans (hL hx hy hmin)
  have hupp := (hL hy (by linarith : 1 ≤ x + ρ) hmax).trans_lt hright
  apply abs_le.mpr
  constructor <;> linarith

theorem wv_cubic_grid_affine_error {A : ℝ → ℝ} (hA : ConvexOn ℝ univ A)
    {η x : ℝ} (hη : 0 < η) (hout : x ∉ wvCubicException (wvRightSlope A) η)
    (k : ℕ) (hlo : (η * ((k : ℝ) + 1)) ^ 3 ≤ wvRightSlope A x)
    (hhi : wvRightSlope A x < (η * ((k : ℝ) + 2)) ^ 3)
    (hx : 1 ≤ x - wvGridWidth η (k + 1))
    {t : ℝ} (ht : |t| ≤ wvGridWidth η (k + 1)) :
    |A (x + t) - A x - wvRightSlope A x * t| ≤ 7 * η := by
  have hL : MonotoneOn (wvRightSlope A) (Ici 1) := by
    have hh := hA.monotoneOn_rightDeriv
    exact hh.mono (by simp)
  have hsl := wv_cubic_grid_slope_bound hL hη hout k hlo hhi hx ht
  have hK : 0 ≤ (η * ((k : ℝ) + 2)) ^ 3 - (η * ((k : ℝ) + 1)) ^ 3 := by linarith
  have he := wv_convex_affine_error hA
    (x := x) (y := x + t) (by simpa only [add_sub_cancel_left] using ht) hK hsl
  simp only [add_sub_cancel_left] at he
  apply he.trans
  rw [wvGridWidth, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two,
    mul_one_div, div_le_iff₀ (by positivity : 0 < η ^ 2 * ((k : ℝ) + 2) ^ 2)]
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hp : 0 ≤ 4 * (k : ℝ) ^ 2 + 19 * (k : ℝ) + 21 := by positivity
  have hh := mul_nonneg (pow_nonneg hη.le 3) hp
  nlinarith

end Bruck
