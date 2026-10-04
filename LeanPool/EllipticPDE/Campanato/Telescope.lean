/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Campanato.Compare


/-!
# Dyadic telescoping estimate and Campanato limit

Halving the radius moves the ball mean by at most `campanatoConst d · M · r^α`, so the means at
the dyadic radii `r, r/2, r/4, …` form a Cauchy sequence with an explicit geometric bound. Summing
that geometric series and closing the gap to an arbitrary smaller radius with
`abs_ballAverage_sub_le_of_le` gives the estimate the whole characterisation rests on,

  `|u_{x,r} - u_{x,s}| ≤ campanatoLimitConst d α · M · r^α` for every `0 < s ≤ r`,

with `B(x,r) ⊆ Ω`. Since the bound does not degrade as `s → 0`, the means converge, and the limit

  `campanatoLimit u x = lim_k u_{x, 2^{-k}}`

inherits the same bound. That limit is the Hölder representative produced in
`EllipticPdes.Campanato.Holder`.
-/

@[expose] public section

open MeasureTheory Set Metric Filter

open scoped NNReal ENNReal Topology

noncomputable section

namespace EllipticPdes.Campanato

variable {d : ℕ}

/-- The geometric ratio of the dyadic ladder, `2^{-α}`. -/
private def dyadicRatio (α : ℝ) : ℝ := (1 / 2 : ℝ) ^ α

private theorem dyadicRatio_pos (α : ℝ) : 0 < dyadicRatio α :=
  Real.rpow_pos_of_pos (by norm_num) α

private theorem dyadicRatio_lt_one {α : ℝ} (hα : 0 < α) : dyadicRatio α < 1 :=
  Real.rpow_lt_one (by norm_num) (by norm_num) hα

/-- The `α`-power of a dyadically shrunken radius factorises. -/
private theorem rpow_mul_half_pow {r : ℝ} (hr : 0 < r) (α : ℝ) (k : ℕ) :
    (r * (1 / 2 : ℝ) ^ k) ^ α = r ^ α * dyadicRatio α ^ k := by
  rw [Real.mul_rpow hr.le (by positivity), dyadicRatio]
  congr 1
  rw [← Real.rpow_natCast (1 / 2 : ℝ) k, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul (by norm_num), Real.rpow_natCast]

/-- The `α`-power of the dyadic radius `2^{-k}` is the `k`-th power of the ratio `2^{-α}`. -/
private theorem half_pow_rpow (α : ℝ) (k : ℕ) :
    ((1 / 2 : ℝ) ^ k) ^ α = dyadicRatio α ^ k := by
  simpa using rpow_mul_half_pow (r := 1) one_pos α k

/-- The constant of the telescoped estimate: the geometric sum of the dyadic steps, plus one more
step to reach an arbitrary radius below the ladder. -/
def campanatoLimitConst (d : ℕ) (α : ℝ) : ℝ :=
  campanatoConst d * (1 / (1 - (1 / 2 : ℝ) ^ α) + 1)

/-- The telescoped constant is nonnegative. -/
theorem campanatoLimitConst_nonneg {α : ℝ} (hα : 0 < α) : 0 ≤ campanatoLimitConst d α := by
  have h1 : dyadicRatio α < 1 := dyadicRatio_lt_one hα
  rw [dyadicRatio] at h1
  have hden : (0 : ℝ) < 1 - (1 / 2 : ℝ) ^ α := by linarith
  exact mul_nonneg campanatoConst_nonneg
    (add_nonneg (div_pos one_pos hden).le zero_le_one)

section Telescope

variable {Ω : Set (EuclideanSpace ℝ (Fin d))} {u : EuclideanSpace ℝ (Fin d) → ℝ} {α M : ℝ}

/-- **Telescoping down the dyadic ladder.** After `k` halvings the mean has moved by at most the
partial geometric sum `campanatoConst d · M · r^α · (1 - 2^{-kα}) / (1 - 2^{-α})`. -/
private theorem abs_ballAverage_sub_dyadic (hα : 0 < α) (hM : 0 ≤ M)
    (hu : MemLp u 2 (volume.restrict Ω)) (hcamp : CampanatoOn Ω u α M)
    {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r) (hxr : Metric.ball x r ⊆ Ω) (k : ℕ) :
    |ballAverage u x r - ballAverage u x (r * (1 / 2 : ℝ) ^ k)|
      ≤ campanatoConst d * M * r ^ α
          * ((1 - dyadicRatio α ^ k) / (1 - dyadicRatio α)) := by
  have hq0 : 0 < dyadicRatio α := dyadicRatio_pos α
  have hq1 : dyadicRatio α < 1 := dyadicRatio_lt_one hα
  have hden : (0 : ℝ) < 1 - dyadicRatio α := by linarith
  induction k with
  | zero => simp
  | succ k ih =>
      have hρpos : (0 : ℝ) < r * (1 / 2 : ℝ) ^ k := by positivity
      have hρle : r * (1 / 2 : ℝ) ^ k ≤ r := by
        nth_rw 2 [← mul_one r]
        exact mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hr.le
      have hρsub : Metric.ball x (r * (1 / 2 : ℝ) ^ k) ⊆ Ω :=
        (Metric.ball_subset_ball hρle).trans hxr
      have hstep : |ballAverage u x (r * (1 / 2 : ℝ) ^ k)
            - ballAverage u x (r * (1 / 2 : ℝ) ^ (k + 1))|
          ≤ campanatoConst d * M * (r ^ α * dyadicRatio α ^ k) := by
        have heq : r * (1 / 2 : ℝ) ^ (k + 1) = r * (1 / 2 : ℝ) ^ k / 2 := by ring
        rw [heq]
        have h := abs_ballAverage_sub_half_le hα.le hM hu hcamp hρpos hρsub
        rwa [rpow_mul_half_pow hr α k] at h
      calc |ballAverage u x r - ballAverage u x (r * (1 / 2 : ℝ) ^ (k + 1))|
          ≤ |ballAverage u x r - ballAverage u x (r * (1 / 2 : ℝ) ^ k)|
              + |ballAverage u x (r * (1 / 2 : ℝ) ^ k)
                  - ballAverage u x (r * (1 / 2 : ℝ) ^ (k + 1))| := abs_sub_le _ _ _
        _ ≤ campanatoConst d * M * r ^ α * ((1 - dyadicRatio α ^ k) / (1 - dyadicRatio α))
              + campanatoConst d * M * (r ^ α * dyadicRatio α ^ k) := add_le_add ih hstep
        _ = campanatoConst d * M * r ^ α
              * ((1 - dyadicRatio α ^ (k + 1)) / (1 - dyadicRatio α)) := by
              field_simp
              ring

/-- **Telescoped estimate.** For every radius `s` below `r`, with `B(x, r) ⊆ Ω`, the two means
differ by at most `campanatoLimitConst d α · M · r^α`. The bound is uniform in `s`, which is what
makes the means converge as the radius shrinks. -/
theorem abs_ballAverage_sub_le_of_le_radius (hα : 0 < α) (hM : 0 ≤ M)
    (hu : MemLp u 2 (volume.restrict Ω)) (hcamp : CampanatoOn Ω u α M)
    {x : EuclideanSpace ℝ (Fin d)} {r s : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    (hxr : Metric.ball x r ⊆ Ω) :
    |ballAverage u x r - ballAverage u x s| ≤ campanatoLimitConst d α * M * r ^ α := by
  have hr : 0 < r := lt_of_lt_of_le hs hsr
  have hq0 : 0 < dyadicRatio α := dyadicRatio_pos α
  have hq1 : dyadicRatio α < 1 := dyadicRatio_lt_one hα
  have hden : (0 : ℝ) < 1 - dyadicRatio α := by linarith
  have hC : 0 ≤ campanatoConst d := campanatoConst_nonneg
  have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr α
  -- Locate `s` between two consecutive dyadic radii below `r`.
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, (2 : ℝ) ^ k ≤ r / s ∧ r / s < 2 ^ (k + 1) :=
    exists_nat_pow_near ((one_le_div hs).mpr hsr) one_lt_two
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hhalf : r * (1 / 2 : ℝ) ^ k = r / 2 ^ k := by
    rw [div_pow, one_pow]; ring
  rw [le_div_iff₀ hs] at hk1
  rw [div_lt_iff₀ hs] at hk2
  have hsρ : s ≤ r * (1 / 2 : ℝ) ^ k := by
    rw [hhalf, le_div_iff₀ h2k]; linarith
  have hρ2s : r * (1 / 2 : ℝ) ^ k ≤ 2 * s := by
    rw [hhalf, div_le_iff₀ h2k]
    have : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := by ring
    nlinarith
  have hρpos : (0 : ℝ) < r * (1 / 2 : ℝ) ^ k := lt_of_lt_of_le hs hsρ
  have hρle : r * (1 / 2 : ℝ) ^ k ≤ r := by
    nth_rw 2 [← mul_one r]
    exact mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hr.le
  have hρsub : Metric.ball x (r * (1 / 2 : ℝ) ^ k) ⊆ Ω :=
    (Metric.ball_subset_ball hρle).trans hxr
  -- The telescoped part, then the single comparable-radii step to reach `s`.
  have htel := abs_ballAverage_sub_dyadic hα hM hu hcamp hr hxr k
  have hcomp := abs_ballAverage_sub_le_of_le hα.le hM hu hcamp hs hsρ hρ2s hρsub
  have hqk : 0 ≤ dyadicRatio α ^ k := le_of_lt (pow_pos hq0 k)
  have htel' : |ballAverage u x r - ballAverage u x (r * (1 / 2 : ℝ) ^ k)|
      ≤ campanatoConst d * M * r ^ α * (1 / (1 - dyadicRatio α)) := by
    refine htel.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [div_le_div_iff_of_pos_right hden]
    linarith
  have hρα : (r * (1 / 2 : ℝ) ^ k) ^ α ≤ r ^ α :=
    Real.rpow_le_rpow hρpos.le hρle hα.le
  have hcomp' : |ballAverage u x (r * (1 / 2 : ℝ) ^ k) - ballAverage u x s|
      ≤ campanatoConst d * M * r ^ α :=
    hcomp.trans (mul_le_mul_of_nonneg_left hρα (by positivity))
  calc |ballAverage u x r - ballAverage u x s|
      ≤ |ballAverage u x r - ballAverage u x (r * (1 / 2 : ℝ) ^ k)|
          + |ballAverage u x (r * (1 / 2 : ℝ) ^ k) - ballAverage u x s| := abs_sub_le _ _ _
    _ ≤ campanatoConst d * M * r ^ α * (1 / (1 - dyadicRatio α))
          + campanatoConst d * M * r ^ α := add_le_add htel' hcomp'
    _ = campanatoLimitConst d α * M * r ^ α := by
        rw [campanatoLimitConst, dyadicRatio]; ring

end Telescope

/-- **Campanato limit.** The limit of the means of `u` over the balls `B(x, 2^{-k})`. Under the
Campanato hypothesis this limit exists at every point of the open set, equals `u` almost
everywhere, and is the Hölder representative. -/
def campanatoLimit (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  limUnder atTop fun k : ℕ => ballAverage u x ((1 / 2 : ℝ) ^ k)

section Limit

variable {Ω : Set (EuclideanSpace ℝ (Fin d))} {u : EuclideanSpace ℝ (Fin d) → ℝ} {α M : ℝ}

/-- The dyadic means converge at every point of the open set. -/
theorem tendsto_ballAverage_campanatoLimit (hα : 0 < α) (hM : 0 ≤ M) (hΩ : IsOpen Ω)
    (hu : MemLp u 2 (volume.restrict Ω)) (hcamp : CampanatoOn Ω u α M)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) :
    Tendsto (fun k : ℕ => ballAverage u x ((1 / 2 : ℝ) ^ k)) atTop
      (𝓝 (campanatoLimit u x)) := by
  have hC : 0 ≤ campanatoLimitConst d α := campanatoLimitConst_nonneg hα
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < ε :=
    exists_pow_lt_of_lt_one hε (by norm_num)
  have hsub : ∀ k : ℕ, N ≤ k → Metric.ball x ((1 / 2 : ℝ) ^ k) ⊆ Ω := by
    intro k hk
    refine (Metric.ball_subset_ball ?_).trans hball
    exact le_of_lt (lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk) hN)
  have hpos : ∀ k : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ k := fun k => by positivity
  -- The telescoped estimate makes the sequence Cauchy.
  have hcauchy : CauchySeq fun k : ℕ => ballAverage u x ((1 / 2 : ℝ) ^ k) := by
    refine Metric.cauchySeq_iff'.mpr fun δ hδ => ?_
    have htend : Tendsto (fun k : ℕ => campanatoLimitConst d α * M * ((1 / 2 : ℝ) ^ k) ^ α)
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun k : ℕ => ((1 / 2 : ℝ) ^ k) ^ α) atTop (𝓝 0) := by
        simp only [half_pow_rpow]
        exact tendsto_pow_atTop_nhds_zero_of_lt_one (dyadicRatio_pos α).le
          (dyadicRatio_lt_one hα)
      simpa using h0.const_mul (campanatoLimitConst d α * M)
    obtain ⟨N', hN'⟩ := Metric.tendsto_atTop.mp htend δ hδ
    refine ⟨max N N', fun n hn => ?_⟩
    have hNn : N ≤ n := le_trans (le_max_left _ _) hn
    have hNm : N ≤ max N N' := le_max_left _ _
    have hle : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ (max N N') :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    have hbound := abs_ballAverage_sub_le_of_le_radius hα hM hu hcamp (hpos n) hle
      (hsub _ hNm)
    have hδ' := hN' (max N N') (le_max_right _ _)
    rw [Real.dist_eq, sub_zero] at hδ'
    rw [Real.dist_eq]
    have habs : |campanatoLimitConst d α * M * ((1 / 2 : ℝ) ^ (max N N')) ^ α|
        = campanatoLimitConst d α * M * ((1 / 2 : ℝ) ^ (max N N')) ^ α :=
      abs_of_nonneg (by positivity)
    rw [habs] at hδ'
    calc |ballAverage u x ((1 / 2 : ℝ) ^ n) - ballAverage u x ((1 / 2 : ℝ) ^ (max N N'))|
        = |ballAverage u x ((1 / 2 : ℝ) ^ (max N N')) - ballAverage u x ((1 / 2 : ℝ) ^ n)| :=
          abs_sub_comm _ _
      _ ≤ campanatoLimitConst d α * M * ((1 / 2 : ℝ) ^ (max N N')) ^ α := hbound
      _ < δ := hδ'
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hcauchy)

/-- **Distance from the mean at any admissible radius to the limit.** This is the estimate
the Hölder bound consumes: the representative is reached from every scale at the Campanato rate. -/
theorem abs_ballAverage_sub_campanatoLimit_le (hα : 0 < α) (hM : 0 ≤ M) (hΩ : IsOpen Ω)
    (hu : MemLp u 2 (volume.restrict Ω)) (hcamp : CampanatoOn Ω u α M)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) {r : ℝ} (hr : 0 < r)
    (hxr : Metric.ball x r ⊆ Ω) :
    |ballAverage u x r - campanatoLimit u x| ≤ campanatoLimitConst d α * M * r ^ α := by
  have htend := tendsto_ballAverage_campanatoLimit hα hM hΩ hu hcamp hx
  have hlim : Tendsto (fun k : ℕ => |ballAverage u x r - ballAverage u x ((1 / 2 : ℝ) ^ k)|)
      atTop (𝓝 |ballAverage u x r - campanatoLimit u x|) :=
    (tendsto_const_nhds.sub htend).abs
  refine le_of_tendsto hlim ?_
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < r := exists_pow_lt_of_lt_one hr (by norm_num)
  filter_upwards [eventually_ge_atTop N] with k hk
  have hkr : (1 / 2 : ℝ) ^ k ≤ r :=
    le_of_lt (lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk) hN)
  exact abs_ballAverage_sub_le_of_le_radius hα hM hu hcamp (by positivity) hkr hxr

end Limit

end EllipticPdes.Campanato
