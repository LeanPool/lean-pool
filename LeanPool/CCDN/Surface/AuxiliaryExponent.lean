/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Statements
import LeanPool.CCDN.ForMathlib.Log

/-! The numerical component of the corrected surface estimate. The auxiliary
 degree contributes a further factor d to the intersection degree, giving d^18
 after taking fourth powers. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- For `d ≥ 16`, the exponent `1 / √d` is at most `1 / 4`. -/
lemma surface_inverse_sqrt_le_quarter {d : ℕ} (hd : 16 ≤ d) :
    1 / Real.sqrt (d : ℝ) ≤ (1 / 4 : ℝ) := by
  have hs : (4 : ℝ) ≤ Real.sqrt (d : ℝ) :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast hd)
  exact one_div_le_one_div_of_le (by norm_num) hs

/-- The large-component fourth moment has exactly the corrected degree
 factor d^18, uniformly for every surface degree at least sixteen. -/
private theorem surface_degree_budget_fourth {d : ℕ} (hd : 16 ≤ d)
    {C B D : ℝ} (_hC : 0 ≤ C) (hB : 1 ≤ B) (hD0 : 0 ≤ D)
    (hD : D ≤ C * (d : ℝ) ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt d)) :
    D ^ 4 ≤ C ^ 4 * (d : ℝ) ^ 18 * B := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hB0 : 0 < B := by linarith
  have hpow := pow_le_pow_left₀ hD0 hD 4
  rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hd0.le (9 / 2 : ℝ) 4,
    ← Real.rpow_mul_natCast hB0.le (1 / Real.sqrt d) 4] at hpow
  norm_num only [show (9 / 2 : ℝ) * (4 : ℕ) = 18 by norm_num, Real.rpow_ofNat] at hpow
  have hexp : (1 / Real.sqrt (d : ℝ)) * (4 : ℕ) ≤ (1 : ℝ) := by
    have hh := surface_inverse_sqrt_le_quarter hd
    norm_num only [Nat.cast_ofNat]
    linarith
  have hbox : B ^ ((1 / Real.sqrt (d : ℝ)) * (4 : ℕ)) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB hexp
  exact hpow.trans (mul_le_mul_of_nonneg_left hbox (by positivity))

private lemma small_degree_rpow_weight {δ : ℕ} (hδ : 2 ≤ δ) {B : ℝ}
    (hB : 1 ≤ B) (hδB : (δ : ℝ) ≤ Real.log B) :
    (δ : ℝ) ^ 3 * B ^ (1 / (δ : ℝ)) ≤
      (48 * Real.exp 1) * B ^ (1 / 2 : ℝ) := by
  have hδ2 : (2 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hB0 : 0 < B := by linarith
  have hpoly : (δ : ℝ) ^ 3 ≤ 48 * Real.exp ((δ : ℝ) / 2) := by
    have hh := Real.pow_div_factorial_le_exp ((δ : ℝ) / 2)
      (show 0 ≤ (δ : ℝ) / 2 by positivity) 3
    norm_num at hh
    nlinarith
  have hexp : (δ : ℝ) / 2 + Real.log B / δ ≤ 1 + Real.log B / 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hδB) (sub_nonneg.mpr hδ2)
    have hc := div_mul_cancel₀ (Real.log B) hδ0.ne'
    nlinarith
  calc
    _ ≤ (48 * Real.exp ((δ : ℝ) / 2)) * B ^ (1 / (δ : ℝ)) :=
      mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = 48 * Real.exp ((δ : ℝ) / 2 + Real.log B / δ) := by
      rw [Real.rpow_def_of_pos hB0, Real.exp_add, mul_assoc]
      congr 2
      congr 1
      ring
    _ ≤ 48 * Real.exp (1 + Real.log B / 2) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)
    _ = _ := by
      rw [Real.exp_add, Real.rpow_def_of_pos hB0, mul_assoc]
      congr 2
      congr 1
      ring

/-- For curve degrees between two and log B, the degree factors can be
 absorbed uniformly into a square-root box bound. -/
private theorem curveBound_small_degree_uniform {δ : ℕ} (hδ : 2 ≤ δ) {B : ℝ}
    (hB : 1 ≤ B) (hδB : (δ : ℝ) ≤ Real.log B) :
    curveBound δ B ≤ (96 * Real.exp 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1) := by
  have hlog := Real.log_nonneg hB
  have hh := mul_le_mul (small_degree_rpow_weight hδ hB hδB)
    (show Real.log B + δ ≤ 2 * (Real.log B + 1) by linarith)
    (show 0 ≤ Real.log B + δ by positivity) (by positivity)
  unfold curveBound
  convert hh using 1
  ring

/-- The logarithm in the total contribution of the small-degree components
 costs only a quarter power of the box size. -/
private lemma surface_small_component_weight {d : ℕ} (hd : 16 ≤ d)
    {B : ℝ} (hB : 1 ≤ B) :
    B ^ (1 / Real.sqrt (d : ℝ)) *
        (B ^ (1 / 2 : ℝ) * (Real.log B + 1)) ≤ 5 * B := by
  have hB0 : 0 < B := by linarith
  have hlog : B ^ (1 / 2 : ℝ) * (Real.log B + 1) ≤
      5 * B ^ (3 / 4 : ℝ) := by
    have hh := Real.rpow_half_mul_log_add_le (ε := (1 / 4 : ℝ)) (D := 1)
      hB (by norm_num) (by norm_num)
    norm_num at hh ⊢
    exact hh
  have hexp : 1 / Real.sqrt (d : ℝ) + (3 / 4 : ℝ) ≤ 1 := by
    have := surface_inverse_sqrt_le_quarter hd
    linarith
  calc
    _ ≤ B ^ (1 / Real.sqrt (d : ℝ)) * (5 * B ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 5 * B ^ (1 / Real.sqrt (d : ℝ) + (3 / 4 : ℝ)) := by
      rw [Real.rpow_add hB0]
      ring
    _ ≤ 5 * B := by
      simpa only [Real.rpow_one] using
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hB hexp)
          (show (0 : ℝ) ≤ 5 by norm_num)

/-- A component count bounded by the intersection degree has uniformly
 bounded small-degree contribution, with the same d^18 factor. -/
private theorem surface_degree_budget_small_components {d : ℕ} (hd : 16 ≤ d)
    {C B D : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B)
    (hD : D ≤ C * (d : ℝ) ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt d)) :
    D * ((96 * Real.exp 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1)) ≤
      (480 * Real.exp 1) * C * (d : ℝ) ^ 18 * B := by
  have hB0 : 0 < B := by linarith
  have hlog := Real.log_nonneg hB
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hdp : (d : ℝ) ^ (9 / 2 : ℝ) ≤ (d : ℝ) ^ 18 := by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_le hd1 (show (9 / 2 : ℝ) ≤ 18 by norm_num)
  calc
    _ ≤ (C * (d : ℝ) ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt d)) *
        ((96 * Real.exp 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1)) :=
      mul_le_mul_of_nonneg_right hD (by positivity)
    _ = (96 * Real.exp 1) * C * (d : ℝ) ^ (9 / 2 : ℝ) *
        (B ^ (1 / Real.sqrt d) * (B ^ (1 / 2 : ℝ) * (Real.log B + 1))) := by ring
    _ ≤ (96 * Real.exp 1) * C * (d : ℝ) ^ (9 / 2 : ℝ) * (5 * B) :=
      mul_le_mul_of_nonneg_left (surface_small_component_weight hd hB) (by positivity)
    _ = (480 * Real.exp 1) * C * (d : ℝ) ^ (9 / 2 : ℝ) * B := by ring
    _ ≤ _ := by gcongr

/-- The sum of fourth powers of nonnegative component degrees is bounded
 by the fourth power of their total degree. -/
private lemma sum_fourth_powers_le_fourth_power_sum {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∑ i ∈ s, (a i) ^ 4 ≤ (∑ i ∈ s, a i) ^ 4 := by
  calc
    _ = ∑ i ∈ s, a i * (a i) ^ 3 := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ s, a i * (∑ j ∈ s, a j) ^ 3 := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (ha i hi)
      exact pow_le_pow_left₀ (ha i hi) (Finset.single_le_sum ha hi) 3
    _ = (∑ i ∈ s, a i) ^ 4 := by rw [← Finset.sum_mul]; ring

/-- Above the logarithmic degree threshold, the curve bound is controlled
 by the fourth power of the curve degree. -/
private theorem curveBound_large_degree {δ : ℕ} (hδ : 0 < δ) {B : ℝ}
    (hB : 1 ≤ B) (hBδ : Real.log B ≤ (δ : ℝ)) :
    curveBound δ B ≤ (2 * Real.exp 1) * (δ : ℝ) ^ 4 := by
  have hδ0 : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hB0 : 0 < B := by linarith
  have hlog := Real.log_nonneg hB
  have hpow : B ^ (1 / (δ : ℝ)) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hB0]
    apply Real.exp_le_exp.mpr
    simpa only [mul_one_div] using (div_le_one hδ0).mpr hBδ
  have hh := mul_le_mul
    (mul_le_mul_of_nonneg_left hpow (show 0 ≤ (δ : ℝ) ^ 3 by positivity))
    (show Real.log B + δ ≤ 2 * δ by linarith)
    (show 0 ≤ Real.log B + δ by positivity)
    (show 0 ≤ (δ : ℝ) ^ 3 * Real.exp 1 by positivity)
  unfold curveBound
  convert hh using 1
  ring

/-- Both degree ranges can be summed using their common total-degree
 budget. Every component here has degree at least two. -/
private theorem sum_curveBound_le_degree_budget {ι : Type*} (s : Finset ι) (δ : ι → ℕ)
    {B D : ℝ} (hB : 1 ≤ B) (hδ : ∀ i ∈ s, 2 ≤ δ i)
    (hD : (∑ i ∈ s, (δ i : ℝ)) ≤ D) :
    ∑ i ∈ s, curveBound (δ i) B ≤
      D * ((96 * Real.exp 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1)) +
        (2 * Real.exp 1) * D ^ 4 := by
  let U := (96 * Real.exp 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1)
  have hlog := Real.log_nonneg hB
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hS : 0 ≤ ∑ i ∈ s, (δ i : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  have hpoint : ∀ i ∈ s, curveBound (δ i) B ≤
      (δ i : ℝ) * U + (2 * Real.exp 1) * (δ i : ℝ) ^ 4 := by
    intro i hi
    by_cases hsmall : (δ i : ℝ) ≤ Real.log B
    · have hc := curveBound_small_degree_uniform (hδ i hi) hB hsmall
      have hd1 : (1 : ℝ) ≤ δ i := by exact_mod_cast (show 1 ≤ δ i by have := hδ i hi; omega)
      have hu : U ≤ (δ i : ℝ) * U := by simpa using mul_le_mul_of_nonneg_right hd1 hU
      have hp : 0 ≤ (2 * Real.exp 1) * (δ i : ℝ) ^ 4 := by positivity
      exact hc.trans (hu.trans (le_add_of_nonneg_right hp))
    · have hc := curveBound_large_degree (show 0 < δ i by have := hδ i hi; omega)
        hB (le_of_lt (lt_of_not_ge hsmall))
      exact hc.trans (le_add_of_nonneg_left (by positivity))
  calc
    _ ≤ ∑ i ∈ s, ((δ i : ℝ) * U + (2 * Real.exp 1) * (δ i : ℝ) ^ 4) :=
      Finset.sum_le_sum hpoint
    _ = (∑ i ∈ s, (δ i : ℝ)) * U +
        (2 * Real.exp 1) * ∑ i ∈ s, (δ i : ℝ) ^ 4 := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ ≤ D * U + (2 * Real.exp 1) * D ^ 4 := by
      apply add_le_add (mul_le_mul_of_nonneg_right hD hU)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (sum_fourth_powers_le_fourth_power_sum s (fun i => (δ i : ℝ))
        (fun _ _ => by positivity)).trans (pow_le_pow_left₀ hS hD 4)

/-- The whole numerical contribution of the nonlinear curve components in
 the surface argument, with the corrected d^18 factor. -/
theorem sum_curveBound_le_surface_degree_budget {ι : Type*}
    (s : Finset ι) (δ : ι → ℕ) {d : ℕ} (hd : 16 ≤ d)
    {B C : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) (hδ : ∀ i ∈ s, 2 ≤ δ i)
    (hD : (∑ i ∈ s, (δ i : ℝ)) ≤
      C * (d : ℝ) ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt d)) :
    ∑ i ∈ s, curveBound (δ i) B ≤
      Real.exp 1 * (480 * C + 2 * C ^ 4) * (d : ℝ) ^ 18 * B := by
  have hS : 0 ≤ ∑ i ∈ s, (δ i : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  have hsplit := sum_curveBound_le_degree_budget s δ hB hδ (le_refl _)
  have hsmall := surface_degree_budget_small_components hd hC hB hD
  have hlarge := mul_le_mul_of_nonneg_left
    (surface_degree_budget_fourth hd hC hB hS hD)
    (show 0 ≤ 2 * Real.exp 1 by positivity)
  calc
    _ ≤ _ := hsplit
    _ ≤ (480 * Real.exp 1) * C * (d : ℝ) ^ 18 * B +
        (2 * Real.exp 1) * (C ^ 4 * (d : ℝ) ^ 18 * B) := add_le_add hsmall hlarge
    _ = _ := by ring

end
end CCDN
