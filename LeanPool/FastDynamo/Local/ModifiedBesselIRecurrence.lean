/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.ModifiedBessel

/-!
# Modified-Bessel `I` recurrences

This module derives the order-zero, order-one, and order-two differentiation and recurrence
identities directly from the regularized hypergeometric series definitions.  The only
non-entire formulas are the quotient recurrences, whose statements explicitly assume `z ≠ 0`.
-/

@[expose] public section

namespace FastDynamo.ModifiedBessel

open Complex

/-- Closed form of the coefficients of the regularized hypergeometric function with denominator
parameter `1`, namely `1 / (n! · n!)`; this is the series underlying `I₀`. -/
private theorem coeff_one (n : ℕ) :
    regularizedHGFunCoeff 0 {(1 : ℂ)} n =
      1 / ((n.factorial : ℂ) * (n.factorial : ℂ)) := by
  simp only [regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero,
    Multiset.map_singleton, Multiset.prod_singleton]
  rw [show (1 : ℂ) + n = (n : ℂ) + 1 by ring, Gamma_nat_eq_factorial]

/-- Closed form of the coefficients of the regularized hypergeometric function
with denominator parameter `2`. -/
theorem coeff_two (n : ℕ) :
    regularizedHGFunCoeff 0 {(2 : ℂ)} n =
      1 / ((n.factorial : ℂ) * ((n + 1).factorial : ℂ)) := by
  simp only [regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero,
    Multiset.map_singleton, Multiset.prod_singleton]
  rw [show (2 : ℂ) + n = (n + 1 : ℕ) + 1 by push_cast; ring,
    Gamma_nat_eq_factorial]

/-- Closed form of the coefficients of the regularized hypergeometric function with denominator
parameter `3`, namely `1 / (n! · (n+2)!)`; this is the series underlying `I₂`. -/
private theorem coeff_three (n : ℕ) :
    regularizedHGFunCoeff 0 {(3 : ℂ)} n =
      1 / ((n.factorial : ℂ) * ((n + 2).factorial : ℂ)) := by
  simp only [regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero,
    Multiset.map_singleton, Multiset.prod_singleton]
  rw [show (3 : ℂ) + n = (n + 2 : ℕ) + 1 by push_cast; ring,
    Gamma_nat_eq_factorial]

/-- Termwise differentiation shifts the denominator parameter from `1` to `2`:
`(n+1) · c₁(n+1) = c₂(n)` for the coefficients above. -/
private theorem coeff_deriv_one (n : ℕ) :
    (n + 1) • regularizedHGFunCoeff 0 {(1 : ℂ)} (n + 1) =
      regularizedHGFunCoeff 0 {(2 : ℂ)} n := by
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  rw [coeff_one, coeff_two, Nat.factorial_succ]
  push_cast
  simp only [smul_eq_mul]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hs : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp [hn, hs]

/-- Termwise differentiation shifts the denominator parameter from `2` to `3`:
`(n+1) · c₂(n+1) = c₃(n)`. -/
private theorem coeff_deriv_two (n : ℕ) :
    (n + 1) • regularizedHGFunCoeff 0 {(2 : ℂ)} (n + 1) =
      regularizedHGFunCoeff 0 {(3 : ℂ)} n := by
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  rw [coeff_two, coeff_three, Nat.factorial_succ (n := n)]
  push_cast
  simp only [smul_eq_mul]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : ((n + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n + 1)
  have hn2 : ((n + 2).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n + 2)
  have hs : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp [hn, hn1, hn2, hs]

/-- The contiguous relation between the three coefficient families:
`c₁(n+1) - c₂(n+1) = c₃(n)`.  It is the coefficient form of the recurrence
`I₀ - I₂ = 2 I₁ / z`. -/
private theorem coeff_contiguous (n : ℕ) :
    regularizedHGFunCoeff 0 {(1 : ℂ)} (n + 1) -
        regularizedHGFunCoeff 0 {(2 : ℂ)} (n + 1) =
      regularizedHGFunCoeff 0 {(3 : ℂ)} n := by
  rw [coeff_one, coeff_two, coeff_three,
    Nat.factorial_succ (n := n), Nat.factorial_succ (n := n + 1)]
  push_cast
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : ((n + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n + 1)
  have hs1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hs2 : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  have hs2' : (2 + n : ℂ) ≠ 0 := by simpa [add_comm] using hs2
  have hs11 : (n + 1 + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (n + 1)
  have hn1' : ((1 + n).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (1 + n)
  field_simp [hn, hn1, hn1', hs1, hs2, hs2', hs11]
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- Termwise identification of the derivative series of the denominator-`1` family with the
denominator-`2` family, evaluated as a one-variable multilinear term. -/
private theorem derivSeries_one_term (n : ℕ) (x : ℂ) :
    ((regularizedHGFunSeries 0 {(1 : ℂ)}).derivSeries n (fun _ ↦ x)) 1 =
      regularizedHGFunSeries 0 {(2 : ℂ)} n (fun _ ↦ x) := by
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp only [smul_apply, FormalMultilinearSeries.derivSeries_coeff_one,
    regularizedHGFunSeries_coeff, coeff_deriv_one]

/-- Summed form of `derivSeries_one_term`: the derivative series of the denominator-`1` family
sums to the denominator-`2` function at every point of the plane. -/
private theorem derivSeries_one_sum_apply (x : ℂ) :
    ((regularizedHGFunSeries 0 {(1 : ℂ)}).derivSeries.sum x) 1 =
      (regularizedHGFunSeries 0 {(2 : ℂ)}).sum x := by
  let p := regularizedHGFunSeries 0 {(1 : ℂ)}
  have hx : x ∈ Metric.eball (0 : ℂ) p.radius := by
    dsimp [p]
    rw [I0_series_radius]
    exact edist_lt_top _ _
  have hxd : x ∈ Metric.eball (0 : ℂ) p.derivSeries.radius :=
    Metric.eball_subset_eball p.radius_le_radius_derivSeries hx
  have hs := p.derivSeries.summable hxd
  unfold FormalMultilinearSeries.sum
  change (∑' n, (p.derivSeries n (fun _ ↦ x))) 1 =
    ∑' n, regularizedHGFunSeries 0 {(2 : ℂ)} n (fun _ ↦ x)
  calc
    _ = (ContinuousLinearMap.apply ℂ ℂ 1)
        (∑' n, p.derivSeries n (fun _ ↦ x)) := rfl
    _ = ∑' n, (p.derivSeries n (fun _ ↦ x)) 1 :=
      (ContinuousLinearMap.apply ℂ ℂ 1).map_tsum hs
    _ = _ := tsum_congr fun n ↦ derivSeries_one_term n x

/-- The regularized hypergeometric function with denominator parameter `1` is differentiable
everywhere with derivative the one with denominator parameter `2`. -/
private theorem regularizedHGFun_one_hasDerivAt (x : ℂ) :
    HasDerivAt (regularizedHGFun 0 {(1 : ℂ)})
      (regularizedHGFun 0 {(2 : ℂ)} x) x := by
  unfold regularizedHGFun
  have hx : ‖x‖ₑ < (regularizedHGFunSeries 0 {(1 : ℂ)}).radius := by
    rw [I0_series_radius]
    exact enorm_lt_top
  have hd := (regularizedHGFunSeries 0 {(1 : ℂ)}).hasFDerivAt_sum hx |>.hasDerivAt
  rw [derivSeries_one_sum_apply] at hd
  exact hd

/-- Termwise identification of the derivative series of the denominator-`2` family with the
denominator-`3` family. -/
private theorem derivSeries_two_term (n : ℕ) (x : ℂ) :
    ((regularizedHGFunSeries 0 {(2 : ℂ)}).derivSeries n (fun _ ↦ x)) 1 =
      regularizedHGFunSeries 0 {(3 : ℂ)} n (fun _ ↦ x) := by
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp only [smul_apply, FormalMultilinearSeries.derivSeries_coeff_one,
    regularizedHGFunSeries_coeff, coeff_deriv_two]

/-- Summed form of `derivSeries_two_term`: the derivative series of the denominator-`2` family
sums to the denominator-`3` function at every point of the plane. -/
private theorem derivSeries_two_sum_apply (x : ℂ) :
    ((regularizedHGFunSeries 0 {(2 : ℂ)}).derivSeries.sum x) 1 =
      (regularizedHGFunSeries 0 {(3 : ℂ)}).sum x := by
  let p := regularizedHGFunSeries 0 {(2 : ℂ)}
  have hx : x ∈ Metric.eball (0 : ℂ) p.radius := by
    dsimp [p]
    rw [radius_regularizedHGFunSeries_eq_top (by simp)]
    exact edist_lt_top _ _
  have hxd : x ∈ Metric.eball (0 : ℂ) p.derivSeries.radius :=
    Metric.eball_subset_eball p.radius_le_radius_derivSeries hx
  have hs := p.derivSeries.summable hxd
  unfold FormalMultilinearSeries.sum
  change (∑' n, (p.derivSeries n (fun _ ↦ x))) 1 =
    ∑' n, regularizedHGFunSeries 0 {(3 : ℂ)} n (fun _ ↦ x)
  calc
    _ = (ContinuousLinearMap.apply ℂ ℂ 1)
        (∑' n, p.derivSeries n (fun _ ↦ x)) := rfl
    _ = ∑' n, (p.derivSeries n (fun _ ↦ x)) 1 :=
      (ContinuousLinearMap.apply ℂ ℂ 1).map_tsum hs
    _ = _ := tsum_congr fun n ↦ derivSeries_two_term n x

/-- The regularized hypergeometric function with denominator parameter `2` is differentiable
everywhere with derivative the one with denominator parameter `3`. -/
private theorem regularizedHGFun_two_hasDerivAt (x : ℂ) :
    HasDerivAt (regularizedHGFun 0 {(2 : ℂ)})
      (regularizedHGFun 0 {(3 : ℂ)} x) x := by
  unfold regularizedHGFun
  have hx : ‖x‖ₑ < (regularizedHGFunSeries 0 {(2 : ℂ)}).radius := by
    rw [radius_regularizedHGFunSeries_eq_top (by simp)]
    exact enorm_lt_top
  have hd := (regularizedHGFunSeries 0 {(2 : ℂ)}).hasFDerivAt_sum hx |>.hasDerivAt
  rw [derivSeries_two_sum_apply] at hd
  exact hd

/-- Termwise form of the contiguous relation at index `n+1`: the difference of the
denominator-`1` and denominator-`2` terms is `x` times the denominator-`3` term of index `n`. -/
private theorem contiguous_term_succ (n : ℕ) (x : ℂ) :
    regularizedHGFunSeries 0 {(1 : ℂ)} (n + 1) (fun _ ↦ x) -
        regularizedHGFunSeries 0 {(2 : ℂ)} (n + 1) (fun _ ↦ x) =
      x * regularizedHGFunSeries 0 {(3 : ℂ)} n (fun _ ↦ x) := by
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp only [regularizedHGFunSeries_coeff, smul_eq_mul]
  rw [pow_succ]
  calc
    _ = x * x ^ n *
        (regularizedHGFunCoeff 0 {(1 : ℂ)} (n + 1) -
          regularizedHGFunCoeff 0 {(2 : ℂ)} (n + 1)) := by ring
    _ = _ := by rw [coeff_contiguous]; ring

/-- The denominator-`1` and denominator-`2` series have the same constant term, so the contiguous
relation has no index-zero contribution. -/
private theorem contiguous_term_zero (x : ℂ) :
    regularizedHGFunSeries 0 {(1 : ℂ)} 0 (fun _ ↦ x) -
        regularizedHGFunSeries 0 {(2 : ℂ)} 0 (fun _ ↦ x) = 0 := by
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp [regularizedHGFunSeries_coeff, coeff_one, coeff_two]

/-- The contiguous relation in summed form:
`regularized ₀F₁(;2;x) = regularized ₀F₁(;1;x) - x · regularized ₀F₁(;3;x)`.
Substituting `x = z²/4` turns it into
`2 I₁ z / z = I₀ z - I₂ z`. -/
private theorem regularizedHGFun_two_eq_one_sub_mul_three (x : ℂ) :
    regularizedHGFun 0 {(2 : ℂ)} x =
      regularizedHGFun 0 {(1 : ℂ)} x -
        x * regularizedHGFun 0 {(3 : ℂ)} x := by
  let p1 := regularizedHGFunSeries 0 {(1 : ℂ)}
  let p2 := regularizedHGFunSeries 0 {(2 : ℂ)}
  let p3 := regularizedHGFunSeries 0 {(3 : ℂ)}
  have hmem (c : ℂ) : x ∈ Metric.eball (0 : ℂ) (regularizedHGFunSeries 0 {c}).radius := by
    rw [radius_regularizedHGFunSeries_eq_top (by simp)]
    exact edist_lt_top _ _
  have h1 : Summable (fun n ↦ p1 n (fun _ ↦ x)) := p1.summable (hmem 1)
  have h2 : Summable (fun n ↦ p2 n (fun _ ↦ x)) := p2.summable (hmem 2)
  have h3 : Summable (fun n ↦ p3 n (fun _ ↦ x)) := p3.summable (hmem 3)
  have hzero : p1 0 (fun _ ↦ x) - p2 0 (fun _ ↦ x) = 0 := by
    simpa [p1, p2] using contiguous_term_zero x
  have hdiff :
      (∑' n, p1 n (fun _ ↦ x)) - (∑' n, p2 n (fun _ ↦ x)) =
        x * ∑' n, p3 n (fun _ ↦ x) := by
    calc
      _ = ∑' n, (p1 n (fun _ ↦ x) - p2 n (fun _ ↦ x)) :=
        (h1.tsum_sub h2).symm
      _ = ∑' n, (p1 (n + 1) (fun _ ↦ x) - p2 (n + 1) (fun _ ↦ x)) := by
        have hs := (h1.sub h2).sum_add_tsum_nat_add 1
        rw [Finset.sum_range_one, hzero, zero_add] at hs
        exact hs.symm
      _ = ∑' n, x * p3 n (fun _ ↦ x) := tsum_congr fun n ↦ by
        simpa [p1, p2, p3] using contiguous_term_succ n x
      _ = _ := h3.tsum_mul_left x
  unfold regularizedHGFun FormalMultilinearSeries.sum
  dsimp [p1, p2, p3] at hdiff
  rw [← hdiff]
  ring

/-- The substitution `z ↦ z²/4` used to pass from the hypergeometric variable to the Bessel
argument has derivative `z/2`. -/
private theorem sq_div_four_hasDerivAt (z : ℂ) :
    @HasDerivAt ℂ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup
      RCLike.innerProductSpace.toModule _ _ (fun z : ℂ ↦ z ^ 2 / 4) (z / 2) z := by
  have h := ((hasDerivAt_id z).pow 2).div_const 4
  simpa only [Pi.pow_apply, id_eq] using
    h.congr_deriv (by simp only [id_eq]; ring)

/-- The standard order-zero/order-two derivative recurrence. -/
theorem I0_hasDerivAt_recurrence (z : ℂ) :
    @HasDerivAt ℂ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup
      RCLike.innerProductSpace.toModule _ _ I0 (z / 2 * (I0 z - I2 z)) z := by
  have h := (regularizedHGFun_one_hasDerivAt (z ^ 2 / 4)).comp z
    (sq_div_four_hasDerivAt z)
  rw [regularizedHGFun_two_eq_one_sub_mul_three] at h
  have heq : Filter.EventuallyEq (nhds z) I0
      (regularizedHGFun 0 {(1 : ℂ)} ∘ fun z : ℂ ↦ z ^ 2 / 4) :=
    Filter.Eventually.of_forall fun _ ↦ rfl
  apply (h.congr_of_eventuallyEq heq).congr_deriv
  simp only [I0, I2]
  ring

/-- Order-one modified Bessel function in the hypergeometric normalization used here. -/
noncomputable def I1 (z : ℂ) : ℂ :=
  (z / 2) * regularizedHGFun 0 {(2 : ℂ)} (z ^ 2 / 4)

/-- The standard order-one/order-zero/order-two recurrence. -/
theorem I1_eq_half_mul_I0_sub_I2 (z : ℂ) :
    I1 z = z / 2 * (I0 z - I2 z) := by
  unfold I1 I0 I2
  rw [regularizedHGFun_two_eq_one_sub_mul_three]

/-- The order-zero derivative is `I1`. -/
theorem I0_hasDerivAt_I1 (z : ℂ) :
    @HasDerivAt ℂ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup
      RCLike.innerProductSpace.toModule _ _ I0 (I1 z) z := by
  rw [I1_eq_half_mul_I0_sub_I2]
  exact I0_hasDerivAt_recurrence z

/-- The prefactor `z ↦ z/2` in the definition of `I₁` has derivative `1/2`. -/
private theorem div_two_hasDerivAt (z : ℂ) :
    @HasDerivAt ℂ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup
      RCLike.innerProductSpace.toModule _ _ (fun z : ℂ ↦ z / 2) (1 / 2) z := by
  have h := (hasDerivAt_id z).div_const 2
  simpa only [Pi.div_apply, id_eq] using
    h.congr_deriv (by simp)

/-- Symmetric derivative recurrence for order one. -/
theorem I1_hasDerivAt (z : ℂ) :
    @HasDerivAt ℂ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup
      RCLike.innerProductSpace.toModule _ _ I1 ((I0 z + I2 z) / 2) z := by
  have hg := (regularizedHGFun_two_hasDerivAt (z ^ 2 / 4)).comp z
    (sq_div_four_hasDerivAt z)
  have hp := (div_two_hasDerivAt z).mul hg
  have heq : Filter.EventuallyEq (nhds z) I1
      ((fun z : ℂ ↦ z / 2) *
        (regularizedHGFun 0 {(2 : ℂ)} ∘ fun z : ℂ ↦ z ^ 2 / 4)) :=
    Filter.Eventually.of_forall fun _ ↦ rfl
  apply (hp.congr_of_eventuallyEq heq).congr_deriv
  simp only [Function.comp_apply, I0, I2]
  rw [regularizedHGFun_two_eq_one_sub_mul_three]
  ring

/-- Solving the order-one recurrence for the order-two function away from the origin:
`I₂ z = I₀ z - 2 I₁ z / z`. -/
theorem I2_eq_I0_sub_two_mul_I1_div (z : ℂ) (hz : z ≠ 0) :
    I2 z = I0 z - 2 * I1 z / z := by
  rw [I1_eq_half_mul_I0_sub_I2]
  field_simp [hz]
  ring

/-- Order-two derivative recurrence away from the removable singularity at zero. -/
theorem I2_hasDerivAt_recurrence (z : ℂ) (hz : z ≠ 0) :
    @HasDerivAt ℂ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup
      RCLike.innerProductSpace.toModule _ _ I2 (I1 z - 2 * I2 z / z) z := by
  have hq := (I1_hasDerivAt z).div (hasDerivAt_id z) hz
  have h := (I0_hasDerivAt_I1 z).sub (hq.const_mul 2)
  apply (h.congr_of_eventuallyEq ?_).congr_deriv
  · simp only [id_eq]
    rw [I1_eq_half_mul_I0_sub_I2]
    field_simp [hz]
    ring
  · filter_upwards [eventually_ne_nhds hz] with w hw
    simp only [Pi.sub_apply, Pi.div_apply, id_eq]
    rw [I2_eq_I0_sub_two_mul_I1_div w hw]
    ring

/-- Derivative-value form of `I2_hasDerivAt_recurrence` away from the origin:
`I₂' z = I₁ z - 2 I₂ z / z`. -/
theorem deriv_I2 (z : ℂ) (hz : z ≠ 0) :
    deriv I2 z = I1 z - 2 * I2 z / z :=
  (I2_hasDerivAt_recurrence z hz).deriv

end FastDynamo.ModifiedBessel
