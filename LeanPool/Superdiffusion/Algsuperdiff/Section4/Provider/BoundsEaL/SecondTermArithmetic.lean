/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# SecondTermArithmetic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 5's second summand: the scalar arithmetic

Everything below is abstract-real arithmetic: no model, no measure, no carrier occurs.

## What is here

The four scalar facts Step 5's per-cube evaluation needs, and that the proved
layer does not already carry.

1. **A power against a decaying exponential.**  `x^n e^{-x} ≤ n!`, hence `y^n
   e^{-aγ^{-1}} ≤ n!/a^n` whenever `0 ≤ y ≤ γ^{-1}`.  This is what makes the
   printed `q²e^{-C^{-1}γ^{-1}}` of bullet (B4) and the printed
   `q³e^{-C^{-1}γ^{-1}}` of bullet (B5) bounded on the anchor's own `p`-range `p
   ≤ C^{-1}γ^{-1}s` (which gives `q ≤ γ^{-1}`): the `γ`-power the moment
   conversion spends is paid by the exponential, with no `p`-restriction.

2. **The `γ^{3/5}|log γ|²` portion of bullet (B2), squared.** `(γ^{3/5}|log
   γ|²)² ≤ 160000 γ`.  The square is essential: `γ^{3/5}|log γ|²` itself is NOT
   `O(γ)`, but `(B2)` is a squared display, and after squaring the `|log
   γ|`-power is beaten by `γ^{1/5}`.  The scale-free ingredient is
   `γ^{1/10}(log γ)² ≤ 400`.

3. **The `min`-square split.**  `(min{1, a+b})² ≤ 2a + 2b²` for `a, b ≥ 0`.
   Applied at `a = γ(t+2)`, `b = γ^{3/5}|log γ|²` this converts bullet (B2)'s
   squared minimum into the linear and flat per-scale shapes of
   `MinkowskiProviderFinal.minkowskiScaleMajorant`, at both branches of the
   minimum at once.

Also here: `(1 − 3^{γ−1})^{-1} ≤ 3` at `γ ≤ 1/2`, the uniformizer that turns the
`γ`-dependent geometric constants of `GradBottomLayer`/`GradSlotMoment` into
dimensional ones.

## References

* ABK26, `l.bounds.mathcal.E.aL`, Step 4 bullets (B2)/(B4)/(B5)/(B6b), Step 5.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

noncomputable section

/-! ## 1. A power against a decaying exponential -/

/-- **`x^n e^{-x} ≤ n!`** for `x ≥ 0`: the single term `x^n/n!` of the
exponential series is at most the whole series. -/
theorem pow_mul_exp_neg_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ n * Real.exp (-x) ≤ (Nat.factorial n : ℝ) := by
  have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hnn : ∀ i ∈ Finset.range (n + 1), (0 : ℝ) ≤ x ^ i / (Nat.factorial i : ℝ) := by
    intro i _
    have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
    exact div_nonneg (pow_nonneg hx i) hfi.le
  have hsingle : x ^ n / (Nat.factorial n : ℝ) ≤
      ∑ i ∈ Finset.range (n + 1), x ^ i / (Nat.factorial i : ℝ) :=
    Finset.single_le_sum hnn (Finset.self_mem_range_succ n)
  have hexp : x ^ n / (Nat.factorial n : ℝ) ≤ Real.exp x :=
    le_trans hsingle (Real.sum_le_exp_of_nonneg hx (n + 1))
  have hxn : x ^ n ≤ (Nat.factorial n : ℝ) * Real.exp x := by
    rw [div_le_iff₀ hfac] at hexp
    linarith only [hexp]
  have hepos : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right hxn hepos.le
  have hcancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc x ^ n * Real.exp (-x) ≤ (Nat.factorial n : ℝ) * Real.exp x * Real.exp (-x) := hmul
    _ = (Nat.factorial n : ℝ) * (Real.exp x * Real.exp (-x)) := by ring
    _ = (Nat.factorial n : ℝ) := by rw [hcancel, mul_one]

/-- **The moment `q`-power against the printed exponential amplitude.**

On the anchor's own range `q ≤ γ^{-1}` the printed `q^n e^{-aγ^{-1}}` of the
Step-4 moment conversions is bounded by the absolute constant `n!/a^n`: NO
restriction on `p` is used, and no `γ`-power is moved. -/
theorem pow_mul_exp_neg_inv_le {a g y : ℝ} (n : ℕ) (ha : 0 < a) (hg : 0 < g)
    (hy0 : 0 ≤ y) (hy : y ≤ g⁻¹) :
    y ^ n * Real.exp (-(a * g⁻¹)) ≤ (Nat.factorial n : ℝ) / a ^ n := by
  have hginv : (0 : ℝ) < g⁻¹ := inv_pos.mpr hg
  have hx : (0 : ℝ) ≤ a * g⁻¹ := (mul_pos ha hginv).le
  have hbase := pow_mul_exp_neg_le n hx
  have hsplit : (a * g⁻¹) ^ n = a ^ n * (g⁻¹) ^ n := mul_pow a g⁻¹ n
  have han : (0 : ℝ) < a ^ n := pow_pos ha n
  have hyn : y ^ n ≤ (g⁻¹) ^ n := pow_le_pow_left₀ hy0 hy n
  have hE : (0 : ℝ) < Real.exp (-(a * g⁻¹)) := Real.exp_pos _
  have h1 : y ^ n * Real.exp (-(a * g⁻¹)) ≤ (g⁻¹) ^ n * Real.exp (-(a * g⁻¹)) :=
    mul_le_mul_of_nonneg_right hyn hE.le
  have h2 : a ^ n * ((g⁻¹) ^ n * Real.exp (-(a * g⁻¹))) ≤ (Nat.factorial n : ℝ) := by
    rw [← mul_assoc, ← hsplit]
    exact hbase
  rw [le_div_iff₀ han]
  have h3 := mul_le_mul_of_nonneg_right h1 han.le
  have hid : (g⁻¹) ^ n * Real.exp (-(a * g⁻¹)) * a ^ n =
      a ^ n * ((g⁻¹) ^ n * Real.exp (-(a * g⁻¹))) := by ring
  linarith only [h2, h3, hid]

/-- **The same, with one factor `γ` to spare.**

`y^n e^{-aγ^{-1}} ≤ ((n+1)!/a^{n+1}) γ` on `0 ≤ y ≤ γ^{-1}`.  This is the form
Step 5's per-scale evaluation needs: the printed exponential beats the moment
`q`-power AND still produces the `γ` of the anchor's own scalar. -/
theorem pow_mul_exp_neg_inv_le_mul {a g y : ℝ} (n : ℕ) (ha : 0 < a) (hg : 0 < g)
    (hy0 : 0 ≤ y) (hy : y ≤ g⁻¹) :
    y ^ n * Real.exp (-(a * g⁻¹)) ≤ (Nat.factorial (n + 1) : ℝ) / a ^ (n + 1) * g := by
  have hginv : (0 : ℝ) < g⁻¹ := inv_pos.mpr hg
  have hstep := pow_mul_exp_neg_inv_le (n + 1) ha hg hginv.le (le_refl g⁻¹)
  have hE : (0 : ℝ) < Real.exp (-(a * g⁻¹)) := Real.exp_pos _
  have hyn : y ^ n ≤ (g⁻¹) ^ n := pow_le_pow_left₀ hy0 hy n
  have h1 : y ^ n * Real.exp (-(a * g⁻¹)) ≤ (g⁻¹) ^ n * Real.exp (-(a * g⁻¹)) :=
    mul_le_mul_of_nonneg_right hyn hE.le
  have hid : g * ((g⁻¹) ^ (n + 1) * Real.exp (-(a * g⁻¹))) =
      (g⁻¹) ^ n * Real.exp (-(a * g⁻¹)) := by
    rw [pow_succ]
    field_simp
  have h2 := mul_le_mul_of_nonneg_left hstep hg.le
  have hid2 : g * ((Nat.factorial (n + 1) : ℝ) / a ^ (n + 1)) =
      (Nat.factorial (n + 1) : ℝ) / a ^ (n + 1) * g := by ring
  linarith only [h1, h2, hid, hid2]

/-! ## 2. The `|log γ|` portion of bullet (B2) -/

/-- `-(t log t) ≤ 1` for `t > 0`.  Local re-derivation (distinct name) of
`Algsuperdiff.Probability.neg_mul_log_le_one`. -/
private theorem negMulLogLeOne {t : ℝ} (ht : 0 < t) : -(t * Real.log t) ≤ 1 := by
  have h1 : Real.log t⁻¹ ≤ t⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  rw [Real.log_inv] at h1
  have h2 : t * -Real.log t ≤ t * (t⁻¹ - 1) := mul_le_mul_of_nonneg_left h1 ht.le
  have h3 : t * (t⁻¹ - 1) = 1 - t := by rw [mul_sub, mul_inv_cancel₀ ht.ne', mul_one]
  linarith only [h2, h3, ht.le]

/-- **The scale-free log bound at the exponent `1/10`.**  `γ^{1/10}(log γ)² ≤ 400`
on `(0,1]`: the `t = γ^{1/20}` core, where `t·t·(20 log t)² = 400 (t log t)²`. -/
theorem rpow_tenth_mul_log_sq_le {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) :
    g ^ ((1 : ℝ) / 10) * Real.log g ^ 2 ≤ 400 := by
  set t : ℝ := g ^ ((1 : ℝ) / 20) with htdef
  have ht0 : (0 : ℝ) < t := Real.rpow_pos_of_pos hg _
  have ht1 : t ≤ 1 := Real.rpow_le_one hg.le hg1 (by norm_num)
  have hlogt : Real.log t = 1 / 20 * Real.log g := by
    rw [htdef, Real.log_rpow hg]
  have htt : t * t = g ^ ((1 : ℝ) / 10) := by
    rw [htdef, ← Real.rpow_add hg]
    norm_num
  have hbound : -(t * Real.log t) ≤ 1 := negMulLogLeOne ht0
  have hlognp : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
  have hnn : (0 : ℝ) ≤ -(t * Real.log t) := by
    have h := mul_nonneg ht0.le (neg_nonneg.mpr hlognp)
    linarith only [h]
  have hsq : (-(t * Real.log t)) ^ 2 ≤ 1 := pow_le_one₀ hnn hbound
  have hid : g ^ ((1 : ℝ) / 10) * Real.log g ^ 2 = 400 * (-(t * Real.log t)) ^ 2 := by
    rw [← htt, hlogt]
    ring
  rw [hid]
  linarith only [hsq]

/-- **Bullet (B2)'s `|log γ|` portion, squared.**

`(γ^{3/5}|log γ|²)² ≤ 160000 γ`.  The square is what makes the portion `O(γ)`:
`γ^{3/5}|log γ|²` itself is not, and (B2) is a squared display. -/
theorem gammaLogPortion_sq_le {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) :
    (g ^ ((3 : ℝ) / 5) * |Real.log g| ^ 2) ^ 2 ≤ 160000 * g := by
  have hkey := rpow_tenth_mul_log_sq_le hg hg1
  have hnn : (0 : ℝ) ≤ g ^ ((1 : ℝ) / 10) * Real.log g ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hg.le _) (sq_nonneg _)
  have hsq : (g ^ ((1 : ℝ) / 10) * Real.log g ^ 2) ^ 2 ≤ 160000 := by
    have h := pow_le_pow_left₀ hnn hkey 2
    norm_num at h
    exact h
  have e1 : (g ^ ((1 : ℝ) / 10) * Real.log g ^ 2) ^ 2 =
      g ^ ((1 : ℝ) / 5) * (Real.log g ^ 2) ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast (g ^ ((1 : ℝ) / 10)) 2, ← Real.rpow_mul hg.le]
    norm_num
  have e2 : (g ^ ((3 : ℝ) / 5) * |Real.log g| ^ 2) ^ 2 =
      g * (g ^ ((1 : ℝ) / 5) * (Real.log g ^ 2) ^ 2) := by
    rw [sq_abs, mul_pow, ← Real.rpow_natCast (g ^ ((3 : ℝ) / 5)) 2, ← Real.rpow_mul hg.le]
    have h65 : g ^ ((3 : ℝ) / 5 * ((2 : ℕ) : ℝ)) = g ^ (1 : ℝ) * g ^ ((1 : ℝ) / 5) := by
      rw [← Real.rpow_add hg]
      norm_num
    rw [h65, Real.rpow_one]
    ring
  rw [e2, ← e1]
  have h := mul_le_mul_of_nonneg_left hsq hg.le
  linarith only [h]

/-- `(x+y)² ≤ 2x² + 2y²`, the two-lane split of bullet (B4)'s squared majorant.
Proved from `(x−y)² ≥ 0` alone: no numeric tactic touches the transcendental
atoms of the lanes. -/
theorem add_sq_le_two_mul (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  have h := sq_nonneg (x - y)
  have h1 : (x + y) ^ 2 = x ^ 2 + 2 * (x * y) + y ^ 2 := by ring
  have h2 : (x - y) ^ 2 = x ^ 2 - 2 * (x * y) + y ^ 2 := by ring
  linarith only [h, h1, h2]

/-! ## 3. The two squared-minimum splits -/

/-- **The `min`-square split.**  `(min{1, a+b})² ≤ 2a + 2b²` for `a, b ≥ 0`.

Both branches of the minimum are covered at once: below the cap the square of
the sum is `≤ 2a² + 2b² ≤ 2a + 2b²`, and above it the constant `1` is already
dominated by `2(a+b) − 1/2 ≥ 3/2`. -/
theorem min_one_add_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min 1 (a + b) ^ 2 ≤ 2 * a + 2 * b ^ 2 := by
  rcases le_total (a + b) 1 with h | h
  · rw [min_eq_right h]
    have ha1 : a ≤ 1 := by linarith only [h, hb]
    have hid : a * (1 - a) = a - a ^ 2 := by ring
    have hprod := mul_nonneg ha (by linarith only [ha1] : (0 : ℝ) ≤ 1 - a)
    have hab := sq_nonneg (a - b)
    have hexp : (a + b) ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2 := by ring
    have hexp2 : (a - b) ^ 2 = a ^ 2 - 2 * (a * b) + b ^ 2 := by ring
    linarith only [hid, hprod, hab, hexp, hexp2]
  · rw [min_eq_left h]
    have hone : (1 : ℝ) ^ 2 = 1 := one_pow 2
    have hbsq := sq_nonneg (b - 1 / 2)
    have hid : (b - 1 / 2) ^ 2 = b ^ 2 - b + 1 / 4 := by ring
    linarith only [h, hone, hbsq, hid]

/-- This is the additive `1` carried through the square, at the branch `√b` of the
minimum. -/
theorem one_add_min_sqrt_sq_le {a b : ℝ} (hb : 0 ≤ b) :
    (1 + min (Real.sqrt a) (Real.sqrt b)) ^ 2 ≤ 2 * (1 + b) := by
  have hx0 : (0 : ℝ) ≤ min (Real.sqrt a) (Real.sqrt b) :=
    le_min (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have hxb : min (Real.sqrt a) (Real.sqrt b) ≤ Real.sqrt b := min_le_right _ _
  have hsq : min (Real.sqrt a) (Real.sqrt b) ^ 2 ≤ b := by
    have h := pow_le_pow_left₀ hx0 hxb 2
    rwa [Real.sq_sqrt hb] at h
  have hd := sq_nonneg (1 - min (Real.sqrt a) (Real.sqrt b))
  have hid1 : (1 + min (Real.sqrt a) (Real.sqrt b)) ^ 2 =
      1 + 2 * min (Real.sqrt a) (Real.sqrt b) + min (Real.sqrt a) (Real.sqrt b) ^ 2 := by
    ring
  have hid2 : (1 - min (Real.sqrt a) (Real.sqrt b)) ^ 2 =
      1 - 2 * min (Real.sqrt a) (Real.sqrt b) + min (Real.sqrt a) (Real.sqrt b) ^ 2 := by
    ring
  linarith only [hsq, hd, hid1, hid2]

/-! ## 4. Two gauge-weight identities -/

/-- **The gauge weight, moved to the other side.**  A bound on `3^y X` is a bound
on `X` with the weight inverted; the development's per-scale evaluation reads
the Step-4 bullets in this second form. -/
theorem le_rpow_neg_mul_of_rpow_mul_le {y X B : ℝ} (h : (3 : ℝ) ^ y * X ≤ B) :
    X ≤ (3 : ℝ) ^ (-y) * B := by
  have hp : (0 : ℝ) < (3 : ℝ) ^ (-y) := Real.rpow_pos_of_pos (by norm_num) _
  have hcancel : (3 : ℝ) ^ (-y) * ((3 : ℝ) ^ y * X) = X := by
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3), neg_add_cancel,
      Real.rpow_zero, one_mul]
  have hmul := mul_le_mul_of_nonneg_left h hp.le
  linarith only [hmul, hcancel]

/-- **The three gauge weights of the second summand's value leg, combined.**
`3^{-a} · (3^{-b} · 3^{2a}) = 3^{a−b}`: the two inverted weights of `σ_m^{-1}`
and of the `λ`-slot against the value slot's `3^{2γm}`.  This is where the
per-scale factor `3^{γ(m−j)}` of Step 5's geometric sum comes from. -/
theorem rpow_three_gauge_triple (a b : ℝ) :
    (3 : ℝ) ^ (-a) * ((3 : ℝ) ^ (-b) * (3 : ℝ) ^ (2 * a)) = (3 : ℝ) ^ (a - b) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- The gauge weight is monotone in the exponent. -/
theorem rpow_three_le_rpow_three {a b : ℝ} (hab : a ≤ b) : (3 : ℝ) ^ a ≤ (3 : ℝ) ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) hab

/-! ## 5. The geometric uniformizer -/

/-- `3^{γ−1} ≤ 3/5` at `γ ≤ 1/2`, through `√3 ≥ 5/3`. -/
theorem rpow_three_gamma_sub_one_le {g : ℝ} (hg : g ≤ 1 / 2) :
    Real.rpow 3 (g - 1) ≤ 3 / 5 := by
  have h1 : Real.rpow 3 (g - 1) ≤ Real.rpow 3 (-((1 : ℝ) / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hg])
  have h2 : Real.rpow 3 (-((1 : ℝ) / 2)) = (Real.sqrt 3)⁻¹ := by
    show (3 : ℝ) ^ (-((1 : ℝ) / 2)) = (Real.sqrt 3)⁻¹
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), ← Real.sqrt_eq_rpow]
  have hs0 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h3 : (5 : ℝ) / 3 ≤ Real.sqrt 3 := by
    have h := Real.sqrt_le_sqrt (show ((5 : ℝ) / 3) ^ 2 ≤ 3 by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 3)] at h
  have h5 : ((3 : ℝ) / 5)⁻¹ = 5 / 3 := by norm_num
  have h4 : (Real.sqrt 3)⁻¹ ≤ 3 / 5 := by
    rw [inv_le_comm₀ hs0 (by norm_num : (0 : ℝ) < 3 / 5), h5]
    exact h3
  linarith only [h1, h2, h4]

/-- **The geometric uniformizer.**  `(1 − 3^{γ−1})^{-1} ≤ 3` at `γ ≤ 1/2`.

This is what turns `GradBottomLayer.fullGradConst` and
`GradSlotMoment.deepGradConst` -- both of which carry the `γ`-dependent factor
`(1 − 3^{γ−1})^{-1}` -- into dimensional constants, as Step 5's per-cube evaluation
needs (its constant is chosen before the model). -/
theorem inv_one_sub_rpow_three_gamma_le {g : ℝ} (hg : g ≤ 1 / 2) :
    (1 - Real.rpow 3 (g - 1))⁻¹ ≤ 3 := by
  have h := rpow_three_gamma_sub_one_le hg
  have hpos : (0 : ℝ) < 1 - Real.rpow 3 (g - 1) := by linarith only [h]
  have h3inv : (3 : ℝ)⁻¹ = 1 / 3 := by norm_num
  rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 3)]
  linarith only [h, h3inv]

end

end Algsuperdiff.Section4.Provider.BoundsEaL
