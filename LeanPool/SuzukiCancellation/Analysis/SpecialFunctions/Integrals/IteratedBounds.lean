/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.RealScalar
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Interval-integral identities and bounds

Ordinary interval integrals used in Dyson-series, Taylor remainder and Trotter
error estimates. The interval integral carries the orientation of its endpoints.

## Main results

* `integral_mul_integral_pow_div_factorial`: the iterated-integral FTC identity.
* `abs_integral_mul_abs_integral_pow_div_factorial`: its two-sided norm companion.
* `integral_abs_sub_pow_uIoc`: the beta integral used in commutator estimates.
* `norm_intervalIntegral_le_of_le_abs_sub_pow`: a pointwise power bound for either time direction.
* `integral_smul_eq_integral_mul_sub`: the substituted Taylor remainder integral.
* `norm_intervalIntegral_le_const_mul_abs_pow_div_factorial_mul`: integrate a
  factorial-polynomial norm bound.
-/

@[expose] public section

open scoped RealScalar

namespace TrotterError

open NormedSpace
open scoped Topology BigOperators Interval

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-! ### The fundamental-theorem identity behind the norm bound -/

/-- For continuous `f`, the iterated-integral identity
`∫ τ in a..b, f τ * (∫ u in a..τ, f u)^n / n! = (∫ u in a..b, f u)^(n+1) / (n+1)!`
(valid for all `a b`, with the interval integral carrying the orientation).
This is the FTC applied to `t ↦ (∫_a^t f)^(n+1)/(n+1)!` and is the key step in bounding the
Dyson terms by `(∫ ‖H‖)^n/n!`. -/
lemma integral_mul_integral_pow_div_factorial (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) (n : ℕ) :
    (∫ τ in a..b, f τ * (∫ u in a..τ, f u) ^ n / Nat.factorial n) =
      (∫ u in a..b, f u) ^ (n + 1) / Nat.factorial (n + 1) := by
  let F : ℝ → ℝ := fun t => ∫ u in a..t, f u
  let G : ℝ → ℝ := fun t => F t ^ (n + 1) / Nat.factorial (n + 1)
  have hFderiv : ∀ t : ℝ, HasDerivAt F (f t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable a t)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hGderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt G (f t * F t ^ n / Nat.factorial n) t := by
    intro t _
    have hdiff : DifferentiableAt ℝ G t := ((hFderiv t).differentiableAt.pow (n + 1)).div_const
      (Nat.factorial (n + 1) : ℝ)
    have hderiv : deriv G t = f t * F t ^ n / Nat.factorial n := by
      dsimp [G]
      rw [deriv_div_const]
      change deriv (F ^ (n + 1)) t / (Nat.factorial (n + 1) : ℝ) = _
      rw [deriv_pow (hFderiv t).differentiableAt (n + 1), (hFderiv t).deriv, Nat.add_one_sub_one,
        Nat.factorial_succ, Nat.cast_mul]
      field_simp
    simpa [hderiv] using hdiff.hasDerivAt
  have hFcont : Continuous F :=
    (intervalIntegral.differentiable_integral_of_continuous hf).continuous
  have hint : IntervalIntegrable (fun τ => f τ * F τ ^ n / Nat.factorial n)
      MeasureTheory.volume a b :=
    (by fun_prop : Continuous fun τ => f τ * F τ ^ n / Nat.factorial n).intervalIntegrable a b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := G)
    (f' := fun τ => f τ * F τ ^ n / Nat.factorial n) hGderiv hint
  calc
    (∫ τ in a..b, f τ * (∫ u in a..τ, f u) ^ n / Nat.factorial n)
        = ∫ τ in a..b, f τ * F τ ^ n / Nat.factorial n := rfl
    _ = G b - G a := hFTC
    _ = (∫ u in a..b, f u) ^ (n + 1) / Nat.factorial (n + 1) := by simp [G, F]

/-- For continuous nonnegative `g`, the two-sided FTC identity
`|∫ τ in a..b, g τ * |∫ u in a..τ, g u|^n / n!| = |∫ u in a..b, g u|^(n+1) / (n+1)!`.
This is the "backward" companion of `integral_mul_integral_pow_div_factorial`. -/
lemma abs_integral_mul_abs_integral_pow_div_factorial (g : ℝ → ℝ) (hg : Continuous g)
    (hgnn : ∀ τ, 0 ≤ g τ) (a b : ℝ) (n : ℕ) :
    |∫ τ in a..b, g τ * |∫ u in a..τ, g u| ^ n / Nat.factorial n| =
      |∫ u in a..b, g u| ^ (n + 1) / Nat.factorial (n + 1) := by
  let F : ℝ → ℝ := fun τ => ∫ u in a..τ, g u
  by_cases hab : a ≤ b
  · -- forward: `F τ ≥ 0` on `[a, b]`, so `|F τ| = F τ` and the integral is nonnegative.
    have hFnn_interval : ∀ τ ∈ Set.Icc a b, 0 ≤ F τ := by
      intro τ hτ
      exact intervalIntegral.integral_nonneg hτ.1 (fun u _ => hgnn u)
    have hFnn_uIoo : ∀ τ ∈ Set.uIoo a b, 0 ≤ F τ := by
      intro τ hτ
      have hmin : min a b < τ := hτ.1
      have haτ : a ≤ τ := by simpa [min_eq_left hab] using le_of_lt hmin
      exact intervalIntegral.integral_nonneg haτ (fun u _ => hgnn u)
    have heq : (∫ τ in a..b, g τ * |F τ| ^ n / Nat.factorial n) =
        ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n := by
      apply intervalIntegral.integral_congr_uIoo
      intro τ hτ
      simp [abs_of_nonneg (hFnn_uIoo τ hτ)]
    have hnonneg : 0 ≤ ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n :=
      intervalIntegral.integral_nonneg hab (fun τ hτ =>
        div_nonneg (mul_nonneg (hgnn τ) (pow_nonneg (hFnn_interval τ hτ) n)) (by positivity))
    calc
      |∫ τ in a..b, g τ * |F τ| ^ n / Nat.factorial n|
          = ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n := by rw [heq, abs_of_nonneg hnonneg]
      _ = F b ^ (n + 1) / Nat.factorial (n + 1) :=
          integral_mul_integral_pow_div_factorial g hg a b n
      _ = |∫ u in a..b, g u| ^ (n + 1) / Nat.factorial (n + 1) := by
          rw [show F b = ∫ u in a..b, g u by rfl,
            abs_of_nonneg (intervalIntegral.integral_nonneg hab (fun u _ => hgnn u))]
  · -- backward: `b ≤ a`, so `F τ ≤ 0` on `[b, a]`, `|F τ| = -F τ`.
    have hba : b ≤ a := le_of_not_ge hab
    have hFnonpos_uIoo : ∀ τ ∈ Set.uIoo a b, F τ ≤ 0 := by
      intro τ hτ
      have hmax : τ < max a b := hτ.2
      have hτa : τ ≤ a := by simpa [max_eq_left hba] using le_of_lt hmax
      calc
        F τ = ∫ u in a..τ, g u := rfl
        _ ≤ 0 := by
          have hnonneg : 0 ≤ ∫ u in τ..a, g u :=
            intervalIntegral.integral_nonneg hτa (fun u _ => hgnn u)
          rw [intervalIntegral.integral_symm]
          linarith
    have heq : (∫ τ in a..b, g τ * |F τ| ^ n / Nat.factorial n) =
        (-1 : ℝ) ^ n * ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n := by
      calc
        (∫ τ in a..b, g τ * |F τ| ^ n / Nat.factorial n)
            = ∫ τ in a..b, (-1 : ℝ) ^ n * (g τ * F τ ^ n / Nat.factorial n) := by
                apply intervalIntegral.integral_congr_uIoo
                intro τ hτ; simp only
                rw [abs_of_nonpos (hFnonpos_uIoo τ hτ), neg_pow]
                ring
        _ = (-1 : ℝ) ^ n * ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n := by
                rw [intervalIntegral.integral_const_mul]
    calc
      |∫ τ in a..b, g τ * |F τ| ^ n / Nat.factorial n|
          = |(-1 : ℝ) ^ n * ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n| := by rw [heq]
      _ = |(-1 : ℝ) ^ n * (F b ^ (n + 1) / Nat.factorial (n + 1))| := by
          rw [integral_mul_integral_pow_div_factorial g hg a b n]
      _ = |∫ u in a..b, g u| ^ (n + 1) / Nat.factorial (n + 1) := by
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_div, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (Nat.factorial (n + 1) : ℝ))]

/-- For continuous nonnegative `g`, the "distance travelled" `|∫_t₁^x g|` is bounded on any
interval `[a, b]` by the sum of its endpoint values: monotonicity of the oriented integral. -/
lemma abs_integral_le_abs_integral_of_mem_Icc {g : ℝ → ℝ} (hg : Continuous g)
    (hgnn : ∀ t, 0 ≤ g t) (t₁ a b x : ℝ) (hx : x ∈ Set.Icc a b) :
    |(∫ u in t₁..x, g u)| ≤ |(∫ u in t₁..a, g u)| + |(∫ u in t₁..b, g u)| := by
  have hmono : Monotone (fun t : ℝ => ∫ u in t₁..t, g u) := by
    intro s t hst
    have hnonneg : 0 ≤ ∫ u in s..t, g u :=
      intervalIntegral.integral_nonneg hst (fun u _ => hgnn u)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (f := g)
      (μ := MeasureTheory.volume) (a := t₁) (b := s) (c := t) (hg.intervalIntegrable t₁ s)
      (hg.intervalIntegrable s t)
    linarith [hadd, hnonneg]
  have hlo : (∫ u in t₁..a, g u) ≤ ∫ u in t₁..x, g u := hmono hx.1
  have hhi : (∫ u in t₁..x, g u) ≤ ∫ u in t₁..b, g u := hmono hx.2
  have hneg_abs : -|∫ u in t₁..a, g u| ≤ ∫ u in t₁..a, g u := by
    simpa using (neg_le_neg (neg_le_abs (∫ u in t₁..a, g u)))
  exact abs_le.mpr ⟨
    le_trans (le_trans (neg_le_neg (le_add_of_nonneg_right (abs_nonneg (∫ u in t₁..b, g u))))
      hneg_abs) hlo,
    le_trans (le_trans hhi (le_abs_self (∫ u in t₁..b, g u)))
      (le_add_of_nonneg_left (abs_nonneg (∫ u in t₁..a, g u)))⟩

/-- `∫ τ in a..b, (τ - a)^n = (b - a)^(n+1) / (n+1)`. -/
lemma integral_sub_pow (a b : ℝ) (n : ℕ) :
    (∫ τ in a..b, (τ - a) ^ n) = (b - a) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
  have hfun : (fun τ : ℝ => (τ - a) ^ n) = fun τ => (τ + (-a)) ^ n := by
    funext τ
    rw [sub_eq_add_neg]
  rw [hfun, intervalIntegral.integral_comp_add_right (f := fun σ : ℝ => σ ^ n) (d := -a),
    integral_pow]
  simp [sub_eq_add_neg]

/-- Left multiplication by a constant commutes with the interval integral (for a general normed
ℝ-algebra). -/
lemma integral_mul_left (c : 𝔸) (f : ℝ → 𝔸) (hf : Continuous f) (a b : ℝ) :
    (∫ x in a..b, c * f x) = c * ∫ x in a..b, f x := by
  simpa only [ContinuousLinearMap.mul_apply'] using
    (ContinuousLinearMap.mul ℝ 𝔸 c).intervalIntegral_comp_comm (hf.intervalIntegrable a b)

/-! ### Distance bound: monotonicity "last mile" -/

/-- For nonnegative continuous `f, g` and `x` in the unordered interval between `a` and `b`, the
sum of the two partial oriented-absolute integrals `|∫_x^b f| + |∫_a^x g|` is at most
`|∫_a^b (f + g)|`. This is the monotonicity "last mile" for the distance bound: both partial
integrals carry the sign of the orientation, so their absolute values telescope into the single
oriented integral of `f + g`. -/
lemma abs_integral_add_le_abs_integral_of_mem_uIcc {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hfnn : ∀ t, 0 ≤ f t) (hgnn : ∀ t, 0 ≤ g t) (a b x : ℝ)
    (hx : x ∈ Set.uIcc a b) :
    |∫ u in x..b, f u| + |∫ u in a..x, g u| ≤ |∫ u in a..b, f u + g u| := by
  by_cases hab : a ≤ b
  · -- forward: `a ≤ x ≤ b`, all partial integrals are nonnegative.
    have hx' : x ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hx
    have hfx : 0 ≤ ∫ u in x..b, f u :=
      intervalIntegral.integral_nonneg hx'.2 (fun u _ => hfnn u)
    have hgx : 0 ≤ ∫ u in a..x, g u :=
      intervalIntegral.integral_nonneg hx'.1 (fun u _ => hgnn u)
    have hfg : 0 ≤ ∫ u in a..b, f u + g u :=
      intervalIntegral.integral_nonneg hab (fun u _ => add_nonneg (hfnn u) (hgnn u))
    rw [abs_of_nonneg hfx, abs_of_nonneg hgx, abs_of_nonneg hfg]
    have hfx_le : ∫ u in x..b, f u ≤ ∫ u in x..b, f u + g u := by
      refine intervalIntegral.integral_mono_on (a := x) (b := b) hx'.2
        (hf.intervalIntegrable x b) ((hf.add hg).intervalIntegrable x b) ?_
      intro u _
      exact le_add_of_nonneg_right (hgnn u)
    have hgx_le : ∫ u in a..x, g u ≤ ∫ u in a..x, f u + g u := by
      refine intervalIntegral.integral_mono_on (a := a) (b := x) hx'.1
        (hg.intervalIntegrable a x) ((hf.add hg).intervalIntegrable a x) ?_
      intro u _
      exact le_add_of_nonneg_left (hfnn u)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (f := fun u => f u + g u)
      (μ := MeasureTheory.volume) (a := a) (b := x) (c := b)
      ((hf.add hg).intervalIntegrable a x) ((hf.add hg).intervalIntegrable x b)
    calc
      (∫ u in x..b, f u) + ∫ u in a..x, g u
          ≤ (∫ u in a..x, f u + g u) + ∫ u in x..b, f u + g u :=
              (add_le_add hfx_le hgx_le).trans_eq (add_comm _ _)
      _ = ∫ u in a..b, f u + g u := hadd
  · -- backward: `b ≤ x ≤ a`, the partial integrals are nonpositive, so their absolute values are
    -- the integrals over the reversed (nonnegative) subintervals.
    have hba : b ≤ a := le_of_not_ge hab
    have hx' : x ∈ Set.Icc b a := by
      simpa [Set.uIcc_of_ge hba] using hx
    have hfx : 0 ≤ ∫ u in b..x, f u :=
      intervalIntegral.integral_nonneg hx'.1 (fun u _ => hfnn u)
    have hgx : 0 ≤ ∫ u in x..a, g u :=
      intervalIntegral.integral_nonneg hx'.2 (fun u _ => hgnn u)
    have hfg : 0 ≤ ∫ u in b..a, f u + g u :=
      intervalIntegral.integral_nonneg hba (fun u _ => add_nonneg (hfnn u) (hgnn u))
    have hfx_le : ∫ u in b..x, f u ≤ ∫ u in b..x, f u + g u := by
      refine intervalIntegral.integral_mono_on (a := b) (b := x) hx'.1
        (hf.intervalIntegrable b x) ((hf.add hg).intervalIntegrable b x) ?_
      intro u _
      exact le_add_of_nonneg_right (hgnn u)
    have hgx_le : ∫ u in x..a, g u ≤ ∫ u in x..a, f u + g u := by
      refine intervalIntegral.integral_mono_on (a := x) (b := a) hx'.2
        (hg.intervalIntegrable x a) ((hf.add hg).intervalIntegrable x a) ?_
      intro u _
      exact le_add_of_nonneg_left (hfnn u)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (f := fun u => f u + g u)
      (μ := MeasureTheory.volume) (a := b) (b := x) (c := a)
      ((hf.add hg).intervalIntegrable b x) ((hf.add hg).intervalIntegrable x a)
    have hsum : (∫ u in b..x, f u) + ∫ u in x..a, g u ≤ ∫ u in b..a, f u + g u := by
      calc
        (∫ u in b..x, f u) + ∫ u in x..a, g u
            ≤ (∫ u in b..x, f u + g u) + ∫ u in x..a, f u + g u := add_le_add hfx_le hgx_le
        _ = ∫ u in b..a, f u + g u := hadd
    have habs_f : |∫ u in x..b, f u| = ∫ u in b..x, f u := by
      rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg hfx]
    have habs_g : |∫ u in a..x, g u| = ∫ u in x..a, g u := by
      rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg hgx]
    have habs_fg : |∫ u in a..b, f u + g u| = ∫ u in b..a, f u + g u := by
      rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg hfg]
    rwa [habs_f, habs_g, habs_fg]

end TrotterError

namespace TrotterError

open NormedSpace MeasureTheory
open scoped algebraMap

/-- The beta-type integral `∫ u in uIoc 0 τ, |τ - u|^(q-1) du = |τ|^q / q`, for `1 ≤ q`. -/
lemma integral_abs_sub_pow_uIoc (q : ℕ) (τ : ℝ) (hq : 1 ≤ q) :
    (∫ u in Set.uIoc (0 : ℝ) τ, |τ - u| ^ (q - 1)) = |τ| ^ q / (q : ℝ) := by
  have h := integral_pow_abs_sub_uIoc (a := τ) (b := (0 : ℝ)) (n := q - 1)
  calc
    (∫ u in Set.uIoc (0 : ℝ) τ, |τ - u| ^ (q - 1))
        = (∫ u in Set.uIoc (τ : ℝ) 0, |u - τ| ^ (q - 1)) := by
            rw [Set.uIoc_comm (a := (0 : ℝ)) (b := τ)]
            exact setIntegral_congr_fun measurableSet_uIoc
              (fun u _ => congrArg (fun t : ℝ => t ^ (q - 1)) (abs_sub_comm τ u))
    _ = |τ| ^ q / (q : ℝ) := by
            rw [h]
            have hcast : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by
              norm_cast
              rw [Nat.sub_add_cancel hq]
            rw [Nat.sub_add_cancel hq, hcast, abs_sub_comm (0 : ℝ) τ, sub_zero]

/-- A pointwise power bound centered at the terminal endpoint bounds the integral for either
orientation of the interval. -/
lemma norm_intervalIntegral_le_of_le_abs_sub_pow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) {C τ : ℝ} {q : ℕ} (hC : 0 ≤ C) (hq : 1 ≤ q)
    (h : ∀ u ∈ Set.uIoc (0 : ℝ) τ, ‖f u‖ ≤ C * |τ - u| ^ (q - 1)) :
    ‖∫ u in 0..τ, f u‖ ≤ C * (|τ| ^ q / q) := by
  calc
    _ ≤ |∫ u in 0..τ, C * |τ - u| ^ (q - 1)| := by
      apply intervalIntegral.norm_integral_le_abs_of_norm_le
      · rw [ae_restrict_iff' measurableSet_uIoc]
        filter_upwards with u hu
        exact h u hu
      · exact (by fun_prop : Continuous fun u : ℝ ↦ C * |τ - u| ^ (q - 1)).intervalIntegrable 0 τ
    _ = _ := by
      rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc, integral_const_mul,
        integral_abs_sub_pow_uIoc q τ hq, abs_of_nonneg (by positivity)]

/-- `∫₀^τ |s|^(p-1)/(p-1)! ds = |τ|^p/p!` over the unordered interval, for `1 ≤ p`. -/
lemma integral_abs_pow_sub_div_factorial_uIoc (p : ℕ) (τ : ℝ) (hp : 1 ≤ p) :
    (∫ s in Set.uIoc (0 : ℝ) τ, |s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) =
      |τ| ^ p / (Nat.factorial p : ℝ) := by
  have hfac : Nat.factorial p = p * Nat.factorial (p - 1) := by
    simpa [Nat.sub_add_cancel hp] using Nat.factorial_succ (p - 1)
  calc
    (∫ s in Set.uIoc (0 : ℝ) τ, |s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ))
        = (∫ s in Set.uIoc (0 : ℝ) τ, |s| ^ (p - 1)) / (Nat.factorial (p - 1) : ℝ) := by
            rw [integral_div]
    _ = (|τ| ^ p / (p : ℝ)) / (Nat.factorial (p - 1) : ℝ) := by
            have hp' : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
              rw [Nat.cast_sub hp]
              ring
            have hpow : (∫ s in Set.uIoc (0 : ℝ) τ, |s| ^ (p - 1)) = |τ| ^ p / (p : ℝ) := by
              have h := integral_pow_abs_sub_uIoc (a := 0) (b := τ) (n := p - 1)
              rw [Nat.sub_add_cancel hp, hp'] at h
              simpa using h
            rw [hpow]
    _ = |τ| ^ p / (Nat.factorial p : ℝ) := by
            rw [hfac, Nat.cast_mul]
            field_simp

/-- `|∫₀^τ |s|^(p-1)/(p-1)! ds| = |τ|^p/p!` for `1 ≤ p`. -/
lemma abs_integral_abs_pow_div_factorial (p : ℕ) (τ : ℝ) (hp : 1 ≤ p) :
    |∫ s in 0..τ, |s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)|
      = |τ| ^ p / (Nat.factorial p : ℝ) := by
  rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc]
  have hnonneg : 0 ≤ (∫ s in Set.uIoc (0 : ℝ) τ, |s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) :=
    setIntegral_nonneg measurableSet_uIoc (fun s _ => by positivity)
  rw [abs_of_nonneg hnonneg, integral_abs_pow_sub_div_factorial_uIoc p τ hp]

/-- The standard Taylor remainder integral equals the paper's substituted form:
`∫₀^τ (τ-s)^n/n! • F s = ∫₀^τ F (τ-s) * (s^n/n!)`. -/
lemma integral_smul_eq_integral_mul_sub {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (F : ℝ → 𝔸) (n : ℕ) (τ : ℝ) :
    (∫ s in 0..τ, ((τ - s) ^ n / (Nat.factorial n : ℝ)) • F s) =
      ∫ s in 0..τ, F (τ - s) * ((s ^ n / (Nat.factorial n : ℝ)) : 𝔸) := by
  calc
    (∫ s in 0..τ, ((τ - s) ^ n / (Nat.factorial n : ℝ)) • F s)
        = ∫ s in 0..τ, F s * (((τ - s) ^ n / (Nat.factorial n : ℝ)) : 𝔸) := by
            apply intervalIntegral.integral_congr_uIoo
            intro s hs
            dsimp only
            rw [Algebra.smul_def, Algebra.commutes]
    _ = ∫ s in 0..τ, F (τ - s) * ((s ^ n / (Nat.factorial n : ℝ)) : 𝔸) := by
            simpa using (intervalIntegral.integral_comp_sub_left (a := 0) (b := τ) (d := τ)
              (f := fun u => F (τ - u) * ((u ^ n / (Nat.factorial n : ℝ)) : 𝔸)))

/-- `∫₀¹ (1-u)^p du = 1/(p+1)`. -/
lemma intervalIntegral_one_sub_pow (p : ℕ) :
    (∫ u in (0 : ℝ)..(1 : ℝ), (1 - u) ^ p) = (1 : ℝ) / ((p + 1 : ℕ) : ℝ) := by
  calc
    (∫ u in (0 : ℝ)..(1 : ℝ), (1 - u) ^ p)
        = ∫ u in (0 : ℝ)..(1 : ℝ), u ^ p := by
            simpa using (intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ p)
              (a := 0) (b := 1) (d := 1))
    _ = (1 : ℝ) / ((p + 1 : ℕ) : ℝ) := by
        have hp : (p + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero p
        rw [integral_pow, one_pow, zero_pow hp]
        simp

/-- `∫₀ᵗ C · |τ|^p / p! dτ = (C / p!) · t^{p+1}/(p+1)`, for `t ≥ 0`. -/
lemma intervalIntegral_const_mul_abs_pow_div_factorial (C : ℝ) (p : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ) =
      (C / (Nat.factorial p : ℝ)) * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := by
  calc
    ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ)
        = ∫ τ in 0..t, (C / (Nat.factorial p : ℝ)) * |τ| ^ p := by
            apply intervalIntegral.integral_congr_uIoo
            intro τ _
            ring
    _ = (C / (Nat.factorial p : ℝ)) * ∫ τ in 0..t, |τ| ^ p := by
            rw [intervalIntegral.integral_const_mul]
    _ = (C / (Nat.factorial p : ℝ)) * ∫ τ in 0..t, τ ^ p := by
            congr 1
            apply intervalIntegral.integral_congr_uIoo
            intro τ hτ
            have hτ_pos : 0 < τ := by simpa [Set.uIoo, min_eq_left ht] using hτ.1
            simp [abs_of_nonneg hτ_pos.le]
    _ = (C / (Nat.factorial p : ℝ)) * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := by simp

/-- `∫₀ᵗ (C · |τ|^p / p!) · E dτ = (C / p!) · E · t^{p+1}/(p+1)`, for `t ≥ 0` and any constant
`E`. -/
lemma intervalIntegral_const_mul_abs_pow_div_factorial_mul (C E : ℝ) (p : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ) * E =
      (C / (Nat.factorial p : ℝ)) * E * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := by
  calc
    ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ) * E
        = (∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ)) * E := by
            rw [intervalIntegral.integral_mul_const]
    _ = (C / (Nat.factorial p : ℝ)) * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) * E := by
            rw [intervalIntegral_const_mul_abs_pow_div_factorial C p t ht]
    _ = (C / (Nat.factorial p : ℝ)) * E * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := by ring

/-- Integrating a factorial-polynomial majorant with a constant multiplier gives a norm
bound in any real normed space. The scalar majorant is continuous; no continuity or
interval-integrability hypothesis on `f` is required. -/
lemma norm_intervalIntegral_le_const_mul_abs_pow_div_factorial_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (C M : ℝ) (p : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hpoint : ∀ τ ∈ Set.Ioc (0 : ℝ) t,
      ‖f τ‖ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) * M) :
    ‖∫ τ in 0..t, f τ‖ ≤
      (C / (Nat.factorial p : ℝ)) * M * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := by
  calc
    ‖∫ τ in 0..t, f τ‖ ≤ ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ) * M :=
      intervalIntegral.norm_integral_le_of_norm_le ht
        (by
          filter_upwards with τ hτ
          exact hpoint τ hτ)
        ((by fun_prop : Continuous fun τ : ℝ =>
          C * |τ| ^ p / (Nat.factorial p : ℝ) * M).intervalIntegrable 0 t)
    _ = _ := intervalIntegral_const_mul_abs_pow_div_factorial_mul C M p t ht

end TrotterError
