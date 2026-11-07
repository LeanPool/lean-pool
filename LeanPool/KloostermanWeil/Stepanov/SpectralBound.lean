/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Stepanov.SpecializedCurve
public import LeanPool.KloostermanWeil.Stepanov.PointCountBridge
public import LeanPool.KloostermanWeil.Stepanov.CarlitzRoots
public import LeanPool.KloostermanWeil.Stepanov.PowerSumSpectral


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# From point counts to the spectral circle

Combines the Carlitz recurrence with Stepanov point-count estimates to bound the two
spectral roots; compare Harcos (2015), §3, equations (2)–(3).
-/

@[expose] public section

namespace KloostermanWeil.Stepanov

open scoped BigOperators
open KloostermanWeil.Carlitz

abbrev CarlitzRootIndex (p : ℕ) :=
  {m : ZMod p // m ≠ 0} × Bool

noncomputable def normalizedCarlitzSquaredRoot
    (p : ℕ) [Fact p.Prime] (c : ZMod p)
    (x : CarlitzRootIndex p) : ℂ :=
  let t := x.1.1 ^ 2 * c
  let root := if x.2 then carlitzAlpha p t else carlitzBeta p t
  root ^ 2 / (p : ℂ)

theorem natSqrt_even_primePower (p n : ℕ) :
    Nat.sqrt (p ^ (2 * n)) = p ^ n := by
  rw [show p ^ (2 * n) = (p ^ n) ^ 2 by
    rw [← pow_mul]
    congr 1
    omega]
  exact Nat.sqrt_eq' _

theorem eventually_kloostermanCurve_large
    (p : ℕ) [Fact p.Prime] :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      100 * (2 * p + 1) * (Nat.sqrt (p ^ (2 * n)) + 1) <
        p ^ (2 * n) := by
  have hp1 : 1 < p := (show p.Prime from Fact.out).one_lt
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt (200 * (2 * p + 1)) hp1
  refine ⟨n₀, fun n hn => ?_⟩
  rw [natSqrt_even_primePower]
  have hpowmono : p ^ n₀ ≤ p ^ n := Nat.pow_le_pow_right
    (show 0 < p from (show p.Prime from Fact.out).pos) hn
  have hconst : 200 * (2 * p + 1) < p ^ n := hn₀.trans_le hpowmono
  have hpownz : 0 < p ^ n := pow_pos
    (show 0 < p from (show p.Prime from Fact.out).pos) n
  have hone : 1 ≤ p ^ n := hpownz
  calc
    100 * (2 * p + 1) * (p ^ n + 1)
        ≤ 200 * (2 * p + 1) * p ^ n := by nlinarith
    _ < p ^ n * p ^ n := Nat.mul_lt_mul_of_pos_right hconst hpownz
    _ = p ^ (2 * n) := by rw [← pow_add]; congr 1; omega

theorem sum_normalizedCarlitzSquaredRoot_pow
    (p n : ℕ) [Fact p.Prime] (c : ZMod p) :
    ∑ x : CarlitzRootIndex p,
        normalizedCarlitzSquaredRoot p c x ^ n =
      (∑ m : {m : ZMod p // m ≠ 0},
        (carlitzAlpha p (m.1 ^ 2 * c) ^ (2 * n) +
          carlitzBeta p (m.1 ^ 2 * c) ^ (2 * n))) /
        (p : ℂ) ^ n := by
  rw [Fintype.sum_prod_type]
  simp only [normalizedCarlitzSquaredRoot, Fintype.sum_bool,
    ite_eq_left, Bool.false_eq_true, ite_false, div_pow, ← pow_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  rw [add_div]

theorem rootPowerSum_eq_neg_errorAggregate_sub_one
    (p n : ℕ) [Fact p.Prime] (c : ZMod p) (hc : c ≠ 0)
    (hn : n ≠ 0) :
    (∑ m : {m : ZMod p // m ≠ 0},
      (carlitzAlpha p (m.1 ^ 2 * c) ^ n +
        carlitzBeta p (m.1 ^ 2 * c) ^ n)) =
      - errorAggregate p n c - 1 := by
  rw [errorAggregate_eq_Kext_sum p n c hn]
  have hs :
      (∑ m : {m : ZMod p // m ≠ 0},
        (let : NeZero n := ⟨hn⟩
         Kext p n (m.1 ^ 2 * c))) =
      ∑ m : {m : ZMod p // m ≠ 0},
        -(carlitzAlpha p (m.1 ^ 2 * c) ^ n +
          carlitzBeta p (m.1 ^ 2 * c) ^ n) := by
    apply Finset.sum_congr rfl
    intro m hm
    have ht : m.1 ^ 2 * c ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 m.2) hc
    exact Kext_eq_neg_root_power_sum_pos p n ht hn
  rw [hs]
  rw [Finset.sum_neg_distrib]
  ring

theorem norm_natCast_sub_natCast_eq_intAbs (a b : ℕ) :
    ‖(a : ℂ) - (b : ℂ)‖ =
      ((|(a : ℤ) - (b : ℤ)| : ℤ) : ℝ) := by
  change ‖((a : ℤ) : ℂ) - ((b : ℤ) : ℂ)‖ = _
  rw [← Int.cast_sub, Complex.norm_intCast, ← Int.cast_abs]

theorem normalizedCarlitzSquaredRoot_powerSum_eventually
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ‖∑ x : CarlitzRootIndex p,
          normalizedCarlitzSquaredRoot p c x ^ n‖ ≤
        (160 * (2 * p + 1) + 2 : ℝ) := by
  obtain ⟨n₁, hn₁⟩ := eventually_kloostermanCurve_large p
  refine ⟨max n₁ 1, fun n hn => ?_⟩
  have hn1 : n₁ ≤ n := (le_max_left _ _).trans hn
  have hnpos : 0 < n := (le_max_right n₁ 1).trans hn
  have hlarge := hn₁ n hn1
  let := Fintype.ofFinite (GaloisField p (2 * n))
  have hcurve := kloostermanCurve_defect_high_extension
    p (2 * n) hpodd c hc (by omega) hlarge
  have hpoint := pointCountError_eq_errorAggregate
    p (2 * n) hpodd c hc (by omega)
  let q := p ^ (2 * n)
  let card := (hyperellipticAffinePointFinset
    (kloostermanCurvePolynomial p (2 * n) c)).card
  let S : ℂ := ∑ m : {m : ZMod p // m ≠ 0},
    (carlitzAlpha p (m.1 ^ 2 * c) ^ (2 * n) +
      carlitzBeta p (m.1 ^ 2 * c) ^ (2 * n))
  have hS : S = (q : ℂ) - (card : ℂ) - 1 := by
    have hroot :=
      rootPowerSum_eq_neg_errorAggregate_sub_one p (2 * n) c hc (by omega)
    dsimp [S, q, card] at hroot ⊢
    rw [← hpoint] at hroot
    linear_combination hroot
  have hcurve' : |(card : ℤ) - (q : ℤ)| <
      (80 * (2 * p + 1) * (p ^ n + 1) + 1 : ℕ) := by
    simpa [card, q, natSqrt_even_primePower] using hcurve
  have hcurveR : ((|(card : ℤ) - (q : ℤ)| : ℤ) : ℝ) <
      (80 * (2 * p + 1) * (p ^ n + 1) + 1 : ℕ) := by
    exact_mod_cast hcurve'
  rw [Int.cast_abs, Int.cast_sub] at hcurveR
  push_cast at hcurveR
  have hSnorm : ‖S‖ ≤
      (160 * (2 * p + 1) + 2 : ℝ) * p ^ n := by
    rw [hS]
    apply le_of_lt
    calc
      ‖(q : ℂ) - (card : ℂ) - 1‖
          ≤ ‖(q : ℂ) - (card : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ((|(q : ℤ) - (card : ℤ)| : ℤ) : ℝ) + 1 := by
        rw [norm_natCast_sub_natCast_eq_intAbs]
        simp
      _ = ((|(card : ℤ) - (q : ℤ)| : ℤ) : ℝ) + 1 := by
        rw [abs_sub_comm]
      _ < (80 * (2 * p + 1) * (p ^ n + 1) + 1 : ℕ) + 1 := by
        push_cast
        nlinarith [hcurveR]
      _ ≤ (160 * (2 * p + 1) + 2 : ℝ) * p ^ n := by
        have hpown : (1 : ℝ) ≤ p ^ n := by
          exact_mod_cast (show 1 ≤ p ^ n from
            Nat.one_le_pow n p (show 0 < p from
              (show p.Prime from Fact.out).pos))
        push_cast
        nlinarith
  rw [sum_normalizedCarlitzSquaredRoot_pow]
  rw [norm_div, norm_pow, Complex.norm_natCast]
  have hpownpos : (0 : ℝ) < (p : ℝ) ^ n := by
    exact pow_pos (by exact_mod_cast
      (show 0 < p from (show p.Prime from Fact.out).pos)) n
  exact (div_le_iff₀ hpownpos).2 hSnorm

theorem normalizedCarlitzSquaredRoot_norm_le_one
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0) (x : CarlitzRootIndex p) :
    ‖normalizedCarlitzSquaredRoot p c x‖ ≤ 1 := by
  obtain ⟨n₀, hpower⟩ :=
    normalizedCarlitzSquaredRoot_powerSum_eventually p hpodd c hc
  apply norm_le_one_of_power_sums_eventually
    (normalizedCarlitzSquaredRoot p c)
    (160 * (2 * p + 1) + 2 : ℝ)
    (by
      have hp0 : (0 : ℝ) ≤ p := by positivity
      nlinarith)
    n₀ hpower x

theorem carlitzAlpha_norm_sq_le_prime
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0)
    (m : {m : ZMod p // m ≠ 0}) :
    ‖carlitzAlpha p (m.1 ^ 2 * c)‖ ^ 2 ≤ p := by
  have h := normalizedCarlitzSquaredRoot_norm_le_one
    p hpodd c hc (m, true)
  change ‖carlitzAlpha p (m.1 ^ 2 * c) ^ 2 / (p : ℂ)‖ ≤ 1 at h
  rw [norm_div, norm_pow, Complex.norm_natCast] at h
  exact (div_le_one (by exact_mod_cast
    (show 0 < p from (show p.Prime from Fact.out).pos))).mp h

theorem carlitzBeta_norm_sq_le_prime
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0)
    (m : {m : ZMod p // m ≠ 0}) :
    ‖carlitzBeta p (m.1 ^ 2 * c)‖ ^ 2 ≤ p := by
  have h := normalizedCarlitzSquaredRoot_norm_le_one
    p hpodd c hc (m, false)
  change ‖carlitzBeta p (m.1 ^ 2 * c) ^ 2 / (p : ℂ)‖ ≤ 1 at h
  rw [norm_div, norm_pow, Complex.norm_natCast] at h
  exact (div_le_one (by exact_mod_cast
    (show 0 < p from (show p.Prime from Fact.out).pos))).mp h


end KloostermanWeil.Stepanov
