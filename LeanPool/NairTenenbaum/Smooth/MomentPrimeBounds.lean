/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Smooth.TiltedAuxiliary
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.PSeries

/-! # Uniform prime bounds for exponential moments

The first-power terms use the logarithmic prime estimate. Higher powers are
controlled geometrically: a fixed finite set of small primes uses the growth
exponent, and large primes use the sharper `A^γ/p` ratio.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- A geometric majorant controls every tail of the local moment increment. -/
theorem localMoment_tail_le {A B ε β M q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (γ : ℕ) (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hbound : ∀ ν, tiltedRootAuxiliary A B ε β γ Q (p ^ ν) ≤ M * q ^ ν) (N : ℕ) :
    (∑' ν : ℕ, localMomentTerm A B ε β γ Q p (ν + N)) ≤ M * q ^ (N + 1) / (1 - q) := by
  have hg := (summable_geometric_of_lt_one hq₀ hq₁).mul_left (M * q ^ (N + 1))
  have hb (ν : ℕ) : localMomentTerm A B ε β γ Q p (ν + N) ≤ (M * q ^ (N + 1)) * q ^ ν := by
    refine (localMomentTerm_le_tilted hA hB γ Q p (ν + N)).trans ?_
    simpa only [Nat.add_assoc, pow_add, mul_assoc, mul_left_comm, mul_comm] using hbound (ν + N + 1)
  have hf := Summable.of_nonneg_of_le (fun ν => localMomentTerm_nonneg hA hB hβ γ Q hp (ν + N)) hb
      hg
  calc
    _ ≤ ∑' ν : ℕ, (M * q ^ (N + 1)) * q ^ ν := Summable.tsum_le_tsum hb hf hg
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq₀ hq₁]; rfl

/-- A prime-independent bound from a fixed gap below the convergence exponent. -/
theorem localMoment_higher_le_small {A B ε β σ : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hβ : 0 ≤ β) (hσ : σ < 1) (γ : ℕ)
    (hγ : (γ : ℝ) * (ε + β) ≤ σ) (Q : ℤ[X]) {p : ℕ} (hp : p.Prime)
    (C : ℕ) (hρ : ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    (∑' ν : ℕ, localMomentTerm A B ε β γ Q p (ν + 1)) ≤
      (C : ℝ) * B / (1 - (2 : ℝ) ^ (σ - 1)) := by
  let q := (2 : ℝ) ^ (σ - 1)
  have hq₀ : 0 ≤ q := by positivity
  have hq₁ : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr : auxiliaryRatio (ε + β) γ p ≤ q := by
    apply (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le)
      (show (γ : ℝ) * (ε + β) - 1 ≤ σ - 1 by linarith)).trans
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
  have hb (ν : ℕ) : tiltedRootAuxiliary A B ε β γ Q (p ^ ν) ≤ (C : ℝ) * B * q ^ ν :=
    (tiltedRootAuxiliary_prime_pow_le hA hB hε γ Q hp C ν (hρ ν)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (auxiliaryRatio_nonneg _ _ _) hr ν) (by
        positivity))
  refine (localMoment_tail_le hA (zero_le_one.trans hB) hβ γ Q hp hq₀ hq₁ hb 1).trans ?_
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hq₁.le)
  exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hq₀ hq₁.le)

/-- At large primes the higher-power tail has a summable inverse-square bound. -/
theorem localMoment_higher_le_large {A B ε β K : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hβ : 0 ≤ β) (γ : ℕ) (Q : ℤ[X]) {p : ℕ} (hp : p.Prime)
    (C : ℕ) (hρ : ∀ ν, rootCount Q (p ^ ν) ≤ C)
    (hK : 0 ≤ K) (hpow : A ^ γ * (p : ℝ) ^ ((γ : ℝ) * β) ≤ K) (hpK : 2 * K ≤ p) :
    (∑' ν : ℕ, localMomentTerm A B ε β γ Q p (ν + 1)) ≤
      2 * (C : ℝ) * B * K ^ 2 / (p : ℝ) ^ 2 := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq₀ : 0 ≤ K / p := div_nonneg hK hp₀.le
  have hq : K / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp₀).mpr (by linarith)
  have hb (ν : ℕ) : tiltedRootAuxiliary A B ε β γ Q (p ^ ν) ≤ (C : ℝ) * B * (K / p) ^ ν :=
    (tiltedRootAuxiliary_prime_pow_le_A hA hB hε γ Q hp C ν (hρ ν)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (div_le_div_of_nonneg_right hpow hp₀.le) ν) (by positivity))
  refine (localMoment_tail_le hA (zero_le_one.trans hB) hβ γ Q hp hq₀ (by linarith) hb 1).trans ?_
  calc
    _ ≤ ((C : ℝ) * B * (K / p) ^ 2) / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    _ = _ := by ring

/-- A cutoff-independent majorant for the higher-power tail. -/
noncomputable def momentHigherMajorant (B σ K : ℝ) (C n : ℕ) : ℝ :=
  (if n ≤ ⌈2 * K⌉₊ then (C : ℝ) * B / (1 - (2 : ℝ) ^ (σ - 1)) else 0) +
    (2 * (C : ℝ) * B * K ^ 2) * (n : ℝ) ^ (-2 : ℝ)

theorem momentHigherMajorant_nonneg {B σ K : ℝ} (hB : 0 ≤ B) (hσ : σ < 1) (C n : ℕ) :
    0 ≤ momentHigherMajorant B σ K C n := by
  have hd : 0 ≤ 1 - (2 : ℝ) ^ (σ - 1) := sub_nonneg.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)).le
  unfold momentHigherMajorant
  split_ifs <;> positivity

theorem momentHigherMajorant_summable (B σ K : ℝ) (C : ℕ) :
    Summable (momentHigherMajorant B σ K C) := by
  have hs : Summable (fun n : ℕ => if n ≤ ⌈2 * K⌉₊ then (C : ℝ) * B / (1 - (2 : ℝ) ^ (σ - 1)) else
      0) := by
    apply (summable_nat_add_iff (⌈2 * K⌉₊ + 1)).mp
    have he (n : ℕ) : ¬n + (⌈2 * K⌉₊ + 1) ≤ ⌈2 * K⌉₊ := by omega
    simp only [he, ite_false]
    exact summable_zero
  exact hs.add ((Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left _)

/-- The varying exponent is uniformly bounded at all primes below the cutoff. -/
theorem rpow_log_cutoff_le_exp {z κ : ℝ} (hz : 2 ≤ z) (hκ : 0 ≤ κ) (γ : ℕ)
    {p : ℕ} (hp : p.Prime) (hpz : (p : ℝ) ≤ z) :
    (p : ℝ) ^ ((γ : ℝ) * (κ / Real.log z)) ≤ Real.exp ((γ : ℝ) * κ) := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  rw [Real.rpow_def_of_pos hp₀]
  apply Real.exp_le_exp.mpr
  calc
    _ = ((γ : ℝ) * κ) * (Real.log p / Real.log z) := by ring
    _ ≤ ((γ : ℝ) * κ) * 1 := mul_le_mul_of_nonneg_left
      ((div_le_one hlz).mpr (Real.log_le_log hp₀ hpz)) (mul_nonneg (Nat.cast_nonneg γ) hκ)
    _ = _ := mul_one _

/-- The full higher-power tail is bounded by one fixed summable sequence. -/
theorem localMoment_higher_le_majorant {A B ε κ σ z : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hκ : 0 ≤ κ) (hσ : σ < 1) (hz : 2 ≤ z) (γ : ℕ)
    (hγ : (γ : ℝ) * (ε + κ / Real.log z) ≤ σ) (Q : ℤ[X]) {p : ℕ} (hp : p.Prime)
    (hpz : (p : ℝ) ≤ z) (C : ℕ) (hρ : ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    (∑' ν : ℕ, localMomentTerm A B ε (κ / Real.log z) γ Q p (ν + 1)) ≤
      momentHigherMajorant B σ (A ^ γ * Real.exp ((γ : ℝ) * κ)) C p := by
  let K := A ^ γ * Real.exp ((γ : ℝ) * κ)
  have hβ : 0 ≤ κ / Real.log z := div_nonneg hκ (Real.log_pos (by linarith : 1 < z)).le
  change _ ≤ (if p ≤ ⌈2 * K⌉₊ then (C : ℝ) * B / (1 - (2 : ℝ) ^ (σ - 1)) else 0) +
    (2 * (C : ℝ) * B * K ^ 2) * (p : ℝ) ^ (-2 : ℝ)
  by_cases hpK : p ≤ ⌈2 * K⌉₊
  · have h := localMoment_higher_le_small hA hB hε hβ hσ γ hγ Q hp C hρ
    rw [ite_eq_left hpK]
    exact h.trans (le_add_of_nonneg_right (by positivity))
  · have hpK' : 2 * K ≤ (p : ℝ) := (Nat.le_ceil (2 * K)).trans (by
    exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hpK)))
    have h := localMoment_higher_le_large hA hB hε hβ γ Q hp C hρ (show 0 ≤ K by positivity)
      (mul_le_mul_of_nonneg_left (rpow_log_cutoff_le_exp hz hκ γ hp hpz) (pow_nonneg hA γ)) hpK'
    refine h.trans_eq ?_
    simp only [ite_eq_right hpK, zero_add]
    rw [Real.rpow_neg (Nat.cast_nonneg p), Real.rpow_two]
    rfl

/-- An explicit bound independent of the cutoff and polynomial coefficients. -/
noncomputable def momentPrimeBound (A B κ σ : ℝ) (γ C : ℕ) : ℝ :=
  ((C : ℝ) * B * A ^ γ) *
    (((γ : ℝ) * κ) * Real.exp ((γ : ℝ) * κ) * Real.log 4 * (1 + (Real.log 2)⁻¹)) +
  ∑' n : ℕ, momentHigherMajorant B σ (A ^ γ * Real.exp ((γ : ℝ) * κ)) C n

/-- The complete local-error sum is bounded uniformly in `z`, provided the
tilted exponent stays a fixed distance below one. -/
theorem localMomentError_sum_uniform {A B ε κ σ z : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hκ : 0 ≤ κ) (hσ : σ < 1) (hz : 2 ≤ z) (γ : ℕ)
    (hγ : (γ : ℝ) * (ε + κ / Real.log z) ≤ σ) (Q : ℤ[X])
    (C : ℕ) (hρ : ∀ p, p.Prime → ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    (∑ p ∈ (Finset.Icc 0 ⌊z⌋₊).filter Nat.Prime,
      localMomentError A B ε (κ / Real.log z) γ Q p) ≤ momentPrimeBound A B κ σ γ C := by
  have hβ : 0 ≤ κ / Real.log z := div_nonneg hκ (Real.log_pos (by linarith : 1 < z)).le
  let S := (Finset.Icc 0 ⌊z⌋₊).filter Nat.Prime
  let K := A ^ γ * Real.exp ((γ : ℝ) * κ)
  have htail : (∑ p ∈ S, ∑' ν : ℕ, localMomentTerm A B ε (κ / Real.log z) γ Q p (ν + 1)) ≤
      ∑' n : ℕ, momentHigherMajorant B σ K C n := by
    calc
      _ ≤ ∑ p ∈ S, momentHigherMajorant B σ K C p := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpx, hpp⟩ := Finset.mem_filter.mp hp
        exact localMoment_higher_le_majorant hA hB hε hκ hσ hz γ hγ Q hpp
          ((Nat.le_floor_iff (by linarith : 0 ≤ z)).mp (Finset.mem_Icc.mp hpx).2) C (hρ p hpp)
      _ ≤ _ := (momentHigherMajorant_summable B σ K C).sum_le_tsum S
        (fun n _ => momentHigherMajorant_nonneg (zero_le_one.trans hB) hσ C n)
  have heq : (∑ p ∈ S, localMomentError A B ε (κ / Real.log z) γ Q p) =
      (∑ p ∈ S, localMomentTerm A B ε (κ / Real.log z) γ Q p 0) +
        ∑ p ∈ S, ∑' ν : ℕ, localMomentTerm A B ε (κ / Real.log z) γ Q p (ν + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    exact (localMomentTerm_summable hA hB hε hβ γ (hγ.trans_lt hσ) Q
      (Finset.mem_filter.mp hp).2 C (hρ p (Finset.mem_filter.mp hp).2)).tsum_eq_zero_add
  rw [show (∑ p ∈ (Finset.Icc 0 ⌊z⌋₊).filter Nat.Prime,
    localMomentError A B ε (κ / Real.log z) γ Q p) = ∑ p ∈ S,
    localMomentError A B ε (κ / Real.log z) γ Q p from rfl, heq]
  exact add_le_add (localMomentTerm_zero_sum_uniform hA hB hε hκ hz γ Q C
    (fun p hp => by simpa using hρ p hp 1)) htail

/-- The moment correction Euler product is uniform in the smoothness cutoff. -/
theorem localMomentError_product_uniform {A B ε κ σ z : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hκ : 0 ≤ κ) (hσ : σ < 1) (hz : 2 ≤ z) (γ : ℕ)
    (hγ : (γ : ℝ) * (ε + κ / Real.log z) ≤ σ) (Q : ℤ[X])
    (C : ℕ) (hρ : ∀ p, p.Prime → ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    (∏ p ∈ (Finset.Icc 0 ⌊z⌋₊).filter Nat.Prime,
      (1 + localMomentError A B ε (κ / Real.log z) γ Q p)) ≤
        Real.exp (momentPrimeBound A B κ σ γ C) := by
  have hβ : 0 ≤ κ / Real.log z := div_nonneg hκ (Real.log_pos (by linarith : 1 < z)).le
  calc
    _ ≤ ∏ p ∈ (Finset.Icc 0 ⌊z⌋₊).filter Nat.Prime,
        Real.exp (localMomentError A B ε (κ / Real.log z) γ Q p) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact add_nonneg zero_le_one (tsum_nonneg (fun ν =>
          localMomentTerm_nonneg hA (zero_le_one.trans hB) hβ γ Q (Finset.mem_filter.mp hp).2 ν))
      · intro p _
        simpa only [add_comm] using Real.add_one_le_exp (localMomentError A B ε (κ / Real.log z) γ
            Q p)
    _ = Real.exp (∑ p ∈ (Finset.Icc 0 ⌊z⌋₊).filter Nat.Prime,
        localMomentError A B ε (κ / Real.log z) γ Q p) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (localMomentError_sum_uniform hA hB hε hκ hσ hz γ hγ Q C hρ)

/-- The logarithmic choice of exponent stays uniformly below one at the
paper's exponential smoothness threshold. -/
theorem moment_exponent_gap {ε κ z : ℝ} (γ : ℕ) (hεγ : (γ : ℝ) * ε ≤ 1 / 8)
    (hκ : 0 ≤ κ) (hz : 2 ≤ z) (hzκ : (4 : ℝ) ^ ((γ : ℝ) * κ) ≤ z) :
    (γ : ℝ) * (ε + κ / Real.log z) ≤ 7 / 8 := by
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hl4 : (4 / 3 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    nlinarith [Real.log_two_gt_d9]
  have hγκ : 0 ≤ (γ : ℝ) * κ := mul_nonneg (Nat.cast_nonneg γ) hκ
  have hlog : ((γ : ℝ) * κ) * Real.log 4 ≤ Real.log z := by
    simpa only [Real.log_rpow (by norm_num : (0 : ℝ) < 4)] using
      Real.log_le_log (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) _) hzκ
  have hq : ((γ : ℝ) * κ) / Real.log z ≤ 3 / 4 := by
    apply (div_le_iff₀ hlz).mpr
    have h := mul_le_mul_of_nonneg_left hl4 hγκ
    nlinarith
  calc
    _ = (γ : ℝ) * ε + ((γ : ℝ) * κ) / Real.log z := by ring
    _ ≤ 1 / 8 + 3 / 4 := add_le_add hεγ hq
    _ = _ := by norm_num

/-- The uniform exponential-moment product for each actual polynomial factor.
All root-count assumptions are discharged by the proved discriminant bounds. -/
theorem PolynomialSystem.factor_moment_product_bound {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε κ z : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hκ : 0 ≤ κ)
    (hz : 2 ≤ z) (hzκ : (4 : ℝ) ^ ((P.total.natDegree : ℝ) * κ) ≤ z) (h : Fin r)
    (hεγ : (totalExponent P.exponent h : ℝ) * ε ≤ 1 / 8) :
    (∏ p ∈ (Finset.Icc 0 ⌊z⌋₊).filter Nat.Prime,
      (1 + localMomentError A B ε (κ / Real.log z) (totalExponent P.exponent h) (P.R h) p)) ≤
      Real.exp (momentPrimeBound A B κ (7 / 8) (totalExponent P.exponent h)
        (max (P.R h).natDegree (P.badDiscriminant ^ 3))) := by
  apply localMomentError_product_uniform hA hB hε hκ (by norm_num) hz
  · apply moment_exponent_gap _ hεγ hκ hz
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast P.totalExponent_le_degree h) hκ)).trans hzκ
  · exact fun p hp ν => P.factor_rootCount_prime_pow_uniform hp ν h

end NairTenenbaum
