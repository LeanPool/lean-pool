/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Smooth.SmoothWeightSum

/-! # Euler products on a band of primes

A logarithmic prime estimate bounds the first powers on `w < p ≤ z`.
When `γ ε < 1/2`, all higher powers have a convergent power-series majorant,
uniform in both endpoints. This gives the prime-band constant needed for the
last truncation step in Lemma 2.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- Integers supported on the primes in a specified band. -/
noncomputable def primeBandNumbers (w z : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊z⌋₊).filter (fun p => w < (p : ℝ))

/-- An elementary bound for the reciprocal prime sum on a band. -/
theorem primeBand_reciprocal_sum_le {w z : ℝ} (hw : 2 ≤ w) (hz : 2 ≤ z) :
    (∑ p ∈ (primeBandNumbers w z).filter Nat.Prime, (p : ℝ)⁻¹) ≤
      Real.log 4 * (1 + Real.log z) / Real.log w := by
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlocal (p : ℕ) (hp : p ∈ (primeBandNumbers w z).filter Nat.Prime) :
      (p : ℝ)⁻¹ ≤ (Real.log p / p) / Real.log w := by
    have hwp := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hp₀ : (0 : ℝ) < p := by linarith
    have hlog : Real.log w ≤ Real.log p := Real.log_le_log (by linarith) hwp.le
    apply (le_div_iff₀ hlw).mpr
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_right hlog (inv_nonneg.mpr hp₀.le)
  calc
    _ ≤ ∑ p ∈ (primeBandNumbers w z).filter Nat.Prime, (Real.log p / p) / Real.log w :=
      Finset.sum_le_sum hlocal
    _ = (∑ p ∈ (primeBandNumbers w z).filter Nat.Prime, Real.log p / p) / Real.log w := by
      rw [Finset.sum_div]
    _ ≤ primeLogSum z / Real.log w := by
      apply div_le_div_of_nonneg_right _ hlw.le
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hp, hprime⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, hprime⟩
      · intro p hp _
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le))
          (Nat.cast_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_right (primeLogSum_le hz) hlw.le

/-- Tail of the un-tilted local root auxiliary under a geometric majorant. -/
theorem rootAuxiliary_geometric_tail_le {A B ε M q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (γ : ℕ) (Q : ℤ[X]) (p : ℕ) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hbound : ∀ ν, rootAuxiliary A B ε γ Q (p ^ ν) ≤ M * q ^ ν) (N : ℕ) :
    (∑' ν : ℕ, rootAuxiliary A B ε γ Q (p ^ (ν + N))) ≤ M * q ^ N / (1 - q) := by
  have hg := (summable_geometric_of_lt_one hq₀ hq₁).mul_left (M * q ^ N)
  have hb (ν : ℕ) : rootAuxiliary A B ε γ Q (p ^ (ν + N)) ≤ (M * q ^ N) * q ^ ν := by
    simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using hbound (ν + N)
  have hf := Summable.of_nonneg_of_le (fun _ => rootAuxiliary_nonneg hA hB γ Q _) hb hg
  calc
    _ ≤ ∑' ν : ℕ, (M * q ^ N) * q ^ ν := Summable.tsum_le_tsum hb hf hg
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq₀ hq₁]; rfl

/-- A summable power bound for all powers of a prime starting at the square. -/
theorem rootAuxiliary_higher_le {A B ε σ : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hσ : σ < 1) (γ : ℕ) (hγ : (γ : ℝ) * ε ≤ σ)
    (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) (C : ℕ)
    (hρ : ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    (∑' ν : ℕ, rootAuxiliary A B ε γ Q (p ^ (ν + 2))) ≤
      ((C : ℝ) * B / (1 - (2 : ℝ) ^ (σ - 1))) * (p : ℝ) ^ (2 * σ - 2) := by
  let q := (p : ℝ) ^ (σ - 1)
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq₀ : 0 ≤ q := by positivity
  have hq₁ : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hp.one_lt) (by linarith)
  have hq₂ : q ≤ (2 : ℝ) ^ (σ - 1) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
  have hr : auxiliaryRatio ε γ p ≤ q :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) (by linarith)
  have hb (ν : ℕ) : rootAuxiliary A B ε γ Q (p ^ ν) ≤ (C : ℝ) * B * q ^ ν :=
    (rootAuxiliary_prime_pow_le hA hB hε γ Q hp C ν (hρ ν)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (auxiliaryRatio_nonneg _ _ _) hr ν) (by
        positivity))
  have hd : 0 < 1 - (2 : ℝ) ^ (σ - 1) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  calc
    _ ≤ (C : ℝ) * B * q ^ 2 / (1 - q) :=
      rootAuxiliary_geometric_tail_le hA (zero_le_one.trans hB) γ Q p hq₀ hq₁ hb 2
    _ ≤ (C : ℝ) * B * q ^ 2 / (1 - (2 : ℝ) ^ (σ - 1)) :=
      div_le_div_of_nonneg_left (by positivity) hd (by linarith)
    _ = _ := by
      have hpow : q ^ 2 = (p : ℝ) ^ (2 * σ - 2) := by
        dsimp only [q]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp₀.le]
        congr 1
        ring
      rw [hpow]
      ring

/-- A summable majorant for higher prime-power root contributions. -/
noncomputable def rootHigherMajorant (B σ : ℝ) (C n : ℕ) : ℝ :=
  ((C : ℝ) * B / (1 - (2 : ℝ) ^ (σ - 1))) * (n : ℝ) ^ (2 * σ - 2)

theorem rootHigherMajorant_nonneg {B σ : ℝ} (hB : 0 ≤ B) (hσ : σ < 1) (C n : ℕ) :
    0 ≤ rootHigherMajorant B σ C n := by
  have hd : 0 ≤ 1 - (2 : ℝ) ^ (σ - 1) := sub_nonneg.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)).le
  exact mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg C) hB) hd)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem rootHigherMajorant_summable (B : ℝ) {σ : ℝ} (hσ : σ < 1 / 2) (C : ℕ) :
    Summable (rootHigherMajorant B σ C) :=
  (Real.summable_nat_rpow.mpr (by linarith : 2 * σ - 2 < -1)).mul_left _

/-- The higher prime powers have a bound independent of the prime set. -/
theorem rootAuxiliary_higher_sum_le {A B ε σ : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hσ : σ < 1 / 2) (γ : ℕ) (hγ : (γ : ℝ) * ε ≤ σ)
    (Q : ℤ[X]) (C : ℕ) (hρ : ∀ p, p.Prime → ∀ ν, rootCount Q (p ^ ν) ≤ C) (s : Finset ℕ) :
    (∑ p ∈ s.filter Nat.Prime, ∑' ν : ℕ, rootAuxiliary A B ε γ Q (p ^ (ν + 2))) ≤
      ∑' n : ℕ, rootHigherMajorant B σ C n := by
  calc
    _ ≤ ∑ p ∈ s.filter Nat.Prime, rootHigherMajorant B σ C p :=
      Finset.sum_le_sum (fun p hp => rootAuxiliary_higher_le hA hB hε (by linarith) γ hγ Q
        (Finset.mem_filter.mp hp).2 C (hρ p (Finset.mem_filter.mp hp).2))
    _ ≤ _ := (rootHigherMajorant_summable B hσ C).sum_le_tsum _
      (fun n _ => rootHigherMajorant_nonneg (zero_le_one.trans hB) (by linarith) C n)

/-- The prime-band Euler-product bound depends only on the logarithm ratio. -/
noncomputable def primeBandBound (A B σ L : ℝ) (γ C : ℕ) : ℝ :=
  Real.exp (((C : ℝ) * B * A ^ γ) * Real.log 4 * (L + (Real.log 2)⁻¹) +
    ∑' n : ℕ, rootHigherMajorant B σ C n)

theorem rootAuxiliary_primeBand_product_le {A B ε σ L w z : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hσ : σ < 1 / 2)
    (hw : 2 ≤ w) (hz : 2 ≤ z) (hlog : Real.log z / Real.log w ≤ L)
    (γ : ℕ) (hγ : (γ : ℝ) * ε ≤ σ) (Q : ℤ[X]) (C : ℕ)
    (hρ : ∀ p, p.Prime → ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    (∏ p ∈ (primeBandNumbers w z).filter Nat.Prime,
      ∑' ν : ℕ, rootAuxiliary A B ε γ Q (p ^ ν)) ≤ primeBandBound A B σ L γ C := by
  have hσ₁ : σ < 1 := by linarith
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let T := (primeBandNumbers w z).filter Nat.Prime
  have hsum (p : ℕ) (hp : p ∈ T) := rootAuxiliary_prime_pow_summable hA hB hε γ
    (hγ.trans_lt hσ₁) Q (Finset.mem_filter.mp hp).2 C (hρ p (Finset.mem_filter.mp hp).2)
  have heq (p : ℕ) (hp : p ∈ T) : (∑' ν : ℕ, rootAuxiliary A B ε γ Q (p ^ ν)) =
      1 + (rootAuxiliary A B ε γ Q p + ∑' ν : ℕ, rootAuxiliary A B ε γ Q (p ^ (ν + 2))) := by
    rw [(hsum p hp).tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr (hsum p hp)).tsum_eq_zero_add]
    simp only [pow_zero, rootAuxiliary_one, zero_add, pow_one, Nat.add_assoc]
  have hrecip : (∑ p ∈ T, (p : ℝ)⁻¹) ≤ Real.log 4 * (L + (Real.log 2)⁻¹) := by
    refine (primeBand_reciprocal_sum_le hw hz).trans ?_
    have hi : (Real.log w)⁻¹ ≤ (Real.log 2)⁻¹ :=
      inv_le_inv₀ hlw hl2 |>.mpr (Real.log_le_log (by norm_num) hw)
    calc
      _ = Real.log 4 * (Real.log z / Real.log w + (Real.log w)⁻¹) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hlog hi) (Real.log_nonneg (by norm_num))
  have hfirst : (∑ p ∈ T, rootAuxiliary A B ε γ Q p) ≤
      ((C : ℝ) * B * A ^ γ) * (Real.log 4 * (L + (Real.log 2)⁻¹)) := by
    calc
      _ ≤ ∑ p ∈ T, ((C : ℝ) * B * A ^ γ) * (p : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        have H := rootAuxiliary_prime_pow_le_A hA hB hε γ Q (Finset.mem_filter.mp hp).2 C 1
          (hρ p (Finset.mem_filter.mp hp).2 1)
        simpa only [pow_one, div_eq_mul_inv, mul_assoc] using H
      _ = ((C : ℝ) * B * A ^ γ) * ∑ p ∈ T, (p : ℝ)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hrecip (by positivity)
  calc
    _ ≤ ∏ p ∈ T, Real.exp (rootAuxiliary A B ε γ Q p +
        ∑' ν : ℕ, rootAuxiliary A B ε γ Q (p ^ (ν + 2))) := by
      apply Finset.prod_le_prod₀ (fun _ _ => tsum_nonneg (fun _ => rootAuxiliary_nonneg hA
          (zero_le_one.trans hB) _ _ _))
      intro p hp
      rw [heq p hp]
      simpa only [add_comm] using Real.add_one_le_exp
        (rootAuxiliary A B ε γ Q p + ∑' ν : ℕ, rootAuxiliary A B ε γ Q (p ^ (ν + 2)))
    _ = Real.exp ((∑ p ∈ T, rootAuxiliary A B ε γ Q p) +
        ∑ p ∈ T, ∑' ν : ℕ, rootAuxiliary A B ε γ Q (p ^ (ν + 2))) := by
      rw [← Real.exp_sum, Finset.sum_add_distrib]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have H := add_le_add hfirst (rootAuxiliary_higher_sum_le hA hB hε hσ γ hγ Q C hρ
        (primeBandNumbers w z))
      simpa only [mul_assoc] using H

end NairTenenbaum
