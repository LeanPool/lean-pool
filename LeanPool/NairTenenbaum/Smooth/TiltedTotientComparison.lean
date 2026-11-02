/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Smooth.RootSmoothTail

/-! # Totient comparison after exponential tilting

The corrected comparison remains uniform when the arithmetic weight is tilted
by a logarithmic moment. A fixed gap below the local convergence exponent
bounds the comparison kernel by a summable power of the prime.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- Uniform geometric bound for the positive prime-power tail of a tilted
auxiliary. Its exponent may vary as long as it stays below `σ < 1`. -/
theorem tiltedRootAuxiliary_tail_uniform {A B ε β σ : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hσ : σ < 1) (γ : ℕ) (hγ : (γ : ℝ) * (ε + β) ≤ σ)
    (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) (C : ℕ)
    (hρ : ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    (∑' ν : ℕ, tiltedRootAuxiliary A B ε β γ Q (p ^ (ν + 1))) ≤
      (C : ℝ) * B * (p : ℝ) ^ (σ - 1) / (1 - (2 : ℝ) ^ (σ - 1)) := by
  let q := (p : ℝ) ^ (σ - 1)
  have hq₀ : 0 ≤ q := by positivity
  have hq₁ : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hp.one_lt) (by linarith)
  have hq₂ : q ≤ (2 : ℝ) ^ (σ - 1) := Real.rpow_le_rpow_of_nonpos
    (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
  have hr : auxiliaryRatio (ε + β) γ p ≤ q :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) (by linarith)
  have hb (ν : ℕ) : tiltedRootAuxiliary A B ε β γ Q (p ^ (ν + 1)) ≤
      ((C : ℝ) * B * q) * q ^ ν := by
    have H := (tiltedRootAuxiliary_prime_pow_le hA hB hε γ Q hp C (ν + 1) (hρ _)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (auxiliaryRatio_nonneg _ _ _) hr _) (by positivity))
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using H
  have hg := (summable_geometric_of_lt_one hq₀ hq₁).mul_left ((C : ℝ) * B * q)
  have hs := Summable.of_nonneg_of_le
    (fun _ => tiltedRootAuxiliary_nonneg hA (zero_le_one.trans hB) γ Q _) hb hg
  have hd : 0 < 1 - (2 : ℝ) ^ (σ - 1) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  calc
    _ ≤ ∑' ν : ℕ, ((C : ℝ) * B * q) * q ^ ν := Summable.tsum_le_tsum hb hs hg
    _ = ((C : ℝ) * B * q) / (1 - q) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq₀ hq₁]; rfl
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hd (by linarith)

/-- The weighted prime error has one additional reciprocal prime from the twist. -/
theorem tilted_kernelLocalError_le {A B ε β σ L : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hσ : σ < 1) (hL : 0 ≤ L) (γ : ℕ)
    (hγ : (γ : ℝ) * (ε + β) ≤ σ) (Q : ℤ[X]) {l : ℕ → ℝ}
    {p : ℕ} (hp : p.Prime) (hl : l p ≤ L / p) (C : ℕ)
    (hρ : ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    kernelLocalError (tiltedRootAuxiliary A B ε β γ Q) l p ≤
      (L * C * B / (1 - (2 : ℝ) ^ (σ - 1))) * (p : ℝ) ^ (σ - 2) := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold kernelLocalError
  calc
    _ ≤ (L / p) * ((C : ℝ) * B * (p : ℝ) ^ (σ - 1) / (1 - (2 : ℝ) ^ (σ - 1))) :=
      mul_le_mul hl (tiltedRootAuxiliary_tail_uniform hA hB hε hσ γ hγ Q hp C hρ)
        (tsum_nonneg (fun _ => tiltedRootAuxiliary_nonneg hA (zero_le_one.trans hB) _ _ _))
        (div_nonneg hL hp₀.le)
    _ = _ := by
      have he : (p : ℝ) ^ (σ - 2) = (p : ℝ) ^ (σ - 1) / p := by
        rw [show σ - 2 = (σ - 1) - 1 by ring, Real.rpow_sub hp₀, Real.rpow_one]
      rw [he]
      ring

/-- Uniform summability and total bound for the tilted comparison kernel. -/
theorem tilted_kernelLocalError_summable_bound {A B ε β σ L : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hσ : σ < 1) (hL : 0 ≤ L) (γ : ℕ)
    (hγ : (γ : ℝ) * (ε + β) ≤ σ) (Q : ℤ[X]) {l : ℕ → ℝ}
    (hl₀ : ∀ p, 0 ≤ l p) (hl : ∀ p, p.Prime → l p ≤ L / p) (C : ℕ)
    (hρ : ∀ p, p.Prime → ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    Summable (fun p : Nat.Primes => kernelLocalError (tiltedRootAuxiliary A B ε β γ Q) l p) ∧
      (∑' p : Nat.Primes, kernelLocalError (tiltedRootAuxiliary A B ε β γ Q) l p) ≤
        (L * C * B / (1 - (2 : ℝ) ^ (σ - 1))) * ∑' n : ℕ, (n : ℝ) ^ (σ - 2) := by
  let K := L * C * B / (1 - (2 : ℝ) ^ (σ - 1))
  have hK : 0 ≤ K := div_nonneg (by positivity) (sub_nonneg.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)).le)
  have hs : Summable (fun n : ℕ => K * (n : ℝ) ^ (σ - 2)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left K
  have hnonneg := fun p : Nat.Primes => kernelLocalError_nonneg
    (tiltedRootAuxiliary_nonneg (ε := ε) (β := β) hA (zero_le_one.trans hB) γ Q) hl₀ p
  have hbound := fun p : Nat.Primes => tilted_kernelLocalError_le hA hB hε hσ hL γ hγ Q
    p.prop (hl p p.prop) C (hρ p p.prop)
  have hs' : Summable (fun p : Nat.Primes => kernelLocalError (tiltedRootAuxiliary A B ε β γ Q) l
      p) :=
    Summable.of_nonneg_of_le hnonneg hbound (hs.comp_injective Subtype.val_injective)
  refine ⟨hs', ?_⟩
  calc
    _ ≤ ∑' p : Nat.Primes, K * (p : ℕ) ^ (σ - 2) :=
      Summable.tsum_le_tsum hbound hs' (hs.comp_injective Subtype.val_injective)
    _ ≤ ∑' n : ℕ, K * (n : ℝ) ^ (σ - 2) :=
      tsum_comp_le_tsum_of_inj hs (fun n => mul_nonneg hK (by positivity)) Subtype.val_injective
    _ = _ := tsum_mul_left

/-- The comparison constant for totient weights after exponential tilting. -/
noncomputable def tiltedTotientBound (B σ : ℝ) (g C : ℕ) : ℝ :=
  Real.exp (((2 * ((2 : ℝ) ^ g - 1)) * C * B / (1 - (2 : ℝ) ^ (σ - 1))) *
    ∑' n : ℕ, (n : ℝ) ^ (σ - 2))

/-- Multiplying the tuple weight by a moment tilts its coprime majorant by the
same amount. -/
theorem Admissible.rootTupleWeight_moment_mul_le {k r : ℕ} {A B ε β : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (γ : Fin k → Fin r → ℕ) (Q : Fin r → ℤ[X]) (a b : Tuple r)
    (hab : ∀ i j, Nat.Coprime (a i) (b j)) :
    rootTupleWeight γ F Q (a * b) * (weightedMass γ (a * b) : ℝ) ^ β ≤
      (∏ i, tiltedRootAuxiliary A B ε β (totalExponent γ i) (Q i) (a i)) *
        (rootTupleWeight γ F Q b * (weightedMass γ b : ℝ) ^ β) := by
  have H := mul_le_mul_of_nonneg_right (hF.rootTupleWeight_mul_le hA hB γ Q a b hab)
    (Real.rpow_nonneg (Nat.cast_nonneg (weightedMass γ (a * b))) β)
  refine H.trans_eq ?_
  rw [weightedMass_mul, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
  have heq : (∏ i, tiltedRootAuxiliary A B ε β (totalExponent γ i) (Q i) (a i)) =
      (∏ i, rootAuxiliary A B ε (totalExponent γ i) (Q i) (a i)) * (weightedMass γ a : ℝ) ^ β := by
    simp only [tiltedRootAuxiliary, Finset.prod_mul_distrib, weightedMass_rpow]
  rw [heq]
  ring

/-- Corrected totient comparison for the tilted weight on any closed finite
domain of dagger tuples. The constant is uniform in the moment exponent. -/
theorem tilted_totient_comparison {k r : ℕ} {A B ε β σ : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hσ : σ < 1)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, (totalExponent γ i : ℝ) * (ε + β) ≤ σ)
    (Q : Fin r → ℤ[X]) (C : Fin r → ℕ)
    (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i)
    (g D : ℕ) (S : Finset (Tuple r)) (N : ℕ+)
    (hbox : ∀ n ∈ S, ∀ i, n i ≤ N) (hdagger : ∀ n ∈ S, Dagger D n)
    (hrest : ∀ n ∈ S, ∀ t ∈ unitaryChoices n, tupleUnitaryRest n t ∈ S) :
    (∑ n ∈ S, (rootTupleWeight γ F Q n * (weightedMass γ n : ℝ) ^ β) *
        ∏ i, totientTwist g (n i)) ≤
      (∏ i, tiltedTotientBound B σ g (C i)) *
        ∑ n ∈ S, rootTupleWeight γ F Q n * (weightedMass γ n : ℝ) ^ β := by
  let U := fun i => tiltedRootAuxiliary A B ε β (totalExponent γ i) (Q i)
  let l := fun (_i : Fin r) p => |totientTwist g p - 1|
  have hloc (i : Fin r) := tilted_kernelLocalError_summable_bound hA hB hε hσ
    (show 0 ≤ 2 * ((2 : ℝ) ^ g - 1) from mul_nonneg (by norm_num)
      (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))) _ (hγ i) (Q i)
    (fun p => abs_nonneg (totientTwist g p - 1)) (fun _ hp => totientTwist_prime_sub_one_le g hp)
    (C i) (hρ i)
  have hw : ∀ n, 0 ≤ rootTupleWeight γ F Q n * (weightedMass γ n : ℝ) ^ β :=
    fun n => mul_nonneg (rootTupleWeight_nonneg γ hF.nonneg Q n) (Real.rpow_nonneg
        (Nat.cast_nonneg _) β)
  have H := tuple_comparison_uniform hw
    (show ∀ i, U i 0 = 0 by intro i; simp [U, tiltedRootAuxiliary, rootAuxiliary])
    (fun i => tiltedRootAuxiliary_one A B ε β _ _)
    (fun i => tiltedRootAuxiliary_nonneg hA (zero_le_one.trans hB) _ _)
    (fun i p => abs_nonneg (totientTwist g p - 1))
    (fun i m n h => tiltedRootAuxiliary_mul A B ε β _ _ h)
    (fun i p hp => tiltedRootAuxiliary_prime_pow_summable hA hB hε _ ((hγ i).trans_lt hσ) _ hp (C
        i) (hρ i p hp))
    (fun i => (hloc i).1) S N hbox hrest (by
      intro n hn t _
      have H := hF.rootTupleWeight_moment_mul_le (β := β) hA hB γ Q
        (tupleUnitaryPart n t) (tupleUnitaryRest n t) ((hdagger n hn).unitary_cross_coprime t)
      simpa only [tupleUnitaryPart_mul_rest] using H)
  have H' : (∑ n ∈ S, (rootTupleWeight γ F Q n * (weightedMass γ n : ℝ) ^ β) *
      ∏ i, totientTwist g (n i)) ≤
        (∏ i, Real.exp (∑' p : Nat.Primes, kernelLocalError (U i) (l i) p)) *
          ∑ n ∈ S, rootTupleWeight γ F Q n * (weightedMass γ n : ℝ) ^ β := by
    simpa only [l, ← totientTwist_eq_radicalProduct g (PNat.ne_zero _)] using H
  refine H'.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun n _ => hw n)))
  apply Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
  intro i _
  exact Real.exp_le_exp.mpr (hloc i).2

end NairTenenbaum
