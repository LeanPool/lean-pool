/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexFactorialLogBounds
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Entropy.ComplexFiniteEntropy
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Entropy.ComplexEntropyContinuity
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.ComplexRationalTypes
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.ComplexTypeCounting
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation

open Filter
open scoped BigOperators Topology

variable {A : Type*} [Fintype A]

theorem log_multinomial (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      Real.log (Nat.factorial (∑ a, counts a) : ℝ) -
        ∑ a, Real.log (Nat.factorial (counts a) : ℝ) := by
  have hspec :
      (∏ a, (Nat.factorial (counts a) : ℝ)) *
          (Nat.multinomial Finset.univ counts : ℝ) =
        (Nat.factorial (∑ a, counts a) : ℝ) := by
    exact_mod_cast Nat.multinomial_spec Finset.univ counts
  have hprod : (∏ a, (Nat.factorial (counts a) : ℝ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun a _ => by positivity)
  have hmulti : (Nat.multinomial Finset.univ counts : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ counts))
  have hlog := congrArg Real.log hspec
  rw [Real.log_mul hprod hmulti,
    Real.log_prod (s := Finset.univ) (f := fun a => (Nat.factorial (counts a) : ℝ))
      (fun a _ => by positivity)] at hlog
  linarith

private theorem entropyTerm_div_scalar (x y : ℝ) :
    entropyTerm (x / y) = entropyTerm x / y + (x / y) * Real.log y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [entropyTerm, Real.log_div hx hy]
  unfold entropyTerm
  ring

theorem finiteEntropy_nat_normalize (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) /
          (∑ a, counts a : ℕ) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  unfold finiteEntropy
  simp only [entropyTerm_div_scalar]
  simp only [entropyTerm, neg_mul,
    Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
    Finset.sum_neg_distrib]
  rw [← Nat.cast_sum, div_self hD']
  ring

theorem log_multinomial_eq_main_add_remainder (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      (∑ a, counts a : ℕ) * Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) +
        factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  rw [log_multinomial]
  unfold factorialLogRemainder
  simp only [Finset.sum_sub_distrib, ← Nat.cast_sum]
  ring

theorem log_multinomial_eq_entropy_add_remainder (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  rw [log_multinomial_eq_main_add_remainder, finiteEntropy_nat_normalize counts hD,
    mul_sub, mul_div_cancel₀ _ hD']

theorem log_multinomial_sub_entropy_eq_remainder (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  by_cases hD : 0 < ∑ a, counts a
  · rw [log_multinomial_eq_entropy_add_remainder counts hD]
    ring
  · have hzero : (∑ a, counts a) = 0 := Nat.eq_zero_of_not_pos hD
    have hc : ∀ a, counts a = 0 := by
      intro a
      have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      rw [hzero] at hle
      exact Nat.eq_zero_of_le_zero hle
    simp [hc, Nat.multinomial]

theorem abs_log_multinomial_sub_entropy_le (counts : A → ℕ) :
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  rw [log_multinomial_sub_entropy_eq_remainder]
  have hsum_nonneg : 0 ≤ ∑ a, factorialLogRemainder (counts a) :=
    Finset.sum_nonneg (fun a _ => factorialLogRemainder_nonneg (counts a))
  have heach (a : A) : factorialLogRemainder (counts a) ≤
      1 + Real.log ((∑ b, counts b) + 1 : ℕ) := by
    refine (factorialLogRemainder_le_one_add_log (counts a)).trans ?_
    apply add_le_add_right
    apply Real.log_le_log
    · positivity
    · have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      exact_mod_cast Nat.add_le_add_right hle 1
  calc
    |factorialLogRemainder (∑ a, counts a) - ∑ a, factorialLogRemainder (counts a)| ≤
        |factorialLogRemainder (∑ a, counts a)| +
          |∑ a, factorialLogRemainder (counts a)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (factorialLogRemainder (∑ a, counts a))
          (-(∑ a, factorialLogRemainder (counts a)))
    _ = factorialLogRemainder (∑ a, counts a) +
        ∑ a, factorialLogRemainder (counts a) := by
      rw [abs_of_nonneg (factorialLogRemainder_nonneg _), abs_of_nonneg hsum_nonneg]
    _ ≤ (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) +
        ∑ _a : A, (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) :=
      add_le_add (factorialLogRemainder_le_one_add_log _)
        (Finset.sum_le_sum (fun a _ => heach a))
    _ = ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem abs_log_multinomial_div_sub_entropy_le (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) / (∑ a, counts a : ℕ) -
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts a) + 1 : ℕ)) / (∑ a, counts a : ℕ)) := by
  have hD' : (0 : ℝ) < (∑ a, counts a : ℕ) := Nat.cast_pos.mpr hD
  calc
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) / (∑ a, counts a : ℕ) -
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| =
        |(Real.log (Nat.multinomial Finset.univ counts : ℝ) -
          (∑ a, counts a : ℕ) *
            finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))) /
              (∑ a, counts a : ℕ)| := by
      rw [sub_div, mul_div_cancel_left₀ _ hD'.ne']
    _ = |Real.log (Nat.multinomial Finset.univ counts : ℝ) -
          (∑ a, counts a : ℕ) *
            finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| /
              (∑ a, counts a : ℕ) := by
      rw [abs_div, abs_of_pos hD']
    _ ≤ ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts a) + 1 : ℕ)) / (∑ a, counts a : ℕ)) := by
      simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (abs_log_multinomial_sub_entropy_le counts) hD'.le

private theorem tendsto_one_add_log_succ_div :
    Tendsto (fun n : ℕ => (1 + Real.log (n + 1 : ℕ)) / (n : ℝ))
      atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hconstant : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hshift := Real.tendsto_log_nat_add_one_sub_log.div_atTop hnat
  have hsum : Tendsto
      (fun n : ℕ => (1 : ℝ) / n +
        ((Real.log ((n : ℝ) + 1) - Real.log n) / n + Real.log n / n))
      atTop (𝓝 0) := by
    simpa using hconstant.add (hshift.add hlog)
  apply hsum.congr
  intro n
  push_cast
  ring

theorem tendsto_log_multinomial_div_sub_entropy {I : Type*} {l : Filter I}
    (counts : I → A → ℕ)
    (htotal : Tendsto (fun i => ∑ a, counts i a) l atTop) :
    Tendsto
      (fun i => Real.log (Nat.multinomial Finset.univ (counts i) : ℝ) /
          (∑ a, counts i a : ℕ) -
        finiteEntropy (fun a => (counts i a : ℝ) / (∑ a, counts i a : ℕ)))
      l (𝓝 0) := by
  have hbound : Tendsto
      (fun i => ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts i a) + 1 : ℕ)) / (∑ a, counts i a : ℕ)))
      l (𝓝 0) := by
    simpa using (tendsto_one_add_log_succ_div.comp htotal).const_mul
      ((Fintype.card A : ℝ) + 1)
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [htotal.eventually (eventually_gt_atTop (0 : ℕ))] with i hi
  simpa only [Real.norm_eq_abs] using
    abs_log_multinomial_div_sub_entropy_le (counts i) hi

theorem tendsto_log_multinomial_of_empirical_tendsto {I : Type*} {l : Filter I}
    (counts : I → A → ℕ) (p : A → ℝ)
    (htotal : Tendsto (fun i => ∑ a, counts i a) l atTop)
    (hmass : ∀ a, Tendsto
      (fun i => (counts i a : ℝ) / (∑ b, counts i b : ℕ)) l (𝓝 (p a))) :
    Tendsto
      (fun i => Real.log (Nat.multinomial Finset.univ (counts i) : ℝ) /
        (∑ a, counts i a : ℕ))
      l (𝓝 (finiteEntropy p)) := by
  have herror := tendsto_log_multinomial_div_sub_entropy counts htotal
  have hentropy := tendsto_finiteEntropy_of_tendsto hmass
  simpa only [zero_add, sub_add_cancel] using herror.add hentropy

private theorem mul_log_mul (x y : ℝ) :
    (x * y) * Real.log (x * y) =
      (x * Real.log x) * y + x * (y * Real.log y) := by
  calc
    (x * y) * Real.log (x * y) = -entropyTerm (x * y) := by
      simp [entropyTerm]
    _ = -(y * entropyTerm x + x * entropyTerm y) := by
      rw [entropyTerm_mul]
    _ = (x * Real.log x) * y + x * (y * Real.log y) := by
      unfold entropyTerm
      ring

theorem log_multinomial_mul_eq (counts : A → ℕ) (t : ℕ) :
    Real.log (Nat.multinomial Finset.univ (fun a => t * counts a) : ℝ) =
      (t : ℝ) *
          ((∑ a, counts a : ℕ) * Real.log (∑ a, counts a : ℕ) -
            ∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) +
        factorialLogRemainder (t * ∑ a, counts a) -
        ∑ a, factorialLogRemainder (t * counts a) := by
  have hsum : (∑ a, t * counts a) = t * ∑ a, counts a :=
    (Finset.mul_sum Finset.univ counts t).symm
  have hlogs :
      (∑ a, ((t : ℝ) * counts a) * Real.log ((t : ℝ) * counts a)) =
        ((t : ℝ) * Real.log t) * (∑ a, counts a : ℕ) +
          (t : ℝ) * ∑ a, (counts a : ℝ) * Real.log (counts a : ℝ) := by
    simp only [mul_log_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Nat.cast_sum]
  rw [log_multinomial_eq_main_add_remainder, hsum]
  simp only [Nat.cast_mul]
  rw [mul_log_mul, hlogs]
  ring

theorem tendsto_log_multinomial_mul (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Tendsto
      (fun t : ℕ =>
        Real.log (Nat.multinomial Finset.univ (fun a => t * counts a) : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  have hsum :
      Tendsto (fun t : ℕ => ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ))
        atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ
      (fun a _ => tendsto_factorialLogRemainder_mul_div (counts a))
  have herror : Tendsto
      (fun t : ℕ =>
        (factorialLogRemainder (t * ∑ a, counts a) / (t : ℝ) -
          ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ)) /
            (∑ a, counts a : ℕ)) atTop (𝓝 0) := by
    simpa using ((tendsto_factorialLogRemainder_mul_div (∑ a, counts a)).sub
      hsum).div_const (∑ a, counts a : ℕ)
  have hlimit : Tendsto
      (fun t : ℕ =>
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
          (factorialLogRemainder (t * ∑ a, counts a) / (t : ℝ) -
            ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ)) /
              (∑ a, counts a : ℕ))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror
  apply hlimit.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
  rw [log_multinomial_mul_eq, finiteEntropy_nat_normalize counts hD,
    ← Finset.sum_div]
  have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  field_simp [ht', hD']
  ring

theorem tendsto_log_multinomial_repetitions {I : Type*} {l : Filter I}
    (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (repetitions : I → ℕ) (hrep : Tendsto repetitions l atTop) :
    Tendsto
      (fun i =>
        Real.log (Nat.multinomial Finset.univ
          (fun a => repetitions i * counts a) : ℝ) /
            ((repetitions i : ℝ) * (∑ a, counts a : ℕ)))
      l (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  exact (tendsto_log_multinomial_mul counts hD).comp hrep

theorem tendsto_log_exactWords_card_mul [DecidableEq A] (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Tendsto
      (fun t : ℕ => Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  simpa only [exactWords_card] using tendsto_log_multinomial_mul counts hD

theorem abs_log_exactWords_card_sub_entropy_le [DecidableEq A] (counts : A → ℕ) :
    |Real.log (Fintype.card (ExactWords counts) : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  simpa only [exactWords_card] using abs_log_multinomial_sub_entropy_le counts

theorem log_card_le_entropy_of_injective_exactWords [DecidableEq A]
    {O : Type*} [Fintype O] [Nonempty O] (counts : A → ℕ)
    (label : O → ExactWords counts) (hinj : Function.Injective label) :
    Real.log (Fintype.card O : ℝ) ≤
      (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ((Fintype.card A : ℝ) + 1) *
          (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  have hcard := Fintype.card_le_of_injective label hinj
  have hlog : Real.log (Fintype.card O : ℝ) ≤
      Real.log (Fintype.card (ExactWords counts) : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr Fintype.card_pos) (by exact_mod_cast hcard)
  have herror := (abs_le.mp (abs_log_exactWords_card_sub_entropy_le counts)).2
  linarith

theorem log_card_div_le_entropy_of_injective_exactWords [DecidableEq A]
    {O : Type*} [Fintype O] [Nonempty O] (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a)
    (label : O → ExactWords counts) (hinj : Function.Injective label) :
    Real.log (Fintype.card O : ℝ) / (∑ a, counts a : ℕ) ≤
      finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ((Fintype.card A : ℝ) + 1) *
          ((1 + Real.log ((∑ a, counts a) + 1 : ℕ)) / (∑ a, counts a : ℕ)) := by
  have hD' : (0 : ℝ) < (∑ a, counts a : ℕ) := Nat.cast_pos.mpr hD
  have h := div_le_div_of_nonneg_right
    (log_card_le_entropy_of_injective_exactWords counts label hinj) hD'.le
  rw [add_div, mul_div_cancel_left₀ _ hD'.ne', mul_div_assoc] at h
  exact h

theorem tendsto_log_exactWords_card_of_empirical_tendsto [DecidableEq A]
    {I : Type*} {l : Filter I} (counts : I → A → ℕ) (p : A → ℝ)
    (htotal : Tendsto (fun i => ∑ a, counts i a) l atTop)
    (hmass : ∀ a, Tendsto
      (fun i => (counts i a : ℝ) / (∑ b, counts i b : ℕ)) l (𝓝 (p a))) :
    Tendsto
      (fun i => Real.log (Fintype.card (ExactWords (counts i)) : ℝ) /
        (∑ a, counts i a : ℕ))
      l (𝓝 (finiteEntropy p)) := by
  simpa only [exactWords_card] using
    tendsto_log_multinomial_of_empirical_tendsto counts p htotal hmass

namespace RationalLaw

theorem exists_exactWords_entropy_limit [DecidableEq A] (p : RationalLaw A) :
    ∃ counts : A → ℕ, 0 < ∑ a, counts a ∧
      (∀ a, (counts a : ℝ) / (∑ a, counts a : ℕ) = p.toFiniteLaw.mass a) ∧
      Tendsto
        (fun t : ℕ => Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy p.toFiniteLaw.mass)) := by
  obtain ⟨counts, hD, hmass⟩ := p.exists_type_representation
  refine ⟨counts, hD, hmass, ?_⟩
  have hfun : (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      p.toFiniteLaw.mass := funext hmass
  rw [← hfun]
  exact tendsto_log_exactWords_card_mul counts hD

end RationalLaw

end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields
