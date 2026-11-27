/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.FiniteProbability
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Concentration of independent finite samples

The exponential moments here are identities for actual uniformly sampled finite
lists.  Markov's inequality then supplies the two tail estimates used for sparse
candidate lists.  Slightly weaker rational exponents simplify the constants in
the paper without changing the eventual parameter regime.
-/

@[expose] public section

namespace Klr.SampleConcentration

open scoped BigOperators
open FiniteProbability

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- The number of samples belonging to an event. -/
noncomputable def count {J : ℕ} (A : Set Ω) (z : Fin J → Ω) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => z i ∈ A).card

/-- The exact probability generating function of the count of independent samples. -/
theorem average_pow_count (A : Set Ω) (J : ℕ) (b : ℝ) :
    average (fun z : Fin J → Ω => b ^ count A z) =
      (1 + (b - 1) * probability A) ^ J := by
  classical
  calc
    average (fun z : Fin J → Ω => b ^ count A z) =
        average (fun z : Fin J → Ω => ∏ i, if z i ∈ A then b else 1) := by
      apply average_congr
      intro z
      simp [count, Finset.prod_ite]
    _ = (average (fun x => if x ∈ A then b else 1)) ^ J := by
      simpa using average_prod_samples (fun x : Ω => if x ∈ A then b else 1) J
    _ = (1 + (b - 1) * probability A) ^ J := by
      congr 1
      calc
        average (fun x => if x ∈ A then b else 1) =
            average (fun x => 1 + (b - 1) * (if x ∈ A then (1 : ℝ) else 0)) := by
          apply average_congr
          intro x
          by_cases hx : x ∈ A <;> simp [hx]
        _ = 1 + (b - 1) * probability A := by
          rw [average_add, average_const, average_const_mul]
          rfl

/-- Exponential-moment tail bound for any base greater than one. -/
theorem probability_count_gt_le (A : Set Ω) (J : ℕ) (b : ℝ) (hb : 1 < b)
    (t : ℝ) :
    probability {z : Fin J → Ω | t < (count A z : ℝ)} ≤
      Real.exp ((b - 1) * probability A * J - Real.log b * t) := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hlog : 0 ≤ Real.log b := Real.log_nonneg (le_of_lt hb)
  have hpn : 0 ≤ probability A := probability_nonneg A
  have hbn : 0 ≤ b - 1 := sub_nonneg.mpr (le_of_lt hb)
  have hmoment : average (fun z : Fin J → Ω => b ^ count A z) ≤
      Real.exp ((b - 1) * probability A * J) := by
    rw [average_pow_count]
    calc
      (1 + (b - 1) * probability A) ^ J ≤
          (Real.exp ((b - 1) * probability A)) ^ J := by
        apply pow_le_pow_left₀ (by positivity)
        simpa only [add_comm] using Real.add_one_le_exp ((b - 1) * probability A)
      _ = Real.exp ((b - 1) * probability A * J) := by
        rw [← Real.exp_nat_mul, mul_comm]
  calc
    probability {z : Fin J → Ω | t < (count A z : ℝ)} ≤
        probability {z : Fin J → Ω |
          Real.exp (Real.log b * t) ≤ b ^ count A z} := by
      apply probability_mono
      intro z hz
      change Real.exp (Real.log b * t) ≤ b ^ count A z
      calc
        Real.exp (Real.log b * t) ≤ Real.exp ((count A z : ℝ) * Real.log b) := by
          apply Real.exp_le_exp.mpr
          nlinarith [show t < (count A z : ℝ) from hz]
        _ = b ^ count A z := by rw [Real.exp_nat_mul, Real.exp_log hb0]
    _ ≤ average (fun z : Fin J → Ω => b ^ count A z) /
        Real.exp (Real.log b * t) :=
      probability_le_average_div _ (fun _ => pow_nonneg (le_of_lt hb0) _)
        _ (Real.exp_pos _)
    _ ≤ Real.exp ((b - 1) * probability A * J) / Real.exp (Real.log b * t) :=
      div_le_div_of_nonneg_right hmoment (le_of_lt (Real.exp_pos _))
    _ = Real.exp ((b - 1) * probability A * J - Real.log b * t) :=
      (Real.exp_sub _ _).symm

/-- A rare bad-rank event occurs in at most a `θ` fraction of the samples,
outside an exceptional set of probability at most `exp (-θ J / 4)`. -/
theorem rank_tail (A : Set Ω) (J : ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hp : probability A ≤ θ / 4) :
    probability {z : Fin J → Ω | θ * J < (count A z : ℝ)} ≤
      Real.exp (-(θ * J) / 4) := by
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    linarith
  calc
    probability {z : Fin J → Ω | θ * J < (count A z : ℝ)} ≤
        Real.exp ((2 - 1) * probability A * J - Real.log 2 * (θ * J)) :=
      probability_count_gt_le A J 2 (by norm_num) _
    _ ≤ Real.exp (-(θ * J) / 4) := by
      apply Real.exp_le_exp.mpr
      have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg _
      have h1 := mul_le_mul_of_nonneg_right hp hJ
      have h2 := mul_le_mul_of_nonneg_right hl (mul_nonneg hθ hJ)
      nlinarith

/-- Twice the marginal incidence is enough for simultaneous sparse supports.
Base `3/2` gives a convenient rational exponential bound. -/
theorem incidence_tail (A : Set Ω) (J : ℕ) (p : ℝ) (hp0 : 0 ≤ p)
    (hp : probability A ≤ p) :
    probability {z : Fin J → Ω | 2 * p * J < (count A z : ℝ)} ≤
      Real.exp (-(p * J) / 6) := by
  have hl : (1 / 3 : ℝ) ≤ Real.log (3 / 2) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
    norm_num at h
    linarith
  calc
    probability {z : Fin J → Ω | 2 * p * J < (count A z : ℝ)} ≤
        Real.exp ((3 / 2 - 1) * probability A * J - Real.log (3 / 2) * (2 * p * J)) :=
      probability_count_gt_le A J (3 / 2) (by norm_num) _
    _ ≤ Real.exp (-(p * J) / 6) := by
      apply Real.exp_le_exp.mpr
      have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg _
      have h1 := mul_le_mul_of_nonneg_right hp hJ
      have h2 := mul_le_mul_of_nonneg_right hl (by positivity : 0 ≤ 2 * p * J)
      nlinarith

/-- A single finite list simultaneously controls all events in both families.
The hypotheses refer to their actual marginal probabilities. -/
theorem exists_simultaneous_samples {α β : Type*} [Fintype α] [Fintype β]
    (A : α → Set Ω) (B : β → Set Ω) (J : ℕ) (θ p : ℝ)
    (hθ : 0 ≤ θ) (hp0 : 0 ≤ p)
    (hA : ∀ a, probability (A a) ≤ θ / 4)
    (hB : ∀ b, probability (B b) ≤ p)
    (hsmall : Fintype.card α * Real.exp (-(θ * J) / 4) +
      Fintype.card β * Real.exp (-(p * J) / 6) < 1) :
    ∃ z : Fin J → Ω,
      (∀ a, (count (A a) z : ℝ) ≤ θ * J) ∧
      (∀ b, (count (B b) z : ℝ) ≤ 2 * p * J) := by
  classical
  let E : α ⊕ β → Set (Fin J → Ω) := Sum.elim
    (fun a => {z | θ * J < (count (A a) z : ℝ)})
    (fun b => {z | 2 * p * J < (count (B b) z : ℝ)})
  have he : probability (⋃ i, E i) < 1 := by
    calc
      probability (⋃ i, E i) ≤ ∑ i, probability (E i) := probability_iUnion_le E
      _ = (∑ a, probability {z : Fin J → Ω | θ * J < (count (A a) z : ℝ)}) +
          ∑ b, probability {z : Fin J → Ω | 2 * p * J < (count (B b) z : ℝ)} := by
        rw [Fintype.sum_sum_type]
        rfl
      _ ≤ Fintype.card α * Real.exp (-(θ * J) / 4) +
          Fintype.card β * Real.exp (-(p * J) / 6) := by
        apply add_le_add
        · calc
            _ ≤ ∑ _a : α, Real.exp (-(θ * J) / 4) :=
              Finset.sum_le_sum fun a _ => rank_tail (A a) J θ hθ (hA a)
            _ = _ := by simp
        · calc
            _ ≤ ∑ _b : β, Real.exp (-(p * J) / 6) :=
              Finset.sum_le_sum fun b _ => incidence_tail (B b) J p hp0 (hB b)
            _ = _ := by simp
      _ < 1 := hsmall
  obtain ⟨z, hz⟩ := exists_not_mem_of_probability_lt_one (⋃ i, E i) he
  refine ⟨z, ?_, ?_⟩
  · intro a
    apply le_of_not_gt
    intro ha
    exact hz (Set.mem_iUnion.mpr ⟨Sum.inl a, ha⟩)
  · intro b
    apply le_of_not_gt
    intro hb
    exact hz (Set.mem_iUnion.mpr ⟨Sum.inr b, hb⟩)

end Klr.SampleConcentration
