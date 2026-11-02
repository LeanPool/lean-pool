/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity


/-!
# Finite probability calculations for adaptive stabilizer learning

These are finite counting identities and real inequalities used in the paper.
They do not assert the quantum measurement laws, independence of physical
samples, or stochastic domination of a history-dependent stopping time.
-/

@[expose] public section

noncomputable section

namespace LeanPool.SingleCopyStabilizer.FiniteProbability

open scoped BigOperators

section Collision

variable {A : Type*} [Fintype A]

/-- The collision mass of a finite vector of class probabilities. -/
def collisionMass (p : A → ℝ) : ℝ := ∑ a, p a ^ 2

/-- For independent draws with weights `p`, the diagonal of the product
weight has total mass `∑ a, p a²`. -/
theorem independent_collision_mass (p : A → ℝ) [DecidableEq A] :
    (∑ a, ∑ b, if a = b then p a * p b else 0) = collisionMass p := by
  simp [collisionMass, sq]

/-- Cauchy--Schwarz in the form used for the coset collision estimate. -/
theorem one_le_card_mul_collision (p : A → ℝ) (hp : ∑ a, p a = 1) :
    1 ≤ (Fintype.card A : ℝ) * collisionMass p := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := p)
  simpa [hp, collisionMass] using h

/-- Any normalized class weights have collision mass at least `1 / #A`. -/
theorem inv_card_le_collision [Nonempty A] (p : A → ℝ) (hp : ∑ a, p a = 1) :
    1 / (Fintype.card A : ℝ) ≤ collisionMass p := by
  have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hc).2
  simpa [mul_comm] using one_le_card_mul_collision p hp

/-- At most `2^r` cosets give the paper's collision lower bound `2^(-r)`.
The expression on the left is written `1 / 2^r` to use natural exponents. -/
theorem inverse_two_pow_le_collision (p : A → ℝ) (hp : ∑ a, p a = 1)
    (r : ℕ) (hcard : Fintype.card A ≤ 2 ^ r) :
    1 / (2 : ℝ) ^ r ≤ collisionMass p := by
  have hc : (Fintype.card A : ℝ) ≤ (2 : ℝ) ^ r := by exact_mod_cast hcard
  have hn : 0 ≤ collisionMass p := Finset.sum_nonneg fun a _ => sq_nonneg (p a)
  have hb := one_le_card_mul_collision p hp
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ r)).2
  nlinarith

end Collision

section Differences

variable {G : Type*} [AddCommGroup G]

/-- Fixing a difference leaves precisely one free outcome: `(x,y) ↦ y`,
with inverse `y ↦ (u+y,y)`. -/
def differenceFiberEquiv (u : G) : {xy : G × G // xy.1 - xy.2 = u} ≃ G where
  toFun xy := xy.val.2
  invFun y := ⟨(u + y, y), by simp⟩
  left_inv xy := by
    apply Subtype.ext
    apply Prod.ext
    · exact (sub_eq_iff_eq_add.mp xy.property).symm
    · rfl
  right_inv _ := rfl

/-- Translating both samples by the same affine offset leaves their
additive difference unchanged. -/
theorem affine_difference (z x y : G) : (z + x) - (z + y) = x - y := by
  abel

variable [Fintype G] [DecidableEq G]

/-- Every difference has exactly `#G` ordered representations in `G × G`. -/
theorem difference_fiber_card (u : G) :
    Fintype.card {xy : G × G // xy.1 - xy.2 = u} = Fintype.card G :=
  Fintype.card_congr (differenceFiberEquiv u)

/-- Thus the difference of two independent uniform samples is uniform,
expressed as the ratio of favorable ordered pairs to all ordered pairs. -/
theorem uniform_difference_probability (u : G) :
    (Fintype.card {xy : G × G // xy.1 - xy.2 = u} : ℝ) /
      (Fintype.card (G × G) : ℝ) = 1 / (Fintype.card G : ℝ) := by
  rw [difference_fiber_card, Fintype.card_prod]
  push_cast
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

omit [DecidableEq G] in
/-- The probability-mass-function pushforward of the uniform ordered-pair
distribution under subtraction is exactly the uniform distribution on `G`. -/
theorem uniform_difference_pmf :
    (PMF.uniformOfFintype (G × G)).map (fun xy => xy.1 - xy.2) =
      PMF.uniformOfFintype G := by
  classical
  ext u
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply, tsum_fintype]
  rw [← Finset.sum_filter]
  have hcount : (Finset.univ.filter fun xy : G × G => u = xy.1 - xy.2).card =
      Fintype.card G := by
    simpa only [Fintype.card_subtype, eq_comm] using difference_fiber_card (G := G) u
  simp only [Finset.sum_const, hcount, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  apply ENNReal.mul_inv_cancel_left
  · exact_mod_cast Fintype.card_ne_zero
  · exact ENNReal.natCast_ne_top _

/-- The mass of one specified within-class difference when each class is
uniform internally and class `a` has mass `p a`. -/
def sameClassDifferenceMass {A : Type*} [Fintype A] (p : A → ℝ) (u : G) : ℝ :=
  ∑ a, ∑ _xy : {xy : G × G // xy.1 - xy.2 = u},
    (p a / Fintype.card G) * (p a / Fintype.card G)

/-- Within-class differences all have the same mass, namely collision
mass divided by the size of the common translation group. -/
theorem same_class_difference_mass {A : Type*} [Fintype A] (p : A → ℝ) (u : G) :
    sameClassDifferenceMass p u = collisionMass p / (Fintype.card G : ℝ) := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold sameClassDifferenceMass collisionMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_const, Finset.card_univ, difference_fiber_card, nsmul_eq_mul]
  field_simp

/-- Summing the nonzero within-class differences gives exactly the factor
`collisionMass p * (1 - 1 / #G)` used in the nullity argument. -/
theorem nonzero_same_class_difference_mass {A : Type*} [Fintype A] (p : A → ℝ) :
    (∑ u ∈ (Finset.univ : Finset G).erase 0, sameClassDifferenceMass p u) =
      collisionMass p * (1 - 1 / (Fintype.card G : ℝ)) := by
  simp_rw [same_class_difference_mass]
  have hc : 0 < Fintype.card G := Fintype.card_pos
  have hc0 : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hc
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (0 : G)),
    Finset.card_univ, nsmul_eq_mul]
  rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card G)]
  push_cast
  field_simp

/-- The low-nullity nonzero collision estimate, with the class and
translation-space cardinality assumptions displayed explicitly. -/
theorem low_nullity_nonzero_mass_lower_bound {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∑ a, p a = 1) (r j : ℕ)
    (hclasses : Fintype.card A ≤ 2 ^ r) (hgroup : Fintype.card G = 2 ^ j) :
    1 / (2 : ℝ) ^ r * (1 - 1 / (2 : ℝ) ^ j) ≤
      ∑ u ∈ (Finset.univ : Finset G).erase 0, sameClassDifferenceMass p u := by
  rw [nonzero_same_class_difference_mass, hgroup]
  push_cast
  apply mul_le_mul_of_nonneg_right (inverse_two_pow_le_collision p hp r hclasses)
  have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hinv : 1 / (2 : ℝ) ^ j ≤ 1 := (div_le_iff₀ hpos).2 (by simpa using hpow)
  linarith

end Differences

section RoundBounds

/-- A numerical survival recurrence gives the usual geometric tail.
The recurrence is an explicit hypothesis, not a proved law of the algorithm. -/
theorem survival_le_geometric (s : ℕ → ℝ) (p : ℝ) (hp : p ≤ 1)
    (hzero : s 0 ≤ 1) (hstep : ∀ k, s (k + 1) ≤ (1 - p) * s k) (k : ℕ) :
    s k ≤ (1 - p) ^ k := by
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
      calc
        s (k + 1) ≤ (1 - p) * s k := hstep k
        _ ≤ (1 - p) * (1 - p) ^ k :=
          mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hp)
        _ = (1 - p) ^ (k + 1) := by rw [pow_succ]; ring

/-- A finite sum of survival terms is bounded by the corresponding finite
geometric sum, written in closed form. -/
theorem finite_survival_sum_le (s : ℕ → ℝ) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hzero : s 0 ≤ 1) (hstep : ∀ k, s (k + 1) ≤ (1 - p) * s k) (n : ℕ) :
    (∑ k ∈ Finset.range n, s k) ≤ (1 - (1 - p) ^ n) / p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn := survival_le_geometric s p hp1 hzero hstep n
      calc
        _ ≤ (1 - (1 - p) ^ n) / p + (1 - p) ^ n := add_le_add ih hn
        _ = (1 - (1 - p) ^ (n + 1)) / p := by
          rw [pow_succ]
          field_simp
          ring

/-- Thus every finite truncation of the tail sum is at most `1/p`.
Connecting this to a random variable's expectation is a separate step. -/
theorem finite_survival_sum_le_inverse (s : ℕ → ℝ) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hzero : s 0 ≤ 1)
    (hstep : ∀ k, s (k + 1) ≤ (1 - p) * s k) (n : ℕ) :
    (∑ k ∈ Finset.range n, s k) ≤ 1 / p := by
  apply (finite_survival_sum_le s p hp0 hp1 hzero hstep n).trans
  apply div_le_div_of_nonneg_right _ (le_of_lt hp0)
  have hpow : 0 ≤ (1 - p) ^ n := pow_nonneg (sub_nonneg.mpr hp1) _
  linarith

/-- The success parameter for a positive codimension `j`. -/
def progressProbability (j : ℕ) : ℝ := (1 - (1 / 2 : ℝ) ^ j) / 2

/-- Every positive level has progress parameter at least one quarter. -/
theorem progress_probability_ge_quarter (j : ℕ) (hj : 0 < j) :
    (1 / 4 : ℝ) ≤ progressProbability j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have hpow : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold progressProbability
  rw [pow_succ]
  nlinarith

/-- A strengthened finite reciprocal-sum estimate. This is an arithmetic
bound, not an expectation or stopping-time theorem. -/
theorem reciprocal_sum_le (n : ℕ) :
    (∑ k ∈ Finset.range n, 2 / (1 - (1 / 2 : ℝ) ^ (k + 1))) ≤
      2 * n + 4 - 4 * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hpow0 : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
      have hpow1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hden : 0 < 1 - (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; nlinarith
      have hterm : 2 / (1 - (1 / 2 : ℝ) ^ (n + 1)) ≤
          2 + 4 * (1 / 2 : ℝ) ^ (n + 1) := by
        apply (div_le_iff₀ hden).2
        rw [pow_succ]
        nlinarith [mul_nonneg hpow0 (sub_nonneg.mpr hpow1)]
      push_cast
      rw [pow_succ] at hterm ⊢
      linarith

/-- The paper's strict numerical bound on the sum of reciprocal progress
parameters. The connection to expected waiting times is not assumed here. -/
theorem reciprocal_sum_lt_two_n_add_four (n : ℕ) :
    (∑ k ∈ Finset.range n, 2 / (1 - (1 / 2 : ℝ) ^ (k + 1))) < 2 * n + 4 := by
  have h := reciprocal_sum_le n
  have hp : 0 < (1 / 2 : ℝ) ^ n := by positivity
  linarith

/-- Scaling the same finite bound gives the low-nullity arithmetic bound. -/
theorem scaled_reciprocal_sum_lt (r n : ℕ) :
    (2 : ℝ) ^ r * (∑ k ∈ Finset.range n, 2 / (1 - (1 / 2 : ℝ) ^ (k + 1))) <
      (2 : ℝ) ^ r * (2 * n + 4) := by
  exact mul_lt_mul_of_pos_left (reciprocal_sum_lt_two_n_add_four n) (by positivity)

end RoundBounds

end LeanPool.SingleCopyStabilizer.FiniteProbability
