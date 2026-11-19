/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.Combinatorics.Subsets
public import LeanPool.HubbardMoments.Defs
import Mathlib.Data.Nat.Factorial.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Finite-population identities

Drawing `k` labels without replacement from a population `ε : V → ℝ` of `N` values with
`∑ ε = 0` (`HubbardMoments.sampleMoment`), with `P₂ = ∑ ε²`, `P₄ = ∑ ε⁴` and
`p_m = k(k-1)⋯(k-m+1)/(N(N-1)⋯(N-m+1))` (`HubbardMoments.inclusionProb`):

* `sampleMoment_one`: the mean of the sample sum is `0`;
* `sampleMoment_two`: its variance is `P₂ (p₁ - p₂)`, and
  `sampleMoment_two_fpc`: `k σ₁² (N - k)/(N - 1)` with `σ₁² = P₂/N`, the finite-population
  correction (§5.3);
* `sampleMoment_four`: its fourth moment is
  `P₄ (p₁ - 7p₂ + 12p₃ - 6p₄) + 3 P₂² (p₂ - 2p₃ + p₄)` (App. B);
* `independent_sum_two`, `independent_sum_four`: for independent zero-mean `X`, `Y`,
  `Var(X + Y) = Var X + Var Y` and `μ₄(X + Y) = μ₄(X) + μ₄(Y) + 6 Var X Var Y` (App. B); the
  first needs only one of the two means to vanish.

The proof of the fourth moment does not list coincidence patterns. Expanding `S_K⁴` over
4-tuples of labels, each tuple with `m` distinct labels lies in `C(N, k) p_m` of the subsets
(`sum_powersetCard_ite_subset`), and `∑ ε = 0` removes one index at a time
(`sum_mul_card_insert`, `sum_mul_card_insert_sum`). `sum_tuple_four` is the resulting
identity for an arbitrary weight `q_m` in place of `p_m`.

## Not covered

That the many-body energies of `k` free fermions of one spin species are the sums of `k`
distinct single-particle energies (Slater determinants). This is standard and is what makes
`sampleMoment` the `μ_ℓ` of the paper at `U = 0`.
-/

@[expose] public section

namespace HubbardMoments

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The `k`-subsets containing `T`: `C(N - |T|, k - |T|)` of them, written without
subtraction. -/
theorem card_supersets_mul (T : Finset V) (k : ℕ) :
    ((powersetCard k univ).filter (fun K => T ⊆ K)).card *
        (Fintype.card V).descFactorial T.card =
      (Fintype.card V).choose k * k.descFactorial T.card := by
  by_cases hTk : T.card ≤ k
  · have h := card_trace_eq T T subset_rfl k hTk
    simp only [inter_eq_left] at h
    rw [h]
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
      show (Fintype.card V).choose k * ((T.card).factorial * k.choose T.card) =
        (T.card).factorial * ((Fintype.card V).choose k * k.choose T.card) by ring,
      Nat.choose_mul hTk]
    ring
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 (show k < T.card by omega), mul_zero]
    have : (powersetCard k univ).filter (fun K => T ⊆ K) = ∅ := by
      ext K
      simp only [mem_filter, mem_powersetCard, subset_univ, true_and, notMem_empty, iff_false,
        not_and]
      intro hK hTK
      exact hTk (hK ▸ card_le_card hTK)
    rw [this, card_empty, zero_mul]

/-- Summing over the `k`-subsets a term that is present only when `K ⊇ T`. -/
theorem sum_powersetCard_ite_subset (T : Finset V) (k : ℕ) (x : ℝ) :
    ∑ K ∈ powersetCard k univ, (if T ⊆ K then x else 0) =
      (Fintype.card V).choose k * inclusionProb (Fintype.card V) k T.card * x := by
  rw [← sum_filter, sum_const, nsmul_eq_mul, inclusionProb]
  have hN : ((Fintype.card V).descFactorial T.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.2 (not_lt.2 (card_le_univ T)))
  have h := card_supersets_mul T k
  have h' : (((powersetCard k univ).filter (fun K => T ⊆ K)).card : ℝ) *
      (Fintype.card V).descFactorial T.card =
        (Fintype.card V).choose k * k.descFactorial T.card := by
    exact_mod_cast h
  field_simp
  linear_combination x * h'

theorem sum_eq_sum_ite (ε : V → ℝ) (K : Finset V) :
    ∑ i ∈ K, ε i = ∑ i, if i ∈ K then ε i else 0 := by
  rw [sum_ite_mem, univ_inter]

/-- `S_K⁴` as a sum over 4-tuples of sites, each present when the tuple lies in `K`. -/
theorem sum_pow_four_eq (ε : V → ℝ) (K : Finset V) :
    (∑ i ∈ K, ε i) ^ 4 = ∑ a, ∑ b, ∑ c, ∑ d,
      if insert d (insert c (insert b {a})) ⊆ K then ε a * ε b * ε c * ε d else 0 := by
  rw [sum_eq_sum_ite, show ∀ x : ℝ, x ^ 4 = x * x * x * x from fun x => by ring]
  simp only [sum_mul, mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ =>
    sum_congr rfl fun d _ => ?_
  by_cases ha : a ∈ K <;> by_cases hb : b ∈ K <;> by_cases hc : c ∈ K <;>
    by_cases hd : d ∈ K <;> simp [ha, hb, hc, hd, insert_subset_iff]
  ring

theorem sum_pow_two_eq (ε : V → ℝ) (K : Finset V) :
    (∑ i ∈ K, ε i) ^ 2 = ∑ a, ∑ b, if insert b {a} ⊆ K then ε a * ε b else 0 := by
  rw [sum_eq_sum_ite, sq]
  simp only [sum_mul, mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  by_cases ha : a ∈ K <;> by_cases hb : b ∈ K <;> simp [ha, hb, insert_subset_iff]
  ring

section Peel

variable (ε : V → ℝ) (hε : ∑ v, ε v = 0)
include hε

theorem sum_compl_eq_neg (T : Finset V) : ∑ v ∈ Tᶜ, ε v = -∑ v ∈ T, ε v := by
  have := sum_add_sum_compl T ε
  linarith

/-- **Removing one index.** With `∑ ε = 0`, summing `ε_d q(|T ∪ {d}|)` over `d` leaves
`(q(|T|) - q(|T| + 1)) ∑_{d ∈ T} ε_d`. -/
theorem sum_mul_card_insert (q : ℕ → ℝ) (T : Finset V) :
    ∑ d, ε d * q (insert d T).card = (q T.card - q (T.card + 1)) * ∑ d ∈ T, ε d := by
  have h1 : ∑ d ∈ T, ε d * q (insert d T).card = (∑ d ∈ T, ε d) * q T.card := by
    rw [sum_mul]
    exact sum_congr rfl fun d hd => by rw [insert_eq_of_mem hd]
  have h2 : ∑ d ∈ Tᶜ, ε d * q (insert d T).card = (∑ d ∈ Tᶜ, ε d) * q (T.card + 1) := by
    rw [sum_mul]
    exact sum_congr rfl fun d hd => by rw [card_insert_of_notMem (mem_compl.1 hd)]
  rw [← sum_add_sum_compl T, h1, h2, sum_compl_eq_neg ε hε]
  ring

/-- **Removing one more index.** -/
theorem sum_mul_card_insert_sum (f : ℕ → ℝ) (T : Finset V) :
    ∑ c, ε c * f (insert c T).card * ∑ d ∈ insert c T, ε d =
      f T.card * (∑ d ∈ T, ε d) ^ 2 +
        f (T.card + 1) * (∑ v, ε v ^ 2 - (∑ d ∈ T, ε d) ^ 2 - ∑ d ∈ T, ε d ^ 2) := by
  have h2 : ∑ v ∈ Tᶜ, ε v ^ 2 = ∑ v, ε v ^ 2 - ∑ v ∈ T, ε v ^ 2 := by
    have := sum_add_sum_compl T (fun v => ε v ^ 2)
    linarith
  have h3 : ∑ c ∈ T, ε c * f (insert c T).card * ∑ d ∈ insert c T, ε d =
      f T.card * (∑ d ∈ T, ε d) ^ 2 := by
    rw [sum_congr rfl fun c hc => show ε c * f (insert c T).card * ∑ d ∈ insert c T, ε d =
      (f T.card * ∑ d ∈ T, ε d) * ε c by rw [insert_eq_of_mem hc]; ring, ← mul_sum]
    ring
  have h4 : ∑ c ∈ Tᶜ, ε c * f (insert c T).card * ∑ d ∈ insert c T, ε d =
      f (T.card + 1) * (∑ c ∈ Tᶜ, ε c ^ 2) + f (T.card + 1) * (∑ d ∈ T, ε d) * ∑ c ∈ Tᶜ, ε c := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun c hc => ?_
    rw [card_insert_of_notMem (mem_compl.1 hc), sum_insert (mem_compl.1 hc)]
    ring
  rw [← sum_add_sum_compl T, h3, h4, h2, sum_compl_eq_neg ε hε]
  ring

/-- The 4-index sum weighted by a function of the number of distinct sites. -/
theorem sum_tuple_four (q : ℕ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, q (insert d (insert c (insert b ({a} : Finset V)))).card *
      (ε a * ε b * ε c * ε d) =
      (∑ i, ε i ^ 4) * (q 1 - 7 * q 2 + 12 * q 3 - 6 * q 4) +
        3 * (∑ i, ε i ^ 2) ^ 2 * (q 2 - 2 * q 3 + q 4) := by
  set P₂ := ∑ i, ε i ^ 2 with hP₂
  set P₄ := ∑ i, ε i ^ 4 with hP₄
  set Δ : ℕ → ℝ := fun m => q m - q (m + 1) with hΔ
  -- remove `d`
  have stepA : ∀ a b c, ∑ d, q (insert d (insert c (insert b ({a} : Finset V)))).card *
      (ε a * ε b * ε c * ε d) = ε a * ε b * ε c *
        (Δ (insert c (insert b ({a} : Finset V))).card *
          ∑ d ∈ insert c (insert b ({a} : Finset V)), ε d) := by
    intro a b c
    rw [← sum_mul_card_insert ε hε q, mul_sum]
    exact sum_congr rfl fun d _ => by ring
  -- remove `c`
  have stepB : ∀ a b, ∑ c, ε a * ε b * ε c *
      (Δ (insert c (insert b ({a} : Finset V))).card *
          ∑ d ∈ insert c (insert b ({a} : Finset V)), ε d) =
        ε a * ε b * (Δ (insert b ({a} : Finset V)).card *
          (∑ d ∈ insert b ({a} : Finset V), ε d) ^ 2 +
          Δ ((insert b ({a} : Finset V)).card + 1) *
            (P₂ - (∑ d ∈ insert b ({a} : Finset V), ε d) ^ 2 -
            ∑ d ∈ insert b ({a} : Finset V), ε d ^ 2)) := by
    intro a b
    rw [← sum_mul_card_insert_sum ε hε Δ, mul_sum]
    exact sum_congr rfl fun c _ => by ring
  -- the two remaining indices, equal or not
  set g₂ : V → V → ℝ := fun a b => ε a * ε b * (Δ 2 * (ε a + ε b) ^ 2 +
    Δ 3 * (P₂ - (ε a + ε b) ^ 2 - ε a ^ 2 - ε b ^ 2)) with hg₂
  set g₁ : V → ℝ := fun a => ε a * ε a * (Δ 1 * ε a ^ 2 + Δ 2 * (P₂ - ε a ^ 2 - ε a ^ 2))
    with hg₁
  have stepC : ∀ a b, ε a * ε b * (Δ (insert b ({a} : Finset V)).card *
          (∑ d ∈ insert b ({a} : Finset V), ε d) ^ 2 +
      Δ ((insert b ({a} : Finset V)).card + 1) *
            (P₂ - (∑ d ∈ insert b ({a} : Finset V), ε d) ^ 2 -
        ∑ d ∈ insert b ({a} : Finset V), ε d ^ 2)) =
      g₂ a b + if b = a then g₁ a - g₂ a a else 0 := by
    intro a b
    by_cases hab : b = a
    · subst hab
      simp only [insert_eq_of_mem (mem_singleton_self b), card_singleton, sum_singleton,
        ↓reduceIte, hg₁]
      ring
    · rw [card_insert_of_notMem (by simpa using hab), card_singleton,
        sum_insert (by simpa using hab), sum_insert (by simpa using hab), sum_singleton,
        sum_singleton]
      simp only [hab, ↓reduceIte, hg₂, add_zero]
      ring
  simp only [stepA, stepB, stepC, sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte]
  -- evaluate in power sums
  have e₂ : ∀ a b, g₂ a b = (Δ 2 - 2 * Δ 3) * (ε a ^ 3 * ε b) +
      (Δ 2 - 2 * Δ 3) * (ε a * ε b ^ 3) + (2 * Δ 2 - 2 * Δ 3) * (ε a ^ 2 * ε b ^ 2) +
        Δ 3 * P₂ * (ε a * ε b) := fun a b => by simp only [hg₂]; ring
  have e₁ : ∀ a, g₁ a - g₂ a a = (Δ 1 - 6 * Δ 2 + 6 * Δ 3) * ε a ^ 4 +
      (Δ 2 - Δ 3) * P₂ * ε a ^ 2 := fun a => by simp only [hg₁, hg₂]; ring
  simp only [e₁]
  simp only [e₂, sum_add_distrib, ← mul_sum, ← sum_mul, hε, mul_zero, zero_mul, add_zero]
  simp only [← hP₂, ← hP₄, hΔ, sum_const_zero]
  ring

end Peel

section Moments

variable (ε : V → ℝ)

omit [DecidableEq V] in
/-- Moving the sum over subsets inside a 4-fold sum over labels. -/
theorem sum_powersetCard_sum_four (k : ℕ) (F : Finset V → V → V → V → V → ℝ) :
    ∑ K ∈ powersetCard k univ, ∑ a, ∑ b, ∑ c, ∑ d, F K a b c d =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ K ∈ powersetCard k univ, F K a b c d := by
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun c _ => ?_
  rw [sum_comm]

/-- The sampled fourth moment as a 4-index sum weighted by `p_m`. -/
theorem sampleMoment_four_eq {k : ℕ} (hk : k ≤ Fintype.card V) :
    sampleMoment ε k 4 = ∑ a, ∑ b, ∑ c, ∑ d,
      inclusionProb (Fintype.card V) k (insert d (insert c (insert b ({a} : Finset V)))).card *
        (ε a * ε b * ε c * ε d) := by
  have hC : ((Fintype.card V).choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  rw [sampleMoment, sum_congr rfl fun K _ => sum_pow_four_eq ε K, sum_powersetCard_sum_four,
    div_eq_iff hC]
  simp only [sum_powersetCard_ite_subset, sum_mul]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ =>
    sum_congr rfl fun d _ => by ring

/-- The sampled second moment as a 2-index sum weighted by `p_m`. -/
theorem sampleMoment_two_eq {k : ℕ} (hk : k ≤ Fintype.card V) :
    sampleMoment ε k 2 = ∑ a, ∑ b,
      inclusionProb (Fintype.card V) k (insert b ({a} : Finset V)).card * (ε a * ε b) := by
  have hC : ((Fintype.card V).choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  rw [sampleMoment, sum_congr rfl fun K _ => sum_pow_two_eq ε K, sum_comm, div_eq_iff hC]
  simp only [sum_mul]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]
  simp only [sum_powersetCard_ite_subset]
  exact sum_congr rfl fun b _ => by ring

variable {ε} (hε : ∑ v, ε v = 0)
include hε

omit [DecidableEq V] in
/-- **The mean of the sample sum vanishes.** -/
theorem sampleMoment_one (k : ℕ) : sampleMoment ε k 1 = 0 := by
  classical
  have h : ∀ K : Finset V, (∑ i ∈ K, ε i) ^ 1 = ∑ a, if ({a} : Finset V) ⊆ K then ε a else 0 :=
    fun K => by rw [pow_one, sum_eq_sum_ite]; simp only [singleton_subset_iff]
  rw [sampleMoment, sum_congr rfl fun K _ => h K, sum_comm]
  simp only [sum_powersetCard_ite_subset, card_singleton, ← mul_sum, hε, mul_zero, zero_div]

omit [DecidableEq V] in
/-- **The variance of the sample sum:** `P₂ (p₁ - p₂)`. -/
theorem sampleMoment_two {k : ℕ} (hk : k ≤ Fintype.card V) :
    sampleMoment ε k 2 = (∑ i, ε i ^ 2) *
      (inclusionProb (Fintype.card V) k 1 - inclusionProb (Fintype.card V) k 2) := by
  classical
  rw [sampleMoment_two_eq ε hk]
  have h : ∀ a, ∑ b, inclusionProb (Fintype.card V) k (insert b ({a} : Finset V)).card *
      (ε a * ε b) = (inclusionProb (Fintype.card V) k 1 - inclusionProb (Fintype.card V) k 2) *
        ε a ^ 2 := by
    intro a
    have h₁ := sum_mul_card_insert ε hε (inclusionProb (Fintype.card V) k) {a}
    rw [card_singleton, sum_singleton] at h₁
    rw [sq, mul_comm (ε a), ← mul_assoc, ← h₁, sum_mul]
    exact sum_congr rfl fun b _ => by ring
  rw [sum_congr rfl fun a _ => h a, ← mul_sum, mul_comm]

omit [DecidableEq V] in
/-- **The fourth moment of the sample sum** (App. B):
`μ₄ = P₄ (p₁ - 7p₂ + 12p₃ - 6p₄) + 3 P₂² (p₂ - 2p₃ + p₄)`. -/
theorem sampleMoment_four {k : ℕ} (hk : k ≤ Fintype.card V) :
    sampleMoment ε k 4 =
      (∑ i, ε i ^ 4) * (inclusionProb (Fintype.card V) k 1 -
        7 * inclusionProb (Fintype.card V) k 2 + 12 * inclusionProb (Fintype.card V) k 3 -
          6 * inclusionProb (Fintype.card V) k 4) +
      3 * (∑ i, ε i ^ 2) ^ 2 * (inclusionProb (Fintype.card V) k 2 -
        2 * inclusionProb (Fintype.card V) k 3 + inclusionProb (Fintype.card V) k 4) := by
  classical
  rw [sampleMoment_four_eq ε hk, sum_tuple_four ε hε]

omit [DecidableEq V] in
/-- **The finite-population correction** (§5.3): the variance of the sum of `k` values drawn
without replacement is `k σ₁² (N - k)/(N - 1)`, `σ₁² = P₂/N`. -/
theorem sampleMoment_two_fpc {k : ℕ} (hk : k ≤ Fintype.card V) (hN : 2 ≤ Fintype.card V) :
    sampleMoment ε k 2 = k * ((∑ i, ε i ^ 2) / Fintype.card V) *
      (Fintype.card V - k) / (Fintype.card V - 1) := by
  rw [sampleMoment_two hε hk, inclusionProb, inclusionProb, Nat.descFactorial_one,
    Nat.descFactorial_one, Nat.cast_descFactorial_two, Nat.cast_descFactorial_two]
  have hN0 : (Fintype.card V : ℝ) ≠ 0 := by positivity
  have hN1 : (Fintype.card V : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
    linarith
  field_simp
  ring

end Moments

section Independent

variable {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] {f : A → ℝ} {g : B → ℝ}

/-- **Second moments of independent variables add** when one of them has mean zero: for the
uniform distribution on `A × B`, `E[(f + g)²] = E[f²] + E[g²]`. -/
theorem independent_sum_two (hg : ∑ b, g b = 0) :
    (∑ a, ∑ b, (f a + g b) ^ 2) / (Fintype.card A * Fintype.card B) =
      (∑ a, f a ^ 2) / Fintype.card A + (∑ b, g b ^ 2) / Fintype.card B := by
  have e : ∀ a b, (f a + g b) ^ 2 = f a ^ 2 + 2 * (f a * g b) + g b ^ 2 := fun a b => by ring
  simp only [e, sum_add_distrib, ← mul_sum, hg, mul_zero, add_zero, sum_const, card_univ,
    nsmul_eq_mul]
  have hA : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

/-- **Fourth moments of independent zero-mean variables** (App. B):
`μ₄(f + g) = μ₄(f) + μ₄(g) + 6 Var f Var g`. -/
theorem independent_sum_four (hf : ∑ a, f a = 0) (hg : ∑ b, g b = 0) :
    (∑ a, ∑ b, (f a + g b) ^ 4) / (Fintype.card A * Fintype.card B) =
      (∑ a, f a ^ 4) / Fintype.card A + (∑ b, g b ^ 4) / Fintype.card B +
        6 * ((∑ a, f a ^ 2) / Fintype.card A) * ((∑ b, g b ^ 2) / Fintype.card B) := by
  have e : ∀ a b, (f a + g b) ^ 4 = f a ^ 4 + 4 * (f a ^ 3 * g b) + 6 * (f a ^ 2 * g b ^ 2) +
      4 * (f a * g b ^ 3) + g b ^ 4 := fun a b => by ring
  simp only [e, sum_add_distrib, ← mul_sum, ← sum_mul, hf, hg, mul_zero, zero_mul, add_zero,
    sum_const, card_univ, nsmul_eq_mul]
  have hA : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  ring

end Independent

end HubbardMoments
