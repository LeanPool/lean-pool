/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.MartinLof
public import LeanPool.KLRandomness.EffectiveSearch
public import Mathlib.Data.List.OfFn
import Mathlib.Tactic.NormNum

/-!
# Measure budgets for plain binary descriptions

There are `2^d` binary programs of length `d`. Consequently charging each
program of length `d` a measure budget `2^(-(2*d+n+1))` gives a total budget
`2^(-n)`. This uses all binary strings, with no prefix-free assumption.

The measure-budget results are modular. `Klr.AffineDescription` instantiates
them with a concrete interpreter and effective affine verifier. Descriptions
of the particular systems chosen in Liu and Meng's construction still require
the stage reconstruction algorithm and its advice bounds.
-/

@[expose] public section

namespace Klr

open MeasureTheory
open scoped ENNReal

/-- The exact budget assigned to all plain binary descriptions. -/
theorem tsum_binary_description_budget (n : ℕ) :
    (∑' p : List Bool, (1 / 2 : ℝ≥0∞) ^ (2 * p.length + n + 1)) =
      (1 / 2 : ℝ≥0∞) ^ n := by
  have by_length :
      (∑' p : List Bool, (1 / 2 : ℝ≥0∞) ^ (2 * p.length + n + 1)) =
        ∑' d : ℕ, ∑' _ : Fin d → Bool, (1 / 2 : ℝ≥0∞) ^ (2 * d + n + 1) := by
    rw [← (List.equivSigmaTuple (α := Bool)).symm.tsum_eq
      (fun p : List Bool => (1 / 2 : ℝ≥0∞) ^ (2 * p.length + n + 1))]
    simpa using tsum_sigma (fun d (_ : Fin d → Bool) =>
      (1 / 2 : ℝ≥0∞) ^ (2 * d + n + 1))
  rw [by_length]
  have term (d : ℕ) :
      (∑' _ : Fin d → Bool, (1 / 2 : ℝ≥0∞) ^ (2 * d + n + 1)) =
        (1 / 2 : ℝ≥0∞) ^ (d + n + 1) := by
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    rw [show 2 * d + n + 1 = d + (d + n + 1) by omega, pow_add,
      ← mul_assoc, ← mul_pow]
    rw [show (2 : ℝ≥0∞) * (1 / 2) = 1 by
      simpa only [one_div] using ENNReal.mul_inv_cancel
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    simp
  simp_rw [term, show ∀ d : ℕ, d + n + 1 = d + (n + 1) by omega, pow_add]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, pow_succ]
  norm_num
  calc
    _ = ((2 : ℝ≥0∞) * 2⁻¹) * 2⁻¹ ^ n := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- Countable subadditivity turns the per-description budgets into a test-level bound. -/
theorem measure_iUnion_le_description_budget {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : List Bool → Set Ω) (n : ℕ)
    (hE : ∀ p, μ (E p) ≤ (1 / 2 : ℝ≥0∞) ^ (2 * p.length + n + 1)) :
    μ (⋃ p, E p) ≤ (1 / 2 : ℝ≥0∞) ^ n := by
  calc
    μ (⋃ p, E p) ≤ ∑' p, μ (E p) := measure_iUnion_le E
    _ ≤ ∑' p : List Bool, (1 / 2 : ℝ≥0∞) ^ (2 * p.length + n + 1) := tsum_le_tsum hE
    _ = _ := tsum_binary_description_budget n

/-- One test level, formed by taking the union of the events described by all programs. -/
def descriptionLevel (W : ℕ × List Bool × List Bool → Prop) (n : ℕ) : Set Cantor :=
  ⋃ p : List Bool, cylinderUnion (fun s => W (n, p, s))

/-- A single c.e. predicate on `(level, program, cylinder)` yields uniformly effective levels. -/
theorem descriptionLevel_uniform {W : ℕ × List Bool × List Bool → Prop}
    (hW : REPred W) : IsUniformlyEffectivelyOpen (descriptionLevel W) := by
  have hc : Computable (fun a : (ℕ × List Bool) × List Bool => (a.1.1, a.2, a.1.2)) :=
    (Computable.fst.comp Computable.fst).pair
      (Computable.snd.pair (Computable.snd.comp Computable.fst))
  have hV : REPred (fun a : ℕ × List Bool => ∃ p : List Bool, W (a.1, p, a.2)) :=
    rePred_exists (hW.comp hc)
  refine ⟨_, hV, fun n => ?_⟩
  ext X
  simp only [descriptionLevel, Set.mem_iUnion, cylinderUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, s, hps, hs⟩
    exact ⟨s, ⟨p, hps⟩, hs⟩
  · rintro ⟨s, ⟨p, hps⟩, hs⟩
    exact ⟨p, s, hps, hs⟩

/-- The Section 3 description budget supplies the required bound at each level. -/
theorem descriptionLevel_measure_le (W : ℕ × List Bool × List Bool → Prop) (n : ℕ)
    (hbound : ∀ p : List Bool, fairCoin (cylinderUnion (fun s => W (n, p, s))) ≤
      (1 / 2 : ℝ≥0∞) ^ (2 * p.length + n + 1)) :
    fairCoin (descriptionLevel W n) ≤ (1 / 2 : ℝ≥0∞) ^ n :=
  measure_iUnion_le_description_budget fairCoin _ n hbound

/-- A uniformly c.e. family with these per-program budgets defines a genuine Martin-Löf test.
The concrete affine-system instance is supplied by `Klr.AffineDescription`. -/
theorem exists_martinLofTest_of_description_family
    {W : ℕ × List Bool × List Bool → Prop} (hW : REPred W)
    (hbound : ∀ (n : ℕ) (p : List Bool),
      fairCoin (cylinderUnion (fun s => W (n, p, s))) ≤
        (1 / 2 : ℝ≥0∞) ^ (2 * p.length + n + 1)) :
    ∃ T : MartinLofTest, ∀ n, T.level n = descriptionLevel W n := by
  exact MartinLofTest.exists_of_uniform (descriptionLevel_uniform hW)
    (fun n => descriptionLevel_measure_le W n (hbound n))

/-- Membership in some sufficiently small described event at every level witnesses nonrandomness. -/
theorem not_martinLofRandom_of_descriptions
    {W : ℕ × List Bool × List Bool → Prop} (hW : REPred W)
    (hbound : ∀ (n : ℕ) (p : List Bool),
      fairCoin (cylinderUnion (fun s => W (n, p, s))) ≤
        (1 / 2 : ℝ≥0∞) ^ (2 * p.length + n + 1))
    {X : Cantor} (hX : ∀ n, ∃ p, X ∈ cylinderUnion (fun s => W (n, p, s))) :
    ¬MartinLofRandom X := by
  apply not_martinLofRandom_of_uniform (descriptionLevel_uniform hW)
    (fun n => descriptionLevel_measure_le W n (hbound n))
  intro n
  exact Set.mem_iUnion.mpr (hX n)

end Klr
