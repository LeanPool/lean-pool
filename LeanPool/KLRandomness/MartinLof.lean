/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.EffectiveOpen
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum

/-!
# Martin-Löf tests and randomness

Test levels are numbered from zero. The bound is `(1/2)^n`; shifting the paper's
positive numbering by one gives the same randomness notion. Every test carries
one actual partial-recursive code, enforcing uniform effectiveness across levels.
-/

@[expose] public section

namespace Klr

open MeasureTheory
open scoped ENNReal

/-- A Martin-Löf test is one program enumerating all its levels, with the usual bounds. -/
structure MartinLofTest where
  /-- A single partial-recursive program recognizing the cylinders for all test levels. -/
  code : Nat.Partrec.Code
  measure_le : ∀ n, fairCoin (programOpen code n) ≤ (1 / 2 : ℝ≥0∞) ^ n

namespace MartinLofTest

/-- Every uniformly effectively open family satisfying the bounds is represented by a test. -/
theorem exists_of_uniform {U : ℕ → Set Cantor} (hU : IsUniformlyEffectivelyOpen U)
    (hbound : ∀ n, fairCoin (U n) ≤ (1 / 2 : ℝ≥0∞) ^ n) :
    ∃ T : MartinLofTest, ∀ n, programOpen T.code n = U n := by
  obtain ⟨c, hc⟩ := (isUniformlyEffectivelyOpen_iff_exists_program U).mp hU
  exact ⟨⟨c, fun n => by rw [← hc n]; exact hbound n⟩, fun n => (hc n).symm⟩

/-- The `n`th open level of a test. -/
def level (T : MartinLofTest) (n : ℕ) : Set Cantor := programOpen T.code n

theorem uniform (T : MartinLofTest) : IsUniformlyEffectivelyOpen T.level :=
  programOpen_uniform T.code

theorem measurableSet_level (T : MartinLofTest) (n : ℕ) : MeasurableSet (T.level n) :=
  (T.uniform.level n).measurableSet

/-- A sequence fails a test when it belongs to all of its levels. -/
def Fails (T : MartinLofTest) (X : Cantor) : Prop := ∀ n, X ∈ T.level n

theorem measure_failure (T : MartinLofTest) : fairCoin {X | T.Fails X} = 0 := by
  apply ENNReal.eq_zero_of_le_mul_pow (ε := 1) (r := (1 / 2 : ℝ≥0∞)) (by norm_num)
  intro n
  simpa using (measure_mono (show {X | T.Fails X} ⊆ T.level n from fun _ h => h n)).trans
    (T.measure_le n)

theorem ae_not_fails (T : MartinLofTest) : ∀ᵐ X ∂fairCoin, ¬T.Fails X := by
  simpa only [ae_iff, not_not] using T.measure_failure

instance : Countable MartinLofTest :=
  Function.Injective.countable (f := MartinLofTest.code) (by
    intro T S h
    cases T
    cases S
    cases h
    rfl)

end MartinLofTest

/-- Martin-Löf randomness for the fair-coin measure. -/
def MartinLofRandom (X : Cantor) : Prop := ∀ T : MartinLofTest, ¬T.Fails X

theorem not_martinLofRandom_iff (X : Cantor) :
    ¬MartinLofRandom X ↔ ∃ T : MartinLofTest, T.Fails X := by
  simp [MartinLofRandom]

theorem not_martinLofRandom_of_mem (T : MartinLofTest) {X : Cantor}
    (hX : ∀ n, X ∈ T.level n) : ¬MartinLofRandom X :=
  fun h => h T hX

/-- The usual set-based formulation can be used without manipulating program codes. -/
theorem not_martinLofRandom_of_uniform {U : ℕ → Set Cantor}
    (hU : IsUniformlyEffectivelyOpen U)
    (hbound : ∀ n, fairCoin (U n) ≤ (1 / 2 : ℝ≥0∞) ^ n)
    {X : Cantor} (hX : ∀ n, X ∈ U n) : ¬MartinLofRandom X := by
  obtain ⟨T, hT⟩ := MartinLofTest.exists_of_uniform hU hbound
  apply not_martinLofRandom_of_mem T
  intro n
  change X ∈ programOpen T.code n
  rw [hT n]
  exact hX n

/-- Equivalence with the standard definition using uniformly effectively open sets. -/
theorem martinLofRandom_iff (X : Cantor) :
    MartinLofRandom X ↔
      ∀ U : ℕ → Set Cantor, IsUniformlyEffectivelyOpen U →
        (∀ n, fairCoin (U n) ≤ (1 / 2 : ℝ≥0∞) ^ n) → ∃ n, X ∉ U n := by
  classical
  constructor
  · intro h U hU hb
    by_contra hfail
    have hX : ∀ n, X ∈ U n := by simpa using hfail
    exact not_martinLofRandom_of_uniform hU hb hX h
  · intro h T hf
    obtain ⟨n, hn⟩ := h T.level T.uniform T.measure_le
    exact hn (hf n)

/-- Every individual effective test has a null failure set, and there are countably many codes. -/
theorem ae_martinLofRandom : ∀ᵐ X ∂fairCoin, MartinLofRandom X :=
  ae_all_iff.mpr fun T => T.ae_not_fails

theorem exists_martinLofRandom : ∃ X : Cantor, MartinLofRandom X :=
  ae_martinLofRandom.exists

end Klr
