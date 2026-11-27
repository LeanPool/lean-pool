/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.ScanMeasure
public import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-!
# The maximal inequality for adaptive fair capital

Finite hitting events are expanded down the transcript tree. Fairness preserves
the capital-weighted cylinder mass at each split. This gives the probability
bound for ever exceeding `2^m`, without introducing a separate filtration.
-/

@[expose] public section

namespace Klr.CapitalProcess

open MeasureTheory
open scoped ENNReal

/-- Inputs on which the capital ever strictly exceeds a threshold. -/
def exceeds (d : CapitalProcess) (π : ScanRule) (a : ℝ) : Set Cantor :=
  {X | ∃ n, a < d.value (π.transcript X n)}

/-- The finite transcript subtree obtained by stopping as soon as capital exceeds `a`. -/
noncomputable def finiteHit (d : CapitalProcess) (π : ScanRule) (a : ℝ) :
    List Bool → ℕ → Set Cantor
  | v, 0 => if a < d.value v then {X | π.transcript X v.length = v} else ∅
  | v, n + 1 => if a < d.value v then {X | π.transcript X v.length = v}
      else d.finiteHit π a (v ++ [false]) n ∪ d.finiteHit π a (v ++ [true]) n

theorem weighted_children (d : CapitalProcess) (v : List Bool) :
    ENNReal.ofReal (d.value (v ++ [false])) * (1 / 2 : ℝ≥0∞) ^ (v ++ [false]).length +
      ENNReal.ofReal (d.value (v ++ [true])) * (1 / 2 : ℝ≥0∞) ^ (v ++ [true]).length =
      ENNReal.ofReal (d.value v) * (1 / 2 : ℝ≥0∞) ^ v.length := by
  simp only [List.length_append, List.length_singleton]
  rw [← add_mul, ← ENNReal.ofReal_add (d.nonneg _) (d.nonneg _), d.fair,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), pow_succ]
  norm_num only [ENNReal.ofReal_ofNat]
  calc
    2 * ENNReal.ofReal (d.value v) * ((1 / 2 : ℝ≥0∞) ^ v.length * (1 / 2)) =
        ENNReal.ofReal (d.value v) * (1 / 2 : ℝ≥0∞) ^ v.length * (2 * (1 / 2)) := by
          ac_rfl
    _ = _ := by
      rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

/-- The weighted maximal inequality on every finite transcript subtree. -/
theorem finiteHit_bound (d : CapitalProcess) (π : ScanRule) (a : ℝ)
    (v : List Bool) (n : ℕ) :
    ENNReal.ofReal a * fairCoin (d.finiteHit π a v n) ≤
      ENNReal.ofReal (d.value v) * (1 / 2 : ℝ≥0∞) ^ v.length := by
  induction n generalizing v with
  | zero =>
    by_cases h : a < d.value v
    · simp only [finiteHit, ite_eq_left h, π.fairCoin_transcript]
      gcongr
    · simp [finiteHit, h]
  | succ n ih =>
    by_cases h : a < d.value v
    · simp only [finiteHit, ite_eq_left h, π.fairCoin_transcript]
      gcongr
    · rw [finiteHit, ite_eq_right h]
      calc
        _ ≤ ENNReal.ofReal a * (fairCoin (d.finiteHit π a (v ++ [false]) n) +
            fairCoin (d.finiteHit π a (v ++ [true]) n)) :=
          by
            gcongr
            exact measure_union_le _ _
        _ = _ := mul_add _ _ _
        _ ≤ _ := add_le_add (ih (v ++ [false])) (ih (v ++ [true]))
        _ = _ := d.weighted_children v

theorem finiteHit_subset_exceeds (d : CapitalProcess) (π : ScanRule) (a : ℝ)
    (v : List Bool) (n : ℕ) : d.finiteHit π a v n ⊆ d.exceeds π a := by
  induction n generalizing v with
  | zero =>
    by_cases h : a < d.value v
    · intro X hX
      have hv : π.transcript X v.length = v := by simpa [finiteHit, h] using hX
      exact ⟨v.length, by simpa [hv] using h⟩
    · simp [finiteHit, h]
  | succ n ih =>
    by_cases h : a < d.value v
    · intro X hX
      have hv : π.transcript X v.length = v := by simpa [finiteHit, h] using hX
      exact ⟨v.length, by simpa [hv] using h⟩
    · simpa only [finiteHit, ite_eq_right h] using Set.union_subset (ih _) (ih _)

theorem mem_finiteHit_of_prefix (d : CapitalProcess) (π : ScanRule) (a : ℝ)
    (X : Cantor) (v : List Bool) (n : ℕ) (hv : π.transcript X v.length = v)
    (h : ∃ k ≤ n, a < d.value (π.transcript X (v.length + k))) :
    X ∈ d.finiteHit π a v n := by
  induction n generalizing v with
  | zero =>
    obtain ⟨k, hk, h⟩ := h
    have : k = 0 := by omega
    subst k
    have ha : a < d.value v := by simpa [hv] using h
    simpa [finiteHit, ha] using hv
  | succ n ih =>
    by_cases ha : a < d.value v
    · simpa [finiteHit, ha] using hv
    · obtain ⟨k, hk, h⟩ := h
      have hk0 : k ≠ 0 := by
        intro heq
        subst k
        exact ha (by simpa [hv] using h)
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      let b := X (π.query v)
      have hvb : π.transcript X (v ++ [b]).length = v ++ [b] := by
        simp [ScanRule.transcript_succ, hv, b]
      have hb : X ∈ d.finiteHit π a (v ++ [b]) n := by
        apply ih (v ++ [b]) hvb
        refine ⟨j, by omega, ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using h
      rw [finiteHit, ite_eq_right ha]
      cases hbval : b
      · exact Or.inl (by simpa [hbval] using hb)
      · exact Or.inr (by simpa [hbval] using hb)

theorem finiteHit_mono (d : CapitalProcess) (π : ScanRule) (a : ℝ) (v : List Bool) :
    Monotone (d.finiteHit π a v) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing v with
  | zero =>
    by_cases h : a < d.value v <;> simp [finiteHit, h]
  | succ n ih =>
    by_cases h : a < d.value v
    · simp [finiteHit, h]
    · simp only [finiteHit, ite_eq_right h]
      exact Set.union_subset_union (ih _) (ih _)

theorem exceeds_eq_iUnion_finiteHit (d : CapitalProcess) (π : ScanRule) (a : ℝ) :
    d.exceeds π a = ⋃ n, d.finiteHit π a [] n := by
  ext X
  constructor
  · rintro ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, d.mem_finiteHit_of_prefix π a X [] n (by simp)
      ⟨n, le_rfl, by simpa using hn⟩⟩
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact d.finiteHit_subset_exceeds π a [] n hn

/-- Every adaptive fair strategy exceeds `2^m` on a set of measure at most `2^-m`. -/
theorem measure_exceeds_pow_le (d : CapitalProcess) (π : ScanRule) (m : ℕ) :
    fairCoin (d.exceeds π ((2 : ℝ) ^ m)) ≤ (1 / 2 : ℝ≥0∞) ^ m := by
  rw [d.exceeds_eq_iUnion_finiteHit, (d.finiteHit_mono π ((2 : ℝ) ^ m) []).measure_iUnion]
  apply iSup_le
  intro n
  have h := d.finiteHit_bound π ((2 : ℝ) ^ m) [] n
  simp only [d.initial, ENNReal.ofReal_one, List.length_nil, pow_zero, mul_one,
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] at h
  have hc : (1 / 2 : ℝ≥0∞) ^ m * (2 : ℝ≥0∞) ^ m = 1 := by
    rw [← mul_pow, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  calc
    _ = (1 / 2 : ℝ≥0∞) ^ m *
        ((2 : ℝ≥0∞) ^ m * fairCoin (d.finiteHit π ((2 : ℝ) ^ m) [] n)) := by
      rw [← mul_assoc, hc, one_mul]
    _ ≤ (1 / 2 : ℝ≥0∞) ^ m * 1 := by gcongr
    _ = _ := mul_one _

end Klr.CapitalProcess
