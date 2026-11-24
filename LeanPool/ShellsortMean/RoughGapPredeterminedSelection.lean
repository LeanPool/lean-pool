/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.RoughGapEndpoint
public import LeanPool.ShellsortMean.ActualCostComposition
public import LeanPool.ShellsortMean.GapComparisonBridge
public import Mathlib.Algebra.Order.Chebyshev

/-! Average over initial rank permutations, with an arbitrary predetermined
prefix state map, and select one common next gap before the input is drawn. -/
@[expose] public noncomputable section
namespace Shellsort.RoughGapSelection
open Finset

def mass {n : ℕ} (p : RankPlacement n) : ℝ := footrule p / n
def energy {n : ℕ} (p : RankPlacement n) : ℝ :=
  (RoughGapScaleAssembly.squareDisplacement p : ℝ) / n

theorem mass_sq_le_energy {n : ℕ} (hn : 0 < n) (p : RankPlacement n) :
    mass p ^ 2 ≤ energy p := by
  let f := fun i : Fin n => ((p i).val : ℝ) - i.val
  have c := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun i => |f i|)
  have cs : footrule p ^ 2 ≤ (n : ℝ) * ∑ i, (f i) ^ 2 := by
    simpa [footrule, transport, f, sq_abs] using c
  have E : (RoughGapScaleAssembly.squareDisplacement p : ℝ) = ∑ i, (f i) ^ 2 := by
    simp [RoughGapScaleAssembly.squareDisplacement, f]
  have N : (0 : ℝ) < n := by exact_mod_cast hn
  unfold mass energy
  rw [E, div_pow, div_le_div_iff₀ (sq_pos_of_pos N) N]
  nlinarith [mul_le_mul_of_nonneg_right cs N.le]

private theorem uniform_sq_mean {n : ℕ} (f : RankPlacement n → ℝ) :
    uniformAverage f ^ 2 ≤ uniformAverage (fun p => f p ^ 2) := by
  have c := sq_sum_le_card_mul_sum_sq (s := univ) (f := f)
  have cs : (∑ p, f p) ^ 2 ≤ (n.factorial : ℝ) * ∑ p, (f p) ^ 2 := by
    simpa [RankPlacement, Fintype.card_perm] using c
  have N : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  unfold uniformAverage
  rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos N) N]
  nlinarith [mul_le_mul_of_nonneg_right cs N.le]

/-- The post-prefix array may have a nonuniform law. Its map is kept
inside every original-input expectation. -/
theorem prefix_mean_mass_le_root_energy {n : ℕ} (hn : 0 < n)
    (P : RankPlacement n → RankPlacement n) :
    uniformAverage (fun p => mass (P p)) ≤ Real.sqrt (uniformAverage (fun p => energy (P p))) := by
  apply Real.le_sqrt_of_sq_le
  apply (uniform_sq_mean _).trans
  exact uniformAverage_mono _ _ (fun p => mass_sq_le_energy hn (P p))

/-- One fixed element of a nonempty finite menu works for all initial inputs
after averaging them. The statewise premise considers a common uniform menu. -/
theorem select_common_gap {n : ℕ} (P : RankPlacement n → RankPlacement n)
    (G : Finset ℕ) (nonempty : G.Nonempty) (bound : RankPlacement n → ℝ)
    (step : ∀ p, (∑ h ∈ G, energy (gapSort (P p) h)) / G.card ≤ bound (P p)) :
    ∃ h ∈ G, uniformAverage (fun p => energy (gapSort (P p) h)) ≤
      uniformAverage (fun p => bound (P p)) := by
  have Gpos : (0 : ℝ) < G.card := by exact_mod_cast card_pos.mpr nonempty
  let next := fun h (p : RankPlacement n) => energy (gapSort (P p) h)
  have hx : uniformAverage (fun p => ∑ h ∈ G, next h p) ≤
      uniformAverage (fun p => (G.card : ℝ) * bound (P p)) :=
    uniformAverage_mono _ _ (fun p => by
      simpa [next, mul_comm] using (div_le_iff₀ Gpos).mp (step p))
  have left : uniformAverage (fun p => ∑ h ∈ G, next h p) = ∑ h ∈ G, uniformAverage (next h) := by
    unfold uniformAverage
    rw [sum_comm, sum_div]
  rw [left, uniformAverage_const_mul] at hx
  by_contra! no
  have contr := sum_lt_sum_of_nonempty nonempty (fun h hh => no h hh)
  simp only [sum_const, nsmul_eq_mul] at contr
  exact (not_lt_of_ge hx) contr

/-- Conditional contraction with the square-root recurrence in the normalized
true-state energy, for one common predetermined gap. -/
theorem select_common_contraction {n : ℕ} (hn : 0 < n)
    (P : RankPlacement n → RankPlacement n) (G : Finset ℕ) (nonempty : G.Nonempty)
    (α K : ℝ) (hK : 0 ≤ K)
    (step : ∀ p, (∑ h ∈ G, energy (gapSort (P p) h)) / G.card ≤
      α * energy (P p) + K * mass (P p)) :
    ∃ h ∈ G, uniformAverage (fun p => energy (gapSort (P p) h)) ≤
      α * uniformAverage (fun p => energy (P p)) +
      K * Real.sqrt (uniformAverage (fun p => energy (P p))) := by
  obtain ⟨h, hg, sel⟩ := select_common_gap P G nonempty (fun q => α * energy q + K * mass q) step
  refine ⟨h, hg, sel.trans ?_⟩
  rw [uniformAverage_add, uniformAverage_const_mul, uniformAverage_const_mul]
  gcongr
  exact prefix_mean_mass_le_root_energy hn P

theorem prefix_mean_comparisons {n h : ℕ} (hn : 0 < n) (hh : 0 < h)
    (P : RankPlacement n → RankPlacement n) :
    uniformAverage (fun p => (gapComparisonCost (P p) h hh : ℝ) / n) ≤
      1 + (2 / (h : ℝ)) * Real.sqrt (uniformAverage (fun p => energy (P p))) := by
  have N : (0 : ℝ) < n := by exact_mod_cast hn
  have H : (0 : ℝ) < h := by exact_mod_cast hh
  have path (p : RankPlacement n) : (gapComparisonCost (P p) h hh : ℝ) / n ≤
      1 + (2 / (h : ℝ)) * mass (P p) := by
    have ins := gapInsertionCost_le_two_footrule_div (P p) h hh
    have cmp : (gapComparisonCost (P p) h hh : ℝ) ≤ (gapInsertionCost (P p) h hh : ℝ) + n := by
      exact_mod_cast gapComparisonCost_upper (P p) h hh
    unfold mass
    apply (div_le_iff₀ N).mpr
    field_simp [N.ne', H.ne'] at ins ⊢
    nlinarith [mul_le_mul_of_nonneg_right cmp H.le]
  apply (uniformAverage_mono _ _ path).trans
  rw [uniformAverage_add, uniformAverage_const, uniformAverage_const_mul]
  gcongr
  exact prefix_mean_mass_le_root_energy hn P





end Shellsort.RoughGapSelection
