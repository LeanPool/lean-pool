/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.BernoulliCounts
public import LeanPool.ShellsortMean.PrefixMean
public import LeanPool.ShellsortMean.SourceVariance

/-!
An explicit independent Bernoulli model for all non-owner source counts.
The owner coordinate is retained with a normalized dummy law, but its residual
is a fixed constant. This is a finite conditional source model, not a theorem
identifying this law with uniform random permutations or actual sorting costs.
-/
@[expose] public section

namespace Shellsort
open scoped BigOperators

def sourceTrialLength (m ell s : ℕ) : ℕ := if s < ell then m + 1 else m

def sourceCoordinateWeight (h m ell : ℕ) (t : ℝ) (s : Fin h)
    (x : Fin (sourceTrialLength m ell s.val) → Bool) : ℝ :=
  bernoulliVectorWeight t (sourceTrialLength m ell s.val) x

def conditionalSourceWeight (h m ell : ℕ) (t : ℝ)
    (x : ∀ s : Fin h, Fin (sourceTrialLength m ell s.val) → Bool) : ℝ :=
  productWeight (sourceCoordinateWeight h m ell t) x

def conditionalSourceResidual (h g m ell : ℕ) (owner : Fin h) (y : ℕ)
    (s : Fin h) (x : Fin (sourceTrialLength m ell s.val) → Bool) : ℝ :=
  if s = owner then sourceResidualReal h g ((owner.val + h * y) % g) owner.val y
  else sourceResidualReal h g ((owner.val + h * y) % g) s.val (bitCount x)

def conditionalSourceDisplacement (h g m ell : ℕ) (owner : Fin h) (y : ℕ)
    (x : ∀ s : Fin h, Fin (sourceTrialLength m ell s.val) → Bool) : ℝ :=
  (((owner.val + h * y) % g : ℕ) : ℝ) +
    ∑ s, conditionalSourceResidual h g m ell owner y s (x s)

theorem sourceCoordinateWeight_nonneg (h m ell : ℕ) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) (s : Fin h)
    (x : Fin (sourceTrialLength m ell s.val) → Bool) :
    0 ≤ sourceCoordinateWeight h m ell t s x :=
  bernoulliVectorWeight_nonneg t ht _ x

theorem sourceCoordinateWeight_sum (h m ell : ℕ) (t : ℝ) (s : Fin h) :
    ∑ x, sourceCoordinateWeight h m ell t s x = 1 :=
  bernoulliVectorWeight_sum t _

theorem conditionalSourceWeight_nonneg (h m ell : ℕ) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1)
    (x : ∀ s : Fin h, Fin (sourceTrialLength m ell s.val) → Bool) :
    0 ≤ conditionalSourceWeight h m ell t x := by
  exact productWeight_nonneg _ (sourceCoordinateWeight_nonneg h m ell t ht) x

theorem conditionalSourceWeight_sum (h m ell : ℕ) (t : ℝ) :
    ∑ x, conditionalSourceWeight h m ell t x = 1 := by
  exact productWeight_sum _ (sourceCoordinateWeight_sum h m ell t)

/-- Each genuine chain marginal has exactly the common-reference mean. -/
theorem bernoulli_source_mean_eq_reference (h g j m ell s : ℕ) (t : ℝ) :
    mean (bernoulliVectorWeight t (sourceTrialLength m ell s))
        (fun x => sourceResidualReal h g j s (bitCount x)) =
      referencePrefixMean h g j ell (bernoulliVectorWeight t m) bitCount t s := by
  let E : ℕ → ℝ := fun L => mean (bernoulliVectorWeight t L)
    (fun x => sourceResidualReal h g j s (bitCount x))
  change E (sourceTrialLength m ell s) = _
  by_cases hs : s < ell
  · rw [show sourceTrialLength m ell s = m + 1 by simp [sourceTrialLength, hs]]
    simp only [E, referencePrefixMean, hs, ite_true]
    exact bernoulli_count_succ_mean t m (sourceResidualReal h g j s)
  · rw [show sourceTrialLength m ell s = m by simp [sourceTrialLength, hs]]
    simp only [E, referencePrefixMean, hs, ite_false]
    ring

theorem conditionalSourceResidual_mean (h g m ell : ℕ) (t : ℝ)
    (owner : Fin h) (y : ℕ) (s : Fin h) :
    mean (sourceCoordinateWeight h m ell t s)
        (conditionalSourceResidual h g m ell owner y s) =
      if s = owner then sourceResidualReal h g ((owner.val + h * y) % g) owner.val y
      else referencePrefixMean h g ((owner.val + h * y) % g) ell
        (bernoulliVectorWeight t m) bitCount t s.val := by
  unfold conditionalSourceResidual sourceCoordinateWeight
  by_cases hs : s = owner
  · simp only [hs, ite_true, mean_const _ (bernoulliVectorWeight_sum t _)]
  · simp only [hs, ite_false]
    exact bernoulli_source_mean_eq_reference h g _ m ell s.val t

theorem conditionalSourceDisplacement_mean (h g m ell : ℕ) (t : ℝ)
    (owner : Fin h) (y : ℕ) :
    mean (conditionalSourceWeight h m ell t) (conditionalSourceDisplacement h g m ell owner y) =
      (((owner.val + h * y) % g : ℕ) : ℝ) +
      ∑ s : Fin h, if s = owner then sourceResidualReal h g ((owner.val + h * y) % g) owner.val y
      else referencePrefixMean h g ((owner.val + h * y) % g) ell
        (bernoulliVectorWeight t m) bitCount t s.val := by
  unfold conditionalSourceDisplacement
  rw [mean_add, mean_const _ (conditionalSourceWeight_sum h m ell t)]
  unfold conditionalSourceWeight
  rw [productWeight_mean_sum _ _ (sourceCoordinateWeight_sum h m ell t)]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact conditionalSourceResidual_mean h g m ell t owner y s

/-- The mean estimate is derived for the explicit product law, not assumed. -/
theorem conditionalSourceDisplacement_mean_bound (h g m ell : ℕ) (t : ℝ)
    (owner : Fin h) (y : ℕ) (ht : 0 ≤ t ∧ t ≤ 1) (hell : ell ≤ h)
    (hg : 0 < g) (hc : Nat.Coprime h g) :
    |mean (conditionalSourceWeight h m ell t)
      (conditionalSourceDisplacement h g m ell owner y)| ≤ (g : ℝ) - 1 := by
  rw [conditionalSourceDisplacement_mean]
  have hb := owner_replaced_referencePrefixMean_bound h g ell owner.val y
    (bernoulliVectorWeight t m) bitCount t
    (bernoulliVectorWeight_nonneg t ht m) (bernoulliVectorWeight_sum t m)
    ht.1 ht.2 hell owner.isLt hg hc
  simpa only [← Fin.sum_univ_eq_sum_range, ← Fin.ext_iff] using hb

theorem source_sum_except_owner (h : ℕ) (owner : Fin h) (v : ℝ) :
    (∑ s : Fin h, if s = owner then 0 else v) = ((h : ℝ) - 1) * v := by
  calc
    (∑ s : Fin h, if s = owner then 0 else v) =
        ∑ s : Fin h, (v - if s = owner then v else 0) := by
      apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> ring
    _ = ((h : ℝ) - 1) * v := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring

/-- The owner coordinate contributes zero variance; every other range has width g-1. -/
theorem conditionalSourceResidual_variance_bound (h g m ell : ℕ) (t : ℝ)
    (owner : Fin h) (y : ℕ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hg : 0 < g) (hc : Nat.Coprime h g) (s : Fin h) :
    centeredSecond (sourceCoordinateWeight h m ell t s)
      (conditionalSourceResidual h g m ell owner y s) ≤
      if s = owner then 0 else ((g : ℝ) - 1) ^ 2 / 4 := by
  let j := (owner.val + h * y) % g
  by_cases hs : s = owner
  · subst s
    unfold conditionalSourceResidual
    simp only [ite_true]
    have hv := centeredSecond_le_range (sourceCoordinateWeight h m ell t owner)
      (fun _ => sourceResidualReal h g j owner.val y)
      (sourceCoordinateWeight_nonneg h m ell t ht owner)
      (sourceCoordinateWeight_sum h m ell t owner)
      (sourceResidualReal h g j owner.val y) (sourceResidualReal h g j owner.val y)
      (fun _ => ⟨le_rfl, le_rfl⟩)
    simpa only [sub_self, zero_pow (by omega : 2 ≠ 0), zero_div] using hv
  · unfold conditionalSourceResidual
    simp only [hs, ite_false]
    obtain ⟨a, ha⟩ := exists_source_residual_interval_real h g j s.val hg hc (Nat.mod_lt _ hg)
    have hv := centeredSecond_le_range (sourceCoordinateWeight h m ell t s)
      (fun x => sourceResidualReal h g j s.val (bitCount x))
      (sourceCoordinateWeight_nonneg h m ell t ht s)
      (sourceCoordinateWeight_sum h m ell t s) a (a + ((g : ℝ) - 1))
      (fun x => ha (bitCount x))
    simpa only [add_sub_cancel_left] using hv

/-- This variance belongs to the explicit independent source law, not the reference coupling. -/
theorem conditionalSourceDisplacement_variance_bound (h g m ell : ℕ) (t : ℝ)
    (owner : Fin h) (y : ℕ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hg : 0 < g) (hc : Nat.Coprime h g) :
    centeredSecond (conditionalSourceWeight h m ell t)
      (conditionalSourceDisplacement h g m ell owner y) ≤
      ((h : ℝ) - 1) * ((g : ℝ) - 1) ^ 2 / 4 := by
  unfold conditionalSourceDisplacement
  rw [centeredSecond_add_const _ _ (conditionalSourceWeight_sum h m ell t)]
  unfold conditionalSourceWeight
  rw [productWeight_variance_sum _ _ (sourceCoordinateWeight_sum h m ell t)]
  calc
    _ ≤ ∑ s : Fin h, if s = owner then 0 else ((g : ℝ) - 1) ^ 2 / 4 := by
      exact Finset.sum_le_sum (fun s _ =>
        conditionalSourceResidual_variance_bound h g m ell t owner y ht hg hc s)
    _ = ((h : ℝ) - 1) * ((g : ℝ) - 1) ^ 2 / 4 := by
      rw [source_sum_except_owner]
      ring

/-- Finite conditional two-pass L1 bound. Its mean and variance are proved above;
the remaining application bridge is identifying a sorting input with this law. -/
theorem conditionalSourceDisplacement_absMean_bound (h g m ell : ℕ) (t : ℝ)
    (owner : Fin h) (y : ℕ) (ht : 0 ≤ t ∧ t ≤ 1) (hell : ell ≤ h)
    (hg : 0 < g) (hc : Nat.Coprime h g) :
    mean (conditionalSourceWeight h m ell t)
      (fun x => |conditionalSourceDisplacement h g m ell owner y x|) ≤
      ((g : ℝ) - 1) * Real.sqrt ((h : ℝ) + 3) / 2 := by
  have hh : 1 ≤ (h : ℝ) := by
    have hhN : 1 ≤ h := by have := owner.isLt; omega
    exact_mod_cast hhN
  have hg' : 1 ≤ (g : ℝ) := by exact_mod_cast hg
  exact twoPass_moment_interface (conditionalSourceWeight h m ell t)
    (conditionalSourceDisplacement h g m ell owner y)
    (conditionalSourceWeight_nonneg h m ell t ht) (conditionalSourceWeight_sum h m ell t)
    h g hh hg'
    (conditionalSourceDisplacement_mean_bound h g m ell t owner y ht hell hg hc)
    (conditionalSourceDisplacement_variance_bound h g m ell t owner y ht hg hc)

end Shellsort
