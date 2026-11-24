/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.CoprimePhase
public import LeanPool.ShellsortMean.MixedPrefix
public import LeanPool.ShellsortMean.ProductWeights

/-!
Finite marginal-mean bridge for the two-pass displacement bound.
The common reference law is used only to sum marginal means. It is NOT
asserted to be the actual joint law and is not used for any variance claim.
-/
@[expose] public section

namespace Shellsort
open scoped BigOperators

/-- The source prefix count scaled by the target gap, centered by the prefix length. -/
def sourceResidualReal (h g j s y : ℕ) : ℝ :=
  (g : ℝ) * sourcePrefixCount h g j s y - y

/-- The mean residual when a Bernoulli bit can extend a reference prefix by one. -/
def referencePrefixMean {B : Type*} [Fintype B] (h g j ell : ℕ)
    (w : B → ℝ) (base : B → ℕ) (t : ℝ) (s : ℕ) : ℝ :=
  (1 - t) * mean w (fun b => sourceResidualReal h g j s (base b)) +
    t * mean w (fun b => sourceResidualReal h g j s
      (if s < ell then base b + 1 else base b))

theorem prefix_mean_bounds {B : Type*} [Fintype B] (w f : B → ℝ)
    (hw0 : ∀ b, 0 ≤ w b) (hw1 : ∑ b, w b = 1) (lo hi : ℝ)
    (hf : ∀ b, lo ≤ f b ∧ f b ≤ hi) :
    lo ≤ mean w f ∧ mean w f ≤ hi := by
  constructor
  · calc
      lo = ∑ b, w b * lo := by rw [← Finset.sum_mul, hw1, one_mul]
      _ ≤ mean w f := Finset.sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_left (hf b).1 (hw0 b)
  · calc
      mean w f ≤ ∑ b, w b * hi := Finset.sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_left (hf b).2 (hw0 b)
      _ = hi := by rw [← Finset.sum_mul, hw1, one_mul]

theorem prefix_convex_bounds (t x y lo hi : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : lo ≤ x ∧ x ≤ hi) (hy : lo ≤ y ∧ y ≤ hi) :
    lo ≤ (1 - t) * x + t * y ∧ (1 - t) * x + t * y ≤ hi := by
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hx0 := mul_le_mul_of_nonneg_left hx.1 ht'
  have hx1 := mul_le_mul_of_nonneg_left hx.2 ht'
  have hy0 := mul_le_mul_of_nonneg_left hy.1 ht0
  have hy1 := mul_le_mul_of_nonneg_left hy.2 ht0
  constructor <;> nlinarith

theorem prefix_mean_finset_sum {B I : Type*} [Fintype B] (w : B → ℝ)
    (S : Finset I) (f : I → B → ℝ) :
    mean w (fun b => ∑ s ∈ S, f s b) = ∑ s ∈ S, mean w (f s) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem prefix_mean_shift_sum {B I : Type*} [Fintype B] (w : B → ℝ)
    (hw1 : ∑ b, w b = 1) (S : Finset I) (f : I → B → ℝ) (c : ℝ) :
    mean w (fun b => c + ∑ s ∈ S, f s b) = c + ∑ s ∈ S, mean w (f s) := by
  rw [mean_add, mean_const w hw1, prefix_mean_finset_sum]

theorem complete_prefix_real_balance (h g j b : ℕ) (hg : 0 < g) (hj : j < g) :
    0 ≤ (j : ℝ) + ∑ s ∈ Finset.range h, sourceResidualReal h g j s b ∧
    (j : ℝ) + (∑ s ∈ Finset.range h, sourceResidualReal h g j s b) ≤ (g : ℝ) - 1 := by
  have hb := complete_prefix_balance h g j b hg hj
  unfold sourceResidualReal
  constructor
  · exact_mod_cast hb.1
  · exact_mod_cast hb.2

theorem mixed_prefix_real_balance (h g j b ell : ℕ) (hell : ell ≤ h)
    (hg : 0 < g) (hj : j < g) :
    0 ≤ (j : ℝ) + ∑ s ∈ Finset.range h,
      sourceResidualReal h g j s (if s < ell then b + 1 else b) ∧
    (j : ℝ) + (∑ s ∈ Finset.range h,
      sourceResidualReal h g j s (if s < ell then b + 1 else b)) ≤ (g : ℝ) - 1 := by
  have hb := mixed_prefix_balance h g j b ell hell hg hj
  unfold sourceResidualReal
  constructor
  · exact_mod_cast hb.1
  · exact_mod_cast hb.2

/-- Linear expectation permits a common reference coupling for marginal means. -/
theorem referencePrefixMean_total_eq {B : Type*} [Fintype B]
    (h g j ell : ℕ) (w : B → ℝ) (base : B → ℕ) (t : ℝ)
    (hw1 : ∑ b, w b = 1) :
    (j : ℝ) + (∑ s ∈ Finset.range h, referencePrefixMean h g j ell w base t s) =
      (1 - t) * mean w (fun b => (j : ℝ) +
        ∑ s ∈ Finset.range h, sourceResidualReal h g j s (base b)) +
      t * mean w (fun b => (j : ℝ) + ∑ s ∈ Finset.range h,
        sourceResidualReal h g j s (if s < ell then base b + 1 else base b)) := by
  rw [prefix_mean_shift_sum w hw1, prefix_mean_shift_sum w hw1]
  simp only [referencePrefixMean, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- No balance premise is supplied: it follows from actual complete and mixed prefixes. -/
theorem referencePrefixMean_balance {B : Type*} [Fintype B]
    (h g j ell : ℕ) (w : B → ℝ) (base : B → ℕ) (t : ℝ)
    (hw0 : ∀ b, 0 ≤ w b) (hw1 : ∑ b, w b = 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hell : ell ≤ h) (hg : 0 < g) (hj : j < g) :
    0 ≤ (j : ℝ) + (∑ s ∈ Finset.range h, referencePrefixMean h g j ell w base t s) ∧
    (j : ℝ) + (∑ s ∈ Finset.range h, referencePrefixMean h g j ell w base t s) ≤
      (g : ℝ) - 1 := by
  have hb0 := prefix_mean_bounds w
    (fun b => (j : ℝ) + ∑ s ∈ Finset.range h, sourceResidualReal h g j s (base b))
    hw0 hw1 0 ((g : ℝ) - 1) (fun b => complete_prefix_real_balance h g j (base b) hg hj)
  have hb1 := prefix_mean_bounds w
    (fun b => (j : ℝ) + ∑ s ∈ Finset.range h,
      sourceResidualReal h g j s (if s < ell then base b + 1 else base b))
    hw0 hw1 0 ((g : ℝ) - 1)
    (fun b => mixed_prefix_real_balance h g j (base b) ell hell hg hj)
  rw [referencePrefixMean_total_eq h g j ell w base t hw1]
  exact prefix_convex_bounds t _ _ 0 ((g : ℝ) - 1) ht0 ht1 hb0 hb1

theorem source_residual_owner_correction_real_bounds (h g s y b : ℕ)
    (hg : 0 < g) (hc : Nat.Coprime h g) :
    -((g : ℝ) - 1) ≤ sourceResidualReal h g ((s + h * y) % g) s y -
      sourceResidualReal h g ((s + h * y) % g) s b ∧
    sourceResidualReal h g ((s + h * y) % g) s y -
      sourceResidualReal h g ((s + h * y) % g) s b ≤ 0 := by
  have hb := source_residual_owner_correction_bounds h g s y b hg hc
  unfold sourceResidualReal
  constructor
  · exact_mod_cast hb.1
  · exact_mod_cast hb.2

theorem owner_minus_referencePrefixMean_bounds {B : Type*} [Fintype B]
    (h g ell s y : ℕ) (w : B → ℝ) (base : B → ℕ) (t : ℝ)
    (hw0 : ∀ b, 0 ≤ w b) (hw1 : ∑ b, w b = 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hg : 0 < g) (hc : Nat.Coprime h g) :
    -((g : ℝ) - 1) ≤ sourceResidualReal h g ((s + h * y) % g) s y -
      referencePrefixMean h g ((s + h * y) % g) ell w base t s ∧
    sourceResidualReal h g ((s + h * y) % g) s y -
      referencePrefixMean h g ((s + h * y) % g) ell w base t s ≤ 0 := by
  let j := (s + h * y) % g
  let c := sourceResidualReal h g j s y
  have hb0 := prefix_mean_bounds w (fun b => c - sourceResidualReal h g j s (base b))
    hw0 hw1 (-((g : ℝ) - 1)) 0
    (fun b => source_residual_owner_correction_real_bounds h g s y (base b) hg hc)
  have hb1 := prefix_mean_bounds w
    (fun b => c - sourceResidualReal h g j s (if s < ell then base b + 1 else base b))
    hw0 hw1 (-((g : ℝ) - 1)) 0
    (fun b => source_residual_owner_correction_real_bounds h g s y
      (if s < ell then base b + 1 else base b) hg hc)
  rw [mean_sub, mean_const w hw1] at hb0 hb1
  have hcmean := prefix_convex_bounds t _ _ (-((g : ℝ) - 1)) 0 ht0 ht1 hb0 hb1
  change - ((g : ℝ) - 1) ≤ c - referencePrefixMean h g j ell w base t s ∧
    c - referencePrefixMean h g j ell w base t s ≤ 0
  unfold referencePrefixMean
  constructor <;> nlinarith [hcmean.1, hcmean.2]

/-- The actual owner replaces exactly one reference mean in the finite source sum. -/
theorem owner_replaced_referencePrefixMean_bound {B : Type*} [Fintype B]
    (h g ell owner y : ℕ) (w : B → ℝ) (base : B → ℕ) (t : ℝ)
    (hw0 : ∀ b, 0 ≤ w b) (hw1 : ∑ b, w b = 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hell : ell ≤ h) (howner : owner < h)
    (hg : 0 < g) (hc : Nat.Coprime h g) :
    |(((owner + h * y) % g : ℕ) : ℝ) + ∑ s ∈ Finset.range h,
      if s = owner then sourceResidualReal h g ((owner + h * y) % g) owner y
      else referencePrefixMean h g ((owner + h * y) % g) ell w base t s| ≤
      (g : ℝ) - 1 := by
  let j := (owner + h * y) % g
  let c := sourceResidualReal h g j owner y
  let m := referencePrefixMean h g j ell w base t
  have hb := referencePrefixMean_balance h g j ell w base t hw0 hw1 ht0 ht1 hell hg
    (Nat.mod_lt _ hg)
  have hcmean := owner_minus_referencePrefixMean_bounds h g ell owner y w base t
    hw0 hw1 ht0 ht1 hg hc
  have hsum : (∑ s ∈ Finset.range h, if s = owner then c else m s) =
      (∑ s ∈ Finset.range h, m s) + c - m owner := by
    calc
      (∑ s ∈ Finset.range h, if s = owner then c else m s) =
          ∑ s ∈ Finset.range h, (m s + if s = owner then c - m owner else 0) := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : s = owner <;> simp [hs]
      _ = (∑ s ∈ Finset.range h, m s) + c - m owner := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_range, howner, ite_true]
        ring
  change |(j : ℝ) + ∑ s ∈ Finset.range h, if s = owner then c else m s| ≤ (g : ℝ) - 1
  rw [hsum, abs_le]
  change - ((g : ℝ) - 1) ≤ (j : ℝ) + ((∑ s ∈ Finset.range h, m s) + c - m owner) ∧
    (j : ℝ) + ((∑ s ∈ Finset.range h, m s) + c - m owner) ≤ (g : ℝ) - 1
  change 0 ≤ (j : ℝ) + (∑ s ∈ Finset.range h, m s) ∧
    (j : ℝ) + (∑ s ∈ Finset.range h, m s) ≤ (g : ℝ) - 1 at hb
  change - ((g : ℝ) - 1) ≤ c - m owner ∧ c - m owner ≤ 0 at hcmean
  constructor <;> linarith [hb.1, hb.2, hcmean.1, hcmean.2]

end Shellsort
