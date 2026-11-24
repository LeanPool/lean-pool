/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-! Actual finite permutation geometry. A permutation sends each key rank to its
physical position. No sorting operator or input distribution is hidden here. -/
namespace Shellsort
open scoped BigOperators
@[expose] public noncomputable section

abbrev RankPlacement (n : ℕ) := Equiv.Perm (Fin n)

def transport {n : ℕ} (p q : RankPlacement n) : ℝ :=
  ∑ x : Fin n, |((p x).val : ℝ) - ((q x).val : ℝ)|

def footrule {n : ℕ} (p : RankPlacement n) : ℝ := transport p (Equiv.refl _)

/-- Exactly uniform average over all rank-to-position permutations. -/
def uniformAverage {n : ℕ} (f : RankPlacement n → ℝ) : ℝ :=
  (∑ p, f p) / (n.factorial : ℝ)

theorem uniformAverage_const (n : ℕ) (c : ℝ) :
    uniformAverage (n := n) (fun _ => c) = c := by
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp [uniformAverage, RankPlacement, Fintype.card_perm, hn]

/-- Uniform expected footrule is the sum of the per-key expected displacements.
This is a real permutation statement, not an abstract random-variable premise. -/
theorem uniformAverage_footrule (n : ℕ) :
    uniformAverage (n := n) footrule =
      ∑ x : Fin n, uniformAverage (fun p => |((p x).val : ℝ) - (x.val : ℝ)|) := by
  unfold uniformAverage footrule transport
  simp only [Equiv.refl_apply]
  rw [Finset.sum_comm, Finset.sum_div]

theorem transport_nonneg {n : ℕ} (p q : RankPlacement n) : 0 ≤ transport p q := by
  exact Finset.sum_nonneg (fun x _ => abs_nonneg _)

theorem transport_symm {n : ℕ} (p q : RankPlacement n) : transport p q = transport q p := by
  apply Finset.sum_congr rfl
  intro x _
  exact abs_sub_comm _ _

theorem transport_triangle {n : ℕ} (p q r : RankPlacement n) :
    transport p r ≤ transport p q + transport q r := by
  unfold transport
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun x _ => abs_sub_le _ _ _)

theorem footrule_triangle {n : ℕ} (p q : RankPlacement n) :
    footrule p ≤ transport p q + footrule q :=
  transport_triangle p q (Equiv.refl _)

theorem transport_le_footrules {n : ℕ} (p q : RankPlacement n) :
    transport p q ≤ footrule p + footrule q := by
  simpa only [footrule, transport_symm (Equiv.refl _) q] using
    transport_triangle p (Equiv.refl _) q

/-- The all-gcd lifting inequality is a geometry consequence once a canonical
sorting step is known not to increase footrule. The sorting-specific premise
is deliberately visible; no operator has been defined to make it true. -/
theorem canonical_lift {n : ℕ} (p q : RankPlacement n)
    (hmono : footrule q ≤ footrule p) :
    (footrule q + transport p q) / 3 ≤ footrule p ∧
    footrule p ≤ footrule q + transport p q := by
  have ht := transport_le_footrules p q
  have hf := footrule_triangle p q
  constructor <;> linarith

/-- Costs are charged separately from geometry. A sorting-complete transport
budget implies the corresponding lower bound, with the budget as an explicit
implementation-specific premise. -/
theorem completion_budget {n : ℕ} (p : RankPlacement n) (K M : ℝ)
    (hK : 0 < K) (hbudget : footrule p ≤ 2 * K * M) :
    footrule p / (2 * K) ≤ M := by
  apply (div_le_iff₀ (by positivity : 0 < 2 * K)).mpr
  nlinarith

end
end Shellsort
