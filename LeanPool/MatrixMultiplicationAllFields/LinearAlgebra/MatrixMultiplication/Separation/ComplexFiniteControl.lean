/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Combinatorics.Additive.AP.Three.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation
namespace FiniteControl

open scoped BigOperators

theorem every_path_safe {State : Type*} (Safe : ℕ → State → Prop)
    (Allows : ℕ → State → State → Prop) (n : ℕ) (path : ℕ → State)
    (initial : Safe 0 (path 0))
    (closed : ∀ t < n, ∀ s s', Safe t s → Allows t s s' → Safe (t + 1) s')
    (steps : ∀ t < n, Allows t (path t) (path (t + 1))) :
    ∀ t ≤ n, Safe t (path t) := by
  intro t
  induction t with
  | zero => intro _; exact initial
  | succ t ih =>
      intro ht
      have htn : t < n := Nat.lt_of_succ_le ht
      exact closed t htn (path t) (path (t + 1))
        (ih (Nat.le_of_lt htn)) (steps t htn)

theorem exists_population_preserving_equiv {I J Node : Type*}
    [Fintype I] [Fintype J] [DecidableEq Node]
    (f : I → Node) (g : J → Node)
    (counts : ∀ node, Fintype.card {i // f i = node} =
      Fintype.card {j // g j = node}) :
    ∃ e : I ≃ J, ∀ i, g (e i) = f i := by
  classical
  let ef : ∀ node, {i // f i = node} ≃ {j // g j = node} :=
    fun node => Fintype.equivOfCardEq (counts node)
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight ef).trans (Equiv.sigmaFiberEquiv g)), ?_⟩
  intro i
  exact (ef (f i) ⟨i, rfl⟩).property

theorem population_product_eq {I J Node M : Type*}
    [Fintype I] [Fintype J] [DecidableEq Node] [CommMonoid M]
    (f : I → Node) (g : J → Node)
    (counts : ∀ node, Fintype.card {i // f i = node} =
      Fintype.card {j // g j = node}) (cost : Node → M) :
    (∏ i, cost (f i)) = ∏ j, cost (g j) := by
  obtain ⟨e, he⟩ := exists_population_preserving_equiv f g counts
  calc
    (∏ i, cost (f i)) = ∏ i, cost (g (e i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [he i]
    _ = ∏ j, cost (g j) := e.prod_comp (fun j => cost (g j))

theorem exists_common_bank_multiple {Node : Type*} [Finite Node]
    (denominator blockSize : Node → ℕ)
    (denominator_pos : ∀ node, 0 < denominator node)
    (blockSize_pos : ∀ node, 0 < blockSize node) :
    ∃ bank : ℕ, 0 < bank ∧
      ∀ node, denominator node * blockSize node ∣ bank := by
  classical
  let : Fintype Node := Fintype.ofFinite Node
  refine ⟨∏ node, denominator node * blockSize node, ?_, ?_⟩
  · exact Finset.prod_pos fun node _ =>
      Nat.mul_pos (denominator_pos node) (blockSize_pos node)
  · intro node
    exact Finset.dvd_prod_of_mem (fun node => denominator node * blockSize node)
      (Finset.mem_univ node)

theorem exists_exact_rational_tiling {Node : Type*} [Finite Node]
    (weight : Node → ℚ) (nonnegative : ∀ node, 0 ≤ weight node)
    (blockSize : Node → ℕ) (blockSize_pos : ∀ node, 0 < blockSize node) :
    ∃ bank : ℕ, 0 < bank ∧ ∀ node, ∃ copies : ℕ,
      (bank : ℚ) * weight node = (copies * blockSize node : ℕ) := by
  classical
  let : Fintype Node := Fintype.ofFinite Node
  obtain ⟨bank, bank_pos, divisible⟩ := exists_common_bank_multiple
    (fun node => (weight node).den) blockSize
    (fun node => (weight node).den_pos) blockSize_pos
  refine ⟨bank, bank_pos, ?_⟩
  intro node
  obtain ⟨multiple, hmultiple⟩ := divisible node
  refine ⟨multiple * (weight node).num.toNat, ?_⟩
  have hnum : ((weight node).num.toNat : ℚ) = ((weight node).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (nonnegative node))
  have hden : ((weight node).den : ℚ) ≠ 0 := by
    exact_mod_cast (weight node).den_ne_zero
  calc
    (bank : ℚ) * weight node =
        (bank : ℚ) * (((weight node).num : ℚ) / ((weight node).den : ℚ)) := by
      rw [(weight node).num_div_den]
    _ = ((multiple * (weight node).num.toNat) * blockSize node : ℕ) := by
      rw [hmultiple]
      push_cast
      rw [hnum]
      field_simp [hden]

theorem target_relation_of_windows (a b c : ℤ) (x y z d : ℝ)
    (hd : 0 < d) (tight : x + y + z = 0)
    (hx : |x - (a : ℝ) * d| ≤ d / 10)
    (hy : |y - (b : ℝ) * d| ≤ d / 10)
    (hz : |z + 2 * (c : ℝ) * d| ≤ d / 10) :
    a + b = c + c := by
  obtain ⟨hx₀, hx₁⟩ := abs_le.mp hx
  obtain ⟨hy₀, hy₁⟩ := abs_le.mp hy
  obtain ⟨hz₀, hz₁⟩ := abs_le.mp hz
  let k : ℤ := a + b - 2 * c
  have hkcast : (k : ℝ) = (a : ℝ) + (b : ℝ) - 2 * (c : ℝ) := by
    simp [k]
  have hlow : -(1 : ℝ) < (k : ℝ) := by
    by_contra hn
    have hn' : (k : ℝ) ≤ -1 := le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_right hn' (le_of_lt hd)
    rw [hkcast] at hm
    nlinarith
  have hhigh : (k : ℝ) < 1 := by
    by_contra hn
    have hn' : 1 ≤ (k : ℝ) := le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_right hn' (le_of_lt hd)
    rw [hkcast] at hm
    nlinarith
  have hsmall : |(k : ℝ)| < 1 := abs_lt.mpr ⟨hlow, hhigh⟩
  have hsmallInt : |k| < 1 := by exact_mod_cast hsmall
  have hk : k = 0 := Int.abs_lt_one_iff.mp hsmallInt
  dsimp [k] at hk
  linarith

theorem synchronized_targets_of_windows (targets : Set ℤ)
    (free : ThreeAPFree targets) (a b c : ℤ)
    (ha : a ∈ targets) (hb : b ∈ targets) (hc : c ∈ targets)
    (x y z d : ℝ) (hd : 0 < d) (tight : x + y + z = 0)
    (hx : |x - (a : ℝ) * d| ≤ d / 10)
    (hy : |y - (b : ℝ) * d| ≤ d / 10)
    (hz : |z + 2 * (c : ℝ) * d| ≤ d / 10) :
    a = b ∧ a = c := by
  have hrelation := target_relation_of_windows a b c x y z d hd tight hx hy hz
  have hac : a = c := free ha hc hb hrelation
  exact ⟨by linarith, hac⟩

end FiniteControl
end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields
