/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Main
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# The exponent (ledger §10, TP-cond)

For a separable cap `A` in a finite `F`-module `U` (`|U| = M ≥ 2`, `|A| = a ≥ 1`) and `σ : Fin 6 ↪
F`, the
graphs `G(A^j)` give, for every `n ≥ 3 q³ M`, a split graph with at most `n` vertices and

  `gap ≥ c · n^α`,   `α = 1 + log a / log M`.
-/

@[expose] public section

namespace GapExtremal

open Finset

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type} [AddCommGroup U] [Module F U] [Fintype U] [DecidableEq U]

/-- The power `A^j` as a `Finset` of `Fin j → U`. -/
def capPow (A : Finset U) (j : ℕ) : Finset (Fin j → U) := Fintype.piFinset fun _ => A

omit [AddCommGroup U] [DecidableEq U] [Fintype U] in
theorem coe_capPow (A : Finset U) (j : ℕ) :
    (capPow A j : Set (Fin j → U)) = Set.pi Set.univ fun _ => (A : Set U) := by
  simp [capPow, Fintype.coe_piFinset]

omit [DecidableEq F] [DecidableEq U] [Fintype F] [Fintype U] in
theorem isCap_capPow {A : Finset U} (hA : IsCap F (A : Set U)) (j : ℕ) :
    IsCap F (capPow A j : Set (Fin j → U)) := by
  rw [coe_capPow]; exact hA.pi

omit [DecidableEq F] [DecidableEq U] [Fintype F] [Fintype U] in
theorem isSep_capPow {A : Finset U} (hA : IsSep F (A : Set U)) (j : ℕ) :
    IsSep F (capPow A j : Set (Fin j → U)) := by
  rw [coe_capPow]; exact hA.pi

omit [AddCommGroup U] [DecidableEq U] [Fintype U] in
theorem card_capPow (A : Finset U) (j : ℕ) : (capPow A j).card = A.card ^ j := by
  simp [capPow]

/-- `(M^j)^α = a^j · M^j` for `α = 1 + log a / log M`. -/
theorem pow_rpow_alpha {a M : ℕ} (ha : 1 ≤ a) (hM : 2 ≤ M) (j : ℕ) :
    ((M : ℝ) ^ j) ^ (1 + Real.log a / Real.log M) = (a : ℝ) ^ j * (M : ℝ) ^ j := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hlogM : Real.log M ≠ 0 := by
    have : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
    exact (Real.log_pos this).ne'
  have key : (M : ℝ) ^ ((j : ℝ) * Real.log a / Real.log M) = (a : ℝ) ^ j := by
    rw [Real.rpow_def_of_pos hM0, ← Real.exp_log (pow_pos ha0 j), Real.log_pow]
    congr 1
    field_simp
  rw [← Real.rpow_natCast, ← Real.rpow_mul hM0.le,
    show (j : ℝ) * (1 + Real.log a / Real.log M) = j + j * Real.log a / Real.log M by ring,
    Real.rpow_add hM0, Real.rpow_natCast, key, mul_comm]

omit [DecidableEq F] [DecidableEq U] in
/-- **TP-cond.** -/
theorem tp_cond (σ : Fin 6 ↪ F) {A : Finset U} (hA : IsCap F (A : Set U)) (hS : IsSep F (A : Set U))
    (ha : 1 ≤ A.card) (hM : 2 ≤ Fintype.card U) (hq : 2 ≤ Fintype.card F) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 3 * Fintype.card F ^ 3 * Fintype.card U ≤ n →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
        Fintype.card V ≤ n ∧ IsSplit G ∧
        c * (n : ℝ) ^ (1 + Real.log A.card / Real.log (Fintype.card U)) ≤ gap G := by
  classical
  set M := Fintype.card U
  set K := 3 * Fintype.card F ^ 3
  set α := 1 + Real.log A.card / Real.log M
  have hK : 0 < K := by positivity
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hα : 0 ≤ α := by
    have h1 : 0 ≤ Real.log A.card := Real.log_nonneg (by exact_mod_cast ha)
    have h2 : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
    positivity
  refine ⟨((K : ℝ) * M) ^ (-α) / 3, by positivity, fun n hn => ?_⟩
  set j := Nat.log M (n / K) with hj
  have hMj : M ^ j ≤ n / K := Nat.pow_log_le_self M (by
    have : 1 ≤ n / K := (Nat.le_div_iff_mul_le hK).mpr (by
      have := Nat.mul_le_mul_left K (show 1 ≤ M by omega); nlinarith)
    omega)
  have hlt : n / K < M ^ (j + 1) := Nat.lt_pow_succ_log_self (by omega) _
  -- the graph
  refine ⟨(F × (Fin j → U)) ⊕ HostIdx F (Fin j → U), inferInstance, instDecidableEqSum,
    hostGraph (palette (capPow A j) σ (isSep_capPow hS j)), ?_, isSplit_hostGraph _, ?_⟩
  · have := card_vertices_le (F := F) (W := Fin j → U) hq
    have hW : Fintype.card (Fin j → U) = M ^ j := by simp [M]
    rw [hW] at this
    calc _ ≤ K * M ^ j := this
      _ ≤ K * (n / K) := Nat.mul_le_mul_left K hMj
      _ ≤ n := Nat.mul_div_le n K
  · have hgap := gap_ge_third (W := Fin j → U) σ (isCap_capPow hA j) (isSep_capPow hS j)
    have hW : Fintype.card (Fin j → U) = M ^ j := by simp [M]
    rw [card_capPow, hW] at hgap
    -- n < K M^{j+1}, so n/(K M) < M^j
    have hn' : (n : ℝ) / (K * M) ≤ (M : ℝ) ^ j := by
      have h1 : n < K * (n / K) + K := by
        have := Nat.div_add_mod n K
        have := Nat.mod_lt n hK
        omega
      have h2 : n < K * M ^ (j + 1) := by
        calc n < K * (n / K) + K := h1
          _ = K * (n / K + 1) := by ring
          _ ≤ K * M ^ (j + 1) := Nat.mul_le_mul_left K hlt
      rw [div_le_iff₀ (by positivity)]
      have : (n : ℝ) < K * M ^ (j + 1) := by exact_mod_cast h2
      rw [pow_succ] at this
      nlinarith
    have hpow := pow_rpow_alpha ha hM j
    have hmono : ((n : ℝ) / (K * M)) ^ α ≤ ((M : ℝ) ^ j) ^ α :=
      Real.rpow_le_rpow (by positivity) hn' hα
    have hsplit : ((n : ℝ) / (K * M)) ^ α = ((K : ℝ) * M) ^ (-α) * (n : ℝ) ^ α := by
      rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity)]
      ring
    push_cast at hgap
    refine le_trans ?_ hgap
    calc ((K : ℝ) * M) ^ (-α) / 3 * (n : ℝ) ^ α = ((n : ℝ) / (K * M)) ^ α / 3 := by
          rw [hsplit]; ring
      _ ≤ ((M : ℝ) ^ j) ^ α / 3 := div_le_div_of_nonneg_right hmono (by norm_num)
      _ = (A.card : ℝ) ^ j * (M : ℝ) ^ j / 3 := by rw [hpow]

end GapExtremal
