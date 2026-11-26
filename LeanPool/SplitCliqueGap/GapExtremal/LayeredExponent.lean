/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.WeightCap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Beyond 5/3 (ledger §16)

* `exponent_of_family`: a family of split graphs with `|V_j| ≤ K M^j` and `gap ≥ a^j M^j / 3` gives
  `gap ≥ c n^{1 + log a / log M}` for every `n ≥ K M` (graphs with at most `n` vertices).
* `tp_layered`: for every cap `A` (no separability) in a finite `F₅`-module `U`, the two-layer
construction over
  `A^j` gives exponent `1 + log |A| / log |U|`.
-/

@[expose] public section

namespace GapExtremal

open Finset

/-- **From a family to all orders.** -/
theorem exponent_of_family {M a K : ℕ} (hM : 2 ≤ M) (ha : 1 ≤ a) (hK : 0 < K)
    (V : ℕ → Type) [∀ j, Fintype (V j)] [∀ j, DecidableEq (V j)] (G : ∀ j, SimpleGraph (V j))
    (hcard : ∀ j, Fintype.card (V j) ≤ K * M ^ j) (hsplit : ∀ j, IsSplit (G j))
    (hgap : ∀ j, (a : ℝ) ^ j * (M : ℝ) ^ j / 3 ≤ gap (G j)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, K * M ≤ n →
      ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (G' : SimpleGraph V'),
        Fintype.card V' ≤ n ∧ IsSplit G' ∧
        c * (n : ℝ) ^ (1 + Real.log a / Real.log M) ≤ gap G' := by
  set α := 1 + Real.log a / Real.log M
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hα : 0 ≤ α := by
    have h1 : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast ha)
    have h2 : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
    positivity
  refine ⟨((K : ℝ) * M) ^ (-α) / 3, by positivity, fun n hn => ?_⟩
  set j := Nat.log M (n / K) with hj
  have hMj : M ^ j ≤ n / K := Nat.pow_log_le_self M (by
    have : 1 ≤ n / K := (Nat.le_div_iff_mul_le hK).mpr (by
      have := Nat.mul_le_mul_left K (show 1 ≤ M by omega); nlinarith)
    omega)
  have hlt : n / K < M ^ (j + 1) := Nat.lt_pow_succ_log_self (by omega) _
  refine ⟨V j, inferInstance, inferInstance, G j, ?_, hsplit j, ?_⟩
  · calc Fintype.card (V j) ≤ K * M ^ j := hcard j
      _ ≤ K * (n / K) := Nat.mul_le_mul_left K hMj
      _ ≤ n := Nat.mul_div_le n K
  · have hn' : (n : ℝ) / (K * M) ≤ (M : ℝ) ^ j := by
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
    have hsplit' : ((n : ℝ) / (K * M)) ^ α = ((K : ℝ) * M) ^ (-α) * (n : ℝ) ^ α := by
      rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity)]
      ring
    refine le_trans ?_ (hgap j)
    calc ((K : ℝ) * M) ^ (-α) / 3 * (n : ℝ) ^ α = ((n : ℝ) / (K * M)) ^ α / 3 := by
          rw [hsplit']; ring
      _ ≤ ((M : ℝ) ^ j) ^ α / 3 := by linarith
      _ = (a : ℝ) ^ j * (M : ℝ) ^ j / 3 := by rw [hpow]

variable {U : Type} [AddCommGroup U] [Module F5 U] [Fintype U] [DecidableEq U]

/-- The layered graph of `A^j`. -/
abbrev LV (U : Type) (j : ℕ) :=
  ((F5 × (Fin j → U)) ⊕ (Fin j → U)) ⊕ PHostIdx F5 (Fin j → U) (Option F5) U

omit [DecidableEq U] in
/-- **Theorem 16.0, conditional form.** Any cap `A` in a finite `F₅`-module gives exponent
`1 + log |A| / log |U|` (no separability). -/
theorem tp_layered {A : Finset U} (hA : IsCap F5 (A : Set U)) (hA0 : A.Nonempty) {e : U} (he : e ≠
  0)
    (hM : 2 ≤ Fintype.card U) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 636 * Fintype.card U * Fintype.card U ≤ n →
      ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (G' : SimpleGraph V'),
        Fintype.card V' ≤ n ∧ IsSplit G' ∧
        c * (n : ℝ) ^ (1 + Real.log A.card / Real.log (Fintype.card U)) ≤ gap G' := by
  classical
  set M := Fintype.card U
  have hcapne : ∀ j, (capPow A j).Nonempty := fun j => by
    obtain ⟨a0, ha0⟩ := hA0
    exact ⟨fun _ => a0, by simp [capPow, ha0]⟩
  refine exponent_of_family hM hA0.card_pos (by positivity) (LV U)
    (fun j => hostGraph (ppalette (layered (W := Fin j → U)) (capPow A j) (prodSep A he j)))
    (fun j => ?_) (fun j => isSplit_hostGraph _) (fun j => ?_)
  · simp only [LV, PHostIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_pi,
    Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Sym2.card, Fintype.card_option, ZMod.card]
    have hM1 : 1 ≤ Fintype.card U := by omega
    have h72 : Nat.choose 7 2 = 21 := by decide
    rw [h72]
    have hp : Fintype.card U ^ j ≤ Fintype.card U * Fintype.card U ^ j :=
      Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  · have h := pgap_ge_third (layered (W := Fin j → U)) (isCap_capPow hA j) (hcapne j)
      (prodSep A he j) layered_same
    rw [card_capPow] at h
    have hW : Fintype.card (Fin j → U) = M ^ j := by simp [M]
    rw [hW] at h
    push_cast at h
    exact h

end GapExtremal
