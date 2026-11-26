/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Layered
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
  refine ⟨((K : ℝ) * M) ^ (-(1 + Real.log a / Real.log M)) / 3, by positivity, fun n hn => ?_⟩
  obtain ⟨j, hsize, hscale⟩ := exponent_budget hM ha hK hn
  exact ⟨V j, inferInstance, inferInstance, G j, (hcard j).trans hsize, hsplit j,
    hscale.trans (hgap j)⟩

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
  · have h := pgap_ge_third (layered (W := Fin j → U)) (isCap_capPow hA j) (capPow_nonempty hA0 j)
      (prodSep A he j) layered_same
    exact capPow_gap_le h

end GapExtremal
