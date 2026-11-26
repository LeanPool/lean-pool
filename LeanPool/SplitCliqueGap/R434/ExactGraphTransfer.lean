/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.ExactOrder

/-! The GraphBase bridge and leaf padding at an arbitrary order. -/

@[expose] public section

open Finset

namespace GapExtremal.R434

theorem exact_graph_of_host_scores
    {V H : Type} [Fintype V] [DecidableEq V] [Fintype H]
    {B : SimpleGraph V} [DecidableRel B.Adj] {N : H → Finset V}
    {φ : V → V → H} (hH : HostHyp B N φ) (v₀ : V)
    (n : ℕ) (hn : Fintype.card (V ⊕ H) ≤ n)
    (I : ℤ) (hI : ∀ P : Finset (Finset V), IsPack P → ∑ Q ∈ P, w B Q ≤ I)
    {y : Finset V → ℝ} (hy : ResPack y) :
    ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (G' : SimpleGraph V'),
      Fintype.card V' = n ∧ IsSplit G' ∧ G'.Connected ∧
      (∑ Q, y Q * (w B Q : ℝ)) - (I : ℝ) ≤ gap G' := by
  classical
  let k := n - Fintype.card (V ⊕ H)
  let N' := padN N v₀ k
  refine ⟨V ⊕ (H ⊕ Fin k), inferInstance, inferInstance, hostGraph N',
    ?_, isSplit_hostGraph N', connected_hostGraph N' v₀ (padN_nonempty N v₀ k), ?_⟩
  · rw [card_pad]
    exact Nat.add_sub_of_le hn
  · exact gap_ge (hH.pad v₀ k) I hI hy

end GapExtremal.R434
