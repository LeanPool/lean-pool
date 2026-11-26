/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.PHosts
public import LeanPool.SplitCliqueGap.GapExtremal.Main
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# The gap of a positioned construction (ledger Cor. 16.4)

`gap (hostGraph (ppalette D C S)) ≥ |C| · |W| / 3` for every cap `C` with a separating family `S`,
on any
positioned core satisfying the twin condition `hsame`.
-/

@[expose] public section

namespace GapExtremal

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [AddCommGroup W] [Module F W] [Fintype W] [DecidableEq W]
variable {V P : Type*} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
variable {U : Type*} [AddCommGroup U] [Module F U] [Fintype U] [DecidableEq U]

omit [Fintype P] in
/-- Transfer a positioned packing score through any suitable host certificate. -/
theorem positioned_gap_ge_third (D : PData F W V P) {C : Finset W}
    {H : Type*} [Fintype H] [DecidableEq H] {N : H → Finset V} {φ : V → V → H}
    (host : HostHyp (PB D C) N φ)
    (integral : ∀ T : Finset (Finset V), IsPack T →
      ∑ Q ∈ T, w (PB D C) Q ≤ 8 * (pblocks D C).card) :
    ((C.card * Fintype.card W : ℕ) : ℝ) / 3 ≤ gap (hostGraph N) := by
  have h := gap_ge host (8 * (pblocks D C).card) integral (presPack (D := D) (C := C))
  have hv := pvalue (D := D) (C := C)
  have hb : ((pblocks D C).card : ℝ) ≤ C.card * Fintype.card W := by
    exact_mod_cast card_pblocks_le D
  push_cast at h ⊢
  linarith

/-- **Cor. 16.4.** -/
theorem pgap_ge_third (D : PData F W V P) {C : Finset W} (hC : IsCap F (C : Set W)) (hC0 :
  C.Nonempty)
    (S : SepFam F C U)
    (hsame : ∀ v v', D.base v = D.base v' → ∀ i j, D.σ i = D.pos v → D.σ j = D.pos v' →
      ¬ H12.graph.Adj i j) :
    ((C.card * Fintype.card W : ℕ) : ℝ) / 3 ≤ gap (hostGraph (ppalette D C S)) := by
  exact positioned_gap_ge_third D (phostHyp (S := S) hC0 hsame) (fun _ => pI_le D hC)


omit [AddCommGroup U] [AddCommGroup W] [DecidableEq F] [DecidableEq P] [DecidableEq U]
    [DecidableEq V] [DecidableEq W] [Field F] [Module F U] [Module F W] in
/-- Order of a positioned construction. -/
theorem pcard_vertices :
    Fintype.card (V ⊕ PHostIdx F W P U) =
      Fintype.card V + Fintype.card (F × W) * (Fintype.card U * Fintype.card F * Fintype.card
        (Sym2 P))
        + Fintype.card (F × W) * Fintype.card (Sym2 P) := by
  simp only [PHostIdx, Fintype.card_sum, Fintype.card_prod]
  ring

end GapExtremal
