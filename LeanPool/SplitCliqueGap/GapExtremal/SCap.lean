/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Single
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# The split-graph gap under a cap supported on active colours

The positioned construction uses only relations among its active colours.
The resulting exponent bound applies to every cap for that colour set.

-/

@[expose] public section

namespace GapExtremal

open Finset



variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [AddCommGroup W] [Module F W] [Fintype W] [DecidableEq W]

section PChain

/-! ### The positioned chain under an S-cap -/

variable {V P : Type*} [Fintype V] [DecidableEq V] [DecidableEq P]
variable (D : PData F W V P) {C : Finset W}

theorem pgap_ge_third_s [Fintype P] {U : Type*} [AddCommGroup U] [Module F U] [Fintype U]
  [DecidableEq U]
    (hC : IsSCap (actCol D) (C : Set W)) (hC0 : C.Nonempty) (S : SepFam F C U)
    (hsame : ∀ v v', D.base v = D.base v' → ∀ i j, D.σ i = D.pos v → D.σ j = D.pos v' →
      ¬ H12.graph.Adj i j) :
    ((C.card * Fintype.card W : ℕ) : ℝ) / 3 ≤ gap (hostGraph (ppalette D C S)) := by
  exact positioned_gap_ge_third D (phostHyp (S := S) hC0 hsame) (fun _ => pI_le_s D hC)

end PChain

section Single

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type} [AddCommGroup U] [Module F U] [Fintype U] [DecidableEq U]

omit [DecidableEq F] [DecidableEq U] [Fintype F] [Fintype U] in
theorem isSCap_capPow {S : Set F} {A : Finset U} (hA : IsSCap S (A : Set U)) (j : ℕ) :
    IsSCap S (capPow A j : Set (Fin j → U)) := by
  rw [coe_capPow]; exact hA.pi

omit [DecidableEq F] [Fintype F] in
theorem actCol_single {W : Type} [AddCommGroup W] [Module F W] (σ : Fin 6 ↪ F) :
    actCol (single (W := W) σ) = Set.range σ := rfl

end Single

end GapExtremal
