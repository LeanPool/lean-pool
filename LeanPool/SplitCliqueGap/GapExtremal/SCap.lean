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
  have h := gap_ge (phostHyp (S := S) hC0 hsame) (8 * (pblocks D C).card)
    (fun T hT => pI_le_s D hC hT) (presPack (D := D) (C := C))
  have hv := pvalue (D := D) (C := C)
  have hb : ((pblocks D C).card : ℝ) ≤ C.card * Fintype.card W := by
    exact_mod_cast card_pblocks_le D
  push_cast at h ⊢
  linarith


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

omit [DecidableEq F] [DecidableEq U] in
/-- **TP-cond for S-caps** (ledger §17): the exponent `1 + log |A| / log |U|` for every S-cap `A`,
`S` the
active colours `range σ`. -/
theorem tp_single_s (σ : Fin 6 ↪ F) {A : Finset U} (hA : IsSCap (Set.range σ) (A : Set U)) (hA0 :
  A.Nonempty) {e : U}
    (he : e ≠ 0) (hM : 2 ≤ Fintype.card U) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      3 * (Fintype.card F + 1) ^ 4 * Fintype.card U * Fintype.card U ≤ n →
      ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (G' : SimpleGraph V'),
        Fintype.card V' ≤ n ∧ IsSplit G' ∧
        c * (n : ℝ) ^ (1 + Real.log A.card / Real.log (Fintype.card U)) ≤ gap G' := by
  classical
  set M := Fintype.card U
  have hcapne : ∀ j, (capPow A j).Nonempty := fun j => by
    obtain ⟨a0, ha0⟩ := hA0
    exact ⟨fun _ => a0, by simp [capPow, ha0]⟩
  refine exponent_of_family hM hA0.card_pos (by positivity) (SV F U)
    (fun j => hostGraph (ppalette (single (W := Fin j → U) σ) (capPow A j) (prodSep A he j)))
    (fun j => ?_) (fun j => isSplit_hostGraph _) (fun j => ?_)
  · exact card_SV_le j
  · have h := pgap_ge_third_s (single (W := Fin j → U) σ) (isSCap_capPow hA j) (hcapne j)
      (prodSep A he j) (single_same σ)
    rw [card_capPow] at h
    have hW : Fintype.card (Fin j → U) = M ^ j := by simp [M]
    rw [hW] at h
    push_cast at h
    exact h


end Single

end GapExtremal
