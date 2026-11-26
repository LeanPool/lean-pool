/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.LayeredExponent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# One-layer cores: any cap, any field with at least six elements (ledger §16.1)

`single σ` is the positioned core `V = F × W` with positions = colours. Together with `prodSep` it
gives, for
every cap `A` in a finite `F`-module `U` (no separability), the exponent `1 + log |A| / log |U|`
for the one-layer cap construction.
-/

@[expose] public section

namespace GapExtremal

open Finset

variable {F : Type}

/-- The one-layer positioned core. -/
def single {W : Type} (σ : Fin 6 ↪ F) : PData F W (F × W) F where
  base := id
  pos := Prod.fst
  col := id
  σ := σ
  base_fst := fun _ => rfl
  inj := fun _ _ h _ => h
  fib := fun _ _ _ h _ => Or.inl h
  rl := fun y _ => y
  rl_base := fun _ _ _ => rfl
  rl_pos := fun _ _ h => h
  colσ := fun _ _ h => Or.inl (σ.injective h)

theorem single_same {W : Type} (σ : Fin 6 ↪ F) :
    ∀ v v' : F × W, (single (W := W) σ).base v = (single (W := W) σ).base v' →
      ∀ i j, σ i = (single (W := W) σ).pos v → σ j = (single (W := W) σ).pos v' →
        ¬ H12.graph.Adj i j := by
  intro v v' hb i j hi hj hij
  simp only [single, id] at hb hi hj
  subst hb
  exact hij.ne (σ.injective (hi.trans hj.symm))

variable [Field F] [Fintype F] [DecidableEq F]
variable {U : Type} [AddCommGroup U] [Module F U] [Fintype U] [DecidableEq U]

/-- The one-layer graph of `A^j`. -/
abbrev SV (F U : Type) (j : ℕ) :=
  (F × (Fin j → U)) ⊕ PHostIdx F (Fin j → U) F U

omit [DecidableEq F] [Field F] [AddCommGroup U] [Module F U] [DecidableEq U] in
/-- Bound the order of the one-layer construction by its field and module sizes. -/
theorem card_SV_le [Nonempty U] (j : ℕ) :
    Fintype.card (SV F U j) ≤ 3 * (Fintype.card F + 1) ^ 4 * Fintype.card U * Fintype.card U ^ j
      := by
  set M := Fintype.card U
  set q := Fintype.card F
  have hc := pcard_vertices (F := F) (W := Fin j → U) (V := F × (Fin j → U)) (P := F) (U := U)
  rw [hc]
  simp only [Fintype.card_prod, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Sym2.card]
  set X := M ^ j
  set C2 := (q + 1).choose 2 with hC2
  have hsym : C2 ≤ (q + 1) ^ 2 := by
    rw [hC2, Nat.choose_two_right, sq]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hq4 : (q + 1) ^ 2 ≤ (q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have f1 : q ≤ (q + 1) ^ 4 := le_trans (by nlinarith) hq4
  have f2 : q * q * C2 ≤ (q + 1) ^ 4 := by
    calc q * q * C2 ≤ q * q * (q + 1) ^ 2 := Nat.mul_le_mul_left _ hsym
      _ ≤ (q + 1) ^ 2 * (q + 1) ^ 2 := Nat.mul_le_mul_right _ (by nlinarith)
      _ = (q + 1) ^ 4 := by ring
  have f3 : q * C2 ≤ (q + 1) ^ 4 := by
    calc q * C2 ≤ (q + 1) * (q + 1) ^ 2 := Nat.mul_le_mul (by omega) hsym
      _ ≤ (q + 1) ^ 4 := by
        calc (q + 1) * (q + 1) ^ 2 = (q + 1) ^ 3 := by ring
          _ ≤ (q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hM1 : 1 ≤ M := Fintype.card_pos
  have hX : X ≤ M * X := Nat.le_mul_of_pos_left _ (by omega)
  have e1 : q * X ≤ (q + 1) ^ 4 * (M * X) := Nat.mul_le_mul f1 hX
  have e2 : q * X * (M * q * C2) = (q * q * C2) * (M * X) := by ring
  have e3 : q * X * C2 = (q * C2) * X := by ring
  have e4 : (q * C2) * X ≤ (q + 1) ^ 4 * (M * X) := Nat.mul_le_mul f3 hX
  have e5 : (q * q * C2) * (M * X) ≤ (q + 1) ^ 4 * (M * X) := Nat.mul_le_mul_right _ f2
  calc q * X + q * X * (M * q * C2) + q * X * C2
      ≤ (q + 1) ^ 4 * (M * X) + (q + 1) ^ 4 * (M * X) + (q + 1) ^ 4 * (M * X) := by
        rw [e2, e3]; exact Nat.add_le_add (Nat.add_le_add e1 e5) e4
    _ = 3 * (q + 1) ^ 4 * M * X := by ring

end GapExtremal
