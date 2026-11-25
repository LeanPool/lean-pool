/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Lookup.Counter
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Diagram.Permute

/-! # Little-endian binary addresses -/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent.Control

theorem value_lt (h : ℕ) (x : Val (word h)) : Lookup.value h x < 2 ^ h := by
  induction h with
  | zero => simp [Lookup.value]
  | succ h ih =>
    obtain ⟨b, y⟩ := x
    have := ih y
    cases b <;> simp [Lookup.value, pow_succ] <;> omega

theorem value_injective (h : ℕ) : Function.Injective (Lookup.value h) := by
  induction h with
  | zero => exact fun _ _ _ => rfl
  | succ h ih =>
    rintro ⟨i, x⟩ ⟨j, y⟩ he
    change i.toNat + 2 * Lookup.value h x = j.toNat + 2 * Lookup.value h y at he
    cases i <;> cases j <;> simp only [Bool.toNat_false, Bool.toNat_true, zero_add] at he
    · have hxy : Lookup.value h x = Lookup.value h y := by omega
      exact Prod.ext rfl (ih hxy)
    · omega
    · omega
    · have hxy : Lookup.value h x = Lookup.value h y := by omega
      exact Prod.ext rfl (ih hxy)

/-- Reindexes `Val (word w)` and `Fin (2 ^ w) where toFun k` by an equivalence. -/
def index (w : ℕ) : Val (word w) ≃ Fin (2 ^ w) where
  toFun k := ⟨Lookup.value w k, value_lt w k⟩
  invFun k := Lookup.bits w k
  left_inv k := value_injective w (Lookup.value_bits (value_lt w k))
  right_inv k := Fin.ext (Lookup.value_bits k.isLt)

/-- Reindexes `(slots (word w) → Bool)` and `Fin (2 ^ w)` by an equivalence. -/
def decode (w : ℕ) : (slots (word w) → Bool) ≃ Fin (2 ^ w) :=
  (bits (word w)).symm.trans (index w)

/-- The indexed operation `x (.inl (decode w (fun j => x (.inr (i, j)))))`. -/
def read (w : ℕ) (x : Fin (2 ^ w) ⊕ (Fin (2 ^ w) × slots (word w)) → Bool) (i : Fin (2 ^ w)) : Bool
    :=
  x (.inl (decode w (fun j => x (.inr (i, j)))))

end MatrixMultiplicationAllFields.MatrixExponent.Control
