/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Replacing the first entries of a finite tuple
-/

@[expose] public section

namespace SGPT.Foundations.FiniteTuple

variable {α : Type*} {n : ℕ}

/-- Replace the first `length` entries of `original` by the entries of `replacement`. -/
def replacePrefix (original replacement : Fin n → α) (length : ℕ) : Fin n → α :=
  fun i ↦ if (i : ℕ) < length then replacement i else original i

theorem replacePrefix_zero (original replacement : Fin n → α) :
    replacePrefix original replacement 0 = original := by
  funext i
  simp [replacePrefix]

theorem replacePrefix_full (original replacement : Fin n → α) :
    replacePrefix original replacement n = replacement := by
  funext i
  simp [replacePrefix, i.isLt]

theorem replacePrefix_succ (original replacement : Fin n → α) {length : ℕ} (h : length < n) :
    replacePrefix original replacement (length + 1) =
      Function.update (replacePrefix original replacement length) ⟨length, h⟩
        (replacement ⟨length, h⟩) := by
  funext i
  by_cases hi : i = ⟨length, h⟩
  · subst hi
    simp [replacePrefix]
  · have hne : (i : ℕ) ≠ length := fun h' ↦ hi (Fin.ext h')
    simp [replacePrefix, Function.update_of_ne hi, Nat.lt_succ_iff_lt_or_eq, hne]

end SGPT.Foundations.FiniteTuple
