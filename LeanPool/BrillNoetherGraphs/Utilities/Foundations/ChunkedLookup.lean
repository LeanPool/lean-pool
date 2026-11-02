/-
Copyright (c) 2026 Nathan Pflueger and OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger, OpenAI
-/
module

public import Mathlib.Data.List.GetD

/-! # Size-tagged lookup for certificate tables -/

@[expose] public section

namespace List

/-- Look up a global index by skipping size-tagged blocks of an existing list table. -/
def lookupChunks {α : Type*} (chunks : List (ℕ × List α)) (index : ℕ) (fallback : α) : α :=
  match chunks with
  | [] => fallback
  | (size, values) :: rest =>
      if index < size then values.getD index fallback
      else lookupChunks rest (index - size) fallback

/-- Correct size tags make block lookup agree with lookup in the concatenated table. -/
theorem lookupChunks_eq_getD_flatMap {α : Type*} (chunks : List (ℕ × List α))
    (hSizes : ∀ chunk ∈ chunks, chunk.1 = chunk.2.length) (index : ℕ) (fallback : α) :
    lookupChunks chunks index fallback = (chunks.flatMap Prod.snd).getD index fallback := by
  induction chunks generalizing index with
  | nil => rfl
  | cons chunk chunks ih =>
      rcases chunk with ⟨size, values⟩
      have hSize : size = values.length := hSizes (size, values) (List.mem_cons.mpr (Or.inl rfl))
      have hRest : ∀ chunk ∈ chunks, chunk.1 = chunk.2.length := by
        intro chunk hMem
        exact hSizes chunk (List.mem_cons_of_mem _ hMem)
      simp only [lookupChunks, List.flatMap_cons]
      split <;> rename_i hIndex
      · rw [List.getD_append values _ fallback index (by simpa only [← hSize] using hIndex)]
      · rw [ih hRest, List.getD_append_right values _ fallback index
          (by simpa only [← hSize] using Nat.le_of_not_gt hIndex), ← hSize]
end List
