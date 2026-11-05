/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.Projection


/-! A complete unsigned-label update for one binary round, including the
zero-difference branch and a deterministic pivot choice. -/

@[expose] public section

noncomputable section


namespace LeanPool.SingleCopyStabilizer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unsigned X or Z labels of a binary qubit register. -/
abbrev BinaryVec (ι : Type*) := Vec (ZMod 2) ι
/-- Binary linear spaces of paired Pauli labels. -/
abbrev BinarySpace (ι : Type*) := Submodule (ZMod 2) (Label (ZMod 2) ι)

theorem bit_eq_one_of_ne_zero (a : ZMod 2) (ha : a ≠ 0) : a = 1 := by
  -- There are only two residues modulo two.
  revert a
  decide

omit [DecidableEq ι] [Fintype ι] in
theorem exists_binary_pivot (u : BinaryVec ι) (hu : u ≠ 0) : ∃ i, u i = 1 := by
  classical
  have h : ∃ i, u i ≠ 0 := by
    by_contra! h
    exact hu (funext h)
  obtain ⟨i, hi⟩ := h
  exact ⟨i, bit_eq_one_of_ne_zero (u i) hi⟩
/-- Select a coordinate equal to one in a nonzero binary vector. -/
def binaryPivot (u : BinaryVec ι) (hu : u ≠ 0) : ι :=
  Classical.choose (exists_binary_pivot u hu)

omit [Fintype ι] [DecidableEq ι] in
theorem binaryPivot_spec (u : BinaryVec ι) (hu : u ≠ 0) : u (binaryPivot u hu) = 1 :=
  Classical.choose_spec (exists_binary_pivot u hu)

/-- The observed shear and local correction acting on a binary label space. -/
def binaryRound (L : BinarySpace ι) (u : BinaryVec ι) (b : ZMod 2) : BinarySpace ι := by
  classical
  exact if hu : u = 0 then L else updatedSpace L (binaryPivot u hu) u b

@[simp] theorem binaryRound_zero (L : BinarySpace ι) (b : ZMod 2) :
    binaryRound L 0 b = L := by
  classical
  exact dite_eq_left rfl

theorem binaryRound_of_ne (L : BinarySpace ι) (u : BinaryVec ι) (b : ZMod 2)
    (hu : u ≠ 0) : binaryRound L u b = updatedSpace L (binaryPivot u hu) u b := by
  classical
  exact dite_eq_right hu

theorem binaryRound_isotropic (L : BinarySpace ι) (hL : IsIsotropic L)
    (u : BinaryVec ι) (b : ZMod 2) : IsIsotropic (binaryRound L u b) := by
  by_cases hu : u = 0
  · subst u
    simpa using hL
  · rw [binaryRound_of_ne L u b hu]
    exact updatedSpace_isotropic L hL _ u b (binaryPivot_spec u hu)

theorem binaryRound_finrank (L : BinarySpace ι) (u : BinaryVec ι) (b : ZMod 2) :
    Module.finrank (ZMod 2) (binaryRound L u b) = Module.finrank (ZMod 2) L := by
  by_cases hu : u = 0
  · subst u
    rw [binaryRound_zero]
  · rw [binaryRound_of_ne L u b hu]
    exact updatedSpace_finrank L _ u b (binaryPivot_spec u hu)

/-- All computationally allowed differences preserve the diagonal dimension,
including those which are not stabilizer X labels in the low-nullity setting. -/
theorem binaryRound_diagonal_mono (L : BinarySpace ι) (u : BinaryVec ι) (b : ZMod 2)
    (hu : u ∈ dotOrthogonal (diagonalSpace L)) :
    Module.finrank (ZMod 2) (diagonalSpace L) ≤
      Module.finrank (ZMod 2) (diagonalSpace (binaryRound L u b)) := by
  by_cases hzero : u = 0
  · subst u
    rw [binaryRound_zero]
  · rw [binaryRound_of_ne L u b hzero]
    exact diagonal_finrank_monotone L u _ b (binaryPivot_spec u hzero)
      ((mem_dotOrthogonal _ _).mp hu)

/-- Every nonzero stabilizer X label has at least one successful correction. -/
theorem binaryRound_exists_progress (L : BinarySpace ι) (hL : IsIsotropic L)
    (u : BinaryVec ι) (hu : u ∈ xProjection L) (hzero : u ≠ 0) :
    ∃ b : ZMod 2, Module.finrank (ZMod 2) (diagonalSpace L) <
      Module.finrank (ZMod 2) (diagonalSpace (binaryRound L u b)) := by
  obtain ⟨v, hv⟩ := (mem_xProjection L u).mp hu
  obtain ⟨b, hb⟩ := exists_diagonal_finrank_progress L hL u v (binaryPivot u hzero)
      (binaryPivot_spec u hzero) hv
  refine ⟨b, ?_⟩
  rw [binaryRound_of_ne L u b hzero]
  exact hb

/-- Totalize sampling from the X projection by leaving the label space
unchanged on labels outside that projection. This is used for exact learning;
those labels can have positive probability for states of positive nullity. -/
def safeBinaryRound (L : BinarySpace ι) (u : BinaryVec ι) (b : ZMod 2) : BinarySpace ι := by
  classical
  exact if u ∈ xProjection L then binaryRound L u b else L

theorem safeBinaryRound_of_mem (L : BinarySpace ι) (u : BinaryVec ι) (b : ZMod 2)
    (hu : u ∈ xProjection L) : safeBinaryRound L u b = binaryRound L u b := by
  classical
  exact ite_eq_left hu

theorem safeBinaryRound_of_not_mem (L : BinarySpace ι) (u : BinaryVec ι) (b : ZMod 2)
    (hu : u ∉ xProjection L) : safeBinaryRound L u b = L := by
  classical
  exact ite_eq_right hu

theorem safeBinaryRound_isotropic (L : BinarySpace ι) (hL : IsIsotropic L)
    (u : BinaryVec ι) (b : ZMod 2) : IsIsotropic (safeBinaryRound L u b) := by
  classical
  by_cases hu : u ∈ xProjection L
  · rw [safeBinaryRound_of_mem L u b hu]
    exact binaryRound_isotropic L hL u b
  · rw [safeBinaryRound_of_not_mem L u b hu]
    exact hL

theorem safeBinaryRound_finrank (L : BinarySpace ι) (u : BinaryVec ι) (b : ZMod 2) :
    Module.finrank (ZMod 2) (safeBinaryRound L u b) = Module.finrank (ZMod 2) L := by
  classical
  by_cases hu : u ∈ xProjection L
  · rw [safeBinaryRound_of_mem L u b hu]
    exact binaryRound_finrank L u b
  · rw [safeBinaryRound_of_not_mem L u b hu]

theorem safeBinaryRound_diagonal_mono (L : BinarySpace ι) (hL : IsIsotropic L)
    (u : BinaryVec ι) (b : ZMod 2) :
    Module.finrank (ZMod 2) (diagonalSpace L) ≤
      Module.finrank (ZMod 2) (diagonalSpace (safeBinaryRound L u b)) := by
  classical
  by_cases hu : u ∈ xProjection L
  · rw [safeBinaryRound_of_mem L u b hu]
    exact binaryRound_diagonal_mono L u b (xProjection_le_orthogonal L hL hu)
  · rw [safeBinaryRound_of_not_mem L u b hu]

end LeanPool.SingleCopyStabilizer
