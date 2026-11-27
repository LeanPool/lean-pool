/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.SparseCandidate
public import LeanPool.KLRandomness.SparseSearchMask
public import LeanPool.KLRandomness.AffineCodeCoverage
public import LeanPool.KLRandomness.SparseCodeCount

/-!
# Concrete matrix codes for the probabilistic candidates

The matrix on a candidate's support is padded by zero columns to the whole
pool. Padding preserves full row rank and every unread-column rank test.
This supplies the algebraic bridge from the classical finite experiment to
the executable code representation used by exhaustive search.
-/

@[expose] public section

namespace Klr.SparseCandidateCode

open SparseCandidate RandomMatrix AffineCode FiniteMeasure

variable {M m r : ℕ}

/-- The candidate's columns, extended by zero to the whole pool. -/
noncomputable def paddedColumns (c : Candidate M m r) (a : Fin M) : Fin r → ZMod 2 :=
  if ha : a ∈ c.1.val then c.2.val ((supportEquiv c.1).symm ⟨a, ha⟩) else 0

@[simp] theorem paddedColumns_position (c : Candidate M m r) (j : Fin m) :
    paddedColumns c (position c.1 j) = c.2.val j := by
  simp only [paddedColumns, dite_eq_left (position_mem c.1 j)]
  change c.2.val ((supportEquiv c.1).symm (supportEquiv c.1 j)) = _
  rw [Equiv.symm_apply_apply]

/-- Restricting padded columns to unread pool positions is exactly restricting
the original matrix to the corresponding support columns. -/
theorem padded_restricted_surjective_iff (c : Candidate M m r) (D : Finset (Fin M)) :
    Function.Surjective (restrictedMap (paddedColumns c) D (K := ZMod 2)) ↔
      Function.Surjective
        (restrictedMap c.2.val (unreadColumns D c.1) (K := ZMod 2)) := by
  classical
  rw [← not_iff_not, restricted_not_surjective_iff, restricted_not_surjective_iff]
  constructor
  · rintro ⟨φ, hφ, hD⟩
    refine ⟨φ, hφ, funext fun j => ?_⟩
    have hj : position c.1 j.val ∈ D := (mem_unreadColumns D c.1 j.val).mp j.property
    have he := congrFun hD ⟨position c.1 j.val, hj⟩
    simpa only [evaluationMap_apply, paddedColumns_position, Pi.zero_apply] using he
  · rintro ⟨φ, hφ, hT⟩
    refine ⟨φ, hφ, funext fun a => ?_⟩
    change φ (paddedColumns c a.val) = 0
    by_cases hS : a.val ∈ c.1.val
    · let j := (supportEquiv c.1).symm ⟨a.val, hS⟩
      have hjpos : position c.1 j = a.val := by
        exact congrArg Subtype.val ((supportEquiv c.1).apply_symm_apply ⟨a.val, hS⟩)
      have hj : j ∈ unreadColumns D c.1 := by
        rw [mem_unreadColumns, hjpos]
        exact a.property
      have he := congrFun hT ⟨j, hj⟩
      simpa only [paddedColumns, dite_eq_left hS, evaluationMap_apply, Pi.zero_apply] using he
    · simp [paddedColumns, hS]

theorem padded_surjective (c : Candidate M m r) :
    Function.Surjective (columnMap (paddedColumns c) (K := ZMod 2)) := by
  have he : unreadColumns Finset.univ c.1 = Finset.univ := by ext j; simp
  have h := padded_restricted_surjective_iff c Finset.univ
  rw [he, restricted_univ_surjective_iff, restricted_univ_surjective_iff] at h
  exact h.mpr c.2.property

/-- Encode the padded candidate matrix. Sparse-list checking uses the direct
rank test, so no right-inverse certificate or syndrome is needed at this point. -/
noncomputable def code (c : Candidate M m r) : Data :=
  AffineCode.encode (fun i a => paddedColumns c a i) 0 0

@[simp] theorem width_code (c : Candidate M m r) : width (code c) = M := rfl
@[simp] theorem rank_code (c : Candidate M m r) : rank (code c) = r := rfl

@[simp] theorem matrix_code (c : Candidate M m r) :
    matrix (code c) = fun i a => paddedColumns c a i := matrix_encode _ _ _

theorem surjective_code (c : Candidate M m r) :
    Function.Surjective (matrix (code c)).mulVecLin := by
  rw [matrix_code]
  change Function.Surjective
    (Matrix.mulVecLin (Matrix.of (fun (i : Fin r) (a : Fin M) => paddedColumns c a i)))
  rw [SparseSearch.mulVecLin_eq_columnMap]
  exact padded_surjective c

@[simp] theorem fullRank_code (c : Candidate M m r) : SparseSearch.fullRank (code c) = true :=
  (SparseSearch.fullRank_eq_true _).mpr (surjective_code c)

/-- Every coefficient outside the support is literally the Boolean value false. -/
theorem entry_code_eq_false (c : Candidate M m r) (i j : ℕ)
    (hi : i < r) (hj : j < M) (hS : (⟨j, hj⟩ : Fin M) ∉ c.1.val) :
    entry (rows (code c)) i j = false := by
  have hp : paddedColumns c (⟨j, hj⟩ : Fin M) = 0 := by
    simp [paddedColumns, hS]
  change ((List.ofFn (fun i : Fin r => List.ofFn
    (fun j : Fin M => boolEquivF2.symm (paddedColumns c j i)))).getD i []).getD j false = false
  rw [AffineCode.getD_ofFn _ ⟨i, hi⟩, AffineCode.getD_ofFn _ ⟨j, hj⟩, hp]
  rfl

/-- The executable mask checker on the padded code is exactly the candidate
rank-preservation predicate on the corresponding unread pool positions. -/
theorem maskedFullRank_code (c : Candidate M m r) (d : List Bool) :
    SparseSearch.maskedFullRank (code c) d = true ↔
      ¬ BadRank (SparseListCode.maskSet M d) c := by
  classical
  rw [SparseSearch.maskedFullRank_eq_true]
  change Function.Surjective
    (restrictedMap (fun (a : Fin M) (i : Fin r) => matrix (code c) i a)
      (SparseListCode.maskSet M d) (K := ZMod 2)) ↔ _
  have hcols : (fun (a : Fin M) (i : Fin r) => matrix (code c) i a) =
      paddedColumns c := by
    funext a i
    exact congrFun (congrFun (matrix_code c) i) a
  rw [hcols]
  simpa only [BadRank, not_not] using
    padded_restricted_surjective_iff c (SparseListCode.maskSet M d)

theorem maskedFullRank_code_false (c : Candidate M m r) (d : List Bool) :
    (!SparseSearch.maskedFullRank (code c) d) = true ↔
      BadRank (SparseListCode.maskSet M d) c := by
  classical
  have h := maskedFullRank_code c d
  cases he : SparseSearch.maskedFullRank (code c) d <;> simp_all

end Klr.SparseCandidateCode
