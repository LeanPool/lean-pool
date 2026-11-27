/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.SparseCandidateCode
public import LeanPool.KLRandomness.SparseCandidateList
public import LeanPool.KLRandomness.SparseListSearch
import Mathlib.Tactic.FieldSimp

/-!
# Coding the sparse lists furnished by the probabilistic argument

Every mathematical candidate has a concrete support mask and a zero-padded
matrix code. Exact counting and rank identities transfer both simultaneous
list conditions to the finite verifier's specification. This bridge is used
only to prove that exhaustive search has a successful code to find.
-/

@[expose] public section

namespace Klr.SparseListCode

open SparseCandidate SparseCandidateCode SampleConcentration

variable {M m r J : ℕ}

/-- The concrete finite representation of a mathematical candidate. -/
noncomputable def entryOf (c : Candidate M m r) : SparseListSearch.Entry :=
  (mask c.1.val, SparseCandidateCode.code c)

/-- Encode a finite list, retaining all repetitions and its index order. -/
noncomputable def listOf (z : Fin J → Candidate M m r) : SparseListSearch.CodeList :=
  List.ofFn fun j => entryOf (z j)

@[simp] theorem length_listOf (z : Fin J → Candidate M m r) : (listOf z).length = J := by
  simp [listOf]

theorem goodEntry_entryOf (c : Candidate M m r) :
    SparseListSearch.GoodEntry M m r (entryOf c) := by
  change (mask c.1.val).length = M ∧ (mask c.1.val).countP id = m ∧
    AffineCode.width (code c) = M ∧ AffineCode.rank (code c) = r ∧
    Function.Surjective (AffineCode.matrix (code c)).mulVecLin ∧ _
  refine ⟨length_mask _, ?_, rfl, rfl, surjective_code c, ?_⟩
  · simpa only [countP_mask] using c.1.property
  · intro i hi j hj hs
    apply entry_code_eq_false c i j hi hj
    change (mask c.1.val).getD (⟨j, hj⟩ : Fin M).val false = false at hs
    rw [getD_mask] at hs
    simpa using hs

theorem count_incidence (z : Fin J → Candidate M m r) (a : Fin M) :
    (listOf z).countP (fun e => e.1.getD a.val false) =
      count {c : Candidate M m r | a ∈ c.1.val} z := by
  apply countP_ofFn_eq_sampleCount z entryOf
  intro c
  change (mask c.1.val).getD a.val false = true ↔ a ∈ c.1.val
  rw [getD_mask, decide_eq_true_eq]

theorem count_badRank (z : Fin J → Candidate M m r) (d : List Bool) :
    (listOf z).countP (fun e => !SparseSearch.maskedFullRank e.2 d) =
      count {c : Candidate M m r | BadRank (maskSet M d) c} z := by
  apply countP_ofFn_eq_sampleCount z entryOf
  intro c
  exact maskedFullRank_code_false c d

/-- A successful mathematical list yields a successful finite code.
The use of classical support enumerations here is an existence argument,
not an assertion that the encoding map is computable. -/
theorem good_of_isGood (z : Fin J → Candidate M m r) (τ θ : ℚ)
    (hz : SparseCandidateList.IsGood z (τ : ℝ) (θ : ℝ)) (hM : 0 < M) :
    SparseListSearch.Good M m r J τ θ (listOf z) := by
  classical
  refine ⟨length_listOf z, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact goodEntry_entryOf (z j)
  · intro i hi
    rw [count_incidence z (⟨i, hi⟩ : Fin M)]
    have hinc := hz.incidence (⟨i, hi⟩ : Fin M)
    have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
    have he : (M : ℝ) * (2 * ((m : ℝ) / M) * J) = 2 * (m : ℝ) * J := by
      field_simp [hM0]
    have hm := mul_le_mul_of_nonneg_left hinc (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
    rw [he] at hm
    exact_mod_cast hm
  · intro d hd hD
    rw [count_badRank]
    have hdR : (τ : ℝ) * M ≤ ((maskSet M d).card : ℝ) := by
      rw [card_maskSet M d hd]
      exact_mod_cast hD
    have hrank := hz.preservesRank (maskSet M d) hdR
    exact_mod_cast hrank

/-- The finite good-code predicate has a witness for every sufficiently large
rank and every fixed positive pair of rational parameters. -/
theorem eventually_exists_goodCode (τ θ : ℚ) (hτ : 0 < τ) (hθ : 0 < θ) :
    ∀ᶠ r : ℕ in Filter.atTop, ∃ L : SparseListSearch.CodeList,
      SparseListSearch.Good (SparseParameters.blockSize r) (SparseParameters.supportSize r)
        r (SparseParameters.listSize r) τ θ L := by
  have hτR : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hθR : (0 : ℝ) < θ := by exact_mod_cast hθ
  filter_upwards [SparseCandidateList.eventually_exists_goodList (τ : ℝ) (θ : ℝ) hτR hθR,
    Filter.eventually_ge_atTop 1] with r hr hr1
  obtain ⟨z, hz⟩ := hr
  have hM : 0 < SparseParameters.blockSize r := Nat.pow_pos (by omega)
  exact ⟨listOf z, good_of_isGood z τ θ hz hM⟩

end Klr.SparseListCode
