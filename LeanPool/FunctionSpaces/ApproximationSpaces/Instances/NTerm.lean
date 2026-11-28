/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Instances.Span

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Nonlinear `n`-term approximation from a dictionary

For a set `D ⊆ X`, the **dictionary**, the scheme `nTerm D` has

`A n = { linear combinations of at most n elements of D }`.

The approximant may use any `n` elements of `D`, chosen depending on `f`, so `A n` is a
union of subspaces and not itself a subspace.  This is nonlinear approximation in the sense
of DeVore: best `n`-term approximation from a wavelet basis or from a redundant dictionary.
The sets need not be closed, so best approximants need not exist.

Linear approximation from the first `n` elements of a sequence is a special case with fewer
approximants, so its errors are larger (`approxError_nTerm_le_ofSpan`).
-/

@[expose] public section

namespace ApproximationScheme

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The scheme of **`n`-term approximation** from a dictionary `D`: `A n` consists of the
linear combinations of at most `n` elements of `D`. -/
def nTerm (D : Set X) : ApproximationScheme X where
  sets n := {x | ∃ S : Finset X, (S : Set X) ⊆ D ∧ S.card ≤ n ∧ x ∈ Submodule.span ℝ (S : Set X)}
  sets_zero := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Nat.le_zero, Finset.card_eq_zero]
    constructor
    · rintro ⟨S, -, rfl, hx⟩
      simpa using hx
    · rintro rfl
      exact ⟨∅, by simp, rfl, Submodule.zero_mem _⟩
  mono _ _ h := by
    rintro x ⟨S, hSD, hS, hx⟩
    exact ⟨S, hSD, hS.trans h, hx⟩
  smul_mem c _ _ := by
    rintro ⟨S, hSD, hS, hx⟩
    exact ⟨S, hSD, hS, Submodule.smul_mem _ c hx⟩
  add_subset m n := by
    classical
    rintro _ ⟨a, ⟨S, hSD, hS, ha⟩, b, ⟨T, hTD, hT, hb⟩, rfl⟩
    refine ⟨S ∪ T, ?_, (Finset.card_union_le S T).trans (Nat.add_le_add hS hT), ?_⟩
    · rw [Finset.coe_union]; exact Set.union_subset hSD hTD
    · rw [Finset.coe_union]
      exact Submodule.add_mem _ (Submodule.span_mono Set.subset_union_left ha)
        (Submodule.span_mono Set.subset_union_right hb)

variable {D : Set X}

/-- `x ∈ A_n` iff `x` is a linear combination of at most `n` elements of `D`. -/
theorem mem_nTerm {n : ℕ} {x : X} : x ∈ nTerm D n ↔
    ∃ S : Finset X, (S : Set X) ⊆ D ∧ S.card ≤ n ∧ x ∈ Submodule.span ℝ (S : Set X) := Iff.rfl

/-- Every element of the dictionary is a `1`-term approximant. -/
theorem mem_nTerm_of_mem {x : X} (hx : x ∈ D) : x ∈ nTerm D 1 :=
  ⟨{x}, by simpa using hx, by simp, Submodule.subset_span (by simp)⟩

/-- Linear approximation from the first `n` elements of `e` is `n`-term approximation from
the dictionary `range e` with a fixed choice of the terms. -/
theorem ofSpan_subset_nTerm (e : ℕ → X) (n : ℕ) : ofSpan e n ⊆ nTerm (Set.range e) n := by
  classical
  intro x hx
  refine ⟨(Finset.range n).image e, ?_, ?_, ?_⟩
  · rw [Finset.coe_image]; exact Set.image_subset_range e _
  · exact (Finset.card_image_le).trans (Finset.card_range n).le
  · rw [Finset.coe_image, Finset.coe_range]; exact hx

/-- `n`-term approximation from `range e` is at least as good as linear approximation from
the first `n` elements of `e`. -/
theorem approxError_nTerm_le_ofSpan (e : ℕ → X) (f : X) (n : ℕ) :
    (nTerm (Set.range e)).approxError f n ≤ (ofSpan e).approxError f n :=
  approxError_anti_scheme (ofSpan_subset_nTerm e) f n

end ApproximationScheme
