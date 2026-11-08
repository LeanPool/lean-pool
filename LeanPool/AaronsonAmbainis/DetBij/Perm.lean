/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import LeanPool.AaronsonAmbainis.DetBij.Identity

/-!
# DetBij / Perm: the bijection theorem

From `LowestUnit` and `LowestBound`: for every field of 1-wings `A x` at the ones of `g` there
is a permutation `σ` of the ones of `g` such that the agreement set of `σ x` and `x` is
disjoint from `A (σ x)` for every `x`, and `#{x : (σ x)_j = x_j} ≤ bdry g j` for every `j`
simultaneously.

This is the bijection theorem (Theorem 3.1 of the paper) for the inverse `σ` of the bijection
`τ` of the paper; `Bijection.lean` states it for `τ`. The proof is that of the paper: a monomial of
`det Q'` with exponents at most `bdry g j` (`exists_lowest_Qmat`, by the argument of
Lemma 3.8 (iii)), and the Leibniz formula for `det Q'` (`exists_perm_of_mem_support`).
-/

@[expose] public section

namespace AaronsonAmbainis.DetBij

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A nonzero polynomial has a monomial of least total degree. -/
theorem exists_isLowest (q : MvPolynomial ι ℤ) (hq : q ≠ 0) : ∃ m, IsLowest q m := by
  have hne : q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact fun h => hq (MvPolynomial.support_eq_empty.mp h)
  obtain ⟨m, hm, hmin⟩ :=
    Finset.exists_min_image q.support (fun m : ι →₀ ℕ => ∑ i, m i) hne
  exact ⟨m, hm, hmin⟩

/-- `det P * det M = det U * det Q'`. -/
theorem det_Pmat_mul_det_agMatrix (g : Cube ι → Bool) (A : Cube ι → Finset ι)
    (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    (Pmat g A).det * (agMatrix g).det = (Umat g A).det * (Qmat g A).det := by
  rw [← Matrix.det_mul, ← Matrix.det_mul, Pmat_mul_agMatrix g A hA]

/-- `det Q'` has a monomial `m` with `m j ≤ bdry g j` for all `j`. -/
theorem exists_lowest_Qmat (hU : LowestUnit) (hB : LowestBound) (g : Cube ι → Bool)
    (A : Cube ι → Finset ι) (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    ∃ m : ι →₀ ℕ, m ∈ (Qmat g A).det.support ∧ ∀ j, m j ≤ bdry g j := by
  obtain ⟨hp, hbound⟩ := hB ι g
  have hdet := det_Pmat_mul_det_agMatrix g A hA
  have hP : (Pmat g A).det ≠ 0 := by
    intro h
    have h1 := constantCoeff_det_Pmat g A
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  have hQ : (Qmat g A).det ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdet
    exact (mul_ne_zero hP hp) hdet
  obtain ⟨m, hm⟩ := exists_isLowest _ hQ
  refine ⟨m, hm.1, hbound m ?_⟩
  have h1 : IsLowest ((Umat g A).det * (Qmat g A).det) m :=
    (hU ι _ _ (constantCoeff_det_Umat g A) m).mpr hm
  rw [← hdet] at h1
  exact (hU ι _ _ (constantCoeff_det_Pmat g A) m).mp h1

/-- A product of entries of `Q'` along a permutation is `0` or a single monomial. -/
theorem Qmat_prod_eq (g : Cube ι → Bool) (A : Cube ι → Finset ι) (σ : Equiv.Perm (Ones g)) :
    ∏ x : Ones g, Qmat g A (σ x) x
      = if ∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (A (σ x).1)
        then monomial (∑ x : Ones g, agExp (σ x).1 x.1) (1 : ℤ) else 0 := by
  split_ifs with h
  · rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Qmat_apply, ite_eq_left (h x), agMon_eq_monomial]
  · have h' : ∃ x : Ones g, ¬ Disjoint (agSet (σ x).1 x.1) (A (σ x).1) := not_forall.mp h
    obtain ⟨x, hx⟩ := h'
    refine Finset.prod_eq_zero (Finset.mem_univ x) ?_
    rw [Qmat_apply, ite_eq_right hx]

omit [Fintype ι] [DecidableEq ι] in
/-- A sign does not change whether a coefficient vanishes. -/
theorem coeff_units_smul_ne_zero (m : ι →₀ ℕ) (u : ℤˣ) (p : MvPolynomial ι ℤ)
    (h : (u • p).coeff m ≠ 0) : p.coeff m ≠ 0 := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using h
  · simpa using h

/-- Leibniz: every monomial of `det Q'` comes from a permutation all of whose entries are
nonzero. -/
theorem exists_perm_of_mem_support (g : Cube ι → Bool) (A : Cube ι → Finset ι) (m : ι →₀ ℕ)
    (hm : m ∈ (Qmat g A).det.support) :
    ∃ σ : Equiv.Perm (Ones g), (∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (A (σ x).1)) ∧
      m = ∑ x : Ones g, agExp (σ x).1 x.1 := by
  rw [MvPolynomial.mem_support_iff, Matrix.det_apply, MvPolynomial.coeff_sum] at hm
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have hσ' := coeff_units_smul_ne_zero m _ _ hσ
  rw [Qmat_prod_eq] at hσ'
  refine ⟨σ, ?_⟩
  by_cases h : ∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (A (σ x).1)
  · refine ⟨h, ?_⟩
    rw [ite_eq_left h, MvPolynomial.coeff_monomial] at hσ'
    by_contra hne
    rw [ite_eq_right (fun h' => hne h'.symm)] at hσ'
    exact hσ' rfl
  · rw [ite_eq_right h, AddMonoidAlgebra.coeff_zero] at hσ'
    exact absurd rfl hσ'

theorem sum_agExp_apply (g : Cube ι → Bool) (σ : Equiv.Perm (Ones g)) (j : ι) :
    (∑ x : Ones g, agExp (σ x).1 x.1) j
      = (univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card := by
  rw [Finsupp.finsetSum_apply, Finset.card_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [agExp_apply]

/-- The bijection theorem (Theorem 3.1 of the paper, for the inverse `σ` of the bijection `τ` of
the paper), from `LowestUnit` and `LowestBound`. -/
theorem exists_perm (hU : LowestUnit) (hB : LowestBound) (g : Cube ι → Bool)
    (A : Cube ι → Finset ι) (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    ∃ σ : Equiv.Perm (Ones g), (∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (A (σ x).1)) ∧
      ∀ j, (univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card ≤ bdry g j := by
  obtain ⟨m, hm, hmb⟩ := exists_lowest_Qmat hU hB g A hA
  obtain ⟨σ, hσ, rfl⟩ := exists_perm_of_mem_support g A m hm
  refine ⟨σ, hσ, fun j => ?_⟩
  rw [← sum_agExp_apply]
  exact hmb j

end AaronsonAmbainis.DetBij
