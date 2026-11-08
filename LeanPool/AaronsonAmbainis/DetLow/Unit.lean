/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Tactic.Push
public import LeanPool.AaronsonAmbainis.DetDefs

/-!
# DetLow: multiplication by a polynomial with constant coefficient 1

Multiplying by a polynomial with constant coefficient `1` does not change the monomials of
least total degree. This is Lemma 3.3 of the paper.
-/

@[expose] public section

namespace AaronsonAmbainis
namespace DetLow

open Finset MvPolynomial

/-- Key computation: if every monomial of `q` has total degree at least that of `m`, then
`u * q` and `q` have the same coefficient at `m` (when `u` has constant coefficient `1`). -/
theorem coeff_unit_mul {ι : Type} [Fintype ι] (u q : MvPolynomial ι ℤ)
    (hu : constantCoeff u = 1) (m : ι →₀ ℕ)
    (hm : ∀ m' ∈ q.support, ∑ i, m i ≤ ∑ i, m' i) :
    (u * q).coeff m = q.coeff m := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (0, m)]
  · have h0 : u.coeff 0 = 1 := hu
    simp [h0]
  · rintro ⟨a, b⟩ hab hne
    have hsum : a + b = m := by simpa using hab
    have ha : a ≠ 0 := by
      rintro rfl
      apply hne
      rw [zero_add] at hsum
      rw [hsum]
    have hb : q.coeff b = 0 := by
      by_contra h
      have h1 := hm b (mem_support_iff.mpr h)
      obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact ha (Finsupp.ext hcon)
      have h2 : 1 ≤ ∑ i, a i :=
        (Nat.one_le_iff_ne_zero.mpr hi).trans
          (Finset.single_le_sum (f := fun i => a i) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i))
      have h3 : ∑ i, m i = ∑ i, a i + ∑ i, b i := by
        rw [← hsum]
        simp [Finset.sum_add_distrib]
      omega
    simp [hb]
  · intro h
    exact absurd (by simp) h

/-- Forward direction of `LowestUnit`. -/
theorem isLowest_unit_mul {ι : Type} [Fintype ι] (u q : MvPolynomial ι ℤ)
    (hu : constantCoeff u = 1) (m : ι →₀ ℕ) (h : IsLowest q m) : IsLowest (u * q) m := by
  obtain ⟨hmem, hmin⟩ := h
  refine ⟨?_, ?_⟩
  · rw [mem_support_iff, coeff_unit_mul u q hu m hmin]
    exact mem_support_iff.mp hmem
  · intro m' hm'
    by_contra hlt
    push Not at hlt
    have hmin' : ∀ m'' ∈ q.support, ∑ i, m' i ≤ ∑ i, m'' i := fun m'' h'' =>
      hlt.le.trans (hmin m'' h'')
    have h1 := coeff_unit_mul u q hu m' hmin'
    have h2 : q.coeff m' = 0 := by
      by_contra hne
      have := hmin m' (mem_support_iff.mpr hne)
      omega
    rw [mem_support_iff, h1] at hm'
    exact hm' h2

/-- A nonzero polynomial has a monomial of least total degree. -/
theorem exists_isLowest {ι : Type} [Fintype ι] (q : MvPolynomial ι ℤ) (hq : q ≠ 0) :
    ∃ m, IsLowest q m := by
  have hne : q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hq (support_eq_empty.mp h)
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image q.support (fun m => ∑ i, m i) hne
  exact ⟨m, hm, hmin⟩

/-- Backward direction of `LowestUnit`. -/
theorem isLowest_of_unit_mul {ι : Type} [Fintype ι] (u q : MvPolynomial ι ℤ)
    (hu : constantCoeff u = 1) (m : ι →₀ ℕ) (h : IsLowest (u * q) m) : IsLowest q m := by
  have hq : q ≠ 0 := by
    rintro rfl
    have h0 := h.1
    simp at h0
  obtain ⟨m0, hm0⟩ := exists_isLowest q hq
  have hm0' := isLowest_unit_mul u q hu m0 hm0
  have hle1 : ∑ i, m i ≤ ∑ i, m0 i := h.2 m0 hm0'.1
  have hmin : ∀ m' ∈ q.support, ∑ i, m i ≤ ∑ i, m' i := fun m' hm' =>
    hle1.trans (hm0.2 m' hm')
  refine ⟨?_, hmin⟩
  have h1 := h.1
  rw [mem_support_iff, coeff_unit_mul u q hu m hmin] at h1
  exact mem_support_iff.mpr h1

end DetLow
end AaronsonAmbainis
