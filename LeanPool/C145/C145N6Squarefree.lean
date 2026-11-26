/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Tactic

/-!
# Squarefree polynomial certificates for the six-vertex tensor constraints.
-/

@[expose] public section
noncomputable section
open MvPolynomial
namespace C145N6
/-- Real polynomials in the three variables of the squarefree calculation. -/
abbrev Poly := MvPolynomial (Fin 3) ℝ
/-- The finitely supported exponent vector for a monomial in three variables. -/
def exponent (a b c : ℕ) : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![a,b,c]
@[simp] theorem exponent_apply (a b c : ℕ) (i : Fin 3) :
    exponent a b c i = ![a,b,c] i := rfl
theorem exponent_ext (d : Fin 3 →₀ ℕ) : d = exponent (d 0) (d 1) (d 2) := by
  ext i; fin_cases i <;> rfl
theorem squarefree_expansion (R : Poly) (hd : ∀ i, degreeOf i R ≤ 1) :
    R = ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2,
      monomial (exponent a.val b.val c.val) (R.coeff (exponent a.val b.val c.val)) := by
  ext d
  by_cases h : ∀ i, d i ≤ 1
  · have h0 := h 0; have h1 := h 1; have h2 := h 2
    rw [exponent_ext d]
    interval_cases hd0 : d 0 <;> interval_cases hd1 : d 1 <;> interval_cases hd2 : d 2 <;>
      simp [Fin.sum_univ_two, coeff_monomial, exponent]
  · have hz : R.coeff d = 0 := by
      by_contra hc
      have hm : d ∈ R.support := mem_support_iff.mpr hc
      exact h (fun i => degreeOf_le_iff.mp (hd i) d hm)
    rw [hz]
    simp only [coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro c _
    rw [coeff_monomial]
    split_ifs with he
    · exfalso
      apply h
      intro i
      rw [← he]
      fin_cases i
      · change a.val ≤ 1; omega
      · change b.val ≤ 1; omega
      · change c.val ≤ 1; omega
    · rfl
theorem symmetric_coeff (R : Poly) (hs : ∀ e : Equiv.Perm (Fin 3), rename e R = R)
    (e : Equiv.Perm (Fin 3)) (d : Fin 3 →₀ ℕ) :
    R.coeff (d.mapDomain e) = R.coeff d := by
  simpa only [hs e] using coeff_rename_mapDomain e e.injective R d

theorem swap01_exponent (a b c : ℕ) :
    (exponent a b c).mapDomain (Equiv.swap (0:Fin 3) 1) = exponent b a c := by
  ext i; fin_cases i <;> norm_num [Finsupp.mapDomain_equiv_apply, exponent, Equiv.swap_apply_def]
theorem swap12_exponent (a b c : ℕ) :
    (exponent a b c).mapDomain (Equiv.swap (1:Fin 3) 2) = exponent a c b := by
  ext i; fin_cases i <;> norm_num [Finsupp.mapDomain_equiv_apply, exponent, Equiv.swap_apply_def]
/-- The symmetric squarefree form with one coefficient for each total degree from zero to three. -/
def fourForm (c : Fin 4 → ℝ) : Poly :=
  monomial (exponent 0 0 0) (c 0) +
  (monomial (exponent 1 0 0) (c 1) + monomial (exponent 0 1 0) (c 1) + monomial (exponent 0 0 1)
    (c 1)) +
  (monomial (exponent 1 1 0) (c 2) + monomial (exponent 1 0 1) (c 2) + monomial (exponent 0 1 1)
    (c 2)) +
  monomial (exponent 1 1 1) (c 3)

theorem symmetric_squarefree_four (R : Poly) (hd : ∀ i, degreeOf i R ≤ 1)
    (hs : ∀ e : Equiv.Perm (Fin 3), rename e R = R) : ∃ c, R = fourForm c := by
  have h01 (a b c : ℕ) := symmetric_coeff R hs (Equiv.swap 0 1) (exponent a b c)
  simp only [swap01_exponent] at h01
  have h12 (a b c : ℕ) := symmetric_coeff R hs (Equiv.swap 1 2) (exponent a b c)
  simp only [swap12_exponent] at h12
  refine ⟨![R.coeff (exponent 0 0 0), R.coeff (exponent 1 0 0),
    R.coeff (exponent 1 1 0), R.coeff (exponent 1 1 1)], ?_⟩
  conv_lhs => rw [squarefree_expansion R hd]
  simp only [Fin.sum_univ_two, fourForm, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.val_zero, Fin.val_one]
  rw [h12 0 1 0, h01 1 0 0, h01 1 0 1, h12 1 1 0]
  abel
end C145N6

end
