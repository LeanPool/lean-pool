/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Polynomial
public import Mathlib.FieldTheory.ChevalleyWarning

/-!
# Quadratic forms over finite fields are isotropic in three or more variables

Over a finite field every quadratic form in at least three variables has a nonzero null vector.
This is the Chevalley–Warning theorem applied to the polynomial `GPR 11.8` attaches to the form:
its total degree is `2`, which is smaller than the number of variables, so the number of solutions
of `q = 0` is divisible by the characteristic. The zero vector is one solution, hence there are at
least `p ≥ 2` of them.

Over a field the two isotropy notions of the literature agree
(`QuadraticMap.isGPRIsotropic_iff_not_anisotropic`), so this also produces a *unimodular* null
vector in the sense of `GPR 11.17`.

## Main results

* `QuadraticForm.not_anisotropic_of_two_lt_finrank` : over a finite field, a quadratic form on a
  space of dimension greater than two is not anisotropic.
* `QuadraticForm.exists_ne_zero_apply_eq_zero_of_two_lt_finrank` : the same, stated as the
  existence of a nonzero null vector.

## Implementation notes

The count is run on the solution *subtype* `{x : Fin n → K // eval x f = 0}` that
`char_dvd_card_solutions` speaks about. Rather than exhibiting two solutions
directly, the proof assumes anisotropy, deduces that the subtype is a singleton, and concludes
`p ∣ 1`; this avoids having to produce a second solution by hand.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.8, 23.14.
* [EKM] Elman, Karpenko, Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*.
-/

@[expose] public section

universe u v

namespace QuadraticForm

variable {K : Type u} [Field K] [Finite K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- **Chevalley–Warning for quadratic forms.** Over a finite field, a quadratic form on a vector
space of dimension greater than two is not anisotropic.

The polynomial `GPR 11.8` attaches to `q` in a basis has total degree at most two, which is less
than the number of variables, so the characteristic divides the number of its zeros. Anisotropy
would make the zero vector the only one. -/
theorem not_anisotropic_of_two_lt_finrank (q : QuadraticForm K V)
    (h : 2 < Module.finrank K V) : ¬ q.Anisotropic := by
  classical
  have : Fintype K := Fintype.ofFinite K
  intro hani
  set n := Module.finrank K V with hn
  let b : Module.Basis (Fin n) K V := Module.finBasis K V
  let f : MvPolynomial (Fin n) K := q.toMvPolynomial b
  have hval : ∀ x : Fin n → K, MvPolynomial.eval x f = q (b.equivFun.symm x) := by
    intro x
    rw [b.equivFun_symm_apply, ← QuadraticForm.aeval_toMvPolynomial_self (q := q) (bm := b) x]
    rfl
  -- Anisotropy makes the solution subtype a singleton.
  have hzero : MvPolynomial.eval (0 : Fin n → K) f = 0 := by
    rw [hval, map_zero, map_zero]
  have hcard : Fintype.card { x : Fin n → K // MvPolynomial.eval x f = 0 } = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, hzero⟩, fun y ↦ ?_⟩
    have hy : q (b.equivFun.symm (y : Fin n → K)) = 0 := (hval _).symm.trans y.2
    exact Subtype.ext (b.equivFun.symm.injective ((hani _ hy).trans (map_zero _).symm))
  -- Chevalley–Warning says the characteristic divides that count.
  set p := ringChar K with hp
  have : CharP K p := ringChar.charP K
  have hdeg : f.totalDegree < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    exact lt_of_le_of_lt (QuadraticForm.totalDegree_toMvPolynomial_le q b) h
  have hdvd : p ∣ Fintype.card { x : Fin n → K // MvPolynomial.eval x f = 0 } :=
    char_dvd_card_solutions p hdeg
  rw [hcard] at hdvd
  exact CharP.char_ne_one K p (Nat.dvd_one.mp hdvd)

/-- **Chevalley–Warning for quadratic forms**, stated as the existence of a nonzero null vector. -/
theorem exists_ne_zero_apply_eq_zero_of_two_lt_finrank (q : QuadraticForm K V)
    (h : 2 < Module.finrank K V) : ∃ v : V, v ≠ 0 ∧ q v = 0 := by
  by_contra hcon
  exact q.not_anisotropic_of_two_lt_finrank h fun v hv ↦ by
    by_contra hv0
    exact hcon ⟨v, hv0, hv⟩

end QuadraticForm
