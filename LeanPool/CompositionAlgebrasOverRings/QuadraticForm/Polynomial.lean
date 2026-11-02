/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.BaseChangeProjective
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# A quadratic form on a free module as a polynomial (`GPR 11.8`)

If `M` is free with basis `bm : Basis (Fin n) R M`, a quadratic form `q : M → R` is a homogeneous
quadratic polynomial in `n` variables, and evaluating that polynomial over any `R`-algebra `S`
computes `q` base-changed to `S`. This is what lets the LG axiom — which speaks about
`MvPolynomial (Fin n) R` — say anything about quadratic forms.

## Main definitions

* `QuadraticForm.toMvPolynomial q bm` : `∑ i, ∑ j, C (B (bm i) (bm j)) * X i * X j`, where `B` is
  the bilinear representative `QuadraticMap.bilinRepr q` used to define
  `QuadraticForm.baseChangeOfProjective`.

## Main results

* `QuadraticForm.aeval_toMvPolynomial_self` :
  `aeval t (toMvPolynomial q bm) = q (∑ i, t i • bm i)`.
* `QuadraticForm.aeval_toMvPolynomial` : the same after base change,
  `aeval s (toMvPolynomial q bm) = (q.baseChangeOfProjective S) (∑ i, s i • (1 ⊗ₜ bm i))`.
* `QuadraticForm.totalDegree_toMvPolynomial_le` : the polynomial has total degree at most two.

## Implementation notes

The polynomial is built from `QuadraticMap.bilinRepr q` rather than from `QuadraticMap.toBilin`
(mathlib's triangular representative) purely so that the base-change statement is immediate:
`QuadraticForm.baseChangeOfProjective` is *defined* as the diagonal of
`LinearMap.BilinForm.baseChange` applied to `bilinRepr`, so both sides of
`aeval_toMvPolynomial` expand to the same double sum without needing
`baseChangeOfProjective_eq_of_toQuadraticMap_eq`. The polynomial is not canonical — a different
bilinear representative gives a different polynomial — but its evaluations are, which is all the
LG axiom cares about.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.8.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace QuadraticForm

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M] {n : ℕ}

variable (q : QuadraticForm R M) (bm : Module.Basis (Fin n) R M)

/-- The quadratic polynomial of `q` in the basis `bm` (`GPR 11.8`), built from the bilinear
representative that `QuadraticForm.baseChangeOfProjective` uses. -/
noncomputable def toMvPolynomial : MvPolynomial (Fin n) R :=
  ∑ i, ∑ j, MvPolynomial.C (QuadraticMap.bilinRepr q (bm i) (bm j)) *
    MvPolynomial.X i * MvPolynomial.X j

/-- The polynomial of a quadratic form in a basis is quadratic: its total degree is at most two.
Each summand `C (B (bm i) (bm j)) * X i * X j` is a constant times two variables. -/
theorem totalDegree_toMvPolynomial_le :
    (QuadraticForm.toMvPolynomial q bm).totalDegree ≤ 2 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · let : Subsingleton (MvPolynomial (Fin n) R) := inferInstance
    rw [Subsingleton.elim (QuadraticForm.toMvPolynomial q bm) 0, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le 2
  have hterm : ∀ i j : Fin n, (MvPolynomial.C (QuadraticMap.bilinRepr q (bm i) (bm j)) *
      MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin n) R).totalDegree ≤ 2 := by
    intro i j
    have h₁ := MvPolynomial.totalDegree_mul
      (MvPolynomial.C (QuadraticMap.bilinRepr q (bm i) (bm j)) *
        (MvPolynomial.X i : MvPolynomial (Fin n) R)) (MvPolynomial.X j)
    have h₂ := MvPolynomial.totalDegree_mul
      (MvPolynomial.C (QuadraticMap.bilinRepr q (bm i) (bm j)))
      (MvPolynomial.X i : MvPolynomial (Fin n) R)
    rw [MvPolynomial.totalDegree_C] at h₂
    rw [MvPolynomial.totalDegree_X] at h₁ h₂
    omega
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le fun i _ ↦ ?_)
  exact le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le fun j _ ↦ hterm i j)

variable {q bm}

/-- Evaluating `toMvPolynomial` over an `R`-algebra `S` gives a double sum in the Gram matrix of
the bilinear representative. -/
theorem aeval_toMvPolynomial_eq_sum {S : Type w} [CommRing S] [Algebra R S] (s : Fin n → S) :
    MvPolynomial.aeval s (QuadraticForm.toMvPolynomial q bm) =
      ∑ i, ∑ j, algebraMap R S (QuadraticMap.bilinRepr q (bm i) (bm j)) * s i * s j := by
  simp only [toMvPolynomial, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]

/-- A bilinear form evaluated on a pair of finite sums is the double sum of its values. -/
private theorem bilin_sum_sum {S : Type w} [CommRing S] {P : Type*} [AddCommGroup P] [Module S P]
    (T : LinearMap.BilinForm S P) (f g : Fin n → P) :
    T (∑ i, f i) (∑ j, g j) = ∑ i, ∑ j, T (f i) (g j) := by
  simp only [map_sum, LinearMap.sum_apply]
  exact Finset.sum_comm

/-- **`GPR 11.8`, over `R` itself.** -/
theorem aeval_toMvPolynomial_self (t : Fin n → R) :
    MvPolynomial.aeval t (QuadraticForm.toMvPolynomial q bm) = q (∑ i, t i • bm i) := by
  rw [aeval_toMvPolynomial_eq_sum, ← QuadraticMap.bilinRepr_apply_self q,
    bilin_sum_sum (QuadraticMap.bilinRepr q)]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Algebra.algebraMap_self_apply]
  ring

/-- **`GPR 11.8`.** The polynomial of `q` in a basis computes `q` after every base change: its
value at `s : Fin n → S` is `q_S` evaluated at the corresponding point of `S ⊗[R] M`. -/
theorem aeval_toMvPolynomial {S : Type w} [CommRing S] [Algebra R S] (s : Fin n → S) :
    MvPolynomial.aeval s (QuadraticForm.toMvPolynomial q bm) =
      (q.baseChangeOfProjective S) (∑ i, s i • ((1 : S) ⊗ₜ[R] bm i)) := by
  rw [aeval_toMvPolynomial_eq_sum, QuadraticForm.baseChangeOfProjective,
    LinearMap.BilinMap.toQuadraticMap_apply,
    bilin_sum_sum (LinearMap.BilinForm.baseChange S (QuadraticMap.bilinRepr q))]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [map_smul, LinearMap.smul_apply, LinearMap.BilinForm.baseChange_tmul, mul_one,
    smul_eq_mul, Algebra.smul_def]
  ring

end QuadraticForm
