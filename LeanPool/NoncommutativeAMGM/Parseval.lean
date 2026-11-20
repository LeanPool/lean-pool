/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.Quadrature

/-!
# Root orthogonality and coefficient norms

The discrete Parseval identity behind Lemma 3.9.
-/

@[expose] public section

namespace NoncommutativeAMGM

open scoped BigOperators ComplexConjugate

theorem root_node_norm {m : ℕ} (hm : 0 < m) {ξ ζ η : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = η) (hη : η = 1 ∨ η = -1) (j : ℕ) :
    ‖ξ * ζ ^ j‖ = 1 := by
  have hξpow : ξ ^ (m * 2) = 1 := by
    rw [pow_mul, hξ]
    rcases hη with rfl | rfl <;> norm_num
  have hnξ := Complex.norm_eq_one_of_pow_eq_one hξpow (by omega)
  rw [norm_mul, norm_pow, hnξ, hζ.norm'_eq_one hm.ne']
  simp

/-- Orthogonality of monomials of degrees less than `m` at the root nodes. -/
theorem root_node_orthogonality {m : ℕ} (hm : 0 < m) {ξ ζ η : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = η) (hη : η = 1 ∨ η = -1)
    (i j : Fin m) :
    (m : ℂ)⁻¹ * ∑ k ∈ Finset.range m,
      conj ((ξ * ζ ^ k) ^ i.val) * (ξ * ζ ^ k) ^ j.val =
        if i = j then 1 else 0 := by
  have hprod (k : ℕ) : conj ((ξ * ζ ^ k) ^ i.val) * (ξ * ζ ^ k) ^ j.val =
      (ξ * ζ ^ k) ^ ((j.val : ℤ) - (i.val : ℤ)) := by
    have hn := root_node_norm hm hζ hξ hη k
    have hz : ξ * ζ ^ k ≠ 0 := by
      intro hz
      simp [hz] at hn
    rw [zpow_sub₀ hz, zpow_natCast, zpow_natCast, div_eq_mul_inv,
      map_pow, ← Complex.inv_eq_conj hn, inv_pow]
    ring
  simp_rw [hprod]
  change rootMonomialAverage m ξ ζ ((j.val : ℤ) - (i.val : ℤ)) = _
  rw [rootMonomialAverage_eq hm hζ]
  have hi : (i.val : ℤ) < m := by exact_mod_cast i.isLt
  have hj : (j.val : ℤ) < m := by exact_mod_cast j.isLt
  have hi0 : (0 : ℤ) ≤ i.val := by positivity
  have hj0 : (0 : ℤ) ≤ j.val := by positivity
  have hdiv : ((m : ℤ) ∣ (j.val : ℤ) - (i.val : ℤ)) ↔ i = j := by
    constructor
    · intro hd
      have he := dvd_in_quadrature_range hm (by omega) (by omega) hd
      apply Fin.ext
      rcases he with he | he | he <;> omega
    · intro he
      subst j
      simp
  simp only [hdiv]
  split_ifs with he
  · subst j
    simp
  · rfl

/-- Evaluation of a coefficient vector at a root node. -/
noncomputable def rootVectorEval {m : ℕ} (ξ ζ : ℂ) (p : Fin m → ℂ) (k : ℕ) : ℂ :=
  ∑ i, p i * (ξ * ζ ^ k) ^ i.val

/-- Discrete Parseval on the roots of `ωᵐ = η`, for a coefficient vector of length `m`. -/
theorem root_vector_parseval {m : ℕ} (hm : 0 < m) {ξ ζ η : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = η) (hη : η = 1 ∨ η = -1)
    (p : Fin m → ℂ) :
    (m : ℂ)⁻¹ * ∑ k ∈ Finset.range m,
      conj (rootVectorEval ξ ζ p k) * rootVectorEval ξ ζ p k =
        ∑ i, conj (p i) * p i := by
  have hexpand : (m : ℂ)⁻¹ * ∑ k ∈ Finset.range m,
      conj (rootVectorEval ξ ζ p k) * rootVectorEval ξ ζ p k =
      ∑ i : Fin m, ∑ j : Fin m, conj (p i) * p j *
        ((m : ℂ)⁻¹ * ∑ k ∈ Finset.range m,
          conj ((ξ * ζ ^ k) ^ i.val) * (ξ * ζ ^ k) ^ j.val) := by
    simp only [rootVectorEval, map_sum, map_mul]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hexpand]
  simp_rw [root_node_orthogonality hm hζ hξ hη]
  simp

/-- Root-node average of the square of the absolute value of a polynomial. -/
noncomputable def rootPolynomialSquareAverage (m : ℕ) (ξ ζ : ℂ) (p : Polynomial ℂ) : ℂ :=
  (m : ℂ)⁻¹ * ∑ k ∈ Finset.range m,
    conj (p.eval (ξ * ζ ^ k)) * p.eval (ξ * ζ ^ k)

theorem root_polynomial_parseval {m : ℕ} (hm : 0 < m) {ξ ζ η : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = η) (hη : η = 1 ∨ η = -1)
    (p : Polynomial ℂ) (hp : p.natDegree < m) :
    rootPolynomialSquareAverage m ξ ζ p =
      ∑ i : Fin m, conj (p.coeff i.val) * p.coeff i.val := by
  have heval (k : ℕ) : p.eval (ξ * ζ ^ k) =
      rootVectorEval ξ ζ (fun i : Fin m ↦ p.coeff i.val) k := by
    rw [rootVectorEval,
      Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ p.coeff i * (ξ * ζ ^ k) ^ i) m]
    exact Polynomial.eval_eq_sum_range' hp _
  simp only [rootPolynomialSquareAverage]
  simp_rw [heval]
  exact root_vector_parseval hm hζ hξ hη _

theorem root_node_pow {m : ℕ} {ξ ζ η : ℂ} (hζ : IsPrimitiveRoot ζ m)
    (hξ : ξ ^ m = η) (k : ℕ) : (ξ * ζ ^ k) ^ m = η := by
  have hpow : (ζ ^ k) ^ m = 1 := by
    rw [← pow_mul, Nat.mul_comm k m, pow_mul, hζ.pow_eq_one, one_pow]
  rw [mul_pow, hξ, hpow, mul_one]

/-- Polynomial division does not change values at the root nodes. -/
theorem root_remainder_eval {m : ℕ} {ξ ζ η : ℂ} (hζ : IsPrimitiveRoot ζ m)
    (hξ : ξ ^ m = η) (p : Polynomial ℂ) (k : ℕ) :
    (p %ₘ (Polynomial.X ^ m - Polynomial.C η)).eval (ξ * ζ ^ k) =
      p.eval (ξ * ζ ^ k) := by
  apply Polynomial.eval₂_modByMonic_eq_self_of_root (f := RingHom.id ℂ)
  simp [root_node_pow hζ hξ k]

/-- The remainder coefficient-norm identity in Lemma 3.9, before its `4⁻ʲ` rescaling.
No degree assumption on the original polynomial is needed. -/
theorem root_remainder_parseval {m : ℕ} (hm : 0 < m) {ξ ζ η : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = η) (hη : η = 1 ∨ η = -1)
    (p : Polynomial ℂ) :
    rootPolynomialSquareAverage m ξ ζ p =
      ∑ i : Fin m,
        conj ((p %ₘ (Polynomial.X ^ m - Polynomial.C η)).coeff i.val) *
          (p %ₘ (Polynomial.X ^ m - Polynomial.C η)).coeff i.val := by
  have hq : (Polynomial.X ^ m - Polynomial.C η : Polynomial ℂ) ≠ 1 := by
    intro heq
    have hdeg := congrArg Polynomial.natDegree heq
    rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_one] at hdeg
    omega
  have hdeg := Polynomial.natDegree_modByMonic_lt p
    (Polynomial.monic_X_pow_sub_C η hm.ne') hq
  rw [Polynomial.natDegree_X_pow_sub_C] at hdeg
  have haverage : rootPolynomialSquareAverage m ξ ζ p =
      rootPolynomialSquareAverage m ξ ζ (p %ₘ (Polynomial.X ^ m - Polynomial.C η)) := by
    simp only [rootPolynomialSquareAverage]
    simp_rw [root_remainder_eval hζ hξ]
  rw [haverage]
  exact root_polynomial_parseval hm hζ hξ hη _ hdeg

/-- The squared coefficient norm, summing only the finite support. -/
noncomputable def coefficientNormSq (p : Polynomial ℂ) : ℝ := p.sum (fun _ c ↦ ‖c‖ ^ 2)

theorem coefficientNormSq_eq_fin_sum {m : ℕ} (p : Polynomial ℂ) (hp : p.natDegree < m) :
    coefficientNormSq p = ∑ i : Fin m, ‖p.coeff i.val‖ ^ 2 := by
  rw [coefficientNormSq, Polynomial.sum_over_range' p (fun _ ↦ by simp) m hp,
    Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ ‖p.coeff i‖ ^ 2) m]

/-- Lemma 3.9 in coefficient-norm form, before multiplication by `4⁻ʲ`. -/
theorem root_remainder_coefficientNormSq {m : ℕ} (hm : 0 < m) {ξ ζ η : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = η) (hη : η = 1 ∨ η = -1)
    (p : Polynomial ℂ) :
    rootPolynomialSquareAverage m ξ ζ p =
      (coefficientNormSq (p %ₘ (Polynomial.X ^ m - Polynomial.C η)) : ℂ) := by
  have hq : (Polynomial.X ^ m - Polynomial.C η : Polynomial ℂ) ≠ 1 := by
    intro heq
    have hdeg := congrArg Polynomial.natDegree heq
    rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_one] at hdeg
    omega
  have hdeg := Polynomial.natDegree_modByMonic_lt p
    (Polynomial.monic_X_pow_sub_C η hm.ne') hq
  rw [Polynomial.natDegree_X_pow_sub_C] at hdeg
  rw [root_remainder_parseval hm hζ hξ hη p, coefficientNormSq_eq_fin_sum _ hdeg]
  push_cast
  simp only [Complex.conj_mul']

end NoncommutativeAMGM
