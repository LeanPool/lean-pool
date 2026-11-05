/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.EulerClosedFormRank
import LeanPool.CCDN.Noether.BivariateFactorForms
import LeanPool.CCDN.Noether.ClosedFormScaling
import LeanPool.CCDN.Noether.EulerPairRange

/-! Degree-correct logarithmic factor forms for the Euler-restricted
operator. The construction works in every characteristic. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

private lemma bivariateTotalDegree_sub_le {R : Type*} [CommRing R] (f g : R[X][X]) :
    bivariateTotalDegree (f - g) ≤ max (bivariateTotalDegree f) (bivariateTotalDegree g) := by
  unfold bivariateTotalDegree
  rw [map_sub]
  exact MvPolynomial.totalDegree_sub _ _

private lemma bivariateEuler_gradient_coeff {R : Type*} [CommRing R]
    (f : R[X][X]) (i j : ℕ) :
    (((bivariateEulerContraction R
      (f.derivative, (bivariateCoefficientDerivative R) f)).coeff i).coeff j) =
      ((i + j : ℕ) : R) * (f.coeff i).coeff j := by
  change ((X * f.derivative + C X * (bivariateCoefficientDerivative R) f).coeff i).coeff j = _
  cases i with
  | zero =>
    simp only [coeff_add, coeff_X_mul_zero, zero_add, coeff_C_mul,
      coeff_bivariateCoefficientDerivative]
    cases j with
    | zero => simp
    | succ j =>
      rw [coeff_X_mul, coeff_derivative]
      push_cast
      ring
  | succ i =>
    rw [coeff_add, coeff_X_mul, coeff_derivative, coeff_C_mul, coeff_add,
      coeff_bivariateCoefficientDerivative]
    rw [show (i : R[X]) + 1 = C ((i : R) + 1) by simp, coeff_mul_C]
    cases j with
    | zero => simp [mul_comm]
    | succ j =>
      rw [coeff_X_mul, coeff_derivative]
      push_cast
      ring

private lemma bivariateEuler_defect_degree {R : Type*} [CommRing R]
    (d : ℕ) (hd : 0 < d) (f : R[X][X]) (hf : bivariateTotalDegree f ≤ d) :
    bivariateTotalDegree
      (bivariateEulerContraction R (f.derivative, (bivariateCoefficientDerivative R) f) -
        (d : R) • f) ≤ d - 1 := by
  rw [bivariateTotalDegree_le_iff]
  intro i j hij
  rw [coeff_sub, coeff_sub, bivariateEuler_gradient_coeff, coeff_smul, coeff_smul,
    smul_eq_mul] at hij
  have hc : (f.coeff i).coeff j ≠ 0 := by
    intro hz
    simp only [hz, mul_zero, sub_self, ne_eq, not_true_eq_false] at hij
  have hh := (bivariateTotalDegree_coeff_le f i j hc).trans hf
  have hne : i + j ≠ d := by
    intro he
    rw [he, sub_self] at hij
    exact hij rfl
  omega

/-- The logarithmic factor pair of `g` and `h` with weights `a` and `b`: the pair `(P, Q)` with
`(P dx + Q dy) / (g * h) = b • dg / g - a • dh / h`, so `P = b • h * ∂ₓg - a • g * ∂ₓh` for the
outer derivative `∂ₓ` and `Q = b • h * ∂ᵧg - a • g * ∂ᵧh` for the inner derivative `∂ᵧ`. -/
def eulerFactorPair {R : Type*} [CommRing R] (a b : ℕ)
    (g h : R[X][X]) : R[X][X] × R[X][X] :=
  ((b : R) • (h * g.derivative) - (a : R) • (g * h.derivative),
   (b : R) • (h * (bivariateCoefficientDerivative R) g) -
     (a : R) • (g * (bivariateCoefficientDerivative R) h))

private lemma eulerFactorPair_contraction {R : Type*} [CommRing R] (a b : ℕ)
    (g h : R[X][X]) :
    bivariateEulerContraction R (eulerFactorPair a b g h) =
      (b : R) • (h * (bivariateEulerContraction R
        (g.derivative, (bivariateCoefficientDerivative R) g) - (a : R) • g)) -
      (a : R) • (g * (bivariateEulerContraction R
        (h.derivative, (bivariateCoefficientDerivative R) h) - (b : R) • h)) := by
  simp only [eulerFactorPair, bivariateEulerContraction, LinearMap.coe_mk, AddHom.coe_mk,
    bivariate_smul_eq_constant_mul]
  ring

private lemma eulerFactorPair_closed {F : Type*} [Field F] (a b : ℕ)
    (g h : F[X][X]) :
    closedFormOperator (g * h) (eulerFactorPair a b g h) = 0 := by
  have hg := bivariate_factor_closed_form g h
  have hh := bivariate_factor_closed_form h g
  have hg' : closedFormOperator (g * h)
      (h * g.derivative, h * (bivariateCoefficientDerivative F) g) = 0 := by
    change _ - _ - _ + _ = (0 : F[X][X])
    linear_combination hg
  have hh' : closedFormOperator (g * h)
      (g * h.derivative, g * (bivariateCoefficientDerivative F) h) = 0 := by
    rw [mul_comm g h]
    change _ - _ - _ + _ = (0 : F[X][X])
    linear_combination hh
  change closedFormOperator (g * h)
    ((b : F) • (h * g.derivative, h * (bivariateCoefficientDerivative F) g) -
      (a : F) • (g * h.derivative, g * (bivariateCoefficientDerivative F) h)) = 0
  rw [map_sub, map_smul, map_smul, hg', hh', smul_zero, smul_zero, sub_self]

/-- If `g` and `h` have total degrees at most `a` and `b` with `a, b > 0` and `a + b = k + 2`, and
their logarithmic factor pair is nonzero, then the Euler closed-form operator of `g * h` has a
nonzero kernel vector in `EulerPairSpace F k`. -/
theorem exists_eulerFactorKernel {F : Type*} [Field F]
    (k a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = k + 2)
    (g h : F[X][X]) (hg : bivariateTotalDegree g ≤ a)
    (hh : bivariateTotalDegree h ≤ b)
    (hne : eulerFactorPair a b g h ≠ 0) :
    ∃ u : EulerPairSpace F k, u ≠ 0 ∧ eulerClosedFormOperator k (g * h) u = 0 := by
  have hpart (s t : F[X][X]) (c e : ℕ) (hc : 0 < c)
      (hs : bivariateTotalDegree s ≤ c) (ht : bivariateTotalDegree t ≤ e)
      (hce : c + e = k + 2) :
      bivariateTotalDegree (t * s.derivative) ≤ k + 1 ∧
        bivariateTotalDegree (t * (bivariateCoefficientDerivative F) s) ≤ k + 1 := by
    constructor
    · have h₁ := bivariateTotalDegree_mul_le t s.derivative
      have h₂ := bivariateTotalDegree_outerDerivative_le s
      omega
    · have h₁ := bivariateTotalDegree_mul_le t ((bivariateCoefficientDerivative F) s)
      have h₂ := bivariateTotalDegree_innerDerivative_le s
      omega
  obtain ⟨hgp, hgq⟩ := hpart g h a b ha hg hh hab
  obtain ⟨hhp, hhq⟩ := hpart h g b a hb hh hg (by omega)
  have hp : bivariateTotalDegree (eulerFactorPair a b g h).1 ≤ k + 1 :=
    (bivariateTotalDegree_sub_le _ _).trans (max_le
      ((bivariateTotalDegree_smul_le _ _).trans hgp)
      ((bivariateTotalDegree_smul_le _ _).trans hhp))
  have hq : bivariateTotalDegree (eulerFactorPair a b g h).2 ≤ k + 1 :=
    (bivariateTotalDegree_sub_le _ _).trans (max_le
      ((bivariateTotalDegree_smul_le _ _).trans hgq)
      ((bivariateTotalDegree_smul_le _ _).trans hhq))
  have he : bivariateTotalDegree
      (bivariateEulerContraction F (eulerFactorPair a b g h)) ≤ k + 1 := by
    rw [eulerFactorPair_contraction]
    apply (bivariateTotalDegree_sub_le _ _).trans
    apply max_le
    · apply (bivariateTotalDegree_smul_le _ _).trans
      have h₁ := bivariateTotalDegree_mul_le h
        (bivariateEulerContraction F (g.derivative, (bivariateCoefficientDerivative F) g) -
          (a : F) • g)
      have h₂ := bivariateEuler_defect_degree a ha g hg
      omega
    · apply (bivariateTotalDegree_smul_le _ _).trans
      have h₁ := bivariateTotalDegree_mul_le g
        (bivariateEulerContraction F (h.derivative, (bivariateCoefficientDerivative F) h) -
          (b : F) • h)
      have h₂ := bivariateEuler_defect_degree b hb h hh
      omega
  obtain ⟨u, hu⟩ := exists_eulerBivariatePair k _ _ hp hq he
  refine ⟨u, ?_, ?_⟩
  · intro hz
    rw [hz, map_zero] at hu
    exact hne hu.symm
  · change closedFormOperator (g * h) (eulerBivariatePair F k u) = 0
    rw [hu]
    exact eulerFactorPair_closed a b g h

end
end CCDN
