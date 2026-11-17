/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.BivariateCoefficientMatrix
import LeanPool.CCDN.Noether.ClosedFormGradient
import LeanPool.CCDN.Noether.ClosedFormScaling

/-! The Euler constraint removes the gradient kernel from the bivariate
closed-form criterion. This supplies the injective operator needed for
Noether minors of degree d^2-1. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- Contraction with the radial vector field; the outer variable is x. -/
def bivariateEulerContraction (R : Type*) [CommRing R] :
    (R[X][X] × R[X][X]) →ₗ[R] R[X][X] where
  toFun u := X * u.1 + C X * u.2
  map_add' u v := by simp only [Prod.fst_add, Prod.snd_add, mul_add]; ring
  map_smul' a u := by
    simp only [Prod.smul_fst, Prod.smul_snd, mul_smul_comm, smul_add, RingHom.id_apply]

private lemma bivariateEulerContraction_gradient_leading {R : Type*} [CommRing R]
    (f : R[X][X]) (hm : f.Monic) (hd : 0 < f.natDegree) :
    (bivariateEulerContraction R (f.derivative, (bivariateCoefficientDerivative R) f)).coeff
      f.natDegree = (f.natDegree : R[X]) := by
  obtain ⟨d, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  change (X * f.derivative + C X * (bivariateCoefficientDerivative R) f).coeff f.natDegree = _
  have hc : f.coeff (d + 1) = 1 := by simpa only [he] using hm.coeff_natDegree
  rw [he, coeff_add, coeff_X_mul, coeff_derivative, hc, coeff_C_mul,
    coeff_bivariateCoefficientDerivative, hc, derivative_one]
  simp


/-- The closed form is zero once its radial contraction has no top outer
coefficient. The positive characteristic-zero degree makes Euler's factor
nonzero. -/
theorem bivariate_euler_closed_form_eq_zero
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (f p q : F[X][X]) (hf : Irreducible f) (hm : f.Monic) (hd : 0 < f.natDegree)
    (hpdeg : p.degree < f.degree) (hqdeg : q.degree < f.degree)
    (hclosed : closedFormOperator f (p, q) = 0)
    (heuler : (bivariateEulerContraction F (p, q)).coeff f.natDegree = 0) :
    p = 0 ∧ q = 0 := by
  have he : (bivariateCoefficientDerivative F) p * f - p * (bivariateCoefficientDerivative F) f =
      q.derivative * f - q * f.derivative := by
    change (bivariateCoefficientDerivative F) p * f - p * (bivariateCoefficientDerivative F) f -
      q.derivative * f + q * f.derivative = 0 at hclosed
    linear_combination hclosed
  have hnat (r : F[X][X]) (hr : r.degree < f.degree) : r.natDegree < f.natDegree := by
    by_cases h0 : r = 0
    · simpa only [h0, natDegree_zero] using hd
    · exact natDegree_lt_natDegree h0 hr
  let D := max (bivariateTotalDegree f) (bivariateTotalDegree p)
  obtain ⟨a, hp, hq⟩ := bivariate_closed_form_eq_gradient f p q hf hm (hnat p hpdeg)
    (hnat q hqdeg) D
    (fun i ↦ (bivariate_coefficient_natDegree_le_totalDegree f i).trans (le_max_left _ _))
    (fun i ↦ (bivariate_coefficient_natDegree_le_totalDegree p i).trans (le_max_right _ _))
    (.of_charZero _) (.of_charZero _) he
  have heq : (p, q) = a • (f.derivative, (bivariateCoefficientDerivative F) f) := by
    apply Prod.ext
    · simpa only [Prod.smul_fst, bivariate_smul_eq_constant_mul] using hp
    · simpa only [Prod.smul_snd, bivariate_smul_eq_constant_mul] using hq
  rw [heq, map_smul, coeff_smul, bivariateEulerContraction_gradient_leading f hm hd] at heuler
  have ha : a = 0 := by
    have hh := congrArg (fun P : F[X] => P.coeff 0) heuler
    rw [coeff_smul, ← C_eq_natCast, coeff_C_zero, coeff_zero] at hh
    change a * (f.natDegree : F) = 0 at hh
    exact (mul_eq_zero.mp hh).resolve_right (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))
  simp only [ha, map_zero, zero_mul] at hp hq
  exact ⟨hp, hq⟩

end
end CCDN
