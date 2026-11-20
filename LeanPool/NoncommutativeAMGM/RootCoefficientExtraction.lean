/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.ChebyshevRootAverage

/-! # Extracting the leading real-polynomial coefficient with two root quadratures -/

@[expose] public section
namespace NoncommutativeAMGM
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- Root-grid averaging of a real polynomial on the real parts of the nodes. -/
noncomputable def rootPolynomialAverage (m : ℕ) (ξ ζ : ℂ) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := rootRealAverage m ξ ζ (fun z ↦ p.eval z.re)
  map_add' p q := by
    simp only [eval_add, rootRealAverage, Finset.sum_add_distrib]
    ring
  map_smul' a p := by
    simp only [eval_smul, smul_eq_mul, rootRealAverage, RingHom.id_apply]
    rw [← Finset.mul_sum]
    ring

theorem rootPolynomialAverage_apply (m : ℕ) (ξ ζ : ℂ) (p : Polynomial ℝ) :
    rootPolynomialAverage m ξ ζ p = rootRealAverage m ξ ζ (fun z ↦ p.eval z.re) := rfl

/-- The signed root quadratures extract the degree-`m` coefficient of every polynomial
of degree at most `m`. The normalization is fixed by the leading coefficient of `Tₘ`. -/
theorem rootPolynomialAverage_difference {m : ℕ} (hm : 0 < m) {ξplus ξminus ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hξplus : ξplus ^ m = 1) (hξminus : ξminus ^ m = -1)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ m) :
    rootPolynomialAverage m ξplus ζ p - rootPolynomialAverage m ξminus ζ p =
      (2 / (2 : ℝ) ^ (m - 1)) * p.coeff m := by
  classical
  let c : ℝ := 2 / (2 : ℝ) ^ (m - 1)
  let H : Polynomial ℝ →ₗ[ℝ] ℝ :=
    (rootPolynomialAverage m ξplus ζ - rootPolynomialAverage m ξminus ζ) - c • lcoeff ℝ m
  have htop (r : ℕ) (hr : r ≤ m) : H (T ℝ (r : ℤ)) = 0 := by
    have hplus := rootRealAverage_chebyshev hm hζ (η := (1 : ℝ))
      (by simpa using hξplus) (Or.inl rfl) r hr
    have hminus := rootRealAverage_chebyshev hm hζ (η := (-1 : ℝ))
      (by simpa using hξminus) (Or.inr rfl) r hr
    change rootPolynomialAverage m ξplus ζ (T ℝ (r : ℤ)) -
      rootPolynomialAverage m ξminus ζ (T ℝ (r : ℤ)) - c * (T ℝ (r : ℤ)).coeff m = 0
    rw [rootPolynomialAverage_apply, rootPolynomialAverage_apply, hplus, hminus]
    by_cases hrm : r = m
    · subst r
      have hdeg : (T ℝ (m : ℤ)).natDegree = m := by simp [natDegree_T]
      have hc : (T ℝ (m : ℤ)).coeff m = (2 : ℝ) ^ (m - 1) := by
        calc
          _ = (T ℝ (m : ℤ)).coeff (T ℝ (m : ℤ)).natDegree := by rw [hdeg]
          _ = _ := by rw [coeff_natDegree, leadingCoeff_T]; simp
      rw [hc]
      norm_num [c, hm.ne']
    · have hlt : r < m := by omega
      have hz : (T ℝ (r : ℤ)).coeff m = 0 := coeff_eq_zero_of_natDegree_lt (by
        simpa only [natDegree_T, Int.natAbs_natCast] using hlt)
      rw [hz]
      by_cases h0 : r = 0 <;> simp [hrm, h0]
  have hcoeff : ∀ i < m + 1, IsUnit ((chebyshevTSequence ℝ) i).leadingCoeff := by
    intro i _
    apply isUnit_iff_ne_zero.mpr
    exact leadingCoeff_ne_zero.mpr (T_ne_zero ℝ (i : ℤ))
  have hspan : Submodule.span ℝ ((chebyshevTSequence ℝ) '' Set.Iio (m + 1)) ≤ H.ker := by
    apply Submodule.span_le.mpr
    rintro q ⟨r, hr, rfl⟩
    exact htop r (by have := hr; change r < m + 1 at this; omega)
  have hpLT : p ∈ degreeLT ℝ (m + 1) := by
    apply mem_degreeLT.mpr
    apply degree_le_natDegree.trans_lt
    exact_mod_cast (show p.natDegree < m + 1 by omega)
  have hpSpan : p ∈ Submodule.span ℝ ((chebyshevTSequence ℝ) '' Set.Iio (m + 1)) := by
    rw [(chebyshevTSequence ℝ).span_degreeLT hcoeff]
    exact hpLT
  have hz : H p = 0 := hspan hpSpan
  change (rootPolynomialAverage m ξplus ζ p - rootPolynomialAverage m ξminus ζ p) -
    c * p.coeff m = 0 at hz
  exact sub_eq_zero.mp hz

/-- The slice coordinate at a real cosine parameter. -/
noncomputable def sliceCoordinatePolynomial (n : ℕ) : Polynomial ℝ :=
  C ((n : ℝ) / 2) * (1 - X)

theorem sliceCoordinatePolynomial_eval (n : ℕ) (t : ℝ) :
    (sliceCoordinatePolynomial n).eval t = (n : ℝ) / 2 * (1 - t) := by
  simp [sliceCoordinatePolynomial]

theorem sliceCoordinatePolynomial_natDegree (n : ℕ) :
    (sliceCoordinatePolynomial n).natDegree ≤ 1 := by
  apply (natDegree_mul_le (p := C ((n : ℝ) / 2)) (q := 1 - X)).trans
  simpa using natDegree_sub_le (1 : Polynomial ℝ) X

end NoncommutativeAMGM
