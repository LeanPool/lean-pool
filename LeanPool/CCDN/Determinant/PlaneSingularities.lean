/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.PDeriv
import LeanPool.CCDN.Algebra.CharZeroOrGT
import LeanPool.CCDN.ForMathlib.MvPolynomialDerivative
import LeanPool.CCDN.Plane.Bezout

/-! The singular-point correction in the finite-field curve estimate. The
remaining estimate for all nonsingular rational points is not asserted here. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A partial derivative lowers the total degree by at least one. -/
theorem pderiv_totalDegree_le {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (i : σ) : (pderiv i f).totalDegree ≤ f.totalDegree - 1 := by
  classical
  apply Finset.sup_le
  intro m hm
  have hcoeff : f.coeff (m + Finsupp.single i 1) ≠ 0 := by
    have h := mem_support_iff.mp hm
    rw [coeff_pderiv] at h
    exact left_ne_zero_of_mul h
  have hd := le_totalDegree (mem_support_iff.mpr hcoeff)
  have he : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index (by simp) (by intros; rfl)]
    simp
  rw [he] at hd
  omega

/-- A nonzero polynomial does not divide any of its nonzero partial derivatives, since these
have smaller total degree. -/
theorem not_dvd_pderiv_of_pderiv_ne_zero {K σ : Type*} [Field K]
    {f : MvPolynomial σ K} (hf : f ≠ 0) {i : σ} (hi : pderiv i f ≠ 0) : ¬ f ∣ pderiv i f := by
  rintro ⟨q, he⟩
  have hq : q ≠ 0 := by rintro rfl; exact hi (by rw [he, mul_zero])
  have hpos : 0 < f.totalDegree := by
    refine Nat.pos_of_ne_zero fun h0 => hi ?_
    rw [totalDegree_eq_zero_iff_eq_C.mp h0, pderiv_C]
  have htotal := totalDegree_mul_of_isDomain hf hq
  rw [← he] at htotal
  have := pderiv_totalDegree_le f i
  omega

/-- Distinct singular points of an irreducible plane equation of degree `d`
number at most `d(d-1)`, whenever the degree is smaller than the characteristic. -/
theorem plane_singular_points_card_le {K ι : Type*} [Field K] [Fintype ι]
    {p : ℕ} [CharP K p] (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) (hchar : f.totalDegree < p)
    (z : ι → Fin 2 → K) (hz : Function.Injective z)
    (hzf : ∀ i, eval (z i) f = 0)
    (hzsing : ∀ i j, eval (z i) (pderiv j f) = 0) :
    Fintype.card ι ≤ f.totalDegree * (f.totalDegree - 1) := by
  classical
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero hpos (CharZeroOrGT.of_charP hchar)
  exact (plane_common_zeros_card_le f (pderiv j f) hf
    (not_dvd_pderiv_of_pderiv_ne_zero hf.ne_zero hj) z hz hzf
    (fun i => hzsing i j)).trans (Nat.mul_le_mul_left _ (pderiv_totalDegree_le f j))

end
end CCDN
