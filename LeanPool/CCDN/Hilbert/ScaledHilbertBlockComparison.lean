/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
import LeanPool.CCDN.Hilbert.PolynomialComparison
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.Tactic.Positivity

/-! Polynomial parameters of degree at most q have function-field degree
at most the Hilbert multiplicity times q to the dimension. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- If `I` has affine dimension `m` and degree `d`, and `r · (m + N).choose m` is at most the affine
Hilbert function of `I` at `D + q N` for all `N`, then `r ≤ d · q ^ m`. -/
theorem hilbert_scaled_block_count_le_multiplicity
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) (m d r D q : ℕ) (hq : 0 < q)
    (hdimdeg : HasAffineDimensionDegree I m d)
    (hlow : ∀ N, r * (m + N).choose m ≤
      Module.finrank K (filteredCoordinateSpace I (D + q * N))) : r ≤ d * q ^ m := by
  obtain ⟨hdim, hdegree⟩ := hdimdeg
  by_cases hr : r = 0
  · omega
  let P := Polynomial.C (r : ℚ) * Polynomial.preHilbertPoly ℚ m 0
  let Q := (filteredHilbertPolynomial I).comp
    (Polynomial.C (q : ℚ) * Polynomial.X + Polynomial.C (D : ℚ))
  have hPdeg : P.natDegree = m := by
    dsimp only [P]
    rw [Polynomial.natDegree_C_mul (by exact_mod_cast hr),
      Polynomial.natDegree_preHilbertPoly]
  have hlinearDegree :
      (Polynomial.C (q : ℚ) * Polynomial.X + Polynomial.C (D : ℚ)).natDegree = 1 := by
    rw [Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul (by positivity),
      Polynomial.natDegree_X]
  have hlinearLC :
      (Polynomial.C (q : ℚ) * Polynomial.X + Polynomial.C (D : ℚ)).leadingCoeff = (q : ℚ) := by
    rw [Polynomial.leadingCoeff, hlinearDegree]
    simp
  have hQdeg : Q.natDegree = m := by
    simp only [Q, Polynomial.natDegree_comp, hlinearDegree, mul_one, hdim]
  have hPlc : P.leadingCoeff = (r : ℚ) / m.factorial := by
    dsimp only [P]
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_preHilbertPoly, div_eq_mul_inv]
  have hQlc : Q.leadingCoeff = (filteredHilbertPolynomial I).leadingCoeff * (q : ℚ) ^ m := by
    dsimp only [Q]
    rw [Polynomial.leadingCoeff_comp (by rw [hlinearDegree]; exact one_ne_zero), hlinearLC, hdim]
  have hPpos : 0 < P.leadingCoeff := by rw [hPlc]; positivity
  have hQpos : 0 < Q.leadingCoeff := by
    rw [hQlc]
    exact mul_pos (filteredHilbertPolynomial_leadingCoeff_pos I hI) (by positivity)
  have hh := polynomial_leadingCoeff_le_of_eventual_nat_eval_le P Q hPpos hQpos
    (hPdeg.trans hQdeg.symm) (by
      obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
      refine ⟨M, fun N hN => ?_⟩
      simp only [P, Q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
        Polynomial.eval_add, Polynomial.eval_X]
      rw [Polynomial.preHilbertPoly_eq_choose_add_sub ℚ m (by omega : 0 ≤ N + m),
        show (q : ℚ) * N + D = ((D + q * N : ℕ) : ℚ) by push_cast; ring,
        hM (D + q * N) (by nlinarith)]
      simp only [Nat.sub_zero, Nat.add_comm N m]
      exact_mod_cast hlow N)
  rw [hPlc, hQlc, hdegree] at hh
  have hqbound : (r : ℚ) ≤ (d : ℚ) * q ^ m := by
    apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℚ) < m.factorial)).mp
    convert hh using 1
    ring
  exact_mod_cast hqbound

end
end CCDN
