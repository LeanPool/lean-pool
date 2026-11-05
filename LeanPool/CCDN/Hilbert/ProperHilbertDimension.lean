/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
public import Mathlib.RingTheory.Polynomial.HilbertPoly
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Hilbert.FullDimension

/-! A prime projective variety of degree greater than one cannot have
full ambient Hilbert dimension. This uses the Hilbert polynomial
of the polynomial ring, rather than an additional geometric hypothesis. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The filtered Hilbert polynomial of the zero ideal in `|σ|` variables is the binomial polynomial
`preHilbertPoly ℚ |σ| 0`. -/
theorem filteredHilbertPolynomial_bot {K σ : Type*} [Field K]
    [Fintype σ] [LinearOrder σ] :
    filteredHilbertPolynomial (⊥ : Ideal (MvPolynomial σ K)) =
      Polynomial.preHilbertPoly ℚ (Fintype.card σ) 0 := by
  apply filteredHilbertPolynomial_eq_of_eventual
  refine ⟨0, fun N _ => ?_⟩
  rw [Polynomial.preHilbertPoly_eq_choose_add_sub ℚ _ (by omega), Nat.sub_zero]
  have he : (Ideal.Quotient.mkₐ K (⊥ : Ideal (MvPolynomial σ K))).toLinearMap =
      (AlgEquiv.quotientBot K (MvPolynomial σ K)).symm.toLinearEquiv.toLinearMap := by
    ext x
    rfl
  rw [filteredCoordinateSpace, he, LinearEquiv.finrank_map_eq,
    finrank_restrictTotalDegree]
  rw [Nat.add_comm, Nat.choose_symm_add]


/-- A proper ideal of Hilbert degree `d > 1` has Hilbert dimension smaller than the number of
variables. -/
theorem hilbert_dimension_lt_ambient_of_degree_gt_one
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) (d : ℕ) (hd : 1 < d)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial) :
    (filteredHilbertPolynomial I).natDegree < Fintype.card σ := by
  obtain ⟨_, _, hle, _⟩ := filteredHilbertPolynomial_positive_multiplicity I hI
  apply lt_of_le_of_ne hle
  intro he
  have hbot := ideal_eq_bot_of_full_hilbert_dimension I hI he
  rw [hbot, filteredHilbertPolynomial_bot, Polynomial.leadingCoeff_preHilbertPoly,
    Polynomial.natDegree_preHilbertPoly] at hdegree
  have hf : (Fintype.card σ).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hfq : ((Fintype.card σ).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hf
  have heq : (1 : ℚ) = d := by
    apply (div_left_inj' hfq).mp
    simpa only [one_div] using hdegree
  have heqn : d = 1 := by exact_mod_cast heq.symm
  omega

end
end CCDN
