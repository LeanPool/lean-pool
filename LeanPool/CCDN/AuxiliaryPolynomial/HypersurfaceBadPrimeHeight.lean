/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Analysis.PrimeCutoff
public import LeanPool.CCDN.AuxiliaryPolynomial.DegreeBound
public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimes
public import LeanPool.CCDN.Plane.IntegerPlaneLogHeight
import LeanPool.CCDN.Algebra.IntegerPolynomialAvoidance
import LeanPool.CCDN.AuxiliaryPolynomial.BadPrimeCharge
import LeanPool.CCDN.AuxiliaryPolynomial.UniversalPlaneBadReduction
import LeanPool.CCDN.Determinant.ClosedFormIntegerMinor
import LeanPool.CCDN.Determinant.ClosedFormMinorCharge

/-!
The geometric bad-prime charge in arbitrary dimension is controlled by
coefficient height, via an explicit integer witness with bounded height.

A nonzero bad-prime witness obtained by evaluating the universal
plane polynomial on a bounded integer grid.

Explicit height estimates for the evaluated universal bad-prime witness.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma universalPlaneBadWitness_eval {σ : Type*}
    (f : MvPolynomial σ ℤ)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
    (v : PlaneParameters σ → ℤ) :
    eval v (universalPlaneBadWitness f rows cols) =
      ((universalPlaneSection f v).coeff f.totalDegree).coeff 0 *
        ((closedFormCoefficientMatrix f.totalDegree (universalPlaneSection f v)).submatrix
          rows cols).det := by
  rw [universalPlaneBadWitness, map_mul, closedForm_minor_map]
  congr 1
  exact (bivariateMap_coeff (eval v) (universalPlanePolynomial f) f.totalDegree 0).symm

/-- The evaluated witness is a leading coefficient times an integer
minor; both are controlled by the height of the same plane section. -/
private theorem universalPlaneBadWitness_eval_log_bound {σ : Type*} [Finite σ]
    (f : MvPolynomial σ ℤ) (hd : 1 ≤ f.totalDegree)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
    (v : PlaneParameters σ → ℤ) (S : ℝ) (hS : 1 ≤ S)
    (hf : BivariateCoefficientBound (universalPlaneSection f v) S)
    (hw : eval v (universalPlaneBadWitness f rows cols) ≠ 0) :
    Real.log |(eval v (universalPlaneBadWitness f rows cols) : ℝ)| ≤
      Real.log S + (27 * (f.totalDegree : ℝ) ^ 4) *
        (1 + Real.log S / (f.totalDegree : ℝ) ^ 2) := by
  classical
  let := Fintype.ofFinite σ
  let g := universalPlaneSection f v
  let c := (g.coeff f.totalDegree).coeff 0
  let D := ((closedFormCoefficientMatrix f.totalDegree g).submatrix rows cols).det
  have he : eval v (universalPlaneBadWitness f rows cols) = c * D :=
    universalPlaneBadWitness_eval f rows cols v
  have hc : c ≠ 0 := fun h => hw (by rw [he, h, zero_mul])
  have hD : D ≠ 0 := fun h => hw (by rw [he, h, mul_zero])
  have ht : bivariateTotalDegree g ≤ f.totalDegree :=
    universalPlanePolynomial_specialization_totalDegree f (eval v)
  have hb := closedForm_minor_log_height f.totalDegree (2 * f.totalDegree ^ 2 - 1)
    hd (Nat.sub_le _ _) g S hS hf
    ((bivariate_natDegree_le_totalDegree g).trans ht)
    (fun i => (bivariate_coefficient_natDegree_le_totalDegree g i).trans ht) rows cols hD
  have hl := Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hc)) (hf f.totalDegree 0)
  rw [he, Int.cast_mul, abs_mul, Real.log_mul
    (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hc)) (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hD))]
  exact add_le_add hl hb

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private lemma bad_prime_dvd_universalPlaneBadWitness_eval {σ : Type*} [Finite σ]
    (f : MvPolynomial σ ℤ) (hpos : 0 < f.totalDegree)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
    (v : PlaneParameters σ → ℤ) (p : ℕ)
    (hp : f.totalDegree < p) (hbad : HypersurfaceBadReduction f p) :
    (p : ℤ) ∣ eval v (universalPlaneBadWitness f rows cols) := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨hpprime, hbad⟩ := hbad
  let : Fact p.Prime := ⟨hpprime⟩
  rw [eval_eq']
  apply Finset.dvd_sum
  intro e _
  exact dvd_mul_of_dvd_left
    (bad_prime_dvd_universalPlaneBadWitness_coeff f hpos rows cols p hp hbad e) _

/-- The universal plane bad-prime witness of an absolutely irreducible integer polynomial
takes a nonzero value at some integer parameter in the box `[0, 2d³]`, and every prime above
`d` with bad geometric reduction divides that value. -/
private theorem exists_bounded_integer_plane_witness
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Finite σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) :
    ∃ (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
      (v : PlaneParameters (Option σ) → ℤ),
      (∀ i, 0 ≤ v i ∧ v i ≤ (2 * f.totalDegree ^ 3 : ℕ)) ∧
      eval v (universalPlaneBadWitness f rows cols) ≠ 0 ∧
      ∀ p : ℕ, f.totalDegree < p → HypersurfaceBadReduction f p →
        (p : ℤ) ∣ eval v (universalPlaneBadWitness f rows cols) := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨rows, cols, hw, hd⟩ := exists_integer_universalPlane_badWitness f hf hpos
  obtain ⟨v, hv, he⟩ := exists_integer_grid_eval_ne_zero _ hw _ hd
  exact ⟨rows, cols, v, hv, he,
    fun p hp hbad => bad_prime_dvd_universalPlaneBadWitness_eval f hpos rows cols v p hp hbad⟩

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- An effective positive integer detecting every bad prime above the degree. -/
theorem exists_hypersurface_bad_prime_height_witness
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H) :
    ∃ D : ℤ, 0 < D ∧
      Real.log D ≤ (27 * (f.totalDegree : ℝ) ^ 4) *
        (hypersurfaceHeightConstant (Fintype.card (Option σ)) *
          (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) ∧
      ∀ p : ℕ, f.totalDegree < p → HypersurfaceBadReduction f p → (p : ℤ) ∣ D := by
  obtain ⟨rows, cols, v, hv, hw, hdiv⟩ := exists_bounded_integer_plane_witness f hf hpos
  let S := integerPlaneHeight (Fintype.card (Option σ)) f.totalDegree H
    (2 * (f.totalDegree : ℝ) ^ 3)
  have hd : 1 ≤ f.totalDegree := hpos
  have hdR : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hd
  have hA : 1 ≤ 2 * (f.totalDegree : ℝ) ^ 3 := by nlinarith [one_le_pow₀ hdR (n := 3)]
  have hv' (i : PlaneParameters (Option σ)) : |(v i : ℝ)| ≤ 2 * (f.totalDegree : ℝ) ^ 3 := by
    rw [abs_of_nonneg (by exact_mod_cast (hv i).1)]
    exact_mod_cast (hv i).2
  have hS : 1 ≤ S := integerPlaneHeight_one_le _ _ hd H hH
  have hcoeffS : BivariateCoefficientBound (universalPlaneSection f v) S :=
    integer_plane_section_coefficient_bound f H _ (by linarith) hA hcoeff v hv'
  refine ⟨|eval v (universalPlaneBadWitness f rows cols)|, abs_pos.mpr hw, ?_, ?_⟩
  · rw [Int.cast_abs]
    exact (universalPlaneBadWitness_eval_log_bound f hd rows cols v S hS hcoeffS hw).trans
      (integerPlaneHeight_scaled_log_le _ _ hd H hH)
  · intro p hp hbad
    exact (dvd_abs _ _).mpr (hdiv p hp hbad)

/-- The logarithmic charge bound for any finite family of bad primes.
This includes degree-dropping primes as well as geometric reducibility. -/
theorem hypersurface_bad_prime_charge
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H)
    (P : Finset ℕ) (hP : ∀ p ∈ P, HypersurfaceBadReduction f p)
    (hcut : ∀ p ∈ P, stepanovThreshold f.totalDegree < p) :
    (∑ p ∈ P, Real.log p / p) ≤
      Real.log (hypersurfaceHeightConstant (Fintype.card (Option σ)) *
        (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + 2 * mertensError + 1 := by
  obtain ⟨D, hD, hheight, hdiv⟩ :=
    exists_hypersurface_bad_prime_height_witness f hf hpos H hH hcoeff
  have hd1 : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hpos
  apply bad_prime_charge_of_height P hD (fun p hp => (hP p hp).choose) _ _ _ _ hheight
  · intro p hp
    apply hdiv p _ (hP p hp)
    have h1 := Nat.le_mul_self f.totalDegree
    have h2 := Nat.le_mul_self (f.totalDegree * f.totalDegree)
    have h3 : 27 * f.totalDegree ^ 4 < p := hcut p hp
    nlinarith [h3]
  · nlinarith [one_le_pow₀ hd1 (n := 4)]
  · exact one_le_mul_of_one_le_of_one_le (hypersurfaceHeightConstant_one_le _)
      (le_add_of_nonneg_right (div_nonneg (Real.log_nonneg hH) (sq_nonneg _)))
  · intro p hp
    exact_mod_cast hcut p hp

/-- The exponential bad-prime factor has the coefficient-height dependence
required in CCDN Corollary 3.2.3. -/
private theorem hypersurface_bad_prime_factor
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H)
    (P : Finset ℕ) (hP : ∀ p ∈ P, HypersurfaceBadReduction f p)
    (hcut : ∀ p ∈ P, stepanovThreshold f.totalDegree < p) :
    primeSetFactor P ≤
      (Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (Fintype.card (Option σ))) *
        (1 + Real.log H / (f.totalDegree : ℝ) ^ 2) := by
  have h := Real.exp_le_exp.mpr (hypersurface_bad_prime_charge f hf hpos H hH hcoeff P hP hcut)
  have hc : 0 < hypersurfaceHeightConstant (Fintype.card (Option σ)) :=
    zero_lt_one.trans_le (hypersurfaceHeightConstant_one_le _)
  have hh : 0 < 1 + Real.log H / (f.totalDegree : ℝ) ^ 2 := by
    have := div_nonneg (Real.log_nonneg hH) (sq_nonneg (f.totalDegree : ℝ))
    linarith
  calc
    _ ≤ Real.exp (Real.log (hypersurfaceHeightConstant (Fintype.card (Option σ)) *
        (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + 2 * mertensError + 1) := h
    _ = _ := by
      rw [add_assoc, Real.exp_add, Real.exp_log (mul_pos hc hh)]
      ring

/-- The maximum formulation of CCDN Corollary 3.2.3, with an explicit
constant depending only on the number of variables. -/
theorem hypersurface_bad_prime_factor_max
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H)
    (P : Finset ℕ) (hP : ∀ p ∈ P, HypersurfaceBadReduction f p)
    (hcut : ∀ p ∈ P, stepanovThreshold f.totalDegree < p) :
    primeSetFactor P ≤
      (2 * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (Fintype.card (Option σ))) *
        max (Real.log H / (f.totalDegree : ℝ) ^ 2) 1 := by
  have h := hypersurface_bad_prime_factor f hf hpos H hH hcoeff P hP hcut
  have hc : 0 ≤ Real.exp (2 * mertensError + 1) *
      hypersurfaceHeightConstant (Fintype.card (Option σ)) :=
    mul_nonneg (Real.exp_pos _).le (le_trans zero_le_one (hypersurfaceHeightConstant_one_le _))
  have hm : 1 + Real.log H / (f.totalDegree : ℝ) ^ 2 ≤
      2 * max (Real.log H / (f.totalDegree : ℝ) ^ 2) 1 := by
    have h1 := le_max_left (Real.log H / (f.totalDegree : ℝ) ^ 2) 1
    have h2 := le_max_right (Real.log H / (f.totalDegree : ℝ) ^ 2) 1
    linarith
  apply h.trans
  convert mul_le_mul_of_nonneg_left hm hc using 1
  ring

end
end CCDN
