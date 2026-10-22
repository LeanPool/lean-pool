/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Analysis.PrimeCutoff
public import LeanPool.CCDN.AuxiliaryPolynomial.ConstantLeadingBadReduction
public import LeanPool.CCDN.Plane.FiniteFieldConstants
import LeanPool.CCDN.AuxiliaryPolynomial.BadPrimeCharge
import LeanPool.CCDN.ForMathlib.Log
import LeanPool.CCDN.Plane.ShearHeight

/-! The geometric bad-prime charge for arbitrary integer plane equations.
The proof combines bounded integral normalization, coefficient growth and an
integer minor witness; reducibility is tested over the residue field's
algebraic closure. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Real

private lemma normalized_shear_height_one_le (d : ℕ) (H : ℝ) (hH : 1 ≤ H) :
    1 ≤ ((d : ℝ) + 1) ^ (d + 2) * H := by
  have hp : 1 ≤ ((d : ℝ) + 1) ^ (d + 2) :=
    one_le_pow₀ (by have h : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
  nlinarith

/-- The normalization cost contributes an absolute constant at the d² scale. -/
private lemma normalized_shear_scaled_log_height (d : ℕ) (hd : 1 ≤ d)
    (H : ℝ) (hH : 1 ≤ H) :
    1 + 2 * Real.log (((d : ℝ) + 1) ^ (d + 2) * H) / (d : ℝ) ^ 2 ≤
      7 * (1 + Real.log H / (d : ℝ) ^ 2) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hlog := Real.log_nonneg hH
  have hdlog := Real.log_add_one_le_self (Nat.cast_nonneg (α := ℝ) d)
  have hcost : ((d : ℝ) + 2) * Real.log ((d : ℝ) + 1) ≤ 3 * (d : ℝ) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hdlog (show 0 ≤ (d : ℝ) + 2 by positivity)
    nlinarith
  rw [Real.log_mul (by positivity : ((d : ℝ) + 1) ^ (d + 2) ≠ 0) (by linarith : H ≠ 0),
    Real.log_pow]
  push_cast
  apply (le_of_mul_le_mul_right ?_ (show 0 < (d : ℝ) ^ 2 by positivity))
  field_simp
  nlinarith

/-- Every absolutely irreducible integer plane equation has a coefficient-
controlled positive integer detecting all geometric bad primes above d. -/
theorem exists_plane_bad_prime_witness
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (d : ℕ) (hd : 1 ≤ d) (f : ℤ[X][X]) (hdeg : bivariateTotalDegree f = d)
    (hir : Irreducible (bivariateMap (Int.castRingHom F) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : BivariateCoefficientBound f H) :
    ∃ D : ℤ, 0 < D ∧
      Real.log D ≤ (189 * (d : ℝ) ^ 4) * (1 + Real.log H / (d : ℝ) ^ 2) ∧
      ∀ p : ℕ, d < p → BivariateBadReduction f d p → (p : ℤ) ∣ D := by
  have hf : f ≠ 0 := by
    intro hz
    apply hir.ne_zero
    rw [hz, map_zero]
  obtain ⟨a, ha, hn, ht⟩ := exists_bounded_full_outer_shear f hf
  rw [hdeg] at ha hn ht
  let g := bivariateShear ℤ (a : ℤ) f
  let H' := ((d : ℝ) + 1) ^ (d + 2) * H
  have hH' : 1 ≤ H' := normalized_shear_height_one_le d H hH
  have hgcoeff : BivariateCoefficientBound g H' :=
    bivariateShear_bounded_coefficient_bound a d ha f hdeg.le H (by linarith) hcoeff
  have hgir : Irreducible (bivariateMap (Int.castRingHom F) g) := by
    dsimp only [g]
    rw [bivariateShear_map, bivariateShear_irreducible_iff]
    exact hir
  obtain ⟨D, hD, hheight, hdiv⟩ :=
    exists_full_outer_bad_prime_witness d hd g hn ht.le hgir H' hH' hgcoeff
  refine ⟨D, hD, ?_, ?_⟩
  · have hs := normalized_shear_scaled_log_height d hd H hH
    change 1 + 2 * Real.log H' / (d : ℝ) ^ 2 ≤ _ at hs
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 27 * (d : ℝ) ^ 4 by positivity)
    nlinarith
  · intro p hp hbad
    apply hdiv p hp
    exact (bivariateBadReduction_shear_iff (a : ℤ) f d p).mpr hbad

/-- Geometric bad primes above 27*d^4 have logarithmic charge controlled by
log(1+log(H)/d²) plus an absolute constant. -/
theorem plane_geometric_bad_prime_charge
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (d : ℕ) (hd : 1 ≤ d) (f : ℤ[X][X]) (hdeg : bivariateTotalDegree f = d)
    (hir : Irreducible (bivariateMap (Int.castRingHom F) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : BivariateCoefficientBound f H)
    (P : Finset ℕ) (hbad : ∀ p ∈ P, BivariateBadReduction f d p)
    (hlo : ∀ p ∈ P, stepanovThreshold (d : ℝ) < (p : ℝ)) :
    (∑ p ∈ P, Real.log p / p) ≤
      Real.log (1 + Real.log H / (d : ℝ) ^ 2) + Real.log 7 + 2 * mertensError + 1 := by
  obtain ⟨D, hD, hheight, hdiv⟩ := exists_plane_bad_prime_witness d hd f hdeg hir H hH hcoeff
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx : 1 ≤ 1 + Real.log H / (d : ℝ) ^ 2 :=
    le_add_of_nonneg_right (div_nonneg (Real.log_nonneg hH) (sq_nonneg _))
  have hcut : (d : ℝ) ≤ 27 * (d : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((d : ℝ) ^ 2 - 1)]
  have h := bad_prime_charge_of_height (D := D) (L := 27 * (d : ℝ) ^ 4)
    (H := 7 * (1 + Real.log H / (d : ℝ) ^ 2)) P hD
    (fun p hp => (hbad p hp).choose)
    (fun p hp => hdiv p (by exact_mod_cast hcut.trans_lt (hlo p hp)) (hbad p hp))
    (by linarith) (by linarith) hlo (by nlinarith [hheight])
  rw [Real.log_mul (by norm_num : (7 : ℝ) ≠ 0)
    (by linarith : 1 + Real.log H / (d : ℝ) ^ 2 ≠ 0)] at h
  linarith

end
end CCDN
