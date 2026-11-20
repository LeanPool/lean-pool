/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.QuadraticBound

/-! # Retaining the zero-slice endpoint in the positive root-grid quadrature -/

@[expose] public section
namespace NoncommutativeAMGM
open Polynomial
open scoped BigOperators

theorem falling_zero_argument {k : ℕ} (hk : k ≠ 0) : falling 0 k = 0 := by
  rw [falling_eq_descPochhammer, descPochhammer_eval_zero, ite_eq_right hk]

theorem root_square_endpoint {m : ℕ} (hm : 0 < m) (ζ : ℂ) (n : ℕ) (p : Polynomial ℝ) :
    (m : ℝ)⁻¹ * (p.eval 0) ^ 2 ≤ rootRealAverage m 1 ζ
      (fun z ↦ (p.eval ((n : ℝ) / 2 * (1 - z.re))) ^ 2) := by
  unfold rootRealAverage
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg m))
  have he := Finset.single_le_sum
    (s := Finset.range m)
    (f := fun j ↦ (p.eval ((n : ℝ) / 2 * (1 - (1 * ζ ^ j).re))) ^ 2)
    (fun j _ ↦ sq_nonneg _) (show 0 ∈ Finset.range m by simpa using hm)
  simpa using he

/-- The positive root grid retains at least its endpoint atom after harmonic decomposition. -/
theorem rootSliceFunctional_endpoint_lower {n m d : ℕ} {ζ : ℂ}
    (f : BooleanPolynomial n) (hn : 0 < n) (hm : 2 ≤ m)
    (hζ : IsPrimitiveRoot ζ m) (hf : BooleanDegreeLE f d)
    (hdn : 2 * d ≤ n) (hdm : 2 * d ≤ m + 1) (hnd : 2 * d ^ 2 ≤ n) :
    (m : ℝ)⁻¹ * sliceFunctional n 0 (f ^ 2) ≤ rootSliceFunctional n m 1 ζ (f ^ 2) := by
  classical
  obtain ⟨p, hp, he⟩ := exists_harmonic_norm_polynomials f hn hdn hf
  let A (k : ℕ) := rootRealAverage m 1 ζ (fun z ↦
    (falling ((n : ℝ) / 2 * (1 - z.re)) k *
      falling ((n : ℝ) - (n : ℝ) / 2 * (1 - z.re)) k / falling n (2 * k)) *
      ∑ S : HomogeneousIndex n k, ((p k S).eval ((n : ℝ) / 2 * (1 - z.re))) ^ 2)
  have hA (k : ℕ) (hk : k ∈ Finset.range (d + 1)) : 0 ≤ A k := by
    dsimp [A]
    simp_rw [Finset.mul_sum]
    rw [rootRealAverage_sum]
    apply Finset.sum_nonneg
    intro S _
    exact root_slice_weighted_polynomial_nonneg (p k S) n m d k hn hm
      (by have := Finset.mem_range.mp hk; omega) hζ (by simp) (Or.inl rfl) (hp k S) hdm hnd
  have hzero : sliceFunctional n 0 (f ^ 2) =
      ∑ S : HomogeneousIndex n 0, ((p 0 S).eval 0) ^ 2 := by
    rw [he 0, Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      rw [falling_zero_argument hk, zero_mul, zero_div, zero_mul]
    · simp
  have hfirst : (m : ℝ)⁻¹ * sliceFunctional n 0 (f ^ 2) ≤ A 0 := by
    rw [hzero, Finset.mul_sum]
    dsimp [A]
    simp only [falling_zero, one_mul, div_one]
    rw [rootRealAverage_sum]
    apply Finset.sum_le_sum
    intro S _
    exact root_square_endpoint (by omega) ζ n (p 0 S)
  have hsum : rootSliceFunctional n m 1 ζ (f ^ 2) = ∑ k ∈ Finset.range (d + 1), A k := by
    unfold rootSliceFunctional
    simp_rw [he]
    exact rootRealAverage_sum _ _ _ _ _
  rw [hsum]
  exact hfirst.trans (Finset.single_le_sum hA (by simp))

/-- Remove the retained endpoint atom from the positive root-grid functional. -/
noncomputable def rootEndpointLinearMap (n m : ℕ) (ζ : ℂ) : BooleanPolynomial n →ₗ[ℝ] ℝ :=
  rootSliceLinearMap n m 1 ζ - (m : ℝ)⁻¹ • sliceFunctional n 0

theorem rootEndpointLinearMap_square_nonneg {n m d : ℕ} {ζ : ℂ}
    (f : BooleanPolynomial n) (hn : 0 < n) (hm : 2 ≤ m)
    (hζ : IsPrimitiveRoot ζ m) (hf : BooleanDegreeLE f d)
    (hdn : 2 * d ≤ n) (hdm : 2 * d ≤ m + 1) (hnd : 2 * d ^ 2 ≤ n) :
    0 ≤ rootEndpointLinearMap n m ζ (f ^ 2) := by
  exact sub_nonneg.mpr (rootSliceFunctional_endpoint_lower f hn hm hζ hf hdn hdm hnd)

end NoncommutativeAMGM
