/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.InterpolationWeights
public import LeanPool.NoncommutativeAMGM.ChebyshevCoefficient
public import LeanPool.NoncommutativeAMGM.ProductScaling

/-! # General interpolation weights acting on the actual Boolean slice maps -/

@[expose] public section

namespace NoncommutativeAMGM
open Polynomial Matrix
open scoped BigOperators

/-- The signed slice quadrature at arbitrary distinct cosine-coordinate nodes. -/
noncomputable def interpolationSliceMap (n m : ℕ) (t : ℕ → ℝ) :
    BooleanPolynomial n →ₗ[ℝ] ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    interpolationWeight m t j • sliceFunctional n ((n : ℝ) / 2 * (1 - t j))

/-- The actual slice moments of the general interpolation rule, with full normalization. -/
theorem interpolationSlice_moments {n m r : ℕ} (hn : 0 < n) (hr : r ≤ m)
    (t : ℕ → ℝ) (ht : Set.InjOn t (Finset.range (m + 1))) :
    (∑ j ∈ Finset.range (m + 1), interpolationWeight m t j *
      sliceMoment n ((n : ℝ) / 2 * (1 - t j)) r) =
      if r = m then ((-(n : ℝ) / 2) ^ m / ((2 : ℝ) ^ (m - 1) * falling n m)) else 0 := by
  let p := (descPochhammer ℝ r).comp (sliceCoordinatePolynomial n)
  have hp : p.natDegree = r := falling_sliceCoordinate_natDegree n r hn
  have he := interpolationWeight_extracts t ht p (hp.le.trans hr)
  have hev (j : ℕ) : p.eval (t j) = falling ((n : ℝ) / 2 * (1 - t j)) r := by
    dsimp only [p]
    rw [eval_comp, sliceCoordinatePolynomial_eval, ← falling_eq_descPochhammer]
  simp_rw [hev] at he
  have hsum : (∑ j ∈ Finset.range (m + 1), interpolationWeight m t j *
      sliceMoment n ((n : ℝ) / 2 * (1 - t j)) r) =
      (∑ j ∈ Finset.range (m + 1), interpolationWeight m t j *
        falling ((n : ℝ) / 2 * (1 - t j)) r) / falling n r := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [sliceMoment]
    ring
  rw [hsum, he]
  by_cases hrm : r = m
  · rw [ite_eq_left hrm]
    have hc : p.coeff m = (-(n : ℝ) / 2) ^ m := by
      dsimp only [p]
      rw [hrm, falling_sliceCoordinate_coeff n m hn]
    rw [hc, hrm]
    ring
  · have hc : p.coeff m = 0 := coeff_eq_zero_of_natDegree_lt (by rw [hp]; omega)
    rw [hc, zero_div, zero_div, ite_eq_right hrm]

/-- No moment assumptions remain: the constructed interpolation map extracts the top layer. -/
theorem interpolationSlice_extracts {n m : ℕ} (hn : 0 < n) (t : ℕ → ℝ)
    (ht : Set.InjOn t (Finset.range (m + 1))) (f : BooleanPolynomial n)
    (hf : BooleanDegreeLE f m) :
    interpolationSliceMap n m t f =
      ((-(n : ℝ) / 2) ^ m / ((2 : ℝ) ^ (m - 1) * falling n m)) *
        layerCoefficientSum n m f := by
  classical
  have hmono (S : Finset (Fin n)) (a : ℝ) (hS : S.card ≤ m) :
      interpolationSliceMap n m t (booleanMonomial S a) =
        ((-(n : ℝ) / 2) ^ m / ((2 : ℝ) ^ (m - 1) * falling n m)) *
          layerCoefficientSum n m (booleanMonomial S a) := by
    simp only [interpolationSliceMap, LinearMap.sum_apply, LinearMap.smul_apply,
      sliceFunctional_monomial, smul_eq_mul]
    have he : (∑ j ∈ Finset.range (m + 1), interpolationWeight m t j *
        (a * sliceMoment n ((n : ℝ) / 2 * (1 - t j)) S.card)) =
        a * (∑ j ∈ Finset.range (m + 1), interpolationWeight m t j *
          sliceMoment n ((n : ℝ) / 2 * (1 - t j)) S.card) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he, interpolationSlice_moments hn hS t ht, layerCoefficientSum_monomial]
    split_ifs <;> ring
  have he : f = ∑ S ∈ f.coeff.support, booleanMonomial S.toFinset (f.coeff S) :=
    (MonoidAlgebra.sum_coeff_single f).symm
  conv_lhs => rw [he]
  conv_rhs => rw [he]
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  exact hmono S (f.coeff S) (hf S (Finsupp.mem_support_iff.mp hS))

/-- Lemma 3.1 for the constructed general interpolation rule and the actual matrix polynomial. -/
theorem interpolationSlice_chebyshev {n m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : 0 < n) (E : Fin n → Matrix ι ι ℝ) (t : ℕ → ℝ)
    (ht : Set.InjOn t (Finset.range (m + 1))) :
    booleanMatrixImage (interpolationSliceMap n m t)
      (aeval (booleanChebyshevArgument E) (Chebyshev.T ℝ (m : ℤ))) =
        ((n : ℝ) ^ m / falling n m) • distinctProductSum n m E := by
  apply Matrix.ext
  intro i j
  have hdeg : BooleanDegreeLE
      ((aeval (booleanChebyshevArgument E) (Chebyshev.T ℝ (m : ℤ))) i j) m := by
    simpa only [Chebyshev.natDegree_T, Int.natAbs_natCast] using
      booleanMatrix_aeval_degree (booleanChebyshevArgument E) (booleanChebyshevArgument_degree E)
        (Chebyshev.T ℝ (m : ℤ)) i j
  have he := interpolationSlice_extracts hn t ht _ hdeg
  have htop := congrArg (fun M : Matrix ι ι ℝ ↦ M i j) (chebyshev_matrix_top E m)
  change interpolationSliceMap n m t
    ((aeval (booleanChebyshevArgument E) (Chebyshev.T ℝ (m : ℤ))) i j) = _
  rw [he]
  change layerCoefficientSum n m
    ((aeval (booleanChebyshevArgument E) (Chebyshev.T ℝ (m : ℤ))) i j) =
      ((2 : ℝ) ^ (m - 1) * (-2 : ℝ) ^ m) * distinctProductSum n m E i j at htop
  rw [htop]
  change _ = ((n : ℝ) ^ m / falling n m) * distinctProductSum n m E i j
  have hp : (-(n : ℝ) / 2) ^ m * (-2 : ℝ) ^ m = (n : ℝ) ^ m := by
    rw [← mul_pow]
    congr 1
    ring
  have htwo : (2 : ℝ) ^ (m - 1) ≠ 0 := by positivity
  have hc : ((-(n : ℝ) / 2) ^ m / ((2 : ℝ) ^ (m - 1) * falling n m)) *
      ((2 : ℝ) ^ (m - 1) * (-2 : ℝ) ^ m) = (n : ℝ) ^ m / falling n m := by
    calc
      _ = ((-(n : ℝ) / 2) ^ m * (-2 : ℝ) ^ m) / falling n m := by field_simp
      _ = _ := by rw [hp]
  calc
    _ = (((-(n : ℝ) / 2) ^ m / ((2 : ℝ) ^ (m - 1) * falling n m)) *
      ((2 : ℝ) ^ (m - 1) * (-2 : ℝ) ^ m)) * distinctProductSum n m E i j := by ring
    _ = _ := by rw [hc]

/-- The normalized interpolation map evaluates to the actual without-replacement mean. -/
theorem interpolationSlice_withoutReplacementMean {n m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hn : 0 < n) (hmn : m ≤ n)
    (A : Fin n → Matrix ι ι ℝ) (t : ℕ → ℝ)
    (ht : Set.InjOn t (Finset.range (m + 1))) :
    booleanMatrixImage (interpolationSliceMap n m t)
      (aeval (booleanChebyshevArgument (fun i ↦ (n : ℝ)⁻¹ • A i))
        (Chebyshev.T ℝ (m : ℤ))) = withoutReplacementMean n m A := by
  rw [interpolationSlice_chebyshev hn _ t ht, normalized_distinctProductSum hn hmn]

end NoncommutativeAMGM
