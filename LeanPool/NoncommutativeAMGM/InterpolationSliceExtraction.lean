/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

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
  let weights := fun j : Fin (m + 1) ↦ interpolationWeight m t j
  let nodes := fun j : Fin (m + 1) ↦ (n : ℝ) / 2 * (1 - t j)
  have hmem : ∀ r ≤ m,
      (∑ j, weights j * sliceMoment n (nodes j) r) =
        if r = m then ((-(n : ℝ) / 2) ^ m / ((2 : ℝ) ^ (m - 1) * falling n m)) else 0 := by
    intro r hr
    dsimp only [weights, nodes]
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ ↦ interpolationWeight m t j * sliceMoment n ((n : ℝ) / 2 * (1 - t j)) r)
      (m + 1)]
    exact interpolationSlice_moments hn hr t ht
  have he : interpolationSliceMap n m t = sliceQuadrature n weights nodes := by
    simp only [interpolationSliceMap, sliceQuadrature, weights, nodes]
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ ↦ interpolationWeight m t j • sliceFunctional n ((n : ℝ) / 2 * (1 - t j)))
      (m + 1)]
  rw [he]
  exact sliceQuadrature_extracts weights nodes _ hmem f hf

/-- Lemma 3.1 for the constructed general interpolation rule and the actual matrix polynomial. -/
theorem interpolationSlice_chebyshev {n m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : 0 < n) (E : Fin n → Matrix ι ι ℝ) (t : ℕ → ℝ)
    (ht : Set.InjOn t (Finset.range (m + 1))) :
    booleanMatrixImage (interpolationSliceMap n m t)
      (aeval (booleanChebyshevArgument E) (Chebyshev.T ℝ (m : ℤ))) =
        ((n : ℝ) ^ m / falling n m) • distinctProductSum n m E := by
  have h := booleanMatrixImage_chebyshev_of_extracts E (interpolationSliceMap n m t) 1
    (fun f hdegree ↦ by
      rw [interpolationSlice_extracts hn t ht f hdegree]
      congr 1
      simp only [div_eq_mul_inv, _root_.mul_inv_rev, one_mul]
      ring)
  simpa only [one_mul] using h

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
