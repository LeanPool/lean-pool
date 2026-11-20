/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.ChebyshevWeights
public import LeanPool.NoncommutativeAMGM.OneSlice
public import LeanPool.NoncommutativeAMGM.SineNodeBounds

/-! # Pointwise slice positivity under the sine-node condition -/

@[expose] public section
namespace NoncommutativeAMGM
open scoped BigOperators

theorem sine_node_slice_square_nonneg {n m d j : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hj : j ≤ m) (hdn : 2 * d ≤ n)
    (hsin : (d : ℝ) - 1 ≤ (n : ℝ) * Real.sin (Real.pi / (2 * (m : ℝ))) ^ 2)
    (f : BooleanPolynomial n) (hf : BooleanDegreeLE f d) :
    0 ≤ sliceFunctional n (idealSliceNode n m j) (f ^ 2) := by
  by_cases hj0 : j = 0
  · subst j
    rw [idealSliceNode_zero]
    exact sliceFunctional_zero_square_nonneg f
  · by_cases hjm : j = m
    · subst j
      rw [idealSliceNode_last hm n]
      exact sliceFunctional_full_square_nonneg f
    · have hs := idealSliceNode_interior hm (by omega : 0 < j) (by omega : j < m) hsin
      exact sliceFunctional_square_nonneg _ f hn hdn hf hs.1 hs.2

theorem cosineParityQuadrature_nonneg {m s : ℕ} (F : ℝ → ℝ)
    (hF : ∀ j, j ≤ m → 0 ≤ F (chebyshevNode m j)) : 0 ≤ cosineParityQuadrature m s F := by
  unfold cosineParityQuadrature
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro j hj
  apply mul_nonneg (cosineEndpointFactor_nonneg m j)
  split_ifs
  · exact hF j (by have := Finset.mem_range.mp hj; omega)
  · exact le_rfl

/-- Both actual root-grid slice functionals are positive on degree-`d` squares
under Theorem 3.5's condition. -/
theorem cosineRootSlice_square_nonneg {n m d : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hdn : 2 * d ≤ n)
    (hsin : (d : ℝ) - 1 ≤ (n : ℝ) * Real.sin (Real.pi / (2 * (m : ℝ))) ^ 2)
    (f : BooleanPolynomial n) (hf : BooleanDegreeLE f d) :
    0 ≤ rootSliceLinearMap n m 1 (cosineRoot m) (f ^ 2) ∧
      0 ≤ rootSliceLinearMap n m (cosineHalfRoot m) (cosineRoot m) (f ^ 2) := by
  let F (t : ℝ) := sliceFunctional n ((n : ℝ) / 2 * (1 - t)) (f ^ 2)
  have hF (j : ℕ) (hj : j ≤ m) : 0 ≤ F (chebyshevNode m j) :=
    sine_node_slice_square_nonneg hm hn hj hdn hsin f hf
  change 0 ≤ rootRealAverage m 1 (cosineRoot m) (fun z ↦ F z.re) ∧
    0 ≤ rootRealAverage m (cosineHalfRoot m) (cosineRoot m) (fun z ↦ F z.re)
  rw [rootRealAverage_cosine_even hm F, rootRealAverage_cosine_odd hm F]
  exact ⟨cosineParityQuadrature_nonneg F hF, cosineParityQuadrature_nonneg F hF⟩

end NoncommutativeAMGM
