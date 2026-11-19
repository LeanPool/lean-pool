/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryBrownianGrid.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGirsanovFiniteProductLaw
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryPolygonalNoise
/-!
# Alternative Bakry Emery Brownian grid

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryBrownianGrid_coordinates_hasLaw`,
`bakryEmeryPolygonalNoise_sampled_endpoint`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace GinibrePoincare
noncomputable section

/-- The actual flattening of a finite Gaussian array preserves its product law. -/
theorem bakryEmeryGaussianArray_flatten (I J : Type*) [Fintype I] [Fintype J]
    (v : ℝ≥0) :
    MeasurePreserving (fun x : I → J → ℝ => fun p : I × J => x p.1 p.2)
      (Measure.pi (fun _ : I => Measure.pi (fun _ : J => gaussianReal 0 v)))
      (Measure.pi (fun _ : I × J => gaussianReal 0 v)) := by
  refine ⟨by fun_prop, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have heq : (fun x : I → J → ℝ => fun p : I × J => x p.1 p.2) ⁻¹' univ.pi s =
      univ.pi (fun i => univ.pi (fun j => s (i, j))) := by
    ext x
    simp only [mem_preimage, mem_univ_pi]
    constructor
    · intro h i j
      exact h (i, j)
    · intro h p
      exact h p.1 p.2
  rw [heq, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun p : I × J => gaussianReal 0 v (s p))).symm

/-- Actual independent scalar Brownian increments on a uniform grid have
the flattened finite Gaussian law used by the polygonal construction. -/
theorem bakryEmeryBrownianGrid_increments_hasLaw
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (h : ℝ≥0) (m : ℕ) :
    HasLaw (fun ω (p : Fin m × ι) => B p.2 ((p.1.val+1 : ℕ)*h) ω-
        B p.2 ((p.1.val : ℕ)*h) ω)
      (Measure.pi (fun _ : Fin m × ι => gaussianReal 0 h)) P := by
  have hτ : Monotone (fun k : ℕ => (k : ℝ≥0)*h) := by
    intro k l hkl
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) h.2
  have hstep (k : ℕ) : ((k+1 : ℕ) : ℝ≥0)*h - (k : ℝ≥0)*h = h := by
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_tsub_cancel_left]
  have hl := brownianFamilyGridInnovation_product_law B P hB hind
    (fun k => (k : ℝ≥0)*h) hτ m
  simp_rw [hstep] at hl
  exact HasLaw.comp (bakryEmeryGaussianArray_flatten (Fin m) ι h).hasLaw hl

theorem bakryEmeryGaussian_standardize (h : ℝ≥0) (hh : h ≠ 0) :
    MeasurePreserving (fun r : ℝ => r/Real.sqrt (h : ℝ)) (gaussianReal 0 h)
      (gaussianReal 0 1) := by
  refine ⟨by fun_prop, ?_⟩
  rw [gaussianReal_map_div_const]
  have hs : NNReal.mk ((Real.sqrt (h : ℝ))^2) (sq_nonneg _) = h := by
    apply Subtype.ext
    exact Real.sq_sqrt h.2
  rw [hs, div_self hh, zero_div]

/-- Standardized original Brownian increments are the actual variance-one
coordinates of the finite Gaussian polygonal-noise approximation. -/
theorem bakryEmeryBrownianGrid_coordinates_hasLaw
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (h : ℝ≥0) (hh : h ≠ 0) (m : ℕ) :
    HasLaw (fun ω (p : Fin m × ι) =>
      (B p.2 ((p.1.val+1 : ℕ)*h) ω-B p.2 ((p.1.val : ℕ)*h) ω)/Real.sqrt (h : ℝ))
      (Measure.pi (fun _ : Fin m × ι => gaussianReal 0 1)) P := by
  exact HasLaw.comp (measurePreserving_pi
    (fun _ : Fin m × ι => gaussianReal 0 h)
    (fun _ : Fin m × ι => gaussianReal 0 1)
    (fun _ => bakryEmeryGaussian_standardize h hh)).hasLaw
      (bakryEmeryBrownianGrid_increments_hasLaw B P hB hind h m)

/-- Decoding the sampled increments gives the original path at the final grid
point, by actual finite telescoping; no interpolation identity is assumed. -/
theorem bakryEmeryPolygonalNoise_sampled_endpoint
    (ι : Type*) [Finite ι] (m : ℕ) (h : ℝ) (hh : 0 < h)
    (u : ℕ → EuclideanSpace ℝ ι) :
    bakryEmeryPolygonalNoise m h
      (fun p : Fin m × ι => (u (p.1.val+1) p.2-u p.1.val p.2)/Real.sqrt h)
      ((m : ℝ)*h) = u m-u 0 := by
  classical
  have := Fintype.ofFinite ι
  have hr (j : Fin m) : bakryEmeryPolygonalRamp h j.val ((m : ℝ)*h) = Real.sqrt h := by
    apply bakryEmeryPolygonalRamp_after h hh
    have hj : ((j.val+1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast j.isLt
    exact mul_le_mul_of_nonneg_right hj hh.le
  have hs : Real.sqrt h ≠ 0 := Real.sqrt_ne_zero'.mpr hh
  apply PiLp.ext
  intro i
  change (∑ j : Fin m, bakryEmeryPolygonalRamp h j.val ((m : ℝ)*h) *
      ((u (j.val+1) i-u j.val i)/Real.sqrt h)) = u m i-u 0 i
  have hf (a : ℝ) : Real.sqrt h*(a/Real.sqrt h)=a := by field_simp
  simp_rw [hr, hf]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => u (j+1) i-u j i)]
  exact Finset.sum_range_sub (fun j => u j i) m

end
end GinibrePoincare
