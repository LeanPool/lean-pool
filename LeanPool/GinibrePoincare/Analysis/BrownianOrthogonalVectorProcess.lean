/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalVectorProcess.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyGaussian
public import LeanPool.GinibrePoincare.Analysis.GaussianProjectionIndependence
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The original independent scalar Brownian family is an actual Euclidean
Brownian process, so its orthogonal projections have independent whole paths. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem brownianFamily_toEuclidean_isGaussianProcess {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IsGaussianProcess (fun t ω => WithLp.toLp 2 (fun i => B i t ω)) P := by
  have := Fintype.ofFinite ι
  classical
  have hG := ginibreBrownian_family_isGaussianProcess B P hB hind
  apply hG.of_isGaussianProcess
  intro t
  let J : Finset (ι × ℝ≥0) := Finset.univ.image (fun i => (i, t))
  let L : (J → ℝ) →L[ℝ] EuclideanSpace ℝ ι :=
    { toFun := fun v => WithLp.toLp 2 (fun i => v ⟨(i, t), by simp [J]⟩)
      map_add' := by intro x y; ext i; rfl
      map_smul' := by intro c x; ext i; rfl }
  exact ⟨J, L, fun ω => rfl⟩

theorem brownianFamily_toEuclidean_covariance {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (x y : EuclideanSpace ℝ ι) :
    covariance (fun ω => inner ℝ x (WithLp.toLp 2 (fun i => B i s ω)))
      (fun ω => inner ℝ y (WithLp.toLp 2 (fun i => B i t ω))) P =
      (min s t : ℝ≥0)*inner ℝ x y := by
  classical
  have hL (i : ι) (u : ℝ≥0) : MemLp (B i u) 2 P :=
    ((hB i).isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  have hcross (i k : ι) : covariance (B i s) (B k t) P =
      if i=k then ((min s t : ℝ≥0) : ℝ) else 0 := by
    by_cases h : i=k
    · subst k; simp only []; exact (hB i).covariance_eval s t
    · rw [ite_eq_right h]
      exact ((hind.indepFun h).comp (measurable_pi_apply s) (measurable_pi_apply
          t)).covariance_eq_zero (hL i s) (hL k t)
  simp only [PiLp.inner_apply, Real.inner_apply]
  rw [covariance_fun_sum_fun_sum
    (fun i => (hL i s).const_mul (x i)) (fun i => (hL i t).const_mul (y i))]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, hcross]
  simp only [mul_ite, mul_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [eq_comm, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

theorem brownianFamily_toEuclidean_isBrownianVectorProcess {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IsBrownianVectorProcess (fun t ω => WithLp.toLp 2 (fun i => B i t ω)) P := by
  refine ⟨⟨brownianFamily_toEuclidean_isGaussianProcess B P
    (fun i => (hB i).toIsPreBrownianReal) hind,
    brownianFamily_toEuclidean_covariance B P (fun i => (hB i).toIsPreBrownianReal) hind⟩,?_,?_⟩
  · filter_upwards [ae_all_iff.mpr (fun i => (hB i).cont)] with ω hω
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hω)
  · filter_upwards [ae_all_iff.mpr (fun i => (hB i).eval_zero_ae_eq_zero)] with ω hω
    ext i
    exact hω i

end
end GinibrePoincare
