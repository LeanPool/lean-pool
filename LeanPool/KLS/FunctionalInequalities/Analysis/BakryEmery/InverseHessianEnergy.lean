/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.MongeAmpere

/-!
# The inverse-Hessian energy of a gradient

For a potential `U` with pointwise positive definite Hessian `H = hessianOperator U x` and a test
`f`, the energy is
`⟪∇f, H⁻¹ ∇f⟫` with the ring inverse `H⁻¹`. Young's inequality `2⟪v, w⟫ ≤ ⟪v, H⁻¹ v⟫ + D²U(w, w)`
(`hessian_inverse_young`, no uniform curvature constant); `⟪∇f x, v⟫ = Df(x) v` (Mathlib
`inner_gradient_left`); the energy
in any orthonormal basis is `Σ_ij (H⁻¹)_ij ∂_i f ∂_j f`
(`inverse_hessian_energy_eq_coordinate_sum`); for smooth `U` and `C¹`
`f` it is continuous (`continuous_inverse_hessian_gradient_energy`), and it is nonnegative
(`inverse_hessian_gradient_energy_nonneg`) in every dimension, zero included. Used by the scalar
Brascamp–Lieb inequality
(`KLS/LogConcave/BrascampLieb.lean`); the smooth inverse entries come from `MongeAmpere.lean`, so
these facts sit above it
rather than in `Analysis/BakryEmery/Hessian/Operator.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set InnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace


namespace FunctionalInequalities.Analysis.BakryEmery

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
/-- Young's inequality for the actual Hessian operator and its ring inverse.
The proof uses positivity on `w - H⁻¹ v`; no uniform curvature constant is used. -/
theorem hessian_inverse_young
    {U : E → ℝ} (hU : ContDiff ℝ 2 U) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ U x v v)
    (v w : E) :
    2 * ⟪v, w⟫ ≤
      ⟪v, Ring.inverse (hessianOperator U x) v⟫ +
        bilinearIteratedFDerivTwo ℝ U x w w := by
  have hunit := hessianOperator_isUnit_of_posDef hU x hPD
  have hcancel :
      hessianOperator U x (Ring.inverse (hessianOperator U x) v) = v := by
    have h := congrArg (fun L : E →L[ℝ] E => L v)
      (Ring.mul_inverse_cancel (hessianOperator U x) hunit)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  have hcross :
      ⟪hessianOperator U x w, Ring.inverse (hessianOperator U x) v⟫ =
        ⟪v, w⟫ := by
    calc
      ⟪hessianOperator U x w, Ring.inverse (hessianOperator U x) v⟫ =
          ⟪w, hessianOperator U x (Ring.inverse (hessianOperator U x) v)⟫ :=
        (hessianOperator_isSelfAdjoint hU x).isSymmetric w
          (Ring.inverse (hessianOperator U x) v)
      _ = ⟪v, w⟫ := by rw [hcancel, real_inner_comm w v]
  have hnonneg :
      0 ≤ ⟪hessianOperator U x (w - Ring.inverse (hessianOperator U x) v),
        w - Ring.inverse (hessianOperator U x) v⟫ := by
    by_cases hz : w - Ring.inverse (hessianOperator U x) v = 0
    · simp [hz]
    · rw [← bilinearIteratedFDerivTwo_eq_inner_hessianOperator hU]
      exact (hPD _ hz).le
  simp only [map_sub, inner_sub_left, inner_sub_right, hcancel, hcross] at hnonneg
  rw [bilinearIteratedFDerivTwo_eq_inner_hessianOperator hU]
  linarith only [hnonneg]

section InverseHessianIdentities

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
/-- Coordinate expansion of the actual inverse-Hessian energy. The coordinates
are those of the actual Fréchet derivative, not an auxiliary measurable field. -/
theorem inverse_hessian_energy_eq_coordinate_sum
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    {U f : E → ℝ} (hU : ContDiff ℝ ∞ U)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ U x v v)
    (x : E) :
    inner ℝ (gradient f x)
        (Ring.inverse (hessianOperator U x) (gradient f x)) =
      ∑ i, ∑ j, inverseHessianEntry U b x i j *
        fderiv ℝ f x (b i) * fderiv ℝ f x (b j) := by
  classical
  have hU2 : ContDiff ℝ 2 U :=
    hU.of_le (WithTop.coe_le_coe.mpr le_top)
  have hunit := hessianOperator_isUnit_of_posDef hU2 x (hPD x)
  have hentry (i j : Fin n) :
      inner ℝ (b i) (Ring.inverse (hessianOperator U x) (b j)) =
        inverseHessianEntry U b x i j := by
    rfl
  have hc (i : Fin n) :
      b.repr (gradient f x) i = fderiv ℝ f x (b i) := by
    rw [b.repr_apply_apply, real_inner_comm]
    exact inner_gradient_left
  calc
    inner ℝ (gradient f x)
        (Ring.inverse (hessianOperator U x) (gradient f x)) =
        inner ℝ (∑ i, b.repr (gradient f x) i • b i)
          (Ring.inverse (hessianOperator U x)
            (∑ j, b.repr (gradient f x) j • b j)) := by
      simp only [b.sum_repr]
    _ = ∑ i, ∑ j, inverseHessianEntry U b x i j *
          fderiv ℝ f x (b i) * fderiv ℝ f x (b j) := by
      simp only [map_sum, map_smul, sum_inner, inner_sum,
        real_inner_smul_left, real_inner_smul_right, hentry, hc]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [inverseHessianEntry_symm b hU2 x j i]
      ring

/-- Smoothness and pointwise positive definiteness of the potential, together
with `C¹` regularity of the test, make the actual energy continuous. -/
theorem continuous_inverse_hessian_gradient_energy
    {U f : E → ℝ} (hU : ContDiff ℝ ∞ U)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ U x v v)
    (hf : ContDiff ℝ 1 f) :
    Continuous (fun x => inner ℝ (gradient f x)
      (Ring.inverse (hessianOperator U x) (gradient f x))) := by
  classical
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
    stdOrthonormalBasis ℝ E
  have hc (i : Fin (Module.finrank ℝ E)) :
      Continuous (fun x => fderiv ℝ f x (b i)) := by
    have heq : (fun x => fderiv ℝ f x (b i)) =
        (fun x => inner ℝ (gradient f x) (b i)) := by
      funext x
      exact (inner_gradient_left (𝕜 := ℝ) (f := f) (x := x) (y := b i)).symm
    rw [heq]
    exact (continuous_gradient hf).inner continuous_const
  have heq :
      (fun x => inner ℝ (gradient f x)
        (Ring.inverse (hessianOperator U x) (gradient f x))) =
      (fun x => ∑ i, ∑ j, inverseHessianEntry U b x i j *
        fderiv ℝ f x (b i) * fderiv ℝ f x (b j)) := by
    funext x
    exact inverse_hessian_energy_eq_coordinate_sum b hU hPD x
  rw [heq]
  refine continuous_finsetSum Finset.univ (fun i _ => ?_)
  refine continuous_finsetSum Finset.univ (fun j _ => ?_)
  exact (((contDiff_inverseHessianEntry b hU hPD i j).continuous).mul
    (hc i)).mul (hc j)

/-- Positivity of the actual inverse-Hessian energy, without a uniform
Hessian lower bound. This also covers the zero-dimensional space. -/
theorem inverse_hessian_gradient_energy_nonneg
    {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ U x v v)
    (x : E) :
    0 ≤ inner ℝ (gradient f x)
      (Ring.inverse (hessianOperator U x) (gradient f x)) := by
  simpa using hessian_inverse_young hU x (hPD x) (gradient f x) 0

end InverseHessianIdentities

end FiniteDimensional

end FunctionalInequalities.Analysis.BakryEmery
