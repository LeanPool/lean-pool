/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Normed-space tensor insertion and Hilbert-space contraction

Pointwise tensoring of a normed-space vector with a finite complex spin vector, as a continuous
bilinear map.

Insert a finite-spin `L²` function into a normed-space-valued `L²` space.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal InnerProduct

namespace LiebThirring

variable {ι α H : Type*} [Fintype ι] [MeasurableSpace α]
  [NormedAddCommGroup H] {μ : Measure α}

section Normed

variable [NormedSpace ℂ H]

/-- Pointwise tensoring of a normed-space vector with a finite complex spin vector,
as a continuous bilinear map. -/
@[expose] noncomputable def tensorInsertionBilinear :
    H →L[ℂ] EuclideanSpace ℂ ι →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  (LinearMap.mk₂ ℂ (fun v : H => fun a : EuclideanSpace ℂ ι =>
    toLp 2 (fun s => a s • v))
    (fun v w a => by
      ext i
      change a i • (v + w) = a i • v + a i • w
      rw [smul_add])
    (fun c v a => by
      ext i
      change a i • (c • v) = c • (a i • v)
      rw [smul_smul, smul_smul, mul_comm])
    (fun v a b => by
      ext i
      change (a i + b i) • v = a i • v + b i • v
      rw [add_smul])
    (fun c v a => by
      ext i
      change (c * a i) • v = c • (a i • v)
      rw [mul_smul])).mkContinuous₂ 1 (fun v a => by
        rw [PiLp.norm_eq_of_L2]
        change √(∑ s : ι, ‖a s • v‖ ^ 2) ≤ 1 * ‖v‖ * ‖a‖
        simp only [norm_smul, one_mul]
        have heq : ∑ s : ι, (‖a s‖ * ‖v‖) ^ 2 = ‖a‖ ^ 2 * ‖v‖ ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _
          ring
        rw [heq, Real.sqrt_mul (sq_nonneg ‖a‖), Real.sqrt_sq_eq_abs, abs_norm,
          Real.sqrt_sq_eq_abs, abs_norm, mul_comm])

/-- Insert a finite-spin `L²` function into a normed-space-valued `L²` space. -/
@[expose] noncomputable def tensorInsertion (f : Lp (EuclideanSpace ℂ ι) 2 μ) :
    H →L[ℂ] Lp (PiLp 2 (fun _ : ι => H)) 2 μ :=
  (tensorInsertionBilinear (ι := ι) (H := H)).compLpL₂ 2 μ |>.flip f

/-- The inserted `L²` class has the expected pointwise representative. -/
theorem tensorInsertion_apply_ae (f : Lp (EuclideanSpace ℂ ι) 2 μ) (v : H) :
    ∀ᵐ x ∂μ, ∀ s : ι, tensorInsertion (ι := ι) (H := H) f v x s = f x s • v := by
  filter_upwards [(tensorInsertionBilinear (ι := ι) (H := H) v).coeFn_compLp' f] with x hx
  intro s
  change ((tensorInsertionBilinear (ι := ι) (H := H) v).compLp f) x s = f x s • v
  exact
    congrArg (fun u : PiLp 2 (fun _ : ι => H) => u s) hx

/-- Exact norm of tensor insertion at a vector. -/
theorem tensorInsertion_norm (f : Lp (EuclideanSpace ℂ ι) 2 μ) (v : H) :
    ‖tensorInsertion (ι := ι) (H := H) f v‖ = ‖f‖ * ‖v‖ := by
  rw [Lp.norm_def]
  have heq : eLpNorm (tensorInsertion (ι := ι) (H := H) f v) 2 μ =
      eLpNorm ((‖v‖ : ℝ) • fun x => f x) 2 μ := by
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
      ((Lp.aestronglyMeasurable f).const_smul _)
    filter_upwards [tensorInsertion_apply_ae (ι := ι) (H := H) f v] with x hx
    have hvec : tensorInsertion (ι := ι) (H := H) f v x =
        toLp 2 (fun s => f x s • v) := by
      ext s
      exact hx s
    rw [hvec]
    rw [PiLp.norm_eq_of_L2]
    change √(∑ s : ι, ‖f x s • v‖ ^ 2) = ‖(‖v‖ : ℝ) • f x‖
    simp only [norm_smul, Real.norm_eq_abs, abs_norm]
    have hs : ∑ s : ι, (‖f x s‖ * ‖v‖) ^ 2 = ‖f x‖ ^ 2 * ‖v‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [hs, Real.sqrt_mul (sq_nonneg ‖f x‖), Real.sqrt_sq_eq_abs, abs_norm,
      Real.sqrt_sq_eq_abs, abs_norm, mul_comm]
  rw [heq, eLpNorm_const_smul]
  simp [enorm_eq_nnnorm, Lp.norm_def, mul_comm]

/-- The operator norm of insertion is bounded by the norm of the inserted
finite-spin function. -/
theorem tensorInsertion_opNorm_le (f : Lp (EuclideanSpace ℂ ι) 2 μ) :
    ‖tensorInsertion (ι := ι) (H := H) f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro v
  rw [tensorInsertion_norm (ι := ι) (H := H)]

/-- Tensor insertion is complex-linear in the inserted finite-spin function. -/
theorem tensorInsertion_smul (a : ℂ) (f : Lp (EuclideanSpace ℂ ι) 2 μ) :
    tensorInsertion (H := H) (a • f) = a • tensorInsertion (H := H) f := by
  exact map_smul
    ((tensorInsertionBilinear (ι := ι) (H := H)).compLpL₂ 2 μ).flip a f

end Normed

section Complete

variable [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The abstract contraction against `f`, defined as the adjoint of tensor
insertion. -/
@[expose] noncomputable def tensorContraction (f : Lp (EuclideanSpace ℂ ι) 2 μ) :
    Lp (PiLp 2 (fun _ : ι => H)) 2 μ →L[ℂ] H :=
  (tensorInsertion (ι := ι) (H := H) f).adjoint

/-- Contraction is conjugate-linear in the contracted finite-spin function. -/
theorem tensorContraction_smul (a : ℂ) (f : Lp (EuclideanSpace ℂ ι) 2 μ) :
    tensorContraction (H := H) (a • f) = star a • tensorContraction (H := H) f := by
  change (tensorInsertion (H := H) (a • f)).adjoint =
    star a • (tensorInsertion (H := H) f).adjoint
  rw [tensorInsertion_smul]
  exact map_smulₛₗ
    (ContinuousLinearMap.adjoint :
      (H →L[ℂ] Lp (PiLp 2 (fun _ : ι => H)) 2 μ) ≃ₗᵢ⋆[ℂ]
        (Lp (PiLp 2 (fun _ : ι => H)) 2 μ →L[ℂ] H))
    a (tensorInsertion (H := H) f)

/-- Contraction has the expected Hilbert-space norm bound. -/
theorem tensorContraction_norm_le (f : Lp (EuclideanSpace ℂ ι) 2 μ)
    (ψ : Lp (PiLp 2 (fun _ : ι => H)) 2 μ) :
    ‖tensorContraction (ι := ι) (H := H) f ψ‖ ≤ ‖f‖ * ‖ψ‖ := by
  calc
    ‖tensorContraction (ι := ι) (H := H) f ψ‖ ≤
        ‖tensorContraction (ι := ι) (H := H) f‖ * ‖ψ‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖tensorInsertion (ι := ι) (H := H) f‖ * ‖ψ‖ := by
      rw [tensorContraction, LinearIsometryEquiv.norm_map]
    _ ≤ ‖f‖ * ‖ψ‖ := mul_le_mul_of_nonneg_right
      (tensorInsertion_opNorm_le (ι := ι) (H := H) f) (norm_nonneg ψ)

end Complete

end LiebThirring

end
