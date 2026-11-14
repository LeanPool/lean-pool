/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import LeanPool.LiebThirring.Electrostatics.Basic
import all LeanPool.LiebThirring.Electrostatics.Basic
import LeanPool.LiebThirring.Electrostatics.SphereRadial
import LeanPool.LiebThirring.Analysis.WeakHarmonicConvolution

/-!
# Integrability for the three-dimensional fundamental solution

The real inverse-norm kernel is integrable on every ball about its pole.

The inverse-norm singularity is locally integrable in three dimensions.
-/

public section

open MeasureTheory Set Metric InnerProductSpace Laplacian
open scoped Topology ENNReal

namespace LiebThirring

/-- The real inverse-norm kernel is integrable on every ball about its pole. -/
theorem integrableOn_inv_norm_sub_ball (y : Position) (R : ℝ) :
    IntegrableOn (fun x : Position => ‖x - y‖⁻¹) (ball y R) := by
  have hzero : IntegrableOn (fun x : Position => ‖x‖⁻¹) (ball 0 R) := by
    apply (integrableOn_fun_norm_addHaar (volume : Measure Position)).mpr
    simp only [Position, finrank_euclideanSpace_fin, Nat.reduceSub, smul_eq_mul]
    have hr : IntegrableOn (fun r : ℝ => r) (Ioo 0 R) :=
      continuous_id.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    apply hr.congr_fun _ measurableSet_Ioo
    intro r hr
    field_simp
  have hpre : (fun x : Position => x - y) ⁻¹' ball 0 R = ball y R := by
    ext x
    simp only [mem_preimage, mem_ball, dist_eq_norm, sub_zero]
  have he := (Homeomorph.subRight y).measurableEmbedding
  simpa only [Function.comp_def, hpre] using
    ((measurePreserving_sub_right (volume : Measure Position) y).integrableOn_comp_preimage
      he).mpr hzero

/-- The inverse-norm singularity is locally integrable in three dimensions. -/
theorem locallyIntegrable_inv_norm_sub (y : Position) :
    LocallyIntegrable (fun x : Position => ‖x - y‖⁻¹) := by
  intro x
  refine ⟨ball y (‖x - y‖ + 1), isOpen_ball.mem_nhds ?_,
    integrableOn_inv_norm_sub_ball y _⟩
  rw [mem_ball, dist_eq_norm]
  exact lt_add_one _

/-- A `C²` function has continuous Mathlib Laplacian on `Position`. -/
theorem continuous_laplacian_position {f : Position → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (Δ f) := by
  have heq : Δ f = fun x => ∑ i,
      fderiv ℝ (fderiv ℝ f) x ((stdOrthonormalBasis ℝ Position) i)
        ((stdOrthonormalBasis ℝ Position) i) := by
    funext x
    simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [heq]
  exact continuous_finsetSum _ (fun i _ => continuous_kernel_hessian hf _ _)

/-- Taking the Laplacian preserves compact support. -/
theorem hasCompactSupport_laplacian_position {f : Position → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (Δ f) := by
  have heq : Δ f = ∑ i,
      (fun x => fderiv ℝ (fderiv ℝ f) x ((stdOrthonormalBasis ℝ Position) i)
        ((stdOrthonormalBasis ℝ Position) i)) := by
    funext x
    simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Finset.sum_apply]
  rw [heq]
  exact HasCompactSupport.finset_sum (fun i _ => hasCompactSupport_kernel_hessian hf _ _)

/-- Absolute integrability in the fundamental solution, before the distributional identity. -/
theorem integrable_inv_norm_sub_mul_laplacian {f : Position → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (y : Position) :
    Integrable (fun x => ‖x - y‖⁻¹ * Δ f x) :=
  (locallyIntegrable_inv_norm_sub y).integrable_smul_right_of_hasCompactSupport
    (continuous_laplacian_position hf) (hasCompactSupport_laplacian_position hfc)

/-- The shared extended potential is measurable for an s-finite charge. -/
theorem measurable_coulombPotential (β : Measure Position) [SFinite β] :
    Measurable (coulombPotential β) := by
  unfold coulombPotential
  have hK : Measurable (Function.uncurry coulombKernel) :=
    ((measurable_fst.sub measurable_snd).norm.ennreal_ofReal).inv
  exact hK.lintegral_prod_right (ν := β)

/-- Bounded extended Coulomb potentials are locally integrable after `toReal`.
The bound is on the extended potential, so it also asserts finiteness everywhere. -/
theorem locallyIntegrable_coulombPotential_toReal (β : Measure Position) [SFinite β]
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hβ : ∀ x, coulombPotential β x ≤ C) :
    LocallyIntegrable (fun x => (coulombPotential β x).toReal) := by
  apply (locallyIntegrable_const (c := C.toReal)).mono
    (measurable_coulombPotential β).ennreal_toReal.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono hC (hβ x)

/-- The left-hand test-function pairing in the fundamental solution is absolutely integrable. -/
theorem integrable_coulombPotential_toReal_mul_laplacian
    (β : Measure Position) [SFinite β] {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hβ : ∀ x, coulombPotential β x ≤ C)
    {f : Position → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Integrable (fun x => (coulombPotential β x).toReal * Δ f x) :=
  (locallyIntegrable_coulombPotential_toReal β hC hβ).integrable_smul_right_of_hasCompactSupport
      (continuous_laplacian_position hf) (hasCompactSupport_laplacian_position hfc)

end LiebThirring

end
