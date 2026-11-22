/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.MeasureTheory.Measure.PiWithDensity

/-! # Lebesgue density of the isotropic Gaussian on Euclidean space -/

@[expose] public section

open ProbabilityTheory MeasureTheory
open scoped ENNReal NNReal Matrix

namespace CutoffRigidity

/-- Transport a density by a measurable equivalence by composing it with the inverse. -/
theorem map_withDensity_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply f (e.measurable hs),
    withDensity_apply (fun y => f (e.symm y)) hs]
  rw [setLIntegral_map (f := fun y => f (e.symm y)) hs
    (by exact hf.comp e.symm.measurable) e.measurable]
  simp

/-- Independent scalar Gaussians form the multivariate Gaussian with diagonal covariance. -/
theorem gaussian_pi_eq_multivariate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (v : ι → ℝ≥0) :
    (Measure.pi (fun i => gaussianReal (m i) (v i))).map (WithLp.toLp 2) =
      multivariateGaussian m (Matrix.diagonal (fun i => (v i : ℝ))) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_pi, charFun_multivariateGaussian
    (Matrix.PosSemidef.diagonal (fun i => (v i).coe_nonneg))]
  simp_rw [charFun_gaussianReal, ← Complex.exp_sum]
  congr 1
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, dotProduct,
    Matrix.mulVec_diagonal, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_div, Complex.ofReal_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

end CutoffRigidity

namespace CutCur

open CutoffRigidity

theorem multivariateGaussian_eq_withDensity (k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)) =
      (volume : Measure (EuclideanSpace ℝ (Fin k))).withDensity
        (fun t => ENNReal.ofReal ((ρ / (2 * Real.pi)) ^ ((k : ℝ) / 2) *
          Real.exp (-(ρ / 2) * ‖t‖ ^ 2))) := by
  set v : ℝ≥0 := Real.toNNReal ρ⁻¹ with hv
  have hvc : (v : ℝ) = ρ⁻¹ := Real.coe_toNNReal _ (by positivity)
  have hv0 : v ≠ 0 := (Real.toNNReal_pos.2 (by positivity)).ne'
  have hmat : ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ) =
      Matrix.diagonal (fun _ => (v : ℝ)) := by
    ext i j
    by_cases h : i = j <;> simp [h, hvc]
  have gaussian_density : gaussianReal 0 v = (volume : Measure ℝ).withDensity (gaussianPDF 0 v) :=
    gaussianReal_of_var_ne_zero 0 hv0
  let : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 v)) :=
    gaussian_density ▸ inferInstanceAs (SigmaFinite (gaussianReal 0 v))
  have hpi : Measure.pi (fun _ : Fin k => gaussianReal 0 v) =
      (Measure.pi (fun _ : Fin k => (volume : Measure ℝ))).withDensity
        (fun x => ∏ i, gaussianPDF 0 v (x i)) := by
    simp_rw [gaussian_density]
    exact TauCeti.pi_withDensity (fun _ : Fin k => volume) (fun _ => measurable_gaussianPDF 0 v)
  have hmap := congrArg (fun μ : Measure (Fin k → ℝ) => μ.map (WithLp.toLp 2)) hpi
  have h1 := gaussian_pi_eq_multivariate (0 : EuclideanSpace ℝ (Fin k)) (fun _ :
      Fin k => v)
  simp only [PiLp.zero_apply] at h1
  rw [hmat, ← h1]
  refine hmap.trans ?_
  change ((Measure.pi (fun _ : Fin k => (volume : Measure ℝ))).withDensity
      (fun x => ∏ i, gaussianPDF 0 v (x i))).map (MeasurableEquiv.toLp 2 (Fin k → ℝ)) = _
  rw [map_withDensity_measurableEquiv _ _ _ (by fun_prop)]
  have hvol : (Measure.pi (fun _ : Fin k => (volume : Measure ℝ))).map (WithLp.toLp 2) =
      volume := (PiLp.volume_preserving_toLp (Fin k)).map_eq
  change ((Measure.pi (fun _ : Fin k => (volume : Measure ℝ))).map (WithLp.toLp 2)).withDensity _
      = _
  rw [hvol]
  congr 1
  ext t
  show ∏ i, gaussianPDF 0 v ((MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm t i) = _
  have hsymm : ∀ i, (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm t i = t i := fun i => rfl
  simp only [hsymm, gaussianPDF_def, gaussianPDFReal_def]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum, Finset.card_univ,
    Fintype.card_fin, EuclideanSpace.norm_sq_eq]
  have h2 : (2 * Real.pi * (v : ℝ)) = 2 * Real.pi / ρ := by rw [hvc]; ring
  have h3 : ((ρ / (2 * Real.pi)) ^ ((k : ℝ) / 2)) = ((Real.sqrt (2 * Real.pi * v))⁻¹) ^ k := by
    have hq : 0 ≤ 2 * Real.pi / ρ := by positivity
    have : ρ / (2 * Real.pi) = (2 * Real.pi / ρ)⁻¹ := by rw [inv_div]
    rw [h2, inv_pow, this, Real.inv_rpow hq, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hq]
    congr 2
    ring
  rw [h3]
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hvc, Real.norm_eq_abs, sq_abs]
  field_simp
  ring_nf

theorem lintegral_exp_neg_sq (k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ t : EuclideanSpace ℝ (Fin k), ENNReal.ofReal (Real.exp (-(ρ / 2) * ‖t‖ ^ 2)) =
      ENNReal.ofReal ((2 * Real.pi / ρ) ^ ((k : ℝ) / 2)) := by
  set c : ℝ := (ρ / (2 * Real.pi)) ^ ((k : ℝ) / 2) with hc
  have hcpos : 0 < c := by positivity
  have h := multivariateGaussian_eq_withDensity k hρ
  have h1 : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
      (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))) Set.univ = 1 := measure_univ
  rw [h, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  rw [← hc] at h1
  simp_rw [ENNReal.ofReal_mul hcpos.le] at h1
  rw [lintegral_const_mul _ (by fun_prop)] at h1
  have hinv : (2 * Real.pi / ρ) ^ ((k : ℝ) / 2) = c⁻¹ := by
    rw [hc, ← Real.inv_rpow (by positivity), inv_div]
  rw [hinv, ENNReal.ofReal_inv_of_pos hcpos]
  exact (ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm] at h1))

end CutCur
