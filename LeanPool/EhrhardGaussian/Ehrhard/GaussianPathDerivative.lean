/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianHeat
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Differentiating a time-dependent Gaussian affine average

A local polynomial bound for a smooth space-time test function gives an
explicit Gaussian integrable majorant for its path derivative. This is the
integral differentiation step for the nonlinear OU interpolation.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (standardGaussianMeasure)
open scoped Topology

namespace EhrhardGaussian.Ehrhard

private theorem norm_affine_bound {n : ℕ} {p : Fin n → ℝ} {a A : ℝ}
    (hp : ‖p‖ ≤ A) (ha : |a| ≤ A) (z : Fin n → ℝ) :
    ‖p + a • z‖ ≤ A * (1 + ‖z‖) := by
  calc
    ‖p + a • z‖ ≤ ‖p‖ + ‖a • z‖ := norm_add_le _ _
    _ ≤ A + A * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add hp (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
    _ = A * (1 + ‖z‖) := by ring

private theorem one_add_norm_affine_bound {n : ℕ} {p : Fin n → ℝ} {a A : ℝ}
    (hp : ‖p‖ ≤ A) (ha : |a| ≤ A) (z : Fin n → ℝ) :
    1 + ‖p + a • z‖ ≤ (1 + A) * (1 + ‖z‖) := by
  have h := norm_affine_bound hp ha z
  linarith only [h, norm_nonneg z]

/-- A locally polynomially bounded smooth space-time function can be differentiated under a Gaussian
integral along smooth centre and scale curves. -/
theorem hasDerivAt_gaussian_path_integral {n : ℕ} {U : Set ℝ} (hU : IsOpen U)
    {t : ℝ} (ht : t ∈ U) {F : ℝ × (Fin n → ℝ) → ℝ}
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    {p p' : ℝ → (Fin n → ℝ)} {a a' : ℝ → ℝ}
    (hp : ∀ s ∈ U, HasDerivAt p (p' s) s)
    (ha : ∀ s ∈ U, HasDerivAt a (a' s) s)
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) {N : ℕ}
    (hcoeff : ∀ s ∈ U, ‖p s‖ ≤ A ∧ |a s| ≤ A ∧ ‖p' s‖ ≤ A ∧ |a' s| ≤ A)
    (hbound : ∀ s ∈ U, ∀ y : Fin n → ℝ,
      |F (s, y)| + ‖fderiv ℝ F (s, y)‖ ≤ C * (1 + ‖y‖) ^ N) :
    HasDerivAt (fun s => ∫ z, F (s, p s + a s • z) ∂standardGaussianMeasure n)
      (∫ z, fderiv ℝ F (t, p t + a t • z) (1, p' t + a' t • z)
        ∂standardGaussianMeasure n) t := by
  let B := 1 + A
  have hB : 0 ≤ B := add_nonneg zero_le_one hA
  have hopen : IsOpen (U ×ˢ (univ : Set (Fin n → ℝ))) := hU.prod isOpen_univ
  have harg (s : ℝ) : Continuous (fun z : Fin n → ℝ => (s, p s + a s • z)) := by fun_prop
  have hmem (s : ℝ) (hs : s ∈ U) (z : Fin n → ℝ) :
      (s, p s + a s • z) ∈ U ×ˢ (univ : Set (Fin n → ℝ)) := ⟨hs, mem_univ _⟩
  have hcont (s : ℝ) (hs : s ∈ U) :
      Continuous (fun z => F (s, p s + a s • z)) :=
    hF.continuousOn.comp_continuous (harg s) (hmem s hs)
  have hmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable
      (fun z => F (s, p s + a s • z)) (standardGaussianMeasure n) := by
    filter_upwards [hU.mem_nhds ht] with s hs
    exact (hcont s hs).measurable.aestronglyMeasurable
  have hnorm (s : ℝ) (hs : s ∈ U) (z : Fin n → ℝ) :
      1 + ‖p s + a s • z‖ ≤ B * (1 + ‖z‖) :=
    one_add_norm_affine_bound (hcoeff s hs).1 (hcoeff s hs).2.1 z
  have hvalue : Integrable (fun z => F (t, p t + a t • z))
      (standardGaussianMeasure n) := by
    apply integrable_of_pi_polynomial_bound (hcont t ht).measurable
      (C := C * B ^ N) (mul_nonneg hC (pow_nonneg hB _)) (d := N)
    intro z
    calc
      |F (t, p t + a t • z)| ≤ C * (1 + ‖p t + a t • z‖) ^ N :=
        (le_add_of_nonneg_right (norm_nonneg _)).trans (hbound t ht _)
      _ ≤ C * (B * (1 + ‖z‖)) ^ N := by gcongr; exact hnorm t ht z
      _ = C * B ^ N * (1 + ‖z‖) ^ N := by rw [mul_pow]; ring
  have hdcont : Continuous (fun z => fderiv ℝ F (t, p t + a t • z)
      (1, p' t + a' t • z)) :=
    ((hF.continuousOn_fderiv_of_isOpen hopen le_rfl).comp_continuous
      (harg t) (hmem t ht)).clm_apply (by fun_prop)
  have hmajor : Integrable (fun z : Fin n → ℝ => C * B ^ (N + 1) * (1 + ‖z‖) ^ (N + 1))
      (standardGaussianMeasure n) := by
    apply integrable_of_pi_polynomial_bound (by fun_prop)
      (C := C * B ^ (N + 1)) (mul_nonneg hC (pow_nonneg hB _)) (d := N + 1)
    intro z
    exact (abs_of_nonneg (mul_nonneg (mul_nonneg hC (pow_nonneg hB _))
      (pow_nonneg (by positivity) _))).le
  have hdom : ∀ᵐ z ∂standardGaussianMeasure n, ∀ s ∈ U,
      ‖fderiv ℝ F (s, p s + a s • z) (1, p' s + a' s • z)‖ ≤
        C * B ^ (N + 1) * (1 + ‖z‖) ^ (N + 1) := by
    apply ae_of_all
    intro z s hs
    have hd : ‖((1 : ℝ), p' s + a' s • z)‖ ≤ B * (1 + ‖z‖) := by
      rw [Prod.norm_mk, norm_one, max_le_iff]
      constructor
      · dsimp only [B]
        nlinarith only [hA, norm_nonneg z]
      · exact (norm_affine_bound (hcoeff s hs).2.2.1 (hcoeff s hs).2.2.2 z).trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity))
    have hf : ‖fderiv ℝ F (s, p s + a s • z)‖ ≤ C * B ^ N * (1 + ‖z‖) ^ N := by
      calc
        ‖fderiv ℝ F (s, p s + a s • z)‖ ≤ C * (1 + ‖p s + a s • z‖) ^ N :=
          (le_add_of_nonneg_left (abs_nonneg _)).trans (hbound s hs _)
        _ ≤ C * (B * (1 + ‖z‖)) ^ N := by gcongr; exact hnorm s hs z
        _ = C * B ^ N * (1 + ‖z‖) ^ N := by rw [mul_pow]; ring
    calc
      ‖fderiv ℝ F (s, p s + a s • z) (1, p' s + a' s • z)‖ ≤
          ‖fderiv ℝ F (s, p s + a s • z)‖ * ‖((1 : ℝ), p' s + a' s • z)‖ :=
        (fderiv ℝ F (s, p s + a s • z)).le_opNorm _
      _ ≤ (C * B ^ N * (1 + ‖z‖) ^ N) * (B * (1 + ‖z‖)) :=
        mul_le_mul hf hd (norm_nonneg _) (by positivity)
      _ = C * B ^ (N + 1) * (1 + ‖z‖) ^ (N + 1) := by rw [pow_succ, pow_succ]; ring
  have hdiff : ∀ᵐ z ∂standardGaussianMeasure n, ∀ s ∈ U,
      HasDerivAt (fun r => F (r, p r + a r • z))
        (fderiv ℝ F (s, p s + a s • z) (1, p' s + a' s • z)) s := by
    apply ae_of_all
    intro z s hs
    have hpath := (hasDerivAt_id s).prodMk ((hp s hs).add ((ha s hs).smul_const z))
    have houter := ((hF.contDiffAt (hopen.mem_nhds (hmem s hs z))).differentiableAt_one).hasFDerivAt
    have hmodule : (RCLike.toInnerProductSpaceReal.toModule : Module ℝ ℝ) =
        (inferInstance : Module ℝ ℝ) := by
      apply Module.ext
      rfl
    have hadd : (Real.normedAddCommGroup.toAddCommGroup : AddCommGroup ℝ) =
        (inferInstance : AddCommGroup ℝ) := rfl
    simpa only [Function.comp_def, Pi.add_apply, id_eq, hmodule, hadd] using
      houter.comp_hasDerivAt s hpath
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (hU.mem_nhds ht)
    hmeas hvalue hdcont.measurable.aestronglyMeasurable hdom hmajor hdiff).2

/-- For `C¹` center and scale curves the coefficient bounds in the preceding
theorem follow on a smaller neighborhood from continuity. -/
theorem hasDerivAt_gaussian_path_integral_of_contDiff {n : ℕ} {U : Set ℝ}
    (hU : IsOpen U) {t : ℝ} (ht : t ∈ U) {F : ℝ × (Fin n → ℝ) → ℝ}
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    {p : ℝ → (Fin n → ℝ)} {a : ℝ → ℝ}
    (hp : ContDiffOn ℝ 1 p U) (ha : ContDiffOn ℝ 1 a U)
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (hbound : ∀ s ∈ U, ∀ y : Fin n → ℝ,
      |F (s, y)| + ‖fderiv ℝ F (s, y)‖ ≤ C * (1 + ‖y‖) ^ N) :
    HasDerivAt (fun s => ∫ z, F (s, p s + a s • z) ∂standardGaussianMeasure n)
      (∫ z, fderiv ℝ F (t, p t + a t • z) (1, deriv p t + deriv a t • z)
        ∂standardGaussianMeasure n) t := by
  let q : ℝ → (Fin n → ℝ) × (ℝ × ((Fin n → ℝ) × ℝ)) :=
    fun s => (p s, a s, deriv p s, deriv a s)
  let A := ‖q t‖ + 1
  have hA : 0 ≤ A := add_nonneg (norm_nonneg _) zero_le_one
  have hq : ContinuousAt q t :=
    (hp.continuousOn.continuousAt (hU.mem_nhds ht)).prodMk
      ((ha.continuousOn.continuousAt (hU.mem_nhds ht)).prodMk
        (((hp.continuousOn_deriv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds ht)).prodMk
          ((ha.continuousOn_deriv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds ht))))
  have hUevent : ∀ᶠ s in 𝓝 t, s ∈ U := hU.mem_nhds ht
  have hev : ∀ᶠ s in 𝓝 t, s ∈ U ∧ ‖q s‖ < A :=
    hUevent.and (hq.norm.eventually (Iio_mem_nhds (lt_add_one ‖q t‖)))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hev
  have hcoeff (s : ℝ) (hs : s ∈ Metric.ball t δ) :
      ‖p s‖ ≤ A ∧ |a s| ≤ A ∧ ‖deriv p s‖ ≤ A ∧ |deriv a s| ≤ A := by
    have hb := (hδsub hs).2.le
    have hpq : ‖p s‖ ≤ ‖q s‖ := norm_fst_le (q s)
    have haq : ‖a s‖ ≤ ‖q s‖ := (norm_fst_le (q s).2).trans (norm_snd_le (q s))
    have hdpq : ‖deriv p s‖ ≤ ‖q s‖ :=
      (norm_fst_le (q s).2.2).trans ((norm_snd_le (q s).2).trans (norm_snd_le (q s)))
    have hdaq : ‖deriv a s‖ ≤ ‖q s‖ :=
      (norm_snd_le (q s).2.2).trans ((norm_snd_le (q s).2).trans (norm_snd_le (q s)))
    exact ⟨hpq.trans hb, by simpa only [Real.norm_eq_abs] using haq.trans hb,
      hdpq.trans hb, by simpa only [Real.norm_eq_abs] using hdaq.trans hb⟩
  apply hasDerivAt_gaussian_path_integral Metric.isOpen_ball
    (Metric.mem_ball_self hδ)
    (hF.mono (fun v hv => ⟨(hδsub hv.1).1, hv.2⟩))
    (p' := deriv p) (a' := deriv a)
    (fun s hs => ((hp.contDiffAt (hU.mem_nhds (hδsub hs).1)).differentiableAt_one).hasDerivAt)
    (fun s hs => ((ha.contDiffAt (hU.mem_nhds (hδsub hs).1)).differentiableAt_one).hasDerivAt)
    hA hC hcoeff
  · intro s hs y
    exact hbound s (hδsub hs).1 y

end EhrhardGaussian.Ehrhard

end
