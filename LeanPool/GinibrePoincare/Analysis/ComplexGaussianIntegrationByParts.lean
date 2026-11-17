/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/ComplexGaussianIntegrationByParts.lean.
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

public import LeanPool.GinibrePoincare.Analysis.RealGaussianIntegrationByParts
public import LeanPool.GinibrePoincare.Concrete.Wirtinger

/-! # Sliced integration by parts for one complex Gaussian coordinate -/


@[expose] public section


open MeasureTheory

namespace GinibrePoincare

noncomputable section

def complexRealSlice (y : ℝ) (x : ℝ) : ℂ := (x : ℂ) + y * Complex.I

def complexImagSlice (x : ℝ) (y : ℝ) : ℂ := (x : ℂ) + y * Complex.I

def configurationCoordinateSlice {m : ℕ} (r : Configuration m) (j : Fin m)
    (w : ℂ) : Configuration m :=
  Function.update r j w

@[simp] theorem configurationCoordinateSlice_apply_self {m : ℕ}
    (r : Configuration m) (j : Fin m) (w : ℂ) :
    configurationCoordinateSlice r j w j = w := by
  simp [configurationCoordinateSlice]

theorem isometry_configurationCoordinateSlice {m : ℕ}
    (r : Configuration m) (j : Fin m) :
    Isometry (configurationCoordinateSlice r j) := by
  rw [isometry_iff_dist_eq]
  intro w w'
  apply le_antisymm
  · apply (dist_pi_le_iff dist_nonneg).2
    intro i
    by_cases hij : i = j
    · subst i
      simp
    · simp [configurationCoordinateSlice, hij]
  · have hj := (dist_pi_le_iff dist_nonneg).1
      (show dist (configurationCoordinateSlice r j w)
          (configurationCoordinateSlice r j w') ≤
        dist (configurationCoordinateSlice r j w)
          (configurationCoordinateSlice r j w') from le_rfl) j
    simpa using hj

theorem hasCompactSupport_comp_configurationCoordinateSlice {m : ℕ}
    {F : Configuration m → ℂ} (hF : HasCompactSupport F)
    (r : Configuration m) (j : Fin m) :
    HasCompactSupport (fun w ↦ F (configurationCoordinateSlice r j w)) := by
  apply HasCompactSupport.intro
    ((isometry_configurationCoordinateSlice r j).isClosedEmbedding.isCompact_preimage hF)
  intro w hw
  by_contra hne
  exact hw (subset_closure hne)

theorem contDiff_configurationCoordinateSlice {m : ℕ}
    (r : Configuration m) (j : Fin m) :
    ContDiff ℝ 1 (configurationCoordinateSlice r j) := by
  rw [contDiff_pi]
  intro i
  by_cases hij : i = j
  · subst i
    simp only [configurationCoordinateSlice, Function.update_self]
    fun_prop
  · simpa [configurationCoordinateSlice, hij] using
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℂ ↦ r i))

theorem contDiff_comp_configurationCoordinateSlice {m : ℕ}
    {F : Configuration m → ℂ} (hF : ContDiff ℝ 1 F)
    (r : Configuration m) (j : Fin m) :
    ContDiff ℝ 1 (fun w ↦ F (configurationCoordinateSlice r j w)) := by
  exact hF.comp (contDiff_configurationCoordinateSlice r j)

theorem hasFDerivAt_configurationCoordinateSlice {m : ℕ}
    (r : Configuration m) (j : Fin m) (w : ℂ) :
    HasFDerivAt (configurationCoordinateSlice r j)
      (ContinuousLinearMap.single ℝ (fun _ : Fin m ↦ ℂ) j) w := by
  have hlin : HasFDerivAt
      (ContinuousLinearMap.single ℝ (fun _ : Fin m ↦ ℂ) j)
      (ContinuousLinearMap.single ℝ (fun _ : Fin m ↦ ℂ) j) w :=
    (ContinuousLinearMap.single ℝ (fun _ : Fin m ↦ ℂ) j).hasFDerivAt
  have h := hlin.const_add (configurationCoordinateSlice r j 0)
  rw [show configurationCoordinateSlice r j =
      fun u ↦ configurationCoordinateSlice r j 0 +
        (ContinuousLinearMap.single ℝ (fun _ : Fin m ↦ ℂ) j) u by
    funext u i
    by_cases hij : i = j
    · subst i
      simp [configurationCoordinateSlice, ContinuousLinearMap.single_apply]
    · simp [configurationCoordinateSlice, ContinuousLinearMap.single_apply, hij]]
  exact h

theorem fderiv_comp_configurationCoordinateSlice_apply {m : ℕ}
    {F : Configuration m → ℂ} (hF : ContDiff ℝ 1 F)
    (r : Configuration m) (j : Fin m) (w v : ℂ) :
    (fderiv ℝ (fun u ↦ F (configurationCoordinateSlice r j u)) w) v =
      (fderiv ℝ F (configurationCoordinateSlice r j w))
        (coordinateDirection j v) := by
  change (fderiv ℝ (F ∘ configurationCoordinateSlice r j) w) v = _
  have hout := (hF.differentiable (by norm_num)
    (configurationCoordinateSlice r j w)).hasFDerivAt
  have hcomp := HasFDerivAt.comp w hout
    (hasFDerivAt_configurationCoordinateSlice r j w)
  have hv := congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L v) hcomp.fderiv
  rw [show coordinateDirection j v = Pi.single j v by
    funext i
    simp [coordinateDirection, Pi.single_apply]]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply] using hv

theorem integrable_of_continuous_hasCompactSupport_isFiniteMeasure
    {α E : Type*} [TopologicalSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    [NormedAddCommGroup E] {μ : Measure α} [IsFiniteMeasure μ] {f : α → E}
    (hf : Continuous f) (hfc : HasCompactSupport f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

theorem integrable_complexGaussian_of_continuous_hasCompactSupport {n : ℕ}
    {F : ℂ → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    Integrable F (complexCoordinateGaussianProbability n : Measure ℂ) :=
  integrable_of_continuous_hasCompactSupport_isFiniteMeasure hF hFc

theorem integrable_complexGaussian_fderiv_real {n : ℕ} {F : ℂ → ℂ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    Integrable (fun z ↦ (fderiv ℝ F z) (1 : ℂ))
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  apply integrable_complexGaussian_of_continuous_hasCompactSupport
  · exact (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  · exact hFc.fderiv_apply ℝ (1 : ℂ)

theorem integrable_complexGaussian_fderiv_imag {n : ℕ} {F : ℂ → ℂ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    Integrable (fun z ↦ (fderiv ℝ F z) Complex.I)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  apply integrable_complexGaussian_of_continuous_hasCompactSupport
  · exact (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  · exact hFc.fderiv_apply ℝ Complex.I

theorem integrable_complexGaussian_re_mul {n : ℕ} {F : ℂ → ℂ}
    (hF : Continuous F) (hFc : HasCompactSupport F) :
    Integrable (fun z ↦ (z.re : ℂ) * F z)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  apply integrable_complexGaussian_of_continuous_hasCompactSupport
  · fun_prop
  · exact hFc.mul_left

theorem integrable_complexGaussian_im_mul {n : ℕ} {F : ℂ → ℂ}
    (hF : Continuous F) (hFc : HasCompactSupport F) :
    Integrable (fun z ↦ (z.im : ℂ) * F z)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  apply integrable_complexGaussian_of_continuous_hasCompactSupport
  · fun_prop
  · exact hFc.mul_left

theorem integrable_piRealGaussian_comp_complexEquiv {n : ℕ} {F : ℂ → ℂ}
    (hF : Integrable F (complexCoordinateGaussianProbability n : Measure ℂ)) :
    Integrable (F ∘ Complex.measurableEquivPi.symm)
      (Measure.pi (fun _ : Fin 2 ↦
        (realCoordinateGaussianProbability n : Measure ℝ))) := by
  unfold complexCoordinateGaussianProbability at hF
  simpa only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pi] using
    (integrable_map_equiv Complex.measurableEquivPi.symm F).mp hF

theorem integrable_piRealGaussian_fderiv_real {n : ℕ} {F : ℂ → ℂ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    Integrable
      (fun x : Fin 2 → ℝ ↦
        (fderiv ℝ F (Complex.measurableEquivPi.symm x)) (1 : ℂ))
      (Measure.pi (fun _ : Fin 2 ↦
        (realCoordinateGaussianProbability n : Measure ℝ))) := by
  exact integrable_piRealGaussian_comp_complexEquiv
    (integrable_complexGaussian_fderiv_real hF hFc)

theorem integrable_piRealGaussian_fderiv_imag {n : ℕ} {F : ℂ → ℂ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    Integrable
      (fun x : Fin 2 → ℝ ↦
        (fderiv ℝ F (Complex.measurableEquivPi.symm x)) Complex.I)
      (Measure.pi (fun _ : Fin 2 ↦
        (realCoordinateGaussianProbability n : Measure ℝ))) := by
  exact integrable_piRealGaussian_comp_complexEquiv
    (integrable_complexGaussian_fderiv_imag hF hFc)

theorem integrable_piRealGaussian_re_mul {n : ℕ} {F : ℂ → ℂ}
    (hF : Continuous F) (hFc : HasCompactSupport F) :
    Integrable
      (fun x : Fin 2 → ℝ ↦
        ((Complex.measurableEquivPi.symm x).re : ℂ) *
          F (Complex.measurableEquivPi.symm x))
      (Measure.pi (fun _ : Fin 2 ↦
        (realCoordinateGaussianProbability n : Measure ℝ))) := by
  exact integrable_piRealGaussian_comp_complexEquiv
    (integrable_complexGaussian_re_mul hF hFc)

theorem integrable_piRealGaussian_im_mul {n : ℕ} {F : ℂ → ℂ}
    (hF : Continuous F) (hFc : HasCompactSupport F) :
    Integrable
      (fun x : Fin 2 → ℝ ↦
        ((Complex.measurableEquivPi.symm x).im : ℂ) *
          F (Complex.measurableEquivPi.symm x))
      (Measure.pi (fun _ : Fin 2 ↦
        (realCoordinateGaussianProbability n : Measure ℝ))) := by
  exact integrable_piRealGaussian_comp_complexEquiv
    (integrable_complexGaussian_im_mul hF hFc)

theorem integral_piFinTwo_eq_integral_prod {n : ℕ} {H : (Fin 2 → ℝ) → ℂ}
    (hH : Integrable H (Measure.pi (fun _ : Fin 2 ↦
      (realCoordinateGaussianProbability n : Measure ℝ)))) :
    (∫ x : Fin 2 → ℝ, H x
      ∂(Measure.pi (fun _ : Fin 2 ↦
        (realCoordinateGaussianProbability n : Measure ℝ)))) =
      ∫ x : ℝ, ∫ y : ℝ, H ![x, y]
        ∂(realCoordinateGaussianProbability n : Measure ℝ)
        ∂(realCoordinateGaussianProbability n : Measure ℝ) := by
  let μ : Fin 2 → Measure ℝ := fun _ ↦ realCoordinateGaussianProbability n
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)
  have he : MeasurePreserving e (Measure.pi μ) ((μ 0).prod (μ 1)) :=
    measurePreserving_piFinTwo μ
  have hprod : Integrable (H ∘ e.symm) ((μ 0).prod (μ 1)) :=
    he.symm.integrable_comp_of_integrable hH
  calc
    _ = ∫ p : ℝ × ℝ, H (e.symm p) ∂((μ 0).prod (μ 1)) :=
      (he.symm.integral_comp' H).symm
    _ = ∫ x : ℝ, ∫ y : ℝ, H (e.symm (x, y)) ∂(μ 1) ∂(μ 0) :=
      integral_prod _ hprod
    _ = _ := by
      simp only [e, MeasurableEquiv.piFinTwo_symm_apply, μ]
      congr 2 with x

theorem integral_piFinTwo_eq_integral_prod_swap {n : ℕ} {H : (Fin 2 → ℝ) → ℂ}
    (hH : Integrable H (Measure.pi (fun _ : Fin 2 ↦
      (realCoordinateGaussianProbability n : Measure ℝ)))) :
    (∫ x : Fin 2 → ℝ, H x
      ∂(Measure.pi (fun _ : Fin 2 ↦
        (realCoordinateGaussianProbability n : Measure ℝ)))) =
      ∫ y : ℝ, ∫ x : ℝ, H ![x, y]
        ∂(realCoordinateGaussianProbability n : Measure ℝ)
        ∂(realCoordinateGaussianProbability n : Measure ℝ) := by
  let μ : Fin 2 → Measure ℝ := fun _ ↦ realCoordinateGaussianProbability n
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)
  have he : MeasurePreserving e (Measure.pi μ) ((μ 0).prod (μ 1)) :=
    measurePreserving_piFinTwo μ
  have hprod : Integrable (H ∘ e.symm) ((μ 0).prod (μ 1)) :=
    he.symm.integrable_comp_of_integrable hH
  calc
    _ = ∫ p : ℝ × ℝ, H (e.symm p) ∂((μ 0).prod (μ 1)) :=
      (he.symm.integral_comp' H).symm
    _ = ∫ y : ℝ, ∫ x : ℝ, H (e.symm (x, y)) ∂(μ 0) ∂(μ 1) :=
      integral_prod_symm _ hprod
    _ = _ := by
      simp only [e, MeasurableEquiv.piFinTwo_symm_apply, μ]
      congr 2 with y

theorem integral_configuration_finSucc_split {k : ℕ} (j : Fin (k + 1))
    {H : Configuration (k + 1) → ℂ}
    (hH : Integrable H (complexGaussianMeasure (k + 1))) :
    (∫ z, H z ∂complexGaussianMeasure (k + 1)) =
      ∫ w : ℂ, ∫ r : Fin k → ℂ,
        H ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) ↦ ℂ) j).symm
          (w, r))
        ∂(Measure.pi (fun _ : Fin k ↦
          (complexCoordinateGaussianProbability (k + 1) : Measure ℂ)))
        ∂(complexCoordinateGaussianProbability (k + 1) : Measure ℂ) := by
  let μ : Fin (k + 1) → Measure ℂ := fun _ ↦
    complexCoordinateGaussianProbability (k + 1)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) ↦ ℂ) j
  have he : MeasurePreserving e (Measure.pi μ)
      ((μ j).prod (Measure.pi fun i : Fin k ↦ μ (j.succAbove i))) :=
    measurePreserving_piFinSuccAbove μ j
  unfold complexGaussianMeasure complexGaussianProbability at hH ⊢
  simp only [ProbabilityMeasure.toMeasure_pi] at hH ⊢
  have hprod : Integrable (H ∘ e.symm)
      ((μ j).prod (Measure.pi fun i : Fin k ↦ μ (j.succAbove i))) :=
    he.symm.integrable_comp_of_integrable hH
  calc
    _ = ∫ p : ℂ × (Fin k → ℂ), H (e.symm p)
        ∂((μ j).prod (Measure.pi fun i : Fin k ↦ μ (j.succAbove i))) :=
      (he.symm.integral_comp' H).symm
    _ = ∫ w : ℂ, ∫ r : Fin k → ℂ, H (e.symm (w, r))
        ∂(Measure.pi fun i : Fin k ↦ μ (j.succAbove i)) ∂(μ j) :=
      integral_prod _ hprod
    _ = _ := by simp only [μ, e]

theorem integral_configuration_finSucc_split_swap {k : ℕ} (j : Fin (k + 1))
    {H : Configuration (k + 1) → ℂ}
    (hH : Integrable H (complexGaussianMeasure (k + 1))) :
    (∫ z, H z ∂complexGaussianMeasure (k + 1)) =
      ∫ r : Fin k → ℂ, ∫ w : ℂ,
        H ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) ↦ ℂ) j).symm
          (w, r))
        ∂(complexCoordinateGaussianProbability (k + 1) : Measure ℂ)
        ∂(Measure.pi (fun _ : Fin k ↦
          (complexCoordinateGaussianProbability (k + 1) : Measure ℂ))) := by
  let μ : Fin (k + 1) → Measure ℂ := fun _ ↦
    complexCoordinateGaussianProbability (k + 1)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) ↦ ℂ) j
  have he : MeasurePreserving e (Measure.pi μ)
      ((μ j).prod (Measure.pi fun i : Fin k ↦ μ (j.succAbove i))) :=
    measurePreserving_piFinSuccAbove μ j
  unfold complexGaussianMeasure complexGaussianProbability at hH ⊢
  simp only [ProbabilityMeasure.toMeasure_pi] at hH ⊢
  have hprod : Integrable (H ∘ e.symm)
      ((μ j).prod (Measure.pi fun i : Fin k ↦ μ (j.succAbove i))) :=
    he.symm.integrable_comp_of_integrable hH
  calc
    _ = ∫ p : ℂ × (Fin k → ℂ), H (e.symm p)
        ∂((μ j).prod (Measure.pi fun i : Fin k ↦ μ (j.succAbove i))) :=
      (he.symm.integral_comp' H).symm
    _ = ∫ r : Fin k → ℂ, ∫ w : ℂ, H (e.symm (w, r))
        ∂(μ j) ∂(Measure.pi fun i : Fin k ↦ μ (j.succAbove i)) :=
      integral_prod_symm _ hprod
    _ = _ := by simp only [μ, e]

theorem integrable_configuration_fderiv_apply {m : ℕ}
    {F : Configuration m → ℂ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) (v : Configuration m) :
    Integrable (fun z ↦ (fderiv ℝ F z) v) (complexGaussianMeasure m) :=
  integrable_of_continuous_hasCompactSupport_isFiniteMeasure
    ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (hFc.fderiv_apply ℝ v)

theorem integrable_configuration_coordinate_re_mul {m : ℕ}
    {F : Configuration m → ℂ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (j : Fin m) :
    Integrable (fun z ↦ ((z j).re : ℂ) * F z) (complexGaussianMeasure m) := by
  apply integrable_of_continuous_hasCompactSupport_isFiniteMeasure
  · fun_prop
  · exact hFc.mul_left

theorem integrable_configuration_coordinate_im_mul {m : ℕ}
    {F : Configuration m → ℂ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (j : Fin m) :
    Integrable (fun z ↦ ((z j).im : ℂ) * F z) (complexGaussianMeasure m) := by
  apply integrable_of_continuous_hasCompactSupport_isFiniteMeasure
  · fun_prop
  · exact hFc.mul_left

theorem piFinSuccAbove_symm_eq_coordinateSlice {k : ℕ} (j : Fin (k + 1))
    (w : ℂ) (r : Fin k → ℂ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) ↦ ℂ) j).symm (w, r) =
      configurationCoordinateSlice
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) ↦ ℂ) j).symm
          (0, r)) j w := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [configurationCoordinateSlice,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  · simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk,
    configurationCoordinateSlice, ne_eq, hij, not_false_eq_true, Function.update_of_ne]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · simp [Fin.insertNth_apply_below hlt]
    · simp [Fin.insertNth_apply_above hgt]

theorem isometry_complexRealSlice (y : ℝ) : Isometry (complexRealSlice y) := by
  rw [isometry_iff_dist_eq]
  intro x x'
  rw [dist_eq_norm, dist_eq_norm]
  unfold complexRealSlice
  ring_nf
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem isometry_complexImagSlice (x : ℝ) : Isometry (complexImagSlice x) := by
  rw [isometry_iff_dist_eq]
  intro y y'
  rw [dist_eq_norm, dist_eq_norm]
  unfold complexImagSlice
  ring_nf
  rw [show (y : ℂ) * Complex.I - Complex.I * (y' : ℂ) =
      ((y - y' : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simp

theorem hasCompactSupport_comp_complexRealSlice {F : ℂ → ℂ}
    (hF : HasCompactSupport F) (y : ℝ) :
    HasCompactSupport (fun x ↦ F (complexRealSlice y x)) := by
  apply HasCompactSupport.intro
    ((isometry_complexRealSlice y).isClosedEmbedding.isCompact_preimage hF)
  intro x hx
  by_contra hne
  exact hx (subset_closure hne)

theorem hasCompactSupport_comp_complexImagSlice {F : ℂ → ℂ}
    (hF : HasCompactSupport F) (x : ℝ) :
    HasCompactSupport (fun y ↦ F (complexImagSlice x y)) := by
  apply HasCompactSupport.intro
    ((isometry_complexImagSlice x).isClosedEmbedding.isCompact_preimage hF)
  intro y hy
  by_contra hne
  exact hy (subset_closure hne)

theorem contDiff_comp_complexRealSlice {F : ℂ → ℂ}
    (hF : ContDiff ℝ 1 F) (y : ℝ) :
    ContDiff ℝ 1 (fun x ↦ F (complexRealSlice y x)) := by
  apply hF.comp
  unfold complexRealSlice
  exact Complex.ofRealCLM.contDiff.add contDiff_const

theorem contDiff_comp_complexImagSlice {F : ℂ → ℂ}
    (hF : ContDiff ℝ 1 F) (x : ℝ) :
    ContDiff ℝ 1 (fun y ↦ F (complexImagSlice x y)) := by
  apply hF.comp
  unfold complexImagSlice
  exact contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)

theorem deriv_comp_complexRealSlice {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (y x : ℝ) :
    deriv (fun r ↦ F (complexRealSlice y r)) x =
      (fderiv ℝ F (complexRealSlice y x)) (1 : ℂ) := by
  change deriv (F ∘ complexRealSlice y) x = _
  apply HasDerivAt.deriv
  have hinner : HasDerivAt (complexRealSlice y) (1 : ℂ) x := by
    change HasDerivAt (fun r : ℝ ↦ (r : ℂ) + (y : ℂ) * Complex.I) (1 : ℂ) x
    simpa using
      (Complex.ofRealCLM.hasFDerivAt.hasDerivAt.add_const
        ((y : ℂ) * Complex.I))
  have houter := (hF.differentiable (by norm_num)
    (complexRealSlice y x)).hasFDerivAt
  simpa only [Function.comp_apply] using
    (HasFDerivAt.comp_hasDerivAt x houter hinner)

theorem deriv_comp_complexImagSlice {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (x y : ℝ) :
    deriv (fun r ↦ F (complexImagSlice x r)) y =
      (fderiv ℝ F (complexImagSlice x y)) Complex.I := by
  change deriv (F ∘ complexImagSlice x) y = _
  apply HasDerivAt.deriv
  have hinner : HasDerivAt (complexImagSlice x) Complex.I y := by
    change HasDerivAt (fun r : ℝ ↦ (x : ℂ) + (r : ℂ) * Complex.I) Complex.I y
    simpa using
      ((Complex.ofRealCLM.hasFDerivAt.hasDerivAt.mul_const Complex.I).const_add
        (x : ℂ))
  have houter := (hF.differentiable (by norm_num)
    (complexImagSlice x y)).hasFDerivAt
  simpa only [Function.comp_apply] using
    (HasFDerivAt.comp_hasDerivAt y houter hinner)

theorem integral_complexGaussian_eq_integral_prod {n : ℕ} {F : ℂ → ℂ}
    (hF : Integrable F (complexCoordinateGaussianProbability n : Measure ℂ)) :
    (∫ z, F z ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      ∫ x : ℝ, ∫ y : ℝ, F ((x : ℂ) + (y : ℂ) * Complex.I)
        ∂(realCoordinateGaussianProbability n : Measure ℝ)
        ∂(realCoordinateGaussianProbability n : Measure ℝ) := by
  have hp := integrable_piRealGaussian_comp_complexEquiv hF
  unfold complexCoordinateGaussianProbability
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pi,
    MeasureTheory.integral_map_equiv]
  simpa only [Function.comp_apply, Complex.measurableEquivPi_symm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using
    integral_piFinTwo_eq_integral_prod hp

theorem integral_complexGaussian_eq_integral_prod_swap {n : ℕ} {F : ℂ → ℂ}
    (hF : Integrable F (complexCoordinateGaussianProbability n : Measure ℂ)) :
    (∫ z, F z ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      ∫ y : ℝ, ∫ x : ℝ, F ((x : ℂ) + (y : ℂ) * Complex.I)
        ∂(realCoordinateGaussianProbability n : Measure ℝ)
        ∂(realCoordinateGaussianProbability n : Measure ℝ) := by
  have hp := integrable_piRealGaussian_comp_complexEquiv hF
  unfold complexCoordinateGaussianProbability
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pi,
    MeasureTheory.integral_map_equiv]
  simpa only [Function.comp_apply, Complex.measurableEquivPi_symm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using
    integral_piFinTwo_eq_integral_prod_swap hp

theorem integrable_realProd_of_integrable_complexGaussian {n : ℕ}
    {F : ℂ → ℂ}
    (hF : Integrable F (complexCoordinateGaussianProbability n : Measure ℂ)) :
    Integrable (fun p : ℝ × ℝ ↦ F ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))
      ((realCoordinateGaussianProbability n : Measure ℝ).prod
        (realCoordinateGaussianProbability n : Measure ℝ)) := by
  have hp := integrable_piRealGaussian_comp_complexEquiv hF
  let μ : Fin 2 → Measure ℝ := fun _ ↦ realCoordinateGaussianProbability n
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)
  have he : MeasurePreserving e (Measure.pi μ) ((μ 0).prod (μ 1)) :=
    measurePreserving_piFinTwo μ
  have hprod := he.symm.integrable_comp_of_integrable hp
  apply hprod.congr
  filter_upwards with p
  simp only [Function.comp_apply, e,
    MeasurableEquiv.piFinTwo_symm_apply,
    Complex.measurableEquivPi_symm_apply
    ]
  congr 1

theorem complexGaussianIntegrationByParts_imag_of_integrable {n : ℕ}
    (hn : 0 < n) {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hFi : Integrable F (complexCoordinateGaussianProbability n : Measure ℂ))
    (hDi : Integrable (fun z ↦ (fderiv ℝ F z) Complex.I)
      (complexCoordinateGaussianProbability n : Measure ℂ))
    (hYi : Integrable (fun z ↦ (z.im : ℂ) * F z)
      (complexCoordinateGaussianProbability n : Measure ℂ)) :
    (∫ z, (fderiv ℝ F z) Complex.I
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      (2 * n : ℝ) * ∫ z, (z.im : ℂ) * F z
        ∂(complexCoordinateGaussianProbability n : Measure ℂ) := by
  have hFp := integrable_realProd_of_integrable_complexGaussian hFi
  have hDp := integrable_realProd_of_integrable_complexGaussian hDi
  have hYp := integrable_realProd_of_integrable_complexGaussian hYi
  have hFs := (integrable_prod_iff hFp.1).mp hFp |>.1
  have hDs := (integrable_prod_iff hDp.1).mp hDp |>.1
  have hYs := (integrable_prod_iff hYp.1).mp hYp |>.1
  rw [integral_complexGaussian_eq_integral_prod hDi,
    integral_complexGaussian_eq_integral_prod hYi, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hFs, hDs, hYs] with x hfx hdx hyx
  have hder : Integrable (deriv (fun y ↦ F (complexImagSlice x y)))
      (realCoordinateGaussianProbability n : Measure ℝ) := by
    apply hdx.congr
    filter_upwards with y
    rw [deriv_comp_complexImagSlice hF x]
    rfl
  have hy : Integrable (fun y : ℝ ↦ (y : ℂ) * F (complexImagSlice x y))
      (realCoordinateGaussianProbability n : Measure ℝ) := by
    apply hyx.congr
    filter_upwards with y
    simp [complexImagSlice]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_add, mul_one,
    zero_mul, add_zero]
  change (∫ y : ℝ, (fderiv ℝ F (complexImagSlice x y)) Complex.I
      ∂(realCoordinateGaussianProbability n : Measure ℝ)) =
    (2 * n : ℝ) * ∫ y : ℝ, (y : ℂ) * F (complexImagSlice x y)
      ∂(realCoordinateGaussianProbability n : Measure ℝ)
  rw [show (fun y : ℝ ↦ (fderiv ℝ F (complexImagSlice x y)) Complex.I) =
      deriv (fun y ↦ F (complexImagSlice x y)) by
    funext y
    exact (deriv_comp_complexImagSlice hF x y).symm]
  exact realGaussianIntegrationByParts_of_gaussian_integrable hn
    (contDiff_comp_complexImagSlice hF x) hfx hder hy

theorem complexGaussianIntegrationByParts_real_of_integrable {n : ℕ}
    (hn : 0 < n) {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hFi : Integrable F (complexCoordinateGaussianProbability n : Measure ℂ))
    (hDi : Integrable (fun z ↦ (fderiv ℝ F z) (1 : ℂ))
      (complexCoordinateGaussianProbability n : Measure ℂ))
    (hXi : Integrable (fun z ↦ (z.re : ℂ) * F z)
      (complexCoordinateGaussianProbability n : Measure ℂ)) :
    (∫ z, (fderiv ℝ F z) (1 : ℂ)
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      (2 * n : ℝ) * ∫ z, (z.re : ℂ) * F z
        ∂(complexCoordinateGaussianProbability n : Measure ℂ) := by
  have hFp := (integrable_realProd_of_integrable_complexGaussian hFi).swap
  have hDp := (integrable_realProd_of_integrable_complexGaussian hDi).swap
  have hXp := (integrable_realProd_of_integrable_complexGaussian hXi).swap
  have hFs := (integrable_prod_iff hFp.1).mp hFp |>.1
  have hDs := (integrable_prod_iff hDp.1).mp hDp |>.1
  have hXs := (integrable_prod_iff hXp.1).mp hXp |>.1
  rw [integral_complexGaussian_eq_integral_prod_swap hDi,
    integral_complexGaussian_eq_integral_prod_swap hXi, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hFs, hDs, hXs] with y hfy hdy hxy
  have hder : Integrable (deriv (fun x ↦ F (complexRealSlice y x)))
      (realCoordinateGaussianProbability n : Measure ℝ) := by
    apply hdy.congr
    filter_upwards with x
    rw [deriv_comp_complexRealSlice hF y]
    rfl
  have hx : Integrable (fun x : ℝ ↦ (x : ℂ) * F (complexRealSlice y x))
      (realCoordinateGaussianProbability n : Measure ℝ) := by
    apply hxy.congr
    filter_upwards with x
    simp [complexRealSlice]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, add_zero]
  change (∫ x : ℝ, (fderiv ℝ F (complexRealSlice y x)) (1 : ℂ)
      ∂(realCoordinateGaussianProbability n : Measure ℝ)) =
    (2 * n : ℝ) * ∫ x : ℝ, (x : ℂ) * F (complexRealSlice y x)
      ∂(realCoordinateGaussianProbability n : Measure ℝ)
  rw [show (fun x : ℝ ↦ (fderiv ℝ F (complexRealSlice y x)) (1 : ℂ)) =
      deriv (fun x ↦ F (complexRealSlice y x)) by
    funext x
    exact (deriv_comp_complexRealSlice hF y x).symm]
  exact realGaussianIntegrationByParts_of_gaussian_integrable hn
    (contDiff_comp_complexRealSlice hF y) hfy hder hx

theorem complexGaussianIntegrationByParts_real {n : ℕ} (hn : 0 < n)
    {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    (∫ z, (fderiv ℝ F z) (1 : ℂ)
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      (2 * n : ℝ) * ∫ z, (z.re : ℂ) * F z
        ∂(complexCoordinateGaussianProbability n : Measure ℂ) := by
  rw [integral_complexGaussian_eq_integral_prod_swap
      (integrable_complexGaussian_fderiv_real hF hFc),
    integral_complexGaussian_eq_integral_prod_swap
      (integrable_complexGaussian_re_mul hF.continuous hFc)]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, mul_zero]
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext y
  change (∫ x, (fderiv ℝ F (complexRealSlice y x)) (1 : ℂ)
      ∂(realCoordinateGaussianProbability n : Measure ℝ)) = _
  simp_rw [← deriv_comp_complexRealSlice hF y]
  simpa [complexRealSlice] using
    realGaussianIntegrationByParts hn (contDiff_comp_complexRealSlice hF y)
      (hasCompactSupport_comp_complexRealSlice hFc y)

theorem complexGaussianIntegrationByParts_imag {n : ℕ} (hn : 0 < n)
    {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    (∫ z, (fderiv ℝ F z) Complex.I
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      (2 * n : ℝ) * ∫ z, (z.im : ℂ) * F z
        ∂(complexCoordinateGaussianProbability n : Measure ℂ) := by
  rw [integral_complexGaussian_eq_integral_prod
      (integrable_complexGaussian_fderiv_imag hF hFc),
    integral_complexGaussian_eq_integral_prod
      (integrable_complexGaussian_im_mul hF.continuous hFc)]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_add, mul_one]
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext x
  change (∫ y, (fderiv ℝ F (complexImagSlice x y)) Complex.I
      ∂(realCoordinateGaussianProbability n : Measure ℝ)) = _
  simp_rw [← deriv_comp_complexImagSlice hF x]
  simpa [complexImagSlice] using
    realGaussianIntegrationByParts hn (contDiff_comp_complexImagSlice hF x)
      (hasCompactSupport_comp_complexImagSlice hFc x)

theorem complexRealSlice_gaussianIntegrationByParts {n : ℕ} (hn : 0 < n)
    {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (y : ℝ) :
    (∫ x, deriv (fun r ↦ F (complexRealSlice y r)) x
      ∂(realCoordinateGaussianProbability n : Measure ℝ)) =
      (2 * n : ℝ) * ∫ x, (x : ℂ) * F (complexRealSlice y x)
        ∂(realCoordinateGaussianProbability n : Measure ℝ) :=
  realGaussianIntegrationByParts hn (contDiff_comp_complexRealSlice hF y)
    (hasCompactSupport_comp_complexRealSlice hFc y)

theorem complexImagSlice_gaussianIntegrationByParts {n : ℕ} (hn : 0 < n)
    {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (x : ℝ) :
    (∫ y, deriv (fun r ↦ F (complexImagSlice x r)) y
      ∂(realCoordinateGaussianProbability n : Measure ℝ)) =
      (2 * n : ℝ) * ∫ y, (y : ℂ) * F (complexImagSlice x y)
        ∂(realCoordinateGaussianProbability n : Measure ℝ) :=
  realGaussianIntegrationByParts hn (contDiff_comp_complexImagSlice hF x)
    (hasCompactSupport_comp_complexImagSlice hFc x)

theorem configurationCoordinateSlice_gaussianIntegrationByParts_real
    {m : ℕ} (hm : 0 < m) {F : Configuration m → ℂ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (r : Configuration m) (j : Fin m) :
    (∫ w, (fderiv ℝ (fun u ↦ F (configurationCoordinateSlice r j u)) w)
        (1 : ℂ) ∂(complexCoordinateGaussianProbability m : Measure ℂ)) =
      (2 * m : ℝ) * ∫ w, (w.re : ℂ) *
        F (configurationCoordinateSlice r j w)
        ∂(complexCoordinateGaussianProbability m : Measure ℂ) :=
  complexGaussianIntegrationByParts_real hm
    (contDiff_comp_configurationCoordinateSlice hF r j)
    (hasCompactSupport_comp_configurationCoordinateSlice hFc r j)

theorem configurationCoordinateSlice_gaussianIntegrationByParts_imag
    {m : ℕ} (hm : 0 < m) {F : Configuration m → ℂ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (r : Configuration m) (j : Fin m) :
    (∫ w, (fderiv ℝ (fun u ↦ F (configurationCoordinateSlice r j u)) w)
        Complex.I ∂(complexCoordinateGaussianProbability m : Measure ℂ)) =
      (2 * m : ℝ) * ∫ w, (w.im : ℂ) *
        F (configurationCoordinateSlice r j w)
        ∂(complexCoordinateGaussianProbability m : Measure ℂ) :=
  complexGaussianIntegrationByParts_imag hm
    (contDiff_comp_configurationCoordinateSlice hF r j)
    (hasCompactSupport_comp_configurationCoordinateSlice hFc r j)

theorem configurationGaussianIntegrationByParts_real_finSucc {k : ℕ}
    (j : Fin (k + 1)) {F : Configuration (k + 1) → ℂ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    (∫ z, (fderiv ℝ F z) (realCoordinateDirection j)
      ∂complexGaussianMeasure (k + 1)) =
      (2 * (k + 1) : ℝ) * ∫ z, ((z j).re : ℂ) * F z
        ∂complexGaussianMeasure (k + 1) := by
  rw [integral_configuration_finSucc_split_swap j
      (integrable_configuration_fderiv_apply hF hFc (realCoordinateDirection j)),
    integral_configuration_finSucc_split_swap j
      (integrable_configuration_coordinate_re_mul hF.continuous hFc j),
    ← MeasureTheory.integral_const_mul]
  congr 1
  funext r
  let z0 := (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (k + 1) ↦ ℂ) j).symm (0, r)
  have hins : (fun w ↦ (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (k + 1) ↦ ℂ) j).symm (w, r)) =
      configurationCoordinateSlice z0 j := by
    funext w
    exact piFinSuccAbove_symm_eq_coordinateSlice j w r
  have hins_apply (w : ℂ) : (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (k + 1) ↦ ℂ) j).symm (w, r) =
      configurationCoordinateSlice z0 j w := congrFun hins w
  simp only [hins_apply]
  rw [show (fun w ↦ (fderiv ℝ F (configurationCoordinateSlice z0 j w))
      (realCoordinateDirection j)) =
      fun w ↦ (fderiv ℝ (fun u ↦ F (configurationCoordinateSlice z0 j u)) w)
        (1 : ℂ) by
    funext w
    rw [fderiv_comp_configurationCoordinateSlice_apply hF]
    rfl]
  simpa using configurationCoordinateSlice_gaussianIntegrationByParts_real
    (Nat.succ_pos k) hF hFc z0 j

theorem configurationGaussianIntegrationByParts_imag_finSucc {k : ℕ}
    (j : Fin (k + 1)) {F : Configuration (k + 1) → ℂ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    (∫ z, (fderiv ℝ F z) (imaginaryCoordinateDirection j)
      ∂complexGaussianMeasure (k + 1)) =
      (2 * (k + 1) : ℝ) * ∫ z, ((z j).im : ℂ) * F z
        ∂complexGaussianMeasure (k + 1) := by
  rw [integral_configuration_finSucc_split_swap j
      (integrable_configuration_fderiv_apply hF hFc (imaginaryCoordinateDirection j)),
    integral_configuration_finSucc_split_swap j
      (integrable_configuration_coordinate_im_mul hF.continuous hFc j),
    ← MeasureTheory.integral_const_mul]
  congr 1
  funext r
  let z0 := (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (k + 1) ↦ ℂ) j).symm (0, r)
  have hins_apply (w : ℂ) : (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (k + 1) ↦ ℂ) j).symm (w, r) =
      configurationCoordinateSlice z0 j w :=
    piFinSuccAbove_symm_eq_coordinateSlice j w r
  simp only [hins_apply]
  rw [show (fun w ↦ (fderiv ℝ F (configurationCoordinateSlice z0 j w))
      (imaginaryCoordinateDirection j)) =
      fun w ↦ (fderiv ℝ (fun u ↦ F (configurationCoordinateSlice z0 j u)) w)
        Complex.I by
    funext w
    rw [fderiv_comp_configurationCoordinateSlice_apply hF]
    rfl]
  simpa using configurationCoordinateSlice_gaussianIntegrationByParts_imag
    (Nat.succ_pos k) hF hFc z0 j

theorem integral_configuration_coordinate_mul_eq_re_add_im_finSucc {k : ℕ}
    (j : Fin (k + 1)) {F : Configuration (k + 1) → ℂ}
    (hF : Continuous F) (hFc : HasCompactSupport F) :
    (∫ z, z j * F z ∂complexGaussianMeasure (k + 1)) =
      (∫ z, ((z j).re : ℂ) * F z ∂complexGaussianMeasure (k + 1)) +
        Complex.I * ∫ z, ((z j).im : ℂ) * F z
          ∂complexGaussianMeasure (k + 1) := by
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add
    (integrable_configuration_coordinate_re_mul hF hFc j)
    ((integrable_configuration_coordinate_im_mul hF hFc j).const_mul Complex.I)]
  apply integral_congr_ae
  filter_upwards [] with z
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.I_re, Complex.I_im, Complex.mul_im, add_zero,
      one_mul, zero_sub]
    ring
  · simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.I_re, Complex.I_im, Complex.mul_re, sub_zero,
      one_mul, zero_add]

theorem configurationGaussianDbarIntegrationByParts_finSucc {k : ℕ}
    (j : Fin (k + 1)) {F : Configuration (k + 1) → ℂ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    (∫ z, dbarComponent F j z ∂complexGaussianMeasure (k + 1)) =
      ((k + 1 : ℕ) : ℂ) * ∫ z, z j * F z
        ∂complexGaussianMeasure (k + 1) := by
  have hr := integrable_configuration_fderiv_apply hF hFc
    (realCoordinateDirection j)
  have hi := integrable_configuration_fderiv_apply hF hFc
    (imaginaryCoordinateDirection j)
  unfold dbarComponent
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add hr (hi.const_mul Complex.I),
    MeasureTheory.integral_const_mul,
    configurationGaussianIntegrationByParts_real_finSucc j hF hFc,
    configurationGaussianIntegrationByParts_imag_finSucc j hF hFc,
    integral_configuration_coordinate_mul_eq_re_add_im_finSucc j hF.continuous hFc]
  push_cast
  ring

theorem configurationGaussianDbarIntegrationByParts {n : ℕ} (hn : 0 < n)
    (j : Fin n) {F : Configuration n → ℂ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    (∫ z, dbarComponent F j z ∂complexGaussianMeasure n) =
      (n : ℂ) * ∫ z, z j * F z ∂complexGaussianMeasure n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact configurationGaussianDbarIntegrationByParts_finSucc j hF hFc

end

end GinibrePoincare
