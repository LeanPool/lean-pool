/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatSmooth
public import LeanPool.EscauriazaSereginSverak.PartV.HeatEntropyH1
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Energy identities for the smooth forced heat response

For a smooth compactly supported tensor supported in positive times, a convex
entropy `Φ` with gradient `T` satisfies the whole-space identity

`∫ Φ(Z(t₁)) = -∫₀^{t₁} ∑_{i,j} ∫ ∂_j[T_i(Z)] (∂_j Z_i + g_ij)`,

obtained from the fundamental theorem of calculus in time, Fubini, and an
integration by parts in space. It is the common core of the energy and
critical estimates of `lem:pv-stokes`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The response vector `Z(p)` to the tensor `g` at a space-time point. -/
@[expose] def responseVec (g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (p : Vec3 × ℝ) : Vec3 :=
  fun k => causalHeatConv (vecTimeDiv g k) p

/-- The spatial derivative `∂_j Z(p)` of the response vector. -/
@[expose] def responseGrad (g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (j : Fin 3) (p : Vec3 × ℝ) : Vec3 :=
  fun k => fderiv ℝ (causalHeatConv (vecTimeDiv g k)) p (CKN.basisVec j, 0)

/-- A continuously differentiable map vanishing at the origin grows at most
linearly, with bounded derivative, on each ball. -/
theorem exists_linear_bound_of_contDiff {T : Vec3 → Vec3} (hT : ContDiff ℝ 1 T)
    (hT0 : T 0 = 0) (R : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ v : Vec3, ‖v‖ ≤ R → ‖T v‖ ≤ L * ‖v‖ ∧ ‖fderiv ℝ T v‖ ≤ L := by
  have hcont : Continuous (fun v => fderiv ℝ T v) := hT.continuous_fderiv one_ne_zero
  obtain ⟨L, hL⟩ :=
    (isCompact_closedBall (0 : Vec3) R).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max L 0, le_max_right _ _, fun v hv => ⟨?_, ?_⟩⟩
  · have hvmem : v ∈ Metric.closedBall (0 : Vec3) R := mem_closedBall_zero_iff.2 hv
    have h0mem : (0 : Vec3) ∈ Metric.closedBall (0 : Vec3) R :=
      mem_closedBall_zero_iff.2 (by rw [norm_zero]; exact (norm_nonneg v).trans hv)
    have hmvt := (convex_closedBall (0 : Vec3) R).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => (hT.differentiable one_ne_zero) x)
      (fun x hx => (hL x hx).trans (le_max_left L 0)) h0mem hvmem
    simpa [hT0] using hmvt
  · exact (hL v (mem_closedBall_zero_iff.2 hv)).trans (le_max_left L 0)

/-- A product of two functions with `(1 + |x|)^{-3}` decay is integrable on
Vec3. -/
theorem integrable_mul_of_decay {f g : Vec3 → ℝ}
    (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfb : ∀ x, |f x| ≤ A / (1 + vec3EuclideanNorm x) ^ 3)
    (hgb : ∀ x, |g x| ≤ B / (1 + vec3EuclideanNorm x) ^ 3) :
    Integrable (fun x => f x * g x) := by
  refine (heat_decay_six_integrable (A * B) (mul_nonneg hA hB)).mono' (hf.mul hg)
    (Eventually.of_forall fun x => ?_)
  have hden : 0 < (1 + vec3EuclideanNorm x) ^ 3 := by
    have := vec3EuclideanNorm_nonneg x
    positivity
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |f x| * |g x| ≤ (A / (1 + vec3EuclideanNorm x) ^ 3) *
        (B / (1 + vec3EuclideanNorm x) ^ 3) :=
      mul_le_mul (hfb x) (hgb x) (abs_nonneg _) (div_nonneg hA hden.le)
    _ = A * B / (1 + vec3EuclideanNorm x) ^ 6 := by
      rw [div_mul_div_comm, ← pow_add]

/-- A space-time function bounded by `C (1 + |x|)^{-6}` on a finite time window
is integrable on the window. -/
theorem integrable_window_of_decay {F : Vec3 × ℝ → ℝ} (hF : Continuous F) {a b C : ℝ}
    (hC : 0 ≤ C)
    (hb : ∀ x t, t ∈ Ioc a b → |F (x, t)| ≤ C / (1 + vec3EuclideanNorm x) ^ 6) :
    Integrable F ((volume : Measure Vec3).prod (volume.restrict (Ioc a b))) := by
  have hdom : Integrable (fun p : Vec3 × ℝ =>
      C / (1 + vec3EuclideanNorm p.1) ^ 6 * (1 : ℝ))
      ((volume : Measure Vec3).prod (volume.restrict (Ioc a b))) :=
    (heat_decay_six_integrable C hC).mul_prod (integrable_const (1 : ℝ))
  refine hdom.mono' hF.aestronglyMeasurable ?_
  have hprod : (volume : Measure Vec3).prod (volume.restrict (Ioc a b)) =
      ((volume : Measure Vec3).prod volume).restrict (univ ×ˢ Ioc a b) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hprod]
  filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioc)] with p hp
  rw [Real.norm_eq_abs, mul_one]
  exact hb p.1 p.2 hp.2

/-- The fundamental theorem of calculus along each spatial point for an
entropy of a smooth vector field vanishing at time zero. -/
theorem entropy_eq_time_integral {Φ : Vec3 → ℝ} {T : Vec3 → Vec3}
    (hΦ : ContDiff ℝ 1 Φ) (hT : Continuous T)
    (hΦT : ∀ v w : Vec3, fderiv ℝ Φ v w = ∑ i : Fin 3, T v i * w i) (hΦ0 : Φ 0 = 0)
    {U : Fin 3 → Vec3 × ℝ → ℝ} (hU : ∀ i, ContDiff ℝ 1 (U i))
    (hU0 : ∀ i x, U i (x, 0) = 0) (x : Vec3) (t₁ : ℝ) :
    Φ (fun i => U i (x, t₁)) = ∫ t in (0 : ℝ)..t₁,
      ∑ i : Fin 3, T (fun k => U k (x, t)) i * fderiv ℝ (U i) (x, t) (0, 1) := by
  let γ : ℝ → Vec3 := fun t i => U i (x, t)
  have hpath (t : ℝ) : HasDerivAt (fun s : ℝ => ((x, s) : Vec3 × ℝ)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have hγ (t : ℝ) : HasDerivAt γ (fun i => fderiv ℝ (U i) (x, t) (0, 1)) t := by
    apply hasDerivAt_pi.2
    intro i
    exact ((hU i).differentiable one_ne_zero (x, t)).hasFDerivAt.comp_hasDerivAt t (hpath t)
  have hf (t : ℝ) : HasDerivAt (fun s => Φ (γ s))
      (∑ i : Fin 3, T (γ t) i * fderiv ℝ (U i) (x, t) (0, 1)) t := by
    have h := ((hΦ.differentiable one_ne_zero) (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t)
    rw [hΦT] at h
    exact h
  have hγc : Continuous γ := continuous_pi fun i =>
    (hU i).continuous.comp (continuous_const.prodMk continuous_id)
  have hcont : Continuous (fun t => ∑ i : Fin 3, T (γ t) i * fderiv ℝ (U i) (x, t) (0, 1)) :=
    continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp (hT.comp hγc)).mul
        ((((hU i).continuous_fderiv one_ne_zero).comp
          (continuous_const.prodMk continuous_id)).clm_apply continuous_const)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hf t)
    (hcont.intervalIntegrable 0 t₁)
  have hγ0 : γ 0 = 0 := by
    funext i
    exact hU0 i x
  change Φ (γ t₁) = _
  rw [hftc, hγ0, hΦ0, sub_zero]

/-- Fubini form of `entropy_eq_time_integral`: the spatial integral of the
entropy at time `t₁` is the time integral of the spatial production. -/
theorem entropy_integral_eq_window_integral {Φ : Vec3 → ℝ} {T : Vec3 → Vec3}
    (hΦ : ContDiff ℝ 1 Φ) (hT : Continuous T)
    (hΦT : ∀ v w : Vec3, fderiv ℝ Φ v w = ∑ i : Fin 3, T v i * w i) (hΦ0 : Φ 0 = 0)
    {U : Fin 3 → Vec3 × ℝ → ℝ} (hU : ∀ i, ContDiff ℝ 1 (U i))
    (hU0 : ∀ i x, U i (x, 0) = 0) {t₁ C : ℝ} (ht₁ : 0 ≤ t₁) (hC : 0 ≤ C)
    (hb : ∀ x t, t ∈ Ioc 0 t₁ → |∑ i : Fin 3, T (fun k => U k (x, t)) i *
      fderiv ℝ (U i) (x, t) (0, 1)| ≤ C / (1 + vec3EuclideanNorm x) ^ 6) :
    ∫ x, Φ (fun i => U i (x, t₁)) = ∫ t in (0 : ℝ)..t₁, ∫ x,
      ∑ i : Fin 3, T (fun k => U k (x, t)) i * fderiv ℝ (U i) (x, t) (0, 1) := by
  let F : Vec3 × ℝ → ℝ := fun p =>
    ∑ i : Fin 3, T (fun k => U k p) i * fderiv ℝ (U i) p (0, 1)
  have hFc : Continuous F := by
    have hUvec : Continuous (fun p : Vec3 × ℝ => fun k => U k p) :=
      continuous_pi fun k => (hU k).continuous
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp (hT.comp hUvec)).mul
        (((hU i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hFint := integrable_window_of_decay hFc hC hb
  have hpoint (x : Vec3) : Φ (fun i => U i (x, t₁)) =
      ∫ t in Ioc 0 t₁, F (x, t) := by
    rw [entropy_eq_time_integral hΦ hT hΦT hΦ0 hU hU0 x t₁,
      intervalIntegral.integral_of_le ht₁]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_of_le ht₁]
  exact integral_integral_swap (f := fun x t => F (x, t)) hFint

end ESS

end
