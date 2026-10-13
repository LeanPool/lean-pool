/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderKernelL1
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# OneStepSchauderSphere

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Sphere averages and the mean value property

The reproducing-convolution route of the Schauder gradient-Hölder estimate rests on the
**mean value property** of harmonic functions.  This module builds it:

* `sphereAverage f x r` — the average of `f` over the sphere of radius `r`
  around `x`, realized as an integral over the **unit** sphere so that the
  radius is a smooth parameter;
* `hasDerivAt_sphereAverage` — differentiation under the integral sign in the
  radius;
* the mean value property itself: a function whose spherical flux vanishes has
  a radius-independent sphere average, hence equals its own sphere average.
-/

-- ==== the sphere average ====
open scoped Real
open MeasureTheory Metric

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ### The surface measure on the unit sphere -/

/-- The surface measure on the unit sphere of `EuclideanSpace ℝ (Fin d)`: the mathlib push of the
Lebesgue (additive Haar) volume onto `Metric.sphere 0 1` via `Measure.toSphere`.  For `d ≥ 1` it is
a finite, strictly positive measure, so it normalizes the spherical average. -/
def sphereMeasure (d : ℕ) : Measure (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
  (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere

instance instIsFiniteMeasureSphereMeasure : IsFiniteMeasure (sphereMeasure d) :=
  inferInstanceAs (IsFiniteMeasure
    ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere))

/-- For `d ≥ 1` the ambient space is nontrivial, hence the surface measure is nonzero. -/
instance instNeZeroSphereMeasure [NeZero d] : NeZero (sphereMeasure d) := by
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) := inferInstance
  exact ⟨Measure.toSphere_ne_zero (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))⟩

theorem sphereMeasure_univ_ne_zero [NeZero d] : (sphereMeasure d) Set.univ ≠ 0 :=
  Measure.measure_univ_ne_zero.2 (NeZero.ne (sphereMeasure d))

theorem sphereMeasure_real_univ_ne_zero [NeZero d] :
    (sphereMeasure d).real Set.univ ≠ 0 :=
  ENNReal.toReal_ne_zero.2 ⟨sphereMeasure_univ_ne_zero, (measure_lt_top _ _).ne⟩

/-! ### The spherical average -/

/-- The normalized spherical average of `u` over `∂B(x, r)`, written as the average
of the dilated-translated function `ω ↦ u (x + r • ω)` over the unit sphere.
(Native port of K `euclideanL2SphereAverage`.) -/
def sphereAverage (x : EuclideanSpace ℝ (Fin d)) (r : ℝ)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  ⨍ ω, u (x + r • (ω : EuclideanSpace ℝ (Fin d))) ∂(sphereMeasure d)

theorem sphereAverage_def (x : EuclideanSpace ℝ (Fin d)) (r : ℝ)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    sphereAverage x r u = ⨍ ω, u (x + r • (ω : EuclideanSpace ℝ (Fin d))) ∂(sphereMeasure d) :=
  rfl

/-- The spherical average of a constant is that constant. -/
@[simp] theorem sphereAverage_const [NeZero d] (x : EuclideanSpace ℝ (Fin d)) (r c : ℝ) :
    sphereAverage x r (fun _ => c) = c :=
  average_const (sphereMeasure d) c

/-- The spherical average at radius `0` is point evaluation at the center. -/
@[simp] theorem sphereAverage_zero [NeZero d] (x : EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    sphereAverage x 0 u = u x := by
  simp only [sphereAverage, zero_smul, add_zero]
  exact average_const (sphereMeasure d) (u x)

/-! ### Continuity in the radius -/

/-- **Continuity in the radius (at a point).**  For continuous `u`, the spherical average
`r ↦ sphereAverage x r u` is continuous at every `r₀`.  Proof: dominated convergence with the
local bound obtained from continuity of `u` on the compact ball `closedBall x (|r₀| + 1)`. -/
theorem continuousAt_sphereAverage [NeZero d] {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (huc : Continuous u) (x : EuclideanSpace ℝ (Fin d)) (r₀ : ℝ) :
    ContinuousAt (fun r : ℝ => sphereAverage x r u) r₀ := by
  -- Reduce to continuity of the un-normalized integral.
  have hintCont : ContinuousAt
      (fun r : ℝ => ∫ ω, u (x + r • (ω : EuclideanSpace ℝ (Fin d))) ∂(sphereMeasure d)) r₀ := by
    -- Local bound from compactness of `closedBall x (|r₀| + 1)`.
    obtain ⟨M, hM⟩ := (isCompact_closedBall x (|r₀| + 1)).exists_bound_of_continuousOn
      huc.continuousOn
    refine continuousAt_of_dominated
      (F := fun r (ω : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) =>
        u (x + r • ((ω : EuclideanSpace ℝ (Fin d)))))
      (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
    · refine Filter.Eventually.of_forall fun r => ?_
      have hc : Continuous (fun ω : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
          u (x + r • (ω : EuclideanSpace ℝ (Fin d)))) := by fun_prop
      exact hc.aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds r₀ one_pos] with r hr
      refine Filter.Eventually.of_forall fun ω => ?_
      have hω : ‖(ω : EuclideanSpace ℝ (Fin d))‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
      have hrle : |r| ≤ |r₀| + 1 := by
        have hlt : |r - r₀| < 1 := by
          have := Metric.mem_ball.mp hr; rwa [Real.dist_eq] at this
        have := abs_sub_abs_le_abs_sub r r₀
        linarith
      have hmem : x + r • (ω : EuclideanSpace ℝ (Fin d)) ∈ closedBall x (|r₀| + 1) := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hω, mul_one,
          Real.norm_eq_abs]
        exact hrle
      exact hM _ hmem
    · refine Filter.Eventually.of_forall fun ω => ?_
      have hc : Continuous (fun r : ℝ => u (x + r • (ω : EuclideanSpace ℝ (Fin d)))) := by
        fun_prop
      exact hc.continuousAt
  have heq : (fun r : ℝ => sphereAverage x r u)
      = fun r => ((sphereMeasure d).real Set.univ)⁻¹ • ∫ ω,
          u (x + r • (ω : EuclideanSpace ℝ (Fin d))) ∂(sphereMeasure d) := by
    funext r; rw [sphereAverage_def, average_eq]
  rw [heq]
  exact hintCont.const_smul (((sphereMeasure d).real Set.univ)⁻¹)

/-- **Continuity in the radius.**  For continuous `u`, the spherical average is
continuous in `r`. -/
theorem continuous_sphereAverage [NeZero d] {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (huc : Continuous u) (x : EuclideanSpace ℝ (Fin d)) :
    Continuous (fun r : ℝ => sphereAverage x r u) :=
  continuous_iff_continuousAt.mpr fun r₀ => continuousAt_sphereAverage huc x r₀

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

-- ==== the derivative of the sphere average ====
open scoped Real
open MeasureTheory Metric

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-- **Radial derivative of the spherical average.**  For a `C¹` function `u`, the spherical average
`r ↦ sphereAverage x r u` is differentiable at every `r₀`, with derivative the spherical average of
the radial directional derivative `ω ↦ ⟨∇u(x + r₀ ω), ω⟩`.

This is proved by differentiation under the integral sign, with the local gradient bound coming from
continuity of `fderiv u` on the compact ball `closedBall x (|r₀| + 1)`.  It is the half of the
mean-value property that does *not* need the divergence theorem. -/
theorem hasDerivAt_sphereAverage [NeZero d] {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : ContDiff ℝ 1 u) (x : EuclideanSpace ℝ (Fin d)) (r₀ : ℝ) :
    HasDerivAt (fun r => sphereAverage x r u)
      (((sphereMeasure d).real Set.univ)⁻¹ •
        ∫ ω, fderiv ℝ u (x + r₀ • (ω : EuclideanSpace ℝ (Fin d)))
          (ω : EuclideanSpace ℝ (Fin d)) ∂(sphereMeasure d)) r₀ := by
  classical
  set μ := sphereMeasure d with hμ
  -- The integrand and its `r`-derivative.
  set F : ℝ → sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ :=
    fun r ω => u (x + r • (ω : EuclideanSpace ℝ (Fin d))) with hF
  set F' : ℝ → sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ :=
    fun r ω => fderiv ℝ u (x + r • (ω : EuclideanSpace ℝ (Fin d)))
      (ω : EuclideanSpace ℝ (Fin d)) with hF'
  have hderiv := hu.differentiable (by norm_num)
  have hcont_fderiv : Continuous (fun y => fderiv ℝ u y) := hu.continuous_fderiv (by norm_num)
  -- Local gradient bound on the compact ball.
  obtain ⟨M, hM⟩ := (isCompact_closedBall x (|r₀| + 1)).exists_bound_of_continuousOn
    (hcont_fderiv.continuousOn)
  -- For `r` in `ball r₀ 1` and `ω` on the sphere, `x + r • ω ∈ closedBall x (|r₀| + 1)`.
  have hmem : ∀ r ∈ ball r₀ 1, ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      x + r • (ω : EuclideanSpace ℝ (Fin d)) ∈ closedBall x (|r₀| + 1) := by
    intro r hr ω
    have hω : ‖(ω : EuclideanSpace ℝ (Fin d))‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    have hrle : |r| ≤ |r₀| + 1 := by
      have hlt : |r - r₀| < 1 := by
        have := Metric.mem_ball.mp hr; rwa [Real.dist_eq] at this
      have := abs_sub_abs_le_abs_sub r r₀
      linarith
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_eq_abs]
    exact hrle
  -- Continuity of `ω ↦ x + r • ω` for fixed `r`.
  have hgcont : ∀ r : ℝ, Continuous
      (fun ω : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        x + r • (ω : EuclideanSpace ℝ (Fin d))) := fun r => by fun_prop
  -- The five hypotheses of `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (with `ε = 1`).
  have hF_meas : ∀ᶠ r in nhds r₀, AEStronglyMeasurable (F r) μ :=
    Filter.Eventually.of_forall fun r => (hu.continuous.comp (hgcont r)).aestronglyMeasurable
  have hF_int : Integrable (F r₀) μ := by
    obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall x (|r₀| + 1)).exists_bound_of_continuousOn
      hu.continuous.continuousOn
    refine Integrable.mono' (integrable_const M₀)
      (hu.continuous.comp (hgcont r₀)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    exact hM₀ _ (hmem r₀ (mem_ball_self one_pos) ω)
  have hF'_meas : AEStronglyMeasurable (F' r₀) μ := by
    have hc : Continuous (fun ω : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        fderiv ℝ u (x + r₀ • (ω : EuclideanSpace ℝ (Fin d)))
          (ω : EuclideanSpace ℝ (Fin d))) := by fun_prop
    exact hc.aestronglyMeasurable
  have h_bound : ∀ᵐ ω ∂μ, ∀ r ∈ ball r₀ 1, ‖F' r ω‖ ≤ M := by
    refine Filter.Eventually.of_forall fun ω r hr => ?_
    have hω : ‖(ω : EuclideanSpace ℝ (Fin d))‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    calc ‖F' r ω‖
        ≤ ‖fderiv ℝ u (x + r • (ω : EuclideanSpace ℝ (Fin d)))‖
            * ‖(ω : EuclideanSpace ℝ (Fin d))‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ u (x + r • (ω : EuclideanSpace ℝ (Fin d)))‖ := by rw [hω, mul_one]
      _ ≤ M := hM _ (hmem r hr ω)
  have h_diff : ∀ᵐ ω ∂μ, ∀ r ∈ ball r₀ 1, HasDerivAt (fun r => F r ω) (F' r ω) r := by
    refine Filter.Eventually.of_forall fun ω r _ => ?_
    have hg : HasDerivAt (fun r : ℝ => x + r • (ω : EuclideanSpace ℝ (Fin d)))
        ((ω : EuclideanSpace ℝ (Fin d))) r := by
      simpa using (((hasDerivAt_id r).smul_const
        (ω : EuclideanSpace ℝ (Fin d))).const_add x)
    exact (hderiv (x + r • (ω : EuclideanSpace ℝ (Fin d)))).hasFDerivAt.comp_hasDerivAt r hg
  -- Differentiation under the integral sign.
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (bound := fun _ => M)
    (F := F) (F' := F') (x₀ := r₀) (Metric.ball_mem_nhds r₀ one_pos) hF_meas hF_int hF'_meas
    h_bound (integrable_const M) h_diff
  -- Repackage as the derivative of the (constant-scaled) average.
  have heq : (fun r : ℝ => sphereAverage x r u)
      = fun r => ((sphereMeasure d).real Set.univ)⁻¹ • ∫ ω, F r ω ∂μ := by
    funext r; rw [sphereAverage_def, average_eq]
  rw [heq]
  exact (hkey.2).const_smul (((sphereMeasure d).real Set.univ)⁻¹)

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

-- ==== the mean value property ====
open scoped Real Topology
open MeasureTheory Metric Filter Set

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-- The average radial flux of `∇u` over the unit sphere at radius `r` about `x`:
`∫_S ⟨∇u(x + r ω), ω⟩ dσ(ω)`, written with `fderiv`.  This is exactly the integral appearing in the
radial derivative `hasDerivAt_sphereAverage`; its vanishing for harmonic `u` is the classical
divergence-theorem input to the mean value property. -/
def sphereFlux (x : EuclideanSpace ℝ (Fin d)) (r : ℝ)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  ∫ ω, fderiv ℝ u (x + r • (ω : EuclideanSpace ℝ (Fin d)))
    (ω : EuclideanSpace ℝ (Fin d)) ∂(sphereMeasure d)

theorem sphereFlux_def (x : EuclideanSpace ℝ (Fin d)) (r : ℝ)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    sphereFlux x r u = ∫ ω, fderiv ℝ u (x + r • (ω : EuclideanSpace ℝ (Fin d)))
      (ω : EuclideanSpace ℝ (Fin d)) ∂(sphereMeasure d) := rfl

/-- **Sphere average is constant on `(0, R)` under flux vanishing.**  If `u` is `C¹` and the average
radial flux `sphereFlux x r u` vanishes for every `r ∈ (0, R)`, then the spherical average is
constant across that radius range: for `0 < a ≤ b < R`, `sphereAverage x a u = sphereAverage x b u`.

The derivative of `r ↦ sphereAverage x r u` is `‖S‖⁻¹ • sphereFlux x r u`
(`hasDerivAt_sphereAverage`),
so the hypothesis makes it vanish on `(0, R)`; `constant_of_has_deriv_right_zero` on `[a, b]`
concludes constancy. -/
theorem sphereAverage_const_of_flux_zero [NeZero d] {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : ContDiff ℝ 1 u) (x : EuclideanSpace ℝ (Fin d)) {R : ℝ}
    (hflux : ∀ r ∈ Ioo (0 : ℝ) R, sphereFlux x r u = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < R) :
    sphereAverage x a u = sphereAverage x b u := by
  set g : ℝ → ℝ := fun r => sphereAverage x r u with hg
  have hcont : ContinuousOn g (Icc a b) :=
    (continuous_sphereAverage hu.continuous x).continuousOn
  have hderiv : ∀ y ∈ Ico a b, HasDerivWithinAt g 0 (Ici y) y := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    have hyR : y < R := hy.2.trans hb
    have hd0 := hasDerivAt_sphereAverage hu x y
    have hfy : (∫ ω, fderiv ℝ u (x + y • (ω : EuclideanSpace ℝ (Fin d)))
        (ω : EuclideanSpace ℝ (Fin d)) ∂(sphereMeasure d)) = 0 := hflux y ⟨hy0, hyR⟩
    rw [hfy, smul_zero] at hd0
    exact hd0.hasDerivWithinAt
  have := constant_of_has_deriv_right_zero hcont hderiv b (right_mem_Icc.2 hab)
  exact this.symm

/-- **Spherical mean value property, modulo flux vanishing.**  If `u` is `C¹` and the average radial
flux vanishes on `(0, R)`, then the spherical average equals the center value at every radius in
`[0, R)`:  `sphereAverage x r u = u x`.

The extension of constancy from `(0, R)` down to the center `r = 0` uses
continuity of the average in the radius. -/
theorem sphereAverage_eq_center_of_flux_zero [NeZero d] {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : ContDiff ℝ 1 u) (x : EuclideanSpace ℝ (Fin d)) {R : ℝ}
    (hflux : ∀ r ∈ Ioo (0 : ℝ) R, sphereFlux x r u = 0) :
    ∀ r ∈ Ico (0 : ℝ) R, sphereAverage x r u = u x := by
  set g : ℝ → ℝ := fun r => sphereAverage x r u with hg
  rintro r ⟨hr0, hrR⟩
  rcases eq_or_lt_of_le hr0 with hr | hr
  · -- `r = 0`: point evaluation at the center.
    simp only [← hr, sphereAverage_zero]
  · -- `0 < r`: `g` is constant on `(0, R)`, and `g → g 0 = u x` as the radius shrinks to `0`.
    have hconst : g r = g 0 := by
      -- `g` agrees with the constant `g r` on the punctured right neighborhood `(0, r)`.
      have hev : g =ᶠ[𝓝[>] (0 : ℝ)] fun _ => g r := by
        have hmem : Ioo (0 : ℝ) r ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hr
        filter_upwards [hmem] with a ha
        exact sphereAverage_const_of_flux_zero hu x hflux ha.1 (le_of_lt ha.2) hrR
      have hcA : ContinuousAt g 0 := (continuous_sphereAverage hu.continuous x).continuousAt
      have h0 : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) := hcA.mono_left nhdsWithin_le_nhds
      have hrlim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g r)) :=
        Tendsto.congr' hev.symm tendsto_const_nhds
      exact tendsto_nhds_unique hrlim h0
    calc g r = g 0 := hconst
      _ = u x := by simp only [hg, sphereAverage_zero]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
