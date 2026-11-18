/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus
public import LeanPool.KLS.FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Kernel
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Integration by parts against smooth compactly supported tests

Source: Blueprint `lem:covariance-core-closure`, the integration by parts in the closability
argument. Read `integral_fderiv_apply_eq_zero`, `integral_mul_fderiv_apply`, then
`integral_mul_inner_gradient`.

For a Haar measure `m` on a finite-dimensional real Hilbert space, the integral of a directional
derivative of a compactly supported `C¹` function vanishes: translating the function does not
change its integral, and differentiating under the integral sign gives the claim. Combined with
the product rule this is integration by parts for smooth functions. For a globally Lipschitz `g`
the identity

`  ∫ φ x * ⟪∇g x, w⟫ dm = -∫ g x * (Dφ x) w dm`

for every `φ ∈ C_c^∞(V)` and `w : V` follows by mollifying `g`: the mollified gradients converge
to `∇g` at every differentiability point, hence almost everywhere by Rademacher's theorem, and
are uniformly bounded by the Lipschitz constant, while the mollified functions converge
uniformly to `g`. Here `∇g` is Mathlib's canonical gradient, zero where `g` is not differentiable;
the identity says exactly that the almost-everywhere gradient of a Lipschitz function is its
distributional gradient.

No measure other than Haar measure enters, and nothing is asserted about closability, densities
or Poincaré inequalities.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff

namespace FunctionalInequalities.Energy.Euclidean

open FunctionalInequalities.Analysis.BakryEmery (continuous_gradient_of_contDiff)

open LipschitzApproximation

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]


omit [CompleteSpace V] in
/-- The derivative of a compactly supported `C¹` function is globally bounded. -/
theorem exists_bound_fderiv_of_hasCompactSupport {u : V → ℝ} (hu : ContDiff ℝ 1 u)
    (hsupp : HasCompactSupport u) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ u x‖ ≤ M := by
  obtain ⟨C, hC⟩ :=
    hsupp.exists_bound_of_continuousOn (hu.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
  by_cases hx : x ∈ tsupport u
  · exact (hC x hx).trans (le_max_left _ _)
  · have h0 : fderiv ℝ u x = 0 := by
      by_contra hne
      exact hx (support_fderiv_subset ℝ (Function.mem_support.mpr hne))
    rw [h0, norm_zero]
    exact le_max_right _ _

section HaarIntegration

variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] (m : Measure V) [m.IsAddHaarMeasure]

omit [SecondCountableTopology V] in
omit [CompleteSpace V] in
/-- The integral of a directional derivative of a compactly supported `C¹` function against a
Haar measure vanishes: translation invariance and differentiation under the integral sign. -/
theorem integral_fderiv_apply_eq_zero {u : V → ℝ} (hu : ContDiff ℝ 1 u)
    (hsupp : HasCompactSupport u) (w : V) : ∫ x, fderiv ℝ u x w ∂m = 0 := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_fderiv_of_hasCompactSupport hu hsupp
  set K' : Set V := Metric.cthickening ‖w‖ (tsupport u) with hK'
  have hK'c : IsCompact K' := hsupp.cthickening
  have hdiff : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hderiv : ∀ x t, HasDerivAt (fun s : ℝ ↦ u (s • w + x)) (fderiv ℝ u (t • w + x) w) t := by
    intro x t
    have h1 : HasDerivAt (fun s : ℝ ↦ s • w + x) w t := by
      simpa using ((hasDerivAt_id t).smul_const w).add_const x
    exact (hdiff _).hasFDerivAt.comp_hasDerivAt t h1
  have hcont : ∀ t : ℝ, Continuous fun x ↦ u (t • w + x) :=
    fun t ↦ hu.continuous.comp (continuous_const.add continuous_id)
  have hF0 : (fun x ↦ u ((0 : ℝ) • w + x)) = u := by
    funext x
    simp
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := m)
    (F := fun t x ↦ u (t • w + x)) (F' := fun t x ↦ fderiv ℝ u (t • w + x) w) (x₀ := (0 : ℝ))
    (bound := K'.indicator fun _ ↦ M * ‖w‖) (s := Metric.ball 0 1)
    (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t ↦ (hcont t).aestronglyMeasurable)
    (by
      rw [hF0]
      exact hu.continuous.integrable_of_hasCompactSupport hsupp)
    (((hu.continuous_fderiv one_ne_zero).comp (continuous_const.add continuous_id)).clm_apply
      continuous_const).aestronglyMeasurable
    (Eventually.of_forall fun x t ht ↦ by
      by_cases hx : x ∈ K'
      · rw [Set.indicator_of_mem hx]
        calc ‖fderiv ℝ u (t • w + x) w‖ ≤ ‖fderiv ℝ u (t • w + x)‖ * ‖w‖ :=
              (fderiv ℝ u (t • w + x)).le_opNorm w
          _ ≤ M * ‖w‖ := by gcongr; exact hM _
      · rw [Set.indicator_of_notMem hx]
        have hy : t • w + x ∉ tsupport u := by
          intro hy
          apply hx
          refine Metric.mem_cthickening_of_dist_le x (t • w + x) ‖w‖ _ hy ?_
          rw [dist_eq_norm, sub_add_cancel_right, norm_neg, norm_smul, Real.norm_eq_abs]
          have ht' : |t| ≤ 1 := by
            have := Metric.mem_ball.mp ht
            rw [dist_zero_right, Real.norm_eq_abs] at this
            exact this.le
          calc |t| * ‖w‖ ≤ 1 * ‖w‖ := by gcongr
            _ = ‖w‖ := one_mul _
        have h0 : fderiv ℝ u (t • w + x) = 0 := by
          by_contra hne
          exact hy (support_fderiv_subset ℝ (Function.mem_support.mpr hne))
        simp [h0])
    ((integrable_indicator_iff hK'c.measurableSet).mpr
      (integrableOn_const hK'c.measure_lt_top.ne))
    (Eventually.of_forall fun x t _ ↦ hderiv x t)
  have hconst : (fun t : ℝ ↦ ∫ x, u (t • w + x) ∂m) = fun _ ↦ ∫ x, u x ∂m :=
    funext fun t ↦ integral_add_left_eq_self u (t • w)
  have h2 := key.2
  rw [hconst] at h2
  have h3 : (∫ x, fderiv ℝ u ((0 : ℝ) • w + x) w ∂m) = 0 :=
    h2.unique (hasDerivAt_const _ _)
  simpa using h3

omit [SecondCountableTopology V] in
omit [CompleteSpace V] in
/-- Integration by parts for a smooth function against a smooth compactly supported test. -/
theorem integral_mul_fderiv_apply {φ ψ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (hψ : ContDiff ℝ ∞ ψ) (w : V) :
    ∫ x, φ x * fderiv ℝ ψ x w ∂m = -∫ x, ψ x * fderiv ℝ φ x w ∂m := by
  have hu : ContDiff ℝ 1 fun x ↦ ψ x * φ x := (hψ.mul hφ).of_le (mod_cast le_top)
  have hsupp : HasCompactSupport fun x ↦ ψ x * φ x := hφs.mul_left
  have h0 := integral_fderiv_apply_eq_zero m hu hsupp w
  have hprod : ∀ x, fderiv ℝ (fun x ↦ ψ x * φ x) x w =
      ψ x * fderiv ℝ φ x w + φ x * fderiv ℝ ψ x w := by
    intro x
    change (fderiv ℝ (ψ * φ) x) w = _
    rw [fderiv_mul (hψ.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
    simp [smul_eq_mul]
  have hφ' : HasCompactSupport fun x ↦ fderiv ℝ φ x w :=
    (hφs.fderiv ℝ).comp_left (g := fun L : V →L[ℝ] ℝ ↦ L w) (by simp)
  have hint₁ : Integrable (fun x ↦ ψ x * fderiv ℝ φ x w) m :=
    (hψ.continuous.mul ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const))
      |>.integrable_of_hasCompactSupport hφ'.mul_left
  have hint₂ : Integrable (fun x ↦ φ x * fderiv ℝ ψ x w) m :=
    (hφ.continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const))
      |>.integrable_of_hasCompactSupport hφs.mul_right
  simp_rw [hprod] at h0
  rw [integral_add hint₁ hint₂] at h0
  linarith

omit [SecondCountableTopology V] in
/-- Weak-derivative identity for a globally Lipschitz function: the almost-everywhere gradient
integrates against smooth compactly supported tests as a distributional gradient. -/
theorem integral_mul_inner_gradient {g : V → ℝ} {K : NNReal} (hg : LipschitzWith K g)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ) (w : V) :
    ∫ x, φ x * inner ℝ (gradient g x) w ∂m = -∫ x, g x * fderiv ℝ φ x w ∂m := by
  -- the identity for the mollified functions
  have hid :
    ∀ j,
      ∫ x, φ x * inner ℝ (gradient (mollify m (radius j) g) x) w ∂m =
        -∫ x, mollify m (radius j) g x * fderiv ℝ φ x w ∂m := by
    intro j
    simp_rw [inner_gradient_left]
    exact integral_mul_fderiv_apply m hφ hφs (contDiff_mollify m (radius_pos j) hg.continuous) w
  have hφ' : HasCompactSupport fun x ↦ fderiv ℝ φ x w :=
    (hφs.fderiv ℝ).comp_left (g := fun L : V →L[ℝ] ℝ ↦ L w) (by simp)
  have hφ'c : Continuous fun x ↦ fderiv ℝ φ x w :=
    (hφ.continuous_fderiv (by simp)).clm_apply
      continuous_const
  -- left-hand sides converge by dominated convergence
  have hL :
    Tendsto (fun j ↦ ∫ x, φ x * inner ℝ (gradient (mollify m (radius j) g) x) w ∂m) atTop
      (𝓝 (∫ x, φ x * inner ℝ (gradient g x) w ∂m)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖φ x‖ * (K * ‖w‖)) ?_ ?_ ?_ ?_
    · intro j
      exact
        (hφ.continuous.mul
            ((continuous_gradient_of_contDiff (contDiff_mollify m (radius_pos j) hg.continuous)
                  (by simp)).inner
              continuous_const)).aestronglyMeasurable
    · exact
        (hφ.continuous.norm.mul continuous_const).integrable_of_hasCompactSupport
          hφs.norm.mul_right
    · intro j
      refine Eventually.of_forall fun x ↦ ?_
      rw [norm_mul]
      gcongr
      calc
        ‖inner ℝ (gradient (mollify m (radius j) g) x) w‖ ≤
            ‖gradient (mollify m (radius j) g) x‖ * ‖w‖ :=
          norm_inner_le_norm _ _
        _ ≤ K * ‖w‖ := by
          gcongr
          exact norm_gradient_le_of_lipschitz (lipschitzWith_mollify m (radius_pos j) hg) x
    · filter_upwards [ae_differentiableAt_of_locallyLipschitz hg.locallyLipschitz m] with x hx
      exact
        tendsto_const_nhds.mul
          ((tendsto_gradient_mollify m hg.continuous hx radius_pos tendsto_radius).inner
            tendsto_const_nhds)
  -- right-hand sides converge by dominated convergence and uniform closeness
  have hR :
    Tendsto (fun j ↦ ∫ x, mollify m (radius j) g x * fderiv ℝ φ x w ∂m) atTop
      (𝓝 (∫ x, g x * fderiv ℝ φ x w ∂m)) := by
    refine
      tendsto_integral_of_dominated_convergence (fun x ↦ (‖g x‖ + K * 2) * ‖fderiv ℝ φ x w‖) ?_
        ?_ ?_ ?_
    · intro j
      exact ((continuous_mollify m (radius_pos j) hg.continuous).mul hφ'c).aestronglyMeasurable
    · exact
        ((hg.continuous.norm.add continuous_const).mul
            hφ'c.norm) |>.integrable_of_hasCompactSupport
          hφ'.norm.mul_left
    · intro j
      refine Eventually.of_forall fun x ↦ ?_
      rw [norm_mul]
      gcongr
      have hr : radius j ≤ 1 := by
        unfold radius
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      calc
        ‖mollify m (radius j) g x‖ ≤ ‖g x‖ + ‖mollify m (radius j) g x - g x‖ := by
          have := norm_add_le (g x) (mollify m (radius j) g x - g x)
          rwa [add_sub_cancel] at this
        _ ≤ ‖g x‖ + K * (2 * radius j) := by
          gcongr
          exact norm_mollify_sub_le m (radius_pos j) hg x
        _ ≤ ‖g x‖ + K * 2 := by
          gcongr
          linarith
    · refine Eventually.of_forall fun x ↦ ?_
      refine Tendsto.mul ?_ tendsto_const_nhds
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine
        squeeze_zero (fun j ↦ norm_nonneg _) (fun j ↦ norm_mollify_sub_le m (radius_pos j) hg x)
          ?_
      have : Tendsto (fun j ↦ (K : ℝ) * (2 * radius j)) atTop (𝓝 ((K : ℝ) * (2 * 0))) :=
        tendsto_const_nhds.mul (tendsto_const_nhds.mul tendsto_radius)
      simpa using this
  have hL' :
    Tendsto (fun j ↦ ∫ x, φ x * inner ℝ (gradient (mollify m (radius j) g) x) w ∂m) atTop
      (𝓝 (-∫ x, g x * fderiv ℝ φ x w ∂m)) :=
    hR.neg.congr fun j ↦ (hid j).symm
  exact tendsto_nhds_unique hL hL'

end HaarIntegration

end FunctionalInequalities.Energy.Euclidean
