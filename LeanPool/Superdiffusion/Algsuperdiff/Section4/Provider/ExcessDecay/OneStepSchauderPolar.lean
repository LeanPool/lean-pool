/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderSphere
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# OneStepSchauderPolar

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Polar decomposition and continuity of the spherical flux

Two ingredients of the flux-vanishing crux behind the mean value property:

* the **polar bridge** — a ball integral against Lebesgue measure written as an
  iterated radius/sphere integral, which is what turns the flux identity into
  an identity about a one-variable function of the radius;
* **continuity of the spherical flux** in the radius, needed before the
  fundamental theorem of calculus can be applied to it.
-/

-- ==== the polar-coordinates bridge ====
open scoped Real ENNReal NNReal
open MeasureTheory Metric Set

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **Reconstruction of a nonzero point from its polar coordinates.**  For `z ≠ 0`, scaling the
unit-sphere direction `(homeomorphUnitSphereProd 𝔼 z).1` by the radius
`(homeomorphUnitSphereProd 𝔼 z).2` recovers `z`. -/
private theorem smul_homeomorphUnitSphereProd_eq (z : ({0}ᶜ : Set 𝔼)) :
    ((homeomorphUnitSphereProd 𝔼 z).2 : ℝ) • ((homeomorphUnitSphereProd 𝔼 z).1 : 𝔼)
      = (z : 𝔼) := by
  have h := (homeomorphUnitSphereProd 𝔼).symm_apply_apply z
  have h2 := congrArg (fun w : ({0}ᶜ : Set 𝔼) => (w : 𝔼)) h
  rw [homeomorphUnitSphereProd_symm_apply_coe] at h2
  exact h2

/-- **The general polar-coordinate bridge.**  For an integrable scalar function `G` on
`EuclideanSpace ℝ (Fin d)` (`d ≥ 1`),
  `∫ z, G z = ∫ r in (0, ∞), r ^ (d - 1) • (∫ ω, G (r • ω) dσ(ω))`,

the disintegration of Lebesgue measure into the surface measure `sphereMeasure d` on the unit sphere
and the radial density `r ^ (d - 1) dr`. -/
theorem integral_eq_integral_Ioi_sphere [NeZero d] {G : 𝔼 → ℝ} (hG : Integrable G) :
    ∫ z, G z
      = ∫ r in Ioi (0 : ℝ), r ^ (d - 1) • ∫ ω, G (r • (ω : 𝔼)) ∂(sphereMeasure d) := by
  classical
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have : Nontrivial 𝔼 := inferInstance
  have hdim : Module.finrank ℝ 𝔼 = d := finrank_euclideanSpace_fin
  have hmp := (volume : Measure 𝔼).measurePreserving_homeomorphUnitSphereProd
  -- The "profile" integrand pulled through the polar homeomorphism.
  set H : sphere (0 : 𝔼) 1 × Ioi (0 : ℝ) → ℝ := fun p => G ((p.2 : ℝ) • (p.1 : 𝔼)) with hH
  -- `H ∘ homeomorphUnitSphereProd` reconstructs `G` off the origin.
  have hHcomp : (fun z : ({0}ᶜ : Set 𝔼) => H (homeomorphUnitSphereProd 𝔼 z))
      = fun z : ({0}ᶜ : Set 𝔼) => G (z : 𝔼) := by
    funext z
    simp only [hH]
    rw [smul_homeomorphUnitSphereProd_eq z]
  -- Integrability of `H` on the product measure.
  have hHint : Integrable H
      ((volume : Measure 𝔼).toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ 𝔼 - 1))) := by
    rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)]
    have hcomp : (H ∘ (homeomorphUnitSphereProd 𝔼)) = fun z : ({0}ᶜ : Set 𝔼) => G (z : 𝔼) := hHcomp
    rw [hcomp]
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0 : 𝔼)).compl).mp
      hG.integrableOn
  -- Step 1: restrict to the complement of the origin as a subtype integral.
  have step1 : (∫ z, G z)
      = ∫ z : ({0}ᶜ : Set 𝔼), G (z : 𝔼) ∂(Measure.comap Subtype.val volume) := by
    rw [integral_subtype_comap (measurableSet_singleton (0 : 𝔼)).compl (fun z => G z),
      restrict_compl_singleton]
  -- Step 2: transport to the product measure via the polar homeomorphism.
  have step2 : (∫ z : ({0}ᶜ : Set 𝔼), G (z : 𝔼) ∂(Measure.comap Subtype.val volume))
      = ∫ p, H p ∂((volume : Measure 𝔼).toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ 𝔼 - 1))) := by
    rw [← hmp.integral_comp (Homeomorph.measurableEmbedding _) H, hHcomp]
  -- Step 3: Fubini — integrate the radius outside.
  have step3 : (∫ p, H p ∂((volume : Measure 𝔼).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ 𝔼 - 1))))
      = ∫ r, (∫ ω, H (ω, r) ∂(sphereMeasure d))
          ∂(Measure.volumeIoiPow (Module.finrank ℝ 𝔼 - 1)) :=
    integral_prod_symm H hHint
  -- Step 4: unfold the `volumeIoiPow` density into Lebesgue measure on `(0, ∞)`.
  have step4 : (∫ r, (∫ ω, H (ω, r) ∂(sphereMeasure d))
        ∂(Measure.volumeIoiPow (Module.finrank ℝ 𝔼 - 1)))
      = ∫ r in Ioi (0 : ℝ), r ^ (d - 1) • ∫ ω, G (r • (ω : 𝔼)) ∂(sphereMeasure d) := by
    simp only [hH]
    simp only [Measure.volumeIoiPow, ENNReal.ofReal]
    rw [integral_withDensity_eq_integral_smul
      (show Measurable fun r : Ioi (0 : ℝ) =>
          Real.toNNReal ((r : ℝ) ^ (Module.finrank ℝ 𝔼 - 1)) from
        (measurable_subtype_coe.pow_const _).real_toNNReal)]
    rw [integral_subtype_comap measurableSet_Ioi
      (fun t : ℝ => Real.toNNReal (t ^ (Module.finrank ℝ 𝔼 - 1)) •
        ∫ ω, G (t • (ω : 𝔼)) ∂(sphereMeasure d))]
    rw [hdim]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt ht) _), smul_eq_mul]
  rw [step1, step2, step3, step4]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

-- ==== continuity of the flux ====
open scoped Real
open MeasureTheory Metric

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-- **Continuity of the radial flux (at a point).**  For `C¹` `u`, the average radial flux
`r ↦ sphereFlux x r u` is continuous at every `r₀`. -/
theorem continuousAt_sphereFlux {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : ContDiff ℝ 1 u) (x : EuclideanSpace ℝ (Fin d)) (r₀ : ℝ) :
    ContinuousAt (fun r : ℝ => sphereFlux x r u) r₀ := by
  set μ := sphereMeasure d with hμ
  have hcont_fderiv : Continuous (fun y => fderiv ℝ u y) := hu.continuous_fderiv (by simp)
  -- The integrand `F r ω = ⟨∇u(x + r ω), ω⟩`.
  set F : ℝ → sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ :=
    fun r ω => fderiv ℝ u (x + r • (ω : EuclideanSpace ℝ (Fin d)))
      (ω : EuclideanSpace ℝ (Fin d)) with hF
  -- Continuity of `ω ↦ x + r • ω` for fixed `r`.
  have hgcont : ∀ r : ℝ, Continuous
      (fun ω : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        x + r • (ω : EuclideanSpace ℝ (Fin d))) :=
    fun r => continuous_const.add
      ((continuous_const : Continuous (fun _ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 => r)).smul
        (continuous_subtype_val : Continuous (fun ω : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
          (ω : EuclideanSpace ℝ (Fin d)))))
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
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
  · -- a.e.-strong measurability of `F r` for `r` near `r₀`
    refine Filter.Eventually.of_forall fun r => ?_
    exact ((hcont_fderiv.comp (hgcont r)).clm_apply continuous_subtype_val).aestronglyMeasurable
  · -- domination
    filter_upwards [Metric.ball_mem_nhds r₀ one_pos] with r hr
    refine Filter.Eventually.of_forall fun ω => ?_
    have hω : ‖(ω : EuclideanSpace ℝ (Fin d))‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    calc ‖F r ω‖
        ≤ ‖fderiv ℝ u (x + r • (ω : EuclideanSpace ℝ (Fin d)))‖
            * ‖(ω : EuclideanSpace ℝ (Fin d))‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ u (x + r • (ω : EuclideanSpace ℝ (Fin d)))‖ := by rw [hω, mul_one]
      _ ≤ M := hM _ (hmem r hr ω)
  · -- continuity in `r` for a.e.
    refine Filter.Eventually.of_forall fun ω => ?_
    have hg : Continuous (fun r : ℝ => x + r • (ω : EuclideanSpace ℝ (Fin d))) :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact ((hcont_fderiv.comp hg).clm_apply continuous_const).continuousAt

/-- **Continuity of the radial flux.**  For `C¹` `u`, the average radial flux is
continuous in `r`. -/
theorem continuous_sphereFlux [NeZero d] {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : ContDiff ℝ 1 u) (x : EuclideanSpace ℝ (Fin d)) :
    Continuous (fun r : ℝ => sphereFlux x r u) :=
  continuous_iff_continuousAt.mpr fun r₀ => continuousAt_sphereFlux hu x r₀

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

