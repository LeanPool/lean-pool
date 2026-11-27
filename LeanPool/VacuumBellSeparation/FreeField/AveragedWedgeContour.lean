/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexTestWedgeContour
public import LeanPool.VacuumBellSeparation.FreeField.ComplexSourceContinuity
public import LeanPool.VacuumBellSeparation.FreeField.EuclideanWedgeContainment
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Genuine integrable averages of the literal Lorentz contours

Each inner integral is integrable by the actual maximal graph and its
AE contour. Joint continuity gives measurability of the parameter
integral; the source-weight bound gives integrability and the probability
average bound. Only the physical containing geometry is required of the
family, with no averaged estimate assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

/-- Complex test contour integrand. -/
noncomputable def complexTestContourIntegrand (m ℓ θ : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (u v : TimeZeroSource)
    (p : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Real.exp (-2 * ℓ * dispersion m p * Real.sin θ) *
    ‖complexSourceWave u (complexifiedSpacetimeMap Λ
      (complexShellBoost m ((θ : ℂ) * Complex.I) p)) +
      Complex.I * complexSourceWave v (complexifiedSpacetimeMap Λ
      (complexShellBoost m ((θ : ℂ) * Complex.I) p))‖ ^ 2

theorem complexTestContourIntegrand_nonneg (m ℓ θ : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (u v : TimeZeroSource) (p : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ complexTestContourIntegrand m ℓ θ Λ u v p :=
  mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

theorem continuous_complexTestContourIntegrand
    {A : Type*} [TopologicalSpace A] (Λ : A → Spacetime ≃L[ℝ] Spacetime)
    (hΛ : ∀ x : Spacetime, Continuous fun a => Λ a x)
    (m ℓ θ : ℝ) (u v : TimeZeroSource) :
    Continuous (fun q : A × EuclideanSpace ℝ (Fin 3) =>
      complexTestContourIntegrand m ℓ θ (Λ q.1) u v q.2) := by
  have hu := continuous_lorentzContourWave Λ hΛ m θ u
  have hv := continuous_lorentzContourWave Λ hΛ m θ v
  have hw := (continuous_dispersion m).comp (continuous_snd : Continuous
    (Prod.snd : A × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)))
  unfold complexTestContourIntegrand
  exact (Real.continuous_exp.comp ((continuous_const.mul hw).mul continuous_const)).mul
    ((hu.add (continuous_const.mul hv)).norm.pow 2)

theorem integrable_complexTestContour
    {m : ℝ} (hm : 0 < m) (ℓ : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ) (hfuture : IsOrthochronousMap Λ)
    {U : Set (EuclideanSpace ℝ (Fin 3))} {R : ℝ} (hR : 0 < R)
    (hU : U ⊆ Metric.ball 0 R)
    (hregion : doubleCone (0, (0 : EuclideanSpace ℝ (Fin 3))) R ⊆ Λ '' leftWedge ℓ)
    (u v : SourceTestSpace hm U) {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) :
    Integrable (complexTestContourIntegrand m ℓ (2 * Real.pi * c) Λ u.1 v.1)
      (oneParticleMeasure m) := by
  obtain ⟨F, hF, hFu⟩ := exists_spacetimeSourceL2_of_timeZeroSource_ball hm hR 0 u.1
    (u.2.1.trans hU) (u.2.2.trans hU)
  obtain ⟨G, hG, hGv⟩ := exists_spacetimeSourceL2_of_timeZeroSource_ball hm hR 0 v.1
    (v.2.1.trans hU) (v.2.2.trans hU)
  obtain ⟨χ, _, haeχ⟩ := timeZero_lorentzWedge_graph_ae hm ℓ Λ hΛ hfuture
    F u.1 hFu (hF.trans hregion) hc hc2
  obtain ⟨ψ, _, haeψ⟩ := timeZero_lorentzWedge_graph_ae hm ℓ Λ hΛ hfuture
    G v.1 hGv (hG.trans hregion) hc hc2
  have hu := MemLp.ae_eq haeχ (Lp.memLp _)
  have hv := MemLp.ae_eq haeψ (Lp.memLp _)
  let q := fun p => complexifiedSpacetimeMap Λ
    (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p)
  have hmem : MemLp (fun p => wedgeContourPhase m ℓ (2 * Real.pi * c) p *
      (complexSourceWave u.1 (q p) + Complex.I * complexSourceWave v.1 (q p)))
      2 (oneParticleMeasure m) := by
    convert hu.add (hv.const_smul Complex.I) using 1
    funext p
    change _ = _ + Complex.I * _
    ring
  have hi := (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  apply hi.congr
  exact Filter.Eventually.of_forall fun p => by
    change ‖wedgeContourPhase m ℓ (2 * Real.pi * c) p *
      (complexSourceWave u.1 (q p) + Complex.I * complexSourceWave v.1 (q p))‖ ^ 2 =
        Real.exp (-2 * ℓ * dispersion m p * Real.sin (2 * Real.pi * c)) *
          ‖complexSourceWave u.1 (q p) + Complex.I * complexSourceWave v.1 (q p)‖ ^ 2
    rw [norm_mul, mul_pow, norm_wedgeContourPhase_sq]

/-- Equation (5.2) for every complexified compact source and genuine
probability average, together with integrability of the outer integral. -/
theorem averaged_complexTestContour_le_sourceWeight
    {A : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
 (ν : Measure A) [IsProbabilityMeasure ν]
    {m : ℝ} (hm : 0 < m) (ℓ : ℝ)
    (Λ : A → Spacetime ≃L[ℝ] Spacetime)
    (hΛ : ∀ a, IsLorentzMap (Λ a)) (hfuture : ∀ a, IsOrthochronousMap (Λ a))
    (hcont : ∀ x : Spacetime, Continuous fun a => Λ a x)
    (hbound : ∀ a, Real.sqrt 2 * spacetimeEuclideanOperatorNorm (Λ a).symm < ℓ)
    {U : Set (EuclideanSpace ℝ (Fin 3))} {R : ℝ} (hR : 0 < R)
    (hU : U ⊆ Metric.ball 0 R) (u v : SourceTestSpace hm U)
    {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    Integrable (fun a => ∫ p,
      complexTestContourIntegrand m (ℓ * R) (2 * Real.pi * c) (Λ a) u.1 v.1 p
      ∂oneParticleMeasure m) ν ∧
    (∫ a, ∫ p, complexTestContourIntegrand m (ℓ * R) (2 * Real.pi * c) (Λ a) u.1 v.1 p
      ∂oneParticleMeasure m ∂ν) ≤
      ‖sourceModularWeight hm U c
        (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U) +
          Complex.I • Gaussian.HilbertComplexification.ofReal (v : SourceHilbert hm U))‖ ^ 2 := by
  let : SigmaFinite (oneParticleMeasure m) := by
    unfold oneParticleMeasure
    infer_instance
  let B := ‖sourceModularWeight hm U c
    (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U) +
      Complex.I • Gaussian.HilbertComplexification.ofReal (v : SourceHilbert hm U))‖ ^ 2
  let f := fun a => ∫ p,
    complexTestContourIntegrand m (ℓ * R) (2 * Real.pi * c) (Λ a) u.1 v.1 p
    ∂oneParticleMeasure m
  have hmeas : StronglyMeasurable f :=
    (continuous_complexTestContourIntegrand Λ hcont m (ℓ * R) (2 * Real.pi * c)
      u.1 v.1).stronglyMeasurable.integral_prod_right'
  have hnonneg (a : A) : 0 ≤ f a := integral_nonneg
    (complexTestContourIntegrand_nonneg m (ℓ * R) (2 * Real.pi * c) (Λ a) u.1 v.1)
  have hle (a : A) : f a ≤ B :=
    complexTest_lorentzContour_le_sourceWeight hm (ℓ * R) (Λ a) (hΛ a) (hfuture a)
      hR hU (doubleCone_subset_transformed_leftWedge (Λ a) hR (hbound a)) u v hc hc2
  have hint : Integrable f ν := (integrable_const B).mono_nonneg hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hnonneg) (Filter.Eventually.of_forall hle)
  refine ⟨hint, ?_⟩
  have h := integral_mono hint (integrable_const B) hle
  simpa only [integral_const, probReal_univ, one_smul] using h

end VacuumBellSeparation
