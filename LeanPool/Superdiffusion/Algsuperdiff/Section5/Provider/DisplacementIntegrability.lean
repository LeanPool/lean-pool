/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.EarlyExitScaleMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.PthMomentProcess

/-!
# Integrability of the constructed displacement

The first result is adapted from the Apache-2.0 upstream module
`SuperdiffusionAudit/Support/SuperdiffusivityIntegrability.lean` at commit
`7f20476385d4af418f110303085ad0740c9eba46`. It uses the production confinement
tail directly, without the comparator's duplicate model vocabulary. The second
result makes finiteness of both Bochner observables in Theorem A explicit.
-/

public section

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form HCPolySupport MarkovProcess MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- Small coupling gives every norm moment of order at least one. -/
theorem exists_ae_integrable_streamProcess_norm_rpow
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gammaI : ℝ, 0 < gammaI ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gammaI →
      ∀ t : ℝ, 0 < t →
      ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
        letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
        letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
        ∀ p : ℝ, 1 ≤ p →
          Integrable (fun path : ContinuousPath (OnePoint (Vec d)) =>
            ‖onePointRetract (0 : Vec d) (path t.toNNReal)‖ ^ p)
            (streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))) := by
  obtain ⟨gammaI, Cscale, CSbar, Kbar, cbar, hgammaI, _hCscale, _hCSbar, _hKbar,
    hcbar, hcbar1, hlift⟩ :=
    measureReal_exitEvent_confinementScale_le_pow_of_threshold
      d hd cstar hcstar
  refine ⟨gammaI, hgammaI, ?_⟩
  intro M hcs hgamma t ht
  obtain ⟨S, K, L, c, CS, pS, _hK, _hKmin, _hc, _hc1, _hcbarle, _hL, _hSform,
    _hSmeas, _hSnn, _hCS, _hpS, _hCSle, _hKle, _hpSrange, _hSmom, _hconf, _hearly,
    _hdispk, _hdispR, htail⟩ := hlift M hcs hgamma t ht 1
  filter_upwards [htail] with omega homega
  let := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
  let := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
  intro p hp
  exact (integral_norm_onePointRetract_streamProcess_rpow_le_of_triadic_sq_tail
    M omega t.toNNReal
    (zpow_pos (by norm_num : (0 : ℝ) < 3) (confinementScale S L omega.1))
    hcbar hcbar1 hp homega).1

/-- The first and second displacement observables have finite Bochner integrals. -/
theorem exists_ae_integrable_streamProcess_displacement
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gammaI : ℝ, 0 < gammaI ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gammaI →
      ∀ t : ℝ, 0 < t →
      ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
        letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
        letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
        Integrable (fun path : ContinuousPath (OnePoint (Vec d)) =>
          onePointRetract (0 : Vec d) (path t.toNNReal))
          (streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))) ∧
        Integrable (fun path : ContinuousPath (OnePoint (Vec d)) =>
          vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal)))
          (streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))) := by
  obtain ⟨gammaI, hgammaI, hfinite⟩ :=
    exists_ae_integrable_streamProcess_norm_rpow d hd cstar hcstar
  refine ⟨gammaI, hgammaI, ?_⟩
  intro M hcs hgamma t ht
  filter_upwards [hfinite M hcs hgamma t ht] with omega homega
  let := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
  let := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
  let Q := streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))
  let X : ContinuousPath (OnePoint (Vec d)) → Vec d := fun path =>
    onePointRetract (0 : Vec d) (path t.toNNReal)
  have hmeas : Measurable X :=
    (measurable_onePointRetract (X := Vec d) 0).comp
      (ContinuousPath.measurable_coordinateProcess t.toNNReal)
  have hnorm : Integrable (fun path => ‖X path‖) Q := by
    simpa only [X, Q, Real.rpow_one] using homega 1 le_rfl
  have hsq : Integrable (fun path => ‖X path‖ ^ (2 : ℕ)) Q := by
    simpa only [X, Q, Real.rpow_two] using homega 2 (by norm_num)
  refine ⟨(integrable_norm_iff hmeas.aestronglyMeasurable).mp hnorm, ?_⟩
  have hcont : Continuous (vecNormSq (d := d)) := by
    unfold vecNormSq vecDot
    fun_prop
  apply (hsq.const_mul (d : ℝ)).mono' (hcont.measurable.comp hmeas).aestronglyMeasurable
  filter_upwards [] with path
  change ‖vecNormSq (X path)‖ ≤ (d : ℝ) * ‖X path‖ ^ (2 : ℕ)
  rw [Real.norm_of_nonneg (vecNormSq_nonneg _)]
  unfold vecNormSq vecDot
  calc
    ∑ i : Fin d, X path i * X path i ≤ ∑ _i : Fin d, ‖X path‖ ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hi : |X path i| ≤ ‖X path‖ := norm_le_pi_norm (X path) i
      calc
        X path i * X path i = |X path i| ^ (2 : ℕ) := by
          rw [pow_two, ← abs_mul, abs_mul_self]
        _ ≤ ‖X path‖ ^ (2 : ℕ) := pow_le_pow_left₀ (abs_nonneg _) hi 2
    _ = (d : ℝ) * ‖X path‖ ^ (2 : ℕ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end

end Algsuperdiff.Section5.Provider
