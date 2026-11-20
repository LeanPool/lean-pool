/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Independence survives almost-everywhere limits

If each random variable `X n` is independent of a σ-algebra `m` and `X n → Y` almost
everywhere, then `Y` is independent of `m`: for a set `A ∈ m` the laws of `Y` under `P|_A` and
under `P(A) • P` have the same integrals against bounded continuous functions, by dominated
convergence, hence coincide.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

namespace LevyStochCalc.Probability

variable {Ω 𝓧 : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [TopologicalSpace 𝓧] [MeasurableSpace 𝓧] [BorelSpace 𝓧] [HasOuterApproxClosed 𝓧]

omit [HasOuterApproxClosed 𝓧] in
/-- For `A ∈ m` and `X` independent of `m`, `∫_A f ∘ X = P(A) ∫ f ∘ X`. -/
lemma setIntegral_eq_measure_mul_of_indep (hm : m ≤ mΩ) {X : Ω → 𝓧}
    (hX : Measurable[mΩ] X) (hind : Indep m (MeasurableSpace.comap X inferInstance) P)
    {A : Set Ω} (hA : MeasurableSet[m] A) (f : 𝓧 →ᵇ ℝ) :
    ∫ ω in A, f (X ω) ∂P = (P A).toReal * ∫ ω, f (X ω) ∂P := by
  have hA' : MeasurableSet[mΩ] A := hm _ hA
  have hindf : IndepFun (A.indicator (1 : Ω → ℝ)) (fun ω => f (X ω)) P := by
    change Indep (MeasurableSpace.comap _ _) (MeasurableSpace.comap _ _) P
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hind ?_) ?_
    · have hmeas : Measurable[m] (A.indicator (1 : Ω → ℝ)) := by
        let := m
        exact measurable_const.indicator hA
      exact hmeas.comap_le
    · rw [show (fun ω => f (X ω)) = f ∘ X from rfl, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (f.continuous.measurable.comap_le)
  have hfX : Integrable (fun ω => f (X ω)) P :=
    Integrable.of_bound (f.continuous.measurable.comp hX).aestronglyMeasurable ‖f‖
      (ae_of_all _ fun ω => f.norm_coe_le_norm _)
  have h := hindf.integral_mul_eq_mul_integral
    ((integrable_const (1 : ℝ)).indicator hA').aestronglyMeasurable hfX.aestronglyMeasurable
  have hfun : (A.indicator (1 : Ω → ℝ) * fun ω => f (X ω)) = A.indicator (fun ω => f (X ω)) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  rw [integral_indicator_one hA', hfun, integral_indicator hA', measureReal_def] at h
  exact h

/-- A σ-algebra independent of each term of an a.e.-convergent sequence of random variables is
independent of the limit. -/
theorem indep_comap_of_tendsto_ae (hm : m ≤ mΩ) {X : ℕ → Ω → 𝓧}
    {Y : Ω → 𝓧} (hX : ∀ n, Measurable[mΩ] (X n)) (hY : Measurable[mΩ] Y)
    (hind : ∀ n, Indep m (MeasurableSpace.comap (X n) inferInstance) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Indep m (MeasurableSpace.comap Y inferInstance) P := by
  rw [Indep_iff]
  intro A B hA hB
  obtain ⟨S, hS, rfl⟩ := hB
  have hA' : MeasurableSet[mΩ] A := hm _ hA
  have : IsFiniteMeasure ((P A) • P.map Y) :=
    ⟨by simp⟩
  have hbound : ∀ (Z : Ω → 𝓧), Measurable[mΩ] Z → ∀ f : 𝓧 →ᵇ ℝ,
      Integrable (fun ω => f (Z ω)) P := fun Z hZ f =>
    Integrable.of_bound (f.continuous.measurable.comp hZ).aestronglyMeasurable ‖f‖
      (ae_of_all _ fun ω => f.norm_coe_le_norm _)
  have hμ : (P.restrict A).map Y = (P A) • P.map Y := by
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    rw [integral_map hY.aemeasurable f.continuous.aestronglyMeasurable,
      integral_smul_measure, integral_map hY.aemeasurable f.continuous.aestronglyMeasurable,
      smul_eq_mul]
    have hL : Tendsto (fun n => ∫ ω in A, f (X n ω) ∂P) atTop (𝓝 (∫ ω in A, f (Y ω) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
        (fun n => (f.continuous.measurable.comp (hX n)).aestronglyMeasurable)
        (integrable_const _) (fun n => ae_of_all _ fun ω => f.norm_coe_le_norm _) ?_
      exact ae_restrict_of_ae (hlim.mono fun ω hω => (f.continuous.tendsto _).comp hω)
    have hR : Tendsto (fun n => (P A).toReal * ∫ ω, f (X n ω) ∂P) atTop
        (𝓝 ((P A).toReal * ∫ ω, f (Y ω) ∂P)) := by
      refine Tendsto.const_mul _ ?_
      refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
        (fun n => (f.continuous.measurable.comp (hX n)).aestronglyMeasurable)
        (integrable_const _) (fun n => ae_of_all _ fun ω => f.norm_coe_le_norm _) ?_
      exact hlim.mono fun ω hω => (f.continuous.tendsto _).comp hω
    have heq : ∀ n, ∫ ω in A, f (X n ω) ∂P = (P A).toReal * ∫ ω, f (X n ω) ∂P := fun n =>
      setIntegral_eq_measure_mul_of_indep hm (hX n) (hind n) hA f
    simp_rw [heq] at hL
    exact tendsto_nhds_unique hL hR
  have h1 : ((P.restrict A).map Y) S = P (A ∩ Y ⁻¹' S) := by
    rw [Measure.map_apply hY hS, Measure.restrict_apply (hY hS), Set.inter_comm]
  have h2 : ((P A) • P.map Y) S = P A * P (Y ⁻¹' S) := by
    rw [smul_apply, Measure.map_apply hY hS, smul_eq_mul]
  rw [← h1, hμ, h2]

end LevyStochCalc.Probability
