/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Process.Basic
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Generator

/-!
# Integrals of bounded functionals of cutoff Eldan processes
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.KLS.BKL.Localization

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
section Integrals

variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {γ : Param n → ℝ} {p : ℝ → Ω → Param n}

/--
**Time integrals of bounded functionals along the cutoff Eldan process** are integrable in `ω`: for
a continuous
`φ` with `|φ(p_s)| ≤ B` for all `s ≥ 0` almost surely, `ω ↦ ∫₀ᵀ φ(p_s(ω)) ds` is integrable. -/
theorem IsEldanCutoff.integrable_integral_of_ae_bound (h : IsEldanCutoff μ hc W ℱ hW γ p)
    {φ : Param n → ℝ} (hφ : Continuous φ) {B : ℝ}
    (hB : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → |φ (p s ω)| ≤ B) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) T, φ (p s ω)) P := by
  have hpcont := h.continuous
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) := stateEquiv (Param n)
  change
    IsDiffusion W ℱ hW (transportDrift Φ (cutoffDrift μ hc γ))
      (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0) (fun t ω => Φ (p t ω)) at h
  obtain ⟨_, _, _, hv⟩ := h
  have h1 : Measurable (fun z : Ω × ℝ => Φ (p z.2 z.1)) := by
    change Measurable (Function.uncurry (fun ω s => Φ (p s ω)))
    exact hv.measurable_uncurry
  have hpmeas : Measurable (fun z : Ω × ℝ => p z.2 z.1) := by
    have h' := Φ.symm.continuous.measurable.comp h1
    change Measurable (fun z : Ω × ℝ => Φ.symm (Φ (p z.2 z.1))) at h'
    simpa only [Φ.symm_apply_apply] using h'
  have hm : Measurable (fun z : Ω × ℝ => φ (p z.2 z.1)) := hφ.measurable.comp hpmeas
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T)
  have hmeas : AEStronglyMeasurable (fun z : Ω × ℝ => φ (p z.2 z.1)) (P.prod ν) :=
    hm.aestronglyMeasurable
  have hsm : AEStronglyMeasurable (fun ω => ∫ s, φ (p s ω) ∂ν) P := hmeas.integral_prod_right'
  change Integrable (fun ω => ∫ s, φ (p s ω) ∂ν) P
  apply Integrable.of_bound hsm (B * T)
  filter_upwards [hB] with ω hω
  calc
    ‖∫ s, φ (p s ω) ∂ν‖ ≤ ∫ s, ‖φ (p s ω)‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ s in Set.Ioc (0 : ℝ) T, B := by
      apply setIntegral_mono_on
      · exact ((hφ.comp (hpcont ω)).norm).integrableOn_Ioc
      · exact continuous_const.integrableOn_Ioc
      · exact measurableSet_Ioc
      · intro s hs
        simpa only [Real.norm_eq_abs] using hω s hs.1.le
    _ = B * T := by
      simp [hT]
      ring

/--
**Monotonicity of the iterated integrals** along the cutoff Eldan process: if `0 ≤ φ(p_s) ≤ ψ(p_s)`
for all
`s ≥ 0` almost surely and `ψ(p_s)` is almost surely bounded, then `E ∫₀ᵀ φ(p_s) ds ≤ E ∫₀ᵀ ψ(p_s)
ds`. -/
theorem IsEldanCutoff.integral_integral_mono (h : IsEldanCutoff μ hc W ℱ hW γ p)
    {φ ψ : Param n → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) {B : ℝ}
    (hB : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → |ψ (p s ω)| ≤ B)
    (hle : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → 0 ≤ φ (p s ω) ∧ φ (p s ω) ≤ ψ (p s ω)) {T : ℝ}
    (hT : 0 ≤ T) :
    ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, φ (p s ω) ∂volume ∂P ≤
      ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, ψ (p s ω) ∂volume ∂P := by
  have hψi := h.integrable_integral_of_ae_bound hψ hB hT
  have hφB : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → |φ (p s ω)| ≤ B := by
    filter_upwards [hB, hle] with ω hω hωle
    intro s hs
    calc
      |φ (p s ω)| = φ (p s ω) := abs_of_nonneg (hωle s hs).1
      _ ≤ ψ (p s ω) := (hωle s hs).2
      _ ≤ |ψ (p s ω)| := le_abs_self _
      _ ≤ B := hω s hs
  apply integral_mono_ae (h.integrable_integral_of_ae_bound hφ hφB hT) hψi
  filter_upwards [hle] with ω hω
  exact
    setIntegral_mono_on (hφ.comp (h.continuous ω)).integrableOn_Ioc
      (hψ.comp (h.continuous ω)).integrableOn_Ioc measurableSet_Ioc
      (fun s hs => (hω s hs.1.le).2)

end Integrals
section Process

variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {γ : Param n → ℝ} {p : ℝ → Ω → Param n}

/-- Joint measurability of the cutoff Eldan path `(ω, s) ↦ p_s(ω)`. -/
theorem IsEldanCutoff.measurable_uncurry_path (h : IsEldanCutoff μ hc W ℱ hW γ p) :
    Measurable (fun z : Ω × ℝ => p z.2 z.1) := by
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) :=
    stateEquiv (Param n)
  change IsDiffusion W ℱ hW
    (transportDrift Φ (cutoffDrift μ hc γ))
    (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0)
    (fun t w => Φ (p t w)) at h
  obtain ⟨_, _, _, hv⟩ := h
  have h1 : Measurable (fun z : Ω × ℝ => Φ (p z.2 z.1)) := by
    change Measurable (Function.uncurry (fun w s => Φ (p s w)))
    exact hv.measurable_uncurry
  have h' := Φ.symm.continuous.measurable.comp h1
  change Measurable (fun z : Ω × ℝ => Φ.symm (Φ (p z.2 z.1))) at h'
  simpa only [Φ.symm_apply_apply] using h'

omit [IsProbabilityMeasure P] in
/-- Almost-sure statements valid for all `s ≥ 0` transfer to the product measure
`P ⊗ Leb|_{(0,T]}`. -/
theorem ae_prod_restrict_Ioc_of_ae
    {Q : Ω → ℝ → Prop}
    (hQ : ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → Q w s) (T : ℝ) :
    ∀ᵐ z ∂(P.prod (volume.restrict (Set.Ioc (0 : ℝ) T))), Q z.1 z.2 := by
  rw [ae_iff] at hQ ⊢
  apply measure_mono_null
    (t := {w | ¬ ∀ s : ℝ, 0 ≤ s → Q w s} ×ˢ (Set.univ : Set ℝ) ∪
      (Set.univ : Set Ω) ×ˢ (Set.Ioc (0 : ℝ) T)ᶜ)
  · intro z hz
    by_cases hS : ∀ s : ℝ, 0 ≤ s → Q z.1 s
    · right
      refine ⟨Set.mem_univ _, fun hs => ?_⟩
      exact hz (hS z.2 hs.1.le)
    · left
      exact ⟨hS, Set.mem_univ _⟩
  · apply measure_union_null
    · rw [Measure.prod_prod, hQ, zero_mul]
    · rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc.compl,
        Set.compl_inter_self, measure_empty, mul_zero]

/-- Bounded continuous functionals of the cutoff Eldan path are integrable on `P ⊗ Leb|_{(0,T]}`. -/
theorem IsEldanCutoff.integrable_prod_of_ae_bound (h : IsEldanCutoff μ hc W ℱ hW γ p)
    {φ : Param n → ℝ} (hφ : Continuous φ) {B : ℝ}
    (hB : ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → |φ (p s w)| ≤ B) (T : ℝ) :
    Integrable (fun z : Ω × ℝ => φ (p z.2 z.1))
      (P.prod (volume.restrict (Set.Ioc (0 : ℝ) T))) := by
  have hm : Measurable (fun z : Ω × ℝ => φ (p z.2 z.1)) :=
    hφ.measurable.comp h.measurable_uncurry_path
  refine Integrable.of_bound hm.aestronglyMeasurable B ?_
  filter_upwards [ae_prod_restrict_Ioc_of_ae hB T] with z hz
  simpa only [Real.norm_eq_abs] using hz

/-- The iterated integral `E ∫₀ᵀ φ(p_s) ds` is the integral over `P ⊗ Leb|_{(0,T]}`. -/
theorem IsEldanCutoff.integral_integral_eq_prod (h : IsEldanCutoff μ hc W ℱ hW γ p)
    {φ : Param n → ℝ} (hφ : Continuous φ) {B : ℝ}
    (hB : ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → |φ (p s w)| ≤ B) (T : ℝ) :
    ∫ w, ∫ s in Set.Ioc (0 : ℝ) T, φ (p s w) ∂volume ∂P =
      ∫ z, φ (p z.2 z.1) ∂(P.prod (volume.restrict (Set.Ioc (0 : ℝ) T))) :=
  (integral_prod _ (h.integrable_prod_of_ae_bound hφ hB T)).symm

end Process
end FunctionalInequalities.KLS.BKL.Localization
