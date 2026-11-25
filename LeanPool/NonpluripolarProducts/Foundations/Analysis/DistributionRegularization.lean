/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.TranslationPairing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.TestLeviPairing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.SmoothPlurisubharmonic

/-!
# Smooth regularization of densities with positive distributional Levi form

A translated smooth compact kernel is an actual test function whenever its
support lies in the distribution's domain. The classical Levi form of the
translation pairing is its distributional Levi pairing. Positivity therefore
gives a smooth plurisubharmonic regularization on the admissible inner domain.

For a density locally integrable only on the open domain, a compact cutoff gives
a globally integrable density. The original and cutoff pairings agree wherever
the translated kernel is supported in that compact set. No regularity of the
original density or boundary extension is assumed.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Distributions ContDiff

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Opens E}

/-- A translate of a smooth compact kernel, bundled in the actual test-function
space on the domain containing its translated support. -/
def translatedTestFunction (φ : E → ℝ) (hφs : HasCompactSupport φ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (z : E)
    (hzΩ : tsupport (fun x => φ (x - z)) ⊆ Ω) : 𝓓(Ω, ℝ) :=
  ⟨fun x => φ (x - z), hφ.comp (contDiff_id.sub contDiff_const),
    hφs.comp_homeomorph (Homeomorph.subRight z), hzΩ⟩

@[simp]
theorem translatedTestFunction_apply (φ : E → ℝ) (hφs : HasCompactSupport φ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (z : E)
    (hzΩ : tsupport (fun x => φ (x - z)) ⊆ Ω) (x : E) :
    translatedTestFunction φ hφs hφ z hzΩ x = φ (x - z) := rfl

/-- Translation commutes with the actual iterated real derivative, including
at points where no differentiability assumption is supplied. -/
theorem realHessian_comp_sub (φ : E → ℝ) (z x v w : E) :
    realHessian (fun y => φ (y - z)) x v w = realHessian φ (x - z) v w := by
  simp only [realHessian, iteratedFDeriv_comp_sub]

section Complex

variable [NormedSpace ℂ E]

theorem leviForm_comp_sub (φ : E → ℝ) (z x v : E) :
    leviForm (fun y => φ (y - z)) x v = leviForm φ (x - z) v := by
  simp only [leviForm, realHessian_comp_sub]

section Pairing

variable [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure E} [SFinite μ] [μ.IsAddLeftInvariant]
variable {u g φ : E → ℝ}

/-- Equality of the density on the translated support is enough for the
classical Levi form to equal the distributional Levi pairing. -/
theorem leviForm_translationPairing_eq_distributionalLevi_of_eqOn
    (hg : LocallyIntegrable g μ) (hu : LocallyIntegrableOn u Ω μ)
    (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : E) (hzΩ : tsupport (fun x => φ (x - z)) ⊆ Ω)
    (hgu : EqOn g u (tsupport (fun x => φ (x - z)))) (v : E) :
    leviForm (translationPairing μ g φ) z v =
      distributionalLeviCLM v (regularDistribution μ u hu)
        (translatedTestFunction φ hφs hφ z hzΩ) := by
  rw [leviForm_translationPairing hg hφs
      (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    distributionalLeviCLM_regularDistribution_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  change g x * leviForm φ (x - z) v =
    u x * leviForm (fun y => φ (y - z)) x v
  rw [leviForm_comp_sub]
  by_cases hx : x ∈ tsupport (fun y => φ (y - z))
  · rw [hgu hx]
  · have hzero : leviForm φ (x - z) v = 0 := by
      simpa only [leviForm_comp_sub] using
        leviForm_eq_zero_of_notMem_tsupport hx v
    rw [hzero, mul_zero, mul_zero]

/-- Positivity is tested against the actual nonnegative translated kernel. -/
theorem leviForm_translationPairing_nonneg_of_eqOn
    (hg : LocallyIntegrable g μ) (hu : LocallyIntegrableOn u Ω μ)
    (hT : HasNonnegativeDistributionalLevi (regularDistribution μ u hu))
    (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφn : ∀ x, 0 ≤ φ x) (z : E)
    (hzΩ : tsupport (fun x => φ (x - z)) ⊆ Ω)
    (hgu : EqOn g u (tsupport (fun x => φ (x - z)))) (v : E) :
    0 ≤ leviForm (translationPairing μ g φ) z v := by
  rw [leviForm_translationPairing_eq_distributionalLevi_of_eqOn
    hg hu hφs hφ z hzΩ hgu v]
  exact hT v (translatedTestFunction φ hφs hφ z hzΩ) (fun x => hφn (x - z))

/-- A globally locally integrable density can be regularized directly. -/
theorem leviForm_translationPairing_nonneg
    (hu : LocallyIntegrable u μ)
    (hT : HasNonnegativeDistributionalLevi
      (regularDistribution μ u (hu.locallyIntegrableOn Ω)))
    (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφn : ∀ x, 0 ≤ φ x) (z : E)
    (hzΩ : tsupport (fun x => φ (x - z)) ⊆ Ω) (v : E) :
    0 ≤ leviForm (translationPairing μ u φ) z v :=
  leviForm_translationPairing_nonneg_of_eqOn hu (hu.locallyIntegrableOn Ω) hT
    hφs hφ hφn z hzΩ (fun _ _ => rfl) v

section Plurisubharmonic

variable [IsScalarTower ℝ ℂ E] {U : Set E}

theorem discPshOn_translationPairing
    (hu : LocallyIntegrable u μ)
    (hT : HasNonnegativeDistributionalLevi
      (regularDistribution μ u (hu.locallyIntegrableOn Ω)))
    (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφn : ∀ x, 0 ≤ φ x)
    (hUΩ : ∀ z ∈ U, tsupport (fun x => φ (x - z)) ⊆ Ω) :
    DiscPshOn (fun z => (translationPairing μ u φ z : EReal)) U := by
  apply discPshOn_of_levi_nonneg
    (contDiff_translationPairing hu hφs
      (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)))
  intro z hz v
  exact leviForm_translationPairing_nonneg hu hT hφs hφ hφn z (hUΩ z hz) v

theorem plurisubharmonicOn_translationPairing
    (hu : LocallyIntegrable u μ)
    (hT : HasNonnegativeDistributionalLevi
      (regularDistribution μ u (hu.locallyIntegrableOn Ω)))
    (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφn : ∀ x, 0 ≤ φ x) (hU : IsOpen U)
    (hUΩ : ∀ z ∈ U, tsupport (fun x => φ (x - z)) ⊆ Ω) :
    PlurisubharmonicOn (fun z => (translationPairing μ u φ z : EReal)) U :=
  (discPshOn_translationPairing hu hT hφs hφ hφn hUΩ).plurisubharmonicOn hU

end Plurisubharmonic
end Pairing
end Complex

section Localization

variable [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure E} {u φ : E → ℝ} {K U : Set E}

omit [NormedSpace ℝ E] in
/-- Local integrability on the domain gives a globally integrable compact
cutoff. No finiteness assumption on the measure of the whole domain is used. -/
theorem integrable_indicator_of_locallyIntegrableOn_isCompact
    (hu : LocallyIntegrableOn u Ω μ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    Integrable (K.indicator u) μ :=
  ((hu.mono_set hKΩ).integrableOn_isCompact hK).integrable_indicator hK.measurableSet

omit [NormedSpace ℝ E] [BorelSpace E] in
/-- The cutoff does not change the scalar pairing when it contains the entire
translated kernel support. This identity itself needs no integrability premise. -/
theorem translationPairing_indicator_eq (u φ : E → ℝ) (z : E)
    (hzK : tsupport (fun x => φ (x - z)) ⊆ K) :
    translationPairing μ (K.indicator u) φ z = translationPairing μ u φ z := by
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx]
  · have hzero : φ (x - z) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => φ (y - z))
        (fun hxs => hx (hzK hxs))
    rw [hzero, mul_zero, mul_zero]

/-- On an inner set with a common compact support bound, the original scalar
pairing is smooth despite the density being locally integrable only on Ω. -/
theorem contDiffOn_translationPairing_of_locallyIntegrableOn
    (hu : LocallyIntegrableOn u Ω μ)
    (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hUK : ∀ z ∈ U, tsupport (fun x => φ (x - z)) ⊆ K) :
    ContDiffOn ℝ (⊤ : ℕ∞) (translationPairing μ u φ) U := by
  have hg := (integrable_indicator_of_locallyIntegrableOn_isCompact hu hK hKΩ).locallyIntegrable
  apply (contDiff_translationPairing hg hφs hφ).contDiffOn.congr
  intro z hz
  exact (translationPairing_indicator_eq u φ z (hUK z hz)).symm

variable [NormedSpace ℂ E] [SFinite μ] [μ.IsAddLeftInvariant]

/-- Positive distributional Levi form survives compact localization wherever
the translated smooth kernel is supported inside the cutoff. -/
theorem leviForm_translationPairing_indicator_nonneg
    (hu : LocallyIntegrableOn u Ω μ)
    (hT : HasNonnegativeDistributionalLevi (regularDistribution μ u hu))
    (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφn : ∀ x, 0 ≤ φ x) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (z : E) (hzK : tsupport (fun x => φ (x - z)) ⊆ K) (v : E) :
    0 ≤ leviForm (translationPairing μ (K.indicator u) φ) z v := by
  apply leviForm_translationPairing_nonneg_of_eqOn
    (integrable_indicator_of_locallyIntegrableOn_isCompact hu hK hKΩ).locallyIntegrable
    hu hT hφs hφ hφn z (hzK.trans hKΩ) _ v
  intro x hx
  exact indicator_of_mem (hzK hx) u

variable [IsScalarTower ℝ ℂ E]

/-- A single compact cutoff gives a globally smooth pairing that is PSH on
every inner set with translated kernel support inside that compact set. -/
theorem discPshOn_translationPairing_indicator
    (hu : LocallyIntegrableOn u Ω μ)
    (hT : HasNonnegativeDistributionalLevi (regularDistribution μ u hu))
    (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφn : ∀ x, 0 ≤ φ x) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hUK : ∀ z ∈ U, tsupport (fun x => φ (x - z)) ⊆ K) :
    DiscPshOn (fun z => (translationPairing μ (K.indicator u) φ z : EReal)) U := by
  apply discPshOn_of_levi_nonneg
    (contDiff_translationPairing
      (integrable_indicator_of_locallyIntegrableOn_isCompact hu hK hKΩ).locallyIntegrable
      hφs (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)))
  intro z hz v
  exact leviForm_translationPairing_indicator_nonneg hu hT hφs hφ hφn
    hK hKΩ z (hUK z hz) v

/-- The original pairing is PSH on the inner set: compact localization is an
auxiliary proof device and does not alter any value there. -/
theorem discPshOn_translationPairing_of_locallyIntegrableOn
    (hu : LocallyIntegrableOn u Ω μ)
    (hT : HasNonnegativeDistributionalLevi (regularDistribution μ u hu))
    (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφn : ∀ x, 0 ≤ φ x) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hUK : ∀ z ∈ U, tsupport (fun x => φ (x - z)) ⊆ K) :
    DiscPshOn (fun z => (translationPairing μ u φ z : EReal)) U := by
  apply (discPshOn_translationPairing_indicator hu hT hφs hφ hφn hK hKΩ hUK).congr
  intro z hz
  exact congrArg (fun t : ℝ => (t : EReal))
    (translationPairing_indicator_eq u φ z (hUK z hz))

/-- The actual locally integrable density has smooth PSH regularizations on
open inner domains with a common compact bound for translated kernel supports. -/
theorem plurisubharmonicOn_translationPairing_of_locallyIntegrableOn
    (hu : LocallyIntegrableOn u Ω μ)
    (hT : HasNonnegativeDistributionalLevi (regularDistribution μ u hu))
    (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφn : ∀ x, 0 ≤ φ x) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hU : IsOpen U) (hUK : ∀ z ∈ U, tsupport (fun x => φ (x - z)) ⊆ K) :
    PlurisubharmonicOn (fun z => (translationPairing μ u φ z : EReal)) U :=
  (discPshOn_translationPairing_of_locallyIntegrableOn
    hu hT hφs hφ hφn hK hKΩ hUK).plurisubharmonicOn hU

end Localization

end SGPT.Foundations.Analysis
