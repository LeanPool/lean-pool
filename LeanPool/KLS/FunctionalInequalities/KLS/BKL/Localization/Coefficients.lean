/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Covariance
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Generator
public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.LipschitzBall
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Regularity
/-!
# Coefficients and generator of the Eldan localization equations

Bizeul–Klartag–Lehec arXiv:2610.05474v1, (67), compact-prior stage: the parameter space `p = (c,
Q)`, the posterior
covariance `A(p)`, the drift `(A⁻¹ a, A⁻¹)`, the noise columns `(A^{-1/2} e_k, 0)`, the generator
`𝓛F = DF[(A⁻¹a, A⁻¹)] + ½ Σ_k D²F[(A^{-1/2}e_k, 0), (A^{-1/2}e_k, 0)]`, and the cutoff coefficients
`γ² · drift`, `γ · noise` for an admissible cutoff `γ`, with `𝓛_γ F = γ² 𝓛F` and the admissibility
of the cutoff
coefficients (globally Lipschitz, bounded, compactly supported) for an isotropic compact prior.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.KLS.BKL.Localization

/-- Parameter space `p = (c, Q)` of the Eldan localization equations (BKL arXiv:2610.05474v1, (67));
`Q` is not required to be symmetric. -/
abbrev Param (n : ℕ) :=
  EuclideanSpace ℝ (Fin n) × (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))

variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

/-- The posterior covariance `A(p) = Cov μ_{c,Q}`. -/
def cov (p : Param n) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))

/-- Drift of (67): `(A⁻¹ a, A⁻¹)`. -/
def drift (p : Param n) : Param n :=
  (Ring.inverse (cov μ hc p) (posteriorMean μ p.1 p.2), Ring.inverse (cov μ hc p))

/-- Noise columns of (67): `(A^{-1/2} e_k, 0)`. -/
def noise (p : Param n) (k : Fin n) : Param n :=
  (inverseSqrt (cov μ hc p) (EuclideanSpace.single k 1), 0)

/--
The generator `𝓛` of (67): `𝓛F = DF[(A⁻¹a, A⁻¹)] + ½ Σ_k D²F[(A^{-1/2}e_k, 0), (A^{-1/2}e_k, 0)]`.
-/
def generator (F : Param n → ℝ) (p : Param n) : ℝ :=
  diffusionGenerator (drift μ hc) (noise μ hc) F p

/-- Cutoff drift `γ² · (A⁻¹ a, A⁻¹)`. -/
def cutoffDrift (γ : Param n → ℝ) (p : Param n) : Param n := (γ p) ^ 2 • drift μ hc p

/-- Cutoff noise `γ · (A^{-1/2} e_k, 0)`. -/
def cutoffNoise (γ : Param n → ℝ) (p : Param n) (k : Fin n) : Param n := γ p • noise μ hc p k

/-- An admissible cutoff: Lipschitz, compactly supported, `[0, 1]`-valued. -/
structure IsCutoff (γ : Param n → ℝ) : Prop where
  lipschitz : ∃ K : ℝ≥0, LipschitzWith K γ
  compactSupport : HasCompactSupport γ
  mem_Icc : ∀ p, γ p ∈ Set.Icc (0 : ℝ) 1

/-- `𝓛_γ F = γ² 𝓛 F`. -/
theorem diffusionGenerator_cutoff (γ : Param n → ℝ) (F : Param n → ℝ) (p : Param n) :
    diffusionGenerator (cutoffDrift μ hc γ) (cutoffNoise μ hc γ) F p =
      γ p ^ 2 * generator μ hc F p := by
  simp only [diffusionGenerator, generator, cutoffDrift, cutoffNoise, map_smul,
    smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem isCutoff_ballCutoff (R : ℝ) : IsCutoff (ballCutoff (V := Param n) R) :=
  { lipschitz := ⟨1, lipschitzWith_ballCutoff R⟩
    compactSupport := hasCompactSupport_ballCutoff R
    mem_Icc := fun p => ballCutoff_mem_Icc R p }

/-- The square-root coefficient `p ↦ A(p)^{-1/2}` is locally Lipschitz. -/
theorem locallyLipschitz_inverseSqrt_cov (hiso : KLS.Isotropic μ) :
    LocallyLipschitz (fun p : Param n => inverseSqrt (cov μ hc p)) := by
  have h := (LipschitzWith.prod_fst.locallyLipschitz).comp
    (Isotropic.locallyLipschitz_coefficients67 μ hc hiso)
  simpa only [Function.comp_def, cov] using h

/-- The drift of (67) is locally Lipschitz. -/
theorem locallyLipschitz_drift (hiso : KLS.Isotropic μ) : LocallyLipschitz (drift μ hc) := by
  have h := (LipschitzWith.prod_snd.locallyLipschitz).comp
    (Isotropic.locallyLipschitz_coefficients67 μ hc hiso)
  change LocallyLipschitz (fun p : Param n => drift μ hc p)
  simpa only [Function.comp_def, drift, cov] using h

/-- Each noise column of (67) is locally Lipschitz. -/
theorem locallyLipschitz_noise (hiso : KLS.Isotropic μ) (k : Fin n) :
    LocallyLipschitz (fun p : Param n => noise μ hc p k) := by
  have h1 : LocallyLipschitz
      ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace.single k (1 : ℝ))) ∘
        (fun p : Param n => inverseSqrt (cov μ hc p))) :=
    ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace.single k (1 : ℝ))).lipschitzWith.locallyLipschitz).comp
      (locallyLipschitz_inverseSqrt_cov μ hc hiso)
  have h2 : LocallyLipschitz
      (fun p : Param n => inverseSqrt (cov μ hc p) (EuclideanSpace.single k (1 : ℝ))) := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using h1
  have h3 := h2.prodMk
    (LocallyLipschitz.const (α := Param n)
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
  simpa only [noise] using h3

theorem cutoffDrift_eq (γ : Param n → ℝ) :
    cutoffDrift μ hc γ = fun p => γ p • (γ p • drift μ hc p) := by
  funext p
  simp only [cutoffDrift, smul_smul, pow_two]

/-- The generator of a `C³` function is continuous (continuous coefficients). -/
theorem continuous_generator_of_contDiff_three (hiso : KLS.Isotropic μ) {F : Param n → ℝ}
    (hF : ContDiff ℝ 3 F) : Continuous (generator μ hc F) := by
  exact continuous_diffusionGenerator
    (locallyLipschitz_drift μ hc hiso).continuous
    (fun k => (locallyLipschitz_noise μ hc hiso k).continuous)
    (hF.of_le (by norm_num))


/-- The cutoff drift is globally Lipschitz and bounded. -/
theorem cutoffDrift_lipschitz_bounded (hiso : KLS.Isotropic μ) {γ : Param n → ℝ}
    (hγ : IsCutoff γ) :
    (∃ K : ℝ≥0, LipschitzWith K (cutoffDrift μ hc γ)) ∧
      ∃ B : ℝ, ∀ p, ‖cutoffDrift μ hc γ p‖ ≤ B := by
  obtain ⟨Kγ, hγL⟩ := hγ.lipschitz
  obtain ⟨⟨K₁, hK₁⟩, -⟩ :=
    exists_lipschitzWith_smul_of_locallyLipschitz hγL hγ.compactSupport
      (locallyLipschitz_drift μ hc hiso)
  obtain ⟨⟨K₂, hK₂⟩, B₂, hB₂⟩ :=
    exists_lipschitzWith_smul_of_locallyLipschitz hγL hγ.compactSupport hK₁.locallyLipschitz
  rw [cutoffDrift_eq]
  exact ⟨⟨K₂, hK₂⟩, B₂, hB₂⟩

/-- Each cutoff noise column is globally Lipschitz and bounded. -/
theorem cutoffNoise_lipschitz_bounded (hiso : KLS.Isotropic μ) {γ : Param n → ℝ}
    (hγ : IsCutoff γ) (k : Fin n) :
    (∃ K : ℝ≥0, LipschitzWith K fun p => cutoffNoise μ hc γ p k) ∧
      ∃ B : ℝ, ∀ p, ‖cutoffNoise μ hc γ p k‖ ≤ B := by
  obtain ⟨Kγ, hγL⟩ := hγ.lipschitz
  exact exists_lipschitzWith_smul_of_locallyLipschitz hγL hγ.compactSupport
    (locallyLipschitz_noise μ hc hiso k)

theorem hasCompactSupport_cutoffDrift {γ : Param n → ℝ} (hγ : IsCutoff γ) :
    HasCompactSupport (cutoffDrift μ hc γ) := by
  refine hγ.compactSupport.mono ?_
  intro p hp hγ0
  apply hp
  show cutoffDrift μ hc γ p = 0
  rw [cutoffDrift, hγ0, zero_pow two_ne_zero]
  exact zero_smul ℝ (drift μ hc p)

theorem hasCompactSupport_cutoffNoise {γ : Param n → ℝ} (hγ : IsCutoff γ) (k : Fin n) :
    HasCompactSupport fun p => cutoffNoise μ hc γ p k := by
  refine hγ.compactSupport.mono ?_
  intro p hp hγ0
  apply hp
  change cutoffNoise μ hc γ p k = 0
  rw [cutoffNoise, hγ0]
  exact zero_smul ℝ (noise μ hc p k)

/--
The cutoff coefficients of (67) are globally Lipschitz, bounded, continuous and compactly supported
for a compactly supported isotropic prior. -/
theorem cutoffCoefficients_admissible (hiso : KLS.Isotropic μ) {γ : Param n → ℝ}
    (hγ : IsCutoff γ) :
    (∃ K : ℝ≥0,
        LipschitzWith K (cutoffDrift μ hc γ) ∧
          ∀ k, LipschitzWith K fun p => cutoffNoise μ hc γ p k) ∧
      (∃ B : ℝ, ∀ p, ‖cutoffDrift μ hc γ p‖ ≤ B ∧ ∀ k, ‖cutoffNoise μ hc γ p k‖ ≤ B) ∧
        HasCompactSupport (cutoffDrift μ hc γ) ∧
          ∀ k, HasCompactSupport fun p => cutoffNoise μ hc γ p k := by
  classical
  obtain ⟨⟨K₀, hK₀⟩, B₀, hB₀⟩ := cutoffDrift_lipschitz_bounded μ hc hiso hγ
  choose Kn hKn using fun k => (cutoffNoise_lipschitz_bounded μ hc hiso hγ k).1
  choose Bn hBn using fun k => (cutoffNoise_lipschitz_bounded μ hc hiso hγ k).2
  refine
    ⟨⟨K₀ + ∑ k, Kn k, ?_, ?_⟩, ⟨max B₀ (∑ k, max (Bn k) 0), ?_⟩,
      hasCompactSupport_cutoffDrift μ hc hγ, hasCompactSupport_cutoffNoise μ hc hγ⟩
  · exact hK₀.weaken (le_add_of_nonneg_right bot_le)
  · intro k
    refine (hKn k).weaken ?_
    exact
      (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ k)).trans
        (le_add_of_nonneg_left bot_le)
  · intro p
    refine ⟨(hB₀ p).trans (le_max_left _ _), fun k => (hBn k p).trans ?_⟩
    exact
      (le_max_left (Bn k) 0).trans
        ((Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ k)).trans
          (le_max_right _ _))

end FunctionalInequalities.KLS.BKL.Localization
