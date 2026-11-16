/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Setup
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Existence
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Dynkin
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Generator
/-!
# Diffusions under a change of coordinates

Continuity of diffusion paths, Dynkin's identity and the noise-free linear identity for a diffusion
transported by a
continuous linear equivalence of the state space (used for the Eldan process on `E × (E →L[ℝ] E)` in
coordinates).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.Probability.Diffusion

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

section Transport

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {N d : ℕ}
  {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}

/-- Every path of a diffusion is continuous. -/
theorem IsDiffusion.continuous_path {b : (Fin N → ℝ) → Fin N → ℝ}
    {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {x₀ : Fin N → ℝ} {Y : ℝ → Ω → Fin N → ℝ}
    (h : IsDiffusion W ℱ hW b σ x₀ Y) (ω : Ω) : Continuous fun t => Y t ω := by
  obtain ⟨_, _, _, hv⟩ := h
  exact hv.continuous_path ω

section DynkinTransport

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/--
**Dynkin's identity in a finite-dimensional state space**: if the coordinates `Φ ∘ Y` of a
`V`-valued process
form a diffusion with the transported coefficients, the coefficients on `V` being continuous with
compact support,
then for every `C²` `F : V → ℝ`, `F(Y_T)` is integrable and `E F(Y_T) − F(x₀) = E ∫₀ᵀ 𝓛F(Y_s) ds`
with the
coordinate-free generator on `V`. -/
theorem IsDiffusion.dynkin_transport (Φ : V ≃L[ℝ] (Fin N → ℝ))
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) {b : V → V}
    {σ : V → Fin d → V} {x₀ : V} (hbc : Continuous b) (hσc : ∀ k, Continuous fun x => σ x k)
    (hbs : HasCompactSupport b) (hσs : ∀ k, HasCompactSupport fun x => σ x k) {Y : ℝ → Ω → V}
    (h :
      IsDiffusion W ℱ hW (transportDrift Φ b) (transportNoise Φ σ) (Φ x₀)
        (fun t ω => Φ (Y t ω)))
    {F : V → ℝ} (hF : ContDiff ℝ 2 F) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ω => F (Y T ω)) P ∧
      ∫ ω, F (Y T ω) ∂P - F x₀ =
        ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, diffusionGenerator b σ F (Y s ω) ∂volume ∂P := by
  classical
  have hbc' : Continuous (transportDrift Φ b) := by
    change Continuous (fun y => Φ (b (Φ.symm y)))
    exact Φ.continuous.comp (hbc.comp Φ.symm.continuous)
  have hσc' : ∀ k, Continuous fun y => transportNoise Φ σ y k := by
    intro k
    change Continuous (fun y => Φ (σ (Φ.symm y) k))
    exact Φ.continuous.comp ((hσc k).comp Φ.symm.continuous)
  have hbs' : HasCompactSupport (transportDrift Φ b) := by
    change HasCompactSupport (fun y => Φ (b (Φ.symm y)))
    have h₁ : HasCompactSupport (Φ ∘ b) := hbs.comp_left (g := Φ) Φ.map_zero
    have h₂ := h₁.comp_homeomorph Φ.symm.toHomeomorph
    have he : ((Φ ∘ b) ∘ ⇑Φ.symm.toHomeomorph) = (fun y => Φ (b (Φ.symm y))) := by
      funext y
      rfl
    rw [he] at h₂
    exact h₂
  have hσs' : ∀ k, HasCompactSupport fun y => transportNoise Φ σ y k := by
    intro k
    change HasCompactSupport (fun y => Φ (σ (Φ.symm y) k))
    have h₁ : HasCompactSupport (Φ ∘ fun x => σ x k) := (hσs k).comp_left (g := Φ) Φ.map_zero
    have h₂ := h₁.comp_homeomorph Φ.symm.toHomeomorph
    have he : ((Φ ∘ fun x => σ x k) ∘ ⇑Φ.symm.toHomeomorph) = (fun y => Φ (σ (Φ.symm y) k)) := by
      funext y
      rfl
    rw [he] at h₂
    exact h₂
  have hF' : ContDiff ℝ 2 (F ∘ Φ.symm) := hF.comp (ContinuousLinearEquiv.contDiff Φ.symm)
  obtain ⟨hInt, hEq⟩ := IsDiffusion.dynkin hℱ0 hnull hbc' hσc' hbs' hσs' h hF' hT
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using hInt
  · calc
      ∫ ω, F (Y T ω) ∂P - F x₀ =
          ∫ ω, (F ∘ Φ.symm) ((fun t ω => Φ (Y t ω)) T ω) ∂P - (F ∘ Φ.symm) (Φ x₀) := by
        simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      _ =
          ∫ ω,
            ∫ s in Set.Ioc (0 : ℝ) T,
              diffusionGenerator (transportDrift Φ b) (transportNoise Φ σ) (F ∘ Φ.symm)
                ((fun t ω => Φ (Y t ω)) s ω) ∂volume ∂P :=
        hEq
      _ = ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, diffusionGenerator b σ F (Y s ω) ∂volume ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        apply integral_congr_ae
        filter_upwards [] with s
        simpa only [Function.comp_apply] using (diffusionGenerator_transport Φ b σ F (Y s ω))

end DynkinTransport

section LinearTransport

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
theorem IsDiffusion.ae_linear_eq_integral_transport
    [FiniteDimensional ℝ V]
    (Φ : V ≃L[ℝ] (Fin N → ℝ))
    {b : V → V} {σ : V → Fin d → V} {x₀ : V}
    (hbc : Continuous b) {B : ℝ} (hbB : ∀ x, ‖b x‖ ≤ B)
    {Y : ℝ → Ω → V}
    (h : IsDiffusion W ℱ hW (transportDrift Φ b) (transportNoise Φ σ) (Φ x₀) (fun t ω => Φ (Y t ω)))
    (ℓ : V →L[ℝ] ℝ) (hℓ : ∀ x k, ℓ (σ x k) = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      ℓ (Y t ω) = ℓ x₀ + ∫ s in Set.Ioc (0 : ℝ) t, ℓ (b (Y s ω)) := by
  classical
  have hbc' : Continuous (transportDrift Φ b) := by
    change Continuous (fun y => Φ (b (Φ.symm y)))
    exact Φ.continuous.comp (hbc.comp Φ.symm.continuous)
  have hbB' : ∀ y, ‖transportDrift Φ b y‖ ≤
      ‖(Φ : V →L[ℝ] (Fin N → ℝ))‖ * B := by
    intro y
    calc
      ‖transportDrift Φ b y‖ = ‖Φ (b (Φ.symm y))‖ := rfl
      _ ≤ ‖(Φ : V →L[ℝ] (Fin N → ℝ))‖ * ‖b (Φ.symm y)‖ :=
        ContinuousLinearMap.le_opNorm (Φ : V →L[ℝ] (Fin N → ℝ)) _
      _ ≤ ‖(Φ : V →L[ℝ] (Fin N → ℝ))‖ * B :=
        mul_le_mul_of_nonneg_left (hbB (Φ.symm y))
          (norm_nonneg (Φ : V →L[ℝ] (Fin N → ℝ)))
  have hℓ' :
      ∀ y k,
        (ℓ.comp (Φ.symm : (Fin N → ℝ) →L[ℝ] V))
            (transportNoise Φ σ y k) = 0 := by
    intro y k
    change ℓ (Φ.symm (Φ (σ (Φ.symm y) k))) = 0
    rw [Φ.symm_apply_apply]
    exact hℓ _ _
  have h' :=
    IsDiffusion.ae_linear_eq_integral hbc' hbB' h
      (ℓ.comp (Φ.symm : (Fin N → ℝ) →L[ℝ] V)) hℓ'
  filter_upwards [h'] with ω hω
  intro t ht
  have hω' := hω t ht
  change ℓ (Φ.symm (Φ (Y t ω))) =
      ℓ (Φ.symm (Φ x₀)) +
        ∫ s in Set.Ioc (0 : ℝ) t,
          ℓ (Φ.symm (transportDrift Φ b (Φ (Y s ω)))) at hω'
  simpa only [ContinuousLinearEquiv.symm_apply_apply, transportDrift] using hω'

end LinearTransport

end Transport

end FunctionalInequalities.Probability.Diffusion
