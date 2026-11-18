/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Coefficients
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Transport
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Setup
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Existence
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Dynkin
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Covariance
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Regularity
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Generator
/-!
# The cutoff Eldan localization process

`IsEldanCutoff μ hc W ℱ hW γ p`: the parameter process `p_t = (c_t, Q_t)` solves the cutoff
localization equations
(67) (drift `γ² (A⁻¹a, A⁻¹)`, noise `γ (A^{-1/2} e_k, 0)`, start `0`) in coordinates; existence for
every admissible
cutoff, continuity of paths, initial value, and Dynkin's identity `E F(p_T) − F(0) = E ∫₀ᵀ γ(p_s)²
𝓛F(p_s) ds` for
every `C²` function (BKL arXiv:2610.05474v1, Section 4, cutoff stage).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.KLS.BKL.Localization

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

/--
**The cutoff Eldan process** (BKL arXiv:2610.05474v1, (67), with cutoff coefficients `γ² · drift`,
`γ · noise`)
in parameter-space form: its coordinates under `stateEquiv (Param n)` form an `IsDiffusion` with the
transported cutoff coefficients, started at `p₀ = (0, 0)`. -/
def IsEldanCutoff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : MultidimBrownianMotion P n) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ) (γ : Param n → ℝ) (p : ℝ → Ω → Param n) : Prop :=
  IsDiffusion W ℱ hW (transportDrift (stateEquiv (Param n)) (cutoffDrift μ hc γ))
    (transportNoise (stateEquiv (Param n)) (cutoffNoise μ hc γ)) (stateEquiv (Param n) 0)
    (fun t ω => stateEquiv (Param n) (p t ω))

/--
**Existence of the cutoff Eldan process** on any Brownian setup with a usual filtration, for a
compactly
supported isotropic prior and an admissible cutoff. -/
theorem exists_isEldanCutoff (hiso : KLS.Isotropic μ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (W : MultidimBrownianMotion P n)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) {γ : Param n → ℝ}
    (hγ : IsCutoff γ) : ∃ p : ℝ → Ω → Param n, IsEldanCutoff μ hc W ℱ hW γ p := by
  classical
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) := stateEquiv (Param n)
  obtain ⟨⟨K, hK, hKσ⟩, ⟨B, hB⟩, _, _⟩ := cutoffCoefficients_admissible μ hc hiso hγ
  let K' : ℝ≥0 :=
    ‖(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))‖₊ *
      (K * ‖(Φ.symm : (Fin (Module.finrank ℝ (Param n)) → ℝ) →L[ℝ] Param n)‖₊)
  have hbt : LipschitzWith K' (transportDrift Φ (cutoffDrift μ hc γ)) := by
    change LipschitzWith K' (fun y => Φ (cutoffDrift μ hc γ (Φ.symm y)))
    have he :
      (⇑(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ)) ∘
          cutoffDrift μ hc γ ∘
            ⇑(Φ.symm : (Fin (Module.finrank ℝ (Param n)) → ℝ) →L[ℝ] Param n)) =
        (fun y => Φ (cutoffDrift μ hc γ (Φ.symm y))) := by
      funext y
      rfl
    rw [← he]
    exact
      (ContinuousLinearMap.lipschitzWith
            (Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))).comp
        (hK.comp
          (ContinuousLinearMap.lipschitzWith
            (Φ.symm : (Fin (Module.finrank ℝ (Param n)) → ℝ) →L[ℝ] Param n)))
  have hσt : ∀ k, LipschitzWith K' (fun y => transportNoise Φ (cutoffNoise μ hc γ) y k) := by
    intro k
    change LipschitzWith K' (fun y => Φ (cutoffNoise μ hc γ (Φ.symm y) k))
    have he :
      (⇑(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ)) ∘
          (fun p => cutoffNoise μ hc γ p k) ∘
            ⇑(Φ.symm : (Fin (Module.finrank ℝ (Param n)) → ℝ) →L[ℝ] Param n)) =
        (fun y => Φ (cutoffNoise μ hc γ (Φ.symm y) k)) := by
      funext y
      rfl
    rw [← he]
    exact
      (ContinuousLinearMap.lipschitzWith
            (Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))).comp
        ((hKσ k).comp
          (ContinuousLinearMap.lipschitzWith
            (Φ.symm : (Fin (Module.finrank ℝ (Param n)) → ℝ) →L[ℝ] Param n)))
  have hbtB :
    ∀ y,
      ‖transportDrift Φ (cutoffDrift μ hc γ) y‖ ≤
        ‖(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))‖ * B := by
    intro y
    calc
      ‖transportDrift Φ (cutoffDrift μ hc γ) y‖ = ‖Φ (cutoffDrift μ hc γ (Φ.symm y))‖ := rfl
      _ ≤
          ‖(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))‖ *
            ‖cutoffDrift μ hc γ (Φ.symm y)‖ :=
        ContinuousLinearMap.le_opNorm (Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))
          _
      _ ≤ ‖(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))‖ * B :=
        mul_le_mul_of_nonneg_left (hB (Φ.symm y)).1
          (norm_nonneg (Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ)))
  have hσtB :
    ∀ y k,
      ‖transportNoise Φ (cutoffNoise μ hc γ) y k‖ ≤
        ‖(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))‖ * B := by
    intro y k
    calc
      ‖transportNoise Φ (cutoffNoise μ hc γ) y k‖ = ‖Φ (cutoffNoise μ hc γ (Φ.symm y) k)‖ := rfl
      _ ≤
          ‖(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))‖ *
            ‖cutoffNoise μ hc γ (Φ.symm y) k‖ :=
        ContinuousLinearMap.le_opNorm (Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))
          _
      _ ≤ ‖(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))‖ * B :=
        mul_le_mul_of_nonneg_left ((hB (Φ.symm y)).2 k)
          (norm_nonneg (Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ)))
  obtain ⟨Y, hY⟩ :=
    FunctionalInequalities.Probability.Diffusion.exists_isDiffusion W ℱ hW hℱ0 hnull hbt hσt
      hbtB hσtB (Φ 0)
  refine ⟨fun t ω => Φ.symm (Y t ω), ?_⟩
  change
    IsDiffusion W ℱ hW (transportDrift Φ (cutoffDrift μ hc γ))
      (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0) (fun t ω => Φ (Φ.symm (Y t ω)))
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hY

section Process

variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {γ : Param n → ℝ} {p : ℝ → Ω → Param n}

/-- Paths of the cutoff Eldan process are continuous everywhere. -/
theorem IsEldanCutoff.continuous (h : IsEldanCutoff μ hc W ℱ hW γ p) (ω : Ω) :
    Continuous fun t => p t ω := by
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) :=
    stateEquiv (Param n)
  change IsDiffusion W ℱ hW
    (transportDrift Φ (cutoffDrift μ hc γ))
    (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0)
    (fun t ω => Φ (p t ω)) at h
  have hp := IsDiffusion.continuous_path h ω
  have hp' := Φ.symm.continuous.comp hp
  have he :
      (Φ.symm ∘ (fun t => Φ (p t ω))) =
        (fun t => Φ.symm (Φ (p t ω))) := by
    funext t
    rfl
  rw [he] at hp'
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hp'

/-- The cutoff Eldan process starts at `p₀ = 0` almost surely. -/
theorem IsEldanCutoff.ae_initial (h : IsEldanCutoff μ hc W ℱ hW γ p) :
    ∀ᵐ ω ∂P, p 0 ω = 0 := by
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) :=
    stateEquiv (Param n)
  change IsDiffusion W ℱ hW
    (transportDrift Φ (cutoffDrift μ hc γ))
    (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0)
    (fun t ω => Φ (p t ω)) at h
  filter_upwards [IsDiffusion.ae_initial h] with ω hω
  apply Φ.injective
  simpa only [Function.comp_apply] using hω

/--
**Dynkin's identity for the cutoff Eldan process**: for every `C²` `F : Param n → ℝ` (no growth
condition:
the cutoff coefficients have compact support), `F(p_T)` is integrable and
`E F(p_T) − F(0) = E ∫₀ᵀ γ(p_s)² 𝓛F(p_s) ds` with the uncut generator `𝓛` of (67). -/
theorem IsEldanCutoff.dynkin (hiso : KLS.Isotropic μ) (hγ : IsCutoff γ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (h : IsEldanCutoff μ hc W ℱ hW γ p) {F : Param n → ℝ} (hF : ContDiff ℝ 2 F) {T : ℝ}
    (hT : 0 ≤ T) :
    Integrable (fun ω => F (p T ω)) P ∧
      ∫ ω, F (p T ω) ∂P - F 0 =
        ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, γ (p s ω) ^ 2 * generator μ hc F (p s ω) ∂volume ∂P := by
  classical
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) := stateEquiv (Param n)
  obtain ⟨⟨_, hK, hKσ⟩, _, hbs, hσs⟩ := cutoffCoefficients_admissible μ hc hiso hγ
  have hbc : Continuous (cutoffDrift μ hc γ) := hK.continuous
  have hσc : ∀ k, Continuous fun p => cutoffNoise μ hc γ p k := by
    intro k
    exact (hKσ k).continuous
  change
    IsDiffusion W ℱ hW (transportDrift Φ (cutoffDrift μ hc γ))
      (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0) (fun t ω => Φ (p t ω)) at h
  obtain ⟨hInt, hEq⟩ :=
    FunctionalInequalities.Probability.Diffusion.IsDiffusion.dynkin_transport (W := W) (ℱ := ℱ)
      (hW := hW) (Y := p) (x₀ := 0) Φ hℱ0 hnull hbc hσc hbs hσs h hF hT
  refine ⟨hInt, ?_⟩
  calc
    ∫ ω, F (p T ω) ∂P - F 0 =
        ∫ ω,
          ∫ s in Set.Ioc (0 : ℝ) T,
            diffusionGenerator (cutoffDrift μ hc γ) (cutoffNoise μ hc γ) F (p s ω) ∂volume ∂P :=
      hEq
    _ = ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, γ (p s ω) ^ 2 * generator μ hc F (p s ω) ∂volume ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      apply integral_congr_ae
      filter_upwards [] with s
      rw [diffusionGenerator_cutoff]

end Process

end FunctionalInequalities.KLS.BKL.Localization

section EldanParameterPositiveSemidefinite

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion

/-! `Q_t = ∫₀ᵗ γ² A⁻¹` pathwise, hence symmetric positive semidefinite. -/

namespace FunctionalInequalities.KLS.BKL.Localization

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

section Process

variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {γ : Param n → ℝ} {p : ℝ → Ω → Param n}

/-- **The `Q`-component is a pathwise integral of the drift** (no noise acts on `Q` in (67)):
`⟪Q_t x, y⟫ = ∫₀ᵗ γ(p_s)² ⟪A(p_s)⁻¹ x, y⟫ ds` for all `t ≥ 0` and all `x, y`, almost surely. -/
theorem IsEldanCutoff.ae_inner_Q_eq_integral (hiso : KLS.Isotropic μ) (hγ : IsCutoff γ)
    (h : IsEldanCutoff μ hc W ℱ hW γ p) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ x y : EuclideanSpace ℝ (Fin n),
      ⟪(p t ω).2 x, y⟫ =
        ∫ s in Set.Ioc (0 : ℝ) t, γ (p s ω) ^ 2 * ⟪Ring.inverse (cov μ hc (p s ω)) x, y⟫ := by
  classical
  obtain ⟨⟨_, hKb, _⟩, ⟨B, hB⟩, _, _⟩ :=
    cutoffCoefficients_admissible μ hc hiso hγ
  let Φ := stateEquiv (Param n)
  have hb : Continuous (transportDrift Φ (cutoffDrift μ hc γ)) :=
    Φ.continuous.comp (hKb.continuous.comp Φ.symm.continuous)
  have hB' : ∀ z,
      ‖transportDrift Φ (cutoffDrift μ hc γ) z‖ ≤
        ‖Φ.toContinuousLinearMap‖ * B := by
    intro z
    change ‖Φ (cutoffDrift μ hc γ (Φ.symm z))‖ ≤
      ‖Φ.toContinuousLinearMap‖ * B
    calc
      ‖Φ (cutoffDrift μ hc γ (Φ.symm z))‖
          ≤ ‖Φ.toContinuousLinearMap‖ *
              ‖cutoffDrift μ hc γ (Φ.symm z)‖ :=
        Φ.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖Φ.toContinuousLinearMap‖ * B :=
        mul_le_mul_of_nonneg_left (hB (Φ.symm z)).1 (norm_nonneg _)
  have hdiff :
      IsDiffusion W ℱ hW
        (transportDrift Φ (cutoffDrift μ hc γ))
        (transportNoise Φ (cutoffNoise μ hc γ))
        (Φ 0) (fun t ω => Φ (p t ω)) := h
  have hfixed (x y : EuclideanSpace ℝ (Fin n)) :
      ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
        ⟪(p t ω).2 x, y⟫ =
          ∫ s in Set.Ioc (0 : ℝ) t,
            γ (p s ω) ^ 2 * ⟪Ring.inverse (cov μ hc (p s ω)) x, y⟫ := by
    let L : Param n →L[ℝ] ℝ :=
      (innerSL ℝ y).comp
        ((ContinuousLinearMap.apply ℝ _ x).comp
          (ContinuousLinearMap.snd ℝ _ _))
    let L' : (Fin (Module.finrank ℝ (Param n)) → ℝ) →L[ℝ] ℝ :=
      L.comp Φ.symm.toContinuousLinearMap
    have hcoord (q : Param n) : L' (Φ q) = ⟪q.2 x, y⟫ := by
      change ⟪y, (Φ.symm (Φ q)).2 x⟫ = ⟪q.2 x, y⟫
      rw [Φ.symm_apply_apply]
      exact real_inner_comm _ _
    have hL : ∀ z k,
        L' (transportNoise Φ (cutoffNoise μ hc γ) z k) = 0 := by
      intro z k
      change L' (Φ (cutoffNoise μ hc γ (Φ.symm z) k)) = 0
      rw [hcoord]
      change ⟪γ (Φ.symm z) • (0 : EuclideanSpace ℝ (Fin n)), y⟫ = 0
      rw [real_inner_smul_left, inner_zero_left, mul_zero]
    have hinit : L' (Φ 0) = 0 := by
      rw [hcoord]
      change ⟪(0 : EuclideanSpace ℝ (Fin n)), y⟫ = 0
      exact inner_zero_left _
    have hdrift (q : Param n) :
        L' (transportDrift Φ (cutoffDrift μ hc γ) (Φ q)) =
          γ q ^ 2 * ⟪Ring.inverse (cov μ hc q) x, y⟫ := by
      change L' (Φ (cutoffDrift μ hc γ (Φ.symm (Φ q)))) = _
      rw [Φ.symm_apply_apply, hcoord]
      change ⟪(γ q ^ 2 • Ring.inverse (cov μ hc q)) x, y⟫ = _
      rw [smul_apply, real_inner_smul_left]
    have ha := IsDiffusion.ae_linear_eq_integral hb hB' hdiff L' hL
    filter_upwards [ha] with ω hω
    intro t ht
    have he := hω t ht
    rw [hinit, zero_add, hcoord] at he
    simpa only [hdrift] using he
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hbasis :
      ∀ᵐ ω ∂P, ∀ i j : Fin n, ∀ t : ℝ, 0 ≤ t →
        ⟪(p t ω).2 (b i), b j⟫ =
          ∫ s in Set.Ioc (0 : ℝ) t,
            γ (p s ω) ^ 2 *
              ⟪Ring.inverse (cov μ hc (p s ω)) (b i), b j⟫ := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    exact hfixed (b i) (b j)
  filter_upwards [hbasis] with ω hω
  intro t ht x y
  let ax : Fin n → ℝ := fun i => (b.repr x).ofLp i
  let ay : Fin n → ℝ := fun j => (b.repr y).ofLp j
  have hx : ∑ i, ax i • b i = x := b.sum_repr x
  have hy : ∑ j, ay j • b j = y := b.sum_repr y
  have hexpand (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      ⟪T x, y⟫ = ∑ i, ∑ j, ax i * ay j * ⟪T (b i), b j⟫ := by
    calc
      ⟪T x, y⟫ = ⟪T (∑ i, ax i • b i), ∑ j, ay j • b j⟫ := by
        rw [hx, hy]
      _ = ∑ i, ∑ j, ax i * ay j * ⟪T (b i), b j⟫ := by
        simp only [map_sum, map_smul, sum_inner, inner_sum,
          real_inner_smul_left, real_inner_smul_right, mul_assoc]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hp : Continuous (fun s : ℝ => p s ω) := by
    obtain ⟨_, _, _, hv⟩ := hdiff
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
      Φ.symm.continuous.comp (hv.continuous_path ω)
  obtain ⟨_, hγL⟩ := hγ.lipschitz
  have hg : Continuous (fun s : ℝ => γ (p s ω)) :=
    hγL.continuous.comp hp
  have hi : Continuous (fun q : Param n => Ring.inverse (cov μ hc q)) := by
    simpa only [cov] using
      (KLS.Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso).continuous
  have hcont (i j : Fin n) :
      Continuous fun s : ℝ =>
        γ (p s ω) ^ 2 *
          ⟪Ring.inverse (cov μ hc (p s ω)) (b i), b j⟫ :=
    (hg.pow 2).mul
      (((hi.comp hp).clm_apply continuous_const).inner continuous_const)
  have hint (i j : Fin n) :
      IntegrableOn
        (fun s : ℝ =>
          γ (p s ω) ^ 2 *
            ⟪Ring.inverse (cov μ hc (p s ω)) (b i), b j⟫)
        (Set.Ioc (0 : ℝ) t) volume :=
    (hcont i j).integrableOn_Ioc
  have hsum_cont (i : Fin n) :
      Continuous (fun s : ℝ =>
        ∑ j, ax i * ay j *
          (γ (p s ω) ^ 2 *
            ⟪Ring.inverse (cov μ hc (p s ω)) (b i), b j⟫)) := by
    fun_prop
  have hsum_int (i : Fin n) :
      IntegrableOn
        (fun s : ℝ =>
          ∑ j, ax i * ay j *
            (γ (p s ω) ^ 2 *
              ⟪Ring.inverse (cov μ hc (p s ω)) (b i), b j⟫))
        (Set.Ioc (0 : ℝ) t) volume :=
    (hsum_cont i).integrableOn_Ioc
  calc
    ⟪(p t ω).2 x, y⟫ =
        ∑ i, ∑ j, ax i * ay j * ⟪(p t ω).2 (b i), b j⟫ :=
      hexpand _
    _ = ∑ i, ∑ j, ax i * ay j *
        ∫ s in Set.Ioc (0 : ℝ) t,
          γ (p s ω) ^ 2 *
            ⟪Ring.inverse (cov μ hc (p s ω)) (b i), b j⟫ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hω i j t ht]
    _ = ∑ i, ∫ s in Set.Ioc (0 : ℝ) t,
        ∑ j, ax i * ay j *
          (γ (p s ω) ^ 2 *
            ⟪Ring.inverse (cov μ hc (p s ω)) (b i), b j⟫) := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
    _ = ∫ s in Set.Ioc (0 : ℝ) t,
        ∑ i, ∑ j, ax i * ay j *
          (γ (p s ω) ^ 2 *
            ⟪Ring.inverse (cov μ hc (p s ω)) (b i), b j⟫) := by
      symm
      rw [integral_finsetSum _ (fun i _ => hsum_int i)]
    _ = ∫ s in Set.Ioc (0 : ℝ) t,
        γ (p s ω) ^ 2 *
          ⟪Ring.inverse (cov μ hc (p s ω)) x, y⟫ := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [hexpand]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/--
**`Q_t` is symmetric positive semidefinite** along the cutoff Eldan process (BKL p. 19: "each `μ_t`
is
log-concave since `Q_t ≥ 0`"). -/
theorem IsEldanCutoff.ae_Q_posSemidef (hiso : KLS.Isotropic μ) (hγ : IsCutoff γ)
    (h : IsEldanCutoff μ hc W ℱ hW γ p) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → IsSelfAdjoint (p t ω).2 ∧ ∀ x, 0 ≤ ⟪(p t ω).2 x, x⟫ := by
  filter_upwards [IsEldanCutoff.ae_inner_Q_eq_integral hiso hγ h] with ω hω
  intro t ht
  have hself : IsSelfAdjoint (p t ω).2 := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    change ⟪(p t ω).2 x, y⟫ = ⟪x, (p t ω).2 y⟫
    calc
      ⟪(p t ω).2 x, y⟫ =
          ∫ s in Set.Ioc (0 : ℝ) t, γ (p s ω) ^ 2 * ⟪Ring.inverse (cov μ hc (p s ω)) x, y⟫ :=
        hω t ht x y
      _ = ∫ s in Set.Ioc (0 : ℝ) t, γ (p s ω) ^ 2 * ⟪Ring.inverse (cov μ hc (p s ω)) y, x⟫ := by
        apply integral_congr_ae
        filter_upwards [] with s
        have hs : IsSelfAdjoint (Ring.inverse (cov μ hc (p s ω))) :=
          (KLS.Isotropic.compactPosterior_ringInverse_covariance μ hc hiso (p s ω).1
                  (p s ω).2).2.2.1
        have hsym :
          ⟪Ring.inverse (cov μ hc (p s ω)) x, y⟫ = ⟪Ring.inverse (cov μ hc (p s ω)) y, x⟫ := by
          have hlin := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hs) x y
          exact hlin.trans (real_inner_comm _ _)
        exact congrArg (fun r : ℝ => γ (p s ω) ^ 2 * r) hsym
      _ = ⟪(p t ω).2 y, x⟫ := (hω t ht y x).symm
      _ = ⟪x, (p t ω).2 y⟫ := real_inner_comm _ _
  refine ⟨hself, ?_⟩
  intro x
  rw [hω t ht x x]
  apply setIntegral_nonneg measurableSet_Ioc
  intro s _
  have hpos : 0 ≤ ⟪Ring.inverse (cov μ hc (p s ω)) x, x⟫ := by
    by_cases hx : x = 0
    · simp [hx]
    · exact
        ((KLS.Isotropic.compactPosterior_ringInverse_covariance μ hc hiso (p s ω).1
                    (p s ω).2).2.2.2
            x hx).le
  exact mul_nonneg (sq_nonneg _) hpos

end Process

end FunctionalInequalities.KLS.BKL.Localization

end EldanParameterPositiveSemidefinite
