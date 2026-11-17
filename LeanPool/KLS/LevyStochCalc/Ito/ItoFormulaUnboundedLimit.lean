/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands

/-!
# Itô's formula without a pointwise bound on the coefficients

Passing to the limit along the clamped approximation gives Itô's formula for a vector Itô process
whose diffusion matrix and drift carry no pointwise bound, first for a function with bounded first
and second derivatives and then, by localisation, for an arbitrary `C²` function.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoFormula_of_unbounded_coeff` — Itô's formula with unbounded
  coefficients, for a function with bounded first and second derivatives.
* `LevyStochCalc.Brownian.Ito.itoFormula_of_unbounded` — Itô's formula for a `C²` function of a
  vector Itô process, with no bound on either the coefficients or the derivatives.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Clamped

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Limits

variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)

variable (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

/-- **The stochastic integrals of the clamped approximation converge in `L²`.** -/
theorem tendsto_lintegral_sq_norm_stochInt_clamp
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {T : ℝ} (hT : 0 < T)
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (hmY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s))
    (hpY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s)
    (hqY : ∀ (i : ℕ) (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hmX : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpX : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqX : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (p : Fin n) (k : Fin d) :
    Filter.Tendsto (fun i : ℕ => ∫⁻ ω,
        (‖stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s)
              (hmY i p k) (hpY i p k) (hqY i p k) T ω
            - stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
              (hmX p k) (hpX p k) (hqX p k) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (𝓝 0) := by
  refine Filter.Tendsto.congr (fun i => ?_)
    (tendsto_energy_diffusionIntegrand_clamp hf'c hK₁0 hf'bd hm hq hYm hXm hge hae p k)
  exact (isometry_diff_stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
    (fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s)
    (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hmY i p k) (hmX p k) (hpY i p k) (hpX p k) (hqY i p k) (hqX p k) hT).symm

/-- **Along a further subsequence the stochastic integrals of the clamped approximation converge
almost surely.** -/
theorem exists_seq_ae_tendsto_stochInt_clamp
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {T : ℝ} (hT : 0 < T)
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (hmY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s))
    (hpY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s)
    (hqY : ∀ (i : ℕ) (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hmX : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpX : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqX : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧ ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
      Filter.Tendsto (fun i : ℕ => stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s => coordDeriv f' p (Y (ms i) s ω) * clampCoeff H (ns (ms i)) p k ω s)
          (hmY (ms i) p k) (hpY (ms i) p k) (hqY (ms i) p k) T ω) Filter.atTop
        (𝓝 (stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
          (hmX p k) (hpX p k) (hqX p k) T ω)) := by
  classical
  obtain ⟨ms, hmsge, hms⟩ := exists_seq_ae_tendsto_of_tendsto_lintegral (μ := P)
    (ι := Fin n × Fin d)
    (u := fun i c ω => stochasticIntegralBrownian (W.W c.2) ℱ' (hcoord c.2)
      (fun ω s => coordDeriv f' c.1 (Y i s ω) * clampCoeff H (ns i) c.1 c.2 ω s)
      (hmY i c.1 c.2) (hpY i c.1 c.2) (hqY i c.1 c.2) T ω)
    (v := fun c ω => stochasticIntegralBrownian (W.W c.2) ℱ' (hcoord c.2)
      (fun ω s => coordDeriv f' c.1 (X s ω) * H c.1 c.2 ω s)
      (hmX c.1 c.2) (hpX c.1 c.2) (hqX c.1 c.2) T ω)
    (fun i c => ((stochasticIntegralBrownian_stronglyAdapted (W.W c.2) ℱ' (hcoord c.2) _
      (hmY i c.1 c.2) (hpY i c.1 c.2) (hqY i c.1 c.2) T).mono (ℱ'.le T)).measurable)
    (fun c => ((stochasticIntegralBrownian_stronglyAdapted (W.W c.2) ℱ' (hcoord c.2) _
      (hmX c.1 c.2) (hpX c.1 c.2) (hqX c.1 c.2) T).mono (ℱ'.le T)).measurable)
    (fun c => tendsto_lintegral_sq_norm_stochInt_clamp W ℱ' hcoord hf'c hK₁0 hf'bd hm hT hq
      hYm hXm hge hae hmY hpY hqY hmX hpX hqX c.1 c.2)
  refine ⟨ms, hmsge, ?_⟩
  filter_upwards [hms] with ω hω
  intro p k
  exact hω (p, k)

/-- **Itô's formula for a vector Itô process with unbounded coefficients**, for a function whose
first two derivatives are bounded. -/
theorem itoFormula_of_unbounded_coeff
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    (hf'c : Continuous f') (hf''c : Continuous f'')
    (hf''unif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ z w : Fin n → ℝ, ‖z - w‖ < δ → ‖f'' z - f'' w‖ ≤ ε)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by
  classical
  have hX₀' : ∀ p : Fin n, Measurable fun ω => X₀ ω p :=
    fun p => (hX₀ p).mono (ℱ'.le 0) le_rfl
  have hqT : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ := fun p k => (hHs p k T hT).ne
  have hbqT : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ := fun p => (hbq p T hT).ne
  obtain ⟨ns, hge, hns⟩ := exists_seq_clampMesh_lt hHm hbm hqT hbqT
  -- the versions driven by the clamped coefficients
  have hex : ∀ j : ℕ, ∃ Z : ℝ → Ω → Fin n → ℝ,
      IsVectorItoVersion W ℱ' hcoord (clampCoeff H j)
        (fun p k => measurable_clampCoeff hHm j p k)
        (fun p k => progressivelyMeasurable_clampCoeff hHp j p k)
        (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
        X₀ (clampDrift bdrift j) Z := fun j =>
    exists_isVectorItoVersion W ℱ' hcoord (clampCoeff H j)
      (fun p k => measurable_clampCoeff hHm j p k)
      (fun p k => progressivelyMeasurable_clampCoeff hHp j p k)
      (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
      (Nat.cast_nonneg j) (abs_clampCoeff_le H j) hℱ0 hnull hX₀ (clampDrift bdrift j)
      (fun p => measurable_clampDrift hbm j p)
      (fun p => progressivelyMeasurable_clampDrift hbp j p)
      (Nat.cast_nonneg j) (abs_clampDrift_le bdrift j)
  choose Xj hXj using hex
  have hYm : ∀ i : ℕ, Measurable (Function.uncurry fun ω s => Xj (ns i) s ω) :=
    fun i => (hXj (ns i)).measurable_uncurry
  have hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Xj (ns i) s ω) Filter.atTop (𝓝 (X s ω)) :=
    ae_ae_tendsto_version_clamp W ℱ' hcoord hX₀' hbm hbq h hXj hns
  -- the integrands along the clamped versions
  have hmY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (Xj (ns i) s ω) * clampCoeff H (ns i) p k ω s) :=
    fun i p k => ((hXj (ns i)).measurable_uncurry_comp
      (continuous_coordDeriv hf'c p).measurable).mul (measurable_clampCoeff hHm (ns i) p k)
  have hpY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (Xj (ns i) s ω) * clampCoeff H (ns i) p k ω s :=
    fun i p k => ((hXj (ns i)).progressivelyMeasurable_comp
      (continuous_coordDeriv hf'c p)).mul (progressivelyMeasurable_clampCoeff hHp (ns i) p k)
  have hqY : ∀ (i : ℕ) (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (Xj (ns i) s ω) * clampCoeff H (ns i) p k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ := by
    intro i p k
    refine energy_lt_top_of_bounded (M := K₁ * ((ns i : ℕ) : ℝ)) fun ω s => ?_
    rw [abs_mul]
    exact mul_le_mul (abs_coordDeriv_le hf'bd p _) (abs_clampCoeff_le H (ns i) p k ω s)
      (abs_nonneg _) hK₁0
  -- the polarised coefficients of the clamped model
  have hma : ∀ (i : ℕ) (p q : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => clampCoeff H (ns i) p k ω s + clampCoeff H (ns i) q k ω s) :=
    fun i p q k => (measurable_clampCoeff hHm (ns i) p k).add
      (measurable_clampCoeff hHm (ns i) q k)
  have hpa : ∀ (i : ℕ) (p q : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => clampCoeff H (ns i) p k ω s + clampCoeff H (ns i) q k ω s :=
    fun i p q k => (progressivelyMeasurable_clampCoeff hHp (ns i) p k).add
      (progressivelyMeasurable_clampCoeff hHp (ns i) q k)
  have hqa : ∀ (i : ℕ) (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖clampCoeff H (ns i) p k ω s + clampCoeff H (ns i) q k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ := by
    intro i p q k
    refine energy_lt_top_of_bounded (M := 2 * ((ns i : ℕ) : ℝ)) fun ω s => ?_
    calc |clampCoeff H (ns i) p k ω s + clampCoeff H (ns i) q k ω s|
        ≤ |clampCoeff H (ns i) p k ω s| + |clampCoeff H (ns i) q k ω s| := abs_add_le _ _
      _ ≤ ((ns i : ℕ) : ℝ) + ((ns i : ℕ) : ℝ) :=
          add_le_add (abs_clampCoeff_le H (ns i) p k ω s) (abs_clampCoeff_le H (ns i) q k ω s)
      _ = 2 * ((ns i : ℕ) : ℝ) := by ring
  -- Itô's formula for each clamped model
  have hform : ∀ i : ℕ,
      (fun ω : Ω => f (Xj (ns i) T ω) - f (Xj (ns i) 0 ω)) =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv f' p (Xj (ns i) s ω) * clampDrift bdrift (ns i) p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s => coordDeriv f' p (Xj (ns i) s ω) * clampCoeff H (ns i) p k ω s)
              (hmY i p k) (hpY i p k) (hqY i p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv₂ f'' p q (Xj (ns i) s ω)
                * ∑ k : Fin d, clampCoeff H (ns i) p k ω s
                    * clampCoeff H (ns i) q k ω s ∂volume := fun i =>
    (hXj (ns i)).itoFormula (Nat.cast_nonneg (ns i)) (abs_clampCoeff_le H (ns i)) hX₀'
      (fun p => measurable_clampDrift hbm (ns i) p) (Nat.cast_nonneg (ns i))
      (abs_clampDrift_le bdrift (ns i)) (hma i) (hpa i) (hqa i) hf hf' hf'bd hK₂0 hf''bd
      hf''c hf''unif (hmY i) (hpY i) (hqY i) hT
  obtain ⟨ms, hmsge, hSI⟩ := exists_seq_ae_tendsto_stochInt_clamp W ℱ' hcoord hf'c hK₁0 hf'bd
    hHm hT (fun p k => hHs p k T hT) hYm h.measurable_uncurry hge hae hmY hpY hqY hmg hpg hqg
  have hmsTop : Filter.Tendsto ms Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hmsge Filter.tendsto_id
  have hfc : Continuous f :=
    Differentiable.continuous fun z => (hf z).differentiableAt
  have hTlim : ∀ᵐ ω ∂P, Filter.Tendsto (fun i => Xj (ns i) T ω) Filter.atTop (𝓝 (X T ω)) :=
    ae_tendsto_version_clamp_at W ℱ' hcoord hX₀' hbm hbq h hXj hns hT le_rfl
  have hzeroj : ∀ᵐ ω ∂P, ∀ j : ℕ, Xj j 0 ω = X₀ ω :=
    MeasureTheory.ae_all_iff.mpr fun j => version_ae_eq_zero W ℱ' hcoord (hXj j)
  have hzeroX : X 0 =ᵐ[P] X₀ := version_ae_eq_zero W ℱ' hcoord h
  have hdrift := ae_tendsto_drift_clamp hf'c hf'bd hbm (fun p => hbq p T hT) hYm
    hge hae
  have hqv := ae_tendsto_quadVar_clamp hf''c hK₂0 hf''bd hHm (fun p k => hHs p k T hT) hYm
    hge hae
  filter_upwards [MeasureTheory.ae_all_iff.mpr hform, hTlim, hzeroj, hzeroX, hdrift, hqv, hSI]
    with ω h1 h2 h3 h4 h5 h6 h7
  have hlhs : Filter.Tendsto
      (fun i : ℕ => f (Xj (ns (ms i)) T ω) - f (Xj (ns (ms i)) 0 ω)) Filter.atTop
      (𝓝 (f (X T ω) - f (X 0 ω))) := by
    have hzeroeq : ∀ i : ℕ, f (Xj (ns (ms i)) 0 ω) = f (X 0 ω) := by
      intro i
      rw [h3 (ns (ms i)), h4]
    have hTt : Filter.Tendsto (fun i : ℕ => f (Xj (ns (ms i)) T ω)) Filter.atTop
        (𝓝 (f (X T ω))) := (hfc.continuousAt.tendsto.comp h2).comp hmsTop
    have hconst : Filter.Tendsto (fun i : ℕ => f (Xj (ns (ms i)) 0 ω)) Filter.atTop
        (𝓝 (f (X 0 ω))) := by
      refine Filter.Tendsto.congr (fun i => (hzeroeq i).symm) ?_
      exact tendsto_const_nhds
    exact hTt.sub hconst
  have hrhs : Filter.Tendsto (fun i : ℕ =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (Xj (ns (ms i)) s ω) * clampDrift bdrift (ns (ms i)) p ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s => coordDeriv f' p (Xj (ns (ms i)) s ω)
              * clampCoeff H (ns (ms i)) p k ω s)
            (hmY (ms i) p k) (hpY (ms i) p k) (hqY (ms i) p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (Xj (ns (ms i)) s ω)
              * ∑ k : Fin d, clampCoeff H (ns (ms i)) p k ω s
                  * clampCoeff H (ns (ms i)) q k ω s ∂volume) Filter.atTop
      (𝓝 ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv₂ f'' p q (X s ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)) := by
    refine ((tendsto_finsetSum _ fun p _ => (h5 p).comp hmsTop).add
      (tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun k _ => h7 p k)).add ?_
    exact (tendsto_finsetSum _ fun p _ =>
      tendsto_finsetSum _ fun q _ => (h6 p q).comp hmsTop).const_mul _
  exact tendsto_nhds_unique (Filter.Tendsto.congr (fun i => h1 (ms i)) hlhs) hrhs

/-- **Itô's formula for a twice continuously differentiable function of a vector Itô process
with unbounded coefficients.** -/
theorem itoFormula_of_unbounded
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume :=
  h.itoFormula_localise hfC hf hf' hmg hpg hqg hT
    (fun _g _g' _g'' _K₁ _K₂ hgf hgf' hK₁ hK₂0 hK₂ hg'c hg''c hunif hmG hpG hqG =>
      itoFormula_of_unbounded_coeff W ℱ' hcoord h hℱ0 hnull hX₀ hbm hbp hbq hgf hgf'
        (le_trans (norm_nonneg _) (hK₁ 0)) hK₁ hK₂0 hK₂ hg'c hg''c hunif hmG hpG hqG hT)

end Limits

end Clamped

end LevyStochCalc.Brownian.Ito
