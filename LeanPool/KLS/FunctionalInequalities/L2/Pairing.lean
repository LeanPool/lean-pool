/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# `L²` pairings of vector fields

Generic facts about the pairing `∫ ⟪a, f⟫ dμ` of two square-integrable fields: identification with
the `L²` inner product, continuity along `L²` convergence, Cauchy–Schwarz, the energy identity
`∫ ‖a‖² = ‖a‖₂²`, and integrability of the pointwise pairing. Used for the Stein-kernel identities
of
Letwin arXiv:2607.24164v1 (Appendix A.7).
-/

@[expose] public section

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology

namespace FunctionalInequalities.L2

/-- The squared norm of a real-inner-product-valued `L²` class is the integral of its
pointwise squared norm. The measure is arbitrary; the target need not be complete. -/
theorem norm_sq_eq_integral_norm_sq {α : Type*} [MeasurableSpace α]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {μ : Measure α} (f : Lp F 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

variable {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {μ : Measure A}

/-- `∫ ⟪a, f⟫ = ⟪a, f⟫_{L²}` for `a, f ∈ L²(μ; E)`. -/
theorem integral_inner_toLp {a f : A → E} (ha : MemLp a 2 μ) (hf : MemLp f 2 μ) :
    (∫ x, ⟪a x, f x⟫ ∂μ) = ⟪ha.toLp a, hf.toLp f⟫ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ha.coeFn_toLp, hf.coeFn_toLp] with x hax hfx
  rw [hax, hfx]

/-- Pairing with a fixed `L²` field is continuous along `L²`-convergent sequences. -/
theorem tendsto_integral_inner_of_eLpNorm_sub {a f : A → E} {seq : ℕ → A → E} (ha : MemLp a 2 μ)
    (hf : MemLp f 2 μ) (hs : ∀ j, MemLp (seq j) 2 μ)
    (hlim : Tendsto (fun j => eLpNorm (fun x => seq j x - f x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, ⟪a x, seq j x⟫ ∂μ) atTop (𝓝 (∫ x, ⟪a x, f x⟫ ∂μ)) := by
  let F : Lp E 2 μ := hf.toLp f
  let S : ℕ → Lp E 2 μ := fun j => (hs j).toLp (seq j)
  have hnorm (j : ℕ) : ‖S j - F‖ = (eLpNorm (fun x => seq j x - f x) 2 μ).toReal := by
    rw [← (hs j).toLp_sub hf]
    exact Lp.norm_toLp _ _
  have hnormlim : Tendsto (fun j => ‖S j - F‖) atTop (𝓝 0) := by
    simp_rw [hnorm]
    simpa only [ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hlim
  have hS : Tendsto S atTop (𝓝 F) := tendsto_iff_norm_sub_tendsto_zero.mpr hnormlim
  have hinner : Tendsto (fun j => ⟪ha.toLp a, S j⟫) atTop (𝓝 ⟪ha.toLp a, F⟫) :=
    (((continuous_const : Continuous (fun _ : Lp E 2 μ => ha.toLp a)).inner
              continuous_id).tendsto
          F).comp
      hS
  simpa only [S, F, ← integral_inner_toLp ha hf, ← integral_inner_toLp ha (hs _)] using
    (hinner : Tendsto (fun j => ⟪ha.toLp a, S j⟫) atTop (𝓝 ⟪ha.toLp a, F⟫))

/-- Cauchy–Schwarz: `|∫ ⟪a, f⟫| ≤ ‖a‖₂ ‖f‖₂`. -/
theorem abs_integral_inner_le {a f : A → E} (ha : MemLp a 2 μ) (hf : MemLp f 2 μ) :
    |∫ x, ⟪a x, f x⟫ ∂μ| ≤ (eLpNorm a 2 μ).toReal * (eLpNorm f 2 μ).toReal := by
  rw [integral_inner_toLp ha hf]
  simpa only [Lp.norm_toLp] using abs_real_inner_le_norm (ha.toLp a) (hf.toLp f)

/-- `∫ ‖a‖² = ‖a‖₂²` for `a ∈ L²`. -/
theorem integral_norm_sq_eq_eLpNorm_sq {a : A → E} (ha : MemLp a 2 μ) :
    (∫ x, ‖a x‖ ^ 2 ∂μ) = (eLpNorm a 2 μ).toReal ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq, Lp.norm_toLp] using integral_inner_toLp ha ha

theorem sqrt_integral_norm_sq_eq {a : A → E} (ha : MemLp a 2 μ) :
    Real.sqrt (∫ x, ‖a x‖ ^ 2 ∂μ) = (eLpNorm a 2 μ).toReal := by
  rw [integral_norm_sq_eq_eLpNorm_sq ha]
  exact Real.sqrt_sq ENNReal.toReal_nonneg

/-- The pointwise pairing of two `L²` fields is integrable. -/
theorem integrable_inner_of_memLp {a f : A → E}
    (ha : MemLp a 2 μ) (hf : MemLp f 2 μ) : Integrable (fun x => ⟪a x, f x⟫) μ := by
  apply (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (ha.toLp a) (hf.toLp f)).congr
  filter_upwards [ha.coeFn_toLp, hf.coeFn_toLp] with x hax hfx
  rw [hax, hfx]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Scalar L2 pairing convergence, expressed using ordinary multiplication. -/
theorem tendsto_integral_mul_of_eLpNorm_sub
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a b : X → ℝ} {u : ℕ → X → ℝ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hu : ∀ m, MemLp (u m) 2 μ)
    (hconv : Tendsto (fun m => eLpNorm (u m - b) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x, a x * u m x ∂μ) atTop
      (𝓝 (∫ x, a x * b x ∂μ)) := by
  simpa only [RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm] using
    tendsto_integral_inner_of_eLpNorm_sub ha hb hu hconv


omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A square-integrable scalar field pairs integrably with a continuous compact
multiplier. Only finiteness of the measure on compact sets is needed. -/
theorem integrable_mul_continuous_of_hasCompactSupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    (ψ : Lp ℝ 2 μ) {q : X → ℝ} (hq : Continuous q) (hqc : HasCompactSupport q) :
    Integrable (fun x => ψ x * q x) μ := by
  have hqL : MemLp q 2 μ := hq.memLp_of_hasCompactSupport hqc
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) ψ (hqL.toLp q)).congr ?_
  filter_upwards [hqL.coeFn_toLp] with x hx
  simp only [hx, Real.inner_apply, mul_comm]

end FunctionalInequalities.L2
