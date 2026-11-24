/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.QuasiPshSingularities
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Order.Filter.Germ.Basic

/-!
# Local holomorphic multiplier integrability

Source: `transcendental-nakamaye-revised-20260831:sec:qpsh`.
We use exactly `|f|² exp(-c φ)`, with no additional factor of two. The weight
is ENNReal-valued: for positive `c` it is infinite when `φ = ⊥`. Its product
with a zero squared norm is zero, the usual convention for nonnegative
Lebesgue integration. In particular no pole is silently replaced by `toReal = 0`.

These are local integrability predicates and a set of actual function germs.
They are not asserted to form a coherent ideal sheaf. Unproved ideal and
singularity-comparison interfaces are isolated in `Pending.MultiplierIdeals`.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis

/-- The manuscript's extended weight `exp(-c φ)`. Positivity of `c` is required
by multiplier membership, not by this total scalar function. -/
noncomputable def multiplierWeight (c : ℝ) (a : EReal) : ℝ≥0∞ :=
  EReal.exp (-((c : EReal) * a))

/-- Nonnegative weighted squared norm, including the convention `0 * ∞ = 0`. -/
noncomputable def multiplierDensity {X : Type*} (φ : X → EReal) (c : ℝ)
    (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal (‖f x‖ ^ 2) * multiplierWeight c (φ x)

@[simp] theorem multiplierWeight_coe (c a : ℝ) :
    multiplierWeight c (a : EReal) = ENNReal.ofReal (Real.exp (-(c * a))) := by
  simp [multiplierWeight, ← EReal.coe_mul, ← EReal.coe_neg]

@[simp] theorem multiplierWeight_bot {c : ℝ} (hc : 0 < c) :
    multiplierWeight c ⊥ = ⊤ := by
  simp [multiplierWeight, EReal.coe_mul_bot_of_pos hc]

@[simp] theorem multiplierWeight_top {c : ℝ} (hc : 0 < c) :
    multiplierWeight c ⊤ = 0 := by
  simp [multiplierWeight, EReal.coe_mul_top_of_pos hc]

theorem multiplierWeight_antitone {c : ℝ} (hc : 0 ≤ c) :
    Antitone (multiplierWeight c) := by
  intro a b hab
  apply EReal.exp_monotone
  exact EReal.neg_le_neg_iff.mpr (mul_le_mul_of_nonneg_left hab (EReal.coe_nonneg.mpr hc))

@[simp] theorem multiplierDensity_zero {X : Type*} (φ : X → EReal) (c : ℝ) (x : X) :
    multiplierDensity φ c (fun _ => 0) x = 0 := by
  simp [multiplierDensity]

theorem multiplierDensity_eq_zero_of_eq_zero {X : Type*} (φ : X → EReal) (c : ℝ)
    {f : X → ℂ} {x : X} (hf : f x = 0) : multiplierDensity φ c f x = 0 := by
  simp [multiplierDensity, hf]

theorem multiplierDensity_eq_top_at_pole {X : Type*} {φ : X → EReal} {c : ℝ}
    {f : X → ℂ} {x : X} (hc : 0 < c) (hφ : φ x = ⊥) (hf : f x ≠ 0) :
    multiplierDensity φ c f x = ⊤ := by
  have hnorm : 0 < ‖f x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hf) _
  unfold multiplierDensity
  rw [hφ, multiplierWeight_bot hc]
  exact ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hnorm))

section LocalL2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Finite weighted L2 mass on a set, with measurability explicitly required. -/
def WeightedL2On (φ : E → EReal) (c : ℝ) (f : E → ℂ) (U : Set E)
    (μ : Measure E) : Prop :=
  AEMeasurable (multiplierDensity φ c f) (μ.restrict U) ∧
    (∫⁻ y in U, multiplierDensity φ c f y ∂μ) < ⊤

/-- A holomorphic representative with weighted L2 mass on an open neighborhood.
The measure is explicit; Lebesgue/Haar measure supplies the usual local notion. -/
def MultiplierIntegrableAt (φ : E → EReal) (c : ℝ) (f : E → ℂ) (x : E)
    (μ : Measure E) : Prop :=
  0 < c ∧ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
    DifferentiableOn ℂ f U ∧ WeightedL2On φ c f U μ

/-- Local multiplier integrability at every point, with ambient holomorphic germs. -/
def MultiplierIntegrableOn (φ : E → EReal) (c : ℝ) (f : E → ℂ) (U : Set E)
    (μ : Measure E) : Prop := ∀ x ∈ U, MultiplierIntegrableAt φ c f x μ

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [BorelSpace E] in
theorem WeightedL2On.mono {φ : E → EReal} {c : ℝ} {f : E → ℂ} {U V : Set E}
    {μ : Measure E} (hf : WeightedL2On φ c f U μ) (hVU : V ⊆ U) :
    WeightedL2On φ c f V μ :=
  ⟨hf.1.mono_measure (Measure.restrict_mono hVU le_rfl),
    (lintegral_mono_set hVU).trans_lt hf.2⟩

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [BorelSpace E] in
theorem weightedL2On_zero (φ : E → EReal) (c : ℝ) (U : Set E) (μ : Measure E) :
    WeightedL2On φ c (fun _ => 0) U μ := by
  have hzero : multiplierDensity φ c (fun _ : E => 0) = fun _ => 0 := by
    funext y
    exact multiplierDensity_zero φ c y
  unfold WeightedL2On
  rw [hzero]
  exact ⟨aemeasurable_const, by simp⟩

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [BorelSpace E] in
/-- Equality on the integration domain suffices, including equality at poles. -/
theorem WeightedL2On.congr {φ ψ : E → EReal} {c : ℝ} {f g : E → ℂ} {U : Set E}
    {μ : Measure E} (hf : WeightedL2On φ c f U μ) (hU : MeasurableSet U)
    (hφ : EqOn φ ψ U) (hfg : EqOn f g U) : WeightedL2On ψ c g U μ := by
  have heq : multiplierDensity φ c f =ᵐ[μ.restrict U] multiplierDensity ψ c g := by
    filter_upwards [ae_restrict_mem hU] with y hy
    simp only [multiplierDensity, hφ hy, hfg hy]
  exact ⟨hf.1.congr heq, (lintegral_congr_ae heq) ▸ hf.2⟩

omit [BorelSpace E] in
theorem multiplierIntegrableAt_zero (φ : E → EReal) {c : ℝ} (hc : 0 < c)
    (x : E) (μ : Measure E) : MultiplierIntegrableAt φ c (fun _ => 0) x μ :=
  ⟨hc, univ, isOpen_univ, mem_univ x, differentiableOn_const _,
    weightedL2On_zero φ c univ μ⟩

/-- Membership is genuinely a germ property in both the potential and the
holomorphic representative. It is not merely equality of real-valued densities. -/
theorem MultiplierIntegrableAt.congr {φ ψ : E → EReal} {c : ℝ} {f g : E → ℂ}
    {x : E} {μ : Measure E} (hf : MultiplierIntegrableAt φ c f x μ)
    (hφ : φ =ᶠ[𝓝 x] ψ) (hfg : f =ᶠ[𝓝 x] g) :
    MultiplierIntegrableAt ψ c g x μ := by
  obtain ⟨hc, U, hU, hxU, hhol, hint⟩ := hf
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp (hφ.and hfg)
  refine ⟨hc, U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_, ?_⟩
  · exact (hhol.mono inter_subset_left).congr (fun y hy => (hVsub hy.2).2.symm)
  · exact (hint.mono inter_subset_left).congr (hU.inter hV).measurableSet
      (fun _ hy => (hVsub hy.2).1) (fun _ hy => (hVsub hy.2).2)

omit [BorelSpace E] in
theorem MultiplierIntegrableOn.mono {φ : E → EReal} {c : ℝ} {f : E → ℂ}
    {U V : Set E} {μ : Measure E} (hf : MultiplierIntegrableOn φ c f U μ)
    (hVU : V ⊆ U) : MultiplierIntegrableOn φ c f V μ :=
  fun x hx => hf x (hVU hx)

/-- The actual set of function germs admitting a holomorphic, weighted-L2
representative. No ideal or coherence structure is asserted here. -/
def multiplierGermSet (φ : E → EReal) (c : ℝ) (x : E) (μ : Measure E) :
    Set (Germ (𝓝 x) ℂ) :=
  {g | ∃ f : E → ℂ, (f : Germ (𝓝 x) ℂ) = g ∧ MultiplierIntegrableAt φ c f x μ}

/-- Germ membership is independent of the chosen representative. -/
theorem mem_multiplierGermSet_iff {φ : E → EReal} {c : ℝ} {f : E → ℂ}
    {x : E} {μ : Measure E} :
    (f : Germ (𝓝 x) ℂ) ∈ multiplierGermSet φ c x μ ↔ MultiplierIntegrableAt φ c f x μ := by
  constructor
  · rintro ⟨g, hgf, hg⟩
    exact hg.congr (Filter.Eventually.of_forall (fun _ => rfl)) (Germ.coe_eq.mp hgf)
  · intro hf
    exact ⟨f, rfl, hf⟩

end LocalL2

end SGPT.Foundations.Analysis
