/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Sequences
import Mathlib.Tactic.NormNum

/-!
# Simultaneous weak limits for pool indicators

A countable family of bounded sequences in a separable real Hilbert space has a
common weakly convergent subsequence.  We prove this using the compact metrizable
weak-dual unit ball and Riesz representation.  In particular, the weak limits
used for the fixed partitions in the pool lemma are obtained from Mathlib's
Banach--Alaoglu theorem, rather than supplied as an additional hypothesis.

For probability-space `L²`, weak limits of functions with values almost
everywhere in `[0,1]` still have values almost everywhere in `[0,1]`.  Testing
against the indicator of a measurable set also gives convergence of every set
integral.  These are the interfaces needed by the fixed-partition construction.
-/

@[expose] public section

noncomputable section

namespace Klr.Pool

open Filter MeasureTheory Set Topology
open scoped ENNReal

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Weak convergence of a sequence in a real inner product space. -/
def WeaklyConverges (u : ℕ → E) (g : E) : Prop :=
  ∀ h : E, Tendsto (fun n => inner ℝ (u n) h) atTop (𝓝 (inner ℝ g h))

theorem WeaklyConverges.subseq {u : ℕ → E} {g : E}
    (hu : WeaklyConverges u g) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    WeaklyConverges (u ∘ φ) g :=
  fun h => (hu h).comp hφ.tendsto_atTop

/-- All sequences in a countable family in the Hilbert unit ball admit one
common weakly convergent subsequence.  The limits remain in the unit ball. -/
theorem exists_simultaneous_weak_subsequence [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (u : ℕ → ℕ → E)
    (hu : ∀ i n, ‖u i n‖ ≤ 1) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → E), StrictMono φ ∧
      (∀ i, ‖g i‖ ≤ 1) ∧ ∀ i, WeaklyConverges (u i ∘ φ) (g i) := by
  let K : Set (WeakDual ℝ E) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) 1
  have hK : IsCompact K := WeakDual.isCompact_closedBall 0 1
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : TopologicalSpace.MetrizableSpace K :=
    WeakDual.metrizable_of_isCompact ℝ E K hK
  let v : ℕ → ℕ → K := fun n i =>
    ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E (u i n)), by
      simpa [K, Metric.mem_closedBall, dist_zero_right] using hu i n⟩
  obtain ⟨vlim, φ, hφ, hvlim⟩ := CompactSpace.tendsto_subseq v
  let g : ℕ → E := fun i =>
    (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual (vlim i).val)
  refine ⟨φ, g, hφ, ?_, ?_⟩
  · intro i
    dsimp [g]
    rw [(InnerProductSpace.toDual ℝ E).symm.norm_map]
    have hb := (vlim i).property
    change dist (WeakDual.toStrongDual (vlim i).val) 0 ≤ 1 at hb
    simpa only [dist_zero_right] using hb
  · intro i h
    have hi' : Tendsto (fun n => v (φ n) i) atTop (𝓝 (vlim i)) :=
      (tendsto_pi_nhds.mp hvlim) i
    have hi : Tendsto (fun n => (v (φ n) i).val) atTop (𝓝 (vlim i).val) :=
      continuous_subtype_val.continuousAt.tendsto.comp hi'
    have he := (WeakDual.eval_continuous h).continuousAt.tendsto.comp hi
    simpa [v, g, Function.comp_def] using he

/-- A scalar convergence already arranged before the simultaneous extraction is
preserved.  This is used after choosing positions whose weighted query
probabilities converge to their limsup. -/
theorem exists_simultaneous_weak_subsequence_preserving [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (u : ℕ → ℕ → E)
    (hu : ∀ i n, ‖u i n‖ ≤ 1) {p : ℕ → ℝ} {pstar : ℝ}
    (hp : Tendsto p atTop (𝓝 pstar)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → E), StrictMono φ ∧
      Tendsto (p ∘ φ) atTop (𝓝 pstar) ∧
      (∀ i, ‖g i‖ ≤ 1) ∧ ∀ i, WeaklyConverges (u i ∘ φ) (g i) := by
  obtain ⟨φ, g, hφ, hg, hconv⟩ := exists_simultaneous_weak_subsequence u hu
  exact ⟨φ, g, hφ, hp.comp hφ.tendsto_atTop, hg, hconv⟩

end Hilbert

section L2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- An `L²` function on a finite measure space is integrable. -/
theorem integrable_L2 (f : Lp ℝ 2 μ) : Integrable f μ := by
  exact memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent (by norm_num))

/-- Weak `L²` convergence implies convergence of every measurable set integral. -/
theorem WeaklyConverges.setIntegral {u : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ}
    (hu : WeaklyConverges u g) {s : Set Ω} (hs : MeasurableSet s) :
    Tendsto (fun n => ∫ x in s, u n x ∂μ) atTop (𝓝 (∫ x in s, g x ∂μ)) := by
  have h := hu (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ))
  have htest (f : Lp ℝ 2 μ) :
      inner ℝ f (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)) =
        ∫ x in s, f x ∂μ := by
    rw [real_inner_comm, L2.inner_indicatorConstLp_one]
  simpa only [htest] using h

/-- Positivity survives weak `L²` convergence. -/
theorem WeaklyConverges.ae_nonneg {u : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ}
    (hu : WeaklyConverges u g) (hu0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ u n x) :
    ∀ᵐ x ∂μ, 0 ≤ g x := by
  refine ae_nonneg_of_forall_setIntegral_nonneg (integrable_L2 g) ?_
  intro s hs _
  exact ge_of_tendsto' (hu.setIntegral hs) fun n =>
    integral_nonneg_of_ae (ae_restrict_of_ae (hu0 n))

/-- An almost everywhere upper bound by one survives weak `L²` convergence. -/
theorem WeaklyConverges.ae_le_one {u : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ}
    (hu : WeaklyConverges u g) (hu1 : ∀ n, ∀ᵐ x ∂μ, u n x ≤ 1) :
    ∀ᵐ x ∂μ, g x ≤ 1 := by
  refine ae_le_of_forall_setIntegral_le (integrable_L2 g) (integrable_const 1) ?_
  intro s hs _
  exact le_of_tendsto' (hu.setIntegral hs) fun n =>
    integral_mono_ae (integrable_L2 (u n)).integrableOn (integrable_const 1)
      (ae_restrict_of_ae (hu1 n))

/-- A probability-space `L²` function with values in `[0,1]` is in the unit ball. -/
theorem norm_le_one_of_ae_unitInterval [IsProbabilityMeasure μ] {f : Lp ℝ 2 μ}
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hf1 : ∀ᵐ x ∂μ, f x ≤ 1) : ‖f‖ ≤ 1 := by
  have hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1 := by
    filter_upwards [hf0, hf1] with x hx0 hx1
    simpa [Real.norm_eq_abs, abs_of_nonneg hx0] using hx1
  simpa [measureUnivNNReal] using
    Lp.norm_le_of_ae_bound (f := f) (by norm_num : (0 : ℝ) ≤ 1) hbound

/-- The common weak subsequence required for the pool lemma, with the interval
bounds on the actual limits proved from weak convergence. -/
theorem exists_unitInterval_weak_limits [IsProbabilityMeasure μ]
    [MeasureTheory.IsSeparable μ] (u : ℕ → ℕ → Lp ℝ 2 μ)
    (hu0 : ∀ i n, ∀ᵐ x ∂μ, 0 ≤ u i n x)
    (hu1 : ∀ i n, ∀ᵐ x ∂μ, u i n x ≤ 1) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Lp ℝ 2 μ), StrictMono φ ∧
      (∀ i, WeaklyConverges (u i ∘ φ) (g i)) ∧
      (∀ i, ∀ᵐ x ∂μ, 0 ≤ g i x) ∧ (∀ i, ∀ᵐ x ∂μ, g i x ≤ 1) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  obtain ⟨φ, g, hφ, _, hconv⟩ := exists_simultaneous_weak_subsequence u
    (fun i n => norm_le_one_of_ae_unitInterval (hu0 i n) (hu1 i n))
  exact ⟨φ, g, hφ, hconv, fun i => (hconv i).ae_nonneg (fun n => hu0 i (φ n)),
    fun i => (hconv i).ae_le_one (fun n => hu1 i (φ n))⟩

end L2

end Klr.Pool
