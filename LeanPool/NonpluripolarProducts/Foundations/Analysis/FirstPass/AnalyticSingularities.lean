/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.LogPole
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.QuasiPshSingularities
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Local logarithmic generators and analytic-singularity conventions

Sources: `transcendental-nakamaye-revised-20260831:sec:qpsh` and
`transcendental-nakamaye-revised-20260831:eq:def-restricted-volume`.

These are presentations by actual finite families of holomorphic functions.
They do not assert the existence of a global coherent ideal, its integral
closure, or a principalization. The rational-coefficient, bounded-remainder
condition describes singularity type only; it does not imply quasi-PSH.
The local expression in [Collins–Tosatti, §2](https://www.numdam.org/item/10.5802/afst.1708.pdf#page=8)
uses a positive real coefficient and a smooth real remainder. The paper also
requires the generators to come from a coherent ideal sheaf. This file models
the local expression and a weaker variant with a bounded, off-pole smooth remainder.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators ContDiff

namespace SGPT.Foundations.Analysis

section FiniteGenerators

variable {X : Type*} {n : ℕ}

/-- The actual Euclidean vector of values of a finite family of generators. -/
def generatorVector (f : Fin n → X → ℂ) (x : X) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun j => f j x)

/-- The finite sum of squared absolute values, before taking its logarithm. -/
def generatorNormSq (f : Fin n → X → ℂ) (x : X) : ℝ := ∑ j, ‖f j x‖ ^ 2

/-- The existing extended logarithmic pole applied to the vector of generators. -/
def generatorLog (f : Fin n → X → ℂ) (x : X) : EReal :=
  logNormSq (generatorVector f x)

theorem generatorVector_norm_sq (f : Fin n → X → ℂ) (x : X) :
    ‖generatorVector f x‖ ^ 2 = generatorNormSq f x := by
  simpa [generatorVector, generatorNormSq] using
    EuclideanSpace.norm_sq_eq (generatorVector f x)

theorem generatorNormSq_nonneg (f : Fin n → X → ℂ) (x : X) :
    0 ≤ generatorNormSq f x := by
  rw [← generatorVector_norm_sq]
  exact sq_nonneg _

/-- This is exactly `log (∑ j, |f j|²)`, including the value at zero. -/
theorem generatorLog_eq_log_sum (f : Fin n → X → ℂ) (x : X) :
    generatorLog f x = ENNReal.log (ENNReal.ofReal (∑ j, ‖f j x‖ ^ 2)) := by
  simp only [generatorLog, logNormSq, generatorVector_norm_sq, generatorNormSq]

@[simp] theorem generatorVector_eq_zero_iff (f : Fin n → X → ℂ) (x : X) :
    generatorVector f x = 0 ↔ ∀ j, f j x = 0 := by
  constructor
  · intro h j
    exact congrArg (fun v : EuclideanSpace ℂ (Fin n) => v j) h
  · intro h
    ext j
    exact h j

@[simp] theorem generatorLog_eq_bot_iff (f : Fin n → X → ℂ) (x : X) :
    generatorLog f x = ⊥ ↔ ∀ j, f j x = 0 := by
  simp [generatorLog]

theorem generatorLog_ne_top (f : Fin n → X → ℂ) (x : X) :
    generatorLog f x ≠ ⊤ := logNormSq_ne_top _

theorem generatorLog_of_nonzero {f : Fin n → X → ℂ} {x : X}
    (hf : ∃ j, f j x ≠ 0) :
    generatorLog f x = (Real.log (generatorNormSq f x) : EReal) := by
  have hv : generatorVector f x ≠ 0 := by
    intro h
    exact hf.elim (fun j hj => hj ((generatorVector_eq_zero_iff f x).mp h j))
  simpa only [generatorLog, generatorVector_norm_sq] using logNormSq_of_ne_zero hv

/-- Positive scaling and a finite real remainder preserve exactly the common zeros. -/
theorem scaled_generatorLog_add_eq_bot_iff (f : Fin n → X → ℂ) (x : X)
    {c : ℝ} (hc : 0 < c) (b : ℝ) :
    (c : EReal) * generatorLog f x + (b : EReal) = ⊥ ↔ ∀ j, f j x = 0 := by
  have hc' : (0 : EReal) < (c : EReal) := EReal.coe_pos.mpr hc
  simp [EReal.add_eq_bot_iff, EReal.mul_eq_bot, hc', not_lt.mpr hc'.le]

end FiniteGenerators

section BoundedGerms

variable {X : Type*} [TopologicalSpace X]

/-- A real germ with one finite absolute bound on some neighborhood. -/
def BoundedRealGermAt (b : X → ℝ) (x : X) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, |b y| ≤ C

theorem boundedRealGermAt_of_continuousAt {b : X → ℝ} {x : X}
    (hb : ContinuousAt b x) : BoundedRealGermAt b x := by
  refine ⟨|b x| + 1, by positivity, ?_⟩
  have h := hb.abs.eventually_lt continuousAt_const (lt_add_one (|b x|))
  exact h.mono (fun _ hy => hy.le)

/-- Bounded germs are closed under sums. -/
theorem BoundedRealGermAt.add {b d : X → ℝ} {x : X} (hb : BoundedRealGermAt b x)
    (hd : BoundedRealGermAt d x) : BoundedRealGermAt (fun y => b y + d y) x := by
  obtain ⟨C, hC, hbC⟩ := hb
  obtain ⟨D, hD, hdD⟩ := hd
  refine ⟨C + D, by linarith, ?_⟩
  filter_upwards [hbC, hdD] with y hy hy'
  exact (abs_add_le _ _).trans (by linarith)

/-- Bounded germs are closed under differences. -/
theorem BoundedRealGermAt.sub {b d : X → ℝ} {x : X} (hb : BoundedRealGermAt b x)
    (hd : BoundedRealGermAt d x) : BoundedRealGermAt (fun y => b y - d y) x := by
  obtain ⟨C, hC, hbC⟩ := hb
  obtain ⟨D, hD, hdD⟩ := hd
  refine ⟨C + D, by linarith, ?_⟩
  filter_upwards [hbC, hdD] with y hy hy'
  exact (abs_sub _ _).trans (by linarith)

/-- A bounded germ pulls back along a map continuous at the point. -/
theorem BoundedRealGermAt.comp_continuousAt {Y : Type*} [TopologicalSpace Y] {b : X → ℝ}
    {F : Y → X} {y : Y} (hb : BoundedRealGermAt b (F y)) (hF : ContinuousAt F y) :
    BoundedRealGermAt (fun z => b (F z)) y := by
  obtain ⟨C, hC, hbC⟩ := hb
  exact ⟨C, hC, hF.eventually hbC⟩

/-- Two additive comparisons of germs, using the existing singularity order. -/
def SameSingularityTypeAt (u v : X → EReal) (x : X) : Prop :=
  MoreSingularAt u v x ∧ MoreSingularAt v u x

theorem SameSingularityTypeAt.symm {u v : X → EReal} {x : X}
    (h : SameSingularityTypeAt u v x) : SameSingularityTypeAt v u x := ⟨h.2, h.1⟩

theorem SameSingularityTypeAt.trans {u v w : X → EReal} {x : X}
    (h : SameSingularityTypeAt u v x) (h' : SameSingularityTypeAt v w x) :
    SameSingularityTypeAt u w x := ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-- No subtraction of infinite values is needed to compare bounded perturbations. -/
theorem sameSingularityTypeAt_of_bounded_remainder {u v : X → EReal}
    {b : X → ℝ} {x : X} (hb : BoundedRealGermAt b x)
    (hu : u =ᶠ[𝓝 x] (fun y => v y + (b y : EReal))) :
    SameSingularityTypeAt u v x := by
  obtain ⟨C, _, hC⟩ := hb
  constructor
  · refine ⟨C, ?_⟩
    filter_upwards [hC, hu] with y hy heq
    rw [heq]
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (abs_le.mp hy).2)
  · refine ⟨C, ?_⟩
    filter_upwards [hC, hu] with y hy heq
    rw [heq, add_assoc, ← EReal.coe_add]
    have h : (0 : EReal) ≤ ((b y + C : ℝ) : EReal) :=
      EReal.coe_nonneg.mpr (by linarith [(abs_le.mp hy).1])
    simpa only [add_zero] using add_le_add (le_rfl : v y ≤ v y) h

end BoundedGerms

section LocalPresentations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A finite holomorphic family on one actual open neighborhood of the center. -/
def HolomorphicGeneratorsAt {n : ℕ} (f : Fin n → E → ℂ) (x : E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∀ j, DifferentiableOn ℂ (f j) U

/-- A fixed positive real coefficient and family, with a bounded real remainder.
This is a presentation condition, not a quasi-PSH assertion. -/
def LogarithmicTypeAt (u : E → EReal) (c : ℝ) {n : ℕ}
    (f : Fin n → E → ℂ) (x : E) : Prop :=
  0 < c ∧ HolomorphicGeneratorsAt f x ∧
    ∃ b : E → ℝ, BoundedRealGermAt b x ∧
      u =ᶠ[𝓝 x] (fun y => (c : EReal) * generatorLog f y + (b y : EReal))

/-- The revised rational-coefficient convention, as a local singularity type.
No compatibility between families at different centers is asserted. -/
def HasAnalyticSingularityTypeAt (u : E → EReal) (x : E) : Prop :=
  ∃ c : ℚ, ∃ n : ℕ, ∃ f : Fin n → E → ℂ, LogarithmicTypeAt u (c : ℝ) f x

theorem LogarithmicTypeAt.sameSingularityTypeAt {u : E → EReal} {c : ℝ}
    {n : ℕ} {f : Fin n → E → ℂ} {x : E} (hu : LogarithmicTypeAt u c f x) :
    SameSingularityTypeAt u (fun y => (c : EReal) * generatorLog f y) x := by
  obtain ⟨_, _, b, hb, heq⟩ := hu
  exact sameSingularityTypeAt_of_bounded_remainder hb heq

theorem LogarithmicTypeAt.eq_bot_iff {u : E → EReal} {c : ℝ}
    {n : ℕ} {f : Fin n → E → ℂ} {x : E} (hu : LogarithmicTypeAt u c f x) :
    u x = ⊥ ↔ ∀ j, f j x = 0 := by
  obtain ⟨hc, _, b, _, heq⟩ := hu
  rw [heq.eq_of_nhds]
  exact scaled_generatorLog_add_eq_bot_iff f x hc (b x)

variable [NormedSpace ℝ E]

/-- The local logarithmic expression of Collins–Tosatti with a positive real coefficient
and a remainder smooth throughout a neighbourhood. -/
def SmoothLogarithmicTypeAt (u : E → EReal) (c : ℝ) {n : ℕ}
    (f : Fin n → E → ℂ) (x : E) : Prop :=
  0 < c ∧ HolomorphicGeneratorsAt f x ∧
    ∃ b : E → ℝ, (∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ b y) ∧
      u =ᶠ[𝓝 x] (fun y => (c : EReal) * generatorLog f y + (b y : EReal))

/-- Local smooth analytic singularities, without an implicit rationality condition. -/
def HasSmoothAnalyticSingularitiesAt (u : E → EReal) (x : E) : Prop :=
  ∃ c : ℝ, ∃ n : ℕ, ∃ f : Fin n → E → ℂ, SmoothLogarithmicTypeAt u c f x

/-- A weaker local variant of the logarithmic expression in [Collins–Tosatti, §2](https://www.numdam.org/item/10.5802/afst.1708.pdf#page=8).
The coefficient is positive real. The remainder is bounded near the point and smooth on the
complement of the common zero set of the holomorphic generators. Collins–Tosatti require
smoothness throughout the neighbourhood. The implication at each nearby point lets the
off-pole clause compose with `Filter.Eventually`. -/
def BoundedSmoothOffPoleLogarithmicTypeAt (u : E → EReal) (c : ℝ) {n : ℕ}
    (f : Fin n → E → ℂ) (x : E) : Prop :=
  0 < c ∧ HolomorphicGeneratorsAt f x ∧
    ∃ b : E → ℝ, BoundedRealGermAt b x ∧
      (∀ᶠ y in 𝓝 x, generatorNormSq f y ≠ 0 → ContDiffAt ℝ ∞ b y) ∧
      u =ᶠ[𝓝 x] (fun y => (c : EReal) * generatorLog f y + (b y : EReal))

/-- Local logarithmic singularities with a positive real coefficient and a remainder
that is bounded near the point and smooth off the pole set. -/
def HasAnalyticSingularitiesSmoothOffPoleAt (u : E → EReal) (x : E) : Prop :=
  ∃ c : ℝ, ∃ n : ℕ, ∃ f : Fin n → E → ℂ,
    BoundedSmoothOffPoleLogarithmicTypeAt u c f x

/-- A remainder smooth on a neighbourhood is locally bounded and smooth off the pole set. -/
theorem SmoothLogarithmicTypeAt.boundedSmoothOffPole {u : E → EReal} {c : ℝ}
    {n : ℕ} {f : Fin n → E → ℂ} {x : E} (hu : SmoothLogarithmicTypeAt u c f x) :
    BoundedSmoothOffPoleLogarithmicTypeAt u c f x := by
  obtain ⟨hc, hf, b, hb, heq⟩ := hu
  refine ⟨hc, hf, b, boundedRealGermAt_of_continuousAt hb.self_of_nhds.continuousAt,
    hb.mono fun _ hy _ => hy, heq⟩

theorem HasSmoothAnalyticSingularitiesAt.smoothOffPole {u : E → EReal} {x : E}
    (hu : HasSmoothAnalyticSingularitiesAt u x) :
    HasAnalyticSingularitiesSmoothOffPoleAt u x := by
  obtain ⟨c, n, f, hu⟩ := hu
  exact ⟨c, n, f, hu.boundedSmoothOffPole⟩

/-- The bounded-remainder convention still is a bounded-remainder presentation, so every statement
about singularity TYPE goes through unchanged. -/
theorem BoundedSmoothOffPoleLogarithmicTypeAt.logarithmicTypeAt {u : E → EReal} {c : ℝ}
    {n : ℕ} {f : Fin n → E → ℂ} {x : E}
    (hu : BoundedSmoothOffPoleLogarithmicTypeAt u c f x) : LogarithmicTypeAt u c f x := by
  obtain ⟨hc, hf, b, hb, -, heq⟩ := hu
  exact ⟨hc, hf, b, hb, heq⟩

theorem BoundedSmoothOffPoleLogarithmicTypeAt.eq_bot_iff {u : E → EReal} {c : ℝ}
    {n : ℕ} {f : Fin n → E → ℂ} {x : E}
    (hu : BoundedSmoothOffPoleLogarithmicTypeAt u c f x) :
    u x = ⊥ ↔ ∀ j, f j x = 0 := hu.logarithmicTypeAt.eq_bot_iff

/-- A presentation in the bounded-remainder convention is a bounded perturbation of the pure
logarithm, hence has the same singularity type. -/
theorem BoundedSmoothOffPoleLogarithmicTypeAt.sameSingularityTypeAt {u : E → EReal} {c : ℝ}
    {n : ℕ} {f : Fin n → E → ℂ} {x : E}
    (hu : BoundedSmoothOffPoleLogarithmicTypeAt u c f x) :
    SameSingularityTypeAt u (fun y => (c : EReal) * generatorLog f y) x :=
  hu.logarithmicTypeAt.sameSingularityTypeAt

/-- Smooth real remainders are bounded after shrinking. The coefficient is
unchanged and remains real; this theorem does not assert its rationality. -/
theorem SmoothLogarithmicTypeAt.logarithmicTypeAt {u : E → EReal} {c : ℝ}
    {n : ℕ} {f : Fin n → E → ℂ} {x : E} (hu : SmoothLogarithmicTypeAt u c f x) :
    LogarithmicTypeAt u c f x := by
  obtain ⟨hc, hf, b, hb, heq⟩ := hu
  exact ⟨hc, hf, b, boundedRealGermAt_of_continuousAt
    hb.self_of_nhds.continuousAt, heq⟩

/-- The smooth convention implies the rational convention when its given
coefficient actually is rational. No such implication is asserted for arbitrary reals. -/
theorem SmoothLogarithmicTypeAt.hasAnalyticSingularityTypeAt {u : E → EReal}
    {c : ℚ} {n : ℕ} {f : Fin n → E → ℂ} {x : E}
    (hu : SmoothLogarithmicTypeAt u (c : ℝ) f x) : HasAnalyticSingularityTypeAt u x :=
  ⟨c, n, f, hu.logarithmicTypeAt⟩

theorem SmoothLogarithmicTypeAt.eq_bot_iff {u : E → EReal} {c : ℝ}
    {n : ℕ} {f : Fin n → E → ℂ} {x : E} (hu : SmoothLogarithmicTypeAt u c f x) :
    u x = ⊥ ↔ ∀ j, f j x = 0 := hu.logarithmicTypeAt.eq_bot_iff

/-- The bounded presentation is combined with an actual nondegenerate quasi-PSH
condition, rather than declaring arbitrary bounded perturbations quasi-PSH. -/
def AnalyticQuasiPshPotentialOn (u : E → EReal) (U : Set E) : Prop :=
  LocalQuasiPshPotentialOn u U ∧ ∀ x ∈ U, HasAnalyticSingularityTypeAt u x

/-- The smooth local convention combined with actual nondegenerate quasi-PSH.
This alone does not specify a global ideal, cohomology class, or current. -/
def SmoothAnalyticQuasiPshPotentialOn (u : E → EReal) (U : Set E) : Prop :=
  LocalQuasiPshPotentialOn u U ∧ ∀ x ∈ U, HasSmoothAnalyticSingularitiesAt u x

end LocalPresentations

end SGPT.Foundations.Analysis
