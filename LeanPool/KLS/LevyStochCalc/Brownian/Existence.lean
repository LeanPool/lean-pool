/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.Construction
public import LeanPool.KLS.BrownianMotion.Gaussian.BrownianMotion

/-!
# Brownian motion from a pre-Brownian process

A process `X : ℝ≥0 → Ω → ℝ` with the finite-dimensional laws of Brownian motion
(`IsPreBrownianReal`), measurable marginals and continuous paths yields a `BrownianMotion P` in
the sense of `LevyStochCalc.Brownian.Construction`: extend to real time by `t ↦ X (t⁺) − X 0`,
which vanishes at non-positive times and is re-centred at the origin. The weak Markov property
`IsPreBrownianReal.indepFun_shift` supplies the σ-algebra independence of the past from a future
increment.

## Main statements

* `BrownianMotion.ofIsPreBrownianReal` — the construction.
* `BrownianMotion.exists` — existence, from the canonical Brownian motion `brownian` on
  `gaussianLimit`, lifted to an arbitrary universe.
-/

@[expose] public section

namespace LevyStochCalc.Brownian

open MeasureTheory ProbabilityTheory
open scoped NNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Real-time extension of an `ℝ≥0`-indexed process: `t ↦ X (t⁺) − X 0`. -/
noncomputable def realTime (X : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  X (Real.toNNReal t) ω - X 0 ω

omit [MeasurableSpace Ω] in
theorem realTime_sub (X : ℝ≥0 → Ω → ℝ) (s t : ℝ) :
    (fun ω => realTime X t ω - realTime X s ω)
      = fun ω => X (Real.toNNReal t) ω - X (Real.toNNReal s) ω := by
  funext ω; simp only [realTime]; ring

omit [MeasurableSpace Ω] in
theorem continuous_realTime {X : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous (X · ω)) (ω : Ω) :
    Continuous (fun t : ℝ => realTime X t ω) :=
  ((hcont ω).comp continuous_real_toNNReal).sub continuous_const

/-- A pre-Brownian process with measurable marginals and continuous paths is a Brownian motion
in real time. -/
noncomputable def BrownianMotion.ofIsPreBrownianReal {X : ℝ≥0 → Ω → ℝ}
    (hX : IsPreBrownianReal X P) (hmeas : ∀ t, Measurable (X t))
    (hcont : ∀ ω, Continuous (X · ω)) : BrownianMotion P where
  W := realTime X
  measurable_eval _ := (hmeas _).sub (hmeas 0)
  joint_measurable :=
    measurable_uncurry_of_continuous_of_measurable (continuous_realTime hcont)
      fun _ => (hmeas _).sub (hmeas 0)
  initial_zero := ae_of_all _ fun ω => by simp [realTime]
  increment_gaussian := by
    intro s t hs hst
    have ht : 0 ≤ t := hs.trans hst.le
    have hd : nndist (Real.toNNReal t).1 (Real.toNNReal s).1 = ⟨t - s, by linarith⟩ := by
      apply NNReal.coe_injective
      simp only [NNReal.val_eq_coe, coe_nndist, Real.dist_eq, Real.coe_toNNReal _ ht,
        Real.coe_toNNReal _ hs, abs_of_pos (sub_pos.mpr hst)]
      rfl
    have h := (hX.hasLaw_sub (Real.toNNReal t) (Real.toNNReal s)).map_eq
    rw [hd] at h
    rw [realTime_sub]
    exact h
  continuous_paths := ae_of_all _ (continuous_realTime hcont)
  negative_zero := fun s hs => ae_of_all _ fun ω => by
    simp [realTime, Real.toNNReal_of_nonpos hs.le]
  joint_increment_independent := by
    intro s t hs hst
    have hst' : Real.toNNReal s ≤ Real.toNNReal t := Real.toNNReal_le_toNNReal hst.le
    have h : Indep
        (MeasurableSpace.comap (fun ω (r : Set.Iic (Real.toNNReal s)) => X r ω) inferInstance)
        (MeasurableSpace.comap
          (fun ω (r : ℝ≥0) => X (Real.toNNReal s + r) ω - X (Real.toNNReal s) ω) inferInstance)
        P :=
      (hX.indepFun_shift (Real.toNNReal s)).symm
    refine indep_of_indep_of_le_left (indep_of_indep_of_le_right h ?_) ?_
    · rw [realTime_sub]
      have : (fun ω => X (Real.toNNReal t) ω - X (Real.toNNReal s) ω)
          = (fun p : ℝ≥0 → ℝ => p (Real.toNNReal t - Real.toNNReal s))
            ∘ (fun ω (r : ℝ≥0) => X (Real.toNNReal s + r) ω - X (Real.toNNReal s) ω) := by
        funext ω; simp [add_tsub_cancel_of_le hst']
      rw [this]
      refine Measurable.comap_le ?_
      exact (measurable_pi_apply _).comp (Measurable.of_comap_le le_rfl)
    · refine iSup₂_le fun j hj => ?_
      have hj' : Real.toNNReal j ≤ Real.toNNReal s := Real.toNNReal_le_toNNReal hj
      have : realTime X j
          = (fun p : Set.Iic (Real.toNNReal s) → ℝ => p ⟨Real.toNNReal j, hj'⟩ - p ⟨0, by simp⟩)
            ∘ (fun ω (r : Set.Iic (Real.toNNReal s)) => X r ω) := by
        funext ω; rfl
      rw [this]
      refine Measurable.comap_le (Measurable.comp ?_ (Measurable.of_comap_le le_rfl))
      exact (measurable_pi_apply _).sub (measurable_pi_apply _)

/-- Existence of a probability space carrying a Brownian motion: the canonical Brownian motion
`brownian` on the projective-limit space `gaussianLimit`, transported along `ULift`. -/
theorem BrownianMotion.exists :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P), Nonempty (BrownianMotion P) := by
  let e : ULift.{u} (ℝ≥0 → ℝ) ≃ᵐ (ℝ≥0 → ℝ) := MeasurableEquiv.ulift
  let P : Measure (ULift.{u} (ℝ≥0 → ℝ)) := gaussianLimit.map e.symm
  have hP : IsProbabilityMeasure P :=
    (Measure.isProbabilityMeasure_map_iff e.symm.measurable.aemeasurable).2 inferInstance
  have hdown : HasLaw e gaussianLimit P :=
    ⟨e.measurable.aemeasurable, by simp [P, Measure.map_map e.measurable e.symm.measurable]⟩
  refine ⟨ULift.{u} (ℝ≥0 → ℝ), inferInstance, P, hP, ⟨?_⟩⟩
  refine BrownianMotion.ofIsPreBrownianReal (X := fun t ω => brownian t (e ω)) ?_ ?_ ?_
  · exact ⟨fun I => (isBrownianReal_brownian.hasLaw I).comp hdown⟩
  · exact fun t => (measurable_brownian t).comp e.measurable
  · exact fun ω => continuous_brownian (e ω)

end LevyStochCalc.Brownian
