/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeSliceCutoff
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The exact scalar oscillator time-slice integral

The integrand is a compactly supported smooth function. An explicit primitive
has past limit zero and future limit `-2 i h b`; the actual whole-line
fundamental theorem of calculus proves the integral. The phase products are
reduced using their proved group law, not an assumed on-shell identity.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Topology Set

/-- Time slice oscillator reduced. -/
noncomputable def timeSliceOscillatorReduced (ε m : ℝ)
    (ξ : EuclideanSpace ℝ (Fin 3)) (a b : ℂ) (t : ℝ) : ℂ :=
  ((deriv (deriv (timeSliceCutoff ε)) t : ℝ) : ℂ) * (massiveEvolutionPhase m (2 * t) ξ * a + b) +
    2 * ((deriv (timeSliceCutoff ε) t : ℝ) : ℂ) * ((massiveSchwartzSymbol m 1 ξ : ℂ) * Complex.I) *
      (massiveEvolutionPhase m (2 * t) ξ * a - b)

/-- Time slice oscillator primitive. -/
noncomputable def timeSliceOscillatorPrimitive (ε m : ℝ)
    (ξ : EuclideanSpace ℝ (Fin 3)) (a b : ℂ) (t : ℝ) : ℂ :=
  ((deriv (timeSliceCutoff ε) t : ℝ) : ℂ) * (massiveEvolutionPhase m (2 * t) ξ * a + b) -
    2 * ((massiveSchwartzSymbol m 1 ξ : ℂ) * Complex.I) * (timeSliceCutoff ε t : ℂ) * b

theorem hasDerivAt_timeSliceOscillatorPrimitive (ε m : ℝ)
    (ξ : EuclideanSpace ℝ (Fin 3)) (a b : ℂ) (t : ℝ) :
    HasDerivAt (timeSliceOscillatorPrimitive ε m ξ a b)
      (timeSliceOscillatorReduced ε m ξ a b t) t := by
  have hχ := ((contDiff_timeSliceCutoff ε).differentiable (by simp) t).hasDerivAt
  have hχ' := ((contDiff_deriv_timeSliceCutoff ε).differentiable (by simp) t).hasDerivAt
  have hp := (hasDerivAt_massiveEvolutionPhase m (2 * t) ξ).scomp t
    ((hasDerivAt_id t).const_mul 2)
  have h := (hχ'.ofReal_comp.mul ((hp.mul_const a).add_const b)).sub
    ((hχ.ofReal_comp.const_mul (2 * ((massiveSchwartzSymbol m 1 ξ : ℂ) * Complex.I))).mul_const b)
  convert h using 1
  · rfl
  · simp only [timeSliceOscillatorReduced, Function.comp_apply, mul_one,
      Complex.real_smul, Complex.ofReal_ofNat]
    ring

theorem continuous_timeSliceOscillatorReduced (ε m : ℝ)
    (ξ : EuclideanSpace ℝ (Fin 3)) (a b : ℂ) :
    Continuous (timeSliceOscillatorReduced ε m ξ a b) := by
  have hχ := (contDiff_deriv_timeSliceCutoff ε).continuous
  have hχ' := (contDiff_deriv_twice_timeSliceCutoff ε).continuous
  have hp : Continuous (fun t => massiveEvolutionPhase m (2 * t) ξ) := by
    unfold massiveEvolutionPhase
    fun_prop
  exact ((Complex.continuous_ofReal.comp hχ').mul ((hp.mul_const a).add_const b)).add
    (((continuous_const.mul (Complex.continuous_ofReal.comp hχ)).mul_const _).mul
      ((hp.mul_const a).sub continuous_const))

theorem hasCompactSupport_timeSliceOscillatorReduced {ε : ℝ} (hε : 0 < ε) (m : ℝ)
    (ξ : EuclideanSpace ℝ (Fin 3)) (a b : ℂ) :
    HasCompactSupport (timeSliceOscillatorReduced ε m ξ a b) := by
  apply HasCompactSupport.intro (K := Icc (-ε) ε) isCompact_Icc
  intro t ht
  have h₁ := deriv_timeSliceCutoff_eq_zero_of_not_mem hε ht
  have h₂ : deriv (deriv (timeSliceCutoff ε)) t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => ht (tsupport_deriv_twice_timeSliceCutoff_subset
      hε h))
  simp only [timeSliceOscillatorReduced, h₁, h₂, Complex.ofReal_zero, zero_mul, mul_zero, add_zero]

theorem timeSliceOscillatorPrimitive_past {ε : ℝ} (hε : 0 < ε) (m : ℝ)
    (ξ : EuclideanSpace ℝ (Fin 3)) (a b : ℂ) {t : ℝ} (ht : t < -ε) :
    timeSliceOscillatorPrimitive ε m ξ a b t = 0 := by
  have hout : t ∉ Icc (-ε) ε := fun h => (not_lt_of_ge h.1) ht
  simp only [timeSliceOscillatorPrimitive, deriv_timeSliceCutoff_eq_zero_of_not_mem hε hout,
    timeSliceCutoff_zero hε ht.le, Complex.ofReal_zero, zero_mul, mul_zero, sub_zero]

theorem timeSliceOscillatorPrimitive_future {ε : ℝ} (hε : 0 < ε) (m : ℝ)
    (ξ : EuclideanSpace ℝ (Fin 3)) (a b : ℂ) {t : ℝ} (ht : ε < t) :
    timeSliceOscillatorPrimitive ε m ξ a b t =
      -2 * ((massiveSchwartzSymbol m 1 ξ : ℂ) * Complex.I) * b := by
  have hout : t ∉ Icc (-ε) ε := fun h => (not_lt_of_ge h.2) ht
  simp only [timeSliceOscillatorPrimitive, deriv_timeSliceCutoff_eq_zero_of_not_mem hε hout,
    timeSliceCutoff_one hε ht.le, Complex.ofReal_zero, Complex.ofReal_one, zero_mul, mul_one,
    zero_sub, neg_mul]

theorem integral_timeSliceOscillatorReduced {ε : ℝ} (hε : 0 < ε) (m : ℝ)
    (ξ : EuclideanSpace ℝ (Fin 3)) (a b : ℂ) :
    ∫ t, timeSliceOscillatorReduced ε m ξ a b t =
      -2 * ((massiveSchwartzSymbol m 1 ξ : ℂ) * Complex.I) * b := by
  have hi := (continuous_timeSliceOscillatorReduced ε m ξ a b).integrable_of_hasCompactSupport
    (μ := volume)
    (hasCompactSupport_timeSliceOscillatorReduced hε m ξ a b)
  have hbot : Tendsto (timeSliceOscillatorPrimitive ε m ξ a b) atBot (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_atBot (-ε)] with t ht
    exact (timeSliceOscillatorPrimitive_past hε m ξ a b ht).symm
  have htop : Tendsto (timeSliceOscillatorPrimitive ε m ξ a b) atTop
      (𝓝 (-2 * ((massiveSchwartzSymbol m 1 ξ : ℂ) * Complex.I) * b)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop ε] with t ht
    exact (timeSliceOscillatorPrimitive_future hε m ξ a b ht).symm
  simpa only [sub_zero] using integral_of_hasDerivAt_of_tendsto
    (hasDerivAt_timeSliceOscillatorPrimitive ε m ξ a b) hi hbot htop

theorem timeSliceOscillator_reduction (ε m : ℝ)
    (ξ : EuclideanSpace ℝ (Fin 3)) (a b : ℂ) (t : ℝ) :
    massiveEvolutionPhase m t ξ *
      (((deriv (deriv (timeSliceCutoff ε)) t : ℝ) : ℂ) *
        (massiveEvolutionPhase m t ξ * a + massiveEvolutionPhase m (-t) ξ * b) +
        2 * ((deriv (timeSliceCutoff ε) t : ℝ) : ℂ) * ((massiveSchwartzSymbol m 1 ξ : ℂ) *
          Complex.I) *
          (massiveEvolutionPhase m t ξ * a - massiveEvolutionPhase m (-t) ξ * b)) =
      timeSliceOscillatorReduced ε m ξ a b t := by
  have hsq : massiveEvolutionPhase m t ξ * massiveEvolutionPhase m t ξ =
      massiveEvolutionPhase m (2 * t) ξ := by
    rw [← massiveEvolutionPhase_add, two_mul]
  have hinv : massiveEvolutionPhase m t ξ * massiveEvolutionPhase m (-t) ξ = 1 := by
    rw [← massiveEvolutionPhase_add, add_neg_cancel]
    simp [massiveEvolutionPhase]
  calc
    _ = ((deriv (deriv (timeSliceCutoff ε)) t : ℝ) : ℂ) *
          (massiveEvolutionPhase m t ξ * massiveEvolutionPhase m t ξ * a +
            massiveEvolutionPhase m t ξ * massiveEvolutionPhase m (-t) ξ * b) +
        2 * ((deriv (timeSliceCutoff ε) t : ℝ) : ℂ) * ((massiveSchwartzSymbol m 1 ξ : ℂ) *
          Complex.I) *
          (massiveEvolutionPhase m t ξ * massiveEvolutionPhase m t ξ * a -
            massiveEvolutionPhase m t ξ * massiveEvolutionPhase m (-t) ξ * b) := by ring
    _ = _ := by rw [hsq, hinv]; simp only [one_mul, timeSliceOscillatorReduced]

end VacuumBellSeparation
