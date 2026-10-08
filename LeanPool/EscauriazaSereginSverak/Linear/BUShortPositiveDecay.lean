/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortZeroFromIntegral
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortParameterLimits

/-!
# Vanishing from exponential decay in the positive phase

An exponential bound with the negative phase gap forces a continuous
field to vanish at interior points of any compact positive-phase set.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- If the weighted mass on a compact positive-phase region has the
negative-phase decay rate at every large Carleman parameter, then the
field vanishes at every interior point. -/
theorem bu_short_zero_of_positive_phase_decay
    (scale : ℝ) (S : Set ParabolicPoint)
    (hScompact : IsCompact S)
    (hSpositive : S ⊆ buShortPositivePhaseRegion scale)
    (v : ParabolicPoint → Vec3) (hv : ContinuousOn v S)
    (C D a₀ : ℝ) (hD : 0 < D)
    (hbound : ∀ a : ℝ, a₀ < a →
      (∫ q in S, buShortShiftedWeight scale a q *
        vec3EuclideanNorm (v q) ^ 2
        ∂(volume : Measure ParabolicPoint)) ≤
      C * Real.exp (-(a * D)))
    {z : ParabolicPoint} (hz : z ∈ interior S) :
    v z = 0 := by
  let f : ParabolicPoint → ℝ := fun q =>
    vec3EuclideanNorm (v q) ^ 2
  let I : ℝ := ∫ q in S,
    buShortShiftedWeight scale 0 q * f q
    ∂(volume : Measure ParabolicPoint)
  have hSmeas : MeasurableSet S := hScompact.isClosed.measurableSet
  have hfCont : ContinuousOn f S :=
    (continuous_vec3EuclideanNorm.pow 2).comp_continuousOn hv
  have hWeightCont (a : ℝ) :
      ContinuousOn (buShortShiftedWeight scale a) S :=
    (buShortShiftedWeight_continuousOn_positive scale a).mono hSpositive
  have hInt (a : ℝ) : IntegrableOn (fun q =>
      buShortShiftedWeight scale a q * f q) S volume :=
    ((hWeightCont a).mul hfCont).integrableOn_compact hScompact
  have hI0 : 0 ≤ I := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem hSmeas] with q hq
    have hWt : 0 ≤ buShortShiftedWeight scale 0 q := by
      dsimp [buShortShiftedWeight, buShortCarlemanWeight]
      positivity
    exact mul_nonneg hWt (sq_nonneg _)
  have hboundBase (a : ℝ) (ha : max a₀ 0 < a) :
      I ≤ C * Real.exp (-(a * D)) := by
    have ha0 : 0 ≤ a := (le_max_right _ _).trans ha.le
    have hpoint : ∀ q ∈ S,
        buShortShiftedWeight scale 0 q * f q ≤
          buShortShiftedWeight scale a q * f q := by
      intro q hq
      exact mul_le_mul_of_nonneg_right
        (buShortShiftedWeight_zero_le_on_positive ha0 (hSpositive hq))
        (sq_nonneg _)
    have hcompare := setIntegral_mono_on (hInt 0) (hInt a)
      hSmeas hpoint
    have ha₀ : a₀ < a := (le_max_left _ _).trans_lt ha
    exact hcompare.trans (hbound a ha₀)
  have hzero : I = 0 :=
    bu_short_eq_zero_of_exponential_bound hI0 hD hboundBase
  exact bu_short_zero_of_base_weighted_integral_zero
    scale S hScompact hSpositive v hv hz hzero

end ESS
