/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPositiveCompact
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Recovering pointwise zero from quadratic mass

On the interior of a compact region, a continuous field with zero
quadratic integral vanishes pointwise.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private instance : Measure.IsOpenPosMeasure
    (volume : Measure ParabolicPoint) where
  open_pos U hU hne := by
    have hopen : IsOpen (parabolicHomeomorph.symm ⁻¹' U) :=
      hU.preimage parabolicHomeomorph.symm.continuous
    have hnonempty : (parabolicHomeomorph.symm ⁻¹' U).Nonempty := by
      obtain ⟨z, hz⟩ := hne
      exact ⟨parabolicHomeomorph z, hz⟩
    exact hopen.measure_ne_zero
      (volume : Measure (Vec3 × ℝ)) hnonempty

/-- Zero quadratic mass of a continuous vector field on a compact set
forces vanishing at every interior point. -/
theorem bu_short_zero_of_compact_sq_integral_zero
    (S : Set ParabolicPoint) (hScompact : IsCompact S)
    (v : ParabolicPoint → Vec3) (hv : ContinuousOn v S)
    {z : ParabolicPoint} (hz : z ∈ interior S)
    (hzero : (∫ q in S, vec3EuclideanNorm (v q) ^ 2
      ∂(volume : Measure ParabolicPoint)) = 0) :
    v z = 0 := by
  let f : ParabolicPoint → ℝ := fun q => vec3EuclideanNorm (v q) ^ 2
  have hfcont : ContinuousOn f S :=
    (continuous_vec3EuclideanNorm.pow 2).comp_continuousOn hv
  have hfInt : IntegrableOn f S volume :=
    hfcont.integrableOn_compact hScompact
  have hf0 : 0 ≤ᵐ[(volume : Measure ParabolicPoint).restrict S] f := by
    filter_upwards [] with q
    exact sq_nonneg _
  have hAE : f =ᵐ[(volume : Measure ParabolicPoint).restrict S] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae hf0 hfInt).mp hzero
  have hAEInt : f =ᵐ[(volume : Measure ParabolicPoint).restrict
      (interior S)] 0 :=
    ae_restrict_of_ae_restrict_of_subset interior_subset hAE
  have hEqOn : EqOn f (fun _ => 0) (interior S) :=
    Measure.eqOn_open_of_ae_eq hAEInt isOpen_interior
      (hfcont.mono interior_subset) continuousOn_const
  have hsq : vec3EuclideanNorm (v z) ^ 2 = 0 := hEqOn hz
  have hnorm : vec3EuclideanNorm (v z) = 0 := by
    nlinarith only [hsq]
  rw [vec3EuclideanNorm_eq_l2] at hnorm
  have hzeroLp : WithLp.toLp 2 (v z) = 0 := norm_eq_zero.mp hnorm
  exact (WithLp.toLp_injective 2) (by simpa using hzeroLp)

/-- Zero mass against the positive phase-independent weight forces a
continuous field to vanish at interior points of the compact region. -/
theorem bu_short_zero_of_base_weighted_integral_zero
    (scale : ℝ) (S : Set ParabolicPoint) (hScompact : IsCompact S)
    (hSpositive : S ⊆ buShortPositivePhaseRegion scale)
    (v : ParabolicPoint → Vec3) (hv : ContinuousOn v S)
    {z : ParabolicPoint} (hz : z ∈ interior S)
    (hzero : (∫ q in S,
      buShortShiftedWeight scale 0 q * vec3EuclideanNorm (v q) ^ 2
      ∂(volume : Measure ParabolicPoint)) = 0) :
    v z = 0 := by
  let f : ParabolicPoint → ℝ := fun q =>
    buShortShiftedWeight scale 0 q * vec3EuclideanNorm (v q) ^ 2
  have hSmeas : MeasurableSet S := hScompact.isClosed.measurableSet
  have hbaseCont : ContinuousOn (buShortShiftedWeight scale 0) S :=
    (buShortShiftedWeight_zero_continuousOn_positive scale).mono hSpositive
  have hnormCont : ContinuousOn
      (fun q => vec3EuclideanNorm (v q) ^ 2) S :=
    (continuous_vec3EuclideanNorm.pow 2).comp_continuousOn hv
  have hfCont : ContinuousOn f S := hbaseCont.mul hnormCont
  have hfInt : IntegrableOn f S volume :=
    hfCont.integrableOn_compact hScompact
  have hbasePos (q : ParabolicPoint) (hq : q ∈ S) :
      0 < buShortShiftedWeight scale 0 q := by
    have hphase := hSpositive hq
    have hs : 0 < q.2 := lt_trans (by norm_num) hphase.2.1
    rw [buShortShiftedWeight_eq scale 0 q hs]
    simp only [mul_zero, zero_mul, Real.exp_zero, mul_one]
    positivity
  have hf0 : 0 ≤ᵐ[(volume : Measure ParabolicPoint).restrict S] f := by
    filter_upwards [ae_restrict_mem hSmeas] with q hq
    exact mul_nonneg (hbasePos q hq).le (sq_nonneg _)
  have hAE : f =ᵐ[(volume : Measure ParabolicPoint).restrict S] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae hf0 hfInt).mp hzero
  have hPlainAE : (fun q => vec3EuclideanNorm (v q) ^ 2) =ᵐ[
      (volume : Measure ParabolicPoint).restrict S] 0 := by
    filter_upwards [hAE, ae_restrict_mem hSmeas] with q hqzero hq
    have hmul : buShortShiftedWeight scale 0 q *
        vec3EuclideanNorm (v q) ^ 2 = 0 := hqzero
    exact (mul_eq_zero.mp hmul).resolve_left
      (ne_of_gt (hbasePos q hq))
  have hPlainZero : (∫ q in S, vec3EuclideanNorm (v q) ^ 2
      ∂(volume : Measure ParabolicPoint)) = 0 :=
    integral_eq_zero_of_ae hPlainAE
  exact bu_short_zero_of_compact_sq_integral_zero
    S hScompact v hv hz hPlainZero

end ESS
