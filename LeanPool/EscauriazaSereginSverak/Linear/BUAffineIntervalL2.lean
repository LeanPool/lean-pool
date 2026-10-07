/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineIntervalWeak
public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineL2

/-!
# Quadratic data on affine time intervals

Local quadratic data survives the change of variables from the physical
initial time interval to the shifted interval in `lem:bu-small-time`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- A finite quadratic integral on bounded source subsets transfers to
bounded subsets of a corresponding affine time interval. -/
theorem bu_affine_l2_comp_interval
    {E : Type*} [NormedAddCommGroup E]
    (τ scale a b : ℝ) (hscale : 0 < scale)
    (f : ParabolicPoint → E)
    (hfloc : LocallyIntegrableOn f
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b))) volume)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖f z‖ₑ ^ (2 : ℝ)) < ⊤)
    (K : Set ParabolicPoint)
    (hKsub : K ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b))
    (hKbounded : Bornology.IsBounded K) :
    (∫⁻ z in K, ‖f (buAffinePoint τ scale z)‖ₑ ^ (2 : ℝ)) < ⊤ := by
  let e := buAffineParabolicHomeomorph τ scale hscale
  let S := e '' K
  have heq : ⇑e = buAffinePoint τ scale :=
    buAffineParabolicHomeomorph_eq τ scale hscale
  have hSsub : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
      (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)) := by
    rintro q ⟨z, hz, rfl⟩
    rw [heq]
    have hp := buAffinePoint_preimage_interval τ scale a b hscale
    exact hp.symm.subset (hKsub hz)
  have hSbounded : Bornology.IsBounded S := by
    change Bornology.IsBounded (e '' K)
    rw [heq]
    exact buAffinePoint_bounded_image τ scale hscale hKbounded
  have hSfin := hL2 S hSsub hSbounded
  let F := fun z : ParabolicPoint => ‖f z‖ₑ ^ (2 : ℝ)
  have hfm : AEStronglyMeasurable f (volume.restrict S) :=
    (hfloc.mono_set hSsub).aestronglyMeasurable
  have hFm : AEMeasurable F (volume.restrict S) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hfm.enorm
  have hmap : Measure.map e volume =
      ENNReal.ofReal (scale⁻¹ ^ 5) • (volume : Measure ParabolicPoint) := by
    rw [heq, buAffinePoint_eq_scalingParabolic]
    exact CKN.map_scalingParabolic scale hscale ((0 : Vec3), τ)
  have hpres : MeasurePreserving e volume
      (ENNReal.ofReal (scale⁻¹ ^ 5) • volume) := ⟨e.measurable, hmap⟩
  have hmapS := (hpres.restrict_image_emb e.measurableEmbedding K).map_eq
  have hFmap : AEMeasurable F (Measure.map e (volume.restrict K)) := by
    rw [hmapS, Measure.restrict_smul]
    exact hFm.smul_measure (ENNReal.ofReal (scale⁻¹ ^ 5))
  have hcomp := lintegral_map' hFmap e.measurable.aemeasurable
  rw [hmapS, Measure.restrict_smul, lintegral_smul_measure] at hcomp
  have hfinite : (∫⁻ z in K, F (e z)) < ⊤ := by
    rw [← hcomp]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSfin
  simpa only [F, heq] using hfinite

/-- Finite local quadratic energy remains finite after affine composition
and multiplication by a subunit scalar. -/
theorem bu_affine_l2_smul_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ scale a b c : ℝ) (hscale : 0 < scale)
    (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (f : ParabolicPoint → E)
    (hfloc : LocallyIntegrableOn f
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b))) volume)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖f z‖ₑ ^ (2 : ℝ)) < ⊤)
    (K : Set ParabolicPoint)
    (hKsub : K ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b))
    (hKbounded : Bornology.IsBounded K) :
    (∫⁻ z in K, ‖c • f (buAffinePoint τ scale z)‖ₑ ^ (2 : ℝ)) < ⊤ := by
  have hbase := bu_affine_l2_comp_interval τ scale a b hscale f hfloc hL2
    K hKsub hKbounded
  have hpoint (z : ParabolicPoint) :
      ‖c • f (buAffinePoint τ scale z)‖ₑ ^ (2 : ℝ) ≤
        ‖f (buAffinePoint τ scale z)‖ₑ ^ (2 : ℝ) := by
    rw [enorm_smul, ← ofReal_norm c, Real.norm_eq_abs, abs_of_nonneg hc]
    rw [ENNReal.rpow_ofNat, mul_pow]
    have hcoef : ENNReal.ofReal c ^ (2 : ℕ) ≤ 1 := by
      exact pow_le_one₀ bot_le (ENNReal.ofReal_le_one.mpr hc1)
    simpa only [ENNReal.rpow_ofNat] using
      (mul_le_of_le_one_left
        (b := ‖f (buAffinePoint τ scale z)‖ₑ ^ 2) bot_le hcoef)
  exact (lintegral_mono hpoint).trans_lt hbase

end ESS
