/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszFarHarmonic
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureIntegrability
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Blowup Riesz Far Time

Pressure reconstruction and convergence bounds for the rescaled sequence.
-/

public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- Slice harmonicity and a uniform global pressure bound give the
`L^(3/2)` far-field estimate on a bounded past cylinder. -/
theorem blowup_harmonic_far_spaceTime_mass_bound :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (h : ParabolicPoint → ℝ) (L R : ℝ) (J : Set ℝ)
        (M : ℝ≥0∞),
        0 < L → 0 < R → R ≤ 3 * L / 4 →
        AEStronglyMeasurable h
          ((volume.restrict (CKN.euclideanBall 0 R)).prod
            (volume.restrict J)) →
        (∀ᵐ t ∂volume.restrict J,
          MemLp (fun x : Vec3 => h (x,t)) (3 / 2 : ℝ≥0∞) volume ∧
          eLpNorm (fun x : Vec3 => h (x,t))
            (3 / 2 : ℝ≥0∞) volume ≤ M ∧
          CKN.Foundation.Heat.WeaklyHarmonicOn
            (CKN.euclideanBall 0 L) (fun x : Vec3 => h (x,t))) →
        (∫⁻ z, ENNReal.ofReal |h z| ^ (3 / 2 : ℝ)
          ∂((volume.restrict (CKN.euclideanBall 0 R)).prod
            (volume.restrict J))) ≤
          volume J *
            (C * ENNReal.ofReal ((L ^ 2)⁻¹) * M *
              volume (CKN.euclideanBall (0 : Vec3) R) ^ (2 / 3 : ℝ)) ^
                (3 / 2 : ℝ) := by
  obtain ⟨C, hC, hCbound⟩ := blowup_harmonic_far_local_bound
  refine ⟨C, hC, ?_⟩
  intro h L R J M hL hR hRL hjoint hSlices
  let BR := CKN.euclideanBall (0 : Vec3) R
  let K : ℝ≥0∞ :=
    C * ENNReal.ofReal ((L ^ 2)⁻¹) * M * volume BR ^ (2 / 3 : ℝ)
  have hpoint : ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x : Vec3 => h (x,t)) (3 / 2 : ℝ≥0∞)
        (volume.restrict BR) ≤ K := by
    filter_upwards [hSlices] with t ht
    have hfar := hCbound (fun x : Vec3 => h (x,t)) L R
      hL hR hRL ht.1 ht.2.2
    have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (f := fun x : Vec3 => h (x,t))
      (μ := volume.restrict BR) (p := (3 / 2 : ℝ≥0∞)) (q := ⊤)
      (by simp) ht.1.aestronglyMeasurable.restrict
    have hmeasure : (volume.restrict BR) Set.univ = volume BR := by
      exact Measure.restrict_apply_univ BR
    calc
      eLpNorm (fun x : Vec3 => h (x,t)) (3 / 2 : ℝ≥0∞)
          (volume.restrict BR) ≤
          eLpNorm (fun x : Vec3 => h (x,t)) ⊤
            (volume.restrict BR) * volume BR ^ (2 / 3 : ℝ) := by
        convert hcompare using 1
        rw [hmeasure]
        norm_num
      _ ≤ (C * ENNReal.ofReal ((L ^ 2)⁻¹) *
            eLpNorm (fun x : Vec3 => h (x,t))
              (3 / 2 : ℝ≥0∞) volume) *
            volume BR ^ (2 / 3 : ℝ) := by gcongr
      _ ≤ K := by dsimp [K]; gcongr; exact ht.2.1
  have htonelli := blowupScalarTimeThreeHalves_eq
    (Ω := BR) (J := J) h hjoint
  have htime :
      (∫⁻ t in J,
        eLpNorm (fun x : Vec3 => h (x,t)) (3 / 2 : ℝ≥0∞)
          (volume.restrict BR) ^ (3 / 2 : ℝ)) ≤
        volume J * K ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ ∫⁻ _t in J, K ^ (3 / 2 : ℝ) := by
        apply lintegral_mono_ae
        filter_upwards [hpoint] with t ht
        exact ENNReal.rpow_le_rpow ht (by norm_num)
      _ = volume J * K ^ (3 / 2 : ℝ) := by
        rw [setLIntegral_const]
        exact mul_comm _ _
  simpa only [BR, K] using htonelli.symm.le.trans htime

/-- The quantitative far-field mass bound vanishes as the outer radius
increases through integer radii. -/
theorem blowup_far_pressure_mass_bound_tendsto_zero
    (C M V T : ℝ≥0∞)
    (hC : C < ⊤) (hM : M < ⊤) (hV : V < ⊤) (hT : T < ⊤) :
    Tendsto (fun n : ℕ =>
      T * (C * ENNReal.ofReal (((n : ℝ) + 1) ^ 2)⁻¹ * M *
        V ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ))
      atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹)
      atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsquare : Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹)
      atTop (nhds 0) := by
    simpa [inv_pow] using hinv.pow 2
  have hcoeff : Tendsto (fun n : ℕ =>
      ENNReal.ofReal ((((n : ℝ) + 1) ^ 2)⁻¹)) atTop (nhds 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsquare
  let K : ℝ≥0∞ := C * M * V ^ (2 / 3 : ℝ)
  have hK : K < ⊤ := by
    dsimp [K]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top hC hM)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hV.ne)
  have hinside : Tendsto (fun n : ℕ =>
      C * ENNReal.ofReal ((((n : ℝ) + 1) ^ 2)⁻¹) * M *
        V ^ (2 / 3 : ℝ)) atTop (nhds 0) := by
    have h := ENNReal.Tendsto.mul_const hcoeff (Or.inr hK.ne)
    simpa only [K, zero_mul, mul_zero, mul_left_comm, mul_comm, mul_assoc] using h
  have hpow : Tendsto (fun n : ℕ =>
      (C * ENNReal.ofReal ((((n : ℝ) + 1) ^ 2)⁻¹) * M *
        V ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,
      show (0 : ℝ≥0∞) ^ (3 / 2 : ℝ) = 0 by norm_num] using
      (ENNReal.continuous_rpow_const (y := (3 / 2 : ℝ))).continuousAt.tendsto.comp
        hinside
  simpa only [zero_mul, mul_zero] using
    (ENNReal.Tendsto.const_mul hpow (Or.inr hT.ne))

end ESS
