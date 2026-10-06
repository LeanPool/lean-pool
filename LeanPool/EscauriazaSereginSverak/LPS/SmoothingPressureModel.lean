/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingPressureTensorBridge
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedDerivativeBridge
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumPressureId
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalPressure
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# High-order Fourier models for the regularized pressure

The double-Riesz image of a high-Bessel tensor lift represents the
canonical regularized pressure on each nonnegative-time slice.
-/

public section

open MeasureTheory FourierTransform Complex Set
open scoped ENNReal FourierTransform Real


noncomputable section

namespace ESS

open CKN.Leray
open CKN CKN.Foundation.Parabolic

/-- The undamped scalar pressure frequency field of a high tensor lift. -/
@[expose] def lps_regR12PressureHighFreq
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (v : C(CKN.Leray.RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * (n + 2) : ℕ) : ℝ) 2))
    (t : ℝ) : Lp ℂ 2 (volume : Measure L2Vec3) :=
  CKN.Leray.pressureFourierMultiplier
    (lps_regR12HighTensorFreq ρ ε hε n T hT v t)

/-- The inverse Fourier field associated with a high-order pressure
frequency path. -/
@[expose] def lps_regR12PressureHighModel
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (v : C(CKN.Leray.RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * (n + 2) : ℕ) : ℝ) 2)) :
    ParabolicPoint → ℝ :=
  CKN.Leray.regR12SpaceTimeField Complex.reCLM
    (lps_dampedFourierWordSymbol n [])
    (lps_regR12PressureHighFreq ρ ε hε n T hT v)

/-- On each finite-time slice, the high-order pressure model agrees
almost everywhere with the canonical pressure
(`prop:lps-smoothing`). -/
theorem lps_regR12PressureHighModel_ae_eq
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (v : C(CKN.Leray.RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * (n + 2) : ℕ) : ℝ) 2))
    (hv : ∀ t : CKN.Leray.RegularizedMildTimeInterval T,
      CKN.Leray.regularisedBesselSobolevToL2CLM
        ((2 * (n + 2) : ℕ) : ℝ) (by positivity) (v t) =
        CKN.Leray.complexifyVectorL2
          (CKN.Leray.regR12Curve ρ ε hε a ha t.1))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (fun x : Vec3 => lps_regR12PressureHighModel ρ ε hε n T hT v (x, t)) =ᵐ[volume]
      fun x : Vec3 => CKN.Leray.forcedQuadPressure ρ ε hε
        (CKN.Leray.regR12Curve ρ ε hε a ha) (x, t) := by
  let V : RealTensorL2 := CKN.Leray.regularizedMildTensor ρ ε hε
    (CKN.Leray.regR12Curve ρ ε hε a ha t)
  let H : Lp ℂ 2 (volume : Measure L2Vec3) :=
    CKN.Leray.pressureL2Operator (CKN.Leray.complexifyTensorL2 V)
  let G := lps_regR12PressureHighFreq ρ ε hε n T hT v t
  have hG : (G : L2Vec3 → ℂ) =ᵐ[volume]
      fun ξ => CKN.Leray.pressureApplyFormula ξ
        ((lps_regR12HighTensorFreq ρ ε hε n T hT v t : ComplexTensorL2) ξ) := by
    exact CKN.Leray.measurableFourierMultiplier_ae_eq _ _ _ _ _
  have hH := lps_regR12Pressure_fourier_high_ae
    ρ ε hε a ha n T hT v hv t ht
  have hGH : ((Lp.fourierTransformₗᵢ L2Vec3 ℂ H :
      Lp ℂ 2 (volume : Measure L2Vec3)) : L2Vec3 → ℂ) =ᵐ[volume]
      fun ξ => lps_dampedFourierWordSymbol n [] ξ •
        (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) • (G : L2Vec3 → ℂ) ξ := by
    filter_upwards [hH, hG] with ξ hHξ hGξ
    rw [hHξ, hGξ]
    simp only [lps_dampedFourierWordSymbol, lps_fourierWordSymbol,
      List.map_nil, List.prod_nil, one_mul, smul_smul]
    rw [lps_damped_base_weight_eq]
  have hfield := CKN.Leray.regR12WeightedField_ae_eq
    (lps_dampedFourierWordSymbol n [])
    (lps_dampedFourierWordSymbol_continuous n []).aestronglyMeasurable
    ((2 * π) ^ (0 : ℕ)) (by positivity)
    (lps_dampedFourierWordSymbol_norm_le n [] (by simp)) G H hGH
  have hfield' :=
    CKN.Leray.vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hfield
  have hquad := CKN.Leray.rieszPressure_ae_eq_quadPressureTilde V
  have hcanonical := CKN.Leray.forcedQuadPressure_slice
    ρ ε hε (CKN.Leray.regR12Curve ρ ε hε a ha) t
  filter_upwards [hfield', hquad, hcanonical] with x hx hq hc
  change Complex.re
    (CKN.Leray.regR12WeightedField (lps_dampedFourierWordSymbol n []) G
      (WithLp.toLp 2 x)) = _
  rw [hx]
  simpa only [H, V, CKN.Leray.quadPressureTilde] using hq.symm.trans hc.symm

/-- The canonical regularized pressure has a continuous spatial slice
at every positive time. -/
theorem lps_regR12Pressure_slice_continuous
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (t : ℝ) (ht : 0 < t) :
    Continuous (fun x : Vec3 => CKN.Leray.forcedQuadPressure ρ ε hε
      (CKN.Leray.regR12Curve ρ ε hε a ha) (x, t)) := by
  have hpath : ∀ T : ℝ, 0 ≤ T →
      ∃ v : C(CKN.Leray.RegularizedMildTimeInterval T,
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2),
      ∀ s : CKN.Leray.RegularizedMildTimeInterval T,
        CKN.Leray.regularisedBesselSobolevToL2CLM
          ((2 * 2 : ℕ) : ℝ) (by positivity) (v s) =
          CKN.Leray.complexifyVectorL2
            (CKN.Leray.regR12Curve ρ ε hε a ha s.1) := by
    intro T hT
    obtain ⟨v, hv⟩ := CKN.Leray.regUniformMollifiedInitial_global_bessel_path
      ρ ε hε a ha 2 T hT
    refine ⟨v, ?_⟩
    intro s
    simpa only [CKN.Leray.regR12Curve] using hv s
  have hp := (CKN.Leray.regR12Pressure_regularity ρ ε hε a ha hpath).1
  have hprod : Continuous (fun x : Vec3 => ((x, t) : Vec3 × ℝ)) :=
    (continuous_id : Continuous (fun x : Vec3 => x)).prodMk
      (continuous_const : Continuous (fun _ : Vec3 => t))
  exact hp.comp_continuous (by
    have heq : (fun x : Vec3 => ((x, t) : ParabolicPoint)) =
        (fun q : Vec3 × ℝ => ((q.1, q.2) : ParabolicPoint)) ∘
          (fun x : Vec3 => (x, t)) := by
      funext x
      rfl
    rw [heq]
    exact CKN.Foundation.Parabolic.continuous_prod_to_parabolicPoint.comp
      hprod)
    (fun x => ⟨Set.mem_univ _, ht⟩)

/-- A high-Bessel pressure model equals the canonical pressure
pointwise on every positive-time slice (`prop:lps-smoothing`). -/
theorem lps_regR12PressureHighModel_eq
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (v : C(CKN.Leray.RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * (n + 2) : ℕ) : ℝ) 2))
    (hv : ∀ t : CKN.Leray.RegularizedMildTimeInterval T,
      CKN.Leray.regularisedBesselSobolevToL2CLM
        ((2 * (n + 2) : ℕ) : ℝ) (by positivity) (v t) =
        CKN.Leray.complexifyVectorL2
          (CKN.Leray.regR12Curve ρ ε hε a ha t.1))
    (t : ℝ) (ht : t ∈ Icc 0 T) (htpos : 0 < t) :
    (fun x : Vec3 => lps_regR12PressureHighModel ρ ε hε n T hT v (x, t)) =
      fun x : Vec3 => CKN.Leray.forcedQuadPressure ρ ε hε
        (CKN.Leray.regR12Curve ρ ε hε a ha) (x, t) := by
  have hmodel : Continuous (fun x : Vec3 =>
      lps_regR12PressureHighModel ρ ε hε n T hT v (x, t)) := by
    let G := lps_regR12PressureHighFreq ρ ε hε n T hT v t
    let M := lps_dampedFourierWordSymbol n []
    let f : L2Vec3 → ℂ := fun ξ =>
      M ξ • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
        (G : L2Vec3 → ℂ) ξ
    have hf : Integrable f volume :=
      CKN.Leray.regR12_weighted_integrable M
        (lps_dampedFourierWordSymbol_continuous n []).aestronglyMeasurable
        ((2 * π) ^ (0 : ℕ)) (by positivity)
        (lps_dampedFourierWordSymbol_norm_le n [] (by simp))
        G (Lp.memLp G)
    have hToLp : Continuous (fun x : Vec3 => (WithLp.toLp 2 x : L2Vec3)) :=
      PiLp.continuous_toLp 2 _
    exact Complex.reCLM.continuous.comp
      ((CKN.Leray.regR12_fourierInv_continuous f hf).comp hToLp)
  exact Measure.eq_of_ae_eq
    (lps_regR12PressureHighModel_ae_eq
      ρ ε hε a ha n T hT v hv t ht)
    hmodel (lps_regR12Pressure_slice_continuous ρ ε hε a ha t htpos)

end ESS
