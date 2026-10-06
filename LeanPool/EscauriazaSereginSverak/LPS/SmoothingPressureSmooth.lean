/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingPressureModel
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Smooth spatial slices of the canonical regularized pressure

Every finite Bessel order controls the corresponding finite number of
Fourier moments of the canonical pressure. The pointwise high-order
models agree with the canonical pressure at positive times.
-/

public section

open MeasureTheory FourierTransform Complex Set
open scoped ENNReal FourierTransform Real


noncomputable section

namespace ESS

open CKN.Leray
open CKN CKN.Foundation.Parabolic

/-- A damped scalar pressure frequency field has every Fourier moment
up to its available Bessel order (`prop:lps-smoothing`). -/
theorem lps_dampedPressureField_moment_integrable
    (n r : ℕ) (hr : r ≤ 2 * (n + 1))
    (G : Lp ℂ 2 (volume : Measure L2Vec3)) :
    Integrable (fun ξ : L2Vec3 => ‖ξ‖ ^ r *
      ‖lps_dampedFourierWordSymbol n [] ξ •
        (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
          (G : L2Vec3 → ℂ) ξ‖) volume := by
  let M : L2Vec3 → ℂ := fun ξ =>
    (((‖ξ‖ ^ r * (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ))) : ℝ) : ℂ)
  have hMcont : Continuous M := by
    unfold M
    exact Complex.continuous_ofReal.comp
      ((continuous_norm.pow r).mul
        ((continuous_const.add (continuous_norm.pow 2)).rpow_const
          fun ξ => Or.inl
            (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne'))
  have hMC (ξ : L2Vec3) : ‖M ξ‖ ≤ 1 * (1 + ‖ξ‖ ^ 2) := by
    have hnonneg : 0 ≤ ‖ξ‖ ^ r *
        (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ)) := by positivity
    change ‖((‖ξ‖ ^ r *
      (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ)) : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg, one_mul]
    exact lps_damped_power_bound n r hr ‖ξ‖ (norm_nonneg ξ)
  have hW : Integrable (fun ξ : L2Vec3 =>
      M ξ • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
        (G : L2Vec3 → ℂ) ξ) volume :=
    CKN.Leray.regR12_weighted_integrable M hMcont.aestronglyMeasurable
      1 zero_le_one hMC G (Lp.memLp G)
  have heq : (fun ξ : L2Vec3 =>
      ‖M ξ • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
        (G : L2Vec3 → ℂ) ξ‖) =
      (fun ξ : L2Vec3 => ‖ξ‖ ^ r *
        ‖lps_dampedFourierWordSymbol n [] ξ •
          (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
            (G : L2Vec3 → ℂ) ξ‖) := by
    funext ξ
    have hnonneg : 0 ≤ ‖ξ‖ ^ r := by positivity
    have hweight : lps_dampedFourierWordSymbol n [] ξ =
        (((1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ)) : ℝ) : ℂ) := by
      simp [lps_dampedFourierWordSymbol, lps_fourierWordSymbol]
    have hM : M ξ = (((‖ξ‖ ^ r : ℝ) : ℂ)) *
        lps_dampedFourierWordSymbol n [] ξ := by
      rw [hweight]
      simp only [M, Complex.ofReal_mul]
    rw [hM, mul_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hW.norm.congr (Filter.Eventually.of_forall fun ξ => congrFun heq ξ)

/-- A pressure model at Bessel order `2(n+2)` is spatially `C^m`
whenever `m ≤ 2(n+1)` (`prop:lps-smoothing`). -/
theorem lps_regR12PressureHighModel_slice_contDiff
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (n m : ℕ) (hm : m ≤ 2 * (n + 1))
    (T : ℝ) (hT : 0 ≤ T)
    (v : C(CKN.Leray.RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * (n + 2) : ℕ) : ℝ) 2))
    (t : ℝ) :
    ContDiff ℝ m (fun x : Vec3 =>
      lps_regR12PressureHighModel ρ ε hε n T hT v (x, t)) := by
  let G := lps_regR12PressureHighFreq ρ ε hε n T hT v t
  let f : L2Vec3 → ℂ := fun ξ =>
    lps_dampedFourierWordSymbol n [] ξ •
      (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
        (G : L2Vec3 → ℂ) ξ
  have hFourier : ContDiff ℝ m (𝓕 f) :=
    Real.contDiff_fourier (fun r hr => by
      exact lps_dampedPressureField_moment_integrable n r
        (by exact (WithTop.coe_le_coe.mp hr).trans hm) G)
  have hInv : ContDiff ℝ m (𝓕⁻ f) := by
    have hid : (𝓕⁻ f) = fun x => 𝓕 f (-x) :=
      funext fun x => Real.fourierInv_eq_fourier_neg f x
    rw [hid]
    exact hFourier.comp contDiff_neg
  have hCoord : ContDiff ℝ m
      (fun x : L2Vec3 => Complex.reCLM (𝓕⁻ f x)) :=
    Complex.reCLM.contDiff.comp hInv
  have hToLp : ContDiff ℝ m
      (fun x : Vec3 => (WithLp.toLp 2 x : L2Vec3)) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff
  simpa only [f, G, lps_regR12PressureHighModel,
    CKN.Leray.regR12SpaceTimeField, CKN.Leray.regR12WeightedField,
    Function.comp_def] using hCoord.comp hToLp

/-- The canonical pressure of the regularized velocity is spatially
smooth at every positive time (`prop:lps-smoothing`). -/
theorem lps_regR12Pressure_slice_contDiff
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (t : ℝ) (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 =>
      CKN.Leray.forcedQuadPressure ρ ε hε
        (CKN.Leray.regR12Curve ρ ε hε a ha) (x, t)) := by
  rw [contDiff_iff_forall_nat_le]
  intro m _
  let n : ℕ := m
  obtain ⟨v, hv⟩ :=
    CKN.Leray.regUniformMollifiedInitial_global_bessel_path
      ρ ε hε a ha (n + 2) t ht.le
  have hv' : ∀ s : CKN.Leray.RegularizedMildTimeInterval t,
      CKN.Leray.regularisedBesselSobolevToL2CLM
        ((2 * (n + 2) : ℕ) : ℝ) (by positivity) (v s) =
        CKN.Leray.complexifyVectorL2
          (CKN.Leray.regR12Curve ρ ε hε a ha s.1) := by
    intro s
    simpa only [CKN.Leray.regR12Curve] using hv s
  have hmodel := lps_regR12PressureHighModel_slice_contDiff
    ρ ε hε n m (by dsimp [n]; omega) t ht.le v t
  rw [lps_regR12PressureHighModel_eq
    ρ ε hε a ha n t ht.le v hv' t ⟨ht.le, le_rfl⟩ ht] at hmodel
  exact hmodel

/-- Every classical ordered spatial derivative of the canonical
regularized pressure belongs to spatial `L²` on a positive-time
slice (`prop:lps-smoothing`). -/
theorem lps_regR12Pressure_all_word_memLp_slice
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (t : ℝ) (ht : 0 < t) (α : List (Fin 3)) :
    MemLp (wordDeriv α (fun x : Vec3 =>
      CKN.Leray.forcedQuadPressure ρ ε hε
        (CKN.Leray.regR12Curve ρ ε hε a ha) (x, t))) 2 volume := by
  let n : ℕ := α.length
  have hα : α.length ≤ 2 * (n + 1) := by dsimp [n]; omega
  obtain ⟨v, hv⟩ :=
    CKN.Leray.regUniformMollifiedInitial_global_bessel_path
      ρ ε hε a ha (n + 2) t ht.le
  have hv' : ∀ s : CKN.Leray.RegularizedMildTimeInterval t,
      CKN.Leray.regularisedBesselSobolevToL2CLM
        ((2 * (n + 2) : ℕ) : ℝ) (by positivity) (v s) =
        CKN.Leray.complexifyVectorL2
          (CKN.Leray.regR12Curve ρ ε hε a ha s.1) := by
    intro s
    simpa only [CKN.Leray.regR12Curve] using hv s
  let G := lps_regR12PressureHighFreq ρ ε hε n t ht.le v
  have hmodel := lps_regR12PressureHighModel_eq
    ρ ε hε a ha n t ht.le v hv' t ⟨ht.le, le_rfl⟩ ht
  have hderiv := lps_dampedSpaceTimeField_wordDeriv n α hα
    Complex.reCLM G t
  have hmem := lps_dampedSpaceTimeField_slice_memLp n α hα
    Complex.reCLM (G t)
  rw [← hmodel]
  change MemLp (wordDeriv α (fun x : Vec3 =>
    CKN.Leray.regR12SpaceTimeField Complex.reCLM
      (lps_dampedFourierWordSymbol n []) G (x, t))) 2 volume
  rw [hderiv]
  exact hmem

end ESS
