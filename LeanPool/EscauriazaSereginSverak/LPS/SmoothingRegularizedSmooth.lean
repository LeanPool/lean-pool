/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedDerivativeBridge
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Smooth spatial slices of the regularized velocity

The all-order Bessel lifts give integrable Fourier moments of every
finite degree. Fourier inversion therefore makes every regularized
velocity slice smooth in space.
-/

public section

open MeasureTheory FourierTransform Complex Set
open scoped ENNReal FourierTransform Real


noncomputable section

namespace ESS

open CKN.Leray
open CKN CKN.Foundation.Parabolic

/-- Every polynomial moment of the Fourier transform of a
nonnegative-time regularized velocity slice is integrable
(`prop:lps-smoothing`). -/
theorem lps_regR12FreqCurve_moment_integrable
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (t : ℝ) (ht : 0 ≤ t) (r : ℕ) :
    Integrable (fun ξ : L2Vec3 =>
      ‖ξ‖ ^ r *
        ‖((CKN.Leray.regR12FreqCurve ρ ε hε a ha t : ComplexVectorL2) :
          L2Vec3 → ComplexVec3) ξ‖) volume := by
  obtain ⟨v, hv⟩ :=
    CKN.Leray.regUniformMollifiedInitial_global_bessel_path
      ρ ε hε a ha (r + 2) t ht
  have hv' : ∀ s : CKN.Leray.RegularizedMildTimeInterval t,
      CKN.Leray.regularisedBesselSobolevToL2CLM
          ((2 * (r + 2) : ℕ) : ℝ) (by positivity) (v s) =
        CKN.Leray.complexifyVectorL2
          (CKN.Leray.regR12Curve ρ ε hε a ha s.1) := by
    intro s
    simpa only [CKN.Leray.regR12Curve] using hv s
  let G : ComplexVectorL2 := lpsRegR12HighLiftFreq r t ht v t
  let M : L2Vec3 → ℂ := fun ξ =>
    (((‖ξ‖ ^ r * (1 + ‖ξ‖ ^ 2) ^ (-(r : ℝ))) : ℝ) : ℂ)
  have hMcont : Continuous M := by
    unfold M
    apply Complex.continuous_ofReal.comp
    exact (continuous_norm.pow r).mul
      ((continuous_const.add (continuous_norm.pow 2)).rpow_const
        fun ξ => Or.inl
          (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne')
  have hMC (ξ : L2Vec3) : ‖M ξ‖ ≤ 1 * (1 + ‖ξ‖ ^ 2) := by
    have hnonneg : 0 ≤ ‖ξ‖ ^ r *
        (1 + ‖ξ‖ ^ 2) ^ (-(r : ℝ)) := by positivity
    change ‖((‖ξ‖ ^ r *
      (1 + ‖ξ‖ ^ 2) ^ (-(r : ℝ)) : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg, one_mul]
    exact lps_damped_power_bound r r (by omega) ‖ξ‖ (norm_nonneg ξ)
  have hW : Integrable (fun ξ : L2Vec3 =>
      M ξ • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
        (G : L2Vec3 → ComplexVec3) ξ) volume :=
    CKN.Leray.regR12_weighted_integrable M hMcont.aestronglyMeasurable
      1 zero_le_one hMC G (Lp.memLp G)
  have hfreq := lps_regR12HighLiftFreq_curve_ae_eq
    ρ ε hε a ha r t ht v hv' t ⟨ht, le_rfl⟩
  have heq :
      (fun ξ : L2Vec3 =>
        ‖M ξ • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
          (G : L2Vec3 → ComplexVec3) ξ‖) =ᵐ[volume]
      (fun ξ : L2Vec3 => ‖ξ‖ ^ r *
        ‖((CKN.Leray.regR12FreqCurve ρ ε hε a ha t : ComplexVectorL2) :
          L2Vec3 → ComplexVec3) ξ‖) := by
    filter_upwards [hfreq] with ξ hξ
    have hweight := lps_damped_base_weight_eq r ξ
    have hvec :
        M ξ • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
          (G : L2Vec3 → ComplexVec3) ξ =
        (((‖ξ‖ ^ r : ℝ) : ℂ)) •
          ((CKN.Leray.regR12FreqCurve ρ ε hε a ha t : ComplexVectorL2) :
            L2Vec3 → ComplexVec3) ξ := by
      rw [hξ]
      simp only [M, Complex.ofReal_mul, smul_smul]
      rw [mul_assoc, hweight]
    rw [hvec, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  exact hW.norm.congr heq

/-- Every nonnegative-time spatial slice of the actual regularized
velocity is smooth to all orders (`prop:lps-smoothing`). -/
theorem lps_regR12Velocity_slice_contDiff
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 =>
      CKN.Leray.regR12Velocity ρ ε hε a ha (x, t) i) := by
  let h : L2Vec3 → ComplexVec3 :=
    (CKN.Leray.regR12FreqCurve ρ ε hε a ha t : ComplexVectorL2)
  have hFourier : ContDiff ℝ (⊤ : ℕ∞) (𝓕 h) :=
    Real.contDiff_fourier (fun r _ => by
      simpa only [h] using
        lps_regR12FreqCurve_moment_integrable ρ ε hε a ha t ht r)
  have hInv : ContDiff ℝ (⊤ : ℕ∞) (𝓕⁻ h) := by
    have hid : (𝓕⁻ h) = fun x => 𝓕 h (-x) :=
      funext fun x => Real.fourierInv_eq_fourier_neg h x
    rw [hid]
    exact hFourier.comp contDiff_neg
  have hCoord : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : L2Vec3 => CKN.Leray.regR12CoordCLM i (𝓕⁻ h x)) :=
    (CKN.Leray.regR12CoordCLM i).contDiff.comp hInv
  have hToLp : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => (WithLp.toLp 2 x : L2Vec3)) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff
  simpa only [h, CKN.Leray.regR12Velocity, CKN.Leray.regR12FreqCurve,
    Function.comp_def] using
    hCoord.comp hToLp

end ESS
