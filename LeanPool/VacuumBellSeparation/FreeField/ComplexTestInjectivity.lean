/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialFourierSlice
public import LeanPool.VacuumBellSeparation.FreeField.AnalyticOddOrder
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroNondegenerate
public import LeanPool.VacuumBellSeparation.FreeField.Lorentz

/-!
# Complex injectivity for compact test sources

The source's entire-function argument is carried out here for actual compactly
supported smooth test pairs. The transverse slice has effective mass
`sqrt (m²+|p_perp|²)>0`, so the odd-order obstruction applies. This does not
extend injectivity to the Hilbert completion: completed source components
must still be embedded into compactly supported distributions.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate

namespace VacuumBellSeparation

theorem dispersion_sq_transverse {m : ℝ} (p : EuclideanSpace ℝ (Fin 3))
    (hp : ⟪e₁, p⟫_ℝ = 0) (t : ℝ) :
    dispersion m (p + t • e₁) ^ 2 = t ^ 2 + dispersion m p ^ 2 := by
  rw [dispersion_sq, dispersion_sq, ← real_inner_self_eq_norm_sq,
    inner_add_smul_e₁, hp, real_inner_self_eq_norm_sq]
  ring

/-- Reality separates two real test functions from their vanishing complex Fourier combination. -/
theorem spatialTestFunctions_eq_zero_of_complex_fourier_eq_zero
    (f g : SpatialTestFunction)
    (h : ∀ p, spatialFourier f p + Complex.I * spatialFourier g p = 0) : f = 0 ∧ g = 0 := by
  have hparts (p : EuclideanSpace ℝ (Fin 3)) : spatialFourier f p = 0 ∧ spatialFourier g p = 0 := by
    have hp := h p
    have hn := congrArg conj (h (-p))
    simp only [map_add, map_mul, spatialFourier_neg, Complex.conj_conj,
      Complex.conj_I, map_zero] at hn
    constructor
    · linear_combination (1 / 2 : ℂ) * hp + (1 / 2 : ℂ) * hn
    · have hi : Complex.I * spatialFourier g p = 0 := by
        linear_combination (1 / 2 : ℂ) * hp - (1 / 2 : ℂ) * hn
      exact (mul_eq_zero.mp hi).resolve_left Complex.I_ne_zero
  exact ⟨spatialTestFunction_eq_zero_of_fourier_eq_zero f (fun p => (hparts p).1),
    spatialTestFunction_eq_zero_of_fourier_eq_zero g (fun p => (hparts p).2)⟩

/-- The pointwise complexified source map has trivial kernel on compact test pairs. -/
theorem timeZero_complex_test_injective {m : ℝ} (hm : 0 < m) (u v : TimeZeroSource)
    (hκ : ∀ p, timeZeroOneParticle m u p + Complex.I * timeZeroOneParticle m v p = 0) :
    u = 0 ∧ v = 0 := by
  let F := fun p => spatialFourier u.1 p + Complex.I * spatialFourier v.1 p
  let G := fun p => spatialFourier u.2 p + Complex.I * spatialFourier v.2 p
  have hlinear (p : EuclideanSpace ℝ (Fin 3)) :
      F p = -(Complex.I * (dispersion m p : ℂ) * G p) := by
    have h := hκ p
    dsimp [F, G, timeZeroOneParticle] at h ⊢
    linear_combination h
  have hparts (p : EuclideanSpace ℝ (Fin 3)) : F p = 0 ∧ G p = 0 := by
    let pperp := p - ⟪e₁, p⟫_ℝ • e₁
    have hpperp : ⟪e₁, pperp⟫_ℝ = 0 := by
      simp [pperp, inner_sub_right, real_inner_smul_right, norm_e₁]
    let M := dispersion m pperp
    have hM : 0 < M := hm.trans_le (le_dispersion hm.le pperp)
    let Fs := fun z => spatialFourierSlice u.1 pperp e₁ z +
      Complex.I * spatialFourierSlice v.1 pperp e₁ z
    let Gs := fun z => spatialFourierSlice u.2 pperp e₁ z +
      Complex.I * spatialFourierSlice v.2 pperp e₁ z
    have hFa : AnalyticOnNhd ℂ Fs Set.univ :=
      (analyticOnNhd_spatialFourierSlice u.1 pperp e₁).add
        (analyticOnNhd_const.mul (analyticOnNhd_spatialFourierSlice v.1 pperp e₁))
    have hGa : AnalyticOnNhd ℂ Gs Set.univ :=
      (analyticOnNhd_spatialFourierSlice u.2 pperp e₁).add
        (analyticOnNhd_const.mul (analyticOnNhd_spatialFourierSlice v.2 pperp e₁))
    have hFs (t : ℝ) : Fs (t : ℂ) = F (pperp + t • e₁) := by
      simp only [Fs, F, spatialFourierSlice_ofReal]
    have hGs (t : ℝ) : Gs (t : ℂ) = G (pperp + t • e₁) := by
      simp only [Gs, G, spatialFourierSlice_ofReal]
    have hrel (t : ℝ) : Fs (t : ℂ) ^ 2 =
        -((t : ℂ) ^ 2 + (M : ℂ) ^ 2) * Gs (t : ℂ) ^ 2 := by
      have hω : (dispersion m (pperp + t • e₁) : ℂ) ^ 2 =
          (t : ℂ) ^ 2 + (M : ℂ) ^ 2 := by
        exact_mod_cast dispersion_sq_transverse pperp hpperp t
      rw [hFs, hGs, hlinear, neg_sq, mul_pow, mul_pow, Complex.I_sq, hω]
      ring
    obtain ⟨hf0, hg0⟩ := entire_massive_square_zero_of_real hM hFa hGa hrel
    have hfp := congrFun hf0 (⟪e₁, p⟫_ℝ : ℂ)
    have hgp := congrFun hg0 (⟪e₁, p⟫_ℝ : ℂ)
    rw [hFs] at hfp
    rw [hGs] at hgp
    simpa [pperp] using And.intro hfp hgp
  obtain ⟨hu1, hv1⟩ := spatialTestFunctions_eq_zero_of_complex_fourier_eq_zero
    u.1 v.1 (fun p => (hparts p).1)
  obtain ⟨hu2, hv2⟩ := spatialTestFunctions_eq_zero_of_complex_fourier_eq_zero
    u.2 v.2 (fun p => (hparts p).2)
  exact ⟨Prod.ext hu1 hu2, Prod.ext hv1 hv2⟩

end VacuumBellSeparation
