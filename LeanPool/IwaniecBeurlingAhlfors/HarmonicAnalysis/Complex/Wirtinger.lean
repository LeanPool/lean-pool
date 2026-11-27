/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Defs

/-!
# The Wirtinger derivatives

For a function `g : ℂ → F` into a complex normed space, with `ℂ ≅ ℝ²` by `x + iy ↦ (x, y)`, the
Wirtinger derivatives at `z` are
`∂g (z) = ½ (∂_x g (z) − i ∂_y g (z))` and `∂_zbar g (z) = ½ (∂_x g (z) + i ∂_y g (z))`,
where `∂_x g (z) = fderiv ℝ g z 1` and `∂_y g (z) = fderiv ℝ g z I`
(`HarmonicAnalysis.dz`, `HarmonicAnalysis.dzbar`). On the Schwartz space `𝓢(ℂ, F)` they are
continuous linear maps (`HarmonicAnalysis.dzCLM`, `HarmonicAnalysis.dzbarCLM`), built from the
line derivatives of Mathlib.

## Main results

* `HarmonicAnalysis.fourier_dzbarCLM`, `HarmonicAnalysis.fourier_dzCLM`: the Fourier symbols.
  With `𝓕 f (ξ) = ∫ e^{−2πi ⟨v, ξ⟩} f (v) dv` (Mathlib's convention, `⟨v, ξ⟩ = Re ((conj v) ξ)`),
  `𝓕 (∂_zbar f) (ξ) = π i ξ 𝓕 f (ξ)` and `𝓕 (∂f) (ξ) = π i (conj ξ) 𝓕 f (ξ)`.
* `HarmonicAnalysis.dzbar_conj`, `HarmonicAnalysis.dz_conj`: the conjugation rules
  `∂_zbar (conj ∘ g) = conj ∘ ∂g` and `∂ (conj ∘ g) = conj ∘ ∂_zbar g`.
* `HarmonicAnalysis.measurable_dz`, `HarmonicAnalysis.measurable_dzbar`: `∂g` and `∂_zbar g` are
  measurable for every `g : ℂ → ℂ`.

## References

* O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes,
  [arXiv:2109.04555](https://arxiv.org/abs/2109.04555), §1.
-/

@[expose] public section

noncomputable section

open scoped SchwartzMap FourierTransform Real ComplexConjugate

namespace HarmonicAnalysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `∂ = ½ (∂_x − i ∂_y)` as a continuous linear map of the Schwartz space `𝓢(ℂ, F)`. -/
def dzCLM : 𝓢(ℂ, F) →L[ℂ] 𝓢(ℂ, F) :=
  (2⁻¹ : ℂ) • (LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, F) (1 : ℂ) -
    Complex.I • LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, F) Complex.I)

/-- `∂_zbar = ½ (∂_x + i ∂_y)` as a continuous linear map of the Schwartz space `𝓢(ℂ, F)`. -/
def dzbarCLM : 𝓢(ℂ, F) →L[ℂ] 𝓢(ℂ, F) :=
  (2⁻¹ : ℂ) • (LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, F) (1 : ℂ) +
    Complex.I • LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, F) Complex.I)

theorem dzCLM_apply (f : 𝓢(ℂ, F)) (z : ℂ) : dzCLM f z = dz f z := by
  simp [dzCLM, dz, SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem dzbarCLM_apply (f : 𝓢(ℂ, F)) (z : ℂ) : dzbarCLM f z = dzbar f z := by
  simp [dzbarCLM, dzbar, SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- `∂^k` on the Schwartz space is the `k`-fold pointwise derivative. -/
theorem coe_dzCLM_pow (k : ℕ) (f : 𝓢(ℂ, F)) : ⇑((dzCLM ^ k) f) = dz^[k] f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, Function.iterate_succ_apply', ← ih]
    exact funext (dzCLM_apply _)

/-- `∂_zbar^k` on the Schwartz space is the `k`-fold pointwise derivative. -/
theorem coe_dzbarCLM_pow (k : ℕ) (f : 𝓢(ℂ, F)) : ⇑((dzbarCLM ^ k) f) = dzbar^[k] f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, Function.iterate_succ_apply', ← ih]
    exact funext (dzbarCLM_apply _)

/-- The Fourier transform of a line derivative, pointwise:
`𝓕 (∂_m f) (ξ) = 2πi ⟨ξ, m⟩ 𝓕 f (ξ)`. -/
private lemma fourier_lineDerivOp_apply (f : 𝓢(ℂ, F)) (m ξ : ℂ) :
    𝓕 (LineDeriv.lineDerivOp m f : ℂ → F) ξ =
      ((2 * π * Complex.I : ℂ) * (inner ℝ ξ m : ℝ)) • 𝓕 (f : ℂ → F) ξ := by
  have : (inner ℝ · m : ℂ → ℝ).HasTemperateGrowth := ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [← SchwartzMap.fourier_coe, SchwartzMap.fourier_lineDerivOp_eq, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply this, SchwartzMap.fourier_coe,
    mul_smul _ ((inner ℝ ξ m : ℝ) : ℂ), Complex.coe_smul]

/-- The Fourier symbol of `∂_zbar`: `𝓕 (∂_zbar f) (ξ) = π i ξ 𝓕 f (ξ)`. -/
theorem fourier_dzbarCLM (f : 𝓢(ℂ, F)) (ξ : ℂ) :
    𝓕 (dzbarCLM f : ℂ → F) ξ = ((π : ℂ) * Complex.I * ξ) • 𝓕 (f : ℂ → F) ξ := by
  have h : dzbarCLM f = (2⁻¹ : ℂ) • (LineDeriv.lineDerivOp (1 : ℂ) f +
      Complex.I • LineDeriv.lineDerivOp Complex.I f) := rfl
  rw [← SchwartzMap.fourier_coe, h]
  simp only [FourierTransform.fourier_smul, FourierTransform.fourier_add, smul_apply, add_apply,
    SchwartzMap.fourier_coe, fourier_lineDerivOp_apply, smul_smul, ← add_smul]
  congr 1
  simp only [Complex.inner, one_mul, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im]
  apply Complex.ext <;> simp <;> ring

/-- The Fourier symbol of `∂`: `𝓕 (∂f) (ξ) = π i (conj ξ) 𝓕 f (ξ)`. -/
theorem fourier_dzCLM (f : 𝓢(ℂ, F)) (ξ : ℂ) :
    𝓕 (dzCLM f : ℂ → F) ξ = ((π : ℂ) * Complex.I * conj ξ) • 𝓕 (f : ℂ → F) ξ := by
  have h : dzCLM f = (2⁻¹ : ℂ) • (LineDeriv.lineDerivOp (1 : ℂ) f -
      Complex.I • LineDeriv.lineDerivOp Complex.I f) := rfl
  rw [← SchwartzMap.fourier_coe, h, sub_eq_add_neg]
  simp only [FourierTransform.fourier_smul, FourierTransform.fourier_add, smul_apply, add_apply,
    SchwartzMap.fourier_coe, fourier_lineDerivOp_apply, smul_smul, ← neg_smul, ← add_smul]
  congr 1
  simp only [Complex.inner, one_mul, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im]
  apply Complex.ext <;> simp <;> ring

/-- `∂` and `∂_zbar` commute on the Schwartz space: their Fourier symbols do. -/
theorem commute_dzCLM_dzbarCLM : Commute (dzCLM : 𝓢(ℂ, ℂ) →L[ℂ] 𝓢(ℂ, ℂ)) dzbarCLM := by
  refine ContinuousLinearMap.ext fun f => ?_
  have h : 𝓕 (dzCLM (dzbarCLM f)) = 𝓕 (dzbarCLM (dzCLM f)) := by
    ext ξ
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, fourier_dzCLM, fourier_dzbarCLM,
      fourier_dzbarCLM, fourier_dzCLM, smul_smul, smul_smul, mul_comm]
  have hinv : ∀ g : 𝓢(ℂ, ℂ), 𝓕⁻ (𝓕 g) = g := FourierTransform.fourierInv_fourier_eq
  rw [mul_apply_eq_comp, mul_apply_eq_comp, ← hinv (dzCLM (dzbarCLM f)), h, hinv]

theorem measurable_dz (g : ℂ → ℂ) : Measurable (dz g) := by
  unfold dz
  fun_prop

theorem measurable_dzbar (g : ℂ → ℂ) : Measurable (dzbar g) := by
  unfold dzbar
  fun_prop

/-- `D (conj ∘ g) (z) v = conj (D g (z) v)` for every `g` (differentiable at `z` or not). -/
private lemma fderiv_conj_apply (g : ℂ → ℂ) (z v : ℂ) :
    fderiv ℝ (fun w => conj (g w)) z v = conj (fderiv ℝ g z v) := by
  have : (fun w => conj (g w)) = Complex.conjCLE ∘ g := rfl
  rw [this, ContinuousLinearEquiv.comp_fderiv]
  rfl

/-- The conjugation rule `∂_zbar (conj ∘ g) = conj ∘ ∂g`. -/
theorem dzbar_conj (g : ℂ → ℂ) (z : ℂ) : dzbar (fun w => conj (g w)) z = conj (dz g z) := by
  simp only [dzbar, dz, fderiv_conj_apply, smul_eq_mul, map_mul, map_sub, Complex.conj_I,
    map_inv₀, map_ofNat]
  ring

/-- The conjugation rule `∂ (conj ∘ g) = conj ∘ ∂_zbar g`. -/
theorem dz_conj (g : ℂ → ℂ) (z : ℂ) : dz (fun w => conj (g w)) z = conj (dzbar g z) := by
  simp only [dzbar, dz, fderiv_conj_apply, smul_eq_mul, map_mul, map_add, Complex.conj_I,
    map_inv₀, map_ofNat]
  ring

end HarmonicAnalysis
