/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Complex.Wirtinger
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.FourierMultiplier.Basic

/-!
# The Beurling–Ahlfors transform and its powers

With `ℂ ≅ ℝ²` by `x + iy ↦ (x, y)` and Mathlib's Fourier transform
`𝓕 f (ξ) = ∫ e^{−2πi ⟨v, ξ⟩} f (v) dv`:

* `HarmonicAnalysis.beurlingSymbol ξ = (conj ξ) / ξ`, the symbol of the Beurling–Ahlfors transform
`𝓑`
  (`0` at `ξ = 0`, by Lean's `0 / 0 = 0`; the value at one point does not matter);
* `HarmonicAnalysis.beurlingPow k f = 𝓕⁻¹ (m^k · 𝓕 f)`, the power `𝓑^k`;
* `HarmonicAnalysis.beurlingPowNorm k p = ‖𝓑^k‖_{L^p (ℝ²) → L^p (ℝ²)}`, computed on Schwartz
  functions (`HarmonicAnalysis.multiplierNorm`).

## Main results

* `HarmonicAnalysis.beurlingPow_dzbarCLM_pow`: `𝓑^k (∂_zbar^k F) = ∂^k F` for every Schwartz `F`
  (on the Fourier side, `m^k (π i ξ)^k = (π i (conj ξ))^k`). For `k = 1` this is the
  characterisation
  `𝓑 (∂_zbar h) = ∂h` of the Beurling–Ahlfors transform. With the pointwise derivatives:
  `HarmonicAnalysis.beurlingPow_dzbar_iterate`. The `k`-fold iterate of `𝓑` is `𝓑^k` on the
  functions `∂_zbar^k F` (`HarmonicAnalysis.iterate_beurlingPow_one_dzbar_iterate`).
* `HarmonicAnalysis.div_le_beurlingPowNorm_of_tendsto` (density): if Schwartz functions `φ_k`
  satisfy `∂_zbar^k φ_k → u` and `∂^k φ_k → v` in `L^p`, then `‖v‖_p / ‖u‖_p ≤ ‖𝓑^k‖_p`. For
  `f ∈ W^{k,p}` with `u = ∂_zbar^k f`, `v = ∂^k f`, this is `𝓑^k (∂_zbar^k f) = ∂^k f` (Dragičević
  2011,
  p. 465; lecture notes, §4.1, and Exercise 2.19 for `k = 1`, whose hint is "first consider smooth
  `h` and then approximate"), used through the norm over Schwartz functions.
* Elementary properties of the symbol: `|m| ≤ 1`, `m (−ξ) = m (ξ)`, `m (t ξ) = m (ξ)` for real
  `t ≠ 0`, continuity off `0`, measurability.

## References

* O. Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
  operator*, Arch. Math. 96 (2011), 463–471, p. 465.
* O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes,
  [arXiv:2109.04555](https://arxiv.org/abs/2109.04555), §1.3 ((1.11)), Exercise 2.19 and §4.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped SchwartzMap ENNReal ComplexConjugate FourierTransform Real

namespace HarmonicAnalysis

theorem norm_beurlingSymbol_le (ξ : ℂ) : ‖beurlingSymbol ξ‖ ≤ 1 := by
  rcases eq_or_ne ξ 0 with rfl | h
  · simp [beurlingSymbol]
  · simp [beurlingSymbol, h]

theorem beurlingSymbol_neg (ξ : ℂ) : beurlingSymbol (-ξ) = beurlingSymbol ξ := by
  simp [beurlingSymbol, neg_div_neg_eq]

theorem beurlingSymbol_ofReal_mul {t : ℝ} (ht : t ≠ 0) (ξ : ℂ) :
    beurlingSymbol (t * ξ) = beurlingSymbol ξ := by
  simp only [beurlingSymbol, map_mul, Complex.conj_ofReal]
  rw [mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr ht)]

theorem continuousAt_beurlingSymbol {ξ : ℂ} (hξ : ξ ≠ 0) : ContinuousAt beurlingSymbol ξ :=
  Complex.continuous_conj.continuousAt.div continuousAt_id hξ

theorem measurable_beurlingSymbol : Measurable beurlingSymbol :=
  Complex.continuous_conj.measurable.div measurable_id

/-- The Fourier symbol of `∂_zbar^k`: `𝓕 (∂_zbar^k F) (ξ) = (π i ξ)^k 𝓕 F (ξ)`. -/
private lemma fourier_dzbarCLM_pow (k : ℕ) (F : 𝓢(ℂ, ℂ)) (ξ : ℂ) :
    𝓕 ((dzbarCLM ^ k) F : ℂ → ℂ) ξ = ((π : ℂ) * Complex.I * ξ) ^ k • 𝓕 (F : ℂ → ℂ) ξ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, fourier_dzbarCLM, ih, smul_smul, ← pow_succ']

/-- The Fourier symbol of `∂^k`: `𝓕 (∂^k F) (ξ) = (π i (conj ξ))^k 𝓕 F (ξ)`. -/
private lemma fourier_dzCLM_pow (k : ℕ) (F : 𝓢(ℂ, ℂ)) (ξ : ℂ) :
    𝓕 ((dzCLM ^ k) F : ℂ → ℂ) ξ = ((π : ℂ) * Complex.I * conj ξ) ^ k • 𝓕 (F : ℂ → ℂ) ξ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, fourier_dzCLM, ih, smul_smul, ← pow_succ']

/-- `𝓑^k (∂_zbar^k F) = ∂^k F` for every Schwartz function `F`. -/
theorem beurlingPow_dzbarCLM_pow (k : ℕ) (F : 𝓢(ℂ, ℂ)) :
    beurlingPow k ((dzbarCLM ^ k) F : ℂ → ℂ) = ((dzCLM ^ k) F : ℂ → ℂ) := by
  -- On the Fourier side, `m^k (π i ξ)^k = (π i (conj ξ))^k`.
  have hsymb : (fun ξ => beurlingSymbol ξ ^ k • 𝓕 ((dzbarCLM ^ k) F : ℂ → ℂ) ξ) =
      𝓕 ((dzCLM ^ k) F : ℂ → ℂ) := by
    ext ξ
    rw [fourier_dzbarCLM_pow, fourier_dzCLM_pow, smul_smul]
    congr 1
    rcases eq_or_ne ξ 0 with rfl | hξ
    · rcases k with _ | k <;> simp [beurlingSymbol]
    · rw [beurlingSymbol, ← mul_pow]
      congr 1
      field_simp
  -- Fourier inversion on `𝓢(ℂ, ℂ)`.
  rw [beurlingPow, fourierMultiplier, hsymb, ← SchwartzMap.fourier_coe,
    ← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq]

/-- `𝓑^k (∂_zbar^k F) = ∂^k F` for every Schwartz function `F`, with the pointwise derivatives. -/
theorem beurlingPow_dzbar_iterate (k : ℕ) (F : 𝓢(ℂ, ℂ)) :
    beurlingPow k (dzbar^[k] F) = dz^[k] F := by
  rw [← coe_dzbarCLM_pow, ← coe_dzCLM_pow]
  exact beurlingPow_dzbarCLM_pow k F

/-- `𝓑^k` is the `k`-fold iterate of `𝓑` on the functions `∂_zbar^k F`, `F` Schwartz: applying `𝓑`
to
`∂_zbar^k F` gives `∂_zbar^{k−1} (∂F)`, then `∂_zbar^{k−2} (∂²F)`, and so on to `∂^k F`. -/
theorem iterate_beurlingPow_one_dzbar_iterate (k : ℕ) (F : 𝓢(ℂ, ℂ)) :
    (beurlingPow 1)^[k] (dzbar^[k] F) = dz^[k] F := by
  rw [← coe_dzbarCLM_pow, ← coe_dzCLM_pow]
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    have h : beurlingPow 1 ((dzbarCLM ^ (k + 1)) F : ℂ → ℂ) =
        ((dzbarCLM ^ k) (dzCLM F) : ℂ → ℂ) := by
      have h1 := beurlingPow_dzbarCLM_pow 1 ((dzbarCLM ^ k) F)
      have h2 := congrArg (fun T => T F) (commute_dzCLM_dzbarCLM.pow_right k).eq
      simp only [pow_one, mul_apply_eq_comp] at h1 h2
      rw [pow_succ', mul_apply_eq_comp, h1, h2]
    rw [Function.iterate_succ_apply, h, ih, pow_succ, mul_apply_eq_comp]

/-- Density: if Schwartz functions `φ_k` satisfy `∂_zbar^k φ_k → u` and `∂^k φ_k → v` in `L^p`,
`1 ≤ p`, then `‖v‖_p / ‖u‖_p ≤ ‖𝓑^k‖_p`. -/
theorem div_le_beurlingPowNorm_of_tendsto (k : ℕ) {p : ℝ} (hp : 1 ≤ p) {φ : ℕ → 𝓢(ℂ, ℂ)}
    {u v : ℂ → ℂ}
    (hφu : Tendsto (fun j => eLpNorm (fun z => (dzbarCLM ^ k) (φ j) z - u z) (ENNReal.ofReal p)
      volume) atTop (𝓝 0))
    (hφv : Tendsto (fun j => eLpNorm (fun z => (dzCLM ^ k) (φ j) z - v z) (ENNReal.ofReal p)
      volume) atTop (𝓝 0)) :
    eLpNorm v (ENNReal.ofReal p) volume / eLpNorm u (ENNReal.ofReal p) volume ≤
      beurlingPowNorm k p := by
  refine div_le_multiplierNorm_of_tendsto _ hp (φ := fun j => (dzbarCLM ^ k) (φ j)) hφu ?_
  have h : ∀ j, fourierMultiplier (fun ξ => beurlingSymbol ξ ^ k) ((dzbarCLM ^ k) (φ j)) =
      ((dzCLM ^ k) (φ j) : ℂ → ℂ) := fun j => beurlingPow_dzbarCLM_pow k (φ j)
  simpa only [h] using hφv

end HarmonicAnalysis
