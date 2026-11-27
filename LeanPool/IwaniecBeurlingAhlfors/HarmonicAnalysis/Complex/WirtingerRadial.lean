/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Complex.Wirtinger
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Wirtinger derivatives of `z^a (conj z)^b K (|z|²)`

The Leibniz and chain rules for the Wirtinger derivatives of the functions
`w ↦ w^a (conj w)^b K (|w|²)`, with `a, b ∈ ℕ` and `K : ℝ → ℂ` differentiable at `|z|²`:

* `HarmonicAnalysis.dzbar_monomial_mul_radial`:
  `∂_zbar (z^a (conj z)^b K (|z|²)) = b z^a (conj z)^{b−1} K (|z|²) + z^{a+1} (conj z)^b K' (|z|²)`;
* `HarmonicAnalysis.dz_monomial_mul_radial`:
  `∂ (z^a (conj z)^b K (|z|²)) = a z^{a−1} (conj z)^b K (|z|²) + z^a (conj z)^{b+1} K' (|z|²)`.

(The terms with the factor `b`, resp. `a`, are absent when `b = 0`, resp. `a = 0`; in Lean the
exponent `b − 1` is truncated, and the factor `0` makes the term vanish.) The proof computes the
real Fréchet derivative by the product and chain rules, with `|w|² = ‖w‖²`, and evaluates it at
`1` and `I`.

## Main results

* `HarmonicAnalysis.differentiableAt_monomial_mul_radial`: `w ↦ w^a (conj w)^b K (|w|²)` is
  real-differentiable at `z`.
* Linearity: `HarmonicAnalysis.dz_add`, `HarmonicAnalysis.dz_sub` (for real-differentiable
  functions), `HarmonicAnalysis.dz_neg`, `HarmonicAnalysis.dz_const_smul`,
  `HarmonicAnalysis.dz_const_mul`, and the same for `dzbar` (`HarmonicAnalysis.dzbar_add`, …).
* Locality: `Filter.EventuallyEq.dz_eq`, `Filter.EventuallyEq.dzbar_eq`.
* `HarmonicAnalysis.dz_sq_mul_radial`, `HarmonicAnalysis.dzbar_sq_mul_radial`: the case `a = 2`,
  `b = 0`, `∂ (z² K (|z|²)) = 2 z K (|z|²) + z² (conj z) K' (|z|²)` and
  `∂_zbar (z² K (|z|²)) = z³ K' (|z|²)`.
* `HarmonicAnalysis.dz_dz_sq_mul_radial`, `HarmonicAnalysis.dzbar_dzbar_sq_mul_radial`: with
  `t = |z|²`, `K` differentiable near `t` and `K'` differentiable at `t`,
  `∂² (z² K (|z|²)) = 2 K (t) + 4 t K' (t) + t² K'' (t)` and `∂_zbar² (z² K (|z|²)) = z⁴ K'' (t)`.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate Topology

namespace HarmonicAnalysis

/-- The real Fréchet derivative of `w ↦ w^a (conj w)^b K (|w|²)` at `z`, by the product rule:
`h ↦ a z^{a−1} h (conj z)^b K + z^a b (conj z)^{b−1} (conj h) K + z^a (conj z)^b K' 2 ⟪z, h⟫`. -/
private lemma hasFDerivAt_monomial_mul_radial (a b : ℕ) {K : ℝ → ℂ} {z : ℂ}
    (hK : DifferentiableAt ℝ K (Complex.normSq z)) :
    HasFDerivAt (fun w => w ^ a * conj w ^ b * K (Complex.normSq w))
      ((z ^ a * conj z ^ b) • ((ContinuousLinearMap.toSpanSingleton ℝ
          (deriv K (Complex.normSq z))).comp (2 • innerSL ℝ z)) +
        K (Complex.normSq z) • (z ^ a • ((b • conj z ^ (b - 1)) •
          (Complex.conjCLE : ℂ →L[ℝ] ℂ)) +
          conj z ^ b • ((a • z ^ (a - 1)) • ContinuousLinearMap.id ℝ ℂ))) z := by
  have h1 := hasFDerivAt_pow (𝕜 := ℝ) a (x := z)
  have h2 := (Complex.conjCLE.hasFDerivAt (x := z)).pow b
  have h3 : HasFDerivAt (fun w => K (Complex.normSq w))
      ((ContinuousLinearMap.toSpanSingleton ℝ
          (deriv K (Complex.normSq z))).comp (2 • innerSL ℝ z)) z := by
    have hK' := hK.hasDerivAt.hasFDerivAt
    rw [Complex.normSq_eq_norm_sq] at hK'
    have := hK'.comp z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
    simp only [← Complex.normSq_eq_norm_sq] at this
    exact this
  exact (h1.mul h2).mul h3

/-- The real Fréchet derivative of `w ↦ w^a (conj w)^b K (|w|²)` at `z`, applied to `h`. -/
private lemma fderiv_monomial_mul_radial_apply (a b : ℕ) {K : ℝ → ℂ} {z : ℂ}
    (hK : DifferentiableAt ℝ K (Complex.normSq z)) (h : ℂ) :
    fderiv ℝ (fun w => w ^ a * conj w ^ b * K (Complex.normSq w)) z h =
      a * z ^ (a - 1) * h * conj z ^ b * K (Complex.normSq z) +
        z ^ a * (b * conj z ^ (b - 1) * conj h) * K (Complex.normSq z) +
        z ^ a * conj z ^ b * (2 * (z.re * h.re + z.im * h.im)) * deriv K (Complex.normSq z) := by
  rw [(hasFDerivAt_monomial_mul_radial a b hK).fderiv]
  simp only [ContinuousLinearMap.comp_smul, nsmul_eq_mul, Nat.cast_ofNat, smul_add, add_apply,
    smul_apply, mul_apply_eq_comp, ContinuousLinearMap.comp_apply, coe_innerSL_apply,
    Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add,
    ContinuousLinearMap.toSpanSingleton_apply, Complex.real_smul, Complex.ofReal_add,
    Complex.ofReal_mul, ContinuousLinearMap.ofNat_apply, smul_eq_mul,
    ContinuousLinearEquiv.coe_coe, ContinuousAlgEquiv.coeCLE_apply, Complex.conjCAE_apply,
    ContinuousLinearMap.id_apply]
  ring

/-- `∂_zbar (z^a (conj z)^b K (|z|²)) = b z^a (conj z)^{b−1} K (|z|²) + z^{a+1} (conj z)^b K'
(|z|²)`. -/
theorem dzbar_monomial_mul_radial (a b : ℕ) {K : ℝ → ℂ} {z : ℂ}
    (hK : DifferentiableAt ℝ K (Complex.normSq z)) :
    dzbar (fun w => w ^ a * conj w ^ b * K (Complex.normSq w)) z =
      b * z ^ a * conj z ^ (b - 1) * K (Complex.normSq z) +
        z ^ (a + 1) * conj z ^ b * deriv K (Complex.normSq z) := by
  simp only [dzbar, smul_eq_mul, fderiv_monomial_mul_radial_apply a b hK, Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im, map_one, Complex.conj_I, Complex.ofReal_one,
    Complex.ofReal_zero]
  linear_combination (2⁻¹ * a * z ^ (a - 1) * conj z ^ b * K (Complex.normSq z) -
      2⁻¹ * b * z ^ a * conj z ^ (b - 1) * K (Complex.normSq z)) * Complex.I_sq +
    z ^ a * conj z ^ b * deriv K (Complex.normSq z) * Complex.re_add_im z

/-- `∂ (z^a (conj z)^b K (|z|²)) = a z^{a−1} (conj z)^b K (|z|²) + z^a (conj z)^{b+1} K' (|z|²)`. -/
theorem dz_monomial_mul_radial (a b : ℕ) {K : ℝ → ℂ} {z : ℂ}
    (hK : DifferentiableAt ℝ K (Complex.normSq z)) :
    dz (fun w => w ^ a * conj w ^ b * K (Complex.normSq w)) z =
      a * z ^ (a - 1) * conj z ^ b * K (Complex.normSq z) +
        z ^ a * conj z ^ (b + 1) * deriv K (Complex.normSq z) := by
  have hc : conj z = z.re - z.im * Complex.I := by apply Complex.ext <;> simp
  simp only [dz, smul_eq_mul, fderiv_monomial_mul_radial_apply a b hK, Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im, map_one, Complex.conj_I, Complex.ofReal_one,
    Complex.ofReal_zero]
  linear_combination (-2⁻¹ * a * z ^ (a - 1) * conj z ^ b * K (Complex.normSq z) +
      2⁻¹ * b * z ^ a * conj z ^ (b - 1) * K (Complex.normSq z)) * Complex.I_sq -
    z ^ a * conj z ^ b * deriv K (Complex.normSq z) * hc

/-- `w ↦ w^a (conj w)^b K (|w|²)` is real-differentiable at `z` if `K` is differentiable at
`|z|²`. -/
theorem differentiableAt_monomial_mul_radial (a b : ℕ) {K : ℝ → ℂ} {z : ℂ}
    (hK : DifferentiableAt ℝ K (Complex.normSq z)) :
    DifferentiableAt ℝ (fun w => w ^ a * conj w ^ b * K (Complex.normSq w)) z :=
  (hasFDerivAt_monomial_mul_radial a b hK).differentiableAt

section Linear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {f g : ℂ → F} {z : ℂ}

/-- `∂ (f + g) = ∂f + ∂g` at a point where `f` and `g` are real-differentiable. -/
theorem dz_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz (fun w => f w + g w) z = dz f z + dz g z := by
  simp only [dz, fderiv_fun_add hf hg, add_apply]
  module

/-- `∂_zbar (f + g) = ∂_zbar f + ∂_zbar g` at a point where `f` and `g` are real-differentiable. -/
theorem dzbar_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dzbar (fun w => f w + g w) z = dzbar f z + dzbar g z := by
  simp only [dzbar, fderiv_fun_add hf hg, add_apply]
  module

/-- `∂ (f − g) = ∂f − ∂g` at a point where `f` and `g` are real-differentiable. -/
theorem dz_sub (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz (fun w => f w - g w) z = dz f z - dz g z := by
  simp only [dz, fderiv_fun_sub hf hg, sub_apply]
  module

/-- `∂_zbar (f − g) = ∂_zbar f − ∂_zbar g` at a point where `f` and `g` are real-differentiable. -/
theorem dzbar_sub (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dzbar (fun w => f w - g w) z = dzbar f z - dzbar g z := by
  simp only [dzbar, fderiv_fun_sub hf hg, sub_apply]
  module

/-- `∂ (−f) = −∂f`. -/
theorem dz_neg : dz (fun w => -f w) z = -dz f z := by
  simp only [dz, fderiv_fun_neg, neg_apply]
  module

/-- `∂_zbar (−f) = −∂_zbar f`. -/
theorem dzbar_neg : dzbar (fun w => -f w) z = -dzbar f z := by
  simp only [dzbar, fderiv_fun_neg, neg_apply]
  module

/-- `∂ (c f) = c ∂f` for a complex constant `c`. -/
theorem dz_const_smul (c : ℂ) : dz (fun w => c • f w) z = c • dz f z := by
  simp only [dz, show (fun w => c • f w) = c • f from rfl, fderiv_const_smul_field,
    Pi.smul_apply, smul_apply]
  module

/-- `∂_zbar (c f) = c ∂_zbar f` for a complex constant `c`. -/
theorem dzbar_const_smul (c : ℂ) : dzbar (fun w => c • f w) z = c • dzbar f z := by
  simp only [dzbar, show (fun w => c • f w) = c • f from rfl, fderiv_const_smul_field,
    Pi.smul_apply, smul_apply]
  module

/-- Locality of `∂`: functions that agree near `z` have the same `∂` at `z`. -/
theorem _root_.Filter.EventuallyEq.dz_eq (h : f =ᶠ[𝓝 z] g) : dz f z = dz g z := by
  simp only [dz, h.fderiv_eq]

/-- Locality of `∂_zbar`: functions that agree near `z` have the same `∂_zbar` at `z`. -/
theorem _root_.Filter.EventuallyEq.dzbar_eq (h : f =ᶠ[𝓝 z] g) : dzbar f z = dzbar g z := by
  simp only [dzbar, h.fderiv_eq]

end Linear

/-- `∂ (c f) = c ∂f` for a complex constant `c` and `f : ℂ → ℂ`. -/
theorem dz_const_mul (c : ℂ) {f : ℂ → ℂ} {z : ℂ} : dz (fun w => c * f w) z = c * dz f z :=
  dz_const_smul c

/-- `∂_zbar (c f) = c ∂_zbar f` for a complex constant `c` and `f : ℂ → ℂ`. -/
theorem dzbar_const_mul (c : ℂ) {f : ℂ → ℂ} {z : ℂ} :
    dzbar (fun w => c * f w) z = c * dzbar f z :=
  dzbar_const_smul c

/-- `∂ (z² K (|z|²)) = 2 z K (|z|²) + z² (conj z) K' (|z|²)`. -/
theorem dz_sq_mul_radial {K : ℝ → ℂ} {z : ℂ} (hK : DifferentiableAt ℝ K (Complex.normSq z)) :
    dz (fun w => w ^ 2 * K (Complex.normSq w)) z =
      2 * z * K (Complex.normSq z) + z ^ 2 * conj z * deriv K (Complex.normSq z) := by
  have := dz_monomial_mul_radial 2 0 hK
  norm_num at this
  exact this

/-- `∂_zbar (z² K (|z|²)) = z³ K' (|z|²)`. -/
theorem dzbar_sq_mul_radial {K : ℝ → ℂ} {z : ℂ} (hK : DifferentiableAt ℝ K (Complex.normSq z)) :
    dzbar (fun w => w ^ 2 * K (Complex.normSq w)) z = z ^ 3 * deriv K (Complex.normSq z) := by
  have := dzbar_monomial_mul_radial 2 0 hK
  norm_num at this
  exact this

/-- `∂² (z² K (|z|²)) = 2 K (t) + 4 t K' (t) + t² K'' (t)`, `t = |z|²`, if `K` is differentiable
near `t` and `K'` at `t`. -/
theorem dz_dz_sq_mul_radial {K : ℝ → ℂ} {z : ℂ}
    (hK : ∀ᶠ t in 𝓝 (Complex.normSq z), DifferentiableAt ℝ K t)
    (hK' : DifferentiableAt ℝ (deriv K) (Complex.normSq z)) :
    dz (dz (fun w => w ^ 2 * K (Complex.normSq w))) z =
      2 * K (Complex.normSq z) + 4 * Complex.normSq z * deriv K (Complex.normSq z) +
        Complex.normSq z ^ 2 * deriv (deriv K) (Complex.normSq z) := by
  have hK0 := hK.self_of_nhds
  have h1 : dz (fun w => w ^ 2 * K (Complex.normSq w)) =ᶠ[𝓝 z] fun w =>
      2 * (w ^ 1 * conj w ^ 0 * K (Complex.normSq w)) +
        w ^ 2 * conj w ^ 1 * deriv K (Complex.normSq w) :=
    (Complex.continuous_normSq.tendsto z |>.eventually hK).mono fun w hw => by
      rw [dz_sq_mul_radial hw]
      ring
  rw [h1.dz_eq, dz_add ((differentiableAt_monomial_mul_radial 1 0 hK0).const_mul 2)
    (differentiableAt_monomial_mul_radial 2 1 hK'), dz_const_mul,
    dz_monomial_mul_radial 1 0 hK0, dz_monomial_mul_radial 2 1 hK', ← Complex.mul_conj]
  ring

/-- `∂_zbar² (z² K (|z|²)) = z⁴ K'' (|z|²)` if `K` is differentiable near `|z|²` and `K'` at
`|z|²`. -/
theorem dzbar_dzbar_sq_mul_radial {K : ℝ → ℂ} {z : ℂ}
    (hK : ∀ᶠ t in 𝓝 (Complex.normSq z), DifferentiableAt ℝ K t)
    (hK' : DifferentiableAt ℝ (deriv K) (Complex.normSq z)) :
    dzbar (dzbar (fun w => w ^ 2 * K (Complex.normSq w))) z =
      z ^ 4 * deriv (deriv K) (Complex.normSq z) := by
  have h1 : dzbar (fun w => w ^ 2 * K (Complex.normSq w)) =ᶠ[𝓝 z] fun w =>
      w ^ 3 * conj w ^ 0 * deriv K (Complex.normSq w) :=
    (Complex.continuous_normSq.tendsto z |>.eventually hK).mono fun w hw => by
      rw [dzbar_sq_mul_radial hw]
      ring
  rw [h1.dzbar_eq, dzbar_monomial_mul_radial 3 0 hK']
  ring

end HarmonicAnalysis
