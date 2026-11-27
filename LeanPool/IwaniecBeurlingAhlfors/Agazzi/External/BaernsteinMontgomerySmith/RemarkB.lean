/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.CompactSupport

/-!
# Baernstein and Montgomery-Smith, remark (b): from `∂` and `∂_zbar` to the norm of `𝒮`

A. Baernstein II and S. J. Montgomery-Smith, *Some conjectures about integral means of `∂f` and
`∂_zbar f`* (1999; arXiv:math/9709215v2, the version read), end of §1:

* Conjecture 3 (Iwaniec): `∫ |∂_zbar f|^p ≤ (p* − 1)^p ∫ |∂f|^p` for `f ∈ W_hom^{1,p} (ℂ, ℂ)`,
  `1 < p < ∞`; "Like Conjecture 1, each of Conjectures 2 and 3 is true if and only the same
  inequality always holds when `∂f` and `∂_zbar f` are interchanged".
* Remark (b): "Truth of Conjecture 3 would show that the norm of `S` on `L^p (ℂ, ℂ)` is precisely
  `p* − 1`."

The source gives no proof of remark (b). The paper (arXiv:2609.28311, TeX line 301) derives the
norm "by the arguments in [Baernstein1997a] (see also [Guerra2026b] for further details)"; Guerra
(arXiv:2608.23388, proof of the corollary labelled `cor:beurling-lp` in its TeX) makes the passage
to `L^p (ℂ)` explicit, for Hessians: density, a potential, the cut-offs `η_R`, and the limit.

Stated here (`remark_b`) for the upper bound, with any constant `C`, the inequality with `∂` and
`∂_zbar` interchanged as the source allows, and the test functions `f ∈ C_c^∞ (ℂ)`, which is what
the
argument needs: if `∫ |∂f|^p ≤ C^p ∫ |∂_zbar f|^p` for every smooth compactly supported `f`, then
`‖𝒮‖_p ≤ C`. The norm is the package `HarmonicAnalysis`'s `beurlingPowNorm 1 p`, the supremum of
`‖𝒮 g‖_p / ‖g‖_p` over Schwartz functions.

## Proof

Guerra's argument, in the gradient case, as formalized in the package `HarmonicAnalysis`
(`HarmonicAnalysis.beurlingPowNorm_one_le_of_forall_hasCompactSupport`):
* the dense class `C_c^∞`: for `g ∈ C_c^∞`, its Cauchy transform
  `f (z) = (1/π) ∫ g (w) / (z − w) dw` has `∂_zbar f = g` (the Cauchy–Pompeiu formula), `∂f = 𝒮 g`
  (Liouville's theorem for `∂f − 𝒮 g`), `f = O (1/|z|)` and `∂f = O (1/|z|²)`;
* the inequality is applied to `η_R f`, with Guerra's cut-offs `η_R`, and `R → ∞`;
* density carries the bound to every Schwartz `g`.

The one departure from Guerra's text is forced: Guerra treats Hessians of real functions, with the
logarithmic potential, while the norm on complex `L^p` needs the gradient case, with the Cauchy
transform. Guerra's "by density" presupposes the boundedness of `𝒮` on `L^p`, which the package
does not prove; its density step uses the convergence of the Fourier transforms in `L¹` and
Fatou's lemma instead. Here the integral inequality is turned into the inequality of `L^p` norms
that the package's statement takes.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace External.BaernsteinMontgomerySmith

/-- `∂f` is continuous for a `C¹` function `f`. -/
theorem continuous_dz_of_contDiff {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) :
    Continuous (HarmonicAnalysis.dz f) := by
  have h := hf.continuous_fderiv one_ne_zero
  unfold HarmonicAnalysis.dz
  fun_prop

/-- `∂_zbar f` is continuous for a `C¹` function `f`. -/
theorem continuous_dzbar_of_contDiff {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) :
    Continuous (HarmonicAnalysis.dzbar f) := by
  have h := hf.continuous_fderiv one_ne_zero
  unfold HarmonicAnalysis.dzbar
  fun_prop

/-- `∂f` has compact support if `f` has. -/
theorem hasCompactSupport_dz {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (HarmonicAnalysis.dz f) :=
  HasCompactSupport.intro (hf.fderiv ℝ) fun z hz => by
    simp [HarmonicAnalysis.dz, image_eq_zero_of_notMem_tsupport hz]

/-- `∂_zbar f` has compact support if `f` has. -/
theorem hasCompactSupport_dzbar {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (HarmonicAnalysis.dzbar f) :=
  HasCompactSupport.intro (hf.fderiv ℝ) fun z hz => by
    simp [HarmonicAnalysis.dzbar, image_eq_zero_of_notMem_tsupport hz]

/-- The integral inequality `∫ |∂f|^p ≤ C^p ∫ |∂_zbar f|^p` as `‖∂f‖_p ≤ C ‖∂_zbar f‖_p`, for `f`
smooth
with compact support, `0 < p` and `0 ≤ C`. -/
theorem eLpNorm_dz_le_of_integral_le {p : ℝ} (hp : 0 < p) {C : ℝ} (hC : 0 ≤ C) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (h : ∫ z, ‖HarmonicAnalysis.dz f z‖ ^ p ≤ C ^ p * ∫ z, ‖HarmonicAnalysis.dzbar f z‖ ^ p) :
    eLpNorm (HarmonicAnalysis.dz f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal C * eLpNorm (HarmonicAnalysis.dzbar f) (ENNReal.ofReal p) volume := by
  have h0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  rw [((continuous_dz_of_contDiff hf1).memLp_of_hasCompactSupport
      (hasCompactSupport_dz hfc)).eLpNorm_eq_integral_rpow_norm h0 ENNReal.ofReal_ne_top,
    ((continuous_dzbar_of_contDiff hf1).memLp_of_hasCompactSupport
      (hasCompactSupport_dzbar hfc)).eLpNorm_eq_integral_rpow_norm h0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  have hI : 0 ≤ ∫ z, ‖HarmonicAnalysis.dzbar f z‖ ^ p := integral_nonneg fun z => by positivity
  calc (∫ z, ‖HarmonicAnalysis.dz f z‖ ^ p) ^ p⁻¹
      ≤ (C ^ p * ∫ z, ‖HarmonicAnalysis.dzbar f z‖ ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow (integral_nonneg fun z => by positivity) h (inv_nonneg.2 hp.le)
    _ = C * (∫ z, ‖HarmonicAnalysis.dzbar f z‖ ^ p) ^ p⁻¹ := by
        rw [Real.mul_rpow (by positivity) hI, Real.rpow_rpow_inv hC hp.ne']

/-- **Remark (b)** of Baernstein–Montgomery-Smith (§1), for the upper bound: if
`∫ |∂f|^p ≤ C^p ∫ |∂_zbar f|^p` for every smooth compactly supported `f : ℂ → ℂ`, then the norm of
the Beurling–Ahlfors transform on `L^p (ℂ)` is at most `C`, `1 < p < ∞`.

Proof: Guerra's passage to `L^p (ℂ)` (arXiv:2608.23388, proof of `cor:beurling-lp`), in the
gradient case, as formalized in the package `HarmonicAnalysis`
(`HarmonicAnalysis.beurlingPowNorm_one_le_of_forall_hasCompactSupport`; the module docstring
says how it follows Guerra's proof). -/
theorem remark_b {p : ℝ} (hp : 1 < p) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f : ℂ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∫ z, ‖HarmonicAnalysis.dz f z‖ ^ p ≤ C ^ p * ∫ z, ‖HarmonicAnalysis.dzbar f z‖ ^ p) :
    HarmonicAnalysis.beurlingPowNorm 1 p ≤ ENNReal.ofReal C :=
  HarmonicAnalysis.beurlingPowNorm_one_le_of_forall_hasCompactSupport hp fun f hf hfc =>
    eLpNorm_dz_le_of_integral_le (by linarith) hC hf hfc (h f hf hfc)

end External.BaernsteinMontgomerySmith
