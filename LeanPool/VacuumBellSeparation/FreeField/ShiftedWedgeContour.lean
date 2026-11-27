/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroWedgeContour
public import LeanPool.VacuumBellSeparation.FreeField.ShiftedWedgeModularPowers

/-!
# The translated wedge contour with the manuscript's exact damping

The source translated by -ell e1 has complex Fourier factor exp(i ell z1).
On the actual imaginary boost its squared modulus is
exp(-2 ell omega sin(2 pi c)). The outer physical translation is unitary.
Every graph and norm below refers to the original source and maximal power.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped InnerProductSpace

theorem spatialDot_edge (z : Fin 3 → ℂ) (ℓ : ℝ) :
    spatialDot z (fun i => ((ℓ • e₁) i : ℂ)) = (ℓ : ℂ) * z 0 := by
  simp [spatialDot_eq, e₁, mul_comm]

theorem complexShellBoost_first_im (m θ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    ((complexShellBoost m ((θ : ℂ) * Complex.I) p).2 0).im =
      dispersion m p * Real.sin θ := by
  simp [complexShellBoost, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.mul_im]

theorem norm_complexTranslation_edge (m ℓ θ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    ‖Complex.exp (-(Complex.I * spatialDot
      (complexShellBoost m ((θ : ℂ) * Complex.I) p).2
      (fun i => ((-(ℓ • e₁)) i : ℂ))))‖ =
      Real.exp (-ℓ * dispersion m p * Real.sin θ) := by
  rw [← neg_smul, spatialDot_edge, Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_sub, neg_neg, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, Complex.neg_im, Complex.ofReal_neg, neg_zero, add_zero,
    complexShellBoost_first_im]
  ring

theorem complexSourceWave_translate_edge_norm_sq (m ℓ θ : ℝ)
    (u : TimeZeroSource) (p : EuclideanSpace ℝ (Fin 3)) :
    ‖complexSourceWave (timeZeroTranslate (-(ℓ • e₁)) u)
      (complexShellBoost m ((θ : ℂ) * Complex.I) p)‖ ^ 2 =
      Real.exp (-2 * ℓ * dispersion m p * Real.sin θ) *
        ‖complexSourceWave u (complexShellBoost m ((θ : ℂ) * Complex.I) p)‖ ^ 2 := by
  rw [complexSourceWave_translate, norm_mul, mul_pow, norm_complexTranslation_edge,
    pow_two, ← Real.exp_add]
  congr 2
  ring

/-- Equation wedge-contour for literal compact Cauchy data, including full
maximal-domain membership, at every translated left wedge. -/
theorem timeZero_shiftedWedge_contour_norm {m : ℝ} (hm : 0 < m) (ℓ : ℝ)
    (u : TimeZeroSource)
    (hf : tsupport u.1.1 ⊆ leftWedgeTimeZero ℓ)
    (hg : tsupport u.2.1 ⊆ leftWedgeTimeZero ℓ)
    {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) :
    ∃ χ : Lp ℂ 2 (oneParticleMeasure m),
      (timeZeroL2 hm u, χ) ∈ (shiftedWedgeExponential hm ℓ c).graph ∧
      ‖χ‖ ^ 2 = ∫ p, Real.exp (-2 * ℓ * dispersion m p * Real.sin (2 * Real.pi * c)) *
        ‖complexSourceWave u
          (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p)‖ ^ 2
        ∂oneParticleMeasure m := by
  let v := timeZeroTranslate (-(ℓ • e₁)) u
  have hvf : tsupport v.1.1 ⊆ leftWedgeTimeZero 0 :=
    spatialTestTranslate_support_subset (leftWedgeTimeZero_sub_edge ℓ) u.1 hf
  have hvg : tsupport v.2.1 ⊆ leftWedgeTimeZero 0 :=
    spatialTestTranslate_support_subset (leftWedgeTimeZero_sub_edge ℓ) u.2 hg
  obtain ⟨ψ, hψ, _, hnorm⟩ := timeZero_wedgePower_contour_norm hm v hvf hvg hc hc2
  refine ⟨oneParticleSpatialTranslation m (ℓ • e₁) ψ, ?_, ?_⟩
  · rw [shiftedWedgeExponential, unitaryPartialTransport_mem_graph,
      LinearIsometryEquiv.symm_apply_apply, oneParticleSpatialTranslation_symm,
      ← timeZeroL2_translate]
    exact hψ
  · rw [LinearIsometryEquiv.norm_map, hnorm]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p =>
      complexSourceWave_translate_edge_norm_sq m ℓ (2 * Real.pi * c) u p)

/-- The literal damped contour estimate for sources in any contained region. -/
theorem shifted_complexSourceWave_contour_le_sourceWeight {m : ℝ} (hm : 0 < m) (ℓ : ℝ)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : U ⊆ leftWedgeTimeZero ℓ)
    (u : SourceTestSpace hm U) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    (∫ p, Real.exp (-2 * ℓ * dispersion m p * Real.sin (2 * Real.pi * c)) *
      ‖complexSourceWave u.1
        (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p)‖ ^ 2
      ∂oneParticleMeasure m) ≤
      ‖sourceModularWeight hm U c
        (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U))‖ ^ 2 := by
  obtain ⟨χ, hχ, hnorm⟩ := timeZero_shiftedWedge_contour_norm hm ℓ u.1
    (u.2.1.trans hU) (u.2.2.trans hU) hc.le hc2
  obtain ⟨ψ, hψ, hbound⟩ := shiftedWedgeExponential_containing_wedge hm ℓ hU hc hc2
    (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U))
  rw [complexSourceMap_ofReal_test] at hψ
  have he := (shiftedWedgeExponential hm ℓ c).mem_graph_snd_inj hχ hψ rfl
  rw [← hnorm, he]
  exact pow_le_pow_left₀ (norm_nonneg _) hbound 2

end VacuumBellSeparation
