/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Complex.CauchyTransform
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.Basic
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.Regularity
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Complex.CauchyPompeiu
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Complex.Liouville
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Complex.WirtingerRadial

/-!
# The Cauchy transform of `g ∈ C_c^∞`: `∂_zbar (C g) = g` and `∂ (C g) = 𝓑 g`

For a smooth compactly supported `g : ℂ → ℂ`, its Cauchy transform
`f = C g`, `f (z) = (1/π) ∫ g (w) / (z − w) dw` (`HarmonicAnalysis.cauchyTransform`), is the
potential of the gradient case of Guerra's argument (A. Guerra, *Quasiconvexity of the Burkholder
function on symmetric matrices*, preprint, arXiv:2608.23388, 2026, §6, proofs of Corollaries 1.2
and 1.4, where the potential of a real `h` is its logarithmic potential `u`, with `Δu = 2h`,
`Du = O (|x|^{−1})` and `D²u = O (|x|^{−2})`, all stated there without proof). Here:

* `HarmonicAnalysis.dzbar_cauchyTransform_eq`: `∂_zbar f = g`, by the Cauchy–Pompeiu formula
  (`HarmonicAnalysis.cauchyTransform_dzbar`), the analogue of `Δu = 2h`;
* `HarmonicAnalysis.dz_cauchyTransform_eq_beurlingPow_one`: `∂f = 𝓑 g`, the analogue of Guerra's
  `𝒮 h = 𝒮 (½ Δu) = 2 𝒮 (u_{z (conj z)}) = 2 u_{zz}`, which applies `𝒮 ∘ ∂_zbar = ∂_z` to `u_z`.
  Here
  `𝓑 (∂_zbar φ) = ∂φ` is known for Schwartz functions `φ`
  (`HarmonicAnalysis.beurlingPow_dzbarCLM_pow`),
  and `f` is not one. The identity is proved through Liouville's theorem:
  `∂f − 𝓑 g = C (∂g) − 𝓑 g` has `∂_zbar (C (∂g)) = C (∂_zbar∂g) = ∂g` (Cauchy–Pompeiu for `∂g`) and
  `∂_zbar (𝓑 g) = ∂g` (`HarmonicAnalysis.dzbar_beurlingPow_one`), so it is entire
  (`HarmonicAnalysis.differentiable_complex_of_dzbar_eq_zero`); it tends to `0` at infinity
  (`C (∂g) = O (1/|z|²)` since `∫ ∂g = 0`, and the Riemann–Lebesgue lemma for `𝓑 g`), so it
  vanishes (`HarmonicAnalysis.eq_zero_of_dzbar_eq_zero`);
* the decay: `f = O (1/|z|)` (`HarmonicAnalysis.exists_norm_cauchyTransform_le`) and
  `∂f = C (∂g) = O (1/|z|²)`, so that `∂f ∈ L^p` for every `1 < p`
  (`HarmonicAnalysis.memLp_dz_cauchyTransform`), the analogues of Guerra's `Du = O (|x|^{−1})`,
  `D²u = O (|x|^{−2})`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff

namespace HarmonicAnalysis

variable {g : ℂ → ℂ}

/-- `∂g` is smooth for a smooth `g`. -/
theorem contDiff_dz (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (dz g) := by
  have h : ContDiff ℝ ∞ (fderiv ℝ g) := (contDiff_infty_iff_fderiv.1 hg).2
  have h1 : ContDiff ℝ ∞ fun z => fderiv ℝ g z 1 := h.clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ fun z => fderiv ℝ g z Complex.I := h.clm_apply contDiff_const
  exact (h1.sub (h2.const_smul Complex.I)).const_smul (2⁻¹ : ℂ)

/-- `∂g` has compact support if `g` has. -/
theorem hasCompactSupport_dz (hgc : HasCompactSupport g) : HasCompactSupport (dz g) :=
  HasCompactSupport.intro (hgc.fderiv ℝ) fun z hz => by
    simp [dz, image_eq_zero_of_notMem_tsupport hz]

/-- `∂_zbar (C g) = g` for `g ∈ C_c^∞`: `∂_zbar (C g) = C (∂_zbar g)` and the Cauchy–Pompeiu
formula. -/
theorem dzbar_cauchyTransform_eq (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    dzbar (cauchyTransform g) = g := by
  rw [dzbar_cauchyTransform hg hgc]
  exact funext (cauchyTransform_dzbar (hg.of_le (by simp)) hgc)

/-- `∂ (C g) = 𝓑 g` for `g ∈ C_c^∞`: `∂ (C g) − 𝓑 g = C (∂g) − 𝓑 g` is entire, since its `∂_zbar` is
`∂g − ∂g = 0`, and tends to `0` at infinity, so it vanishes by Liouville's theorem. -/
theorem dz_cauchyTransform_eq_beurlingPow_one (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) : dz (cauchyTransform g) = beurlingPow 1 g := by
  set G : 𝓢(ℂ, ℂ) := hgc.toSchwartzMap hg
  have hG : (G : ℂ → ℂ) = g := rfl
  have hdg := contDiff_dz hg
  have hdgc := hasCompactSupport_dz hgc
  rw [dz_cauchyTransform hg hgc]
  have hd1 : Differentiable ℝ (cauchyTransform (dz g)) :=
    (contDiff_cauchyTransform hdg hdgc).differentiable (by simp)
  have hd2 : Differentiable ℝ (beurlingPow 1 g) := by
    rw [← hG]
    exact differentiable_beurlingPow_one G
  have hbar : ∀ w, dzbar (fun z => cauchyTransform (dz g) z - beurlingPow 1 g z) w = 0 := by
    intro w
    rw [dzbar_sub (hd1 w) (hd2 w), congrFun (dzbar_cauchyTransform hdg hdgc) w,
      cauchyTransform_dzbar (hdg.of_le (by simp)) hdgc w, ← hG, dzbar_beurlingPow_one G w,
      sub_self]
  have hlim : Tendsto (fun z => cauchyTransform (dz g) z - beurlingPow 1 g z) (cocompact ℂ)
      (𝓝 0) := by
    have h1 := tendsto_cauchyTransform_cocompact hdg.continuous hdgc
    have h2 : Tendsto (beurlingPow 1 g) (cocompact ℂ) (𝓝 0) := by
      rw [← hG]
      exact tendsto_beurlingPow_one_cocompact G
    simpa using h1.sub h2
  funext z
  exact sub_eq_zero.1 (eq_zero_of_dzbar_eq_zero (hd1.sub hd2) hbar hlim z)

/-- `∂ (C g) ∈ L^p` for `g ∈ C_c^∞` and `1 < p`: `∂ (C g) = C (∂g)` is continuous and
`O (1/|z|²)` at infinity, since `∫ ∂g = 0`. -/
theorem memLp_dz_cauchyTransform (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) {p : ℝ}
    (hp : 1 < p) : MemLp (dz (cauchyTransform g)) (ENNReal.ofReal p) volume := by
  rw [dz_cauchyTransform hg hgc]
  obtain ⟨A, R, hR, h⟩ := exists_norm_cauchyTransform_le_of_integral_eq_zero
    (contDiff_dz hg).continuous (hasCompactSupport_dz hgc)
    (integral_dz_eq_zero (hg.of_le (by simp)) hgc)
  exact memLp_of_norm_le_div_sq
    (continuous_cauchyTransform (contDiff_dz hg).continuous (hasCompactSupport_dz hgc)) hR h hp

end HarmonicAnalysis
