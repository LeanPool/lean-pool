/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Corollary2.Norm
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.Beltrami

/-!
# Quasiregular extension of Astala's higher-integrability result

"Corollary 2 implies the sharp higher integrability of derivatives of quasiconformal maps in the
plane, originally obtained by complex-analytical methods in [Astala1994]."

Corollary 1.2 of K. Astala, *Area distortion of quasiconformal mappings*,
Acta Math. 173 (1994), 37–60, gives the sharp exponent for quasiconformal homeomorphisms.
Here `astala` extends the derivative-integrability conclusion to quasiregular maps by applying
Bojarski's criterion to the sharp Beurling–Ahlfors norm from Corollary 2 of Agazzi et al.

Let `Ω ⊆ ℂ` be open and `0 ≤ k < 1`. A map `f ∈ W^{1,2}_loc (Ω)` with `|∂_zbar f| ≤ k |∂f|` almost
everywhere in `Ω` is `K`-quasiregular, `K = (1 + k) / (1 − k)`; the `K`-quasiconformal maps are the
homeomorphic ones. With the weak partial derivatives `fx`, `fy` of `f`, `∂f = (fx − i fy) / 2` and
`∂_zbar f = (fx + i fy) / 2`, so the condition reads `|fx + i fy| ≤ k |fx − i fy|`.

* `astala`: `Df ∈ L^p_loc (Ω)`, that is `fx, fy ∈ L^p_loc (Ω)`, for every `p ≥ 2` with
  `k (p − 1) < 1`, that is `2 ≤ p < 1 + 1/k = 2K / (K − 1)` (every `p ≥ 2` if `k = 0`). This is the
  quasiregular extension of Astala's Corollary 1.2.
* `astala_sharp`: the exponent is sharp. For `K > 1`, the radial stretch `f (z) = z |z|^{1/K − 1}`
  is a homeomorphism of `ℂ` in `W^{1,2}_loc (ℂ)` with `|∂_zbar f| = k |∂f|` off `0`,
  `k = (K − 1) / (K + 1)`, so it is `K`-quasiconformal, while `∂_x f ∉ L^{2K/(K−1)}` on every disc
  around `0`; at `p = 2K / (K − 1)`, `k (p − 1) = 1`.

## Proof

`astala`: Corollary 2 (b) gives `‖𝒮‖_p = p* − 1 = p − 1` for `p ≥ 2` (`corollary2_norm`).
Since `k ‖𝒮‖_p = k (p − 1) < 1`, Bojarski's integrability criterion gives `Df ∈ L^p_loc (Ω)`
(`HarmonicAnalysis.memLpLoc_of_beltrami`: a cut-off `g = η f`, `∂g = 𝒮 ∂_zbar g`, and a Neumann
series for `∂_zbar g − μ 𝒮 ∂_zbar g = h` on `L^p`, compared with the `L²` solution). The weak
partial derivatives give the weak derivative `Df (z) v = v.re fx (z) + v.im fy (z)`.

`astala_sharp`: the radial stretch with exponent `α = 1/K`, in the package
(`HarmonicAnalysis.Complex.RadialStretch`): `∂f = ((1 + α)/2) |z|^{α − 1}`,
`|∂_zbar f| = ((1 − α)/2) |z|^{α − 1}`, `|∂_x f| ≥ α |z|^{α − 1}`, and `∫_{|z| < r} |z|^{−2} = ∞`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Agazzi

/-- The real-linear map `v ↦ v.re a + v.im b`, the derivative with the partial derivatives `a`
and `b`. -/
private def partialsCLM (a b : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight a + Complex.imCLM.smulRight b

private theorem partialsCLM_apply (a b v : ℂ) : partialsCLM a b v = v.re • a + v.im • b := by
  simp [partialsCLM]

private theorem continuous_partialsCLM :
    Continuous fun q : ℂ × ℂ => partialsCLM q.1 q.2 :=
  ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM).continuous.comp continuous_fst).add
    ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM).continuous.comp continuous_snd)

private theorem norm_partialsCLM_le (a b : ℂ) : ‖partialsCLM a b‖ ≤ ‖a‖ + ‖b‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [partialsCLM_apply]
  calc ‖v.re • a + v.im • b‖ ≤ |v.re| * ‖a‖ + |v.im| * ‖b‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖v‖ * ‖a‖ + ‖v‖ * ‖b‖ := by
        gcongr
        · exact Complex.abs_re_le_norm v
        · exact Complex.abs_im_le_norm v
    _ = (‖a‖ + ‖b‖) * ‖v‖ := by ring

private theorem dzPart_partialsCLM (a b : ℂ) :
    HarmonicAnalysis.dzPart (partialsCLM a b) = (2⁻¹ : ℂ) * (a - Complex.I * b) := by
  simp [HarmonicAnalysis.dzPart, partialsCLM_apply]

private theorem dzbarPart_partialsCLM (a b : ℂ) :
    HarmonicAnalysis.dzbarPart (partialsCLM a b) = (2⁻¹ : ℂ) * (a + Complex.I * b) := by
  simp [HarmonicAnalysis.dzbarPart, partialsCLM_apply]

/-- The weak partial derivatives `fx`, `fy` give the weak derivative
`Df (z) v = v.re fx (z) + v.im fy (z)` (`∂_v φ = v.re ∂_x φ + v.im ∂_y φ`). -/
private theorem hasWeakFDerivOn_partialsCLM {Ω : Set ℂ} (hΩ : IsOpen Ω) {f fx fy : ℂ → ℂ}
    (hf : MemW12Loc Ω f fx fy) :
    HarmonicAnalysis.HasWeakFDerivOn Ω f fun z => partialsCLM (fx z) (fy z) := by
  obtain ⟨hf2, hfx2, hfy2, hx, hy⟩ := hf
  have hloc : ∀ g : ℂ → ℂ, MemLpLoc g 2 Ω → LocallyIntegrableOn g Ω volume := fun g hg =>
    HarmonicAnalysis.MemLpLoc.locallyIntegrableOn hΩ (by norm_num) hg
  intro v φ hφ hφc hφΩ
  have hint : ∀ w : ℂ, Integrable fun z => fderiv ℝ φ z w • f z := fun w =>
    HarmonicAnalysis.sob_integrable_smul_of_tsupport_subset (hloc f hf2)
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hφc.fderiv_apply (𝕜 := ℝ) w)
      ((tsupport_fderiv_apply_subset ℝ w).trans hφΩ)
  have hint' : ∀ g : ℂ → ℂ, MemLpLoc g 2 Ω → Integrable fun z => φ z • g z := fun g hg =>
    HarmonicAnalysis.sob_integrable_smul_of_tsupport_subset (hloc g hg) hφ.continuous hφc hφΩ
  have hv : ∀ z, fderiv ℝ φ z v =
      v.re * fderiv ℝ φ z 1 + v.im * fderiv ℝ φ z Complex.I := by
    intro z
    have : v = v.re • (1 : ℂ) + v.im • Complex.I := by
      simp [Complex.real_smul, Complex.re_add_im]
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hφx := hx φ hφ hφc hφΩ
  have hφy := hy φ hφ hφc hφΩ
  calc ∫ z, fderiv ℝ φ z v • f z
      = ∫ z, (v.re • (fderiv ℝ φ z 1 • f z) + v.im • (fderiv ℝ φ z Complex.I • f z)) := by
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        simp only [hv, add_smul, mul_smul]
    _ = v.re • (∫ z, fderiv ℝ φ z 1 • f z) + v.im • ∫ z, fderiv ℝ φ z Complex.I • f z := by
        have h := integral_add ((hint 1).smul v.re) ((hint Complex.I).smul v.im)
        simp only [Pi.smul_apply] at h
        rw [h, integral_smul, integral_smul]
    _ = -(v.re • (∫ z, φ z • fx z) + v.im • ∫ z, φ z • fy z) := by
        rw [hφx, hφy, smul_neg, smul_neg, neg_add]
    _ = -∫ z, φ z • partialsCLM (fx z) (fy z) v := by
        have h := integral_add ((hint' fx hfx2).smul v.re) ((hint' fy hfy2).smul v.im)
        simp only [Pi.smul_apply] at h
        rw [← integral_smul, ← integral_smul, ← h]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        simp only [partialsCLM_apply, smul_add, smul_comm (φ z)]

/-- The partial derivatives are in `L^p_loc` with the derivative they define. -/
private theorem memLpLoc_partialsCLM {Ω : Set ℂ} {fx fy : ℂ → ℂ} {p : ℝ≥0∞}
    (hx : MemLpLoc fx p Ω) (hy : MemLpLoc fy p Ω) :
    HarmonicAnalysis.MemLpLoc (fun z => partialsCLM (fx z) (fy z)) p Ω := by
  intro K hKΩ hK
  have hxK := hx K hKΩ hK
  have hyK := hy K hKΩ hK
  refine (hxK.norm.add hyK.norm).of_le
    (continuous_partialsCLM.comp_aestronglyMeasurable
      (hxK.aestronglyMeasurable.prodMk hyK.aestronglyMeasurable)) (ae_of_all _ fun z => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs]
  exact (norm_partialsCLM_le _ _).trans (le_abs_self _)

/-- A derivative in `L^p_loc` has its partial derivatives in `L^p_loc`. -/
private theorem memLpLoc_apply {Ω : Set ℂ} {Df : ℂ → ℂ →L[ℝ] ℂ} {p : ℝ≥0∞}
    (h : HarmonicAnalysis.MemLpLoc Df p Ω) (v : ℂ) : MemLpLoc (fun z => Df z v) p Ω :=
  fun K hKΩ hK => (ContinuousLinearMap.apply ℝ ℂ v).comp_memLp' (h K hKΩ hK)

/-- **Quasiregular extension of Astala's Corollary 1.2** (Acta Math. 173 (1994)):
let `Ω ⊆ ℂ` be open, `0 ≤ k < 1`, and `f ∈ W^{1,2}_loc (Ω)` with the weak partial derivatives
`fx`, `fy` and `|∂_zbar f| ≤ k |∂f|` almost everywhere in `Ω` (`∂_zbar f = (fx + i fy)/2`,
`∂f = (fx − i fy)/2`: `f` is `K`-quasiregular, `K = (1 + k)/(1 − k)`). Then `Df ∈ L^p_loc (Ω)` for
every `p ≥ 2` with `k (p − 1) < 1`, that is `2 ≤ p < 1 + 1/k = 2K/(K − 1)`.

Proof: apply Bojarski's criterion with `‖𝒮‖_p = p − 1` from Corollary 2 (b). -/
theorem astala {Ω : Set ℂ} (hΩ : IsOpen Ω) {k p : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hp : 2 ≤ p)
    (hpk : k * (p - 1) < 1) {f fx fy : ℂ → ℂ} (hf : MemW12Loc Ω f fx fy)
    (hbel : ∀ᵐ z ∂(volume.restrict Ω),
      ‖fx z + Complex.I * fy z‖ ≤ k * ‖fx z - Complex.I * fy z‖) :
    MemLpLoc fx (ENNReal.ofReal p) Ω ∧ MemLpLoc fy (ENNReal.ofReal p) Ω := by
  have hS : HarmonicAnalysis.beurlingPowNorm 1 p = ENNReal.ofReal (p - 1) := by
    rw [← beurlingNorm_eq_beurlingPowNorm, corollary2_norm (by linarith),
      pStar_sub_one_of_two_le hp]
  have hbel' : ∀ᵐ z ∂(volume.restrict Ω),
      ‖HarmonicAnalysis.dzbarPart (partialsCLM (fx z) (fy z))‖ ≤
        k * ‖HarmonicAnalysis.dzPart (partialsCLM (fx z) (fy z))‖ := by
    filter_upwards [hbel] with z hz
    rw [dzbarPart_partialsCLM, dzPart_partialsCLM, norm_mul, norm_mul, ← mul_assoc,
      mul_comm k, mul_assoc]
    exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)
  have h := HarmonicAnalysis.memLpLoc_of_beltrami hΩ hk hk1 hp
    (by rw [hS]; exact ENNReal.ofReal_ne_top)
    (by rw [hS, ENNReal.toReal_ofReal (by linarith)]; exact hpk) hf.1
    (memLpLoc_partialsCLM hf.2.1 hf.2.2.1) (hasWeakFDerivOn_partialsCLM hΩ hf) hbel'
  refine ⟨?_, ?_⟩
  · simpa [partialsCLM_apply] using memLpLoc_apply h 1
  · simpa [partialsCLM_apply] using memLpLoc_apply h Complex.I

/-- A continuous function is in `L^p_loc (ℂ)`. -/
private theorem memLpLoc_of_continuous {g : ℂ → ℂ} (hg : Continuous g) (p : ℝ≥0∞) :
    MemLpLoc g p Set.univ := by
  intro K _ hK
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable M
    (ae_restrict_of_forall_mem hK.measurableSet hM)

/-- `A 1 + i A i = 2 ∂_zbar A` and `A 1 − i A i = 2 ∂A`. -/
private theorem norm_apply_add_I_mul (A : ℂ →L[ℝ] ℂ) :
    ‖A 1 + Complex.I * A Complex.I‖ = 2 * ‖HarmonicAnalysis.dzbarPart A‖ := by
  simp only [HarmonicAnalysis.dzbarPart, norm_mul, norm_inv, Complex.norm_ofNat]
  field_simp

private theorem norm_apply_sub_I_mul (A : ℂ →L[ℝ] ℂ) :
    ‖A 1 - Complex.I * A Complex.I‖ = 2 * ‖HarmonicAnalysis.dzPart A‖ := by
  simp only [HarmonicAnalysis.dzPart, norm_mul, norm_inv, Complex.norm_ofNat]
  field_simp

/-- **Sharpness of Astala's theorem** (TeX line 325): for `K > 1`, the radial stretch
`f (z) = z |z|^{1/K − 1}` is `K`-quasiconformal: a homeomorphism of `ℂ`, in `W^{1,2}_loc (ℂ)`
with the weak partial derivatives `fx = ∂_x f`, `fy = ∂_y f` (its pointwise ones), and
`|∂_zbar f| = k |∂f|` off `0` (`|fx + i fy| = k |fx − i fy|`), `k = (K − 1)/(K + 1)`. For
`p = 2K/(K − 1)`, `k (p − 1) = 1`, and `fx ∉ L^p` on every disc around `0`: the condition
`k (p − 1) < 1` of `astala` cannot be relaxed.

Proof: the radial stretch with exponent `1/K` in the package `HarmonicAnalysis`
(`HarmonicAnalysis.Complex.RadialStretch`). -/
theorem astala_sharp {K : ℝ} (hK : 1 < K) :
    (∃ e : ℂ ≃ₜ ℂ, ⇑e = radialStretch K⁻¹) ∧
    MemW12Loc Set.univ (radialStretch K⁻¹) (fun z => fderiv ℝ (radialStretch K⁻¹) z 1)
      (fun z => fderiv ℝ (radialStretch K⁻¹) z Complex.I) ∧
    (∀ z, z ≠ 0 →
      ‖fderiv ℝ (radialStretch K⁻¹) z 1 + Complex.I * fderiv ℝ (radialStretch K⁻¹) z Complex.I‖ =
        (K - 1) / (K + 1) * ‖fderiv ℝ (radialStretch K⁻¹) z 1 -
          Complex.I * fderiv ℝ (radialStretch K⁻¹) z Complex.I‖) ∧
    (K - 1) / (K + 1) * (2 * K / (K - 1) - 1) = 1 ∧
    ∀ r, 0 < r → ¬ MemLp (fun z => fderiv ℝ (radialStretch K⁻¹) z 1)
      (ENNReal.ofReal (2 * K / (K - 1))) (volume.restrict (Metric.ball 0 r)) := by
  have hK0 : 0 < K := by linarith
  have hα : 0 < K⁻¹ := inv_pos.2 hK0
  have hα1 : K⁻¹ < 1 := inv_lt_one_of_one_lt₀ hK
  have hw := HarmonicAnalysis.hasWeakFDerivOn_radialStretch hα hα1.le
  have hD := HarmonicAnalysis.memLpLoc_fderiv_radialStretch hα hα1.le
  refine ⟨HarmonicAnalysis.exists_homeomorph_radialStretch hα,
    ⟨memLpLoc_of_continuous (HarmonicAnalysis.continuous_radialStretch hα) 2,
      memLpLoc_apply hD 1, memLpLoc_apply hD Complex.I, hw 1, hw Complex.I⟩,
    fun z hz => ?_, ?_, fun r hr => ?_⟩
  · rw [norm_apply_add_I_mul, norm_apply_sub_I_mul, radialStretch_eq,
      HarmonicAnalysis.norm_dzbarPart_fderiv_radialStretch hα hα1.le hz]
    have : (1 - K⁻¹) / (1 + K⁻¹) = (K - 1) / (K + 1) := by
      field_simp
    rw [this]
    ring
  · have : K - 1 ≠ 0 := by linarith
    have : K + 1 ≠ 0 := by linarith
    field_simp
    ring
  · have h := HarmonicAnalysis.not_memLp_fderiv_radialStretch_apply_one hα hα1 hr
    have : 2 / (1 - K⁻¹) = 2 * K / (K - 1) := by
      have : K - 1 ≠ 0 := by linarith
      field_simp
    rwa [this] at h

end Agazzi
