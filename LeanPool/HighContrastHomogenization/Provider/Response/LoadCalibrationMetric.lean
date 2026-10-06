/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationSchur

/-!
# High-contrast homogenization: Provider.Response.LoadCalibrationMetric

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The calibrated canonical sandwich

The first two boxed displays of the response-load calibration:

    β⁻¹ 𝐌₀ ≤ 𝐆₀ᵗ M(E_t) 𝐆₀ ≤ β 𝐌₀,      κ_t ≤ ϱ^d κ_s,   κ_s ≤ ϱ^{2d} κ_t,

together with the two canonical-balance chains the later displays consume,

    β⁻¹ 𝐌₀ ≤ Ê_t ≤ β√κ_t 𝐌₀,            Ê_s ≤ c_ε √κ_s 𝐌₀.

Here `E⁰, E_s, E_t` are positive doubled blocks with `E_t ≤ E_s`,
`E_s^♯ ≤ E_s`, `E_t^♯ ≤ E_t`, and `(1-ε_cal)E⁰ ≤ E_s ≤ (1+ε_cal)E⁰`;
`c_ε = ((1+ε_cal)/(1-ε_cal))^{1/2}`, `ϱ = (det E_s/det E_t)^{1/d}`,
`β = c_ε ϱ^{d/2}`, and `𝐆₀ = G_{g(E⁰)}`, `𝐌₀ = diag(m(E⁰), m(E⁰)⁻¹)`.

The proof is the printed one.  Sharp order reversal turns the near-isometry
hypothesis into a comparison of sharps; joint monotonicity and homogeneity of
the metric geometric mean turn that into
`c_ε⁻¹ M(E⁰) ≤ M(E_s) ≤ c_ε M(E⁰)`, the comparison of the canonical metrics of
two near-isometric blocks.  The determinant-loss comparison
`e.global.selection.metric.loss` at the ordered pair `(E_s, E_t)` supplies
`ϱ^{-d/2} M(E_t) ≤ M(E_s) ≤ ϱ^{d/2} M(E_t)` and the two imbalance clauses.
Composing gives the sandwich around `M(E⁰)`, and congruence by `𝐆₀` moves it
onto `𝐌₀`, because `M(E⁰) = G_{-g₀}ᵗ 𝐌₀ G_{-g₀}` and `G_{-g₀}G_{g₀} = I`.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## Scalar dilation helpers -/

/-- Cancel a positive dilation on the left of a Loewner bound. -/
theorem le_of_smul_inv_le {n : Type*} [Fintype n] {c : ℝ} (hc : 0 < c)
    {A B : Matrix n n ℝ} (h : c⁻¹ • A ≤ B) : A ≤ c • B := by
  have := smul_le_smul_of_le hc.le h
  rwa [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] at this

/-! ## The near-isometric mean comparison -/

variable {E0 Es Et : FullBlockMat d}

/-- **The near-isometric mean comparison** of the canonical metrics:
`c_ε⁻¹ M(E⁰) ≤ M(E_s) ≤ c_ε M(E⁰)` with `c_ε = ((1+ζ)/(1-ζ))^{1/2}`.  This is
the internal step of `e.global.selection.metric.comparison`, which reports only the
imbalance and projective consequences. -/
theorem canonBlock_near_isometry (hE0 : E0.PosDef) (hEs : Es.PosDef) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) (hlow : (1 - z) • E0 ≤ Es) (hhigh : Es ≤ (1 + z) • E0) :
    (Real.sqrt ((1 + z) / (1 - z)))⁻¹ • canonBlock E0 ≤ canonBlock Es ∧
      canonBlock Es ≤ Real.sqrt ((1 + z) / (1 - z)) • canonBlock E0 := by
  have hm : (0 : ℝ) < 1 - z := by linarith only [hz1]
  have hp : (0 : ℝ) < 1 + z := by linarith only [hz0]
  have hSE : (fullBlockSharp E0).PosDef := posDef_fullBlockSharp hE0
  have hSF : (fullBlockSharp Es).PosDef := posDef_fullBlockSharp hEs
  have hsharpUp : fullBlockSharp Es ≤ (1 - z)⁻¹ • fullBlockSharp E0 := by
    have h := fullBlockSharp_le_fullBlockSharp (posDef_smul hE0 hm) hEs hlow
    rwa [fullBlockSharp_smul hE0 hm] at h
  have hsharpLow : (1 + z)⁻¹ • fullBlockSharp E0 ≤ fullBlockSharp Es := by
    have h := fullBlockSharp_le_fullBlockSharp hEs (posDef_smul hE0 hp) hhigh
    rwa [fullBlockSharp_smul hE0 hp] at h
  constructor
  · have hmono := matGeomMean_mono (posDef_smul hE0 hm) hEs
      (posDef_smul hSE (inv_pos.mpr hp)) hSF hlow hsharpLow
    rw [matGeomMean_smul hE0 hSE hm (inv_pos.mpr hp)] at hmono
    have hrw : (1 - z) * (1 + z)⁻¹ = ((1 + z) / (1 - z))⁻¹ := by
      field_simp
    rwa [hrw, Real.sqrt_inv] at hmono
  · have hmono := matGeomMean_mono hEs (posDef_smul hE0 hp) hSF
      (posDef_smul hSE (inv_pos.mpr hm)) hhigh hsharpUp
    rwa [matGeomMean_smul hE0 hSE hp (inv_pos.mpr hm), ← div_eq_mul_inv] at hmono

/-! ## Congruence by the canonical shear -/

/-- **The canonical block is `𝐌₀` after congruence by `𝐆₀`.**  The canonical
factorization reads `M(E⁰) = G_{-g₀}ᵗ 𝐌₀ G_{-g₀}`, and shears compose
additively, so conjugating by `G_{g₀}` cancels the shear exactly. -/
theorem shear_conj_canonBlock (hE0 : E0.PosDef) :
    (fullBlockShear (canonShear E0))ᴴ * canonBlock E0 * fullBlockShear (canonShear E0) =
      Matrix.fromBlocks (canonMetric E0) 0 0 (canonMetric E0)⁻¹ := by
  obtain ⟨-, -, hfac⟩ := canonFactor_spec hE0
  rw [hfac, schurBlock_conj_shear, sub_self, schurBlock_zero]

/-! ## The calibrated sandwich -/

/-- **The calibrated sandwich around `M(E⁰)`.**  Composing the near-isometric
mean comparison with the determinant-loss mean comparison gives
`β⁻¹ M(E⁰) ≤ M(E_t) ≤ β M(E⁰)` with `β = c_ε ϱ^{d/2}`. -/
theorem canonBlock_sandwich (hd : 2 ≤ d) (hE0 : E0.PosDef) (hEs : Es.PosDef)
    (hEt : Et.PosDef) (hts : Et ≤ Es) {z ceps rho beta : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hlow : (1 - z) • E0 ≤ Es) (hhigh : Es ≤ (1 + z) • E0)
    (hceps : ceps = Real.sqrt ((1 + z) / (1 - z))) (hrho : rho = canonDetRatio Es Et)
    (hbeta : beta = ceps * Real.sqrt (rho ^ d)) :
    beta⁻¹ • canonBlock E0 ≤ canonBlock Et ∧ canonBlock Et ≤ beta • canonBlock E0 := by
  have hm : (0 : ℝ) < 1 - z := by linarith only [hz1]
  have hp : (0 : ℝ) < 1 + z := by linarith only [hz0]
  have hcpos : 0 < ceps := by rw [hceps]; exact Real.sqrt_pos.mpr (div_pos hp hm)
  have hdet : (0 : ℝ) < Es.det / Et.det := div_pos hEs.det_pos hEt.det_pos
  have hrpow : rho ^ d = Es.det / Et.det := by
    rw [hrho]
    exact canonDetRatio_pow (by omega) hdet.le
  have hspos : 0 < Real.sqrt (rho ^ d) := by rw [hrpow]; exact Real.sqrt_pos.mpr hdet
  obtain ⟨hnearLow, hnearUp⟩ :=
    canonBlock_near_isometry hE0 hEs hz0 hz1 hlow hhigh
  rw [← hceps] at hnearLow hnearUp
  obtain ⟨-, -, ⟨hdetLow, hdetUp⟩, -, -⟩ :=
    canonDeterminantLoss hd hEs hEt hts (r := rho)
      (by rw [hrho]; exact canonDetRatio_nonneg hdet.le) hrpow
  constructor
  · -- `ceps⁻¹ M(E⁰) ≤ M(E_s) ≤ ϱ^{d/2} M(E_t)`
    have hchain : ceps⁻¹ • canonBlock E0 ≤ Real.sqrt (rho ^ d) • canonBlock Et :=
      hnearLow.trans hdetUp
    have h := smul_le_smul_of_le (inv_nonneg.mpr hspos.le) hchain
    rw [smul_smul, smul_smul, inv_mul_cancel₀ hspos.ne', one_smul] at h
    have hrw : (Real.sqrt (rho ^ d))⁻¹ * ceps⁻¹ = beta⁻¹ := by
      rw [hbeta, mul_inv]
      ring
    rwa [hrw] at h
  · -- `ϱ^{-d/2} M(E_t) ≤ M(E_s) ≤ ceps M(E⁰)`
    have hchain : (Real.sqrt (rho ^ d))⁻¹ • canonBlock Et ≤ ceps • canonBlock E0 :=
      hdetLow.trans hnearUp
    have h := smul_le_smul_of_le hspos.le hchain
    rw [smul_smul, smul_smul, mul_inv_cancel₀ hspos.ne', one_smul] at h
    have hrw : Real.sqrt (rho ^ d) * ceps = beta := by rw [hbeta]; ring
    rwa [hrw] at h

/-- **The first boxed display** of the response-load calibration:
`β⁻¹ 𝐌₀ ≤ 𝐆₀ᵗ M(E_t) 𝐆₀ ≤ β 𝐌₀`. -/
theorem metric_sandwich (hd : 2 ≤ d) (hE0 : E0.PosDef) (hEs : Es.PosDef)
    (hEt : Et.PosDef) (hts : Et ≤ Es) {z ceps rho beta : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hlow : (1 - z) • E0 ≤ Es) (hhigh : Es ≤ (1 + z) • E0)
    (hceps : ceps = Real.sqrt ((1 + z) / (1 - z))) (hrho : rho = canonDetRatio Es Et)
    (hbeta : beta = ceps * Real.sqrt (rho ^ d))
    {G0 M0 : FullBlockMat d} (hG0 : G0 = fullBlockShear (canonShear E0))
    (hM0 : M0 = Matrix.fromBlocks (canonMetric E0) 0 0 (canonMetric E0)⁻¹) :
    beta⁻¹ • M0 ≤ G0ᴴ * canonBlock Et * G0 ∧ G0ᴴ * canonBlock Et * G0 ≤ beta • M0 := by
  obtain ⟨hlow', hhigh'⟩ :=
    canonBlock_sandwich hd hE0 hEs hEt hts hz0 hz1 hlow hhigh hceps hrho hbeta
  have hcong : G0ᴴ * canonBlock E0 * G0 = M0 := by
    rw [hG0, hM0]
    exact shear_conj_canonBlock hE0
  constructor
  · have h := conj_le_conj G0 hlow'
    rwa [conj_smul, hcong] at h
  · have h := conj_le_conj G0 hhigh'
    rwa [conj_smul, hcong] at h

/-- **The second boxed display** of the response-load calibration: the two imbalance
comparisons `κ_t ≤ ϱ^d κ_s` and `κ_s ≤ ϱ^{2d} κ_t`, at `ϱ = (det E_s/det E_t)^{1/d}`. -/
theorem imbalance_comparisons (hd : 2 ≤ d) (hEs : Es.PosDef) (hEt : Et.PosDef)
    (hts : Et ≤ Es) {rho : ℝ} (hrho : rho = canonDetRatio Es Et) :
    canonImbalance Et ≤ rho ^ d * canonImbalance Es ∧
      canonImbalance Es ≤ rho ^ (2 * d) * canonImbalance Et := by
  have hdet : (0 : ℝ) < Es.det / Et.det := div_pos hEs.det_pos hEt.det_pos
  obtain ⟨-, -, -, hpair, -⟩ :=
    canonDeterminantLoss hd hEs hEt hts (r := rho)
      (by rw [hrho]; exact canonDetRatio_nonneg hdet.le)
      (by rw [hrho]; exact canonDetRatio_pow (by omega) hdet.le)
  exact hpair

/-! ## The two balance chains -/

/-- **The terminal balance chain**:
`β⁻¹ 𝐌₀ ≤ 𝐆₀ᵗ M(E_t) 𝐆₀ ≤ Ê_t ≤ β√κ_t 𝐌₀`. -/
theorem hatE_terminal_sandwich (hd : 2 ≤ d) (hE0 : E0.PosDef) (hEs : Es.PosDef)
    (hEt : Et.PosDef) (hts : Et ≤ Es) (htSharp : fullBlockSharp Et ≤ Et)
    {z ceps rho beta : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hlow : (1 - z) • E0 ≤ Es) (hhigh : Es ≤ (1 + z) • E0)
    (hceps : ceps = Real.sqrt ((1 + z) / (1 - z))) (hrho : rho = canonDetRatio Es Et)
    (hbeta : beta = ceps * Real.sqrt (rho ^ d))
    {G0 M0 : FullBlockMat d} (hG0 : G0 = fullBlockShear (canonShear E0))
    (hM0 : M0 = Matrix.fromBlocks (canonMetric E0) 0 0 (canonMetric E0)⁻¹) :
    beta⁻¹ • M0 ≤ G0ᴴ * Et * G0 ∧
      G0ᴴ * Et * G0 ≤ (beta * Real.sqrt (canonImbalance Et)) • M0 := by
  obtain ⟨hsandLow, hsandUp⟩ :=
    metric_sandwich hd hE0 hEs hEt hts hz0 hz1 hlow hhigh hceps hrho hbeta hG0 hM0
  obtain ⟨-, hMle, hleM⟩ := canonBalance hEt htSharp
  refine ⟨hsandLow.trans (conj_le_conj G0 hMle), ?_⟩
  have hstep := conj_le_conj G0 hleM
  rw [conj_smul] at hstep
  refine hstep.trans ?_
  have h := smul_le_smul_of_le (Real.sqrt_nonneg (canonImbalance Et)) hsandUp
  rw [smul_smul] at h
  rw [mul_comm beta (Real.sqrt (canonImbalance Et))]
  exact h

/-- **The earlier-scale balance chain**:
`Ê_s ≤ √κ_s 𝐆₀ᵗ M(E_s) 𝐆₀ ≤ c_ε √κ_s 𝐌₀`. -/
theorem hatE_earlier_bound (hE0 : E0.PosDef) (hEs : Es.PosDef)
    (hsSharp : fullBlockSharp Es ≤ Es) {z ceps : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hlow : (1 - z) • E0 ≤ Es) (hhigh : Es ≤ (1 + z) • E0)
    (hceps : ceps = Real.sqrt ((1 + z) / (1 - z)))
    {G0 M0 : FullBlockMat d} (hG0 : G0 = fullBlockShear (canonShear E0))
    (hM0 : M0 = Matrix.fromBlocks (canonMetric E0) 0 0 (canonMetric E0)⁻¹) :
    G0ᴴ * Es * G0 ≤ (ceps * Real.sqrt (canonImbalance Es)) • M0 := by
  obtain ⟨-, hnearUp⟩ := canonBlock_near_isometry hE0 hEs hz0 hz1 hlow hhigh
  rw [← hceps] at hnearUp
  obtain ⟨-, -, hleM⟩ := canonBalance hEs hsSharp
  have hcong : G0ᴴ * canonBlock E0 * G0 = M0 := by
    rw [hG0, hM0]; exact shear_conj_canonBlock hE0
  have hstep := conj_le_conj G0 hleM
  rw [conj_smul] at hstep
  refine hstep.trans ?_
  have hup : G0ᴴ * canonBlock Es * G0 ≤ ceps • M0 := by
    have h := conj_le_conj G0 hnearUp
    rwa [conj_smul, hcong] at h
  have h := smul_le_smul_of_le (Real.sqrt_nonneg (canonImbalance Es)) hup
  rw [smul_smul] at h
  rw [mul_comm ceps (Real.sqrt (canonImbalance Es))]
  exact h

end

end Response
end HighContrast
end HCPolySupport
