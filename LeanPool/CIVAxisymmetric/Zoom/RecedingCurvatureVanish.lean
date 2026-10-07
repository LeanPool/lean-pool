/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingEquation

/-!
# Receding-axis curvature terms vanish in the limit

As the recentring offset `A = rc / lam → ∞`, the two correction terms
`− Vₙ/(Aₙ+R)·Θₙ` and `− Θₙ/(Aₙ+R)²` of `zoomTheta_pde` tend to zero at a fixed
point `((R, Z), τ)`.

The two play different roles in `eq:aniso:zoom:receding:equation`. Only
`− Θₙ/(Aₙ+R)²` is one of the three terms the manuscript drops on passing to the limit;
the other two dropped terms are `∂_R Θₙ/(Aₙ+R)` and `∂_Z(Sₙ²)/(Aₙ+R)`. The stretching
term `− Vₙ Θₙ/(Aₙ+R)` is *not* dropped: `zoomTheta_transport_divergenceForm` absorbs it
into the perfect divergence `∂_R(Vₙ Θₙ) + ∂_Z(Wₙ Θₙ)` that the limiting equation
retains. The limit proved for it here is an auxiliary estimate on the transport part,
not the removal of an axis term.

The limits are taken along the germ `𝓝[>] 0` of the zoom scale, and every hypothesis
about the zoom point is an eventual one: at a fixed `((R, Z), τ)` the recentred zoom
point lies in the unit cylinder only for small scales, never for all of them (`lam = 1`
forces `τ < 0` while `lam = √(1/(-τ))` forces `lam² τ = -1`, so the all-scales form is
satisfied by no real `τ`). `eventually_zoomPointRec_mem_unitCylinder_at` produces the
eventual form from the standing hypotheses of `prop:aniso:small`.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section



namespace CIV

/-! ### Producing the eventual hypotheses -/

/-- The one-point form of `eventually_zoomPointRec_mem_unitCylinder`: at a fixed
negative-time point `p`, and for a recentring `(rc, zc)` strictly inside the unit disc of
the meridional plane, the recentred zoom point lies in the unit cylinder for all
sufficiently small scales. This is the witness that makes the eventual membership
hypotheses of this file and of `CIV.Zoom.RecedingDrTermVanish` satisfiable. -/
theorem eventually_zoomPointRec_mem_unitCylinder_at {h rc zc : ℝ} (hh : 0 < h ∧ h < 1 / 2)
    (hm : rc ^ 2 + zc ^ 2 < 1) (p : (ℝ × ℝ) × ℝ) (hp : p.2 < 0) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ), zoomPointRec lam h rc zc p ∈ unitCylinder := by
  have hsum_nonneg : (0 : ℝ) ≤ rc ^ 2 + zc ^ 2 := by positivity
  set ρ : ℝ := Real.sqrt ((rc ^ 2 + zc ^ 2 + 1) / 2) with hρ_def
  have hhalf_nonneg : (0 : ℝ) ≤ (rc ^ 2 + zc ^ 2 + 1) / 2 := by linarith only [hsum_nonneg]
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρsq : ρ ^ 2 = (rc ^ 2 + zc ^ 2 + 1) / 2 := Real.sq_sqrt hhalf_nonneg
  have hmlt : rc ^ 2 + zc ^ 2 < ρ ^ 2 := by rw [hρsq]; linarith only [hm]
  have hρlt : ρ < 1 := by
    have h1 : ρ ^ 2 < 1 := by rw [hρsq]; linarith only [hm]
    nlinarith only [h1, hρ0]
  have hall := eventually_zoomPointRec_mem_unitCylinder hh hρ0 hmlt hρlt {p} isCompact_singleton
    (by intro q hq; rw [mem_singleton_iff] at hq; subst hq; exact hp)
  filter_upwards [hall] with lam hlam
  exact hlam p rfl

/-- The `(0, 0)` entry of `eq:aniso:zoom:derivatives` in eventual form: the recentred
radial velocity is bounded by the scale-independent constant `C (-τ)^{-1/2}` for all
sufficiently small scales. This produces the `hV` hypothesis of
`tendsto_zoomTheta_pde_curvature_terms_nhdsWithin_zero`. -/
theorem eventually_abs_zoomVRec_le {C h rc zc : ℝ} (hh : 0 < h ∧ h < 1 / 2)
    (hm : rc ^ 2 + zc ^ 2 < 1) (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u)
    (p : (ℝ × ℝ) × ℝ) (hp : p.2 < 0) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ), |zoomVRec lam h rc zc u p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_zoomPointRec_mem_unitCylinder_at hh hm p hp] with lam hlam hmem
  have hle := abs_zoomVRec_le C h lam rc zc hlam u hb p hmem
  rwa [show (-(1 / 2 : ℝ) - 0 / 2 - (1 / 2 - h) * 0) = -(1 / 2 : ℝ) from by ring] at hle

/-- `eq:aniso:zoom:receding:bound` in eventual form: since `δ = lam ^ (2 * h) ≤ 1` for
small scales, the two terms of `abs_zoomTheta_le` collapse to the scale-independent
constant `C ((-τ)^{-1+h} + (-τ)^{-1-h})`. This produces the `hTheta` hypothesis of
`tendsto_zoomTheta_pde_curvature_terms_nhdsWithin_zero`. -/
theorem eventually_abs_zoomTheta_le {C h rc zc : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hC : 0 ≤ C)
    (hm : rc ^ 2 + zc ^ 2 < 1) (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : p.2 < 0) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ),
      |zoomTheta lam h rc zc u p| ≤ C * ((-p.2) ^ (-1 + h) + (-p.2) ^ (-1 - h)) := by
  have hsmall : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [self_mem_nhdsWithin, hsmall,
    eventually_zoomPointRec_mem_unitCylinder_at hh hm p hp] with lam hlam hlam1 hmem
  have hle := abs_zoomTheta_le C h lam rc zc hlam u hb hu p hmem
  have hnn : (0 : ℝ) ≤ lam ^ (2 * h) := Real.rpow_nonneg hlam.le _
  have hdelta : lam ^ (2 * h) ≤ 1 :=
    Real.rpow_le_one hlam1.1.le hlam1.2.le (by linarith only [hh.1])
  have hsq : (lam ^ (2 * h)) ^ 2 ≤ 1 := by nlinarith only [hnn, hdelta]
  have hpow_nonneg : (0 : ℝ) ≤ (-p.2) ^ (-1 + h) := Real.rpow_nonneg (by linarith only [hp]) _
  have hstep : (lam ^ (2 * h)) ^ 2 * (-p.2) ^ (-1 + h) ≤ (-p.2) ^ (-1 + h) := by
    nlinarith only [hsq, hpow_nonneg]
  calc |zoomTheta lam h rc zc u p|
      ≤ C * ((lam ^ (2 * h)) ^ 2 * (-p.2) ^ (-1 + h) + (-p.2) ^ (-1 - h)) := hle
    _ ≤ C * ((-p.2) ^ (-1 + h) + (-p.2) ^ (-1 - h)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hstep]) hC

/-! ### The two offset decay lemmas -/

/-- `eq:aniso:zoom:receding:limit`: a numerator bounded for small scales, divided by
`(A + R)²` with `A = rc / lam → ∞`, tends to `0` as `lam → 0⁺`. -/
theorem tendsto_offset_sq_term_nhdsWithin_zero {rc M : ℝ} (hrc : 0 < rc) {R : ℝ} (hR : 0 ≤ R)
    (D : ℝ → ℝ) (hD : ∀ᶠ lam in 𝓝[>] (0 : ℝ), |D lam| ≤ M) :
    Tendsto (fun lam : ℝ => D lam / (rc / lam + R) ^ 2) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hpos_sum : ∀ lam, 0 < lam → 0 < rc / lam + R := by
    intro lam hlam
    have hdiv : 0 < rc / lam := div_pos hrc hlam
    linarith only [hdiv, hR]
  have hratio_tendsto : Tendsto (fun lam : ℝ => rc / lam) (𝓝[>] 0) atTop :=
    tendsto_zoomPointRec_ratio_atTop hrc
  have hsum_tendsto : Tendsto (fun lam : ℝ => rc / lam + R) (𝓝[>] 0) atTop :=
    hratio_tendsto.atTop_add tendsto_const_nhds
  have hinv_tendsto : Tendsto (fun lam : ℝ => (rc / lam + R)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    hsum_tendsto.inv_tendsto_atTop
  have hsq_tendsto : Tendsto (fun lam : ℝ => ((rc / lam + R)⁻¹) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using hinv_tendsto.pow 2
  have hbound_tendsto : Tendsto (fun lam : ℝ => M * ((rc / lam + R)⁻¹) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa [mul_comm] using hsq_tendsto.const_mul M
  refine squeeze_zero_norm' ?_ hbound_tendsto
  filter_upwards [self_mem_nhdsWithin, hD] with lam hlam hDlam
  have hpos : 0 < rc / lam + R := hpos_sum lam hlam
  have hpos_ne : rc / lam + R ≠ 0 := hpos.ne'
  calc
    |D lam / (rc / lam + R) ^ 2| = |D lam| / |(rc / lam + R) ^ 2| := by rw [abs_div]
    _ = |D lam| / ((rc / lam + R) ^ 2) := by rw [abs_of_pos (pow_pos hpos 2)]
    _ ≤ M / ((rc / lam + R) ^ 2) := (div_le_div_iff_of_pos_right (pow_pos hpos 2)).mpr hDlam
    _ = M * ((rc / lam + R)⁻¹) ^ 2 := by rw [div_eq_mul_inv, inv_pow]

/-- `eq:aniso:zoom:receding:limit`: the same with the offset to the first power, the form
consumed by the `∂_R Θₙ/(Aₙ+R)` limit of `CIV.Zoom.RecedingDrTermVanish` and by the
divergence limit of the receding drift. -/
theorem tendsto_offset_term_nhdsWithin_zero {rc M : ℝ} (hrc : 0 < rc) {R : ℝ} (hR : 0 ≤ R)
    (D : ℝ → ℝ) (hD : ∀ᶠ lam in 𝓝[>] (0 : ℝ), |D lam| ≤ M) :
    Tendsto (fun lam : ℝ => D lam / (rc / lam + R)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hpos_sum : ∀ lam, 0 < lam → 0 < rc / lam + R := by
    intro lam hlam
    have hdiv : 0 < rc / lam := div_pos hrc hlam
    linarith only [hdiv, hR]
  have hratio_tendsto : Tendsto (fun lam : ℝ => rc / lam) (𝓝[>] 0) atTop :=
    tendsto_zoomPointRec_ratio_atTop hrc
  have hsum_tendsto : Tendsto (fun lam : ℝ => rc / lam + R) (𝓝[>] 0) atTop :=
    hratio_tendsto.atTop_add tendsto_const_nhds
  have hinv_tendsto : Tendsto (fun lam : ℝ => (rc / lam + R)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    hsum_tendsto.inv_tendsto_atTop
  have hbound_tendsto : Tendsto (fun lam : ℝ => M * (rc / lam + R)⁻¹) (𝓝[>] 0) (𝓝 0) := by
    simpa [mul_comm] using hinv_tendsto.const_mul M
  refine squeeze_zero_norm' ?_ hbound_tendsto
  filter_upwards [self_mem_nhdsWithin, hD] with lam hlam hDlam
  have hpos : 0 < rc / lam + R := hpos_sum lam hlam
  calc
    ‖D lam / (rc / lam + R)‖ = |D lam / (rc / lam + R)| := by rw [Real.norm_eq_abs]
    _ = |D lam| / |rc / lam + R| := by rw [abs_div]
    _ = |D lam| / (rc / lam + R) := by rw [abs_of_pos hpos]
    _ = |D lam| * (rc / lam + R)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ M * (rc / lam + R)⁻¹ := mul_le_mul_of_nonneg_right hDlam (by positivity)

/-! ### The two curvature terms -/

/-- `eq:aniso:zoom:receding:limit` (the curvature pair): the two terms
`− Vₙ/(Aₙ+R)·Θₙ − Θₙ/(Aₙ+R)²` of `zoomTheta_pde` vanish as `lam → 0⁺`. The bounds on
`Vₙ` and `Θₙ` are required only for small scales, which is what
`eventually_abs_zoomVRec_le` and `eventually_abs_zoomTheta_le` supply. -/
theorem tendsto_zoomTheta_pde_curvature_terms_nhdsWithin_zero {rc h zc : ℝ} (hrc : 0 < rc)
    {R Z tau : ℝ} (hR : 0 ≤ R) (u : ParabolicPoint → Vec3)
    {MV MTheta : ℝ}
    (hV : ∀ᶠ lam in 𝓝[>] (0 : ℝ), |zoomVRec lam h rc zc u ((R, Z), tau)| ≤ MV)
    (hTheta : ∀ᶠ lam in 𝓝[>] (0 : ℝ), |zoomTheta lam h rc zc u ((R, Z), tau)| ≤ MTheta) :
    Tendsto (fun lam : ℝ =>
        zoomVRec lam h rc zc u ((R, Z), tau) / (rc / lam + R) * zoomTheta lam h rc zc u ((R, Z),
          tau)
          + zoomTheta lam h rc zc u ((R, Z), tau) / (rc / lam + R) ^ 2)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  set V := fun lam : ℝ => zoomVRec lam h rc zc u ((R, Z), tau)
  set Θ := fun lam : ℝ => zoomTheta lam h rc zc u ((R, Z), tau)
  have hpos_sum : ∀ lam, 0 < lam → 0 < rc / lam + R := by
    intro lam hlam
    have hdiv : 0 < rc / lam := div_pos hrc hlam
    linarith only [hdiv, hR]
  have hratio_tendsto : Tendsto (fun lam : ℝ => rc / lam) (𝓝[>] 0) atTop :=
    tendsto_zoomPointRec_ratio_atTop hrc
  have hsum_tendsto : Tendsto (fun lam : ℝ => rc / lam + R) (𝓝[>] 0) atTop :=
    hratio_tendsto.atTop_add tendsto_const_nhds
  have hinv_tendsto : Tendsto (fun lam : ℝ => (rc / lam + R)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    hsum_tendsto.inv_tendsto_atTop
  have hsq_tendsto : Tendsto (fun lam : ℝ => ((rc / lam + R)⁻¹) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using hinv_tendsto.pow 2
  have hfirst_bound_tendsto : Tendsto (fun lam : ℝ => (MV * MTheta) * (rc / lam + R)⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
    simpa [mul_comm] using hinv_tendsto.const_mul (MV * MTheta)
  have hsecond_bound_tendsto : Tendsto (fun lam : ℝ => MTheta * ((rc / lam + R)⁻¹) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    simpa [mul_comm] using hsq_tendsto.const_mul MTheta
  have hsum_bound_tendsto : Tendsto
      (fun lam : ℝ => (MV * MTheta) * (rc / lam + R)⁻¹ + MTheta * ((rc / lam + R)⁻¹) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hfirst_bound_tendsto.add hsecond_bound_tendsto
  refine squeeze_zero_norm' ?_ hsum_bound_tendsto
  filter_upwards [self_mem_nhdsWithin, hV, hTheta] with lam hlam hVraw hThetaRaw
  have hpos : 0 < rc / lam + R := hpos_sum lam hlam
  set A := rc / lam + R with hA_def
  have hVbound : |V lam| ≤ MV := hVraw
  have hThetaBound : |Θ lam| ≤ MTheta := hThetaRaw
  have hMV_nonneg : 0 ≤ MV := by
    have h := abs_nonneg (V lam)
    linarith only [h, hVbound]
  have hMTheta_nonneg : 0 ≤ MTheta := by
    have h := abs_nonneg (Θ lam)
    linarith only [h, hThetaBound]
  calc
    |V lam / A * Θ lam + Θ lam / A ^ 2|
        ≤ |V lam / A * Θ lam| + |Θ lam / A ^ 2| := abs_add_le _ _
    _ = |V lam / A| * |Θ lam| + |Θ lam / A ^ 2| := by rw [abs_mul]
    _ = (|V lam| / |A|) * |Θ lam| + |Θ lam| / |A ^ 2| := by
      rw [abs_div, abs_div]
    _ = (|V lam| / A) * |Θ lam| + |Θ lam| / (A ^ 2) := by
      rw [abs_of_pos hpos, abs_of_pos (pow_pos hpos 2)]
    _ ≤ (|V lam| / A) * MTheta + MTheta / (A ^ 2) := by
      refine add_le_add ?_ ?_
      · refine mul_le_mul_of_nonneg_left hThetaBound ?_
        exact div_nonneg (abs_nonneg _) hpos.le
      · exact (div_le_div_iff_of_pos_right (pow_pos hpos 2)).mpr hThetaBound
    _ ≤ (MV / A) * MTheta + MTheta / A ^ 2 := by
      refine add_le_add ?_ (by rfl)
      refine mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hpos).mpr hVbound)
        hMTheta_nonneg
    _ = (MV * MTheta) * A⁻¹ + MTheta * (A⁻¹) ^ 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv, inv_pow]
      ring

end CIV
