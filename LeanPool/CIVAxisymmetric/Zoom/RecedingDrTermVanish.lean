/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingThetaDerivative
public import LeanPool.CIVAxisymmetric.Zoom.RecedingCurvatureVanish

/-!
# The receding-axis `∂_R Θₙ/(Aₙ+R)` term vanishes in the limit

The manuscript drops three terms from `eq:aniso:zoom:receding:equation` as the
recentring offset `A = rc / lam → ∞`: `∂_R Θₙ/(Aₙ+R)`, `Θₙ/(Aₙ+R)²` and
`∂_Z(Sₙ²)/(Aₙ+R)`. The second is `CIV.tendsto_zoomTheta_pde_curvature_terms_nhdsWithin_zero`
of `CIV.Zoom.RecedingCurvatureVanish`; the first is proved here. The stretching term
`− Vₙ Θₙ/(Aₙ+R)` of the same equation is *not* one of the dropped three: it is absorbed
into the perfect divergence `∂_R(Vₙ Θₙ) + ∂_Z(Wₙ Θₙ)` by
`zoomTheta_transport_divergenceForm` and is kept in the limiting equation.

Every hypothesis on the zoom scale is eventual (`∀ᶠ lam in 𝓝[>] 0`). At a fixed
`((R, Z), τ)` neither the cylinder membership nor `lam ^ (2 * h) ≤ 1` can hold at every
positive scale — the first fails at `lam = √(1 / (-τ))`, the second at `lam = 2` when
`0 < h` — so the all-scales forms are satisfied by nothing.
`eventually_zoomPointRec_mem_unitCylinder_at` and `eventually_zoomDelta_le_one` produce
the eventual forms, and `tendsto_zoomTheta_pde_axis_terms_of_recentring` discharges all
four of them from the standing hypotheses of `prop:aniso:small`.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- `δ = lam ^ (2 * h) ≤ 1` for every scale below `1`, hence for all sufficiently small
scales. This is the witness that makes the eventual `hdelta` hypotheses of this file
satisfiable; the all-scales form `∀ lam > 0, lam ^ (2 * h) ≤ 1` is refuted by `lam = 2`
whenever `0 < h`. -/
theorem eventually_zoomDelta_le_one {h : ℝ} (hh : 0 ≤ h) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ^ (2 * h) ≤ 1 := by
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [hmem] with lam hlam
  exact Real.rpow_le_one hlam.1.le hlam.2.le (by linarith only [hh])

/-- The `∂_R Θ_n` term alone is bounded by the same power-law decay as the sum
`|∂_R Θ_n| + |∂_Z Θ_n|`. -/
theorem abs_dr_zoomTheta_le {C h lam rc zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2) (hdelta : lam ^ (2 * h) ≤ 1)
    {p : (ℝ × ℝ) × ℝ} (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (htau : p.2 ≤ -1) :
    |dr (zoomTheta lam h rc zc u) p| ≤ 4 * C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  have hsum := abs_dr_zoomTheta_add_abs_dz_zoomTheta_le hlam hb hu hC hh0 hh1 hdelta hp htau
  have hdz_nonneg : 0 ≤ |dz (zoomTheta lam h rc zc u) p| := abs_nonneg _
  linarith only [hsum, hdz_nonneg]

/-- `eq:aniso:zoom:receding:limit` (the `∂_R Θₙ` term): the `∂_R Θₙ/(Aₙ+R)` correction
vanishes as `lam → 0⁺`, using the derivative bound `abs_dr_zoomTheta_le` on the scales
where the recentred zoom point lies in the unit cylinder and `δ ≤ 1`. -/
theorem tendsto_zoomTheta_pde_dr_term_nhdsWithin_zero {C h rc zc : ℝ} (hrc : 0 < rc)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2)
    {R Z tau : ℝ} (hR : 0 ≤ R) (htau : tau ≤ -1)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hmem : ∀ᶠ lam in 𝓝[>] (0 : ℝ), zoomPointRec lam h rc zc ((R, Z), tau) ∈ unitCylinder)
    (hdelta : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ^ (2 * h) ≤ 1) :
    Tendsto (fun lam : ℝ => dr (zoomTheta lam h rc zc u) ((R, Z), tau) / (rc / lam + R))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  set D := fun lam : ℝ => dr (zoomTheta lam h rc zc u) ((R, Z), tau) with hD_def
  set M := 4 * C * (-tau) ^ (-(1 / 2 : ℝ)) with hM_def
  have hD : ∀ᶠ lam in 𝓝[>] (0 : ℝ), |D lam| ≤ M := by
    filter_upwards [self_mem_nhdsWithin, hmem, hdelta] with lam hlam hmem_lam hdelta_lam
    rw [hD_def, hM_def]
    exact abs_dr_zoomTheta_le hlam hb hu hC hh0 hh1 hdelta_lam hmem_lam htau
  exact tendsto_offset_term_nhdsWithin_zero hrc hR D hD

/-- `eq:aniso:zoom:receding:limit`: the three `1/(Aₙ+R)`-weighted corrections of
`eq:aniso:zoom:receding:equation` that vanish as `lam → 0⁺`. Two of them,
`Θₙ/(Aₙ+R)²` and `∂_R Θₙ/(Aₙ+R)`, are dropped by the manuscript on passing to the limit;
the third, the stretching term `Vₙ Θₙ/(Aₙ+R)`, is instead absorbed into the perfect
divergence by `zoomTheta_transport_divergenceForm`, and its limit is recorded here only
as an estimate on the transport part. The curvature pair comes from
`CIV.tendsto_zoomTheta_pde_curvature_terms_nhdsWithin_zero`, the `∂_R Θₙ` term from
`CIV.tendsto_zoomTheta_pde_dr_term_nhdsWithin_zero`. -/
theorem tendsto_zoomTheta_pde_axis_terms_nhdsWithin_zero {C h rc zc : ℝ} (hrc : 0 < rc)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2)
    {R Z tau : ℝ} (hR : 0 ≤ R) (htau : tau ≤ -1)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hmem : ∀ᶠ lam in 𝓝[>] (0 : ℝ), zoomPointRec lam h rc zc ((R, Z), tau) ∈ unitCylinder)
    (hdelta : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ^ (2 * h) ≤ 1)
    {MV MTheta : ℝ}
    (hV : ∀ᶠ lam in 𝓝[>] (0 : ℝ), |zoomVRec lam h rc zc u ((R, Z), tau)| ≤ MV)
    (hTheta : ∀ᶠ lam in 𝓝[>] (0 : ℝ), |zoomTheta lam h rc zc u ((R, Z), tau)| ≤ MTheta) :
    Tendsto (fun lam : ℝ =>
        zoomVRec lam h rc zc u ((R, Z), tau) / (rc / lam + R) * zoomTheta lam h rc zc u ((R, Z),
          tau)
          + zoomTheta lam h rc zc u ((R, Z), tau) / (rc / lam + R) ^ 2
          + dr (zoomTheta lam h rc zc u) ((R, Z), tau) / (rc / lam + R))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hcurv := tendsto_zoomTheta_pde_curvature_terms_nhdsWithin_zero hrc hR u hV hTheta
  have hdr := tendsto_zoomTheta_pde_dr_term_nhdsWithin_zero hrc hC hh0 hh1 hR htau u hb hu hmem
    hdelta
  simpa [add_assoc] using hcurv.add hdr

/-- The same limit with every eventual hypothesis discharged: under the standing
hypotheses of `prop:aniso:small` — `0 < h < 1/2`, the anisotropic bounds
`eq:aniso:bounds` with a nonnegative constant, a `C²` velocity on the unit cylinder, a
recentring `(rc, zc)` strictly inside the unit disc of the meridional plane, and a
selected time `τ ≤ -1` — the three `1/(Aₙ+R)`-weighted corrections tend to `0` with no
hypothesis left on the zoom scale. This is the consumption witness for
`tendsto_zoomTheta_pde_axis_terms_nhdsWithin_zero`: each of its four eventual
hypotheses is produced here, so the statement is satisfiable and not vacuous. -/
theorem tendsto_zoomTheta_pde_axis_terms_of_recentring {C h rc zc : ℝ} (hrc : 0 < rc)
    (hh : 0 < h ∧ h < 1 / 2) (hC : 0 ≤ C) (hm : rc ^ 2 + zc ^ 2 < 1)
    {R Z tau : ℝ} (hR : 0 ≤ R) (htau : tau ≤ -1)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) :
    Tendsto (fun lam : ℝ =>
        zoomVRec lam h rc zc u ((R, Z), tau) / (rc / lam + R) * zoomTheta lam h rc zc u ((R, Z),
          tau)
          + zoomTheta lam h rc zc u ((R, Z), tau) / (rc / lam + R) ^ 2
          + dr (zoomTheta lam h rc zc u) ((R, Z), tau) / (rc / lam + R))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have htau0 : tau < 0 := by linarith only [htau]
  exact tendsto_zoomTheta_pde_axis_terms_nhdsWithin_zero hrc hC hh.1.le hh.2.le hR htau u hb hu
    (eventually_zoomPointRec_mem_unitCylinder_at hh hm ((R, Z), tau) htau0)
    (eventually_zoomDelta_le_one hh.1.le)
    (eventually_abs_zoomVRec_le hh hm u hb ((R, Z), tau) htau0)
    (eventually_abs_zoomTheta_le hh hC hm u hb hu ((R, Z), tau) htau0)

end CIV
