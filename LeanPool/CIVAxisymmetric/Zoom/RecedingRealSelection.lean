/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingContradictionClosure
public import LeanPool.CIVAxisymmetric.Zoom.RecedingSelectionIdentity
public import LeanPool.CIVAxisymmetric.Zoom.RecedingSecondDerivativeBoundsV
public import LeanPool.CIVAxisymmetric.Zoom.RecedingSecondDerivativeBoundsW
public import LeanPool.CIVAxisymmetric.Zoom.FiniteZoomCutoffField
public import LeanPool.CIVAxisymmetric.Zoom.FiniteZoomCutoffSecondDeriv
public import LeanPool.CIVAxisymmetric.Zoom.FiniteZoomCutoffBounds
public import LeanPool.CIVAxisymmetric.Zoom.OperatorNormProd
public import LeanPool.CIVAxisymmetric.Zoom.MeridionalContradictionDichotomy
public import LeanPool.CIVAxisymmetric.Zoom.PassToLimit
public import LeanPool.CIVAxisymmetric.Zoom.RecedingSliceSmoothness

/-!
# The receding-axis contradiction at the selected points

The last paragraph of Step 3 of the proof of `prop:aniso:small`: in the receding-axis case
(`A_n = r_n / λ_n → ∞`) the rescaled fields `V_n`, `W_n` of `eq:aniso:zoom:fields`, taken about
the selected points `x_n = (r_n, z_n)` in the variables `eq:aniso:zoom:receding:variables`, are
bounded in `C²` on compact sets at `τ = -1`; if the rescaled azimuthal vorticity `Θ_n(·, -1)`
tends to zero, the endpoint argument `eq:aniso:zoom:receding:endpoint` makes `∂_R V_n(0,0,-1)`
and `∂_Z W_n(0,0,-1)` tend to zero, `eq:aniso:zoom:receding:quotient` makes the quotient term
tend to zero, and the selection `eq:aniso:zoom:selected` is contradicted.

The endpoint argument (`CIV.step_receding_contradiction`) is stated for fields smooth on the
whole plane. The rescaled fields at `τ = -1` are smooth only on the preimage of the unit
cylinder under the zoom map, a region which exhausts the plane as `n → ∞`; they are multiplied
here by a bump function equal to `1` on a ball of radius `(1 - ρ) / (4 (λ_n + μ_n))` and
supported where the zoom map lands in the cylinder, `μ_n = λ_n^{1-2h}`.
-/

public section

open Set Filter Topology Metric
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### The slice region -/

/-- The points of the recentred zoomed plane mapped into the unit cylinder at `τ = -1`. -/
@[expose] def recSliceSet (lam h rc zc : ℝ) : Set (ℝ × ℝ) :=
  {q | zoomPointRec lam h rc zc (q, -1) ∈ unitCylinder}

theorem isOpen_recSliceSet (lam h rc zc : ℝ) : IsOpen (recSliceSet lam h rc zc) :=
  isOpen_unitCylinder_prod.preimage
    ((continuous_zoomPointRec lam h rc zc).comp (continuous_id.prodMk continuous_const))

/-! ### A safe radius around the selected point -/

/-- If `rc² + zc² ≤ ρ² < 1`, a sup-ball of radius `s` with `(λ + λ^{1-2h}) s ≤ (1 - ρ)/2` lies
in the slice region. -/
theorem mem_recSliceSet_of_norm_le {h ρ lam rc zc s : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcz : rc ^ 2 + zc ^ 2 ≤ ρ ^ 2) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hs : (lam + lam ^ (1 - 2 * h)) * s ≤ (1 - ρ) / 2) {q : ℝ × ℝ} (hq : ‖q‖ ≤ s) :
    q ∈ recSliceSet lam h rc zc := by
  have hμ0 : 0 ≤ lam ^ (1 - 2 * h) := Real.rpow_nonneg hlam0.le _
  have hq1 : |q.1| ≤ s := by
    have := norm_fst_le q; rw [Real.norm_eq_abs] at this; linarith only [this, hq]
  have hq2 : |q.2| ≤ s := by
    have := norm_snd_le q; rw [Real.norm_eq_abs] at this; linarith only [this, hq]
  set x : ℝ := lam * q.1 with hx
  set y : ℝ := lam ^ (1 - 2 * h) * q.2 with hy
  have hxa : |x| ≤ lam * s := by
    rw [hx, abs_mul, abs_of_pos hlam0]; exact mul_le_mul_of_nonneg_left hq1 hlam0.le
  have hya : |y| ≤ lam ^ (1 - 2 * h) * s := by
    rw [hy, abs_mul, abs_of_nonneg hμ0]; exact mul_le_mul_of_nonneg_left hq2 hμ0
  have he : |x| + |y| ≤ (1 - ρ) / 2 := by nlinarith only [hxa, hya, hs]
  have hrc : |rc| ≤ ρ := abs_le_of_sq_le_sq' (by nlinarith only [hcz, sq_nonneg zc]) hρ0
    |> fun h => abs_le.mpr h
  have hzc : |zc| ≤ ρ := abs_le_of_sq_le_sq' (by nlinarith only [hcz, sq_nonneg rc]) hρ0
    |> fun h => abs_le.mpr h
  have h1 : rc * x ≤ ρ * |x| := by
    have := neg_abs_le (rc * x); have h2 := le_abs_self (rc * x)
    rw [abs_mul] at h2
    nlinarith only [h2, hrc, abs_nonneg x]
  have h2 : zc * y ≤ ρ * |y| := by
    have h3 := le_abs_self (zc * y)
    rw [abs_mul] at h3
    nlinarith only [h3, hzc, abs_nonneg y]
  have hxx : x ^ 2 + y ^ 2 ≤ (|x| + |y|) ^ 2 := by
    nlinarith only [sq_abs x, sq_abs y, abs_nonneg x, abs_nonneg y]
  have hsum : (rc + x) ^ 2 + (zc + y) ^ 2 < 1 := by
    have hexp : (rc + x) ^ 2 + (zc + y) ^ 2 = (rc ^ 2 + zc ^ 2) + 2 * (rc * x + zc * y)
        + (x ^ 2 + y ^ 2) := by ring
    have hb : (ρ + (1 - ρ) / 2) ^ 2 < 1 := by nlinarith only [hρ0, hρ1]
    have hmono : (ρ + (|x| + |y|)) ^ 2 ≤ (ρ + (1 - ρ) / 2) ^ 2 := by
      have : 0 ≤ ρ + (|x| + |y|) := by positivity
      nlinarith only [he, this]
    nlinarith only [hexp, hcz, h1, h2, hxx, hmono, hb]
  show zoomPointRec lam h rc zc (q, -1) ∈ unitCylinder
  rw [zoomPointRec_mem_unitCylinder_iff]
  refine ⟨hsum, ?_, ?_⟩
  · show -1 < lam ^ 2 * (-1 : ℝ)
    nlinarith only [hlam0, hlam1]
  · show lam ^ 2 * (-1 : ℝ) < 0
    nlinarith only [hlam0]

/-! ### The bump function and the cutoff fields -/

/-- The outer radius `(1 - ρ) / (2 (λ + λ^{1-2h}))` of the cutoff at scale `λ`. -/
@[expose] def recCutoffRadius (h ρ lam : ℝ) : ℝ := (1 - ρ) / (2 * (lam + lam ^ (1 - 2 * h)))

theorem recCutoffRadius_pos {h ρ lam : ℝ} (hρ1 : ρ < 1) (hlam0 : 0 < lam) :
    0 < recCutoffRadius h ρ lam := by
  have hμ : 0 < lam ^ (1 - 2 * h) := Real.rpow_pos_of_pos hlam0 _
  unfold recCutoffRadius
  exact div_pos (by linarith only [hρ1]) (by linarith only [hlam0, hμ])

/-- The cutoff at scale `λ`: equal to `1` on the closed ball of radius half the outer radius. -/
@[expose] def recCutoffBump (h ρ lam : ℝ) (hρ1 : ρ < 1) (hlam0 : 0 < lam) : ContDiffBump (0 : ℝ
  × ℝ) where
  rIn := recCutoffRadius h ρ lam / 2
  rOut := recCutoffRadius h ρ lam
  rIn_pos := by have := recCutoffRadius_pos (h := h) hρ1 hlam0; linarith only [this]
  rIn_lt_rOut := by have := recCutoffRadius_pos (h := h) hρ1 hlam0; linarith only [this]

theorem recCutoffBump_safe {h ρ lam rc zc : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcz : rc ^ 2 + zc ^ 2 ≤ ρ ^ 2) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    closedBall (0 : ℝ × ℝ) (recCutoffBump h ρ lam hρ1 hlam0).rOut ⊆ recSliceSet lam h rc zc := by
  intro q hq
  rw [mem_closedBall, dist_eq_norm, sub_zero] at hq
  refine mem_recSliceSet_of_norm_le hρ0 hρ1 hcz hlam0 hlam1 ?_ hq
  have hμ : 0 < lam ^ (1 - 2 * h) := Real.rpow_pos_of_pos hlam0 _
  show (lam + lam ^ (1 - 2 * h)) * recCutoffRadius h ρ lam ≤ (1 - ρ) / 2
  unfold recCutoffRadius
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith only [hlam0, hμ]

/-- The inner radius of the cutoff grows without bound along a zoom sequence. -/
theorem eventually_lt_recCutoffBump_rIn {h ρ : ℝ} (hh1 : h < 1 / 2) (hρ1 : ρ < 1)
    {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n) (hlam_lim : Tendsto lam atTop (nhds 0)) (r : ℝ) :
    ∀ᶠ n in atTop, r < (recCutoffBump h ρ (lam n) hρ1 (hlam0 n)).rIn := by
  have hexp : (0 : ℝ) < 1 - 2 * h := by linarith only [hh1]
  have hrpow : Tendsto (fun n => lam n ^ (1 - 2 * h)) atTop (nhds ((0 : ℝ) ^ (1 - 2 * h))) :=
    (Real.continuousAt_rpow_const 0 (1 - 2 * h) (Or.inr hexp.le)).tendsto.comp hlam_lim
  rw [Real.zero_rpow hexp.ne'] at hrpow
  have hsum : Tendsto (fun n => lam n + lam n ^ (1 - 2 * h)) atTop (nhds 0) := by
    simpa using hlam_lim.add hrpow
  set r' : ℝ := max r 1 with hr'
  have hr'pos : 0 < r' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hpos : (0 : ℝ) < (1 - ρ) / (4 * r') := div_pos (by linarith only [hρ1]) (by positivity)
  filter_upwards [hsum.eventually_lt_const hpos] with n hn
  have hμ : 0 < lam n ^ (1 - 2 * h) := Real.rpow_pos_of_pos (hlam0 n) _
  have hS : 0 < lam n + lam n ^ (1 - 2 * h) := by linarith only [hlam0 n, hμ]
  show r < recCutoffRadius h ρ (lam n) / 2
  unfold recCutoffRadius
  have h1 : (lam n + lam n ^ (1 - 2 * h)) * (4 * r') < 1 - ρ :=
    (lt_div_iff₀ (by positivity)).mp hn
  have h2 : r' < (1 - ρ) / (2 * (lam n + lam n ^ (1 - 2 * h))) / 2 := by
    rw [div_div, lt_div_iff₀ (by positivity)]
    linarith only [h1]
  exact lt_of_le_of_lt (le_max_left _ _) h2

/-- The cutoff-multiplied recentred radial field at `τ = -1`. -/
@[expose] def recCutoffV (h ρ lam rc zc : ℝ) (hρ1 : ρ < 1) (hlam0 : 0 < lam) (u : ParabolicPoint
  → Vec3) :
    ℝ × ℝ → ℝ :=
  fun q => recCutoffBump h ρ lam hρ1 hlam0 q * zoomVRec lam h rc zc u (q, -1)

/-- The cutoff-multiplied recentred axial field at `τ = -1`. -/
@[expose] def recCutoffW (h ρ lam rc zc : ℝ) (hρ1 : ρ < 1) (hlam0 : 0 < lam) (u : ParabolicPoint
  → Vec3) :
    ℝ × ℝ → ℝ :=
  fun q => recCutoffBump h ρ lam hρ1 hlam0 q * zoomWRec lam h rc zc u (q, -1)

theorem contDiff_recCutoffV {h ρ lam rc zc : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcz : rc ^ 2 + zc ^ 2 ≤ ρ ^ 2) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    {u : ParabolicPoint → Vec3} {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) :
    ContDiff ℝ (⊤ : ℕ∞) (recCutoffV h ρ lam rc zc hρ1 hlam0 u) :=
  contDiff_bump_mul_of_contDiffOn_of_subset_closedBall _ (isOpen_recSliceSet lam h rc zc)
    (contDiffOn_zoomVRec_slice hsol) (recCutoffBump_safe hρ0 hρ1 hcz hlam0 hlam1)

theorem contDiff_recCutoffW {h ρ lam rc zc : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcz : rc ^ 2 + zc ^ 2 ≤ ρ ^ 2) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    {u : ParabolicPoint → Vec3} {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) :
    ContDiff ℝ (⊤ : ℕ∞) (recCutoffW h ρ lam rc zc hρ1 hlam0 u) :=
  contDiff_bump_mul_of_contDiffOn_of_subset_closedBall _ (isOpen_recSliceSet lam h rc zc)
    (contDiffOn_zoomWRec_slice hsol) (recCutoffBump_safe hρ0 hρ1 hcz hlam0 hlam1)

/-- Inside the inner ball the cutoff fields agree with the raw slices near the point. -/
theorem recCutoffV_eventuallyEq {h ρ lam rc zc : ℝ} (hρ1 : ρ < 1) (hlam0 : 0 < lam)
    {u : ParabolicPoint → Vec3} {y : ℝ × ℝ}
    (hy : ‖y‖ < (recCutoffBump h ρ lam hρ1 hlam0).rIn) :
    recCutoffV h ρ lam rc zc hρ1 hlam0 u =ᶠ[𝓝 y]
      fun q : ℝ × ℝ => zoomVRec lam h rc zc u (q, -1) := by
  have hmem : y ∈ ball (0 : ℝ × ℝ) (recCutoffBump h ρ lam hρ1 hlam0).rIn := by
    rw [mem_ball, dist_eq_norm, sub_zero]; exact hy
  filter_upwards [(recCutoffBump h ρ lam hρ1 hlam0).eventuallyEq_one_of_mem_ball hmem]
    with q hq
  simp only [recCutoffV, hq, Pi.one_apply, one_mul]

theorem recCutoffW_eventuallyEq {h ρ lam rc zc : ℝ} (hρ1 : ρ < 1) (hlam0 : 0 < lam)
    {u : ParabolicPoint → Vec3} {y : ℝ × ℝ}
    (hy : ‖y‖ < (recCutoffBump h ρ lam hρ1 hlam0).rIn) :
    recCutoffW h ρ lam rc zc hρ1 hlam0 u =ᶠ[𝓝 y]
      fun q : ℝ × ℝ => zoomWRec lam h rc zc u (q, -1) := by
  have hmem : y ∈ ball (0 : ℝ × ℝ) (recCutoffBump h ρ lam hρ1 hlam0).rIn := by
    rw [mem_ball, dist_eq_norm, sub_zero]; exact hy
  filter_upwards [(recCutoffBump h ρ lam hρ1 hlam0).eventuallyEq_one_of_mem_ball hmem]
    with q hq
  simp only [recCutoffW, hq, Pi.one_apply, one_mul]

/-- The inner ball lies in the slice region. -/
theorem mem_recSliceSet_of_lt_rIn {h ρ lam rc zc : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcz : rc ^ 2 + zc ^ 2 ≤ ρ ^ 2) (hlam0 : 0 < lam) (hlam1 : lam < 1) {y : ℝ × ℝ}
    (hy : ‖y‖ < (recCutoffBump h ρ lam hρ1 hlam0).rIn) : y ∈ recSliceSet lam h rc zc := by
  refine recCutoffBump_safe hρ0 hρ1 hcz hlam0 hlam1 ?_
  rw [mem_closedBall, dist_eq_norm, sub_zero]
  exact hy.le.trans (recCutoffBump h ρ lam hρ1 hlam0).rIn_lt_rOut.le

/-! ### Pointwise bounds of the cutoff fields inside the inner ball -/

theorem hasFDerivAt_zoomVRec_slice {h lam rc zc : ℝ} {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {y : ℝ × ℝ}
    (hy : y ∈ recSliceSet lam h rc zc) :
    HasFDerivAt (fun q : ℝ × ℝ => zoomVRec lam h rc zc u (q, -1))
      (fderiv ℝ (fun q : ℝ × ℝ => zoomVRec lam h rc zc u (q, -1)) y) y :=
  (((contDiffOn_zoomVRec_slice hsol).contDiffAt
    ((isOpen_recSliceSet lam h rc zc).mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt

theorem hasFDerivAt_zoomWRec_slice {h lam rc zc : ℝ} {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {y : ℝ × ℝ}
    (hy : y ∈ recSliceSet lam h rc zc) :
    HasFDerivAt (fun q : ℝ × ℝ => zoomWRec lam h rc zc u (q, -1))
      (fderiv ℝ (fun q : ℝ × ℝ => zoomWRec lam h rc zc u (q, -1)) y) y :=
  (((contDiffOn_zoomWRec_slice hsol).contDiffAt
    ((isOpen_recSliceSet lam h rc zc).mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt

theorem recCutoffV_bounds {C h ρ lam rc zc : ℝ} (hC : 0 ≤ C) (hh1 : h < 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hcz : rc ^ 2 + zc ^ 2 ≤ ρ ^ 2) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {y : ℝ × ℝ}
    (hy : ‖y‖ < (recCutoffBump h ρ lam hρ1 hlam0).rIn) :
    |recCutoffV h ρ lam rc zc hρ1 hlam0 u y| ≤ 4 * C ∧
      ‖fderiv ℝ (recCutoffV h ρ lam rc zc hρ1 hlam0 u) y‖ ≤ 4 * C ∧
      ‖fderiv ℝ (fderiv ℝ (recCutoffV h ρ lam rc zc hρ1 hlam0 u)) y‖ ≤ 4 * C := by
  have hS := mem_recSliceSet_of_lt_rIn hρ0 hρ1 hcz hlam0 hlam1 hy
  have hSy : zoomPointRec lam h rc zc (y, -1) ∈ unitCylinder := hS
  have hEq := recCutoffV_eventuallyEq (rc := rc) (zc := zc) (u := u) hρ1 hlam0 hy
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1.of_le (by norm_num)
  have hτ : ((y, (-1 : ℝ)) : (ℝ × ℝ) × ℝ).2 ≤ -1 := le_rfl
  obtain ⟨y1, y2⟩ := y
  have hHF := hasFDerivAt_zoomVRec_slice hsol hS
  have hd1 : fderiv ℝ (fun q : ℝ × ℝ => zoomVRec lam h rc zc u (q, -1)) (y1, y2) (1, 0)
      = dr (zoomVRec lam h rc zc u) ((y1, y2), -1) :=
    (dr_eq_of_hasFDerivAt (zoomVRec lam h rc zc u) (-1) hHF).symm
  have hd2 : fderiv ℝ (fun q : ℝ × ℝ => zoomVRec lam h rc zc u (q, -1)) (y1, y2) (0, 1)
      = dz (zoomVRec lam h rc zc u) ((y1, y2), -1) :=
    (dz_eq_of_hasFDerivAt (zoomVRec lam h rc zc u) (-1) hHF).symm
  have hv : |zoomVRec lam h rc zc u ((y1, y2), -1)| ≤ C := by
    simpa using abs_zoomVRec_le C h lam rc zc hlam0 u hb _ hSy
  have hb1 : |dr (zoomVRec lam h rc zc u) ((y1, y2), -1)| ≤ C := by
    simpa using abs_dr_zoomVRec_le C h lam rc zc hlam0 u hb hu2 _ hSy
  have hb2 : |dz (zoomVRec lam h rc zc u) ((y1, y2), -1)| ≤ C := by
    simpa using abs_dz_zoomVRec_le C h lam rc zc hlam0 u hb hu2 _ hSy
  have hF1 : fderiv ℝ (recCutoffV h ρ lam rc zc hρ1 hlam0 u) (y1, y2)
      = fderiv ℝ (fun q : ℝ × ℝ => zoomVRec lam h rc zc u (q, -1)) (y1, y2) := hEq.fderiv_eq
  have hF2 : fderiv ℝ (fderiv ℝ (recCutoffV h ρ lam rc zc hρ1 hlam0 u)) (y1, y2)
      = fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => zoomVRec lam h rc zc u (q, -1))) (y1, y2) :=
    hEq.fderiv.fderiv_eq
  refine ⟨?_, ?_, ?_⟩
  · rw [hEq.eq_of_nhds]; linarith only [hv, hC]
  · have hnorm := norm_clm_le_norm_apply_add_norm_apply
      (fderiv ℝ (fun q : ℝ × ℝ => zoomVRec lam h rc zc u (q, -1)) (y1, y2))
    rw [hd1, hd2, Real.norm_eq_abs, Real.norm_eq_abs] at hnorm
    rw [hF1]; linarith only [hnorm, hb1, hb2, hC]
  · have hCD := contDiff_recCutoffV (h := h) hρ0 hρ1 hcz hlam0 hlam1 (rc := rc) (zc := zc) hsol
    have hzr := fderiv_fderiv_apply_axial_radial_eq_of_contDiff hCD (y1, y2)
    have hopen := isOpen_recSliceSet lam h rc zc
    have hrr := fderiv_fderiv_apply_radial_radial_eq_drdr hopen
      (contDiffOn_zoomVRec_slice (lam := lam) (h := h) (rc := rc) (zc := zc) hsol) hS
    have hrz := fderiv_fderiv_apply_radial_axial_eq_drdz hopen
      (contDiffOn_zoomVRec_slice (lam := lam) (h := h) (rc := rc) (zc := zc) hsol) hS
    have hzz := fderiv_fderiv_apply_axial_axial_eq_dzdz hopen
      (contDiffOn_zoomVRec_slice (lam := lam) (h := h) (rc := rc) (zc := zc) hsol) hS
    have hc1 : |dr (dr (zoomVRec lam h rc zc u)) ((y1, y2), -1)| ≤ C := by
      simpa using abs_drdr_zoomVRec_le_rpow_neg_half hlam0 hb hu2 hSy hC hτ
    have hc2 : |dr (dz (zoomVRec lam h rc zc u)) ((y1, y2), -1)| ≤ C := by
      simpa using abs_drdz_zoomVRec_le_rpow_neg_half hlam0 hb hu2 hSy hC hh1.le hτ
    have hc3 : |dz (dz (zoomVRec lam h rc zc u)) ((y1, y2), -1)| ≤ C := by
      simpa using abs_dzdz_zoomVRec_le_rpow_neg_half hlam0 hb hu2 hSy hC hh1.le hτ
    have hnorm := norm_fderiv_fderiv_le_of_apply (recCutoffV h ρ lam rc zc hρ1 hlam0 u) (y1, y2)
    rw [hzr, hF2, hrr, hrz, hzz] at hnorm
    rw [hF2]
    linarith only [hnorm, hc1, hc2, hc3]

theorem recCutoffW_bounds {C h ρ lam rc zc : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hcz : rc ^ 2 + zc ^ 2 ≤ ρ ^ 2) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {y : ℝ × ℝ}
    (hy : ‖y‖ < (recCutoffBump h ρ lam hρ1 hlam0).rIn) :
    |recCutoffW h ρ lam rc zc hρ1 hlam0 u y| ≤ 4 * C ∧
      ‖fderiv ℝ (recCutoffW h ρ lam rc zc hρ1 hlam0 u) y‖ ≤ 4 * C ∧
      ‖fderiv ℝ (fderiv ℝ (recCutoffW h ρ lam rc zc hρ1 hlam0 u)) y‖ ≤ 4 * C := by
  have hS := mem_recSliceSet_of_lt_rIn hρ0 hρ1 hcz hlam0 hlam1 hy
  have hSy : zoomPointRec lam h rc zc (y, -1) ∈ unitCylinder := hS
  have hEq := recCutoffW_eventuallyEq (rc := rc) (zc := zc) (u := u) hρ1 hlam0 hy
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1.of_le (by norm_num)
  have hτ : ((y, (-1 : ℝ)) : (ℝ × ℝ) × ℝ).2 ≤ -1 := le_rfl
  obtain ⟨y1, y2⟩ := y
  have hHF := hasFDerivAt_zoomWRec_slice hsol hS
  have hd1 : fderiv ℝ (fun q : ℝ × ℝ => zoomWRec lam h rc zc u (q, -1)) (y1, y2) (1, 0)
      = dr (zoomWRec lam h rc zc u) ((y1, y2), -1) :=
    (dr_eq_of_hasFDerivAt (zoomWRec lam h rc zc u) (-1) hHF).symm
  have hd2 : fderiv ℝ (fun q : ℝ × ℝ => zoomWRec lam h rc zc u (q, -1)) (y1, y2) (0, 1)
      = dz (zoomWRec lam h rc zc u) ((y1, y2), -1) :=
    (dz_eq_of_hasFDerivAt (zoomWRec lam h rc zc u) (-1) hHF).symm
  have hv : |zoomWRec lam h rc zc u ((y1, y2), -1)| ≤ C := by
    have := abs_zoomWRec_add_abs_zoomSRec_le C h lam rc zc hlam0 u hb _ hSy
    have h0 := abs_nonneg (zoomSRec lam h rc zc u ((y1, y2), -1))
    simp only [neg_neg, Real.one_rpow, mul_one] at this
    linarith only [this, h0]
  have hb1 : |dr (zoomWRec lam h rc zc u) ((y1, y2), -1)| ≤ C := by
    have := abs_dr_zoomWRec_add_abs_dr_zoomSRec_le C h lam rc zc hlam0 u hb hu2 _ hSy
    have h0 := abs_nonneg (dr (zoomSRec lam h rc zc u) ((y1, y2), -1))
    simp only [neg_neg, Real.one_rpow, mul_one] at this
    linarith only [this, h0]
  have hb2 : |dz (zoomWRec lam h rc zc u) ((y1, y2), -1)| ≤ C := by
    have := abs_dz_zoomWRec_add_abs_dz_zoomSRec_le C h lam rc zc hlam0 u hb hu2 _ hSy
    have h0 := abs_nonneg (dz (zoomSRec lam h rc zc u) ((y1, y2), -1))
    simp only [neg_neg, Real.one_rpow, mul_one] at this
    linarith only [this, h0]
  have hF1 : fderiv ℝ (recCutoffW h ρ lam rc zc hρ1 hlam0 u) (y1, y2)
      = fderiv ℝ (fun q : ℝ × ℝ => zoomWRec lam h rc zc u (q, -1)) (y1, y2) := hEq.fderiv_eq
  have hF2 : fderiv ℝ (fderiv ℝ (recCutoffW h ρ lam rc zc hρ1 hlam0 u)) (y1, y2)
      = fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => zoomWRec lam h rc zc u (q, -1))) (y1, y2) :=
    hEq.fderiv.fderiv_eq
  refine ⟨?_, ?_, ?_⟩
  · rw [hEq.eq_of_nhds]; linarith only [hv, hC]
  · have hnorm := norm_clm_le_norm_apply_add_norm_apply
      (fderiv ℝ (fun q : ℝ × ℝ => zoomWRec lam h rc zc u (q, -1)) (y1, y2))
    rw [hd1, hd2, Real.norm_eq_abs, Real.norm_eq_abs] at hnorm
    rw [hF1]; linarith only [hnorm, hb1, hb2, hC]
  · have hCD := contDiff_recCutoffW (h := h) hρ0 hρ1 hcz hlam0 hlam1 (rc := rc) (zc := zc) hsol
    have hzr := fderiv_fderiv_apply_axial_radial_eq_of_contDiff hCD (y1, y2)
    have hopen := isOpen_recSliceSet lam h rc zc
    have hrr := fderiv_fderiv_apply_radial_radial_eq_drdr hopen
      (contDiffOn_zoomWRec_slice (lam := lam) (h := h) (rc := rc) (zc := zc) hsol) hS
    have hrz := fderiv_fderiv_apply_radial_axial_eq_drdz hopen
      (contDiffOn_zoomWRec_slice (lam := lam) (h := h) (rc := rc) (zc := zc) hsol) hS
    have hzz := fderiv_fderiv_apply_axial_axial_eq_dzdz hopen
      (contDiffOn_zoomWRec_slice (lam := lam) (h := h) (rc := rc) (zc := zc) hsol) hS
    have hc1 : |dr (dr (zoomWRec lam h rc zc u)) ((y1, y2), -1)| ≤ C := by
      simpa using abs_drdr_zoomWRec_le_rpow_neg_half hlam0 hb hu2 hSy hC hh0 hτ
    have hc2 : |dr (dz (zoomWRec lam h rc zc u)) ((y1, y2), -1)| ≤ C := by
      simpa using abs_drdz_zoomWRec_le_rpow_neg_half hlam0 hb hu2 hSy hC hτ
    have hc3 : |dz (dz (zoomWRec lam h rc zc u)) ((y1, y2), -1)| ≤ C := by
      simpa using abs_dzdz_zoomWRec_le_rpow_neg_half hlam0 hb hu2 hSy hC hh1.le hτ
    have hnorm := norm_fderiv_fderiv_le_of_apply (recCutoffW h ρ lam rc zc hρ1 hlam0 u) (y1, y2)
    rw [hzr, hF2, hrr, hrz, hzz] at hnorm
    rw [hF2]
    linarith only [hnorm, hc1, hc2, hc3]

/-! ### The contradiction -/

/-- Every point of `planeRectangle j` has sup norm at most `j + 1`. -/
theorem norm_le_of_mem_planeRectangle {j : ℕ} {y : ℝ × ℝ} (hy : y ∈ planeRectangle j) :
    ‖y‖ ≤ (j : ℝ) + 1 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (abs_le.mpr ⟨hy.1.1, hy.1.2⟩) (abs_le.mpr ⟨hy.2.1, hy.2.2⟩)

/-- The receding-axis branch of the selection of `eq:aniso:zoom:selected` is contradictory once
the rescaled azimuthal vorticity about the selected points `x_n = (x₁ n, x₃ n)`, at scale
`λ_n = √(-t_n)`, tends to zero at every point of `{τ = -1}`. -/
theorem false_of_real_receding_selection {C h ρ : ℝ} (hC : 0 ≤ C) (hh0 : 0 < h)
    (hh1 : h < 1 / 2) (hρ : ρ < 1) {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hb : AnisotropicBounds C h u) {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {c₀ : ℝ} (hc₀ : 0 < c₀) {t x₁ x₃ : ℕ → ℝ}
    (htlim : Tendsto t atTop (nhds 0))
    (hmem : ∀ n, meridional (x₁ n) (x₃ n) ∈ vec3Ball (0 : Vec3) ρ)
    (htmem : ∀ n, t n ∈ Set.Ioo (-1 : ℝ) 0)
    (hineq : ∀ n, c₀ < (-(t n)) *
        (|spatialPartial (fun w => u w 0) 0 (meridional (x₁ n) (x₃ n), t n)| +
          |radialQuotient u (meridional (x₁ n) (x₃ n), t n)| +
          |spatialPartial (fun w => u w 2) 2 (meridional (x₁ n) (x₃ n), t n)|))
    (hA : Tendsto (fun n => x₁ n / Real.sqrt (-(t n))) atTop atTop)
    (hΘ0 : ∀ q : ℝ × ℝ,
      Tendsto (fun n => zoomTheta (Real.sqrt (-(t n))) h (x₁ n) (x₃ n) u (q, -1)) atTop
        (nhds 0)) :
    False := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  set lam : ℕ → ℝ := fun n => Real.sqrt (-(t n)) with hlam_def
  have hlam0 : ∀ n, 0 < lam n := fun n => Real.sqrt_pos.mpr (by linarith only [(htmem n).2])
  have hlam1 : ∀ n, lam n < 1 := fun n => by
    rw [hlam_def, Real.sqrt_lt' one_pos]; linarith only [(htmem n).1]
  have hlamsq : ∀ n, lam n ^ 2 = -(t n) := fun n => Real.sq_sqrt (by linarith only [(htmem n).2])
  have hlamT : Tendsto lam atTop (nhds 0) := by
    have : Tendsto (fun n => Real.sqrt (-(t n))) atTop (nhds (Real.sqrt (-0))) :=
      (htlim.neg).sqrt
    simpa using this
  have hcz : ∀ n, x₁ n ^ 2 + x₃ n ^ 2 ≤ ρ ^ 2 := fun n =>
    ((meridional_mem_vec3Ball_zero_iff _ _ _).mp (hmem n)).1.le
  have hρ0 : 0 ≤ ρ := ((meridional_mem_vec3Ball_zero_iff _ _ _).mp (hmem 0)).2.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hA.eventually_gt_atTop 0)
  have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop := tendsto_add_atTop_nat N
  -- the shifted data
  set lam' : ℕ → ℝ := fun n => lam (n + N) with hlam'
  have hlam0' : ∀ n, 0 < lam' n := fun n => hlam0 (n + N)
  have hlamT' : Tendsto lam' atTop (nhds 0) := hlamT.comp hshift
  set A : ℕ → ℝ := fun n => x₁ (n + N) / lam' n with hAdef
  have hApos : ∀ n, 0 < A n := fun n => hN (n + N) (Nat.le_add_left N n)
  have hAtop : Tendsto A atTop atTop := hA.comp hshift
  set Vseq : ℕ → ℝ × ℝ → ℝ := fun n =>
    recCutoffV h ρ (lam' n) (x₁ (n + N)) (x₃ (n + N)) hρ (hlam0' n) u with hVdef
  set Wseq : ℕ → ℝ × ℝ → ℝ := fun n =>
    recCutoffW h ρ (lam' n) (x₁ (n + N)) (x₃ (n + N)) hρ (hlam0' n) u with hWdef
  have hin : ∀ r : ℝ, ∀ᶠ n in atTop, r < (recCutoffBump h ρ (lam' n) hρ (hlam0' n)).rIn :=
    eventually_lt_recCutoffBump_rIn hh1 hρ hlam0' hlamT'
  -- raw data at a point of the inner ball
  have hraw : ∀ n, ∀ p : ℝ × ℝ, ‖p‖ < (recCutoffBump h ρ (lam' n) hρ (hlam0' n)).rIn →
      zoomPointRec (lam' n) h (x₁ (n + N)) (x₃ (n + N)) (p, -1) ∈ unitCylinder ∧
      Vseq n p = zoomVRec (lam' n) h (x₁ (n + N)) (x₃ (n + N)) u (p, -1) ∧
      Wseq n p = zoomWRec (lam' n) h (x₁ (n + N)) (x₃ (n + N)) u (p, -1) ∧
      fderiv ℝ (Vseq n) p (1, 0) = dr (zoomVRec (lam' n) h (x₁ (n + N)) (x₃ (n + N)) u) (p, -1) ∧
      fderiv ℝ (Wseq n) p (1, 0) = dr (zoomWRec (lam' n) h (x₁ (n + N)) (x₃ (n + N)) u) (p, -1) ∧
      fderiv ℝ (Wseq n) p (0, 1) = dz (zoomWRec (lam' n) h (x₁ (n + N)) (x₃ (n + N)) u) (p, -1)
        := by
    intro n p hp
    have hS := mem_recSliceSet_of_lt_rIn hρ0 hρ (hcz (n + N)) (hlam0' n) (hlam1 (n + N)) hp
    have hEV := recCutoffV_eventuallyEq (rc := x₁ (n + N)) (zc := x₃ (n + N)) (u := u) hρ
      (hlam0' n) hp
    have hEW := recCutoffW_eventuallyEq (rc := x₁ (n + N)) (zc := x₃ (n + N)) (u := u) hρ
      (hlam0' n) hp
    obtain ⟨p1, p2⟩ := p
    have hFV := hasFDerivAt_zoomVRec_slice hsol hS
    have hFW := hasFDerivAt_zoomWRec_slice hsol hS
    refine ⟨hS, hEV.eq_of_nhds, hEW.eq_of_nhds, ?_, ?_, ?_⟩
    · rw [hEV.fderiv_eq]; exact (dr_eq_of_hasFDerivAt _ (-1) hFV).symm
    · rw [hEW.fderiv_eq]; exact (dr_eq_of_hasFDerivAt _ (-1) hFW).symm
    · rw [hEW.fderiv_eq]; exact (dz_eq_of_hasFDerivAt _ (-1) hFW).symm
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  refine step_receding_contradiction (L := 4 * C) hc₀ (by linarith only [hC]) hAtop hApos
    Vseq Wseq
    (fun n => contDiff_recCutoffV hρ0 hρ (hcz (n + N)) (hlam0' n) (hlam1 (n + N)) hsol)
    (fun n => contDiff_recCutoffW hρ0 hρ (hcz (n + N)) (hlam0' n) (hlam1 (n + N)) hsol)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    filter_upwards [hin ((j : ℝ) + 2)] with n hn y hy
    exact recCutoffV_bounds hC hh1 hρ0 hρ (hcz (n + N)) (hlam0' n) (hlam1 (n + N)) hb hsol
      (by linarith only [norm_le_of_mem_planeRectangle hy, hn])
  · intro j
    filter_upwards [hin ((j : ℝ) + 2)] with n hn y hy
    exact recCutoffW_bounds hC hh0.le hh1 hρ0 hρ (hcz (n + N)) (hlam0' n) (hlam1 (n + N)) hb hsol
      (by linarith only [norm_le_of_mem_planeRectangle hy, hn])
  · intro p
    filter_upwards [hin (‖p‖ + 1), hAtop.eventually_gt_atTop (-p.1)] with n hn hAn
    obtain ⟨hS, hV, -, hdV, -, hdW⟩ := hraw n p (by linarith only [hn])
    have hR : p.1 ≠ -(x₁ (n + N) / lam' n) := by
      intro hc; simp only [hAdef] at hAn; linarith only [hAn, hc]
    obtain ⟨p1, p2⟩ := p
    have hdiv := zoomRec_divergence_identity (lam' n) h (x₁ (n + N)) (x₃ (n + N)) (hlam0' n) u
      pres f hsol haxi ((p1, p2), -1) hS hR
    rw [hdV, hV, hdW]
    simpa [hAdef] using hdiv
  · intro p
    have hAp : Tendsto (fun n => A n + p.1) atTop atTop := tendsto_atTop_add_const_right _ _ hAtop
    have hlim : Tendsto (fun n => 4 * C / (A n + p.1)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hAp
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hin (‖p‖ + 1), hAp.eventually_gt_atTop 0] with n hn hpos
    have hbd := (recCutoffV_bounds hC hh1 hρ0 hρ (hcz (n + N)) (hlam0' n) (hlam1 (n + N)) hb hsol
      (y := p) (by linarith only [hn])).1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right hbd hpos.le
  · intro p
    have hΘ : Tendsto (fun n => zoomTheta (lam' n) h (x₁ (n + N)) (x₃ (n + N)) u (p, -1)) atTop
        (nhds 0) := (hΘ0 p).comp hshift
    have hlamW : Tendsto lam' atTop (nhdsWithin 0 (Ioi 0)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlamT', Eventually.of_forall hlam0'⟩
    have hδ := (tendsto_zoomDeltaSq_nhdsWithin_zero hh0).comp hlamW
    have hδC : Tendsto (fun n => C * (lam' n ^ (2 * h)) ^ 2) atTop (nhds 0) := by
      simpa using hδ.const_mul C
    have hmem_ev : ∀ᶠ n in atTop,
        zoomPointRec (lam' n) h (x₁ (n + N)) (x₃ (n + N)) (p, -1) ∈ unitCylinder := by
      filter_upwards [hin (‖p‖ + 1)] with n hn
      exact (hraw n p (by linarith only [hn])).1
    have hfirst : Tendsto (fun n => (lam' n ^ (2 * h)) ^ 2 *
        dz (zoomVRec (lam' n) h (x₁ (n + N)) (x₃ (n + N)) u) (p, -1)) atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ hδC
      filter_upwards [hmem_ev] with n hn
      have hdz : |dz (zoomVRec (lam' n) h (x₁ (n + N)) (x₃ (n + N)) u) (p, -1)| ≤ C := by
        simpa using abs_dz_zoomVRec_le C h (lam' n) (x₁ (n + N)) (x₃ (n + N)) (hlam0' n) u hb
          hu2 (p, -1) hn
      have hδ0 : 0 ≤ (lam' n ^ (2 * h)) ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hδ0, mul_comm C]
      exact mul_le_mul_of_nonneg_left hdz hδ0
    have hsum := hfirst.sub hΘ
    rw [sub_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [hin (‖p‖ + 1)] with n hn
    obtain ⟨hS, -, -, -, hdW, -⟩ := hraw n p (by linarith only [hn])
    rw [hdW, zoomTheta_eq (lam' n) h (x₁ (n + N)) (x₃ (n + N)) (hlam0' n) u hu1 (p, -1) hS]
    ring
  · intro n
    have h0 : ‖((0 : ℝ), (0 : ℝ))‖ < (recCutoffBump h ρ (lam' n) hρ (hlam0' n)).rIn := by
      simpa using (recCutoffBump h ρ (lam' n) hρ (hlam0' n)).rIn_pos
    obtain ⟨hS, hV, -, hdV, -, hdW⟩ := hraw n (0, 0) h0
    have hR : (0 : ℝ) ≠ -(x₁ (n + N) / lam' n) := by
      have := hApos n; simp only [hAdef] at this; intro hc; linarith only [this, hc]
    have hid := neg_t_mul_meridionalQuantity_receding_selection_eq (h := h) hu1
      (htmem (n + N)).2 (hlam0' n) hR (hlamsq (n + N)) hS
    simp only [mul_zero, add_zero] at hid
    have hi := hineq (n + N)
    rw [hid] at hi
    rw [hdV, hV, hdW]
    have hle := hi.le
    rw [abs_div] at hle
    have hA' : |x₁ (n + N) / lam' n| = A n := abs_of_pos (hApos n)
    rw [hA'] at hle
    exact hle

end CIV
