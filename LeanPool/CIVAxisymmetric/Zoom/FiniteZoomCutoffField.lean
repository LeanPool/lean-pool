/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RescaledBounds
public import LeanPool.CIVAxisymmetric.Zoom.VBoundedRectangle
public import LeanPool.CIVAxisymmetric.Zoom.DivergenceIdentity
public import LeanPool.CIVAxisymmetric.Zoom.FiniteAxisBounds
public import LeanPool.CIVAxisymmetric.Zoom.EndpointFiniteAxis
public import LeanPool.CIVAxisymmetric.Setting.AngularMeanSmooth
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The cutoff adapter: globally smooth fields agreeing with the zoom slices on growing squares

`CIV.step_finite_contradiction` (`FiniteContradictionClosure.lean`) asks for a sequence of
meridional fields `Vseq`, `Wseq : ℕ → ℝ × ℝ → ℝ` that is `ContDiff ℝ (⊤ : ℕ∞)` on **all** of `ℝ × ℝ`
for **every** `n`. The actual finite-axis zoom fields `zoomV (lam n) h (zc n) u (·, -1)`,
`zoomW (lam n) h (zc n) u (·, -1)` are smooth only on the preimage of `unitCylinder` under the
zoom map at scale `lam n`, a bounded region whose size grows without bound only as
`lam n → 0` (no *single* positive scale covers an unbounded region). This file builds the
repair: for each `n`, a smooth cutoff supported strictly inside
that preimage, equal to `1` on a square that grows without bound as `lam n → 0`, whose product
with the zoom slice is globally smooth (`ContDiff ℝ (⊤ : ℕ∞)` on the *whole* plane, for every `n`,
not merely eventually) because the product is identically zero on a neighbourhood of every
point outside the cutoff's support, regardless of how the raw slice behaves there.

The zoom centre is a sequence `zc : ℕ → ℝ`, one axial offset per stage, uniformly bounded by a
single `ζ < 1`: the paper zooms about the moving pair `(0, z_n)`, so a single fixed centre
cannot be fed the selected data of `CIV.exists_seq_three_terms_dichotomy`, whose third output
is itself a sequence of heights.

The cutoff is a plain Mathlib `ContDiffBump` centred at the origin of `ℝ × ℝ`, which carries
the sup norm (`Prod.norm_def`) — the same norm `CIV.halfPlaneRectangle`'s squares use — so no
Euclidean/sup conversion factor is needed anywhere in this file.
-/

public section

open Set Filter Topology Metric
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### The safe radius: an explicit sup-square inside the preimage of `unitCylinder` -/

/-- If a square of sup-radius `r` around the origin satisfies `lam ^ (1 - 2h) * r ≤ (1 - |zc|)
/ 2`, every point of that square zooms, at the frozen time `τ = -1`, into `unitCylinder`. The
margin `(1 - |zc|) / 2` is what is left over from the standing bound `|zc| < 1` after the
meridional radius and the axial offset are each kept below it; the algebra is the same
splitting used in `CIV.eventually_zoomPoint_mem_unitCylinder`, specialised to an explicit
radius instead of an asymptotic filter. -/
theorem zoomPoint_mem_unitCylinder_of_norm_le {h zc lam r : ℝ} (hh0 : 0 ≤ h)
    (hzc : |zc| < 1) (hlam0 : 0 < lam) (hlam1 : lam < 1) (hr : lam ^ (1 - 2 * h) * r ≤ (1 -
      |zc|) / 2)
    {q : ℝ × ℝ} (hq : ‖q‖ ≤ r) :
    zoomPoint lam h zc (q, -1) ∈ unitCylinder := by
  have hnorm : ‖q‖ = max |q.1| |q.2| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have hq1 : |q.1| ≤ r := by
    have : |q.1| ≤ ‖q‖ := by rw [hnorm]; exact le_max_left _ _
    linarith only [this, hq]
  have hq2 : |q.2| ≤ r := by
    have : |q.2| ≤ ‖q‖ := by rw [hnorm]; exact le_max_right _ _
    linarith only [this, hq]
  have hr0 : 0 ≤ r := (abs_nonneg q.1).trans hq1
  have hrpow_nonneg : 0 ≤ lam ^ (1 - 2 * h) := Real.rpow_nonneg hlam0.le _
  have hlam_le : lam ≤ lam ^ (1 - 2 * h) := by
    have hle := Real.rpow_le_rpow_of_exponent_ge hlam0 hlam1.le
      (show (1 - 2 * h) ≤ (1 : ℝ) by linarith only [hh0])
    simpa using hle
  have habs1 : |lam * q.1| ≤ (1 - |zc|) / 2 := by
    rw [abs_mul, abs_of_pos hlam0]
    have h1 : lam * |q.1| ≤ lam ^ (1 - 2 * h) * r := by nlinarith only [hq1, hlam0, hlam_le, hr0]
    linarith only [h1, hr]
  have habs2 : |lam ^ (1 - 2 * h) * q.2| ≤ (1 - |zc|) / 2 := by
    rw [abs_mul, abs_of_nonneg hrpow_nonneg]
    have h1 : lam ^ (1 - 2 * h) * |q.2| ≤ lam ^ (1 - 2 * h) * r :=
      mul_le_mul_of_nonneg_left hq2 hrpow_nonneg
    linarith only [h1, hr]
  have hsq1 : (lam * q.1) ^ 2 ≤ ((1 - |zc|) / 2) ^ 2 := by
    have hp := pow_le_pow_left₀ (abs_nonneg _) habs1 2
    rwa [sq_abs] at hp
  have habs3 : |zc + lam ^ (1 - 2 * h) * q.2| ≤ |zc| + (1 - |zc|) / 2 :=
    (abs_add_le zc (lam ^ (1 - 2 * h) * q.2)).trans (by linarith only [habs2])
  have hsq2 : (zc + lam ^ (1 - 2 * h) * q.2) ^ 2 ≤ (|zc| + (1 - |zc|) / 2) ^ 2 := by
    have hp := pow_le_pow_left₀ (abs_nonneg _) habs3 2
    rwa [sq_abs] at hp
  have ha2 : |zc| ^ 2 < 1 := by nlinarith only [hzc, abs_nonneg zc]
  have hfinal : ((1 - |zc|) / 2) ^ 2 + (|zc| + (1 - |zc|) / 2) ^ 2 < 1 := by nlinarith only [ha2]
  rw [zoomPoint_mem_unitCylinder_iff]
  refine ⟨by nlinarith only [hsq1, hsq2, hfinal], ?_, ?_⟩
  · nlinarith only [hlam0, hlam1]
  · nlinarith only [hlam0]

/-! ### A bump-multiplied local field is globally smooth -/

/-- A bump function whose closed outer ball lies inside an open set on which `g` is smooth
gives a globally smooth product. At a point of the open set both factors are smooth there; at
a point outside the bump's outer ball the product is identically zero on a neighbourhood
(because the bump itself is, `ContDiffBump.zero_of_le_dist`), regardless of `g`'s behaviour
there — `g` need not even be continuous outside the open set. -/
theorem contDiff_bump_mul_of_contDiffOn_of_subset_closedBall
    (bump : ContDiffBump (0 : ℝ × ℝ)) {g : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} (hSopen : IsOpen S)
    (hgS : ContDiffOn ℝ (⊤ : ℕ∞) g S) (hsub : closedBall (0 : ℝ × ℝ) bump.rOut ⊆ S) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => bump q * g q) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : q ∈ S
  · exact bump.contDiff.contDiffAt.mul (hgS.contDiffAt (hSopen.mem_nhds hq))
  · have hqOut : bump.rOut < ‖q‖ := by
      by_contra hcon
      refine hq (hsub ?_)
      rw [mem_closedBall, dist_eq_norm, sub_zero]
      linarith only [not_lt.mp hcon]
    have hopenOut : IsOpen {q' : ℝ × ℝ | bump.rOut < ‖q'‖} :=
      isOpen_lt continuous_const continuous_norm
    have hzero : (fun q' : ℝ × ℝ => bump q' * g q') =ᶠ[nhds q] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopenOut.mem_nhds hqOut] with q' hq'
      have hb0 : bump q' = 0 := bump.zero_of_le_dist (by
        rw [dist_eq_norm, sub_zero]; exact hq'.le)
      rw [hb0]; ring
    exact contDiffAt_const.congr_of_eventuallyEq hzero

/-! ### The cutoff attached to a zoom scale -/

/-- The cutoff attached to the scale `lam`, stage `n` of the axial-offset sequence `zc`
(uniformly bounded by `ζ < 1` through `hzc`), and the vertical exponent `h`: its outer radius
`(1 - |zc n|) / (2 lam ^ (1 - 2h))` is exactly the radius at which
`zoomPoint_mem_unitCylinder_of_norm_le` certifies safety, so its closed outer ball lies inside
the preimage of `unitCylinder`; its inner radius is half of that, so it equals `1` on the
sup-square of that half-radius. -/
@[expose] def cutoffBump (h : ℝ) (zc : ℕ → ℝ) {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) (lam : ℝ)
    (hlam0 : 0 < lam) (n : ℕ) : ContDiffBump (0 : ℝ × ℝ) where
  rIn := (1 - |zc n|) / (4 * lam ^ (1 - 2 * h))
  rOut := (1 - |zc n|) / (2 * lam ^ (1 - 2 * h))
  rIn_pos := by
    have h1 : (0 : ℝ) < 1 - |zc n| := by linarith only [(hzc n).trans_lt hζ]
    have h2 : (0 : ℝ) < lam ^ (1 - 2 * h) := Real.rpow_pos_of_pos hlam0 _
    exact div_pos h1 (by linarith only [h2])
  rIn_lt_rOut := by
    have h1 : (0 : ℝ) < 1 - |zc n| := by linarith only [(hzc n).trans_lt hζ]
    have h2 : (0 : ℝ) < lam ^ (1 - 2 * h) := Real.rpow_pos_of_pos hlam0 _
    exact (div_lt_div_iff_of_pos_left h1 (by linarith only [h2]) (by linarith only [h2])).mpr
      (by linarith only [h2])

theorem cutoffBump_rOut (h : ℝ) (zc : ℕ → ℝ) {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1)
    (lam : ℝ) (hlam0 : 0 < lam) (n : ℕ) :
    (cutoffBump h zc hzc hζ lam hlam0 n).rOut = (1 - |zc n|) / (2 * lam ^ (1 - 2 * h)) := rfl

theorem cutoffBump_rIn (h : ℝ) (zc : ℕ → ℝ) {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1)
    (lam : ℝ) (hlam0 : 0 < lam) (n : ℕ) :
    (cutoffBump h zc hzc hζ lam hlam0 n).rIn = (1 - |zc n|) / (4 * lam ^ (1 - 2 * h)) := rfl

/-- The cutoff's outer radius is exactly the safe radius, so its closed outer ball lies
inside the preimage of `unitCylinder` at the frozen time `τ = -1`, at the stage-`n` centre
`zc n`. -/
theorem cutoffBump_safe {h : ℝ} (hh0 : 0 ≤ h) {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ)
    (hζ : ζ < 1) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (n : ℕ) :
    closedBall (0 : ℝ × ℝ) (cutoffBump h zc hzc hζ lam hlam0 n).rOut ⊆
      {q : ℝ × ℝ | zoomPoint lam h (zc n) (q, -1) ∈ unitCylinder} := by
  intro q hq
  rw [mem_closedBall, dist_eq_norm, sub_zero] at hq
  refine zoomPoint_mem_unitCylinder_of_norm_le hh0 ((hzc n).trans_lt hζ) hlam0 hlam1 ?_ hq
  rw [cutoffBump_rOut]
  have h2 : (0 : ℝ) < lam ^ (1 - 2 * h) := Real.rpow_pos_of_pos hlam0 _
  have heq : lam ^ (1 - 2 * h) * ((1 - |zc n|) / (2 * lam ^ (1 - 2 * h))) = (1 - |zc n|) / 2 := by
    field_simp
  exact heq.le

/-- As the scale `lam` tends to `0` the cutoff's inner radius grows without bound, uniformly
over the stage `n`: for every target square radius `r`, eventually (for `lam n` small) the
inner radius at stage `n` exceeds `r`, so the cutoff equals `1` throughout that square
(`ContDiffBump.eventuallyEq_one_of_mem_ball` gives it pointwise; the radius bound gives every
point of the square membership in that inner ball). Only the shared bound `ζ` on `|zc n|` is
used, so the bound is uniform over the whole moving sequence at once. -/
theorem eventually_cutoffBump_rIn_gt {h : ℝ} (hh1 : h < 1 / 2) {zc : ℕ → ℝ} {ζ : ℝ}
    (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n)
    (hlamTendsto : Tendsto lam atTop (nhds 0)) (r : ℝ) :
    ∀ᶠ n in atTop, r < (cutoffBump h zc hzc hζ (lam n) (hlam0 n) n).rIn := by
  have hexp : (0 : ℝ) < 1 - 2 * h := by linarith only [hh1]
  have hrpow : Tendsto (fun n => (lam n) ^ (1 - 2 * h)) atTop (nhds ((0 : ℝ) ^ (1 - 2 * h))) :=
    (Real.continuousAt_rpow_const 0 (1 - 2 * h) (Or.inr hexp.le)).tendsto.comp hlamTendsto
  rw [Real.zero_rpow hexp.ne'] at hrpow
  have hmargin : (0 : ℝ) < (1 - ζ) / 4 := by linarith only [hζ]
  have hrIn_ge : ∀ n, (1 - ζ) / (4 * lam n ^ (1 - 2 * h)) ≤
      (cutoffBump h zc hzc hζ (lam n) (hlam0 n) n).rIn := by
    intro n
    rw [cutoffBump_rIn]
    have h2 : (0 : ℝ) ≤ 4 * lam n ^ (1 - 2 * h) := by
      have := Real.rpow_nonneg (hlam0 n).le (1 - 2 * h)
      linarith only [this]
    exact div_le_div_of_nonneg_right (by linarith only [hzc n]) h2
  by_cases hr0 : r ≤ 0
  · refine Filter.Eventually.of_forall (fun n => ?_)
    have h2 : (0 : ℝ) < lam n ^ (1 - 2 * h) := Real.rpow_pos_of_pos (hlam0 n) _
    have hrIn : (0 : ℝ) < (1 - ζ) / (4 * lam n ^ (1 - 2 * h)) :=
      div_pos (by linarith only [hζ]) (by linarith only [h2])
    linarith only [hr0, hrIn, hrIn_ge n]
  · have hr0' : (0 : ℝ) < r := not_le.mp hr0
    have hc : ∀ᶠ n in atTop, lam n ^ (1 - 2 * h) < (1 - ζ) / (4 * r) := by
      have hpos : (0 : ℝ) < (1 - ζ) / (4 * r) := div_pos (by linarith only [hζ]) (by
        linarith only [hr0'])
      have := hrpow.eventually_lt_const hpos
      simpa using this
    filter_upwards [hc] with n hn
    have h2 : (0 : ℝ) < lam n ^ (1 - 2 * h) := Real.rpow_pos_of_pos (hlam0 n) _
    have hstep : r < (1 - ζ) / (4 * lam n ^ (1 - 2 * h)) := by
      rw [lt_div_iff₀ (show (0 : ℝ) < 4 * lam n ^ (1 - 2 * h) by linarith only [h2])]
      rw [lt_div_iff₀ (show (0 : ℝ) < 4 * r by linarith only [hr0'])] at hn
      nlinarith only [hn]
    linarith only [hstep, hrIn_ge n]

end CIV
