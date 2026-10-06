/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteZoomCutoffBounds
public import LeanPool.CIVAxisymmetric.Zoom.FiniteAxisSecondDerivativeBoundsV
public import LeanPool.CIVAxisymmetric.Zoom.FiniteAxisSecondDerivativeBoundsW
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The second Fréchet derivative of a raw zoom slice, read off nested `dr`/`dz`

`CIV.step_finite_contradiction` needs `‖fderiv ℝ (fderiv ℝ (Vseq n)) y‖ ≤ L`. This file supplies
the bridge between that operator norm and the pointwise second-order bounds
`CIV.abs_drdr_zoomV_le_rpow_neg_half` etc.: on the open set where a space-time field's time
slice is `ContDiff ℝ (⊤ : ℕ∞)`, the three independent entries of its second derivative are
exactly `dr (dr ·)`, `dr (dz ·)`, `dz (dz ·)` evaluated at the frozen time, and the fourth
(`dz (dr ·)`) agrees with `dr (dz ·)` by symmetry of the second derivative
(`second_derivative_symmetric`) — so no separate bound on it is needed.
-/

public section

open Set Filter Topology Metric
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### `HasFDerivAt` for a field and its derivative, on an open set -/

/-- On an open set where a time slice is `ContDiff ℝ (⊤ : ℕ∞)`, both the slice and its own
Fréchet derivative have a `HasFDerivAt` at every point of the set, reading `fderiv` at that
point as their respective derivatives. -/
theorem hasFDerivAt_and_hasFDerivAt_fderiv_of_contDiffOn {g : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g S) {y : ℝ × ℝ} (hy : y ∈ S) :
    HasFDerivAt g (fderiv ℝ g y) y ∧
      HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) y) y := by
  obtain ⟨hdiff1, hg1⟩ := (contDiffOn_infty_iff_fderiv_of_isOpen hS).1 hg
  obtain ⟨hdiff2, -⟩ := (contDiffOn_infty_iff_fderiv_of_isOpen hS).1 hg1
  exact ⟨(hdiff1.differentiableAt (hS.mem_nhds hy)).hasFDerivAt,
    (hdiff2.differentiableAt (hS.mem_nhds hy)).hasFDerivAt⟩

/-! ### The three independent entries of the second derivative -/

/-- The radial-radial entry of the second derivative of a time slice equals `dr (dr φ)` at the
frozen time. -/
theorem fderiv_fderiv_apply_radial_radial_eq_drdr {φ : (ℝ × ℝ) × ℝ → ℝ} {t : ℝ} {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => φ (q, t)) S) {y : ℝ × ℝ}
    (hy : y ∈ S) :
    fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => φ (q, t))) y (1, 0) (1, 0) = dr (dr φ) (y, t) := by
  set g : ℝ × ℝ → ℝ := fun q => φ (q, t) with hgdef
  obtain ⟨-, hFD2⟩ := hasFDerivAt_and_hasFDerivAt_fderiv_of_contDiffOn hS hφ hy
  have hg1 : HasFDerivAt (fun q : ℝ × ℝ => fderiv ℝ g q (1, 0))
      ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))).comp (fderiv ℝ (fderiv ℝ g) y)) y :=
    (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))).hasFDerivAt.comp y hFD2
  have hg1' : HasDerivAt (fun r : ℝ => fderiv ℝ g (r, y.2) (1, 0))
      (fderiv ℝ (fderiv ℝ g) y (1, 0) (1, 0)) y.1 := by
    have h := hasDerivAt_radial_of_hasFDerivAt (f := fun q : ℝ × ℝ => fderiv ℝ g q (1, 0)) hg1
    simpa using h
  have heqOn : ∀ r : ℝ, (r, y.2) ∈ S → fderiv ℝ g (r, y.2) (1, 0) = dr φ ((r, y.2), t) := by
    intro r hr
    have hHF : HasFDerivAt g (fderiv ℝ g (r, y.2)) (r, y.2) :=
      ((hasFDerivAt_and_hasFDerivAt_fderiv_of_contDiffOn hS hφ hr).1)
    exact (dr_eq_of_hasFDerivAt φ t hHF).symm
  have hSy : IsOpen {r : ℝ | (r, y.2) ∈ S} := hS.preimage (continuous_id.prodMk continuous_const)
  have hmemy : y.1 ∈ {r : ℝ | (r, y.2) ∈ S} := by simpa using hy
  have heqNhds : (fun r : ℝ => fderiv ℝ g (r, y.2) (1, 0)) =ᶠ[nhds y.1]
      (fun r : ℝ => dr φ ((r, y.2), t)) := by
    filter_upwards [hSy.mem_nhds hmemy] with r hr using heqOn r hr
  have hfinal : HasDerivAt (fun r : ℝ => dr φ ((r, y.2), t))
      (fderiv ℝ (fderiv ℝ g) y (1, 0) (1, 0)) y.1 :=
    hg1'.congr_of_eventuallyEq heqNhds.symm
  show fderiv ℝ (fderiv ℝ g) y (1, 0) (1, 0) = dr (dr φ) (y, t)
  rw [← hfinal.deriv]
  rfl

/-- The radial-axial entry of the second derivative of a time slice equals `dr (dz φ)` at the
frozen time. -/
theorem fderiv_fderiv_apply_radial_axial_eq_drdz {φ : (ℝ × ℝ) × ℝ → ℝ} {t : ℝ} {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => φ (q, t)) S) {y : ℝ × ℝ}
    (hy : y ∈ S) :
    fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => φ (q, t))) y (1, 0) (0, 1) = dr (dz φ) (y, t) := by
  set g : ℝ × ℝ → ℝ := fun q => φ (q, t) with hgdef
  obtain ⟨-, hFD2⟩ := hasFDerivAt_and_hasFDerivAt_fderiv_of_contDiffOn hS hφ hy
  have hg2 : HasFDerivAt (fun q : ℝ × ℝ => fderiv ℝ g q (0, 1))
      ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).comp (fderiv ℝ (fderiv ℝ g) y)) y :=
    (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).hasFDerivAt.comp y hFD2
  have hg2' : HasDerivAt (fun r : ℝ => fderiv ℝ g (r, y.2) (0, 1))
      (fderiv ℝ (fderiv ℝ g) y (1, 0) (0, 1)) y.1 := by
    have h := hasDerivAt_radial_of_hasFDerivAt (f := fun q : ℝ × ℝ => fderiv ℝ g q (0, 1)) hg2
    simpa using h
  have heqOn : ∀ r : ℝ, (r, y.2) ∈ S → fderiv ℝ g (r, y.2) (0, 1) = dz φ ((r, y.2), t) := by
    intro r hr
    have hHF : HasFDerivAt g (fderiv ℝ g (r, y.2)) (r, y.2) :=
      ((hasFDerivAt_and_hasFDerivAt_fderiv_of_contDiffOn hS hφ hr).1)
    exact (dz_eq_of_hasFDerivAt φ t hHF).symm
  have hSy : IsOpen {r : ℝ | (r, y.2) ∈ S} := hS.preimage (continuous_id.prodMk continuous_const)
  have hmemy : y.1 ∈ {r : ℝ | (r, y.2) ∈ S} := by simpa using hy
  have heqNhds : (fun r : ℝ => fderiv ℝ g (r, y.2) (0, 1)) =ᶠ[nhds y.1]
      (fun r : ℝ => dz φ ((r, y.2), t)) := by
    filter_upwards [hSy.mem_nhds hmemy] with r hr using heqOn r hr
  have hfinal : HasDerivAt (fun r : ℝ => dz φ ((r, y.2), t))
      (fderiv ℝ (fderiv ℝ g) y (1, 0) (0, 1)) y.1 :=
    hg2'.congr_of_eventuallyEq heqNhds.symm
  show fderiv ℝ (fderiv ℝ g) y (1, 0) (0, 1) = dr (dz φ) (y, t)
  rw [← hfinal.deriv]
  rfl

/-- The axial-axial entry of the second derivative of a time slice equals `dz (dz φ)` at the
frozen time. -/
theorem fderiv_fderiv_apply_axial_axial_eq_dzdz {φ : (ℝ × ℝ) × ℝ → ℝ} {t : ℝ} {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => φ (q, t)) S) {y : ℝ × ℝ}
    (hy : y ∈ S) :
    fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => φ (q, t))) y (0, 1) (0, 1) = dz (dz φ) (y, t) := by
  set g : ℝ × ℝ → ℝ := fun q => φ (q, t) with hgdef
  obtain ⟨-, hFD2⟩ := hasFDerivAt_and_hasFDerivAt_fderiv_of_contDiffOn hS hφ hy
  have hg2 : HasFDerivAt (fun q : ℝ × ℝ => fderiv ℝ g q (0, 1))
      ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).comp (fderiv ℝ (fderiv ℝ g) y)) y :=
    (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).hasFDerivAt.comp y hFD2
  have hg2' : HasDerivAt (fun z : ℝ => fderiv ℝ g (y.1, z) (0, 1))
      (fderiv ℝ (fderiv ℝ g) y (0, 1) (0, 1)) y.2 := by
    have h := hasDerivAt_axial_of_hasFDerivAt (f := fun q : ℝ × ℝ => fderiv ℝ g q (0, 1)) hg2
    simpa using h
  have heqOn : ∀ z : ℝ, (y.1, z) ∈ S → fderiv ℝ g (y.1, z) (0, 1) = dz φ ((y.1, z), t) := by
    intro z hz
    have hHF : HasFDerivAt g (fderiv ℝ g (y.1, z)) (y.1, z) :=
      ((hasFDerivAt_and_hasFDerivAt_fderiv_of_contDiffOn hS hφ hz).1)
    exact (dz_eq_of_hasFDerivAt φ t hHF).symm
  have hSz : IsOpen {z : ℝ | (y.1, z) ∈ S} := hS.preimage (continuous_const.prodMk continuous_id)
  have hmemz : y.2 ∈ {z : ℝ | (y.1, z) ∈ S} := by simpa using hy
  have heqNhds : (fun z : ℝ => fderiv ℝ g (y.1, z) (0, 1)) =ᶠ[nhds y.2]
      (fun z : ℝ => dz φ ((y.1, z), t)) := by
    filter_upwards [hSz.mem_nhds hmemz] with z hz using heqOn z hz
  have hfinal : HasDerivAt (fun z : ℝ => dz φ ((y.1, z), t))
      (fderiv ℝ (fderiv ℝ g) y (0, 1) (0, 1)) y.2 :=
    hg2'.congr_of_eventuallyEq heqNhds.symm
  show fderiv ℝ (fderiv ℝ g) y (0, 1) (0, 1) = dz (dz φ) (y, t)
  rw [← hfinal.deriv]
  rfl

/-- The fourth (axial-radial) entry agrees with the radial-axial one by symmetry of the second
derivative of a `ContDiff ℝ (⊤ : ℕ∞)` function, so it needs no separate bound. -/
theorem fderiv_fderiv_apply_axial_radial_eq_of_contDiff {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (y : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ g) y (0, 1) (1, 0) = fderiv ℝ (fderiv ℝ g) y (1, 0) (0, 1) := by
  have hf' : ∀ q, HasFDerivAt g (fderiv ℝ g q) q :=
    fun q => ((contDiff_infty_iff_fderiv.mp hg).1 q).hasFDerivAt
  have hfx : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) y) y :=
    ((contDiff_infty_iff_fderiv.mp hg).2.differentiable (by norm_num) y).hasFDerivAt
  exact second_derivative_symmetric hf' hfx (0, 1) (1, 0)

end CIV
