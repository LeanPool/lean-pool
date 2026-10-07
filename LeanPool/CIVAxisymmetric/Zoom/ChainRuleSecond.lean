/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.ChainRule
public import LeanPool.CIVAxisymmetric.Zoom.Rescaling
public import LeanPool.CIVAxisymmetric.Statements.MeridionalPartial
public import LeanPool.CIVAxisymmetric.Identities.PartialSmooth
public import LeanPool.CIVAxisymmetric.Setting.AngularMeanSmooth

/-!
# Second-order zoom chain rules

For `(a,b) ∈ {(2,0),(1,1),(0,2)}` and each of the three rescaled fields `zoomV`, `zoomW`, `zoomS`,
nine theorems giving `(dr)^[a] ((dz)^[b] F) p` in terms of `meridionalPartial`.

The first-order identities `(1,0)` and `(0,1)` are already in `CIV.Zoom.ChainRule`.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



/-! ### Open-neighbourhood lemmas -/

theorem isOpen_zoomPoint_preimage (lam h zc : ℝ) :
    IsOpen {q : (ℝ × ℝ) × ℝ | zoomPoint lam h zc q ∈ unitCylinder} :=
  isOpen_unitCylinder_prod.preimage (continuous_zoomPoint lam h zc)

theorem isOpen_slice_r (lam h zc : ℝ) (p : (ℝ × ℝ) × ℝ) :
    IsOpen {r : ℝ | zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder} := by
  have h_cont : Continuous (fun r : ℝ => ((r, p.1.2), p.2)) :=
    (Continuous.prodMk continuous_id continuous_const).prodMk continuous_const
  exact (isOpen_zoomPoint_preimage lam h zc).preimage h_cont

theorem isOpen_slice_z (lam h zc : ℝ) (p : (ℝ × ℝ) × ℝ) :
    IsOpen {s : ℝ | zoomPoint lam h zc ((p.1.1, s), p.2) ∈ unitCylinder} := by
  have h_cont : Continuous (fun s : ℝ => ((p.1.1, s), p.2)) :=
    (Continuous.prodMk continuous_const continuous_id).prodMk continuous_const
  exact (isOpen_zoomPoint_preimage lam h zc).preimage h_cont

/-! ### First-order identities on slices -/

theorem eventually_dr_on_slice_r (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    (fun r : ℝ => dr (zoomV lam h zc u) ((r, p.1.2), p.2))
      =ᶠ[𝓝 p.1.1]
    fun r : ℝ =>
      lam ^ 2 * spatialPartial (fun w => u w 0) 0 (zoomPoint lam h zc ((r, p.1.2), p.2)) := by
  set S := {r : ℝ | zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder}
  have hS_open : IsOpen S := isOpen_slice_r lam h zc p
  have hpS : p.1.1 ∈ S := by simpa [S] using hp
  filter_upwards [hS_open.mem_nhds hpS] with r hr
  have h_cyl : zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder := hr
  rw [dr_zoomV lam h zc u (hu.of_le (by norm_num)) ((r, p.1.2), p.2) h_cyl]

theorem eventually_dz_on_slice_r (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    (fun r : ℝ => dz (zoomV lam h zc u) ((r, p.1.2), p.2))
      =ᶠ[𝓝 p.1.1]
    fun r : ℝ =>
      lam * lam ^ (1 - 2 * h) * spatialPartial (fun w => u w 0) 2 (zoomPoint lam h zc ((r,
        p.1.2), p.2)) := by
  set S := {r : ℝ | zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder}
  have hS_open : IsOpen S := isOpen_slice_r lam h zc p
  have hpS : p.1.1 ∈ S := by simpa [S] using hp
  filter_upwards [hS_open.mem_nhds hpS] with r hr
  have h_cyl : zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder := hr
  rw [dz_zoomV lam h zc u (hu.of_le (by norm_num)) ((r, p.1.2), p.2) h_cyl]

theorem eventually_dr_on_slice_z (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    (fun s : ℝ => dr (zoomV lam h zc u) ((p.1.1, s), p.2))
      =ᶠ[𝓝 p.1.2]
    fun s : ℝ =>
      lam ^ 2 * spatialPartial (fun w => u w 0) 0 (zoomPoint lam h zc ((p.1.1, s), p.2)) := by
  set S := {s : ℝ | zoomPoint lam h zc ((p.1.1, s), p.2) ∈ unitCylinder}
  have hS_open : IsOpen S := isOpen_slice_z lam h zc p
  have hpS : p.1.2 ∈ S := by simpa [S] using hp
  filter_upwards [hS_open.mem_nhds hpS] with s hs
  have h_cyl : zoomPoint lam h zc ((p.1.1, s), p.2) ∈ unitCylinder := hs
  rw [dr_zoomV lam h zc u (hu.of_le (by norm_num)) ((p.1.1, s), p.2) h_cyl]

theorem eventually_dz_on_slice_z (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    (fun s : ℝ => dz (zoomV lam h zc u) ((p.1.1, s), p.2))
      =ᶠ[𝓝 p.1.2]
    fun s : ℝ =>
      lam * lam ^ (1 - 2 * h) * spatialPartial (fun w => u w 0) 2 (zoomPoint lam h zc ((p.1.1,
        s), p.2)) := by
  set S := {s : ℝ | zoomPoint lam h zc ((p.1.1, s), p.2) ∈ unitCylinder}
  have hS_open : IsOpen S := isOpen_slice_z lam h zc p
  have hpS : p.1.2 ∈ S := by simpa [S] using hp
  filter_upwards [hS_open.mem_nhds hpS] with s hs
  have h_cyl : zoomPoint lam h zc ((p.1.1, s), p.2) ∈ unitCylinder := hs
  rw [dz_zoomV lam h zc u (hu.of_le (by norm_num)) ((p.1.1, s), p.2) h_cyl]

/-! ### ContDiffOn bridges for iterated spatialPartial vector fields -/

theorem contDiffOn_spatialPartial_vec0 (u : ParabolicPoint → Vec3) (i : Fin 3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ 1 (fun z : Vec3 × ℝ =>
      ![spatialPartial (fun w => u w i) 0 z,
        spatialPartial (fun w => u w i) 0 z,
        spatialPartial (fun w => u w i) 0 z]) unitCylinder := by
  have h_comp : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z i) unitCylinder :=
    contDiffOn_component hu i
  refine contDiffOn_pi.2 fun j => ?_
  fin_cases j
  · exact contDiffOn_spatialPartial_of_contDiffOn h_comp 0
  · exact contDiffOn_spatialPartial_of_contDiffOn h_comp 0
  · exact contDiffOn_spatialPartial_of_contDiffOn h_comp 0

theorem contDiffOn_spatialPartial_vec2 (u : ParabolicPoint → Vec3) (i : Fin 3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ 1 (fun z : Vec3 × ℝ =>
      ![spatialPartial (fun w => u w i) 2 z,
        spatialPartial (fun w => u w i) 2 z,
        spatialPartial (fun w => u w i) 2 z]) unitCylinder := by
  have h_comp : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z i) unitCylinder :=
    contDiffOn_component hu i
  refine contDiffOn_pi.2 fun j => ?_
  fin_cases j
  · exact contDiffOn_spatialPartial_of_contDiffOn h_comp 2
  · exact contDiffOn_spatialPartial_of_contDiffOn h_comp 2
  · exact contDiffOn_spatialPartial_of_contDiffOn h_comp 2

/-! ### Second-derivative helpers via `hasDerivAt_comp_spatialSlice` -/

/-- r-derivative of `spatialPartial (u· i) 0` composed with `zoomPoint`.
Returns `lam * meridionalPartial (u· i) 2 0 (zoomPoint lam h zc p)`. -/
theorem hasDerivAt_spatialPartial_zero_zoom_r (lam h zc : ℝ) (u : ParabolicPoint → Vec3) (i : Fin 3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    HasDerivAt (fun r : ℝ =>
      spatialPartial (fun w => u w i) 0 (zoomPoint lam h zc ((r, p.1.2), p.2)))
      (lam * meridionalPartial (fun w => u w i) 2 0 (zoomPoint lam h zc p)) p.1.1 := by
  set u' : ParabolicPoint → Vec3 := fun z =>
    ![spatialPartial (fun w => u w i) 0 z,
      spatialPartial (fun w => u w i) 0 z,
      spatialPartial (fun w => u w i) 0 z]
  have hu'_contDiff : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u' z) unitCylinder :=
    contDiffOn_spatialPartial_vec0 u i hu
  have h_meridional : HasDerivAt (fun s : ℝ =>
      meridional (lam * s) (zc + lam ^ (1 - 2 * h) * p.1.2))
      (lam • basisVec 0) p.1.1 :=
    hasDerivAt_meridional_fst lam (zc + lam ^ (1 - 2 * h) * p.1.2) p.1.1
  have h_result := hasDerivAt_comp_spatialSlice hu'_contDiff hp h_meridional rfl 0
  dsimp [u', zoomPoint] at h_result ⊢
  simpa [meridionalPartial, Function.iterate_succ, Function.iterate_zero] using h_result

/-- r-derivative of `spatialPartial (u· i) 2` composed with `zoomPoint`.
Returns `lam * meridionalPartial (u· i) 1 1 (zoomPoint lam h zc p)`. -/
theorem hasDerivAt_spatialPartial_two_zoom_r (lam h zc : ℝ) (u : ParabolicPoint → Vec3) (i : Fin 3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    HasDerivAt (fun r : ℝ =>
      spatialPartial (fun w => u w i) 2 (zoomPoint lam h zc ((r, p.1.2), p.2)))
      (lam * meridionalPartial (fun w => u w i) 1 1 (zoomPoint lam h zc p)) p.1.1 := by
  set u' : ParabolicPoint → Vec3 := fun z =>
    ![spatialPartial (fun w => u w i) 2 z,
      spatialPartial (fun w => u w i) 2 z,
      spatialPartial (fun w => u w i) 2 z]
  have hu'_contDiff : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u' z) unitCylinder :=
    contDiffOn_spatialPartial_vec2 u i hu
  have h_meridional : HasDerivAt (fun s : ℝ =>
      meridional (lam * s) (zc + lam ^ (1 - 2 * h) * p.1.2))
      (lam • basisVec 0) p.1.1 :=
    hasDerivAt_meridional_fst lam (zc + lam ^ (1 - 2 * h) * p.1.2) p.1.1
  have h_result := hasDerivAt_comp_spatialSlice hu'_contDiff hp h_meridional rfl 0
  dsimp [u', zoomPoint] at h_result ⊢
  simpa [meridionalPartial, Function.iterate_succ, Function.iterate_zero] using h_result

/-- z-derivative of `spatialPartial (u· i) 2` composed with `zoomPoint`.
Returns `lam^(1-2h) * meridionalPartial (u· i) 0 2 (zoomPoint lam h zc p)`. -/
theorem hasDerivAt_spatialPartial_two_zoom_z (lam h zc : ℝ) (u : ParabolicPoint → Vec3) (i : Fin 3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ =>
      spatialPartial (fun w => u w i) 2 (zoomPoint lam h zc ((p.1.1, s), p.2)))
      (lam ^ (1 - 2 * h) * meridionalPartial (fun w => u w i) 0 2 (zoomPoint lam h zc p)) p.1.2
        := by
  set u' : ParabolicPoint → Vec3 := fun z =>
    ![spatialPartial (fun w => u w i) 2 z,
      spatialPartial (fun w => u w i) 2 z,
      spatialPartial (fun w => u w i) 2 z]
  have hu'_contDiff : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u' z) unitCylinder :=
    contDiffOn_spatialPartial_vec2 u i hu
  have h_meridional : HasDerivAt (fun s : ℝ =>
      meridional (lam * p.1.1) (zc + lam ^ (1 - 2 * h) * s))
      (lam ^ (1 - 2 * h) • basisVec 2) p.1.2 :=
    hasDerivAt_meridional_snd (lam * p.1.1) zc (lam ^ (1 - 2 * h)) p.1.2
  have h_result := hasDerivAt_comp_spatialSlice hu'_contDiff hp h_meridional rfl 0
  dsimp [u', zoomPoint] at h_result ⊢
  simpa [meridionalPartial, Function.iterate_succ, Function.iterate_zero] using h_result

/-! ### dr² of zoomV -/

theorem drdr_zoomV (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    dr (dr (zoomV lam h zc u)) p
      = lam ^ 3 * meridionalPartial (fun w => u w 0) 2 0 (zoomPoint lam h zc p) := by
  rw [dr]
  have h_event := eventually_dr_on_slice_r lam h zc u hu p hp
  have h_deriv_rhs : HasDerivAt (fun r : ℝ =>
      lam ^ 2 * spatialPartial (fun w => u w 0) 0 (zoomPoint lam h zc ((r, p.1.2), p.2)))
      (lam ^ 3 * meridionalPartial (fun w => u w 0) 2 0 (zoomPoint lam h zc p)) p.1.1 := by
    have h_inner := hasDerivAt_spatialPartial_zero_zoom_r lam h zc u 0 hu p hp
    have h_mul := h_inner.const_mul (lam ^ 2)
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  have h_deriv_lhs : HasDerivAt (fun r : ℝ =>
      dr (zoomV lam h zc u) ((r, p.1.2), p.2))
      (lam ^ 3 * meridionalPartial (fun w => u w 0) 2 0 (zoomPoint lam h zc p)) p.1.1 :=
    h_deriv_rhs.congr_of_eventuallyEq h_event
  exact h_deriv_lhs.deriv

/-! ### dr dz of zoomV -/

theorem drdz_zoomV (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    dr (dz (zoomV lam h zc u)) p
      = lam ^ 2 * lam ^ (1 - 2 * h) * meridionalPartial (fun w => u w 0) 1 1 (zoomPoint lam h zc
        p) := by
  rw [dr]
  have h_event := eventually_dz_on_slice_r lam h zc u hu p hp
  have h_deriv_rhs : HasDerivAt (fun r : ℝ =>
      lam * lam ^ (1 - 2 * h) * spatialPartial (fun w => u w 0) 2 (zoomPoint lam h zc ((r,
        p.1.2), p.2)))
      (lam ^ 2 * lam ^ (1 - 2 * h) * meridionalPartial (fun w => u w 0) 1 1 (zoomPoint lam h zc
        p)) p.1.1 := by
    have h_inner := hasDerivAt_spatialPartial_two_zoom_r lam h zc u 0 hu p hp
    have h_mul := h_inner.const_mul (lam * lam ^ (1 - 2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  have h_deriv_lhs : HasDerivAt (fun r : ℝ =>
      dz (zoomV lam h zc u) ((r, p.1.2), p.2))
      (lam ^ 2 * lam ^ (1 - 2 * h) * meridionalPartial (fun w => u w 0) 1 1 (zoomPoint lam h zc
        p)) p.1.1 :=
    h_deriv_rhs.congr_of_eventuallyEq h_event
  exact h_deriv_lhs.deriv

/-! ### dz² of zoomV -/

theorem dzdz_zoomV (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    dz (dz (zoomV lam h zc u)) p
      = lam * (lam ^ (1 - 2 * h)) ^ 2 * meridionalPartial (fun w => u w 0) 0 2 (zoomPoint lam h
        zc p) := by
  rw [dz]
  have h_event := eventually_dz_on_slice_z lam h zc u hu p hp
  have h_deriv_rhs : HasDerivAt (fun s : ℝ =>
      lam * lam ^ (1 - 2 * h) * spatialPartial (fun w => u w 0) 2 (zoomPoint lam h zc ((p.1.1,
        s), p.2)))
      (lam * (lam ^ (1 - 2 * h)) ^ 2 *
        meridionalPartial (fun w => u w 0) 0 2 (zoomPoint lam h zc p)) p.1.2 := by
    have h_inner := hasDerivAt_spatialPartial_two_zoom_z lam h zc u 0 hu p hp
    have h_mul := h_inner.const_mul (lam * lam ^ (1 - 2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  have h_deriv_lhs : HasDerivAt (fun s : ℝ =>
      dz (zoomV lam h zc u) ((p.1.1, s), p.2))
      (lam * (lam ^ (1 - 2 * h)) ^ 2 *
        meridionalPartial (fun w => u w 0) 0 2 (zoomPoint lam h zc p)) p.1.2 :=
    h_deriv_rhs.congr_of_eventuallyEq h_event
  exact h_deriv_lhs.deriv

/-! ### dr² of zoomW -/

theorem drdr_zoomW (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    dr (dr (zoomW lam h zc u)) p
      = lam ^ 3 * lam ^ (2 * h) * meridionalPartial (fun w => u w 2) 2 0 (zoomPoint lam h zc p)
        := by
  rw [dr]
  have h_event : (fun r : ℝ => dr (zoomW lam h zc u) ((r, p.1.2), p.2))
      =ᶠ[𝓝 p.1.1]
    fun r : ℝ =>
      lam ^ 2 * lam ^ (2 * h) * spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc ((r,
        p.1.2), p.2)) := by
    set S := {r : ℝ | zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder}
    have hS_open : IsOpen S := isOpen_slice_r lam h zc p
    have hpS : p.1.1 ∈ S := by simpa [S] using hp
    filter_upwards [hS_open.mem_nhds hpS] with r hr
    have h_cyl : zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder := hr
    rw [dr_zoomW lam h zc u (hu.of_le (by norm_num)) ((r, p.1.2), p.2) h_cyl]
  have h_deriv_rhs : HasDerivAt (fun r : ℝ =>
      lam ^ 2 * lam ^ (2 * h) * spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc ((r,
        p.1.2), p.2)))
      (lam ^ 3 * lam ^ (2 * h) * meridionalPartial (fun w => u w 2) 2 0 (zoomPoint lam h zc p))
        p.1.1 := by
    have h_inner := hasDerivAt_spatialPartial_zero_zoom_r lam h zc u 2 hu p hp
    have h_mul := h_inner.const_mul (lam ^ 2 * lam ^ (2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  have h_deriv_lhs : HasDerivAt (fun r : ℝ =>
      dr (zoomW lam h zc u) ((r, p.1.2), p.2))
      (lam ^ 3 * lam ^ (2 * h) * meridionalPartial (fun w => u w 2) 2 0 (zoomPoint lam h zc p))
        p.1.1 :=
    h_deriv_rhs.congr_of_eventuallyEq h_event
  exact h_deriv_lhs.deriv

/-! ### dr dz of zoomW -/

theorem drdz_zoomW (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    dr (dz (zoomW lam h zc u)) p
      = lam ^ 2 * lam ^ (2 * h) * lam ^ (1 - 2 * h) * meridionalPartial (fun w => u w 2) 1 1
        (zoomPoint lam h zc p) := by
  rw [dr]
  have h_event : (fun r : ℝ => dz (zoomW lam h zc u) ((r, p.1.2), p.2))
      =ᶠ[𝓝 p.1.1]
    fun r : ℝ =>
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) * spatialPartial (fun w => u w 2) 2 (zoomPoint lam
        h zc ((r, p.1.2), p.2)) := by
    set S := {r : ℝ | zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder}
    have hS_open : IsOpen S := isOpen_slice_r lam h zc p
    have hpS : p.1.1 ∈ S := by simpa [S] using hp
    filter_upwards [hS_open.mem_nhds hpS] with r hr
    have h_cyl : zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder := hr
    rw [dz_zoomW lam h zc u (hu.of_le (by norm_num)) ((r, p.1.2), p.2) h_cyl]
  have h_deriv_rhs : HasDerivAt (fun r : ℝ =>
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) * spatialPartial (fun w => u w 2) 2 (zoomPoint lam
        h zc ((r, p.1.2), p.2)))
      (lam ^ 2 * lam ^ (2 * h) * lam ^ (1 - 2 * h) *
        meridionalPartial (fun w => u w 2) 1 1 (zoomPoint lam h zc p)) p.1.1 := by
    have h_inner := hasDerivAt_spatialPartial_two_zoom_r lam h zc u 2 hu p hp
    have h_mul := h_inner.const_mul (lam * lam ^ (1 - 2 * h) * lam ^ (2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  have h_deriv_lhs : HasDerivAt (fun r : ℝ =>
      dz (zoomW lam h zc u) ((r, p.1.2), p.2))
      (lam ^ 2 * lam ^ (2 * h) * lam ^ (1 - 2 * h) * meridionalPartial (fun w => u w 2) 1 1
        (zoomPoint lam h zc p)) p.1.1 :=
    h_deriv_rhs.congr_of_eventuallyEq h_event
  exact h_deriv_lhs.deriv

/-! ### dz² of zoomW -/

theorem dzdz_zoomW (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    dz (dz (zoomW lam h zc u)) p
      = lam * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ 2 * meridionalPartial (fun w => u w 2) 0 2
        (zoomPoint lam h zc p) := by
  rw [dz]
  have h_event : (fun s : ℝ => dz (zoomW lam h zc u) ((p.1.1, s), p.2))
      =ᶠ[𝓝 p.1.2]
    fun s : ℝ =>
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) * spatialPartial (fun w => u w 2) 2 (zoomPoint lam
        h zc ((p.1.1, s), p.2)) := by
    set S := {s : ℝ | zoomPoint lam h zc ((p.1.1, s), p.2) ∈ unitCylinder}
    have hS_open : IsOpen S := isOpen_slice_z lam h zc p
    have hpS : p.1.2 ∈ S := by simpa [S] using hp
    filter_upwards [hS_open.mem_nhds hpS] with s hs
    have h_cyl : zoomPoint lam h zc ((p.1.1, s), p.2) ∈ unitCylinder := hs
    rw [dz_zoomW lam h zc u (hu.of_le (by norm_num)) ((p.1.1, s), p.2) h_cyl]
  have h_deriv_rhs : HasDerivAt (fun s : ℝ =>
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) * spatialPartial (fun w => u w 2) 2 (zoomPoint lam
        h zc ((p.1.1, s), p.2)))
      (lam * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ 2 *
        meridionalPartial (fun w => u w 2) 0 2 (zoomPoint lam h zc p)) p.1.2 := by
    have h_inner := hasDerivAt_spatialPartial_two_zoom_z lam h zc u 2 hu p hp
    have h_mul := h_inner.const_mul (lam * lam ^ (1 - 2 * h) * lam ^ (2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  have h_deriv_lhs : HasDerivAt (fun s : ℝ =>
      dz (zoomW lam h zc u) ((p.1.1, s), p.2))
      (lam * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ 2 *
        meridionalPartial (fun w => u w 2) 0 2 (zoomPoint lam h zc p)) p.1.2 :=
    h_deriv_rhs.congr_of_eventuallyEq h_event
  exact h_deriv_lhs.deriv

/-! ### dr² of zoomS -/

theorem drdr_zoomS (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    dr (dr (zoomS lam h zc u)) p
      = lam ^ 3 * lam ^ (2 * h) * meridionalPartial (fun w => u w 1) 2 0 (zoomPoint lam h zc p)
        := by
  rw [dr]
  have h_event : (fun r : ℝ => dr (zoomS lam h zc u) ((r, p.1.2), p.2))
      =ᶠ[𝓝 p.1.1]
    fun r : ℝ =>
      lam ^ 2 * lam ^ (2 * h) * spatialPartial (fun w => u w 1) 0 (zoomPoint lam h zc ((r,
        p.1.2), p.2)) := by
    set S := {r : ℝ | zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder}
    have hS_open : IsOpen S := isOpen_slice_r lam h zc p
    have hpS : p.1.1 ∈ S := by simpa [S] using hp
    filter_upwards [hS_open.mem_nhds hpS] with r hr
    have h_cyl : zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder := hr
    rw [dr_zoomS lam h zc u (hu.of_le (by norm_num)) ((r, p.1.2), p.2) h_cyl]
  have h_deriv_rhs : HasDerivAt (fun r : ℝ =>
      lam ^ 2 * lam ^ (2 * h) * spatialPartial (fun w => u w 1) 0 (zoomPoint lam h zc ((r,
        p.1.2), p.2)))
      (lam ^ 3 * lam ^ (2 * h) * meridionalPartial (fun w => u w 1) 2 0 (zoomPoint lam h zc p))
        p.1.1 := by
    have h_inner := hasDerivAt_spatialPartial_zero_zoom_r lam h zc u 1 hu p hp
    have h_mul := h_inner.const_mul (lam ^ 2 * lam ^ (2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  have h_deriv_lhs : HasDerivAt (fun r : ℝ =>
      dr (zoomS lam h zc u) ((r, p.1.2), p.2))
      (lam ^ 3 * lam ^ (2 * h) * meridionalPartial (fun w => u w 1) 2 0 (zoomPoint lam h zc p))
        p.1.1 :=
    h_deriv_rhs.congr_of_eventuallyEq h_event
  exact h_deriv_lhs.deriv

/-! ### dr dz of zoomS -/

theorem drdz_zoomS (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    dr (dz (zoomS lam h zc u)) p
      = lam ^ 2 * lam ^ (2 * h) * lam ^ (1 - 2 * h) * meridionalPartial (fun w => u w 1) 1 1
        (zoomPoint lam h zc p) := by
  rw [dr]
  have h_event : (fun r : ℝ => dz (zoomS lam h zc u) ((r, p.1.2), p.2))
      =ᶠ[𝓝 p.1.1]
    fun r : ℝ =>
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) * spatialPartial (fun w => u w 1) 2 (zoomPoint lam
        h zc ((r, p.1.2), p.2)) := by
    set S := {r : ℝ | zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder}
    have hS_open : IsOpen S := isOpen_slice_r lam h zc p
    have hpS : p.1.1 ∈ S := by simpa [S] using hp
    filter_upwards [hS_open.mem_nhds hpS] with r hr
    have h_cyl : zoomPoint lam h zc ((r, p.1.2), p.2) ∈ unitCylinder := hr
    rw [dz_zoomS lam h zc u (hu.of_le (by norm_num)) ((r, p.1.2), p.2) h_cyl]
  have h_deriv_rhs : HasDerivAt (fun r : ℝ =>
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) * spatialPartial (fun w => u w 1) 2 (zoomPoint lam
        h zc ((r, p.1.2), p.2)))
      (lam ^ 2 * lam ^ (2 * h) * lam ^ (1 - 2 * h) *
        meridionalPartial (fun w => u w 1) 1 1 (zoomPoint lam h zc p)) p.1.1 := by
    have h_inner := hasDerivAt_spatialPartial_two_zoom_r lam h zc u 1 hu p hp
    have h_mul := h_inner.const_mul (lam * lam ^ (1 - 2 * h) * lam ^ (2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  have h_deriv_lhs : HasDerivAt (fun r : ℝ =>
      dz (zoomS lam h zc u) ((r, p.1.2), p.2))
      (lam ^ 2 * lam ^ (2 * h) * lam ^ (1 - 2 * h) * meridionalPartial (fun w => u w 1) 1 1
        (zoomPoint lam h zc p)) p.1.1 :=
    h_deriv_rhs.congr_of_eventuallyEq h_event
  exact h_deriv_lhs.deriv

/-! ### dz² of zoomS -/

theorem dzdz_zoomS (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    dz (dz (zoomS lam h zc u)) p
      = lam * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ 2 * meridionalPartial (fun w => u w 1) 0 2
        (zoomPoint lam h zc p) := by
  rw [dz]
  have h_event : (fun s : ℝ => dz (zoomS lam h zc u) ((p.1.1, s), p.2))
      =ᶠ[𝓝 p.1.2]
    fun s : ℝ =>
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) * spatialPartial (fun w => u w 1) 2 (zoomPoint lam
        h zc ((p.1.1, s), p.2)) := by
    set S := {s : ℝ | zoomPoint lam h zc ((p.1.1, s), p.2) ∈ unitCylinder}
    have hS_open : IsOpen S := isOpen_slice_z lam h zc p
    have hpS : p.1.2 ∈ S := by simpa [S] using hp
    filter_upwards [hS_open.mem_nhds hpS] with s hs
    have h_cyl : zoomPoint lam h zc ((p.1.1, s), p.2) ∈ unitCylinder := hs
    rw [dz_zoomS lam h zc u (hu.of_le (by norm_num)) ((p.1.1, s), p.2) h_cyl]
  have h_deriv_rhs : HasDerivAt (fun s : ℝ =>
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) * spatialPartial (fun w => u w 1) 2 (zoomPoint lam
        h zc ((p.1.1, s), p.2)))
      (lam * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ 2 *
        meridionalPartial (fun w => u w 1) 0 2 (zoomPoint lam h zc p)) p.1.2 := by
    have h_inner := hasDerivAt_spatialPartial_two_zoom_z lam h zc u 1 hu p hp
    have h_mul := h_inner.const_mul (lam * lam ^ (1 - 2 * h) * lam ^ (2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  have h_deriv_lhs : HasDerivAt (fun s : ℝ =>
      dz (zoomS lam h zc u) ((p.1.1, s), p.2))
      (lam * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ 2 *
        meridionalPartial (fun w => u w 1) 0 2 (zoomPoint lam h zc p)) p.1.2 :=
    h_deriv_rhs.congr_of_eventuallyEq h_event
  exact h_deriv_lhs.deriv

end CIV
