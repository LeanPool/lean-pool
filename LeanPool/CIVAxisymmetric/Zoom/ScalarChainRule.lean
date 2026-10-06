/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.ChainRule
public import LeanPool.CIVAxisymmetric.Statements.DtPast
public import LeanPool.CIVAxisymmetric.Statements.MeridionalPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial

/-!
# Chain rules for a general scalar composed with the zoom map

`CIV.Zoom.ChainRule` and `CIV.Zoom.ChainRuleSecond` differentiate the *components of a
vector field* along the zoom map `zoomPoint` of `eq:aniso:zoom:finite:variables`. The
rescaled potential vorticity `Ω_n` of `eq:aniso:zoom:fields` is instead a plain scalar
`Φ : ParabolicPoint → ℝ`, and — unlike the velocity — it is only smooth *off the axis*, so
the chain rules below are stated on an arbitrary open subset `D` of the product carrier
`Vec3 × ℝ` rather than on `unitCylinder`.

The zoom map sends `((R, Z), τ)` to `(meridional (lam R) (zc + lam^{1-2h} Z), lam² τ)`.
Its time slot does not depend on `R` or `Z` and its space slot does not depend on `τ`, so:

* `∂_R (Φ ∘ zoomPoint) = lam ∂₁Φ`,
* `∂_Z (Φ ∘ zoomPoint) = lam^{1-2h} ∂₃Φ`,
* `∂_τ (Φ ∘ zoomPoint) = lam² ∂_tΦ`,

with the corresponding products for the three second-order meridional derivatives. Every
spatial derivative is taken on `Vec3` and every time derivative on `ℝ`, never on the
parabolic carrier itself (design note R2: `ParabolicPoint` carries the parabolic metric and
no linear structure of its own).

The time derivative `dtPast` is a `derivWithin` over the past `Iic τ`; since the zoom is
affine in `τ` the two-sided derivative exists, and `HasDerivWithinAt.derivWithin` together
with `uniqueDiffWithinAt_Iic` turns it into the honest one-sided value.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### Slices of a scalar field on an open set -/

/-- The spatial slice of a `C¹` scalar is differentiable at every point of an open set. -/
theorem differentiableAt_spatialSlice_of_isOpen {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {Phi : ParabolicPoint → ℝ} (hPhi : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) D)
    {z : ParabolicPoint} (hz : z ∈ D) :
    DifferentiableAt ℝ (fun y : Vec3 => Phi (y, z.2)) z.1 := by
  have hjoint : DifferentiableAt ℝ (fun w : Vec3 × ℝ => Phi w) z :=
    (hPhi.differentiableOn one_ne_zero z hz).differentiableAt (hD.mem_nhds hz)
  exact hjoint.comp z.1 (hasFDerivAt_prodMk_left z.1 z.2).differentiableAt

/-- The time slice of a `C¹` scalar is differentiable at every point of an open set. -/
theorem differentiableAt_timeSlice_of_isOpen {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {Phi : ParabolicPoint → ℝ} (hPhi : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) D)
    {z : ParabolicPoint} (hz : z ∈ D) :
    DifferentiableAt ℝ (fun s : ℝ => Phi (z.1, s)) z.2 := by
  have hjoint : DifferentiableAt ℝ (fun w : Vec3 × ℝ => Phi w) z :=
    (hPhi.differentiableOn one_ne_zero z hz).differentiableAt (hD.mem_nhds hz)
  exact hjoint.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2).differentiableAt

/-- A `C¹` scalar read along a curve `cu` that stays in the time slice of `z` and passes
through `z` with velocity `a • e_j` has derivative `a ∂_j Φ (z)`. Only the spatial slice
`fun y : Vec3 => Φ (y, z.2)` is differentiated. -/
theorem hasDerivAt_comp_spatialSlice_scalar {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {Phi : ParabolicPoint → ℝ} (hPhi : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) D)
    {z : ParabolicPoint} (hz : z ∈ D) {cu : ℝ → Vec3} {a x : ℝ} {j : Fin 3}
    (hcu : HasDerivAt cu (a • basisVec j) x) (hx : cu x = z.1) :
    HasDerivAt (fun s : ℝ => Phi (cu s, z.2)) (a * spatialPartial Phi j z) x := by
  have hF : HasFDerivAt (fun y : Vec3 => Phi (y, z.2))
      (fderiv ℝ (fun y : Vec3 => Phi (y, z.2)) z.1) z.1 :=
    (differentiableAt_spatialSlice_of_isOpen hD hPhi hz).hasFDerivAt
  have hcomp : HasDerivAt (fun s : ℝ => Phi (cu s, z.2))
      ((fderiv ℝ (fun y : Vec3 => Phi (y, z.2)) z.1) (a • basisVec j)) x :=
    HasFDerivAt.comp_hasDerivAt_of_eq (hl := hF) (hf := hcu) (hy := hx.symm)
  have hval : (fderiv ℝ (fun y : Vec3 => Phi (y, z.2)) z.1) (a • basisVec j)
      = a * spatialPartial Phi j z := by
    rw [map_smul]
    rfl
  rwa [hval] at hcomp

/-! ### Openness of the zoom preimage and of its coordinate slices -/

/-- The preimage of an open set under the zoom map is open. -/
theorem isOpen_zoomPoint_preimage_of_isOpen (lam h zc : ℝ) {D : Set (Vec3 × ℝ)} (hD : IsOpen D) :
    IsOpen {q : (ℝ × ℝ) × ℝ | zoomPoint lam h zc q ∈ D} :=
  hD.preimage (continuous_zoomPoint lam h zc)

/-- The radial slice of the zoom preimage of an open set is open. -/
theorem isOpen_zoomSlice_r (lam h zc : ℝ) {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    (p : (ℝ × ℝ) × ℝ) :
    IsOpen {r : ℝ | zoomPoint lam h zc ((r, p.1.2), p.2) ∈ D} := by
  have hcont : Continuous (fun r : ℝ => ((r, p.1.2), p.2)) :=
    (Continuous.prodMk continuous_id continuous_const).prodMk continuous_const
  exact (isOpen_zoomPoint_preimage_of_isOpen lam h zc hD).preimage hcont

/-- The vertical slice of the zoom preimage of an open set is open. -/
theorem isOpen_zoomSlice_z (lam h zc : ℝ) {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    (p : (ℝ × ℝ) × ℝ) :
    IsOpen {s : ℝ | zoomPoint lam h zc ((p.1.1, s), p.2) ∈ D} := by
  have hcont : Continuous (fun s : ℝ => ((p.1.1, s), p.2)) :=
    (Continuous.prodMk continuous_const continuous_id).prodMk continuous_const
  exact (isOpen_zoomPoint_preimage_of_isOpen lam h zc hD).preimage hcont

/-! ### The three one-dimensional derivatives of `Φ ∘ zoomPoint` -/

/-- Differentiating a scalar along the zoom map in the radial variable. -/
theorem hasDerivAt_zoomScalar_r (lam h zc : ℝ) {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {Phi : ParabolicPoint → ℝ} (hPhi : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) D)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ D) :
    HasDerivAt (fun r : ℝ => Phi (zoomPoint lam h zc ((r, p.1.2), p.2)))
      (lam * spatialPartial Phi 0 (zoomPoint lam h zc p)) p.1.1 :=
  hasDerivAt_comp_spatialSlice_scalar hD hPhi hp
    (hasDerivAt_meridional_fst lam (zc + lam ^ (1 - 2 * h) * p.1.2) p.1.1) rfl

/-- Differentiating a scalar along the zoom map in the vertical variable. -/
theorem hasDerivAt_zoomScalar_z (lam h zc : ℝ) {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {Phi : ParabolicPoint → ℝ} (hPhi : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) D)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ D) :
    HasDerivAt (fun s : ℝ => Phi (zoomPoint lam h zc ((p.1.1, s), p.2)))
      (lam ^ (1 - 2 * h) * spatialPartial Phi 2 (zoomPoint lam h zc p)) p.1.2 :=
  hasDerivAt_comp_spatialSlice_scalar hD hPhi hp
    (hasDerivAt_meridional_snd (lam * p.1.1) zc (lam ^ (1 - 2 * h)) p.1.2) rfl

/-- Differentiating a scalar along the zoom map in the time variable. The zoom is affine in
`τ` with slope `lam ^ 2`, so the two-sided derivative exists. -/
theorem hasDerivAt_zoomScalar_t (lam h zc : ℝ) {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {Phi : ParabolicPoint → ℝ} (hPhi : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) D)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ D) :
    HasDerivAt (fun t : ℝ => Phi (zoomPoint lam h zc (p.1, t)))
      (lam ^ 2 * timePartial Phi (zoomPoint lam h zc p)) p.2 := by
  have hslice : HasDerivAt (fun s : ℝ => Phi ((zoomPoint lam h zc p).1, s))
      (timePartial Phi (zoomPoint lam h zc p)) (lam ^ 2 * p.2) :=
    (differentiableAt_timeSlice_of_isOpen hD hPhi hp).hasDerivAt
  have hlin : HasDerivAt (fun t : ℝ => lam ^ 2 * t) (lam ^ 2) p.2 := by
    simpa using (hasDerivAt_id p.2).const_mul (lam ^ 2)
  have hcomp := hslice.comp p.2 hlin
  have hval : timePartial Phi (zoomPoint lam h zc p) * lam ^ 2
      = lam ^ 2 * timePartial Phi (zoomPoint lam h zc p) := mul_comm _ _
  rw [hval] at hcomp
  exact hcomp

/-! ### First-order chain rules -/

/-- `∂_R` of a scalar composed with the zoom map. -/
theorem dr_comp_zoomPoint (lam h zc : ℝ) {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {Phi : ParabolicPoint → ℝ} (hPhi : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) D)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ D) :
    dr (fun q => Phi (zoomPoint lam h zc q)) p
      = lam * spatialPartial Phi 0 (zoomPoint lam h zc p) :=
  (hasDerivAt_zoomScalar_r lam h zc hD hPhi p hp).deriv

/-- `∂_Z` of a scalar composed with the zoom map. -/
theorem dz_comp_zoomPoint (lam h zc : ℝ) {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {Phi : ParabolicPoint → ℝ} (hPhi : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) D)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ D) :
    dz (fun q => Phi (zoomPoint lam h zc q)) p
      = lam ^ (1 - 2 * h) * spatialPartial Phi 2 (zoomPoint lam h zc p) :=
  (hasDerivAt_zoomScalar_z lam h zc hD hPhi p hp).deriv

/-- `∂_τ` from the past of a scalar composed with the zoom map. -/
theorem dtPast_comp_zoomPoint (lam h zc : ℝ) {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {Phi : ParabolicPoint → ℝ} (hPhi : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) D)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ D) :
    dtPast (fun q => Phi (zoomPoint lam h zc q)) p
      = lam ^ 2 * timePartial Phi (zoomPoint lam h zc p) :=
  (hasDerivAt_zoomScalar_t lam h zc hD hPhi p hp).hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_Iic p.2)

/-! ### Smoothness of a spatial partial derivative on an open set -/

/-- A `C^{n+1}` scalar has `C^n` spatial partial derivatives on any open set. -/
theorem contDiffOn_spatialPartial_of_isOpen {n : ℕ} {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {Phi : ParabolicPoint → ℝ} (hPhi : ContDiffOn ℝ (n + 1) (fun z : Vec3 × ℝ => Phi z) D)
    (i : Fin 3) :
    ContDiffOn ℝ n (fun z : Vec3 × ℝ => spatialPartial Phi i z) D := by
  have hfderiv : ContDiffOn ℝ n (fderiv ℝ (fun z : Vec3 × ℝ => Phi z)) D :=
    hPhi.fderiv_of_isOpen hD (le_refl _)
  have hdiffOn : DifferentiableOn ℝ (fun z : Vec3 × ℝ => Phi z) D :=
    hPhi.differentiableOn (by simp)
  have hpointwise : ∀ z ∈ D, spatialPartial Phi i z
      = (fderiv ℝ (fun w : Vec3 × ℝ => Phi w) z) (basisVec i, (0 : ℝ)) := by
    intro z hz
    have hjoint : DifferentiableAt ℝ (fun w : Vec3 × ℝ => Phi w) z :=
      hdiffOn.differentiableAt (hD.mem_nhds hz)
    have hslot : DifferentiableAt ℝ (fun y : Vec3 => ((y, z.2) : Vec3 × ℝ)) z.1 :=
      (hasFDerivAt_prodMk_left z.1 z.2).differentiableAt
    have hchain := fderiv_comp z.1 hjoint hslot
    have hslot_fderiv : fderiv ℝ (fun y : Vec3 => ((y, z.2) : Vec3 × ℝ)) z.1
        = ContinuousLinearMap.inl ℝ Vec3 ℝ := (hasFDerivAt_prodMk_left z.1 z.2).fderiv
    calc spatialPartial Phi i z
        = (fderiv ℝ ((fun w : Vec3 × ℝ => Phi w) ∘ fun y : Vec3 => ((y, z.2) : Vec3 × ℝ)) z.1)
            (basisVec i) := rfl
      _ = ((fderiv ℝ (fun w : Vec3 × ℝ => Phi w) z).comp
            (fderiv ℝ (fun y : Vec3 => ((y, z.2) : Vec3 × ℝ)) z.1)) (basisVec i) := by
          rw [hchain]
      _ = (fderiv ℝ (fun w : Vec3 × ℝ => Phi w) z)
            ((fderiv ℝ (fun y : Vec3 => ((y, z.2) : Vec3 × ℝ)) z.1) (basisVec i)) := rfl
      _ = (fderiv ℝ (fun w : Vec3 × ℝ => Phi w) z)
            ((ContinuousLinearMap.inl ℝ Vec3 ℝ) (basisVec i)) := by rw [hslot_fderiv]
      _ = (fderiv ℝ (fun w : Vec3 × ℝ => Phi w) z) (basisVec i, (0 : ℝ)) := by simp
  exact (hfderiv.clm_apply contDiffOn_const).congr hpointwise

/-! ### Second-order chain rules -/

/-- `∂_R∂_R` of a scalar composed with the zoom map. -/
theorem drdr_comp_zoomPoint (lam h zc : ℝ) {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {Phi : ParabolicPoint → ℝ} (hPhi : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => Phi z) D)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ D) :
    dr (dr (fun q => Phi (zoomPoint lam h zc q))) p
      = lam ^ 2 * meridionalPartial Phi 2 0 (zoomPoint lam h zc p) := by
  have hPhi1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) D := hPhi.of_le (by norm_num)
  have hpar : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => spatialPartial Phi 0 z) D :=
    contDiffOn_spatialPartial_of_isOpen hD hPhi 0
  have hslice : p.1.1 ∈ {r : ℝ | zoomPoint lam h zc ((r, p.1.2), p.2) ∈ D} := by simpa using hp
  have hev : (fun r : ℝ => dr (fun q => Phi (zoomPoint lam h zc q)) ((r, p.1.2), p.2))
      =ᶠ[𝓝 p.1.1]
      fun r : ℝ => lam * spatialPartial Phi 0 (zoomPoint lam h zc ((r, p.1.2), p.2)) := by
    filter_upwards [(isOpen_zoomSlice_r lam h zc hD p).mem_nhds hslice] with r hr
    exact dr_comp_zoomPoint lam h zc hD hPhi1 ((r, p.1.2), p.2) hr
  have hrhs : HasDerivAt
      (fun r : ℝ => lam * spatialPartial Phi 0 (zoomPoint lam h zc ((r, p.1.2), p.2)))
      (lam ^ 2 * meridionalPartial Phi 2 0 (zoomPoint lam h zc p)) p.1.1 := by
    have hbase := (hasDerivAt_zoomScalar_r (Phi := fun w : ParabolicPoint => spatialPartial Phi 0 w)
      lam h zc hD hpar p hp).const_mul lam
    have hval : lam * (lam * spatialPartial (fun w : ParabolicPoint => spatialPartial Phi 0 w) 0
          (zoomPoint lam h zc p))
        = lam ^ 2 * meridionalPartial Phi 2 0 (zoomPoint lam h zc p) := by
      change lam * (lam * spatialPartial (fun w : ParabolicPoint => spatialPartial Phi 0 w) 0
          (zoomPoint lam h zc p))
        = lam ^ 2 * spatialPartial (fun w : ParabolicPoint => spatialPartial Phi 0 w) 0
          (zoomPoint lam h zc p)
      ring
    rw [hval] at hbase
    exact hbase
  rw [dr]
  exact (hrhs.congr_of_eventuallyEq hev).deriv

/-- `∂_R∂_Z` of a scalar composed with the zoom map. -/
theorem drdz_comp_zoomPoint (lam h zc : ℝ) {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {Phi : ParabolicPoint → ℝ} (hPhi : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => Phi z) D)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ D) :
    dr (dz (fun q => Phi (zoomPoint lam h zc q))) p
      = lam * lam ^ (1 - 2 * h) * meridionalPartial Phi 1 1 (zoomPoint lam h zc p) := by
  have hPhi1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) D := hPhi.of_le (by norm_num)
  have hpar : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => spatialPartial Phi 2 z) D :=
    contDiffOn_spatialPartial_of_isOpen hD hPhi 2
  have hslice : p.1.1 ∈ {r : ℝ | zoomPoint lam h zc ((r, p.1.2), p.2) ∈ D} := by simpa using hp
  have hev : (fun r : ℝ => dz (fun q => Phi (zoomPoint lam h zc q)) ((r, p.1.2), p.2))
      =ᶠ[𝓝 p.1.1]
      fun r : ℝ =>
        lam ^ (1 - 2 * h) * spatialPartial Phi 2 (zoomPoint lam h zc ((r, p.1.2), p.2)) := by
    filter_upwards [(isOpen_zoomSlice_r lam h zc hD p).mem_nhds hslice] with r hr
    exact dz_comp_zoomPoint lam h zc hD hPhi1 ((r, p.1.2), p.2) hr
  have hrhs : HasDerivAt
      (fun r : ℝ =>
        lam ^ (1 - 2 * h) * spatialPartial Phi 2 (zoomPoint lam h zc ((r, p.1.2), p.2)))
      (lam * lam ^ (1 - 2 * h) * meridionalPartial Phi 1 1 (zoomPoint lam h zc p)) p.1.1 := by
    have hbase := (hasDerivAt_zoomScalar_r (Phi := fun w : ParabolicPoint => spatialPartial Phi 2 w)
      lam h zc hD hpar p hp).const_mul (lam ^ (1 - 2 * h))
    have hval : lam ^ (1 - 2 * h) *
          (lam * spatialPartial (fun w : ParabolicPoint => spatialPartial Phi 2 w) 0
            (zoomPoint lam h zc p))
        = lam * lam ^ (1 - 2 * h) * meridionalPartial Phi 1 1 (zoomPoint lam h zc p) := by
      change lam ^ (1 - 2 * h) *
          (lam * spatialPartial (fun w : ParabolicPoint => spatialPartial Phi 2 w) 0
            (zoomPoint lam h zc p))
        = lam * lam ^ (1 - 2 * h) *
          spatialPartial (fun w : ParabolicPoint => spatialPartial Phi 2 w) 0
            (zoomPoint lam h zc p)
      ring
    rw [hval] at hbase
    exact hbase
  rw [dr]
  exact (hrhs.congr_of_eventuallyEq hev).deriv

/-- `∂_Z∂_Z` of a scalar composed with the zoom map. -/
theorem dzdz_comp_zoomPoint (lam h zc : ℝ) {D : Set (Vec3 × ℝ)} (hD : IsOpen D)
    {Phi : ParabolicPoint → ℝ} (hPhi : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => Phi z) D)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ D) :
    dz (dz (fun q => Phi (zoomPoint lam h zc q))) p
      = (lam ^ (1 - 2 * h)) ^ 2 * meridionalPartial Phi 0 2 (zoomPoint lam h zc p) := by
  have hPhi1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) D := hPhi.of_le (by norm_num)
  have hpar : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => spatialPartial Phi 2 z) D :=
    contDiffOn_spatialPartial_of_isOpen hD hPhi 2
  have hslice : p.1.2 ∈ {s : ℝ | zoomPoint lam h zc ((p.1.1, s), p.2) ∈ D} := by simpa using hp
  have hev : (fun s : ℝ => dz (fun q => Phi (zoomPoint lam h zc q)) ((p.1.1, s), p.2))
      =ᶠ[𝓝 p.1.2]
      fun s : ℝ =>
        lam ^ (1 - 2 * h) * spatialPartial Phi 2 (zoomPoint lam h zc ((p.1.1, s), p.2)) := by
    filter_upwards [(isOpen_zoomSlice_z lam h zc hD p).mem_nhds hslice] with s hs
    exact dz_comp_zoomPoint lam h zc hD hPhi1 ((p.1.1, s), p.2) hs
  have hrhs : HasDerivAt
      (fun s : ℝ =>
        lam ^ (1 - 2 * h) * spatialPartial Phi 2 (zoomPoint lam h zc ((p.1.1, s), p.2)))
      ((lam ^ (1 - 2 * h)) ^ 2 * meridionalPartial Phi 0 2 (zoomPoint lam h zc p)) p.1.2 := by
    have hbase := (hasDerivAt_zoomScalar_z (Phi := fun w : ParabolicPoint => spatialPartial Phi 2 w)
      lam h zc hD hpar p hp).const_mul (lam ^ (1 - 2 * h))
    have hval : lam ^ (1 - 2 * h) *
          (lam ^ (1 - 2 * h) *
            spatialPartial (fun w : ParabolicPoint => spatialPartial Phi 2 w) 2
              (zoomPoint lam h zc p))
        = (lam ^ (1 - 2 * h)) ^ 2 * meridionalPartial Phi 0 2 (zoomPoint lam h zc p) := by
      change lam ^ (1 - 2 * h) *
          (lam ^ (1 - 2 * h) *
            spatialPartial (fun w : ParabolicPoint => spatialPartial Phi 2 w) 2
              (zoomPoint lam h zc p))
        = (lam ^ (1 - 2 * h)) ^ 2 *
          spatialPartial (fun w : ParabolicPoint => spatialPartial Phi 2 w) 2
            (zoomPoint lam h zc p)
      ring
    rw [hval] at hbase
    exact hbase
  rw [dz]
  exact (hrhs.congr_of_eventuallyEq hev).deriv

end CIV
