/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.Receding
public import LeanPool.CIVAxisymmetric.Zoom.Preimage
public import LeanPool.CIVAxisymmetric.Zoom.SwirlSource
public import LeanPool.CIVAxisymmetric.Identities.VorticityEquation

/-!
# The receding-axis rescaled azimuthal vorticity equation

This file completes the receding-axis zoom of `CIV.Zoom.Receding` with the rescaled
azimuthal-vorticity equation `eq:aniso:zoom:receding:equation`, the receding preimage
clause, and the circulation-based swirl-source bounds.

Every derivative in `CIV.Zoom.Receding` is stated over `zoomPointRec`, whose radial slot
`rc + lam * R` differs from the finite-axis `zoomPoint`'s `lam * R` by the constant offset
`rc`. The scalar chain rules of `CIV.Zoom.ScalarChainRule` are stated concretely over
`zoomPoint`, and only coincide with the recentred map after the substitution
`R ↦ R + rc / lam`, which needs `lam ≠ 0` — a hypothesis none of those chain rules carry.
Rather than adding a `lam ≠ 0` binder to `CIV.Zoom.ScalarChainRule` (which this file does
not modify), the scalar chain rules below are restated directly for `zoomPointRec`, built
from the same low-level pieces `CIV.hasDerivAt_comp_spatialSlice_scalar` and
`CIV.differentiableAt_timeSlice_of_isOpen`, which are already stated for an arbitrary curve
and already carry no nonvanishing hypothesis on the affine slope. The radial line uses
`CIV.hasDerivAt_meridional_fst_shift` of `CIV.Zoom.Receding`, already proved there for an
arbitrary offset; the vertical and time lines coincide verbatim with the finite-axis case,
since only the radial slot of `zoomPointRec` carries an offset.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### Scalar chain rules for the recentred zoom map -/

/-- Differentiating a scalar composed with `zoomPointRec` in the radial variable. The
curve is the offset radial line `hasDerivAt_meridional_fst_shift`, so no `lam ≠ 0`
hypothesis is needed. -/
theorem hasDerivAt_zoomRecScalar_r (lam h rc zc : ℝ) {Phi : ParabolicPoint → ℝ}
    (hPhi : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    HasDerivAt (fun r : ℝ => Phi (zoomPointRec lam h rc zc ((r, p.1.2), p.2)))
      (lam * spatialPartial Phi 0 (zoomPointRec lam h rc zc p)) p.1.1 :=
  hasDerivAt_comp_spatialSlice_scalar isOpen_unitCylinder_prod hPhi hp
    (hasDerivAt_meridional_fst_shift rc lam (zc + lam ^ (1 - 2 * h) * p.1.2) p.1.1) rfl

/-- Differentiating a scalar composed with `zoomPointRec` in the vertical variable. The
vertical slot of `zoomPointRec` carries the same offset `zc` as `zoomPoint`, so this is
verbatim the finite-axis chain rule. -/
theorem hasDerivAt_zoomRecScalar_z (lam h rc zc : ℝ) {Phi : ParabolicPoint → ℝ}
    (hPhi : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ => Phi (zoomPointRec lam h rc zc ((p.1.1, s), p.2)))
      (lam ^ (1 - 2 * h) * spatialPartial Phi 2 (zoomPointRec lam h rc zc p)) p.1.2 :=
  hasDerivAt_comp_spatialSlice_scalar isOpen_unitCylinder_prod hPhi hp
    (hasDerivAt_meridional_snd (rc + lam * p.1.1) zc (lam ^ (1 - 2 * h)) p.1.2) rfl

/-- Differentiating a scalar composed with `zoomPointRec` in the time variable. The time
slot of `zoomPointRec` is `lam ^ 2 * τ`, exactly as for `zoomPoint`, independent of `rc`. -/
theorem hasDerivAt_zoomRecScalar_t (lam h rc zc : ℝ) {Phi : ParabolicPoint → ℝ}
    (hPhi : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    HasDerivAt (fun t : ℝ => Phi (zoomPointRec lam h rc zc (p.1, t)))
      (lam ^ 2 * timePartial Phi (zoomPointRec lam h rc zc p)) p.2 := by
  have hslice : HasDerivAt (fun s : ℝ => Phi ((zoomPointRec lam h rc zc p).1, s))
      (timePartial Phi (zoomPointRec lam h rc zc p)) (lam ^ 2 * p.2) :=
    (differentiableAt_timeSlice_of_isOpen isOpen_unitCylinder_prod hPhi hp).hasDerivAt
  have hlin : HasDerivAt (fun t : ℝ => lam ^ 2 * t) (lam ^ 2) p.2 := by
    simpa using (hasDerivAt_id p.2).const_mul (lam ^ 2)
  have hcomp := hslice.comp p.2 hlin
  have hval : timePartial Phi (zoomPointRec lam h rc zc p) * lam ^ 2
      = lam ^ 2 * timePartial Phi (zoomPointRec lam h rc zc p) := mul_comm _ _
  rw [hval] at hcomp
  exact hcomp

/-- `∂_R` of a scalar composed with `zoomPointRec`. -/
theorem dr_comp_zoomPointRec (lam h rc zc : ℝ) {Phi : ParabolicPoint → ℝ}
    (hPhi : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dr (fun q => Phi (zoomPointRec lam h rc zc q)) p
      = lam * spatialPartial Phi 0 (zoomPointRec lam h rc zc p) :=
  (hasDerivAt_zoomRecScalar_r lam h rc zc hPhi p hp).deriv

/-- `∂_Z` of a scalar composed with `zoomPointRec`. -/
theorem dz_comp_zoomPointRec (lam h rc zc : ℝ) {Phi : ParabolicPoint → ℝ}
    (hPhi : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dz (fun q => Phi (zoomPointRec lam h rc zc q)) p
      = lam ^ (1 - 2 * h) * spatialPartial Phi 2 (zoomPointRec lam h rc zc p) :=
  (hasDerivAt_zoomRecScalar_z lam h rc zc hPhi p hp).deriv

/-- `∂_τ` from the past of a scalar composed with `zoomPointRec`. -/
theorem dtPast_comp_zoomPointRec (lam h rc zc : ℝ) {Phi : ParabolicPoint → ℝ}
    (hPhi : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => Phi z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dtPast (fun q => Phi (zoomPointRec lam h rc zc q)) p
      = lam ^ 2 * timePartial Phi (zoomPointRec lam h rc zc p) :=
  (hasDerivAt_zoomRecScalar_t lam h rc zc hPhi p hp).hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_Iic p.2)

/-! ### The rescaled azimuthal-vorticity equation -/

/-- `eq:aniso:zoom:receding:equation`: the rescaled azimuthal-vorticity equation for
`zoomTheta` in the recentred variables, with `A = rc / lam`. It is `lam ^ 4 * δ` times
`azimuthal_vorticity_pde` at the recentred zoom point, `δ = lam ^ (2 * h)`. -/
theorem zoomTheta_pde (lam h rc zc : ℝ) (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (pres : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u pres f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder)
    (hR : p.1.1 ≠ -(rc / lam)) :
    dtPast (zoomTheta lam h rc zc u) p
        + zoomVRec lam h rc zc u p * dr (zoomTheta lam h rc zc u) p
        + zoomWRec lam h rc zc u p * dz (zoomTheta lam h rc zc u) p
        - zoomVRec lam h rc zc u p / (rc / lam + p.1.1) * zoomTheta lam h rc zc u p
      = dr (dr (zoomTheta lam h rc zc u)) p
        + 1 / (rc / lam + p.1.1) * dr (zoomTheta lam h rc zc u) p
        + (lam ^ (2 * h)) ^ 2 * dz (dz (zoomTheta lam h rc zc u)) p
        - zoomTheta lam h rc zc u p / (rc / lam + p.1.1) ^ 2
        + 1 / (rc / lam + p.1.1) * dz (fun q => zoomSRec lam h rc zc u q ^ 2) p
        + lam ^ 4 * lam ^ (2 * h) * curlComp f 1 (zoomPointRec lam h rc zc p) := by
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have hA : rc / lam + p.1.1 ≠ 0 := fun hcontra => hR (by linarith only [hcontra])
  have hz0 : (zoomPointRec lam h rc zc p).1 0 = rc + lam * p.1.1 := by
    simp [zoomPointRec, meridional]
  have hplane : (zoomPointRec lam h rc zc p).1 1 = 0 := by simp [zoomPointRec, meridional]
  have heq : rc + lam * p.1.1 = lam * (rc / lam + p.1.1) := by field_simp
  have hr_zoom : (zoomPointRec lam h rc zc p).1 0 ≠ 0 := by
    rw [hz0, heq]; exact mul_ne_zero hlam_ne hA
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  have hOmegaTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => azimuthalVorticity u z)
      unitCylinder := contDiffOn_azimuthalVorticity hu
  have hOmega1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => azimuthalVorticity u z) unitCylinder :=
    hOmegaTop.of_le (by norm_num)
  have hOmega2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => azimuthalVorticity u z) unitCylinder :=
    hOmegaTop.of_le (by norm_num)
  have hpar0 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => spatialPartial (azimuthalVorticity u) 0 z)
      unitCylinder := contDiffOn_spatialPartial_of_isOpen isOpen_unitCylinder_prod hOmega2 0
  have hpar2 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => spatialPartial (azimuthalVorticity u) 2 z)
      unitCylinder := contDiffOn_spatialPartial_of_isOpen isOpen_unitCylinder_prod hOmega2 2
  have hswirlSmooth : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z 1 ^ 2) unitCylinder := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z 1) unitCylinder :=
      contDiffOn_pi.1 hu 1
    exact (h1.pow 2).of_le (by norm_num)
  have hslice_r : p.1.1 ∈ {r : ℝ | zoomPointRec lam h rc zc ((r, p.1.2), p.2) ∈ unitCylinder} :=
    by simpa using hp
  have hslice_z : p.1.2 ∈ {s : ℝ | zoomPointRec lam h rc zc ((p.1.1, s), p.2) ∈ unitCylinder} :=
    by simpa using hp
  -- the chain rules for the rescaled azimuthal vorticity
  have hdt : dtPast (zoomTheta lam h rc zc u) p
      = lam ^ 2 * lam ^ (2 * h) *
        (lam ^ 2 * timePartial (azimuthalVorticity u) (zoomPointRec lam h rc zc p)) :=
    ((hasDerivAt_zoomRecScalar_t lam h rc zc hOmega1 p hp).const_mul
      (lam ^ 2 * lam ^ (2 * h))).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic p.2)
  have hdr : dr (zoomTheta lam h rc zc u) p
      = lam ^ 2 * lam ^ (2 * h) *
        (lam * spatialPartial (azimuthalVorticity u) 0 (zoomPointRec lam h rc zc p)) :=
    ((hasDerivAt_zoomRecScalar_r lam h rc zc hOmega1 p hp).const_mul
      (lam ^ 2 * lam ^ (2 * h))).deriv
  have hdz : dz (zoomTheta lam h rc zc u) p
      = lam ^ 2 * lam ^ (2 * h) *
        (lam ^ (1 - 2 * h) *
          spatialPartial (azimuthalVorticity u) 2 (zoomPointRec lam h rc zc p)) :=
    ((hasDerivAt_zoomRecScalar_z lam h rc zc hOmega1 p hp).const_mul
      (lam ^ 2 * lam ^ (2 * h))).deriv
  have hdrr : dr (dr (zoomTheta lam h rc zc u)) p
      = lam ^ 2 * lam ^ (2 * h) *
        (lam * (lam * spatialSecondPartial (azimuthalVorticity u) 0 0
          (zoomPointRec lam h rc zc p))) := by
    have hev : (fun r : ℝ => dr (zoomTheta lam h rc zc u) ((r, p.1.2), p.2))
        =ᶠ[𝓝 p.1.1]
        fun r : ℝ => lam ^ 2 * lam ^ (2 * h) *
          (lam * spatialPartial (azimuthalVorticity u) 0
            (zoomPointRec lam h rc zc ((r, p.1.2), p.2))) := by
      filter_upwards [(isOpen_slice_r_rec lam h rc zc p).mem_nhds hslice_r] with r hrmem
      exact ((hasDerivAt_zoomRecScalar_r lam h rc zc hOmega1
        ((r, p.1.2), p.2) hrmem).const_mul (lam ^ 2 * lam ^ (2 * h))).deriv
    have hrhs : HasDerivAt (fun r : ℝ => lam ^ 2 * lam ^ (2 * h) *
        (lam * spatialPartial (azimuthalVorticity u) 0
          (zoomPointRec lam h rc zc ((r, p.1.2), p.2))))
        (lam ^ 2 * lam ^ (2 * h) *
          (lam * (lam * spatialSecondPartial (azimuthalVorticity u) 0 0
            (zoomPointRec lam h rc zc p)))) p.1.1 :=
      ((hasDerivAt_zoomRecScalar_r
        (Phi := fun w : ParabolicPoint => spatialPartial (azimuthalVorticity u) 0 w)
        lam h rc zc hpar0 p hp).const_mul lam).const_mul (lam ^ 2 * lam ^ (2 * h))
    rw [dr]
    exact (hrhs.congr_of_eventuallyEq hev).deriv
  have hdzz : dz (dz (zoomTheta lam h rc zc u)) p
      = lam ^ 2 * lam ^ (2 * h) *
        (lam ^ (1 - 2 * h) * (lam ^ (1 - 2 * h) *
          spatialSecondPartial (azimuthalVorticity u) 2 2
            (zoomPointRec lam h rc zc p))) := by
    have hev : (fun s : ℝ => dz (zoomTheta lam h rc zc u) ((p.1.1, s), p.2))
        =ᶠ[𝓝 p.1.2]
        fun s : ℝ => lam ^ 2 * lam ^ (2 * h) *
          (lam ^ (1 - 2 * h) * spatialPartial (azimuthalVorticity u) 2
            (zoomPointRec lam h rc zc ((p.1.1, s), p.2))) := by
      filter_upwards [(isOpen_slice_z_rec lam h rc zc p).mem_nhds hslice_z] with s hsmem
      exact ((hasDerivAt_zoomRecScalar_z lam h rc zc hOmega1
        ((p.1.1, s), p.2) hsmem).const_mul (lam ^ 2 * lam ^ (2 * h))).deriv
    have hrhs : HasDerivAt (fun s : ℝ => lam ^ 2 * lam ^ (2 * h) *
        (lam ^ (1 - 2 * h) * spatialPartial (azimuthalVorticity u) 2
          (zoomPointRec lam h rc zc ((p.1.1, s), p.2))))
        (lam ^ 2 * lam ^ (2 * h) *
          (lam ^ (1 - 2 * h) * (lam ^ (1 - 2 * h) *
            spatialSecondPartial (azimuthalVorticity u) 2 2
              (zoomPointRec lam h rc zc p)))) p.1.2 :=
      ((hasDerivAt_zoomRecScalar_z
        (Phi := fun w : ParabolicPoint => spatialPartial (azimuthalVorticity u) 2 w)
        lam h rc zc hpar2 p hp).const_mul (lam ^ (1 - 2 * h))).const_mul
        (lam ^ 2 * lam ^ (2 * h))
    rw [dz]
    exact (hrhs.congr_of_eventuallyEq hev).deriv
  -- the swirl source term
  have hswirlFun : (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2)
      = fun q : (ℝ × ℝ) × ℝ => lam ^ 2 * (lam ^ (2 * h)) ^ 2 *
          (u (zoomPointRec lam h rc zc q) 1 ^ 2) := by
    funext q
    change (lam * lam ^ (2 * h) * u (zoomPointRec lam h rc zc q) 1) ^ 2 = _
    ring
  have hswirl : dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) p
      = lam ^ 2 * (lam ^ (2 * h)) ^ 2 *
        (lam ^ (1 - 2 * h) *
          spatialPartial (fun w : ParabolicPoint => u w 1 ^ 2) 2
            (zoomPointRec lam h rc zc p)) := by
    rw [hswirlFun, dz]
    exact ((hasDerivAt_zoomRecScalar_z
      (Phi := fun w : ParabolicPoint => u w 1 ^ 2)
      lam h rc zc hswirlSmooth p hp).const_mul
      (lam ^ 2 * (lam ^ (2 * h)) ^ 2)).deriv
  -- the azimuthal vorticity equation at the recentred zoom point
  have hPDE := azimuthal_vorticity_pde u pres f hsol haxi
    (zoomPointRec lam h rc zc p) hp hplane hr_zoom
  rw [hz0] at hPDE
  rw [← curlComp_one f (zoomPointRec lam h rc zc p)] at hPDE
  have hdm : lam ^ (2 * h) * lam ^ (1 - 2 * h) = lam := (zoom_lambda_eq_delta_mul_mu hlam).symm
  have hReq : rc / lam + p.1.1 = (rc + lam * p.1.1) / lam := by rw [heq]; field_simp
  rw [hdt, hdr, hdz, hdrr, hdzz, hswirl]
  simp only [zoomVRec, zoomWRec, zoomTheta, hReq, div_pow, div_div_eq_mul_div]
  set T := timePartial (azimuthalVorticity u) (zoomPointRec lam h rc zc p)
  set Ar := spatialPartial (azimuthalVorticity u) 0 (zoomPointRec lam h rc zc p)
  set Az := spatialPartial (azimuthalVorticity u) 2 (zoomPointRec lam h rc zc p)
  set Arr := spatialSecondPartial (azimuthalVorticity u) 0 0 (zoomPointRec lam h rc zc p)
  set Azz := spatialSecondPartial (azimuthalVorticity u) 2 2 (zoomPointRec lam h rc zc p)
  set Sw := spatialPartial (fun w : ParabolicPoint => u w 1 ^ 2) 2
    (zoomPointRec lam h rc zc p)
  set Om := azimuthalVorticity u (zoomPointRec lam h rc zc p)
  set Fq := curlComp f 1 (zoomPointRec lam h rc zc p)
  set u0 := u (zoomPointRec lam h rc zc p) 0
  set u2 := u (zoomPointRec lam h rc zc p) 2
  set dd := lam ^ (2 * h)
  set mm := lam ^ (1 - 2 * h)
  linear_combination (lam ^ 4 * dd) * hPDE +
    (lam ^ 3 * dd * u2 * Az - lam ^ 2 * dd * Azz * (dd * mm + lam) -
      lam ^ 3 * dd * Sw / (rc + lam * p.1.1)) * hdm

/-! ### The receding-axis circulation identity and swirl bound -/

/-- The receding-axis circulation identity: `(A + R) * S_n = δ * Γ` at the recentred zoom
point, with `A = rc / lam` and `δ = lam ^ (2 * h)`. -/
theorem mul_zoomSRec_eq_circulation (lam h rc zc : ℝ) (hlam : lam ≠ 0)
    (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) :
    (rc / lam + p.1.1) * zoomSRec lam h rc zc u p
      = lam ^ (2 * h) * circulation u (zoomPointRec lam h rc zc p) := by
  have hz0 : (zoomPointRec lam h rc zc p).1 0 = rc + lam * p.1.1 := by
    simp [zoomPointRec, meridional]
  have hplane : (zoomPointRec lam h rc zc p).1 1 = 0 := by simp [zoomPointRec, meridional]
  unfold zoomSRec circulation
  rw [hz0, hplane]
  field_simp
  ring

/-- Item (c): the receding-axis circulation bound `|S_n| ≤ C_Γ δ / (A + R)`, for
`A + R > 0`. -/
theorem abs_zoomSRec_le_of_circulation {lam h rc zc CΓ : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} {p : (ℝ × ℝ) × ℝ} (hApos : 0 < rc / lam + p.1.1)
    (hΓ : |circulation u (zoomPointRec lam h rc zc p)| ≤ CΓ) :
    |zoomSRec lam h rc zc u p| ≤ CΓ * lam ^ (2 * h) / (rc / lam + p.1.1) := by
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have hA_ne : rc / lam + p.1.1 ≠ 0 := hApos.ne'
  have hδnn : (0 : ℝ) ≤ lam ^ (2 * h) := Real.rpow_nonneg hlam.le _
  have hSeq : zoomSRec lam h rc zc u p
      = lam ^ (2 * h) * circulation u (zoomPointRec lam h rc zc p) / (rc / lam + p.1.1) := by
    rw [eq_div_iff hA_ne, mul_comm]
    exact mul_zoomSRec_eq_circulation lam h rc zc hlam_ne u p
  rw [hSeq, abs_div, abs_of_pos hApos, abs_mul, abs_of_nonneg hδnn, mul_comm CΓ (lam ^ (2 * h))]
  gcongr

/-! ### The receding-axis swirl-source form and value bound -/

/-- Item (d), the form part: along the vertical slice through `p`, `A + R` does not depend
on `Z`, so the swirl-source term `1 / (A + R) * ∂_Z (S_n ^ 2)` of `zoomTheta_pde` is the
vertical derivative of the conservative swirl source `S_n ^ 2 / (A + R)`. -/
theorem dz_zoomSRecSq_div_eq (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) :
    dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2 / (rc / lam + q.1.1)) p
      = 1 / (rc / lam + p.1.1) * dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) p := by
  have hfun : (fun z : ℝ =>
      zoomSRec lam h rc zc u ((p.1.1, z), p.2) ^ 2 / (rc / lam + p.1.1))
      = fun z : ℝ =>
        (1 / (rc / lam + p.1.1)) * zoomSRec lam h rc zc u ((p.1.1, z), p.2) ^ 2 := by
    funext z; ring
  change deriv (fun z : ℝ => zoomSRec lam h rc zc u ((p.1.1, z), p.2) ^ 2 / (rc / lam + p.1.1))
      p.1.2 = _
  rw [hfun, deriv_const_mul_field]
  rfl

/-- Item (d), the value bound: the receding-axis swirl-source value `S_n ^ 2 / (A + R)` is
bounded by `C_Γ ^ 2 δ ^ 2 / (A + R) ^ 3`, for `A + R > 0`, from the circulation bound of
`abs_zoomSRec_le_of_circulation`. -/
theorem abs_zoomSRecSq_div_le {lam h rc zc CΓ : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} {p : (ℝ × ℝ) × ℝ} (hApos : 0 < rc / lam + p.1.1)
    (hCΓ : 0 ≤ CΓ) (hΓ : |circulation u (zoomPointRec lam h rc zc p)| ≤ CΓ) :
    |zoomSRec lam h rc zc u p ^ 2 / (rc / lam + p.1.1)|
      ≤ CΓ ^ 2 * (lam ^ (2 * h)) ^ 2 / (rc / lam + p.1.1) ^ 3 := by
  have hS := abs_zoomSRec_le_of_circulation hlam hApos hΓ
  have hSnn : (0 : ℝ) ≤ |zoomSRec lam h rc zc u p| := abs_nonneg _
  have hbound : (0 : ℝ) ≤ CΓ * lam ^ (2 * h) / (rc / lam + p.1.1) :=
    div_nonneg (mul_nonneg hCΓ (Real.rpow_nonneg hlam.le _)) hApos.le
  have hsq : zoomSRec lam h rc zc u p ^ 2
      ≤ (CΓ * lam ^ (2 * h) / (rc / lam + p.1.1)) ^ 2 := by
    rw [← sq_abs (zoomSRec lam h rc zc u p)]
    exact pow_le_pow_left₀ hSnn hS 2
  have hpow : (CΓ * lam ^ (2 * h) / (rc / lam + p.1.1)) ^ 2
      = CΓ ^ 2 * (lam ^ (2 * h)) ^ 2 / (rc / lam + p.1.1) ^ 2 := by
    rw [div_pow, mul_pow]
  rw [hpow] at hsq
  rw [abs_div, abs_of_pos hApos]
  have hnum : zoomSRec lam h rc zc u p ^ 2 / (rc / lam + p.1.1)
      ≤ CΓ ^ 2 * (lam ^ (2 * h)) ^ 2 / (rc / lam + p.1.1) ^ 2 / (rc / lam + p.1.1) := by
    apply div_le_div_of_nonneg_right hsq hApos.le
  have habs : |zoomSRec lam h rc zc u p ^ 2| = zoomSRec lam h rc zc u p ^ 2 :=
    abs_of_nonneg (sq_nonneg _)
  rw [habs]
  refine hnum.trans_eq ?_
  rw [div_div]
  ring

/-! ### The receding preimage clause -/

/-- Extract coordinate-wise absolute bounds from a compact set in the product space, the
receding-axis copy of the analogous private helper of `CIV.Zoom.Preimage`. -/
private lemma exists_bound_of_compact_rec {K : Set ((ℝ × ℝ) × ℝ)} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ p ∈ K, |p.1.1| ≤ B ∧ |p.1.2| ≤ B ∧ |p.2| ≤ B := by
  have h_cont1 : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => p.1.1) K :=
    (continuous_fst.comp continuous_fst).continuousOn
  have h_cont2 : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => p.1.2) K :=
    (continuous_snd.comp continuous_fst).continuousOn
  have h_cont3 : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => p.2) K := continuous_snd.continuousOn
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn h_cont1
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn h_cont2
  obtain ⟨B3, hB3⟩ := hK.exists_bound_of_continuousOn h_cont3
  refine ⟨max (max B1 B2) B3, fun p hp => ?_⟩
  have h1 : |p.1.1| ≤ B1 := by have hx := hB1 p hp; rwa [Real.norm_eq_abs] at hx
  have h2 : |p.1.2| ≤ B2 := by have hy := hB2 p hp; rwa [Real.norm_eq_abs] at hy
  have h3 : |p.2| ≤ B3 := by have ht := hB3 p hp; rwa [Real.norm_eq_abs] at ht
  exact ⟨h1.trans ((le_max_left B1 B2).trans (le_max_left _ B3)),
    h2.trans ((le_max_right B1 B2).trans (le_max_left _ B3)),
    h3.trans (le_max_right _ B3)⟩

/-- The receding-axis meridional bound: replacing both meridional coordinates of the
recentred zoom point by their absolute triangle-inequality bounds can only increase the
squared meridional radius, since the radial slot now carries the offset `rc` exactly as
the axial slot already carries `zc`. -/
private lemma zoomPointRec_meridional_sq_le {lam h rc zc B' x y : ℝ} (hlam : 0 < lam)
    (hx : |x| ≤ B') (hy : |y| ≤ B') :
    (rc + lam * x) ^ 2 + (zc + lam ^ (1 - 2 * h) * y) ^ 2
      ≤ (|rc| + lam * B') ^ 2 + (|zc| + lam ^ (1 - 2 * h) * B') ^ 2 := by
  have hrpow : (0 : ℝ) ≤ lam ^ (1 - 2 * h) := Real.rpow_nonneg hlam.le _
  have habs1 : |rc + lam * x| ≤ |rc| + lam * B' := by
    refine (abs_add_le rc (lam * x)).trans ?_
    rw [abs_mul, abs_of_pos hlam]
    linarith only [mul_le_mul_of_nonneg_left hx hlam.le]
  have habs2 : |zc + lam ^ (1 - 2 * h) * y| ≤ |zc| + lam ^ (1 - 2 * h) * B' := by
    refine (abs_add_le zc (lam ^ (1 - 2 * h) * y)).trans ?_
    rw [abs_mul, abs_of_nonneg hrpow]
    linarith only [mul_le_mul_of_nonneg_left hy hrpow]
  have hsq1 : (rc + lam * x) ^ 2 ≤ (|rc| + lam * B') ^ 2 :=
    sq_le_sq' (neg_le_of_abs_le habs1) (le_of_abs_le habs1)
  have hsq2 : (zc + lam ^ (1 - 2 * h) * y) ^ 2 ≤ (|zc| + lam ^ (1 - 2 * h) * B') ^ 2 :=
    sq_le_sq' (neg_le_of_abs_le habs2) (le_of_abs_le habs2)
  linarith only [hsq1, hsq2]

/-- As `lam → 0⁺` the squared meridional radius of the receding-axis bounding point tends to
`rc ^ 2 + zc ^ 2`, so it eventually stays below any strictly larger level `R`. -/
private lemma eventually_meridional_sq_lt_rec {h rc zc R B' : ℝ} (hexp : 0 < 1 - 2 * h)
    (hm : rc ^ 2 + zc ^ 2 < R) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ),
      (|rc| + lam * B') ^ 2 + (|zc| + lam ^ (1 - 2 * h) * B') ^ 2 < R := by
  have hid : Tendsto (fun lam : ℝ => lam) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    Filter.Tendsto.mono_left tendsto_id nhdsWithin_le_nhds
  have hrpow : Tendsto (fun lam : ℝ => lam ^ (1 - 2 * h)) (𝓝[>] (0 : ℝ))
      (𝓝 ((0 : ℝ) ^ (1 - 2 * h))) :=
    Filter.Tendsto.mono_left
      (Real.continuousAt_rpow_const 0 (1 - 2 * h) (Or.inr hexp.le)).tendsto
      nhdsWithin_le_nhds
  have hlim : Tendsto
      (fun lam : ℝ => (|rc| + lam * B') ^ 2 + (|zc| + lam ^ (1 - 2 * h) * B') ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((|rc| + (0 : ℝ) * B') ^ 2 + (|zc| + (0 : ℝ) ^ (1 - 2 * h) * B') ^ 2)) :=
    ((tendsto_const_nhds.add (hid.mul tendsto_const_nhds)).pow 2).add
      ((tendsto_const_nhds.add (hrpow.mul tendsto_const_nhds)).pow 2)
  have hval : (|rc| + (0 : ℝ) * B') ^ 2 + (|zc| + (0 : ℝ) ^ (1 - 2 * h) * B') ^ 2 < R := by
    rw [Real.zero_rpow (ne_of_gt hexp), zero_mul, add_zero]
    have habs : rc ^ 2 + zc ^ 2 = |rc| ^ 2 + |zc| ^ 2 := by rw [sq_abs, sq_abs]
    linarith only [hm, habs]
  exact hlim.eventually_lt_const hval

/-- The parabolic time factor `lam ^ 2 * B'` eventually drops below any positive level, the
receding-axis copy of the analogous private helper of `CIV.Zoom.Preimage`. -/
private lemma eventually_sq_mul_lt_rec {B' c : ℝ} (hc : 0 < c) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ^ 2 * B' < c := by
  have hid : Tendsto (fun lam : ℝ => lam) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    Filter.Tendsto.mono_left tendsto_id nhdsWithin_le_nhds
  have hlim : Tendsto (fun lam : ℝ => lam ^ 2 * B') (𝓝[>] (0 : ℝ))
      (𝓝 ((0 : ℝ) ^ 2 * B')) := (hid.pow 2).mul tendsto_const_nhds
  have hval : (0 : ℝ) ^ 2 * B' < c := by
    rw [show ((0 : ℝ) ^ 2) = 0 by norm_num, zero_mul]
    exact hc
  exact hlim.eventually_lt_const hval

/-- Item (b), the cylinder clause: for a compact set `K` of negative-time points bounded
away from the axis offset by `|rc| ^ 2 + |zc| ^ 2 < ρ ^ 2 < 1`, the recentred zoom point of
every point of `K` eventually lies in the unit cylinder `Q`. -/
theorem eventually_zoomPointRec_mem_unitCylinder {h rc zc ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2)
    (hρ0 : 0 ≤ ρ) (hm : rc ^ 2 + zc ^ 2 < ρ ^ 2) (hρ : ρ < 1)
    (K : Set ((ℝ × ℝ) × ℝ)) (hK : IsCompact K) (hKt : ∀ p ∈ K, p.2 < 0) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ), ∀ p ∈ K, zoomPointRec lam h rc zc p ∈ unitCylinder := by
  have hexp : 0 < 1 - 2 * h := by linarith only [hh.2]
  have hρsq : ρ ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one ρ).mpr (by rwa [abs_of_nonneg hρ0])
  have hm1 : rc ^ 2 + zc ^ 2 < 1 := lt_trans hm hρsq
  obtain ⟨B, hB⟩ := exists_bound_of_compact_rec hK
  have hmer : ∀ᶠ lam in 𝓝[>] (0 : ℝ),
      (|rc| + lam * B) ^ 2 + (|zc| + lam ^ (1 - 2 * h) * B) ^ 2 < 1 :=
    eventually_meridional_sq_lt_rec (B' := B) hexp hm1
  have htime : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ^ 2 * B < 1 :=
    eventually_sq_mul_lt_rec (B' := B) (by norm_num)
  filter_upwards [self_mem_nhdsWithin, hmer, htime] with lam hlam hlam_mer hlam_time
  intro p hp
  have hlam_pos : (0 : ℝ) < lam := hlam
  obtain ⟨hx, hy, ht⟩ := hB p hp
  have hmul : lam ^ 2 * (-B) ≤ lam ^ 2 * p.2 :=
    mul_le_mul_of_nonneg_left (neg_le_of_abs_le ht) (sq_nonneg lam)
  rw [zoomPointRec_mem_unitCylinder_iff]
  refine ⟨lt_of_le_of_lt (zoomPointRec_meridional_sq_le hlam_pos hx hy) hlam_mer,
    mem_Ioo.mpr ⟨?_, mul_neg_of_pos_of_neg (pow_pos hlam_pos 2) (hKt p hp)⟩⟩
  linarith only [hmul, hlam_time]

/-- Item (b), the ball clause: for a compact set `K` bounded away from the axis offset by
`rc ^ 2 + zc ^ 2 < ρ ^ 2 < R_*`, the recentred zoom point of every point of `K` eventually
has its spatial part in the ball `B(R_*)`. -/
theorem eventually_zoomPointRec_mem_ball {h rc zc ρ Rstar : ℝ} (hh : 0 < h ∧ h < 1 / 2)
    (hρ0 : 0 ≤ ρ) (hm : rc ^ 2 + zc ^ 2 < ρ ^ 2) (hρ : ρ < Rstar)
    (K : Set ((ℝ × ℝ) × ℝ)) (hK : IsCompact K) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ), ∀ p ∈ K, (zoomPointRec lam h rc zc p).1 ∈ vec3Ball 0 Rstar := by
  have hexp : 0 < 1 - 2 * h := by linarith only [hh.2]
  have hRstar_pos : (0 : ℝ) < Rstar := lt_of_le_of_lt hρ0 hρ
  have hρsq : ρ ^ 2 < Rstar ^ 2 :=
    sq_lt_sq' (by linarith only [hρ0, hRstar_pos]) hρ
  have hm1 : rc ^ 2 + zc ^ 2 < Rstar ^ 2 := lt_trans hm hρsq
  obtain ⟨B, hB⟩ := exists_bound_of_compact_rec hK
  have hmer : ∀ᶠ lam in 𝓝[>] (0 : ℝ),
      (|rc| + lam * B) ^ 2 + (|zc| + lam ^ (1 - 2 * h) * B) ^ 2 < Rstar ^ 2 :=
    eventually_meridional_sq_lt_rec (B' := B) hexp hm1
  filter_upwards [self_mem_nhdsWithin, hmer] with lam hlam hlam_mer
  intro p hp
  have hlam_pos : (0 : ℝ) < lam := hlam
  obtain ⟨hx, hy, _⟩ := hB p hp
  have hfst : (zoomPointRec lam h rc zc p).1
      = meridional (rc + lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2) := rfl
  rw [hfst, meridional_mem_vec3Ball_zero_iff]
  exact ⟨lt_of_le_of_lt (zoomPointRec_meridional_sq_le hlam_pos hx hy) hlam_mer, hRstar_pos⟩

/-- Item (b), the time clause: the time slot of `zoomPointRec` is `lam ^ 2 * τ`, exactly as
for `zoomPoint`, independent of `rc`, so this reduces to `eventually_zoomPoint_time_mem`. -/
theorem eventually_zoomPointRec_time_mem (rc : ℝ) {h zc tstar : ℝ} (htstar : tstar < 0)
    (K : Set ((ℝ × ℝ) × ℝ)) (hK : IsCompact K) (hKt : ∀ p ∈ K, p.2 < 0) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ), ∀ p ∈ K, (zoomPointRec lam h rc zc p).2 ∈ Ioo tstar 0 := by
  filter_upwards [eventually_zoomPoint_time_mem (h := h) (zc := zc) htstar K hK hKt]
    with lam hlam p hp
  have heq : (zoomPointRec lam h rc zc p).2 = (zoomPoint lam h zc p).2 := rfl
  rw [heq]
  exact hlam p hp

/-- Item (b) in full: the ball and time clauses together, the set on which the
circulation bound `abs_zoomSRec_le_of_circulation` and the anisotropic bounds of
`CIV.Zoom.Receding` hold. -/
theorem eventually_zoomPointRec_mem_ball_and_time {h rc zc ρ Rstar tstar : ℝ}
    (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ) (hm : rc ^ 2 + zc ^ 2 < ρ ^ 2) (hρ : ρ < Rstar)
    (htstar : tstar < 0) (K : Set ((ℝ × ℝ) × ℝ)) (hK : IsCompact K) (hKt : ∀ p ∈ K, p.2 < 0) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ), ∀ p ∈ K,
      (zoomPointRec lam h rc zc p).1 ∈ vec3Ball 0 Rstar ∧
        (zoomPointRec lam h rc zc p).2 ∈ Ioo tstar 0 := by
  filter_upwards [eventually_zoomPointRec_mem_ball hh hρ0 hm hρ K hK,
    eventually_zoomPointRec_time_mem rc htstar K hK hKt] with lam hball htime p hp
  exact ⟨hball p hp, htime p hp⟩

/-- The receding-axis regime named in item (b): for a fixed positive radial offset `rc`,
the ratio `A = rc / lam` tends to infinity as the zoom scale `lam` shrinks to `0`. -/
theorem tendsto_zoomPointRec_ratio_atTop {rc : ℝ} (hrc : 0 < rc) :
    Tendsto (fun lam : ℝ => rc / lam) (𝓝[>] (0 : ℝ)) atTop := by
  have h1 : Tendsto (fun lam : ℝ => lam⁻¹ * rc) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero.atTop_mul_const hrc
  simpa [div_eq_inv_mul] using h1

end CIV
