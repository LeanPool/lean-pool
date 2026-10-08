/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.AnisotropicBounds
public import LeanPool.CIVAxisymmetric.Zoom.ChainRule
public import LeanPool.CIVAxisymmetric.Zoom.ChainRuleSecond
public import LeanPool.CIVAxisymmetric.Zoom.Exponents

/-!
# Rescaled anisotropic bounds (`eq:aniso:zoom:derivatives`)

The anisotropic Type II bounds `eq:aniso:bounds` are invariant under the zoom-in map
`eq:aniso:zoom:finite:variables`: the rescaled fields `zoomV`, `zoomW`, `zoomS` of
`eq:aniso:zoom:fields` obey the *same* bounds, with the *same* constant `C`, in the
rescaled parabolic time `p.2`.

Each of the twelve statements below is an instantiation of one of the two private
scale-invariance lemmas: the derivative is rewritten by the chain rules of
`CIV.Zoom.ChainRule` / `CIV.Zoom.ChainRuleSecond`, `AnisotropicBounds` is applied at the
zoomed point `zoomPoint lam h zc p`, whose parabolic time is `lam ^ 2 * p.2`, and the
`lam` prefactors are cancelled against that `lam ^ 2` by `zoom_rescaled_exponent`
(radial component) or `zoom_rescaled_exponent_swirl` (vertical and swirl components).
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- Scale invariance of the radial anisotropic bound. If `F` is the `lam`-prefactored
meridional derivative `∂₁^a ∂₃^b u_r` evaluated at the zoomed point, then `F` obeys the
anisotropic bound of order `(a, b)` in the rescaled time `p.2`. -/
private theorem abs_zoomV_prefactor_le {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) (a b : ℕ) (hab : a + b ≤ 2)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) (F e : ℝ)
    (hF : F = lam ^ (1 + a) * (lam ^ (1 - 2 * h)) ^ b *
      meridionalPartial (fun z => u z 0) a b (zoomPoint lam h zc p))
    (he : e = -(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ)) :
    |F| ≤ C * (-p.2) ^ e := by
  subst hF
  subst he
  have hlamsq : (0 : ℝ) < lam ^ 2 := by positivity
  have htime : lam ^ 2 * p.2 < 0 :=
    ((zoomPoint_mem_unitCylinder_iff lam h zc p).mp hp).2.2
  have htau : p.2 < 0 := by nlinarith only [htime, hlamsq]
  have hKnn : (0 : ℝ) ≤ lam ^ (1 + a) * (lam ^ (1 - 2 * h)) ^ b :=
    mul_nonneg (pow_nonneg hlam.le _) (pow_nonneg (Real.rpow_nonneg hlam.le _) _)
  have hbound :=
    (hb a b hab (lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2) (lam ^ 2 * p.2) hp).1
  rw [abs_mul, abs_of_nonneg hKnn]
  refine (mul_le_mul_of_nonneg_left hbound hKnn).trans_eq ?_
  have hneg : -(lam ^ 2 * p.2) = lam ^ 2 * (-p.2) := by ring
  rw [hneg]
  calc
    lam ^ (1 + a) * (lam ^ (1 - 2 * h)) ^ b *
        (C * (lam ^ 2 * (-p.2)) ^ (-(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ)))
        = C * (lam ^ (1 + a) * (lam ^ (1 - 2 * h)) ^ b *
          (lam ^ 2 * (-p.2)) ^ (-(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ))) := by
      ring
    _ = C * (-p.2) ^ (-(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ)) := by
      rw [zoom_rescaled_exponent hlam a b p.2 htau]

/-- Scale invariance of the joint vertical/swirl anisotropic bound. If `F` and `G` are the
`lam`-prefactored meridional derivatives `∂₁^a ∂₃^b u_z` and `∂₁^a ∂₃^b u_θ` evaluated at
the zoomed point, then `|F| + |G|` obeys the anisotropic bound of order `(a, b)` in the
rescaled time `p.2`. -/
private theorem abs_zoomWS_prefactor_le {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) (a b : ℕ) (hab : a + b ≤ 2)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) (F G e : ℝ)
    (hF : F = lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
      meridionalPartial (fun z => u z 2) a b (zoomPoint lam h zc p))
    (hG : G = lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
      meridionalPartial (fun z => u z 1) a b (zoomPoint lam h zc p))
    (he : e = -(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ)) :
    |F| + |G| ≤ C * (-p.2) ^ e := by
  subst hF
  subst hG
  subst he
  have hlamsq : (0 : ℝ) < lam ^ 2 := by positivity
  have htime : lam ^ 2 * p.2 < 0 :=
    ((zoomPoint_mem_unitCylinder_iff lam h zc p).mp hp).2.2
  have htau : p.2 < 0 := by nlinarith only [htime, hlamsq]
  have hKnn : (0 : ℝ) ≤ lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b :=
    mul_nonneg (mul_nonneg (pow_nonneg hlam.le _) (Real.rpow_nonneg hlam.le _))
      (pow_nonneg (Real.rpow_nonneg hlam.le _) _)
  have hbound :=
    (hb a b hab (lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2) (lam ^ 2 * p.2) hp).2
  have habsW : |lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
      meridionalPartial (fun z => u z 2) a b (zoomPoint lam h zc p)|
      = lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
        |meridionalPartial (fun z => u z 2) a b (zoomPoint lam h zc p)| := by
    rw [abs_mul, abs_of_nonneg hKnn]
  have habsS : |lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
      meridionalPartial (fun z => u z 1) a b (zoomPoint lam h zc p)|
      = lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
        |meridionalPartial (fun z => u z 1) a b (zoomPoint lam h zc p)| := by
    rw [abs_mul, abs_of_nonneg hKnn]
  rw [habsW, habsS, ← mul_add]
  refine (mul_le_mul_of_nonneg_left hbound hKnn).trans_eq ?_
  have hneg : -(lam ^ 2 * p.2) = lam ^ 2 * (-p.2) := by ring
  rw [hneg]
  calc
    lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
        (C * (lam ^ 2 * (-p.2)) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ)))
        = C * (lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
          (lam ^ 2 * (-p.2)) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ))) := by
      ring
    _ = C * (-p.2) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ)) := by
      rw [zoom_rescaled_exponent_swirl hlam a b p.2 htau]

theorem abs_zoomV_le (C h lam zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    |zoomV lam h zc u p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - 0 / 2 - (1 / 2 - h) * 0) := by
  refine abs_zoomV_prefactor_le hlam hb 0 0 (by omega) p hp _ _ ?_ (by norm_num)
  simp only [meridionalPartial, Function.iterate_zero_apply]
  rw [zoomV]
  ring

theorem abs_dr_zoomV_le (C h lam zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    |dr (zoomV lam h zc u) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - 1 / 2 - (1 / 2 - h) * 0) := by
  refine abs_zoomV_prefactor_le hlam hb 1 0 (by omega) p hp _ _ ?_ (by norm_num)
  rw [dr_zoomV lam h zc u (hu.of_le (by norm_num)) p hp]
  simp only [meridionalPartial, Function.iterate_zero_apply, Function.iterate_one]
  ring

theorem abs_dz_zoomV_le (C h lam zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    |dz (zoomV lam h zc u) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - 0 / 2 - (1 / 2 - h) * 1) := by
  refine abs_zoomV_prefactor_le hlam hb 0 1 (by omega) p hp _ _ ?_ (by norm_num)
  rw [dz_zoomV lam h zc u (hu.of_le (by norm_num)) p hp]
  simp only [meridionalPartial, Function.iterate_zero_apply, Function.iterate_one]
  ring

theorem abs_drdr_zoomV_le (C h lam zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    |dr (dr (zoomV lam h zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - 2 / 2 - (1 / 2 - h) * 0) := by
  refine abs_zoomV_prefactor_le hlam hb 2 0 (by omega) p hp _ _ ?_ (by norm_num)
  rw [drdr_zoomV lam h zc u hu p hp]
  ring

theorem abs_drdz_zoomV_le (C h lam zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    |dr (dz (zoomV lam h zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - 1 / 2 - (1 / 2 - h) * 1) := by
  refine abs_zoomV_prefactor_le hlam hb 1 1 (by omega) p hp _ _ ?_ (by norm_num)
  rw [drdz_zoomV lam h zc u hu p hp]
  ring

theorem abs_dzdz_zoomV_le (C h lam zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    |dz (dz (zoomV lam h zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - 0 / 2 - (1 / 2 - h) * 2) := by
  refine abs_zoomV_prefactor_le hlam hb 0 2 (by omega) p hp _ _ ?_ (by norm_num)
  rw [dzdz_zoomV lam h zc u hu p hp]
  ring

theorem abs_zoomW_add_abs_zoomS_le (C h lam zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    |zoomW lam h zc u p| + |zoomS lam h zc u p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 0 / 2 - (1 / 2 - h) * 0) := by
  refine abs_zoomWS_prefactor_le hlam hb 0 0 (by omega) p hp _ _ _ ?_ ?_ (by norm_num)
  · simp only [meridionalPartial, Function.iterate_zero_apply]
    rw [zoomW]
    ring
  · simp only [meridionalPartial, Function.iterate_zero_apply]
    rw [zoomS]
    ring

theorem abs_dr_zoomW_add_abs_dr_zoomS_le (C h lam zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint →
    Vec3)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    |dr (zoomW lam h zc u) p| + |dr (zoomS lam h zc u) p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 1 / 2 - (1 / 2 - h) * 0) := by
  refine abs_zoomWS_prefactor_le hlam hb 1 0 (by omega) p hp _ _ _ ?_ ?_ (by norm_num)
  · rw [dr_zoomW lam h zc u (hu.of_le (by norm_num)) p hp]
    simp only [meridionalPartial, Function.iterate_zero_apply, Function.iterate_one]
    ring
  · rw [dr_zoomS lam h zc u (hu.of_le (by norm_num)) p hp]
    simp only [meridionalPartial, Function.iterate_zero_apply, Function.iterate_one]
    ring

theorem abs_dz_zoomW_add_abs_dz_zoomS_le (C h lam zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint →
    Vec3)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    |dz (zoomW lam h zc u) p| + |dz (zoomS lam h zc u) p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 0 / 2 - (1 / 2 - h) * 1) := by
  refine abs_zoomWS_prefactor_le hlam hb 0 1 (by omega) p hp _ _ _ ?_ ?_ (by norm_num)
  · rw [dz_zoomW lam h zc u (hu.of_le (by norm_num)) p hp]
    simp only [meridionalPartial, Function.iterate_zero_apply, Function.iterate_one]
    ring
  · rw [dz_zoomS lam h zc u (hu.of_le (by norm_num)) p hp]
    simp only [meridionalPartial, Function.iterate_zero_apply, Function.iterate_one]
    ring

theorem abs_drdr_zoomW_add_abs_drdr_zoomS_le (C h lam zc : ℝ) (hlam : 0 < lam) (u :
    ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    |dr (dr (zoomW lam h zc u)) p| + |dr (dr (zoomS lam h zc u)) p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 2 / 2 - (1 / 2 - h) * 0) := by
  refine abs_zoomWS_prefactor_le hlam hb 2 0 (by omega) p hp _ _ _ ?_ ?_ (by norm_num)
  · rw [drdr_zoomW lam h zc u hu p hp]
    ring
  · rw [drdr_zoomS lam h zc u hu p hp]
    ring

theorem abs_drdz_zoomW_add_abs_drdz_zoomS_le (C h lam zc : ℝ) (hlam : 0 < lam) (u :
    ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    |dr (dz (zoomW lam h zc u)) p| + |dr (dz (zoomS lam h zc u)) p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 1 / 2 - (1 / 2 - h) * 1) := by
  refine abs_zoomWS_prefactor_le hlam hb 1 1 (by omega) p hp _ _ _ ?_ ?_ (by norm_num)
  · rw [drdz_zoomW lam h zc u hu p hp]
    ring
  · rw [drdz_zoomS lam h zc u hu p hp]
    ring

theorem abs_dzdz_zoomW_add_abs_dzdz_zoomS_le (C h lam zc : ℝ) (hlam : 0 < lam) (u :
    ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    |dz (dz (zoomW lam h zc u)) p| + |dz (dz (zoomS lam h zc u)) p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 0 / 2 - (1 / 2 - h) * 2) := by
  refine abs_zoomWS_prefactor_le hlam hb 0 2 (by omega) p hp _ _ _ ?_ ?_ (by norm_num)
  · rw [dzdz_zoomW lam h zc u hu p hp]
    ring
  · rw [dzdz_zoomS lam h zc u hu p hp]
    ring

end CIV
