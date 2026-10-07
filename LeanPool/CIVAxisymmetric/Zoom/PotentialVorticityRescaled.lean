/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.ChainRule
public import LeanPool.CIVAxisymmetric.Identities.PotentialVorticity

/-!
# Potential Vorticity Rescaled

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- The rescaled potential vorticity `Ω_n = λ³ δ Ω` of `eq:aniso:zoom:fields`. -/
@[expose] def zoomOmega (lam h zc : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  lam ^ 3 * lam ^ (2 * h) * potentialVorticity u (zoomPoint lam h zc p)

theorem zoomOmega_eq (lam h zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) (hR : p.1.1 ≠ 0) :
    zoomOmega lam h zc u p =
      ((lam ^ (2 * h)) ^ 2 * dz (zoomV lam h zc u) p - dr (zoomW lam h zc u) p) / p.1.1 := by
  set δ := lam ^ (2 * h) with hδ_def
  set μ := lam ^ (1 - 2 * h) with hμ_def
  have hδμ : δ * μ = lam := by
    dsimp [δ, μ]
    calc
      lam ^ (2 * h) * lam ^ (1 - 2 * h) = lam ^ ((2 * h) + (1 - 2 * h)) := by
        rw [Real.rpow_add hlam]
      _ = lam ^ (1 : ℝ) := by
        congr 1
        ring
      _ = lam := by simp
  have hz0_ne : (zoomPoint lam h zc p).1 0 ≠ 0 := by
    dsimp [zoomPoint, meridional]
    exact mul_ne_zero (by linarith only [hlam, hR]) hR
  have hlam_ne : lam ≠ 0 := by linarith only [hlam]
  have h_zoomPoint_fst0 : (zoomPoint lam h zc p).1 0 = lam * p.1.1 := by
    simp [zoomPoint, meridional]
  unfold zoomOmega
  rw [potentialVorticity_eq_div u hz0_ne, azimuthalVorticity, curlComp_one]
  rw [h_zoomPoint_fst0]
  rw [dz_zoomV lam h zc u hu p hp, dr_zoomW lam h zc u hu p hp]
  have h_denom1 : lam * p.1.1 ≠ 0 := mul_ne_zero hlam_ne hR
  rw [← mul_div_assoc, div_eq_iff h_denom1]
  -- Goal: lam^3 * lam^(2h) * (A - B) = ((δ^2 * lam * lam^(1-2h) * A - lam^2 * lam^(2h) *
  -- B) / p.1.1) * (lam * p.1.1)
  -- Simplify RHS: (X / p.1.1) * (lam * p.1.1) = X * lam
  have hsimp : ∀ (X : ℝ), (X / p.1.1) * (lam * p.1.1) = X * lam := by
    intro X
    field_simp [hR]
  rw [hsimp]
  dsimp [δ, μ] at hδμ ⊢
  -- Goal: lam^3 * lam^(2h) * (A - B) = ((lam^(2h))^2 * lam * lam^(1-2h) * A - lam^2 *
  -- lam^(2h) * B) * lam
  have hkey : lam ^ 3 * lam ^ (2 * h) = (lam ^ (2 * h)) ^ 2 * lam ^ 2 * lam ^ (1 - 2 * h) := by
    calc
      lam ^ 3 * lam ^ (2 * h) = lam ^ (2 * h) * lam ^ 2 * lam := by
        ring_nf
      _ = lam ^ (2 * h) * lam ^ 2 * (lam ^ (2 * h) * lam ^ (1 - 2 * h)) := by rw [hδμ]
      _ = (lam ^ (2 * h)) ^ 2 * lam ^ 2 * lam ^ (1 - 2 * h) := by
        ring_nf
  calc
    lam ^ 3 * lam ^ (2 * h) * ((spatialPartial (fun w => u w 0) 2 (zoomPoint lam h zc p)) -
      (spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc p)))
        = (lam ^ 3 * lam ^ (2 * h)) * (spatialPartial (fun w => u w 0) 2 (zoomPoint lam h zc p)) -
          (lam ^ 3 * lam ^ (2 * h)) * (spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc p))
            := by
        ring_nf
    _ = ((lam ^ (2 * h)) ^ 2 * lam ^ 2 * lam ^ (1 - 2 * h)) * (spatialPartial (fun w => u w 0) 2
      (zoomPoint lam h zc p)) -
        (lam ^ 3 * lam ^ (2 * h)) * (spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc p))
          := by rw [hkey]
    _ = ((lam ^ (2 * h)) ^ 2 * lam * lam ^ (1 - 2 * h) *
        (spatialPartial (fun w => u w 0) 2 (zoomPoint lam h zc p)) -
        lam ^ 2 * lam ^ (2 * h) * (spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc p))) *
          lam := by
        ring_nf
    _ = (((lam ^ (2 * h)) ^ 2 * (lam * lam ^ (1 - 2 * h) *
        (spatialPartial (fun w => u w 0) 2 (zoomPoint lam h zc p))) -
        lam ^ 2 * lam ^ (2 * h) * (spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc p))) *
          lam) := by
        ring_nf

end CIV
