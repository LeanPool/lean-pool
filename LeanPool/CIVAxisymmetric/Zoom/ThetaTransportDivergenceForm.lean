/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingEquation

/-!
# Theta Transport Divergence Form

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

theorem zoomTheta_transport_divergenceForm (lam h rc zc : ℝ) (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder)
    (hR : p.1.1 ≠ -(rc / lam)) :
    zoomVRec lam h rc zc u p * dr (zoomTheta lam h rc zc u) p
        + zoomWRec lam h rc zc u p * dz (zoomTheta lam h rc zc u) p
      = dr (fun q => zoomVRec lam h rc zc u q * zoomTheta lam h rc zc u q) p
        + dz (fun q => zoomWRec lam h rc zc u q * zoomTheta lam h rc zc u q) p
        + zoomVRec lam h rc zc u p / (rc / lam + p.1.1) * zoomTheta lam h rc zc u p := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu.of_le (by exact_mod_cast le_top)
  have hOmega1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => azimuthalVorticity u z) unitCylinder :=
    (contDiffOn_azimuthalVorticity hu).of_le (by exact_mod_cast le_top)
  have hVr : DifferentiableAt ℝ (fun r : ℝ => zoomVRec lam h rc zc u ((r, p.1.2), p.2)) p.1.1 :=
    ((hasDerivAt_zoomRec_component_r lam h rc zc hu1 p hp 0).const_mul lam).differentiableAt
  have hWz : DifferentiableAt ℝ (fun s : ℝ => zoomWRec lam h rc zc u ((p.1.1, s), p.2)) p.1.2 :=
    ((hasDerivAt_zoomRec_component_z lam h rc zc hu1 p hp 2).const_mul
      (lam * lam ^ (2 * h))).differentiableAt
  have hTheta_r : DifferentiableAt ℝ (fun r : ℝ => azimuthalVorticity u (zoomPointRec lam h rc
    zc ((r, p.1.2), p.2))) p.1.1 :=
    (hasDerivAt_zoomRecScalar_r lam h rc zc hOmega1 p hp).differentiableAt
  have hTheta_z : DifferentiableAt ℝ (fun s : ℝ => azimuthalVorticity u (zoomPointRec lam h rc
    zc ((p.1.1, s), p.2))) p.1.2 :=
    (hasDerivAt_zoomRecScalar_z lam h rc zc hOmega1 p hp).differentiableAt
  have hThetaTheta_r : DifferentiableAt ℝ (fun r : ℝ => zoomTheta lam h rc zc u ((r, p.1.2),
    p.2)) p.1.1 :=
    (hTheta_r.hasDerivAt.const_mul (lam ^ 2 * lam ^ (2 * h))).differentiableAt
  have hThetaTheta_z : DifferentiableAt ℝ (fun s : ℝ => zoomTheta lam h rc zc u ((p.1.1, s),
    p.2)) p.1.2 :=
    (hTheta_z.hasDerivAt.const_mul (lam ^ 2 * lam ^ (2 * h))).differentiableAt
  have hprodR : dr (fun q => zoomVRec lam h rc zc u q * zoomTheta lam h rc zc u q) p
      = dr (zoomVRec lam h rc zc u) p * zoomTheta lam h rc zc u p
        + zoomVRec lam h rc zc u p * dr (zoomTheta lam h rc zc u) p :=
    (hVr.hasDerivAt.mul hThetaTheta_r.hasDerivAt).deriv
  have hprodZ : dz (fun q => zoomWRec lam h rc zc u q * zoomTheta lam h rc zc u q) p
      = dz (zoomWRec lam h rc zc u) p * zoomTheta lam h rc zc u p
        + zoomWRec lam h rc zc u p * dz (zoomTheta lam h rc zc u) p :=
    (hWz.hasDerivAt.mul hThetaTheta_z.hasDerivAt).deriv
  have hdiv := zoomRec_divergence_identity lam h rc zc hlam u pr f hsol haxi p hp hR
  rw [hprodR, hprodZ]
  linear_combination (-(zoomTheta lam h rc zc u p)) * hdiv

theorem zoomTheta_pde_divergenceForm (lam h rc zc : ℝ) (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder)
    (hR : p.1.1 ≠ -(rc / lam)) :
    dtPast (zoomTheta lam h rc zc u) p
        + dr (fun q => zoomVRec lam h rc zc u q * zoomTheta lam h rc zc u q) p
        + dz (fun q => zoomWRec lam h rc zc u q * zoomTheta lam h rc zc u q) p
      = dr (dr (zoomTheta lam h rc zc u)) p
        + 1 / (rc / lam + p.1.1) * dr (zoomTheta lam h rc zc u) p
        + (lam ^ (2 * h)) ^ 2 * dz (dz (zoomTheta lam h rc zc u)) p
        - zoomTheta lam h rc zc u p / (rc / lam + p.1.1) ^ 2
        + 1 / (rc / lam + p.1.1) * dz (fun q => zoomSRec lam h rc zc u q ^ 2) p
        + lam ^ 4 * lam ^ (2 * h) * curlComp f 1 (zoomPointRec lam h rc zc p) := by
  have hpde := zoomTheta_pde lam h rc zc hlam u pr f hsol haxi p hp hR
  have htr := zoomTheta_transport_divergenceForm lam h rc zc hlam u pr f hsol haxi p hp hR
  linarith only [hpde, htr]

end CIV
