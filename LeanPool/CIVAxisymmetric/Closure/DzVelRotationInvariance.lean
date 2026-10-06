/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.StretchingBounds

/-!
# Rotation invariance of the vertical-derivative velocity gradient

`gradientSq_eq_polarR` and `curlSq_eq_polarR` transfer the Frobenius norm of `∇u` and the
Euclidean norm of `curl u` from a general point of the unit ball to its meridional
representative. The elliptic Cauchy–Schwarz step of `eq:aniso:closure:mixed:bound` needs the
same transfer one derivative order higher, for the second-derivative factor
`∂_z (∂_r u_z) = ∂_z∂_r u_z` of `eq:aniso:closure:mixed`: this file supplies it by observing
that `∂_z u` is itself a smooth axisymmetric field, so `gradientSq_eq_polarR` applies to it
directly.

The vertical derivative `∂_z u`, read componentwise (`dzVel`), intertwines the rotations about
the axis exactly as `u` does: `fderiv_comp_rotZ` applied to the direction `basisVec 2`, which
every `rotZ φ` fixes, gives `dzVel u (rotZ φ x, t) = rotZ φ (dzVel u (x, t))`
(`dzVel_rotZ_eq`), hence `dzVel u` is axisymmetric on the unit cylinder
(`isAxisymmetricOn_dzVel`) and, being a spatial derivative of a smooth field, is itself smooth
there (`contDiffOn_dzVel`). Feeding these into `gradientSq_eq_polarR` gives the invariance of
`∑ᵢⱼ (∂ⱼ∂_z uᵢ)²` (`dzGradientSq_eq_polarR`), which is exactly the sum containing
`(∂_z∂_r u_z)² = (spatialSecondPartial (u_z) 0 2)²` as one term.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-! ### The vertical derivative of the velocity, componentwise -/

/-- The vertical spatial derivative of the velocity, read componentwise: `∂_z u`. -/
@[expose] def dzVel (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : Vec3 :=
  fun i : Fin 3 => spatialPartial (fun w => u w i) 2 z

/-- Every rotation about the axis fixes the vertical basis vector. -/
theorem rotZ_basisVec_two (φ : ℝ) : rotZ φ (basisVec 2 : Vec3) = (basisVec 2 : Vec3) := by
  ext i
  fin_cases i <;> simp [rotZ, basisVec_apply]

/-- `dzVel` agrees with the full spatial derivative applied to the vertical basis vector. -/
theorem dzVel_eq_fderiv {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    dzVel u z = fderiv ℝ (fun y : Vec3 => u (y, z.2)) z.1 (basisVec 2) := by
  funext i
  exact spatialPartial_eq_fderiv_apply hu hz i 2

/-- `dzVel` intertwines the rotations about the axis, exactly like the velocity field itself:
`fderiv_comp_rotZ` at the direction `basisVec 2`, which every rotation fixes. -/
theorem dzVel_rotZ_eq {u : ParabolicPoint → Vec3} (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (φ : ℝ) :
    dzVel u (rotZ φ z.1, z.2) = rotZ φ (dzVel u z) := by
  have hz' : ((rotZ φ z.1 : Vec3), z.2) ∈ unitCylinder := rotZ_mem_unitCylinder φ hz
  have hkey := fderiv_comp_rotZ h hu hz φ (basisVec 2)
  rw [rotZ_basisVec_two] at hkey
  rw [dzVel_eq_fderiv hu hz', dzVel_eq_fderiv hu hz]
  exact hkey

/-- `dzVel u` is fixed by every rotation about the axis, in the `rotField` sense. -/
theorem rotField_dzVel_eq {u : ParabolicPoint → Vec3} (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) (φ : ℝ) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    rotField φ (dzVel u) z = dzVel u z := by
  have hz' : (((rotZ (-φ) z.1 : Vec3), z.2) : ParabolicPoint) ∈ unitCylinder :=
    rotZ_mem_unitCylinder (-φ) hz
  have hkey := dzVel_rotZ_eq h hu hz' φ
  rw [rotZ_rotZ_neg] at hkey
  exact hkey.symm

/-- `dzVel u` is axisymmetric on the unit cylinder whenever `u` is. -/
theorem isAxisymmetricOn_dzVel {u : ParabolicPoint → Vec3} (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) :
    IsAxisymmetricOn (dzVel u) unitCylinder :=
  isAxisymmetricOn_of_forall_rotField_eq fun φ _ hz => rotField_dzVel_eq h hu φ hz

/-- `dzVel u` is smooth on the unit cylinder whenever `u` is: it is a classical spatial
partial derivative of each component of `u`. -/
theorem contDiffOn_dzVel {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => dzVel u z) unitCylinder :=
  contDiffOn_pi.2 fun i => contDiffOn_spatialPartial (contDiffOn_component hu i) 2

/-! ### The transfer to the meridional representative -/

/-- **The rotation invariance behind `eq:aniso:closure:mixed:bound`'s Cauchy–Schwarz step.**
The sum `∑ᵢⱼ (∂ⱼ∂_z uᵢ)²` — the Frobenius norm of the gradient of `∂_z u` — is invariant under
the rotations about the axis, transferring the value at a general point to the value at its
meridional representative exactly as `gradientSq_eq_polarR` does for `∇u` itself: `∂_z u` is
again a smooth axisymmetric field (`isAxisymmetricOn_dzVel`, `contDiffOn_dzVel`), so
`gradientSq_eq_polarR` applies to it directly. -/
theorem dzGradientSq_eq_polarR {u : ParabolicPoint → Vec3} (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) {x : Vec3} {t : ℝ}
    (hz : ((x, t) : ParabolicPoint) ∈ unitCylinder) :
    ∑ i : Fin 3, ∑ j : Fin 3, (spatialSecondPartial (fun w => u w i) 2 j (x, t)) ^ 2
      = ∑ i : Fin 3, ∑ j : Fin 3,
          (spatialSecondPartial (fun w => u w i) 2 j (meridional (polarR x) (x 2), t)) ^ 2 := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu.of_le (by exact_mod_cast le_top)
  have hdz1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => dzVel u z) unitCylinder :=
    (contDiffOn_dzVel hu).of_le (by exact_mod_cast le_top)
  exact gradientSq_eq_polarR (isAxisymmetricOn_dzVel h hu1) hdz1 hz

end CIV
