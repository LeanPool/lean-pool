/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressurePackageForce
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierCoordinateL2Bridge

/-!
# The force-pressure gradient of the zero force

The pointwise force-pressure gradient `forcePressureGradientFunction` vanishes
identically on the zero coordinate field, as used for (R3) of
`thm:regularised` with zero forcing.
-/

public section

open MeasureTheory
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The pointwise force-pressure gradient of the zero coordinate field is
identically zero. -/
theorem forcePressureGradientFunction_zero
    (hf : MemLp (fun _ : Vec3 => (0 : Vec3)) 2 volume) :
    forcePressureGradientFunction (fun _ : Vec3 => (0 : Vec3)) hf = fun _ => 0 := by
  have hin : realVectorL2OfCoordinateFunction (fun _ : Vec3 => (0 : Vec3)) hf = 0 := by
    apply realVectorL2Representative_injective_ae
    have hrep0 : realVectorL2Representative (0 : RealVectorL2) = fun _ => 0 := by
      funext x
      simp [realVectorL2Representative]
    rw [hrep0]
    exact realVectorL2OfCoordinateFunction_rep (fun _ : Vec3 => (0 : Vec3)) hf
  have hgrad : forcePressureGradientL2 (0 : RealVectorL2) = 0 :=
    norm_eq_zero.mp (le_antisymm
      ((forcePressureGradientL2_norm_le 0).trans_eq (by simp)) (norm_nonneg _))
  unfold forcePressureGradientFunction
  change forcePressureGradientRepresentative (forcePressureGradientL2
    (realVectorL2OfCoordinateFunction (fun _ : Vec3 => (0 : Vec3)) hf)) = fun _ => 0
  rw [hin, hgrad]
  funext x
  simp [forcePressureGradientRepresentative]


end CKN.Leray
