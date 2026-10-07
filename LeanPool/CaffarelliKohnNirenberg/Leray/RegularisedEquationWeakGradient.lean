/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationIntervalPressure
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Classical slice derivatives as weak derivatives

Joint differentiability on a positive-time interval gives the slice weak
derivative identity needed to compare the mild equation with the forced weak
momentum identity.
-/

public section

open MeasureTheory
open CKN
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray





/-- If a forced representative agrees almost everywhere with a C¹ slice,
its mollified weak gradient agrees almost everywhere with the classical
spatial partial derivative of that slice. -/
theorem forcedMollifiedGrad_ae_eq_classical_of_ae_eq
    (v u : ParabolicPoint → Vec3) (t : ℝ) (i j : Fin 3)
    (hVloc : LocallyIntegrable (fun x : Vec3 => v (x, t) i) volume)
    (hVae : (fun x : Vec3 => v (x, t)) =ᵐ[volume]
      (fun x : Vec3 => u (x, t)))
    (hC1 : ContDiff ℝ 1 (fun x : Vec3 => u (x, t) i)) :
    (fun x : Vec3 => forcedMollifiedGrad v (x, t) i j) =ᵐ[volume]
      (fun x : Vec3 => spatialPartial (fun y => u y i) j (x, t)) := by
  let G : Vec3 → ℝ := fun x => spatialPartial (fun y => u y i) j (x, t)
  have hGcont : Continuous G := by
    change Continuous (fun x : Vec3 =>
      (fderiv ℝ (fun y : Vec3 => u (y, t) i) x) (basisVec j))
    exact (hC1.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const : Continuous fun _ : Vec3 => basisVec j)
  have hGloc : LocallyIntegrable G volume := hGcont.locallyIntegrable
  have hweakU : CKN.HasWeakPartialDerivOn (Set.univ : Set Vec3) j
      (fun x : Vec3 => u (x, t) i) G := by
    have h := CKN.HasWeakPartialDerivOn.of_contDiff
      (U := (Set.univ : Set Vec3)) (i := j) hC1
    simpa [G, spatialPartial] using h
  have hweakV : CKN.HasWeakPartialDerivOn (Set.univ : Set Vec3) j
      (fun x : Vec3 => v (x, t) i) G := by
    intro φ hφ hφc hφs
    have hleft : (∫ x in (Set.univ : Set Vec3),
        v (x, t) i * (fderiv ℝ φ x) (basisVec j)) =
        ∫ x in (Set.univ : Set Vec3),
          u (x, t) i * (fderiv ℝ φ x) (basisVec j) := by
      rw [setIntegral_univ, setIntegral_univ]
      apply integral_congr_ae
      filter_upwards [hVae] with x hx
      exact congrArg (fun w : Vec3 => w i * (fderiv ℝ φ x) (basisVec j)) hx
    rw [hleft]
    exact hweakU φ hφ hφc hφs
  exact forcedMollifiedGrad_slice_ae_eq hVloc hGloc hweakV

end CKN.Leray

end
