/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Measure preservation on the plane from a unit Jacobian

Two generic change-of-variables facts for self-maps of `ℝ × ℝ`: an injective, everywhere
differentiable map whose Jacobian determinant is `1` at every point preserves the volume of every
measurable set, and a measurable map with such a two-sided inverse preserves Lebesgue measure.
Both are thin wrappers of `MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image`.

They are the "area formula" step in the proof of `cor:ideal-growth`, consumed by
`PeriodizedPlaneFlowData.measurePreserving_flow`
(`FastDynamo/Dynamics/Flow/PeriodizedFlowData.lean`);
nothing in them refers to the velocity, to a flow or to a parameter.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-! ## The area formula for a map of the plane with unit Jacobian -/

/-- **Change of variables with unit Jacobian.**  An injective, everywhere differentiable self-map
of the plane whose Jacobian determinant is `1` everywhere preserves the volume of every
measurable set.  This is `MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image` with the
integrand identically `1`; it is the "area formula" step in the proof of `cor:ideal-growth`. -/
theorem volume_image_of_det_fderiv_eq_one {f : (ℝ × ℝ) → ℝ × ℝ} (hf : Differentiable ℝ f)
    (hinj : Function.Injective f)
    (hdet : ∀ x : ℝ × ℝ, LinearMap.det ((fderiv ℝ f x : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) = 1)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) : volume (f '' s) = volume s := by
  have hchange := lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure (ℝ × ℝ)) hs
    (f' := fun x => fderiv ℝ f x) (fun x _ => (hf x).hasFDerivAt.hasFDerivWithinAt)
    hinj.injOn
  have hone : ∀ x : ℝ × ℝ, ENNReal.ofReal |(fderiv ℝ f x).det| = 1 := by
    intro x
    rw [show (fderiv ℝ f x).det = LinearMap.det ((fderiv ℝ f x : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) from rfl,
      hdet x]
    simp
  rw [← hchange]
  simp only [hone]
  exact setLIntegral_one s

/-- **Measure preservation from a unit Jacobian.**  A measurable self-map `f` of the plane with a
two-sided inverse `g` that is differentiable with unit Jacobian preserves Lebesgue measure: the
preimage of a measurable set under `f` is its image under `g`, whose volume is unchanged by
`volume_image_of_det_fderiv_eq_one`.  (Proof of `cor:ideal-growth`.) -/
theorem planeMeasurePreserving_of_det_fderiv_eq_one {f g : (ℝ × ℝ) → ℝ × ℝ}
    (hfmeas : Measurable f) (hg : Differentiable ℝ g)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ x, f (g x) = x)
    (hdet : ∀ x : ℝ × ℝ, LinearMap.det ((fderiv ℝ g x : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) = 1) :
    MeasurePreserving f volume volume := by
  refine ⟨hfmeas, ?_⟩
  have hginj : Function.Injective g := Function.LeftInverse.injective hfg
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hfmeas hs]
  have hpre : f ⁻¹' s = g '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨f x, hx, hgf x⟩
    · rintro ⟨y, hy, rfl⟩
      change f (g y) ∈ s
      rwa [hfg y]
  rw [hpre, volume_image_of_det_fderiv_eq_one hg hginj hdet hs]

end

end FastDynamo
