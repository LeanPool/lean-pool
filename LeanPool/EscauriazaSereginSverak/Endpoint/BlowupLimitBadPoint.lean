/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupEnergyScaling
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupVanishing

/-!
# Bad-point lower bound in the blow-up limit

Badness gives a uniform lower bound at sufficiently small radii, while
vanishing of both limiting critical fields makes the unit-cylinder energy
tend to zero.
-/

public section


open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Every sufficiently small scale at a bad point has the stated rescaled
unit-cylinder energy lower bound. -/
theorem blowup_limit_bad_point_lower_bound
    (ε₀ : ℝ) (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hbad : ¬ IsGoodPoint ε₀ u p (x₀, t₀))
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0)) :
    ∀ᶠ k in atTop,
      ENNReal.ofReal (ε₀ / 8) ≤
        goodPointEnergy (blowupVelocity x₀ t₀ (r k) u)
          (blowupPressure x₀ t₀ (r k) p) 0 0 1 := by
  exact blowupBadPoint_eventually_lower ε₀ u p x₀ t₀ r
    hx₀ ht₀ hbad hr hr0

/-- Strong local critical-norm convergence to zero makes the blow-up energy
on the unit past cylinder tend to zero. -/
theorem blowup_limit_zero_alternative
    (v : ℕ → ParabolicPoint → Vec3) (p : ℕ → ParabolicPoint → ℝ)
    (hv : ∀ k, AEStronglyMeasurable
      (fun z => vec3EuclideanNorm (v k z))
      (volume.restrict (goodPointPastCylinder 0 0 1)))
    (hp : ∀ k, AEStronglyMeasurable (p k)
      (volume.restrict (goodPointPastCylinder 0 0 1)))
    (hV : Tendsto (fun k => eLpNorm
      (fun z => vec3EuclideanNorm (v k z)) 3
      (volume.restrict (goodPointPastCylinder 0 0 1))) atTop (nhds 0))
    (hP : Tendsto (fun k => eLpNorm (p k) (3 / 2 : ℝ≥0∞)
      (volume.restrict (goodPointPastCylinder 0 0 1))) atTop (nhds 0)) :
    Tendsto (fun k => goodPointEnergy (v k) (p k) 0 0 1)
      atTop (nhds 0) :=
  blowupUnitEnergy_tendsto_zero v p hv hp hV hP

end ESS
