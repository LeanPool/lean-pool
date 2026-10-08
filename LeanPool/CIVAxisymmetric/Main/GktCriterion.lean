/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.Hypotheses
public import LeanPool.CIVAxisymmetric.Prerequisites.Gkt.Criterion

/-!
# The public statement `CIV.Main.gktCriterion`

This module proves the statement `CIV.gktCriterion`: smallness of the scale-invariant `L⁴_t L⁶_x`
quantity of `u` on top-boundary cylinders at the origin gives boundedness near the origin. The proof
is `CIV.boundedNearOrigin_of_L4L6_small`: Hölder turns the hypothesis into `L³` smallness, the Lin
pressure estimate is iterated over finitely many scales at base points below the top boundary, and
CKN's Theorem A in its top-boundary form concludes. The smoothness of `p` and `f` on the open
cylinder is not used.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV
namespace Main

/-- The public statement of the Gustafson–Kang–Tsai criterion, with the exponents
`p* = 6`, `q = 4`: if the scale-invariant `L⁴_t L⁶_x` norm of `u` on the top-boundary cylinders
`B(r) × (−r², 0)` tends to zero with `r`, then `u` is bounded near the origin. -/
theorem gktCriterion (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∫⁻ t in Ioo (-(r ^ 2)) 0,
        (∫⁻ x in vec3Ball 0 r, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ))
          ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal ε) :
    BoundedNearOrigin u := by
  -- the pressure and force smoothness hypotheses of the statement are not used by this proof
  have _hpCont : ContinuousOn (fun z : Vec3 × ℝ => p z) unitCylinder := hp.continuousOn
  have _hfCont : ContinuousOn (fun z : Vec3 × ℝ => f z) unitCylinder := hf.continuousOn
  exact boundedNearOrigin_of_L4L6_small q u Du p f hsol henergy hu hMf hsmall

end Main
end CIV
