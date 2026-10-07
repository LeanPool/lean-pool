/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.Hypotheses
public import LeanPool.CIVAxisymmetric.Closure.ClosureLemmaAssembly

/-!
# The public statement `CIV.Main.closureLemma`

This module proves the statement `CIV.closureLemma` (`lem:aniso:closure`). The proof is
`CIV.boundedNearOrigin_of_meridionalSmallness`: the regular annulus of `CIV.Main.regularAnnulus`,
the energy inequality `eq:aniso:closure:energy` for the canonical ball cutoff with the suprema `G`
and `W` fixed before the constant `C_*`, the choice `η = 1/(16 C_*)`, the swirl bound
`eq:aniso:closure:w` by the axis maximum principle, the Grönwall and `L⁶` steps, and the
Gustafson–Kang–Tsai criterion `CIV.Main.gktCriterion`.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV
namespace Main

/-- The public statement of the closure lemma `lem:aniso:closure`: for an axisymmetric
suitable weak solution, smooth on the unit cylinder, with an axisymmetric force satisfying
`eq:interior:force:c-two`, the smallness `lim_{t↑0} (-t) G_{ρ₀}(t) = 0` of `eq:aniso:closure:small`
for some `ρ₀ ∈ (0, 1)` makes `(0,0)` a regular point. -/
theorem closureLemma (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (hMf : ForceC2Bounded f)
    (ρ₀ : ℝ) (hρ₀ : ρ₀ ∈ Ioo (0 : ℝ) 1) (hsmall : MeridionalSmallness ρ₀ u) :
    BoundedNearOrigin u :=
  boundedNearOrigin_of_meridionalSmallness q u Du p f hsol henergy hu hp hf haxi hfaxi hMf
    ρ₀ hρ₀ hsmall

end Main
end CIV
