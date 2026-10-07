/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.Hypotheses
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.InteriorEstimates

/-!
# The public statement `CIV.Main.serrinInteriorEstimates`

This module proves the statement `CIV.serrinInteriorEstimates`: on a cylindrical annulus inside the
unit cylinder where the velocity is bounded, and with the force bounded in `C²`, the velocity and
its spatial derivatives through order two are bounded on every smaller annulus, uniformly up to the
blow-up time. The proof is `CIV.serrin_interior_estimates_of_suitable`: the weak solution is
classical on the open cylinder, the vorticity equation in divergence form is estimated level by
level through its cut-off heat representation and a distance-weighted absorption, and the velocity
derivatives are recovered from the vorticity by the Newtonian potential. The energy class is not
used.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV
namespace Main

/-- The public statement of Serrin's interior estimates: bounds for the velocity and its spatial
derivatives through order two on a smaller annular cylinder, uniformly up to the blow-up time. -/
theorem serrinInteriorEstimates (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f)
    (Rm Rp t₀ : ℝ) (hR : 0 ≤ Rm ∧ Rm < Rp ∧ Rp ≤ 1) (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    (Mu : ℝ) (hbdd : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ 0, vec3EuclideanNorm (u (x, t)) ≤ Mu)
    (Rm' Rp' t₀' : ℝ) (hR' : Rm < Rm' ∧ Rm' < Rp' ∧ Rp' < Rp) (ht₀' : t₀ < t₀' ∧ t₀' < 0) :
    ∃ K : ℝ, ∀ x : Vec3, Rm' < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp' →
      ∀ t ∈ Ioo t₀' 0, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ K := by
  -- the energy-class hypothesis of the statement is not used by this proof
  have _henergy : GlobalEnergyClass u Du p := henergy
  exact serrin_interior_estimates_of_suitable q u Du p f hsol hu hp hf hMf Rm Rp t₀ hR ht₀ Mu
    hbdd Rm' Rp' t₀' hR' ht₀'

end Main
end CIV
