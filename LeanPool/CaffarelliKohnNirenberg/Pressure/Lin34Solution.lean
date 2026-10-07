/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Lin34Faithful

/-!
# Solution-level Lin 3.4 pressure estimates

This module exposes the pointwise solenoidal estimate and both integrated
pressure estimates of `prop:lin34` through the pressure namespace.
-/

public section

open MeasureTheory
open CKN.Foundation.Parabolic Set
open scoped ENNReal


noncomputable section

namespace CKN.Pressure

/-- The three solution-level conclusions of `prop:lin34`.  The first two use
the local space-time distributional divergence condition; the general-force
bound uses the tree's `q`-dependent dominating normalization of `C₃₂(q)`. -/
theorem pressure_lin34_of_sws (q : ℝ) :
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r → r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      (((∀ ψ : Vec3 × ℝ → ℝ,
          ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
          IntegrableOn (fun w => ∑ i : Fin 3, f w i * spatialPartial ψ i w)
              (tsupport ψ) volume ∧
            ∫ w in spaceTimeSet Ω I,
              ∑ i : Fin 3, f w i * spatialPartial ψ i w = 0) →
          ((∀ᵐ t ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          r⁻¹ ^ 2 * ∫ y in vec3Ball z.1 r, |p (y, t)| ^ (3 / 2 : ℝ) ≤
            lin34AbsoluteConstant *
              ((ρ / r) ^ 2 * (ρ⁻¹ ^ 2 *
                  ∫ y in vec3Ball z.1 ρ,
                    vec3EuclideanNorm (meanFreeVec u z.1 ρ t y) ^ (3 : ℕ)) +
                (r / ρ) * (ρ⁻¹ ^ 2 *
                  ∫ y in vec3Ball z.1 ρ, |p (y, t)| ^ (3 / 2 : ℝ)))) ∧
          pressureD p z r ≤ lin34AbsoluteConstant *
            ((ρ / r) ^ 2 * pressureChat u z ρ +
              (r / ρ) * pressureD p z ρ))) ∧
        pressureD p z r ≤ CKN.Core.Endgame.theoremALin34Constant q *
          ((ρ / r) ^ 2 * pressureChat u z ρ +
            (r / ρ) * pressureD p z ρ +
            (r / ρ) ^ (3 / 2 : ℝ) * lambda q f z ρ ^ (3 / 2 : ℝ))) := by
  exact CKN.pressure_lin34_of_sws q

end CKN.Pressure

end
