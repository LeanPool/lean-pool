/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.NewtonianRepresentationSource
public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZHarmonicCorollaryParts

/-!
# CZHarmonic Residual Identification

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean
noncomputable section

namespace CKN

/-- The first pressure part agrees almost everywhere with the completed
double-Riesz extension of the localized tensor source on almost every slice. -/
theorem czPressurePart_ae_eq_rieszSecond_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) {z : ParabolicPoint} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      czPressurePart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => ⨍ y in vec3Ball z.1 ρ, u (y, t) j) p f s =ᵐ[volume]
        pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
          (czPressureSource (mollifiedBallCutoff z.1 hρ) u
            (fun t j => ⨍ y in vec3Ball z.1 ρ, u (y, t) j) s) := by
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  let c : ℝ → Vec3 := fun t j => ⨍ y in vec3Ball z.1 ρ, u (y, t) j
  have hrepr := pressure_newtonian_representation_source hsol hρ hsub
  have hrepr' :
      ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
        (fun x => η x * p (x, s)) =ᵐ[volume]
          (fun x => pressureSecondExtensionOperator rieszSecondL2Input
            rieszSecondL2_weak_type
              (fun i j y => η y * pressureUTensor u c (y, s) i j) x +
            pressureP2 η u c s x + pressureP3 η u c s x +
            pressureP4 η u c s x + pressureP5 η p s x +
            pressureP6 η p s x + pressureP7 η f s x + pressureP8 η f s x) := by
    simpa [η, c] using hrepr
  filter_upwards [hrepr'] with s hs
  filter_upwards [hs] with x hx
  change η x * p (x, s) =
    pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
      (fun i j y => η y * pressureUTensor u c (y, s) i j) x +
        pressureP2 η u c s x + pressureP3 η u c s x +
        pressureP4 η u c s x + pressureP5 η p s x +
        pressureP6 η p s x + pressureP7 η f s x + pressureP8 η f s x at hx
  change η x * p (x, s) -
      (pressureP2 η u c s x + pressureP3 η u c s x +
        pressureP4 η u c s x + pressureP5 η p s x +
        pressureP6 η p s x + pressureP7 η f s x + pressureP8 η f s x) =
    pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
      (fun i j y => η y * pressureUTensor u c (y, s) i j) x
  linarith only [hx]

end CKN

end
