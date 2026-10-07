/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.NewtonianRepresentationSource
public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZHarmonicResidualIdentification

/-!
# Pressure Decomposition Riesz

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean
noncomputable section

namespace CKN

/-- The eight-term pressure decomposition with its first term realized by the
completed double-Riesz extension, for almost every time in the interior
parabolic cylinder. -/
theorem pressure_decomposition_eight_terms_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    let η := mollifiedBallCutoff z.1 hρ
    let c := fun s j => average (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, s) j)
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (fun x => η x * p (x, s)) =ᵐ[volume]
        (fun x => pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
          (fun i j y => η y * pressureUTensor u c (y, s) i j) x +
          pressureP2 η u c s x + pressureP3 η u c s x + pressureP4 η u c s x +
          pressureP5 η p s x + pressureP6 η p s x + pressureP7 η f s x + pressureP8 η f s x) := by
  exact pressure_newtonian_representation_source hsol hρ hsub

/-- The first summand in the pressure decomposition is the completed
double-Riesz extension of the cut-off velocity tensor on almost every slice. -/
theorem pressure_decomposition_first_term_riesz_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y => u (y, t) j)) p f s =ᵐ[volume]
        pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
          (fun i j y => mollifiedBallCutoff z.1 hρ y *
            pressureUTensor u
              (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                (fun y => u (y, t) j)) (y, s) i j) := by
  change ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
    pressureP1 (mollifiedBallCutoff z.1 hρ) u
      (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
        (fun y => u (y, t) j)) p f s =ᵐ[volume]
      pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
        (czPressureSource (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y => u (y, t) j)) s)
  exact czPressurePart_ae_eq_rieszSecond_of_sws hsol hρ hsub

end CKN

end
