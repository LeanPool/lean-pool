/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZP1UnconditionalAssembly
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionGrowthSWS

/-! # The completed-operator pressure decomposition

The whole-space identification of the first pressure term yields the eight-term
Newtonian representation at almost every time of an interior cylinder.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean
noncomputable section
namespace CKN

/-- The localized pressure equals its completed double-Riesz term plus the
seven Newtonian remainder terms at almost every interior-cylinder time. -/
theorem pressure_newtonian_representation_source
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    let η := mollifiedBallCutoff z.1 hρ
    let c := fun s j => average (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y,s) j)
    ∀ᵐ s ∂volume.restrict (Ioc (z.2-ρ^2) z.2),
      (fun x => η x * p (x,s)) =ᵐ[volume]
        (fun x => pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
          (fun i j y => η y * pressureUTensor u c (y,s) i j) x +
          pressureP2 η u c s x + pressureP3 η u c s x + pressureP4 η u c s x +
          pressureP5 η p s x + pressureP6 η p s x + pressureP7 η f s x + pressureP8 η f s x) := by
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  let c : ℝ → Vec3 := fun s j => average
    (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, s) j)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := mollifiedBallCutoff_smooth z.1 hρ
  have hηc : HasCompactSupport η := mollifiedBallCutoff_hasCompactSupport z.1 hρ
  obtain ⟨Ω', J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hηΩ : tsupport η ⊆ Ω :=
    (pressure_cutoff_support_subset_ball z.1 hρ).trans
      (fun x hx => hbox.2.2.1 (subset_closure (hball hx)))
  have htimeI : Ioc (z.2 - ρ ^ 2) z.2 ⊆ I :=
    htime.trans (subset_closure.trans hbox.2.2.2.2.2)
  have hP1 := ae_restrict_of_ae_restrict_of_subset htimeI
    (pressureP1_cz_hP1_ae_of_sws hsol hη hηc hηΩ c)
  have hP1Int := ae_restrict_of_ae_restrict_of_subset htimeI
    (pressureP1_cz_hP1Int_ae_of_sws hsol hη hηc hηΩ c)
  have hSource := pressureUTensor_source_data_ae_of_sws hsol hρ hsub
  have hResidual := pressureSecondExtension_residual_growth_ae_of_sws hsol hρ hsub
  filter_upwards [hP1, hP1Int, hSource, hResidual] with s hsP1 hsP1Int hsSource hsResidual
  obtain ⟨C, hC, hmem, hgrowth⟩ := hsResidual
  have hident := pressureP1_hident_of_pressureSecondExtension_unconditional
    hC hsSource.1 hsP1 hsP1Int hmem hgrowth
  filter_upwards [hident] with x hx
  change η x * p (x, s) = _
  rw [pressure_decomposition_pointwise η u c p f s x, hx]

end CKN
