/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.ForceCancellationUnconditional

/-!
# Force Divergence Free Bridge

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
noncomputable section

namespace CKN

/-- The space-time distributional force identity implies the slice-wise
distributional divergence condition used by the force cancellation consumers. -/
theorem pressure_force_slice_divergenceFree_of_spacetime
    {I : Set ℝ} {f : ParabolicPoint → Vec3}
    (hloc : ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
      LocallyIntegrable (fun x : Vec3 => f (x, s) i) volume)
    (hslice : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ᵐ s ∂volume.restrict I,
        ∫ x, ∑ i : Fin 3, f (x, s) i * (fderiv ℝ ψ x) (basisVec i)
          ∂volume = 0) :
    ∀ᵐ s ∂volume.restrict I,
      DistributionalDivergenceFree (fun x : Vec3 => f (x, s)) := by
  have hdiv := ae_distributional_divergence_free_of_forall_test hloc hslice
  filter_upwards [hdiv] with s hs
  intro ψ hψ
  exact hs ψ hψ

/-- The force cancellation theorem with the slice-wise divergence interface
used by the pressure consumers. -/
theorem pressure_force_eq_zero_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hdiv : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      DistributionalDivergenceFree (fun x : Vec3 => f (x, s))) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f s =ᵐ[volume] 0 := by
  have hproducer := pressure_force_memLp_and_lpNorm_growth_ae_of_sws
    hsol hρ hsub
  let C : ℝ → ℝ := fun s =>
    CKN.Foundation.Euclidean.pressureP7GrowthConstant
        (mollifiedBallCutoff z.1 hρ) f s
        (vec3EuclideanNorm z.1 + ρ) +
      CKN.Foundation.Euclidean.pressureP8GrowthConstant
        (mollifiedBallCutoff z.1 hρ) f s
        (vec3EuclideanNorm z.1 + ρ)
  have hmem : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ R : ℝ, 0 < R →
        MemLp (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2))
          (volume.restrict (euclideanBall (0 : Vec3) R)) :=
    hproducer.mono fun s hs => hs.1
  have hgrowth : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      0 ≤ C s ∧ ∀ R : ℝ, 0 < R →
        lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2))
          (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C s * (1 + R) := by
    filter_upwards [hproducer] with s hs
    exact ⟨by simpa [C] using hs.2.1, by simpa [C] using hs.2.2⟩
  exact pressure_force_eq_zero_of_sws_distributionalDivergenceFree
    hsol hρ hsub hdiv hmem hgrowth

end CKN
