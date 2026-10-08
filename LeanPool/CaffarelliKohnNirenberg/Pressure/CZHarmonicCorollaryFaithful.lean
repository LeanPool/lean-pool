/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZHarmonicCorollary
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionGrowthLocalBox

/-!
# CZHarmonic Corollary Faithful

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
noncomputable section

namespace CKN

/-- The source-level Calderón--Zygmund/harmonic/force decomposition, with the
completed second-Riesz identification, the all-order harmonic estimate, and
force cancellation conditional only on slice-wise distributional
divergence-freeness. -/
theorem czHarmonic_corollary_of_sws :
    ∀ k : ℕ, ∃ C₁₆ : ℝ, 0 ≤ C₁₆ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ : ℝ},
          (hρ : 0 < ρ) →
          closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
          let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
          let c : ℝ → Vec3 := fun t j =>
            average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)
          (∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
            (∀ x ∈ euclideanBall z.1 (13 * ρ / 20),
              p (x, s) = czPressurePart η u c p f s x +
                harmonicPressurePart η u c p s x + forcePressurePart η f s x) ∧
            czPressurePart η u c p f s =ᵐ[volume] czPressureRieszPart η u c s ∧
            WeaklyHarmonicOn (euclideanBall z.1 (13 * ρ / 20))
              (harmonicPressurePart η u c p s) ∧
            ∀ x ∈ vec3Ball z.1 (ρ / 2),
              ‖iteratedFDeriv ℝ k (harmonicPressurePart η u c p s) x‖ ≤
                C₁₆ * ρ ^ (-(2 + k : ℝ)) *
                  (alpha u z ρ ^ 2 +
                    lpNorm (fun y : Vec3 => p (y, s))
                      (ENNReal.ofReal (3 / 2 : ℝ))
                      (volume.restrict (vec3Ball z.1 ρ)))) ∧
          ((∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
            DistributionalDivergenceFree (fun x : Vec3 => f (x, s))) →
            ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
              forcePressurePart η f s =ᵐ[volume] 0) := by
  intro k
  obtain ⟨C₁₆, hC₁₆, hbound⟩ := exists_harmonicPressurePart_Ck_ae_of_sws k
  refine ⟨C₁₆, hC₁₆, ?_⟩
  intro Ω I q u Du p f hsol z ρ hρ hsub
  dsimp only
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  let c : ℝ → Vec3 := fun t j =>
    average (volume.restrict (vec3Ball z.1 ρ))
      (fun y : Vec3 => u (y, t) j)
  have hballΩ : closure (vec3Ball z.1 ρ) ⊆ Ω := by
    intro x hx
    have hxclosed : vec3EuclideanNorm (x - z.1) ≤ ρ := by
      rw [closure_vec3Ball hρ] at hx
      exact hx
    have hpair : (x, z.2) ∈ closure (parabolicCylinder z.1 z.2 ρ) := by
      rw [closure_parabolicCylinder hρ]
      exact ⟨hxclosed, ⟨by nlinarith only [sq_pos_of_pos hρ], le_rfl⟩⟩
    have hdom := hsub hpair
    change x ∈ Ω ∧ z.2 ∈ I at hdom
    exact hdom.1
  have htime : Ioc (z.2 - ρ ^ 2) z.2 ⊆ I := by
    intro s hs
    have hzball : z.1 ∈ vec3Ball z.1 ρ := by
      rw [mem_vec3Ball]
      simpa [vec3EuclideanNorm] using hρ
    have hpoint : (z.1, s) ∈ parabolicCylinder z.1 z.2 ρ := by
      rw [mem_parabolicCylinder]
      exact ⟨hzball, hs.1, hs.2⟩
    have hdom := hsub (subset_closure hpoint)
    change z.1 ∈ Ω ∧ s ∈ I at hdom
    exact hdom.2
  have hRiesz := pressureP1_riesz_identity_of_sws hsol hρ hballΩ
  have hRieszJ := ae_restrict_of_ae_restrict_of_subset htime hRiesz
  have hRieszJ' : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      czPressurePart η u c p f s =ᵐ[volume] czPressureRieszPart η u c s := by
    exact hRieszJ
  have hsplit : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ x ∈ euclideanBall z.1 (13 * ρ / 20),
        p (x, s) = czPressurePart η u c p f s x +
          harmonicPressurePart η u c p s x + forcePressurePart η f s x := by
    filter_upwards [] with s
    intro x hx
    exact czHarmonic_decomposition_on_inner_ball u c p f z.1 hρ s hx
  have hharm := czHarmonic_harmonicPart_weaklyHarmonicOn_ae_of_sws
    hsol hρ hsub
  have hbound' := hbound hsol hρ hsub
  have hmain : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ x ∈ euclideanBall z.1 (13 * ρ / 20),
        p (x, s) = czPressurePart η u c p f s x +
          harmonicPressurePart η u c p s x + forcePressurePart η f s x) ∧
      czPressurePart η u c p f s =ᵐ[volume] czPressureRieszPart η u c s ∧
      WeaklyHarmonicOn (euclideanBall z.1 (13 * ρ / 20))
        (harmonicPressurePart η u c p s) ∧
      ∀ x ∈ vec3Ball z.1 (ρ / 2),
        ‖iteratedFDeriv ℝ k (harmonicPressurePart η u c p s) x‖ ≤
          C₁₆ * ρ ^ (-(2 + k : ℝ)) *
            (alpha u z ρ ^ 2 +
              lpNorm (fun y : Vec3 => p (y, s))
                (ENNReal.ofReal (3 / 2 : ℝ))
                (volume.restrict (vec3Ball z.1 ρ))) := by
    filter_upwards [hsplit, hRieszJ', hharm, hbound']
      with s hs hsR hsH hsCk
    exact ⟨hs, hsR, hsH, hsCk⟩
  refine ⟨hmain, ?_⟩
  intro hdiv
  simpa [forcePressurePart, η] using
    czHarmonic_forcePart_eq_zero_of_divergenceFree_ae_of_sws
      hsol hρ hsub hdiv

end CKN

end
