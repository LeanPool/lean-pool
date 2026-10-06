/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionGrowthLocalBoxGrowth

/-!
# Identification Extension Growth Local Box

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
noncomputable section
namespace CKN
open CKN.Foundation.Euclidean
/-- The first term in the localized pressure decomposition is the completed
whole-space second Riesz extension of its cut-off velocity tensor, for almost
every time in the full open solution interval.  The paper's literal singular
integral is represented by the completed indexed operator; see deviation B48. -/
theorem pressureP1_riesz_identity_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (vec3Ball x₀ ρ) ⊆ Ω) :
    ∀ᵐ s ∂volume.restrict I,
      pressureP1 (mollifiedBallCutoff x₀ hρ) u
        (fun t j => average (volume.restrict (vec3Ball x₀ ρ))
          (fun y => u (y, t) j)) p f s =ᵐ[volume]
        pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
          (fun i j x => mollifiedBallCutoff x₀ hρ x *
            pressureUTensor u
              (fun t j => average (volume.restrict (vec3Ball x₀ ρ))
                (fun y => u (y, t) j)) (x, s) i j) := by
  let η : Vec3 → ℝ := mollifiedBallCutoff x₀ hρ
  let c : ℝ → Vec3 := fun t j =>
    average (volume.restrict (vec3Ball x₀ ρ)) (fun y => u (y, t) j)
  have hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η] using mollifiedBallCutoff_smooth x₀ hρ
  have hηc : HasCompactSupport η := by
    simpa [η] using mollifiedBallCutoff_hasCompactSupport x₀ hρ
  have hηΩ : tsupport η ⊆ Ω := by
    exact (pressure_cutoff_support_subset_ball x₀ hρ).trans
      (subset_closure.trans hsub)
  have hP1 := pressureP1_cz_hP1_ae_of_sws hsol hηsmooth hηc hηΩ c
  have hP1Int := pressureP1_cz_hP1Int_ae_of_sws hsol hηsmooth hηc hηΩ c
  have hKcompact : IsCompact (closure (vec3Ball x₀ ρ)) :=
    isCompact_closure_vec3Ball hρ
  obtain ⟨Ω', hΩ'open, hKΩ', hΩ'Ω, hΩ'compact⟩ :=
    exists_open_between_and_isCompact_closure hKcompact hsol.1 hsub
  have hball : vec3Ball x₀ ρ ⊆ Ω' := subset_closure.trans hKΩ'
  let P : ℝ → Prop := fun s =>
    pressureP1 η u c p f s =ᵐ[volume]
      pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
        (fun i j x => η x * pressureUTensor u c (x, s) i j)
  let bad : Set ℝ := {s | s ∈ I ∧ ¬ P s}
  have hbadNull : volume bad = 0 := by
    apply MeasureTheory.measure_null_of_locally_null bad
    intro t ht
    have htI : t ∈ I := ht.1
    obtain ⟨ε, hε, hεI⟩ := Metric.mem_nhds_iff.mp
      ((hsol.2.1).mem_nhds htI)
    let δ : ℝ := ε / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith only [hε]
    have hδlt : δ < ε := by dsimp [δ]; linarith only [hε]
    have hJsub : Metric.closedBall t δ ⊆ I :=
      (closedBall_subset_ball hδlt).trans hεI
    let J : Set ℝ := Metric.closedBall t δ
    have hJcompact : IsCompact (closure J) := by
      simpa only [J, Metric.closure_closedBall] using
        (ProperSpace.isCompact_closedBall t δ)
    have hJord : J.OrdConnected := by
      rw [show J = Icc (t - δ) (t + δ) by
        ext s
        simp only [J, mem_closedBall, Real.dist_eq, mem_Icc, abs_le]
        constructor <;> intro hs <;> constructor <;> linarith only [hs.1, hs.2]
      ]
      exact ordConnected_Icc
    have hJsubset : closure J ⊆ I := by
      simpa only [J, Metric.closure_closedBall] using hJsub
    have hbox : localBox Ω I Ω' J :=
      ⟨hΩ'open, hΩ'compact, hΩ'Ω, hJord, hJcompact, hJsubset⟩
    have hlocal := @pressureSecondExtension_residual_growth_ae_of_sws_localBox
      Ω I q u Du p f hsol (x₀, 0) ρ hρ Ω' J hbox hball
    have hP1J := ae_restrict_of_ae_restrict_of_subset hJsub hP1
    have hP1IntJ := ae_restrict_of_ae_restrict_of_subset hJsub hP1Int
    have hEqJ : ∀ᵐ s ∂volume.restrict J, P s := by
      filter_upwards [hlocal, hP1J, hP1IntJ] with s hs hps hpInt
      rcases hs with ⟨hG, ⟨C, hC, hmem, hgrowth⟩⟩
      have hident := pressureP1_hident_of_pressureSecondExtension_unconditional
        hC hG hps hpInt hmem hgrowth
      simpa [P, η, c] using hident
    have hglobalJ : ∀ᵐ s ∂volume, s ∈ J → P s :=
      ae_imp_of_ae_restrict hEqJ
    have hnullJ : volume {s | s ∈ J ∧ ¬ P s} = 0 := by
      have hnull' : volume {s | ¬ (s ∈ J → P s)} = 0 := ae_iff.mp hglobalJ
      simpa only [not_imp] using hnull'
    have hJmeas : MeasurableSet J := by
      simpa [J] using Metric.isClosed_closedBall.measurableSet
    have hballJ : Metric.ball t δ ⊆ J := Metric.ball_subset_closedBall
    have hUsubset : bad ∩ Metric.ball t δ ⊆ {s | s ∈ J ∧ ¬ P s} := by
      rintro s ⟨⟨_hsI, hnotP⟩, hsball⟩
      exact ⟨hballJ hsball, hnotP⟩
    refine ⟨bad ∩ Metric.ball t δ, ?_, measure_mono_null hUsubset hnullJ⟩
    refine mem_nhdsWithin.mpr ⟨Metric.ball t δ, isOpen_ball,
      mem_ball_self hδ, ?_⟩
    intro s hs
    exact ⟨hs.2, hs.1⟩
  have hbadAE : ∀ᵐ s ∂volume, s ∉ bad := by
    filter_upwards [compl_mem_ae_iff.mpr hbadNull] with s hs
    exact hs
  have hIae : ∀ᵐ s ∂volume.restrict I, s ∈ I :=
    ae_restrict_mem hsol.2.1.measurableSet
  filter_upwards [hbadAE.filter_mono ae_restrict_le, hIae] with s hsbad hsI
  have hPs : P s := by
    by_contra hnot
    exact hsbad ⟨hsI, hnot⟩
  simpa [P, η, c] using hPs


end CKN
