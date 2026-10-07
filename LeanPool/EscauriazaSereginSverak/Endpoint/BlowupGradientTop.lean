/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupGradientRescale
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Blowup Gradient Top

Gradient estimates for the rescaled sequence used in endpoint compactness.
-/

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace ESS

/-- Uniform bounds on past subcylinders extend to the open terminal time. -/
theorem blowup_nonnegative_integral_bound_to_time_zero
    (A : Set Vec3) (hA : MeasurableSet A) (a C : ℝ)
    (f : ParabolicPoint → ℝ)
    (hf : ∀ b : ℝ, b < 0 → IntegrableOn f (A ×ˢ Ioo a b) volume)
    (hnonneg : ∀ z, 0 ≤ f z)
    (hbound : ∀ b : ℝ, b < 0 →
      (∫ (z : ParabolicPoint) in A ×ˢ Ioo a b, f z) ≤ C) :
    IntegrableOn f (A ×ˢ Ioo a 0) volume ∧
      (∫ (z : ParabolicPoint) in A ×ˢ Ioo a 0, f z) ≤ C := by
  let s : Set ParabolicPoint := A ×ˢ Ioo a 0
  let b : ℕ → ℝ := fun n => -(1 / ((n : ℝ) + 1))
  let φ : ℕ → Set ParabolicPoint := fun n => A ×ˢ Ioo a (b n)
  let μ : Measure ParabolicPoint := volume.restrict s
  have hs : MeasurableSet s := hA.prod measurableSet_Ioo
  have hbneg (n : ℕ) : b n < 0 := by dsimp [b]; exact neg_neg_of_pos (by positivity)
  have hb0 : Tendsto b atTop (nhds 0) := by
    simpa only [b, neg_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  have hφmeas (n : ℕ) : MeasurableSet (φ n) := hA.prod measurableSet_Ioo
  have hφsub (n : ℕ) : φ n ⊆ s := by
    intro z hz
    exact ⟨hz.1, hz.2.1, lt_trans hz.2.2 (hbneg n)⟩
  have hcover : AECover μ atTop φ := by
    apply aecover_restrict_of_ae_imp hs
    · filter_upwards [] with z hz
      have hz' : z.2 < 0 := hz.2.2
      filter_upwards [hb0.eventually (eventually_gt_nhds hz')] with n hn
      exact ⟨hz.1, hz.2.1, hn⟩
    · exact hφmeas
  have hμeq (n : ℕ) : μ.restrict (φ n) = volume.restrict (φ n) := by
    rw [show μ = volume.restrict s by rfl,
      Measure.restrict_restrict (hφmeas n), inter_eq_left.mpr (hφsub n)]
  have hfi (n : ℕ) : IntegrableOn f (φ n) μ := by
    change Integrable f (μ.restrict (φ n))
    rw [hμeq]
    exact hf (b n) (hbneg n)
  have hnonneg_ae : ∀ᵐ z ∂μ, 0 ≤ f z :=
    Filter.Eventually.of_forall hnonneg
  have hbounded : ∀ᶠ n in atTop, (∫ z in φ n, f z ∂μ) ≤ C := by
    filter_upwards [] with n
    rw [hμeq]
    exact hbound (b n) (hbneg n)
  have hint : Integrable f μ :=
    hcover.integrable_of_integral_bounded_of_nonneg_ae C hfi hnonneg_ae hbounded
  have htop : (∫ z, f z ∂μ) ≤ C :=
    le_of_tendsto (hcover.integral_tendsto_of_countably_generated hint) hbounded
  refine ⟨hint, ?_⟩
  change (∫ z in s, f z ∂volume) ≤ C
  simpa only [μ] using htop

/-- The suitable energy on a finite past cylinder is integrable on each
smaller cylinder whose upper time is negative. -/
theorem blowupGradient_integrableOn_inner_pastBox
    (R a b : ℝ) (hR : 0 < R) (hb : b < 0)
    {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable
      (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0) q u Du p 0) :
    IntegrableOn (fun z => spatialGradientSq u Du z)
      (spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a b)) volume := by
  let inner := spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a b)
  let ψ := blowupEnergyCutoff R a b
  have htest := (blowupEnergyCutoff_test R a b hR hb).1
  have hpos := (blowupEnergyCutoff_test R a b hR hb).2
  have hweighted : IntegrableOn
      (fun z : ParabolicPoint => spatialGradientSq u Du z * ψ z) inner volume :=
    (suitableWeakSolution_energy_integrable hsol htest hpos).1.integrableOn
  have hinnerMeas : MeasurableSet inner := by
    change MeasurableSet (CKN.euclideanBall 0 R ×ˢ Ioo a b)
    exact (isOpen_euclideanBall 0 R).measurableSet.prod measurableSet_Ioo
  apply hweighted.congr_fun _ hinnerMeas
  intro z hz
  change spatialGradientSq u Du z * blowupEnergyCutoff R a b z =
    spatialGradientSq u Du z
  rw [blowupEnergyCutoff_eq_one hR hb
    ⟨hz.1, ⟨hz.2.1.le, hz.2.2.le⟩⟩, mul_one]

/-- A uniform energy estimate below time zero includes the full open past
cylinder up to time zero. -/
theorem blowupGradient_bound_to_time_zero
    (R a C : ℝ) (hR : 0 < R)
    {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable
      (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0) q u Du p 0)
    (hbound : ∀ b : ℝ, b < 0 →
      2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a b),
        spatialGradientSq u Du z) ≤ C) :
    IntegrableOn (fun z => spatialGradientSq u Du z)
      (spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a 0)) volume ∧
    2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a 0),
      spatialGradientSq u Du z) ≤ C := by
  have hA : MeasurableSet (CKN.euclideanBall (0 : Vec3) R) :=
    (isOpen_euclideanBall 0 R).measurableSet
  have hinner : ∀ b : ℝ, b < 0 →
      IntegrableOn (fun z => spatialGradientSq u Du z)
        (CKN.euclideanBall 0 R ×ˢ Ioo a b) volume := by
    intro b hb
    exact blowupGradient_integrableOn_inner_pastBox R a b hR hb hsol
  have hnonneg : ∀ z : ParabolicPoint, 0 ≤ spatialGradientSq u Du z := by
    intro z
    dsimp [spatialGradientSq]
    positivity
  have hhalf : ∀ b : ℝ, b < 0 →
      (∫ (z : ParabolicPoint) in CKN.euclideanBall 0 R ×ˢ Ioo a b,
        spatialGradientSq u Du z) ≤ C / 2 := by
    intro b hb
    have h := hbound b hb
    dsimp only [spaceTimeSet] at h
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    calc
      (∫ (z : ParabolicPoint) in CKN.euclideanBall 0 R ×ˢ Ioo a b,
          spatialGradientSq u Du z) * 2 =
          2 * (∫ (z : ParabolicPoint) in CKN.euclideanBall 0 R ×ˢ Ioo a b,
            spatialGradientSq u Du z) := by ring
      _ ≤ C := h
  obtain ⟨hint, htop⟩ :=
    blowup_nonnegative_integral_bound_to_time_zero
      (CKN.euclideanBall 0 R) hA a (C / 2)
      (fun z => spatialGradientSq u Du z) hinner hnonneg hhalf
  refine ⟨hint, ?_⟩
  dsimp only [spaceTimeSet]
  calc
    2 * (∫ (z : ParabolicPoint) in CKN.euclideanBall 0 R ×ˢ Ioo a 0,
      spatialGradientSq u Du z) =
        (∫ (z : ParabolicPoint) in CKN.euclideanBall 0 R ×ˢ Ioo a 0,
          spatialGradientSq u Du z) * 2 := by ring
    _ ≤ C := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).1 htop

/-- The same scale tail controls the gradient energy on the full open past
cylinder up to time zero. -/
theorem blowupRescale_eventually_gradient_bound_to_time_zero_of_local_norms
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ)
    (hSuitable : IsSuitableWeakSolution (vec3Ball 0 (3 / 4 : ℝ))
      (Ioo (-1) 0) 3 u Du p (0 : ParabolicPoint → Vec3))
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) (hR : 0 < R) (ha : a < 0)
    (hvel : ∃ Bᵤ : ℝ≥0∞, Bᵤ < ⊤ ∧
      ∀ᶠ k in atTop,
        eLpNorm (fun z => vec3EuclideanNorm
          (blowupVelocity x₀ t₀ (r k) u z)) 3
          (volume.restrict (vec3Ball 0 (R + 1) ×ˢ Ioo (a - 2) 0)) ≤ Bᵤ)
    (hpress : ∃ Bₚ : ℝ≥0∞, Bₚ < ⊤ ∧
      ∀ᶠ k in atTop,
        eLpNorm (blowupPressure x₀ t₀ (r k) p) (3 / 2 : ℝ≥0∞)
          (volume.restrict (vec3Ball 0 (R + 1) ×ˢ Ioo (a - 2) 0)) ≤ Bₚ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      IntegrableOn (fun z => spatialGradientSq
        (parabolicRescaleVelocity x₀ t₀ (r k) u)
        (parabolicRescaleGradient x₀ t₀ (r k) Du) z)
        (spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a 0)) volume ∧
      2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a 0),
        spatialGradientSq
          (parabolicRescaleVelocity x₀ t₀ (r k) u)
          (parabolicRescaleGradient x₀ t₀ (r k) Du) z) ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    blowupRescale_eventually_gradient_bound_of_local_norms
      u Du p hSuitable x₀ t₀ r hx₀ ht₀ hr hr0 R a hR ha hvel hpress
  have hsuit := blowupRescale_eventually_suitableIntegrable_outer
    u Du p hSuitable x₀ t₀ r hx₀ ht₀ hr hr0 R a hR ha
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsuit, hbound] with k hk hb
  exact blowupGradient_bound_to_time_zero R a C hR hk (hb)

end ESS
