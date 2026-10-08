/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCInitialErrorNear

/-!
# Weighted mass on the initial time transition

A bounded Gaussian weight turns unweighted integral flatness and finite
quadratic mass into bounds for the initial cutoff error.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private theorem uc_weighted_mass_le
    {S : Set ParabolicPoint} (hS : MeasurableSet S)
    {F : ParabolicPoint → ℝ} (hF : Measurable F)
    {M : ℝ} (hF0 : ∀ z ∈ S, 0 ≤ F z)
    (hFM : ∀ z ∈ S, F z ≤ M)
    {v : ParabolicPoint → Vec3}
    (hv : IntegrableOn (fun z => vec3EuclideanNorm (v z) ^ 2) S volume) :
    IntegrableOn (fun z => F z * vec3EuclideanNorm (v z) ^ 2) S volume ∧
      (∫ z in S, F z * vec3EuclideanNorm (v z) ^ 2) ≤
        M * ∫ z in S, vec3EuclideanNorm (v z) ^ 2 := by
  let μ := volume.restrict S
  have hFMnorm : ∀ᵐ z ∂μ, ‖F z‖ ≤ M := by
    filter_upwards [ae_restrict_mem hS] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 z hz)]
    exact hFM z hz
  have hFmeas : AEStronglyMeasurable F μ := hF.aestronglyMeasurable
  have hInt' : Integrable (fun z =>
      F z * vec3EuclideanNorm (v z) ^ 2) μ := by
    have h := hv.mul_bdd hFmeas hFMnorm
    convert h using 1
    ext z
    ring
  have hconst : Integrable (fun z =>
      M * vec3EuclideanNorm (v z) ^ 2) μ := hv.const_mul M
  have hpoint : ∀ᵐ z ∂μ,
      F z * vec3EuclideanNorm (v z) ^ 2 ≤
        M * vec3EuclideanNorm (v z) ^ 2 := by
    filter_upwards [ae_restrict_mem hS] with z hz
    exact mul_le_mul_of_nonneg_right (hFM z hz) (sq_nonneg _)
  refine ⟨hInt', ?_⟩
  have hle := integral_mono_ae hInt' hconst hpoint
  simpa only [integral_const_mul] using hle

/-- The weighted mass during the initial cutoff transition has a
polynomially flat near part and an exponentially suppressed far part. -/
theorem uc_initial_weighted_transition_bound
    (ρ : ℝ) (hρ : 4 ≤ ρ) (a : ℝ) (ha : 0 ≤ a)
    (v : ParabolicPoint → Vec3)
    (hInt : IntegrableOn (fun z => vec3EuclideanNorm (v z) ^ 2)
      (ucCylinder ρ) volume)
    (hflat : UCIntegralFlatness 0 ρ 2 v)
    (N : ℕ) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        let r := Real.sqrt (Real.sqrt ε)
        let B := (ε * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a)
        (∫ z in spaceTimeSet (vec3Ball 0 ρ) (Icc ε (2 * ε)),
          ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2) ≤
          B * (C * ε ^ N +
            Real.exp (-(r ^ 2 / (8 * ε))) *
              ∫ z in ucCylinder ρ, vec3EuclideanNorm (v z) ^ 2) := by
  obtain ⟨C, δ₀, hC, hδ₀, hnear⟩ :=
    uc_initial_near_mass_le ρ hρ v hInt hflat N
  let δ := min δ₀ (1 / 4 : ℝ)
  have hδ : 0 < δ := lt_min hδ₀ (by norm_num)
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro ε hε hεδ
  dsimp
  let r := Real.sqrt (Real.sqrt ε)
  let B := (ε * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a)
  have hεsmall : ε < 1 / 4 := hεδ.trans_le (min_le_right _ _)
  have hε1 : ε ≤ 1 := by linarith only [hεsmall]
  have h2ε : 2 * ε < 2 := by linarith only [hεsmall]
  obtain ⟨hr, hrρ, _, _⟩ :=
    uc_initial_error_fourth_root_geometry hρ hε hεsmall
  let S : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball 0 ρ) (Icc ε (2 * ε))
  let A : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball 0 r) (Icc ε (2 * ε))
  let F : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball 0 ρ \ vec3Ball 0 r) (Icc ε (2 * ε))
  have hSmeas : MeasurableSet S := by
    dsimp [S, spaceTimeSet]
    exact (isOpen_vec3Ball 0 ρ).measurableSet.prod measurableSet_Icc
  have hAmeas : MeasurableSet A := by
    dsimp [A, spaceTimeSet]
    exact (isOpen_vec3Ball 0 r).measurableSet.prod measurableSet_Icc
  have hFmeas : MeasurableSet F := by
    dsimp [F, spaceTimeSet]
    exact ((isOpen_vec3Ball 0 ρ).measurableSet.diff
      (isOpen_vec3Ball 0 r).measurableSet).prod measurableSet_Icc
  have hSsub : S ⊆ ucCylinder ρ := by
    intro z hz
    exact ⟨hz.1, ⟨hε.trans_le hz.2.1, hz.2.2.trans_lt h2ε⟩⟩
  have hAsub : A ⊆ S := by
    intro z hz
    exact ⟨(vec3Ball_mono hrρ.le) hz.1, hz.2⟩
  have hFsub : F ⊆ S := by
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  have hIntA : IntegrableOn (fun z => vec3EuclideanNorm (v z) ^ 2)
      A volume := hInt.mono_set (hAsub.trans hSsub)
  have hIntF : IntegrableOn (fun z => vec3EuclideanNorm (v z) ^ 2)
      F volume := hInt.mono_set (hFsub.trans hSsub)
  have hweightA0 (z : ParabolicPoint) (hz : z ∈ A) :
      0 ≤ ucGaussianWeight a z :=
    ucGaussianWeight_nonneg a (hε.trans_le hz.2.1)
  have hweightF0 (z : ParabolicPoint) (hz : z ∈ F) :
      0 ≤ ucGaussianWeight a z :=
    ucGaussianWeight_nonneg a (hε.trans_le hz.2.1)
  have hweightA (z : ParabolicPoint) (hz : z ∈ A) :
      ucGaussianWeight a z ≤ B := by
    apply ucGaussianWeight_le_after hε ha hz.2.1
    exact hz.2.2.trans h2ε.le
  have hweightF (z : ParabolicPoint) (hz : z ∈ F) :
      ucGaussianWeight a z ≤
        B * Real.exp (-(r ^ 2 / (8 * ε))) := by
    exact ucGaussianWeight_le_far_initial hε ha hr hε1
      hz.2.1 hz.2.2 hz.1.2
  obtain ⟨hIntWA, hWA⟩ := uc_weighted_mass_le hAmeas
    (ucGaussianWeight_measurable a) hweightA0 hweightA hIntA
  obtain ⟨hIntWF, hWF⟩ := uc_weighted_mass_le hFmeas
    (ucGaussianWeight_measurable a) hweightF0 hweightF hIntF
  have hUnion : S = A ∪ F := by
    ext z
    constructor
    · intro hz
      by_cases hzA : z.1 ∈ vec3Ball 0 r
      · exact Or.inl ⟨hzA, hz.2⟩
      · exact Or.inr ⟨⟨hz.1, hzA⟩, hz.2⟩
    · rintro (hz | hz)
      · exact hAsub hz
      · exact hFsub hz
  have hDisj : Disjoint A F := by
    apply Set.disjoint_left.mpr
    intro z hzA hzF
    exact hzF.1.2 hzA.1
  have hmassA := hnear ε hε (hεδ.trans_le (min_le_left _ _))
  change (∫ z in A, vec3EuclideanNorm (v z) ^ 2) ≤ C * ε ^ N
    at hmassA
  have hmassF : (∫ z in F, vec3EuclideanNorm (v z) ^ 2) ≤
      ∫ z in ucCylinder ρ, vec3EuclideanNorm (v z) ^ 2 := by
    apply setIntegral_mono_set hInt _
      (Filter.Eventually.of_forall (hFsub.trans hSsub))
    filter_upwards [] with z
    exact sq_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBE : 0 ≤ B * Real.exp (-(r ^ 2 / (8 * ε))) := by
    positivity
  change (∫ z in S, ucGaussianWeight a z *
      vec3EuclideanNorm (v z) ^ 2) ≤
      B * (C * ε ^ N +
        Real.exp (-(r ^ 2 / (8 * ε))) *
          ∫ z in ucCylinder ρ, vec3EuclideanNorm (v z) ^ 2)
  rw [hUnion, setIntegral_union hDisj hFmeas hIntWA hIntWF]
  calc
    (∫ z in A, ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2) +
        (∫ z in F, ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2) ≤
      B * (∫ z in A, vec3EuclideanNorm (v z) ^ 2) +
        (B * Real.exp (-(r ^ 2 / (8 * ε)))) *
          (∫ z in F, vec3EuclideanNorm (v z) ^ 2) :=
      add_le_add hWA hWF
    _ ≤ B * (C * ε ^ N) +
        (B * Real.exp (-(r ^ 2 / (8 * ε)))) *
          (∫ z in ucCylinder ρ, vec3EuclideanNorm (v z) ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hmassA hB)
        (mul_le_mul_of_nonneg_left hmassF hBE)
    _ = _ := by ring


end ESS
