/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEarlyMajorant

/-!
# Local trace integrability from quadratic growth

The quadratic growth bound makes the rescaled field square integrable on
each bounded strip used in the initial-time cutoff estimate.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The shifted rescaling has integrable quadratic mass on a bounded
closed early-time strip. -/
theorem bu_short_shifted_trace_integrable
    (M scale R ε : ℝ) (hM : 0 < M)
    (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε) (hεsmall : ε < 1 / 4)
    (w : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1))
    (hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (w z) ≤
        Real.exp (M * vec3EuclideanNorm z.1 ^ 2)) :
    IntegrableOn
      (fun z => vec3EuclideanNorm
        ((buAffineField (-scale ^ 2 / 2) scale w) z) ^ 2)
      (spaceTimeSet (buShortTraceBall R)
        (Icc (1 / 2 + ε) (1 / 2 + 2 * ε))) volume := by
  let B := buShortTraceBall R
  let I := Icc (1 / 2 + ε) (1 / 2 + 2 * ε)
  let S := spaceTimeSet B I
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let f : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (v z) ^ 2
  let C : Set ParabolicPoint := parabolicHomeomorph ⁻¹'
    (euclideanClosedBall 0 (2 * R) ×ˢ Icc (1 / 2 : ℝ) 1)
  have hCcompact : IsCompact C := by
    dsimp [C]
    apply parabolicHomeomorph.isCompact_preimage.mpr
    exact (isCompact_euclideanClosedBall (0 : Vec3)
      (by positivity)).prod isCompact_Icc
  have hSsubC : S ⊆ C := by
    intro z hz
    rcases hz with ⟨hy, ht⟩
    have hyclosed : z.1 ∈ euclideanClosedBall 0 (2 * R) := by
      change euclideanSqDist z.1 0 ≤ (2 * R) ^ 2
      exact (show euclideanSqDist z.1 0 < (2 * R) ^ 2 from hy.1).le
    change z.1 ∈ euclideanClosedBall 0 (2 * R) ∧
      z.2 ∈ Icc (1 / 2 : ℝ) 1
    exact ⟨hyclosed, ⟨by linarith only [ht.1, hε], by
      linarith only [ht.2, hεsmall]⟩⟩
  have hCfinite : (volume : Measure ParabolicPoint) C < ⊤ := by
    have hCfin : IsFiniteMeasure ((volume : Measure ParabolicPoint).restrict C) :=
      CKN.isFiniteMeasure_restrict_of_isCompact hCcompact
    simpa using hCfin.measure_univ_lt_top
  have hSfinite : (volume : Measure ParabolicPoint) S < ⊤ :=
    (measure_mono hSsubC).trans_lt hCfinite
  have hSmeas : MeasurableSet S := by
    change MeasurableSet (parabolicHomeomorph ⁻¹' (B ×ˢ I))
    exact (((buShortTraceBall_geometry hR).1.measurableSet).prod
      measurableSet_Icc).preimage parabolicHomeomorph.measurable
  have hSsub : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
      (Ioo (1 / 2 : ℝ) 1) := by
    intro z hz
    exact ⟨(buShortTraceBall_geometry hR).2.2 hz.1,
      ⟨by linarith only [hz.2.1, hε], by
        linarith only [hz.2.2, hεsmall]⟩⟩
  have hcontv := bu_short_field_continuousOn scale hscale hscale1 w hcont
  have hcontS : ContinuousOn v S := by
    apply hcontv.mono
    intro z hz
    exact ⟨(hSsub hz).1, (hSsub hz).2.1.le, (hSsub hz).2.2⟩
  have hfcont : ContinuousOn f S :=
    (continuous_vec3EuclideanNorm.pow 2).comp_continuousOn hcontS
  have hfmeas : AEStronglyMeasurable f (volume.restrict S) :=
    hfcont.aestronglyMeasurable hSmeas
  let A := M * scale ^ 2
  let C₀ := Real.exp (A * (2 * R) ^ 2) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbound : ∀ᵐ z ∂(volume.restrict S), ‖f z‖ ≤ C₀ := by
    filter_upwards [ae_restrict_mem hSmeas] with z hz
    have hz' := hSsub hz
    have hg := bu_short_field_growth M scale hscale hscale1 w hgrowth hz'
    have hyNorm : vec3EuclideanNorm z.1 < 2 * R := by
      have h := (mem_euclideanBall_iff_vecEuclideanNorm_lt
        (show 0 < 2 * R by positivity)).1 hz.1.1
      simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq,
        vecDot, sub_zero, pow_two] using h
    have hySq : vec3EuclideanNorm z.1 ^ 2 ≤ (2 * R) ^ 2 := by
      nlinarith only [hyNorm, vec3EuclideanNorm_nonneg z.1]
    have hExp : Real.exp (A * vec3EuclideanNorm z.1 ^ 2) ≤
        Real.exp (A * (2 * R) ^ 2) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hySq hA)
    have hnorm : 0 ≤ vec3EuclideanNorm (v z) :=
      vec3EuclideanNorm_nonneg _
    have hExp0 : 0 ≤ Real.exp (A * (2 * R) ^ 2) :=
      (Real.exp_pos _).le
    change |vec3EuclideanNorm (v z) ^ 2| ≤ C₀
    rw [abs_of_nonneg (sq_nonneg _)]
    dsimp [C₀]
    nlinarith only [hg, hExp, hnorm, hExp0]
  exact IntegrableOn.of_bound hSfinite hfmeas C₀ hbound

end ESS
