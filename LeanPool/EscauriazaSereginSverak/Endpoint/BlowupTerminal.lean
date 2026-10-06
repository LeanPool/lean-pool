/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTenThirdsVector
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceBasic

public section

open MeasureTheory Filter CKN.Foundation.Parabolic
open scoped ENNReal
namespace ESS

/-- A ball centered at the rescaled point is exactly the inverse image of
the corresponding source ball. -/
theorem blowup_rescaled_ball_eq
    (x₀ c : Vec3) (r : ℝ) (hr : 0 < r) :
    CKN.rescaledSpace r x₀ (vec3Ball (x₀ + r • c) r) =
      vec3Ball c 1 := by
  ext y
  have hdiff : x₀ + r • y - (x₀ + r • c) = r • (y - c) := by
    rw [smul_sub]
    abel
  simp only [CKN.rescaledSpace, CKN.scalingSpace, Set.mem_preimage,
    mem_vec3Ball, hdiff, vec3EuclideanNorm_smul, abs_of_pos hr]
  simpa only [mul_one] using
    (mul_lt_mul_iff_of_pos_left hr
      (b := vec3EuclideanNorm (y - c)) (c := 1))

/-- Critical spatial `L³` mass is unchanged when a shrinking source ball is
rescaled to a fixed unit ball. -/
theorem blowup_rescaled_ball_velocity_mass_eq
    (u : Vec3 → Vec3)
    (hu : AEStronglyMeasurable u (volume : Measure Vec3))
    (x₀ c : Vec3) (r : ℝ) (hr : 0 < r) :
    (∫⁻ x in vec3Ball c 1,
      ENNReal.ofReal (vec3EuclideanNorm (r • u (x₀ + r • x))) ^ (3 : ℝ)) =
    ∫⁻ y in vec3Ball (x₀ + r • c) r,
      ENNReal.ofReal (vec3EuclideanNorm (u y)) ^ (3 : ℝ) := by
  let B := vec3Ball c 1
  let Ω := vec3Ball (x₀ + r • c) r
  have hB : MeasurableSet B := vec3Ball_measurable c 1
  have hΩ : MeasurableSet Ω := vec3Ball_measurable _ _
  have hI : AEStronglyMeasurable (Ω.indicator u) (volume : Measure Vec3) :=
    (aestronglyMeasurable_indicator_iff hΩ).mpr hu.restrict
  have hmem (x : Vec3) : x ∈ B ↔ x₀ + r • x ∈ Ω := by
    have hs := blowup_rescaled_ball_eq x₀ c r hr
    simpa only [B, Ω, CKN.rescaledSpace, CKN.scalingSpace,
      Set.mem_preimage] using (Set.ext_iff.mp hs x).symm
  have hleft (x : Vec3) :
      ENNReal.ofReal (vec3EuclideanNorm (r • Ω.indicator u (x₀ + r • x))) ^
          (3 : ℝ) =
      B.indicator (fun z =>
        ENNReal.ofReal (vec3EuclideanNorm (r • u (x₀ + r • z))) ^ (3 : ℝ)) x := by
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hmem x).mp hx)]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (mt (hmem x).mpr hx)]
      simp [vec3EuclideanNorm_zero]
  have hright (y : Vec3) :
      ENNReal.ofReal (vec3EuclideanNorm (Ω.indicator u y)) ^ (3 : ℝ) =
      Ω.indicator (fun z =>
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)) y := by
    by_cases hy : y ∈ Ω
    · simp only [Set.indicator_of_mem hy]
    · simp only [Set.indicator_of_notMem hy]
      simp [vec3EuclideanNorm_zero]
  have h := blowupVelocitySlice_mass_eq (Ω.indicator u) hI x₀ r hr
  simp_rw [hleft, hright] at h
  simpa only [MeasureTheory.lintegral_indicator hB,
    MeasureTheory.lintegral_indicator hΩ] using h

/-- The critical `L³` seminorm of the Euclidean velocity magnitude is
preserved by spatial rescaling between corresponding balls. -/
theorem blowup_rescaled_ball_velocity_eLpNorm_three_eq
    (u : Vec3 → Vec3)
    (hu : AEStronglyMeasurable u (volume : Measure Vec3))
    (x₀ c : Vec3) (r : ℝ) (hr : 0 < r) :
    eLpNorm (fun x => vec3EuclideanNorm (r • u (x₀ + r • x))) 3
      (volume.restrict (vec3Ball c 1)) =
    eLpNorm (fun y => vec3EuclideanNorm (u y)) 3
      (volume.restrict (vec3Ball (x₀ + r • c) r)) := by
  let g : Vec3 → ℝ := fun y => vec3EuclideanNorm (u y)
  have hgm : AEStronglyMeasurable g (volume : Measure Vec3) :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hu
  let a : ℝ≥0∞ := ENNReal.ofReal (r⁻¹ ^ 3)
  have hmap : Measure.map (CKN.scalingSpace r x₀) volume =
      a • (volume : Measure Vec3) := CKN.map_scalingSpace r hr x₀
  have hga : AEStronglyMeasurable g
      (Measure.map (CKN.scalingSpace r x₀) volume) := by
    rw [hmap]
    exact hgm.mono_ac Measure.smul_absolutelyContinuous
  have hscaleMeas : Measurable (CKN.scalingSpace r x₀) := by
    unfold CKN.scalingSpace
    fun_prop
  have hcomp : AEStronglyMeasurable (g ∘ CKN.scalingSpace r x₀)
      (volume : Measure Vec3) :=
    hga.comp_aemeasurable hscaleMeas.aemeasurable
  have hrescaled : AEStronglyMeasurable
      (fun x => vec3EuclideanNorm (r • u (x₀ + r • x)))
      (volume : Measure Vec3) := by
    have hmul := hcomp.const_mul r
    convert hmul using 1
    funext x
    simp only [Function.comp_def, CKN.scalingSpace, g,
      vec3EuclideanNorm_smul, abs_of_pos hr]
  have hleft :
      eLpNorm (fun x => vec3EuclideanNorm (r • u (x₀ + r • x))) 3
        (volume.restrict (vec3Ball c 1)) =
      (∫⁻ x in vec3Ball c 1,
        ENNReal.ofReal (vec3EuclideanNorm (r • u (x₀ + r • x))) ^
          (3 : ℝ)) ^ (1 / 3 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (3 : ℝ≥0∞) ≠ 0)
      (by finiteness : (3 : ℝ≥0∞) ≠ ⊤) hrescaled.restrict]
    norm_num
    simp only [Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
  have hright :
      eLpNorm (fun y => vec3EuclideanNorm (u y)) 3
        (volume.restrict (vec3Ball (x₀ + r • c) r)) =
      (∫⁻ y in vec3Ball (x₀ + r • c) r,
        ENNReal.ofReal (vec3EuclideanNorm (u y)) ^ (3 : ℝ)) ^
          (1 / 3 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (3 : ℝ≥0∞) ≠ 0)
      (by finiteness : (3 : ℝ≥0∞) ≠ ⊤) hgm.restrict]
    norm_num
    simp only [g, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
  rw [hleft, hright, blowup_rescaled_ball_velocity_mass_eq u hu x₀ c r hr]

/-- A positive spatial rescaling preserves almost everywhere strong
measurability of a velocity slice. -/
theorem blowup_rescaled_velocitySlice_aestronglyMeasurable
    (u : Vec3 → Vec3)
    (hu : AEStronglyMeasurable u (volume : Measure Vec3))
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r) :
    AEStronglyMeasurable (fun x => r • u (x₀ + r • x))
      (volume : Measure Vec3) := by
  let a : ℝ≥0∞ := ENNReal.ofReal (r⁻¹ ^ 3)
  have hmap : Measure.map (CKN.scalingSpace r x₀) volume =
      a • (volume : Measure Vec3) := CKN.map_scalingSpace r hr x₀
  have hua : AEStronglyMeasurable u
      (Measure.map (CKN.scalingSpace r x₀) volume) := by
    rw [hmap]
    exact hu.mono_ac Measure.smul_absolutelyContinuous
  have hscaleMeas : Measurable (CKN.scalingSpace r x₀) := by
    unfold CKN.scalingSpace
    fun_prop
  have hcomp : AEStronglyMeasurable (u ∘ CKN.scalingSpace r x₀)
      (volume : Measure Vec3) :=
    hua.comp_aemeasurable hscaleMeas.aemeasurable
  have hcont : Continuous (fun v : Vec3 => r • v) := by fun_prop
  have hscaled := hcont.comp_aestronglyMeasurable hcomp
  simpa only [Function.comp_def, CKN.scalingSpace] using hscaled

/-- The `L³` mass of a fixed velocity slice vanishes on balls whose radii
shrink to zero, even when their centers move with the radii. -/
theorem blowup_terminal_shrinking_ball_eLpNorm_tendsto_zero
    {E : Type*} [NormedAddCommGroup E]
    (u : Vec3 → E) (hu : MemLp u 3 (volume : Measure Vec3))
    (x₀ c : Vec3) (r : ℕ → ℝ)
    (hr0 : Tendsto r atTop (nhds 0)) :
    Tendsto (fun k => eLpNorm u 3
      (volume.restrict (vec3Ball (x₀ + r k • c) (r k))))
      atTop (nhds 0) := by
  have hR : Tendsto (fun k => ENNReal.ofReal (r k)) atTop (nhds 0) := by
    change Tendsto (ENNReal.ofReal ∘ r) atTop (nhds 0)
    simpa only [ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hr0
  have hV : Tendsto (fun k => volume (vec3Ball (x₀ + r k • c) (r k)))
      atTop (nhds 0) := by
    simp_rw [volume_vec3Ball_eq]
    simpa using ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow hR)
      (Or.inr ENNReal.ofReal_ne_top :
        (0 : ℝ≥0∞) ^ 3 ≠ 0 ∨ ENNReal.ofReal (Real.pi * 4 / 3) ≠ ∞)
  have hSmall := hu.tendsto_eLpNorm_restrict_zero
    (by norm_num : (1 : ℝ≥0∞) ≤ 3)
    (by norm_num : (3 : ℝ≥0∞) ≠ ∞)
  rw [ENNReal.tendsto_nhds_zero] at hSmall ⊢
  intro ε hε
  have hEv := hSmall ε hε
  obtain ⟨δ, hδ, hδSmall⟩ := ENNReal.nhds_zero_basis_Iic.eventually_iff.mp hEv
  have hVev : ∀ᶠ k in atTop,
      volume (vec3Ball (x₀ + r k • c) (r k)) ≤ δ :=
    (ENNReal.tendsto_nhds_zero.mp hV) δ hδ
  filter_upwards [hVev] with k hk
  let B := vec3Ball (x₀ + r k • c) (r k)
  have hle : eLpNorm u 3 (volume.restrict B) ≤
      ⨆ (s : Set Vec3) (_ : volume s ≤ volume B),
        eLpNorm u 3 (volume.restrict s) := by
    exact le_iSup_of_le B (le_iSup_of_le le_rfl le_rfl)
  exact hle.trans (hδSmall hk)

/-- The Euclidean magnitude of a rescaled fixed `L³` slice vanishes in
`L²` on every unit ball. -/
theorem blowup_terminal_rescaled_eLpNorm_two_tendsto_zero
    (u : Vec3 → Vec3)
    (hu : AEStronglyMeasurable u (volume : Measure Vec3))
    (hu₃ : MemLp (fun y => vec3EuclideanNorm (u y)) 3
      (volume : Measure Vec3))
    (x₀ c : Vec3) (r : ℕ → ℝ)
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (nhds 0)) :
    Tendsto (fun k => eLpNorm
      (fun x => vec3EuclideanNorm (r k • u (x₀ + r k • x))) 2
      (volume.restrict (vec3Ball c 1))) atTop (nhds 0) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball c 1)
  have h₃ : Tendsto (fun k => eLpNorm
      (fun x => vec3EuclideanNorm (r k • u (x₀ + r k • x))) 3 μ)
      atTop (nhds 0) := by
    have hsmall := blowup_terminal_shrinking_ball_eLpNorm_tendsto_zero
      (fun y => vec3EuclideanNorm (u y)) hu₃ x₀ c r hr0
    have heq (k : ℕ) :
        eLpNorm (fun x => vec3EuclideanNorm (r k • u (x₀ + r k • x))) 3 μ =
        eLpNorm (fun y => vec3EuclideanNorm (u y)) 3
          (volume.restrict (vec3Ball (x₀ + r k • c) (r k))) :=
      blowup_rescaled_ball_velocity_eLpNorm_three_eq u hu x₀ c (r k) (hr k)
    exact hsmall.congr' (Eventually.of_forall fun k => (heq k).symm)
  let C : ℝ≥0∞ := (μ Set.univ) ^ (1 / 6 : ℝ)
  have hC : C < ⊤ := by
    dsimp [C, μ]
    rw [Measure.restrict_apply_univ]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top
        (x := c) (r := 1)).ne
  have hbound (k : ℕ) :
      eLpNorm (fun x => vec3EuclideanNorm (r k • u (x₀ + r k • x))) 2 μ ≤
      eLpNorm (fun x => vec3EuclideanNorm (r k • u (x₀ + r k • x))) 3 μ * C := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos
      (μ := μ)
      (f := fun x => vec3EuclideanNorm (r k • u (x₀ + r k • x)))
      (p := (2 : ℝ≥0∞)) (q := (3 : ℝ≥0∞))
      (by norm_num) (by norm_num)
    convert h using 1
    norm_num [C]
  have hprod : Tendsto (fun k =>
      eLpNorm (fun x => vec3EuclideanNorm (r k • u (x₀ + r k • x))) 3 μ * C)
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const h₃ (Or.inr hC.ne)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hev := (ENNReal.tendsto_nhds_zero.mp hprod) ε hε
  filter_upwards [hev] with k hk
  exact (hbound k).trans hk

/-- A rescaled fixed `L³` terminal slice converges strongly to zero in
local `L²`. -/
theorem blowup_terminal_rescaled_vector_eLpNorm_two_tendsto_zero
    (u : Vec3 → Vec3)
    (hu : AEStronglyMeasurable u (volume : Measure Vec3))
    (hu₃ : MemLp (fun y => vec3EuclideanNorm (u y)) 3
      (volume : Measure Vec3))
    (x₀ c : Vec3) (r : ℕ → ℝ)
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (nhds 0)) :
    Tendsto (fun k => eLpNorm
      (fun x => r k • u (x₀ + r k • x)) 2
      (volume.restrict (vec3Ball c 1))) atTop (nhds 0) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball c 1)
  have hmag := blowup_terminal_rescaled_eLpNorm_two_tendsto_zero
    u hu hu₃ x₀ c r hr hr0
  have hbound (k : ℕ) :
      eLpNorm (fun x => r k • u (x₀ + r k • x)) 2 μ ≤
      eLpNorm (fun x => vec3EuclideanNorm (r k • u (x₀ + r k • x))) 2 μ := by
    apply eLpNorm_mono_enorm_ae
      ((blowup_rescaled_velocitySlice_aestronglyMeasurable
        u hu x₀ (r k) (hr k)).restrict)
    filter_upwards [] with x
    rw [← ofReal_norm, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (norm_le_vec3EuclideanNorm _)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hev := (ENNReal.tendsto_nhds_zero.mp hmag) ε hε
  filter_upwards [hev] with k hk
  exact (hbound k).trans hk

/-- Zero extension of an `L³` velocity slice has an `L³` Euclidean
magnitude. -/
theorem blowup_terminal_indicator_magnitude_memLp
    (B : Set Vec3) (hB : MeasurableSet B)
    (u : Vec3 → Vec3)
    (hu : MemLp u 3 (volume.restrict B)) :
    MemLp (fun y => vec3EuclideanNorm (B.indicator u y)) 3
      (volume : Measure Vec3) := by
  have hEuMeas : AEStronglyMeasurable
      (fun y => vec3EuclideanNorm (u y)) (volume.restrict B) :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      hu.aestronglyMeasurable
  have hEu : MemLp (fun y => vec3EuclideanNorm (u y)) 3
      (volume.restrict B) := by
    apply MemLp.of_le_mul hu hEuMeas
    filter_upwards [] with y
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _)] using
      (vec3EuclideanNorm_le_sqrt_three_mul_norm (u y))
  have hInd : MemLp (B.indicator fun y => vec3EuclideanNorm (u y)) 3
      (volume : Measure Vec3) :=
    (memLp_indicator_iff_restrict hB).mpr hEu
  have hEq : (fun y => vec3EuclideanNorm (B.indicator u y)) =
      B.indicator (fun y => vec3EuclideanNorm (u y)) := by
    funext y
    by_cases hy : y ∈ B
    · simp only [Set.indicator_of_mem hy]
    · simp only [Set.indicator_of_notMem hy, vec3EuclideanNorm_zero]
  rwa [hEq]

/-- The zero extended local terminal trace has rescalings vanishing in
`L²` on every unit ball. -/
theorem blowup_terminal_local_trace_rescaled_tendsto_zero
    (B : Set Vec3) (hB : MeasurableSet B)
    (u : Vec3 → Vec3)
    (hu : MemLp u 3 (volume.restrict B))
    (x₀ c : Vec3) (r : ℕ → ℝ)
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (nhds 0)) :
    Tendsto (fun k => eLpNorm
      (fun x => r k • B.indicator u (x₀ + r k • x)) 2
      (volume.restrict (vec3Ball c 1))) atTop (nhds 0) := by
  have hU : MemLp (B.indicator u) 3 (volume : Measure Vec3) :=
    (memLp_indicator_iff_restrict hB).mpr hu
  have hmag := blowup_terminal_indicator_magnitude_memLp B hB u hu
  exact blowup_terminal_rescaled_vector_eLpNorm_two_tendsto_zero
    (B.indicator u) hU.aestronglyMeasurable hmag x₀ c r hr hr0

end ESS
