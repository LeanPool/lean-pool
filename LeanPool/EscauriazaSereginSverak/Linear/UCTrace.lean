/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCollar
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Boundary values from shrinking Gaussian boxes

Continuity turns decay of the parabolic box averages in `thm:uc` into
vanishing of the initial trace.
-/

public section


open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Finite quadratic vector energy controls the Euclidean square on every
measurable subregion. -/
theorem uc_squared_norm_integrable_on_subset
    (S B : Set ParabolicPoint) (w : ParabolicPoint → Vec3)
    (hweak : LocallyIntegrableOn w S volume)
    (hL2 : (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hsub : B ⊆ S) :
    IntegrableOn (fun z : ParabolicPoint => vec3EuclideanNorm (w z) ^ 2) B volume := by
  have hwmeas : AEStronglyMeasurable w (volume.restrict S) :=
    hweak.aestronglyMeasurable
  have hwLp : MemLp w (2 : ℝ≥0∞) (volume.restrict S) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (μ := volume.restrict S)
      (by norm_num) (by norm_num) hwmeas).2
    simpa using hL2
  have hnormInt : Integrable (fun z : ParabolicPoint => ‖w z‖ ^ 2)
      (volume.restrict S) := by
    simpa using hwLp.integrable_norm_pow (p := 2) (by norm_num)
  have hgmeas : AEStronglyMeasurable
      (fun z : ParabolicPoint => vec3EuclideanNorm (w z) ^ 2)
      (volume.restrict S) :=
    ((CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm).pow 2).comp_aestronglyMeasurable
      hwmeas
  have hbound (z : ParabolicPoint) :
      vec3EuclideanNorm (w z) ^ 2 ≤ 3 * ‖w z‖ ^ 2 := by
    have h := vec3EuclideanNorm_le_sqrt_three_mul_norm (w z)
    have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := by norm_num
    have hnn : 0 ≤ vec3EuclideanNorm (w z) := vec3EuclideanNorm_nonneg _
    have hn : 0 ≤ Real.sqrt 3 * ‖w z‖ := by positivity
    nlinarith only [h, hs, hnn, hn, sq_nonneg (‖w z‖)]
  have hgInt : Integrable
      (fun z : ParabolicPoint => vec3EuclideanNorm (w z) ^ 2)
      (volume.restrict S) := by
    apply Integrable.mono' (hnormInt.const_mul 3) hgmeas
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound z
  exact IntegrableOn.mono_set hgInt hsub

private theorem uc_box_measure (x : Vec3) {t : ℝ} (ht : 0 < t) :
    volume.real (spaceTimeSet (vec3Ball x (Real.sqrt (2 * t))) (Ioo t (2 * t))) =
      Real.sqrt (2 * t) ^ 3 * (Real.pi * 4 / 3) * t := by
  have hrad : 0 ≤ Real.sqrt (2 * t) := Real.sqrt_nonneg _
  have hπ : 0 ≤ Real.pi * 4 / 3 := by positivity
  rw [measureReal_def,
    CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
  change (((volume : Measure Vec3).prod (volume : Measure ℝ))
      (vec3Ball x (Real.sqrt (2 * t)) ×ˢ Ioo t (2 * t))).toReal = _
  rw [Measure.prod_prod, volume_vec3Ball_eq, Real.volume_Ioo]
  have htime : (2 * t - t) = t := by ring
  rw [htime, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hrad, ENNReal.toReal_ofReal hπ,
    ENNReal.toReal_ofReal ht.le]

/-- The shrinking box has a fixed volume after parabolic normalization. -/
theorem uc_box_normalized_measure (x : Vec3) {t : ℝ} (ht : 0 < t) :
    Real.rpow t (-(5 / 2 : ℝ)) *
      volume.real (spaceTimeSet (vec3Ball x (Real.sqrt (2 * t))) (Ioo t (2 * t))) =
        Real.sqrt 2 ^ 3 * (Real.pi * 4 / 3) := by
  rw [uc_box_measure x ht]
  have hsqrt : Real.sqrt (2 * t) = Real.sqrt 2 * Real.sqrt t := by
    exact Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) t
  rw [hsqrt]
  have htroot : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hrootpos : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  change t ^ (-(5 / 2 : ℝ)) *
    ((Real.sqrt 2 * Real.sqrt t) ^ 3 * (Real.pi * 4 / 3) * t) = _
  rw [show (-(5 / 2 : ℝ)) = (-5 : ℝ) / 2 by ring,
    Real.rpow_div_two_eq_sqrt (-5) ht.le,
    Real.rpow_neg_ofNat (Real.sqrt t) 5, zpow_neg]
  have hprod :
      (Real.sqrt 2 * Real.sqrt t) ^ 3 * (Real.pi * 4 / 3) * t =
        Real.sqrt t ^ 5 * (Real.sqrt 2 ^ 3 * (Real.pi * 4 / 3)) := by
    calc
      _ = (Real.sqrt 2 * Real.sqrt t) ^ 3 * (Real.pi * 4 / 3) *
          Real.sqrt t ^ 2 := by rw [htroot]
      _ = _ := by ring
  calc
    (Real.sqrt t ^ (5 : ℕ))⁻¹ *
        ((Real.sqrt 2 * Real.sqrt t) ^ 3 * (Real.pi * 4 / 3) * t) =
      (Real.sqrt t ^ 5)⁻¹ * (Real.sqrt t ^ 5) *
        (Real.sqrt 2 ^ 3 * (Real.pi * 4 / 3)) := by
          rw [hprod]
          ring_nf
    _ = _ := by
      rw [inv_mul_cancel₀ (pow_ne_zero _ hrootpos.ne')]
      ring

/-- Every shrinking box has finite space-time volume. -/
theorem uc_box_measure_lt_top (x : Vec3) (t : ℝ) :
    volume (spaceTimeSet (vec3Ball x (Real.sqrt (2 * t))) (Ioo t (2 * t))) < ∞ := by
  rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
  change ((volume : Measure Vec3).prod (volume : Measure ℝ))
    (vec3Ball x (Real.sqrt (2 * t)) ×ˢ Ioo t (2 * t)) < ∞
  rw [Measure.prod_prod, Real.volume_Ioo]
  exact ENNReal.mul_lt_top
    (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top (x := x))
    ENNReal.ofReal_lt_top

/-- Decay of integrable box averages and continuity give a zero boundary
value (`thm:uc`). -/
theorem uc_shrinking_average_to_trace
    (x : Vec3) (w : ParabolicPoint → Vec3) (S : Set ParabolicPoint)
    (τ : ℝ) (hτ : 0 < τ)
    (hcont : ContinuousWithinAt w S (x, 0))
    (hB : ∀ t : ℝ, 0 < t → t < τ →
      spaceTimeSet (vec3Ball x (Real.sqrt (2 * t))) (Ioo t (2 * t)) ⊆ S)
    (hInt : ∀ t : ℝ, 0 < t → t < τ → IntegrableOn
      (fun z : ParabolicPoint => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (vec3Ball x (Real.sqrt (2 * t))) (Ioo t (2 * t))) volume)
    (havg : Filter.Tendsto
      (fun t : ℝ => Real.rpow t (-(5 / 2 : ℝ)) *
        ∫ z in spaceTimeSet (vec3Ball x (Real.sqrt (2 * t))) (Ioo t (2 * t)),
          vec3EuclideanNorm (w z) ^ 2)
      (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    w (x, 0) = 0 := by
  let g : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (w z) ^ 2
  have hgcont : ContinuousWithinAt g S (x, 0) :=
    ContinuousAt.comp_continuousWithinAt
      ((CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm).pow 2).continuousAt hcont
  have hg0 : 0 ≤ g (x, 0) := sq_nonneg _
  by_contra hnonzero
  have hgpos : 0 < g (x, 0) := by
    have hnormpos : 0 < vec3EuclideanNorm (w (x, 0)) := by
      rw [vec3EuclideanNorm_eq_l2]
      exact norm_pos_iff.mpr (by
        intro h
        apply hnonzero
        simpa only [WithLp.toLp_eq_zero] using h)
    exact sq_pos_of_pos hnormpos
  let c : ℝ := g (x, 0) / 2
  have hc : 0 < c := by dsimp [c]; linarith only [hgpos]
  have hcbase : c < g ((x, 0) : ParabolicPoint) := by
    dsimp [c]
    linarith only [hgpos]
  have hnear := hgcont.preimage_mem_nhdsWithin
    (IsOpen.mem_nhds isOpen_Ioi hcbase)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp hnear
  let κ : ℝ := Real.sqrt 2 ^ 3 * (Real.pi * 4 / 3)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hsmall : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0),
      Real.rpow t (-(5 / 2 : ℝ)) *
        (∫ z in spaceTimeSet (vec3Ball x (Real.sqrt (2 * t))) (Ioo t (2 * t)),
          vec3EuclideanNorm (w z) ^ 2) < κ * c := by
    exact havg.eventually (eventually_lt_nhds (mul_pos hκ hc))
  have htpos : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), 0 < t := self_mem_nhdsWithin
  have htδ : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), t < δ ^ 2 / 2 :=
    (eventually_lt_nhds (by positivity : (0 : ℝ) < δ ^ 2 / 2)).filter_mono
      nhdsWithin_le_nhds
  have htτ : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), t < τ :=
    (eventually_lt_nhds hτ).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, htt, httau, htavg⟩ :=
    (htpos.and (htδ.and (htτ.and hsmall))).exists
  have hroot : Real.sqrt (2 * t) < δ := by
    apply (Real.sqrt_lt' hδ).2
    linarith only [htt]
  let B : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball x (Real.sqrt (2 * t))) (Ioo t (2 * t))
  have hlower : ∀ z ∈ B, c ≤ g z := by
    intro z hz
    have htime : 0 < z.2 := lt_trans ht hz.2.1
    have htimeupper : z.2 < 2 * t := hz.2.2
    have hzlow : c < g z := by
      apply hball
      constructor
      · change dist z (x, 0) < δ
        calc
          _ = parabolicDist z ((x, 0) : ParabolicPoint) :=
            dist_eq_parabolicDist z ((x, 0) : ParabolicPoint)
          _ < δ := by
            change max (vec3EuclideanNorm (z.1 - x))
              (Real.sqrt |z.2 - 0|) < δ
            apply max_lt
            · exact hz.1.trans hroot
            · rw [sub_zero, abs_of_pos htime]
              exact (Real.sqrt_lt_sqrt htime.le htimeupper).trans hroot
      · exact hB t ht httau hz
    exact hzlow.le
  have hBmeas : MeasurableSet B := by
    exact (vec3Ball_measurable x _).prod measurableSet_Ioo
  have hBfinite : volume B ≠ ∞ :=
    (uc_box_measure_lt_top x t).ne
  have hIntegral : c * volume.real B ≤ ∫ z in B, g z := by
    exact setIntegral_ge_of_const_le_real hBmeas hBfinite hlower (hInt t ht httau)
  have htrpow : 0 ≤ Real.rpow t (-(5 / 2 : ℝ)) :=
    (Real.rpow_pos_of_pos ht _).le
  have hScaled := mul_le_mul_of_nonneg_left hIntegral htrpow
  have hnormed : κ * c ≤ Real.rpow t (-(5 / 2 : ℝ)) * ∫ z in B, g z := by
    calc
      κ * c = Real.rpow t (-(5 / 2 : ℝ)) * volume.real B * c := by
        rw [uc_box_normalized_measure x ht]
      _ = Real.rpow t (-(5 / 2 : ℝ)) * (c * volume.real B) := by ring
      _ ≤ _ := hScaled
  exact (not_lt_of_ge hnormed) htavg

/-- The source continuity and quadratic-integrability hypotheses supply the
shrinking-box trace argument on a spatial cylinder (`thm:uc`). -/
theorem uc_shrinking_average_to_trace_on_cylinder
    (R T : ℝ) (hT : 0 < T)
    (x₀ x : Vec3) (hx : x ∈ vec3Ball x₀ R)
    (w : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w (spaceTimeSet (vec3Ball x₀ R) (Ico 0 T)))
    (hwloc : LocallyIntegrableOn w
      (spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T)) volume)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T),
      ‖w z‖ₑ ^ (2 : ℝ)) < ⊤)
    (havg : Filter.Tendsto
      (fun t : ℝ => Real.rpow t (-(5 / 2 : ℝ)) *
        ∫ z in spaceTimeSet (vec3Ball x (Real.sqrt (2 * t))) (Ioo t (2 * t)),
          vec3EuclideanNorm (w z) ^ 2)
      (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    w (x, 0) = 0 := by
  let d : ℝ := R - vec3EuclideanNorm (x - x₀)
  have hd : 0 < d := by
    have hx' := (mem_vec3Ball).1 hx
    exact sub_pos.mpr hx'
  let τ : ℝ := min (T / 2) (d ^ 2 / 2)
  have hτ : 0 < τ := lt_min (by linarith only [hT]) (by positivity)
  let S : Set ParabolicPoint := spaceTimeSet (vec3Ball x₀ R) (Ico 0 T)
  let U : Set ParabolicPoint := spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T)
  have hB (t : ℝ) (ht : 0 < t) (htτ : t < τ) :
      spaceTimeSet (vec3Ball x (Real.sqrt (2 * t))) (Ioo t (2 * t)) ⊆ U := by
    have htT : 2 * t < T := by
      have hτT : τ ≤ T / 2 := min_le_left _ _
      linarith only [htτ, hτT]
    have hrad : Real.sqrt (2 * t) < d := by
      apply (Real.sqrt_lt' hd).2
      have hτd : τ ≤ d ^ 2 / 2 := min_le_right _ _
      linarith only [htτ, hτd]
    rintro z ⟨hzx, hzt⟩
    have hzball : z.1 ∈ vec3Ball x₀ R := by
      apply (mem_vec3Ball).2
      have htri := vec3EuclideanNorm_add_le (z.1 - x) (x - x₀)
      have hzdist : vec3EuclideanNorm (z.1 - x) < Real.sqrt (2 * t) := hzx
      have hnorm : vec3EuclideanNorm (z.1 - x₀) ≤
          vec3EuclideanNorm (z.1 - x) + vec3EuclideanNorm (x - x₀) := by
        simpa only [sub_add_sub_cancel] using htri
      linarith only [hnorm, hzdist, hrad]
    exact ⟨hzball, lt_trans ht hzt.1, lt_trans hzt.2 htT⟩
  have hBS (t : ℝ) (ht : 0 < t) (htτ : t < τ) :
      spaceTimeSet (vec3Ball x (Real.sqrt (2 * t))) (Ioo t (2 * t)) ⊆ S := by
    intro z hz
    have hzU := hB t ht htτ hz
    exact ⟨hzU.1, ⟨hzU.2.1.le, hzU.2.2⟩⟩
  have hInt (t : ℝ) (ht : 0 < t) (htτ : t < τ) :
      IntegrableOn (fun z : ParabolicPoint => vec3EuclideanNorm (w z) ^ 2)
        (spaceTimeSet (vec3Ball x (Real.sqrt (2 * t))) (Ioo t (2 * t))) volume :=
    uc_squared_norm_integrable_on_subset U _ w hwloc hL2 (hB t ht htτ)
  have hp : ((x, 0) : ParabolicPoint) ∈ S := by
    exact ⟨hx, ⟨le_refl 0, hT⟩⟩
  exact uc_shrinking_average_to_trace x w S τ hτ
    (hcont.continuousWithinAt hp) hBS hInt havg

end ESS
